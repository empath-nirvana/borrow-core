// pidigits, as bg/pidigits.bc (n = 30 by default, first argument otherwise): the Game's unbounded
// spigot on a hand-written bignum (no GMP, no crate): 32-bit limbs in a Vec<u32>, operations in
// place (multiply by a small number, add, subtract, compare), the signed accumulator as a sign and
// a magnitude, the small quotient by repeated subtraction, as the probe does. Two scratch
// bignums are reused across iterations (as GMP's tmp1/tmp2 in the Game's C program).
use std::cmp::Ordering;
use std::io::Write;
rs::counting!();

fn trim(a: &mut Vec<u32>) { while a.last() == Some(&0) { a.pop(); } }
fn mul_small(a: &mut Vec<u32>, m: u64) {
    let mut c = 0u64;
    for x in a.iter_mut() { let t = *x as u64 * m + c; *x = t as u32; c = t >> 32 }
    while c != 0 { a.push(c as u32); c >>= 32 }
    if m == 0 { a.clear() }
}
fn cmp(a: &[u32], b: &[u32]) -> Ordering {
    if a.len() != b.len() { return a.len().cmp(&b.len()) }
    for i in (0..a.len()).rev() { if a[i] != b[i] { return a[i].cmp(&b[i]) } }
    Ordering::Equal
}
fn add(a: &mut Vec<u32>, b: &[u32]) {
    if a.len() < b.len() { a.resize(b.len(), 0) }
    let mut c = 0u64;
    for i in 0..a.len() {
        let t = a[i] as u64 + *b.get(i).unwrap_or(&0) as u64 + c;
        a[i] = t as u32; c = t >> 32;
        if c == 0 && i >= b.len() { break }
    }
    if c != 0 { a.push(c as u32) }
}
/// a -= b, for a >= b.
fn sub(a: &mut Vec<u32>, b: &[u32]) {
    let mut br = 0i64;
    for i in 0..a.len() {
        let t = a[i] as i64 - *b.get(i).unwrap_or(&0) as i64 - br;
        if t < 0 { a[i] = (t + (1 << 32)) as u32; br = 1 } else { a[i] = t as u32; br = 0 }
        if br == 0 && i >= b.len() { break }
    }
    trim(a);
}
/// b := b - a, for b >= a (a reversed subtraction into a): a = b - a.
fn rsub(a: &mut Vec<u32>, b: &[u32]) {
    let mut br = 0i64;
    if a.len() < b.len() { a.resize(b.len(), 0) }
    for i in 0..a.len() {
        let t = b[i] as i64 - a[i] as i64 - br;
        if t < 0 { a[i] = (t + (1 << 32)) as u32; br = 1 } else { a[i] = t as u32; br = 0 }
    }
    trim(a);
}
struct S { neg: bool, m: Vec<u32> }
impl S {
    /// self += x for a natural x.
    fn add_nat(&mut self, x: &[u32]) {
        if !self.neg { add(&mut self.m, x) }
        else if cmp(&self.m, x) == Ordering::Less { rsub(&mut self.m, x); self.neg = false }
        else { sub(&mut self.m, x); self.neg = !self.m.is_empty() }
    }
    fn sub_nat(&mut self, x: &[u32]) { self.neg = !self.neg && !self.m.is_empty(); self.add_nat(x); self.neg = !self.neg && !self.m.is_empty() }
}
fn extract(num: &[u32], acc: &S, den: &[u32], m: u64, t: &mut S) -> u32 {
    t.m.clear(); t.m.extend_from_slice(num); t.neg = false;
    mul_small(&mut t.m, m);
    if acc.neg { t.sub_nat(&acc.m) } else { t.add_nat(&acc.m) }
    let mut q = 0;
    while cmp(&t.m, den) != Ordering::Less { sub(&mut t.m, den); q += 1 }
    q
}
fn main() {
    let s0 = rs::snap();
    let n: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(30);
    let mut acc = S { neg: false, m: Vec::new() };
    let mut den = vec![1u32];
    let mut num = vec![1u32];
    let mut t = S { neg: false, m: Vec::new() };
    let mut tmp: Vec<u32> = Vec::new();
    let mut out = Vec::with_capacity(16 * n + 16);
    let (mut k, mut i) = (0u64, 0usize);
    while i < n {
        k += 1;
        let k2 = 2 * k + 1;
        tmp.clear(); tmp.extend_from_slice(&num); mul_small(&mut tmp, 2);
        acc.add_nat(&tmp);
        mul_small(&mut acc.m, k2);
        mul_small(&mut den, k2);
        mul_small(&mut num, k);
        if acc.neg || cmp(&num, &acc.m) == Ordering::Greater { continue }
        let d = extract(&num, &acc, &den, 3, &mut t);
        let e = extract(&num, &acc, &den, 4, &mut t);
        if d != e { continue }
        out.push(b'0' + d as u8);
        i += 1;
        if i % 10 == 0 { write!(out, "\t:{}\n", i).unwrap() }
        tmp.clear(); tmp.extend_from_slice(&den); mul_small(&mut tmp, d as u64);
        acc.sub_nat(&tmp);
        mul_small(&mut acc.m, 10);
        mul_small(&mut num, 10);
    }
    rs::report(s0);
    std::io::stdout().write_all(&out).unwrap();
}

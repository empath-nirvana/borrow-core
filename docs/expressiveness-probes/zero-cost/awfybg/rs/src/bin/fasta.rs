// fasta, as bg/fasta.bc (n = 1000 by default): ALU repeated 2n, IUB 3n and HomoSapiens 5n random
// bytes by the Game's LCG, 60 a line, through one output buffer flushed at 8 KiB.
use std::io::Write;
rs::counting!();
const ALU: &[u8] = b"GGCCGGGCGCGGTGGCTCACGCCTGTAATCCCAGCACTTTGGGAGGCCGAGGCGGGCGGATCACCTGAGGTCAGGAGTTCGAGACCAGCCTGGCCAACATGGTGAAACCCCGTCTCTACTAAAAATACAAAAATTAGCCGGGCGTGGTGGCGCGCGCCTGTAATCCCAGCTACTCGGGAGGCTGAGGCAGGAGAATCGCTTGAACCCGGGAGGCGGAGGTTGCAGTGAGCCGAGATCGCGCCACTGCACTCCAGCCTGGGCGACAGAGCGAGACTCCGTCTCAAAAA";
const IM: u32 = 139968;
struct Out { buf: Vec<u8>, out: std::io::Stdout }
impl Out {
    fn byte(&mut self, b: u8) { self.buf.push(b); if self.buf.len() >= 8192 { self.out.write_all(&self.buf).unwrap(); self.buf.clear() } }
}
fn repeat(o: &mut Out, s: &[u8], n: usize) {
    for i in 0..n { o.byte(s[i % s.len()]); if (i + 1) % 60 == 0 { o.byte(b'\n') } }
    if n % 60 != 0 { o.byte(b'\n') }
}
fn random(o: &mut Out, seed: &mut u32, syms: &[u8], probs: &[f64], n: usize) {
    let mut cum = [0.0f64; 16];
    let mut acc = 0.0;
    for (i, p) in probs.iter().enumerate() { acc += p; cum[i] = acc }
    let k = probs.len();
    for i in 0..n {
        *seed = (*seed * 3877 + 29573) % IM;
        let r = *seed as f64 / IM as f64;
        let j = cum[..k].iter().position(|&c| r < c).unwrap_or(k - 1);
        o.byte(syms[j]);
        if (i + 1) % 60 == 0 { o.byte(b'\n') }
    }
    if n % 60 != 0 { o.byte(b'\n') }
}
fn main() {
    let s0 = rs::snap();
    let n: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(1000);
    let mut o = Out { buf: Vec::with_capacity(16384), out: std::io::stdout() };
    for &b in b">ONE Homo sapiens alu\n" { o.byte(b) }
    repeat(&mut o, ALU, 2 * n);
    for &b in b">TWO IUB ambiguity codes\n" { o.byte(b) }
    let mut seed = 42;
    let mut iub = [0.02f64; 15];
    iub[0] = 0.27; iub[1] = 0.12; iub[2] = 0.12; iub[3] = 0.27;
    random(&mut o, &mut seed, b"acgtBDHKMNRSVWY", &iub, 3 * n);
    for &b in b">THREE Homo sapiens frequency\n" { o.byte(b) }
    random(&mut o, &mut seed, b"acgt", &[0.3029549426680, 0.1979883004921, 0.1975473066391, 0.3015094502008], 5 * n);
    o.out.write_all(&o.buf).unwrap();
    o.out.flush().unwrap();
    rs::report(s0);
}

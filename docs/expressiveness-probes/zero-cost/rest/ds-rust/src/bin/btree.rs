// ds/btree.bc, three Rust forms on the same keys:
//  (1) the same arena design (keys[5u..], kids[6u..], cnt[u], leaf[u]; CLRS insert, min degree 3)
//  (2) std BTreeMap<K, count> (one allocation per node; duplicates as a count)
//  (3) the natural boxed form: struct Node { keys: Vec<K>, kids: Vec<Box<Node>> } (CLRS, t = 3)
#[path = "../count.rs"] mod count;
use std::collections::BTreeMap;
const MT: usize = 3; const MAXK: usize = 5;
struct BT<K> { ks: Vec<K>, kids: Vec<usize>, cnt: Vec<usize>, leaf: Vec<bool>, root: usize }
impl<K: Copy + Default> BT<K> {
    fn new() -> Self { let mut t = BT { ks: Vec::with_capacity(16), kids: Vec::with_capacity(16), cnt: Vec::with_capacity(4), leaf: Vec::with_capacity(4), root: 0 }; t.new_node(true); t }
    fn new_node(&mut self, l: bool) -> usize { let u = self.cnt.len(); for _ in 0..MAXK { self.ks.push(K::default()) } for _ in 0..MAXK + 1 { self.kids.push(0) } self.cnt.push(0); self.leaf.push(l); u }
    fn split_child(&mut self, x: usize, i: usize) {
        let y = self.kids[(MAXK + 1) * x + i]; let yl = self.leaf[y]; let z = self.new_node(yl);
        for j in 0..MT - 1 { self.ks[MAXK * z + j] = self.ks[MAXK * y + j + MT] }
        if !yl { for j in 0..MT { self.kids[(MAXK + 1) * z + j] = self.kids[(MAXK + 1) * y + j + MT] } }
        self.cnt[z] = MT - 1; self.cnt[y] = MT - 1;
        let xn = self.cnt[x];
        for j in (i + 1..=xn).rev() { self.kids[(MAXK + 1) * x + j + 1] = self.kids[(MAXK + 1) * x + j] }
        self.kids[(MAXK + 1) * x + i + 1] = z;
        for j in (i..xn).rev() { self.ks[MAXK * x + j + 1] = self.ks[MAXK * x + j] }
        self.ks[MAXK * x + i] = self.ks[MAXK * y + MT - 1];
        self.cnt[x] = xn + 1;
    }
    fn insert(&mut self, k: K, c: impl Fn(K, K) -> i32) {
        if self.cnt[self.root] == MAXK { let s = self.new_node(false); self.kids[(MAXK + 1) * s] = self.root; self.root = s; self.split_child(s, 0) }
        let mut x = self.root;
        loop {
            let xn = self.cnt[x];
            if self.leaf[x] {
                let mut i = xn as isize - 1;
                while i >= 0 && c(self.ks[MAXK * x + i as usize], k) > 0 { self.ks[MAXK * x + i as usize + 1] = self.ks[MAXK * x + i as usize]; i -= 1 }
                self.ks[MAXK * x + (i + 1) as usize] = k; self.cnt[x] = xn + 1; return
            }
            let mut i = xn as isize - 1;
            while i >= 0 && c(self.ks[MAXK * x + i as usize], k) > 0 { i -= 1 }
            let mut i = (i + 1) as usize;
            let ch = self.kids[(MAXK + 1) * x + i];
            if self.cnt[ch] == MAXK { self.split_child(x, i); if c(k, self.ks[MAXK * x + i]) > 0 { i += 1 } }
            x = self.kids[(MAXK + 1) * x + i];
        }
    }
    fn contains(&self, k: K, c: impl Fn(K, K) -> i32) -> bool {
        let mut x = self.root;
        loop {
            let xn = self.cnt[x]; let mut i = 0; let mut r = 1;
            while i < xn { r = c(k, self.ks[MAXK * x + i]); if r <= 0 { break } i += 1 }
            if r == 0 && i < xn { return true }
            if self.leaf[x] { return false }
            x = self.kids[(MAXK + 1) * x + i];
        }
    }
    fn height(&self) -> usize { let mut x = self.root; let mut h = 1; while !self.leaf[x] { x = self.kids[(MAXK + 1) * x]; h += 1 } h }
}
fn cmp_i32(a: i32, b: i32) -> i32 { (a > b) as i32 - (a < b) as i32 }
fn cmp_pair(a: (i32, i32), b: (i32, i32)) -> i32 { let c = cmp_i32(a.1, b.1); if c == 0 { cmp_i32(a.0, b.0) } else { c } }
fn lcg(x: u32) -> u32 { x.wrapping_mul(1103515245).wrapping_add(12345) & 2147483647 }

struct Node { keys: Vec<i32>, kids: Vec<Box<Node>> }
impl Node {
    fn leaf() -> Box<Node> { Box::new(Node { keys: Vec::with_capacity(MAXK), kids: Vec::new() }) }
    fn split_child(&mut self, i: usize) {
        let y = &mut self.kids[i];
        let mut z = Node::leaf();
        z.keys.extend(y.keys.drain(MT..));
        if !y.kids.is_empty() { z.kids.reserve_exact(MAXK + 1); z.kids.extend(y.kids.drain(MT..)) }
        let med = y.keys.pop().unwrap();
        self.keys.insert(i, med); self.kids.insert(i + 1, z);
    }
    fn insert_nonfull(&mut self, k: i32) {
        let i = self.keys.partition_point(|&v| v <= k);
        if self.kids.is_empty() { self.keys.insert(i, k); return }
        let mut i = i;
        if self.kids[i].keys.len() == MAXK { self.split_child(i); if k > self.keys[i] { i += 1 } }
        self.kids[i].insert_nonfull(k)
    }
    fn contains(&self, k: i32) -> bool { match self.keys.binary_search(&k) { Ok(_) => true, Err(i) => !self.kids.is_empty() && self.kids[i].contains(k) } }
}
fn boxed_insert(root: &mut Box<Node>, k: i32) {
    if root.keys.len() == MAXK { let old = std::mem::replace(root, Node::leaf()); root.kids.reserve_exact(MAXK + 1); root.kids.push(old); root.split_child(0) }
    root.insert_nonfull(k)
}

fn main() {
    count::warm();
    let s0 = count::snap();
    let mut t = BT::<i32>::new();
    let mut x = 1u32;
    for _ in 0..2000 { x = lcg(x); t.insert((x >> 8) as i32, cmp_i32) }
    let mut x = 1u32; let mut hits = 0;
    for _ in 0..2000 { x = lcg(x); if t.contains((x >> 8) as i32, cmp_i32) { hits += 1 } }
    let f = t.contains(-5, cmp_i32); let h = t.height();
    eprintln!("{} {} {}", hits, f as i32, h);
    let mut p = BT::<(i32, i32)>::new();
    for i in 0..100 { p.insert((i, 100 - i), cmp_pair) }
    eprintln!("{}{}", p.contains((40, 60), cmp_pair) as i32, p.contains((40, 61), cmp_pair) as i32);
    drop(t); drop(p);
    count::report("btree same arena design", s0);

    let s0 = count::snap();
    let mut t: BTreeMap<i32, u32> = BTreeMap::new();
    let mut x = 1u32;
    for _ in 0..2000 { x = lcg(x); *t.entry((x >> 8) as i32).or_insert(0) += 1 }
    let mut x = 1u32; let mut hits = 0;
    for _ in 0..2000 { x = lcg(x); if t.contains_key(&((x >> 8) as i32)) { hits += 1 } }
    let f = t.contains_key(&-5);
    eprintln!("{} {}", hits, f as i32);
    let mut p: BTreeMap<(i32, i32), u32> = BTreeMap::new(); // (second, first) as the key order
    for i in 0..100 { *p.entry((100 - i, i)).or_insert(0) += 1 }
    eprintln!("{}{}", p.contains_key(&(60, 40)) as i32, p.contains_key(&(61, 40)) as i32);
    drop(t); drop(p);
    count::report("btree std BTreeMap", s0);

    let s0 = count::snap();
    let mut t = Node::leaf();
    let mut x = 1u32;
    for _ in 0..2000 { x = lcg(x); boxed_insert(&mut t, (x >> 8) as i32) }
    let mut x = 1u32; let mut hits = 0;
    for _ in 0..2000 { x = lcg(x); if t.contains((x >> 8) as i32) { hits += 1 } }
    eprintln!("{} {}", hits, t.contains(-5) as i32);
    drop(t);
    count::report("btree boxed nodes (i32 tree only: Box + keys Vec + kids Vec per node)", s0);
}

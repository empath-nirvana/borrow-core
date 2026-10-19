// ds/pq.bc: std BinaryHeap (min-heap via Reverse) over Strings and u32s; pairs by a comparator
// as an Ord newtype (a performance-minded Rust programmer's comparator heap).
#[path = "../count.rs"] mod count;
use std::cmp::{Ordering, Reverse};
use std::collections::BinaryHeap;
#[derive(PartialEq, Eq)] struct BySecondDesc((i32, i32));
impl Ord for BySecondDesc { fn cmp(&self, o: &Self) -> Ordering { let (a, b) = (self.0, o.0); a.1.cmp(&b.1).then(Ordering::Equal) } }
impl PartialOrd for BySecondDesc { fn partial_cmp(&self, o: &Self) -> Option<Ordering> { Some(self.cmp(o)) } }
fn main() {
    count::warm();
    let s0 = count::snap();
    let mut h: BinaryHeap<Reverse<String>> = BinaryHeap::with_capacity(4);
    for s in ["pear", "apple", "zucchini", "fig"] { h.push(Reverse(s.to_string())) }
    for _ in 0..4 { if let Some(Reverse(s)) = h.pop() { eprint!("{s} ") } }
    eprintln!();
    let mut g: BinaryHeap<Reverse<u32>> = BinaryHeap::with_capacity(4);
    let mut x: u32 = 7;
    for _ in 0..1000 { x = x.wrapping_mul(1103515245).wrapping_add(12345) & 2147483647; g.push(Reverse(x >> 16)) }
    let (mut last, mut bad) = (0u32, 0);
    let mut first = true;
    for _ in 0..1000 { match g.pop() { Some(Reverse(v)) => { if !first && v < last { bad += 1 } last = v; first = false } None => bad += 1 } }
    eprintln!("{bad}");
    let mut q: BinaryHeap<BySecondDesc> = BinaryHeap::with_capacity(4);
    for i in 0..10 { q.push(BySecondDesc((i, (i * 7) & 7))) }
    for _ in 0..4 { if let Some(BySecondDesc((a, b))) = q.pop() { eprint!("{a}/{b} ") } }
    eprintln!();
    drop(h); drop(g); drop(q);
    count::report("pq (std BinaryHeap)", s0);
}

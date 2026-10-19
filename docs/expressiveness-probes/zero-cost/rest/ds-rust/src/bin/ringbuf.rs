// ds/ringbuf.bc: VecDeque at a fixed capacity (push refused when full; push_over drops the oldest).
#[path = "../count.rs"] mod count;
use std::collections::VecDeque;
struct Ring<A> { q: VecDeque<A>, cap: usize }
impl<A> Ring<A> {
    fn new(cap: usize) -> Self { Ring { q: VecDeque::with_capacity(cap), cap } }
    fn push(&mut self, x: A) -> Result<(), A> { if self.q.len() == self.cap { Err(x) } else { self.q.push_back(x); Ok(()) } }
    fn push_over(&mut self, x: A) { if self.q.len() == self.cap { self.q.pop_front(); } self.q.push_back(x) }
}
fn main() {
    count::warm();
    let s0 = count::snap();
    let mut r = Ring::<i32>::new(4);
    for i in 1..7 { r.push_over(i) }
    let n = r.q.len();
    eprint!("{n}:");
    for _ in 0..n { if let Some(x) = r.q.pop_front() { eprint!(" {x}") } }
    eprintln!();
    let mut s = Ring::<String>::new(2);
    let _ = s.push("a".to_string());
    let _ = s.push("b".to_string());
    if let Err(back) = s.push("c".to_string()) { eprint!("{back}") }
    if let Some(f) = s.q.pop_front() { eprint!("{f}") }
    eprintln!();
    drop(s);
    count::report("ringbuf", s0);
}

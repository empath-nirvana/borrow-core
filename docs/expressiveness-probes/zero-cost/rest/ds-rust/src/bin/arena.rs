// ds/arena.bc: Vec<Option<T>> slots (cap 4) + free list Vec<usize> (cap 8) + live count.
#[path = "../count.rs"] mod count;
struct Arena<T> { slots: Vec<Option<T>>, free: Vec<usize>, live: usize }
impl<T> Arena<T> {
    fn new(cap: usize) -> Self { Arena { slots: Vec::with_capacity(cap), free: Vec::with_capacity(8), live: 0 } }
    fn alloc(&mut self, x: T) -> usize {
        self.live += 1;
        match self.free.pop() { Some(i) => { self.slots[i] = Some(x); i } None => { self.slots.push(Some(x)); self.slots.len() - 1 } }
    }
    fn free(&mut self, id: usize) -> Option<T> {
        let o = self.slots[id].take(); if o.is_some() { self.free.push(id); self.live -= 1; } o
    }
    fn with<R>(&mut self, id: usize, f: impl FnOnce(&mut T) -> R, d: R) -> R { match &mut self.slots[id] { Some(x) => f(x), None => d } }
}
fn main() {
    count::warm();
    let s0 = count::snap();
    let mut a = Arena::<String>::new(4);
    let _x = a.alloc("one".to_string());
    let y = a.alloc("two".to_string());
    let _z = a.alloc("three".to_string());
    let got = a.free(y);
    if let Some(s) = got { eprint!("{s}"); }
    eprint!(" ");
    let w = a.alloc("four".to_string());
    let n = a.with(w, |s| { s.push('!'); s.len() }, 0);
    eprintln!("{} {} {} {}", w, n, a.live, a.slots.len());
    drop(a);
    count::report("arena", s0);
}

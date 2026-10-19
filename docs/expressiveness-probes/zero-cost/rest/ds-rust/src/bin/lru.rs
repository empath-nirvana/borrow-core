// ds/lru-arena.bc and ds/lru-cells.bc / ds/dll-cells.bc, three Rust forms:
//  (1) index form: one Vec of nodes {key, val, prev, next} with a sentinel at 0 + HashMap<i32, usize>
//  (2) Rc<RefCell<Node>> doubly linked list + HashMap<i32, Rc<..>>
//  (3) the DLL demo as std LinkedList (one allocation per node) and as one index Vec
#[path = "../count.rs"] mod count;
use std::cell::RefCell;
use std::collections::{HashMap, LinkedList};
use std::rc::{Rc, Weak};

#[derive(Clone, Copy)] struct N { key: i32, val: i32, prev: usize, next: usize }
struct Links { n: Vec<N> }
impl Links {
    fn new() -> Self { let mut n = Vec::with_capacity(8); n.push(N { key: 0, val: 0, prev: 0, next: 0 }); Links { n } }
    fn new_node(&mut self, key: i32, val: i32) -> usize { let i = self.n.len(); self.n.push(N { key, val, prev: i, next: i }); i }
    fn unlink(&mut self, i: usize) { let (a, b) = (self.n[i].prev, self.n[i].next); self.n[b].prev = a; self.n[a].next = b }
    fn link_after(&mut self, at: usize, i: usize) { let b = self.n[at].next; self.n[at].next = i; self.n[i].next = b; self.n[b].prev = i; self.n[i].prev = at }
    fn push_front(&mut self, i: usize) { self.link_after(0, i) }
    fn push_back(&mut self, i: usize) { let last = self.n[0].prev; self.link_after(last, i) }
    fn walk(&self, fwd: bool) { let mut i = 0; loop { i = if fwd { self.n[i].next } else { self.n[i].prev }; if i == 0 { break } eprint!("{i} ") } eprintln!() }
}
struct Lru { m: HashMap<i32, usize>, l: Links, cap: usize }
impl Lru {
    fn new(cap: usize) -> Self { Lru { m: HashMap::with_capacity(cap), l: Links::new(), cap } }
    fn get(&mut self, k: i32) -> Option<i32> { let i = *self.m.get(&k)?; self.l.unlink(i); self.l.push_front(i); Some(self.l.n[i].val) }
    fn put(&mut self, k: i32, v: i32) {
        if let Some(&i) = self.m.get(&k) { self.l.unlink(i); self.l.push_front(i); self.l.n[i].val = v; return }
        if self.m.len() < self.cap { let i = self.l.new_node(k, v); self.m.insert(k, i); self.l.push_front(i) }
        else { let t = self.l.n[0].prev; self.l.unlink(t); self.m.remove(&self.l.n[t].key); self.m.insert(k, t); self.l.n[t].key = k; self.l.n[t].val = v; self.l.push_front(t) }
    }
}

// (2) the pointer form
struct RNode { key: i32, val: i32, prev: Option<Weak<RefCell<RNode>>>, next: Option<Rc<RefCell<RNode>>> }
struct RLru { m: HashMap<i32, Rc<RefCell<RNode>>>, head: Option<Rc<RefCell<RNode>>>, tail: Option<Rc<RefCell<RNode>>>, cap: usize }
impl RLru {
    fn new(cap: usize) -> Self { RLru { m: HashMap::with_capacity(cap), head: None, tail: None, cap } }
    fn detach(&mut self, n: &Rc<RefCell<RNode>>) {
        let (p, nx) = { let mut b = n.borrow_mut(); (b.prev.take().and_then(|w| w.upgrade()), b.next.take()) };
        match &p { Some(p) => p.borrow_mut().next = nx.clone(), None => self.head = nx.clone() }
        match &nx { Some(x) => x.borrow_mut().prev = p.as_ref().map(Rc::downgrade), None => self.tail = p.clone() }
    }
    fn attach_front(&mut self, n: &Rc<RefCell<RNode>>) {
        match self.head.take() { Some(h) => { h.borrow_mut().prev = Some(Rc::downgrade(n)); n.borrow_mut().next = Some(h) } None => self.tail = Some(n.clone()) }
        self.head = Some(n.clone());
    }
    fn get(&mut self, k: i32) -> Option<i32> { let n = self.m.get(&k)?.clone(); self.detach(&n); self.attach_front(&n); let v = n.borrow().val; Some(v) }
    fn put(&mut self, k: i32, v: i32) {
        if let Some(n) = self.m.get(&k).cloned() { n.borrow_mut().val = v; self.detach(&n); self.attach_front(&n); return }
        if self.m.len() == self.cap { let t = self.tail.clone().unwrap(); self.detach(&t); let key = t.borrow().key; self.m.remove(&key); }
        let n = Rc::new(RefCell::new(RNode { key: k, val: v, prev: None, next: None }));
        self.m.insert(k, n.clone()); self.attach_front(&n);
    }
}
fn show(o: Option<i32>) { match o { Some(v) => eprint!("{v} "), None => eprint!("- ") } }

fn main() {
    count::warm();
    // the DLL demo, index form (as ours)
    let s0 = count::snap();
    let mut l = Links::new();
    let (a, b, c, d) = (l.new_node(0, 0), l.new_node(0, 0), l.new_node(0, 0), l.new_node(0, 0));
    l.push_back(a); l.push_back(b); l.push_back(c); l.push_back(d);
    l.unlink(c);
    let e = l.new_node(0, 0); l.push_front(e);
    l.walk(true); l.walk(false);
    drop(l);
    count::report("dll index form (one Vec of nodes)", s0);
    // the DLL demo, std LinkedList: 1 2 3 4, 3 removed (split_off + pop_front + append), 5 at the front
    let s0 = count::snap();
    let mut ll: LinkedList<i32> = LinkedList::new();
    for i in 1..5 { ll.push_back(i) }
    let mut tail = ll.split_off(2); tail.pop_front(); ll.append(&mut tail);
    ll.push_front(5);
    for x in &ll { eprint!("{x} ") } eprintln!();
    for x in ll.iter().rev() { eprint!("{x} ") } eprintln!();
    drop(ll);
    count::report("dll std LinkedList", s0);
    // LRU, index form
    let s0 = count::snap();
    let mut c = Lru::new(2);
    c.put(1, 1); c.put(2, 2); let r1 = c.get(1); c.put(3, 3); let r2 = c.get(2); c.put(4, 4);
    let r3 = c.get(1); let r4 = c.get(3); let r5 = c.get(4);
    show(r1); show(r2); show(r3); show(r4); show(r5); eprintln!();
    drop(c);
    count::report("lru index form (HashMap + Vec<Node>)", s0);
    // LRU, Rc<RefCell> form
    let s0 = count::snap();
    let mut c = RLru::new(2);
    c.put(1, 1); c.put(2, 2); let r1 = c.get(1); c.put(3, 3); let r2 = c.get(2); c.put(4, 4);
    let r3 = c.get(1); let r4 = c.get(3); let r5 = c.get(4);
    show(r1); show(r2); show(r3); show(r4); show(r5); eprintln!();
    drop(c);
    count::report("lru Rc<RefCell<Node>> form", s0);
}

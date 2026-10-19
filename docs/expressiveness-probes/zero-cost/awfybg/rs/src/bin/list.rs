// AWFY List, as awfy/list.bc: tail(makeList(15), makeList(10), makeList(6)), length 10.
// The natural Rust form: owned Box cons lists, `tail` and `isShorterThan` over shared
// references (AWFY shares the arguments between the recursive calls; every result of `tail`
// is a suffix of one of its arguments, so it returns a reference).
rs::counting!();
struct Node { val: i32, next: Option<Box<Node>> }
type L = Option<Box<Node>>;
fn make(n: i32) -> L { if n == 0 { None } else { Some(Box::new(Node { val: n, next: make(n - 1) })) } }
fn length(l: &L) -> i32 { match l { None => 0, Some(n) => 1 + length(&n.next) } }
fn shorter(x: &L, y: &L) -> bool {
    match (x, y) { (_, None) => false, (None, _) => true, (Some(a), Some(b)) => shorter(&a.next, &b.next) }
}
fn next(l: &L) -> &L { match l { None => l, Some(n) => &n.next } }
fn tail<'a>(x: &'a L, y: &'a L, z: &'a L) -> &'a L {
    if shorter(y, x) {
        let a = tail(next(x), y, z);
        let b = tail(next(y), z, x);
        let c = tail(next(z), x, y);
        tail(a, b, c)
    } else { z }
}
fn main() {
    let s0 = rs::snap();
    let (a, b, c) = (make(15), make(10), make(6));
    let r = length(tail(&a, &b, &c));
    let _ = a.as_ref().map(|n| n.val);
    rs::report(s0);
    println!("{}", r);
}

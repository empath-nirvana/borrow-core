// AWFY Storage, as awfy/storage.bc: a tree of depth 7, four children a level (in an array, as
// AWFY), a leaf an array of 1..10 i32s sized by AWFY's Random; counts nodes, 5461.
rs::counting!();
enum S { Leaf(Vec<i32>), Node(Vec<S>) }
fn next(s: &mut i32) -> i32 { *s = (s.wrapping_mul(1309).wrapping_add(13849)) & 65535; *s }
fn build(depth: i32, seed: &mut i32, count: &mut i32) -> S {
    *count += 1;
    if depth == 1 { S::Leaf(vec![0; (next(seed) % 10 + 1) as usize]) }
    else { S::Node((0..4).map(|_| build(depth - 1, seed, count)).collect()) }
}
fn main() {
    let s0 = rs::snap();
    let (mut seed, mut c) = (74755, 0);
    let t = build(7, &mut seed, &mut c);
    rs::report(s0);
    if let S::Node(v) = &t { assert_eq!(v.len(), 4) }
    println!("{}", c);
}

// The boxed B-tree of ds/btree-boxed.bc, mirrored: minimum degree 3 (at most 5 keys a node), a
// node owning its keys and its children, `Vec<Option<Node>>` as `buf (1 + X)`; a leaf's children
// empty (no allocation), an inner node's of capacity 6, every node's keys of capacity 5. CLRS's
// insertion with splits on the way down; 200 keys from the same generator; contains, height, size.
rs::counting!();
const MAXK: usize = 5;
struct Node { keys: Vec<i32>, kids: Vec<Option<Node>> }
fn leaf() -> Node { Node { keys: Vec::with_capacity(MAXK), kids: Vec::new() } }
fn split(x: &mut Node, i: usize) {
    let mut y = x.kids[i].take().unwrap();
    let m = y.keys[2];
    let mut z = Node { keys: Vec::with_capacity(MAXK), kids: Vec::new() };
    z.keys.push(y.keys[3]); z.keys.push(y.keys[4]); y.keys.truncate(2);
    if !y.kids.is_empty() {
        z.kids = Vec::with_capacity(MAXK + 1);
        for j in 0..3 { z.kids.push(y.kids[j + 3].take()) }
        y.kids.truncate(3);
    }
    x.keys.insert(i, m);
    x.kids[i] = Some(y);
    x.kids.insert(i + 1, Some(z));
}
fn ins_nonfull(x: &mut Node, k: i32) {
    let i = x.keys.iter().take_while(|&&v| v < k).count();
    if x.kids.is_empty() { x.keys.insert(i, k); return }
    let full = x.kids[i].as_ref().unwrap().keys.len() == MAXK;
    let j = if full { split(x, i); if x.keys[i] < k { i + 1 } else { i } } else { i };
    ins_nonfull(x.kids[j].as_mut().unwrap(), k)
}
fn insert(t: Node, k: i32) -> Node {
    let mut t = t;
    if t.keys.len() == MAXK {
        let mut s = Node { keys: Vec::with_capacity(MAXK), kids: Vec::with_capacity(MAXK + 1) };
        s.kids.push(Some(t)); split(&mut s, 0); t = s;
    }
    ins_nonfull(&mut t, k); t
}
fn contains(x: &Node, k: i32) -> bool {
    let i = x.keys.iter().take_while(|&&v| v < k).count();
    if i < x.keys.len() && x.keys[i] == k { return true }
    match x.kids.get(i) { Some(Some(c)) => contains(c, k), _ => false }
}
fn height(x: &Node) -> i32 { match x.kids.first() { Some(Some(c)) => 1 + height(c), _ => 1 } }
fn size(x: &Node) -> i32 { x.keys.len() as i32 + x.kids.iter().flatten().map(size).sum::<i32>() }
fn next(x: i32) -> i32 { (x.wrapping_mul(1103515245).wrapping_add(12345)) & 2147483647 }
fn main() {
    let s0 = rs::snap();
    let mut t = leaf();
    let mut x = 1;
    for _ in 0..200 { x = next(x); t = insert(t, ((x as u32) >> 8) as i32) }
    let mut x = 1; let mut hits = 0;
    for _ in 0..200 { x = next(x); if contains(&t, ((x as u32) >> 8) as i32) { hits += 1 } }
    let f = contains(&t, -5);
    let (h, n) = (height(&t), size(&t));
    drop(t);
    rs::report(s0);
    println!("{} {} {}", hits, f as i32, h);
    println!("{}", n);
}

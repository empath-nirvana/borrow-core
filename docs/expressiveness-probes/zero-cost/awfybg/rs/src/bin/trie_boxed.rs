// The trie of corpus/pending/lc-0208-trie-boxed.bc, mirrored: a node owning an array of its 26
// children, `Vec<Option<Trie>>` as `array (1 + X)`, allocated whole when the node is made; the
// input read into a buffer of 4096 bytes; each line's tokens as strings of capacity 8 in a vector
// of capacity 8, the cases in a vector of capacity 8, as the program's `buf`s grow (doubling).
use std::io::{Read, Write};
rs::counting!();
struct Trie { end: bool, kids: Vec<Option<Trie>> }
fn fresh() -> Trie { Trie { end: false, kids: (0..26).map(|_| None).collect() } }
fn words(l: &[u8]) -> Vec<Vec<u8>> {
    let mut out = Vec::with_capacity(8);
    let mut w = Vec::with_capacity(8);
    for &b in l {
        if b == b' ' { if !w.is_empty() { out.push(w); w = Vec::with_capacity(8) } }
        else { w.push(b) }
    }
    if !w.is_empty() { out.push(w) }
    out
}
fn insert(t: &mut Trie, w: &[u8]) {
    if w.is_empty() { t.end = true; return }
    let c = (w[0] - b'a') as usize;
    if t.kids[c].is_none() { t.kids[c] = Some(fresh()) }
    insert(t.kids[c].as_mut().unwrap(), &w[1..])
}
fn walk(t: &Trie, w: &[u8]) -> (bool, bool) {
    if w.is_empty() { return (true, t.end) }
    match &t.kids[(w[0] - b'a') as usize] { Some(c) => walk(c, &w[1..]), None => (false, false) }
}
fn main() {
    let mut o = std::io::stdout().lock();
    o.flush().unwrap();
    let mut inp = std::io::stdin().lock();
    let s0 = rs::snap();
    let mut s = Vec::with_capacity(4096);
    inp.read_to_end(&mut s).unwrap();
    let mut cs: Vec<Vec<Vec<u8>>> = Vec::with_capacity(8);
    for l in s.split(|&b| b == b'\n') { if !l.is_empty() { cs.push(words(l)) } }
    for ws in &cs {
        let mut t = fresh();
        let mut first = true;
        for w in ws {
            let op = w[0];
            if op == b'+' { insert(&mut t, &w[1..]) } else {
                let (stays, end) = walk(&t, &w[1..]);
                let yes = if op == b'?' { stays && end } else { stays };
                if first { first = false } else { o.write_all(b" ").unwrap() }
                o.write_all(if yes { b"1" } else { b"0" }).unwrap();
            }
        }
        o.write_all(b"\n").unwrap();
    }
    let n = cs.len();
    drop(cs);
    rs::report(s0);
    writeln!(o, "{}", n).unwrap();
}

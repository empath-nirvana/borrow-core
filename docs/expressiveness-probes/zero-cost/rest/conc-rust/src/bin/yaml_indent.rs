// ns/yaml-indent.bc: YAML block mappings (one-letter keys, one-digit scalars) into a JSON-shaped
// tree by a stack of indentation frames; printed as JSON.
use conc_rust::*;
use std::io::{BufRead, Write};
#[global_allocator] static A: Counting = Counting;
enum J { Scalar(i32), Map(Vec<(u8, J)>) }
fn show(j: &J, out: &mut impl Write) {
    match j {
        J::Scalar(v) => write!(out, "{v}").unwrap(),
        J::Map(es) => { out.write_all(b"{").unwrap(); for (i, (k, v)) in es.iter().enumerate() { if i > 0 { out.write_all(b",").unwrap() } write!(out, "\"{}\":", *k as char).unwrap(); show(v, out) } out.write_all(b"}").unwrap() }
    }
}
fn main() {
    let stdin = std::io::stdin();
    let mut inp = stdin.lock();
    let _ = inp.fill_buf();
    let a0 = snapshot();
    // (indent, key, entries); the root at indent -1.
    let mut stack: Vec<(i32, u8, Vec<(u8, J)>)> = vec![(-1, 0, Vec::new())];
    let pop = |stack: &mut Vec<(i32, u8, Vec<(u8, J)>)>| { let (_, k, es) = stack.pop().unwrap(); stack.last_mut().unwrap().2.push((k, J::Map(es))) };
    let mut line = Vec::new();
    while { line.clear(); inp.read_until(b'\n', &mut line).unwrap() > 0 } {
        let ind = line.iter().take_while(|&&b| b == b' ').count() as i32;
        let rest = &line[ind as usize..];
        let k = rest[0];
        let v = rest[1..].iter().find(|b| b.is_ascii_digit()).map(|b| (b - b'0') as i32);
        while stack.last().unwrap().0 >= ind { pop(&mut stack) }
        match v { Some(v) => stack.last_mut().unwrap().2.push((k, J::Scalar(v))), None => stack.push((ind, k, Vec::new())) }
    }
    while stack.len() > 1 { pop(&mut stack) }
    let root = J::Map(stack.pop().unwrap().2);
    report("yaml_indent (before printing)", a0);
    let out = std::io::stdout();
    let mut out = out.lock();
    show(&root, &mut out);
    out.write_all(b"\n").unwrap();
    drop(out);
    report("yaml_indent", a0);
}

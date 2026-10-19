#[path = "../counting.rs"] mod counting;
// T06: word frequencies in first-seen order, keyed by slices of the text.
use std::collections::HashMap;
use std::fmt::Write;
fn freq(text: &str) -> String {
    let mut freq: HashMap<&str, i32> = HashMap::with_capacity(16);
    let mut order: Vec<&str> = Vec::with_capacity(8);
    for w in text.split(' ').filter(|w| !w.is_empty()) {
        let c = freq.entry(w).or_insert(0);
        if *c == 0 { order.push(w); }
        *c += 1;
    }
    let mut out = String::with_capacity(32);
    for (i, w) in order.iter().enumerate() {
        if i > 0 { out.push(','); }
        write!(out, "{}:{}", w, freq[w]).unwrap();
    }
    out
}
fn main() {
    let c0 = counting::now();
    let out = freq(std::hint::black_box("the cat and the hat and the bat"));
    let used = counting::now() - c0;
    println!("{out}");
    eprintln!("body allocs {used}");
}

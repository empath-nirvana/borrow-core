// ds/hashmap.bc: std HashMap<String, i32> and HashMap<i32, String>, with_capacity(4).
#[path = "../count.rs"] mod count;
use std::collections::HashMap;
fn main() {
    count::warm();
    let s0 = count::snap();
    let mut m: HashMap<String, i32> = HashMap::with_capacity(4);
    m.insert("apple".to_string(), 1);
    m.insert("pear".to_string(), 2);
    m.insert("plum".to_string(), 3);
    let o = m.insert("pear".to_string(), 20).unwrap_or(-1);
    eprint!("{o} ");
    let fv = m.get("pear").copied().unwrap_or(-1);   // lookup by &str: no key allocated
    eprint!("{fv} ");
    let rv = m.remove("apple").unwrap_or(-1);
    eprint!("{rv} ");
    eprintln!("{}", m.len());
    let mut w: HashMap<i32, String> = HashMap::with_capacity(4);
    w.insert(7, "seven".to_string());
    w.insert(3, "three".to_string());
    for (k, v) in &w { eprint!("{k}={} ", &v[..]) }
    eprintln!();
    drop(m); drop(w);
    count::report("hashmap (std HashMap)", s0);
}

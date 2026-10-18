use std::collections::HashMap;
use std::io::Read;

/// The words of standard input counted in a hash map keyed by slices of the input: the number of
/// words and of distinct words, and the highest count.
fn main() {
    let mut s = String::new();
    std::io::stdin().read_to_string(&mut s).unwrap();
    let mut m: HashMap<&str, i32> = HashMap::with_capacity(1024);
    let mut words = 0;
    let mut most = 0;
    for w in s.split_ascii_whitespace() {
        let c = m.entry(w).or_insert(0);
        *c += 1;
        most = most.max(*c);
        words += 1;
    }
    println!("{} {} {}", words, m.len(), most);
}

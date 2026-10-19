#[path = "../counting.rs"] mod counting;
use std::io::Read;

/// The numbers of standard input, one per line: their count and their sum.
fn real_main() {
    let mut s = String::new();
    std::io::stdin().read_to_string(&mut s).unwrap();
    let (k, acc) = s
        .split_ascii_whitespace()
        .map(|w| w.parse::<i64>().unwrap())
        .fold((0, 0i64), |(k, acc), x| (k + 1, acc + x));
    println!("{k} {acc}");
}

fn main() { real_main(); counting::report(); }

#[path = "../counting.rs"] mod counting;
// Startup cost only: read standard input whole and print one line.
use std::io::Read;
fn real_main() { let mut s = String::new(); std::io::stdin().read_to_string(&mut s).unwrap(); println!("{}", s.len()); }
fn main() { real_main(); counting::report(); }

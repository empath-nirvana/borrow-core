#[path = "../counting.rs"] mod counting;
// Startup cost only: collect the arguments and print one line.
fn real_main() { let args: Vec<String> = std::env::args().collect(); println!("{}", args.len()); }
fn main() { real_main(); counting::report(); }

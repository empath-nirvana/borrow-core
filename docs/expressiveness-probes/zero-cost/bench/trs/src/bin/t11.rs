#[path = "../counting.rs"] mod counting;
// T11: a configuration updated field by field from options, then frozen.
#[derive(Debug)]
struct Cfg { width: i32, height: i32, title: String, verbose: bool }
fn main() {
    let c0 = counting::now();
    let mut cfg = Cfg { width: 40, height: 25, title: String::from("untitled"), verbose: false };
    let mut unknown = 0;
    for a in std::hint::black_box("--width=80 --title=demo -v --frob").split_whitespace() {
        if let Some(v) = a.strip_prefix("--width=") { cfg.width = v.parse().unwrap_or(cfg.width) }
        else if let Some(v) = a.strip_prefix("--title=") { cfg.title = v.to_string() }
        else if a == "-v" { cfg.verbose = true }
        else { unknown += 1 }
    }
    if cfg.verbose { cfg.height *= 2; }
    let cfg = cfg;
    let used = counting::now() - c0;
    println!("{cfg:?} {} {unknown}", cfg.width * cfg.height);
    eprintln!("body allocs {used}");
}

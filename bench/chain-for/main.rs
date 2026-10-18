fn arg(args: &[String], k: usize, d: i32) -> i32 {
    args.get(k).and_then(|s| s.parse().ok()).unwrap_or(d)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n = arg(&args, 1, 1000) as i64;
    let s: i64 = (0..n).map(|x| x * 3 + 1).filter(|x| x % 7 != 0).sum();
    println!("{s}");
}

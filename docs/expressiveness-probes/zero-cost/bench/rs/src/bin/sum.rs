#[path = "../counting.rs"] mod counting;
fn arg(args: &[String], k: usize, d: i32) -> i32 {
    args.get(k).and_then(|s| s.parse().ok()).unwrap_or(d)
}

fn value(i: i32) -> i64 {
    (i.wrapping_mul(7919) % 1000) as i64
}

fn real_main() {
    let args: Vec<String> = std::env::args().collect();
    let n = arg(&args, 1, 1000);
    let reps = arg(&args, 2, 1);
    let a: Vec<i64> = (0..n).map(value).collect();
    let mut acc: i64 = 0;
    for _ in 0..reps {
        acc = acc.wrapping_add(a.iter().sum::<i64>());
    }
    println!("{acc}");
}

fn main() { real_main(); counting::report(); }

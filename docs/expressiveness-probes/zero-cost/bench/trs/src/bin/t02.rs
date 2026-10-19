#[path = "../counting.rs"] mod counting;
// T02: early exit with a value from a `for`, and a `while` with a bare `break`.
fn first_over(xs: &[i32], limit: i32) -> i32 {
    let mut run = 0;
    for (i, &x) in xs.iter().enumerate() {
        run += x;
        if run > limit { return i as i32; }
    }
    -1
}
fn main() {
    let c0 = counting::now();
    let xs = std::hint::black_box([4, 1, -3, 9, 2, 8]);
    let mut i = 0;
    let mut all_pos = true;
    while i < xs.len() { if xs[i] < 0 { all_pos = false; break; } i += 1; }
    let (f10, f100) = (first_over(&xs, 10), first_over(&xs, 100));
    let used = counting::now() - c0;
    println!("({f10}, ({f100}, ({all_pos}, {i})))");
    eprintln!("body allocs {used}");
}

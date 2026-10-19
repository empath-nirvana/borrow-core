#[path = "../counting.rs"] mod counting;
// T01: loop-carried accumulators over a borrowed array.
fn main() {
    let c0 = counting::now();
    let xs = std::hint::black_box([3, 8, -2, 7, 10, 5, -6, 4]);
    let (mut sq, mut odd, mut best) = (0, 0, i32::MIN);
    for &x in &xs {
        if x % 2 == 0 { sq += x * x } else { odd += 1 }
        if x > best { best = x }
    }
    let used = counting::now() - c0;
    println!("({sq}, ({odd}, {best}))");
    eprintln!("body allocs {used}");
}

#[path = "../counting.rs"] mod counting;
// T10: simultaneous updates by tuple assignment.
fn main() {
    let c0 = counting::now();
    let (mut a, mut b) = (0, 1);
    for _ in 0..std::hint::black_box(20) { (a, b) = (b, a + b); }
    let (mut x, mut y, mut z) = (1, 2, 3);
    for _ in 0..std::hint::black_box(4) { (x, y, z) = (y, z, x); }
    let (mut p, mut q) = std::hint::black_box((1071, 462));
    while q != 0 { (p, q) = (q, p % q); }
    let used = counting::now() - c0;
    println!("{a} {x} {y} {z} {p}");
    eprintln!("body allocs {used}");
}

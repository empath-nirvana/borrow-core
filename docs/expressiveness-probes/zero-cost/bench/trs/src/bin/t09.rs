#[path = "../counting.rs"] mod counting;
// T09: particles updated in place through `&mut [P]`.
struct P { x: i32, v: i32 }
fn step(ps: &mut [P]) -> i32 {
    let mut b = 0;
    for p in ps.iter_mut() {
        p.x += p.v;
        if p.x < 0 || p.x > 100 { p.v = -p.v; p.x += 2 * p.v; b += 1; }
    }
    b
}
fn main() {
    let c0 = counting::now();
    let mut world = std::hint::black_box([P { x: 10, v: 7 }, P { x: 50, v: -3 }, P { x: 99, v: 11 }]);
    let mut bounces = 0;
    for _ in 0..50 { bounces += step(&mut world); }
    let used = counting::now() - c0;
    let xs: Vec<i32> = world.iter().map(|p| p.x).collect();
    println!("{xs:?} {bounces}");
    eprintln!("body allocs {used}");
}

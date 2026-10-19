// conc/split-halves.bc: an owned array of 6 split into disjoint &mut halves, each squared in place
// by its own task (awaiting after each element), interleaved on one thread; then summed.
// Also the parallel form (std::thread::scope over split_at_mut), the reference for B12.
use conc_rust::*;
#[global_allocator] static A: Counting = Counting;
async fn square_half(v: &mut [i32]) -> i32 {
    for x in v.iter_mut() { *x *= *x; yield_now().await; }
    v.len() as i32
}
fn main() {
    let a0 = snapshot();
    let mut arr: Vec<i32> = (1..=6).collect();
    let r = {
        let (lo, hi) = arr.split_at_mut(3);
        run(vec![Box::pin(square_half(lo)) as Task<i32>, Box::pin(square_half(hi))])
    };
    let s: i32 = arr.iter().sum();
    report("split_halves (async, one thread)", a0);
    println!("{r:?} {s}");
    let a0 = snapshot();
    let mut arr: Vec<i32> = (1..=6).collect();
    let (lo, hi) = arr.split_at_mut(3);
    let (n1, n2) = std::thread::scope(|sc| {
        let h = sc.spawn(|| { for x in lo.iter_mut() { *x *= *x } 3 });
        for x in hi.iter_mut() { *x *= *x }
        (h.join().unwrap(), 3)
    });
    let s: i32 = arr.iter().sum();
        let a1 = snapshot();
    println!("{n1} {n2} {s}");
    eprintln!("split_halves (thread::scope, 1 spawned thread): allocs {} reallocs {}", a1.0 - a0.0, a1.1 - a0.1);
}

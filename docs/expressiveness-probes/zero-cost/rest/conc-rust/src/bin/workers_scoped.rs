// corpus/async-workers-scoped.bc: two workers share &Config across their awaits.
use conc_rust::*;
#[global_allocator] static A: Counting = Counting;
struct Config { scale: i32, offset: i32 }
async fn worker(cfg: &Config, first: i32, jobs: i32) -> i32 {
    let (scale, offset) = (cfg.scale, cfg.offset);
    let mut sum = 0;
    for i in 0..jobs { sum += (first + i) * scale + offset; yield_now().await }
    sum
}
fn main() {
    let a0 = snapshot();
    let cfg = Config { scale: 10, offset: 1 };
    let totals = run(vec![Box::pin(worker(&cfg, 1, 3)) as Task<i32>, Box::pin(worker(&cfg, 4, 2))]);
    let sum: i32 = totals.iter().sum();
    report("workers_scoped", a0);
    println!("{totals:?} {sum}");
}

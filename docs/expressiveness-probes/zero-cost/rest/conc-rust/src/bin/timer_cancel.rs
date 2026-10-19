// ns/timer-cancel.bc: a victim owns a cell and polls the clock until its deadline, awaiting
// between polls; a killer task owns the victim, awaits twice and cancels it (drops it). The
// victim is spawned (run to its first await) but only the killer is queued, as in ours.
use conc_rust::*;
use std::task::Context;
use std::time::{Duration, Instant};
#[global_allocator] static A: Counting = Counting;
async fn victim(ms: u64) -> i32 {
    let cell = Box::new(7);              // ours: `alloc(7)`, to show the cancel frees it
    let t0 = Instant::now();
    let mut fired = 0;
    for _ in 0..1_000_000 { if t0.elapsed() >= Duration::from_millis(ms) { fired = 1; break } yield_now().await }
    *cell + fired
}
async fn killer(t: Task<'_, i32>) -> i32 { yield_now().await; yield_now().await; drop(t); 2 }
fn main() {
    let a0 = snapshot();
    let w = noop_waker();
    let mut cx = Context::from_waker(&w);
    let mut v: Task<i32> = Box::pin(victim(10_000));
    POLLS.with(|p| p.set(p.get() + 1));
    let _ = v.as_mut().poll(&mut cx);
    let r = run(vec![Box::pin(killer(v)) as Task<i32>]);
    report("timer_cancel", a0);
    println!("{r:?}");
}

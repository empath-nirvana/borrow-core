// corpus/async-timers.bc: an event loop with tick timers and deadlines. Three tasks (fetch,
// latency 4; heartbeat, 3 beats; slow job, deadline 5, sleeping 10); a task past its deadline is
// cancelled by dropping its future.
use conc_rust::*;
use std::cell::Cell;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
#[global_allocator] static A: Counting = Counting;
thread_local! { static NOW: Cell<i32> = const { Cell::new(0) }; static WAKE: Cell<i32> = const { Cell::new(0) }; }
struct Sleep { ticks: i32, until: Option<i32> }
impl Future for Sleep {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<()> {
        let now = NOW.with(|n| n.get());
        let t = self.ticks; let until = *self.until.get_or_insert(now + t);
        if now >= until { Poll::Ready(()) } else { WAKE.with(|w| w.set(until)); Poll::Pending }
    }
}
fn sleep(ticks: i32) -> Sleep { Sleep { ticks, until: None } }
async fn fetch(id: i32, latency: i32) -> i32 { sleep(latency).await; id * 100 }
async fn heartbeat(beats: i32) -> i32 { let mut n = 0; for _ in 0..beats { sleep(1).await; n += 1 } n * 2 }
async fn slow_job() -> i32 { sleep(10).await; 7 }
fn main() {
    let a0 = snapshot();
    let w = noop_waker();
    let mut cx = Context::from_waker(&w);
    // (id, deadline, wakes at, task)
    let mut pending: Vec<(i32, i32, i32, Task<i32>)> = Vec::with_capacity(3);
    let mut finished: Vec<(i32, Option<i32>, i32)> = Vec::with_capacity(3);
    let tasks: [(i32, i32, Task<i32>); 3] = [(1, 50, Box::pin(fetch(1, 4))), (2, 50, Box::pin(heartbeat(3))), (3, 5, Box::pin(slow_job()))];
    for (id, dl, mut t) in tasks {
        POLLS.with(|p| p.set(p.get() + 1));
        if let Poll::Pending = t.as_mut().poll(&mut cx) { pending.push((id, dl, WAKE.with(|w| w.get()), t)) }
    }
    for now in 1..12 {
        NOW.with(|n| n.set(now));
        let mut i = 0;
        while i < pending.len() {
            let (id, dl, at, _) = pending[i];
            if now >= dl { pending.remove(i); finished.push((id, None, now)); continue }
            if at <= now {
                POLLS.with(|p| p.set(p.get() + 1));
                match pending[i].3.as_mut().poll(&mut cx) {
                    Poll::Ready(v) => { pending.remove(i); finished.push((id, Some(v), now)); continue }
                    Poll::Pending => pending[i].2 = WAKE.with(|w| w.get()),
                }
            }
            i += 1;
        }
    }
    report("timers", a0);
    println!("{finished:?}");
}

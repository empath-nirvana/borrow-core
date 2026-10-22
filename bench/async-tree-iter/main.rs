// Each task is one `async fn` that walks the tree in order with an explicit stack of pending
// ranges (as bench/gen-tree's Rust side does) and yields once per node. No recursion, so no
// boxing per call: one boxed future per task, and a wake resumes it directly.
use std::collections::VecDeque;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};
fn arg(args: &[String], k: usize, d: i32) -> i32 { args.get(k).and_then(|s| s.parse().ok()).unwrap_or(d) }
fn value(k: i32, r: i32) -> i32 { k.wrapping_mul(7919).wrapping_add(r) % 1000 }
struct YieldNow(bool);
impl Future for YieldNow {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        if self.0 { Poll::Ready(()) } else { self.0 = true; cx.waker().wake_by_ref(); Poll::Pending }
    }
}
async fn tsum(lo: i32, hi: i32, r: i32) -> i64 {
    let mut stack: Vec<(i32, i32)> = Vec::new();
    let descend = |stack: &mut Vec<(i32, i32)>, lo: i32, mut hi: i32| {
        while lo < hi { let m = lo + (hi - lo) / 2; stack.push((m, hi)); hi = m; }
    };
    descend(&mut stack, lo, hi);
    let mut s = 0i64;
    while let Some((m, hi)) = stack.pop() {
        YieldNow(false).await;
        s += value(m, r) as i64;
        descend(&mut stack, m + 1, hi);
    }
    s
}
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n = arg(&args, 1, 1000);
    let tasks = arg(&args, 2, 1);
    let mut queue: VecDeque<(usize, Pin<Box<dyn Future<Output = i64>>>)> =
        (0..tasks).map(|r| (r as usize, Box::pin(tsum(0, n, r)) as Pin<Box<dyn Future<Output = i64>>>)).collect();
    let mut results = vec![0i64; tasks.max(0) as usize];
    let mut cx = Context::from_waker(Waker::noop());
    while let Some((i, mut t)) = queue.pop_front() {
        match t.as_mut().poll(&mut cx) {
            Poll::Ready(v) => results[i] = v,
            Poll::Pending => queue.push_back((i, t)),
        }
    }
    for v in results { println!("{v}"); }
}

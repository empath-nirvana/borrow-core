// Recursive async tasks: `tasks` tasks, each a recursive `async fn` over the implicit balanced
// search tree of the keys 0..n that yields once at every node, polled round robin by a minimal
// single-threaded executor (std only). A recursive `async fn` needs its recursive calls boxed:
// `Box::pin` per call.
use std::collections::VecDeque;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};

fn arg(args: &[String], k: usize, d: i32) -> i32 {
    args.get(k).and_then(|s| s.parse().ok()).unwrap_or(d)
}

fn value(k: i32, r: i32) -> i32 {
    k.wrapping_mul(7919).wrapping_add(r) % 1000
}

// Pending once, then ready: one turn of the scheduler.
struct YieldNow(bool);

impl Future for YieldNow {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<()> {
        if self.0 {
            Poll::Ready(())
        } else {
            self.0 = true;
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}

fn tsum(lo: i32, hi: i32, r: i32) -> Pin<Box<dyn Future<Output = i64>>> {
    Box::pin(async move {
        if lo < hi {
            let m = lo + (hi - lo) / 2;
            let a = tsum(lo, m, r).await;
            YieldNow(false).await;
            let b = tsum(m + 1, hi, r).await;
            a + value(m, r) as i64 + b
        } else {
            0
        }
    })
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n = arg(&args, 1, 1000);
    let tasks = arg(&args, 2, 1);
    let mut queue: VecDeque<(usize, Pin<Box<dyn Future<Output = i64>>>)> =
        (0..tasks).map(|r| (r as usize, tsum(0, n, r))).collect();
    let mut results = vec![0i64; tasks.max(0) as usize];
    let mut cx = Context::from_waker(Waker::noop());
    while let Some((i, mut t)) = queue.pop_front() {
        match t.as_mut().poll(&mut cx) {
            Poll::Ready(v) => results[i] = v,
            Poll::Pending => queue.push_back((i, t)),
        }
    }
    for v in results {
        println!("{v}");
    }
}

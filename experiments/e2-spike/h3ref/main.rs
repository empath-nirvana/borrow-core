// H3's Rust side: `tasks` tasks, each OWNING a balanced search tree of the keys `0 .. n` (Box
// nodes), walked in order with an explicit stack of `&Node` (a borrow of the task's own tree held
// across each await: the future is self-referential, pinned in its Box) and yielding once per
// node. The scheduler is `bench/async-tree-iter/main.rs`'s. The value printed is the sum of the
// tasks' sums. `mode`: 0 the borrowing walk; 1 a consuming walk (each node taken apart by value,
// as `src-owned-tree.bc`); 2 the tree built and dropped with no walk (the build's cost).
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
struct Node { l: Option<Box<Node>>, k: i32, r: Option<Box<Node>> }
fn build(lo: i32, hi: i32) -> Option<Box<Node>> {
    if lo < hi { let m = lo + (hi - lo) / 2; Some(Box::new(Node { l: build(lo, m), k: m, r: build(m + 1, hi) })) } else { None }
}
async fn tsum(n: i32, r: i32, mode: i32) -> i64 {
    let tree = build(0, n);
    let mut s = 0i64;
    if mode == 0 {
        let mut stack: Vec<&Node> = Vec::new();
        let mut cur = tree.as_deref();
        while let Some(c) = cur { stack.push(c); cur = c.l.as_deref(); }
        while let Some(c) = stack.pop() {
            YieldNow(false).await;
            s += value(c.k, r) as i64;
            let mut cur = c.r.as_deref();
            while let Some(x) = cur { stack.push(x); cur = x.l.as_deref(); }
        }
    } else if mode == 1 {
        let mut stack: Vec<(Option<Box<Node>>, i32)> = Vec::new();
        let mut cur = tree;
        while let Some(c) = cur { let Node { l, k, r: rr } = *c; stack.push((rr, k)); cur = l; }
        while let Some((rr, k)) = stack.pop() {
            YieldNow(false).await;
            s += value(k, r) as i64;
            let mut cur = rr;
            while let Some(c) = cur { let Node { l, k, r: rr } = *c; stack.push((rr, k)); cur = l; }
        }
    } else {
        YieldNow(false).await;
        drop(tree);
    }
    s
}
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n = arg(&args, 1, 1000);
    let tasks = arg(&args, 2, 1);
    let mode = arg(&args, 3, 0);
    let mut queue: VecDeque<(usize, Pin<Box<dyn Future<Output = i64>>>)> =
        (0..tasks).map(|r| (r as usize, Box::pin(tsum(n, r, mode)) as Pin<Box<dyn Future<Output = i64>>>)).collect();
    let mut results = vec![0i64; tasks.max(0) as usize];
    let mut cx = Context::from_waker(Waker::noop());
    while let Some((i, mut t)) = queue.pop_front() {
        match t.as_mut().poll(&mut cx) {
            Poll::Ready(v) => results[i] = v,
            Poll::Pending => queue.push_back((i, t)),
        }
    }
    println!("{}", results.iter().sum::<i64>());
}

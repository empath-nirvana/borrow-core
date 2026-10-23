// B1's Rust side: `main` OWNS `tasks` balanced search trees of the keys `0 .. n` (Box nodes) and
// lends one to each task, `&'a Node`; each task walks its tree in order with an explicit stack of
// `&Node` held across each await (the futures are not `'static`: they borrow `main`'s trees,
// Rust's scoped spawn). The scheduler is `h3/main.rs`'s round robin, at the trees' lifetime. The
// value printed is the sum of the tasks' sums, as `h3/main.rs`'s. `mode`: 0 the borrowing walk;
// 2 the trees built and dropped with no walk (the build's cost); 3 the borrowing walk over an
// arena (`c1-arena-held.bc`'s layout: one `Vec<ANode>` of all the trees, children by index, built
// from a work list), still with a stack of `&ANode` held across each await; 4 the arena's build
// alone; 5 ONE tree, owned by `main` and walked by every task through its own `&Node` stack
// (`c2s-mu-path-shared.bc`'s workload); 6 that one tree's build alone.
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
struct ANode { k: i32, l: i32, r: i32 }
fn mid(lo: i32, hi: i32) -> i32 { lo + (hi - lo) / 2 }
fn build_arena(n: i32, tasks: i32) -> Vec<ANode> {
    let mut a: Vec<ANode> = (0..(n as i64 * tasks as i64)).map(|_| ANode { k: 0, l: -1, r: -1 }).collect();
    let mut ws: Vec<(i32, i32, i32)> = (0..tasks).map(|t| (0, n, t * n)).collect();
    while let Some((lo, hi, base)) = ws.pop() {
        if lo < hi {
            let m = mid(lo, hi);
            let l = if lo < m { base + mid(lo, m) } else { -1 };
            let r = if m + 1 < hi { base + mid(m + 1, hi) } else { -1 };
            a[(base + m) as usize] = ANode { k: m, l, r };
            ws.push((m + 1, hi, base));
            ws.push((lo, m, base));
        }
    }
    a
}
async fn awalk<'a>(a: &'a [ANode], root: i32, r: i32) -> i64 {
    let mut s = 0i64;
    let mut stack: Vec<&'a ANode> = Vec::new();
    let mut i = root;
    while i >= 0 { let c = &a[i as usize]; stack.push(c); i = c.l; }
    while let Some(c) = stack.pop() {
        YieldNow(false).await;
        s += value(c.k, r) as i64;
        let mut i = c.r;
        while i >= 0 { let x = &a[i as usize]; stack.push(x); i = x.l; }
    }
    s
}
async fn twalk<'a>(tree: Option<&'a Node>, r: i32) -> i64 {
    let mut s = 0i64;
    let mut stack: Vec<&'a Node> = Vec::new();
    let mut cur = tree;
    while let Some(c) = cur { stack.push(c); cur = c.l.as_deref(); }
    while let Some(c) = stack.pop() {
        YieldNow(false).await;
        s += value(c.k, r) as i64;
        let mut cur = c.r.as_deref();
        while let Some(x) = cur { stack.push(x); cur = x.l.as_deref(); }
    }
    s
}
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n = arg(&args, 1, 1000);
    let tasks = arg(&args, 2, 1);
    let mode = arg(&args, 3, 0);
    let mut results = vec![0i64; tasks.max(0) as usize];
    if mode == 3 || mode == 4 {
        let arena = build_arena(n, tasks);
        if mode == 3 {
            let a: &[ANode] = &arena;
            let mut queue: VecDeque<(usize, Pin<Box<dyn Future<Output = i64> + '_>>)> = (0..tasks)
                .map(|t| (t as usize, Box::pin(awalk(a, t * n + mid(0, n), t)) as Pin<Box<dyn Future<Output = i64> + '_>>))
                .collect();
            let mut cx = Context::from_waker(Waker::noop());
            while let Some((i, mut t)) = queue.pop_front() {
                match t.as_mut().poll(&mut cx) {
                    Poll::Ready(v) => results[i] = v,
                    Poll::Pending => queue.push_back((i, t)),
                }
            }
        }
        drop(arena);
        println!("{}", results.iter().sum::<i64>());
        return;
    }
    if mode == 6 {
        let tree = build(0, n);
        drop(tree);
        println!("0");
        return;
    }
    if mode == 5 {
        let tree = build(0, n);
        let mut queue: VecDeque<(usize, Pin<Box<dyn Future<Output = i64> + '_>>)> = (0..tasks)
            .map(|r| (r as usize, Box::pin(twalk(tree.as_deref(), r)) as Pin<Box<dyn Future<Output = i64> + '_>>))
            .collect();
        let mut cx = Context::from_waker(Waker::noop());
        while let Some((i, mut t)) = queue.pop_front() {
            match t.as_mut().poll(&mut cx) {
                Poll::Ready(v) => results[i] = v,
                Poll::Pending => queue.push_back((i, t)),
            }
        }
        drop(queue);
        drop(tree);
        println!("{}", results.iter().sum::<i64>());
        return;
    }
    let trees: Vec<Option<Box<Node>>> = (0..tasks).map(|_| build(0, n)).collect();
    if mode == 0 {
        let mut queue: VecDeque<(usize, Pin<Box<dyn Future<Output = i64> + '_>>)> = trees
            .iter()
            .enumerate()
            .map(|(r, t)| (r, Box::pin(twalk(t.as_deref(), r as i32)) as Pin<Box<dyn Future<Output = i64> + '_>>))
            .collect();
        let mut cx = Context::from_waker(Waker::noop());
        while let Some((i, mut t)) = queue.pop_front() {
            match t.as_mut().poll(&mut cx) {
                Poll::Ready(v) => results[i] = v,
                Poll::Pending => queue.push_back((i, t)),
            }
        }
    }
    drop(trees);
    println!("{}", results.iter().sum::<i64>());
}

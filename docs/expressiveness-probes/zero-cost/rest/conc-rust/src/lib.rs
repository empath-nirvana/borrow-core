//! Shared pieces of the category-4 Rust references: a counting allocator, a poll counter, and a
//! minimal single-threaded executor (std only: a VecDeque of Pin<Box<dyn Future>> and a no-op
//! waker), as a performance-minded Rust programmer writes it for a handful of tasks.
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};
use std::collections::VecDeque;

pub struct Counting;
pub static ALLOCS: AtomicUsize = AtomicUsize::new(0);
pub static REALLOCS: AtomicUsize = AtomicUsize::new(0);
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 { ALLOCS.fetch_add(1, Relaxed); unsafe { System.alloc(l) } }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) { unsafe { System.dealloc(p, l) } }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 { ALLOCS.fetch_add(1, Relaxed); unsafe { System.alloc_zeroed(l) } }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 { REALLOCS.fetch_add(1, Relaxed); unsafe { System.realloc(p, l, n) } }
}
pub fn snapshot() -> (usize, usize) { (ALLOCS.load(Relaxed), REALLOCS.load(Relaxed)) }

thread_local! { pub static POLLS: Cell<usize> = const { Cell::new(0) }; }
pub fn polls() -> usize { POLLS.with(|p| p.get()) }

/// Returns Pending once, then Ready: `await()`.
pub struct YieldNow(bool);
impl Future for YieldNow {
    type Output = ();
    fn poll(mut self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<()> {
        if self.0 { Poll::Ready(()) } else { self.0 = true; Poll::Pending }
    }
}
pub fn yield_now() -> YieldNow { YieldNow(false) }

fn noop_raw() -> RawWaker {
    fn clone(_: *const ()) -> RawWaker { noop_raw() }
    fn noop(_: *const ()) {}
    static VT: RawWakerVTable = RawWakerVTable::new(clone, noop, noop, noop);
    RawWaker::new(std::ptr::null(), &VT)
}
pub fn noop_waker() -> Waker { unsafe { Waker::from_raw(noop_raw()) } }

pub type Task<'a, T> = Pin<Box<dyn Future<Output = T> + 'a>>;

/// Round robin until every task has finished; values in queue order. One `dyn` poll per resume.
pub fn run<'a, T>(tasks: Vec<Task<'a, T>>) -> Vec<T> {
    let n = tasks.len();
    let mut q: VecDeque<(usize, Task<'a, T>)> = tasks.into_iter().enumerate().collect();
    let mut out: Vec<Option<T>> = (0..n).map(|_| None).collect();
    let w = noop_waker();
    let mut cx = Context::from_waker(&w);
    while let Some((i, mut t)) = q.pop_front() {
        POLLS.with(|p| p.set(p.get() + 1));
        match t.as_mut().poll(&mut cx) {
            Poll::Ready(v) => out[i] = Some(v),
            Poll::Pending => q.push_back((i, t)),
        }
    }
    out.into_iter().map(|v| v.unwrap()).collect()
}

pub fn report(name: &str, a0: (usize, usize)) {
    let a1 = snapshot();
    eprintln!("{name}: allocs {} reallocs {} dyn-polls {}", a1.0 - a0.0, a1.1 - a0.1, polls());
}

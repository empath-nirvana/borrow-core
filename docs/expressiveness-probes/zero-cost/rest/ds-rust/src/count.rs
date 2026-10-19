// Counting allocator: alloc, alloc_zeroed and realloc each count one.
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
pub struct Counting;
pub static ALLOCS: AtomicUsize = AtomicUsize::new(0);
pub static REALLOCS: AtomicUsize = AtomicUsize::new(0);
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 { ALLOCS.fetch_add(1, Relaxed); unsafe { System.alloc(l) } }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) { unsafe { System.dealloc(p, l) } }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 { ALLOCS.fetch_add(1, Relaxed); unsafe { System.alloc_zeroed(l) } }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 { REALLOCS.fetch_add(1, Relaxed); unsafe { System.realloc(p, l, n) } }
}
#[global_allocator]
static A: Counting = Counting;
pub fn snap() -> (usize, usize) { (ALLOCS.load(Relaxed), REALLOCS.load(Relaxed)) }
pub fn report(label: &str, s0: (usize, usize)) {
    let s = snap();
    eprintln!("{label}: allocs {} reallocs {} total {}", s.0 - s0.0, s.1 - s0.1, (s.0 - s0.0) + (s.1 - s0.1));
}
/// std's first write to stderr allocates once (its thread handle); done before measuring.
pub fn warm() { eprint!(""); }

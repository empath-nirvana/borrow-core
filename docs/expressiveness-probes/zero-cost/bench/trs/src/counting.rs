// A global allocator that counts calls to alloc, alloc_zeroed and realloc, and frees.
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

pub struct Counting;
pub static ALLOCS: AtomicUsize = AtomicUsize::new(0);
pub static REALLOCS: AtomicUsize = AtomicUsize::new(0);
pub static FREES: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 { ALLOCS.fetch_add(1, Relaxed); unsafe { System.alloc(l) } }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 { ALLOCS.fetch_add(1, Relaxed); unsafe { System.alloc_zeroed(l) } }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 { REALLOCS.fetch_add(1, Relaxed); unsafe { System.realloc(p, l, n) } }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) { FREES.fetch_add(1, Relaxed); unsafe { System.dealloc(p, l) } }
}

#[global_allocator]
static A: Counting = Counting;

pub fn report() {
    let a = ALLOCS.load(Relaxed);
    let r = REALLOCS.load(Relaxed);
    eprintln!("rust allocs {} (alloc {} + realloc {}) frees {}", a + r, a, r, FREES.load(Relaxed));
}

/// Allocations (alloc + realloc) so far.
pub fn now() -> usize { ALLOCS.load(Relaxed) + REALLOCS.load(Relaxed) }

//! Counting allocator shared by every reference binary: counts alloc + realloc calls.
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

pub struct Counting;
pub static ALLOCS: AtomicUsize = AtomicUsize::new(0);
pub static REALLOCS: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 { ALLOCS.fetch_add(1, Relaxed); unsafe { System.alloc(l) } }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 { ALLOCS.fetch_add(1, Relaxed); unsafe { System.alloc_zeroed(l) } }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) { unsafe { System.dealloc(p, l) } }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 { REALLOCS.fetch_add(1, Relaxed); unsafe { System.realloc(p, l, n) } }
}

/// Snapshot (allocs, reallocs) now.
pub fn snap() -> (usize, usize) { (ALLOCS.load(Relaxed), REALLOCS.load(Relaxed)) }

/// Print total and program-only counts (since `start`) to stderr.
pub fn report(start: (usize, usize)) {
    let (a, r) = snap();
    eprintln!("rust allocs {} (alloc {} + realloc {}); program-only {} (alloc {} + realloc {})",
        a + r, a, r, (a - start.0) + (r - start.1), a - start.0, r - start.1);
}

#[macro_export]
macro_rules! counting { () => { #[global_allocator] static GA: rs::Counting = rs::Counting; } }

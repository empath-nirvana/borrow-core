// Runs one maneatingape day (parse + part1 + part2) on stdin with a counting allocator.
use std::alloc::{GlobalAlloc, Layout, System};

use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

struct Counting;
static ALLOCS: AtomicUsize = AtomicUsize::new(0);
static REALLOCS: AtomicUsize = AtomicUsize::new(0);
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 { ALLOCS.fetch_add(1, Relaxed); unsafe { System.alloc(l) } }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) { unsafe { System.dealloc(p, l) } }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 { ALLOCS.fetch_add(1, Relaxed); unsafe { System.alloc_zeroed(l) } }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 { REALLOCS.fetch_add(1, Relaxed); unsafe { System.realloc(p, l, n) } }
}
#[global_allocator]
static A: Counting = Counting;

macro_rules! days { ($($name:literal => $y:ident :: $d:ident),*) => {
    fn run(day: &str, input: &str) -> (String, String) {
        match day {
            $($name => { let i = aoc::$y::$d::parse(input); (aoc::$y::$d::part1(&i).to_string(), aoc::$y::$d::part2(&i).to_string()) })*
            _ => panic!("unknown day"),
        }
    }
}}
days!("2020-07" => year2020::day07, "2020-08" => year2020::day08, "2021-06" => year2021::day06,
      "2021-10" => year2021::day10, "2021-15" => year2021::day15, "2022-01" => year2022::day01,
      "2022-12" => year2022::day12, "2022-21" => year2022::day21, "2023-01" => year2023::day01,
      "2023-03" => year2023::day03, "2023-07" => year2023::day07, "2024-01" => year2024::day01,
      "2024-02" => year2024::day02, "2024-11" => year2024::day11);

fn main() {
    let day = std::env::args().nth(1).unwrap();
    let path = std::env::args().nth(2).unwrap();
    let a0 = ALLOCS.load(Relaxed); let r0 = REALLOCS.load(Relaxed);
    let input = std::fs::read_to_string(&path).unwrap();


    let a1 = ALLOCS.load(Relaxed); let r1 = REALLOCS.load(Relaxed);
    let (p1, p2) = run(&day, &input);
    // The answers are formatted to Strings: subtract those two allocations.
    let a2 = ALLOCS.load(Relaxed); let r2 = REALLOCS.load(Relaxed);
    println!("{p1}\n{p2}");
    eprintln!("input allocs {} reallocs {} | solve allocs {} reallocs {} (incl. 2 to_string)", a1-a0, r1-r0, a2-a1, r2-r1);
}

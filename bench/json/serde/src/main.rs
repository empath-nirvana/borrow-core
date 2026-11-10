//! #977's Rust baseline. `json-bench parse`: standard input read whole, `from_slice::<Value>`,
//! the value `black_box`ed, and one checksum line printed: the top-level kind (0 null, 1 bool,
//! 2 number, 3 string, 4 array, 5 object) and an array's or object's length, else 0, as
//! `bench/json/parse.bc` prints it. `json-bench roundtrip`: the same parse, then `to_vec`, written
//! to standard output followed by a newline, as `bench/json/roundtrip.bc` writes it.
//!
//! With `JSON_BENCH_ALLOCS` set, the number of allocations (`alloc`, `alloc_zeroed` and `realloc`
//! calls, each one) is written to standard error as `allocs N` at the end.

use serde_json::Value;
use std::alloc::{GlobalAlloc, Layout, System};
use std::hint::black_box;
use std::io::{Read, Write};
use std::process::ExitCode;
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

struct Counting;

static ALLOCS: AtomicU64 = AtomicU64::new(0);

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        ALLOCS.fetch_add(1, Relaxed);
        unsafe { System.alloc(l) }
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        ALLOCS.fetch_add(1, Relaxed);
        unsafe { System.alloc_zeroed(l) }
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        ALLOCS.fetch_add(1, Relaxed);
        unsafe { System.realloc(p, l, n) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        unsafe { System.dealloc(p, l) }
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

fn checksum(v: &Value) -> (u32, usize) {
    match v {
        Value::Null => (0, 0),
        Value::Bool(_) => (1, 0),
        Value::Number(_) => (2, 0),
        Value::String(_) => (3, 0),
        Value::Array(a) => (4, a.len()),
        Value::Object(m) => (5, m.len()),
    }
}

fn main() -> ExitCode {
    let mode = std::env::args().nth(1).unwrap_or_default();
    if mode != "parse" && mode != "roundtrip" {
        eprintln!("usage: json-bench parse|roundtrip < input.json");
        return ExitCode::from(2);
    }
    let mut input = Vec::new();
    std::io::stdin().lock().read_to_end(&mut input).expect("read stdin");
    let code = match serde_json::from_slice::<Value>(&input) {
        Err(_) => {
            println!("error");
            ExitCode::from(1)
        }
        Ok(v) => {
            let mut out = std::io::stdout().lock();
            if mode == "parse" {
                let v = black_box(v);
                let (k, n) = checksum(&v);
                writeln!(out, "{k} {n}").expect("write");
            } else {
                let mut bytes = serde_json::to_vec(&v).expect("serialise");
                bytes.push(b'\n');
                out.write_all(&bytes).expect("write");
            }
            out.flush().expect("flush");
            ExitCode::SUCCESS
        }
    };
    if std::env::var_os("JSON_BENCH_ALLOCS").is_some() {
        eprintln!("allocs {}", ALLOCS.load(Relaxed));
    }
    code
}

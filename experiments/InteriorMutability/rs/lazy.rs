// Lazy configuration: `LazyLock` computes the configuration on first use, from any function,
// with no parameter. `INITS` counts how many times it was computed. Prints (15, 36, 1): two
// functions that read the configuration, and one initialization.
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::LazyLock;

struct Config {
    width: i32,
    scale: i32,
}

static INITS: AtomicU32 = AtomicU32::new(0);

static CONFIG: LazyLock<Config> = LazyLock::new(|| {
    INITS.fetch_add(1, Ordering::Relaxed);
    Config { width: 12, scale: 3 }
});

fn padded(n: i32) -> i32 {
    n + CONFIG.width
}

fn area() -> i32 {
    CONFIG.width * CONFIG.scale
}

fn main() {
    let a = padded(3);
    let b = area();
    println!("({}, {}, {})", a, b, INITS.load(Ordering::Relaxed));
}

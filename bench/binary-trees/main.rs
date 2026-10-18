// Binary trees (the Benchmarks Game's): complete binary trees built bottom-up and counted,
// many short-lived ones at each depth from 4 to `n` in steps of 2, beside one long-lived tree.
// A node is one `Box`.

struct Node {
    left: Option<Box<Node>>,
    right: Option<Box<Node>>,
}

fn make(d: i32) -> Box<Node> {
    if d == 0 {
        Box::new(Node { left: None, right: None })
    } else {
        Box::new(Node { left: Some(make(d - 1)), right: Some(make(d - 1)) })
    }
}

impl Node {
    fn check(&self) -> i32 {
        1 + self.left.as_ref().map_or(0, |l| l.check()) + self.right.as_ref().map_or(0, |r| r.check())
    }
}

fn main() {
    let n: i32 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(10);
    let min_depth = 4;
    let max_depth = if min_depth + 2 > n { min_depth + 2 } else { n };
    println!("stretch tree of depth {}\t check: {}", max_depth + 1, make(max_depth + 1).check());
    let long_lived = make(max_depth);
    for d in (min_depth..=max_depth).step_by(2) {
        let iterations = 1 << (max_depth - d + min_depth);
        let mut c = 0;
        for _ in 0..iterations {
            c += make(d).check();
        }
        println!("{iterations}\t trees of depth {d}\t check: {c}");
    }
    println!("long lived tree of depth {}\t check: {}", max_depth, long_lived.check());
}

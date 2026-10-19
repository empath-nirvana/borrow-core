#[path = "../counting.rs"] mod counting;
// T03: a cursor over a borrowed byte string; numbers pushed into a Vec.
fn parse(s: &[u8]) -> (Vec<i32>, i32) {
    let mut pos = 0;
    let mut vals = Vec::with_capacity(4);
    let mut errs = 0;
    while pos < s.len() {
        while pos < s.len() && s[pos] == b' ' { pos += 1; }
        let neg = pos < s.len() && s[pos] == b'-';
        if neg { pos += 1; }
        let start = pos;
        let mut n = 0;
        while pos < s.len() && s[pos].is_ascii_digit() { n = n * 10 + (s[pos] - b'0') as i32; pos += 1; }
        if pos == start { errs += 1 } else { vals.push(if neg { -n } else { n }) }
        while pos < s.len() && s[pos] != b',' { pos += 1; }
        pos += 1;
    }
    (vals, errs)
}
fn main() {
    let c0 = counting::now();
    let (vals, errs) = parse(std::hint::black_box(b"12,-3, 40,x,7"));
    let used = counting::now() - c0;
    println!("{vals:?} {errs}");
    eprintln!("body allocs {used}");
}

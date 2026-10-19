#[path = "../counting.rs"] mod counting;
// T07: a turnstile over the bytes of a literal.
#[derive(Debug, Clone, Copy)]
enum St { Locked, Open }
fn main() {
    let c0 = counting::now();
    let (mut st, mut passed, mut rejected, mut wasted) = (St::Locked, 0, 0, 0);
    for &e in std::hint::black_box(b"cpppccpcp") {
        st = match (st, e) {
            (St::Locked, b'c') => St::Open,
            (St::Locked, _) => { rejected += 1; St::Locked }
            (St::Open, b'p') => { passed += 1; St::Locked }
            (St::Open, _) => { wasted += 1; St::Open }
        };
    }
    let used = counting::now() - c0;
    println!("{st:?} {passed} {rejected} {wasted}");
    eprintln!("body allocs {used}");
}

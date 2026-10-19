#[path = "../counting.rs"] mod counting;
// T04: insertion sort through `&mut [i32]`, then reversing a copy in place.
fn insertion_sort(v: &mut [i32]) -> i32 {
    let mut swaps = 0;
    for i in 1..v.len() {
        let mut j = i;
        while j > 0 && v[j - 1] > v[j] { v.swap(j - 1, j); swaps += 1; j -= 1; }
    }
    swaps
}
fn main() {
    let c0 = counting::now();
    let mut a = std::hint::black_box([5, 2, 9, 1, 5, 6]);
    let swaps = insertion_sort(&mut a);
    let mut b = a;
    let (mut lo, mut hi) = (0, b.len() - 1);
    while lo < hi { b.swap(lo, hi); lo += 1; hi -= 1; }
    let used = counting::now() - c0;
    println!("{a:?} {b:?} {swaps}");
    eprintln!("body allocs {used}");
}

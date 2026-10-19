#[path = "../counting.rs"] mod counting;
fn arg(args: &[String], k: usize, d: i32) -> i32 {
    args.get(k).and_then(|s| s.parse().ok()).unwrap_or(d)
}

/// Element `i` of the input: bits 16…30 of an LCG step, centred on 0.
fn data(i: i32) -> i32 {
    let x = (i.wrapping_mul(1103515245).wrapping_add(12345)) & 2147483647;
    ((x as u32) >> 16) as i32 - 16384
}

/// Lomuto's partition of `v` around its middle element, moved to the end first: the elements
/// below it go to the front, and it goes to the first slot after them, which is returned.
fn partition(v: &mut [i32]) -> usize {
    let hi = v.len() - 1;
    v.swap(hi / 2, hi);
    let p = v[hi];
    let mut i = 0;
    for j in 0..hi {
        if v[j] < p {
            v.swap(i, j);
            i += 1;
        }
    }
    v.swap(i, hi);
    i
}

fn quicksort(v: &mut [i32]) {
    if v.len() > 1 {
        let p = partition(v);
        let (left, right) = v.split_at_mut(p);
        quicksort(left);
        quicksort(&mut right[1..]);
    }
}

fn real_main() {
    let args: Vec<String> = std::env::args().collect();
    let n = arg(&args, 1, 2000);
    let reps = arg(&args, 2, 1);
    let mut bad = 0;
    let mut check = 0i32;
    for _ in 0..reps {
        let mut a: Vec<i32> = (0..n).map(data).collect();
        quicksort(&mut a);
        bad += a.windows(2).filter(|w| w[1] < w[0]).count();
        check = check.wrapping_add(a[a.len() / 2]);
    }
    println!("{bad} {check}");
}

fn main() { real_main(); counting::report(); }

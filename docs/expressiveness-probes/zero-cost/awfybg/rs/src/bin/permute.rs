// AWFY Permute, as awfy/permute_natural.bc: permutations of a 6-element array by swaps; 8660.
rs::counting!();
fn permute(v: &mut [i32], n: usize, count: &mut i32) {
    *count += 1;
    if n != 0 {
        let n1 = n - 1;
        permute(v, n1, count);
        for i in (0..n).rev() { v.swap(n1, i); permute(v, n1, count); v.swap(n1, i) }
    }
}
fn main() {
    let s0 = rs::snap();
    let mut v = vec![0i32; 6];
    let mut c = 0;
    permute(&mut v, 6, &mut c);
    rs::report(s0);
    println!("{}", c);
}

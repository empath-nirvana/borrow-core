// conc/pipeline-gen.bc: 1..=6 |> square (counting) |> keep even; summed.
use conc_rust::*;
#[global_allocator] static A: Counting = Counting;
fn main() {
    let a0 = snapshot();
    let n = std::hint::black_box(6);
    let mut seen = 0;
    let s: i32 = (1..=n).map(|x| { seen += 1; x * x + seen * 0 }).filter(|x| x & 1 == 0).sum();
    report("pipeline_gen", a0);
    println!("{s}");
}

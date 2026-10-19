// k-nucleotide, as bg/knuc.bc: sequence THREE of the FASTA on stdin, upper-cased; 1- and 2-mer
// frequencies (most frequent first, then by key) and the counts of five k-mers. Each count is a
// HashMap keyed by slices of the sequence (&[u8]), as the probe's maps keyed by views.
use std::collections::HashMap;
use std::io::{Read, Write};
rs::counting!();
fn count(t: &[u8], k: usize) -> HashMap<&[u8], u32> {
    let mut m = HashMap::with_capacity(1024);
    for w in t.windows(k) { *m.entry(w).or_insert(0) += 1 }
    m
}
fn frequencies(o: &mut Vec<u8>, t: &[u8], k: usize) {
    let tot = (t.len() - k + 1) as f64;
    let m = count(t, k);
    let mut es: Vec<(&[u8], u32)> = m.into_iter().collect();
    es.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
    for (key, c) in es { o.extend_from_slice(key); writeln!(o, " {:.3}", c as f64 * 100.0 / tot).unwrap() }
    o.push(b'\n');
}
fn count_of(o: &mut Vec<u8>, t: &[u8], q: &str) {
    let m = count(t, q.len());
    let c = m.get(q.as_bytes()).copied().unwrap_or(0);
    writeln!(o, "{}\t{}", c, q).unwrap();
}
fn main() {
    let s0 = rs::snap();
    let mut inp = Vec::new();
    std::io::stdin().read_to_end(&mut inp).unwrap();
    let mut seq = Vec::with_capacity(inp.len());
    let mut lines = inp.split(|&b| b == b'\n');
    for l in lines.by_ref() { if l.starts_with(b">THREE") { break } }
    for l in lines { if l.starts_with(b">") { break } seq.extend(l.iter().map(|b| b.to_ascii_uppercase())) }
    let mut o = Vec::with_capacity(4096);
    frequencies(&mut o, &seq, 1);
    frequencies(&mut o, &seq, 2);
    for q in ["GGT", "GGTA", "GGTATT", "GGTATTTTAATT", "GGTATTTTAATTTATAGT"] { count_of(&mut o, &seq, q) }
    rs::report(s0);
    std::io::stdout().write_all(&o).unwrap();
}

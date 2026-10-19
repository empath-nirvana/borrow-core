// reverse-complement, as bg/revcomp.bc: FASTA on stdin; each sequence reverse-complemented in
// place through a 256-byte table and written 60 a line into one output buffer.
use std::io::{Read, Write};
rs::counting!();
fn table() -> [u8; 256] {
    let mut t = [0u8; 256];
    for i in 0..256 { t[i] = i as u8 }
    for (a, b) in [(b'A', b'T'), (b'C', b'G'), (b'G', b'C'), (b'T', b'A'), (b'U', b'A'), (b'M', b'K'), (b'R', b'Y'),
                   (b'W', b'W'), (b'S', b'S'), (b'Y', b'R'), (b'K', b'M'), (b'V', b'B'), (b'H', b'D'), (b'D', b'H'),
                   (b'B', b'V'), (b'N', b'N')] {
        t[a as usize] = b; t[a.to_ascii_lowercase() as usize] = b;
    }
    t
}
fn flush(o: &mut Vec<u8>, seq: &mut Vec<u8>, t: &[u8; 256]) {
    let n = seq.len();
    for i in 0..(n + 1) / 2 {
        let j = n - 1 - i;
        let (x, y) = (seq[i], seq[j]);
        seq[i] = t[y as usize]; seq[j] = t[x as usize];
    }
    for line in seq.chunks(60) { o.extend_from_slice(line); o.push(b'\n') }
    seq.clear();
}
fn main() {
    let s0 = rs::snap();
    let mut inp = Vec::new();
    std::io::stdin().read_to_end(&mut inp).unwrap();
    let t = table();
    let n = inp.len();
    let mut o = Vec::with_capacity(n + n / 60 + 16);
    let mut seq = Vec::with_capacity(n);
    let mut header = false;
    for &b in &inp {
        if b == b'>' { flush(&mut o, &mut seq, &t); header = true }
        if header { o.push(b); if b == b'\n' { header = false } }
        else if b != b'\n' { seq.push(b) }
    }
    flush(&mut o, &mut seq, &t);
    let mut out = std::io::stdout().lock();
    out.write_all(&o).unwrap();
    out.flush().unwrap();
    rs::report(s0);
}

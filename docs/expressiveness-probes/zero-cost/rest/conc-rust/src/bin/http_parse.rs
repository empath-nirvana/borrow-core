// ns/http-parse.bc: an HTTP/1.1 response's status code, Content-Length and body bytes, read from
// stdin. Two forms: the push state machine fed byte by byte (as ours and httparse/llhttp), and
// the pull form over a BufRead (read_line into a reused String).
use conc_rust::*;
use std::io::{BufRead, Read};
#[global_allocator] static A: Counting = Counting;
fn main() {
    let pull = std::env::args().nth(1).as_deref() == Some("pull");
    let stdin = std::io::stdin();
    let mut inp = stdin.lock();
    let _ = inp.fill_buf();
    let a0 = snapshot();
    let r = if !pull {
        let (mut ph, mut sp, mut code, mut mi, mut inv, mut cl, mut body, mut ll) = (0, 0, 0, 0i32, false, 0, 0, 0);
        const NAME: &[u8] = b"content-length";
        for b in inp.by_ref().bytes() {
            let b = b.unwrap();
            match ph {
                0 => if b == b'\n' { ph = 1; mi = 0; inv = false; ll = 0 } else if b == b' ' { sp += 1 } else if sp == 1 && b.is_ascii_digit() { code = code * 10 + (b - b'0') as i32 },
                1 => if b == b'\n' { if ll == 0 { ph = 2 } else { mi = 0; inv = false; ll = 0 } } else if b != b'\r' {
                        ll += 1;
                        if inv { if b.is_ascii_digit() { cl = cl * 10 + (b - b'0') as i32 } }
                        else if b == b':' { inv = mi == 14; mi = -1 }
                        else { mi = if (0..14).contains(&mi) && b.to_ascii_lowercase() == NAME[mi as usize] { mi + 1 } else { -1 } }
                    },
                _ => body += 1,
            }
            if ph == 2 && body >= cl { break }
        }
        code * 10000 + cl * 100 + body
    } else {
        let mut line = String::new();
        inp.read_line(&mut line).unwrap();
        let code: i32 = line.split(' ').nth(1).unwrap().parse().unwrap();
        let mut cl = 0;
        loop {
            line.clear();
            inp.read_line(&mut line).unwrap();
            let l = line.trim_end();
            if l.is_empty() { break }
            if let Some((k, v)) = l.split_once(':') { if k.eq_ignore_ascii_case("content-length") { cl = v.trim().parse().unwrap() } }
        }
        let mut body = 0;
        for _ in inp.by_ref().bytes().take(cl as usize) { body += 1 }
        code * 10000 + cl * 100 + body
    };
    report(if pull { "http_parse (pull)" } else { "http_parse (push)" }, a0);
    println!("{r}");
}

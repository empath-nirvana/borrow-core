//! Probe: an HTTPS GET through `wasi:http/outgoing-handler`, with an optional bearer token read
//! from a file (as a Kubernetes service-account token is), streaming the response body to
//! standard output in chunks. The host performs TCP, TLS and HTTP; this component sees only
//! request and response resources.
//!
//!   wasmtime run -S http,cli --dir <dir> https-guest.wasm <url> [<token-file>]

use std::io::Write;
use wasip2::http::outgoing_handler;
use wasip2::http::types::{Fields, IncomingBody, Method, OutgoingBody, OutgoingRequest, Scheme};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let url = args.get(1).expect("usage: https-guest <url> [<token-file>]");
    let token = args.get(2).map(|p| std::fs::read_to_string(p).expect("read token file"));

    let (scheme, rest) = url.split_once("://").expect("url has a scheme");
    let (authority, path) = match rest.find('/') {
        Some(i) => (&rest[..i], &rest[i..]),
        None => (rest, "/"),
    };

    let headers = Fields::new();
    if let Some(t) = &token {
        let v = format!("Bearer {}", t.trim());
        headers.append("authorization", v.as_bytes()).expect("authorization header");
    }
    headers.append("accept", b"application/json").expect("accept header");

    let req = OutgoingRequest::new(headers);
    req.set_method(&Method::Get).unwrap();
    req.set_scheme(Some(&if scheme == "https" { Scheme::Https } else { Scheme::Http })).unwrap();
    req.set_authority(Some(authority)).unwrap();
    req.set_path_with_query(Some(path)).unwrap();
    let body = req.body().unwrap();
    OutgoingBody::finish(body, None).unwrap();

    let fut = outgoing_handler::handle(req, None).expect("request accepted");
    fut.subscribe().block();
    let resp = match fut.get().expect("ready").expect("first get") {
        Ok(r) => r,
        Err(e) => {
            eprintln!("request failed: {e:?}");
            std::process::exit(2);
        }
    };
    eprintln!("status {}", resp.status());

    let incoming = resp.consume().unwrap();
    let stream = incoming.stream().unwrap();
    let mut out = std::io::stdout();
    let mut total = 0usize;
    let mut chunks = 0usize;
    loop {
        match stream.blocking_read(4096) {
            Ok(bytes) => {
                total += bytes.len();
                chunks += 1;
                out.write_all(&bytes).unwrap();
            }
            Err(_closed) => break,
        }
    }
    drop(stream);
    let _trailers = IncomingBody::finish(incoming);
    out.flush().unwrap();
    eprintln!("body {total} bytes in {chunks} reads");
}

//! Probe: which wasmtime flags a guest needs for TCP and DNS. Connects, writes a line, reads
//! the reply.
//!
//!   wasmtime run [-S inherit-network] [-S allow-ip-name-lookup] tcp-guest.wasm <host:port>

use std::io::{Read, Write};
fn main() {
    let a = std::env::args().nth(1).unwrap();
    match std::net::TcpStream::connect(a.as_str()) {
        Ok(mut s) => { s.write_all(b"ping\n").unwrap(); let mut b = [0u8; 16]; let n = s.read(&mut b).unwrap(); println!("connected, read {} bytes", n); }
        Err(e) => println!("connect failed: {e}"),
    }
}

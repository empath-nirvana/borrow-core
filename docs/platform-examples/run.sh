#!/bin/sh
# Platform probes for docs/platform-design.md §5. Not part of the gate: they need network access,
# Rust with the wasm32-wasip2 target, wasm-tools, openssl and python3, besides wasmtime.
#
#   docs/platform-examples/run.sh            all three probes
#
# 1. wat-component: a hand-written core module shaped like our backend's output, importing
#    WASI 0.2 by canonical-ABI signatures, wrapped as a component, run by `wasmtime run`.
# 2. https-guest under `wasmtime run -S http`: an HTTPS GET to a public site (public roots), and
#    the same GET to a local server whose certificate a private CA signed (fails: the CLI's
#    roots are compiled in).
# 4. tcp-guest: which `-S` flags TCP and DNS need (after 3).
# 3. custom-ca/host: an embedder of wasmtime 49 whose `send_request` hook verifies against the
#    private CA; the same component then gets the bearer-token-protected, chunked watch stream.
set -e
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'kill $srv 2>/dev/null || true; rm -rf "$tmp"' EXIT

echo "== wasmtime $(wasmtime --version | cut -d' ' -f2)"

echo "== 1. a core module of our shape, as a component"
cd "$here/wat-component"
wasm-tools parse probe.wat -o "$tmp/core.wasm"
wasm-tools component embed wit --world probe "$tmp/core.wasm" -o "$tmp/embed.wasm"
wasm-tools component new "$tmp/embed.wasm" -o "$tmp/probe.wasm"
wasmtime run -W tail-call=y "$tmp/probe.wasm"

echo "== 2. wasi:http under the wasmtime CLI"
cd "$here/https-guest"
cargo build -q --release --target wasm32-wasip2
guest="$here/https-guest/target/wasm32-wasip2/release/https-guest.wasm"
wasmtime run -S http "$guest" https://example.com/ >/dev/null
"$here/custom-ca/make-ca.sh" "$tmp/pki" >/dev/null
python3 "$here/custom-ca/server.py" "$tmp/pki/server.crt" "$tmp/pki/server.key" \
  "$(cat "$tmp/pki/token")" 8443 &
srv=$!
i=0; until curl -sk -o /dev/null https://127.0.0.1:8443/ || [ $i -ge 50 ]; do sleep 0.2; i=$((i+1)); done
echo "-- private CA, wasmtime CLI (expected to fail):"
wasmtime run -S http --dir "$tmp/pki::/pki" "$guest" 'https://localhost:8443/api/v1/pods?watch=1' \
  /pki/token || true

echo "== 3. the same component under an embedder with the cluster CA"
cd "$here/custom-ca/host"
cargo build -q --release
./target/release/ca-host "$tmp/pki/ca.crt" "$guest" "$tmp/pki" \
  'https://localhost:8443/api/v1/pods?watch=1' /pki/token

echo "== 4. TCP and DNS permissions under the wasmtime CLI"
cd "$here/tcp-guest"
cargo build -q --release --target wasm32-wasip2
tcp="$here/tcp-guest/target/wasm32-wasip2/release/tcp-guest.wasm"
python3 -c "
import socket;s=socket.socket();s.setsockopt(socket.SOL_SOCKET,socket.SO_REUSEADDR,1)
s.bind(('127.0.0.1',9099));s.listen(5)
for _ in range(2):
  c,_=s.accept();c.recv(16);c.sendall(b'pong\\n');c.close()" &
sleep 0.5
echo "-- no flags:"; wasmtime run "$tcp" 127.0.0.1:9099
echo "-- -S inherit-network:"; wasmtime run -S inherit-network "$tcp" 127.0.0.1:9099
echo "-- -S inherit-network, a name:"; wasmtime run -S inherit-network "$tcp" localhost:9099
echo "-- -S inherit-network -S allow-ip-name-lookup, a name:"
wasmtime run -S inherit-network -S allow-ip-name-lookup "$tcp" localhost:9099

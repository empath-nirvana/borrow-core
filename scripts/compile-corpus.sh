#!/usr/bin/env bash
# Compile and run the corpus. For every corpus/*.bc with a `main` (except a file marked
# `-- check: parse-only`), `bcc run` (WebAssembly under wasmtime) must print the value that
# `Support`'s interpreter prints (`bcc interp`), and then `live 0`: no object is live once the
# value is dropped. (Each prints `live N`; the source counts cells, the compiled stages all
# objects, so the two agree when either is 0.) On a difference, the closure-IR and flat-IR
# interpreters (`bcc interp --stage clos|flat`) name the first stage that diverges.
set -euo pipefail
cd "$(dirname "$0")/.."
command -v wasmtime >/dev/null || { echo "wasmtime is not on PATH"; exit 1; }
lake build bcc >/dev/null
bcc=.lake/build/bin/bcc
bad=0
# Same value, and memory empty in both or in neither.
agree() {
  [ "$(echo "$1" | head -1)" = "$(echo "$2" | head -1)" ] &&
    { [ "$(echo "$1" | tail -1)" = "live 0" ] && [ "$(echo "$2" | tail -1)" = "live 0" ] ||
      { [ "$(echo "$1" | tail -1)" != "live 0" ] && [ "$(echo "$2" | tail -1)" != "live 0" ]; }; }
}
for f in corpus/*.bc; do
  if grep -q '^-- check: parse-only' "$f"; then echo "$f: parse-only, skipped"; continue; fi
  if ! grep -q '^main' "$f"; then echo "$f: no main, skipped"; continue; fi
  if ! want=$("$bcc" interp "$f" 2>&1); then
    echo "$f: the source interpreter fails: $want"; bad=$((bad + 1)); continue
  fi
  got=$("$bcc" run "$f" 2>&1) || true
  if ! agree "$want" "$got"; then
    stage=wasm
    for s in clos flat; do
      out=$("$bcc" interp --stage "$s" "$f" 2>&1) || true
      if ! agree "$want" "$out"; then stage=$s; break; fi
    done
    echo "$f: differs, first at stage $stage"
    echo "  interpreter: $(echo "$want" | tr '\n' ' ')"
    echo "  wasm:        $(echo "$got" | tr '\n' ' ')"
    bad=$((bad + 1))
  elif [ "$(echo "$got" | tail -1)" != "live 0" ]; then
    echo "$f: agrees, but leaves objects live: $(echo "$got" | tr '\n' ' ')"; bad=$((bad + 1))
  else
    echo "$f: $(echo "$got" | head -1) | $(echo "$got" | tail -1)"
  fi
done
echo "$bad failure(s)."
[ "$bad" -eq 0 ]

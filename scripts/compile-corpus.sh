#!/usr/bin/env bash
# Compile and run the corpus. For every corpus/*.bc with a `main` (except a file marked
# `-- check: parse-only`), `bcc run` (WebAssembly under wasmtime) must print the value that
# `Support`'s interpreter prints (`bcc interp`), and then `live 0`: no object is live once the
# value is dropped. (Each prints `live N`; the source counts cells, the compiled stages all
# objects, so the two agree when either is 0.) On a difference, the closure-IR and flat-IR
# interpreters (`bcc interp --stage clos|flat`) name the first stage that diverges.
#
# A program with a golden output `corpus/<name>.out` (the standard I/O programs of SPEC §11)
# reads `corpus/<name>.in` as standard input (the empty input if there is none). At every stage,
# its whole standard output, the program's bytes followed by the report, must equal
# `corpus/<name>.out`, and its standard error `corpus/<name>.err` (empty if there is none).
set -euo pipefail
cd "$(dirname "$0")/.."
command -v wasmtime >/dev/null || { echo "wasmtime is not on PATH"; exit 1; }
lake build bcc >/dev/null
bcc=.lake/build/bin/bcc
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
bad=0
# Same value, and memory empty in both or in neither.
agree() {
  [ "$(echo "$1" | head -1)" = "$(echo "$2" | head -1)" ] &&
    { [ "$(echo "$1" | tail -1)" = "live 0" ] && [ "$(echo "$2" | tail -1)" = "live 0" ] ||
      { [ "$(echo "$1" | tail -1)" != "live 0" ] && [ "$(echo "$2" | tail -1)" != "live 0" ]; }; }
}
# Run stage $1 of file $2 on input $3 into $tmp/out and $tmp/err.
runStage() {
  if [ "$1" = wasm ]; then "$bcc" run "$2" < "$3" > "$tmp/out" 2> "$tmp/err"
  else "$bcc" interp --stage "$1" "$2" < "$3" > "$tmp/out" 2> "$tmp/err"; fi
}
for f in corpus/*.bc; do
  if grep -q '^-- check: parse-only' "$f"; then echo "$f: parse-only, skipped"; continue; fi
  if ! grep -q '^main' "$f"; then echo "$f: no main, skipped"; continue; fi
  base=${f%.bc}
  if [ -f "$base.out" ]; then
    in=/dev/null; [ -f "$base.in" ] && in="$base.in"
    err=/dev/null; [ -f "$base.err" ] && err="$base.err"
    ok=1
    for st in source clos flat wasm; do
      if ! runStage "$st" "$f" "$in"; then
        echo "$f: stage $st fails: $(head -3 "$tmp/err")"; ok=0; break
      fi
      if ! cmp -s "$tmp/out" "$base.out" || ! cmp -s "$tmp/err" "$err"; then
        echo "$f: stage $st differs from $base.out or from its standard error"
        diff "$tmp/out" "$base.out" | head -6 | sed 's/^/  /' || true; ok=0; break
      fi
    done
    if [ "$ok" = 1 ] && [ "$(tail -1 "$base.out")" != "live 0" ]; then
      echo "$f: agrees, but leaves objects live"; ok=0
    fi
    if [ "$ok" = 1 ]; then echo "$f: $(wc -c < "$base.out" | tr -d ' ') bytes as $base.out at every stage | live 0"
    else bad=$((bad + 1)); fi
    continue
  fi
  if ! want=$("$bcc" interp "$f" 2>&1 < /dev/null); then
    echo "$f: the source interpreter fails: $want"; bad=$((bad + 1)); continue
  fi
  got=$("$bcc" run "$f" 2>&1 < /dev/null) || true
  if ! agree "$want" "$got"; then
    stage=wasm
    for s in clos flat; do
      out=$("$bcc" interp --stage "$s" "$f" 2>&1 < /dev/null) || true
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

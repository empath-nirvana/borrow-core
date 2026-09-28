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
#
# No I/O program has a bound on its input: `corpus/io-cat.bc` also copies a generated input of
# 4860 bytes, at every stage.
#
# Counts. Every program run is also run by `bcc-counts` (the flat IR and wasm, built to count,
# which must agree): the objects it allocates and the indirect calls it makes, the closure
# calls whose code a `switch` on the closure's tag chooses at run time. Each must be at most the
# program's entry in `corpus/counts.expected` (`name allocs indirect`); a count above it fails,
# one below it is reported so the file can be lowered. `--write-counts` rewrites the file with
# the counts of this run.
set -euo pipefail
cd "$(dirname "$0")/.."
command -v wasmtime >/dev/null || { echo "wasmtime is not on PATH"; exit 1; }
lake build bcc bcc-counts >/dev/null
bcc=.lake/build/bin/bcc
bccCounts=.lake/build/bin/bcc-counts
expected=corpus/counts.expected
write=0; [ "${1:-}" = "--write-counts" ] && write=1
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
bad=0
: > "$tmp/counts"
# The counts of file $1 on input $2, checked against the expected ones; appended to the table.
counts() {
  local name got a i want wa wi
  name=$(basename "${1%.bc}")
  if ! got=$("$bccCounts" "$1" < "$2" 2>&1); then echo "$1: counts: $got"; return 1; fi
  a=$(echo "$got" | awk '{print $2}'); i=$(echo "$got" | awk '{print $4}')
  echo "$name $a $i" >> "$tmp/counts"
  cnt="allocs $a, indirect $i"
  [ "$write" = 1 ] && return 0
  want=$(awk -v n="$name" '$1 == n {print $2, $3}' "$expected" 2>/dev/null || true)
  if [ -z "$want" ]; then echo "$1: no entry in $expected ($cnt)"; return 1; fi
  wa=${want% *}; wi=${want#* }
  if [ "$a" -gt "$wa" ] || [ "$i" -gt "$wi" ]; then
    echo "$1: counts regressed: $cnt, expected at most allocs $wa, indirect $wi"; return 1
  fi
  if [ "$a" -lt "$wa" ] || [ "$i" -lt "$wi" ]; then
    cnt="$cnt (below $expected's $wa, $wi: lower it)"
  fi
}
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
    if [ "$ok" = 1 ] && ! counts "$f" "$in"; then ok=0; fi
    if [ "$ok" = 1 ]; then echo "$f: $(wc -c < "$base.out" | tr -d ' ') bytes as $base.out at every stage | live 0 | $cnt"
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
  elif ! counts "$f" /dev/null; then
    bad=$((bad + 1))
  else
    echo "$f: $(echo "$got" | head -1) | $(echo "$got" | tail -1) | $cnt"
  fi
done
# An input past any fixed bound: 4860 bytes, copied whole at every stage.
awk 'BEGIN { for (i = 0; i < 90; i++) printf "line %02d of a long input, copied byte for byte by cat.\n", i }' \
  > "$tmp/big.in"
printf '()\nlive 0\n' | cat "$tmp/big.in" - > "$tmp/big.out"
bigok=1
for st in source clos flat wasm; do
  runStage "$st" corpus/io-cat.bc "$tmp/big.in" || true
  if ! cmp -s "$tmp/out" "$tmp/big.out"; then echo "corpus/io-cat.bc: stage $st differs on a $(wc -c < "$tmp/big.in" | tr -d ' ')-byte input"; bigok=0; fi
done
if [ "$bigok" = 1 ]; then echo "corpus/io-cat.bc: a $(wc -c < "$tmp/big.in" | tr -d ' ')-byte input copied whole at every stage"; else bad=$((bad + 1)); fi
if [ "$write" = 1 ]; then
  { echo "# Allocations and indirect (dispatched) calls per run of each corpus program (scripts/compile-corpus.sh)."
    echo "# name allocs indirect"
    sort "$tmp/counts"; } > "$expected"
  echo "wrote $expected"
fi
echo "$bad failure(s)."
[ "$bad" -eq 0 ]

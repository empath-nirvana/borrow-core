#!/usr/bin/env bash
# Compile and run the corpus. For every corpus/*.bc, corpus/surface/*.bc and corpus/axes/*.bc with
# a `main` (except a file marked `-- check: parse-only`), `bcc run` (WebAssembly under wasmtime)
# must print the value that `Support`'s interpreter prints (`bcc interp`), and then `live 0`: no
# object is live once the value is dropped. (Each prints `live N`; the source counts cells, the
# compiled stages all objects, so the two agree when either is 0.) On a difference, the closure-IR and flat-IR
# interpreters (`bcc interp --stage clos|flat`) name the first stage that diverges.
#
# A program with a golden output `<name>.out` beside it (the standard I/O programs of SPEC §11)
# reads `<name>.in` as standard input (the empty input if there is none). At every stage,
# its whole standard output, the program's bytes followed by the report, must equal
# `<name>.out`, and its standard error `<name>.err` (empty if there is none).
#
# A program marked `-- check: no-source` has a golden output and is too large for the source
# interpreter (`corpus/deep-list.bc`): it is run at every other stage.
#
# No I/O program has a bound on its input: `corpus/io-cat.bc` also copies a generated input of
# 4860 bytes, at every stage.
#
# Counts. Every program run is also run by `bcc-counts` (the flat IR and wasm, built to count,
# which must agree): the objects it allocates, the indirect calls it makes (the closure
# calls whose code a `switch` on the closure's tag chooses at run time), and the copies it makes of
# a variable at a non-trivial type (deep copies the ownership discipline inserts where a variable
# is used twice; Backend/README.md, Memory discipline). Each must be at most the
# program's entry in `corpus/counts.expected` (`name allocs indirect copies`, the name the file's path
# under `corpus/`, as `io-wc`, `surface/io-wc` or `axes/data-effects`); a count above it fails,
# one below it is reported so the file can be lowered. `--write-counts` rewrites the file with
# the counts of this run, keeping the comment an entry ends with (`# …`).
set -euo pipefail
cd "$(dirname "$0")/.."
command -v wasmtime >/dev/null || { echo "wasmtime is not on PATH"; exit 1; }
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc bcc-counts >/dev/null
. scripts/par.sh
export bcc=.lake/build/bin/bcc
export bccCounts=.lake/build/bin/bcc-counts
export expected=corpus/counts.expected
export write=0; [ "${1:-}" = "--write-counts" ] && write=1
export tmp; tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
bad=0
: > "$tmp/counts"
# The counts of file $1 on input $2, checked against the expected ones; appended to the table.
counts() {
  local name got a i c want wa wi wc note
  name=${1#corpus/}; name=${name%.bc}
  if ! got=$("$bccCounts" "$1" < "$2" 2>&1); then echo "$1: counts: $got"; return 1; fi
  a=$(echo "$got" | awk '{print $2}'); i=$(echo "$got" | awk '{print $4}')
  c=$(echo "$got" | awk '{print $6}')
  # An entry may end with a comment (`# …`), kept when the file is rewritten.
  note=$(awk -v n="$name" '$1 == n { sub(/^[^#]*/, ""); print }' "$expected" 2>/dev/null || true)
  echo "$name $a $i $c${note:+ $note}" >> "$tmp/counts"
  cnt="allocs $a, indirect $i, copies $c"
  [ "$write" = 1 ] && return 0
  want=$(awk -v n="$name" '$1 == n {print $2, $3, $4}' "$expected" 2>/dev/null || true)
  if [ -z "$want" ]; then echo "$1: no entry in $expected ($cnt)"; return 1; fi
  read -r wa wi wc <<< "$want"
  if [ -z "$wc" ]; then echo "$1: $expected's entry has no copies column"; return 1; fi
  if [ "$a" -gt "$wa" ] || [ "$i" -gt "$wi" ] || [ "$c" -gt "$wc" ]; then
    echo "$1: counts regressed: $cnt, expected at most allocs $wa, indirect $wi, copies $wc"; return 1
  fi
  if [ "$a" -lt "$wa" ] || [ "$i" -lt "$wi" ] || [ "$c" -lt "$wc" ]; then
    cnt="$cnt (below $expected's $wa, $wi, $wc: lower it)"
  fi
}
# Same value, and memory empty in both or in neither.
agree() {
  [ "$(echo "$1" | head -1)" = "$(echo "$2" | head -1)" ] &&
    { [ "$(echo "$1" | tail -1)" = "live 0" ] && [ "$(echo "$2" | tail -1)" = "live 0" ] ||
      { [ "$(echo "$1" | tail -1)" != "live 0" ] && [ "$(echo "$2" | tail -1)" != "live 0" ]; }; }
}
# Run stage $1 of file $2 on input $3 into $w/out and $w/err.
runStage() {
  if [ "$1" = wasm ]; then "$bcc" run "$2" < "$3" > "$w/out" 2> "$w/err"
  else "$bcc" interp --stage "$1" "$2" < "$3" > "$w/out" 2> "$w/err"; fi
}
# One corpus program, run at every stage and counted (in parallel, by `par`; its scratch
# directory is $PAR_TMP).
program() {
  local f=$1 w=${PAR_TMP:-$tmp} base in err ok stages st want got out stage s cnt
  if grep -q '^-- check: parse-only' "$f"; then echo "$f: parse-only, skipped"; return 0; fi
  if ! grep -q '^main' "$f"; then echo "$f: no main, skipped"; return 0; fi
  base=${f%.bc}
  if [ -f "$base.out" ]; then
    in=/dev/null; [ -f "$base.in" ] && in="$base.in"
    err=/dev/null; [ -f "$base.err" ] && err="$base.err"
    ok=1
    stages="source clos flat wasm"
    grep -q '^-- check: no-source' "$f" && stages="clos flat wasm"
    for st in $stages; do
      if ! runStage "$st" "$f" "$in"; then
        echo "$f: stage $st fails: $(head -3 "$w/err")"; ok=0; break
      fi
      if ! cmp -s "$w/out" "$base.out" || ! cmp -s "$w/err" "$err"; then
        echo "$f: stage $st differs from $base.out or from its standard error"
        diff "$w/out" "$base.out" | head -6 | sed 's/^/  /' || true; ok=0; break
      fi
    done
    if [ "$ok" = 1 ] && [ "$(tail -1 "$base.out")" != "live 0" ]; then
      echo "$f: agrees, but leaves objects live"; ok=0
    fi
    if [ "$ok" = 1 ] && ! counts "$f" "$in"; then ok=0; fi
    if [ "$ok" = 1 ]; then echo "$f: $(wc -c < "$base.out" | tr -d ' ') bytes as $base.out at every stage | live 0 | $cnt"
    else return 1; fi
    return 0
  fi
  if ! want=$("$bcc" interp "$f" 2>&1 < /dev/null); then
    echo "$f: the source interpreter fails: $want"; return 1
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
    return 1
  elif [ "$(echo "$got" | tail -1)" != "live 0" ]; then
    echo "$f: agrees, but leaves objects live: $(echo "$got" | tr '\n' ' ')"; return 1
  elif ! counts "$f" /dev/null; then
    return 1
  else
    echo "$f: $(echo "$got" | head -1) | $(echo "$got" | tail -1) | $cnt"
  fi
}
# An input past any fixed bound: 4860 bytes, copied whole at every stage. (The source
# interpreter takes about a minute on it, so it runs beside the corpus.)
bigcat() {
  local w=$tmp/bigcat st ok=1
  mkdir -p "$w"
  awk 'BEGIN { for (i = 0; i < 90; i++) printf "line %02d of a long input, copied byte for byte by cat.\n", i }' \
    > "$w/big.in"
  printf '()\nlive 0\n' | cat "$w/big.in" - > "$w/big.out"
  for st in source clos flat wasm; do
    runStage "$st" corpus/io-cat.bc "$w/big.in" || true
    if ! cmp -s "$w/out" "$w/big.out"; then echo "corpus/io-cat.bc: stage $st differs on a $(wc -c < "$w/big.in" | tr -d ' ')-byte input"; ok=0; fi
  done
  if [ "$ok" = 1 ]; then echo "corpus/io-cat.bc: a $(wc -c < "$w/big.in" | tr -d ' ')-byte input copied whole at every stage"; else return 1; fi
}
export -f counts agree runStage program
bigcat > "$tmp/bigcat.log" 2>&1 &
bigpid=$!
par program corpus/*.bc corpus/surface/*.bc corpus/axes/*.bc
bad=$par_failed
if wait "$bigpid"; then cat "$tmp/bigcat.log"; else cat "$tmp/bigcat.log"; bad=$((bad + 1)); fi
if [ "$write" = 1 ]; then
  { echo "# Allocations, indirect (dispatched) calls and copies at a non-trivial type per run of each corpus program (scripts/compile-corpus.sh)."
    echo "# name allocs indirect copies"
    sort "$tmp/counts"; } > "$expected"
  echo "wrote $expected"
fi
echo "$bad failure(s)."
[ "$bad" -eq 0 ]

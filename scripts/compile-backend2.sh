#!/usr/bin/env bash
# The new backend (`Backend2/`, docs/n1-plan.md) on the corpus. Every corpus program with a golden
# (as scripts/compile-corpus.sh runs them) is converted to the LIR and linted (`bcc lir --lint`). A
# program outside the new backend's fragment (it has an effect node: N2 and later) is listed and
# skipped. Every other is run at the LIR interpreter (`--stage lir`), the word IR's interpreter
# (`--stage lflat`) and in Wasm (`bcc run --backend new`), and natively when there is a C compiler
# (`bcc run --backend new --native`); each must print the golden standard output and error and end
# with the golden status. Its counts (`bcc-counts --backend new`) must be at most its entry in
# `corpus/counts-backend2.expected` (`name allocs indirect copies loads stores bounds`), the new
# backend's own table; they are also printed beside the old backend's (`corpus/counts.expected`),
# which they are compared with at the switch (docs/compiler.md §5.4, criterion 6).
#
#     scripts/compile-backend2.sh [file.bc…]
#     scripts/compile-backend2.sh --write-counts [file.bc…]
set -euo pipefail
cd "$(dirname "$0")/.."
export write=0
files=()
while [ $# -gt 0 ]; do
  case "$1" in
    --write-counts) write=1 ;;
    -*) echo "usage: scripts/compile-backend2.sh [--write-counts] [file.bc…]"; exit 2 ;;
    *) files+=("$1") ;;
  esac
  shift
done
[ ${#files[@]} -gt 0 ] || files=(corpus/*.bc corpus/surface/*.bc corpus/axes/*.bc corpus/aoc/*.bc corpus/leetcode/*/*.bc)
command -v wasmtime >/dev/null || { echo "wasmtime is not on PATH"; exit 1; }
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc bcc-counts >/dev/null
. scripts/par.sh
export bcc=.lake/build/bin/bcc
export bccCounts=.lake/build/bin/bcc-counts
export expected=corpus/counts-backend2.expected
export old=corpus/counts.expected
export native=0
if "$bcc" cc >/dev/null 2>&1; then native=1; fi
export tmp; tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

argsOf() {
  args=()
  local a=${1%.bc}.args line
  [ -f "$a" ] || return 0
  while IFS= read -r line || [ -n "$line" ]; do args+=("$line"); done < "$a"
}
statusOf() {
  local s=${1%.bc}.status
  if [ -f "$s" ]; then tr -d ' \n' < "$s"; else echo 0; fi
}

# One program: linted, run at every stage, counted.
program() {
  local f=$1 w=${PAR_TMP:-$tmp} base in err st rc name got a i c l s b want wa wi wc wl ws wb oldc note
  grep -q '^-- check: parse-only' "$f" && return 0
  grep -q '^main' "$f" || return 0
  base=${f%.bc}
  [ -f "$base.out" ] || return 0
  if ! "$bcc" lir --lint "$f" > "$w/lint" 2>&1; then
    if grep -q 'outside the pure fragment' "$w/lint"; then echo "$f: outside the new backend's fragment"; : > "$tmp/out.$RANDOM$RANDOM"; return 0; fi
    echo "$f: lint: $(head -3 "$w/lint")"; return 1
  fi
  in=/dev/null; [ -f "$base.in" ] && in="$base.in"
  err=/dev/null; [ -f "$base.err" ] && err="$base.err"
  argsOf "$f"
  for st in lir lflat wasm $([ "$native" = 1 ] && echo native); do
    rc=0
    case "$st" in
      wasm) "$bcc" run --backend new "$f" "${args[@]+"${args[@]}"}" < "$in" > "$w/out" 2> "$w/err" || rc=$? ;;
      native) "$bcc" run --backend new --native "$f" "${args[@]+"${args[@]}"}" < "$in" > "$w/out" 2> "$w/err" || rc=$? ;;
      *) "$bcc" interp --stage "$st" "$f" -- "${args[@]+"${args[@]}"}" < "$in" > "$w/out" 2> "$w/err" || rc=$? ;;
    esac
    if [ "$rc" != "$(statusOf "$f")" ] || ! cmp -s "$w/out" "$base.out" || ! cmp -s "$w/err" "$err"; then
      echo "$f: the new backend's $st stage differs from the golden (status $rc): $(head -c 300 "$w/err" | head -3)"
      return 1
    fi
  done
  name=${f#corpus/}; name=${name%.bc}
  if ! got=$("$bccCounts" --backend new "$f" -- "${args[@]+"${args[@]}"}" < "$in" 2>&1); then
    echo "$f: counts: $got"; return 1
  fi
  read -r _ a _ i _ c _ l _ s _ b <<< "$got"
  oldc=$(awk -v n="$name" '$1 == n { print $2, $3, $4 }' "$old" 2>/dev/null || true)
  note=$(awk -v n="$name" '$1 == n { sub(/^[^#]*/, ""); print }' "$expected" 2>/dev/null || true)
  echo "$name $a $i $c $l $s $b${note:+ $note}" > "$w/count"
  cat "$w/count" >> "$tmp/counts.$$.$RANDOM"
  [ "$write" = 1 ] && { echo "$f: ok (allocs $a indirect $i copies $c; old $oldc)"; return 0; }
  want=$(awk -v n="$name" '$1 == n { sub(/#.*/, ""); print $2, $3, $4, $5, $6, $7 }' "$expected" 2>/dev/null || true)
  if [ -z "$want" ]; then echo "$f: no entry in $expected (allocs $a indirect $i copies $c loads $l stores $s bounds $b)"; return 1; fi
  read -r wa wi wc wl ws wb <<< "$want"
  if [ "$a" -gt "$wa" ] || [ "$i" -gt "$wi" ] || [ "$c" -gt "$wc" ] ||
     [ "$l" -gt "$wl" ] || [ "$s" -gt "$ws" ] || [ "$b" -gt "$wb" ]; then
    echo "$f: counts regressed: allocs $a indirect $i copies $c loads $l stores $s bounds $b, expected at most $want"
    return 1
  fi
  echo "$f: ok (allocs $a indirect $i copies $c; old $oldc)"
}
export -f program argsOf statusOf
par program "${files[@]}"
if [ "$write" = 1 ]; then
  cat "$tmp"/counts.* 2>/dev/null | sort > "$tmp/new"
  { echo "# The new backend's counts per run (scripts/compile-backend2.sh, bcc-counts --backend new): name allocs indirect copies loads stores bounds."; cat "$tmp/new"; } > "$expected"
  echo "wrote $expected"
fi
echo "the new backend: $(cat "$tmp"/counts.* 2>/dev/null | wc -l | tr -d ' ') program(s) at their goldens, $(ls "$tmp"/out.* 2>/dev/null | wc -l | tr -d ' ') outside its fragment; $par_failed failure(s)."
[ "$par_failed" -eq 0 ]

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
# which they are compared with at the switch (docs/compiler.md §5.4, criterion 6). The effect
# erasure's postcondition (SPEC §47, §49, `bcc lir --erasure`): the program has no `handle` or
# `perform` left, and the `handle`, `perform` and `raise` nodes erased, and those compiled as state
# machines, are its line of `corpus/erasure-backend2.expected`.
#
#     scripts/compile-backend2.sh [file.bc…]
#     scripts/compile-backend2.sh --final [file.bc…]
#     scripts/compile-backend2.sh --write-counts [file.bc…]
#
# `--final` (`make gate`) lints each program and runs it in Wasm only: no LIR or word-IR
# interpreter, no native run, no erasure check and no counts. A program whose Wasm run differs
# from the golden is then run at the `lir` and `lflat` stages, and the first that differs is named.
set -euo pipefail
cd "$(dirname "$0")/.."
export write=0
export final=0
files=()
while [ $# -gt 0 ]; do
  case "$1" in
    --write-counts) write=1 ;;
    --final) final=1 ;;
    -*) echo "usage: scripts/compile-backend2.sh [--final | --write-counts] [file.bc…]"; exit 2 ;;
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
export erasure=corpus/erasure-backend2.expected
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

# --final: after program $1's Wasm run differs (input $2, standard error golden $3, base $4),
# the first of the lir and lflat stages that differs from the golden, if either does.
localise() {
  local st rc
  for st in lir lflat; do
    rc=0
    "$bcc" interp --stage "$st" "$1" -- "${args[@]+"${args[@]}"}" < "$2" > "$w/out" 2> "$w/err" || rc=$?
    if [ "$rc" != "$(statusOf "$1")" ] || ! cmp -s "$w/out" "$4.out" || ! cmp -s "$w/err" "$3"; then
      echo "  localised: the $st stage differs already"; return 0
    fi
  done
  echo "  localised: the lir and lflat stages agree with the golden; Wasm alone differs"
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
  local stages="lir lflat wasm $([ "$native" = 1 ] && echo native)"
  [ "$final" = 0 ] || stages="wasm"
  for st in $stages; do
    rc=0
    case "$st" in
      wasm) "$bcc" run --backend new "$f" "${args[@]+"${args[@]}"}" < "$in" > "$w/out" 2> "$w/err" || rc=$? ;;
      native) "$bcc" run --backend new --native "$f" "${args[@]+"${args[@]}"}" < "$in" > "$w/out" 2> "$w/err" || rc=$? ;;
      *) "$bcc" interp --stage "$st" "$f" -- "${args[@]+"${args[@]}"}" < "$in" > "$w/out" 2> "$w/err" || rc=$? ;;
    esac
    if [ "$rc" != "$(statusOf "$f")" ] || ! cmp -s "$w/out" "$base.out" || ! cmp -s "$w/err" "$err"; then
      echo "$f: the new backend's $st stage differs from the golden (status $rc): $(head -c 300 "$w/err" | head -3)"
      [ "$final" = 1 ] && localise "$f" "$in" "$err" "$base"
      return 1
    fi
  done
  if [ "$final" = 1 ]; then echo "$f: ok at wasm"; echo "$f" > "$tmp/counts.$$.$RANDOM"; return 0; fi
  name=${f#corpus/}; name=${name%.bc}
  local er wer
  er=$("$bcc" lir --erasure "$f" 2>&1)
  case "$er" in
    "erased "*" left 0 0") ;;
    *) echo "$f: the effect erasure's postcondition: $er"; return 1 ;;
  esac
  echo "$name $er" >> "$tmp/erasure.$$.$RANDOM"
  if [ "$write" != 1 ]; then
    wer=$(awk -v n="$name" '$1 == n { $1 = ""; sub(/^ /, ""); print }' "$erasure" 2>/dev/null || true)
    if [ "$wer" != "$er" ]; then echo "$f: erasure \"$er\", pinned \"$wer\" ($erasure)"; return 1; fi
  fi
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
export -f program localise argsOf statusOf
par program "${files[@]}"
if [ "$write" = 1 ]; then
  cat "$tmp"/counts.* 2>/dev/null | sort > "$tmp/new"
  { echo "# The new backend's counts per run (scripts/compile-backend2.sh, bcc-counts --backend new): name allocs indirect copies loads stores bounds."; cat "$tmp/new"; } > "$expected"
  echo "wrote $expected"
  cat "$tmp"/erasure.* 2>/dev/null | sort > "$tmp/newe"
  { echo "# The effect erasure per program the new backend compiles (scripts/compile-backend2.sh, bcc lir --erasure; SPEC §47, §49): name, the handle, perform and raise nodes erased, the handle nodes compiled as drives and the performs as suspensions of state machines (machines, suspends), and the handle nodes left (stored-continuation sites, other)."; cat "$tmp/newe"; } > "$erasure"
  echo "wrote $erasure"
fi
echo "the new backend: $(cat "$tmp"/counts.* 2>/dev/null | wc -l | tr -d ' ') program(s) at their goldens, $(ls "$tmp"/out.* 2>/dev/null | wc -l | tr -d ' ') outside its fragment; $par_failed failure(s)."
[ "$par_failed" -eq 0 ]

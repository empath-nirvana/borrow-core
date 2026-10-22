#!/usr/bin/env bash
# The new backend's native facts (SPEC §50), on the corpus. For every corpus program in the new
# backend's fragment (as scripts/compile-backend2.sh runs them):
#
#   * the differential run: the program built with its parameters' facts left out
#     (`bcc run --backend new --native --no-facts`) prints the golden standard output and error and
#     ends with the golden status, as the build with them (compile-backend2.sh's native stage) must;
#     both are `clang -O2`;
#   * `alwaysinline`: no call of a function the word IR asks to inline (`Fn.inline`) is left in the
#     `clang -O2` IR of the build with its facts;
#   * the frame slots: the cells the new backend places in a frame slot per run are at least the
#     old backend's, in every program where the old backend has a scoped cell (`bcc-counts
#     --sites`' `scoped-cells`): `bcc-counts --frames`, the frame slots a run starts at the flat IR.
#
#     scripts/native-facts.sh [file.bc…]
set -euo pipefail
cd "$(dirname "$0")/.."
files=("$@")
[ ${#files[@]} -gt 0 ] || files=(corpus/*.bc corpus/surface/*.bc corpus/axes/*.bc corpus/aoc/*.bc corpus/leetcode/*/*.bc)
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc bcc-counts >/dev/null
export bcc=.lake/build/bin/bcc
export bccCounts=.lake/build/bin/bcc-counts
if ! cc=$("$bcc" cc 2>/dev/null); then echo "native-facts: no C compiler: skipped"; exit 0; fi
export cc
. scripts/par.sh
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

program() {
  local f=$1 w=${PAR_TMP:-$tmp} base in err rc fns fn left old new
  grep -q '^-- check: parse-only' "$f" && return 0
  grep -q '^main' "$f" || return 0
  base=${f%.bc}
  [ -f "$base.out" ] || return 0
  if ! "$bcc" compile --backend new --target native "$f" -o "$w/on.ll" > "$w/log" 2>&1; then
    grep -q 'outside the pure fragment' "$w/log" && return 0
    echo "$f: $(head -3 "$w/log")"; return 1
  fi
  in=/dev/null; [ -f "$base.in" ] && in="$base.in"
  err=/dev/null; [ -f "$base.err" ] && err="$base.err"
  argsOf "$f"
  rc=0
  "$bcc" run --backend new --native --no-facts "$f" "${args[@]+"${args[@]}"}" < "$in" > "$w/out" 2> "$w/err" || rc=$?
  if [ "$rc" != "$(statusOf "$f")" ] || ! cmp -s "$w/out" "$base.out" || ! cmp -s "$w/err" "$err"; then
    echo "$f: without its facts the native build differs from the golden (status $rc)"
    return 1
  fi
  # `alwaysinline`: the functions asked for, and no call of one left after `-O2`.
  fns=$(sed -n 's/^define internal .* @\(f[0-9]*\)(.*) nounwind alwaysinline .*/\1/p' "$w/on.ll")
  if [ -n "$fns" ]; then
    $cc -O2 -S -emit-llvm -w "$w/on.ll" -o "$w/opt.ll" 2>/dev/null
    left=""
    for fn in $fns; do
      grep -q "call .*@$fn(" "$w/opt.ll" && left="$left $fn"
    done
    if [ -n "$left" ]; then echo "$f: alwaysinline, but called after -O2:$left"; return 1; fi
  fi
  # Frame slots: the cells the new backend places in a frame slot per run at least the old
  # backend's, where the old backend has a scoped cell (`--sites`); counted at the flat IR.
  old=""; new=""
  if [ "$("$bccCounts" --sites "$f" 2>/dev/null | sed -n 's/.*scoped-cells framed \([0-9]*\).*/\1/p')" != 0 ]; then
    old=$("$bccCounts" --frames "$f" -- "${args[@]+"${args[@]}"}" < "$in" 2>/dev/null | sed -n 's/^slots //p')
    new=$("$bccCounts" --backend new --frames "$f" -- "${args[@]+"${args[@]}"}" < "$in" 2>/dev/null | sed -n 's/^slots //p')
    if [ -z "$old" ] || [ -z "$new" ]; then echo "$f: no frame slot counts (old '$old', new '$new')"; return 1; fi
    if [ "$new" -lt "$old" ]; then
      echo "$f: $new frame slots per run, the old backend's $old"
      return 1
    fi
  fi
  echo "$f: ok${new:+ (frame slots $new, old $old)}${fns:+ (inlined $(echo $fns | wc -w | tr -d ' '))}"
}
export -f program argsOf statusOf
par program "${files[@]}"
echo "native facts: $par_failed failure(s)."
[ "$par_failed" -eq 0 ]

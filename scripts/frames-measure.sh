#!/usr/bin/env bash
# The frame elaboration of `let mut` (`BCC_FRAMES=1`, #632), measured on the corpus: each program
# the corpus runs (scripts/compile-corpus.sh's set), elaborated with `BCC_FRAMES=1` and run in
# WebAssembly (`bcc run`) on its `.in` and `.args`, is
#   * `same`: its output, standard error and exit status are its goldens;
#   * `DIFFERS`: it runs and prints something else (a wrong answer: there must be none);
#   * `refused`: it does not check, with the first line of the message;
# and its counts (`bcc-counts`) beside its entry in `corpus/counts.expected`.
#
#     scripts/frames-measure.sh [file.bc…]    one line a program, then the totals
#
# Not a gate step: the frame elaboration is a prototype behind the flag.
set -uo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc bcc-counts >/dev/null
. scripts/par.sh
export bcc=.lake/build/bin/bcc
export bccCounts=.lake/build/bin/bcc-counts
export BCC_FRAMES=${BCC_FRAMES-1}
files=("$@")
[ ${#files[@]} -gt 0 ] || files=(corpus/*.bc corpus/surface/*.bc corpus/axes/*.bc corpus/aoc/*.bc corpus/leetcode/*/*.bc)

one() {
  local f=$1 w=$PAR_TMP base in err rc=0 st name want got
  if grep -q '^-- check: parse-only' "$f" || ! grep -q '^main' "$f"; then return 0; fi
  base=${f%.bc}
  in=/dev/null; [ -f "$base.in" ] && in="$base.in"
  err=/dev/null; [ -f "$base.err" ] && err="$base.err"
  args=()
  if [ -f "$base.args" ]; then while IFS= read -r line || [ -n "$line" ]; do args+=("$line"); done < "$base.args"; fi
  st=0; [ -f "$base.status" ] && st=$(tr -d ' \n' < "$base.status")
  "$bcc" run "$f" "${args[@]+"${args[@]}"}" < "$in" > "$w/out" 2> "$w/err" || rc=$?
  if ! grep -q '^live ' "$w/out" && [ "$rc" != "$st" -o ! -s "$w/out" ]; then
    echo "refused $f: $(grep -v '^$' "$w/err" | head -1 | sed "s|^$f:||")"; return 0
  fi
  if [ "$rc" != "$st" ] || ! cmp -s "$w/out" "$base.out" || ! cmp -s "$w/err" "$err"; then
    echo "DIFFERS $f: exit $rc; $(diff "$w/out" "$base.out" | head -3 | tr '\n' ' ')"; return 0
  fi
  name=${f#corpus/}; name=${name%.bc}
  want=$(awk -v n="$name" '$1 == n { print $2, $3, $4, $5, $6, $7 }' corpus/counts.expected)
  got=$("$bccCounts" "$f" -- "${args[@]+"${args[@]}"}" < "$in" 2>/dev/null | awk '{ print $2, $4, $6, $8, $10, $12 }')
  if [ "$got" = "$want" ]; then echo "same $f: counts as expected"
  else echo "same $f: counts $got, expected $want"; fi
}
export -f one
par one "${files[@]}" | sort > "${MEASURE_OUT:-/dev/stdout}"

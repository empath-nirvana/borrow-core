#!/usr/bin/env bash
# Parse the corpus with `bcc parse`. Every `corpus/*.bc`, `corpus/surface/*.bc`,
# `corpus/axes/*.bc`, `corpus/aoc/*.bc` and `corpus/leetcode/*/*.bc` must parse and survive the print/re-parse round trip; every
# `corpus/fail/*.bc` must be rejected with the message on its `-- expect:` line.
# (`corpus/pending/` is checked by `check-corpus.sh`.)
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc >/dev/null
. scripts/par.sh
export bcc=.lake/build/bin/bcc
parses() { "$bcc" parse "$1"; }
fails() {
  set -e
  local f=$1 want out
  want=$(sed -n '/^-- expect: /{s///p;q;}' "$f")
  if out=$("$bcc" parse "$f" 2>&1); then
    echo "$f: accepted, but must fail"; return 1
  elif [ "$out" != "$f:$want" ]; then
    echo "$f: wrong error"; echo "  want: $want"; echo "  got:  ${out#"$f:"}"; return 1
  else
    echo "$f: rejected as expected"
  fi
}
export -f parses fails
# Each file is a unit of the result cache (scripts/par.sh), run one at a time, in order.
export PAR_CACHE=parse-corpus
JOBS=1 par parses corpus/*.bc corpus/surface/*.bc corpus/axes/*.bc corpus/aoc/*.bc corpus/leetcode/*/*.bc
bad=$par_failed
JOBS=1 par fails corpus/fail/*.bc
bad=$((bad + par_failed))
echo "$bad failure(s)."
[ "$bad" -eq 0 ]

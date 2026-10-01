#!/usr/bin/env bash
# Parse the corpus with `bcc parse`. Every `corpus/*.bc`, `corpus/surface/*.bc` and
# `corpus/axes/*.bc` must parse and survive the print/re-parse round trip; every
# `corpus/fail/*.bc` must be rejected with the message on its `-- expect:` line.
# (`corpus/pending/` is checked by `check-corpus.sh`.)
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc >/dev/null
bcc=.lake/build/bin/bcc
bad=0
for f in corpus/*.bc corpus/surface/*.bc corpus/axes/*.bc; do
  if ! "$bcc" parse "$f"; then bad=$((bad + 1)); fi
done
for f in corpus/fail/*.bc; do
  want=$(sed -n 's/^-- expect: //p' "$f" | head -1)
  if out=$("$bcc" parse "$f" 2>&1); then
    echo "$f: accepted, but must fail"; bad=$((bad + 1))
  elif [ "$out" != "$f:$want" ]; then
    echo "$f: wrong error"; echo "  want: $want"; echo "  got:  ${out#"$f:"}"; bad=$((bad + 1))
  else
    echo "$f: rejected as expected"
  fi
done
echo "$bad failure(s)."
[ "$bad" -eq 0 ]

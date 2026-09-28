#!/usr/bin/env bash
# Type-check the corpus with `bcc check`. Every `corpus/*.bc` and `corpus/surface/*.bc` must
# check, except a file marked `-- check: parse-only` (it is for the parser); every `corpus/reject/*.bc` must parse and be
# rejected by the checker with the message on its `-- expect:` line (`line:col: message`),
# continued by any `-- expect| ` lines for a message of several lines.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build bcc >/dev/null
bcc=.lake/build/bin/bcc
bad=0
for f in corpus/*.bc corpus/surface/*.bc; do
  if grep -q '^-- check: parse-only' "$f"; then
    echo "$f: parse-only, skipped"; continue
  fi
  if out=$("$bcc" check "$f" 2>&1); then
    echo "$f: checks"
  else
    echo "$f: rejected, but must check"; echo "  $out"; bad=$((bad + 1))
  fi
done
for f in corpus/reject/*.bc; do
  [ -e "$f" ] || continue
  want=$(sed -n 's/^-- expect: //p; s/^-- expect| //p' "$f")
  if ! "$bcc" parse "$f" >/dev/null 2>&1; then
    echo "$f: does not parse, so it does not test the checker"; bad=$((bad + 1))
  elif out=$("$bcc" check "$f" 2>&1); then
    echo "$f: accepted, but must be rejected"; bad=$((bad + 1))
  elif [ "$out" != "$f:$want" ]; then
    echo "$f: wrong error"; echo "  want: $want"; echo "  got:  ${out#"$f:"}"; bad=$((bad + 1))
  else
    echo "$f: rejected as expected"
  fi
done
echo "$bad failure(s)."
[ "$bad" -eq 0 ]

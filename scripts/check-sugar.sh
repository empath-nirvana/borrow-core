#!/usr/bin/env bash
# The I/O sugar (SPEC §11) is elaboration only. For every corpus/sugar/<name>.bc there is a
# corpus/sugar/<name>.core.bc written without the sugar: both must check, and the checked `main`
# of each must erase to the same term (`bcc erase`). A core form must also be its own
# elaboration: `bcc desugar` leaves it as it is.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build bcc >/dev/null
bcc=.lake/build/bin/bcc
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
bad=0
for f in corpus/sugar/*.bc; do
  case "$f" in *.core.bc) continue ;; esac
  core=${f%.bc}.core.bc
  if [ ! -f "$core" ]; then echo "$f: no $core"; bad=$((bad + 1)); continue; fi
  if ! "$bcc" check "$f" > /dev/null 2> "$tmp/err" || ! "$bcc" check "$core" > /dev/null 2>> "$tmp/err"; then
    echo "$f: does not check: $(cat "$tmp/err")"; bad=$((bad + 1)); continue
  fi
  "$bcc" erase "$f" > "$tmp/a"; "$bcc" erase "$core" > "$tmp/b"
  "$bcc" desugar "$core" > "$tmp/c"; "$bcc" print "$core" > "$tmp/d"
  if ! cmp -s "$tmp/a" "$tmp/b"; then echo "$f: its erasure differs from $core's"; bad=$((bad + 1))
  elif ! cmp -s "$tmp/c" "$tmp/d"; then echo "$core: has sugar left"; bad=$((bad + 1))
  else echo "$f: erases as $core"; fi
done
echo "$bad failure(s)."
[ "$bad" -eq 0 ]

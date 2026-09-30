#!/usr/bin/env bash
# Runs the examples of docs/iteration-design.md §13: each is checked, run by the source
# interpreter and compiled to WebAssembly, and counted (allocations, dispatched calls, copies).
# A program the checker rejects is reported as rejected (some are expected to be, as marked in
# their first comment). Not part of the CI gate.
set -uo pipefail
cd "$(dirname "$0")/../.."
lake build bcc bcc-counts >/dev/null
B=.lake/build/bin
for f in docs/iteration-examples/*.bc; do
  n=${f%.bc}; in=/dev/null; [ -f "$n.in" ] && in=$n.in
  if ! err=$("$B/bcc" check "$f" 2>&1 >/dev/null); then
    echo "$(basename "$f"): rejected: $(echo "$err" | tail -1)"; continue
  fi
  i=$("$B/bcc" interp "$f" < "$in" 2>&1 | tr '\n' ' ')
  r=$("$B/bcc" run "$f" < "$in" 2>&1 | tr '\n' ' ')
  c=$("$B/bcc-counts" "$f" < "$in" 2>&1 | tr '\n' ' ')
  [ "$i" = "$r" ] || echo "$(basename "$f"): interp and run differ"
  echo "$(basename "$f"): $r| $c"
done

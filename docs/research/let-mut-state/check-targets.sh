#!/usr/bin/env bash
# For each target pair here: does the surface program check and answer what its hand-written core
# answers, and does the elaboration erase to that core? Not part of the gate: a pair that is met
# moves to `corpus/sugar/` (#613); the README says what separates the others.
set -uo pipefail
cd "$(dirname "$0")/../../.."
bcc=.lake/build/bin/bcc
for f in docs/research/let-mut-state/targets/*.bc; do
  case "$f" in *.core.bc) continue ;; esac
  c=${f%.bc}.core.bc
  a=$("$bcc" interp "$f" 2>&1 | head -1); b=$("$bcc" interp "$c" 2>&1 | head -1)
  if cmp -s <("$bcc" erase "$f" 2>&1) <("$bcc" erase "$c" 2>&1); then e=yes; else e=no; fi
  echo "$(basename "$f"): $a, target $b, erases as the target: $e"
done
r=corpus/reject/mut-shadow-assign.bc
if "$bcc" check "$r" > /dev/null 2>&1; then echo "$(basename "$r"): accepted (target: rejected)"
else echo "$(basename "$r"): rejected"; fi

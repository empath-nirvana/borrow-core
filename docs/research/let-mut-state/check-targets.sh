#!/usr/bin/env bash
# For each target pair here: does the surface program check and answer what its hand-written core
# answers, and does today's elaboration erase to that core? Not part of the gate: these are the
# targets an elaboration of `let mut` is measured against (#611), which today's does not meet.
set -uo pipefail
cd "$(dirname "$0")/../../.."
bcc=.lake/build/bin/bcc
for f in docs/research/let-mut-state/targets/*.bc; do
  case "$f" in *.core.bc) continue ;; esac
  c=${f%.bc}.core.bc
  a=$("$bcc" interp "$f" 2>&1 | head -1); b=$("$bcc" interp "$c" 2>&1 | head -1)
  if cmp -s <("$bcc" erase "$f" 2>&1) <("$bcc" erase "$c" 2>&1); then e=yes; else e=no; fi
  echo "$(basename "$f"): today $a, target $b, erases as the target: $e"
done
r=docs/research/let-mut-state/targets/reject/mut-shadow-assign.bc
if "$bcc" check "$r" > /dev/null 2>&1; then echo "$(basename "$r"): accepted (target: rejected)"
else echo "$(basename "$r"): rejected"; fi

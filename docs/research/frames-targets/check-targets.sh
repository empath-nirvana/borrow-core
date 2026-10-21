#!/usr/bin/env bash
# The typestate targets of SPEC §47, under `BCC_FRAMES=1`: each program at the interpreter, the new
# backend's LIR interpreter and Wasm, and the old backend's Wasm, against its `-- Answer:` line, every
# cell freed at its end (`live 0`); a program marked `-- Refused.` must be refused.
#
#     docs/research/frames-targets/check-targets.sh
set -uo pipefail
cd "$(dirname "$0")/../../.."
export BCC_FRAMES=1
bcc=.lake/build/bin/bcc
fail=0
for f in docs/research/frames-targets/*.bc; do
  want=$(sed -n 's/^-- Answer: \(.*\)\.$/\1/p' "$f")
  if [ -z "$want" ]; then
    if "$bcc" check "$f" >/dev/null 2>&1; then echo "FAIL $f: accepted, expected a refusal"; fail=1
    else echo "ok   $f: refused ($("$bcc" check "$f" 2>&1 | head -1 | sed "s|^$f:||"))"; fi
    continue
  fi
  for how in "interp" "interp --stage lir" "run --backend new" "run"; do
    got=$("$bcc" $how "$f" 2>&1 | head -1)
    if [ "$got" != "$want" ]; then echo "FAIL $f ($how): $got, expected $want"; fail=1; fi
  done
  live=$("$bcc" interp "$f" 2>&1 | sed -n 2p)
  if [ "$live" != "live 0" ]; then echo "FAIL $f: $live at the end"; fail=1; fi
  [ $fail = 0 ] && echo "ok   $f: $want, live 0"
done
exit $fail

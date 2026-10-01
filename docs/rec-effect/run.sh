#!/usr/bin/env bash
# Runs the hand-lowerings of docs/rec-effect/README.md: each `.bc` is checked, compiled to
# WebAssembly and run (`bcc run`), and counted (`bcc-counts`: allocations, dispatched calls, copies).
# Not part of the CI gate.
#
# Header lines a program may carry:
#   -- uses: rec.bc          rec.bc is put in front of it (an error's line is then offset by the
#                            length of rec.bc; run.sh reports it in the program's own lines)
#   -- expect: rejected      the checker is expected to reject it; the error is printed
#   -- expect: fails         it checks, and the compiled run is expected to fail (stack)
#   -- counts-at: s/X/Y/     count a smaller instance, the program with that sed substitution
#                            applied: the counting interpreter (the flat IR, in Lean) overflows
#                            Lean's stack on the full size, where wasmtime does not
#   -- stage: all            also run by the source interpreter (`bcc interp`), which must agree;
#                            it is slow on machines of many observations, so it is opt-in
# A `<name>.in` beside a program is its standard input.
set -uo pipefail
cd "$(dirname "$0")/../.."
lake build bcc bcc-counts >/dev/null
B=.lake/build/bin
D=docs/rec-effect
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
off=$(wc -l < "$D/rec.bc" | tr -d ' ')
for f in "$D"/*.bc; do
  name=$(basename "$f")
  [ "$name" = rec.bc ] && continue
  n=${f%.bc}; in=/dev/null; [ -f "$n.in" ] && in=$n.in
  src=$f; shift_by=0
  if grep -q '^-- uses: rec.bc' "$f"; then
    src=$T/$name; cat "$D/rec.bc" "$f" > "$src"; shift_by=$off
  fi
  if ! err=$("$B/bcc" check "$src" 2>&1 >/dev/null); then
    msg=$(echo "$err" | head -1 | sed "s|$T/||")
    line=$(echo "$msg" | sed -n 's/^[^:]*:\([0-9]*\):.*/\1/p')
    if [ -n "$line" ] && [ "$shift_by" -gt 0 ] && [ "$line" -gt "$shift_by" ]; then
      msg="(line $((line - shift_by)) of $name) $msg"
    fi
    if grep -q '^-- expect: rejected' "$f"; then echo "$name: rejected, as expected: $msg"
    else echo "$name: REJECTED: $msg"; fi
    continue
  fi
  grep -q '^-- expect: rejected' "$f" && echo "$name: CHECKS, but was expected to be rejected"
  raw=$("$B/bcc" run "$src" < "$in" 2>&1)
  r=$(echo "$raw" | tr '\n' ' ')
  if grep -q '^-- expect: fails' "$f"; then
    echo "$name: run fails, as expected: $(echo "$raw" | grep -m1 'trap' | sed 's/^ *[0-9]*: *//')"; continue
  fi
  if grep -q '^-- stage: all' "$f"; then
    i=$("$B/bcc" interp "$src" < "$in" 2>&1 | tr '\n' ' ')
    [ "$i" = "$r" ] || echo "$name: interp and run differ: interp gives $i"
  fi
  csrc=$src; at=""
  sub=$(sed -n 's/^-- counts-at: //p' "$f")
  if [ -n "$sub" ]; then
    csrc=$T/counts-$name; sed "$sub" "$src" > "$csrc"; at=" (counted at $sub)"
  fi
  c=$("$B/bcc-counts" "$csrc" < "$in" 2>&1 | tr '\n' ' ')
  echo "$name: $r| $c$at"
done

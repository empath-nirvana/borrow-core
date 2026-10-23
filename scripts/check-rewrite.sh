#!/usr/bin/env bash
# The Core → Core rewriter (SPEC §54, #680): for every corpus program that checks and has a `main`,
# the program read back from its typed term, after the rules, and checked again
# (`bcc rewrite --identity`). Its line: the instances of `def`s read back, the declarations and
# the lifetime-polymorphic ones among them; then
#
# * at a program no rule rewrites (step 0, the identity): the uses; the rewritten `main`'s erasure
#   against the source's (`same`, or `beta`: other only at the instantiations of polymorphic
#   declarations, the typed terms agreeing everywhere else); the LIR of the rewritten program
#   against the source's, byte for byte (`same`; `outside` when both are outside the new backend's
#   fragment with one message; `differs`); and the typed terms' mismatches, node by node and field
#   by field modulo spans, by node kind and field (`poly:` inside a polymorphic declaration's body);
# * at a program R0 rewrites: its abortive names, each `rewritten` or `left` with its reason; the
#   source nodes R0 rewrote, by rule (`main` and each instance's body once); the binders `π` maps
#   elsewhere; and whether the new backend compiles the rewritten program (`ok`), both are outside
#   its fragment (`outside`), or only the source compiles (`red`).
#
# The gate: every line of a program no rule rewrites has `erasure same` or `beta` and `lir same`
# or `outside`, and every line of a program R0 rewrites `lir ok` or `outside`; the table is pinned
# in corpus/rewrite.expected, so a change shows here; R0's seeded faults are refused; and its
# controls (faults only the goldens see) change the output.
#
#     scripts/check-rewrite.sh            compare with corpus/rewrite.expected
#     scripts/check-rewrite.sh --write    write it
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc >/dev/null
bcc=.lake/build/bin/bcc
row() {
  local f=$1 l
  grep -q '^main' "$f" || return 0
  "$bcc" check "$f" >/dev/null 2>&1 || return 0
  if ! l=$("$bcc" rewrite --identity "$f" 2>&1); then
    echo "$f error: $(printf '%s' "$l" | head -c 300 | tr '\n' ' ')"
    return 0
  fi
  echo "$f $l"
}
. scripts/par.sh
export bcc
export -f row
table() {
  local fs=()
  while read -r f; do
    grep -q '^-- check: parse-only' "$f" || fs+=("$f")
  done < <(git ls-files 'corpus/*.bc' | grep -v '^corpus/\(reject\|pending\|fail\)/' | sort)
  par row "${fs[@]}"
}
out=$(mktemp)
trap 'rm -rf "$out"' EXIT
table > "$out"
bad=$(awk '/ R0 .*:rewritten/ { if (!/ lir (ok|outside)$/) print; next }
          !/ erasure (same|beta) / || !/ lir (same|outside) / { print }' "$out")
if [ "${1:-}" = "--write" ]; then
  cp "$out" corpus/rewrite.expected
  echo "corpus/rewrite.expected: $(wc -l < corpus/rewrite.expected | tr -d " ") programs"
  [ -z "$bad" ] || { echo "check-rewrite: not the identity:"; printf '%s\n' "$bad"; exit 1; }
  exit 0
fi
fail=0
if [ -n "$bad" ]; then
  echo "check-rewrite: not the identity:"; printf '%s\n' "$bad"; fail=1
fi
if ! diff -u corpus/rewrite.expected "$out"; then
  echo "check-rewrite: the rewriter's identity table changed (corpus/rewrite.expected)"; fail=1
fi
# R0's reject tests: a fault planted in R0 (`bcc rewrite --seed`) is refused, by the guard check
# or the kernel's re-check named. `dropFin` leaves a written finaliser off the abort arm, `dupFin`
# runs it twice there, `dropGlue` leaves drop glue's arm off, `tdReplaced` frees an unwinding
# borrow's source by `free` instead of its destructor, `dupClauses` copies a handler's clauses
# into each arm of the payload's `case`, `widenLin` gives an operation at `1` a continuation at
# `1?` (G-κ's fault; the kernel refuses it first: a handler's row is its clauses' operations at
# the counts the source's check inferred).
seeds=(
  "dropFin corpus/core-r0-unwind.bc guard"
  "dupFin corpus/core-r0-unwind.bc kernel"
  "dropFin corpus/core-r0-unwind-linear.bc kernel"
  "dupFin corpus/core-r0-unwind-linear.bc kernel"
  "dropGlue corpus/core-effects-drop-glue.bc guard G-fin"
  "tdReplaced corpus/core-effects-borrow-abort.bc guard G-fin"
  "dupClauses corpus/core-r0-two-ops.bc guard G-bang"
  "widenLin corpus/core-r0-forward.bc kernel"
)
for t in "${seeds[@]}"; do
  read -r sd f by g <<< "$t"
  got=$("$bcc" rewrite --seed "$sd" "$f" 2>&1 || true)
  case "$by:$got" in
    "guard:refused: guard${g:+ $g}"*|"kernel:refused: rewrite: the kernel refuses"*) ;;
    *) echo "check-rewrite: R0 seeded with $sd on $f is not refused by the $by ${g:-}: $got"; fail=1 ;;
  esac
done
# R0's controls: faults the kernel and the guard accept, which only the goldens catch (a wrong
# injection index, the payload's `case` arms swapped, the forwarding answer clause's arms swapped,
# each between summands of one type): accepted, and the program's output differs from its golden.
controls=(
  "injIndex corpus/core-r0-two-ops.bc"
  "swapDispatch corpus/core-r0-two-ops.bc"
  "swapFwd corpus/core-r0-forward.bc"
)
for t in "${controls[@]}"; do
  read -r sd f <<< "$t"
  if [ "$("$bcc" rewrite --seed "$sd" "$f" 2>&1)" != "ACCEPTED" ]; then
    echo "check-rewrite: the control $sd on $f is refused"; fail=1; continue
  fi
  if "$bcc" rewrite --seed-run "$sd" "$f" 2>&1 | cmp -s - "${f%.bc}.out"; then
    echo "check-rewrite: the control $sd on $f does not change the output"; fail=1
  fi
done
[ "$fail" = 0 ] || exit 1
echo "check-rewrite: $(wc -l < "$out" | tr -d " ") programs read back and checked again, as pinned: every program no rule rewrites the identity (its erasure and LIR the source's, up to the instantiations of polymorphic declarations), every program R0 rewrites compiled; ${#seeds[@]} seeded faults refused, ${#controls[@]} controls caught by the goldens only"

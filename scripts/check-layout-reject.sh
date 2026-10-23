#!/usr/bin/env bash
# The reject tests of the closure classes' check (`Backend2/LayoutCheck.lean`, docs/compiler.md
# §5.2). On each program below, `bcc lir --layout-reject` checks the layouts and the closure flow
# as computed, which must be accepted, and then each perturbation of them, each aimed at one family
# of the checks (`LayCheck.perturbLayouts`, `LayCheck.perturbFlow`). No perturbation may be
# accepted, and each must be refused, on at least one program, by its own family's refusal: the
# message fragment the table below gives it.
#
#     scripts/check-layout-reject.sh
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc >/dev/null
bcc=.lake/build/bin/bcc
# Programs chosen so that every perturbation has a target in one of them: closure classes of
# several codes and widths, recursive types with boxed fields, a class kept on the heap, cells, and
# §52's stack machines (`async-stack-pause`: a κ region and a machine's frames).
progs=(
  corpus/aff-higher.bc
  corpus/deep-list.bc
  corpus/data-box-tree.bc
  corpus/sched-a.bc
  corpus/async-scheduler.bc
  corpus/async-stack-deep.bc
  corpus/async-stack-pause.bc
)
# Each perturbation, and the refusal of its family (an extended regular expression).
families=(
  "drop a code from its class|do not hold c[0-9]+"
  "drop a code's class|'s class is none"
  "merge two classes of one shape and different widths|has width [0-9]+, its children give"
  "change a class's width|has width [0-9]+, its children give"
  "call a class trivial|has triviality true, its children give false"
  "move a code's environment node|code c[0-9]+: f[0-9]+'s captured parameter"
  "move a code's argument node|code c[0-9]+: f[0-9]+'s argument"
  "move a code's answer node|code c[0-9]+: f[0-9]+'s answer"
  "unbox a boxed field|a cycle with no box"
  "keep a heap class's environment inline|a cycle with no box"
  "shrink a cell|cell has [0-9]+ words, its contents node"
  "give a slot the wrong width|-byte slot, its contents"
  "give one cell two sizes|one cell is seen at pointer nodes"
  "move a κ region's node|its κ region"
  "move a machine's frame node at one access|machine [0-9]+'s frame"
  "move a reborrowed read's node|a read through a shared borrow of contents"
  "split a variable's node from the places it is joined with|which are not joined|is not a layout of"
  "drop a code from a variable's flow set|whose set does not hold|which its set does not"
  "drop a code from a call's answer|'s answer: code c[0-9]+ reaches"
  "a direct call where several codes reach|a direct call of x[0-9]+ at code"
)
fail=0
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
: > "$tmp/all"
for f in "${progs[@]}"; do
  if [ ! -f "$f" ]; then echo "$f: missing"; fail=1; continue; fi
  if ! "$bcc" lir --layout-reject "$f" > "$tmp/out" 2>&1; then
    echo "$f: $(head -3 "$tmp/out")"; fail=1; continue
  fi
  if ! head -1 "$tmp/out" | grep -q '^accepted:'; then
    echo "$f: the layouts as computed are not accepted: $(head -1 "$tmp/out")"; fail=1
  fi
  if grep '^ACCEPTED:' "$tmp/out"; then
    echo "$f: a perturbation the checks let through (above)"; fail=1
  fi
  grep '^refused:' "$tmp/out" >> "$tmp/all"
  echo "$f: $(grep -c '^refused:' "$tmp/out") refused, $(grep -c '^n/a:' "$tmp/out") not applicable"
done
# Every perturbation is one of the table's, and is refused somewhere by its family's refusal.
sed -En "s/^(refused|n\/a|ACCEPTED): ([^:]*).*/\2/p" "$tmp/out" | sort -u > "$tmp/names"
printf '%s\n' "${families[@]}" | cut -d'|' -f1 | sort -u > "$tmp/known"
if ! cmp -s "$tmp/names" "$tmp/known"; then
  echo "the perturbations and the table differ:"; diff "$tmp/known" "$tmp/names" || true; fail=1
fi
for fam in "${families[@]}"; do
  name=${fam%%|*}; re=${fam#*|}
  if ! grep -F "refused: $name: " "$tmp/all" | grep -Eq -e "$re"; then
    echo "perturbation \"$name\" was not refused by its family's refusal ($re) on any program"; fail=1
  fi
done
[ "$fail" = 0 ] && echo "layout reject tests: every perturbation refused, each by its family's check"
exit "$fail"

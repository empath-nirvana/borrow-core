#!/usr/bin/env bash
# The reject tests of the closure classes' check (`Backend2/LayoutCheck.lean`, docs/compiler.md
# §5.2). On each program below, `bcc lir --layout-reject` checks the layouts and the closure flow
# as computed, which must be accepted, and then each perturbation of them (a code dropped from its
# class, two classes of different widths merged, a width changed, a boxed field unboxed, a heap
# class kept inline, a cell shrunk, a variable's node split from its places, a code dropped from a
# flow set, a direct call where several codes reach), each of which must be refused. Every
# perturbation must have been applied, and refused, on at least one program.
#
#     scripts/check-layout-reject.sh
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc >/dev/null
bcc=.lake/build/bin/bcc
# Programs chosen so that every perturbation has a target in one of them: closure classes of
# several codes and widths, recursive types with boxed fields, a class kept on the heap, cells.
progs=(
  corpus/aff-higher.bc
  corpus/deep-list.bc
  corpus/data-box-tree.bc
  corpus/sched-a.bc
  corpus/async-scheduler.bc
)
fail=0
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
: > "$tmp/refused"
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
  grep '^refused:' "$tmp/out" | sed 's/^refused: \([^:]*\):.*/\1/' >> "$tmp/refused"
  echo "$f: $(grep -c '^refused:' "$tmp/out") refused, $(grep -c '^n/a:' "$tmp/out") not applicable"
done
# Every perturbation, refused somewhere.
"$bcc" lir --layout-reject "${progs[0]}" | sed -En "s/^(refused|n\/a|ACCEPTED): ([^:]*).*/\2/p" > "$tmp/all"
while IFS= read -r name; do
  if ! grep -qxF "$name" "$tmp/refused"; then
    echo "perturbation \"$name\" was not refused on any program (no target?)"; fail=1
  fi
done < "$tmp/all"
[ "$fail" = 0 ] && echo "layout reject tests: every perturbation refused"
exit "$fail"

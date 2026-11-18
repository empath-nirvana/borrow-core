#!/usr/bin/env bash
# The checker's cell classes against the layout types' cell widths (SPEC §5). For every corpus
# program that checks, `bcc-counts --cells` compares the classes the checker carries
# (`Checked.cells`: every type a cell allocated at a type may hold) with the widths
# `Backend/Clos/Types.lean` gives each allocation's cell, and prints a row when either side has a
# cell wider than the value it is allocated with, or a class holds a type whose width its type does
# not give (a closure). The table, disagreements included, is pinned in corpus/cells.expected, so a
# change to either side shows here.
#
#     scripts/check-cells.sh            compare with corpus/cells.expected
#     scripts/check-cells.sh --write    write it
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc-counts >/dev/null
counts=.lake/build/bin/bcc-counts
row() {
  local f=$1 r
  r=$("$counts" --cells "$f" 2>/dev/null) || { echo "$f: FAILS: bcc-counts --cells"; return 1; }
  [ -z "$r" ] || printf '%s: %s\n' "$f" "$r"
}
. scripts/par.sh
export counts
export -f row
# The working tree's corpus programs and sugar files (`scripts/corpus-set.sh programs sugar`), as
# the other gate steps read them: a program not yet committed is in the table too. A file marked
# `-- check: parse-only`, one with no `main`, and one marked `-- check: old-backend-refuses` (the
# layout side is the old backend's, which does not lower it) are skipped, as pinned in
# `corpus/skips.expected`.
list=$(scripts/corpus-set.sh programs sugar | sort)
fs=()
skips=$(mktemp)
for f in $list; do
  if grep -q '^-- check: parse-only' "$f"; then echo "parse-only $f" >> "$skips"
  elif ! grep -q '^main' "$f"; then echo "no-main $f" >> "$skips"
  elif grep -q '^-- check: old-backend-refuses' "$f"; then echo "old-backend-refuses $f" >> "$skips"
  else fs+=("$f"); fi
done
skipped=$(scripts/corpus-set.sh --skips check-cells parse-only no-main old-backend-refuses < "$skips") || { rm -f "$skips"; echo "$skipped"; exit 1; }
rm -f "$skips"
echo "$skipped"
# The table; a file the tool fails on is a line `<file>: FAILS: <tool>`, which fails the step.
table() {
  local t; t=$(mktemp)
  par row "${fs[@]}" > "$t"
  if grep ': FAILS: ' "$t" >&2; then rm -f "$t"; echo "check-cells: the table could not be made for the files above" >&2; return 1; fi
  cat "$t"; rm -f "$t"
}
summary() { echo "$(wc -l < "$1" | tr -d ' ') programs, $(grep -c '; disagree$' "$1" || true) disagreements"; }
if [ "${1:-}" = "--write" ]; then
  t=$(mktemp); table > "$t"; cat "$t" > corpus/cells.expected; rm -f "$t"
  echo "corpus/cells.expected: $(summary corpus/cells.expected)"
  exit 0
fi
got=$(mktemp); trap 'rm -f "$got"' EXIT
table > "$got"
if ! diff -u corpus/cells.expected "$got"; then
  echo "check-cells: the checker's cell classes or the layout types' widths changed (corpus/cells.expected)"
  exit 1
fi
echo "check-cells: $(summary corpus/cells.expected) as pinned"

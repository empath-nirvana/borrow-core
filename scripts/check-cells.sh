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
  r=$("$counts" --cells "$f" 2>/dev/null) || return 0
  [ -z "$r" ] || printf '%s: %s\n' "$f" "$r"
}
. scripts/par.sh
export counts
export -f row
table() {
  local fs=()
  while read -r f; do
    grep -q '^-- check: parse-only' "$f" || fs+=("$f")
  done < <(git ls-files 'corpus/*.bc' | grep -v '^corpus/\(reject\|pending\|fail\)/' | sort)
  par row "${fs[@]}"
}
summary() { echo "$(wc -l < "$1" | tr -d ' ') programs, $(grep -c '; disagree$' "$1" || true) disagreements"; }
if [ "${1:-}" = "--write" ]; then
  table > corpus/cells.expected
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

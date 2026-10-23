#!/usr/bin/env bash
# The grade census (SPEC §53). For every corpus program that checks, each `handle` node's
# operations as `bcc grades` prints them: the count (`0`, `1`, `1?`), how it is fixed (inferred,
# declared `linear ctl`, or written in a core row), the node and the reason that pin a `1?`, the
# world, the clause's position and where `κ` is kept. The table is pinned in corpus/grades.expected,
# so a count that rises (`1` to `1?`), a position that moves (`tail` to `once` to `stored`) or a new
# storage shows here, with the reason the census gives.
#
# Checked besides the pin:
#   * no count is `ω`, nor any qualifier `unr`: an unrestricted continuation is not a type;
#   * every inferred `1?` names the node and the reason that pin it.
#
#     scripts/check-grades.sh            compare with corpus/grades.expected
#     scripts/check-grades.sh --write    write it
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc >/dev/null
bcc=.lake/build/bin/bcc
row() {
  local f=$1 g
  g=$("$bcc" grades "$f" 2>/dev/null) || return 0
  [ -n "$g" ] || return 0
  printf '%s\n' "$g" | sed "s|^|$f |"
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
summary() {
  # Totals per count, per how it is fixed, and the `1?` operations pinned by inference.
  awk '
    {
      line = $0; sub(/^[^:]*:[^:]*: handle [0-9]+: /, "", line)
      m = split(line, ops, "; ")
      for (j = 1; j <= m; j++) {
        split(ops[j], w, " ")
        c = w[2]; s = w[3]; sub(/,$/, "", s)
        n[c]++; src[c " " s]++
        if (c == "1?" && ops[j] ~ /pinned at/) pinned++
      }
    }
    END {
      printf "check-grades: %d sites; count 0: %d, 1: %d, 1?: %d", NR, n["0"], n["1"], n["1?"]
      printf " (0 inferred %d, abortive %d; 1 inferred %d, declared %d, written %d;",
        src["0 inferred"], src["0 abortive"], src["1 inferred"], src["1 declared"], src["1 written"]
      printf " 1? inferred %d, written %d, pinned %d)\n", src["1? inferred"], src["1? written"], pinned
    }' "$1"
}
tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT
table > "$tmp"
bad=0
if grep -n 'ω\|\bunr\b' "$tmp"; then
  echo "check-grades: an unrestricted count or qualifier above"; bad=1
fi
if awk '{ line = $0; sub(/^[^:]*:[^:]*: handle [0-9]+: /, "", line); m = split(line, ops, "; ")
          for (j = 1; j <= m; j++) if (ops[j] ~ / 1\? inferred/ && ops[j] !~ /pinned at/) { print FILENAME ": " $0; f = 1 } }
        END { exit !f }' "$tmp"; then
  echo "check-grades: an inferred 1? above with no node that pins it"; bad=1
fi
if [ "${1:-}" = "--write" ]; then
  cp "$tmp" corpus/grades.expected
  summary corpus/grades.expected
  exit $bad
fi
if ! diff -u corpus/grades.expected "$tmp"; then
  echo "check-grades: the grade census changed (corpus/grades.expected)"
  bad=1
fi
summary "$tmp"
exit $bad

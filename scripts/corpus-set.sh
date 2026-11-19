#!/usr/bin/env bash
# The corpus's files, by class: every step that runs corpus programs takes its files from here, so
# no program is renamed, tabled or checked by one step and left unrun by another.
#
#     scripts/corpus-set.sh [CLASS…]
#
# prints the files of the classes named (default `programs`), one per line, in byte order:
#
#     programs  every `corpus/**/*.bc`, at any depth, outside `corpus/{reject,pending,fail,sugar}/`
#     reject, pending, fail, sugar
#               every `.bc` under that directory, at any depth
#     all       every `corpus/**/*.bc`
#
# A step does not run every program it is given: a program marked `-- check: parse-only` is for
# the parser, one with no `main` is a library, and one outside the new backend's fragment cannot
# be compiled by it. Each such skip is pinned, with its reason, in `corpus/skips.expected`
# (`reason file`, one per line). A step collects the skips it made as `reason file` lines and ends
# with
#
#     scripts/corpus-set.sh --skips STEP REASON… < its-skips
#
# which prints the count of each reason and its files, and fails unless the skips of those
# reasons are exactly the pinned ones: a new skip is listed there, or it fails the step.
set -euo pipefail
cd "$(dirname "$0")/.."
export LC_ALL=C
pinned=corpus/skips.expected

if [ "${1:-}" = --skips ]; then
  [ $# -ge 3 ] || { echo "usage: scripts/corpus-set.sh --skips STEP REASON… < skips"; exit 2; }
  step=$2; shift 2
  tmp=$(mktemp -d)
  trap 'rm -rf "$tmp"' EXIT
  sort -u > "$tmp/got"
  : > "$tmp/want"
  [ -f "$pinned" ] && grep -v '^#' "$pinned" | grep . | sort -u > "$tmp/pinned" || : > "$tmp/pinned"
  for r in "$@"; do
    awk -v r="$r" '$1 == r' "$tmp/pinned" >> "$tmp/want"
    n=$(awk -v r="$r" '$1 == r' "$tmp/got" | wc -l | tr -d ' ')
    echo "$step: $n skipped: $r$([ "$n" = 0 ] || printf ': %s' "$(awk -v r="$r" '$1 == r { printf "%s%s", s, $2; s = " " }' "$tmp/got")")"
  done
  awk 'NR == FNR { ok[$1] = 1; next } !($1 in ok)' <(printf '%s\n' "$@") "$tmp/got" > "$tmp/other"
  if [ -s "$tmp/other" ]; then
    echo "$step: skips of a reason it does not name:"; sed 's/^/  /' "$tmp/other"; exit 1
  fi
  sort -u "$tmp/want" -o "$tmp/want"
  if ! cmp -s "$tmp/want" "$tmp/got"; then
    echo "$step: the skips differ from $pinned (< pinned, > this run):"
    diff "$tmp/want" "$tmp/got" | grep '^[<>]' | sed 's/^/  /' || true
    exit 1
  fi
  exit 0
fi

[ $# -gt 0 ] || set -- programs
for c in "$@"; do
  case "$c" in
    programs|reject|pending|fail|sugar|all) ;;
    *) echo "scripts/corpus-set.sh: no class $c (programs, reject, pending, fail, sugar, all)" >&2; exit 2 ;;
  esac
done
classes=" $* "
# `corpus/.respell-old/` holds the twins in today's spelling of the files respelled (SPEC §82,
# scripts/check-respell.sh): not programs of the corpus.
find corpus -path corpus/.respell-old -prune -o -name '*.bc' -type f -print | sort | while IFS= read -r f; do
  case "$f" in
    corpus/reject/*) c=reject ;; corpus/pending/*) c=pending ;;
    corpus/fail/*) c=fail ;; corpus/sugar/*) c=sugar ;;
    *) c=programs ;;
  esac
  case "$classes" in *" $c "*|*" all "*) echo "$f" ;; esac
done

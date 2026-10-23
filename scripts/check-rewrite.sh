#!/usr/bin/env bash
# The Core → Core rewriter's step 0, the identity (SPEC §54, #680): for every corpus program that
# checks and has a `main`, the program read back from its typed term and checked again
# (`bcc rewrite --identity`). Its line: the instances of `def`s read back, the declarations and
# the lifetime-polymorphic ones among them, the uses; the rewritten `main`'s erasure against the
# source's (`same`, or `beta`: other only at the instantiations of polymorphic declarations, the
# typed terms agreeing everywhere else); the LIR of the rewritten program against the source's,
# byte for byte (`same`; `outside` when both are outside the new backend's fragment with one
# message; `differs`); and the typed terms' mismatches, node by node and field by field modulo
# spans, by node kind and field (`poly:` inside a polymorphic declaration's body).
#
# The gate: every line has `erasure same` or `beta` and `lir same` or `outside`; and the table,
# mismatches included, is pinned in corpus/rewrite.expected, so a change shows here.
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
bad=$(awk '!/ erasure (same|beta) / || !/ lir (same|outside) / { print }' "$out")
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
[ "$fail" = 0 ] || exit 1
echo "check-rewrite: $(wc -l < "$out" | tr -d " ") programs read back and checked again: every erasure and every LIR the source's (up to the instantiations of polymorphic declarations), as pinned"

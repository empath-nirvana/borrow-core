#!/usr/bin/env bash
# `own` (SPEC §54) on the pure corpus. Every corpus program that checks (not the parse-only ones)
# is given to `lowering-check` (`scripts/LoweringCheck.lean`): a program with no capability whose
# typed term is in the pure fragment (`Lowering.pureT`) has its masks decided to agree with its
# leaves (`Lowering.agreeAt`, a theorem: `agreeAt_of_typed`), `own`'s output decided low
# (`Lowering.lowB`), and `own`'s output run by the source interpreter to the erasure's report.
# The programs in the fragment are pinned in corpus/lowering.expected, so a program that leaves or
# joins the fragment shows here.
#
#     scripts/check-lowering.sh            check, and compare the fragment with the pinned list
#     scripts/check-lowering.sh --write    write the list
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build lowering-check >/dev/null
files=()
while read -r f; do
  grep -q '^-- check: parse-only' "$f" || files+=("$f")
done < <(git ls-files 'corpus/*.bc' | grep -v '^corpus/\(reject\|pending\|fail\)/' | sort)
out=$(mktemp); got=$(mktemp); trap 'rm -f "$out" "$got"' EXIT
status=0
.lake/build/bin/lowering-check "${files[@]}" > "$out" || status=$?
grep '^ok ' "$out" | sed -E 's/^ok ([^:]*):.*/\1/' > "$got"
if [ "$status" != 0 ]; then
  grep -A2 '^FAIL' "$out"
  tail -1 "$out"
  exit 1
fi
if [ "${1:-}" = "--write" ]; then
  cp "$got" corpus/lowering.expected
  echo "corpus/lowering.expected: $(wc -l < "$got" | tr -d ' ') programs in the pure fragment"
  exit 0
fi
if ! diff -u corpus/lowering.expected "$got"; then
  echo "check-lowering: the programs in the pure fragment changed (corpus/lowering.expected)"
  exit 1
fi
tail -1 "$out"

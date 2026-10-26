#!/usr/bin/env bash
# R5's admission, report only (SPEC §54, R5-0; #680): for every corpus program that checks and
# has a `main`, each `handle` node with an operation R0 does not rewrite, the form R5 gives it
# (`bcc rewrite --admission`): `R5 opt`, `R5 fallback (<conjuncts>)` at a stored node, or
# `left: <conjunct>`, with what the admission read (points, in-clause `tail` performs, the
# region's shape, suspending calls, `Env_N`'s slots, `U` slots of a boxed state, whether R0
# forwards through the node, inner nodes of its name, the pins of its `lendR`s, its open forces,
# its other gaps). Nothing is rewritten.
#
# The gate: the table is pinned in corpus/admission.expected; every `left` reason is one of the
# R5 scope's (§3.C, §5); a node left at `lendR` names its pin position (S-R5-22).
#
#     scripts/check-admission.sh            compare with corpus/admission.expected
#     scripts/check-admission.sh --write    write it
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc >/dev/null
bcc=.lake/build/bin/bcc
row() {
  local f=$1 l
  grep -q '^main' "$f" || return 0
  "$bcc" check "$f" >/dev/null 2>&1 || return 0
  if ! l=$("$bcc" rewrite --admission "$f" 2>&1); then
    echo "$f error: $(printf '%s' "$l" | head -c 300 | tr '\n' ' ')"
    return 0
  fi
  [ -z "$l" ] || printf '%s\n' "$l" | sed "s|^|$f |"
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
# The reasons the scope names: the gaps of §3.C, the crossing conjunct, the sibling rows of §5
# (a node with no stored operation), R0's left abortive names.
bad=$(awk '
  / error: / { print; next }
  {
    i = index($0, " left: "); if (i == 0) next
    r = substr($0, i + 7); sub(/ \| .*/, "", r)
    if (r ~ /^lendR \(T1, PinLaw\.stop at [0-9]+:[0-9]+\)$/) { if ($0 !~ / pins \[/) print; next }
    if (r ~ /^codata at row n \(#691, at [0-9]+:[0-9]+\)$/) next
    if (r == "answer types differ at n (#692)") next
    if (r ~ /^div region \(.*\)$/) next
    if (r ~ /^state does not outlive d \(slot [^)]*\)$/) next
    if (r == "a finaliser that performs") next
    if (r ~ /^perform path crosses handler [0-9]+ \(.*, in Backend2\)$/) next
    if (r ~ /^(R1|R1-ev|R1σ|R2|R2σ|R3|R0 left)(, (R1σ|R2|R2σ|R3))*$/) next
    print
  }' "$out")
if [ "${1:-}" = "--write" ]; then
  cp "$out" corpus/admission.expected
  echo "corpus/admission.expected: $(wc -l < corpus/admission.expected | tr -d " ") nodes"
  [ -z "$bad" ] || { echo "check-admission: a reason not in the scope's list:"; printf '%s\n' "$bad"; exit 1; }
  exit 0
fi
fail=0
if [ -n "$bad" ]; then
  echo "check-admission: a reason not in the scope's list, or a lendR node without its pin:"
  printf '%s\n' "$bad"; fail=1
fi
if ! diff -u corpus/admission.expected "$out"; then
  echo "check-admission: R5's admission changed (corpus/admission.expected)"; fail=1
fi
[ "$fail" = 0 ] || exit 1
stored=$(grep -c ' | points ' "$out" || true)
echo "check-admission: $(wc -l < "$out" | tr -d " ") nodes as pinned, $stored of them stored: $(grep -c ' R5 opt ' "$out" || true) opt, $(grep -c ' R5 fallback ' "$out" || true) fallback, $((stored - $(grep -c ' R5 opt \| R5 fallback ' "$out" || true))) left; every left reason one of the scope's"

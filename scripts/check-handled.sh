#!/usr/bin/env bash
# The names handled inside each handled computation, and condition 2 of the direct call of a
# tail-resumptive clause (SPEC §19, *The clause's names in the continuation*). For every corpus
# program that checks: `main`'s flow record and its frames (`bcc handled`); each `handle` node of
# `main` with the frames its handled computation holds (`inside`), its outer row's names and
# whether condition 2 holds for its clauses (no name of the row is one the flow record may catch,
# `Checked.unhandledIn`); and each operation the backend lowers (`bcc-counts --lowering`), with
# the kinds of its clauses and whether condition 2 holds at every `handle` node of its name.
#
# A `direct` call of a clause assumes condition 2: the backend's own premise is stronger (the
# clause neither suspends nor raises). The two agree at a direct call when condition 2 holds at
# every node of the name; a direct call where it does not is marked `disagree`, and rests on the
# backend's premise alone. Any other lowering makes no direct call (`-`). The table, disagreements
# included, is pinned in corpus/handled.expected.
#
#     scripts/check-handled.sh            compare with corpus/handled.expected
#     scripts/check-handled.sh --write    write it
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc bcc-counts >/dev/null
bcc=.lake/build/bin/bcc
counts=.lake/build/bin/bcc-counts
row() {
  local f=$1 h l
  h=$("$bcc" handled "$f" 2>/dev/null) || return 0
  [ -n "$h" ] || return 0
  l=$("$counts" --lowering "$f" 2>&1) || l="error: $l"
  awk -v f="$f" '
    FNR == NR {
      if ($0 ~ /^error/) { err = $0; next }
      key = $0; sub(/ .*/, "", key)
      v = $0; sub(/^[^ ]* /, "", v)
      be[key] = v
      next
    }
    /^flows / { print f " " $0; next }
    {
      print f " " $0
      n = $0; sub(/^[^:]*:[^:]*: handle /, "", n); sub(/:.*/, "", n)
      c2 = ($0 ~ /; condition 2 holds$/) ? 1 : 0
      if (!(n in hold)) hold[n] = 1
      if (!c2) hold[n] = 0
      ops = $0; sub(/.*; ops /, "", ops); sub(/; names .*/, "", ops)
      m = split(ops, os, ", ")
      for (j = 1; j <= m; j++) {
        split(os[j], w, " ")
        key = w[1]; kind = w[2]
        if (!(key in seen)) { order[++no] = key; seen[key] = 1; nm[key] = n }
        if (index("," kinds[key] ",", "," kind ",") == 0)
          kinds[key] = (kinds[key] == "" ? kind : kinds[key] "," kind)
      }
    }
    END {
      for (j = 1; j <= no; j++) {
        key = order[j]
        b = (key in be) ? be[key] : (err != "" ? err : "-")
        lo = b; sub(/:.*/, "", lo)
        c = hold[nm[key]] ? "condition 2 holds" : "condition 2 fails"
        if (lo == "direct") verdict = (hold[nm[key]] ? "agree" : "disagree")
        else verdict = "-"
        printf "%s %s %s: %s; %s; %s\n", f, key, kinds[key], lo, c, verdict
      }
    }' <(printf '%s\n' "$l") <(printf '%s\n' "$h")
}
. scripts/par.sh
export bcc counts
export -f row
table() {
  local fs=()
  while read -r f; do
    grep -q '^-- check: parse-only' "$f" || fs+=("$f")
  done < <(git ls-files 'corpus/*.bc' | grep -v '^corpus/\(reject\|pending\|fail\)/' | sort)
  par row "${fs[@]}"
}
summary() {
  local t=$1
  echo "$(grep -c ': handle ' "$t") handle nodes, $(grep -c '; agree$' "$t") direct calls where condition 2 holds, $(grep -c '; disagree$' "$t") where it does not"
}
if [ "${1:-}" = "--write" ]; then
  table > corpus/handled.expected
  echo "corpus/handled.expected: $(summary corpus/handled.expected)"
  exit 0
fi
if ! diff -u corpus/handled.expected <(table); then
  echo "check-handled: the records at [handle] or the backend's lowering changed (corpus/handled.expected)"
  exit 1
fi
echo "check-handled: $(summary corpus/handled.expected) as pinned"

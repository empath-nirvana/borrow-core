#!/usr/bin/env bash
# The checker's clause kinds against the backend's lowering (SPEC §19, *Clause kinds*). For every
# corpus program that checks, each operation `n.i` of a handler: the kinds the checker gives its
# clause at the handlers of the name `n` (`bcc kinds`), and what the backend makes of the
# operation today (`bcc-counts --lowering`): a direct call of the clause (`direct`), a suspension
# driven by its handler's machine (`machine`, with the backend's reason), a branch per call
# (`branch`), or nothing, when the program never performs it (`-`).
#
# The two agree when
#   abortive                  ↔ branch
#   tail at every handler     ↔ direct
#   any other kind somewhere  ↔ machine
# A `direct` where a handler's kind is not `tail` lowers a clause whose premise does not hold; a
# `machine` where every kind is `tail` is a direct call the backend does not make. Each such row is
# marked `disagree`. The table, disagreements included, is pinned in corpus/kinds.expected, so a
# change to either side shows here.
#
#     scripts/check-kinds.sh            compare with corpus/kinds.expected
#     scripts/check-kinds.sh --write    write it
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc bcc-counts >/dev/null
bcc=.lake/build/bin/bcc
counts=.lake/build/bin/bcc-counts
row() {
  local f=$1 k l
  k=$("$bcc" kinds "$f" 2>/dev/null) || return 0
  [ -n "$k" ] || return 0
  l=$("$counts" --lowering "$f" 2>&1) || l="error: $l"
  awk -v f="$f" '
    FNR == NR {
      if ($0 ~ /^error/) { err = $0; next }
      key = $0; sub(/ .*/, "", key)
      v = $0; sub(/^[^ ]* /, "", v)
      be[key] = v
      next
    }
    {
      line = $0; sub(/^[^:]*:[^:]*: handle [0-9]+( \(boxed κ\))?: /, "", line)
      m = split(line, ops, "; ")
      for (j = 1; j <= m; j++) {
        split(ops[j], w, " ")
        key = w[1]; kind = w[3]
        if (!(key in seen)) { order[++no] = key; seen[key] = 1; q[key] = w[2] }
        if (index("," kinds[key] ",", "," kind ",") == 0)
          kinds[key] = (kinds[key] == "" ? kind : kinds[key] "," kind)
      }
    }
    END {
      for (j = 1; j <= no; j++) {
        key = order[j]; ks = kinds[key]
        b = (key in be) ? be[key] : (err != "" ? err : "-")
        lo = b; sub(/:.*/, "", lo)
        alltail = (ks == "tail")
        abort = (ks == "abortive")
        if (lo == "-") verdict = "agree"
        else if (abort) verdict = (lo == "branch" ? "agree" : "disagree")
        else if (lo == "direct") verdict = (alltail ? "agree" : "disagree")
        else if (lo == "machine") verdict = (alltail ? "disagree" : "agree")
        else verdict = "disagree"
        printf "%s %s %s %s: %s; %s\n", f, key, q[key], ks, b, verdict
      }
    }' <(printf '%s\n' "$l") <(printf '%s\n' "$k")
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
if [ "${1:-}" = "--write" ]; then
  table > corpus/kinds.expected
  echo "corpus/kinds.expected: $(wc -l < corpus/kinds.expected) operations, $(grep -c '; disagree$' corpus/kinds.expected || true) disagreements"
  exit 0
fi
if ! diff -u corpus/kinds.expected <(table); then
  echo "check-kinds: the clause kinds or the backend's lowering changed (corpus/kinds.expected)"
  exit 1
fi
echo "check-kinds: $(wc -l < corpus/kinds.expected) operations as pinned, $(grep -c '; disagree$' corpus/kinds.expected || true) disagreements"

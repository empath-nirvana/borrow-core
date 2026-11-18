#!/usr/bin/env bash
# Parse the corpus with `bcc parse`. Every corpus program (`scripts/corpus-set.sh`) must parse and
# survive the print/re-parse round trip; every `corpus/fail/` file must be rejected with the
# message on its `-- expect:` line.
# (`corpus/pending/` is checked by `check-corpus.sh`.)
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc >/dev/null
bcc=.lake/build/bin/bcc
bad=0
list=$(scripts/corpus-set.sh)
progs=(); while IFS= read -r f; do [ -z "$f" ] || progs+=("$f"); done <<< "$list"
list=$(scripts/corpus-set.sh fail)
fails=(); while IFS= read -r f; do [ -z "$f" ] || fails+=("$f"); done <<< "$list"
for f in "${progs[@]}"; do
  if ! "$bcc" parse "$f"; then bad=$((bad + 1)); fi
done
for f in ${fails[@]+"${fails[@]}"}; do
  want=$(sed -n '/^-- expect: /{s///p;q;}' "$f")
  if out=$("$bcc" parse "$f" 2>&1); then
    echo "$f: accepted, but must fail"; bad=$((bad + 1))
  elif [ "$out" != "$f:$want" ]; then
    echo "$f: wrong error"; echo "  want: $want"; echo "  got:  ${out#"$f:"}"; bad=$((bad + 1))
  else
    echo "$f: rejected as expected"
  fi
done
echo "$bad failure(s)."
[ "$bad" -eq 0 ]

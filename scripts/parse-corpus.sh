#!/usr/bin/env bash
# Parse the corpus with `bcc parse`. Every corpus program (`scripts/corpus-set.sh`) must parse and
# survive the print/re-parse round trip; every `corpus/fail/` file must be rejected with the
# message on its `-- expect:` line.
# (`corpus/pending/` is checked by `check-corpus.sh`.)
#
#     scripts/parse-corpus.sh [file.bc…]   every file above, or only the files named (a
#                                          `corpus/fail/` file must be rejected, any other parse)
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc >/dev/null
export GATE_CACHE_BUILT=1  # the binaries the result cache may key on are this build's
. scripts/par.sh
export bcc=.lake/build/bin/bcc
parses() { "$bcc" parse "$1"; }
fails() {
  set -e
  local f=$1 want out
  want=$(sed -nE '/^(--|#) expect: /{s///p;q;}' "$f")
  if out=$("$bcc" parse "$f" 2>&1); then
    echo "$f: accepted, but must fail"; return 1
  elif [ "$out" != "$f:$want" ]; then
    echo "$f: wrong error"; echo "  want: $want"; echo "  got:  ${out#"$f:"}"; return 1
  else
    echo "$f: rejected as expected"
  fi
}
export -f parses fails
# Each file is a unit of the result cache (scripts/par.sh), in a slot of the job pool; reported in
# order.
export PAR_CACHE=parse-corpus
if [ $# -gt 0 ]; then
  progs=(); fails=()
  for f in "$@"; do
    [ -f "$f" ] || { echo "$f: no such file"; exit 2; }
    case "$f" in corpus/fail/*) fails+=("$f") ;; *) progs+=("$f") ;; esac
  done
else
  list=$(scripts/corpus-set.sh)
  progs=(); while IFS= read -r f; do [ -z "$f" ] || progs+=("$f"); done <<< "$list"
  list=$(scripts/corpus-set.sh fail)
  fails=(); while IFS= read -r f; do [ -z "$f" ] || fails+=("$f"); done <<< "$list"
fi
par parses ${progs[@]+"${progs[@]}"}
bad=$par_failed
par fails ${fails[@]+"${fails[@]}"}
bad=$((bad + par_failed))
echo "$bad failure(s)."
[ "$bad" -eq 0 ]

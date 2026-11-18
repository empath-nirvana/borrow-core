#!/usr/bin/env bash
# Type-check the corpus with `bcc check`. Every corpus program (`scripts/corpus-set.sh`) must check,
# except a file marked `-- check: parse-only` (it is for the parser; the skips are pinned in
# `corpus/skips.expected`); every `corpus/reject/` file must parse and be rejected by the checker
# with the message on its `-- expect:` line (`line:col: message`), continued by any `-- expect| `
# lines for a message of several lines. A reject marked `-- check: proved-only` must check, and be
# rejected by `bcc check --proved-only` (SPEC §29). A message at a position inside an included
# library module names the module's file instead (`lib/m.bc:line:col: message`, #883).
#
# Reports. For every corpus/reports/<name>.txt, the effects lines `bcc check corpus/<name>.bc` prints
# (`effect`, `row`, `lowering`, `call`: SPEC §18) must be exactly that file: the rows, the lowering
# shape of each handler and each call site's elaboration are pinned.
#
# The trusted base. For every corpus/trusted/<name>.txt, what `bcc trusted corpus/<name>.bc` prints
# (the externs `main` reaches, with their contracts and host implementations: SPEC §11, §34) must
# be exactly that file.
#
# Derived copies. For every corpus/copies/<name>.txt, what `bcc copies corpus/<name>.bc` prints (each
# copy of an `imm` borrow the checker inserted: its source, the variable and its type, SPEC §12)
# must be exactly that file.
#
# Pending programs. Every `corpus/pending/*.bc` is a program we cannot write yet, named by its
# `-- pending: <issue or limit>` line. It is an expected failure: `bcc check` (which parses first)
# must reject it with the message on its `-- now:` line, continued by `-- now| ` lines, so the
# failure it documents is the current one (a position in a library module naming its file, as for
# a reject). When a pending program checks, the feature it waits for has landed: the gate fails
# and says to move it into the corpus with its golden output.
#
#     scripts/check-corpus.sh [file…]
#
# checks every file above, or only the files named, each as its directory says (a corpus program
# with its reports file, if it has one; a `corpus/reject/`, `corpus/pending/` or `corpus/reports/`
# file).
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc >/dev/null
export GATE_CACHE_BUILT=1  # the binaries the result cache may key on are this build's
. scripts/par.sh
export bcc=.lake/build/bin/bcc
# A unit's skip lines are a side file (`skips`, scripts/par.sh), gathered in $skipdir.
export skipdir; skipdir=$(mktemp -d)
trap 'rm -rf "$skipdir"' EXIT
export PAR_COLLECT=$skipdir
: > "$skipdir/skips"
bad=0
checks() {
  local f=$1 out
  if grep -q '^-- check: parse-only' "$f"; then
    echo "$f: parse-only, skipped"; echo "parse-only $f" >> "$PAR_SIDE/skips"; return 0
  fi
  if out=$("$bcc" check "$f" 2>&1); then
    echo "$f: checks"
  else
    echo "$f: rejected, but must check"; echo "  $out"; return 1
  fi
}
rejects() {
  local f=$1 want out flag
  want=$(sed -n 's/^-- expect: //p; s/^-- expect| //p' "$f")
  flag=; grep -q '^-- check: proved-only' "$f" && flag=--proved-only
  if ! "$bcc" parse "$f" >/dev/null 2>&1; then
    echo "$f: does not parse, so it does not test the checker"; return 1
  elif [ -n "$flag" ] && ! out=$("$bcc" check "$f" 2>&1); then
    echo "$f: rejected without --proved-only, but must check"; echo "  $out"; return 1
  elif out=$("$bcc" check $flag "$f" 2>&1); then
    echo "$f: accepted, but must be rejected"; return 1
  elif [ "$out" != "$f:$want" ] && { [ "${want#lib/}" = "$want" ] || [ "$out" != "$want" ]; }; then
    echo "$f: wrong error"; echo "  want: $want"; echo "  got:  ${out#"$f:"}"; return 1
  else
    echo "$f: rejected as expected"
  fi
}
reports() {
  local g=$1 f
  f=corpus/$(basename "${g%.txt}").bc
  if ! diff -u "$g" <("$bcc" check "$f" 2>&1 | grep -E '^(effect|row|lowering|call) '); then
    echo "$g: the reports differ"; return 1
  else echo "$g: reports match"; fi
}
trusted() {
  local g=$1 f
  f=corpus/$(basename "${g%.txt}").bc
  if ! diff -u "$g" <("$bcc" trusted "$f" 2>&1); then
    echo "$g: the trusted base differs"; return 1
  else echo "$g: trusted base matches"; fi
}
copies() {
  local g=$1 f
  f=corpus/$(basename "${g%.txt}").bc
  if ! diff -u "$g" <("$bcc" copies "$f" 2>&1); then
    echo "$g: the derived copies differ"; return 1
  else echo "$g: derived copies match"; fi
}
# A pending program: exit 0 if it fails as recorded, 1 if not.
pending() {
  local f=$1 issue want out
  issue=$(sed -n '/^-- pending: /{s///p;q;}' "$f")
  want=$(sed -n 's/^-- now: //p; s/^-- now| //p' "$f")
  if [ -z "$issue" ] || [ -z "$want" ]; then
    echo "$f: needs a \`-- pending:\` line and a \`-- now:\` line"; return 1
  elif out=$("$bcc" check "$f" 2>&1); then
    echo "$f: checks now ($issue): move it into the corpus with its golden output"; return 1
  elif [ "$out" != "$f:$want" ] && { [ "${want#lib/}" = "$want" ] || [ "$out" != "$want" ]; }; then
    echo "$f: pending, but fails differently"; echo "  now:  $want"; echo "  got:  ${out#"$f:"}"
    return 1
  else
    echo "$f: pending ($issue), fails as recorded"
  fi
}
export -f checks rejects reports trusted copies pending
# Each program, reject, reports file and pending program is a unit of the result cache
# (scripts/par.sh, scripts/gate_cache.py).
export PAR_CACHE=check-corpus
if [ $# -gt 0 ]; then
  for f in "$@"; do [ -f "$f" ] || { echo "$f: no such file"; exit 2; }; done
  for f in "$@"; do
    case "$f" in
      corpus/reject/*) par rejects "$f" ;;
      corpus/pending/*) par pending "$f" ;;
      corpus/reports/*.txt) par reports "$f" ;;
      corpus/trusted/*.txt) par trusted "$f" ;;
      corpus/copies/*.txt) par copies "$f" ;;
      *) par checks "$f"; r=corpus/reports/$(basename "${f%.bc}").txt
         if [ "$par_failed" = 0 ] && [ "$f" = "corpus/$(basename "$f")" ] && [ -f "$r" ]; then par reports "$r"; fi ;;
    esac
    bad=$((bad + par_failed))
  done
  echo "$bad failure(s)."
  [ "$bad" -eq 0 ]
  exit
fi
list=$(scripts/corpus-set.sh)
progs=(); while IFS= read -r f; do [ -z "$f" ] || progs+=("$f"); done <<< "$list"
list=$(scripts/corpus-set.sh reject)
rejectFiles=(); while IFS= read -r f; do [ -z "$f" ] || rejectFiles+=("$f"); done <<< "$list"
list=$(scripts/corpus-set.sh pending)
pend=(); while IFS= read -r f; do [ -z "$f" ] || pend+=("$f"); done <<< "$list"
par checks "${progs[@]}"; bad=$((bad + par_failed))
scripts/corpus-set.sh --skips check-corpus parse-only < "$skipdir/skips" || bad=$((bad + 1))
shopt -s nullglob
par rejects ${rejectFiles[@]+"${rejectFiles[@]}"}; bad=$((bad + par_failed))
par reports corpus/reports/*.txt; bad=$((bad + par_failed))
par trusted corpus/trusted/*.txt; bad=$((bad + par_failed))
par copies corpus/copies/*.txt; bad=$((bad + par_failed))
par pending ${pend[@]+"${pend[@]}"}; bad=$((bad + par_failed))
echo "$(( ${#pend[@]} - par_failed )) pending program(s), expected failures."
echo "$bad failure(s)."
[ "$bad" -eq 0 ]

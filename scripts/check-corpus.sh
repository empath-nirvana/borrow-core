#!/usr/bin/env bash
# Type-check the corpus with `bcc check`. Every `corpus/*.bc`, `corpus/surface/*.bc` and
# `corpus/axes/*.bc` must check, except a file marked `-- check: parse-only` (it is for the
# parser); every `corpus/reject/*.bc` must parse and be rejected by the checker with the message
# on its `-- expect:` line (`line:col: message`), continued by any `-- expect| ` lines for a
# message of several lines.
#
# Reports. For every corpus/reports/<name>.txt, the effects lines `bcc check corpus/<name>.bc` prints
# (`effect`, `row`, `lowering`, `call`: SPEC §18) must be exactly that file: the rows, the lowering
# shape of each handler and each call site's elaboration are pinned.
#
# Pending programs. Every `corpus/pending/*.bc` is a program we cannot write yet, named by its
# `-- pending: <issue or limit>` line. It is an expected failure: `bcc check` (which parses first)
# must reject it with the message on its `-- now:` line, continued by `-- now| ` lines, so the
# failure it documents is the current one. When a pending program checks, the feature it waits
# for has landed: the gate fails and says to move it into the corpus with its golden output.
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc >/dev/null
. scripts/par.sh
export bcc=.lake/build/bin/bcc
bad=0
checks() {
  local f=$1 out
  if grep -q '^-- check: parse-only' "$f"; then
    echo "$f: parse-only, skipped"; return 0
  fi
  if out=$("$bcc" check "$f" 2>&1); then
    echo "$f: checks"
  else
    echo "$f: rejected, but must check"; echo "  $out"; return 1
  fi
}
rejects() {
  local f=$1 want out
  want=$(sed -n 's/^-- expect: //p; s/^-- expect| //p' "$f")
  if ! "$bcc" parse "$f" >/dev/null 2>&1; then
    echo "$f: does not parse, so it does not test the checker"; return 1
  elif out=$("$bcc" check "$f" 2>&1); then
    echo "$f: accepted, but must be rejected"; return 1
  elif [ "$out" != "$f:$want" ]; then
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
# A pending program: exit 0 if it fails as recorded, 1 if not.
pending() {
  local f=$1 issue want out
  issue=$(sed -n 's/^-- pending: //p' "$f" | head -1)
  want=$(sed -n 's/^-- now: //p; s/^-- now| //p' "$f")
  if [ -z "$issue" ] || [ -z "$want" ]; then
    echo "$f: needs a \`-- pending:\` line and a \`-- now:\` line"; return 1
  elif out=$("$bcc" check "$f" 2>&1); then
    echo "$f: checks now ($issue): move it into the corpus with its golden output"; return 1
  elif [ "$out" != "$f:$want" ]; then
    echo "$f: pending, but fails differently"; echo "  now:  $want"; echo "  got:  ${out#"$f:"}"
    return 1
  else
    echo "$f: pending ($issue), fails as recorded"
  fi
}
export -f checks rejects reports pending
par checks corpus/*.bc corpus/surface/*.bc corpus/axes/*.bc; bad=$((bad + par_failed))
shopt -s nullglob
par rejects corpus/reject/*.bc; bad=$((bad + par_failed))
par reports corpus/reports/*.txt; bad=$((bad + par_failed))
pend=(corpus/pending/*.bc)
par pending ${pend[@]+"${pend[@]}"}; bad=$((bad + par_failed))
echo "$(( ${#pend[@]} - par_failed )) pending program(s), expected failures."
echo "$bad failure(s)."
[ "$bad" -eq 0 ]

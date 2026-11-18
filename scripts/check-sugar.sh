#!/usr/bin/env bash
# The I/O sugar (SPEC §11) is elaboration only. For every corpus/sugar/<name>.bc there is a
# corpus/sugar/<name>.core.bc written without the sugar: both must check, and the checked `main`
# of each must erase to the same term (`bcc erase`). A core form must also be its own
# elaboration: `bcc desugar` leaves it as it is. A sugared file whose first line is
# `-- core: <other>.core.bc` is compared with that core form instead.
#
# A lowering. Every corpus/sugar/<name>.lowered.bc whose first line is `-- lowers: <program>`
# writes that corpus program's declarations out by their elaboration rules (SPEC §42), in the
# surface: both must check, and their checked `main`s must erase to the same term.
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc >/dev/null
export GATE_CACHE_BUILT=1  # the binaries the result cache may key on are this build's
. scripts/par.sh
export bcc=.lake/build/bin/bcc
# A sugared file and its core form. Under `set -e`, as the script's own loop ran: a command that
# fails ends the pair as failed.
pair() {
  set -e
  local f=$1 tmp=$PAR_TMP core named
  core=${f%.bc}.core.bc
  named=$(sed -n '1s/^-- core: //p' "$f")
  [ -n "$named" ] && core="$(dirname "$f")/$named"
  if [ ! -f "$core" ]; then echo "$f: no $core"; return 1; fi
  if ! "$bcc" check "$f" > /dev/null 2> "$tmp/err" || ! "$bcc" check "$core" > /dev/null 2>> "$tmp/err"; then
    echo "$f: does not check: $(cat "$tmp/err")"; return 1
  fi
  "$bcc" erase "$f" > "$tmp/a"; "$bcc" erase "$core" > "$tmp/b"
  "$bcc" desugar "$core" > "$tmp/c"; "$bcc" print "$core" > "$tmp/d"
  if ! cmp -s "$tmp/a" "$tmp/b"; then echo "$f: its erasure differs from $core's"; return 1
  elif ! cmp -s "$tmp/c" "$tmp/d"; then echo "$core: has sugar left"; return 1
  else echo "$f: erases as $core"; fi
}
# A lowering and the program it lowers (under `set -e`, as `pair`).
lowered() {
  set -e
  local f=$1 tmp=$PAR_TMP prog
  prog=$(sed -n '1s/^-- lowers: //p' "$f")
  if [ -z "$prog" ] || [ ! -f "$prog" ]; then echo "$f: no \`-- lowers: <program>\` line"; return 1; fi
  if ! "$bcc" check "$prog" > /dev/null 2> "$tmp/err" || ! "$bcc" check "$f" > /dev/null 2>> "$tmp/err"; then
    echo "$f: does not check: $(cat "$tmp/err")"; return 1
  fi
  "$bcc" erase "$prog" > "$tmp/a"; "$bcc" erase "$f" > "$tmp/b"
  if ! cmp -s "$tmp/a" "$tmp/b"; then echo "$f: its erasure differs from $prog's"; return 1
  else echo "$prog: erases as $f"; fi
}
export -f pair lowered
# Each pair is a unit of the result cache (scripts/par.sh), keyed on both files, in a slot of the
# job pool; reported in order.
export PAR_CACHE=check-sugar PAR_CACHE_DEPS=sugar
sugared=()
for f in corpus/sugar/*.bc; do
  case "$f" in *.core.bc|*.lowered.bc) ;; *) sugared+=("$f") ;; esac
done
par pair ${sugared[@]+"${sugared[@]}"}
bad=$par_failed
shopt -s nullglob
low=(corpus/sugar/*.lowered.bc)
par lowered ${low[@]+"${low[@]}"}
bad=$((bad + par_failed))
echo "$bad failure(s)."
[ "$bad" -eq 0 ]

#!/usr/bin/env bash
# The respelling's oracle (SPEC §82). A source text in the new spelling is marked by its first line,
# the pragma (`bcc respell --pragma`). While both spellings are alive, each such file under corpus/
# or lib/ keeps its text in today's spelling, its twin, at `corpus/.respell-old/<path>`: the twin of
# `corpus/x/y.bc` is `corpus/.respell-old/x/y.bc`, of `lib/m.bc` `corpus/.respell-old/lib/m.bc`.
# For every pair:
#
#   * a program: `bcc erase` of the two (the de Bruijn erasure of the checked `main`) is
#     byte-identical, so the two have the same core term and the same golden;
#   * a refusal (a reject, fail or pending file, or any file whose check fails): both fail, with
#     the same message up to positions (`msg`: the positions move with the spelling);
#   * a file with no `main` (a library module): `bcc print` of the two (the declarations read, as
#     core text, with no positions) is byte-identical; its terms are compared again in every
#     program that imports it.
#
# It also fails when a file in the new spelling has no twin, or a twin has no file in the new
# spelling.
#
#     scripts/check-respell.sh [file…]   every pair, or the pairs of the files named (either side
#                                        of a pair)
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc >/dev/null
export GATE_CACHE_BUILT=1  # the binaries the result cache may key on are this build's
. scripts/par.sh
export bcc=.lake/build/bin/bcc
export LC_ALL=C
pragma=$("$bcc" respell --pragma)
export pragma
twin() { case "$1" in corpus/*) echo "corpus/.respell-old/${1#corpus/}" ;; lib/*) echo "corpus/.respell-old/$1" ;; esac; }
spelt() { local r=${1#corpus/.respell-old/}; case "$r" in lib/*) echo "$r" ;; *) echo "corpus/$r" ;; esac; }
isNew() { [ "$(head -n 1 "$1")" = "$pragma" ]; }
export -f twin spelt isNew
# The message of a refusal, without the file and position it is reported at, with every position
# it quotes blanked (the respelling moves lines, by the pragma line, and columns, by braces added
# round an arm) and every lifetime name blanked (a mode drops a written lifetime, and the parser
# names it `'io_lf<n>`: answers B5). With `new`, the line in a generated name `io_l<k><L>_<n>` is
# mapped back by the pragma line.
msg() {
  sed -E '1s/^[^:]*:[0-9]+:[0-9]+: //; 1s/^[^:]*: no `main`$/no `main`/' | perl -pe "s/\\b\\d+:\\d+\\b/L:C/g; s/'[a-z][A-Za-z0-9_]*/'_/g" |
    if [ "${1:-}" = new ]; then perl -pe 's/\b(io_l[a-z]+)(\d+)_/$1.($2-1)."_"/ge'; else cat; fi
}
export -f msg
# A pair: the file in the new spelling and its twin (under `set -e`, as check-sugar.sh's pairs).
pair() {
  set -e
  local f=$1 tmp=$PAR_TMP old ro=0 rn=0
  old=$(twin "$f")
  if [ ! -f "$old" ]; then echo "$f: in the new spelling, but has no twin $old"; return 1; fi
  if isNew "$old"; then echo "$old: a twin in the new spelling"; return 1; fi
  "$bcc" erase "$old" > "$tmp/o" 2> "$tmp/oe" || ro=$?
  "$bcc" erase "$f" > "$tmp/n" 2> "$tmp/ne" || rn=$?
  if [ "$ro" = 0 ] && [ "$rn" = 0 ]; then
    if cmp -s "$tmp/o" "$tmp/n"; then echo "$f: erases as $old"; return 0; fi
    echo "$f: its erasure differs from $old's"; return 1
  fi
  if [ "$ro" = 0 ] || [ "$rn" = 0 ]; then
    echo "$f: one of the pair checks and the other does not:"
    sed 's/^/  /' "$tmp/oe" "$tmp/ne"; return 1
  fi
  msg < "$tmp/oe" > "$tmp/om"; msg new < "$tmp/ne" > "$tmp/nm"
  if ! cmp -s "$tmp/om" "$tmp/nm"; then
    echo "$f: refused differently from $old:"; echo "  old: $(cat "$tmp/oe")"; echo "  new: $(cat "$tmp/ne")"; return 1
  fi
  if [ "$(cat "$tmp/om")" = 'no `main`' ]; then
    "$bcc" print "$old" > "$tmp/op" 2>&1 || true
    "$bcc" print "$f" > "$tmp/np" 2>&1 || true
    if cmp -s "$tmp/op" "$tmp/np"; then echo "$f: no main; prints as $old"; return 0; fi
    echo "$f: no main, and it prints differently from $old"; return 1
  fi
  echo "$f: refused as $old"
}
export -f pair
# The pairs: from the files named, or every file in the new spelling and every twin.
news=(); orphans=0
add() { local x; for x in ${news[@]+"${news[@]}"}; do [ "$x" = "$1" ] && return 0; done; news+=("$1"); }
if [ $# -gt 0 ]; then
  for f in "$@"; do
    [ -f "$f" ] || { echo "$f: no such file"; exit 2; }
    case "$f" in corpus/.respell-old/*) add "$(spelt "$f")" ;; *) isNew "$f" && add "$f" ;; esac
  done
else
  while IFS= read -r f; do isNew "$f" && add "$f"; done < <(
    { find corpus -path corpus/.respell-old -prune -o -name '*.bc' -type f -print; ls lib/*.bc; } | sort)
  if [ -d corpus/.respell-old ]; then
    while IFS= read -r o; do
      s=$(spelt "$o")
      if [ ! -f "$s" ] || ! isNew "$s"; then echo "$o: a twin with no file in the new spelling ($s)"; orphans=$((orphans + 1)); fi
    done < <(find corpus/.respell-old -name '*.bc' -type f | sort)
  fi
fi
# Each pair is a unit of the result cache (scripts/par.sh), keyed on both texts.
export PAR_CACHE=check-respell PAR_CACHE_DEPS=respell
par pair ${news[@]+"${news[@]}"}
bad=$((par_failed + orphans))
echo "${#news[@]} pair(s); $bad failure(s)."
[ "$bad" -eq 0 ]

#!/usr/bin/env bash
# The respelling's oracle (SPEC §82). A source text in the new spelling is marked by its first line,
# the pragma (`bcc respell --pragma`). While both spellings are alive, each such file under corpus/
# or lib/ keeps its text in today's spelling, its twin, at `corpus/.respell-old/<path>`: the twin of
# `corpus/x/y.bc` is `corpus/.respell-old/x/y.bc`, of `lib/m.bc` `corpus/.respell-old/lib/m.bc`.
# For every pair:
#
#   * a program: `bcc erase` of the two (the de Bruijn erasure of the checked `main`) is
#     byte-identical, so the two have the same core term and the same golden; and, since the
#     erasure holds no types, `bcc check`'s declarations with their checked types are the same
#     (`sigs`: positions blanked);
#   * a refusal (a reject, fail or pending file, or any file whose check fails): both fail, with
#     the same message up to positions (`msg`: the positions move with the spelling);
#   * a corpus file with no `main`: `bcc print` of the two (the declarations read, as core text,
#     with no positions) is byte-identical;
#   * a library module `lib/m.bc`: judged by its users (below), not by `bcc print`, which does not
#     see what a generic function's body lends where it is instantiated.
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
# round an arm, so a line shift alone does not map them) and every lifetime name blanked on both
# sides (a mode drops a written lifetime, and the parser names it `'io_lf<n>`). With `new`, the line
# in a generated name `io_l<k><L>_<n>` is mapped back by the pragma line.
msg() {
  sed -E '1s/^[^:]*:[0-9]+:[0-9]+: //; 1s/^[^:]*: no `main`$/no `main`/' | perl -pe "s/\\b\\d+:\\d+\\b/L:C/g; s/'[a-z][A-Za-z0-9_]*/'_/g" |
    if [ "${1:-}" = new ]; then perl -pe 's/\b(io_l[a-z]+)(\d+)_/$1.($2-1)."_"/ge'; else cat; fi
}
export -f msg
# What `bcc check` prints of a program that checks: each declaration with its checked type (its
# lifetimes numbered by the checker), and notes on its loops, calls and effects, with positions
# blanked and, with `new`, generated names mapped back by the pragma line, as in `msg`. The lines
# are sorted: the notes come in the order of their positions, which the respelling moves.
sigs() {
  perl -pe 's/\b\d+:\d+\b/L:C/g' |
    if [ "${1:-}" = new ]; then perl -pe 's/\b(io_l[a-z]+)(\d+)_/$1.($2-1)."_"/ge'; else cat; fi |
    sort
}
export -f sigs
# A pair: the file in the new spelling and its twin (under `set -e`, as check-sugar.sh's pairs).
pair() {
  set -e
  local f=$1 tmp=$PAR_TMP old ro=0 rn=0
  old=$(twin "$f")
  if [ ! -f "$old" ]; then echo "$f: in the new spelling, but has no twin $old"; return 1; fi
  if isNew "$old"; then echo "$old: a twin in the new spelling"; return 1; fi
  case "$f" in lib/*) echo "$f: a library module, judged by the programs that use it (below)"; return 0 ;; esac
  "$bcc" erase "$old" > "$tmp/o" 2> "$tmp/oe" || ro=$?
  "$bcc" erase "$f" > "$tmp/n" 2> "$tmp/ne" || rn=$?
  if [ "$ro" = 0 ] && [ "$rn" = 0 ]; then
    if ! cmp -s "$tmp/o" "$tmp/n"; then echo "$f: its erasure differs from $old's"; return 1; fi
    # The erasure holds no types: the declarations' checked types are compared as well.
    "$bcc" check "$old" 2>&1 | sigs > "$tmp/os"
    "$bcc" check "$f" 2>&1 | sigs new > "$tmp/ns"
    if ! cmp -s "$tmp/os" "$tmp/ns"; then
      echo "$f: the checked types of its declarations differ from $old's:"
      diff "$tmp/os" "$tmp/ns" | sed 's/^/  /'; return 1
    fi
    echo "$f: erases as $old, with the same declaration types"; return 0
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

# A library module in the new spelling is judged by its users: every corpus program whose
# imports reach it (`io`, `div` and `prelude` every program reaches) is erased over today's
# library, `oldlib` (lib/ with each respelled module replaced by its twin), and over lib/, and the
# two must be identical (refusals: as `msg`). This sees what `bcc print` of the module alone does
# not: a generic function's body is elaborated only where it is instantiated. A module no program
# reaches fails as uncovered, unless `uncovered` below names it with the reason.
uncovered=()
mods=()
for f in ${news[@]+"${news[@]}"}; do case "$f" in lib/*) m=${f#lib/}; mods+=("${m%.bc}") ;; esac; done
users=0
if [ ${#mods[@]} -gt 0 ]; then
  oldlib=$PWD/.lake/respell-old-lib
  rm -rf "$oldlib"; mkdir -p "$oldlib"
  cp lib/*.bc "$oldlib"/
  cp corpus/.respell-old/lib/*.bc "$oldlib"/
  export oldlib
  # The programs: corpus files with a `main` outside the twins, and which modules they reach.
  progs=$(find corpus -path corpus/.respell-old -prune -o -name '*.bc' -type f -print | sort |
    while IFS= read -r f; do if grepq -E '^(main|fn main\()' "$f"; then echo "$f"; fi; done) ||
    { echo "check-respell: a program could not be read"; exit 2; }
  reach=$(printf '%s\n' "$progs" | python3 -I -c '
import re, sys
mods = set(sys.argv[1:])
imp = re.compile(r"^(?:include|import)\s+([A-Za-z_][A-Za-z0-9_]*)", re.M)
def imports(path, module=False):
    # A name with no file under lib/ is no library module; any other failure to read is fatal,
    # never taken for a file that imports nothing.
    try:
        with open(path, encoding="utf-8", errors="surrogateescape") as fh:
            return imp.findall(fh.read())
    except FileNotFoundError:
        if module:
            return []
        raise
    except OSError as e:
        sys.exit(f"check-respell: cannot read {path}: {e}")
lib = {}
def closure(start):
    seen, todo = set(), list(start)
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        if m not in lib:
            lib[m] = imports(f"lib/{m}.bc", module=True)
        todo += lib[m]
    return seen
for p in sys.stdin.read().split():
    hit = sorted(closure(["io", "div", "prelude"] + imports(p)) & mods)
    if hit:
        print(p, " ".join(hit))
' "${mods[@]}") || { echo "check-respell: the modules each program reaches could not be read"; exit 2; }
  for m in "${mods[@]}"; do
    if ! printf '%s\n' "$reach" | grepq -E " $m( |\$)"; then
      ok=0; for u in ${uncovered[@]+"${uncovered[@]}"}; do [ "${u%%:*}" = "$m" ] && ok=1; done
      if [ "$ok" = 0 ]; then echo "lib/$m.bc: no corpus program uses it, so nothing judges its respelling"; bad=$((bad + 1)); fi
    fi
  done
  user() {
    set -e
    local f=$1 tmp=$PAR_TMP ro=0 rn=0
    BCC_LIB=$oldlib "$bcc" erase "$f" > "$tmp/o" 2> "$tmp/oe" || ro=$?
    "$bcc" erase "$f" > "$tmp/n" 2> "$tmp/ne" || rn=$?
    if [ "$ro" = 0 ] && [ "$rn" = 0 ]; then
      if cmp -s "$tmp/o" "$tmp/n"; then echo "$f: erases the same over today's library and lib/"; return 0; fi
      echo "$f: its erasure over lib/ differs from its erasure over today's library"; return 1
    fi
    if [ "$ro" != 0 ] && [ "$rn" != 0 ]; then
      msg < "$tmp/oe" > "$tmp/om"; msg < "$tmp/ne" > "$tmp/nm"
      if cmp -s "$tmp/om" "$tmp/nm"; then echo "$f: refused the same over today's library and lib/"; return 0; fi
    fi
    echo "$f: over today's library and over lib/ it is not the same:"
    sed 's/^/  /' "$tmp/oe" "$tmp/ne"; return 1
  }
  export -f user
  us=()
  while IFS=' ' read -r p _; do [ -n "$p" ] && us+=("$p"); done <<< "$reach"
  # Each user is a unit of the result cache, keyed on the program and every twin of lib/.
  export PAR_CACHE=check-respell-lib PAR_CACHE_DEPS=respell-lib
  par user ${us[@]+"${us[@]}"}
  bad=$((bad + par_failed)); users=${#us[@]}
fi
echo "${#news[@]} pair(s), ${#mods[@]} library module(s) judged by $users program(s); $bad failure(s)."
[ "$bad" -eq 0 ]

#!/usr/bin/env bash
# Compile and run the corpus. Every corpus/*.bc, corpus/surface/*.bc, corpus/axes/*.bc,
# corpus/aoc/*.bc and corpus/leetcode/*/*.bc with a `main` (except a file marked `-- check: parse-only`) has a golden output
# `<name>.out` beside it: the reference semantics, what `Support`'s interpreter (`bcc interp`, the
# source stage) prints.
# It reads `<name>.in` as standard input (the empty input if there is none), and `<name>.args`, one
# argument per line, as its arguments (SPEC §34; none if there is no such file). At the closure-IR
# and flat-IR interpreters (`bcc interp --stage clos|flat`) and in WebAssembly under wasmtime
# (`bcc run`), its whole standard output, the program's bytes followed by the report `live N`,
# must equal `<name>.out`, its standard error `<name>.err` (empty if there is none), and its exit
# status `<name>.status` (`0` if there is none: a program that an arithmetic error ends exits with
# `1`, SPEC §38). The first stage that differs is named. The report must be `live 0`: no object is live once the
# value is dropped. (The source counts cells, the compiled stages all objects, so the two agree
# when either is 0.)
#
#     scripts/compile-corpus.sh [--source] [file.bc…]   check the corpus, or the files named
#     scripts/compile-corpus.sh --write-goldens [file.bc…]
#     scripts/compile-corpus.sh --write-counts [file.bc…]
#
# The source stage (scripts/source-stage.sh). By default it runs only on the programs whose golden
# is unverified, those whose `.bc`, `.in`, `.out` or `.err` differs from the merge base with
# origin/main: an edited program is checked against the reference semantics even when its golden
# did not change. With `--source` (or `BCC_SOURCE=1`) it runs on every program, and must print
# the golden: `make gate-full` re-verifies every golden this way. With `BCC_SOURCE=0` it never
# runs (`ci-local.sh --changed`), and the unverified programs are listed.
#
# `--write-goldens` (`make goldens`) writes `<name>.out`, `<name>.err` (removed when empty) and
# `<name>.status` (removed when `0`) from the source stage, and only from it: a golden is never a
# compiled stage's output. It refuses a program that fails or leaves cells live; a nonzero exit
# status is the program's only when the stage wrote its report (`live N`).
#
# A program marked `-- check: no-source` is too large for the source interpreter
# (`corpus/deep-list.bc`): its golden is written by hand, and it is run at every other stage.
#
# No I/O program has a bound on its input: `corpus/io-cat.bc` also copies a generated input of
# 4860 bytes, at every stage (at the source stage when the source stage runs on io-cat.bc).
#
# Counts. Every program run is also run by `bcc-counts` (the flat IR and wasm, built to count,
# which must agree): the objects it allocates, the indirect calls it makes (the closure
# calls whose code a `switch` on the closure's tag chooses at run time), and the copies it makes of
# a variable at a non-trivial type (deep copies the ownership discipline inserts where a variable
# is used twice; Backend/README.md, Memory discipline). Each must be at most the
# program's entry in `corpus/counts.expected` (`name allocs indirect copies`, the name the file's path
# under `corpus/`, as `io-wc`, `surface/io-wc`, `axes/data-effects` or `aoc/2022-01`); a count
# above it fails, one below it is reported so the file can be lowered. `--write-counts` rewrites the entries of the
# programs run (every program, when none is named) with this run's counts, keeping the comment an
# entry ends with (`# …`).
set -euo pipefail
cd "$(dirname "$0")/.."
usage() { echo "usage: scripts/compile-corpus.sh [--source | --write-goldens | --write-counts] [file.bc…]"; exit 2; }
export write=0
goldens=0
files=()
while [ $# -gt 0 ]; do
  case "$1" in
    --write-counts) write=1 ;;
    --write-goldens) goldens=1 ;;
    --source) export BCC_SOURCE=1 ;;
    -*) usage ;;
    *) files+=("$1") ;;
  esac
  shift
done
[ "$write" = 0 ] || [ "$goldens" = 0 ] || usage
named=1
[ ${#files[@]} -gt 0 ] || { named=0; files=(corpus/*.bc corpus/surface/*.bc corpus/axes/*.bc corpus/aoc/*.bc corpus/leetcode/*/*.bc); }
for f in "${files[@]}"; do [ -f "$f" ] || { echo "$f: no such file"; exit 2; }; done
command -v wasmtime >/dev/null || [ "$goldens" = 1 ] || { echo "wasmtime is not on PATH"; exit 1; }
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc bcc-counts >/dev/null
. scripts/par.sh
export bcc=.lake/build/bin/bcc
export bccCounts=.lake/build/bin/bcc-counts
export expected=corpus/counts.expected
export tmp; tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# The arguments of program $1, from `<name>.args` (one per line), into the array `args`.
argsOf() {
  args=()
  local a=${1%.bc}.args line
  [ -f "$a" ] || return 0
  while IFS= read -r line || [ -n "$line" ]; do args+=("$line"); done < "$a"
}
# The exit status program $1 must end with: `<name>.status`, else `0`.
statusOf() {
  local s=${1%.bc}.status
  if [ -f "$s" ]; then tr -d ' \n' < "$s"; else echo 0; fi
}
# Whether file $1 is a program the corpus runs; if not, says why.
runnable() {
  if grep -q '^-- check: parse-only' "$1"; then echo "$1: parse-only, skipped"; return 1; fi
  if ! grep -q '^main' "$1"; then echo "$1: no main, skipped"; return 1; fi
}
# --write-goldens: the golden of file $1, from the source stage.
golden() {
  local f=$1 w=${PAR_TMP:-$tmp} base in
  runnable "$f" || return 0
  base=${f%.bc}
  if grep -q '^-- check: no-source' "$f"; then
    echo "$f: no-source: $base.out is written by hand, kept"; return 0
  fi
  in=/dev/null; [ -f "$base.in" ] && in="$base.in"
  argsOf "$f"
  local rc=0
  "$bcc" interp "$f" -- "${args[@]+"${args[@]}"}" < "$in" > "$w/out" 2> "$w/err" || rc=$?
  if [ "$rc" != 0 ] && ! grep -q '^live ' "$w/out"; then
    echo "$f: the source interpreter fails, golden not written: $(head -3 "$w/err")"; return 1
  fi
  if [ "$(tail -1 "$w/out")" != "live 0" ]; then
    echo "$f: leaves cells live ($(tail -1 "$w/out")), golden not written"; return 1
  fi
  cp "$w/out" "$base.out"
  if [ -s "$w/err" ]; then cp "$w/err" "$base.err"; else rm -f "$base.err"; fi
  if [ "$rc" != 0 ]; then echo "$rc" > "$base.status"; else rm -f "$base.status"; fi
  echo "$f: wrote $base.out$([ -s "$w/err" ] && echo " and $base.err")$([ "$rc" != 0 ] && echo " and $base.status ($rc)")"
}
if [ "$goldens" = 1 ]; then
  export -f runnable golden argsOf statusOf
  par golden "${files[@]}"
  echo "$par_failed failure(s)."
  [ "$par_failed" -eq 0 ]
  exit
fi

. scripts/source-stage.sh
bad=0
: > "$tmp/counts"
# The counts of file $1 on input $2, checked against the expected ones; appended to the table.
counts() {
  local name got a i c want wa wi wc note
  name=${1#corpus/}; name=${name%.bc}
  argsOf "$1"
  if ! got=$("$bccCounts" "$1" -- "${args[@]+"${args[@]}"}" < "$2" 2>&1); then echo "$1: counts: $got"; return 1; fi
  a=$(echo "$got" | awk '{print $2}'); i=$(echo "$got" | awk '{print $4}')
  c=$(echo "$got" | awk '{print $6}')
  # An entry may end with a comment (`# …`), kept when the file is rewritten.
  note=$(awk -v n="$name" '$1 == n { sub(/^[^#]*/, ""); print }' "$expected" 2>/dev/null || true)
  echo "$name $a $i $c${note:+ $note}" >> "$tmp/counts"
  cnt="allocs $a, indirect $i, copies $c"
  [ "$write" = 1 ] && return 0
  want=$(awk -v n="$name" '$1 == n {print $2, $3, $4}' "$expected" 2>/dev/null || true)
  if [ -z "$want" ]; then echo "$1: no entry in $expected ($cnt)"; return 1; fi
  read -r wa wi wc <<< "$want"
  if [ -z "$wc" ]; then echo "$1: $expected's entry has no copies column"; return 1; fi
  if [ "$a" -gt "$wa" ] || [ "$i" -gt "$wi" ] || [ "$c" -gt "$wc" ]; then
    echo "$1: counts regressed: $cnt, expected at most allocs $wa, indirect $wi, copies $wc"; return 1
  fi
  if [ "$a" -lt "$wa" ] || [ "$i" -lt "$wi" ] || [ "$c" -lt "$wc" ]; then
    cnt="$cnt (below $expected's $wa, $wi, $wc: lower it)"
  fi
}
# Run stage $1 of file $2 on input $3 into $w/out and $w/err; it fails unless it ends with the
# program's exit status (`statusOf`).
runStage() {
  local rc=0
  argsOf "$2"
  if [ "$1" = wasm ]; then "$bcc" run "$2" "${args[@]+"${args[@]}"}" < "$3" > "$w/out" 2> "$w/err" || rc=$?
  elif [ "$1" = source ]; then "$bcc" interp "$2" -- "${args[@]+"${args[@]}"}" < "$3" > "$w/out" 2> "$w/err" || rc=$?
  else "$bcc" interp --stage "$1" "$2" -- "${args[@]+"${args[@]}"}" < "$3" > "$w/out" 2> "$w/err" || rc=$?; fi
  [ "$rc" = "$(statusOf "$2")" ]
}
# Whether the source stage runs on program $1 (scripts/source-stage.sh); reports an unverified
# golden it does not run on.
withSource() {
  local f=$1 base=${1%.bc}
  case "$BCC_SOURCE" in
    1) return 0 ;;
    0) if unverified "$f" "$base.in" "$base.out" "$base.err" "$base.status"; then
         echo "$f: unverified: changed since $source_base, not run at the source stage (scripts/compile-corpus.sh $f runs it)"
       fi
       return 1 ;;
    *) unverified "$f" "$base.in" "$base.out" "$base.err" "$base.status" ;;
  esac
}
# One corpus program, run at every stage and counted (in parallel, by `par`; its scratch
# directory is $PAR_TMP).
program() {
  local f=$1 w=${PAR_TMP:-$tmp} base in err ok stages st note=""
  runnable "$f" || return 0
  base=${f%.bc}
  if [ ! -f "$base.out" ]; then
    echo "$f: no golden $base.out: write it from the source stage with \`scripts/compile-corpus.sh --write-goldens $f\`"
    return 1
  fi
  in=/dev/null; [ -f "$base.in" ] && in="$base.in"
  err=/dev/null; [ -f "$base.err" ] && err="$base.err"
  ok=1
  stages="clos flat wasm"
  if grep -q '^-- check: no-source' "$f"; then :
  elif withSource "$f"; then
    stages="source $stages"
    [ "$BCC_SOURCE" = 1 ] || note=" (unverified since $source_base, so at the source stage too)"
  fi
  for st in $stages; do
    if ! runStage "$st" "$f" "$in"; then
      echo "$f: stage $st fails, or does not exit with status $(statusOf "$f"): $(head -3 "$w/err")"; ok=0; break
    fi
    if ! cmp -s "$w/out" "$base.out" || ! cmp -s "$w/err" "$err"; then
      echo "$f: stage $st differs from $base.out or from its standard error"
      diff "$w/out" "$base.out" | head -6 | sed 's/^/  /' || true
      if [ "$st" = source ]; then
        echo "  the golden is not the reference semantics: if the program's new output is intended, write it with"
        echo "  \`scripts/compile-corpus.sh --write-goldens $f\` and check it with \`scripts/compile-corpus.sh $f\`"
      fi
      ok=0; break
    fi
  done
  if [ "$ok" = 1 ] && [ "$(tail -1 "$base.out")" != "live 0" ]; then
    echo "$f: agrees, but leaves objects live"; ok=0
  fi
  if [ "$ok" = 1 ] && ! counts "$f" "$in"; then ok=0; fi
  [ "$ok" = 1 ] || return 1
  echo "$f: $(wc -c < "$base.out" | tr -d ' ') bytes as $base.out at $(echo $stages | tr ' ' ,)$note | live 0 | $cnt"
}
# An input past any fixed bound: 4860 bytes, copied whole at every stage. (The source
# interpreter takes about a minute on it, so it runs beside the corpus.)
bigcat() {
  local w=$tmp/bigcat st ok=1 stages="clos flat wasm"
  mkdir -p "$w"
  awk 'BEGIN { for (i = 0; i < 90; i++) printf "line %02d of a long input, copied byte for byte by cat.\n", i }' \
    > "$w/big.in"
  printf '()\nlive 0\n' | cat "$w/big.in" - > "$w/big.out"
  withSource corpus/io-cat.bc > /dev/null && stages="source $stages"
  for st in $stages; do
    runStage "$st" corpus/io-cat.bc "$w/big.in" || true
    if ! cmp -s "$w/out" "$w/big.out"; then echo "corpus/io-cat.bc: stage $st differs on a $(wc -c < "$w/big.in" | tr -d ' ')-byte input"; ok=0; fi
  done
  if [ "$ok" = 1 ]; then echo "corpus/io-cat.bc: a $(wc -c < "$w/big.in" | tr -d ' ')-byte input copied whole at $(echo $stages | tr ' ' ,)"; else return 1; fi
}
export -f counts runStage withSource runnable program argsOf statusOf
bigpid=""
case " ${files[*]} " in *" corpus/io-cat.bc "*) bigcat > "$tmp/bigcat.log" 2>&1 & bigpid=$! ;; esac
par program "${files[@]}"
bad=$par_failed
if [ -n "$bigpid" ]; then
  if wait "$bigpid"; then cat "$tmp/bigcat.log"; else cat "$tmp/bigcat.log"; bad=$((bad + 1)); fi
fi
if [ "$write" = 1 ]; then
  # Keep the entries of the programs not named.
  [ "$named" = 0 ] || awk 'NR == FNR { run[$1] = 1; next } /^#/ { next } !($1 in run)' "$tmp/counts" "$expected" >> "$tmp/counts"
  { echo "# Allocations, indirect (dispatched) calls and copies at a non-trivial type per run of each corpus program (scripts/compile-corpus.sh)."
    echo "# name allocs indirect copies"
    sort "$tmp/counts"; } > "$expected"
  echo "wrote $expected"
fi
case "$BCC_SOURCE" in
  1) echo "source stage: every program" ;;
  0) echo "source stage: not run (BCC_SOURCE=0)" ;;
  *) echo "source stage: the programs unverified since ${source_base:-(no merge base)} only (--source runs every program)" ;;
esac
echo "$bad failure(s)."
[ "$bad" -eq 0 ]

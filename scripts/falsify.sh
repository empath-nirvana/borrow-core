#!/usr/bin/env bash
# The falsifier's differential runs (docs/async-capabilities.md §6.1, `Backend/Falsify.lean`).
# Every accepted program is run four ways at the source stage:
#
#   default   `bcc interp`: Support's interpreter (its allocator never reuses a location)
#   least     `bcc interp --alloc least`: the least-free allocator (`Alloc.leastFree`, `runM`),
#             which reuses a freed location at once
#   fresh     `bcc interp --check fresh`: a never-reuse allocator; a use after free is reported
#   tags      `bcc interp --check tags`: never-reuse, and every lend tagged; an access through a
#             tag that has ended or is suspended, an aliased access, an owner access while lent,
#             or a lend that never ends is reported
#
# Each must succeed, print what the default prints (standard output and standard error), and end
# with `live 0`.
#
#     scripts/falsify.sh                  the corpus, the AsyncCap programs that check, the kernel
#                                         programs, and the negative tests
#     scripts/falsify.sh file.bc…         those files only
#
# Accepted programs: every corpus/*.bc, corpus/surface/*.bc, corpus/axes/*.bc, corpus/aoc/*.bc and
# corpus/leetcode/*/*.bc with a `main` (except one marked `-- check: parse-only` or `-- check: no-source`, too large for
# the source interpreter), and every program of experiments/AsyncCap/bc and bc/accept that `bcc check`
# accepts today (the others are pending, and listed; bc/reject is never run); each reads `<name>.in` as standard input and `<name>.args` as its arguments when there is one. The
# kernel programs are `bcc kernel list`.
#
# The negative tests (`bcc kernel negatives`, `Backend/FalsifyTests.lean`) are untyped terms,
# each breaking one rule: the mode named must fail with the report named, and the default run
# must give the answer named (the fault is invisible to it, or it is stuck).
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build bcc >/dev/null
. scripts/par.sh
export bcc=.lake/build/bin/bcc

# run TAG ARGS…: run `bcc ARGS…` (stdin from $in, and the program's arguments from $argsf, one per
# line, after `--`), leaving $TAG.out, $TAG.err, $TAG.rc.
run() {
  local tag=$1; shift
  local w=${PAR_TMP:-/tmp} line
  if [ -n "${argsf:-}" ]; then
    set -- "$@" --
    while IFS= read -r line || [ -n "$line" ]; do set -- "$@" "$line"; done < "$argsf"
  fi
  if [ -n "${in:-}" ]; then "$bcc" "$@" < "$in" > "$w/$tag.out" 2> "$w/$tag.err" && echo 0 > "$w/$tag.rc" || echo $? > "$w/$tag.rc"
  else "$bcc" "$@" < /dev/null > "$w/$tag.out" 2> "$w/$tag.err" && echo 0 > "$w/$tag.rc" || echo $? > "$w/$tag.rc"; fi
}
export -f run

# differ NAME KIND…: run NAME four ways (KIND is `interp` or `kernel interp`) and compare.
differ() {
  local name=$1; shift
  local w=${PAR_TMP:-/tmp} m stats=""
  run default "$@" "$name"
  if [ "$(cat "$w/default.rc")" != 0 ]; then
    echo "$name: FAIL: the default run fails: $(head -c 400 "$w/default.err")"; return 1
  fi
  if [ "$(tail -n 1 "$w/default.out")" != "live 0" ]; then
    echo "$name: FAIL: the default run leaves cells: $(tail -n 1 "$w/default.out")"; return 1
  fi
  for m in least fresh tags; do
    case $m in
      least) run "$m" "$@" --alloc least "$name" ;;
      tags) run "$m" "$@" --check tags --stats "$name" ;;
      *) run "$m" "$@" --check "$m" "$name" ;;
    esac
    if [ "$(cat "$w/$m.rc")" != 0 ]; then
      echo "$name: FAIL ($m): $(head -c 600 "$w/$m.err")"; return 1
    fi
    if [ "$m" = tags ]; then
      stats=$(tail -n 1 "$w/tags.err")
      sed '$d' "$w/tags.err" > "$w/tags.err2" && mv "$w/tags.err2" "$w/tags.err"
    fi
    if ! cmp -s "$w/default.out" "$w/$m.out"; then
      echo "$name: FAIL ($m): standard output differs: $(head -c 300 "$w/$m.out") (default: $(head -c 300 "$w/default.out"))"
      return 1
    fi
    if ! cmp -s "$w/default.err" "$w/$m.err"; then
      echo "$name: FAIL ($m): standard error differs"; return 1
    fi
  done
  echo "$name: ok $(head -n 1 "$w/default.out" | head -c 60); ${stats#check tags: }"
}
export -f differ

one_file() {
  local f=$1
  export in="" argsf=""
  [ -f "${f%.bc}.in" ] && in="${f%.bc}.in"
  [ -f "${f%.bc}.args" ] && argsf="${f%.bc}.args"
  differ "$f" interp
}
export -f one_file

one_kernel() { export in="" argsf=""; differ "$1" kernel interp; }
export -f one_kernel

# negative NAME MODE MESSAGE ANSWER
negative() {
  local name=$1 mode=$2 msg=$3 ans=$4 w=${PAR_TMP:-/tmp} flag
  export in="" argsf=""
  run default kernel interp "$name"
  if ! grep -qF -- "$ans" "$w/default.out" "$w/default.err"; then
    echo "$name: FAIL: the default run does not give \`$ans\`: $(cat "$w/default.out" "$w/default.err")"; return 1
  fi
  run least kernel interp --alloc least "$name"
  [ "$mode" = least ] && flag="--alloc least" || flag="--check $mode"
  # shellcheck disable=SC2086
  run checked kernel interp $flag "$name"
  if [ "$(cat "$w/checked.rc")" = 0 ]; then
    echo "$name: FAIL: --check $mode passes: $(cat "$w/checked.out")"; return 1
  fi
  if ! grep -qF -- "$msg" "$w/checked.err"; then
    echo "$name: FAIL: --check $mode reports something else: $(cat "$w/checked.err")"; return 1
  fi
  echo "$name: ok: default: $(tr '\n' ' ' < "$w/default.out")$(tr '\n' ' ' < "$w/default.err")| least: $(tr '\n' ' ' < "$w/least.out")$(tr '\n' ' ' < "$w/least.err")| $mode: $(cat "$w/checked.err")"
}
export -f negative

files=("$@")
all=0
if [ ${#files[@]} -eq 0 ]; then
  all=1
  for f in corpus/*.bc corpus/surface/*.bc corpus/axes/*.bc corpus/aoc/*.bc corpus/leetcode/*/*.bc; do
    grep -q '^-- check: parse-only' "$f" && continue
    grep -q '^-- check: no-source' "$f" && { echo "$f: no-source, skipped"; continue; }
    grep -q '^main' "$f" || continue
    files+=("$f")
  done
  for f in experiments/AsyncCap/bc/*.bc experiments/AsyncCap/bc/accept/*.bc; do
    if "$bcc" check "$f" >/dev/null 2>&1; then files+=("$f")
    else echo "$f: pending (does not check today), skipped"; fi
  done
fi

bad=0
par one_file "${files[@]}"
nf=${#files[@]}; ff=$par_failed; bad=$((bad + par_failed))
nk=0; fk=0; nn=0; fn=0
if [ "$all" = 1 ]; then
  kernels=()
  while IFS= read -r k; do kernels+=("$k"); done < <("$bcc" kernel list)
  nk=${#kernels[@]}
  par one_kernel "${kernels[@]}"
  fk=$par_failed; bad=$((bad + par_failed))
  while IFS=$'\t' read -r name mode msg ans; do
    nn=$((nn + 1))
    out=$(PAR_TMP=$(mktemp -d) negative "$name" "$mode" "$msg" "$ans") || { fn=$((fn + 1)); bad=$((bad + 1)); }
    echo "$out"
  done < <("$bcc" kernel negatives)
fi
echo "falsify: programs $((nf - ff))/$nf passed under default, least, fresh and tags; kernel programs $((nk - fk))/$nk; negative tests $((nn - fn))/$nn"
[ "$bad" = 0 ]

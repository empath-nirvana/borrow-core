# Sourced by the corpus scripts: run a function on many files at once, and report in order.
#
#   par FN FILE...   runs `FN FILE` for every FILE, $JOBS at a time (default: the CPU count), each
#                    in its own shell; prints each one's output in the order the files were given;
#                    and sets `par_failed` to the number whose FN returned non-zero.
#
# FN runs under `set -uo pipefail`. FN, and every variable and function it uses, must be exported (`export -f`, `export`). Each run
# gets a scratch directory of its own in `$PAR_TMP`.
JOBS=${JOBS:-$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)}
export JOBS
par() {
  local fn=$1; shift
  local dir i j n=$#
  dir=$(mktemp -d)
  par_failed=0
  [ $# -gt 0 ] || { rm -rf "$dir"; return 0; }
  i=0; for f in "$@"; do i=$((i + 1)); printf '%s\n%s\n' "$i" "$f"; done |
    PAR_DIR="$dir" xargs -P "$JOBS" -n 2 bash -c '
      set -uo pipefail
      mkdir "$PAR_DIR/$1.d"
      PAR_TMP="$PAR_DIR/$1.d" '"$fn"' "$2" > "$PAR_DIR/$1.out" 2>&1
      echo $? > "$PAR_DIR/$1.rc"' _
  for ((j = 1; j <= n; j++)); do
    cat "$dir/$j.out" 2>/dev/null || echo "par: job $j ($fn) did not run"
    [ "$(cat "$dir/$j.rc" 2>/dev/null || echo 1)" = 0 ] || par_failed=$((par_failed + 1))
  done
  rm -rf "$dir"
}

# Sourced by the corpus scripts: run a function on many files at once, and report in order.
#
#   par FN FILE...   runs `FN FILE` for every FILE, each in its own shell, in a slot of the
#                    machine-wide job pool (scripts/slot: one CPU slot and `$PAR_MEM` GB, default
#                    1, each); prints each one's output in the order the files were given; and
#                    sets `par_failed` to the number whose FN returned non-zero. At most $JOBS
#                    (default: the CPU count) wait for or hold a slot at once; the pool, shared by
#                    every gate on the machine, bounds how many run. With `SLOT_OFF=1` (or no
#                    perl) the pool is off and $JOBS run at once, as without it.
#
# FN runs under `set -uo pipefail`, in a subshell of its own (a FN that sets `-e` ends only itself). FN, and every variable and function it uses, must be exported (`export -f`, `export`). Each run
# gets a scratch directory of its own in `$PAR_TMP`, removed as soon as the run ends (only its
# output, status and side files are kept until the call ends), so a call holds a few files per
# job, not every job's scratch.
#
# Side files. A run hands files back to its script by writing them under `$PAR_SIDE`; after every
# run has ended, each run's files are appended, in the order the files were given, to the file of
# the same relative path under `$PAR_COLLECT` (the script's own directory).
#
# The result cache (scripts/gate_cache.py). When `PAR_CACHE` is set (`<step> <mode…>`: the step's
# name and every flag or variable that changes what FN does), each run is a unit whose key covers
# what it reads: FN, `PAR_CACHE`, the binaries, the library, scripts/, the tools, the `BC_*`,
# `BCC_*` and `CI_LOCAL_*` variables, and the files of FILE (`PAR_CACHE_DEPS`: `corpus`, the
# default, FILE and its sidecars and table rows; `sugar`, `book`, or `files:<path…>`). A unit
# recorded as passing is replayed (its output and side files) instead of run; a run that passes
# is recorded, unless it calls `par_nostore` (it ran the source interpreter, or wrote a file of
# the tree). `GATE_CACHE=0` neither reads nor writes the cache.
unset PAR_CACHE PAR_CACHE_DEPS PAR_CACHE_NATIVE PAR_COLLECT
PAR_HOME=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
JOBS=${JOBS:-$(getconf _NPROCESSORS_ONLN 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)}
export JOBS PAR_HOME
# The job pool is off with SLOT_OFF=1 or without perl, for every job. With perl, a pool that does
# not answer (`slot -s`: under ENFILE perl cannot even load its modules) makes every call fail,
# saying why (`par_pool_error`), as ci-local stops the gate and scripts/slotpool.py raises: jobs
# never run outside the pool unannounced.
par_pool_error=""
if [ "${SLOT_OFF:-}" != 1 ]; then
  if ! command -v perl >/dev/null; then export SLOT_OFF=1
  elif ! par_pool_out=$("$PAR_HOME/slot" -s 2>&1); then
    par_pool_error="par: the job pool does not answer (scripts/slot -s: $(printf '%s' "$par_pool_out" | head -1))"
  fi
fi
# The job pool's prefix for each job's shell, or none when the pool is off. A job (FN) holds its
# slot while it runs, so it must not call `par` with `PAR_CACHE` set: a nested cached unit could
# wait on another gate's entry lock (scripts/par_unit.py) while holding a slot.
par_slot() {
  if [ "${SLOT_OFF:-}" != 1 ]; then printf '%s\n' "$PAR_HOME/slot" -m "${PAR_MEM:-1}" --; fi
}
par() {
  local fn=$1; shift
  local dir i f
  [ -z "$par_pool_error" ] || { echo "$par_pool_error"; par_failed=$#; return 0; }
  dir=$(mktemp -d)
  par_failed=0
  [ $# -gt 0 ] || { rm -rf "$dir"; return 0; }
  i=0; for f in "$@"; do i=$((i + 1)); printf '%s\n%s\n' "$i" "$f"; done > "$dir/jobs"
  python3 "$PAR_HOME/gate_cache.py" par-start "$dir" "$fn" > "$dir/run" || { echo "par: the cache's keys failed ($fn)"; rm -rf "$dir"; par_failed=$#; return 0; }
  # Each job: in a slot of the job pool; and, when its result is cached, under its entry's lock,
  # so that a gate missing the same unit at the same time replays it instead (scripts/par_unit.py).
  local pre=()
  [ ! -s "$dir/entries" ] || pre=(python3 -S "$PAR_HOME/par_unit.py" "$dir" --)
  while IFS= read -r i; do pre+=("$i"); done < <(par_slot)
  [ ! -s "$dir/run" ] || PAR_DIR="$dir" xargs -P "$JOBS" -n 2 ${pre[@]+"${pre[@]}"} bash -c '
      set -uo pipefail
      mkdir "$PAR_DIR/$1.d"; mkdir -p "$PAR_DIR/$1.side"
      par_nostore() { : > "$PAR_NOSTORE"; }; export -f par_nostore
      (PAR_TMP="$PAR_DIR/$1.d" PAR_SIDE="$PAR_DIR/$1.side" PAR_NOSTORE="$PAR_DIR/$1.nostore" '"$fn"' "$2") > "$PAR_DIR/$1.out" 2>&1
      echo $? > "$PAR_DIR/$1.rc"; rm -rf "$PAR_DIR/$1.d"' _ < "$dir/run" || true
  python3 "$PAR_HOME/gate_cache.py" par-finish "$dir" "$fn"
  par_failed=$(cat "$dir/failed" 2>/dev/null || echo $#)
  rm -rf "$dir"
}

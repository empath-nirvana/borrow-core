# Sourced by scripts/compile-backend2.sh and scripts/compile-native.sh (after scripts/par.sh):
# Backend2's native build and run of each corpus program (`bcc run --native`, the default backend,
# which `--backend new` names), done once for both. Both steps compared this same run of the same
# command (`Frontend/Main.lean`: `runLL (compile2 true file)` either way).
#
#   native_runs DIR FILE…   runs `native_run` on each FILE that has `main` and is not
#                           parse-only, as `par` jobs; the results are DIR/<file>/{out,err,rc}.
#
# Each run is a unit of the result cache (scripts/par.sh) whose key is the same in both steps
# (`PAR_CACHE=native-run`, the function `native_run`, the program's files): the step that comes
# second replays it, or waits on its lock while the first runs it (scripts/par_unit.py). A run is
# recorded only when it matches the program's golden (status, standard output and error), so a
# run that differs runs again next time; each step compares the results itself, as before.
native_run() {
  local f=$1 base=${1%.bc} in=/dev/null err=/dev/null d rc=0
  [ -f "$base.in" ] && in="$base.in"
  [ -f "$base.err" ] && err="$base.err"
  argsOf "$f"
  d=$PAR_SIDE/$f; mkdir -p "$d"
  "$bcc" run --native "$f" "${args[@]+"${args[@]}"}" < "$in" > "$d/out" 2> "$d/err" || rc=$?
  echo "$rc" > "$d/rc"
  [ "$rc" = "$(statusOf "$f")" ] && cmp -s "$d/out" "$base.out" && cmp -s "$d/err" "$err"
}
export -f native_run
native_runs() {
  local dir=$1 f fs=(); shift
  for f in "$@"; do
    grep -q '^-- check: parse-only' "$f" || ! grep -q '^main' "$f" || fs+=("$f")
  done
  mkdir -p "$dir"
  ( export PAR_COLLECT=$dir PAR_CACHE=native-run PAR_CACHE_NATIVE=1; unset PAR_CACHE_DEPS; par native_run ${fs[@]+"${fs[@]}"} > /dev/null )
}
# native_result DIR F W: the recorded run of F into W/out and W/err; its status on standard output.
# A program with no recorded run (its run did not end) has status `none`, which matches no golden.
native_result() {
  local d=$1/$2
  if [ -f "$d/rc" ]; then cp "$d/out" "$3/out"; cp "$d/err" "$3/err"; cat "$d/rc"
  else : > "$3/out"; echo "native-run: no recorded run of $2" > "$3/err"; echo none; fi
}
export -f native_result

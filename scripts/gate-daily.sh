#!/usr/bin/env bash
# The daily full gate on main: every check of `make gate-full`, without the result cache, on the
# current origin/main, with its verdict posted to the board for the coordinator.
#
#     scripts/gate-daily.sh            gate origin/main unless it already has a verdict
#     scripts/gate-daily.sh --force    gate origin/main even if it has one, or a run was made today
#     make gate-daily                  the same as the first
#
# What it does, in order:
#   1. Takes the daily lock ($out/.lock); a second start while one runs says so and exits 0.
#   2. Uses a checkout of its own, $GATE_DAILY_DIR (default ~/repos/borrow-core-daily). On the
#      first run it is created as a detached worktree of this repository, with `.lake` cloned
#      copy-on-write from $GATE_DAILY_LAKE_FROM (default: the checkout this script is in), and
#      marked as the daily checkout. A directory without the mark is refused, so the run never
#      resets an agent's worktree.
#   3. Fetches, and stops (exit 0) if origin/main's commit already has a verdict in
#      $out/verdicts.tsv, or if a run was recorded today (so a run at login after a 04:00 run on
#      an older commit does not gate during the working day). `--force` skips both.
#   4. Resets the checkout to origin/main, detached (`reset --hard`, `clean -fd`; ignored files
#      such as `.lake` stay, so the Lean build is incremental over yesterday's).
#   5. Runs the gate there: `~/repos/scripts-local/gate-serial.sh gate-full` (queued behind any
#      agent's gate, and they behind it), under `caffeinate -i` (no idle sleep mid-run), under
#      `timeout` ($GATE_DAILY_LIMIT, default 4h, queue included; at the limit the gate's own
#      process group is stopped, and the verdict is TIMEOUT), and under the gate30 sampler when
#      it is present. The result cache is never read: `GATE_CACHE=record` when the checked-out
#      scripts/gate_cache.py knows that mode (run every unit, record the passes, so current main
#      warms the machine-wide cache), else `GATE_CACHE=0`.
#   6. Writes the log ($out/<date>-<commit>.log; kept whatever the verdict) and one line in
#      $out/verdicts.tsv: date, commit, verdict (PASS, FAIL or TIMEOUT), failing steps, wall
#      seconds, CPU seconds, log. A FAIL or TIMEOUT log ends with the merges since the last
#      passing run (`git log --merges --oneline <last-pass>..<commit>`).
#   7. Posts a board note to the coordinator (`board note verdict --to coordinator --unit
#      $GATE_DAILY_UNIT --file <log>`): on a pass one line; on a failure the failing steps and the
#      pull requests merged since the last passing run. A run that cannot start (fetch, checkout)
#      posts a note too and records no verdict.
# Exit status: 0 pass or nothing to do, 1 FAIL or TIMEOUT, 2 the run could not start.
#
# Environment (defaults in brackets): GATE_DAILY_DIR [~/repos/borrow-core-daily],
# GATE_DAILY_OUT [~/repos/scratch-archive/gate30/daily], GATE_DAILY_LAKE_FROM [this checkout],
# GATE_DAILY_LIMIT [4h], GATE_DAILY_UNIT [gate30], GATE_DAILY_CMD [the gate-serial command; a
# command line run by `bash -c` in the daily checkout, for tests: e.g. a stub printing a gate's
# summary], GATE_DAILY_BOARD [~/repos/scratch-archive/board/board; the command posting the note],
# GATE_DAILY_SAMPLER [~/repos/scratch-archive/gate30/tools/gate-measure.sh; ignored if absent].
#
# Scheduling: scripts/gate-daily.plist, a launchd agent running this script from the daily
# checkout at 04:00 and at login. Install and remove (macOS; run from any checkout):
#
#     sed "s|@HOME@|$HOME|g" scripts/gate-daily.plist > ~/Library/LaunchAgents/local.borrow-core.gate-daily.plist
#     launchctl bootstrap gui/$(id -u) ~/Library/LaunchAgents/local.borrow-core.gate-daily.plist
#
#     launchctl bootout gui/$(id -u)/local.borrow-core.gate-daily
#     rm ~/Library/LaunchAgents/local.borrow-core.gate-daily.plist
#
# The agent runs ~/repos/borrow-core-daily/scripts/gate-daily.sh, so the daily checkout must
# exist (run this script once by hand) and origin/main must contain this script. A missed day:
# launchd runs a calendar job missed while the machine slept when it wakes (several missed days
# coalesce into one run); while the machine is off or the user logged out it does not run, and
# the run at the next login (RunAtLoad) catches the day up. `launchctl print
# gui/$(id -u)/local.borrow-core.gate-daily` shows the agent and its last exit status; launchd's
# own output goes to $out/launchd.log.
set -uo pipefail

# Run from a copy, so that checking out origin/main in the checkout this script is in (the daily
# checkout, under launchd) does not rewrite the file bash is reading.
out=${GATE_DAILY_OUT:-$HOME/repos/scratch-archive/gate30/daily}
mkdir -p "$out"
if [ -z "${GATE_DAILY_SELF:-}" ]; then
  here=$(cd "$(dirname "$0")/.." && pwd)
  copy=$(mktemp "$out/.gate-daily.XXXXXX")
  cp "$0" "$copy"
  GATE_DAILY_SELF=$copy GATE_DAILY_HERE=$here exec bash "$copy" "$@"
fi
here=$GATE_DAILY_HERE
force=0
case "${1:-}" in
  "") ;;
  --force) force=1 ;;
  *) echo "usage: scripts/gate-daily.sh [--force]"; rm -f "$GATE_DAILY_SELF"; exit 2 ;;
esac

dir=${GATE_DAILY_DIR:-$HOME/repos/borrow-core-daily}
limit=${GATE_DAILY_LIMIT:-4h}
unit=${GATE_DAILY_UNIT:-gate30}
board=${GATE_DAILY_BOARD:-$HOME/repos/scratch-archive/board/board}
sampler=${GATE_DAILY_SAMPLER:-$HOME/repos/scratch-archive/gate30/tools/gate-measure.sh}
gatecmd=${GATE_DAILY_CMD:-$HOME/repos/scripts-local/gate-serial.sh gate-full}
verdicts=$out/verdicts.tsv
lock=$out/.lock

say() { echo "gate-daily: $*"; }
note() { # note BODY [FILE]: the verdict note to the coordinator, body cut to the board's 400
  local body=${1:0:400}
  BOARD_AS=gate-daily "$board" note verdict --to coordinator --unit "$unit" ${2:+--file "$2"} "$body" ||
    say "could not post the board note: $body"
}
cannot() { say "$*"; note "daily gate-full on main could not run: $*"; exit 2; }

# 1. The lock. A lock whose owner has exited is stale and taken over (`kill -0` only asks
# whether the process exists).
until mkdir "$lock" 2>/dev/null; do
  pid=$(cat "$lock/pid" 2>/dev/null || true)
  if [ -n "$pid" ] && kill -0 "$pid" 2>/dev/null; then
    say "a daily run is already going (pid $pid): nothing to do"; rm -f "$GATE_DAILY_SELF"; exit 0
  fi
  [ -n "$pid" ] || [ -n "$(find "$lock" -maxdepth 0 -mmin +1 2>/dev/null)" ] || { sleep 1; continue; }
  rm -rf "$lock"
done
echo $$ > "$lock/pid"
trap 'rm -rf "$lock"; rm -f "$GATE_DAILY_SELF"' EXIT

# 2. The daily checkout. Its mark lives in the worktree's own git directory, which `git clean`
# never touches.
mark() { local g; g=$(git -C "$1" rev-parse --absolute-git-dir 2>/dev/null) && echo "$g/gate-daily"; }
case "$dir" in
  "$HOME/repos/borrow-core"|"$HOME/repos/borrow-core-team") cannot "refusing $dir: it is a shared checkout" ;;
esac
if [ ! -e "$dir" ]; then
  say "creating the daily checkout $dir"
  git -C "$here" fetch -q origin || cannot "git fetch failed in $here"
  git -C "$here" worktree add -q --detach "$dir" origin/main || cannot "git worktree add $dir failed"
  touch "$(mark "$dir")"
  from=${GATE_DAILY_LAKE_FROM:-$here}
  if [ -d "$from/.lake" ]; then
    say "cloning $from/.lake"
    cp -cR "$from/.lake" "$dir/.lake" 2>/dev/null || cp -R "$from/.lake" "$dir/.lake" ||
      cannot "cloning $from/.lake failed"
  fi
fi
m=$(mark "$dir") && [ -f "$m" ] || cannot "refusing $dir: not a git worktree marked as the daily checkout"

# 3. What to gate.
git -C "$dir" fetch -q origin || cannot "git fetch failed in $dir"
commit=$(git -C "$dir" rev-parse origin/main) || cannot "no origin/main in $dir"
short=${commit:0:8}
today=$(date +%F)
if [ "$force" = 0 ] && [ -f "$verdicts" ]; then
  if awk -F'\t' -v c="$commit" '$2 == c { f = 1 } END { exit !f }' "$verdicts"; then
    say "origin/main $short already has a verdict: $(awk -F'\t' -v c="$commit" '$2 == c { v = $3 } END { print v }' "$verdicts")"; exit 0
  fi
  if awk -F'\t' -v d="$today" 'substr($1, 1, 10) == d { f = 1 } END { exit !f }' "$verdicts"; then
    say "a daily run was already made today ($today); origin/main $short waits for tomorrow's"; exit 0
  fi
fi

# 4. Check it out.
git -C "$dir" reset -q --hard && git -C "$dir" clean -fdq && git -C "$dir" checkout -q --detach "$commit" ||
  cannot "checking out $short in $dir failed"

# 5. Run the gate.
mode=0
grep -q 'GATE_CACHE=record' "$dir/scripts/gate_cache.py" 2>/dev/null && mode=record
stem=$out/$(date +%Y%m%d-%H%M%S)-$short
log=$stem.log
measure=()
if [ -x "$sampler" ]; then
  mkdir -p "$out/measure"
  measure=("$sampler" "daily-$(basename "$stem")" --)
fi
say "gating origin/main $short in $dir (GATE_CACHE=$mode, limit $limit): $log"
started=$(date +%s)
{
  echo "gate-daily: origin/main $commit in $dir, GATE_CACHE=$mode, limit $limit, started $(date '+%F %T %z')"
  echo "gate-daily: command: $gatecmd"
  (cd "$dir" && GATE_CACHE=$mode GATE_MEASURE_DIR=$out/measure \
     /usr/bin/time -p -o "$stem.time" timeout --kill-after=120 "$limit" caffeinate -i \
     ${measure[@]+"${measure[@]}"} bash -c "$gatecmd")
} > "$log" 2>&1
rc=$?
wall=$(( $(date +%s) - started ))
cpu=$(awk '/^(user|sys) / { s += $2 } END { printf "%.0f", s }' "$stem.time" 2>/dev/null)
rm -f "$stem.time"
mfile=$out/measure/daily-$(basename "$stem").txt
[ ! -f "$mfile" ] || { echo; echo "gate-daily: the sampler's record ($mfile):"; cat "$mfile"; } >> "$log"

# 6. The verdict.
steps=$(sed -n 's/^    FAILED: \(.*\) ([0-9?]*s)$/\1/p' "$log" | paste -sd ',' - | sed 's/,/, /g')
if [ "$rc" = 124 ] || [ "$rc" = 137 ]; then verdict=TIMEOUT; steps=${steps:-"none failed before the limit"}
elif [ "$rc" = 0 ] && grep -q 'ALL PASSED' "$log"; then verdict=PASS
else verdict=FAIL; steps=${steps:-"no step failed; the gate exited $rc (see the log)"}
fi
lastpass=$( [ -f "$verdicts" ] && awk -F'\t' '$3 == "PASS" { c = $2 } END { print c }' "$verdicts")
printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$(date '+%FT%T%z')" "$commit" "$verdict" "${steps:--}" "$wall" "${cpu:-?}" "$log" >> "$verdicts"
ln -sf "$log" "$out/latest.log"

# 7. The note.
if [ "$verdict" = PASS ]; then
  say "PASS ($wall s)"
  note "daily gate-full on main $short: PASS (wall ${wall}s, CPU ${cpu:-?}s, GATE_CACHE=$mode)" "$log"
  exit 0
fi
if [ -n "$lastpass" ] && git -C "$dir" merge-base --is-ancestor "$lastpass" "$commit" 2>/dev/null; then
  merges=$(git -C "$dir" log --merges --oneline "$lastpass..$commit")
  since="merges since the last pass ${lastpass:0:8}"
else
  merges=$(git -C "$dir" log --merges --oneline -20 "$commit")
  since="no earlier pass on this history; the last 20 merges"
fi
{ echo; echo "gate-daily: $verdict on $short; failing: $steps"; echo "gate-daily: $since:"; echo "$merges"; } >> "$log"
prs=$(echo "$merges" | grep -o 'pull request #[0-9]*' | sed 's/pull request //' | paste -sd ' ' -)
say "$verdict: $steps"
note "daily gate-full on main $short: $verdict. Failing: $steps. $since: ${prs:-none}. Log: $log" "$log"
exit 1

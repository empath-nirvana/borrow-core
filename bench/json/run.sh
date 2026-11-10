#!/bin/bash
# #977's timing run. Holds the gate lock (`~/repos/.gate-lock`, gate-serial's convention: a
# directory made by `mkdir`, its `owner` the holder's pid first) for the whole run so that no gate
# starts meanwhile, and releases it on exit. Then: the data checked (`fetch.sh`), both sides
# built (`measure.py build`), their outputs checked (`check.sh`), and the timing
# (`measure.py time`, which discards a run on a loaded or busy machine). Arguments go to
# `measure.py time`. Ask the coordinator for a quiet window first; never pkill anything.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
lock="$HOME/repos/.gate-lock"
until mkdir "$lock" 2>/dev/null; do
  holder=$(cat "$lock/owner" 2>/dev/null || true)
  pid=${holder%% *}
  if [ -n "$pid" ] && ! kill -0 "$pid" 2>/dev/null; then rm -rf "$lock"; continue; fi
  echo "run.sh: waiting for the gate lock, held by $holder" >&2; sleep 30
done
echo "$$ #977 bench $$" > "$lock/owner"
release() { [ "$(cut -d' ' -f1 "$lock/owner" 2>/dev/null)" = "$$" ] && rm -rf "$lock"; }
trap release EXIT
echo "run.sh: holding $lock"
"$here/fetch.sh"
python3 -I "$here/measure.py" build
"$here/check.sh"
python3 -I "$here/measure.py" time "$@"

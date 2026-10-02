#!/usr/bin/env bash
# Runs this experiment's checked programs: each bc/*.bc is checked and run compiled (`bcc run`)
# and by the model's interpreter (`bcc interp`); both must print bc/<name>.out. The programs in
# sketches/ are not checked: they need the relaxations of docs/outlives-strictness.md §3 in the
# checker, which this experiment does not change.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../.." && pwd)"
cd "$root"
lake build bcc >/dev/null
bcc="$root/.lake/build/bin/bcc"
bad=0
for f in "$here"/bc/*.bc; do
  n=$(basename "${f%.bc}")
  run=$("$bcc" run "$f" 2>&1) || { echo "$n: run failed: $run"; bad=1; continue; }
  interp=$("$bcc" interp "$f" 2>&1) || { echo "$n: interp failed: $interp"; bad=1; continue; }
  [ "$run" = "$interp" ] || { echo "$n: run and interp differ"; bad=1; }
  [ "$run" = "$(cat "$here/bc/$n.out")" ] || { echo "$n: output differs from bc/$n.out: $run"; bad=1; }
  echo "ok  bc/$n.bc  $(echo "$run" | head -1)"
done
exit $bad

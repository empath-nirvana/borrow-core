#!/usr/bin/env bash
# B2.2/B2.3: the cached form (UNCHECKED) applied to the proven program and to the three typed
# programs whose owner changes between steps, at the files' sizes (n = 200, tasks = 3). Each is
# compiled by `bcc`, edited by `cache_edit.py`, and linked with `cached_step.c` built with
# `-DCHECK_STALE`, which counts every popped position whose cell is no longer a live node (a read
# of a freed cell). Prints the answer, `live`, and the count. The proven answer of each is 297900.
#
#     experiments/e2-spike/b2/cached_check.sh [workdir]      (from the repository root)
set -e
cd "$(dirname "$0")/../../.."
here=experiments/e2-spike/b2
out=${1:-$HOME/repos/682b-work/cached-check}
mkdir -p "$out"
python3 - "$out/runtime.c" <<'PY'
import sys
src = open("Backend/Native/Runtime.lean").read()
s = src.index('r##"', src.index("def runtimeC")) + 4
open(sys.argv[1], "w").write(src[s:src.index('"##', s)])
PY
run() {
  local name=$1; shift
  .lake/build/bin/bcc compile --backend new --target native "$here/$name.bc" -o "$out/$name.ll"
  xcrun clang -O2 -w -pthread "$out/$name.ll" "$out/runtime.c" -o "$out/$name"
  python3 "$here/cache_edit.py" "$out/$name.ll" "$out/$name.cached.ll" "$@" > /dev/null
  xcrun clang -O2 -flto -w -pthread -DCHECK_STALE "$out/$name.cached.ll" "$here/cached_step.c" "$out/runtime.c" -o "$out/$name.cached"
  echo "$name | proven: $("$out/$name" 2>&1 | tr '\n' ' ')| cached${1:+ ($*)}: $("$out/$name.cached" 2>&1 | tr '\n' ' ')"
}
run p1-r3-owned-reborrow
run inv-b-owner-mutated --hook auto 50
run inv-c-owner-moved --move 50
run inv-c2-owner-moved-fresh --move-fresh 50

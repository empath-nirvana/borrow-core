#!/usr/bin/env bash
# The corpus files `Frontend/Check/CrossCheck.lean` reads at elaboration (`bcc_program% "…"`) are
# in its build trace, under its library's `needs` (the `CrossCheck` library of lakefile.toml), so
# that an edit to one rebuilds it. Fails if any is not: the library order of lakefile.toml, or a
# file read without an `[[input_file]]`, would otherwise let a stale CrossCheck build pass.
#
#     scripts/check-crosscheck-trace.sh      (after `lake build`)
set -euo pipefail
cd "$(dirname "$0")/.."
python3 - <<'PY'
import json, os, re, sys
src = "Frontend/Check/CrossCheck.lean"
trace = ".lake/build/lib/lean/Frontend/Check/CrossCheck.trace"
read = sorted(set(re.findall(r'bcc_program%\s+"([^"\s]+\.bc)"', open(src, encoding="utf-8").read())))
if not read:
    print(f"check-crosscheck-trace: {src} reads no corpus file (bcc_program%)"); sys.exit(1)
try:
    t = json.load(open(trace))
except OSError:
    print(f"check-crosscheck-trace: no {trace}: build first"); sys.exit(1)
def deps(x, out):
    if isinstance(x, list):
        if len(x) == 2 and isinstance(x[0], str) and isinstance(x[1], list) and x[0].endswith(":extraDep"):
            for e in x[1]:
                if isinstance(e, list) and e and isinstance(e[0], str): out.add(e[0])
        for y in x: deps(y, out)
    return out
traced = {os.path.relpath(p, os.getcwd()) for p in deps(t.get("inputs", []), set()) if os.path.isabs(p)}
missing = [f for f in read if f not in traced]
if missing:
    print(f"check-crosscheck-trace: {src} reads {', '.join(missing)}, not in its build trace "
          "(lakefile.toml: the CrossCheck library, after Frontend, with an [[input_file]] for each)")
    sys.exit(1)
print(f"check-crosscheck-trace: the {len(read)} corpus files CrossCheck reads are in its build trace")
PY

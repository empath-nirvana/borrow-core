#!/usr/bin/env bash
# No `sorry`, `axiom`, `native_decide`, `implemented_by`, `opaque`, `partial`,
# `unsafe` in Paper/, Support/, Examples/, Core/, Frontend/, Target/, Pipeline/, Backend/ and Backend2/,
# outside comments; then every declaration's axioms.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 - <<'PY'
import re, pathlib, sys
BAD = re.compile(r"\b(sorry|axiom|native_decide|implemented_by|opaque|partial|unsafe)\b")
hits = 0
files = []
for d in ("Paper", "Support", "Examples", "Core", "Frontend", "Target", "Pipeline", "Backend", "Backend2"):
    files += sorted(pathlib.Path(d).glob("**/*.lean")) + [pathlib.Path(d + ".lean")]
for p in files:
    src = p.read_text(encoding="utf-8")
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i): depth += 1; i += 2; continue
        if depth and src.startswith("-/", i): depth -= 1; i += 2; continue
        if not depth and src.startswith("--", i):
            j = src.find("\n", i); i = len(src) if j < 0 else j; continue
        if not depth: out.append(src[i])
        i += 1
    code = "".join(out)
    for m in BAD.finditer(code):
        line = code[:m.start()].count("\n") + 1
        print(f"{p}:{line}: {m.group(0)}"); hits += 1
print(f"{hits} forbidden keyword(s) outside comments.")
sys.exit(1 if hits else 0)
PY
# Frontend/, Target/, Pipeline/, Backend/ and Backend2/ import only the library (and Lean's `Std`), never experiments/.
if grep -rhE '^import ' Frontend Frontend.lean Target Target.lean Pipeline Pipeline.lean Backend Backend.lean \
    Backend2 Backend2.lean \
    | grep -vE '^import +(Frontend|Target|Pipeline|Backend|Backend2|Support|Paper|Examples|Core|Std)([. ]|$)'; then
  echo "Frontend/, Target/, Pipeline/, Backend/ or Backend2/ imports a module outside the library."; exit 1
fi
# The prelude declares no `type` abbreviation: the data table reads none from it
# (`Parser.tableOf`, SPEC §61), so one would not be opened around a recursive declaration.
if grep -nE '^type ' lib/prelude.bc; then
  echo "lib/prelude.bc declares a type abbreviation, which Parser.tableOf does not read (SPEC §61)."; exit 1
fi
# The extended judgment of SPEC §29 and the typed term of SPEC §3 are generated from `CDerives`:
# they must be up to date.
python3 scripts/gen-pin.py --check
lake env lean --run scripts/CheckAxioms.lean

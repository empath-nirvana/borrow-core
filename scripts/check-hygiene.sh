#!/usr/bin/env bash
# No `sorry`, `axiom`, `native_decide`, `implemented_by`, `opaque`, `partial`,
# `unsafe` in Paper/, Support/, Examples/, Core/, Frontend/, Target/, Pipeline/, Reference/, Backend/
# and Backend2/, and in the tree archive research/tree/,
# outside comments; then every declaration's axioms.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 - <<'PY'
import re, pathlib, sys
BAD = re.compile(r"\b(sorry|axiom|native_decide|implemented_by|opaque|partial|unsafe)\b")
hits = 0
files = []
for d in ("Paper", "Support", "Examples", "Core", "Frontend", "Target", "Pipeline", "Reference", "Backend", "Backend2"):
    files += sorted(pathlib.Path(d).glob("**/*.lean")) + [pathlib.Path(d + ".lean")]
files += sorted(pathlib.Path("research/tree/ResearchTree").glob("**/*.lean")) + [pathlib.Path("research/tree/ResearchTree.lean")]  # the tree archive (#1133)
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
# Frontend/, Target/, Pipeline/, Reference/, Backend/ and Backend2/ import only the library (and Lean's `Std`), never experiments/.
if grep -rhE '^import ' Frontend Frontend.lean Target Target.lean Pipeline Pipeline.lean Reference Reference.lean \
    Backend Backend.lean Backend2 Backend2.lean \
    | grep -vE '^import +(Frontend|Target|Pipeline|Reference|Backend|Backend2|Support|Paper|Examples|Core|Std)([. ]|$)'; then
  echo "Frontend/, Target/, Pipeline/, Reference/, Backend/ or Backend2/ imports a module outside the library."; exit 1
fi
# The library and the compiler never import the tree archive (research/tree, #1133).
if grep -rlE '^import +ResearchTree([. ]|$)' Paper Support Examples Core Frontend Target Pipeline Reference \
    Backend Backend2 Paper.lean Support.lean Examples.lean Core.lean Frontend.lean Target.lean Pipeline.lean \
    Reference.lean Backend.lean Backend2.lean; then
  echo "A module of the library or the compiler imports the tree archive (ResearchTree)."; exit 1
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

#!/usr/bin/env bash
# No `sorry`, `axiom`, `native_decide`, `implemented_by`, `opaque`, `partial`,
# `unsafe` in Paper/, Support/, Examples/, Core/, Frontend/, Target/, Pipeline/, Reference/, Backend/
# and Backend2/, and in the tree archive research/tree/,
# outside comments; that CrossCheck's corpus files are in its build trace; then every
# declaration's axioms.
set -euo pipefail
cd "$(dirname "$0")/.."
# One unit of the result cache (scripts/gate_cache.py `step`): a recorded pass is replayed when
# the Lean sources, Lake's configuration, scripts/, the tools and lib/prelude.bc are as they were.
[ "${GATE_CACHE_INNER:-}" = hygiene ] || exec python3 scripts/gate_cache.py step hygiene lean --files lib/prelude.bc -- scripts/check-hygiene.sh "$@"
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
# The corpus files CrossCheck reads at elaboration are in its build trace.
scripts/check-crosscheck-trace.sh
# Every declaration's axioms (`gate-census axioms`), then the census's negative test in the same
# run: declarations that reach an axiom outside the three, elaborated into the environment, must
# each be reported.
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cat > "$tmp/Neg.lean" <<'LEAN'
axiom Core.negAxiom : False
theorem Core.negThm : 1 = 2 := Core.negAxiom.elim
def Core.negSorry : Nat := sorry
LEAN
mkdir "$tmp/c"
scripts/gate-census.sh --out "$tmp/c" axioms "axioms+$tmp/Neg.lean"
cat "$tmp/c/axioms.out"
[ "$(cat "$tmp/c/axioms.status")" = 0 ] || exit 1
if [ "$(cat "$tmp/c/axioms-neg.status")" = 0 ]; then
  echo "check-hygiene: the axioms census's negative test passed"; cat "$tmp/c/axioms-neg.out"; exit 1
fi
for want in "Core.negThm depends on axiom Core.negAxiom" "Core.negSorry depends on axiom sorryAx"; do
  if ! grep -qxF "$want" "$tmp/c/axioms-neg.out"; then
    echo "check-hygiene: the axioms census's negative test lacks: $want"; cat "$tmp/c/axioms-neg.out"; exit 1
  fi
done

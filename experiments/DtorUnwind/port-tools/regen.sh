#!/bin/bash
# Regenerate the ported files in order. Usage: regen.sh [FIRST]
set -e
cd ~/repos/borrow-core-tree-life
S=$(cd "$(dirname "$0")" && pwd)
P=experiments/DtorUnwind/DtorUnwind/Tree/Port
gen() { # name imports sources...
  local name=$1; local imps=$2; shift 2
  python3 $S/port.py $P/$name.lean $imps -- "$@"
  python3 $S/fixups.py $name $P/$name.lean
  if [ "$name" = AlgebraInstances ]; then
    python3 - "$P/$name.lean" "$S/AlgebraInstances_tail.lean.txt" <<'PY'
import sys
f, t = sys.argv[1], sys.argv[2]
s = open(f).read().rstrip()
if s.endswith('\nend'): s = s[:-4]
open(f, 'w').write(s + open(t).read())
PY
  fi
  echo "== $name"
  lake build DtorUnwind.Tree.Port.$name 2>&1 | grep -A12 "error:" | head -40 || true
}
STEPS=(
"Walks|DtorUnwind.Tree.Port.Base|Support/Model/Walks.lean"
"WalkSplitting|DtorUnwind.Tree.Port.Walks|Support/Model/WalkSplitting.lean"
"Flattening|DtorUnwind.Tree.Port.WalkSplitting|Support/Model/Flattening.lean"
"Singletons|DtorUnwind.Tree.Port.WalkSplitting|Support/Model/Singletons.lean"
"Compatibility|DtorUnwind.Tree.Port.Singletons|Support/Model/Compatibility.lean"
"Split|DtorUnwind.Tree.Port.Compatibility,DtorUnwind.Tree.Port.Flattening|Paper/S6_1_StandardLemmas/Lemmas.lean:243-1722"
"AlgebraInstances|DtorUnwind.Tree.Port.Cells|Support/Model/AlgebraInstances.lean"
"FlatteningCells|DtorUnwind.Tree.Port.AlgebraInstances|Support/Model/FlatteningCells.lean"
"RelaxedWalks|DtorUnwind.Tree.Port.FlatteningCells|Support/Model/RelaxedWalks.lean"
"Update|DtorUnwind.Tree.Port.RelaxedWalks,DtorUnwind.Tree.Port.Cells|Support/Model/Update.lean"
"Ancestors|DtorUnwind.Tree.Port.Update|Support/Model/Ancestors.lean"
"UpdateFrame|DtorUnwind.Tree.Port.Ancestors|Support/Model/UpdateFrame.lean"
"AgBeneath|DtorUnwind.Tree.Port.UpdateFrame|Paper/S6_2_NonStandardLemmas/Lemmas.lean:1159-1262"
"Six48|DtorUnwind.Tree.Port.AgBeneath|Paper/S6_2_NonStandardLemmas/Lemmas.lean:1947-2371"
"Reborrow|DtorUnwind.Tree.Port.RebDef|Support/Model/Reborrow.lean"
"ReborrowFrame|DtorUnwind.Tree.Port.Reborrow|Support/Model/ReborrowFrame.lean"
"ReborrowLowering|DtorUnwind.Tree.Port.ReborrowFrame|Support/Model/Restriction.lean Support/Model/ReborrowLowering.lean"
"Subtraction|DtorUnwind.Tree.Port.SubDef|Support/Model/Subtraction.lean"
"Six25to33|DtorUnwind.Tree.Port.Subtraction|Support/Model/Surgery.lean:30-40 $S/end_fig16.lean.txt Paper/S6_2_NonStandardLemmas/Lemmas.lean:395-585"
"Six28to29|DtorUnwind.Tree.Port.SurgeryB|Paper/S6_2_NonStandardLemmas/Lemmas.lean:673-998"
)
for st in "${STEPS[@]}"; do
  IFS='|' read -r name imps srcs <<< "$st"
  if [ -n "$1" ] && [ "$started" != 1 ] && [ "$name" != "$1" ]; then continue; fi
  started=1
  gen "$name" "$imps" $srcs
done

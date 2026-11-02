#!/bin/bash
# Regenerate the generated files of Support/Model/Tree/Port from the printed sources, in
# dependency order.
#   scripts/tree-port/regen.sh [FIRST]   rewrite each file in place (from FIRST on) and build it
#                                        (NOBUILD=1: rewrite only)
#   scripts/tree-port/regen.sh --check   regenerate every file into a temporary directory and
#                                        fail unless each equals the checked-in one
set -e
S=$(cd "$(dirname "$0")" && pwd)
cd "$S/../.."
P=Support/Model/Tree/Port
check=0
if [ "$1" = --check ]; then check=1; shift; tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT; fi
bad=0
gen() { # name imports sources...
  local name=$1; local imps=$2; shift 2
  local out=$P/$name.lean
  [ "$check" = 1 ] && out=$tmp/$name.lean
  python3 "$S/port.py" "$out" "$imps" -- "$@"
  python3 "$S/fixups.py" "$name" "$out"
  if [ "$name" = AlgebraInstances ]; then
    python3 - "$out" "$S/AlgebraInstances_tail.lean.txt" <<'PY'
import sys
f, t = sys.argv[1], sys.argv[2]
s = open(f).read().rstrip()
if s.endswith('\nend'): s = s[:-4]
open(f, 'w').write(s + open(t).read())
PY
  fi
  if [ "$check" = 1 ]; then
    if ! diff -q "$out" "$P/$name.lean" >/dev/null; then
      echo "tree-port: $P/$name.lean differs from its regeneration"; diff "$out" "$P/$name.lean" | head -20; bad=1
    fi
  else
    echo "== $name"
    [ -n "$NOBUILD" ] || { lake build Support.Model.Tree.Port.$name 2>&1 | grep -A12 "error:" | head -40 || true; }
  fi
}
STEPS=(
"Walks|Support.Model.Tree.Port.Base|Support/Model/Walks.lean"
"WalkSplitting|Support.Model.Tree.Port.Walks|Support/Model/WalkSplitting.lean"
"Flattening|Support.Model.Tree.Port.WalkSplitting|Support/Model/Flattening.lean"
"Singletons|Support.Model.Tree.Port.WalkSplitting|Support/Model/Singletons.lean"
"Compatibility|Support.Model.Tree.Port.Singletons|Support/Model/Compatibility.lean"
"Split|Support.Model.Tree.Port.Compatibility,Support.Model.Tree.Port.Flattening|Paper/S6_1_StandardLemmas/Lemmas.lean:243-1722"
"AlgebraInstances|Support.Model.Tree.Port.Cells|Support/Model/AlgebraInstances.lean"
"FlatteningCells|Support.Model.Tree.Port.AlgebraInstances|Support/Model/FlatteningCells.lean"
"RelaxedWalks|Support.Model.Tree.Port.FlatteningCells|Support/Model/RelaxedWalks.lean"
"Update|Support.Model.Tree.Port.RelaxedWalks,Support.Model.Tree.Port.Cells|Support/Model/Update.lean"
"Ancestors|Support.Model.Tree.Port.Update|Support/Model/Ancestors.lean"
"UpdateFrame|Support.Model.Tree.Port.Ancestors|Support/Model/UpdateFrame.lean"
"AgBeneath|Support.Model.Tree.Port.UpdateFrame|Paper/S6_2_NonStandardLemmas/Lemmas.lean:1159-1262"
"Six48|Support.Model.Tree.Port.AgBeneath|Paper/S6_2_NonStandardLemmas/Lemmas.lean:1947-2371"
"Reborrow|Support.Model.Tree.Port.RebDef|Support/Model/Reborrow.lean"
"ReborrowFrame|Support.Model.Tree.Port.Reborrow|Support/Model/ReborrowFrame.lean"
"ReborrowLowering|Support.Model.Tree.Port.ReborrowFrame|Support/Model/Restriction.lean Support/Model/ReborrowLowering.lean"
"Subtraction|Support.Model.Tree.Port.SubDef|Support/Model/Subtraction.lean"
"Six25to33|Support.Model.Tree.Port.Subtraction|Support/Model/Surgery.lean:30-40 $S/end_fig16.lean.txt Paper/S6_2_NonStandardLemmas/Lemmas.lean:395-585"
"Six28to29|Support.Model.Tree.Port.SurgeryB|Paper/S6_2_NonStandardLemmas/Lemmas.lean:673-998"
"SurgeryC|Support.Model.Tree.Port.Six28to29|Support/Model/Surgery.lean:31-32 Support/Model/Surgery.lean:156-386"
"Six34to39|Support.Model.Tree.Port.SurgeryC|Paper/S6_2_NonStandardLemmas/Remarks.lean:17-115 Paper/S6_2_NonStandardLemmas/Lemmas.lean:1024-1155 Paper/S6_2_NonStandardLemmas/Lemmas.lean:1159-1160 Paper/S6_2_NonStandardLemmas/Lemmas.lean:1263-1776"
"ClosingSentence|Support.Model.Tree.Port.Six34to39|Support/Model/ClosingSentence.lean"
"Six49to52|Support.Model.Tree.Port.OutlivesB|Paper/S6_2_NonStandardLemmas/Lemmas.lean:2372-2690"
"Six43to46|Support.Model.Tree.Port.Six49to52|Paper/S6_2_NonStandardLemmas/Lemmas.lean:1790-1850 Paper/S6_2_NonStandardLemmas/Lemmas.lean:1918-1943"
"Six53to59|Support.Model.Tree.Port.Six43to46|Paper/S6_2_NonStandardLemmas/Lemmas.lean:2694-3598"
)
for st in "${STEPS[@]}"; do
  IFS='|' read -r name imps srcs <<< "$st"
  if [ -n "$1" ] && [ "$started" != 1 ] && [ "$name" != "$1" ]; then continue; fi
  started=1
  gen "$name" "$imps" $srcs
done
if [ "$check" = 1 ]; then
  [ "$bad" = 0 ] && echo "tree-port: every generated file equals its regeneration"
  exit $bad
fi

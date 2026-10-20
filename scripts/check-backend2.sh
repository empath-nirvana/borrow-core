#!/usr/bin/env bash
# The new backend's fence and ban list (docs/compiler.md §5.2, docs/n1-plan.md). Fails when:
#
#   * a module of Backend2/ other than Backend2/Driver.lean (the one contact with the frontend)
#     imports, directly or through the repository's modules, anything of the old backend's
#     reconstruction (Backend.Clos.*, Backend.Flat.Lower, Backend.Driver) or of the elaboration
#     (Frontend.Elab.*, Frontend.Sugar, Frontend.Parser);
#   * a module of Backend2/ names the erasure (`.erase`), matches on the untyped term's
#     constructors, or names a pass the new backend replaces (a recogniser of user code, a
#     unifier of types, an ownership inference from occurrences).
#
#     scripts/check-backend2.sh
set -euo pipefail
cd "$(dirname "$0")/.."
fail=0

# The repository modules a module imports.
imports() { sed -n 's/^import \([A-Za-z0-9_.]*\).*/\1/p' "$1"; }
fileOf() { echo "${1//.//}.lean"; }

banned='^(Backend\.Clos(\..*)?|Backend\.Flat\.Lower|Backend\.Driver|Frontend\.Elab(\..*)?|Frontend\.Sugar|Frontend\.Parser)$'

for m in Backend2/*.lean; do
  [ "$m" = Backend2/Driver.lean ] && continue
  # The transitive imports within the repository, breadth first.
  seen=" "
  todo=$(imports "$m")
  while [ -n "$todo" ]; do
    next=""
    for i in $todo; do
      case "$seen" in *" $i "*) continue ;; esac
      seen="$seen$i "
      if [[ "$i" =~ $banned ]]; then
        echo "check-backend2: $m imports $i (through its imports): outside the fence"
        fail=1
      fi
      f=$(fileOf "$i")
      [ -f "$f" ] && next="$next $(imports "$f")"
    done
    todo=$next
  done
done

# The ban list: the erasure, the untyped term, and the passes §3.6 deletes.
ban='TExpr\.erase|\.erase *$|\.erase *[])},]|\.main\.e\b|BoCa\.Expr|\bExpr\.(app|lam|val|var|pair|case|letpair|seq|inj)|isSwap|travShape|foldShape|fixBody|fixValue|litTable|litView\?|litTree|plan2|markScoped|markLitViews|markUbinds|polyLet|polySelect|collapse\?|tailClause|clausesAt|SFacts|UFacts|crossedScopes|unif'
if grep -nEi "$ban" Backend2/*.lean | grep -v '^Backend2/Driver.lean:' | grep -vE '^\S+:[0-9]+:\s*(--|/-|`|\*)' ; then
  echo "check-backend2: a banned name in Backend2/ (above)"
  fail=1
fi

[ $fail = 0 ] && echo "check-backend2: the fence and the ban list hold"
exit $fail

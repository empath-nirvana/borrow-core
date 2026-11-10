#!/usr/bin/env bash
# The new backend's fence and ban list (docs/compiler.md §5.2, docs/n1-plan.md), and the reference
# run's fence. Fails when:
#
#   * a module of Backend2/, Backend2/Driver.lean included, imports, directly or through the
#     repository's modules, any module of the old backend (`Backend` or `Backend.*`): what
#     Backend2 shares with it is in Target/ and Pipeline/;
#   * a module of Backend2/ other than Backend2/Driver.lean (the one contact with the frontend,
#     which parses and checks through Pipeline/Driver.lean) imports, directly or through the
#     repository's modules, the elaboration (Frontend.Elab.*, Frontend.Sugar, Frontend.Parser);
#   * a module of Backend2/ other than Backend2/Driver.lean names the erasure (`.erase`), matches
#     on the untyped term's constructors, or names a pass the new backend replaces (a recogniser
#     of user code, a unifier of types, an ownership inference from occurrences);
#   * a module of Reference/ (the reference run: the source stage and the falsifier), or its root
#     Reference.lean, imports, directly or through the repository's modules, any module of the
#     old backend (`Backend` or `Backend.*`): the reference run outlives the old backend.
#
#     scripts/check-backend2.sh
set -euo pipefail
cd "$(dirname "$0")/.."
fail=0

# The repository modules a module imports.
imports() { sed -n 's/^import \([A-Za-z0-9_.]*\).*/\1/p' "$1"; }
fileOf() { echo "${1//.//}.lean"; }

oldBackend='^Backend(\..*)?$'
frontend='^(Frontend\.Elab(\..*)?|Frontend\.Sugar|Frontend\.Parser)$'

for m in Backend2/*.lean; do
  # The transitive imports within the repository, breadth first.
  seen=" "
  todo=$(imports "$m")
  while [ -n "$todo" ]; do
    next=""
    for i in $todo; do
      case "$seen" in *" $i "*) continue ;; esac
      seen="$seen$i "
      if [[ "$i" =~ $oldBackend ]] ||
         { [ "$m" != Backend2/Driver.lean ] && [[ "$i" =~ $frontend ]]; }; then
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

# The reference run's fence: no module of Reference/ reaches the old backend.
for m in Reference.lean $(find Reference -name '*.lean' | sort); do
  seen=" "
  todo=$(imports "$m")
  while [ -n "$todo" ]; do
    next=""
    for i in $todo; do
      case "$seen" in *" $i "*) continue ;; esac
      seen="$seen$i "
      if [[ "$i" =~ $oldBackend ]]; then
        echo "check-backend2: $m imports $i (through its imports): Reference/ must not reach Backend/"
        fail=1
      fi
      f=$(fileOf "$i")
      [ -f "$f" ] && next="$next $(imports "$f")"
    done
    todo=$next
  done
done

[ $fail = 0 ] && echo "check-backend2: the fences (Backend2/, Reference/) and the ban list hold"
exit $fail

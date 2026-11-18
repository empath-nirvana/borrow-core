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
# One unit of the result cache (scripts/gate_cache.py `step`): a recorded pass is replayed when
# the Lean sources, Lake's configuration, scripts/ and the tools are as they were.
[ "${GATE_CACHE_INNER:-}" = backend2-fence ] || exec python3 scripts/gate_cache.py step backend2-fence lean -- scripts/check-backend2.sh "$@"
fail=0

# The fences, in one process: each module's transitive imports within the repository, breadth
# first from it (each file's `import` lines read once), and a message for each import outside its
# fence, in the order the walk meets them. The module lists are the shell's (its glob and sort
# order).
fences() {
  python3 - "$@" <<'PY'
import os, re, sys
IMPORT = re.compile(r"^import ([A-Za-z0-9_.]*)", re.M)
OLD = re.compile(r"Backend(\..*)?")
FRONT = re.compile(r"(Frontend\.Elab(\..*)?|Frontend\.Sugar|Frontend\.Parser)")
cache = {}
def imports(f):
    if f not in cache:
        with open(f, encoding="utf-8", errors="surrogateescape") as fh:
            cache[f] = [i for i in IMPORT.findall(fh.read()) if i]
    return cache[f]
fail = 0
mode, mods = sys.argv[1], sys.argv[2:]
for m in mods:
    seen = set()
    todo = imports(m)
    while todo:
        nxt = []
        for i in todo:
            if i in seen:
                continue
            seen.add(i)
            if mode == "backend2":
                if OLD.fullmatch(i) or (m != "Backend2/Driver.lean" and FRONT.fullmatch(i)):
                    print(f"check-backend2: {m} imports {i} (through its imports): outside the fence"); fail = 1
            elif OLD.fullmatch(i):
                print(f"check-backend2: {m} imports {i} (through its imports): Reference/ must not reach Backend/"); fail = 1
            f = i.replace(".", "/") + ".lean"
            if os.path.isfile(f):
                nxt += imports(f)
        todo = nxt
sys.exit(fail)
PY
}

fences backend2 Backend2/*.lean || fail=1

# The ban list: the erasure, the untyped term, and the passes §3.6 deletes.
ban='TExpr\.erase|\.erase *$|\.erase *[])},]|\.main\.e\b|BoCa\.Expr|\bExpr\.(app|lam|val|var|pair|case|letpair|seq|inj)|isSwap|travShape|foldShape|fixBody|fixValue|litTable|litView\?|litTree|plan2|markScoped|markLitViews|markUbinds|polyLet|polySelect|collapse\?|tailClause|clausesAt|SFacts|UFacts|crossedScopes|unif'
if grep -nEi "$ban" Backend2/*.lean | grep -v '^Backend2/Driver.lean:' | grep -vE '^\S+:[0-9]+:\s*(--|/-|`|\*)' ; then
  echo "check-backend2: a banned name in Backend2/ (above)"
  fail=1
fi

# The reference run's fence: no module of Reference/ reaches the old backend.
fences reference Reference.lean $(find Reference -name '*.lean' | sort) || fail=1

[ $fail = 0 ] && echo "check-backend2: the fences (Backend2/, Reference/) and the ban list hold"
exit $fail

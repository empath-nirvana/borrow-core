#!/usr/bin/env bash
# Tests of scripts/gate-tier.sh: for each set of changed paths, the tier it names and the steps it
# runs on every program, on some programs, or not at all. Also: a path no rule knows makes the tier
# `full` and is named; a checkout whose origin cannot be fetched gets `full` and says why.
set -uo pipefail
cd "$(dirname "$0")/.."
bad=0
# has GREP-ARGS…: grep in the plan held in $p (a here-string, not a pipe: under pipefail an early
# `grep -q` exit can fail the writer with SIGPIPE and turn a match into a miss).
has() { grep "$@" <<< "$p"; }
# plan PATHS…: the plan for those changed paths.
plan() { printf '%s\n' "$@" | scripts/gate-tier.sh --plan --paths --base 0000000000000000; }
# expect "PATHS" TIER [+STEP (every program)] [~STEP (named files)] [-STEP (left out)] [=TEXT (in the tier line)]
#   [@BUILD (none, bins or all)]
expect() {
  local paths=$1 tier=$2 p got e s
  shift 2
  # shellcheck disable=SC2086
  p=$(plan $paths)
  got=$(printf '%s\n' "$p" | sed -n 's/^tier //p')
  [ "$got" = "$tier" ] || { echo "FAIL [$paths]: tier $got, want $tier"; bad=$((bad + 1)); return; }
  # Hygiene reads CrossCheck's build (check-crosscheck-trace.sh): it never runs without the whole build.
  if has -qx 'run hygiene + axioms' && ! has -qx 'build all'; then
    echo "FAIL [$paths]: hygiene runs without the whole build"; bad=$((bad + 1))
  fi
  for e in "$@"; do
    s=${e:1}
    case "$e" in
      +*) has -qxF "run $s" || { echo "FAIL [$paths]: $s not on every program"; bad=$((bad + 1)); } ;;
      ~*) has -q "^run $s	" || { echo "FAIL [$paths]: $s not on named files"; bad=$((bad + 1)); } ;;
      -*) ! has -q "^run $s\(	\|$\)" || { echo "FAIL [$paths]: $s runs"; bad=$((bad + 1)); } ;;
      @*) has -qx "build $s" || { echo "FAIL [$paths]: build is not $s"; bad=$((bad + 1)); } ;;
      =*) has '^line ' | grep -F "$s" > /dev/null || { echo "FAIL [$paths]: line lacks '$s'"; bad=$((bad + 1)); } ;;
    esac
  done
  echo "ok: [$paths] -> $tier"
}

expect "docs/overview.md SPEC.md experiments/X.lean" docs +"spec files" +"judgment freeze" -"parse corpus" -"hygiene + axioms"
expect "" docs +"spec files" -"check corpus"
expect "book/src/guide/intro.md" book +"book doc-tests" +"book build" -"check corpus"
expect "corpus/int-slash.bc" corpus ~"check corpus" ~"corpus (Backend2)" ~"native" +"clause kinds" -"hygiene + axioms" -"let mut combos"
expect "corpus/name-clash.out" corpus ~"corpus (old backend)" ~"renaming"
expect "corpus/reject/$(ls corpus/reject | sed -n 1p)" corpus ~"check corpus" ~"renaming" -"corpus (Backend2)"
expect "corpus/counts-backend2.expected" corpus +"corpus (Backend2)" -"corpus (old backend)"
expect "corpus/deep-list.bc" corpus +"native" ~"corpus (Backend2)"
expect "research/tree/ResearchTree.lean" research +"research archive" +"hygiene + axioms" -"check corpus"
expect "Backend2/Convert.lean" compiler +"hygiene + axioms" +"check corpus" +"corpus (Backend2, final)" +"corpus (old backend, final)" +"compile scaling" -"renaming" -"let mut combos" -"corpus (Backend2)" ="cut 2"
expect "Frontend/Sugar.lean" compiler +"renaming" +"let mut combos" ="+R: Frontend/"
expect "Core/Judgment.lean" compiler +"renaming" +"axiom report"
expect "Paper/S1_Syntax/Definitions.lean" compiler +"renaming"
expect "lib/prelude.bc" compiler +"renaming" +"check corpus" -"hygiene + axioms"
expect "Frontend/Sugar.lean corpus/int-slash.bc" compiler +"check corpus" ~"corpus (Backend2)" ~"native facts"
expect "corpus/13-1-library.bc" compiler +"check corpus" ~"corpus (Backend2)" +"renaming"
expect "scripts/check-sugar.sh" scripts +"sugar pairs" +"check corpus" -"renaming"
expect "scripts/native-facts.sh" scripts +"native facts" -"native" @bins
expect "scripts/TypeEq.lean" scripts +"type equality" @all
expect "scripts/pin/TExpr.tmpl.lean" scripts +"hygiene + axioms" @all
expect "docs/x.md" docs @none
expect "corpus/int-slash.bc" corpus @bins
expect "Core/Judgment.lean" compiler @all
expect "scripts/falsify.sh" docs -"check corpus"
expect "scripts/gate-daily.sh scripts/gate-daily.plist" docs @none -"check corpus"
expect "scripts/par.sh" full +"native" +"renaming"
expect "lakefile.toml" full +"corpus (Backend2)"
expect "Makefile docs/x.md" full +"cell classes"
expect "README.md weird/thing.txt" full +"native" ="unrecognised, so full: weird/thing.txt"
expect "corpus/skips.expected" corpus +"corpus (Backend2)" +"native" +"check corpus" -"renaming"
expect "scripts/corpus-set.sh" full
expect "scripts/slot" full
expect "scripts/GateCensus/View.lean" scripts +"type equality" +"hygiene + axioms" @all
expect "scripts/census-neg/pins.lean" scripts +"insertion pins" @all
expect "scripts/native-run.sh" scripts +"native" +"corpus (Backend2)" @bins
expect "scripts/check-crosscheck-trace.sh" scripts +"hygiene + axioms" @all
expect "corpus/aoc/new.py" full ="unrecognised, so full: corpus/aoc/new.py"

# A rename counts as its old path too: a Lean module moved into docs/ is a compiler change, staged
# or committed.
t=$(mktemp -d)
mkdir -p "$t/scripts" "$t/Core" "$t/docs" && cp scripts/gate-tier.sh "$t/scripts/"
echo 'def foo := 1' > "$t/Core/Foo.lean"
(cd "$t" && git init -q && git add -A && git -c user.email=t@t -c user.name=t commit -q -m t && git mv Core/Foo.lean docs/foo.md)
p1=$(cd "$t" && unset CI_LOCAL_BASE && scripts/gate-tier.sh --plan --base HEAD | sed -n 's/^tier //p')
(cd "$t" && git -c user.email=t@t -c user.name=t commit -q -m mv)
p2=$(cd "$t" && unset CI_LOCAL_BASE && scripts/gate-tier.sh --plan --base HEAD~1 | sed -n 's/^tier //p')
(cd "$t" && git rm -q docs/foo.md && git -c user.email=t@t -c user.name=t commit -q -m rm)
p3=$(cd "$t" && unset CI_LOCAL_BASE && scripts/gate-tier.sh --plan --base HEAD~2 | sed -n 's/^tier //p')
echo 'def foo := 1' > "$t/Core/Foo.lean"
(cd "$t" && git add -A && git -c user.email=t@t -c user.name=t commit -q -m back && rm Core/Foo.lean && ln -s ../docs Core/Foo.lean)
p4=$(cd "$t" && unset CI_LOCAL_BASE && scripts/gate-tier.sh --plan --base HEAD | sed -n 's/^tier //p')
rm -rf "$t"
if [ "$p1" = compiler ] && [ "$p2" = compiler ] && [ "$p3" = compiler ] && [ "$p4" = compiler ]; then
  echo "ok: a Lean module renamed into docs/ (staged, committed), deleted, or turned into a link -> compiler"
else echo "FAIL: rename/delete/type change of a Lean module: tiers $p1, $p2, $p3, $p4, want compiler"; bad=$((bad + 1)); fi

# A program at any depth is a program (scripts/corpus-set.sh decides, not the tier's own globs).
t=$(mktemp -d)
mkdir -p "$t/scripts" "$t/corpus/leetcode/deep/one" "$t/corpus/fail"
cp scripts/gate-tier.sh scripts/corpus-set.sh "$t/scripts/"
echo 'main = 1' > "$t/corpus/leetcode/deep/one/x.bc"; echo x > "$t/corpus/fail/y.bc"
p=$(cd "$t" && printf '%s\n' corpus/leetcode/deep/one/x.bc corpus/fail/y.bc | scripts/gate-tier.sh --plan --paths --base 0)
rm -rf "$t"
if has -q "^run corpus (Backend2)	corpus/leetcode/deep/one/x.bc$" &&
   has -q "^run parse corpus	corpus/fail/y.bc	corpus/leetcode/deep/one/x.bc$"; then
  echo "ok: a nested program runs in every program step; a fail/ file is parsed"
else echo "FAIL: nested program: $(has '^run ')"; bad=$((bad + 1)); fi

# No base: a checkout whose origin cannot be fetched.
t=$(mktemp -d)
mkdir "$t/scripts" && cp scripts/gate-tier.sh "$t/scripts/"
(cd "$t" && git init -q && git -c user.email=t@t -c user.name=t commit -q --allow-empty -m t &&
  git remote add origin "$t/nowhere")
p=$(unset CI_LOCAL_BASE; "$t/scripts/gate-tier.sh" --plan)
rm -rf "$t"
if has -qx 'tier full' && has -q '^line .*no base: origin could not be fetched'; then
  echo "ok: no fetchable origin -> full"
else echo "FAIL: no fetchable origin: $(has -E '^(tier|line) ')"; bad=$((bad + 1)); fi

echo "$bad failure(s)."
[ "$bad" -eq 0 ]

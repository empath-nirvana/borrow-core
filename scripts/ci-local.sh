#!/usr/bin/env bash
# The project's gate, run locally. Needs elan and wasmtime; mdbook is optional (the book build is
# skipped with a notice if absent), and so is a C compiler for the native target
# (scripts/compile-native.sh says so and passes).
#
#     scripts/ci-local.sh             the sanity gate (`make gate`): run before opening a PR
#     scripts/ci-local.sh --source    the full gate (`make gate-full`): every step, and the source
#                                     stage on every program
#     scripts/ci-local.sh --changed   for iteration only: the sanity gate's steps the changes since
#                                     origin/main can affect (below) (`make gate-fast`)
#
# The sanity gate (`gateSteps` below) checks that the library builds; hygiene (no forbidden
# keyword, every declaration's axioms within propext, Classical.choice and Quot.sound) and the
# axioms of the theorems SPEC.md names; the typing-judgment freeze and the new backend's import
# fence; that the corpus parses and checks; and that every corpus program, compiled to WebAssembly
# by each backend, prints its golden output with `live 0` (`compile-corpus.sh --final`,
# `compile-backend2.sh --final`: no intermediate-IR interpreter runs and no counts, except to name
# the first differing stage of a program whose WebAssembly run is wrong). The full gate runs every
# step in `steps`, the two corpus runs at every stage with their counts, and the compile-time
# guard (`compile scaling`).
#
# The source stage. A corpus program's `.out` and a book block's `-- answer:` are goldens: the
# output of `Support`'s interpreter (`bcc interp`), the reference semantics. Every compiled stage
# a step runs is checked against the golden. The interpreter itself is slow (minutes on the largest
# programs), so by default it runs only where a golden is unverified: on the corpus programs and
# book blocks that are new or changed since the merge base (scripts/source-stage.sh). With
# `--source`, it runs on every program and book block, and every golden is re-verified. The full
# gate is required when Paper/, Support/ (the interpreter and the machine) or Backend/ changed
# since the merge base; the sanity gate says so when they have. `--changed` never runs the
# interpreter: it lists the unverified programs instead.
#
# A gate builds everything (`lake build`), then (the full gate) runs the compile-time guard alone
# (it measures time), then every other step at once, each one's output printed in order as it
# finishes, with its wall time. The steps are independent: each reads the build and the sources,
# and writes only its own temporary files (and `mdbook` its `book/book`). The scripts skip their
# own `lake build` when this one has built (`CI_LOCAL_BUILT`); when the build fails, they run one
# after another, each trying its own build, as when run alone.
#
# `--changed` compares the working tree (committed, staged, unstaged and untracked files) with
# its merge base with origin/main (or with the commit `CI_LOCAL_BASE` names):
#   * a `.lean` file outside experiments/, the lakefile, the manifest or the toolchain: every
#     step of the sanity gate (the compiler imports the proofs, so every Lean change reaches it);
#   * otherwise no Lean step runs (no `lake build` of the library, no hygiene, no axioms): only
#     `lake build bcc bcc-counts`, and the sanity gate's steps whose inputs changed: corpus/ or lib/
#     for the corpus steps, a script for its own step (source-stage.sh for the corpus runs), and
#     ci-local.sh or par.sh for all of them. Documentation alone runs nothing.
set -uo pipefail
cd "$(dirname "$0")/.."
changed=0
full=0
[ $# -le 1 ] || { echo "usage: scripts/ci-local.sh [--source | --changed]"; exit 2; }
case "${1:-}" in
  --changed) changed=1; export BCC_SOURCE=0 ;;
  --source) full=1; export BCC_SOURCE=1 ;;
  "") ;;
  *) echo "usage: scripts/ci-local.sh [--source | --changed]"; exit 2 ;;
esac
# A change that reaches the reference semantics or the compiler needs the full gate.
reach=""
if [ "$full" = 0 ] && base=${CI_LOCAL_BASE:-$(git merge-base origin/main HEAD 2>/dev/null)}; then
  reach=$({ git diff --name-only "$base"; git ls-files --others --exclude-standard; } | grep -E '^(Paper|Support|Backend)/' | head -1 || true)
  [ -z "$reach" ] || echo "ci-local: $reach (and perhaps more of Paper/, Support/, Backend/) changed since $(git rev-parse --short "$base"): \`make gate-full\` is required as well"
fi
start=$SECONDS
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
fail=0
step() {
  local name="$1" t=$SECONDS; shift
  printf '==> %s\n' "$name"
  if "$@"; then printf '    ok: %s (%ss)\n' "$name" $((SECONDS - t)); else printf '    FAILED: %s (%ss)\n' "$name" $((SECONDS - t)); fail=1; fi
}

# The full gate's steps after the build, in the order they are reported: name, then command.
steps=(
  "hygiene + axioms" "scripts/check-hygiene.sh"
  "judgment freeze"  "scripts/check-judgments.sh"
  "type equality"    "scripts/check-type-eq.sh"
  "axiom report"     "lake env lean scripts/AxiomCheck.lean"
  "insertion pins"   "scripts/check-pins.sh"
  "parse corpus"     "scripts/parse-corpus.sh"
  "check corpus"     "scripts/check-corpus.sh"
  "clause kinds"     "scripts/check-kinds.sh"
  "handled names"    "scripts/check-handled.sh"
  "cell classes"     "scripts/check-cells.sh"
  "compile corpus"   "scripts/compile-corpus.sh"
  "compile corpus (final)"  "scripts/compile-corpus.sh --final"
  "compile kernel"   "scripts/compile-kernel.sh"
  "backend2 fence"   "scripts/check-backend2.sh"
  "backend2 corpus"  "scripts/compile-backend2.sh"
  "backend2 corpus (final)" "scripts/compile-backend2.sh --final"
  "layout rejects"   "scripts/check-layout-reject.sh"
  "native facts"     "scripts/native-facts.sh"
  "native"           "scripts/compile-native.sh"
  "sugar pairs"      "scripts/check-sugar.sh"
  "let mut combos"   "scripts/mut-combos.py --gate --count 400"
  "renaming"         "scripts/alpha-check.py"
  "book doc-tests"   "scripts/book-doctest.sh"
  "book build"       "mdbook build book"
)
# The sanity gate's steps (`make gate`, `--changed`). The `(final)` corpus runs are its own: the
# full gate runs the corpus at every stage instead.
gateSteps=("hygiene + axioms" "judgment freeze" "axiom report" "parse corpus" "check corpus"
  "compile corpus (final)" "backend2 fence" "backend2 corpus (final)")
if [ "$full" = 1 ]; then
  everyStep=("compile scaling")
  for ((i = 0; i < ${#steps[@]}; i += 2)); do
    case "${steps[i]}" in *"(final)") ;; *) everyStep+=("${steps[i]}") ;; esac
  done
else
  everyStep=("${gateSteps[@]}")
fi
inGate() { local s; for s in "${everyStep[@]}"; do [ "$s" = "$1" ] && return 0; done; return 1; }

# --changed: the steps to run (`|name|name|…|`), from the paths changed.
all=1
run="|"
add() { local s; for s in "$@"; do run="$run$s|"; done; }
if [ "$changed" = 1 ]; then
  base=${CI_LOCAL_BASE:-$(git merge-base origin/main HEAD)} || { echo "ci-local: no merge base with origin/main"; exit 1; }
  files=$({ git diff --name-only "$base"; git ls-files --others --exclude-standard; } | sort -u)
  lean=0
  for f in $files; do
    case "$f" in
      experiments/*) ;;
      *.lean|lakefile.toml|lake-manifest.json|lean-toolchain) lean=1 ;;
    esac
  done
  if [ "$lean" = 0 ]; then
    all=0
    corpus=("parse corpus" "check corpus" "compile corpus (final)" "backend2 corpus (final)")
    for f in $files; do
      case "$f" in
        corpus/*|lib/*) add "${corpus[@]}" ;;
        scripts/ci-local.sh|scripts/par.sh) add "${everyStep[@]}" ;;
        scripts/parse-corpus.sh) add "parse corpus" ;;
        scripts/check-corpus.sh) add "check corpus" ;;
        scripts/compile-corpus.sh|scripts/source-stage.sh) add "compile corpus (final)" ;;
        scripts/compile-backend2.sh) add "backend2 corpus (final)" ;;
        scripts/check-backend2.sh) add "backend2 fence" ;;
      esac
    done
  fi
  echo "ci-local --changed: $(printf '%s\n' "$files" | grep -c . || true) path(s) changed since $(git rev-parse --short "$base")"
fi
# Hygiene and the axioms read only Lean sources: they run exactly when every step does.
wanted() {
  inGate "$1" || return 1
  [ "$all" = 1 ] && return 0
  case "$1" in "hygiene + axioms"|"axiom report") return 1 ;; esac
  case "$run" in *"|$1|"*) return 0 ;; *) return 1 ;; esac
}

if [ "$all" = 1 ]; then step "build" lake build
else step "build (bcc, bcc-counts)" lake build bcc bcc-counts; fi
built=$fail
[ "$built" = 0 ] && export CI_LOCAL_BUILT=1

if wanted "compile scaling"; then step "compile scaling" scripts/compile-scaling.sh --guard; fi

mdbook=1; command -v mdbook >/dev/null || mdbook=0
names=(); pids=()
for ((i = 0; i < ${#steps[@]}; i += 2)); do
  name=${steps[i]}; cmd=${steps[i + 1]}
  wanted "$name" || continue
  if [ "$name" = "book build" ] && [ "$mdbook" = 0 ]; then continue; fi
  if [ "$built" = 0 ]; then
    k=${#names[@]}
    (t=$SECONDS; $cmd > "$out/$k.log" 2>&1; rc=$?; echo $((SECONDS - t)) > "$out/$k.time"; exit $rc) &
    names+=("$name"); pids+=($!)
  else
    step "$name" $cmd
  fi
done
for ((k = 0; k < ${#names[@]}; k++)); do
  printf '==> %s\n' "${names[k]}"
  if wait "${pids[k]}"; then rc=0; else rc=1; fi
  cat "$out/$k.log"
  t=$(cat "$out/$k.time" 2>/dev/null || echo "?")
  if [ "$rc" = 0 ]; then printf '    ok: %s (%ss)\n' "${names[k]}" "$t"; else printf '    FAILED: %s (%ss)\n' "${names[k]}" "$t"; fail=1; fi
done
if [ "$mdbook" = 0 ] && wanted "book build"; then echo "==> book build: skipped (mdbook not installed)"; fi
if [ "$all" = 0 ]; then
  skipped=""
  for s in "${everyStep[@]}"; do wanted "$s" || skipped="$skipped${skipped:+, }$s"; done
  [ -z "$skipped" ] || echo "==> skipped (no change reaches them): $skipped"
fi

echo
tag="ci-local"; [ "$changed" = 1 ] && tag="ci-local --changed"; [ "$full" = 1 ] && tag="ci-local --source"
if [ "$fail" -eq 0 ]; then echo "$tag: ALL PASSED ($((SECONDS - start))s)"; else echo "$tag: FAILURES (see above) ($((SECONDS - start))s)"; fi
[ "$changed" = 1 ] && echo "(--changed is for iteration only: the sanity gate, scripts/ci-local.sh, runs before a PR)"
[ "$full" = 0 ] && echo "(the sanity gate: \`make gate-full\` runs every check, and re-verifies every golden)"
[ -z "$reach" ] || echo "($reach changed: \`make gate-full\` is required as well)"
exit "$fail"

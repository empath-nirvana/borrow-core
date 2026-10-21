#!/usr/bin/env bash
# The project's gate: every check CI would run, run locally. Run before opening or merging a PR,
# and paste the final summary into the PR. Needs elan and wasmtime; mdbook is optional (the book
# build is skipped with a notice if absent), and so is a C compiler for the native target
# (scripts/compile-native.sh says so and passes).
#
#     scripts/ci-local.sh             the full gate: the merge requirement (`make gate`)
#     scripts/ci-local.sh --source    the full gate with the source stage on every program
#                                     (`make gate-full`)
#     scripts/ci-local.sh --changed   for iteration only: the steps the changes since origin/main
#                                     can affect (below); it does not replace the full gate
#                                     (`make gate-fast`)
#
# The source stage. A corpus program's `.out` and a book block's `-- answer:` are goldens: the
# output of `Support`'s interpreter (`bcc interp`), the reference semantics. Every compiled stage
# (clos, flat, wasm) is always checked against the golden. The interpreter itself is slow (minutes
# on the largest programs), so by default it runs only where a golden is unverified: on the corpus
# programs and book blocks that are new or changed since the merge base (scripts/source-stage.sh).
# With `--source`, it runs on every program and book block, and every golden is re-verified.
# The full gate turns `--source` on by itself when Paper/, Support/ (the interpreter and the
# machine) or Backend/ changed since the merge base. `--changed` never runs the interpreter: it
# lists the unverified programs instead.
#
# The full gate builds everything (`lake build`), then runs the compile-time guard alone (it
# measures time) on the new backend: `scripts/compile-scaling.sh --guard --backend new` compiles a
# body inside the new backend's fragment with it, at the same limit (the decision on #646: the old
# backend is deleted at N6; SPEC §49). Then every other step at once, each one's output printed in order as it
# finishes. The steps are independent: each reads the build and the sources, and writes only its
# own temporary files (and `mdbook` its `book/book`). The scripts skip their own `lake build`
# when this one has built (`CI_LOCAL_BUILT`); when the build fails, they run one after another,
# each trying its own build, as when run alone.
#
# `--changed` compares the working tree (committed, staged, unstaged and untracked files) with
# its merge base with origin/main (or with the commit `CI_LOCAL_BASE` names):
#   * a `.lean` file outside experiments/, the lakefile, the manifest or the toolchain: every
#     step, as the full gate (the compiler imports the proofs, so every Lean change reaches it);
#   * otherwise no Lean step runs (no `lake build` of the library, no hygiene, no axioms): only
#     `lake build bcc bcc-counts`, and the steps whose inputs changed: corpus/ for the corpus
#     steps, lib/ for every step that elaborates a program, book/ for the book, a script for its
#     own step (source-stage.sh for the corpus and the book), and ci-local.sh or par.sh for all
#     of them. Documentation alone runs nothing.
set -uo pipefail
cd "$(dirname "$0")/.."
changed=0
[ $# -le 1 ] || { echo "usage: scripts/ci-local.sh [--source | --changed]"; exit 2; }
case "${1:-}" in
  --changed) changed=1; export BCC_SOURCE=0 ;;
  --source) export BCC_SOURCE=1 ;;
  "") ;;
  *) echo "usage: scripts/ci-local.sh [--source | --changed]"; exit 2 ;;
esac
# The full gate runs the source stage everywhere when a change reaches the reference semantics or
# the compiler.
if [ "$changed" = 0 ] && [ "${BCC_SOURCE:-}" != 1 ]; then
  if base=${CI_LOCAL_BASE:-$(git merge-base origin/main HEAD 2>/dev/null)}; then
    reach=$({ git diff --name-only "$base"; git ls-files --others --exclude-standard; } | grep -E '^(Paper|Support|Backend)/' | head -1 || true)
    if [ -n "$reach" ]; then
      export BCC_SOURCE=1
      echo "ci-local: $reach (and perhaps more of Paper/, Support/, Backend/) changed since $(git rev-parse --short "$base"): the source stage runs on every program, as with --source"
    fi
  fi
fi
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
fail=0
step() {
  local name="$1"; shift
  printf '==> %s\n' "$name"
  if "$@"; then printf '    ok: %s\n' "$name"; else printf '    FAILED: %s\n' "$name"; fail=1; fi
}

# The steps after the build, in the order they are reported: name, then command.
steps=(
  "hygiene + axioms" "scripts/check-hygiene.sh"
  "axiom report"     "lake env lean scripts/AxiomCheck.lean"
  "parse corpus"     "scripts/parse-corpus.sh"
  "check corpus"     "scripts/check-corpus.sh"
  "clause kinds"     "scripts/check-kinds.sh"
  "handled names"    "scripts/check-handled.sh"
  "cell classes"     "scripts/check-cells.sh"
  "compile corpus"   "scripts/compile-corpus.sh"
  "compile kernel"   "scripts/compile-kernel.sh"
  "backend2 fence"   "scripts/check-backend2.sh"
  "backend2 corpus"  "scripts/compile-backend2.sh"
  "native"           "scripts/compile-native.sh"
  "sugar pairs"      "scripts/check-sugar.sh"
  "let mut combos"   "scripts/mut-combos.py --gate --count 400"
  "renaming"         "scripts/alpha-check.py"
  "book doc-tests"   "scripts/book-doctest.sh"
  "book build"       "mdbook build book"
)
everyStep=("compile scaling")
for ((i = 0; i < ${#steps[@]}; i += 2)); do everyStep+=("${steps[i]}"); done

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
    corpus=("parse corpus" "check corpus" "clause kinds" "handled names" "cell classes" "compile corpus" "backend2 corpus" "sugar pairs" "native" "renaming")
    for f in $files; do
      case "$f" in
        corpus/kernel-counts.expected) add "compile kernel" ;;
        corpus/*) add "${corpus[@]}" ;;
        lib/*) add "${corpus[@]}" "book doc-tests" "compile scaling" "let mut combos" ;;
        book/*) add "book doc-tests" "book build" ;;
        scripts/ci-local.sh|scripts/par.sh) add "${everyStep[@]}" ;;
        scripts/parse-corpus.sh) add "parse corpus" ;;
        scripts/check-corpus.sh) add "check corpus" ;;
        scripts/check-kinds.sh) add "clause kinds" ;;
        scripts/check-handled.sh) add "handled names" ;;
        scripts/check-cells.sh) add "cell classes" ;;
        scripts/compile-corpus.sh) add "compile corpus" ;;
        scripts/compile-kernel.sh) add "compile kernel" ;;
        scripts/compile-backend2.sh) add "backend2 corpus" ;;
        scripts/check-backend2.sh) add "backend2 fence" ;;
        scripts/compile-native.sh) add "native" ;;
        scripts/compile-scaling.sh) add "compile scaling" ;;
        scripts/check-sugar.sh) add "sugar pairs" ;;
        scripts/mut-combos.py) add "let mut combos" ;;
        scripts/alpha-check.py) add "renaming" ;;
        scripts/book-doctest.sh) add "book doc-tests" ;;
        scripts/source-stage.sh) add "compile corpus" "book doc-tests" ;;
      esac
    done
  fi
  echo "ci-local --changed: $(printf '%s\n' "$files" | grep -c . || true) path(s) changed since $(git rev-parse --short "$base")"
fi
# Hygiene and the axioms read only Lean sources: they run exactly when every step does.
wanted() {
  [ "$all" = 1 ] && return 0
  case "$1" in "hygiene + axioms"|"axiom report") return 1 ;; esac
  case "$run" in *"|$1|"*) return 0 ;; *) return 1 ;; esac
}

if [ "$all" = 1 ]; then step "build" lake build
else step "build (bcc, bcc-counts)" lake build bcc bcc-counts; fi
built=$fail
[ "$built" = 0 ] && export CI_LOCAL_BUILT=1

if wanted "compile scaling"; then step "compile scaling" scripts/compile-scaling.sh --guard --backend new; fi

mdbook=1; command -v mdbook >/dev/null || mdbook=0
names=(); pids=()
for ((i = 0; i < ${#steps[@]}; i += 2)); do
  name=${steps[i]}; cmd=${steps[i + 1]}
  wanted "$name" || continue
  if [ "$name" = "book build" ] && [ "$mdbook" = 0 ]; then continue; fi
  if [ "$built" = 0 ]; then
    k=${#names[@]}
    $cmd > "$out/$k.log" 2>&1 &
    names+=("$name"); pids+=($!)
  else
    step "$name" $cmd
  fi
done
for ((k = 0; k < ${#names[@]}; k++)); do
  printf '==> %s\n' "${names[k]}"
  if wait "${pids[k]}"; then rc=0; else rc=1; fi
  cat "$out/$k.log"
  if [ "$rc" = 0 ]; then printf '    ok: %s\n' "${names[k]}"; else printf '    FAILED: %s\n' "${names[k]}"; fail=1; fi
done
if [ "$mdbook" = 0 ] && wanted "book build"; then echo "==> book build: skipped (mdbook not installed)"; fi
if [ "$all" = 0 ]; then
  skipped=""
  for s in "${everyStep[@]}"; do wanted "$s" || skipped="$skipped${skipped:+, }$s"; done
  [ -z "$skipped" ] || echo "==> skipped (no change reaches them): $skipped"
fi

echo
tag="ci-local"; [ "$changed" = 1 ] && tag="ci-local --changed"; [ "${BCC_SOURCE:-}" = 1 ] && tag="ci-local --source"
if [ "$fail" -eq 0 ]; then echo "$tag: ALL PASSED"; else echo "$tag: FAILURES (see above)"; fi
[ "$changed" = 1 ] && echo "(--changed is for iteration only: the full gate, scripts/ci-local.sh, is the merge requirement)"
[ -z "${BCC_SOURCE:-}" ] && echo "(the source stage ran on the unverified goldens only: \`make gate-full\` re-verifies every golden)"
exit "$fail"

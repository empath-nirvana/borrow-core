#!/usr/bin/env bash
# The project's gate: every check CI would run, run locally. Run before opening or merging a PR,
# and paste the final summary into the PR. Needs elan and wasmtime; mdbook is optional (skipped
# with a notice if absent).
set -uo pipefail
cd "$(dirname "$0")/.."
fail=0
step() {
  local name="$1"; shift
  printf '==> %s\n' "$name"
  if "$@"; then printf '    ok: %s\n' "$name"; else printf '    FAILED: %s\n' "$name"; fail=1; fi
}
step "build"            lake build
step "hygiene + axioms" scripts/check-hygiene.sh
step "axiom report"     lake env lean scripts/AxiomCheck.lean
step "parse corpus"     scripts/parse-corpus.sh
step "check corpus"     scripts/check-corpus.sh
step "compile corpus"   scripts/compile-corpus.sh
step "compile scaling"  scripts/compile-scaling.sh --guard
step "sugar pairs"      scripts/check-sugar.sh
step "typed IR"         scripts/check-elab.sh
step "book doc-tests"   scripts/book-doctest.sh
if command -v mdbook >/dev/null; then
  step "book build" mdbook build book
else
  echo "==> book build: skipped (mdbook not installed)"
fi
echo
if [ "$fail" -eq 0 ]; then echo "ci-local: ALL PASSED"; else echo "ci-local: FAILURES (see above)"; fi
exit "$fail"

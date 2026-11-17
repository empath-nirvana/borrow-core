#!/usr/bin/env bash
# The research archive (#1133): `research/tree/`, the tree interpretation, off the default build.
# Gate-full's `research archive` step: it builds (`lake build ResearchTree`), its axiom report reads
# the same text as the library's (`research/tree/AxiomCheck.lean` is `scripts/AxiomCheck.lean`
# under the archive's imports), and that report passes on `research/tree/axioms/*.names`.
set -euo pipefail
cd "$(dirname "$0")/.."
body() { sed '1,/^import Lean$/d' "$1"; }
if ! diff <(body scripts/AxiomCheck.lean) <(body research/tree/AxiomCheck.lean) >/dev/null; then
  echo "check-research: research/tree/AxiomCheck.lean is not scripts/AxiomCheck.lean below its imports"; exit 1
fi
lake build ResearchTree
lake env lean research/tree/AxiomCheck.lean

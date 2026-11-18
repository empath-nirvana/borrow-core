#!/usr/bin/env bash
# The research archive (#1133): `research/tree/`, the tree interpretation, off the default build.
# Gate-full's `research archive` step: it builds (`lake build ResearchTree`), and its axiom report,
# the library's report (`scripts/AxiomCheck.lean`) under the archive's imports
# (`gate-census research-axiom-report`), passes on `research/tree/axioms/*.names`.
set -euo pipefail
cd "$(dirname "$0")/.."
# One unit of the result cache (scripts/gate_cache.py `step`): a recorded pass is replayed when
# the Lean sources, Lake's configuration, scripts/, the tools and research/tree/ are as they were.
[ "${GATE_CACHE_INNER:-}" = research ] || exec python3 scripts/gate_cache.py step research lean --files research/tree -- scripts/check-research.sh "$@"
# The archive's build, when it has work (`--no-build` exits 3), holds a library token of the job
# pool (scripts/slot -l: it maps the library's .olean files).
rc=0; lake build --no-build ResearchTree || rc=$?
if [ "$rc" = 3 ]; then
  if [ "${SLOT_OFF:-}" != 1 ] && scripts/slot -s >/dev/null 2>&1; then scripts/slot -c 999 -m 16 -l 1 -- lake build ResearchTree
  else lake build ResearchTree; fi
elif [ "$rc" != 0 ]; then exit "$rc"; fi
scripts/gate-census.sh research-axiom-report

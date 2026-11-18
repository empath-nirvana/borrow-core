#!/usr/bin/env bash
# The gate's checks that read the Lean environment (`scripts/GateCensus.lean`): builds
# `gate-census` unless the gate has (`CI_LOCAL_BUILT`), then runs it on the arguments under the
# library's search path.
#
#     scripts/gate-census.sh CENSUS[+FILE]
#     scripts/gate-census.sh --out DIR CENSUS[+FILE]...
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build gate-census >/dev/null
exec lake env .lake/build/bin/gate-census "$@"

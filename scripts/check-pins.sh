#!/usr/bin/env bash
# The insertion pins (`gate-census pins`, scripts/PinSites.lean), then the script's own
# negative tests: the same check, with declarations added that a correct check refuses, must fail
# with each one named (scripts/census-neg/pins.lean; the same `gate-census` run, on the
# environment with them elaborated into it).
#
#   * `Backend2.installConsume`, a site the table does not list (a name that starts like Lean's
#     generated `inst…` declarations);
#   * `Backend2.theRule`, a rule chosen in a definition of its own, and `Backend2.useRule`, a node
#     built at it.
#
#     scripts/check-pins.sh
set -euo pipefail
cd "$(dirname "$0")/.."
# One unit of the result cache (scripts/gate_cache.py `step`): a recorded pass is replayed when
# the Lean sources, Lake's configuration, scripts/ and the tools are as they were.
[ "${GATE_CACHE_INNER:-}" = pins ] || exec python3 scripts/gate_cache.py step pins lean -- scripts/check-pins.sh "$@"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir "$tmp/c"
scripts/gate-census.sh --out "$tmp/c" pins pins+scripts/census-neg/pins.lean
cat "$tmp/c/pins.out"
[ "$(cat "$tmp/c/pins.status")" = 0 ] || exit 1
cp "$tmp/c/pins-neg.out" "$tmp/out"
if [ "$(cat "$tmp/c/pins-neg.status")" = 0 ]; then
  echo "check-pins: the negative tests passed the check"; exit 1
fi
for want in "Backend2.installConsume: builds nodes at" "Backend2.theRule: a definition of a rule"; do
  if ! grep -qF "$want" "$tmp/out"; then
    echo "check-pins: the negative tests' output lacks: $want"; cat "$tmp/out"; exit 1
  fi
done
echo "check-pins: the negative tests are refused"

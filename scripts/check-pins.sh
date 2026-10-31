#!/usr/bin/env bash
# The insertion pins (`scripts/PinSites.lean`), then the script's own negative tests: the same
# check, with declarations added that a correct check refuses, must fail with each one named.
#
#   * `Backend2.installDrop`, a site the table does not list (a name that starts like Lean's
#     generated `inst…` declarations);
#   * `Backend2.theRule`, a rule chosen in a definition of its own, and `Backend2.useRule`, a node
#     built at it.
#
#     scripts/check-pins.sh
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean scripts/PinSites.lean
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
{
  sed -n '/^import /p' scripts/PinSites.lean
  cat <<'LEAN'
def Backend2.installDrop (x : Backend2.Var) (b : Backend2.Tm) : Backend2.Tm := .drop .unused x b
def Backend2.theRule : Backend2.DropRule := .dtor
def Backend2.useRule (x : Backend2.Var) (b : Backend2.Tm) : Backend2.Tm := .drop Backend2.theRule x b
LEAN
  sed '/^import /d' scripts/PinSites.lean
} > "$tmp/Neg.lean"
if lake env lean "$tmp/Neg.lean" > "$tmp/out" 2>&1; then
  echo "check-pins: the negative tests passed the check"; exit 1
fi
for want in "Backend2.installDrop: builds nodes at" "Backend2.theRule: a definition of a rule"; do
  if ! grep -qF "$want" "$tmp/out"; then
    echo "check-pins: the negative tests' output lacks: $want"; cat "$tmp/out"; exit 1
  fi
done
echo "check-pins: the negative tests are refused"

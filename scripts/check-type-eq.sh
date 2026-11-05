#!/usr/bin/env bash
# The checker compares two kernel types only up to `[α]`, through one helper (SPEC §3):
# `tyEqV`/`tyEqC`/`tyEqEnts` (Frontend/Check/TyEq.lean) and `convVal`/`convComp`
# (Frontend/Check/Conv.lean). `scripts/TypeEq.lean` lists every declaration of a `Frontend`
# module whose elaborated body decides an equality of a `VTy`, `CTy`, `OpSig` or a row; each one
# under `Frontend.Check` must be in scripts/type-eq.allow, with its reason. Then the script's own
# negative tests: the same check, with declarations added that a correct check refuses, must fail
# with each one named:
#
#   * `Frontend.Check.negBeq`, a `==` of two value types;
#   * `Frontend.Check.negDecide`, a `decide (C = D)` of two computation types;
#   * `Frontend.Check.negFind`, a lookup of a row's operation by `==`;
#   * `Frontend.Check.negAlpha`, `VTy.alphaB` called outside the helper.
#
#     scripts/check-type-eq.sh
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build Frontend >/dev/null
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
allow=$(grep -vE '^(#|$)' scripts/type-eq.allow | awk '{print $1}' | sort -u)

# check FILE: the census of FILE's declarations under `Frontend.Check` (and of FILE itself),
# against the allowlist. Prints the unlisted ones; fails when there are any.
check() {
  lake env lean "$1" > "$tmp/census" 2>&1 || { echo "check-type-eq: the census failed:"; cat "$tmp/census"; return 2; }
  awk -F'\t' '$1 ~ /^Frontend\.Check(\.|$)/ || $1 == "main" {print $1 "\t" $2}' "$tmp/census" > "$tmp/hits"
  local bad=0 used=""
  while IFS=$'\t' read -r mod decl; do
    if printf '%s\n' "$allow" | grep -qxF "$decl"; then used="$used$decl"$'\n'
    elif printf '%s\n' "$allow" | grep -qxF "$mod.*"; then used="$used$mod.*"$'\n'
    else echo "  $decl ($mod): compares kernel types outside the helper"; bad=1
    fi
  done < "$tmp/hits"
  printf '%s' "$used" | sort -u > "$tmp/used"
  [ "$bad" = 0 ] || return 1
  printf '%s\n' "$allow" > "$tmp/allow"
  gone=$(comm -23 "$tmp/allow" "$tmp/used")
  if [ -n "$gone" ]; then
    echo "check-type-eq: allowlisted but no longer comparing types (remove these lines):"
    printf '  %s\n' $gone
    return 1
  fi
}

if ! check scripts/TypeEq.lean; then
  echo "check-type-eq: route these through tyEqV/tyEqC/tyEqEnts or convVal/convComp, or add them"
  echo "to scripts/type-eq.allow with the reason the exact comparison is right"
  exit 1
fi
n=$(wc -l < "$tmp/hits" | tr -d ' ')

{
  sed -n '/^import /p' scripts/TypeEq.lean
  cat <<'LEAN'
def Frontend.Check.negBeq (A B : Frontend.Check.CVTy) : Bool := A == B
def Frontend.Check.negDecide (C D : Frontend.Check.CCTy) : Bool := decide (C = D)
def Frontend.Check.negFind (S : Frontend.Check.CRow) (o : Frontend.Check.COpSig) : Bool :=
  (S.find? (· == o)).isSome
def Frontend.Check.negAlpha (A B : Frontend.Check.CVTy) : Bool :=
  BoCa.Fig16.LogRel.Core.VTy.alphaB [] A B
LEAN
  sed '/^import /d' scripts/TypeEq.lean
} > "$tmp/Neg.lean"
if check "$tmp/Neg.lean" > "$tmp/negout"; then
  echo "check-type-eq: the negative tests passed the check"; exit 1
fi
for want in negBeq negDecide negFind negAlpha; do
  if ! grep -qF "Frontend.Check.$want (main)" "$tmp/negout"; then
    echo "check-type-eq: the negative tests' output lacks Frontend.Check.$want"; cat "$tmp/negout"; exit 1
  fi
done
echo "check-type-eq: $n declarations under Frontend/Check decide a type equality, each the helper or allowlisted; the negative tests are refused"

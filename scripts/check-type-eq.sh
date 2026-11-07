#!/usr/bin/env bash
# The checker, the elaborator and the backends compare two kernel types only up to `[α]`, through
# one helper (SPEC §3): `tyEqV`/`tyEqC`/`tyEqEnts` (Frontend/Check/TyEq.lean) and
# `convVal`/`convComp` (Frontend/Check/Conv.lean). `scripts/TypeEq.lean` lists every declaration
# of a compiled module (`bcc`'s import closure outside `Core`, `Support` and `Paper`: `Frontend`,
# `Backend`, `Backend2`) whose elaborated body decides, at run time, an equality of a `VTy`, `CTy`,
# `OpSig` or a row, directly or through a kernel declaration that does; each one must be the
# helper or in scripts/type-eq.allow, with its reason. Then the script's own negative tests: the
# same check, with declarations added that a correct check refuses, must fail with each one named:
#
#   * `Frontend.Check.negBeq`, a `==` of two value types;
#   * `Frontend.Check.negDecide`, a `decide (C = D)` of two computation types;
#   * `Frontend.Check.negFind`, a lookup of a row's operation by `==`;
#   * `Frontend.Check.negAlpha`, `VTy.alphaB` called outside the helper;
#   * `Frontend.Sugar.negElab`, a `=` of two value types in the elaborator's namespace;
#   * `Frontend.Check.negViaCore`, a comparison through a kernel helper (`FoldP.callE`, a key
#     lookup by the keys' `DecidableEq`);
#   * `Backend2.negHandle`, two handle nodes' rows and signatures compared exactly.
#
#     scripts/check-type-eq.sh
set -euo pipefail
cd "$(dirname "$0")/.."
[ -n "${CI_LOCAL_BUILT:-}" ] || lake build Frontend Backend Backend2 >/dev/null
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
allow=$(grep -vE '^(#|$)' scripts/type-eq.allow | awk '{print $1}' | sort -u)

# check FILE: the census of FILE's declarations in the compiled modules (and of FILE itself),
# against the allowlist. Prints the unlisted ones; fails when there are any.
check() {
  lake env lean "$1" > "$tmp/census" 2>&1 || { echo "check-type-eq: the census failed:"; cat "$tmp/census"; return 2; }
  scanned=$(awk -F'\t' '$1 == "#scanned" {print $2}' "$tmp/census")
  if [ "$scanned" != "Backend Backend2 Frontend Pipeline Target" ]; then
    echo "check-type-eq: the census read the modules under \"$scanned\", not Backend Backend2 Frontend Pipeline Target"
    echo "(a new library in bcc's import closure: add it here and to SPEC §3)"; return 2
  fi
  awk -F'\t' '$1 != "#scanned" {print $1 "\t" $2}' "$tmp/census" > "$tmp/hits"
  local bad=0 used=""
  while IFS=$'\t' read -r mod decl; do
    if printf '%s\n' "$allow" | grep -qxF "$decl"; then used="$used$decl"$'\n'
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
def Frontend.Sugar.negElab (A B : Frontend.Check.CVTy) : Bool := decide (A = B)
def Frontend.Check.negViaCore (ks : List BoCa.Fig16.LogRel.Core.FoldP.Bnd)
    (k : BoCa.Fig16.LogRel.Core.FoldP.Bnd) : BoCa.Expr :=
  BoCa.Fig16.LogRel.Core.FoldP.callE ks k
def Backend2.negHandle (g h : Backend2.HNode) : Bool :=
  decide (BoCa.Fig16.LogRel.Core.CTy.effOf g.S .unit = BoCa.Fig16.LogRel.Core.CTy.effOf h.S .unit) &&
    decide (g.E = h.E)
LEAN
  sed '/^import /d' scripts/TypeEq.lean
} > "$tmp/Neg.lean"
if check "$tmp/Neg.lean" > "$tmp/negout"; then
  echo "check-type-eq: the negative tests passed the check"; exit 1
fi
for want in Frontend.Check.negBeq Frontend.Check.negDecide Frontend.Check.negFind \
    Frontend.Check.negAlpha Frontend.Sugar.negElab Frontend.Check.negViaCore Backend2.negHandle; do
  if ! grep -qF "$want (main)" "$tmp/negout"; then
    echo "check-type-eq: the negative tests' output lacks $want"; cat "$tmp/negout"; exit 1
  fi
done
echo "check-type-eq: $n declarations under Backend, Backend2, Frontend, Pipeline and Target decide a type equality, each the helper or allowlisted; the negative tests are refused"

import Frontend.Check.Rules

/-!
# Frontend — Check — conversion  `[spec §3, §19]`

A checked term carried from the type it was derived at to the type it is wanted at: the
decisions of `Frontend/Check/TyEq.lean` with the derivation nodes they license. Equal types need no
node; types equal up to the names of their lifetime binders take `[α]` (`rAlpha`); a returner chain
`F_Σ′ A` wanted at `F_Σ B` takes `[sub]` (`rEffSub`) to `Σ` read at `Σ′`'s names (`alignRow`), then
`[α]`. These are the checker's only conversions between types: `convV`, `convC`, `liftRow`, `appIt`,
the binder of `fun`, `nu_in`, `shorten`, a handler's clauses and the derived copies each call
`convVal` or `convComp`.
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (Jdg)

/-- Why a conversion did not reach: the types differ, or both are returner chains with the same
answer up to `[α]` and the synthesized row `S'` is not within the wanted row `S`. -/
inductive ConvFail where
  | mismatch
  | row (S' S : CRow)

section
variable {Δ : LifeCtx} {T : List CVTy} (i : TInfo)

/-- A value derived at `B`, at `A`: equal, or equal up to the names of lifetime binders (`[α]`). -/
def convVal (A : CVTy) : (Σ B : CVTy, Res Δ T (.val B)) → Option (Res Δ T (.val A))
  | ⟨B, r⟩ =>
    if h : B = A then some (h ▸ r)
    else if hα : tyEqV B A = true then some (rAlpha (j := .val B) (j' := .val A) i hα r)
    else none

/-- A computation derived at `D`, at `C`: equal; equal up to the names of lifetime binders
(`[α]`); or `F_Σ′ A′` within `F_Σ A` by `[sub]` at `Σ′ ⊆ Σ` (SPEC §19), then `[α]` from `Σ` read
at `Σ′`'s names (`alignRow`) and `A′` to `C`. -/
def convComp (C : CCTy) : (Σ D : CCTy, Res Δ T (.comp D)) → Except ConvFail (Res Δ T (.comp C))
  | ⟨D, r⟩ =>
    if h : D = C then pure (h ▸ r) else
    if hα : tyEqC D C = true then pure (rAlpha (j := .comp D) (j' := .comp C) i hα r) else
    match effRow? D, effRow? C with
    | some (S', A'), some (S, _) =>
      if hD : effOf S' A' = D then
        if hC : effOf S A' = C ∧ rowLeB S' S = true then
          pure (hC.1 ▸ rEffSub i hC.2 (hD ▸ r))
        else
          let S₀ := alignRow S' S
          if hα : tyEqC (effOf S₀ A') C = true then
            if hle : rowLeB S' S₀ = true then
              pure (rAlpha (j := .comp (effOf S₀ A')) (j' := .comp C) i hα
                (rEffSub i hle (hD ▸ r)))
            else throw (.row S' S)
          else throw .mismatch
      else throw .mismatch
    | _, _ => throw .mismatch

/-- A computation at the row `S′`, at the row `S` of its binding (`liftRow`): `[sub]` when `S′ ⊆ S`,
equal rows included, so every effectful binding's head has the node; else `convComp`'s `[sub]`
then `[α]`. -/
def convRow {S' : CRow} {A : CVTy} (S : CRow) (r : Res Δ T (.comp (effOf S' A))) :
    Except ConvFail (Res Δ T (.comp (effOf S A))) :=
  if hle : rowLeB S' S = true then pure (rEffSub i hle r)
  else convComp i (effOf S A) ⟨_, r⟩

end

end Frontend.Check

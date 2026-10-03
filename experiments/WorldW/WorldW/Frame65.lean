import WorldW.Wp

/-!
# WorldW — `OpenFrame65` and its out-of-order forms (DESIGN §3.1, §3.4, stage C1)

**World: the W-draft.** OQ-9 (a) for `[TR]` 6.65. `OpenFrame65OutStable` and `OpenFrame65Out`
drop `YoungerThan`: the borrower holds entries older than the lend (a continuation it resumes or
cancels, §3.4's checkpoint 2). The statements are the design's, verbatim; their proofs are not in
this file: the outcome is reported in `README.md`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace WorldW
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The same as `OpenFrame64` for a [TR] 6.65 lend. -/
def OpenFrame65 : Prop :=
  ∀ (T : OpTab), ClosedOps T → T.Local → NoUnr T →
  ∀ (l : BoCa.Loc) (α : Life) (S : VTy) (δ : LSub) (Q : List SRec → Val → WProp)
    (τi σ : List OEnt) (ls : List SRec) (b : Expr) (ρ : WRes),
    YoungerThan τi α → OpenInv τi ls (.mut l α S δ) ρ →
    ewpW τi (.mut l α S δ :: σ) ls b (opTableW T) (exitM l α S δ Q) ρ →
    ewpW (τi ++ [.mut l α S δ]) σ ls b (opTabW T (GhostEnd.owner l S δ)) Q ρ

/-- `OpenFrame65` without `YoungerThan`: the borrower holds entries older than the lend (a
continuation it resumes or cancels), at a payload type whose relation does not read the record
list. -/
def OpenFrame65OutStable : Prop :=
  ∀ (T : OpTab), ClosedOps T → T.Local → NoUnr T →
  ∀ (l : BoCa.Loc) (α : Life) (S : VTy) (δ : LSub), ListStable S δ →
  ∀ (Q : List SRec → Val → WProp) (τi σ : List OEnt) (ls : List SRec) (b : Expr) (ρ : WRes),
    OpenInv τi ls (.mut l α S δ) ρ →
    ewpW τi (.mut l α S δ :: σ) ls b (opTableW T) (exitM l α S δ Q) ρ →
    ewpW (τi ++ [.mut l α S δ]) σ ls b (opTabW T (GhostEnd.owner l S δ)) Q ρ

/-- The same at every payload type. -/
def OpenFrame65Out : Prop :=
  ∀ (T : OpTab), ClosedOps T → T.Local → NoUnr T →
  ∀ (l : BoCa.Loc) (α : Life) (S : VTy) (δ : LSub)
    (Q : List SRec → Val → WProp) (τi σ : List OEnt) (ls : List SRec) (b : Expr) (ρ : WRes),
    OpenInv τi ls (.mut l α S δ) ρ →
    ewpW τi (.mut l α S δ :: σ) ls b (opTableW T) (exitM l α S δ Q) ρ →
    ewpW (τi ++ [.mut l α S δ]) σ ls b (opTabW T (GhostEnd.owner l S δ)) Q ρ

end WorldW

end

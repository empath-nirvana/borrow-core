import WorldW.Wp

/-!
# WorldW — `OpenFrame66` (DESIGN §3.2, stage C2)

**World: the W-draft.** OQ-9 (a) for `[TR]` 6.66. The statement is the design's, verbatim; its
proof is not in this file: the outcome is reported in `README.md`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace WorldW
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- OQ-9 (a), [TR] 6.66, at a mixed row. A run holds the open anti-frame
`e = anti l α β S δ P̂`: the cell at `l` unfolded to `own(v) ● ρ_P̂` for the body `b`. `e` closes
by 6.66's refold when `b` returns, is handed on, unfolded, at a resuming stop, and is refolded at
an abortive stop and at a cancel's end, the view `ℓ ↦ Mut α` handed back beside them. -/
def OpenFrame66 : Prop :=
  ∀ (T : OpTab), ClosedOps T → T.Local → NoUnr T →
  ∀ (l : BoCa.Loc) (α β : Life) (S : VTy) (δ : LSub) (P : Val → SPropS BoCa.Loc Val β)
    (Q : List SRec → Val → WProp) (τi σ : List OEnt) (ls : List SRec) (b : Expr) (ρ : WRes),
    YoungerThan τi α → OpenInv τi ls (.anti l α β S δ P) ρ →
    ewpW τi (.anti l α β S δ P :: σ) ls b (opTableW T) (antiPost l α S δ Q) ρ →
    ewpW (τi ++ [.anti l α β S δ P]) σ ls b (opTabW T (viewM l α S δ)) Q ρ

end WorldW

end

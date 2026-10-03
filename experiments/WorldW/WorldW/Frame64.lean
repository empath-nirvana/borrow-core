import WorldW.Wp

/-!
# WorldW — `OpenFrame64` (DESIGN §3.1, stage B)

**World: the W-draft.** OQ-9 (a) for `[TR]` 6.64 at a row that mixes linear, affine and abortive
operations. The statement is the design's, verbatim. Its proof is stage B's and is not in this
file: the outcome is reported in `README.md`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace WorldW
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- OQ-9 (a), [TR] 6.64, at a row that mixes linear, affine and abortive operations.
* A run holds the open frame `e = imm (p, α)` and the entries `τi` its borrower holds.
* Its borrower `b` is given at the fixed `α`.
* Conclusions: `e` closes by 6.64's exit when `b` returns. At a resuming stop `e` is handed on,
  open: the share demands the resume at every answer and, at an affine operation, the cancel run
  (`owedW`). At an abortive stop `e` closes there. At a cancel's end the cancel run closes `e`.
  At the last two, the owner is handed back beside the stop for the lender's finaliser.
* The borrower may hold 6.66 and 6.150 entries of its own: `τi` ranges over every kind.
  `YoungerThan`: the 6.64 entries it holds were opened inside the lend. -/
def OpenFrame64 : Prop :=
  ∀ (T : OpTab), ClosedOps T → T.Local → NoUnr T →
  ∀ (p : FrameRec) (α : Life) (Q : List SRec → Val → WProp), QExt Q →
  ∀ (τi σ : List OEnt) (ls : List SRec) (b : Expr) (ρ : WRes),
    YoungerThan τi α → OpenInv τi ls (.imm (p, α)) ρ →
    ewpW τi (.imm (p, α) :: σ) ls b (opTableW T) (exitI p α Q) ρ →
    ewpW (τi ++ [.imm (p, α)]) σ ls b (opTabW T (GhostEnd.ownerI p.le p.v p.T p.δ)) Q ρ

end WorldW

end

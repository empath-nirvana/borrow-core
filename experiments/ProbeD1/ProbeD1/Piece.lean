import ProbeD1.World

/-!
# ProbeD1 — the effectful piece with the share over futures (DESIGN §2.3)

GhostEnd's piece `OpenS` (`Stacked.lean`) runs at one stack `σ`: a stop of depth `k` ghost-ends the
innermost `k` entries and owes its continuation, re-lent below them, at the same stack. The share
over futures, `OpenSF`, owes the continuation also at every future of the kept part `σ.drop k`: the
handler may resume it inside new lends and new handlers, which places new entries between the
continuation's own (re-lent) lends and the kept ones. The continuation's stack is then
`σ.take k ++ futS k' τ N (σ.drop k)`, so the continuation variable carries its stack (`XTF`).

At `fut = false` the only future is the kept part itself, and `OpenSF` is `OpenS` read at the one
stack. The relation (`Relation.lean`) uses GhostEnd's own `OpenS` there, so that `StackStep.lean`
applies to it verbatim.

Definitions only.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack vwS dropS stratS boxTop ReLend ghostS tabK)

/-- The continuation a stop owes, indexed by the stack it resumes at, then as GhostEnd's `XT`:
the depth, the drops, the lifetimes it ended and those of the entries it kept. -/
abbrev XTF := LStack → Nat → List Bool → List Life → List Life → List SRec → Expr → WProp

/-- **`Relendable_σ` at one list, over the kept stack's futures**: the share splits into the views
it dropped and a part strictly above the outermost lend that, at every re-lend and every future
(`FutQ`) of the kept stack `σ`, handed the views, is in `P` at the future's stack. `inner` is the
part the stop ghost-ended: its places shadow `σ`'s views, and an inserted entry's variable and
place are new to it too. -/
def RelendableNF (fut : Bool) (δ : LSub) (inner σ : LStack)
    (P : LStack → List Life → WProp) (αs : List Life) (ls : List SRec) : WProp := fun ρ =>
  ∃ ds ρz ρn, ResU.CompS ρz ρn ρ ∧ vwS δ (inner.map LEnt.l) σ ds αs ls ρn ∧ stratS αs ρz ∧
    ∀ αs', ReLend αs' αs → ∀ k τ αt N, FutQ fut δ σ αs' k τ αt N ρz →
      (∀ e ∈ τ, e.x ∉ inner.map LEnt.x ∧ e.l ∉ inner.map LEnt.l) →
      (vwS δ (inner.map LEnt.l) σ ds αs' ls ─⋆ P (futS k τ N σ) (futL k αt αs')) ρz

/-- **A stop with the stack open at `αs`**, as GhostEnd's `stopS`, the kept part's continuation
owed at its futures. -/
def stopSF (fut : Bool) (δ : LSub) (σ : LStack) (Tab : OpTab) (X : XTF) (αs : List Life)
    (ls : List SRec) (t : Expr) : WProp :=
  ex fun k => ex fun ds => dropS [] (σ.take k) ds ⋆
    ghostS δ (σ.take k) (αs.take k) ls
      (opTable (tabK σ k Tab) ls t fun ls' e' =>
        RelendableNF fut δ (σ.take k) (σ.drop k)
          (fun σo αo => X (σ.take k ++ σo) k ds (αs.take k) αo ls' e') (αs.drop k) ls')

/-- One run at the stack `σ`: an answer in `Q σ αs`, or a stop. -/
def bodySF (fut : Bool) (δ : LSub) (Tab : OpTab)
    (Q : LStack → List Life → List SRec → Val → WProp) (X : XTF) (σ : LStack) (αs : List Life) :
    List SRec → Expr → WProp :=
  fun ls e => wpG ls e fun ls'' t ρ => valPost (Q σ αs) ls'' t ρ ∨ stopSF fut δ σ Tab X αs ls'' t ρ

/-- One unfolding: the ghost-ended entries re-lent below the lifetimes they ended and below the
kept ones, the share in `[top]` and handed the views its drops ask for. -/
def openFSF (fut : Bool) (δ : LSub) (Tab : OpTab)
    (Q : LStack → List Life → List SRec → Val → WProp) (X : XTF) : XTF :=
  fun σ k ds αi αo ls e ρ =>
    ∀ αi', List.Forall₂ (· < ·) αi' αi → List.IsChain (· < ·) (αi' ++ αo) →
      boxTop αi' (vwS δ [] (σ.take k) ds αi' ls ─⋆ bodySF fut δ Tab Q X σ (αi' ++ αo) ls e) ρ

/-- **`OpenSF`**: the least fixed point of `openFSF`, written in `Prop` as `ewpTS` is. -/
def OpenSF (fut : Bool) (δ : LSub) (Tab : OpTab)
    (Q : LStack → List Life → List SRec → Val → WProp) : XTF :=
  fun σ k ds αi αo ls e ρ =>
    ∀ X : XTF, (∀ σ k ds αi αo ls e ρ, openFSF fut δ Tab Q X σ k ds αi αo ls e ρ →
      X σ k ds αi αo ls e ρ) → X σ k ds αi αo ls e ρ

end ProbeD1

end

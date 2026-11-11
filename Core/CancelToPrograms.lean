import Core.EffCancel
import Core.StepsN

/-!
# Core — runs of `cancelTo`  `[spec §51]`

`cancelTo_n k` cancels the handled region of the nearest `hnd (n, H)` in place, without capturing
a continuation, and then runs `k ()` where the handler stood (`[cancel-to]`).  The region in each
program is `hnd (2, H₂) (ubind (id, λ_. D) [·])`: a handler, dead under the cancel, and a
finaliser, which the cancel runs.

* `ctOk`: the finaliser returns; the cancel answers `()`, and `k ()` runs (`ctOk_run`).
* `ctErr`: the finaliser raises `3`; the error is kept and re-raised at the canceller, so `k ()`
  does not run, and the live handler of `3` outside the node catches it (`ctErr_run`).
* `ctStuck`: a `cancelTo` with no handler of its name around it is final (`ctStuck_final`).

No surface or elaborator produces `cancelTo`; these are closed core terms.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.CancelIntercept
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont hndE hndVal raiseE ccatchE cfinE ubindE opPayload
  cancelVal cancelToE cancelToPayload)

/-- `k = λ_. inj₁ ()`. -/
def kCT : Val := constC (Val.inj₁ Val.unit)

/-- `cancelTo_1 k`. -/
def cancelToU : Expr := cancelToE (.val (cancelToPayload 1 kCT))

/-- The frame `[·]; k ()` around `K`. -/
abbrev kF (K : Kont) : Kont := .seq K (.app (.val kCT) (.val Val.unit))

/-- `hnd (1, H₁) (hnd (2, H₂) (ubind (id, λ_. D) (cancelTo_1 k)))`. -/
def ctBody (D : Expr) : Expr := hndE H₁ ((hF H₂ (uF D .hole)).plug cancelToU)

/-- The finaliser returns `()`. -/
def ctOk : Expr := ctBody .unit

/-- The finaliser raises `3`, under a live handler of `3` outside the node. -/
def ctErr : Expr := hndE H₃ (ctBody (raiseU 3))

/-- `[cancel-to]` at `ctBody D`: the handler frame `1` is consumed, the dead handler `2` removed,
and the finaliser runs under `cfin`. -/
theorem ctBody_start (μ : Heap) (D : Expr) :
    Steps (ℍ := ℍ) μ (ctBody D) μ
      ((kF (ccF .hole)).plug (cfinE (cancelVal none) (D.subst 0 Val.unit))) := by
  refine .more (st .hole (Head.cancelTo μ 1 (qualsVal [.unr]) idV (Val.pair cancelC Val.unit)
    kCT (hF H₂ (uF D .hole)) rfl)) ?_
  show Steps μ ((kF (ccF .hole)).plug
    (ubindE (Val.pair idV (finV D)) (raiseE (.val (cancelVal none))))) μ _
  exact Steps.plug (kF (ccF .hole)) (fin_cancel μ D none)

/-- **`ctOk`**: the finaliser returns, the cancel answers `()`, and `k ()` answers `inj₁ ()`. -/
theorem ctOk_run (μ : Heap) : Steps (ℍ := ℍ) μ ctOk μ (.val (Val.inj₁ Val.unit)) := by
  refine (ctBody_start μ .unit).trans ?_
  refine .more (st (kF (ccF .hole)) (Head.cfret μ none Val.unit)) ?_
  refine .more (st (kF .hole) (Head.cancel μ .hole rfl)) ?_
  refine .more (st .hole (Head.seq μ _)) ?_
  refine .more (st .hole (Head.beta μ _ Val.unit)) ?_
  exact .refl _ _

/-- **`ctErr`**: the finaliser's raise of `3` is kept and re-raised at the canceller, before
`k ()`; the handler of `3` outside the node catches it and answers `inj₂ ()`. -/
theorem ctErr_run (μ : Heap) : Steps (ℍ := ℍ) μ ctErr μ (.val (Val.inj₂ Val.unit)) := by
  refine (Steps.plug (hF H₃ .hole) (ctBody_start μ (raiseU 3))).trans ?_
  refine .more (st (hF H₃ (kF (ccF .hole)))
    (Head.cferr μ none 3 0 Val.unit .hole (by decide) rfl)) ?_
  refine .more (st (hF H₃ (kF .hole)) (Head.creraise μ (opPayload 3 0 Val.unit) .hole rfl)) ?_
  refine .more (st .hole (Head.hunwind μ 3 0 (qualsVal [.unr]) idV (Val.pair c₃ Val.unit) c₃
    Val.unit (kF .hole) (hcl c₃) rfl)) ?_
  refine .more (st .hole (Head.beta μ _ Val.unit)) ?_
  exact .refl _ _

/-- `cancelTo_1 k` under a handler of another name. -/
def ctStuck : Expr := hndE H₂ cancelToU

/-- **`ctStuck`** is final: its only handler is of another name.  `[spec §51]` -/
theorem ctStuck_final (μ : Heap) : Final (ℍ := ℍ) μ ctStuck :=
  final_cancelToPlug (K := hF H₂ .hole) (payloadName_cancelToPayload 1 kCT) rfl μ

end BoCa.Fig16.LogRel.Core.CancelIntercept

end

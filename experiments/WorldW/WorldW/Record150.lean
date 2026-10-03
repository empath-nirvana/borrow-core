import WorldW.Wp
import Core.Compatibility

/-!
# WorldW — a 6.150 record handed on at a stop (DESIGN §3.3, stage E)

**World: the W-draft, with Core's `TW`.** `RebExitW` is `RebChooseTW`'s exit clause
(`Core/Reborrow.lean:124-128`) with T1's list equalities replaced by `Keeps`; `RebChooseTWW` is
`RebChooseTW` with it. `OpenRecord150` is the probe. The statements are the design's, verbatim.
`rebChooseTW_pin_W` is proved here (it passes the exit clause through, as
`rebChooseTW_pin` does); the other dischargers and the probe are not: the outcome is reported in
`README.md`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace WorldW
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `RebChooseTW`'s exit clause at the exit worlds a run under `StopW` can reach: T1's list
equalities are replaced by `Keeps (rsOf ls) (rsOf ls') ρ_i`; `W''.InStratum β` is kept. -/
def RebExitW (ls : List SRec) (l : BoCa.Loc) (s : LSet) (w : Val) (σR : WRes)
    (hs : σR.InStratum s.join) (β : Life) (χ : WRes) : Prop :=
  ∀ (ps' : List FrameRec) (ls' : List SRec) (Wp W'' : WRes),
    Keeps (rsOf ls) (rsOf ls') (ResU.single l (CellU.immOf s w σR hs)) →
    TW Wp ps' (rsOf ls') → Tagged Wp ps' ls' →
    (∃ (s' : LSet) (hs' : σR.InStratum s'.join), W''.get l = some (CellU.immOf s' w σR hs')) →
    ResU.CompS W'' (χ.restrictDom σR.exclPart) Wp → W''.InStratum β →
    TW W'' ps' (rsOf ls') ∧ Tagged W'' ps' ls'

/-- `RebChooseTW` (`Core/Reborrow.lean:112`) with `RebExitW` as its exit clause. The entry
clauses are Core's verbatim. -/
def RebChooseTWW (ls : List SRec) (l : BoCa.Loc) (R : Val → WRes → Prop)
    (P₀ P : Life → Val → WProp) : Prop :=
  ∀ (W F χ₀ σ : WRes) (ps : List FrameRec) (β : Life) (w : Val) (s : LSet)
    (hs : σ.InStratum s.join),
    TW W ps (rsOf ls) → Tagged W ps ls → W.InStratum β →
    ResU.CompS (ResU.single l (CellU.immOf s w σ hs)) F W → R w σ →
    ResU.Reb β σ χ₀ → P₀ β w χ₀ →
    ∃ χ, ResU.Reb β σ χ ∧ P β w χ ∧ (∃ A, AgW χ A) ∧
      (∀ a, AgW F a → EscrowAgree σ χ a) ∧
      (∀ a, AgW (ResU.single l (CellU.immOf s w σ hs)) a → EscrowAgree σ χ a) ∧
      (∀ W', ResU.CompS W χ W' → ResU.Valid W' → TW W' ps (rsOf ls) ∧ Tagged W' ps ls) ∧
      RebExitW ls l s w σ hs β χ

/-- `rebChooseTW_pin` (`Core/Compatibility.lean:134`) with `RebChooseTWW`: it passes the exit
clause through unchanged. -/
theorem rebChooseTW_pin_W {ls : List SRec} {l : BoCa.Loc} {R : Val → WRes → Prop}
    {P₀ P : Life → Val → WProp} (c : Val) (h : RebChooseTWW ls l R P₀ P) :
    RebChooseTWW ls l (fun w σ => w = c ∧ R w σ) P₀ (fun β w χ => (⌜c = w⌝ ⋆ P β w) χ) := by
  intro W F χ₀ σ ps β w s hs hT htag hβ hW hR hreb₀ hP₀
  obtain ⟨hwc, hR'⟩ := hR
  obtain ⟨χ, hreb, hPχ, hag, hEF, hEI, hen, hex⟩ :=
    h W F χ₀ σ ps β w s hs hT htag hβ hW hR' hreb₀ hP₀
  exact ⟨χ, hreb, pure_sep_mk hwc.symm hPχ, hag, hEF, hEI, hen, hex⟩

/-- `rebChooseTW_top` at `W`: the same hypotheses, `RebChooseTWW` concluded. -/
def RebChooseTWTopW : Prop :=
  ∀ {ls : List SRec} {r : FrameRec} {x : LifeVar} {δ' : LSub},
    r ∈ rsOf ls → AgreeOn r.T δ' r.δ → ¬ VFree x r.T →
    RebChooseTWW ls r.le (fun w σ => vC false r.T ls δ' w σ)
      (fun β w χ => vShape (r.T.immReborrow (.var x)) (δ'.extend x β) w χ)
      (fun β w χ => vC true (r.T.immReborrow (.var x)) ls (δ'.extend x β) w χ)

/-- `rebChooseTW_deep` at `W`. -/
def RebChooseTWDeepW : Prop :=
  ∀ {ls : List SRec} {r : FrameRec} {p₀ : Option BoCa.Loc} {l₀ : BoCa.Loc} {S₀ : VTy} {u₀ : Val}
    {x : LifeVar} {δ' : LSub},
    r ∈ rsOf ls → Chain r.R r.T r.v p₀ l₀ S₀ u₀ → AgreeOn S₀ δ' r.δ → ¬ VFree x S₀ →
    RebChooseTWW ls l₀ (fun w σ => vC false S₀ ls δ' w σ)
      (fun β w χ => vShape (S₀.immReborrow (.var x)) (δ'.extend x β) w χ)
      (fun β w χ => vC true (S₀.immReborrow (.var x)) ls (δ'.extend x β) w χ)

/-- OQ-9 (a), [TR] 6.150, at a mixed row. A run holds the view `ρ_i = l ↦ imm(s, w, σR)` beside
the resource `X` of its borrower `b`, which holds the open reborrow `e = reb l s w σR hs β χ`.
`e` closes by 6.150's exit when `b` returns: the image subtracted from the leftover and the view
kept (H24–H33: 6.52, 6.58, 6.59, `TW.rebEnd`). It is handed on at a resuming stop and closed at
an abortive stop and at a cancel's end, with the view handed back for the finaliser. -/
def OpenRecord150 : Prop :=
  ∀ (T : OpTab), ClosedOps T → T.Local → NoUnr T →
  ∀ (l : BoCa.Loc) (s : LSet) (w : Val) (σR : WRes) (hs : σR.InStratum s.join) (β : Life)
    (χ : WRes) (Q : List SRec → Val → WProp) (τi σ : List OEnt) (ls : List SRec) (b : Expr)
    (ρ X : WRes),
    YoungerThan τi β → RebExitW ls l s w σR hs β χ →
    ResU.CompS (ResU.single l (CellU.immOf s w σR hs)) X ρ →
    OpenInvReb τi l s w σR hs β χ X →
    ewpW τi (.reb l s w σR hs β χ :: σ) ls b (opTableW T) (fun ls v => box β (Q ls v)) X →
    ewpW (τi ++ [.reb l s w σR hs β χ]) σ ls b
      (opTabW T (fun _ ρ' => ρ' = ResU.single l (CellU.immOf s w σR hs))) Q ρ

end WorldW

end

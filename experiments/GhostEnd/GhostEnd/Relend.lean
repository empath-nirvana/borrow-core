import Core.EffRules

/-!
# GhostEnd — the lender's frame across suspensions

`[TR]` 6.65 (Mut Frame) at a table that may **resume**. A stop of the callback ends the lend as a
return does, and the continuation hands the owner `ℓ ↦ w ⋆ P̂(w)` back. When the continuation is
resumed, the frame re-applies 6.65 at a fresh lifetime.

The printed proof of 6.65 at `wpG` (`wpG_M_frameX`, H26–H35) inspects only resources, never the
term a run ends at. So a stop is as good as a return, provided the callback's share at the stop
has the postcondition shape `[α] ∀w. ℓ ↦ w ─⋆ P̂(w) ─⋆ _`. `ewpTS_M_frameU` is this fact at an
abortive table. Here the table may resume. A resumed continuation is owed the owner and a
callback the frame can lend to again.

`Relend` is that callback: the least fixed point of `relendF`. At every resumption it is lent at
a fresh lifetime (`fresh`, `[TR]` p. 6, row 18). It holds no lifetime of the lend it was given
before the stop.

* `ewpTS_M_frameR`: the frame holds over `ewpTS` at every monotone table. The proof is induction
  on `Relend` with `wpG_M_frameX` at each unfolding, so each resumption re-applies 6.65 as
  printed.
* `relend_step`, `relend_fold`: `Relend` is closed under pure steps, and introduced by one
  unfolding.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The lender's place, owned: `∃w. ℓ ↦ w ⋆ 𝒱⟦T⟧(ls)δ(w)`, 6.65's precondition and the shape
its postcondition hands back. -/
def owner (l : BoCa.Loc) (T : VTy) (δ : LSub) (ls : List SRec) : WProp :=
  ex fun w => ptoOwn l w ⋆ vC true T ls δ w

/-- A callback lent at a fresh `α` that runs to a value in `Q` or to a stop the table admits,
owing `Φ`. At either, its share is in `[α]` and hands the owner back. -/
def relendG (Tb : Table) (l : BoCa.Loc) (T : VTy) (δ : LSub) (Q : List SRec → Val → WProp)
    (Φ : List SRec → Expr → WProp) : List SRec → Expr → WProp :=
  fun ls e => fresh fun α => ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ─⋆
    wpG ls e (fun ls'' t => box α (all fun w => ptoOwn l w ─⋆ (vC true T ls'' δ w ─⋆
      fun ρ => valPost Q ls'' t ρ ∨ Tb ls'' t Φ ρ)))

/-- One unfolding of the re-lendable callback: a stop owes its continuation the owner and the
next unfolding. -/
def relendF (Tb : Table) (l : BoCa.Loc) (T : VTy) (δ : LSub) (Q : List SRec → Val → WProp)
    (X : List SRec → Expr → WProp) : List SRec → Expr → WProp :=
  relendG Tb l T δ Q (fun ls' e' => owner l T δ ls' ⋆ X ls' e')

/-- The re-lendable callback: the least fixed point of `relendF`, written in `Prop` as
`ewpTS` is. -/
def Relend (Tb : Table) (l : BoCa.Loc) (T : VTy) (δ : LSub) (Q : List SRec → Val → WProp)
    (ls : List SRec) (e : Expr) : WProp := fun ρ =>
  ∀ X : List SRec → Expr → WProp, (∀ ls e ρ, relendF Tb l T δ Q X ls e ρ → X ls e ρ) → X ls e ρ

theorem box_mono {α : Life} {P P' : WProp} (h : Entails P P') : Entails (box α P) (box α P') :=
  fun ρ hp => ⟨h ρ hp.1, hp.2⟩

theorem fresh_mono {P P' : Life → WProp} (h : ∀ α, Entails (P α) (P' α)) :
    Entails (fresh P) (fresh P') := by
  rintro ρ ⟨β, hβ⟩
  exact ⟨β, fun α hα => box_mono (h α) ρ (hβ α hα)⟩

theorem wand_mono_right {P Q Q' : WProp} (h : Entails Q Q') : Entails (P ─⋆ Q) (P ─⋆ Q') :=
  fun _ hw ρ₁ ρ₂ hp hc => h ρ₂ (hw ρ₁ ρ₂ hp hc)

/-- `relendG` is monotone in the continuation it owes. -/
theorem relendG_mono {Tb : Table} (hTb : Tb.Mono) {l : BoCa.Loc} {T : VTy} {δ : LSub}
    {Q : List SRec → Val → WProp} {Φ Φ' : List SRec → Expr → WProp}
    (hΦ : ∀ ls e ρ, Φ ls e ρ → Φ' ls e ρ) {ls : List SRec} {e : Expr} :
    Entails (relendG Tb l T δ Q Φ ls e) (relendG Tb l T δ Q Φ' ls e) := by
  refine fresh_mono fun α => wand_mono_right fun _ hw => wpG_mono (fun ls'' t σ hb => ?_) hw
  refine ⟨fun w ρ₁ ρ₂ h₁ hc₁ ρ₃ ρ₄ h₃ hc₃ => ?_, hb.2⟩
  rcases hb.1 w ρ₁ ρ₂ h₁ hc₁ ρ₃ ρ₄ h₃ hc₃ with hq | hq
  · exact Or.inl hq
  · exact Or.inr (hTb _ _ _ _ _ hΦ hq)

/-- `relendF` is monotone in the continuation it owes. -/
theorem relendF_mono {Tb : Table} (hTb : Tb.Mono) {l : BoCa.Loc} {T : VTy} {δ : LSub}
    {Q : List SRec → Val → WProp} {X X' : List SRec → Expr → WProp}
    (hX : ∀ ls e ρ, X ls e ρ → X' ls e ρ) {ls : List SRec} {e : Expr} :
    Entails (relendF Tb l T δ Q X ls e) (relendF Tb l T δ Q X' ls e) :=
  relendG_mono hTb fun _ _ _ ⟨τ₁, τ₂, hc, ho, hx⟩ => ⟨τ₁, τ₂, hc, ho, hX _ _ _ hx⟩

/-- One unfolding introduces `Relend`. -/
theorem relend_fold {Tb : Table} (hTb : Tb.Mono) {l : BoCa.Loc} {T : VTy} {δ : LSub}
    {Q : List SRec → Val → WProp} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : relendF Tb l T δ Q (Relend Tb l T δ Q) ls e ρ) : Relend Tb l T δ Q ls e ρ :=
  fun X hX => hX ls e ρ (relendF_mono hTb (fun _ _ _ h' => h' X hX) ρ h)

/-- `Relend` unfolds once. -/
theorem relend_unfold {Tb : Table} (hTb : Tb.Mono) {l : BoCa.Loc} {T : VTy} {δ : LSub}
    {Q : List SRec → Val → WProp} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : Relend Tb l T δ Q ls e ρ) : relendF Tb l T δ Q (Relend Tb l T δ Q) ls e ρ :=
  h (fun ls e ρ => relendF Tb l T δ Q (Relend Tb l T δ Q) ls e ρ)
    (fun _ _ _ h' => relendF_mono hTb (fun _ _ _ h'' => relend_fold hTb h'') _ h')

/-- `Relend` is closed under a pure step in front. -/
theorem relend_step {Tb : Table} (hTb : Tb.Mono) {l : BoCa.Loc} {T : VTy} {δ : LSub}
    {Q : List SRec → Val → WProp} {ls : List SRec} {e e' : Expr}
    (hs : ∀ μ : Heap, Step1N μ e μ e') {ρ : WRes}
    (h : Relend Tb l T δ Q ls e' ρ) : Relend Tb l T δ Q ls e ρ := by
  refine relend_fold hTb ?_
  exact fresh_mono (fun α => wand_mono_right (wpG_step hs ls _)) ρ (relend_unfold hTb h)

/-- **`[TR]` 6.65 at a resuming table.** At every monotone table, the owner and a re-lendable
callback give the callback's `ewpTS`. At a return this is 6.65. At a stop the lend ends as at a
return (`wpG_M_frameX`, whose H26–H35 never read the term), and the continuation is owed the
owner and the callback again. When it is resumed, the frame re-applies 6.65 at a lifetime chosen
fresh at that point (H4: below every record of the resumer's list and the payload's stratum).
Nothing of the earlier lend survives the stop. -/
theorem ewpTS_M_frameR (Tb : Table) (hTb : Tb.Mono) (l : BoCa.Loc) (T : VTy) (δ : LSub)
    (β : Life) (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β)
    (Q : List SRec → Val → WProp) (ls : List SRec) (e : Expr) :
    Entails (owner l T δ ls ⋆ Relend Tb l T δ Q ls e) (ewpTS ls e Tb Q) := by
  rintro ρ ⟨ρo, ρr, hc, ho, hr⟩
  refine hr (fun ls e ρr => ∀ ρo ρ, owner l T δ ls ρo → ResU.CompS ρo ρr ρ → ewpTS ls e Tb Q ρ)
    ?_ ρo ρ ho hc
  intro ls e ρr hF ρo ρ ho hc
  obtain ⟨v, ρl, ρP, hcl, hl, hv⟩ := ho
  obtain ⟨σ, hcσ, hcρ⟩ := compS_reassoc hcl hc
  refine ewp_fold hTb ?_
  refine wpG_M_frameX l T δ β hP v e ls _ ρ ⟨ρl, σ, hcρ, hl, ρP, ρr, hcσ, hv, ?_⟩
  refine relendG_mono hTb ?_ ρr hF
  rintro ls' e' τ ⟨τ₁, τ₂, hcτ, ho', hm⟩
  exact hm τ₁ τ ho' hcτ

end GhostEnd

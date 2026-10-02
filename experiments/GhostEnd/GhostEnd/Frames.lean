import GhostEnd.Relend

/-!
# GhostEnd — the other printed frames at resuming tables: the step each needs

`ewpTS_M_frameR` lifts 6.65 to a resuming table by induction on the callback's own least fixed
point, with the printed proof (`wpG_M_frameX`) at each unfolding. The same shape lifts 6.64, 6.66
and 6.150, since each is proved at `wpG` and never reads the term its run ends at
(`wpG_I_frameX`, `wpG_M_antiFrameX`, `wpG_reborrow`). Each adds one step of its own:

* **6.64 (Imm Frame)** takes `hQ`: its postcondition carried along `Ext`, from the list with the
  frame's record to the list without it. At a resuming table the postcondition is the table's
  stop, which is carried along `Ext` because the continuation's share is quantified over every
  extension (`opTable_extR`, by `Ext.trans`).
* **6.66 (Anti Frame)** refolds `ℓ ↦ M_α` at the end of the run, so at a stop the continuation is
  owed the view, and at the resumption the frame unfolds it again. `ewpTS_M_antiFrameR` is the
  lift, proved here.
* **6.150 (↺)** consumes `ℓ ↦ Imm α (R ∧ Иβ. ↺_β P̂₀)`. At a resumption the frame needs the view
  again, so a copy is kept beside the callback (`ptoImmS_dup`, `I-Dup`) and handed to the
  continuation at the stop.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **6.64's `hQ` at a resuming table**: a stop the table admits is carried along `Ext`. -/
theorem opTable_extR {Tab : OpTab} (hL : Tab.Local) {ls ls' : List SRec} {t : Expr}
    {Φ : List SRec → Expr → WProp} {ρ : WRes} (he : Ext ls ls' ρ) (h : opTable Tab ls t Φ ρ) :
    opTable Tab ls' t Φ ρ := by
  rcases h with ⟨K, n, i, v, en, h⟩ | ⟨K, n, i, v, en, h⟩
  · obtain ⟨hp, ρa, ρk, hc, hA, hu, hk⟩ := pure_sep_iff.mp h
    exact Or.inl ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc,
      (hL n i en hp.2.2.1 ls ls' v ρa (he.left hc)).1 hA, hu,
      fun ls'' he' => hk ls'' ((he.right hc).trans he')⟩⟩
  · obtain ⟨hp, ρa, ρn, hc, ⟨hA, hnA⟩, hn⟩ := pure_sep_iff.mp h
    exact Or.inr ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρn, hc,
      ⟨(hL n i en hp.2.2.1 ls ls' v ρa (he.left hc)).1 hA, hnA⟩, hn⟩⟩

/-- The postcondition 6.64 is applied at, over a resuming table: an answer in `Q` or a stop. It
is carried along `Ext` when `Q` is. -/
theorem ewpPostR_ext {Tab : OpTab} (hL : Tab.Local) {Q : List SRec → Val → WProp}
    (hQ : ∀ ls₁ ls₂ v ρ, Ext ls₁ ls₂ ρ → Q ls₁ v ρ → Q ls₂ v ρ) {Φ : List SRec → Expr → WProp} :
    ∀ ls₁ ls₂ (t : Expr) ρ, Ext ls₁ ls₂ ρ →
      (valPost Q ls₁ t ρ ∨ opTable Tab ls₁ t Φ ρ) → (valPost Q ls₂ t ρ ∨ opTable Tab ls₂ t Φ ρ) := by
  intro ls₁ ls₂ t ρ he h
  rcases h with ⟨v, rfl, hv⟩ | h
  · exact Or.inl ⟨v, rfl, hQ _ _ _ _ he hv⟩
  · exact Or.inr (opTable_extR hL he h)

/-! ### 6.66 at a resuming table -/

/-- One unfolding of the anti-framed callback: from the content handed out, run to an answer or a
stop, handing the content back and taking the view; a stop owes the view and the callback again. -/
def antiF (Tb : Table) (l : BoCa.Loc) (α : Life) (T : VTy) (δ : LSub)
    (Q : List SRec → Val → WProp) (X : List SRec → Expr → WProp) : List SRec → Expr → WProp :=
  fun ls e => all fun v => ptoOwn l v ─⋆ (vC true T ls δ v ─⋆
    wpG ls e (fun ls'' t => ex fun w => ptoOwn l w ⋆ vC true T ls'' δ w ⋆
      (ptoMutS l α ls'' (fun ls₀ => vC true T ls₀ δ) ─⋆
        fun ρ => valPost Q ls'' t ρ ∨
          Tb ls'' t (fun ls' e' => ptoMutS l α ls' (fun ls₀ => vC true T ls₀ δ) ⋆ X ls' e') ρ)))

/-- The anti-framed callback: the least fixed point of `antiF`. -/
def AntiRelend (Tb : Table) (l : BoCa.Loc) (α : Life) (T : VTy) (δ : LSub)
    (Q : List SRec → Val → WProp) (ls : List SRec) (e : Expr) : WProp := fun ρ =>
  ∀ X : List SRec → Expr → WProp, (∀ ls e ρ, antiF Tb l α T δ Q X ls e ρ → X ls e ρ) → X ls e ρ

theorem antiF_mono {Tb : Table} (hTb : Tb.Mono) {l : BoCa.Loc} {α : Life} {T : VTy} {δ : LSub}
    {Q : List SRec → Val → WProp} {X X' : List SRec → Expr → WProp}
    (hX : ∀ ls e ρ, X ls e ρ → X' ls e ρ) {ls : List SRec} {e : Expr} :
    Entails (antiF Tb l α T δ Q X ls e) (antiF Tb l α T δ Q X' ls e) := by
  intro ρ h v ρa ρb ha hcab ρc ρd hv hccd
  refine wpG_mono (fun ls'' t σ hp => ?_) (h v ρa ρb ha hcab ρc ρd hv hccd)
  obtain ⟨w, τ₁, τ₂, hc, ho, τ₃, τ₄, hc', hT, hw⟩ := hp
  refine ⟨w, τ₁, τ₂, hc, ho, τ₃, τ₄, hc', hT, fun π₁ π₂ hm hcm => ?_⟩
  rcases hw π₁ π₂ hm hcm with hq | hq
  · exact Or.inl hq
  · exact Or.inr (hTb _ _ _ _ _ (fun _ _ _ ⟨s₁, s₂, hcs, hs₁, hs₂⟩ =>
      ⟨s₁, s₂, hcs, hs₁, hX _ _ _ hs₂⟩) hq)

/-- **`[TR]` 6.66 at a resuming table.** The view and an anti-framed callback give the callback's
`ewpTS`. At a return this is 6.66. At a stop the frame refolds the view as at a return
(`wpG_M_antiFrameX`, which never reads the term), and the continuation is owed the view and the
callback; at the resumption the frame unfolds it again. By induction on `AntiRelend`. -/
theorem ewpTS_M_antiFrameR (Tb : Table) (hTb : Tb.Mono) (l : BoCa.Loc) (α : Life) (T : VTy)
    (δ : LSub) (Q : List SRec → Val → WProp) (ls : List SRec) (e : Expr) :
    Entails (ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ⋆ AntiRelend Tb l α T δ Q ls e)
      (ewpTS ls e Tb Q) := by
  rintro ρ ⟨ρm, ρr, hc, hm, hr⟩
  refine hr (fun ls e ρr => ∀ ρm ρ, ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ρm →
    ResU.CompS ρm ρr ρ → ewpTS ls e Tb Q ρ) ?_ ρm ρ hm hc
  intro ls e ρr hF ρm ρ hm hc
  refine ewp_fold hTb (wpG_M_antiFrameX l α T δ e ls _ ρ ⟨ρm, ρr, hc, hm, ?_⟩)
  intro v ρa ρb ha hcab ρc ρd hv hccd
  refine wpG_mono (fun ls'' t σ hp => ?_) (hF v ρa ρb ha hcab ρc ρd hv hccd)
  obtain ⟨w, τ₁, τ₂, hcτ, hown, τ₃, τ₄, hc', hT, hw⟩ := hp
  refine ⟨w, τ₁, τ₂, hcτ, hown, τ₃, τ₄, hc', hT, fun π₁ π₂ hm' hcm => ?_⟩
  rcases hw π₁ π₂ hm' hcm with hq | hq
  · exact Or.inl hq
  · exact Or.inr (hTb _ _ _ _ _ (fun _ _ _ ⟨s₁, s₂, hcs, hs₁, hs₂⟩ => hs₂ s₁ _ hs₁ hcs) hq)

/-! ### 6.150 at a resuming table: the view kept for the next resumption -/

/-- **`I-Dup` at the unstratified `imm` view** 6.150 consumes: the cell is idempotent, so a copy
can be kept beside the callback and handed to the continuation at a stop. -/
theorem ptoImm_dup {l : BoCa.Loc} {α : Life} {P : Val → WProp} {ρ : WRes} (hp : ptoImm l α P ρ) :
    ∃ τ₁ τ₂, ResU.CompS τ₁ τ₂ ρ ∧ ptoImm l α P τ₁ ∧ ptoImm l α P τ₂ := by
  obtain ⟨s, v, σ, hs, rfl, hP, hα⟩ := hp
  have h₃ : σ.InStratum (s ∪ s).join := ResU.InStratum.sup hs hs
  have e : CellU.immOf (s ∪ s) v σ h₃ = CellU.immOf s v σ hs :=
    CellU.immOf_congr (LSet.union_self s) rfl rfl h₃ hs
  have hcomp := ResU.compS_single_imm l s s v σ hs hs h₃
  rw [e] at hcomp
  exact ⟨_, _, hcomp, ⟨s, v, σ, hs, rfl, hP, hα⟩, ⟨s, v, σ, hs, rfl, hP, hα⟩⟩

end GhostEnd

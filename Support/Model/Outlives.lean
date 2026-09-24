import Paper.S1_Syntax.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Paper.S6_2_NonStandardLemmas.Definitions
import Support.Model.Algebra
import Support.Model.AlgebraInstances
import Support.Model.Cells
import Support.Model.Compatibility
import Support.Model.Composition
import Support.Model.FlatteningCells
import Support.Model.Lifetimes
import Support.Model.Notation
import Support.Model.Prelude
import Support.Model.ReborrowFrame
import Support.Model.Restriction
import Support.Model.Subtraction
import Support.Model.WalkSplitting
import Support.Model.Walks

/-!
# Support — Model — Outlives

`[about ours]`.  `@ρ ⊐ α` across `⦇−⦈`, the walks and `↭` (the steps Lemma 6.50's one sentence elides), and *“there are no borrows at any lifetime shorter than `α`”*.
-/

noncomputable section

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-- `@ψ ⊐ α` puts `ψ` in `Cell_α`; an `own` cell is in every stratum anyway. -/
theorem cell_inStratum_of_at {α : Life} {ψ : CellU BoCa.Loc BoCa.Val}
    (h : ψ.at ⊐ α) : ψ.InStratum α := by
  cases ψ with
  | own v => exact trivial
  | imm i => exact h
  | «mut» m => exact h

/-- The converse of `cell_inStratum_of_at`, away from `own`. -/
theorem cell_at_of_inStratum {α : Life} {ψ : CellU BoCa.Loc BoCa.Val}
    (hk : ψ.kind ≠ Kind.own) (h : ψ.InStratum α) : ψ.at ⊐ α := by
  cases ψ with
  | own v => exact absurd rfl hk
  | imm i => exact h
  | «mut» m => exact h

/-- A cell's witness lies in every stratum the cell does.
`[about ours: the hereditary reading of Fig. 16's own typing constraints on the
`imm` and `mut` payloads]` -/
theorem cell_wit_inStratum {α : Life} {ψ : CellU BoCa.Loc BoCa.Val}
    (h : ψ.InStratum α) : ψ.wit.InStratum α := by
  cases ψ with
  | own v => intro l χ e; exact absurd e (by simp [CellU.wit])
  | imm i =>
      exact ResU.InStratum.mono
        (le_of_lt (lt_of_lt_of_le h i.ls.meet_le_join)) (Res.toU_inStratum i.ρ)
  | «mut» m => exact ResU.InStratum.mono (le_of_lt h) (Res.toU_inStratum m.ρ)

/-- `Cell_α` is closed under `●`.  `[about ours: `[TR]` Lemma 6.45's cell level, read at `Cell_α`]` -/
theorem cellCompS_inStratum {α : Life} {ψ₁ ψ₂ ψ : CellU BoCa.Loc BoCa.Val}
    (h : CellU.CompS ψ₁ ψ₂ ψ) (h₁ : ψ₁.InStratum α) (h₂ : ψ₂.InStratum α) :
    ψ.InStratum α := by
  obtain ⟨k₁, k₂⟩ := CellU.CompatS.kinds h.compat
  refine cell_inStratum_of_at ?_
  rw [CellU.CompS.at h]
  exact Nat.max_lt.mpr
    ⟨cell_at_of_inStratum (by rw [k₁]; simp) h₁,
      cell_at_of_inStratum (by rw [k₂]; simp) h₂⟩

/-- `Cell_α` is closed under `○`.
`[about ours: `Cell_α` at `[TR]` p. 5's `○`]` -/
theorem cellCompR_inStratum {α : Life} {ψ₁ ψ₂ ψ : CellU BoCa.Loc BoCa.Val}
    (h : CellU.CompR ψ₁ ψ₂ ψ) (h₁ : ψ₁.InStratum α) (h₂ : ψ₂.InStratum α) :
    ψ.InStratum α := by
  cases h with
  | same χ => exact h₁
  | strict k => exact cellCompS_inStratum (CellU.compS_spec _ _ k) h₁ h₂
  | mutMut a b v ρ ha hb P Q hP hQ => exact Nat.max_lt.mpr ⟨h₁, h₂⟩
  | mutOwn a v ρ ha P hP => exact h₁
  | ownMut a v ρ ha P hP => exact h₂
  | immOwn s v ρ hs => exact h₁
  | ownImm s v ρ hs => exact h₂
  | immMut s v ρ hs b hb P hP => exact h₁
  | mutImm s v ρ hs b hb P hP => exact h₂

/-- `○` does not shorten an `imm` operand.
`[about ours: the lifetime half of "`ag(ρ)` keeps every `imm` cell of `ρ`"]` -/
theorem cellCompR_at_le_imm {ψ₁ ψ₂ ψ : CellU BoCa.Loc BoCa.Val}
    (h : CellU.CompR ψ₁ ψ₂ ψ) (hk : ψ₁.kind = Kind.imm) : ψ.at ≤ ψ₁.at := by
  cases h with
  | same χ => exact le_refl _
  | strict k => rw [CellU.CompS.at (CellU.compS_spec _ _ k)]; exact inf_le_left
  | mutMut a b v ρ ha hb P Q hP hQ => exact absurd hk (by simp)
  | mutOwn a v ρ ha P hP => exact absurd hk (by simp)
  | ownMut a v ρ ha P hP => exact absurd hk (by simp)
  | immOwn s v ρ hs => exact Nat.le_refl _
  | ownImm s v ρ hs => exact absurd hk (by simp)
  | immMut s v ρ hs b hb P hP => exact Nat.le_refl _
  | mutImm s v ρ hs b hb P hP => exact absurd hk (by simp)

theorem inStratum_restrict {α : Life} {ρ : WRes} {k : Kind} (h : ρ.InStratum α) :
    (ρ.restrict k).InStratum α :=
  fun l ψ e => h l ψ (ResU.restrict_eq_some.mp e).1

/-- `Res_α` is closed under `◐` whenever `Cell_α` is closed under the cell
operation.
`[about ours: `Res_α` at the composition schema]` -/
theorem inStratum_comp {α : Life}
    {R : CellU BoCa.Loc BoCa.Val → CellU BoCa.Loc BoCa.Val → Prop}
    {C : CellU BoCa.Loc BoCa.Val → CellU BoCa.Loc BoCa.Val → CellU BoCa.Loc BoCa.Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ₁.InStratum α → ψ₂.InStratum α → ψ.InStratum α)
    {ρ₁ ρ₂ ρ : WRes} (h : ResU.Comp R C ρ₁ ρ₂ ρ)
    (h₁ : ρ₁.InStratum α) (h₂ : ρ₂.InStratum α) : ρ.InStratum α := by
  intro l ψ e
  rcases h.get l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, f, hCc⟩
  · rw [f] at e; exact absurd e (by simp)
  · rw [f] at e; cases Option.some.inj e; exact h₁ l _ f₁
  · rw [f] at e; cases Option.some.inj e; exact h₂ l _ f₂
  · rw [f] at e; cases Option.some.inj e; exact hC _ _ _ hCc (h₁ l _ f₁) (h₂ l _ f₂)

/-- `Res_α` is closed under `⨀`. -/
theorem inStratum_bigComp {α : Life}
    {R : CellU BoCa.Loc BoCa.Val → CellU BoCa.Loc BoCa.Val → Prop}
    {C : CellU BoCa.Loc BoCa.Val → CellU BoCa.Loc BoCa.Val → CellU BoCa.Loc BoCa.Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ₁.InStratum α → ψ₂.InStratum α → ψ.InStratum α) :
    ∀ {xs : List WRes} {b : WRes}, BigComp R C xs b →
      (∀ x ∈ xs, x.InStratum α) → b.InStratum α := by
  intro xs b h
  induction h with
  | nil => intro _ l ψ e; exact absurd e (by simp)
  | cons ht hc ih =>
      intro hx
      exact inStratum_comp hC hc (hx _ (by simp))
        (ih fun x hm => hx x (by simp [hm]))

theorem compS_hC (α : Life) : ∀ ψ₁ ψ₂ ψ : CellU BoCa.Loc BoCa.Val,
    CellU.CompS ψ₁ ψ₂ ψ → ψ₁.InStratum α → ψ₂.InStratum α → ψ.InStratum α :=
  fun _ _ _ => cellCompS_inStratum

theorem compR_hC (α : Life) : ∀ ψ₁ ψ₂ ψ : CellU BoCa.Loc BoCa.Val,
    CellU.CompR ψ₁ ψ₂ ψ → ψ₁.InStratum α → ψ₂.InStratum α → ψ.InStratum α :=
  fun _ _ _ => cellCompR_inStratum

/-- The exclusive walk keeps the stratum.
`[about ours: the step 6.50's proof needs and does not name, at `ex(ρ)_◐`]` -/
theorem ExW.inStratum
    {R : CellU BoCa.Loc BoCa.Val → CellU BoCa.Loc BoCa.Val → Prop}
    {C : CellU BoCa.Loc BoCa.Val → CellU BoCa.Loc BoCa.Val → CellU BoCa.Loc BoCa.Val → Prop}
    (hC : ∀ (α : Life) ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ₁.InStratum α → ψ₂.InStratum α →
        ψ.InStratum α)
    {ρ σ : WRes} (h : ExW R C ρ σ) : ∀ α, ρ.InStratum α → σ.InStratum α := by
  refine ExW.rec (motive_1 := fun ρ σ _ => ∀ α, ResU.InStratum α ρ → ResU.InStratum α σ)
    (motive_2 := fun ρ w _ => ∀ α, ResU.InStratum α ρ → ∀ p ∈ w, ResU.InStratum α p.2)
    ?mk ?nil ?cons h
  case mk =>
    intro ρ' σ' nm b w hs hw hb hnm hσ ih α hρ
    refine inStratum_comp (hC α) hσ
      (inStratum_comp (hC α) hnm (inStratum_restrict hρ) (inStratum_restrict hρ))
      (inStratum_bigComp (hC α) hb ?_)
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact ih α hρ p hp
  case nil => intro ρ' α hρ p hp; exact absurd hp (by simp)
  case cons =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw α hρ p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ihe α (cell_wit_inStratum (hρ l ψ hψ))
    · exact ihw α hρ p hp

/-- The aliasable walk keeps the stratum.
`[about ours: the step 6.50's proof needs and does not name, at `ag(ρ)`]` -/
theorem AgW.inStratum {ρ σ : WRes} (h : AgW ρ σ) :
    ∀ α, ρ.InStratum α → σ.InStratum α := by
  refine AgW.rec (motive_1 := fun ρ σ _ => ∀ α, ResU.InStratum α ρ → ResU.InStratum α σ)
    (motive_2 := fun ρ w _ => ∀ α, ResU.InStratum α ρ → ∀ p ∈ w, ResU.InStratum α p.2)
    (motive_3 := fun ρ w _ => ∀ α, ResU.InStratum α ρ → ∀ p ∈ w, ResU.InStratum α p.2)
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ' σ' a bm bi wm wi hsm hsi hwm hwi hbm hbi ha hσ ihm ihi α hρ
    refine inStratum_comp (compR_hC α) hσ
      (inStratum_comp (compR_hC α) ha (inStratum_restrict hρ)
        (inStratum_bigComp (compR_hC α) hbm ?_))
      (inStratum_bigComp (compR_hC α) hbi ?_)
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact ihm α hρ p hp
    · intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact ihi α hρ p hp
  case nilM => intro ρ' α hρ p hp; exact absurd hp (by simp)
  case consM =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw α hρ p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ihe α (cell_wit_inStratum (hρ l ψ hψ))
    · exact ihw α hρ p hp
  case nilI => intro ρ' α hρ p hp; exact absurd hp (by simp)
  case consI =>
    intro ρ' q l w ψ hψ hk e a hex hag hc hw iha ihw α hρ p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact inStratum_comp (compR_hC α) hc
        (ExW.inStratum compR_hC hex α (cell_wit_inStratum (hρ l ψ hψ)))
        (iha α (cell_wit_inStratum (hρ l ψ hψ)))
    · exact ihw α hρ p hp

/-- `ρ ∈ Res_α` implies `⦇ρ⦈ ∈ Res_α`.
`[about ours: the first elided step of `[TR]` Lemma 6.50's proof]` -/
theorem flat_inStratum {ρ σ : WRes} {α : Life} (h : ResU.Flat ρ σ)
    (hρ : ρ.InStratum α) : σ.InStratum α := by
  obtain ⟨e, a, he, ha, hc⟩ := h
  exact inStratum_comp (compS_hC α) hc (ExW.inStratum compS_hC he α hρ)
    (AgW.inStratum ha α hρ)

/-- `ag(ρ)` keeps every `imm` cell of `ρ` at its own location and does not
shorten it.
`[about ours: `Fig16.AgW.get_imm` with the lifetime relation the print's
"`ag(ρ)` keeps every `imm` cell" leaves implicit]` -/
theorem compR_get_at {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompR ρ₁ ρ₂ ρ) {l : BoCa.Loc}
    {ψ : CellU BoCa.Loc BoCa.Val} (e : ρ₁.get l = some ψ) (hk : ψ.kind = Kind.imm) :
    ∃ χ, ρ.get l = some χ ∧ χ.kind = Kind.imm ∧ χ.at ≤ ψ.at := by
  rcases h.get l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hCc⟩
  · rw [f₁] at e; exact absurd e (by simp)
  · rw [f₁] at e; cases Option.some.inj e; exact ⟨_, f, hk, le_refl _⟩
  · rw [f₁] at e; exact absurd e (by simp)
  · rw [f₁] at e
    cases Option.some.inj e
    exact ⟨χ, f, (CellU.CompR.imm_left hCc hk).1, cellCompR_at_le_imm hCc hk⟩

theorem agW_get_at {ρ σ : WRes} (h : AgW ρ σ) {l : BoCa.Loc}
    {ψ : CellU BoCa.Loc BoCa.Val} (e : ρ.get l = some ψ) (hk : ψ.kind = Kind.imm) :
    ∃ χ, σ.get l = some χ ∧ χ.kind = Kind.imm ∧ χ.at ≤ ψ.at := by
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      obtain ⟨χ₀, f₀, k₀, le₀⟩ := compR_get_at ha (ResU.restrict_get_some e hk) hk
      obtain ⟨χ, f, k', le₁⟩ := compR_get_at hσ f₀ k₀
      exact ⟨χ, f, k', le_trans le₁ le₀⟩

/-- `⦇ρ⦈ ∈ Res_α` implies `ρ ∈ Res_α`.
`[about ours: the second elided step of `[TR]` Lemma 6.50's proof]` -/
theorem flat_inStratum_inv {ρ σ : WRes} {α : Life} (h : ResU.Flat ρ σ)
    (hσ : σ.InStratum α) : ρ.InStratum α := by
  obtain ⟨e, a, he, ha, hc⟩ := h
  intro l ψ hl
  by_cases hk : ψ.kind = Kind.imm
  · obtain ⟨χ, hχ, hkχ, hle⟩ := agW_get_at ha hl hk
    have hσl : σ.get l = some χ :=
      ResU.CompS.get_right_of_immFree hc (ExS.immFree he) hχ
    exact cell_inStratum_of_at (lt_of_lt_of_le
      (cell_at_of_inStratum (by rw [hkχ]; simp) (hσ l χ hσl)) hle)
  · exact hσ l ψ (ResU.CompS.get_left_of_ne_imm hc (ExS.get_of_ne_imm he hl hk) hk).2

end BoCa.Fig16.BoLo

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- A cell's witness lies in the cell's own stratum.
`[about ours: Fig. 16's typing of the `imm` and `mut` payloads, at `@ψ`]` -/
theorem CellU.wit_inStratum_at (ψ : CellU Loc Val) : ψ.wit.InStratum ψ.at := by
  cases ψ with
  | own v => intro m ζ e; exact absurd e (by simp [CellU.wit])
  | imm i => exact ResU.InStratum.mono i.ls.meet_le_join i.ρ.toU_inStratum
  | «mut» m => exact m.ρ.toU_inStratum

/-- A lifetime of a `○` composite is a lifetime of one of the operands. -/
theorem CellU.CompR.lsOf_inv {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompR ψ₁ ψ₂ ψ)
    {s : LSet} (hs : ψ.lsOf = some s) {x : Life} (hx : s.mem x) :
    (∃ t, ψ₁.lsOf = some t ∧ t.mem x) ∨ (∃ t, ψ₂.lsOf = some t ∧ t.mem x) := by
  cases h with
  | same ζ => exact Or.inl ⟨s, hs, hx⟩
  | strict k =>
      obtain ⟨t₁, t₂, w, τ, k₁, k₂, k₃, f₁, f₂, f₃⟩ := CellU.compS_spec _ _ k
      rw [f₃] at hs
      have hxx : (t₁ ∪ t₂).mem x := by
        rw [show t₁ ∪ t₂ = s from Option.some.inj hs]; exact hx
      rcases hxx with hxx | hxx
      · exact Or.inl ⟨t₁, by rw [f₁]; rfl, hxx⟩
      · exact Or.inr ⟨t₂, by rw [f₂]; rfl, hxx⟩
  | mutMut a b w τ ha hb P Q hP hQ => exact absurd hs (by simp)
  | mutOwn a w τ ha P hP => exact absurd hs (by simp)
  | ownMut a w τ ha P hP => exact absurd hs (by simp)
  | immOwn t w τ ht => exact Or.inl ⟨s, hs, hx⟩
  | ownImm t w τ ht => exact Or.inr ⟨s, hs, hx⟩
  | immMut t w τ ht b hb P hP => exact Or.inl ⟨s, hs, hx⟩
  | mutImm t w τ ht b hb P hP => exact Or.inr ⟨s, hs, hx⟩

/-- The same at a location of a `○`. -/
theorem ResU.CompR.lsOf_inv {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompR ρ₁ ρ₂ ρ)
    {l : Loc} {ζ : CellU Loc Val} (hg : ρ.get l = some ζ) {s : LSet}
    (hs : ζ.lsOf = some s) {x : Life} (hx : s.mem x) :
    (∃ ξ t, ρ₁.get l = some ξ ∧ ξ.lsOf = some t ∧ t.mem x) ∨
    (∃ ξ t, ρ₂.get l = some ξ ∧ ξ.lsOf = some t ∧ t.mem x) := by
  rcases h.get l with ⟨-, -, e⟩ | ⟨ξ, e₁, -, e⟩ | ⟨ξ, -, e₂, e⟩ |
      ⟨ξ₁, ξ₂, ξ, e₁, e₂, e, hC⟩
  · rw [e] at hg; exact absurd hg (by simp)
  · rw [show ζ = ξ from Option.some.inj (hg.symm.trans e)] at hs
    exact Or.inl ⟨ξ, s, e₁, hs, hx⟩
  · rw [show ζ = ξ from Option.some.inj (hg.symm.trans e)] at hs
    exact Or.inr ⟨ξ, s, e₂, hs, hx⟩
  · rw [show ζ = ξ from Option.some.inj (hg.symm.trans e)] at hs
    rcases CellU.CompR.lsOf_inv hC hs hx with ⟨t, ht, hxt⟩ | ⟨t, ht, hxt⟩
    · exact Or.inl ⟨ξ₁, t, e₁, ht, hxt⟩
    · exact Or.inr ⟨ξ₂, t, e₂, ht, hxt⟩

/-- The same along `⨀`. -/
theorem BigComp.lsOf_inv :
    ∀ {L : List (ResU Loc Val)} {b : ResU Loc Val},
      BigComp CellU.CompatR CellU.CompR L b →
      ∀ {l : Loc} {ζ : CellU Loc Val}, b.get l = some ζ →
      ∀ {s : LSet}, ζ.lsOf = some s → ∀ {x : Life}, s.mem x →
      ∃ σ ∈ L, ∃ ξ t, σ.get l = some ξ ∧ ξ.lsOf = some t ∧ t.mem x := by
  intro L
  induction L with
  | nil => intro b h l ζ hg s hs x hx; cases h; exact absurd hg (by simp)
  | cons σ L' ih =>
      intro b h l ζ hg s hs x hx
      cases h with
      | cons hrest hc =>
          rcases ResU.CompR.lsOf_inv hc hg hs hx with
            ⟨ξ, t, e, ht, hxt⟩ | ⟨ξ, t, e, ht, hxt⟩
          · exact ⟨σ, List.mem_cons_self, ξ, t, e, ht, hxt⟩
          · obtain ⟨σ', hm, ξ', t', e', ht', hxt'⟩ := ih hrest e ht hxt
            exact ⟨σ', List.mem_cons_of_mem _ hm, ξ', t', e', ht', hxt'⟩

/-- A cell with a lifetime set is an `imm` cell, and `Res_α` asks of it exactly
that its meet outlive `α`. -/
theorem CellU.sqsupset_of_lsOf {ζ : CellU Loc Val} {t : LSet}
    (h : ζ.lsOf = some t) {α : Life} (hi : ζ.InStratum α) : t.meet ⊐ α := by
  cases ζ with
  | own v => simp [CellU.lsOf] at h
  | imm i => rw [← Option.some.inj h]; exact hi
  | «mut» m => simp [CellU.lsOf] at h

theorem CellU.kind_of_lsOf {ζ : CellU Loc Val} {t : LSet} (h : ζ.lsOf = some t) :
    ζ.kind = Kind.imm := by
  cases ζ with
  | own v => simp [CellU.lsOf] at h
  | imm i => rfl
  | «mut» m => simp [CellU.lsOf] at h

/-- A cell `ag(X)` raises to a location `X` does not cover sits strictly
inside a borrow of `X`: `[TR]` 6.52's *"there cannot be any borrow that contains
`ρ(ℓ)`"*, read as a statement about lifetimes.
`[about ours: the nesting `[TR]` 6.52's proof rules out, at `ag(−)`]` -/
theorem AgW.lsOf_source {X a : ResU BoCa.Loc BoCa.Val} (h : AgW X a)
    {l : BoCa.Loc} {ζ : CellU BoCa.Loc BoCa.Val} (hg : a.get l = some ζ)
    {s : LSet} (hs : ζ.lsOf = some s) {x : Life} (hx : s.mem x) :
    (∃ φ t, X.get l = some φ ∧ φ.lsOf = some t ∧ t.mem x) ∨
      (∃ m φ, X.get m = some φ ∧ φ.at < x) := by
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      rename_i aa bm bi wm wi
      rcases ResU.CompR.lsOf_inv hσ hg hs hx with ⟨ξ, t, e, ht, hxt⟩ | ⟨ξ, t, e, ht, hxt⟩
      · rcases ResU.CompR.lsOf_inv ha e ht hxt with
          ⟨ξ', t', e', ht', hxt'⟩ | ⟨ξ', t', e', ht', hxt'⟩
        · exact Or.inl ⟨ξ', t', (ResU.restrict_eq_some.mp e').1, ht', hxt'⟩
        · obtain ⟨σ, hm, ξ'', t'', e'', ht'', hxt''⟩ := BigComp.lsOf_inv hbm e' ht' hxt'
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
          obtain ⟨ψq, hψq, hagq⟩ := AgWitsM.mem hwm q hq
          refine Or.inr ⟨q.1, ψq, hψq, lt_of_lt_of_le ?_ (t''.meet_least x hxt'')⟩
          exact CellU.sqsupset_of_lsOf ht''
            (BoLo.AgW.inStratum hagq _ (CellU.wit_inStratum_at ψq) l ξ'' e'')
      · obtain ⟨σ, hm, ξ'', t'', e'', ht'', hxt''⟩ := BigComp.lsOf_inv hbi e ht hxt
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
        obtain ⟨ψq, ev, av, hψq, hexq, hagq, hcq⟩ := AgWitsI.mem hwi q hq
        refine Or.inr ⟨q.1, ψq, hψq, lt_of_lt_of_le ?_ (t''.meet_least x hxt'')⟩
        refine CellU.sqsupset_of_lsOf ht'' ?_
        exact BoLo.inStratum_comp (BoLo.compR_hC ψq.at) hcq
          (BoLo.ExW.inStratum BoLo.compR_hC hexq _ (CellU.wit_inStratum_at ψq))
          (BoLo.AgW.inStratum hagq _ (CellU.wit_inStratum_at ψq)) l ξ'' e''

/-- If no borrow of `X` is at a lifetime strictly shorter than `α`, then a cell
of `⦇X⦈` carrying `α` among its lifetimes is at a location `X` covers: `[TR]`
6.52's *"there are no borrows, mutable or immutable, at any lifetime shorter than
`α`, so there cannot be any borrow that contains `ρ(ℓ)`"*.
`[about ours: `[TR]` 6.52's phrasing of the step 6.29 takes, at several
locations at once]` -/
theorem ResU.flat_imm_at_top_of_no_shorter {X σ : ResU BoCa.Loc BoCa.Val}
    {α : Life} (hσ : ResU.Flat X σ) {l : BoCa.Loc}
    {ζ : CellU BoCa.Loc BoCa.Val} (hl : σ.get l = some ζ) {s : LSet}
    (hs : ζ.lsOf = some s) (hmem : s.mem α)
    (hnb : ∀ m φ, X.get m = some φ → ¬ (φ.at < α)) :
    ∃ φ t, X.get l = some φ ∧ φ.lsOf = some t ∧ t.mem α := by
  obtain ⟨ex, ag, hex, hag, hc⟩ := hσ
  refine (?_ : (∃ φ t, X.get l = some φ ∧ φ.lsOf = some t ∧ t.mem α) ∨
      (∃ m φ, X.get m = some φ ∧ φ.at < α)).resolve_right ?_
  · exact (by
      have hkζ : ζ.kind = Kind.imm := CellU.kind_of_lsOf hs
      have hexl : ex.get l = none := by
        cases f : ex.get l with
        | none => rfl
        | some ξ =>
            have hknz : ξ.kind ≠ Kind.imm := ExS.immFree hex l ξ f
            have hh := (ResU.CompS.get_left_of_ne_imm hc f hknz).2
            rw [hl] at hh
            cases Option.some.inj hh
            exact absurd hkζ hknz
      have hagl : ag.get l = some ζ := by
        have hp := hc.2 l
        rw [hexl] at hp
        cases hag' : ag.get l with
        | none => rw [hag'] at hp; rw [hp] at hl; exact absurd hl (by simp)
        | some ψ =>
            rw [hag'] at hp
            exact congrArg some (Option.some.inj (hp.symm.trans hl))
      exact AgW.lsOf_source hag hagl hs hmem)
  · rintro ⟨m, φ, hφ, hlt⟩; exact hnb m φ hφ hlt

end BoCa.Fig16

namespace BoCa.Fig16

theorem Life.not_lt_of_down_lt {a b : Life} (h : (↓a) < b) : ¬ (b < a) := by
  intro hlt
  have h1 : OrderDual.ofDual b < OrderDual.ofDual a + 1 := h
  have h2 : OrderDual.ofDual a < OrderDual.ofDual b := hlt
  omega

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

theorem CellU.not_at_lt_of_inStratum_down {ζ : CellU Loc Val} {α : Life}
    (h : ζ.InStratum (↓α)) : ¬ (ζ.at < α) := by
  cases ζ with
  | own v =>
      intro hlt
      exact absurd (lt_of_lt_of_le hlt (Life.top_sqsubseteq α)) (lt_irrefl _)
  | imm i => exact Life.not_lt_of_down_lt h
  | «mut» m => exact Life.not_lt_of_down_lt h

/-- `Res_α` is inherited by a `●`-factor. -/
theorem ResU.CompS.inStratum_left {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {α : Life} (hρ : ρ.InStratum α) : ρ₁.InStratum α := by
  intro l ψ e₁
  rcases ResU.Comp.get h l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁; cases Option.some.inj f₁; exact hρ l _ f
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁
    cases Option.some.inj f₁
    exact ((CellU.CompS.inStratum hC α).mp (hρ l _ f)).1

theorem ResU.CompS.inStratum_right {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.CompS ρ₁ ρ₂ ρ)
    {α : Life} (hρ : ρ.InStratum α) : ρ₂.InStratum α :=
  ResU.CompS.inStratum_left (ResU.CompS.comm h) hρ

end BoCa.Fig16

namespace BoCa.Fig16

/-- `↓α ⊏ β` gives `α ⊑ β`. -/
theorem Life.le_of_down_lt {a b : Life} (h : (↓a) < b) : a ≤ b := by
  have h1 : OrderDual.ofDual b < OrderDual.ofDual a + 1 := h
  show OrderDual.ofDual b ≤ OrderDual.ofDual a
  omega

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- A cell in `Res_{↓α}` has its witness in `Res_α`.
`[about ours: Fig. 16's typing of the `imm` and `mut` payloads, read at `↓α`]` -/
theorem CellU.wit_inStratum_of_down {ψ : CellU Loc Val} {α : Life}
    (h : ψ.InStratum (↓α)) : ψ.wit.InStratum α := by
  cases ψ with
  | own v => intro l χ e; exact absurd e (by simp [CellU.wit])
  | imm i =>
      exact ResU.InStratum.mono (Life.le_of_down_lt h) (CellU.wit_inStratum_at _)
  | «mut» m =>
      exact ResU.InStratum.mono (Life.le_of_down_lt h) (CellU.wit_inStratum_at _)

/-- `BoLo.inStratum_comp` at one location. -/
theorem ResU.inStratum_comp_at {α : Life}
    {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ₁.InStratum α → ψ₂.InStratum α → ψ.InStratum α)
    {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.Comp R C ρ₁ ρ₂ ρ) {l : Loc}
    (h₁ : ∀ φ, ρ₁.get l = some φ → φ.InStratum α)
    (h₂ : ∀ φ, ρ₂.get l = some φ → φ.InStratum α)
    {ψ : CellU Loc Val} (e : ρ.get l = some ψ) : ψ.InStratum α := by
  rcases ResU.Comp.get h l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, f, hCc⟩
  · rw [f] at e; exact absurd e (by simp)
  · rw [f] at e; cases Option.some.inj e; exact h₁ _ f₁
  · rw [f] at e; cases Option.some.inj e; exact h₂ _ f₂
  · rw [f] at e; cases Option.some.inj e; exact hC _ _ _ hCc (h₁ _ f₁) (h₂ _ f₂)

/-- `Cell_α` is closed under `●`. -/
theorem CellU.compS_hC (α : Life) : ∀ ψ₁ ψ₂ ψ : CellU Loc Val,
    CellU.CompS ψ₁ ψ₂ ψ → ψ₁.InStratum α → ψ₂.InStratum α → ψ.InStratum α :=
  fun _ _ _ hC h₁ h₂ => (CellU.CompS.inStratum hC α).mpr ⟨h₁, h₂⟩

/-- `ResU.CompS.inStratum_left` at one location. -/
theorem ResU.CompS.inStratum_left_at {ρ₁ ρ₂ ρ : ResU Loc Val}
    (h : ResU.CompS ρ₁ ρ₂ ρ) {α : Life} {l : Loc}
    (hρ : ∀ φ, ρ.get l = some φ → φ.InStratum α)
    {ψ : CellU Loc Val} (e₁ : ρ₁.get l = some ψ) : ψ.InStratum α := by
  rcases ResU.Comp.get h l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁; cases Option.some.inj f₁; exact hρ _ f
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁
    cases Option.some.inj f₁
    exact ((CellU.CompS.inStratum hC α).mp (hρ _ f)).1

theorem ResU.CompS.inStratum_right_at {ρ₁ ρ₂ ρ : ResU Loc Val}
    (h : ResU.CompS ρ₁ ρ₂ ρ) {α : Life} {l : Loc}
    (hρ : ∀ φ, ρ.get l = some φ → φ.InStratum α)
    {ψ : CellU Loc Val} (e₂ : ρ₂.get l = some ψ) : ψ.InStratum α :=
  ResU.CompS.inStratum_left_at (ResU.CompS.comm h) hρ e₂

/-- The exclusive walk keeps the stratum at one location.
`[about ours: `BoLo.ExW.inStratum` at one location]` -/
theorem ExW.inStratum_at
    {R : CellU BoCa.Loc BoCa.Val → CellU BoCa.Loc BoCa.Val → Prop}
    {C : CellU BoCa.Loc BoCa.Val → CellU BoCa.Loc BoCa.Val →
      CellU BoCa.Loc BoCa.Val → Prop}
    (hC : ∀ (α : Life) ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ₁.InStratum α → ψ₂.InStratum α →
        ψ.InStratum α)
    {ρ σ : ResU BoCa.Loc BoCa.Val} (h : ExW R C ρ σ) {α : Life}
    (hd : ρ.InStratum (↓α)) {l : BoCa.Loc}
    (hl : ∀ φ, ρ.get l = some φ → φ.InStratum α)
    {ψ : CellU BoCa.Loc BoCa.Val} (hg : σ.get l = some ψ) : ψ.InStratum α := by
  cases h with
  | mk hs hw hb hnm hσ =>
      rename_i nm b w
      have hbs : b.InStratum α := by
        refine BoLo.inStratum_bigComp (hC α) hb ?_
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        obtain ⟨φ, hφ, he⟩ := ExWits.mem hw p hp
        exact BoLo.ExW.inStratum hC he α (CellU.wit_inStratum_of_down (hd _ _ hφ))
      refine ResU.inStratum_comp_at (hC α) hσ ?_ (fun φ e => hbs l φ e) hg
      intro φ e
      exact ResU.inStratum_comp_at (hC α) hnm
        (fun χ f => hl χ (ResU.restrict_eq_some.mp f).1)
        (fun χ f => hl χ (ResU.restrict_eq_some.mp f).1) e

/-- The aliasable walk keeps the stratum at one location.
`[about ours: `BoLo.AgW.inStratum` at one location]` -/
theorem AgW.inStratum_at {ρ σ : ResU BoCa.Loc BoCa.Val} (h : AgW ρ σ) {α : Life}
    (hd : ρ.InStratum (↓α)) {l : BoCa.Loc}
    (hl : ∀ φ, ρ.get l = some φ → φ.InStratum α)
    {ψ : CellU BoCa.Loc BoCa.Val} (hg : σ.get l = some ψ) : ψ.InStratum α := by
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      rename_i a bm bi wm wi
      have hbms : bm.InStratum α := by
        refine BoLo.inStratum_bigComp (BoLo.compR_hC α) hbm ?_
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        obtain ⟨φ, hφ, hag⟩ := AgWitsM.mem hwm p hp
        exact BoLo.AgW.inStratum hag α (CellU.wit_inStratum_of_down (hd _ _ hφ))
      have hbis : bi.InStratum α := by
        refine BoLo.inStratum_bigComp (BoLo.compR_hC α) hbi ?_
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        obtain ⟨φ, ev, av, hφ, hex, hag, hc⟩ := AgWitsI.mem hwi p hp
        exact BoLo.inStratum_comp (BoLo.compR_hC α) hc
          (BoLo.ExW.inStratum BoLo.compR_hC hex α
            (CellU.wit_inStratum_of_down (hd _ _ hφ)))
          (BoLo.AgW.inStratum hag α (CellU.wit_inStratum_of_down (hd _ _ hφ)))
      refine ResU.inStratum_comp_at (BoLo.compR_hC α) hσ ?_ (fun φ e => hbis l φ e) hg
      intro φ e
      exact ResU.inStratum_comp_at (BoLo.compR_hC α) ha
        (fun χ f => hl χ (ResU.restrict_eq_some.mp f).1)
        (fun χ f => hbms l χ f) e

/-- `BoLo.flat_inStratum` at one location, for a resource in `Res_{↓α}`.
`[about ours: the first elided step of `[TR]` Lemma 6.50's proof, at one
location]` -/
theorem ResU.flat_inStratum_at {ρ σ : ResU BoCa.Loc BoCa.Val} {α : Life}
    (h : ResU.Flat ρ σ) (hd : ρ.InStratum (↓α)) {l : BoCa.Loc}
    (hl : ∀ φ, ρ.get l = some φ → φ.InStratum α)
    {ψ : CellU BoCa.Loc BoCa.Val} (hg : σ.get l = some ψ) : ψ.InStratum α := by
  obtain ⟨e, a, he, ha, hc⟩ := h
  exact ResU.inStratum_comp_at (BoLo.compS_hC α) hc
    (fun φ f => ExW.inStratum_at BoLo.compS_hC he hd hl f)
    (fun φ f => AgW.inStratum_at ha hd hl f) hg

/-- `BoLo.flat_inStratum_inv` at one location.
`[about ours: the second elided step of `[TR]` Lemma 6.50's proof, at one
location]` -/
theorem ResU.flat_inStratum_inv_at {ρ σ : ResU BoCa.Loc BoCa.Val} {α : Life}
    (h : ResU.Flat ρ σ) {l : BoCa.Loc}
    (hσ : ∀ φ, σ.get l = some φ → φ.InStratum α)
    {ψ : CellU BoCa.Loc BoCa.Val} (hl : ρ.get l = some ψ) : ψ.InStratum α := by
  obtain ⟨e, a, he, ha, hc⟩ := h
  by_cases hk : ψ.kind = Kind.imm
  · obtain ⟨χ, hχ, hkχ, hle⟩ := BoLo.agW_get_at ha hl hk
    have hσl : σ.get l = some χ :=
      ResU.CompS.get_right_of_immFree hc (ExS.immFree he) hχ
    exact BoLo.cell_inStratum_of_at (lt_of_lt_of_le
      (BoLo.cell_at_of_inStratum (by rw [hkχ]; simp) (hσ χ hσl)) hle)
  · exact hσ ψ (ResU.CompS.get_left_of_ne_imm hc (ExS.get_of_ne_imm he hl hk) hk).2

/-- `[TR]` Lemma 6.50 at one location, for a resource in `Res_{↓α}`.
`[about ours: `[TR]` Lemma 6.50 (p. 16) at one location]` -/
theorem ResU.updV_outlives_at {ρ ρ' : ResU BoCa.Loc BoCa.Val} {α : Life}
    (hd : ρ.InStratum (↓α)) (hu : ResU.UpdV ρ ρ') {l : BoCa.Loc}
    (hl : ∀ φ, ρ.get l = some φ → φ.InStratum α)
    {ψ : CellU BoCa.Loc BoCa.Val} (hg : ρ'.get l = some ψ) : ψ.InStratum α := by
  obtain ⟨σ, hσ⟩ := hu.2.1
  obtain ⟨σ', hσ'⟩ := hu.2.2
  refine ResU.flat_inStratum_inv_at hσ' (fun χ hχ => ?_) hg
  rcases CellU.rep χ with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b, w, ξ, hξ, P, hP, rfl⟩
  · exact trivial
  · obtain ⟨τ, hτ, hgg⟩ := (hu.1.1 l s w ξ hξ).mpr ⟨σ', hσ', hχ⟩
    cases ResU.Flat.functional hτ hσ
    exact ResU.flat_inStratum_at hσ hd hl hgg
  · obtain ⟨w₀, ξ₀, hξ₀, hP₀, τ, hτ, hgg⟩ :=
      (hu.1.2 l b P).mpr ⟨w, ξ, hξ, hP, ⟨σ', hσ', hχ⟩⟩
    cases ResU.Flat.functional hτ hσ
    exact (ResU.flat_inStratum_at hσ hd hl hgg : b ⊐ α)

/-- `@(ρ ⊟ ρ′) ⊐ α`: `[TR]` 6.52's second conclusion.  `hoff` is the printed
*"all parts of the resource outlive `α`"*, off `dom(ρ′)`; `hon` is the printed
exception *"except for the locations in `ρ` that are mut or own in `ρ′ᵢ`"*.
`[about ours: `[TR]` 6.52's second conclusion, stated at `⊟`]` -/
theorem ResU.Sub.inStratum {ρ ρ' χ : ResU Loc Val} {α : Life}
    (h : ResU.Sub ρ ρ' χ) (hd : ρ.InStratum (↓α))
    (hoff : ∀ (l : Loc) (φ : CellU Loc Val), ρ'.get l = none →
        ρ.get l = some φ → φ.InStratum α)
    (hon : ∀ (l : Loc) (ζ : CellU Loc Val), ρ'.get l = some ζ →
        ∃ (s s' : LSet) (v : Val) (w : ResU Loc Val)
          (hs : w.InStratum s.join) (hs' : w.InStratum s'.join),
          ρ.get l = some (CellU.immOf s v w hs) ∧
          ζ = CellU.immOf s' v w hs' ∧ s'.mem α) :
    χ.InStratum α := by
  classical
  obtain ⟨ρ'', -, hle, -, hclause, hcomp⟩ := h
  intro l ψ hψ
  refine ResU.inStratum_comp_at (CellU.compS_hC α) hcomp ?_ ?_ hψ
  · -- `ρ|own,mut`: at a location `ρ′` covers, `ρ`'s cell is `imm`
    intro φ hφ
    obtain ⟨hφg, hφk⟩ := ResU.exclPart_eq_some.mp hφ
    cases hl : ρ'.get l with
    | none => exact hoff l φ hl hφg
    | some ζ =>
        obtain ⟨s, s', v, w, hs, hs', hρl, -, -⟩ := hon l ζ hl
        rw [show φ = CellU.immOf s v w hs from Option.some.inj (hφg.symm.trans hρl)] at hφk
        exact absurd (CellU.kind_immOf s v w hs) hφk
  · -- `ρ″`
    intro φ hφ
    cases hl : ρ'.get l with
    | none =>
        obtain ⟨f, hf⟩ := hle
        refine ResU.CompS.inStratum_left_at hf (fun ω hω => ?_) hφ
        exact hoff l ω hl (ResU.restrict_eq_some.mp hω).1
    | some ζ =>
        obtain ⟨s, s', v, w, hs, hs', hρl, hζ, hα⟩ := hon l ζ hl
        obtain ⟨hempty, hdiff⟩ :=
          hclause l s s' v w hs hs' hρl (hl.trans (congrArg some hζ))
        by_cases he : LSet.DiffEmpty s s'
        · rw [hempty he] at hφ; exact absurd hφ (by simp)
        · obtain ⟨u, hu⟩ := LSet.exists_diff he
          obtain ⟨hu', hgot⟩ := hdiff u hu he
          rw [show φ = CellU.immOf u v w hu' from Option.some.inj (hφ.symm.trans hgot)]
          obtain ⟨hmems, hnot⟩ := (hu u.meet).mp u.meet_mem
          have hsm : (↓α) < s.meet := hd l _ hρl
          have hdown : (↓α) < u.meet :=
            lt_of_lt_of_le hsm (s.meet_least u.meet hmems)
          exact lt_of_le_of_ne (Life.le_of_down_lt hdown)
            (fun e => hnot (e ▸ hα))

/-- `ρ|dom(ρ′ᵢ|mut,own)` carries `imm` cells only.
`[about ours: Definition 6.3's first bullet at `[TR]` 6.52's subtrahend]` -/
theorem ResU.reb_restrictDom_exclPart_empty {α : Life} {ρ'i ρ : ResU Loc Val}
    (hreb : ResU.Reb α ρ'i ρ) :
    (ρ.restrictDom ρ'i.exclPart).exclPart = PMap.empty := by
  refine PMap.ext fun m => ?_
  have hnone : (ρ.restrictDom ρ'i.exclPart).exclPart.get m = none := by
    cases f : (ρ.restrictDom ρ'i.exclPart).exclPart.get m with
    | none => rfl
    | some ξ =>
        obtain ⟨g1, g2⟩ := ResU.exclPart_eq_some.mp f
        exact absurd (ResU.reb_imm_image hreb (ResU.restrictDom_get_inv g1)) g2
  rw [hnone]; rfl

end BoCa.Fig16

end

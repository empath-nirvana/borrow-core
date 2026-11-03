import Support.Model.Tree.Port.Six16to24

/-!
# The walks' strata, over the tree-stratified carrier

`[spec §62]`. `Support/Model/Outlives.lean`'s strata of cells, compositions and walks, read at
`CellUT K`.
-/

noncomputable section

namespace BoCa.Fig16.Tree.BoLo
open BoCa.Fig16 BoCa.Fig16.Tree
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-! The printed `@ψ ⊐ α` is `ψ ∈ Cell_α` here, read at every member of the cell's lifetime
set; the printed `@χ ⊑ @ψ` ("`χ` no longer-lived than `ψ`") is read as what the proofs use of
it, that every stratum holding `χ` holds `ψ` (`StratumLE`). -/

/-- Every stratum holding `χ` holds `ψ`: the printed `@χ ⊑ @ψ`, read as strata. -/
def StratumLE (χ ψ : CellUT BoCa.Loc BoCa.Val K) : Prop := ∀ α, χ.InStratum α → ψ.InStratum α

/-- A cell's witness lies in every stratum the cell does: the witness is above every member
of the cell's lifetime set, and every member is above the stratum. -/
theorem cell_wit_inStratum {α : TSet} {ψ : CellUT BoCa.Loc BoCa.Val K}
    (h : ψ.InStratum α) : ψ.wit.InStratum α := by
  cases ψ with
  | own v => intro l χ e; exact absurd e (by simp [CellUT.wit])
  | imm i =>
      refine ResUT.InStratum.mono (fun x hx => ?_) (CellUT.wit_inStratum_imm (i := i))
      obtain ⟨y, hy⟩ := i.ls.ne
      exact ⟨y, hy, (h x hx y hy).le⟩
  | «mut» m =>
      refine ResUT.InStratum.mono (fun x hx => ?_) (CellUT.wit_inStratum_mut (m := m))
      obtain ⟨y, hy⟩ := m.ls.ne
      exact ⟨y, hy, (h x hx y hy).le⟩

/-- `Cell_α` is closed under `●`. -/
theorem cellCompS_inStratum {α : TSet} {ψ₁ ψ₂ ψ : CellUT BoCa.Loc BoCa.Val K}
    (h : CellUT.CompS ψ₁ ψ₂ ψ) (h₁ : ψ₁.InStratum α) (h₂ : ψ₂.InStratum α) :
    ψ.InStratum α :=
  (CellUT.CompS.inStratum h α).mpr ⟨h₁, h₂⟩

/-- `Cell_α` is closed under `○`; clause 3's `min(β̄₁ ∪ β̄₂)` is above `α` when both are. -/
theorem cellCompR_inStratum {α : TSet} {ψ₁ ψ₂ ψ : CellUT BoCa.Loc BoCa.Val K}
    (h : CellUT.CompR ψ₁ ψ₂ ψ) (h₁ : ψ₁.InStratum α) (h₂ : ψ₂.InStratum α) :
    ψ.InStratum α := by
  cases h with
  | same χ => exact h₁
  | strict k => exact cellCompS_inStratum (CellUT.compS_spec _ _ k) h₁ h₂
  | mutMut a b v ρ ha hb P Q hP hQ =>
      exact (K.above_minS_iff).mpr ((K.above_union_iff).mpr ⟨h₁, h₂⟩)
  | mutOwn a v ρ ha P hP => exact h₁
  | ownMut a v ρ ha P hP => exact h₂
  | immOwn s v ρ hs => exact h₁
  | ownImm s v ρ hs => exact h₂
  | immMut s v ρ hs b hb P hP => exact h₁
  | mutImm s v ρ hs b hb P hP => exact h₂

/-- `○` does not shorten an `imm` operand: the composite's lifetime set contains it. -/
theorem cellCompR_at_le_imm {ψ₁ ψ₂ ψ : CellUT BoCa.Loc BoCa.Val K}
    (h : CellUT.CompR ψ₁ ψ₂ ψ) (hk : ψ₁.kind = Kind.imm) : StratumLE ψ ψ₁ := by
  intro α hα
  cases h with
  | same χ => exact hα
  | strict k =>
      exact ((CellUT.CompS.inStratum (CellUT.compS_spec _ _ k) α).mp hα).1
  | mutMut a b v ρ ha hb P Q hP hQ => exact absurd hk (by simp)
  | mutOwn a v ρ ha P hP => exact absurd hk (by simp)
  | ownMut a v ρ ha P hP => exact absurd hk (by simp)
  | immOwn s v ρ hs => exact hα
  | ownImm s v ρ hs => exact absurd hk (by simp)
  | immMut s v ρ hs b hb P hP => exact hα
  | mutImm s v ρ hs b hb P hP => exact absurd hk (by simp)

theorem inStratum_restrict {α : TSet} {ρ : ResUT BoCa.Loc BoCa.Val K} {k : Kind} (h : ρ.InStratum α) :
    ResUT.InStratum (ρ := (G.restrict CellUT.kind ρ k)) α :=
  fun l ψ e => h l ψ (ResUT.restrict_eq_some.mp e).1

/-- `Res_α` is closed under `◐` whenever `Cell_α` is closed under the cell
operation.
`[about ours: `Res_α` at the composition schema]` -/
theorem inStratum_comp {α : TSet}
    {R : CellUT BoCa.Loc BoCa.Val K → CellUT BoCa.Loc BoCa.Val K → Prop}
    {C : CellUT BoCa.Loc BoCa.Val K → CellUT BoCa.Loc BoCa.Val K → CellUT BoCa.Loc BoCa.Val K → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ₁.InStratum α → ψ₂.InStratum α → ψ.InStratum α)
    {ρ₁ ρ₂ ρ : ResUT BoCa.Loc BoCa.Val K} (h : ResUT.Comp R C ρ₁ ρ₂ ρ)
    (h₁ : ρ₁.InStratum α) (h₂ : ρ₂.InStratum α) : ρ.InStratum α := by
  intro l ψ e
  rcases h.get l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, f, hCc⟩
  · rw [f] at e; exact absurd e (by simp)
  · rw [f] at e; cases Option.some.inj e; exact h₁ l _ f₁
  · rw [f] at e; cases Option.some.inj e; exact h₂ l _ f₂
  · rw [f] at e; cases Option.some.inj e; exact hC _ _ _ hCc (h₁ l _ f₁) (h₂ l _ f₂)

/-- `Res_α` is closed under `⨀`. -/
theorem inStratum_bigComp {α : TSet}
    {R : CellUT BoCa.Loc BoCa.Val K → CellUT BoCa.Loc BoCa.Val K → Prop}
    {C : CellUT BoCa.Loc BoCa.Val K → CellUT BoCa.Loc BoCa.Val K → CellUT BoCa.Loc BoCa.Val K → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ₁.InStratum α → ψ₂.InStratum α → ψ.InStratum α) :
    ∀ {xs : List (ResUT BoCa.Loc BoCa.Val K)} {b : ResUT BoCa.Loc BoCa.Val K}, BigCompT R C xs b →
      (∀ x ∈ xs, x.InStratum α) → b.InStratum α := by
  intro xs b h
  induction h with
  | nil => intro _ l ψ e; exact absurd e (by simp)
  | cons ht hc ih =>
      intro hx
      exact inStratum_comp hC hc (hx _ (by simp))
        (ih fun x hm => hx x (by simp [hm]))

theorem compS_hC (α : TSet) : ∀ ψ₁ ψ₂ ψ : CellUT BoCa.Loc BoCa.Val K,
    CellUT.CompS ψ₁ ψ₂ ψ → ψ₁.InStratum α → ψ₂.InStratum α → ψ.InStratum α :=
  fun _ _ _ => cellCompS_inStratum

theorem compR_hC (α : TSet) : ∀ ψ₁ ψ₂ ψ : CellUT BoCa.Loc BoCa.Val K,
    CellUT.CompR ψ₁ ψ₂ ψ → ψ₁.InStratum α → ψ₂.InStratum α → ψ.InStratum α :=
  fun _ _ _ => cellCompR_inStratum

/-- The exclusive walk keeps the stratum.
`[about ours: the step 6.50's proof needs and does not name, at `ex(ρ)_◐`]` -/
theorem ExWT.inStratum
    {R : CellUT BoCa.Loc BoCa.Val K → CellUT BoCa.Loc BoCa.Val K → Prop}
    {C : CellUT BoCa.Loc BoCa.Val K → CellUT BoCa.Loc BoCa.Val K → CellUT BoCa.Loc BoCa.Val K → Prop}
    (hC : ∀ (α : TSet) ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ₁.InStratum α → ψ₂.InStratum α →
        ψ.InStratum α)
    {ρ σ : ResUT BoCa.Loc BoCa.Val K} (h : ExWT R C ρ σ) : ∀ α, ρ.InStratum α → σ.InStratum α := by
  refine G.ExW.rec (motive_1 := fun ρ σ _ => ∀ α, ResUT.InStratum α ρ → ResUT.InStratum α σ)
    (motive_2 := fun ρ w _ => ∀ α, ResUT.InStratum α ρ → ∀ p ∈ w, ResUT.InStratum α p.2)
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
theorem AgWT.inStratum {ρ σ : ResUT BoCa.Loc BoCa.Val K} (h : AgWT ρ σ) :
    ∀ α, ρ.InStratum α → σ.InStratum α := by
  refine G.AgW.rec (motive_1 := fun ρ σ _ => ∀ α, ResUT.InStratum α ρ → ResUT.InStratum α σ)
    (motive_2 := fun ρ w _ => ∀ α, ResUT.InStratum α ρ → ∀ p ∈ w, ResUT.InStratum α p.2)
    (motive_3 := fun ρ w _ => ∀ α, ResUT.InStratum α ρ → ∀ p ∈ w, ResUT.InStratum α p.2)
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
        (ExWT.inStratum compR_hC hex α (cell_wit_inStratum (hρ l ψ hψ)))
        (iha α (cell_wit_inStratum (hρ l ψ hψ)))
    · exact ihw α hρ p hp

/-- `ρ ∈ Res_α` implies `⦇ρ⦈ ∈ Res_α`.
`[about ours: the first elided step of `[TR]` Lemma 6.50's proof]` -/
theorem flat_inStratum {ρ σ : ResUT BoCa.Loc BoCa.Val K} {α : TSet} (h : ResUT.Flat ρ σ)
    (hρ : ρ.InStratum α) : σ.InStratum α := by
  obtain ⟨e, a, he, ha, hc⟩ := h
  exact inStratum_comp (compS_hC α) hc (ExWT.inStratum compS_hC he α hρ)
    (AgWT.inStratum ha α hρ)


/-- `ag(ρ)` keeps every `imm` cell of `ρ` at its own location and does not shorten it. -/
theorem compR_get_at {ρ₁ ρ₂ ρ : ResUT BoCa.Loc BoCa.Val K} (h : ResUT.CompR ρ₁ ρ₂ ρ)
    {l : BoCa.Loc} {ψ : CellUT BoCa.Loc BoCa.Val K} (e : ρ₁.get l = some ψ)
    (hk : ψ.kind = Kind.imm) :
    ∃ χ, ρ.get l = some χ ∧ χ.kind = Kind.imm ∧ StratumLE χ ψ := by
  rcases ResUT.Comp.get h l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hCc⟩
  · rw [f₁] at e; exact absurd e (by simp)
  · rw [f₁] at e; cases Option.some.inj e; exact ⟨_, f, hk, fun _ h => h⟩
  · rw [f₁] at e; exact absurd e (by simp)
  · rw [f₁] at e
    cases Option.some.inj e
    exact ⟨χ, f, (CellUT.CompR.imm_left hCc hk).1, cellCompR_at_le_imm hCc hk⟩

theorem agW_get_at {ρ σ : ResUT BoCa.Loc BoCa.Val K} (h : AgWT ρ σ) {l : BoCa.Loc}
    {ψ : CellUT BoCa.Loc BoCa.Val K} (e : ρ.get l = some ψ) (hk : ψ.kind = Kind.imm) :
    ∃ χ, σ.get l = some χ ∧ χ.kind = Kind.imm ∧ StratumLE χ ψ := by
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      obtain ⟨χ₀, f₀, k₀, le₀⟩ := compR_get_at ha (ResUT.restrict_get_some e hk) hk
      obtain ⟨χ, f, k', le₁⟩ := compR_get_at hσ f₀ k₀
      exact ⟨χ, f, k', fun α hα => le₀ α (le₁ α hα)⟩

/-- `⦇ρ⦈ ∈ Res_α` implies `ρ ∈ Res_α`. -/
theorem flat_inStratum_inv {ρ σ : ResUT BoCa.Loc BoCa.Val K} {α : TSet} (h : ResUT.Flat ρ σ)
    (hσ : σ.InStratum α) : ρ.InStratum α := by
  obtain ⟨e, a, he, ha, hc⟩ := h
  intro l ψ hl
  by_cases hk : ψ.kind = Kind.imm
  · obtain ⟨χ, hχ, hkχ, hle⟩ := agW_get_at ha hl hk
    have hσl : σ.get l = some χ :=
      ResUT.CompS.get_right_of_immFree hc (ExST.immFree he) hχ
    exact hle α (hσ l χ hσl)
  · exact hσ l ψ (ResUT.CompS.get_left_of_ne_imm hc (ExST.get_of_ne_imm he hl hk) hk).2

end BoCa.Fig16.Tree.BoLo

end

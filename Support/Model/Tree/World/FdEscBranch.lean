import Support.Model.Tree.World.FdEsc
import Support.Model.Tree.World.Coherent
import Support.Model.Tree.World.InvUses

/-!
# The escrow's frame condition from branch points

`[spec §62]`. `FdEscOfBranchT` (`World/FdEsc.lean`): at a `TWNT` world, for a record proper `p` framed
at `α`, a part `ρ_rest` of the world whose top cells are on a branch `n` not inside `α` holds
nothing, in its flattening, at `p`'s location nor at its escrow's exclusive locations.

* **The flattening is on the branch** (`flat_onBranch`): the strata put every cell beneath a cell
  above every lifetime of that cell, so a resource's walks keep its branch, read off the top
  cells.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K : WCactus}

/-! ### The walks keep the branch -/

/-- **The strata carry a cell's branch to its witness**: every cell of an `imm`/`mut` cell's
witness carries lifetimes strictly enclosing every lifetime of the cell. -/
theorem CellAboveT.wit {n : Life} {ψ : TCell K} (h : CellAboveT K n ψ) :
    OnBranchResT K n ψ.wit := by
  intro l χ e s hs x hx
  cases ψ with
  | own v => simp [CellUT.wit] at e
  | imm i =>
      have hst : χ.InStratum i.ls := CellUT.wit_inStratum_imm l χ e
      obtain ⟨a, ha⟩ := i.ls.ne
      have hna := h i.ls rfl a ha
      cases χ with
      | own => cases hs
      | imm j => cases hs; exact K.trans hna (hst a ha x hx).1
      | «mut» m => cases hs; exact K.trans hna (hst a ha x hx).1
  | «mut» m =>
      have hst : χ.InStratum m.ls := CellUT.wit_inStratum_mut l χ e
      obtain ⟨a, ha⟩ := m.ls.ne
      have hna := h m.ls rfl a ha
      cases χ with
      | own => cases hs
      | imm j => cases hs; exact K.trans hna (hst a ha x hx).1
      | «mut» m' => cases hs; exact K.trans hna (hst a ha x hx).1

/-- `○` keeps the branch: its composite carries lifetimes of its operands. -/
theorem CellAboveT.compR {n : Life} {ψ₁ ψ₂ ψ : TCell K} (hc : CellUT.CompR ψ₁ ψ₂ ψ)
    (h₁ : CellAboveT K n ψ₁) (h₂ : CellAboveT K n ψ₂) : CellAboveT K n ψ := by
  cases hc with
  | same => exact h₁
  | strict hcs =>
      obtain ⟨s₁, s₂, e₁, e₂, e₃⟩ := CellUT.CompS.ls (CellUT.compS_spec _ _ hcs)
      intro s hs x hx
      rw [e₃] at hs; cases hs
      simp only [TSet.union_set, Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact h₁ s₁ e₁ x hx
      · exact h₂ s₂ e₂ x hx
  | mutMut s t v ρ hs ht P Q hP hQ =>
      intro u hu x hx
      rw [CellUT.lsOf_mutOf] at hu; cases hu
      have hx' := K.minS_sub hx
      simp only [TSet.union_set, Finset.mem_union] at hx'
      rcases hx' with hx' | hx'
      · exact h₁ s (CellUT.lsOf_mutOf _ _ _ _ _ _) x hx'
      · exact h₂ t (CellUT.lsOf_mutOf _ _ _ _ _ _) x hx'
  | mutOwn => exact h₁
  | ownMut => exact h₂
  | immOwn => exact h₁
  | ownImm => exact h₂
  | immMut => exact h₁
  | mutImm => exact h₂

theorem CellAboveT.compS {n : Life} {ψ₁ ψ₂ ψ : TCell K} (hc : CellUT.CompS ψ₁ ψ₂ ψ)
    (h₁ : CellAboveT K n ψ₁) (h₂ : CellAboveT K n ψ₂) : CellAboveT K n ψ := by
  obtain ⟨s₁, s₂, e₁, e₂, e₃⟩ := CellUT.CompS.ls hc
  intro s hs x hx
  rw [e₃] at hs; cases hs
  simp only [TSet.union_set, Finset.mem_union] at hx
  rcases hx with hx | hx
  · exact h₁ s₁ e₁ x hx
  · exact h₂ s₂ e₂ x hx

theorem OnBranchResT.comp {R : TCell K → TCell K → Prop} {C : TCell K → TCell K → TCell K → Prop}
    {n : Life} (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → CellAboveT K n ψ₁ → CellAboveT K n ψ₂ →
      CellAboveT K n ψ) {a b c : TRes K} (hc : ResUT.Comp R C a b c)
    (ha : OnBranchResT K n a) (hb : OnBranchResT K n b) : OnBranchResT K n c := by
  intro l ψ e
  rcases ResUT.Comp.get hc l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, f, hC'⟩
  · rw [e] at f; cases f
  · rw [e] at f; cases Option.some.inj f; exact ha l _ f₁
  · rw [e] at f; cases Option.some.inj f; exact hb l _ f₂
  · rw [e] at f; cases Option.some.inj f; exact hC _ _ _ hC' (ha l _ f₁) (hb l _ f₂)

theorem OnBranchResT.bigComp {R : TCell K → TCell K → Prop}
    {C : TCell K → TCell K → TCell K → Prop} {n : Life}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → CellAboveT K n ψ₁ → CellAboveT K n ψ₂ → CellAboveT K n ψ)
    {xs : List (TRes K)} {b : TRes K} (h : BigCompT R C xs b)
    (hx : ∀ x ∈ xs, OnBranchResT K n x) : OnBranchResT K n b := by
  induction h with
  | nil => exact OnBranchResT.empty n
  | cons _ hc ih =>
      exact OnBranchResT.comp hC hc (hx _ List.mem_cons_self)
        (ih fun x hx' => hx x (List.mem_cons_of_mem _ hx'))

theorem OnBranchResT.restrict {n : Life} {ρ : TRes K} (h : OnBranchResT K n ρ) (k : Kind) :
    OnBranchResT K n (G.restrict CellUT.kind ρ k) :=
  fun l ψ e => h l ψ (ResUT.restrict_eq_some.mp e).1

/-- The exclusive walk keeps the branch. -/
theorem exWT_onBranch {R : TCell K → TCell K → Prop} {C : TCell K → TCell K → TCell K → Prop}
    {n : Life} (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → CellAboveT K n ψ₁ → CellAboveT K n ψ₂ →
      CellAboveT K n ψ) {ρ σ : TRes K} (h : ExWT R C ρ σ) :
    OnBranchResT K n ρ → OnBranchResT K n σ := by
  refine G.ExW.rec (motive_1 := fun ρ σ _ => OnBranchResT K n ρ → OnBranchResT K n σ)
    (motive_2 := fun ρ w _ => OnBranchResT K n ρ → ∀ q ∈ w, OnBranchResT K n q.2)
    ?mk ?nil ?cons h
  case mk =>
    intro ρ' σ' nm b w hs hw hb hnm hσ ih hρ
    refine OnBranchResT.comp hC hσ
      (OnBranchResT.comp hC hnm (hρ.restrict _) (hρ.restrict _))
      (OnBranchResT.bigComp hC hb fun x hx => ?_)
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact ih hρ q hq
  case nil => intro ρ' hρ q hq; exact absurd hq (by simp)
  case cons =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw hρ q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ihe (hρ l ψ hψ).wit
    · exact ihw hρ q hq

/-- The aliasable walk keeps the branch. -/
theorem agWT_onBranch {n : Life} {ρ σ : TRes K} (h : AgWT ρ σ) :
    OnBranchResT K n ρ → OnBranchResT K n σ := by
  have hR : ∀ ψ₁ ψ₂ ψ : TCell K, CellUT.CompR ψ₁ ψ₂ ψ → CellAboveT K n ψ₁ →
      CellAboveT K n ψ₂ → CellAboveT K n ψ := fun _ _ _ hc => CellAboveT.compR hc
  refine G.AgW.rec (motive_1 := fun ρ σ _ => OnBranchResT K n ρ → OnBranchResT K n σ)
    (motive_2 := fun ρ w _ => OnBranchResT K n ρ → ∀ q ∈ w, OnBranchResT K n q.2)
    (motive_3 := fun ρ w _ => OnBranchResT K n ρ → ∀ q ∈ w, OnBranchResT K n q.2)
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ' σ' a bm bi wm wi hsm hsi hwm hwi hbm hbi ha hσ ihm ihi hρ
    refine OnBranchResT.comp hR hσ
      (OnBranchResT.comp hR ha (hρ.restrict _) (OnBranchResT.bigComp hR hbm fun x hx => ?_))
      (OnBranchResT.bigComp hR hbi fun x hx => ?_)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx; exact ihm hρ q hq
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx; exact ihi hρ q hq
  case nilM => intro ρ' hρ q hq; exact absurd hq (by simp)
  case consM =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw hρ q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ihe (hρ l ψ hψ).wit
    · exact ihw hρ q hq
  case nilI => intro ρ' hρ q hq; exact absurd hq (by simp)
  case consI =>
    intro ρ' pe l w ψ hψ hk e a hex hag hc hw iha ihw hρ q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · have hwb := (hρ l ψ hψ).wit
      exact OnBranchResT.comp hR hc (exWT_onBranch hR hex hwb) (iha hwb)
    · exact ihw hρ q hq

/-- **The flattening of a resource on a branch is on it.** -/
theorem flat_onBranch {n : Life} {ρ τ : TRes K} (h : OnBranchResT K n ρ) (hτ : ResUT.Flat ρ τ) :
    OnBranchResT K n τ := by
  obtain ⟨e, a, he, ha, hc⟩ := hτ
  have hS : ∀ ψ₁ ψ₂ ψ : TCell K, CellUT.CompS ψ₁ ψ₂ ψ → CellAboveT K n ψ₁ →
      CellAboveT K n ψ₂ → CellAboveT K n ψ := fun _ _ _ hc => CellAboveT.compS hc
  exact OnBranchResT.comp hS hc (exWT_onBranch hS he h) (agWT_onBranch ha h)

/-! ### Where a non-`imm` cell of a walk comes from -/

/-- A non-`imm` composite of `○` is an operand's cell kind and witness. -/
theorem CellUT.CompR.back_kind {ψ₁ ψ₂ ψ : TCell K} (hc : CellUT.CompR ψ₁ ψ₂ ψ)
    (hk : ψ.kind ≠ Kind.imm) :
    (ψ₁.kind = ψ.kind ∧ ψ₁.wit = ψ.wit) ∨ (ψ₂.kind = ψ.kind ∧ ψ₂.wit = ψ.wit) := by
  cases hc with
  | same => exact Or.inl ⟨rfl, rfl⟩
  | strict hcs => exact absurd (CellUT.CompS.kind_imm (CellUT.compS_spec _ _ hcs)) hk
  | mutMut s t v ρ hs ht P Q hP hQ =>
      refine Or.inl ⟨rfl, ?_⟩
      rw [CellUT.wit_mutOf, CellUT.wit_mutOf]
  | mutOwn => exact Or.inl ⟨rfl, rfl⟩
  | ownMut => exact Or.inr ⟨rfl, rfl⟩
  | immOwn => exact absurd (CellUT.kind_immOf _ _ _ _) hk
  | ownImm => exact absurd (CellUT.kind_immOf _ _ _ _) hk
  | immMut => exact absurd (CellUT.kind_immOf _ _ _ _) hk
  | mutImm => exact absurd (CellUT.kind_immOf _ _ _ _) hk

theorem back_kind {R : TCell K → TCell K → Prop} {C : TCell K → TCell K → TCell K → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ.kind ≠ Kind.imm →
      (ψ₁.kind = ψ.kind ∧ ψ₁.wit = ψ.wit) ∨ (ψ₂.kind = ψ.kind ∧ ψ₂.wit = ψ.wit))
    {a₁ a₂ a : TRes K} (h : ResUT.Comp R C a₁ a₂ a) {l : BoCa.Loc} {ψ : TCell K}
    (e : a.get l = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    (∃ ψ₁, a₁.get l = some ψ₁ ∧ ψ₁.kind = ψ.kind ∧ ψ₁.wit = ψ.wit) ∨
    (∃ ψ₂, a₂.get l = some ψ₂ ∧ ψ₂.kind = ψ.kind ∧ ψ₂.wit = ψ.wit) := by
  rcases ResUT.Comp.get h l with ⟨-, -, e'⟩ | ⟨ζ, e₁, -, e'⟩ | ⟨ζ, -, e₂, e'⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁, e₂, e', hc⟩
  · rw [e'] at e; cases e
  · rw [e'] at e; cases e; exact Or.inl ⟨_, e₁, rfl, rfl⟩
  · rw [e'] at e; cases e; exact Or.inr ⟨_, e₂, rfl, rfl⟩
  · rw [e'] at e; cases e
    rcases hC _ _ _ hc hk with ⟨k, w⟩ | ⟨k, w⟩
    · exact Or.inl ⟨_, e₁, k, w⟩
    · exact Or.inr ⟨_, e₂, k, w⟩

theorem bigComp_back_kind {R : TCell K → TCell K → Prop}
    {C : TCell K → TCell K → TCell K → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ.kind ≠ Kind.imm →
      (ψ₁.kind = ψ.kind ∧ ψ₁.wit = ψ.wit) ∨ (ψ₂.kind = ψ.kind ∧ ψ₂.wit = ψ.wit))
    {xs : List (TRes K)} {b : TRes K} (h : BigCompT R C xs b) {l : BoCa.Loc} {ψ : TCell K}
    (e : b.get l = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    ∃ x ∈ xs, ∃ ψ', x.get l = some ψ' ∧ ψ'.kind = ψ.kind ∧ ψ'.wit = ψ.wit := by
  induction h generalizing ψ with
  | nil => rw [PMap.empty_get] at e; cases e
  | @cons σ τ ρ σs _ hc ih =>
      rcases back_kind hC hc e hk with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₁, e₁, k₁, w₁⟩
      · exact ⟨σ, List.mem_cons_self .., ψ₁, e₁, k₁, w₁⟩
      · obtain ⟨x, hx, ψ', e', k', w'⟩ := ih e₁ (k₁ ▸ hk)
        exact ⟨x, List.mem_cons_of_mem _ hx, ψ', e', k'.trans k₁, w'.trans w₁⟩

theorem hCR_kind : ∀ ψ₁ ψ₂ ψ : TCell K, CellUT.CompR ψ₁ ψ₂ ψ → ψ.kind ≠ Kind.imm →
    (ψ₁.kind = ψ.kind ∧ ψ₁.wit = ψ.wit) ∨ (ψ₂.kind = ψ.kind ∧ ψ₂.wit = ψ.wit) :=
  fun _ _ _ hc hk => CellUT.CompR.back_kind hc hk

/-- A non-`imm` cell of `ex(ρ)_○` is a cell at depth of `ρ`, its kind and witness kept. -/
theorem exRT_cellAt_kind {ρ σ : TRes K} (h : ExRT ρ σ) :
    ∀ x (ψ : TCell K), σ.get x = some ψ → ψ.kind ≠ Kind.imm →
      ∃ ψ₀, CellAt ρ x ψ₀ ∧ ψ₀.kind = ψ.kind ∧ ψ₀.wit = ψ.wit := by
  refine G.ExW.rec (motive_1 := fun ρ σ _ => ∀ x (ψ : TCell K), σ.get x = some ψ →
      ψ.kind ≠ Kind.imm → ∃ ψ₀, CellAt ρ x ψ₀ ∧ ψ₀.kind = ψ.kind ∧ ψ₀.wit = ψ.wit)
    (motive_2 := fun ρ w _ => ∀ q ∈ w, ∀ x (ψ : TCell K), q.2.get x = some ψ →
      ψ.kind ≠ Kind.imm → ∃ ψ₀, CellAt ρ x ψ₀ ∧ ψ₀.kind = ψ.kind ∧ ψ₀.wit = ψ.wit)
    ?mk ?nil ?cons h
  case mk =>
    intro ρ' σ' nm b w hs hw hb hnm hσ ih x ψ e hk
    rcases back_kind hCR_kind hσ e hk with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₁, e₁, k₁, w₁⟩
    · rcases back_kind hCR_kind hnm e₁ (k₁ ▸ hk) with ⟨ψ₂, e₂, k₂, w₂⟩ | ⟨ψ₂, e₂, k₂, w₂⟩
      · exact ⟨ψ₂, .top (ResUT.restrict_eq_some.mp e₂).1, k₂.trans k₁, w₂.trans w₁⟩
      · exact ⟨ψ₂, .top (ResUT.restrict_eq_some.mp e₂).1, k₂.trans k₁, w₂.trans w₁⟩
    · obtain ⟨τ, hτ, ψ', e', k', w'⟩ := bigComp_back_kind hCR_kind hb e₁ (k₁ ▸ hk)
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hτ
      obtain ⟨ψ₀, c₀, k₀, w₀⟩ := ih q hq x ψ' e' (by rw [k', k₁]; exact hk)
      exact ⟨ψ₀, c₀, k₀.trans (k'.trans k₁), w₀.trans (w'.trans w₁)⟩
  case nil => intro ρ' q hq; exact absurd hq (by simp)
  case cons =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · intro x φ ex kx
      obtain ⟨ψ₀, c₀, k₀, w₀⟩ := ihe x φ ex kx
      exact ⟨ψ₀, .nest hψ c₀, k₀, w₀⟩
    · exact ihw q hq'

/-- **A non-`imm` cell of `ag(ρ)` sits beneath a borrow of `ρ`**, its kind and witness kept. -/
theorem agW_nonimm_beneath {ρ σ : TRes K} (h : AgWT ρ σ) :
    ∀ x (ψ : TCell K), σ.get x = some ψ → ψ.kind ≠ Kind.imm →
      ∃ (m : BoCa.Loc) (χ : TCell K), ρ.get m = some χ ∧ χ.kind ≠ Kind.own ∧
        ∃ ψ₀, CellAt χ.wit x ψ₀ ∧ ψ₀.kind = ψ.kind ∧ ψ₀.wit = ψ.wit := by
  refine G.AgW.rec (motive_1 := fun ρ σ _ => ∀ x (ψ : TCell K), σ.get x = some ψ →
      ψ.kind ≠ Kind.imm → ∃ (m : BoCa.Loc) (χ : TCell K), ρ.get m = some χ ∧ χ.kind ≠ Kind.own ∧
        ∃ ψ₀, CellAt χ.wit x ψ₀ ∧ ψ₀.kind = ψ.kind ∧ ψ₀.wit = ψ.wit)
    (motive_2 := fun ρ w _ => ∀ q ∈ w, ∀ x (ψ : TCell K), q.2.get x = some ψ →
      ψ.kind ≠ Kind.imm → ∃ (m : BoCa.Loc) (χ : TCell K), ρ.get m = some χ ∧ χ.kind ≠ Kind.own ∧
        ∃ ψ₀, CellAt χ.wit x ψ₀ ∧ ψ₀.kind = ψ.kind ∧ ψ₀.wit = ψ.wit)
    (motive_3 := fun ρ w _ => ∀ q ∈ w, ∀ x (ψ : TCell K), q.2.get x = some ψ →
      ψ.kind ≠ Kind.imm → ∃ (m : BoCa.Loc) (χ : TCell K), ρ.get m = some χ ∧ χ.kind ≠ Kind.own ∧
        ∃ ψ₀, CellAt χ.wit x ψ₀ ∧ ψ₀.kind = ψ.kind ∧ ψ₀.wit = ψ.wit)
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ' σ' a bm bi wm wi hsm hsi hwm hwi hbm hbi ha hσ ihm ihi x ψ e hk
    rcases back_kind hCR_kind hσ e hk with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₁, e₁, k₁, w₁⟩
    · rcases back_kind hCR_kind ha e₁ (k₁ ▸ hk) with ⟨ψ₂, e₂, k₂, -⟩ | ⟨ψ₂, e₂, k₂, w₂⟩
      · exact absurd ((ResUT.restrict_eq_some.mp e₂).2.symm.trans (k₂.trans k₁)) (Ne.symm hk)
      · obtain ⟨τ, hτ, ψ', e', k', w'⟩ := bigComp_back_kind hCR_kind hbm e₂ (by rw [k₂, k₁]; exact hk)
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hτ
        obtain ⟨m, χ, hm, hχ, ψ₀, c₀, k₀, w₀⟩ := ihm q hq x ψ' e' (by rw [k', k₂, k₁]; exact hk)
        exact ⟨m, χ, hm, hχ, ψ₀, c₀, k₀.trans (k'.trans (k₂.trans k₁)),
          w₀.trans (w'.trans (w₂.trans w₁))⟩
    · obtain ⟨τ, hτ, ψ', e', k', w'⟩ := bigComp_back_kind hCR_kind hbi e₁ (k₁ ▸ hk)
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hτ
      obtain ⟨m, χ, hm, hχ, ψ₀, c₀, k₀, w₀⟩ := ihi q hq x ψ' e' (by rw [k', k₁]; exact hk)
      exact ⟨m, χ, hm, hχ, ψ₀, c₀, k₀.trans (k'.trans k₁), w₀.trans (w'.trans w₁)⟩
  case nilM => intro ρ' q hq; exact absurd hq (by simp)
  case consM =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · intro x φ ex kx
      obtain ⟨m, χ, hm, -, ψ₀, c₀, k₀, w₀⟩ := ihe x φ ex kx
      exact ⟨l, ψ, hψ, by rw [hk]; simp, ψ₀, .nest hm c₀, k₀, w₀⟩
    · exact ihw q hq'
  case nilI => intro ρ' q hq; exact absurd hq (by simp)
  case consI =>
    intro ρ' pe l w ψ hψ hk e a hex hag hc hw iha ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · intro x φ ex kx
      rcases back_kind hCR_kind hc ex kx with ⟨φ₁, e₁, k₁, w₁⟩ | ⟨φ₁, e₁, k₁, w₁⟩
      · obtain ⟨ψ₀, c₀, k₀, w₀⟩ := exRT_cellAt_kind hex x φ₁ e₁ (k₁ ▸ kx)
        exact ⟨l, ψ, hψ, by rw [hk]; simp, ψ₀, c₀, k₀.trans k₁, w₀.trans w₁⟩
      · obtain ⟨m, χ, hm, -, ψ₀, c₀, k₀, w₀⟩ := iha x φ₁ e₁ (k₁ ▸ kx)
        exact ⟨l, ψ, hψ, by rw [hk]; simp, ψ₀, .nest hm c₀, k₀.trans k₁, w₀.trans w₁⟩
    · exact ihw q hq'

/-- An `own` cell at depth is `OwnAt`. -/
theorem CellAt.ownAt {ρ : TRes K} {x : BoCa.Loc} {ψ : TCell K} (h : CellAt ρ x ψ)
    (hk : ψ.kind = Kind.own) : OwnAt ρ x := by
  induction h with
  | top e => exact .top e hk
  | @nest ρ m y χ ψ e h' ih =>
      refine .nest e (fun hχ => ?_) (ih hk)
      cases χ with
      | own => exact CellAt.not_empty h'
      | imm => cases hχ
      | «mut» => cases hχ

/-- A `mut` cell at depth is `MutAtT`. -/
theorem CellAt.mutAt {ρ : TRes K} {x : BoCa.Loc} {ψ : TCell K} (h : CellAt ρ x ψ)
    (hk : ψ.kind = Kind.mut) : MutAtT ρ x := by
  induction h with
  | top e => exact .top e hk
  | @nest ρ m y χ ψ e h' ih =>
      refine .nest e (fun hχ => ?_) (ih hk)
      cases χ with
      | own => exact CellAt.not_empty h'
      | imm => cases hχ
      | «mut» => cases hχ

/-- A borrow of `ρ` reaches a composite `ρ ● ρ'` over the same witness. -/
theorem beneath_of_compS_right {a b c : TRes K} (hc : ResUT.CompS a b c) {m : BoCa.Loc}
    {χ : TCell K} (e : b.get m = some χ) (hk : χ.kind ≠ Kind.own) {x : BoCa.Loc} {ψ : TCell K}
    (h : CellAt χ.wit x ψ) : ∃ χ' : TCell K, c.get m = some χ' ∧ χ'.kind ≠ Kind.own ∧
      CellAt χ'.wit x ψ := by
  obtain ⟨χ', e', k', w', -⟩ := compS_get_right' hc e
  exact ⟨χ', e', k' ▸ hk, w' ▸ h⟩

/-! ### The join's frame condition at the lent location -/

/-- **The frame condition at `p`'s location from a branch point**: a view there carries a lifetime of the branch, while `ag(W)`'s view there is at the
frame `α` (`FrameLifeT`); an `own`/`mut` cell of the exclusive walk meets `ag(W)`'s view
(`LeInvT`); a `mut` cell of the aliasable walk is a `mut` cell at depth (`NoMutT`); an `own` cell
of it sits beneath a borrow (`NoOwnUnderT`). -/
theorem fd_le_of_branch {Θ : CodeTy} {tc : TChoice K}
    {W ρo ρrest : TRes K} {ps rs : List (FrameRecT K)} {p : FrameRecT K} {α n : Life}
    (hT : TWNT K Θ tc W ps rs) (hp : p ∈ ps) (hW : ResUT.CompS ρo ρrest W)
    (hFL : FrameLifeT K W p α) (hbr : OnBranchResT K n ρrest) (hnα : ¬ K.le n α)
    {τ : TRes K} (hτ : ResUT.Flat ρrest τ) : τ.get p.le = none := by
  have hTI := hT.inv
  have hv := hT.valid
  obtain ⟨aW, haW⟩ := agW_of_valid hv
  obtain ⟨ψL, eL, kL, -, -⟩ := hTI.2.1 p hp aW haW
  cases hg : τ.get p.le with
  | none => rfl
  | some χ =>
  exfalso
  have hτn := flat_onBranch hbr hτ p.le χ hg
  obtain ⟨er, ar, her, har, hcr⟩ := hτ
  obtain ⟨a₁, a₂, ha₁, ha₂, hcW⟩ := (AgWT.split hW).mp haW
  obtain rfl := AgWT.functional ha₂ har
  rcases ResUT.Comp.get hcr p.le with ⟨-, -, f⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, -, f₂, f⟩ |
      ⟨ψ₁, ψ₂, ψ, f₁, -, f, hC⟩
  · rw [hg] at f; cases f
  · -- from `ex(ρ_rest)`: in `ex(W)`, which `ag(W)`'s view excludes
    rw [hg] at f; cases Option.some.inj f
    have hk : χ.kind ≠ Kind.imm := ExST.immFree her _ _ f₁
    obtain ⟨eW, heW⟩ : ∃ eW, ExST W eW := by
      obtain ⟨σ, eW, aW', heW, -, -⟩ := hv; exact ⟨eW, heW⟩
    obtain ⟨e₁, e₂, -, he₂, hc₁⟩ := (ExST.split hW).mp heW
    obtain rfl := ExST.functional he₂ her
    have := (ResUT.CompS.get_right_of_ne_imm hc₁ f₁ hk).2
    exact ex_ag_disjoint hv heW haW this eL
  · rw [hg] at f; cases Option.some.inj f
    cases hk : χ.kind with
    | imm =>
        -- a view: its lifetimes are on the branch and in `ag(W)`'s view at `α`
        obtain ⟨s, hs, hη⟩ := CellUT.imm_eta hk
        obtain ⟨t, ht, hηL⟩ := CellUT.imm_eta kL
        rw [hη] at f₂
        rw [hηL] at eL
        obtain ⟨y, hy⟩ := s.ne
        have hyW : y ∈ t.set := ResUT.CompR.get_ls_imm (ResUT.CompR.comm hcW) f₂ eL hy
        have hyα := hFL.1 aW haW _ t eL (CellUT.lsOfI_immOf _ _ _ _) y hyW
        have hny := hτn s (by rw [hη]; exact CellUT.lsOf_immOf _ _ _ _) y hy
        exact hnα (hyα ▸ hny)
    | own =>
        obtain ⟨m, χ', hm, hχ', ψ₀, c₀, k₀, -⟩ :=
          agW_nonimm_beneath har _ χ f₂ (by rw [hk]; simp)
        obtain ⟨χ'', e'', k'', c''⟩ := beneath_of_compS_right hW hm hχ' c₀
        exact TWNT.noOwnUnder hT p hp ⟨m, χ'', e'', k'', c''.ownAt (k₀.trans hk)⟩
    | «mut» =>
        obtain ⟨m, χ', hm, hχ', ψ₀, c₀, k₀, -⟩ :=
          agW_nonimm_beneath har _ χ f₂ (by rw [hk]; simp)
        obtain ⟨χ'', e'', k'', c''⟩ := beneath_of_compS_right hW hm hχ' c₀
        exact hTI.2.2.2.2.2.1.1 p hp (.nest e'' k'' (c''.mutAt (k₀.trans hk)))
  · rw [hg] at f; cases Option.some.inj f
    obtain ⟨_, _, _, _, _, _, _, h₁, _, _⟩ := hC
    exact ExST.immFree her _ _ f₁ (by rw [h₁]; exact CellUT.kind_immOf _ _ _ _)

/-! ### The escrow's exclusive locations are its lineage's -/

theorem GPosT.sumL {R : TRes K} {T₁ T₂ : KTy} {v₁ : BoCa.Val} {m : BoCa.Loc} {S : KTy}
    (h : GPosT R T₁ v₁ m S) : GPosT R (.sum T₁ T₂) (BoCa.Val.inj₁ v₁) m S := by
  cases h with
  | here h => exact .here (.sumL h)
  | step hr e g => exact .step (.sumL hr) e g

theorem GPosT.sumR {R : TRes K} {T₁ T₂ : KTy} {v₂ : BoCa.Val} {m : BoCa.Loc} {S : KTy}
    (h : GPosT R T₂ v₂ m S) : GPosT R (.sum T₁ T₂) (BoCa.Val.inj₂ v₂) m S := by
  cases h with
  | here h => exact .here (.sumR h)
  | step hr e g => exact .step (.sumR hr) e g

theorem GPosT.box {R : TRes K} {a : Life} {T : KTy} {v : BoCa.Val} {m : BoCa.Loc} {S : KTy}
    (h : GPosT R T v m S) : GPosT R (.box a T) v m S := by
  cases h with
  | here h => exact .here (.box h)
  | step hr e g => exact .step (.box hr) e g

theorem GPosT.mono {R₁ R₂ : TRes K}
    (hown : ∀ m u, R₁.get m = some (CellUT.ownOf u) → R₂.get m = some (CellUT.ownOf u))
    {T : KTy} {v : BoCa.Val} {m : BoCa.Loc} {S : KTy} (h : GPosT R₁ T v m S) :
    GPosT R₂ T v m S := by
  induction h with
  | here h => exact .here h
  | step hr e _ ih => exact .step hr (hown _ _ e) ih

/-- **Every `mut` cell of a typed escrow is at a `Mut` position**, its witness of the position's
code. -/
theorem mut_gposT (Θ : CodeTy) :
    ∀ (T : KTy) {v : BoCa.Val} {R : TRes K}, (T.interp Θ).P K v R →
      ∀ {y : BoCa.Loc} {ζ : TCell K}, R.get y = some ζ → ζ.kind = Kind.mut →
      ∃ S, GPosT R T v y S ∧ (S.interp Θ).P K ζ.erase ζ.wit := by
  intro T
  induction T with
  | unit => rintro v R ⟨-, rfl⟩ y ζ e; simp at e
  | sum A B ihA ihB =>
      rintro v R (⟨v₁, rfl, h⟩ | ⟨v₂, rfl, h⟩) y ζ e hk
      · obtain ⟨S, g, hS⟩ := ihA h e hk; exact ⟨S, g.sumL, hS⟩
      · obtain ⟨S, g, hS⟩ := ihB h e hk; exact ⟨S, g.sumR, hS⟩
  | imm a A _ =>
      rintro v R ⟨l, i, rfl, rfl, -⟩ y ζ e hk
      rw [PMap.sng_get] at e
      split_ifs at e
      cases e; cases hk
  | «mut» a A _ =>
      rintro v R ⟨l, m, rfl, rfl, hΘ, -, hP⟩ y ζ e hk
      rw [PMap.sng_get] at e
      split_ifs at e with hy
      cases e; subst hy
      exact ⟨A, .here (.mut a A y), (hP m.v m.ρ).mp m.hw⟩
  | box a A ih =>
      rintro v R ⟨h, -⟩ y ζ e hk
      obtain ⟨S, g, hS⟩ := ih h e hk; exact ⟨S, g.box, hS⟩
  | ref A ih =>
      classical
      rintro v R ⟨l, w, ρ₁, rfl, hl, rfl, h⟩ y ζ e hk
      rw [PMap.ins_get] at e
      split_ifs at e with hy
      · cases e; cases hk
      · obtain ⟨S, g, hS⟩ := ih h e hk
        refine ⟨S, .step (.ref A l) (by rw [PMap.ins_get, if_pos rfl]; rfl) (g.mono ?_), hS⟩
        intro m u em
        rw [PMap.ins_get, if_neg]; exact em
        rintro rfl; rw [hl] at em; cases em

/-- A `●` of two operands: a cell of the composite is a cell of an operand, at the same kind. -/
theorem bigCompS_back_some {xs : List (TRes K)} {b : TRes K}
    (h : BigCompT CellUT.CompatS CellUT.CompS xs b) {l : BoCa.Loc} {ψ : TCell K}
    (e : b.get l = some ψ) : ∃ x ∈ xs, ∃ ψ', x.get l = some ψ' ∧ ψ'.kind = ψ.kind := by
  induction h generalizing ψ with
  | nil => rw [PMap.empty_get] at e; cases e
  | @cons σ τ ρ σs _ hc ih =>
      rcases compS_back hc e with ⟨ψ₁, e₁, k₁, -⟩ | ⟨ψ₁, e₁, k₁, -⟩
      · exact ⟨σ, List.mem_cons_self .., ψ₁, e₁, k₁⟩
      · obtain ⟨x, hx, ψ', e', k'⟩ := ih e₁
        exact ⟨x, List.mem_cons_of_mem _ hx, ψ', e', k'.trans k₁⟩

/-- **A location of a typed record's escrow's exclusive walk is a top `own`/`mut` location of a
member of its lineage.** -/
theorem exST_lineage (Θ : CodeTy) {ρ σ : TRes K} (h : ExST ρ σ) :
    ∀ r : FrameRecT K, r.R = ρ → (r.T.interp Θ).P K r.v r.R →
      ∀ x (ψ : TCell K), σ.get x = some ψ →
        ∃ d, DescRT r d ∧ ∃ ζ : TCell K, d.R.get x = some ζ ∧ ζ.kind ≠ Kind.imm := by
  refine G.ExW.rec (motive_1 := fun ρ σ _ => ∀ r : FrameRecT K, r.R = ρ →
      (r.T.interp Θ).P K r.v r.R → ∀ x (ψ : TCell K), σ.get x = some ψ →
        ∃ d, DescRT r d ∧ ∃ ζ : TCell K, d.R.get x = some ζ ∧ ζ.kind ≠ Kind.imm)
    (motive_2 := fun ρ w _ => ∀ r : FrameRecT K, r.R = ρ → (r.T.interp Θ).P K r.v r.R →
      ∀ q ∈ w, ∀ x (ψ : TCell K), q.2.get x = some ψ →
        ∃ d, DescRT r d ∧ ∃ ζ : TCell K, d.R.get x = some ζ ∧ ζ.kind ≠ Kind.imm)
    ?mk ?nil ?cons h
  case mk =>
    intro ρ' σ' nm b w hs hw hb hnm hσ ih r hr hty x ψ e
    rcases compS_back hσ e with ⟨ψ₁, e₁, -, -⟩ | ⟨ψ₁, e₁, -, -⟩
    · rcases compS_back hnm e₁ with ⟨ψ₂, e₂, -, -⟩ | ⟨ψ₂, e₂, -, -⟩
      · obtain ⟨e₃, k₃⟩ := ResUT.restrict_eq_some.mp e₂
        exact ⟨r, ⟨[], .nil r⟩, ψ₂, hr ▸ e₃, by rw [k₃]; simp⟩
      · obtain ⟨e₃, k₃⟩ := ResUT.restrict_eq_some.mp e₂
        exact ⟨r, ⟨[], .nil r⟩, ψ₂, hr ▸ e₃, by rw [k₃]; simp⟩
    · obtain ⟨τ, hτ, ψ', e', -⟩ := bigCompS_back_some hb e₁
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hτ
      exact ih r hr hty q hq x ψ' e'
  case nil => intro ρ' r _ _ q hq; exact absurd hq (by simp)
  case cons =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw r hr hty q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · intro x φ ex
      obtain ⟨S, g, hS⟩ := mut_gposT Θ r.T hty (hr ▸ hψ) hk
      let d₀ : FrameRecT K := ⟨l, ψ.erase, ψ.wit, S⟩
      have hsub : SubRecT r d₀ := ⟨g, ψ, hr ▸ hψ, hk, rfl, rfl⟩
      obtain ⟨d, ⟨pa, hpa⟩, hd⟩ := ihe d₀ rfl hS x φ ex
      exact ⟨d, ⟨_, .cons hsub hpa⟩, hd⟩
    · exact ihw r hr hty q hq'

/-! ### Beneath a view -/

/-- **Everything beneath a view at depth shows in the aliasable walk.** -/
theorem cellAt_beneath_imm_ag {W : TRes K} {y : BoCa.Loc} {ψ₀ : TCell K} (h : CellAt W y ψ₀)
    (hk : ψ₀.kind = Kind.imm) {x : BoCa.Loc} {χ : TCell K} (hx : CellAt ψ₀.wit x χ) :
    ∀ {aW : TRes K}, AgWT W aW → ∃ ζ, aW.get x = some ζ := by
  induction h with
  | @top W y ψ₀ e =>
      intro aW haW
      obtain ⟨ev, av, p, z, hev, hav, hp, hz⟩ := AgWT.imm_wit_le haW e hk
      rcases cellAt_walk_dom hx hRR ResUT.compLawsR hev hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
      · obtain ⟨_, h1⟩ := comp_some hp hζ; exact comp_some hz h1
      · obtain ⟨_, h1⟩ := comp_some_r hp hζ; exact comp_some hz h1
  | @nest W m y χ₁ ψ₀ e h' ih =>
      intro aW haW
      cases hk₁ : χ₁.kind with
      | own =>
          cases χ₁ with
          | own => exact absurd h' CellAt.not_empty
          | imm => cases hk₁
          | «mut» => cases hk₁
      | imm =>
          obtain ⟨ev, av, p, z, hev, hav, hp, hz⟩ := AgWT.imm_wit_le haW e hk₁
          obtain ⟨ζ, hζ⟩ := ih hk hx hav
          obtain ⟨_, h1⟩ := comp_some_r hp hζ; exact comp_some hz h1
      | «mut» =>
          obtain ⟨av, z, hav, hz⟩ := AgWT.mut_wit_le haW e hk₁
          obtain ⟨ζ, hζ⟩ := ih hk hx hav
          exact comp_some hz hζ

/-- The record's view at depth, over its escrow: an `imm` cell (a `mut` one would be refused by
`NoMutT`, an `own` one has no witness). -/
theorem le_view_cellAt {Θ : CodeTy} {tc : TChoice K} {W : TRes K}
    {ps rs : List (FrameRecT K)} (hT : TWNT K Θ tc W ps rs) {p : FrameRecT K} (hp : p ∈ ps)
    {x : BoCa.Loc} {χ : TCell K} (hx : CellAt p.R x χ) {aW : TRes K} (haW : AgWT W aW) :
    ∃ ζ, aW.get x = some ζ := by
  have hTI := hT.inv
  obtain ⟨ψ, eψ, kψ, -, wψ⟩ := hTI.2.1 p hp aW haW
  obtain ⟨ψ₀, c₀, w₀⟩ := agW_cellAt haW _ ψ eψ (by rw [kψ]; simp)
  have hx' : CellAt ψ₀.wit x χ := by rw [w₀, wψ]; exact hx
  cases hk : ψ₀.kind with
  | imm => exact cellAt_beneath_imm_ag c₀ hk hx' haW
  | «mut» => exact absurd (c₀.mutAt hk) (hTI.2.2.2.2.2.1.1 p hp)
  | own =>
      cases ψ₀ with
      | own => exact absurd hx' CellAt.not_empty
      | imm => cases hk
      | «mut» => cases hk

/-! ### The frame condition at the escrow -/

/-- **The case `fd_esc_of_branch` reads as a hypothesis**: a cell of `ρ_rest`'s aliasable walk
beneath a borrow of `ρ_rest`, at a top location of `p`'s lineage that holds `mut`, or an `own`
cell where the lineage holds `own`. Derived in `World/EscBeneath.lean` (`escBeneathT`), through
the innermost view above the cell (`Coverage`, `DeepInv`) to `p`'s lineage. -/
def EscBeneathT : Prop :=
  ∀ (K : WCactus) (Θ : CodeTy) (tc : TChoice K) (W ρo ρrest : TRes K)
    (ps rs : List (FrameRecT K)) (p : FrameRecT K) (α n : Life),
    TWNT K Θ tc W ps rs → p ∈ ps → ResUT.CompS ρo ρrest W → FrameLifeT K W p α →
    OnBranchResT K n ρrest → ¬ K.le n α →
    ∀ d, DescRT p d → ∀ x (ζ : TCell K), d.R.get x = some ζ → ζ.kind ≠ Kind.imm →
    ∀ ar, AgWT ρrest ar → ∀ χ : TCell K, ar.get x = some χ → χ.kind ≠ Kind.imm →
    (ζ.kind = Kind.own → χ.kind = Kind.own) → False

/-- **The frame condition at the escrow's exclusive locations, from a branch point**, but for
`EscBeneathT`'s case: a cell of the exclusive walk meets `ag(W)` beneath the record's view; a view
carries a lifetime of the branch while `ag(W)`'s view at a lineage location is inside `α`
(`FrameLifeT`); a `mut` cell where the lineage holds `own` is refused by `NoMutT`. -/
theorem fd_esc_of_branch (hB : EscBeneathT) {Θ : CodeTy} {tc : TChoice K}
    {W ρo ρrest : TRes K} {ps rs : List (FrameRecT K)} {p : FrameRecT K} {α n : Life}
    (hT : TWNT K Θ tc W ps rs) (hp : p ∈ ps) (hW : ResUT.CompS ρo ρrest W)
    (hFL : FrameLifeT K W p α) (hbr : OnBranchResT K n ρrest) (hnα : ¬ K.le n α)
    {τ : TRes K} (hτ : ResUT.Flat ρrest τ) {eR : TRes K} (heR : ExST p.R eR) {x : BoCa.Loc}
    (hx : (eR.get x).isSome) : τ.get x = none := by
  have hTI := hT.inv
  have hv := hT.valid
  have hprs : p ∈ rs := (hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hp, [], .nil p⟩
  obtain ⟨ψx, eψx⟩ := Option.isSome_iff_exists.mp hx
  obtain ⟨d, ⟨pd, hpd⟩, ζ, eζ, kζ⟩ := exST_lineage Θ heR p rfl (hTI.1.2.2.2.1 p hprs) x ψx eψx
  have hdrs : d ∈ rs := (hTI.2.2.2.2.2.2.1 d).mpr ⟨p, hp, pd, hpd⟩
  have hlin : LinLocT p x := ⟨d, ⟨pd, hpd⟩, ζ, eζ, kζ⟩
  have hxR : CellAt p.R x ζ := hpd.cellAt (fun y φ e => .top e) x ζ eζ
  obtain ⟨aW, haW⟩ := agW_of_valid hv
  obtain ⟨ζW, eζW⟩ := le_view_cellAt hT hp hxR haW
  cases hg : τ.get x with
  | none => rfl
  | some χ =>
  exfalso
  have hτn := flat_onBranch hbr hτ x χ hg
  obtain ⟨er, ar, her, har, hcr⟩ := hτ
  obtain ⟨a₁, a₂, ha₁, ha₂, hcW⟩ := (AgWT.split hW).mp haW
  obtain rfl := AgWT.functional ha₂ har
  rcases ResUT.Comp.get hcr x with ⟨-, -, f⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, -, f₂, f⟩ |
      ⟨ψ₁, ψ₂, ψ, f₁, -, f, hC⟩
  · rw [hg] at f; cases f
  · rw [hg] at f; cases Option.some.inj f
    have hk : χ.kind ≠ Kind.imm := ExST.immFree her _ _ f₁
    obtain ⟨eW, heW⟩ : ∃ eW, ExST W eW := by
      obtain ⟨σ, eW, aW', heW, -, -⟩ := hv; exact ⟨eW, heW⟩
    obtain ⟨e₁, e₂, -, he₂, hc₁⟩ := (ExST.split hW).mp heW
    obtain rfl := ExST.functional he₂ her
    exact ex_ag_disjoint hv heW haW (ResUT.CompS.get_right_of_ne_imm hc₁ f₁ hk).2 eζW
  · rw [hg] at f; cases Option.some.inj f
    cases hk : χ.kind with
    | imm =>
        obtain ⟨χW, eχW, kχW, -, -⟩ := ResUT.CompR.get_imm_left (ResUT.CompR.comm hcW) f₂ hk
        obtain ⟨s, hs, hη⟩ := CellUT.imm_eta hk
        obtain ⟨t, ht, hηW⟩ := CellUT.imm_eta kχW
        rw [hη] at f₂
        rw [hηW] at eχW
        obtain ⟨y, hy⟩ := s.ne
        have hyW : y ∈ t.set := ResUT.CompR.get_ls_imm (ResUT.CompR.comm hcW) f₂ eχW hy
        have hyα := hFL.2 aW haW x hlin _ t eχW (CellUT.lsOfI_immOf _ _ _ _) y hyW
        have hny := hτn s (by rw [hη]; exact CellUT.lsOf_immOf _ _ _ _) y hy
        exact hnα (K.trans hny hyα)
    | «mut» =>
        cases hkζ : ζ.kind with
        | own =>
            obtain ⟨m, χ', hm, hχ', ψ₀, c₀, k₀, -⟩ :=
              agW_nonimm_beneath har _ χ f₂ (by rw [hk]; simp)
            obtain ⟨χ'', e'', k'', c''⟩ := beneath_of_compS_right hW hm hχ' c₀
            have hζo : ζ = CellUT.ownOf ζ.erase := by
              cases ζ with
              | own => rfl
              | imm => cases hkζ
              | «mut» => cases hkζ
            rw [hζo] at eζ
            exact hTI.2.2.2.2.2.1.2 d hdrs x _ eζ (.nest e'' k'' (c''.mutAt (k₀.trans hk)))
        | imm => exact kζ hkζ
        | «mut» =>
            exact hB K Θ tc W ρo ρrest ps rs p α n hT hp hW hFL hbr hnα d ⟨pd, hpd⟩ x ζ eζ kζ
              _ ha₂ χ f₂ (by rw [hk]; simp) (fun h => by rw [hkζ] at h; cases h)
    | own =>
        exact hB K Θ tc W ρo ρrest ps rs p α n hT hp hW hFL hbr hnα d ⟨pd, hpd⟩ x ζ eζ kζ
          _ ha₂ χ f₂ (by rw [hk]; simp) (fun _ => hk)
  · rw [hg] at f; cases Option.some.inj f
    obtain ⟨_, _, _, _, _, _, _, h₁, _, _⟩ := hC
    exact ExST.immFree her _ _ f₁ (by rw [h₁]; exact CellUT.kind_immOf _ _ _ _)

/-! ### At a join -/

/-- **A composite of valid resources holding nothing at `P` holds nothing there.** -/
theorem NoneAt.compS {P : BoCa.Loc → Prop} {a b c : TRes K} (hc : ResUT.CompS a b c)
    (hva : ResUT.Valid a) (hvb : ResUT.Valid b) (ha : NoneAt P a) (hb : NoneAt P b) :
    NoneAt P c := by
  intro τ hτ x hx
  cases hg : τ.get x with
  | none => rfl
  | some χ =>
  exfalso
  obtain ⟨e₁, e₂, e, a₁, a₂, a', he₁, he₂, he, ha₁, ha₂, ha', hσ⟩ := (ResUT.Flat.split hc).mp hτ
  obtain ⟨τa, ea, aa, hea, haa, hca⟩ := hva
  obtain ⟨τb, eb, ab, heb, hab, hcb⟩ := hvb
  obtain rfl := ExST.functional hea he₁
  obtain rfl := AgWT.functional haa ha₁
  obtain rfl := ExST.functional heb he₂
  obtain rfl := AgWT.functional hab ha₂
  have hA : ∀ ψ, τa.get x = some ψ → False := fun ψ h => by
    rw [ha τa ⟨ea, aa, hea, haa, hca⟩ x hx] at h; cases h
  have hB : ∀ ψ, τb.get x = some ψ → False := fun ψ h => by
    rw [hb τb ⟨eb, ab, heb, hab, hcb⟩ x hx] at h; cases h
  rcases back_some hσ hg with ⟨ψ, hψ⟩ | ⟨ψ, hψ⟩
  · rcases back_some he hψ with ⟨ψ', h'⟩ | ⟨ψ', h'⟩
    · obtain ⟨_, h''⟩ := comp_some hca h'; exact hA _ h''
    · obtain ⟨_, h''⟩ := comp_some hcb h'; exact hB _ h''
  · rcases back_some ha' hψ with ⟨ψ', h'⟩ | ⟨ψ', h'⟩
    · obtain ⟨_, h''⟩ := comp_some_r hca h'; exact hA _ h''
    · obtain ⟨_, h''⟩ := comp_some_r hcb h'; exact hB _ h''

theorem fdEsc_iff_noneAt {l : BoCa.Loc} {R Y : TRes K} : FdEsc l R Y ↔ NoneAt (escLocs l R) Y := by
  refine ⟨fun h τ hτ x hx => ?_, fun h τ hτ => ⟨h τ hτ l (Or.inl rfl),
    fun eR heR x hx => h τ hτ x (Or.inr ⟨eR, heR, hx⟩)⟩⟩
  rcases hx with rfl | ⟨eR, heR, hx⟩
  · exact (h τ hτ).1
  · exact (h τ hτ).2 eR heR x hx

theorem noneAt_empty (P : BoCa.Loc → Prop) : NoneAt P (PMap.empty : TRes K) := by
  intro τ hτ x _
  obtain ⟨e, a, he, ha, hc⟩ := hτ
  obtain rfl := ExST.functional he exW_empty
  obtain rfl := AgWT.functional ha agW_empty
  rw [ResUT.CompS.functional hc (ResUT.compS_empty_right _)]; rfl

end BoCa.Fig16.Tree.Wp

end

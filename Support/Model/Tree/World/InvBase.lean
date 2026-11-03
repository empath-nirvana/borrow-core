import Support.Model.Tree.World.InvSimple
import Support.Model.Tree.World.ShapeT

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K : WCactus}

theorem CellUT.CompR.lsOf_inv {ψ₁ ψ₂ ψ : TCell K} (h : CellUT.CompR ψ₁ ψ₂ ψ)
    {s : TSet} (hs : ψ.lsOfI = some s) {x : Life} (hx : x ∈ s.set) :
    (∃ t, ψ₁.lsOfI = some t ∧ x ∈ t.set) ∨ (∃ t, ψ₂.lsOfI = some t ∧ x ∈ t.set) := by
  rw [compR_lsOfI_eq h] at hs
  cases e₁ : ψ₁.lsOfI with
  | none =>
      rw [e₁] at hs; exact Or.inr ⟨s, hs, hx⟩
  | some t₁ =>
      cases e₂ : ψ₂.lsOfI with
      | none => rw [e₁, e₂] at hs; cases Option.some.inj hs; exact Or.inl ⟨_, rfl, hx⟩
      | some t₂ =>
          rw [e₁, e₂] at hs; cases Option.some.inj hs
          rcases Finset.mem_union.mp hx with h | h
          · exact Or.inl ⟨_, rfl, h⟩
          · exact Or.inr ⟨_, rfl, h⟩

theorem ResUT.CompR.lsOf_inv {ρ₁ ρ₂ ρ : ResUT BoCa.Loc BoCa.Val K} (h : ResUT.CompR ρ₁ ρ₂ ρ)
    {l : BoCa.Loc} {ζ : TCell K} (hg : ρ.get l = some ζ) {s : TSet}
    (hs : ζ.lsOfI = some s) {x : Life} (hx : x ∈ s.set) :
    (∃ ξ t, ρ₁.get l = some ξ ∧ ξ.lsOfI = some t ∧ x ∈ t.set) ∨
    (∃ ξ t, ρ₂.get l = some ξ ∧ ξ.lsOfI = some t ∧ x ∈ t.set) := by
  rcases h.get l with ⟨-, -, e⟩ | ⟨ξ, e₁, -, e⟩ | ⟨ξ, -, e₂, e⟩ |
      ⟨ξ₁, ξ₂, ξ, e₁, e₂, e, hC⟩
  · rw [e] at hg; exact absurd hg (by simp)
  · rw [show ζ = ξ from Option.some.inj (hg.symm.trans e)] at hs
    exact Or.inl ⟨ξ, s, e₁, hs, hx⟩
  · rw [show ζ = ξ from Option.some.inj (hg.symm.trans e)] at hs
    exact Or.inr ⟨ξ, s, e₂, hs, hx⟩
  · rw [show ζ = ξ from Option.some.inj (hg.symm.trans e)] at hs
    rcases CellUT.CompR.lsOf_inv hC hs hx with ⟨t, ht, hxt⟩ | ⟨t, ht, hxt⟩
    · exact Or.inl ⟨ξ₁, t, e₁, ht, hxt⟩
    · exact Or.inr ⟨ξ₂, t, e₂, ht, hxt⟩

theorem CellUT.kind_of_lsOf {ζ : TCell K} {t : TSet} (h : ζ.lsOfI = some t) :
    ζ.kind = Kind.imm := by
  cases ζ with
  | own v => simp [CellUT.lsOfI] at h
  | imm i => rfl
  | «mut» m => simp [CellUT.lsOfI] at h

theorem imm_back_full {a₁ a₂ a : TRes K} (h : ResUT.CompR a₁ a₂ a) {l : BoCa.Loc}
    {ψ : TCell K} (e : a.get l = some ψ) (hk : ψ.kind = Kind.imm) :
    (∃ ψ₁, a₁.get l = some ψ₁ ∧ ψ₁.kind = Kind.imm ∧ ψ₁.erase = ψ.erase ∧ ψ₁.wit = ψ.wit) ∨
    (∃ ψ₂, a₂.get l = some ψ₂ ∧ ψ₂.kind = Kind.imm ∧ ψ₂.erase = ψ.erase ∧ ψ₂.wit = ψ.wit) := by
  rcases ResUT.Comp.get h l with ⟨-, -, e'⟩ | ⟨ζ, e₁, -, e'⟩ | ⟨ζ, -, e₂, e'⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁, e₂, e', hC⟩
  · rw [e'] at e; cases e
  · rw [e'] at e; cases e; exact Or.inl ⟨_, e₁, hk, rfl, rfl⟩
  · rw [e'] at e; cases e; exact Or.inr ⟨_, e₂, hk, rfl, rfl⟩
  · rw [e'] at e; cases Option.some.inj e
    obtain ⟨s, hs, hψ⟩ := CellUT.imm_eta hk
    rcases CellUT.CompR.imm_source hC hψ with ⟨s₁, h₁, e₁'⟩ | ⟨s₂, h₂, e₂'⟩
    · exact Or.inl ⟨_, e₁, by rw [e₁']; rfl, by rw [e₁']; simp, by rw [e₁']; simp⟩
    · exact Or.inr ⟨_, e₂, by rw [e₂']; rfl, by rw [e₂']; simp, by rw [e₂']; simp⟩

theorem imm_fwd_full_l {a₁ a₂ a : TRes K} (h : ResUT.CompR a₁ a₂ a) {l : BoCa.Loc}
    {ψ₁ : TCell K} (e : a₁.get l = some ψ₁) (hk : ψ₁.kind = Kind.imm) :
    ∃ ψ, a.get l = some ψ ∧ ψ.kind = Kind.imm ∧ ψ.erase = ψ₁.erase ∧ ψ.wit = ψ₁.wit :=
  ResUT.CompR.get_imm_left h e hk

theorem imm_fwd_full_r {a₁ a₂ a : TRes K} (h : ResUT.CompR a₁ a₂ a) {l : BoCa.Loc}
    {ψ₂ : TCell K} (e : a₂.get l = some ψ₂) (hk : ψ₂.kind = Kind.imm) :
    ∃ ψ, a.get l = some ψ ∧ ψ.kind = Kind.imm ∧ ψ.erase = ψ₂.erase ∧ ψ.wit = ψ₂.wit :=
  ResUT.CompR.get_imm_right h e hk

theorem frame_fwd_imm {W X Z R W' a' : TRes K} {l : BoCa.Loc} {v : BoCa.Val} {α : Life}
    {h : R.InStratum (TSet.single α)}
    (hX : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) R X) (hW : ResUT.CompS X Z W)
    (hW' : ResUT.CompS (ResUT.single l (CellUT.immOf (TSet.single α) v R h)) Z W')
    (hv : ResUT.Valid W) (ha' : AgWT W' a') {aW : TRes K} (haW : AgWT W aW) {m : BoCa.Loc}
    {ψ₀ : TCell K} (e₀ : aW.get m = some ψ₀) (k₀ : ψ₀.kind = Kind.imm) :
    ∃ ψ, a'.get m = some ψ ∧ ψ.kind = Kind.imm ∧ ψ.erase = ψ₀.erase ∧ ψ.wit = ψ₀.wit := by
  obtain ⟨eW, aW', r, z, eR, σc, pc, -, haW', -, hrz, -, -, -, hpc, hcp, hcz⟩ :=
    frame_walks hX hW hW' hv ha'
  rw [AgWT.functional haW' haW] at hrz
  rcases imm_back_full hrz e₀ k₀ with ⟨ψ₁, e₁, k₁, r₁, w₁⟩ | ⟨ψ₁, e₁, k₁, r₁, w₁⟩
  · obtain ⟨ψ₂, e₂, k₂, r₂, w₂⟩ := imm_fwd_full_r hpc e₁ k₁
    obtain ⟨ψ₃, e₃, k₃, r₃, w₃⟩ := imm_fwd_full_r hcp e₂ k₂
    obtain ⟨ψ, e, k, r', w⟩ := imm_fwd_full_l hcz e₃ k₃
    exact ⟨ψ, e, k, r'.trans (r₃.trans (r₂.trans r₁)), w.trans (w₃.trans (w₂.trans w₁))⟩
  · obtain ⟨ψ, e, k, r', w⟩ := imm_fwd_full_r hcz e₁ k₁
    exact ⟨ψ, e, k, r'.trans r₁, w.trans w₁⟩

/-- Each record's cell is an `imm` view of `ag(W)` over the recorded value and escrow. -/
theorem lsOf_eta {ψ : TCell K} {s : TSet} (h : ψ.lsOfI = some s) :
    ∃ (v : BoCa.Val) (χ : TRes K) (hs : χ.InStratum s), ψ = CellUT.immOf s v χ hs := by
  obtain ⟨s', hs', he⟩ := CellUT.imm_eta (CellUT.kind_of_lsOf h)
  have h' : CellUT.lsOfI (CellUT.immOf s' ψ.erase ψ.wit hs') = some s := he ▸ h
  rw [CellUT.lsOfI_immOf] at h'
  cases Option.some.inj h'
  exact ⟨_, _, hs', he⟩

theorem lsOf_of_imm {ψ : TCell K} (h : ψ.kind = Kind.imm) : ∃ s, ψ.lsOfI = some s := by
  obtain ⟨s, hs, e⟩ := CellUT.imm_eta h
  exact ⟨s, by rw [e, CellUT.lsOfI_immOf]⟩

/-- `ψ`, if `imm`, has an `imm` counterpart at `x` in `a` over the same value and witness
whose lifetime set contains `ψ`'s. -/
def ICp (a : TRes K) (x : BoCa.Loc) (ψ : TCell K) : Prop :=
  ψ.kind = Kind.imm → ∃ ζ : TCell K, a.get x = some ζ ∧ ζ.kind = Kind.imm ∧
    ζ.erase = ψ.erase ∧ ζ.wit = ψ.wit ∧
    ∀ s t, ψ.lsOfI = some s → ζ.lsOfI = some t → ∀ y, y ∈ s.set → y ∈ t.set

/-- Every cell of `ρ` at `x` has an `imm` counterpart in `a`. -/
def ICpAt (a ρ : TRes K) (x : BoCa.Loc) : Prop := ∀ ψ, ρ.get x = some ψ → ICp a x ψ

def AllICp (a ρ : TRes K) : Prop := ∀ x, ICpAt a ρ x

theorem ICp.ls {a : TRes K} {x : BoCa.Loc} {ψ : TCell K} (h : ICp a x ψ) {s : TSet}
    (hs : ψ.lsOfI = some s) {y : Life} (hy : y ∈ s.set) :
    ∃ ζ t, a.get x = some ζ ∧ ζ.lsOfI = some t ∧ y ∈ t.set := by
  obtain ⟨ζ, eζ, kζ, -, -, lζ⟩ := h (CellUT.kind_of_lsOf hs)
  obtain ⟨t, ht⟩ := lsOf_of_imm kζ
  exact ⟨ζ, t, eζ, ht, lζ s t hs ht y hy⟩

theorem icpAt_left {a₁ a₂ a : TRes K} (h : ResUT.CompR a₁ a₂ a) (x : BoCa.Loc) : ICpAt a a₁ x := by
  intro ψ e hk
  obtain ⟨χ, eχ, kχ, rχ, wχ⟩ := ResUT.CompR.get_imm_left h e hk
  refine ⟨χ, eχ, kχ, rχ, wχ, fun s t hs ht y hy => ?_⟩
  obtain ⟨v₁, χ₁, h₁, hψ⟩ := lsOf_eta hs
  obtain ⟨v₂, χ₂, h₂, hχ⟩ := lsOf_eta ht
  rw [hψ] at e; rw [hχ] at eχ
  exact ResUT.CompR.get_ls_imm h e eχ hy

theorem icpAt_right {a₁ a₂ a : TRes K} (h : ResUT.CompR a₁ a₂ a) (x : BoCa.Loc) : ICpAt a a₂ x :=
  icpAt_left (ResUT.CompR.comm h) x

theorem icp_trans {a b : TRes K} {x : BoCa.Loc} {ψ : TCell K} (h₁ : ICp b x ψ)
    (h₂ : ICpAt a b x) : ICp a x ψ := by
  intro hk
  obtain ⟨ζ, eζ, kζ, rζ, wζ, lζ⟩ := h₁ hk
  obtain ⟨ξ, eξ, kξ, rξ, wξ, lξ⟩ := h₂ ζ eζ kζ
  refine ⟨ξ, eξ, kξ, rξ.trans rζ, wξ.trans wζ, fun s t hs ht y hy => ?_⟩
  obtain ⟨u, hu⟩ := lsOf_of_imm kζ
  exact lξ u t hu ht y (lζ s u hs hu y hy)

theorem icpAt_trans {a b ρ : TRes K} {x : BoCa.Loc} (h₁ : ICpAt b ρ x) (h₂ : ICpAt a b x) :
    ICpAt a ρ x := fun ψ e => icp_trans (h₁ ψ e) h₂

theorem icpAt_comp {b ρ₁ ρ₂ ρ : TRes K} (h : ResUT.CompR ρ₁ ρ₂ ρ) {x : BoCa.Loc}
    (h₁ : ICpAt b ρ₁ x) (h₂ : ICpAt b ρ₂ x) : ICpAt b ρ x := by
  intro ψ e hk
  obtain ⟨s, hs, hψ⟩ := CellUT.imm_eta hk
  have e' := e
  rw [hψ] at e'
  have src : ∃ ζ, b.get x = some ζ ∧ ζ.kind = Kind.imm ∧ ζ.erase = ψ.erase ∧
      ζ.wit = ψ.wit := by
    rcases ResUT.CompR.imm_source h e' with ⟨s₁, k₁, e₁⟩ | ⟨s₂, k₂, e₂⟩
    · obtain ⟨ζ, eζ, kζ, rζ, wζ, -⟩ := h₁ _ e₁ (CellUT.kind_immOf _ _ _ _)
      exact ⟨ζ, eζ, kζ, by rw [rζ]; simp, by rw [wζ]; simp⟩
    · obtain ⟨ζ, eζ, kζ, rζ, wζ, -⟩ := h₂ _ e₂ (CellUT.kind_immOf _ _ _ _)
      exact ⟨ζ, eζ, kζ, by rw [rζ]; simp, by rw [wζ]; simp⟩
  obtain ⟨ζ, eζ, kζ, rζ, wζ⟩ := src
  refine ⟨ζ, eζ, kζ, rζ, wζ, fun s' t hs' ht y hy => ?_⟩
  rcases ResUT.CompR.lsOf_inv h e hs' hy with ⟨ξ, t₁, e₁, ht₁, hy₁⟩ | ⟨ξ, t₁, e₁, ht₁, hy₁⟩
  · obtain ⟨ζ', t', eζ', ht', hy'⟩ := (h₁ ξ e₁).ls ht₁ hy₁
    rw [eζ] at eζ'; cases Option.some.inj eζ'
    rw [ht] at ht'; cases Option.some.inj ht'; exact hy'
  · obtain ⟨ζ', t', eζ', ht', hy'⟩ := (h₂ ξ e₁).ls ht₁ hy₁
    rw [eζ] at eζ'; cases Option.some.inj eζ'
    rw [ht] at ht'; cases Option.some.inj ht'; exact hy'

theorem icpAt_bigComp {b : TRes K} {x : BoCa.Loc} :
    ∀ {L : List (TRes K)} {c : TRes K}, BigCompT CellUT.CompatR CellUT.CompR L c →
      (∀ σ ∈ L, ICpAt b σ x) → ICpAt b c x
  | [], c, h, _ => by
      cases h
      intro ψ e; rw [PMap.empty_get] at e; cases e
  | σ :: L, c, h, hL => by
      cases h with
      | cons hrest hc =>
          exact icpAt_comp hc (hL σ List.mem_cons_self)
            (icpAt_bigComp hrest (fun τ hτ => hL τ (List.mem_cons_of_mem _ hτ)))

theorem icpAt_of_immFree {b ρ : TRes K} (h : ρ.ImmFree) (x : BoCa.Loc) : ICpAt b ρ x :=
  fun ψ e hk => absurd hk (h x ψ e)

theorem icpAt_none {b ρ : TRes K} {x : BoCa.Loc} (h : ρ.get x = none) : ICpAt b ρ x := by
  intro ψ e; rw [h] at e; cases e

/-- `ag(ρ)` keeps every `imm` cell of `ρ` over its value and witness, and never drops a
lifetime (`AgWT.get_imm`, `AgWT.get_ls_imm`). -/
theorem icpAt_agW {ρ σ : TRes K} (h : AgWT ρ σ) (x : BoCa.Loc) : ICpAt σ ρ x := by
  intro ψ e hk
  obtain ⟨χ, eχ, kχ, rχ, wχ⟩ := AgWT.get_imm h e hk
  refine ⟨χ, eχ, kχ, rχ, wχ, fun s t hs ht y hy => ?_⟩
  obtain ⟨v₁, χ₁, h₁, hψ⟩ := lsOf_eta hs
  obtain ⟨v₂, χ₂, h₂, hχ⟩ := lsOf_eta ht
  rw [hψ] at e; rw [hχ] at eχ
  exact AgWT.get_ls_imm h e eχ hy
theorem compR_mut_src : ∀ ψ₁ ψ₂ ψ : TCell K, CellUT.CompR ψ₁ ψ₂ ψ →
    ψ.kind = Kind.mut → ψ₁.kind = Kind.mut ∨ ψ₂.kind = Kind.mut := by
  intro ψ₁ ψ₂ ψ h hk
  cases h with
  | same => exact Or.inl hk
  | strict k =>
      rw [CellUT.CompS.kind (CellUT.compS_spec _ _ k)] at hk; cases hk
  | mutMut => exact Or.inl (by simp)
  | mutOwn => exact Or.inl (by simp)
  | ownMut => exact Or.inr (by simp)
  | immOwn => simp at hk
  | ownImm => simp at hk
  | immMut => simp at hk
  | mutImm => simp at hk

theorem comp_mut_src {R : TCell K → TCell K → Prop}
    {C : TCell K → TCell K → TCell K → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ.kind = Kind.mut → ψ₁.kind = Kind.mut ∨ ψ₂.kind = Kind.mut)
    {a b c : TRes K} (h : ResUT.Comp R C a b c) {x : BoCa.Loc} {ψ : TCell K}
    (e : c.get x = some ψ) (hk : ψ.kind = Kind.mut) :
    (∃ ψ₁ : TCell K, a.get x = some ψ₁ ∧ ψ₁.kind = Kind.mut) ∨
    (∃ ψ₂ : TCell K, b.get x = some ψ₂ ∧ ψ₂.kind = Kind.mut) := by
  rcases ResUT.Comp.get h x with ⟨-, -, e'⟩ | ⟨χ, e₁, -, e'⟩ | ⟨χ, -, e₂, e'⟩ |
      ⟨χ₁, χ₂, χ, e₁, e₂, e', hCc⟩
  · rw [e'] at e; cases e
  · rw [e'] at e; cases e; exact Or.inl ⟨_, e₁, hk⟩
  · rw [e'] at e; cases e; exact Or.inr ⟨_, e₂, hk⟩
  · rw [e'] at e; cases e
    rcases hC _ _ _ hCc hk with k | k
    · exact Or.inl ⟨_, e₁, k⟩
    · exact Or.inr ⟨_, e₂, k⟩

theorem bigComp_mut_src {R : TCell K → TCell K → Prop}
    {C : TCell K → TCell K → TCell K → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ.kind = Kind.mut → ψ₁.kind = Kind.mut ∨ ψ₂.kind = Kind.mut) :
    ∀ {L : List (TRes K)} {b : TRes K}, BigCompT R C L b → ∀ {x : BoCa.Loc} {ψ : TCell K},
      b.get x = some ψ → ψ.kind = Kind.mut →
      ∃ σ ∈ L, ∃ ψ' : TCell K, σ.get x = some ψ' ∧ ψ'.kind = Kind.mut
  | [], b, h, x, ψ, e, _ => by cases h; rw [PMap.empty_get] at e; cases e
  | σ :: L, b, h, x, ψ, e, hk => by
      cases h with
      | cons hrest hc =>
          rcases comp_mut_src hC hc e hk with ⟨ψ₁, e₁, k₁⟩ | ⟨ψ₂, e₂, k₂⟩
          · exact ⟨σ, List.mem_cons_self, ψ₁, e₁, k₁⟩
          · obtain ⟨τ, hτ, ψ', e', k'⟩ := bigComp_mut_src hC hrest e₂ k₂
            exact ⟨τ, List.mem_cons_of_mem _ hτ, ψ', e', k'⟩

/-- `ex(ρ)` raises a `mut` cell only from one in `ρ`. -/
theorem exW_mut {R : TCell K → TCell K → Prop}
    {C : TCell K → TCell K → TCell K → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ.kind = Kind.mut → ψ₁.kind = Kind.mut ∨ ψ₂.kind = Kind.mut)
    {ρ σ : TRes K} (h : ExWT R C ρ σ) :
    ∀ x (ψ : TCell K), σ.get x = some ψ → ψ.kind = Kind.mut → MutAtT ρ x := by
  refine G.ExW.rec (motive_1 := fun ρ σ _ => ∀ x (ψ : TCell K), σ.get x = some ψ →
      ψ.kind = Kind.mut → MutAtT ρ x)
    (motive_2 := fun ρ w _ => ∀ p ∈ w, ∀ x (ψ : TCell K), p.2.get x = some ψ →
      ψ.kind = Kind.mut → MutAtT ρ x) ?mk ?nil ?cons h
  case mk =>
    intro ρ' σ' nm b w hs hw hb hnm hσ ih x ψ e hk
    rcases comp_mut_src hC hσ e hk with ⟨ψ₁, e₁, k₁⟩ | ⟨ψ₂, e₂, k₂⟩
    · rcases comp_mut_src hC hnm e₁ k₁ with ⟨ψ₃, e₃, k₃⟩ | ⟨ψ₃, e₃, k₃⟩
      · have := (ResUT.restrict_eq_some.mp e₃).2; rw [k₃] at this; cases this
      · exact MutAtT.top (ResUT.restrict_eq_some.mp e₃).1 k₃
    · obtain ⟨τ, hτ, ψ', e', k'⟩ := bigComp_mut_src hC hb e₂ k₂
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hτ
      exact ih p hp x ψ' e' k'
  case nil => intro ρ' p hp; exact absurd hp (by simp)
  case cons =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw p hp x ψ' e' k'
    rcases List.mem_cons.mp hp with rfl | hp
    · exact MutAtT.nest hψ (by rw [hk]; simp) (ihe x ψ' e' k')
    · exact ihw p hp x ψ' e' k'

/-- `ag(ρ)` raises a `mut` cell only from one in `ρ`. -/
theorem agW_mut {ρ σ : TRes K} (h : AgWT ρ σ) :
    ∀ x (ψ : TCell K), σ.get x = some ψ → ψ.kind = Kind.mut → MutAtT ρ x := by
  refine G.AgW.rec (motive_1 := fun ρ σ _ => ∀ x (ψ : TCell K), σ.get x = some ψ →
      ψ.kind = Kind.mut → MutAtT ρ x)
    (motive_2 := fun ρ w _ => ∀ p ∈ w, ∀ x (ψ : TCell K), p.2.get x = some ψ →
      ψ.kind = Kind.mut → MutAtT ρ x)
    (motive_3 := fun ρ w _ => ∀ p ∈ w, ∀ x (ψ : TCell K), p.2.get x = some ψ →
      ψ.kind = Kind.mut → MutAtT ρ x)
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ' σ' a bm bi wm wi hsm hsi hwm hwi hbm hbi ha hσ ihm ihi x ψ e hk
    rcases comp_mut_src compR_mut_src hσ e hk with ⟨ψ₁, e₁, k₁⟩ | ⟨ψ₂, e₂, k₂⟩
    · rcases comp_mut_src compR_mut_src ha e₁ k₁ with ⟨ψ₃, e₃, k₃⟩ | ⟨ψ₃, e₃, k₃⟩
      · have := (ResUT.restrict_eq_some.mp e₃).2; rw [k₃] at this; cases this
      · obtain ⟨τ, hτ, ψ', e', k'⟩ := bigComp_mut_src compR_mut_src hbm e₃ k₃
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hτ
        exact ihm p hp x ψ' e' k'
    · obtain ⟨τ, hτ, ψ', e', k'⟩ := bigComp_mut_src compR_mut_src hbi e₂ k₂
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hτ
      exact ihi p hp x ψ' e' k'
  case nilM => intro ρ' p hp; exact absurd hp (by simp)
  case consM =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw p hp x ψ' e' k'
    rcases List.mem_cons.mp hp with rfl | hp
    · exact MutAtT.nest hψ (by rw [hk]; simp) (ihe x ψ' e' k')
    · exact ihw p hp x ψ' e' k'
  case nilI => intro ρ' p hp; exact absurd hp (by simp)
  case consI =>
    intro ρ' q l w ψ hψ hk e a hex hag hc hw iha ihw p hp x ψ' e' k'
    rcases List.mem_cons.mp hp with rfl | hp
    · rcases comp_mut_src compR_mut_src hc e' k' with ⟨ψ₁, e₁, k₁⟩ | ⟨ψ₁, e₁, k₁⟩
      · exact MutAtT.nest hψ (by rw [hk]; simp) (exW_mut compR_mut_src hex x ψ₁ e₁ k₁)
      · exact MutAtT.nest hψ (by rw [hk]; simp) (iha x ψ₁ e₁ k₁)
    · exact ihw p hp x ψ' e' k'

/-- A `mut` cell at `ℓ` at any depth of `ρ` shows at `ℓ` in `ex(ρ)` or in `ag(ρ)`. -/
theorem mutAt_walk_dom {ρ : TRes K} {x : BoCa.Loc} (h : MutAtT ρ x) :
    ∀ {R : TCell K → TCell K → Prop}
      {C : TCell K → TCell K → TCell K → Prop},
      (∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) → ResUT.CompLaws C →
      ∀ {e a : TRes K}, ExWT R C ρ e → AgWT ρ a →
      (∃ ζ, e.get x = some ζ) ∨ (∃ ζ, a.get x = some ζ) := by
  induction h with
  | @top ρ l ψ e hk =>
      intro R C hR hC ex a hex ha
      cases hex with
      | mk hs hw hb hnm hσ =>
          obtain ⟨ζ₁, e₁⟩ := comp_some_r hnm (ResUT.restrict_get_some e hk)
          exact Or.inl (comp_some hσ e₁)
  | @nest ρ l m ψ e hk hmw ih =>
      intro R C hR hC ex a hex ha
      cases hkk : ψ.kind with
      | own => exact absurd hkk hk
      | imm =>
          obtain ⟨ev, av, p, z, hev, hav, hp, hz⟩ := AgWT.imm_wit_le ha e hkk
          rcases ih hRR ResUT.compLawsR hev hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
          · obtain ⟨_, h1⟩ := comp_some hp hζ; exact Or.inr (comp_some hz h1)
          · obtain ⟨_, h1⟩ := comp_some_r hp hζ; exact Or.inr (comp_some hz h1)
      | «mut» =>
          obtain ⟨ev, z, hev, hz⟩ := ExWT.wit_le hR hC hex e hkk
          obtain ⟨av, z', hav, hz'⟩ := AgWT.mut_wit_le ha e hkk
          rcases ih hR hC hev hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
          · exact Or.inl (comp_some hz hζ)
          · exact Or.inr (comp_some hz' hζ)

/-- A top-level `ℓ ↦ own(u)` of a valid resource is borrowed mutably nowhere in it.
`⦇W⦈ = ex(W)_● ● ag(W)`: a `mut` cell at `ℓ` under an `imm` cell lands in `ag(W)`, which is
disjoint from `ex(W)_●`'s `own(u)` (`ex_ag_disjoint`); under a `mut` cell it lands in
`ex(W)_●`'s `⨀`, which `●`s against `W|own`'s `own(u)`, and `●` joins `imm` cells only. -/
theorem not_mutAt_top_own {W : TRes K} (hv : ResUT.Valid W) {x : BoCa.Loc} {u : BoCa.Val}
    (hx : W.get x = some (CellUT.ownOf u)) : ¬ MutAtT W x := by
  intro hm
  obtain ⟨σ, eW, aW, heW, haW, hc⟩ := hv
  have eo : eW.get x = some (CellUT.ownOf u) := ExST.get_of_ne_imm heW hx (by simp)
  have noAg : ∀ ζ, aW.get x = some ζ → False := fun ζ hζ =>
    ex_ag_disjoint ⟨σ, eW, aW, heW, haW, hc⟩ heW haW eo hζ
  cases hm with
  | top e hk => rw [hx] at e; cases Option.some.inj e; exact absurd hk (by simp)
  | @nest _ _ m ψ e hk hmw =>
      cases hkk : ψ.kind with
      | own => exact hk hkk
      | imm =>
          obtain ⟨ev, av, p, z, hev, hav, hp, hz⟩ := AgWT.imm_wit_le haW e hkk
          rcases mutAt_walk_dom hmw hRR ResUT.compLawsR hev hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
          · obtain ⟨_, h1⟩ := comp_some hp hζ
            obtain ⟨_, h2⟩ := comp_some hz h1
            exact noAg _ h2
          · obtain ⟨_, h1⟩ := comp_some_r hp hζ
            obtain ⟨_, h2⟩ := comp_some hz h1
            exact noAg _ h2
      | «mut» =>
          obtain ⟨av, z, hav, hz⟩ := AgWT.mut_wit_le haW e hkk
          cases heW with
          | mk hs hw hb hnm hσ =>
              rename_i nm b w
              obtain ⟨q, hq, hq₁⟩ := List.mem_map.mp ((hs.2 m).mpr ⟨ψ, e, hkk⟩)
              obtain ⟨ψ', hψ', hex'⟩ := ExWitsT.mem hw q hq
              rw [hq₁, e] at hψ'
              cases Option.some.inj hψ'
              rcases mutAt_walk_dom hmw hSS ResUT.compLawsS hex' hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
              · obtain ⟨z', hz'⟩ :=
                  BigCompT.mem_factor hSS ResUT.compLawsS hb q.2 (List.mem_map.mpr ⟨q, hq, rfl⟩)
                obtain ⟨ζb, hζb⟩ := comp_some hz' hζ
                have hno : (G.restrict CellUT.kind W Kind.mut).get x = none := by
                  cases e' : (G.restrict CellUT.kind W Kind.mut).get x with
                  | none => rfl
                  | some χ =>
                      obtain ⟨e'', k''⟩ := ResUT.restrict_eq_some.mp e'
                      rw [hx] at e''; cases Option.some.inj e''; exact absurd k'' (by simp)
                have hnm' : nm.get x = some (CellUT.ownOf u) := by
                  have hown : (G.restrict CellUT.kind W Kind.own).get x = some (CellUT.ownOf u) :=
                    ResUT.restrict_get_some hx (by simp)
                  exact (ResUT.CompS.get_left_of_ne_imm hnm hown (by simp)).2
                have := ResUT.CompatS.right_eq_none hσ.1 hnm' (by simp)
                rw [hζb] at this; cases this
              · obtain ⟨_, h1⟩ := comp_some hz hζ
                exact noAg _ h1

/-- A cell of `c ∈ reb_β(σ)`, with its lifetimes (`[TR]` p. 5, `reb_α`'s three clauses):
over an `own` or `mut` cell of `σ` it is `imm({β}, …)`; over an `imm` cell `imm(s, v, χ)` it
is `imm(t, v, χ)` with `t ⊆ s`. -/
theorem reb_cell_ls {β : Life} {σ c : TRes K} (hr : ResUT.Reb β σ c) {m : BoCa.Loc}
    {ψ : TCell K} (e : c.get m = some ψ) :
    ((∃ ζ : TCell K, σ.get m = some ζ ∧ ζ.kind ≠ Kind.imm) ∧
        ψ.lsOfI = some (TSet.single β)) ∨
    (∃ ζ : TCell K, σ.get m = some ζ ∧ ζ.kind = Kind.imm ∧ ψ.erase = ζ.erase ∧
      ψ.wit = ζ.wit ∧ ∀ s t, ζ.lsOfI = some s → ψ.lsOfI = some t → ∀ y, y ∈ t.set → y ∈ s.set) := by
  obtain ⟨-, π, b, hdom, hbig, hle, hbody⟩ := hr
  obtain ⟨⟨l₀, q⟩, hpm, hpl⟩ := List.mem_map.mp ((hdom.2 m).mpr ⟨_, e⟩)
  simp only at hpl
  subst hpl
  have hq := hbody l₀ q hpm
  have hmem : q ∈ π.map Prod.snd := List.mem_map.mpr ⟨_, hpm, rfl⟩
  obtain ⟨b', hb', hle'⟩ := BigCompT.leS_of_sublist (List.singleton_sublist.mpr hmem) hbig
  rw [(BigCompT.singleton_iff ResUT.compLawsS).mp hb'] at hle'
  obtain ⟨ζq, hζq⟩ := hq.1
  obtain ⟨τ, hτ⟩ := hle'.trans hle
  obtain ⟨ζ, hζ⟩ := comp_some hτ hζq
  rcases CellUT.rep' ζ with ⟨u, rfl⟩ | ⟨s, v, χ, hs, rfl⟩ | ⟨b₀, _, v, χ, hb₀, P, hw, rfl⟩
  · obtain ⟨hh, he⟩ := hq.2.1 u hζ
    rw [e] at he; cases Option.some.inj he
    exact Or.inl ⟨⟨_, hζ, by simp⟩, CellUT.lsOfI_immOf _ _ _ _⟩
  · obtain ⟨⟨t, ht, hts, he⟩, -⟩ := hq.2.2.2 s v χ hs hζ
    rw [e] at he; cases Option.some.inj he
    refine Or.inr ⟨_, hζ, CellUT.kind_immOf _ _ _ _, by simp, by simp,
      fun s' t' hs' ht' y hy => ?_⟩
    rw [CellUT.lsOfI_immOf] at hs' ht'
    cases Option.some.inj hs'; cases Option.some.inj ht'
    exact hts hy
  · obtain ⟨⟨hh, he⟩, -⟩ := hq.2.2.1 b₀ v χ hb₀ P hw hζ
    rw [e] at he; cases Option.some.inj he
    exact Or.inl ⟨⟨_, hζ, by simp⟩, CellUT.lsOfI_immOf _ _ _ _⟩

/-- A reborrow image carries no `mut` cell its source does not: every cell of it is `imm`
over a witness that is a piece of the source (`own` clause) or a witness of the source's own
cell (`mut`, `imm` clauses). -/
theorem mutAt_image {β : Life} {w₀ c : TRes K} (hr : ResUT.Reb β w₀ c) {x : BoCa.Loc}
    (hm : MutAtT c x) : MutAtT w₀ x := by
  cases hm with
  | top e hk => rw [(reb_cell hr e).1] at hk; cases hk
  | @nest _ _ m ψ e hk hw =>
      obtain ⟨-, hcase⟩ := reb_cell hr e
      rcases hcase with ⟨u, q, h, hown, rfl, hqσ, ζq, hζq⟩ | ⟨ζ, eζ, kζ, wζ⟩ | ⟨ζ, eζ, kζ, wζ⟩
      · rw [CellUT.wit_immOf] at hw
        exact MutAtT.of_le hqσ (MutAtT.of_del hw)
      · exact MutAtT.nest eζ (by rw [kζ]; simp) (wζ ▸ hw)
      · exact MutAtT.nest eζ (by rw [kζ]; simp) (wζ ▸ hw)

/-- `W(ℓₑ) = imm(s, v, w₀)` makes every `mut` cell of `w₀` one of `W`. -/
theorem mutAt_of_cell {W w₀ : TRes K} {le : BoCa.Loc} {s : TSet} {v : BoCa.Val}
    {hs : w₀.InStratum s} (hle : W.get le = some (CellUT.immOf s v w₀ hs)) {x : BoCa.Loc}
    (hm : MutAtT w₀ x) : MutAtT W x :=
  MutAtT.nest hle (by simp) (by rw [CellUT.wit_immOf]; exact hm)

/-- `ag(ρ₀)` of an escrow sits in `ag(W)` — `W(ℓₑ) = imm(s, v, ρ₀)` contributes
`ex(ρ₀)_○ ○ ag(ρ₀)` to `ag(W)`. -/
theorem escrow_icp {W a₁ w₀ : TRes K} {le : BoCa.Loc} {s : TSet} {v : BoCa.Val}
    {hs : w₀.InStratum s} (ha₁ : AgWT W a₁)
    (hle : W.get le = some (CellUT.immOf s v w₀ hs)) :
    ∃ e₀ a₀, ExRT w₀ e₀ ∧ AgWT w₀ a₀ ∧ AllICp a₁ a₀ := by
  obtain ⟨a₁', a₂, -, h₂, h12⟩ := (AgWT.split (ResUT.del_compS hle)).mp ha₁
  obtain ⟨e₀, a₀, p₀, he₀, ha₀, hp₀, hcp₀⟩ := AgWT.single_imm_inv h₂
  exact ⟨e₀, a₀, he₀, ha₀, fun x =>
    icpAt_trans (icpAt_right hp₀ x) (icpAt_trans (icpAt_right hcp₀ x) (icpAt_right h12 x))⟩

/-- The walk of a part of a reborrow image, taken at `W(ℓₑ) = imm(s, v, w₀)`.  If every
cell of `d` is a cell of `c ∈ reb_β(w₀)`, then `ag(d) = d ○ b` where every `imm` cell of `b`
has an `imm` counterpart in `ag(W)`: `b` is `⨀` of `ex(χ)_○ ○ ag(χ)` over `d`'s witnesses
`χ`, each a piece of `w₀` or a witness of one of its cells (`[TR]` 6.54's *"every witness is
also in ⦇ρ⦈○"*). -/
theorem img_walk {W₁ a₁ w₀ c d ad : TRes K} {le : BoCa.Loc} {s : TSet} {v : BoCa.Val}
    {hs : w₀.InStratum s} {β : Life} (ha₁ : AgWT W₁ a₁)
    (hle : W₁.get le = some (CellUT.immOf s v w₀ hs)) (hr : ResUT.Reb β w₀ c)
    (hsub : ∀ x (ψ : TCell K), d.get x = some ψ → c.get x = some ψ) (had : AgWT d ad) :
    ∃ d' bi, ResUT.CompR d' bi ad ∧ AllICp a₁ bi ∧
      (∀ x (ψ : TCell K), d'.get x = some ψ → d.get x = some ψ) := by
  obtain ⟨e₀, a₀, he₀, ha₀, icp₀⟩ := escrow_icp ha₁ hle
  have hkind : ∀ x (ψ : TCell K), d.get x = some ψ → ψ.kind = Kind.imm :=
    fun x ψ e => (reb_cell hr (hsub x ψ e)).1
  -- the `ag` of each witness of `d` sits in `ag(w₀)`
  have witICp : ∀ x (ψ : TCell K), d.get x = some ψ → ∀ av, AgWT ψ.wit av →
      AllICp a₁ av := by
    intro x ψ e av hav
    obtain ⟨-, hcase⟩ := reb_cell hr (hsub x ψ e)
    rcases hcase with ⟨u, q, h, hown, rfl, hqσ, ζq, hζq⟩ | ⟨ζ, eζ, kζ, wζ⟩ | ⟨ζ, eζ, kζ, wζ⟩
    · rw [CellUT.wit_immOf] at hav
      obtain ⟨τ, hτ⟩ : ResUT.Le (q.del x) w₀ := ResUT.Le.trans ⟨_, ResUT.del_compS hζq⟩ hqσ
      obtain ⟨y₁, y₂, hy₁, -, hy⟩ := (AgWT.split hτ).mp ha₀
      rw [AgWT.functional hy₁ hav] at hy
      exact fun z => icpAt_trans (icpAt_left hy z) (icp₀ z)
    · obtain ⟨av', z, hav', hz⟩ := AgWT.mut_wit_le ha₀ eζ kζ
      rw [← wζ] at hav'
      rw [AgWT.functional hav hav']
      exact fun y => icpAt_trans (icpAt_left hz y) (icp₀ y)
    · obtain ⟨ev', av', p', z, -, hav', hp', hz⟩ := AgWT.imm_wit_le ha₀ eζ kζ
      rw [← wζ] at hav'
      rw [AgWT.functional hav hav']
      exact fun y => icpAt_trans (icpAt_right hp' y) (icpAt_trans (icpAt_left hz y) (icp₀ y))
  cases had with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      rename_i a bm bi wm wi
      -- `d` has no `mut` cell, so the `mut` family is empty
      have hwm0 : wm = [] := by
        cases wm with
        | nil => rfl
        | cons p ps =>
            obtain ⟨ψ, e, k⟩ := (hsm.2 p.1).mp (by simp)
            rw [hkind _ _ e] at k; cases k
      subst hwm0
      cases hbm
      have hae : a = (G.restrict CellUT.kind d Kind.imm) :=
        ResUT.CompR.functional ha (ResUT.comp_empty_right _)
      subst hae
      refine ⟨_, bi, hσ, fun y => icpAt_bigComp hbi (fun σ hσm => ?_),
        fun x ψ e => (ResUT.restrict_eq_some.mp e).1⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hσm
      obtain ⟨ψ, ev, av, eψ, hev, hav, hc⟩ := AgWitsIT.mem hwi p hp
      exact icpAt_comp hc (icpAt_of_immFree (ExRT.immFree hev) y) (witICp _ ψ eψ av hav y)

/-- A cell of the image, against `ag(W)`: over an `imm` cell of `w₀` it has an `imm`
counterpart in `ag(W)`; over an `own` or `mut` cell it is `imm({β}, …)`. -/
theorem img_cell {W₁ a₁ w₀ c : TRes K} {le : BoCa.Loc} {s : TSet} {v : BoCa.Val}
    {hs : w₀.InStratum s} {β : Life} (ha₁ : AgWT W₁ a₁)
    (hle : W₁.get le = some (CellUT.immOf s v w₀ hs)) (hr : ResUT.Reb β w₀ c) {x : BoCa.Loc}
    {ψ : TCell K} (e : c.get x = some ψ) :
    ICp a₁ x ψ ∨ ((∃ ζ : TCell K, w₀.get x = some ζ ∧ ζ.kind ≠ Kind.imm) ∧
      ψ.lsOfI = some (TSet.single β)) := by
  rcases reb_cell_ls hr e with h | ⟨ζ, eζ, kζ, rζ, wζ, lζ⟩
  · exact Or.inr h
  · left
    obtain ⟨e₀, a₀, he₀, ha₀, icp₀⟩ := escrow_icp ha₁ hle
    intro hk
    obtain ⟨ξ, eξ, kξ, rξ, wξ, lξ⟩ := icp_trans (icpAt_agW ha₀ x ζ eζ) (icp₀ x) kζ
    refine ⟨ξ, eξ, kξ, rξ.trans rζ.symm, wξ.trans wζ.symm, fun s₁ t hs₁ ht y hy => ?_⟩
    obtain ⟨u, hu⟩ := lsOf_of_imm kζ
    exact lξ u t hu ht y (lζ u s₁ hu hs₁ y hy)

/-- The lifetimes of `ag(d)` at `m`, for `d` a part of the image: each is one of `ag(W)`'s,
or `β` at a cell of `d` over an `own`/`mut` cell of `w₀`. -/
theorem img_ls {W₁ a₁ w₀ c d ad : TRes K} {le : BoCa.Loc} {s : TSet} {v : BoCa.Val}
    {hs : w₀.InStratum s} {β : Life} (ha₁ : AgWT W₁ a₁)
    (hle : W₁.get le = some (CellUT.immOf s v w₀ hs)) (hr : ResUT.Reb β w₀ c)
    (hsub : ∀ x (ψ : TCell K), d.get x = some ψ → c.get x = some ψ) (had : AgWT d ad)
    {m : BoCa.Loc} {ψ : TCell K} (e : ad.get m = some ψ) {t : TSet} (ht : ψ.lsOfI = some t)
    {y : Life} (hy : y ∈ t.set) :
    (∃ ζ t', a₁.get m = some ζ ∧ ζ.lsOfI = some t' ∧ y ∈ t'.set) ∨
    (y = β ∧ (∃ φ, d.get m = some φ) ∧
      ∃ ζ : TCell K, w₀.get m = some ζ ∧ ζ.kind ≠ Kind.imm) := by
  obtain ⟨d', bi, hc, hbi, hd'⟩ := img_walk ha₁ hle hr hsub had
  rcases ResUT.CompR.lsOf_inv hc e ht hy with ⟨ξ, t₁, e₁, ht₁, hy₁⟩ | ⟨ξ, t₁, e₁, ht₁, hy₁⟩
  · have ed := hd' m ξ e₁
    rcases img_cell ha₁ hle hr (hsub m ξ ed) with hi | ⟨hz, hl⟩
    · exact Or.inl (hi.ls ht₁ hy₁)
    · rw [hl] at ht₁; cases Option.some.inj ht₁
      exact Or.inr ⟨by simpa [TSet.single_set] using hy₁, ⟨ξ, ed⟩, hz⟩
  · exact Or.inl ((hbi m ξ e₁).ls ht₁ hy₁)

/-- `NestLife` along a map that sends lifetimes of `ag(W′)`'s child views to `ag(W)` (or
finds the parent directly), and lifetimes of `ag(W)`'s parent views to `ag(W′)`. -/
theorem nestLife_of_maps {W W' aW : TRes K} {r : FrameRecT K} (hN : NestLifeT K W r)
    (haW : AgWT W aW)
    (back : ∀ a', AgWT W' a' → ∀ l₀ m S u, ChainT r.R r.T r.v (some l₀) m S u →
      ∀ (ψ : TCell K) s x, a'.get m = some ψ → ψ.lsOfI = some s → x ∈ s.set →
      (∃ (ζ : TCell K) (t : TSet), aW.get m = some ζ ∧ ζ.lsOfI = some t ∧ x ∈ t.set) ∨
      (∃ (ζ : TCell K) (t : TSet) (y : Life), a'.get l₀ = some ζ ∧ ζ.lsOfI = some t ∧
        y ∈ t.set ∧ K.lt x y))
    (fwd : ∀ a', AgWT W' a' → ∀ l₀ m S u, ChainT r.R r.T r.v (some l₀) m S u →
      ∀ (ζ : TCell K) t y, aW.get l₀ = some ζ → ζ.lsOfI = some t → y ∈ t.set →
      ∃ (ζ' : TCell K) (t' : TSet), a'.get l₀ = some ζ' ∧ ζ'.lsOfI = some t' ∧ y ∈ t'.set) :
    NestLifeT K W' r := by
  intro l₀ m S u hc a' ha' ψ s e hs x hx
  rcases back a' ha' l₀ m S u hc ψ s x e hs hx with ⟨ζ, t, eζ, ht, hxt⟩ | hd
  · obtain ⟨ζ₀, t₀, y, e₀, ht₀, hy, hxy⟩ := hN l₀ m S u hc aW haW ζ t eζ ht x hxt
    obtain ⟨ζ', t', e', ht', hy'⟩ := fwd a' ha' l₀ m S u hc ζ₀ t₀ y e₀ ht₀ hy
    exact ⟨ζ', t', y, e', ht', hy', hxy⟩
  · exact hd

theorem nestLife_of_icp {W W' aW : TRes K} {r : FrameRecT K} (hN : NestLifeT K W r)
    (haW : AgWT W aW)
    (back : ∀ a', AgWT W' a' → ∀ l₀ m S u, ChainT r.R r.T r.v (some l₀) m S u → ICpAt aW a' m)
    (fwd : ∀ a', AgWT W' a' → ∀ l₀ m S u, ChainT r.R r.T r.v (some l₀) m S u →
      ICpAt a' aW l₀) : NestLifeT K W' r :=
  nestLife_of_maps hN haW
    (fun a' ha' l₀ m S u hc ψ _s _x e hs hx =>
      Or.inl ((back a' ha' l₀ m S u hc ψ e).ls hs hx))
    (fun a' ha' l₀ m S u hc ζ _t _y e ht hy => (fwd a' ha' l₀ m S u hc ζ e).ls ht hy)

theorem leInv_of_reb {W W' c : TRes K} {rs : List (FrameRecT K)} (hvW : ResUT.Valid W)
    (hW : ResUT.CompS W c W') (il : LeInvT W rs) : LeInvT W' rs := by
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  intro r' hr' a ha
  obtain ⟨ψ₀, e₀, k₀, r₀, w₀⟩ := il r' hr' aW haW
  obtain ⟨aW', ac, haW', -, hcomp⟩ := (AgWT.split hW).mp ha
  rw [AgWT.functional haW' haW] at hcomp
  obtain ⟨ψ, e, k, r'', w⟩ := imm_fwd_full_l hcomp e₀ k₀
  exact ⟨ψ, e, k, r''.trans r₀, w.trans w₀⟩

end BoCa.Fig16.Tree.Wp

end

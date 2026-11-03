import Support.Model.Tree.CarrierChain

/-!
# At the chain, the tree carrier's operations are the printed ones

`[spec §62]`. Along `chainEquiv` (`ΦU`, `Tree/CarrierChain.lean`): the tags, values, witnesses and strata are
the printed ones (`ΦU_kind`, `ΦU_erase`, `ΦU_wit`, `ΦU_inStratum_iff`), and `▶◀`, `●`, `⋈`, `○`
hold of tree cells exactly when they hold of their images (`chain_compatS_iff`,
`chain_compS_iff`, `chain_compatR_iff`, `chain_compR_iff`). Clause 3 of `○` restated
(`min(β̄₁ ∪ β̄₂)`) is the printed clause 3 (`α ⊓ β`) there.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16 WCactus

variable {Loc Val : Type}

/-! ### `⋈` and `▶◀` by values and witnesses, in the tree carrier -/

/-- `⋈` holds exactly when the two cells share a value, and a witness wherever both have one:
`CellU.compatR_iff` by its proof. -/
theorem CellUT.compatR_iff {K : WCactus} {ψ₁ ψ₂ : CellUT Loc Val K} :
    CellUT.CompatR ψ₁ ψ₂ ↔
      (ψ₁.erase = ψ₂.erase ∧
        (ψ₁.kind ≠ Kind.own → ψ₂.kind ≠ Kind.own → ψ₁.wit = ψ₂.wit)) := by
  constructor
  · rintro ⟨ψ, h⟩
    exact ⟨(CellUT.CompR.erase h).1, fun k₁ k₂ => CellUT.CompR.wit h k₁ k₂⟩
  · rintro ⟨hv, hw⟩
    rcases CellUT.rep ψ₁ with ⟨v₁, rfl⟩ | ⟨s₁, v₁, τ₁, m₁, rfl⟩ |
        ⟨b₁, a₁, v₁, τ₁, m₁, P₁, w₁, rfl⟩ <;>
      rcases CellUT.rep ψ₂ with ⟨v₂, rfl⟩ | ⟨s₂, v₂, τ₂, m₂, rfl⟩ |
        ⟨b₂, a₂, v₂, τ₂, m₂, P₂, w₂, rfl⟩ <;>
      simp only [CellUT.erase_ownOf, CellUT.erase_immOf, CellUT.erase_mutOf] at hv <;>
      subst hv
    · exact ⟨_, CellUT.CompR.same _⟩
    · exact ⟨_, CellUT.CompR.ownImm s₂ _ τ₂ m₂⟩
    · exact ⟨_, CellUT.CompR.ownMut b₂ _ τ₂ m₂ P₂ w₂⟩
    · exact ⟨_, CellUT.CompR.immOwn s₁ _ τ₁ m₁⟩
    · have hτ : τ₁ = τ₂ := by
        have hww := hw (by simp) (by simp)
        rwa [CellUT.wit_immOf, CellUT.wit_immOf] at hww
      subst hτ
      exact ⟨_, CellUT.CompR.strict ⟨s₁, s₂, _, τ₁, m₁, m₂, rfl, rfl⟩⟩
    · have hτ : τ₁ = τ₂ := by
        have hww := hw (by simp) (by simp)
        rwa [CellUT.wit_immOf, CellUT.wit_mutOf] at hww
      subst hτ
      exact ⟨_, CellUT.CompR.immMut s₁ _ τ₁ m₁ b₂ m₂ P₂ w₂⟩
    · exact ⟨_, CellUT.CompR.mutOwn b₁ _ τ₁ m₁ P₁ w₁⟩
    · have hτ : τ₁ = τ₂ := by
        have hww := hw (by simp) (by simp)
        rwa [CellUT.wit_mutOf, CellUT.wit_immOf] at hww
      subst hτ
      exact ⟨_, CellUT.CompR.mutImm s₂ _ τ₁ m₂ b₁ m₁ P₁ w₁⟩
    · have hτ : τ₁ = τ₂ := by
        have hww := hw (by simp) (by simp)
        rwa [CellUT.wit_mutOf, CellUT.wit_mutOf] at hww
      subst hτ
      exact ⟨_, CellUT.CompR.mutMut b₁ b₂ _ τ₁ m₁ m₂ P₁ P₂ w₁ w₂⟩

/-- `▶◀` holds exactly of two `imm` cells sharing a value and a witness. -/
theorem CellUT.compatS_iff {K : WCactus} {ψ₁ ψ₂ : CellUT Loc Val K} :
    CellUT.CompatS ψ₁ ψ₂ ↔ (ψ₁.kind = Kind.imm ∧ ψ₂.kind = Kind.imm ∧
      ψ₁.erase = ψ₂.erase ∧ ψ₁.wit = ψ₂.wit) := by
  constructor
  · rintro ⟨s₁, s₂, v, ρ, h₁, h₂, rfl, rfl⟩
    simp
  · rintro ⟨k₁, k₂, hv, hw⟩
    rcases CellUT.rep ψ₁ with ⟨v₁, rfl⟩ | ⟨s₁, v₁, τ₁, m₁, rfl⟩ |
        ⟨b₁, a₁, v₁, τ₁, m₁, P₁, w₁, rfl⟩ <;> simp at k₁
    rcases CellUT.rep ψ₂ with ⟨v₂, rfl⟩ | ⟨s₂, v₂, τ₂, m₂, rfl⟩ |
        ⟨b₂, a₂, v₂, τ₂, m₂, P₂, w₂, rfl⟩ <;> simp at k₂
    simp only [CellUT.erase_immOf] at hv
    simp only [CellUT.wit_immOf] at hw
    subst hv; subst hw
    exact ⟨s₁, s₂, _, τ₁, m₁, m₂, rfl, rfl⟩

/-- The same in the printed carrier. -/
theorem CellU.compatS_iff' {ψ₁ ψ₂ : CellU Loc Val} :
    CellU.CompatS ψ₁ ψ₂ ↔ (ψ₁.kind = Kind.imm ∧ ψ₂.kind = Kind.imm ∧
      ψ₁.erase = ψ₂.erase ∧ ψ₁.wit = ψ₂.wit) := by
  constructor
  · rintro ⟨s₁, s₂, v, ρ, h₁, h₂, rfl, rfl⟩
    simp
  · rintro ⟨k₁, k₂, hv, hw⟩
    rcases CellU.rep ψ₁ with ⟨v₁, rfl⟩ | ⟨s₁, v₁, τ₁, m₁, rfl⟩ |
        ⟨b₁, v₁, τ₁, m₁, P₁, w₁, rfl⟩ <;> simp at k₁
    rcases CellU.rep ψ₂ with ⟨v₂, rfl⟩ | ⟨s₂, v₂, τ₂, m₂, rfl⟩ |
        ⟨b₂, v₂, τ₂, m₂, P₂, w₂, rfl⟩ <;> simp at k₂
    simp only [CellU.erase_immOf] at hv
    simp only [CellU.wit_immOf] at hw
    subst hv; subst hw
    exact ⟨s₁, s₂, _, τ₁, m₁, m₂, rfl, rfl⟩

/-! ### `ΦU` keeps tags, values and witnesses -/

theorem ΦU_kind (ψ : CellUT Loc Val chain) : (ΦU ψ).kind = ψ.kind := by
  cases ψ <;> rfl

theorem ΦU_erase (ψ : CellUT Loc Val chain) : (ΦU ψ).erase = ψ.erase := by
  cases ψ <;> rfl

theorem ΦU_wit (ψ : CellUT Loc Val chain) : (ΦU ψ).wit = ψ.wit.map ΦU := by
  cases ψ with
  | own v =>
      refine PMap.ext fun l => ?_
      show (PMap.empty : ResU Loc Val).get l = ((PMap.empty : ResUT Loc Val chain).map ΦU).get l
      simp
  | imm i =>
      show (CellU.immOf i.ls.toLSet i.v (i.ρ.map (Phi i.ls).1) _).wit = _
      rw [CellU.wit_immOf, Phi_map]; rfl
  | «mut» m =>
      show (CellU.mutOf m.ls.jn m.v (m.ρ.map (Phi m.ls).1) _
        (fun w r => ∃ r₀ : ResT Loc Val chain m.ls, r₀.map (Phi m.ls).1 = r.val ∧ m.P w r₀)
        ⟨m.ρ, rfl, m.hw⟩).wit = _
      rw [CellU.wit_mutOf, Phi_map]; rfl

theorem ΦU_injective : Function.Injective (ΦU (Loc := Loc) (Val := Val)) := fun a b h => by
  rw [← ΨU_ΦU a, ← ΨU_ΦU b, h]

theorem ΦU_map_injective {r r' : ResUT Loc Val chain} (h : r.map ΦU = r'.map ΦU) : r = r' := by
  have e : (r.map ΦU).map ΨU = (r'.map ΦU).map ΨU := by rw [h]
  simp only [PMap.map_map] at e
  have hid : ΨU ∘ ΦU = (id : CellUT Loc Val chain → CellUT Loc Val chain) :=
    funext fun ψ => ΨU_ΦU ψ
  rw [hid, PMap.map_id', PMap.map_id'] at e
  exact e

theorem ΦU_inStratum_single_iff {a : Life} {ψ : CellUT Loc Val chain} :
    (ΦU ψ).InStratum a ↔ ψ.InStratum (TSet.single a) := by
  have := ΦU_inStratum_iff (S := TSet.single a) (ψ := ψ)
  rwa [TSet.jn_single] at this

/-! ### `▶◀` and `⋈` -/

theorem chain_compatS_iff {ψ₁ ψ₂ : CellUT Loc Val chain} :
    CellU.CompatS (ΦU ψ₁) (ΦU ψ₂) ↔ CellUT.CompatS ψ₁ ψ₂ := by
  rw [CellU.compatS_iff', CellUT.compatS_iff, ΦU_kind, ΦU_kind, ΦU_erase, ΦU_erase, ΦU_wit,
    ΦU_wit]
  exact ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, ΦU_map_injective d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d ▸ rfl⟩⟩

/-! ### `●` -/

theorem chain_compS_of {ψ₁ ψ₂ ψ : CellUT Loc Val chain} (h : CellUT.CompS ψ₁ ψ₂ ψ) :
    CellU.CompS (ΦU ψ₁) (ΦU ψ₂) (ΦU ψ) := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, rfl, rfl, rfl⟩ := h
  rw [ΦU_immOf, ΦU_immOf, ΦU_immOf]
  refine ⟨s₁.toLSet, s₂.toLSet, v, ρ.map ΦU, _, _, ?_, rfl, rfl, ?_⟩
  · rw [← TSet.toLSet_union]; exact ΦU_map_inStratum h₃
  · exact CellU.immOf_congr (TSet.toLSet_union s₁ s₂) rfl rfl _ _

theorem chain_compS_iff {ψ₁ ψ₂ ψ : CellUT Loc Val chain} :
    CellU.CompS (ΦU ψ₁) (ΦU ψ₂) (ΦU ψ) ↔ CellUT.CompS ψ₁ ψ₂ ψ := by
  refine ⟨fun h => ?_, chain_compS_of⟩
  have k : CellUT.CompatS ψ₁ ψ₂ := chain_compatS_iff.mp (CellU.CompS.compat h)
  have h' := chain_compS_of (CellUT.compS_spec ψ₁ ψ₂ k)
  have e := ΦU_injective (CellU.CompS.functional h' h)
  rw [← e]
  exact CellUT.compS_spec ψ₁ ψ₂ k

/-! ### `○`, clause 3 restated -/

/-- Clause 3 at the chain: the tree's `mut(min(β̄₁ ∪ β̄₂), v, ρ, P̂ ∧ Q̂)` is the printed
`mut(α ⊓ β, v, ρ, P̂ ∧ Q̂)`. -/
theorem chain_mutMut (s t : TSet) [as : Fact (chain.Anti s)] [at_ : Fact (chain.Anti t)] (v : Val)
    (ρ : ResUT Loc Val chain) (hs : ρ.InStratum s) (ht : ρ.InStratum t)
    (P : Val → SPropST Loc Val chain s) (Q : Val → SPropST Loc Val chain t)
    (hP : P v ⟨ρ, hs⟩) (hQ : Q v ⟨ρ, ht⟩) :
    CellU.CompR (ΦU (CellUT.mutOf s v ρ hs P hP)) (ΦU (CellUT.mutOf t v ρ ht Q hQ))
      (ΦU (CellUT.mutOf (chain.minS (s ∪ t)) v ρ (hs.minUnion ht)
        (SPropST.conj P Q) (SPropST.conj_holds hs ht hP hQ))) := by
  rw [ΦU_mutOf, ΦU_mutOf, ΦU_mutOf]
  have hst : (chain.minS (s ∪ t)).jn = s.jn ⊓ t.jn := by
    rw [chain_anti_iff.mp as.out, chain_anti_iff.mp at_.out, chain_minS_single, TSet.jn_single,
      ← chain_anti_iff.mp as.out, ← chain_anti_iff.mp at_.out]
  have H := CellU.CompR.mutMut s.jn t.jn v (ρ.map ΦU) (ΦU_map_inStratum hs)
    (ΦU_map_inStratum ht)
    (fun w r => ∃ (r₀ : ResUT Loc Val chain) (h₀ : r₀.InStratum s),
      r₀.map ΦU = r.val ∧ P w ⟨r₀, h₀⟩)
    (fun w r => ∃ (r₀ : ResUT Loc Val chain) (h₀ : r₀.InStratum t),
      r₀.map ΦU = r.val ∧ Q w ⟨r₀, h₀⟩) ⟨ρ, hs, rfl, hP⟩ ⟨ρ, ht, rfl, hQ⟩
  refine (CellU.mutOf_congr' hst.symm rfl _ _ _ _ _ _ ?_) ▸ H
  intro r hr hr' w
  constructor
  · rintro ⟨⟨k₁, r₁, h₁, e₁, p₁⟩, ⟨k₂, r₂, h₂, e₂, p₂⟩⟩
    have e : r₁ = r₂ := ΦU_map_injective (e₁.trans e₂.symm)
    subst e
    exact ⟨r₁, h₁.minUnion h₂, e₁, ⟨h₁, p₁⟩, ⟨h₂, p₂⟩⟩
  · rintro ⟨r₀, h₀, e₀, ⟨h₁, p₁⟩, ⟨h₂, p₂⟩⟩
    exact ⟨⟨e₀ ▸ ΦU_map_inStratum h₁, r₀, h₁, e₀, p₁⟩,
      ⟨e₀ ▸ ΦU_map_inStratum h₂, r₀, h₂, e₀, p₂⟩⟩

theorem chain_compR_of {ψ₁ ψ₂ ψ : CellUT Loc Val chain} (h : CellUT.CompR ψ₁ ψ₂ ψ) :
    CellU.CompR (ΦU ψ₁) (ΦU ψ₂) (ΦU ψ) := by
  cases h with
  | same => exact CellU.CompR.same _
  | strict k =>
      have hs := chain_compS_of (CellUT.compS_spec _ _ k)
      have e := CellU.CompS.functional (CellU.compS_spec _ _ hs.compat) hs
      exact e ▸ CellU.CompR.strict hs.compat
  | mutMut s t v ρ hs ht P Q hP hQ => exact chain_mutMut s t v ρ hs ht P Q hP hQ
  | mutOwn s v ρ hs P hP =>
      rw [ΦU_mutOf]; exact CellU.CompR.mutOwn _ _ _ _ _ _
  | ownMut s v ρ hs P hP =>
      rw [ΦU_mutOf]; exact CellU.CompR.ownMut _ _ _ _ _ _
  | immOwn s v ρ h =>
      rw [ΦU_immOf]; exact CellU.CompR.immOwn _ _ _ _
  | ownImm s v ρ h =>
      rw [ΦU_immOf]; exact CellU.CompR.ownImm _ _ _ _
  | immMut s v ρ h b hb P hP =>
      rw [ΦU_immOf, ΦU_mutOf]; exact CellU.CompR.immMut _ _ _ _ _ _ _ _
  | mutImm s v ρ h b hb P hP =>
      rw [ΦU_immOf, ΦU_mutOf]; exact CellU.CompR.mutImm _ _ _ _ _ _ _ _

/-- **At the chain, `⋈` is the printed `⋈`.** -/
theorem chain_compatR_iff {ψ₁ ψ₂ : CellUT Loc Val chain} :
    CellU.CompatR (ΦU ψ₁) (ΦU ψ₂) ↔ CellUT.CompatR ψ₁ ψ₂ := by
  constructor
  · rintro ⟨ψ, h⟩
    refine CellUT.compatR_iff.mpr ⟨?_, fun k₁ k₂ => ?_⟩
    · have := (CellU.CompR.erase h).1
      rwa [ΦU_erase, ΦU_erase] at this
    · have := CellU.CompR.wit h (by rwa [ΦU_kind]) (by rwa [ΦU_kind])
      rw [ΦU_wit, ΦU_wit] at this
      exact ΦU_map_injective this
  · rintro ⟨ψ, h⟩
    exact ⟨_, chain_compR_of h⟩

/-- **At the chain, `○` is the printed `○`.** -/
theorem chain_compR_iff {ψ₁ ψ₂ ψ : CellUT Loc Val chain} :
    CellU.CompR (ΦU ψ₁) (ΦU ψ₂) (ΦU ψ) ↔ CellUT.CompR ψ₁ ψ₂ ψ := by
  refine ⟨fun h => ?_, chain_compR_of⟩
  obtain ⟨ψ', h'⟩ := chain_compatR_iff.mp ⟨_, h⟩
  have e := ΦU_injective (CellU.CompR.functional (chain_compR_of h') h)
  exact e ▸ h'

end BoCa.Fig16.Tree

end

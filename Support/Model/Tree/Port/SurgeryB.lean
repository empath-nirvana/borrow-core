import Support.Model.Tree.Port.Six25to33

/-!
# `Support/Model/Surgery.lean`'s cell-level support, over the tree-stratified carrier

`[spec §62]`. `Support/Model/Surgery.lean`'s cell-level support, read at `CellUT K`.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-- `○` drops no lifetime from an `imm` operand.
`[about ours: the set half of "`ag(ρ)` keeps every `imm` cell of `ρ`"]` -/
theorem CellUT.CompR.ls_imm {ψ₁ ψ₂ ψ : CellUT Loc Val K} (hc : CellUT.CompR ψ₁ ψ₂ ψ)
    {s₁ : TSet} {v₁ : Val} {χ₁ : ResUT Loc Val K} {h₁ : χ₁.InStratum s₁}
    (e₁ : ψ₁ = CellUT.immOf s₁ v₁ χ₁ h₁)
    {s : TSet} {v : Val} {χ : ResUT Loc Val K} {h : χ.InStratum s}
    (e : ψ = CellUT.immOf s v χ h) {x : Life} (hx : x ∈ s₁.set) : x ∈ s.set := by
  cases hc with
  | same χ' =>
      obtain ⟨hs, -, -⟩ := CellUT.immOf_inj (e₁.symm.trans e)
      exact hs ▸ hx
  | strict k =>
      obtain ⟨t₁, t₂, w, τ, k₁, k₂, k₃, f₁, f₂, f₃⟩ := CellUT.compS_spec _ _ k
      obtain ⟨ht₁, -, -⟩ := CellUT.immOf_inj (e₁.symm.trans f₁)
      obtain ⟨ht, -, -⟩ := CellUT.immOf_inj (f₃.symm.trans e)
      exact ht ▸ Finset.mem_union_left _ (ht₁ ▸ hx)
  | mutMut a b w τ ha hb P Q hP hQ => exact absurd e₁.symm CellUT.immOf_ne_mutOf
  | mutOwn a w τ ha P hP => exact absurd e₁.symm CellUT.immOf_ne_mutOf
  | ownMut a w τ ha P hP => exact absurd e₁ CellUT.ownOf_ne_immOf
  | immOwn t w τ ht =>
      obtain ⟨hs, -, -⟩ := CellUT.immOf_inj (e₁.symm.trans e)
      exact hs ▸ hx
  | ownImm t w τ ht => exact absurd e₁ CellUT.ownOf_ne_immOf
  | immMut t w τ ht b hb P hP =>
      obtain ⟨hs, -, -⟩ := CellUT.immOf_inj (e₁.symm.trans e)
      exact hs ▸ hx
  | mutImm t w τ ht b hb P hP => exact absurd e₁.symm CellUT.immOf_ne_mutOf

/-- The same at a location of a `○`. -/
theorem ResUT.CompR.get_ls_imm {ρ₁ ρ₂ ρ : ResUT Loc Val K} (h : ResUT.CompR ρ₁ ρ₂ ρ)
    {l : Loc} {s₁ : TSet} {v₁ : Val} {χ₁ : ResUT Loc Val K} {h₁ : χ₁.InStratum s₁}
    (e₁ : ρ₁.get l = some (CellUT.immOf s₁ v₁ χ₁ h₁))
    {s : TSet} {v : Val} {χ : ResUT Loc Val K} {hh : χ.InStratum s}
    (e : ρ.get l = some (CellUT.immOf s v χ hh)) {x : Life} (hx : x ∈ s₁.set) : x ∈ s.set := by
  rcases ResUT.Comp.get h l with ⟨f₁, -, -⟩ | ⟨ζ, f₁, -, f⟩ | ⟨ζ, f₁, -, -⟩ | ⟨ζ₁, ζ₂, ζ, f₁, -, f, hC⟩
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁
    rw [← Option.some.inj f₁] at f
    obtain ⟨hs, -, -⟩ := CellUT.immOf_inj (Option.some.inj (f.symm.trans e))
    exact hs ▸ hx
  · rw [e₁] at f₁; exact absurd f₁ (by simp)
  · rw [e₁] at f₁
    exact CellUT.CompR.ls_imm hC (Option.some.inj f₁).symm
      (Option.some.inj (f.symm.trans e)) hx

/-- The same through `ag`. -/
theorem AgWT.get_ls_imm {ρ σ : ResUT Loc Val K} (h : AgWT ρ σ)
    {l : Loc} {s₁ : TSet} {v₁ : Val} {χ₁ : ResUT Loc Val K} {h₁ : χ₁.InStratum s₁}
    (e₁ : ρ.get l = some (CellUT.immOf s₁ v₁ χ₁ h₁))
    {s : TSet} {v : Val} {χ : ResUT Loc Val K} {hh : χ.InStratum s}
    (e : σ.get l = some (CellUT.immOf s v χ hh)) {x : Life} (hx : x ∈ s₁.set) : x ∈ s.set := by
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      have hk₁ : (CellUT.immOf s₁ v₁ χ₁ h₁).kind = Kind.imm := CellUT.kind_immOf _ _ _ _
      obtain ⟨ζ, hζ, hkζ, -, -⟩ :=
        ResUT.CompR.get_imm_left ha (ResUT.restrict_get_some e₁ hk₁) hk₁
      obtain ⟨t, ht, hetaζ⟩ := CellUT.imm_eta hkζ
      refine ResUT.CompR.get_ls_imm hσ (hζ.trans (congrArg some hetaζ)) e ?_
      exact ResUT.CompR.get_ls_imm ha (ResUT.restrict_get_some e₁ hk₁)
        (hζ.trans (congrArg some hetaζ)) hx

/-- The same through `⦇−⦈`. -/
theorem ResUT.Flat.get_ls_imm {ρ σ : ResUT Loc Val K} (h : ResUT.Flat ρ σ)
    {l : Loc} {s₁ : TSet} {v₁ : Val} {χ₁ : ResUT Loc Val K} {h₁ : χ₁.InStratum s₁}
    (e₁ : ρ.get l = some (CellUT.immOf s₁ v₁ χ₁ h₁))
    {s : TSet} {v : Val} {χ : ResUT Loc Val K} {hh : χ.InStratum s}
    (e : σ.get l = some (CellUT.immOf s v χ hh)) {x : Life} (hx : x ∈ s₁.set) : x ∈ s.set := by
  obtain ⟨ex, ag, hex, hag, hc⟩ := h
  have hk₁ : (CellUT.immOf s₁ v₁ χ₁ h₁).kind = Kind.imm := CellUT.kind_immOf _ _ _ _
  obtain ⟨ζ, hζ, hkζ, -, -⟩ := AgWT.get_imm hag e₁ hk₁
  have : σ.get l = some ζ := ResUT.CompS.get_right_of_immFree hc (ExST.immFree hex) hζ
  rw [e] at this
  obtain rfl : ζ = CellUT.immOf s v χ hh := (Option.some.inj this).symm
  exact AgWT.get_ls_imm hag e₁ hζ hx

/-- If `⦇X⦈` carries an `imm` cell at `ℓ` one of whose lifetimes is `α`, and
every other cell of the flattening lies in `Res_α`, then `X` carries a cell at
`ℓ`: `[TR]` 6.29's (p. 11) *"all borrows in `⦇ρ′⦈` other than `ρᵢ` must be
disjoint from `α`, which by well-formedness of the resource `ρ′` implies that
the cell … cannot be in any `ρ″` …"*, repeated in 6.52 (p. 17).
*"Well-formedness"* is Fig. 16's typing of the borrow cells' witnesses, which
are arguments of `CellUT.immOf` and `CellUT.mutOf`.
`[about ours: the step of `[TR]` 6.29's and 6.52's proofs]`
At the tree `Res_α` is the stratum `{α}`, and an `imm` cell of `ag` lies in every stratum its
`ag` image does (`BoLo.agW_get_at`'s `StratumLE`), where the chain compares `@`. -/
theorem ResUT.flat_imm_at_top {X σ : ResUT BoCa.Loc BoCa.Val K} {α : Life}
    (hσ : ResUT.Flat X σ) {l : BoCa.Loc} {s : TSet} {v : BoCa.Val}
    {χ : ResUT BoCa.Loc BoCa.Val K} {h : χ.InStratum s}
    (hl : σ.get l = some (CellUT.immOf s v χ h)) (hmem : α ∈ s.set)
    (hoff : ∀ m, m ≠ l → ∀ ψ, σ.get m = some ψ → ψ.InStratum (TSet.single α)) :
    ∃ φ, X.get l = some φ := by
  obtain ⟨ex', ag', hex', hag', hc'⟩ := hσ
  have hpoint : ∀ m, (∀ ζ, σ.get m = some ζ → ζ.InStratum (TSet.single α)) →
      ∀ ψ, X.get m = some ψ → ψ.InStratum (TSet.single α) := by
    intro m hstr ψ hm
    by_cases hk : ψ.kind = Kind.imm
    · obtain ⟨ζ, hζ, hkζ, hle⟩ := BoLo.agW_get_at hag' hm hk
      have hσm : σ.get m = some ζ :=
        ResUT.CompS.get_right_of_immFree hc' (ExST.immFree hex') hζ
      exact hle _ (hstr ζ hσm)
    · exact hstr ψ (ResUT.CompS.get_left_of_ne_imm hc'
        (ExST.get_of_ne_imm hex' hm hk) hk).2
  cases hg : X.get l with
  | some φ => exact ⟨φ, rfl⟩
  | none =>
      exfalso
      have hin : X.InStratum (TSet.single α) := by
        intro m ψ hm
        by_cases hml : m = l
        · subst hml; rw [hg] at hm; exact absurd hm (by simp)
        · exact hpoint m (fun ζ hζ => hoff m hml ζ hζ) ψ hm
      have hbad := BoLo.flat_inStratum ⟨ex', ag', hex', hag', hc'⟩ hin l _ hl
      rw [CellUT.inStratum_immOf] at hbad
      exact Cactus.lt_irrefl _ α (hbad α (by simp) α hmem)

end BoCa.Fig16.Tree

end

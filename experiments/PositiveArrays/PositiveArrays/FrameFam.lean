import PositiveArrays.Index

/-!
# PositiveArrays — the Mut Frame over a family of places

`[TR]` Theorem 6.65 (Mut Frame) frames one owned cell. `wpTS_M_frameList` frames the cells of
any finite list of places `I` around one expression: it is `wpTS_M_frameX` applied once per
place, by induction on the list, generalized over the postcondition.

    ⊛_{ℓ∈I} 𝒱⟦Ref T⟧(ℓ) ⋆ ⋔α. (⊛_{ℓ∈I} ℓ ↦ M_α 𝒱⟦T⟧ ─⋆ wp(e){Φ})  ⊨  wp(e){Q}
        whenever  ⊛_{ℓ∈I} 𝒱⟦Ref T⟧(ℓ) ⋆ Φ ⊨ Q  and  Φ ⊨ [β′]Φ

`wpTS_M_frameFam` is the instance at a run-time range `I = [ℓ, …, ℓ + n − 1]`, an owned array;
a static list of a struct's leaves is another instance.

Frame `j` picks its own lifetime `α_j`, each strictly below the one before, and the callback
receives every leaf at the innermost: `ptoMutS` is antitone in its lifetime (6.118), so the leaf
of frame `j` is a leaf at `α_n`. Frame `j`'s postcondition sits under `[α_j]`, while the callback
returns a resource known to be in `Res_{α_n}` only. The premise `Φ ⊨ [β′]Φ` supplies the
missing strata: every `α_j` is chosen below `β′`. That premise is where K2's side condition on
its result type enters (6.60, `vC_outlives`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.PositiveArrays
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- An owned leaf `ℓ ↦ v ⋆ 𝒱⟦T ℓ⟧(v)`, its type chosen by its place: a struct's field. -/
abbrev ownLeafH (T : Loc → VTy) (ls : List SRec) (δ : LSub) : Loc → WProp :=
  fun m => vP (.ref (T m)) ls δ (.loc m)

/-- A `mut` leaf at `α`, its type chosen by its place. -/
abbrev mutLeafH (T : Loc → VTy) (ls : List SRec) (δ : LSub) (α : Life) : Loc → WProp :=
  fun m => ptoMutS m α ls (fun ls₀ => vC true (T m) ls₀ δ)

/-- An owned leaf of one type, the leaf of `Array T`. -/
abbrev ownLeaf (T : VTy) (ls : List SRec) (δ : LSub) : Loc → WProp := ownLeafH (fun _ => T) ls δ

/-- A `mut` leaf of one type, the leaf of `[Mut 'c T]` at `'c ↦ α`. -/
abbrev mutLeaf (T : VTy) (ls : List SRec) (δ : LSub) (α : Life) : Loc → WProp :=
  mutLeafH (fun _ => T) ls δ α

/-- A property of resources closed under `●` and holding at `∅`: membership in `Res_α`. -/
theorem outlives_compS_closed (α : Life) :
    ∀ ρ₁ ρ₂ ρ : WRes, ResU.CompS ρ₁ ρ₂ ρ → BoLo.Outlives ρ₁ α → BoLo.Outlives ρ₂ α →
      BoLo.Outlives ρ α :=
  fun _ _ _ hc h₁ h₂ => (BoLo.outlives_comp hc α).mpr ⟨h₁, h₂⟩

/-- An owned leaf is in `Res_α` when its payload's relation is. -/
theorem ownLeaf_outlives {T : Loc → VTy} {δ : LSub} {β α : Life} (hαβ : α ⊑ β)
    (hP : ∀ m ls w σ, vC true (T m) ls δ w σ → σ.InStratum β) {ls : List SRec} {m : Loc}
    {ρ : WRes} (h : ownLeafH T ls δ m ρ) : BoLo.Outlives ρ α := by
  obtain ⟨ℓ', w, hk⟩ := h
  obtain ⟨-, c, p, hcp, hc, hp⟩ := pure_sep_iff.mp hk
  refine (BoLo.outlives_comp hcp α).mpr ⟨?_, ?_⟩
  · rw [hc]; exact ResU.inStratum_single_own α ℓ' w
  · exact BoLo.Outlives.mono hαβ (hP m ls w p hp)

/-- A family of owned leaves is in `Res_α`. -/
theorem ownList_outlives {T : Loc → VTy} {δ : LSub} {β α : Life} (hαβ : α ⊑ β)
    (hP : ∀ m ls w σ, vC true (T m) ls δ w σ → σ.InStratum β) {ls : List SRec} {I : List Loc}
    {ρ : WRes} (h : sepList (ownLeafH T ls δ) I ρ) : BoLo.Outlives ρ α :=
  sepList_closed (ResU.inStratum_empty α) (outlives_compS_closed α)
    (fun _ _ h => ownLeaf_outlives hαβ hP h) h

/-- **One Mut Frame per place, around one expression.** The leaves may differ in type. -/
theorem wpTS_M_frameList (T : Loc → VTy) (δ : LSub) (β : Life)
    (hP : ∀ m ls w σ, vC true (T m) ls δ w σ → σ.InStratum β) (e : Expr) (ls : List SRec)
    (Φ : List SRec → Val → WProp) (β' : Life) (hΦ : ∀ ls v ρ, Φ ls v ρ → BoLo.Outlives ρ β') :
    ∀ (I : List Loc) (Q : List SRec → Val → WProp),
      (∀ ls' v, Entails (sepList (ownLeafH T ls' δ) I ⋆ Φ ls' v) (Q ls' v)) →
      Entails
        (sepList (ownLeafH T ls δ) I ⋆
          fresh (fun α => sepList (mutLeafH T ls δ α) I ─⋆ wpTS ls e Φ))
        (wpTS ls e Q)
  | [], Q, hQ => by
      rintro ρ ⟨ρo, ρH, hc, ⟨rfl, -⟩, γH, hH⟩
      rw [eq_of_compS_empty_left hc]
      obtain ⟨hw, -⟩ := hH (↓γH) (Life.down_sqsubset γH)
      have hwp := hw PMap.empty ρH ⟨rfl, trivial⟩ (ResU.comp_empty_right ρH)
      exact wpTS_mono (fun ls' v σ h => hQ ls' v σ
        ⟨PMap.empty, σ, compS_empty_left σ, ⟨rfl, trivial⟩, h⟩) ρH hwp
  | ℓ :: I, Q, hQ => by
      rintro ρ ⟨ρo, ρH, hc, ⟨ρ0, ρr, hc0, hleaf, hrest⟩, γH, hH⟩
      obtain ⟨ℓ', v, hk⟩ := hleaf
      obtain ⟨hl, c, p, hcp, hcell, hpv⟩ := pure_sep_iff.mp hk
      have hℓ : ℓ' = ℓ := by
        have := congrArg Subtype.val hl; simpa using this.symm
      subst hℓ
      -- `ρ = c ● (p ● (ρr ● ρH))`
      obtain ⟨F, hF, hρ⟩ := compS_reassoc hc0 hc
      obtain ⟨G, hG, hρ'⟩ := compS_reassoc hcp hρ
      refine wpTS_M_frameX ℓ' (T ℓ') δ β (hP ℓ') v e ls Q ρ ⟨c, G, hρ', hcell, p, F, hG, hpv, ?_⟩
      -- the outer frame's lifetime `α₁`, below `@F`, `β′` and `β`
      obtain ⟨aF, haF⟩ := F.exists_atLife
      refine ⟨aF ⊓ β' ⊓ β, fun α₁ hα₁ => ⟨?_, outlives_of_atLife haF
        (lt_of_lt_of_le hα₁ (le_trans inf_le_left inf_le_left))⟩⟩
      have hα₁β' : α₁ ⊑ β' := le_of_lt (lt_of_lt_of_le hα₁ (le_trans inf_le_left inf_le_right))
      have hα₁β : α₁ ⊑ β := le_of_lt (lt_of_lt_of_le hα₁ inf_le_right)
      intro ρm ρ' hm hcm
      -- `ρ′ = ρr ● (ρH ● ρm)`
      obtain ⟨R, hR, hρ''⟩ := compS_reassoc hF hcm
      -- the remaining places, framed by the induction hypothesis
      refine wpTS_M_frameList T δ β hP e ls Φ β' hΦ I _ ?_ ρ'
        ⟨ρr, R, hρ'', hrest, ?_⟩
      · -- the outer frame's postcondition from the inner ones'
        intro ls' v' σ ⟨σo, σΦ, hσ, ho, hφ⟩
        refine ⟨?_, (BoLo.outlives_comp hσ α₁).mpr
          ⟨ownList_outlives hα₁β hP ho, BoLo.Outlives.mono hα₁β' (hΦ ls' v' σΦ hφ)⟩⟩
        intro w c₁ c₂ hc₁ hcc p₁ p₂ hp₁ hcp₁
        -- the returned leaf `c₁ ● p₁`, beside the rest and `Φ`
        obtain ⟨cp, hcp', hp₂⟩ := compS_reassoc hcc hcp₁
        obtain ⟨oc, hoc, hp₂'⟩ := compS_exch hσ hp₂
        exact hQ ls' v' p₂ ⟨oc, σΦ, hp₂', ⟨cp, σo, ResU.CompS.comm hoc,
          ⟨ℓ', w, pure_sep_mk rfl ⟨c₁, p₁, hcp', hc₁, hp₁⟩⟩, ho⟩, hφ⟩
      · -- the inner frames' lifetime `α₂`, below `@R`, `α₁` and the callback's bound
        obtain ⟨aR, haR⟩ := R.exists_atLife
        refine ⟨aR ⊓ α₁ ⊓ γH, fun α₂ hα₂ => ⟨?_, outlives_of_atLife haR
          (lt_of_lt_of_le hα₂ (le_trans inf_le_left inf_le_left))⟩⟩
        have hα₂α₁ : α₂ ⊑ α₁ :=
          le_of_lt (lt_of_lt_of_le hα₂ (le_trans inf_le_left inf_le_right))
        have hα₂H : α₂ ⊏ γH := lt_of_lt_of_le hα₂ inf_le_right
        intro ρm₂ ρ₃ hm₂ hcm₂
        -- the outer leaf, shortened to `α₂` (6.118), heads the family
        obtain ⟨X, hX, hρ₃⟩ := compS_reassoc hR hcm₂
        exact (hH α₂ hα₂H).1 X ρ₃ ⟨ρm, ρm₂, hX, ptoMutS_antitone hα₂α₁ hm, hm₂⟩ hρ₃

/-- A range of owned leaves is in `Res_α`. -/
theorem ownRange_outlives {T : VTy} {δ : LSub} {β α : Life} (hαβ : α ⊑ β)
    (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β) {ls : List SRec} {ℓ : Loc} {n : Nat}
    {ρ : WRes} (h : sepRange (ownLeaf T ls δ) ℓ n ρ) : BoLo.Outlives ρ α := by
  rw [sepRange_eq_sepList] at h; exact ownList_outlives (T := fun _ => T) hαβ (fun _ => hP) h

/-- **`n` Mut Frames around one expression**: the family is an owned array's range. -/
theorem wpTS_M_frameFam (T : VTy) (δ : LSub) (β : Life)
    (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β) (e : Expr) (ls : List SRec)
    (Φ : List SRec → Val → WProp) (β' : Life) (hΦ : ∀ ls v ρ, Φ ls v ρ → BoLo.Outlives ρ β')
    (n : Nat) (ℓ : Loc) (Q : List SRec → Val → WProp)
    (hQ : ∀ ls' v, Entails (sepRange (ownLeaf T ls' δ) ℓ n ⋆ Φ ls' v) (Q ls' v)) :
    Entails
      (sepRange (ownLeaf T ls δ) ℓ n ⋆
        fresh (fun α => sepRange (mutLeaf T ls δ α) ℓ n ─⋆ wpTS ls e Φ))
      (wpTS ls e Q) := by
  simp only [sepRange_eq_sepList] at hQ ⊢
  exact wpTS_M_frameList (fun _ => T) δ β (fun _ => hP) e ls Φ β' hΦ _ Q hQ

end BoCa.Fig16.LogRel.Core.PositiveArrays

end

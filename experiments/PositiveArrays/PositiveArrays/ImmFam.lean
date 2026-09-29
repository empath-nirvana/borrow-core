import PositiveArrays.FrameFam

/-!
# PositiveArrays — the Imm Frame over a run-time family

`[TR]` Theorem 6.64 (Imm Frame) frames one owned cell and adds its record to the list at the
frame's lifetime. `wpTS_I_frameList` frames the cells of any finite list of places around one
expression: `wpTS_I_frameX` applied once per place, by induction on the list.
`wpTS_I_frameFam` is the instance at an owned array's range.

The bookkeeping `wpTS_M_frameFam` does not have:

- each frame extends the record list (`AddAt` at its lifetime), so the callback runs at a list
  `ls′` `Ext`-above the original, and the hypothesis quantifies over every such list;
- a leaf carries its frame's record (`immLeaf`), and both leaf and record survive later
  extensions: `Ext` keeps the records relevant to the leaf's `imm` cell (`immLeaf_ext`);
- 6.64 asks for a postcondition stable along `Ext`, so the induction runs at the fixed
  postcondition `⊛ 𝒱⟦Ref T⟧ ⋆ Φ` (with `Φ` stable) and weakens afterwards.

As at `Mut`, the outer frames' postconditions sit under their own `[α_j]` while the callback
returns at the innermost; `Φ ⊨ [β′]Φ` and `𝒱⟦T⟧ ⊨ [β]𝒱⟦T⟧` supply the strata. The second is a
premise `withbor1` (`[TR]` 6.172) does not need: with one frame the returned payload is the
frame's own business, with `n` it sits beside the other frames' postconditions.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.PositiveArrays
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- An `imm` leaf at `α`, its type chosen by its place, with the record its frame made. -/
def immLeafH (T : Loc → VTy) (ls : List SRec) (δ : LSub) (α : Life) : Loc → WProp := fun m ρ =>
  (∃ r ∈ rsOf ls, r.le = m ∧ r.T = T m ∧ r.δ = δ) ∧
    ptoImmS m α ls (fun ls₀ => vC true (T m) ls₀ δ) ρ

/-- An `imm` leaf of one type. -/
abbrev immLeaf (T : VTy) (ls : List SRec) (δ : LSub) (α : Life) : Loc → WProp :=
  immLeafH (fun _ => T) ls δ α

/-- `[TR]` 6.114 (`I ⊒`) at a leaf. -/
theorem immLeaf_antitone {T : Loc → VTy} {ls : List SRec} {δ : LSub} {α β : Life} (h : β ⊑ α)
    {m : Loc} {ρ : WRes} (hl : immLeafH T ls δ α m ρ) : immLeafH T ls δ β m ρ :=
  ⟨hl.1, ptoImmS_antitone h hl.2⟩

/-- A leaf and its record are stable along `Ext`. -/
theorem immLeaf_ext {T : Loc → VTy} {ls ls' : List SRec} {δ : LSub} {α : Life} {m : Loc}
    {ρ : WRes} (hk : Ext ls ls' ρ) (hl : immLeafH T ls δ α m ρ) : immLeafH T ls' δ α m ρ := by
  obtain ⟨⟨r, hr, hle, hT, hδ⟩, s, u, σ, hs, ls₀, hρ, hP, hαs, hls₀⟩ := hl
  subst hρ
  have hcell : CellIn (ResU.single m (CellU.immOf s u σ hs)) s.meet :=
    CellIn.single (by simp)
  have hrel : Rel r (ResU.single m (CellU.immOf s u σ hs)) :=
    ⟨m, _, ResU.single_get_self _ _, CellU.kind_immOf _ _ _ _, Or.inl hle.symm⟩
  refine ⟨⟨r, hk.1 r hr hrel, hle, hT, hδ⟩, s, u, σ, hs, ls₀, rfl, hP, hαs, fun x => ?_⟩
  rw [hls₀ x]
  exact ⟨fun ⟨hx, hb⟩ => ⟨(hk.2 _ hcell x hb).mp hx, hb⟩,
         fun ⟨hx, hb⟩ => ⟨(hk.2 _ hcell x hb).mpr hx, hb⟩⟩

/-- A family of leaves stable along `Ext` is. -/
theorem sepList_ext {P : List SRec → Loc → WProp}
    (hP : ∀ ls ls' m ρ, Ext ls ls' ρ → P ls m ρ → P ls' m ρ) {ls ls' : List SRec}
    {I : List Loc} {ρ : WRes} (hk : Ext ls ls' ρ) (h : sepList (P ls) I ρ) : sepList (P ls') I ρ :=
  sepList_mono_down (R := fun σ => Ext ls ls' σ)
    (fun _ _ _ hc hk' => ⟨hk'.left hc, hk'.right hc⟩) (fun m σ hkσ hm => hP _ _ m σ hkσ hm) hk h

theorem ownList_ext {T : Loc → VTy} {δ : LSub} {ls ls' : List SRec} {I : List Loc}
    {ρ : WRes} (hk : Ext ls ls' ρ) (h : sepList (ownLeafH T ls δ) I ρ) :
    sepList (ownLeafH T ls' δ) I ρ :=
  sepList_ext (P := fun ls => ownLeafH T ls δ) (fun _ _ _ _ hk' h => vC_local true _ hk' h) hk h

/-- **One Imm Frame per place, around one expression.** The leaves may differ in type. -/
theorem wpTS_I_frameList (T : Loc → VTy) (δ : LSub) (β : Life)
    (hP : ∀ m ls w σ, vC true (T m) ls δ w σ → σ.InStratum β) (hadm : ∀ m, AdmWf (T m) δ)
    (e : Expr)
    (Φ : List SRec → Val → WProp) (β' : Life) (hΦ : ∀ ls v ρ, Φ ls v ρ → BoLo.Outlives ρ β')
    (hΦext : ∀ ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Φ ls₁ w ρ → Φ ls₂ w ρ) :
    ∀ (I : List Loc) (ls : List SRec),
      Entails
        (sepList (ownLeafH T ls δ) I ⋆
          fresh (fun α ρ => ∀ ls', Ext ls ls' ρ →
            (sepList (immLeafH T ls' δ α) I ─⋆ wpTS ls' e Φ) ρ))
        (wpTS ls e (fun ls' v => sepList (ownLeafH T ls' δ) I ⋆ Φ ls' v))
  | [], ls => by
      rintro ρ ⟨ρo, ρH, hc, ⟨rfl, -⟩, γH, hH⟩
      rw [eq_of_compS_empty_left hc]
      obtain ⟨hw, -⟩ := hH (↓γH) (Life.down_sqsubset γH)
      have hwp := hw ls (Ext.refl _ _) PMap.empty ρH ⟨rfl, trivial⟩ (ResU.comp_empty_right ρH)
      exact wpTS_mono (fun ls' v σ h =>
        ⟨PMap.empty, σ, compS_empty_left σ, ⟨rfl, trivial⟩, h⟩) ρH hwp
  | ℓ :: I, ls => by
      rintro ρ ⟨ρo, ρH, hc, ⟨ρ0, ρr, hc0, hleaf, hrest⟩, γH, hH⟩
      obtain ⟨ℓ', v, hk⟩ := hleaf
      obtain ⟨hl, c, p, hcp, hcell, hpv⟩ := pure_sep_iff.mp hk
      have hℓ : ℓ' = ℓ := by
        have := congrArg Subtype.val hl; simpa using this.symm
      subst hℓ
      obtain ⟨F, hF, hρ⟩ := compS_reassoc hc0 hc
      obtain ⟨G, hG, hρ'⟩ := compS_reassoc hcp hρ
      -- 6.64's postcondition is stable along `Ext`
      have hQext : ∀ ls₁ ls₂ w σ, Ext ls₁ ls₂ σ →
          (sepList (ownLeafH T ls₁ δ) (ℓ' :: I) ⋆ Φ ls₁ w) σ →
          (sepList (ownLeafH T ls₂ δ) (ℓ' :: I) ⋆ Φ ls₂ w) σ := by
        rintro ls₁ ls₂ w σ hk ⟨σo, σΦ, hσ, ho, hφ⟩
        exact ⟨σo, σΦ, hσ, ownList_ext (hk.left hσ) ho, hΦext _ _ _ _ (hk.right hσ) hφ⟩
      refine wpTS_I_frameX ℓ' (T ℓ') δ (hadm ℓ') v e ls _ hQext ρ
        ⟨c, G, hρ', hcell, p, F, hG, hpv, ?_⟩
      obtain ⟨aF, haF⟩ := F.exists_atLife
      have houtF : ∀ α₁, α₁ ⊏ aF ⊓ β' ⊓ β → F.InStratum α₁ := fun α₁ hα₁ =>
        outlives_of_atLife haF (lt_of_lt_of_le hα₁ (le_trans inf_le_left inf_le_left))
      refine ⟨aF ⊓ β' ⊓ β, fun α₁ hα₁ => ⟨?_, houtF α₁ hα₁⟩⟩
      have hα₁β' : α₁ ⊑ β' := le_of_lt (lt_of_lt_of_le hα₁ (le_trans inf_le_left inf_le_right))
      have hα₁β : α₁ ⊑ β := le_of_lt (lt_of_lt_of_le hα₁ inf_le_right)
      intro ls₁ hadd hrec ρm ρ' hm hcm
      have hkF : Ext ls ls₁ F := ext_add hadd (houtF α₁ hα₁)
      obtain ⟨R, hR, hρ''⟩ := compS_reassoc hF hcm
      refine wpTS_mono (Q := fun ls'' v' => box α₁ (ptoOwn ℓ' v ─⋆
          (vC true (T ℓ') ls'' δ v ─⋆ (sepList (ownLeafH T ls'' δ) (ℓ' :: I) ⋆ Φ ls'' v'))))
        ?_ ρ' (wpTS_I_frameList T δ β hP hadm e Φ β' hΦ hΦext I ls₁ ρ'
          ⟨ρr, R, hρ'', ownList_ext (hkF.left hF) hrest, ?_⟩)
      · -- the outer frame's postcondition from the inner ones'
        intro ls' v' σ ⟨σo, σΦ, hσ, ho, hφ⟩
        refine ⟨?_, (BoLo.outlives_comp hσ α₁).mpr
          ⟨ownList_outlives hα₁β hP ho, BoLo.Outlives.mono hα₁β' (hΦ ls' v' σΦ hφ)⟩⟩
        intro c₁ c₂ hc₁ hcc p₁ p₂ hp₁ hcp₁
        obtain ⟨cp, hcp', hp₂⟩ := compS_reassoc hcc hcp₁
        obtain ⟨oc, hoc, hp₂'⟩ := compS_exch hσ hp₂
        exact ⟨oc, σΦ, hp₂', ⟨cp, σo, ResU.CompS.comm hoc,
          ⟨ℓ', v, pure_sep_mk rfl ⟨c₁, p₁, hcp', hc₁, hp₁⟩⟩, ho⟩, hφ⟩
      · -- the inner frames' lifetime `α₂`, below `@R`, `α₁` and the callback's bound
        obtain ⟨aR, haR⟩ := R.exists_atLife
        refine ⟨aR ⊓ α₁ ⊓ γH, fun α₂ hα₂ => ⟨?_, outlives_of_atLife haR
          (lt_of_lt_of_le hα₂ (le_trans inf_le_left inf_le_left))⟩⟩
        have hα₂α₁ : α₂ ⊑ α₁ :=
          le_of_lt (lt_of_lt_of_le hα₂ (le_trans inf_le_left inf_le_right))
        have hα₂H : α₂ ⊏ γH := lt_of_lt_of_le hα₂ inf_le_right
        intro ls' hext ρm₂ ρ₃ hm₂ hcm₂
        -- the callback's list is `Ext`-above the original at the outer hypothesis' resource
        have hkH : Ext ls ls' ρH := (hkF.right hF).trans (hext.left hR)
        -- the outer leaf, at `α₂` and at `ls′`, heads the family
        have hlead : immLeafH T ls' δ α₂ ℓ' ρm :=
          immLeaf_ext (hext.right hR) (immLeaf_antitone hα₂α₁ ⟨hrec, hm⟩)
        obtain ⟨X, hX, hρ₃⟩ := compS_reassoc hR hcm₂
        exact (hH α₂ hα₂H).1 ls' hkH X ρ₃ ⟨ρm, ρm₂, hX, hlead, hm₂⟩ hρ₃

/-- **`n` Imm Frames around one expression**: the family is an owned array's range. -/
theorem wpTS_I_frameFam (T : VTy) (δ : LSub) (β : Life)
    (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum β) (hadm : AdmWf T δ) (e : Expr)
    (Φ : List SRec → Val → WProp) (β' : Life) (hΦ : ∀ ls v ρ, Φ ls v ρ → BoLo.Outlives ρ β')
    (hΦext : ∀ ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Φ ls₁ w ρ → Φ ls₂ w ρ)
    (n : Nat) (ℓ : Loc) (ls : List SRec) :
    Entails
      (sepRange (ownLeaf T ls δ) ℓ n ⋆
        fresh (fun α ρ => ∀ ls', Ext ls ls' ρ →
          (sepRange (immLeaf T ls' δ α) ℓ n ─⋆ wpTS ls' e Φ) ρ))
      (wpTS ls e (fun ls' v => sepRange (ownLeaf T ls' δ) ℓ n ⋆ Φ ls' v)) := by
  simp only [sepRange_eq_sepList]
  exact wpTS_I_frameList (fun _ => T) δ β (fun _ => hP) (fun _ => hadm) e Φ β' hΦ hΦext _ ls

end BoCa.Fig16.LogRel.Core.PositiveArrays

end

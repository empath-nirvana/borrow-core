import Core.Chain.SI.Ghost

/-!
# The pair `WRes × GRes`: carrying a lifetime, `WF_C`, masks with their authorities  `[spec §62]`

`docs/new-core/scope-821-loans.md`, stage 1.

* A resource **carries** `α` when its flattening holds an `imm` cell whose lifetime set holds `α`
  (`Carries`). Carrying passes from a part to a composite and back
  (`carries_comp_left`, `carries_comp_split`), since `●` on `imm` cells is the union of their
  lifetime sets over one value and witness (row 5.15) and `○` keeps an `imm` operand.
* **`WF_C`** (`WFC C x`): for every `α ∈ C` that `x` carries, `x` holds a positive fraction of
  `[α]`. `C` is the world's counted set (`GRes.counted`).
* **Masks** are sets of locations with the authority each is masked by: `[α]_1` or `xm`
  (`Mask`, `Auth`). `MaskAuth M g` says `g` holds every authority `M` names.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

/-! ### `imm` cells of a composite's flattening -/

/-- In `σ = e ● a` with `e` `imm`-free, `σ`'s `imm` cells are `a`'s. -/
theorem flat_imm_iff_ag {e a σ : WRes} (hfree : e.ImmFree) (hc : ResU.CompS e a σ) {l : Loc}
    {s : LSet} {v : Val} {χ : WRes} {h : χ.InStratum s.join} :
    σ.get l = some (CellU.immOf s v χ h) ↔ a.get l = some (CellU.immOf s v χ h) := by
  constructor
  · intro hσ
    rcases ResU.Comp.get hc l with ⟨-, -, f⟩ | ⟨ζ, f₁, -, f⟩ | ⟨ζ, -, f₂, f⟩ |
        ⟨ζ₁, ζ₂, ζ, f₁, -, -, hC⟩
    · rw [hσ] at f; cases f
    · rw [hσ] at f
      cases Option.some.inj f
      exact absurd (CellU.kind_immOf _ _ _ _) (hfree l _ f₁)
    · rw [hσ] at f; rw [f₂, Option.some.inj f]
    · obtain ⟨s₁, s₂, v', ρ', k₁, k₂, k₃, e₁, -, -⟩ := hC
      exact absurd (by rw [e₁]; exact CellU.kind_immOf _ _ _ _) (hfree l _ f₁)
  · intro hg
    have hex : e.get l = none := by
      cases f : e.get l with
      | none => rfl
      | some ξ =>
          exact absurd (CellU.CompatS.kinds (hc.1 l ξ _ f hg)).1 (hfree l ξ f)
    rcases ResU.Comp.get hc l with ⟨-, f₂, -⟩ | ⟨ζ, -, f₂, -⟩ | ⟨ζ, -, f₂, f⟩ |
        ⟨ζ₁, ζ₂, ζ, f₁, -, -, -⟩
    · rw [hg] at f₂; exact absurd f₂ (by simp)
    · rw [hg] at f₂; exact absurd f₂ (by simp)
    · exact f.trans (congrArg some (Option.some.inj (f₂.symm.trans hg)))
    · rw [hex] at f₁; exact absurd f₁ (by simp)

/-- **A part's `imm` cell is the composite's, over the same value and witness, at a larger
lifetime set.** -/
theorem flatAt_comp_imm_left {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (hv : ρ.Valid)
    {l : Loc} {s : LSet} {v : Val} {χ : WRes} {h : χ.InStratum s.join}
    (h₁ : ρ₁.FlatAt l (CellU.immOf s v χ h)) :
    ∃ (s' : LSet) (h' : χ.InStratum s'.join), ρ.FlatAt l (CellU.immOf s' v χ h') ∧
      ∀ α, s.mem α → s'.mem α := by
  obtain ⟨σ, hσ⟩ := hv
  obtain ⟨e₁, e₂, e, a₁, a₂, a, σ₁, σ₂, he₁, he₂, hec, ha₁, ha₂, hac, hc', hσ₁, hσ₂⟩ :=
    ResU.Flat.split_factors hc hσ
  have hfree : e.ImmFree := ResU.ImmFree.compS hec (ExS.immFree he₁) (ExS.immFree he₂)
  obtain ⟨σ₁', hσ₁', hg₁⟩ := h₁
  obtain rfl : σ₁' = σ₁ := ResU.Flat.functional hσ₁' ⟨e₁, a₁, he₁, ha₁, hσ₁⟩
  have ha1 := (flat_imm_iff_ag (ExS.immFree he₁) hσ₁).mp hg₁
  have key : ∃ (s' : LSet) (h' : χ.InStratum s'.join),
      a.get l = some (CellU.immOf s' v χ h') ∧ ∀ α, s.mem α → s'.mem α := by
    rcases ResU.Comp.get hac l with ⟨f₁, -, -⟩ | ⟨ζ, f₁, -, f⟩ | ⟨ζ, f₁, -, -⟩ |
        ⟨ζ₁, ζ₂, ζ, f₁, -, f, hC⟩
    · rw [ha1] at f₁; cases f₁
    · rw [ha1] at f₁; cases Option.some.inj f₁
      exact ⟨s, h, f, fun _ x => x⟩
    · rw [ha1] at f₁; cases f₁
    · rw [ha1] at f₁; cases Option.some.inj f₁
      rcases hC.inv with ⟨-, rfl⟩ | ⟨k, rfl⟩ | ⟨a', b', v', ρ', ha', hb', P, Q, hP, hQ, e₁', -, -⟩ |
          ⟨rfl, -, -⟩ | ⟨-, k₁, -⟩ | ⟨rfl, -, -⟩ | ⟨-, k₁, -⟩
      · exact ⟨s, h, f, fun _ x => x⟩
      · obtain ⟨t₁, t₂, w, ρw, k₁, k₂, k₃, e₁', e₂', e₃'⟩ := CellU.compS_spec _ _ k
        obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj e₁'
        exact ⟨s ∪ t₂, k₃, f.trans (congrArg some e₃'), fun _ x => Or.inl x⟩
      · exact absurd e₁' CellU.immOf_ne_mutOf
      · exact ⟨s, h, f, fun _ x => x⟩
      · simp at k₁
      · exact ⟨s, h, f, fun _ x => x⟩
      · simp at k₁
  obtain ⟨s', h', ha', hs'⟩ := key
  exact ⟨s', h', ⟨σ, hσ, (flat_imm_iff_ag hfree hc').mpr ha'⟩, hs'⟩

theorem flatAt_comp_imm_right {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (hv : ρ.Valid)
    {l : Loc} {s : LSet} {v : Val} {χ : WRes} {h : χ.InStratum s.join}
    (h₂ : ρ₂.FlatAt l (CellU.immOf s v χ h)) :
    ∃ (s' : LSet) (h' : χ.InStratum s'.join), ρ.FlatAt l (CellU.immOf s' v χ h') ∧
      ∀ α, s.mem α → s'.mem α :=
  flatAt_comp_imm_left (ResU.CompS.comm hc) hv h₂

/-- **A composite's `imm` cell comes from its parts**: every lifetime it carries is carried, at
the same value and witness, by a part. -/
theorem flatAt_comp_imm_split {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) {l : Loc} {s : LSet}
    {v : Val} {χ : WRes} {h : χ.InStratum s.join} (hρ : ρ.FlatAt l (CellU.immOf s v χ h))
    {α : Life} (hα : s.mem α) :
    (∃ (s₁ : LSet) (h₁ : χ.InStratum s₁.join), ρ₁.FlatAt l (CellU.immOf s₁ v χ h₁) ∧ s₁.mem α) ∨
    (∃ (s₂ : LSet) (h₂ : χ.InStratum s₂.join), ρ₂.FlatAt l (CellU.immOf s₂ v χ h₂) ∧
      s₂.mem α) := by
  obtain ⟨σ, hσ, hg⟩ := hρ
  obtain ⟨e₁, e₂, e, a₁, a₂, a, σ₁, σ₂, he₁, he₂, hec, ha₁, ha₂, hac, hc', hσ₁, hσ₂⟩ :=
    ResU.Flat.split_factors hc hσ
  have hfree : e.ImmFree := ResU.ImmFree.compS hec (ExS.immFree he₁) (ExS.immFree he₂)
  have ha := (flat_imm_iff_ag hfree hc').mp hg
  have L : ∀ {t : LSet} {ht : χ.InStratum t.join},
      a₁.get l = some (CellU.immOf t v χ ht) → ρ₁.FlatAt l (CellU.immOf t v χ ht) :=
    fun hh => ⟨σ₁, ⟨e₁, a₁, he₁, ha₁, hσ₁⟩, (flat_imm_iff_ag (ExS.immFree he₁) hσ₁).mpr hh⟩
  have R : ∀ {t : LSet} {ht : χ.InStratum t.join},
      a₂.get l = some (CellU.immOf t v χ ht) → ρ₂.FlatAt l (CellU.immOf t v χ ht) :=
    fun hh => ⟨σ₂, ⟨e₂, a₂, he₂, ha₂, hσ₂⟩, (flat_imm_iff_ag (ExS.immFree he₂) hσ₂).mpr hh⟩
  rcases ResU.Comp.get hac l with ⟨-, -, f⟩ | ⟨ζ, f₁, -, f⟩ | ⟨ζ, -, f₂, f⟩ |
      ⟨ζ₁, ζ₂, ζ, f₁, f₂, f, hC⟩
  · rw [ha] at f; cases f
  · rw [ha] at f; cases Option.some.inj f
    exact .inl ⟨s, h, L f₁, hα⟩
  · rw [ha] at f; cases Option.some.inj f
    exact .inr ⟨s, h, R f₂, hα⟩
  · rw [ha] at f; cases Option.some.inj f
    rcases hC.inv with ⟨rfl, e'⟩ | ⟨k, e'⟩ | ⟨a', b', v', ρ', ha', hb', P, Q, hP, hQ, -, -, e'⟩ |
        ⟨e', -, -⟩ | ⟨e', -, -⟩ | ⟨e', -, -⟩ | ⟨e', -, -⟩
    · rw [← e'] at f₁; exact .inl ⟨s, h, L f₁, hα⟩
    · obtain ⟨t₁, t₂, w, ρw, k₁, k₂, k₃, e₁', e₂', e₃'⟩ := CellU.compS_spec _ _ k
      rw [← e'] at e₃'
      obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj e₃'
      rcases hα with hα | hα
      · rw [e₁'] at f₁; exact .inl ⟨t₁, k₁, L f₁, hα⟩
      · rw [e₂'] at f₂; exact .inr ⟨t₂, k₂, R f₂, hα⟩
    · exact absurd e' CellU.immOf_ne_mutOf
    · rw [← e'] at f₁; exact .inl ⟨s, h, L f₁, hα⟩
    · rw [← e'] at f₂; exact .inr ⟨s, h, R f₂, hα⟩
    · rw [← e'] at f₁; exact .inl ⟨s, h, L f₁, hα⟩
    · rw [← e'] at f₂; exact .inr ⟨s, h, R f₂, hα⟩

/-! ### Carrying a lifetime -/

/-- `ρ` **carries** `α`: its flattening holds an `imm` cell whose lifetime set holds `α`. -/
def Carries (ρ : WRes) (α : Life) : Prop :=
  ∃ (l : Loc) (s : LSet) (v : Val) (χ : WRes) (h : χ.InStratum s.join),
    ρ.FlatAt l (CellU.immOf s v χ h) ∧ s.mem α

theorem carries_comp_left {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (hv : ρ.Valid) {α : Life}
    (h : Carries ρ₁ α) : Carries ρ α := by
  obtain ⟨l, s, v, χ, hh, hf, hm⟩ := h
  obtain ⟨s', h', hf', hs⟩ := flatAt_comp_imm_left hc hv hf
  exact ⟨l, s', v, χ, h', hf', hs α hm⟩

theorem carries_comp_right {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (hv : ρ.Valid) {α : Life}
    (h : Carries ρ₂ α) : Carries ρ α :=
  carries_comp_left (ResU.CompS.comm hc) hv h

theorem carries_comp_split {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) {α : Life}
    (h : Carries ρ α) : Carries ρ₁ α ∨ Carries ρ₂ α := by
  obtain ⟨l, s, v, χ, hh, hf, hm⟩ := h
  rcases flatAt_comp_imm_split hc hf hm with ⟨s₁, h₁, hf₁, hm₁⟩ | ⟨s₂, h₂, hf₂, hm₂⟩
  · exact .inl ⟨l, s₁, v, χ, h₁, hf₁, hm₁⟩
  · exact .inr ⟨l, s₂, v, χ, h₂, hf₂, hm₂⟩

theorem not_carries_empty (α : Life) : ¬ Carries (PMap.empty : WRes) α := by
  rintro ⟨l, s, v, χ, hh, ⟨σ, hσ, hg⟩, -⟩
  obtain rfl := ResU.Flat.functional hσ flat_empty
  rw [PMap.empty_get] at hg
  cases hg

/-- `↭`'s `imm` clause keeps what is carried, both ways. -/
theorem carries_of_updImmM {M : Set Loc} {ρ₁ ρ₂ : WRes} (h : UpdImmM M ρ₁ ρ₂) {α : Life}
    (hc : Carries ρ₂ α)
    (hM : ∀ l s v χ hh, ρ₂.FlatAt l (CellU.immOf s v χ hh) → s.mem α → l ∉ M) :
    Carries ρ₁ α := by
  obtain ⟨l, s, v, χ, hh, hf, hm⟩ := hc
  exact ⟨l, s, v, χ, hh, (h l (hM l s v χ hh hf hm) s v χ hh).mpr hf, hm⟩

/-! ### Shallowness of composites -/

theorem maskShallow_comp {M : Set Loc} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h₁ : MaskShallow M ρ₁) (h₂ : MaskShallow M ρ₂) : MaskShallow M ρ := by
  intro l hl s v χ hh hf
  rcases flatAt_comp_imm_split hc hf s.join_mem with ⟨s₁, k₁, hf₁, -⟩ | ⟨s₂, k₂, hf₂, -⟩
  · exact h₁ l hl s₁ v χ k₁ hf₁
  · exact h₂ l hl s₂ v χ k₂ hf₂

theorem maskShallow_left {M : Set Loc} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (hv : ρ.Valid) (h : MaskShallow M ρ) : MaskShallow M ρ₁ := by
  intro l hl s v χ hh hf
  obtain ⟨s', h', hf', -⟩ := flatAt_comp_imm_left hc hv hf
  exact h l hl s' v χ h' hf'

theorem maskShallow_right {M : Set Loc} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (hv : ρ.Valid) (h : MaskShallow M ρ) : MaskShallow M ρ₂ :=
  maskShallow_left (ResU.CompS.comm hc) hv h

/-! ### `WF_C` -/

/-- A resource of the one relation. -/
abbrev XRes : Type := WRes × GRes

/-- **`WF_C`**: for every counted `α` the part carries, it holds a positive fraction of `[α]`. -/
def WFC (C : Set Life) (x : XRes) : Prop := ∀ α, α ∈ C → Carries x.1 α → 0 < x.2.tok α

/-- No lifetime counted at the end and not at the start is carried by `ρ`: what keeps a fixed
frame `WF_C` when the counted set grows. -/
def NewNotCarried (C C' : Set Life) (ρ : WRes) : Prop :=
  ∀ α, α ∈ C' → α ∉ C → ¬ Carries ρ α

theorem WFC.mono {C C' : Set Life} (hC : C' ⊆ C) {x : XRes} (h : WFC C x) : WFC C' x :=
  fun α hα hc => h α (hC hα) hc

theorem wfc_empty (x : XRes) : WFC ∅ x := fun _ h => absurd h (by simp)

/-- A ghost-free resource is `WF_C` where it carries nothing counted. -/
theorem wfc_zero {C : Set Life} {ρ : WRes} (h : ∀ α, α ∈ C → ¬ Carries ρ α) : WFC C (ρ, 0) :=
  fun α hα hc => absurd hc (h α hα)

/-- `WF_C` of a composite from its parts. -/
theorem wfc_comp {C : Set Life} {ρ₁ ρ₂ ρ : WRes} {g₁ g₂ : GRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h₁ : WFC C (ρ₁, g₁)) (h₂ : WFC C (ρ₂, g₂)) : WFC C (ρ, g₁ + g₂) := by
  intro α hα hcar
  show 0 < g₁.tok α + g₂.tok α
  rcases carries_comp_split hc hcar with h | h
  · exact lt_of_lt_of_le (h₁ α hα h) le_self_add
  · exact lt_of_lt_of_le (h₂ α hα h) le_add_self

/-- A fixed frame stays `WF_C` as the counted set grows, when it carries nothing new. -/
theorem wfc_grow {C C' : Set Life} {x : XRes} (h : WFC C x) (hn : NewNotCarried C C' x.1) :
    WFC C' x := by
  intro α hα hc
  by_cases hαC : α ∈ C
  · exact h α hαC hc
  · exact absurd hc (hn α hα hαC)

/-! ### Masks -/

/-- What masks a location: a whole lifetime token, or a `mut` authority. -/
inductive Auth where
  | life (α : Life)
  | xm

/-- A mask: locations, each with the authority it is masked by. -/
abbrev Mask : Type := Set (Loc × Auth)

/-- The masked locations. -/
def Mask.locs (M : Mask) : Set Loc := {l | ∃ a, (l, a) ∈ M}

/-- `g` holds the authority `a` at `l`. -/
def Auth.Held (g : GRes) (l : Loc) : Auth → Prop
  | .life α => g.tok α = 1
  | .xm => g.xm l = 1

/-- **The mask's authorities are held**: by `g`, at every location `M` masks. -/
def MaskAuth (M : Mask) (g : GRes) : Prop := ∀ l a, (l, a) ∈ M → a.Held g l

theorem maskAuth_empty (g : GRes) : MaskAuth ∅ g := fun _ _ h => absurd h (by simp)

@[simp] theorem Mask.locs_empty : (∅ : Mask).locs = ∅ := by
  ext l; simp [Mask.locs]

/-- An authority a part holds, a valid sum holds. -/
theorem Auth.Held.add_right {g h : GRes} (hv : (g + h).Valid) {l : Loc} {a : Auth}
    (ha : a.Held g l) : a.Held (g + h) l := by
  cases a with
  | life α => exact GRes.tok_one_of_add hv ha
  | xm => exact GRes.xm_one_of_add hv ha

theorem MaskAuth.add_right {M : Mask} {g h : GRes} (hv : (g + h).Valid) (hm : MaskAuth M g) :
    MaskAuth M (g + h) :=
  fun l a hla => (hm l a hla).add_right hv

end BoCa.Fig16.LogRel.Core.Chain.SI

end

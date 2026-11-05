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

/-- What masks a location: a whole lifetime token, a `mut` authority, or the authority of a
loan held across stops: an `imm` lend (`lend κ`) or a `mut` loan (`mloan κ`), each held by a whole
token `[κ]_1` that the lender keeps for as long as it holds the location. -/
inductive Auth where
  | life (α : Life)
  | xm
  | lend (κ : Life)
  | mloan (κ : Life)

/-- A mask: locations, each with the authority it is masked by. -/
abbrev Mask : Type := Set (Loc × Auth)

/-- The masked locations. -/
def Mask.locs (M : Mask) : Set Loc := {l | ∃ a, (l, a) ∈ M}

/-- The locations masked by an `imm` lend held across stops. -/
def Mask.lendLocs (M : Mask) : Set Loc := {l | ∃ κ, (l, Auth.lend κ) ∈ M}

@[simp] theorem Mask.lendLocs_empty : (∅ : Mask).lendLocs = ∅ := by
  ext l; simp [Mask.lendLocs]

/-- `g` holds the authority `a` at `l`. -/
def Auth.Held (g : GRes) (l : Loc) : Auth → Prop
  | .life α => g.tok α = 1
  | .xm => g.xm l = 1
  | .lend κ => g.tok κ = 1
  | .mloan κ => g.tok κ = 1

/-- **The mask's authorities are held**: by `g`, at every location `M` masks. -/
def MaskAuth (M : Mask) (g : GRes) : Prop := ∀ l a, (l, a) ∈ M → a.Held g l

theorem maskAuth_empty (g : GRes) : MaskAuth ∅ g := fun _ _ h => absurd h (by simp)

@[simp] theorem Mask.locs_empty : (∅ : Mask).locs = ∅ := by
  ext l; simp [Mask.locs]

theorem maskShallow_locs_empty (ρ : WRes) : MaskShallow (∅ : Mask).locs ρ := by
  rw [Mask.locs_empty]; exact maskShallow_empty ρ

/-- An authority a part holds, a valid sum holds. -/
theorem Auth.Held.add_right {g h : GRes} (hv : (g + h).Valid) {l : Loc} {a : Auth}
    (ha : a.Held g l) : a.Held (g + h) l := by
  cases a with
  | life α => exact GRes.tok_one_of_add hv ha
  | xm => exact GRes.xm_one_of_add hv ha
  | lend κ => exact GRes.tok_one_of_add hv ha
  | mloan κ => exact GRes.tok_one_of_add hv ha

theorem MaskAuth.add_right {M : Mask} {g h : GRes} (hv : (g + h).Valid) (hm : MaskAuth M g) :
    MaskAuth M (g + h) :=
  fun l a hla => (hm l a hla).add_right hv

/-- A ghost-free resource holds no authority, so the only mask it runs at is empty. -/
theorem MaskAuth.zero {M : Mask} (h : MaskAuth M 0) : M = ∅ := by
  ext ⟨l, a⟩
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hla
  have := h l a hla
  cases a <;> simp [Auth.Held] at this

/-! ### What a frame may hold at a lent location -/

/-- **At a location lent `imm` across stops, the part holds only copies**: every cell of its
flattening there is `imm`. The lender alone holds the location's `own` cell or `mut` cells, at any
depth. -/
def MaskOff (M : Mask) (ρ : WRes) : Prop :=
  ∀ l, l ∈ M.lendLocs → ∀ ψ, ρ.FlatAt l ψ → ψ.kind = Kind.imm

theorem maskOff_empty (ρ : WRes) : MaskOff ∅ ρ := fun _ h => by simp at h

theorem maskOff_emptyRes (M : Mask) : MaskOff M (PMap.empty : WRes) := by
  intro l _ ψ ⟨σ, hσ, hg⟩
  obtain rfl := ResU.Flat.functional hσ flat_empty
  rw [PMap.empty_get] at hg; cases hg

/-- `○` of two `imm` cells is `imm`. -/
theorem CellU.CompR.kind_imm {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompR ψ₁ ψ₂ ψ)
    (h₁ : ψ₁.kind = Kind.imm) (h₂ : ψ₂.kind = Kind.imm) : ψ.kind = Kind.imm := by
  cases h with
  | same => exact h₁
  | strict k =>
      obtain ⟨s₁, s₂, w, τ, k₁, k₂, k₃, f₁, f₂, f₃⟩ := CellU.compS_spec _ _ k
      rw [f₃]; exact CellU.kind_immOf _ _ _ _
  | mutMut => simp at h₁
  | mutOwn => simp at h₁
  | ownMut => simp at h₁
  | immOwn => simp at h₂
  | ownImm => simp at h₁
  | immMut => simp at h₂
  | mutImm => simp at h₁

/-- `MaskOff` of a composite from its parts: `⦇ρ₁ ● ρ₂⦈ = ⦇ρ₁⦈ ○ ⦇ρ₂⦈`. -/
theorem maskOff_comp {M : Mask} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h₁ : MaskOff M ρ₁) (h₂ : MaskOff M ρ₂) : MaskOff M ρ := by
  intro l hl ψ ⟨σ, hσ, hg⟩
  obtain ⟨σ₁, σ₂, hσ₁, hσ₂, hR⟩ := flat_compR hc hσ
  rcases ResU.Comp.get hR l with ⟨-, -, e⟩ | ⟨ζ, f₁, -, e⟩ | ⟨ζ, -, f₂, e⟩ |
      ⟨ζ₁, ζ₂, ζ, f₁, f₂, e, hC⟩
  · rw [hg] at e; cases e
  · rw [hg] at e; cases Option.some.inj e; exact h₁ l hl _ ⟨σ₁, hσ₁, f₁⟩
  · rw [hg] at e; cases Option.some.inj e; exact h₂ l hl _ ⟨σ₂, hσ₂, f₂⟩
  · rw [hg] at e; cases Option.some.inj e
    exact CellU.CompR.kind_imm hC (h₁ l hl _ ⟨σ₁, hσ₁, f₁⟩) (h₂ l hl _ ⟨σ₂, hσ₂, f₂⟩)

/-! ### The records outside the lent locations -/

/-- Two record lists agree at every record not at a location lent across stops. -/
def RecAgree (M : Mask) (ps' ps : List FrameRec) : Prop :=
  ∀ p, p.le ∉ M.lendLocs → (p ∈ ps' ↔ p ∈ ps)

/-- Two tagged lists agree at every entry whose record is not at a location lent across stops. -/
def ListAgree (M : Mask) (ls' ls : List SRec) : Prop :=
  ∀ y, y.1.le ∉ M.lendLocs → (y ∈ ls' ↔ y ∈ ls)

theorem RecAgree.refl (M : Mask) (ps : List FrameRec) : RecAgree M ps ps := fun _ _ => Iff.rfl

theorem ListAgree.refl (M : Mask) (ls : List SRec) : ListAgree M ls ls := fun _ _ => Iff.rfl

theorem RecAgree.trans {M : Mask} {a b c : List FrameRec} (h₁ : RecAgree M a b)
    (h₂ : RecAgree M b c) : RecAgree M a c := fun p hp => (h₁ p hp).trans (h₂ p hp)

theorem ListAgree.trans {M : Mask} {a b c : List SRec} (h₁ : ListAgree M a b)
    (h₂ : ListAgree M b c) : ListAgree M a c := fun y hy => (h₁ y hy).trans (h₂ y hy)

theorem RecAgree.of_iff {M : Mask} {ps' ps : List FrameRec} (h : ∀ p, p ∈ ps' ↔ p ∈ ps) :
    RecAgree M ps' ps := fun p _ => h p

theorem ListAgree.of_iff {M : Mask} {ls' ls : List SRec} (h : ∀ y, y ∈ ls' ↔ y ∈ ls) :
    ListAgree M ls' ls := fun y _ => h y

theorem RecAgree.empty_iff {ps' ps : List FrameRec} :
    RecAgree ∅ ps' ps ↔ ∀ p, p ∈ ps' ↔ p ∈ ps :=
  ⟨fun h p => h p (by simp), RecAgree.of_iff⟩

theorem ListAgree.empty_iff {ls' ls : List SRec} :
    ListAgree ∅ ls' ls ↔ ∀ y, y ∈ ls' ↔ y ∈ ls :=
  ⟨fun h y => h y (by simp), ListAgree.of_iff⟩

/-! ### The mask a stop resumes at

A segment runs at its mask `M`; its stop names the mask `M′` its continuation resumes at
(`EndOKX`). `M′` is new against `M` at `M.fresh M′`: the locations `M′` masks and `M` does not,
and the locations `M′` lends across stops and `M` does not. At those the segment's frame holds
nothing (`FlatNone`), as a name Iris allocates is fresh. -/

@[simp] theorem Mask.locs_union (M M' : Mask) : (M ∪ M').locs = M.locs ∪ M'.locs := by
  ext l; simp [Mask.locs, exists_or]

@[simp] theorem Mask.lendLocs_union (M M' : Mask) :
    (M ∪ M').lendLocs = M.lendLocs ∪ M'.lendLocs := by
  ext l; simp [Mask.lendLocs, exists_or]

theorem Mask.lendLocs_mono {M M' : Mask} (h : M ⊆ M') : M.lendLocs ⊆ M'.lendLocs :=
  fun _ ⟨κ, hκ⟩ => ⟨κ, h hκ⟩

theorem Mask.locs_mono {M M' : Mask} (h : M ⊆ M') : M.locs ⊆ M'.locs :=
  fun _ ⟨a, ha⟩ => ⟨a, h ha⟩

/-- **What a stop's mask `M′` masks that the segment's mask `M` does not.** -/
def Mask.fresh (M M' : Mask) : Set Loc := (M'.locs \ M.locs) ∪ (M'.lendLocs \ M.lendLocs)

@[simp] theorem Mask.fresh_self (M : Mask) : M.fresh M = ∅ := by
  ext l; simp [Mask.fresh]

theorem Mask.locs_sub_fresh (M M' : Mask) : M'.locs ⊆ M.locs ∪ M.fresh M' := by
  intro l hl
  by_cases h : l ∈ M.locs
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨hl, h⟩)

theorem Mask.lendLocs_sub_fresh (M M' : Mask) : M'.lendLocs ⊆ M.lendLocs ∪ M.fresh M' := by
  intro l hl
  by_cases h : l ∈ M.lendLocs
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨hl, h⟩)

/-- `ρ`'s flattening holds nothing at `L`. -/
def FlatNone (L : Set Loc) (ρ : WRes) : Prop := ∀ l, l ∈ L → ∀ ψ, ¬ ρ.FlatAt l ψ

theorem flatNone_empty (ρ : WRes) : FlatNone ∅ ρ := fun _ h => absurd h (by simp)

theorem FlatNone.mono {L L' : Set Loc} (hL : L' ⊆ L) {ρ : WRes} (h : FlatNone L ρ) :
    FlatNone L' ρ := fun l hl => h l (hL hl)

/-- A part's cell is under a cell of the composite: `⦇ρ₁ ● ρ₂⦈ = ⦇ρ₁⦈ ○ ⦇ρ₂⦈`. -/
theorem flatAt_comp_defined_left {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (hv : ρ.Valid)
    {l : Loc} {ψ : CellU Loc Val} (h : ρ₁.FlatAt l ψ) : ∃ ψ', ρ.FlatAt l ψ' := by
  obtain ⟨σ, hσ⟩ := hv
  obtain ⟨σ₁, σ₂, hσ₁, hσ₂, hR⟩ := flat_compR hc hσ
  obtain ⟨σ₁', hσ₁', hg⟩ := h
  obtain rfl := ResU.Flat.functional hσ₁' hσ₁
  rcases ResU.Comp.get hR l with ⟨f₁, -, -⟩ | ⟨ζ, -, -, f⟩ | ⟨ζ, f₁, -, -⟩ |
      ⟨ζ₁, ζ₂, ζ, -, -, f, -⟩
  · rw [hg] at f₁; cases f₁
  · exact ⟨ζ, σ, hσ, f⟩
  · rw [hg] at f₁; cases f₁
  · exact ⟨ζ, σ, hσ, f⟩

theorem FlatNone.left {L : Set Loc} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (hv : ρ.Valid)
    (h : FlatNone L ρ) : FlatNone L ρ₁ := by
  intro l hl ψ hψ
  obtain ⟨ψ', hψ'⟩ := flatAt_comp_defined_left hc hv hψ
  exact h l hl ψ' hψ'

theorem FlatNone.right {L : Set Loc} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (hv : ρ.Valid)
    (h : FlatNone L ρ) : FlatNone L ρ₂ :=
  FlatNone.left (ResU.CompS.comm hc) hv h

theorem FlatNone.maskShallow {L : Set Loc} {ρ : WRes} (h : FlatNone L ρ) : MaskShallow L ρ :=
  fun l hl _ _ _ _ hf => absurd hf (h l hl _)

theorem maskShallow_union {A B : Set Loc} {ρ : WRes} (hA : MaskShallow A ρ)
    (hB : MaskShallow B ρ) : MaskShallow (A ∪ B) ρ := by
  intro l hl
  rcases hl with hl | hl
  · exact hA l hl
  · exact hB l hl

theorem MaskShallow.mono {A B : Set Loc} (hAB : A ⊆ B) {ρ : WRes} (h : MaskShallow B ρ) :
    MaskShallow A ρ := fun l hl => h l (hAB hl)

/-- `ρ` is shallow at the stop's mask when it is at the segment's and holds nothing new. -/
theorem maskShallow_fresh {M M' : Mask} {ρ : WRes} (h : MaskShallow M.locs ρ)
    (hn : FlatNone (M.fresh M') ρ) : MaskShallow M'.locs ρ :=
  MaskShallow.mono (Mask.locs_sub_fresh M M') (maskShallow_union h hn.maskShallow)

/-- `MaskOff` at the stop's mask, from the segment's and nothing new. -/
theorem maskOff_fresh {M M' : Mask} {ρ : WRes} (h : MaskOff M ρ) (hn : FlatNone (M.fresh M') ρ) :
    MaskOff M' ρ := by
  intro l hl ψ hψ
  rcases Mask.lendLocs_sub_fresh M M' hl with hl | hl
  · exact h l hl ψ hψ
  · exact absurd hψ (hn l hl ψ)

theorem RecAgree.mono {M M' : Mask} (hM : M.lendLocs ⊆ M'.lendLocs) {a b : List FrameRec}
    (h : RecAgree M a b) : RecAgree M' a b := fun p hp => h p (fun h' => hp (hM h'))

theorem ListAgree.mono {M M' : Mask} (hM : M.lendLocs ⊆ M'.lendLocs) {a b : List SRec}
    (h : ListAgree M a b) : ListAgree M' a b := fun y hy => h y (fun h' => hy (hM h'))

end BoCa.Fig16.LogRel.Core.Chain.SI

end

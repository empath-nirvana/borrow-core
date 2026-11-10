import LicUpd.Refute

/-!
# LicUpd — the growth clause (#1007)

The source is theory's `imm-getter-growth.md`. Two definitions change G1:
- **`DerLt`**: derivability is read per lifetime. `base` takes a lifetime of an `imm` cell of
  `σ` at `l`, with its value and witness. `proj` is one projection step taken one lifetime at a
  time.
- **`UpdImmG`**, the growth clause, has two directions:
  - (→) a start `imm` cell persists, with the same value and witness, and its lifetime set may
    only grow;
  - (←) every lifetime of an end `imm` cell at `(l, v, χ)` is a start lifetime there, or is
    `DerLt` from the start's flattening.

`UpdG` is `UpdImmG` with `↭`'s `mut` clause unchanged. `UpdVG` adds validity.

Proved here:
- the bridge from G1 (`Derivable.derLt`, `UpdImmG.of_lic`) and conservativity
  (`UpdVG.of_updV`);
- transitivity (`UpdImmG.trans`, `UpdVG.trans`);
- 6.48's `imm` half under growth (`updImmG_frame`), from the cell facts (C2) (`compR_get_grow_left`,
  `compR_get_imm_source`, `compR_get_imm_cover`) and the monotonicity (M) (`DerLt.mono`);
- `licFrame_fails`'s configuration, now accepted (`k7_accepted`).
-/

noncomputable section

namespace BoCa.Fig16.LicUpd
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

/-! ### Per-lifetime derivability -/

/-- `x` is a derivable lifetime at `l` for value `v` and witness `w`, from the flattening `σ`. -/
inductive DerLt (σ : WRes) : Loc → Val → WRes → Life → Prop
  | base {l : Loc} {s : LSet} {v : Val} {w : WRes} {h : w.InStratum s.join} {x : Life} :
      σ.get l = some (CellU.immOf s v w h) → s.mem x → DerLt σ l v w x
  | proj {m l : Loc} {u v : Val} {χ w : WRes} {y x : Life} :
      DerLt σ m u χ y → χ.get l = some (CellU.ownOf v) → ResU.Le w χ → x ≤ y →
      DerLt σ l v w x

theorem DerLt.root {σ : WRes} {l : Loc} {v : Val} {w : WRes} {x : Life} (h : DerLt σ l v w x) :
    ∃ (m : Loc) (s : LSet) (u : Val) (χ : WRes) (hχ : χ.InStratum s.join),
      σ.get m = some (CellU.immOf s u χ hχ) := by
  induction h with
  | base e _ => exact ⟨_, _, _, _, _, e⟩
  | proj _ _ _ _ ih => exact ih

/-- **`DerLt` is a closure.** -/
theorem DerLt.trans {σ₀ σ₁ : WRes}
    (H : ∀ (l : Loc) (s : LSet) (v : Val) (w : WRes) (h : w.InStratum s.join) (x : Life),
      σ₁.get l = some (CellU.immOf s v w h) → s.mem x → DerLt σ₀ l v w x)
    {l : Loc} {v : Val} {w : WRes} {x : Life} (h : DerLt σ₁ l v w x) : DerLt σ₀ l v w x := by
  induction h with
  | base e hx => exact H _ _ _ _ _ _ e hx
  | proj _ hl hle hxy ih => exact DerLt.proj ih hl hle hxy

/-- **(M)** `DerLt` is monotone along an inclusion of `imm` lifetimes at each
(location, value, witness). -/
theorem DerLt.mono {σ σ' : WRes}
    (H : ∀ (l : Loc) (s : LSet) (v : Val) (w : WRes) (h : w.InStratum s.join) (x : Life),
      σ.get l = some (CellU.immOf s v w h) → s.mem x →
      ∃ (s' : LSet) (h' : w.InStratum s'.join), σ'.get l = some (CellU.immOf s' v w h') ∧ s'.mem x)
    {l : Loc} {v : Val} {w : WRes} {x : Life} (hd : DerLt σ l v w x) : DerLt σ' l v w x := by
  refine DerLt.trans (fun l s v w h x e hx => ?_) hd
  obtain ⟨s', h', e', hx'⟩ := H l s v w h x e hx
  exact DerLt.base e' hx'

/-- G1's set-level `Derivable` gives `DerLt` at each lifetime. -/
theorem Derivable.derLt {σ : WRes} {l : Loc} {ψ : CellU Loc Val} (hd : Derivable σ l ψ) :
    ∀ (t : LSet) (v : Val) (w : WRes) (h : w.InStratum t.join), ψ = CellU.immOf t v w h →
      ∀ x, t.mem x → DerLt σ l v w x := by
  induction hd with
  | base e _ =>
      intro t v w h hψ x hx
      subst hψ
      exact DerLt.base e hx
  | proj _ hl ht hle ih =>
      intro t' v' w' h' hψ x hx
      obtain ⟨rfl, rfl, rfl⟩ := CellU.immOf_inj hψ
      obtain ⟨y, hy, hxy⟩ := ht x hx
      exact DerLt.proj (ih _ _ _ _ rfl y hy) hl hle hxy

/-! ### The growth clause -/

def UpdImmG (ρ₁ ρ₂ : WRes) : Prop :=
  (∀ (l : Loc) (s : LSet) (v : Val) (χ : WRes) (h : χ.InStratum s.join),
    ρ₁.FlatAt l (CellU.immOf s v χ h) →
      ∃ (s' : LSet) (h' : χ.InStratum s'.join), (∀ x, s.mem x → s'.mem x) ∧
        ρ₂.FlatAt l (CellU.immOf s' v χ h')) ∧
  (∀ (l : Loc) (s' : LSet) (v : Val) (χ : WRes) (h' : χ.InStratum s'.join),
    ρ₂.FlatAt l (CellU.immOf s' v χ h') → ∀ x, s'.mem x →
      (∃ (s : LSet) (h : χ.InStratum s.join), ρ₁.FlatAt l (CellU.immOf s v χ h) ∧ s.mem x) ∨
      (∃ σ₁, ResU.Flat ρ₁ σ₁ ∧ DerLt σ₁ l v χ x))

def UpdG (ρ₁ ρ₂ : WRes) : Prop := UpdImmG ρ₁ ρ₂ ∧ ResU.UpdMut ρ₁ ρ₂

def UpdVG (ρ₁ ρ₂ : WRes) : Prop := UpdG ρ₁ ρ₂ ∧ ρ₁.Valid ∧ ρ₂.Valid

theorem UpdImmG.of_updImm {ρ₁ ρ₂ : WRes} (h : ResU.UpdImm ρ₁ ρ₂) : UpdImmG ρ₁ ρ₂ :=
  ⟨fun l s v χ hs hf => ⟨s, hs, fun _ hx => hx, (h l s v χ hs).mp hf⟩,
    fun l s v χ hs hf x hx => Or.inl ⟨s, hs, (h l s v χ hs).mpr hf, hx⟩⟩

theorem UpdVG.of_updV {ρ₁ ρ₂ : WRes} (h : ResU.UpdV ρ₁ ρ₂) : UpdVG ρ₁ ρ₂ :=
  ⟨⟨UpdImmG.of_updImm h.1.1, h.1.2⟩, h.2⟩

/-- G1 is a case of the growth clause. -/
theorem UpdImmG.of_lic {ρ₁ ρ₂ : WRes} (h : UpdImmLic ρ₁ ρ₂) : UpdImmG ρ₁ ρ₂ := by
  refine ⟨fun l s v χ hs hf => ⟨s, hs, fun _ hx => hx, h.1 l s v χ hs hf⟩,
    fun l s v χ hs hf x hx => ?_⟩
  rcases h.2 l s v χ hs hf with h' | ⟨σ, hσ, hd⟩
  · exact Or.inl ⟨s, hs, h', hx⟩
  · exact Or.inr ⟨σ, hσ, hd.derLt s v χ hs rfl x hx⟩

theorem UpdVG.of_lic {ρ₁ ρ₂ : WRes} (h : UpdVLic ρ₁ ρ₂) : UpdVG ρ₁ ρ₂ :=
  ⟨⟨UpdImmG.of_lic h.1.1, h.1.2⟩, h.2⟩

/-! ### Transitivity -/

theorem UpdImmG.trans {ρ₀ ρ₁ ρ₂ : WRes} (h₁ : UpdImmG ρ₀ ρ₁) (h₂ : UpdImmG ρ₁ ρ₂) :
    UpdImmG ρ₀ ρ₂ := by
  refine ⟨fun l s v χ hs hf => ?_, fun l s v χ hs hf x hx => ?_⟩
  · obtain ⟨s₁, hs₁, hsub₁, hf₁⟩ := h₁.1 l s v χ hs hf
    obtain ⟨s₂, hs₂, hsub₂, hf₂⟩ := h₂.1 l s₁ v χ hs₁ hf₁
    exact ⟨s₂, hs₂, fun y hy => hsub₂ y (hsub₁ y hy), hf₂⟩
  · rcases h₂.2 l s v χ hs hf x hx with ⟨s₁, hs₁, hf₁, hx₁⟩ | ⟨σ₁, hσ₁, hd⟩
    · exact h₁.2 l s₁ v χ hs₁ hf₁ x hx₁
    · obtain ⟨m, s₀, u, χ₀, hχ₀, e₀⟩ := hd.root
      obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, ResU.Flat ρ₀ σ₀ := by
        rcases h₁.2 m s₀ u χ₀ hχ₀ ⟨σ₁, hσ₁, e₀⟩ s₀.meet s₀.meet_mem with
            ⟨_, _, ⟨σ, hσ, -⟩, -⟩ | ⟨σ, hσ, -⟩
        · exact ⟨σ, hσ⟩
        · exact ⟨σ, hσ⟩
      refine Or.inr ⟨σ₀, hσ₀, DerLt.trans (fun l' s' v' w' h' y e hy => ?_) hd⟩
      rcases h₁.2 l' s' v' w' h' ⟨σ₁, hσ₁, e⟩ y hy with ⟨s₀', h₀', ⟨σ, hσ, e'⟩, hy'⟩ |
          ⟨σ, hσ, hd'⟩
      · rw [ResU.Flat.functional hσ hσ₀] at e'
        exact DerLt.base e' hy'
      · rw [ResU.Flat.functional hσ hσ₀] at hd'
        exact hd'

theorem UpdG.trans {ρ₀ ρ₁ ρ₂ : WRes} (h₁ : UpdG ρ₀ ρ₁) (h₂ : UpdG ρ₁ ρ₂) : UpdG ρ₀ ρ₂ :=
  ⟨h₁.1.trans h₂.1, fun l b P => (h₁.2 l b P).trans (h₂.2 l b P)⟩

theorem UpdVG.trans {ρ₀ ρ₁ ρ₂ : WRes} (h₁ : UpdVG ρ₀ ρ₁) (h₂ : UpdVG ρ₁ ρ₂) : UpdVG ρ₀ ρ₂ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1, h₂.2.2⟩

/-! ### (C2): composition keeps an `imm` cell's value and witness and grows its lifetimes -/

/-- An `imm` left operand of `○` comes back as an `imm` cell over the same value and witness,
with at least its lifetimes. -/
theorem compR_imm_grow_left {ψ₁ ψ₂ ψ : CellU Loc Val} (hc : CellU.CompR ψ₁ ψ₂ ψ)
    {s₁ : LSet} {v : Val} {χ : WRes} {h₁ : χ.InStratum s₁.join}
    (e : ψ₁ = CellU.immOf s₁ v χ h₁) :
    ∃ (s : LSet) (h : χ.InStratum s.join), ψ = CellU.immOf s v χ h ∧
      ∀ x, s₁.mem x → s.mem x := by
  obtain ⟨s, h, hψ⟩ := CellU.CompR.imm_left_eq hc e
  exact ⟨s, h, hψ, fun x hx => CellU.CompR.ls_imm hc e hψ hx⟩

/-- An operand of `○` with a lifetime set, under an `imm` composite, is an `imm` cell over the
composite's value and witness. -/
theorem imm_of_lsOf_left {ψ₁ ψ₂ : CellU Loc Val} {s : LSet} {v : Val} {χ : WRes}
    {h : χ.InStratum s.join} (hc : CellU.CompR ψ₁ ψ₂ (CellU.immOf s v χ h)) {t : LSet}
    (ht : ψ₁.lsOf = some t) : ∃ h₁ : χ.InStratum t.join, ψ₁ = CellU.immOf t v χ h₁ := by
  rcases CellU.rep ψ₁ with ⟨u, rfl⟩ | ⟨s₁, v₁, χ₁, h₁, rfl⟩ | ⟨b, v₁, χ₁, h₁, P, hw, rfl⟩
  · simp at ht
  · rw [CellU.lsOf_immOf] at ht
    cases Option.some.inj ht
    obtain ⟨-, he, hw⟩ := CellU.CompR.imm_left hc (CellU.kind_immOf _ _ _ _)
    simp only [CellU.erase_immOf, CellU.wit_immOf] at he hw
    subst he
    subst hw
    exact ⟨h₁, rfl⟩
  · simp at ht

/-- Each lifetime of an `imm` composite of `○` is a lifetime of an `imm` operand over the same
value and witness. -/
theorem compR_imm_source_mem {ψ₁ ψ₂ : CellU Loc Val} {s : LSet} {v : Val} {χ : WRes}
    {h : χ.InStratum s.join} (hc : CellU.CompR ψ₁ ψ₂ (CellU.immOf s v χ h)) {x : Life}
    (hx : s.mem x) :
    (∃ (s₁ : LSet) (h₁ : χ.InStratum s₁.join), ψ₁ = CellU.immOf s₁ v χ h₁ ∧ s₁.mem x) ∨
    (∃ (s₂ : LSet) (h₂ : χ.InStratum s₂.join), ψ₂ = CellU.immOf s₂ v χ h₂ ∧ s₂.mem x) := by
  rcases CellU.CompR.lsOf_inv hc (CellU.lsOf_immOf _ _ _ _) hx with ⟨t, ht, hxt⟩ | ⟨t, ht, hxt⟩
  · obtain ⟨h₁, e⟩ := imm_of_lsOf_left hc ht
    exact Or.inl ⟨t, h₁, e, hxt⟩
  · obtain ⟨h₂, e⟩ := imm_of_lsOf_left (CellU.CompR.comm hc) ht
    exact Or.inr ⟨t, h₂, e, hxt⟩

/-- At the resource level: an `imm` cell of the left operand grows into the composite. -/
theorem compR_get_grow_left {a₁ a₃ a' : WRes} (hc : ResU.CompR a₁ a₃ a') {l : Loc}
    {s₁ : LSet} {v : Val} {χ : WRes} {h₁ : χ.InStratum s₁.join}
    (e : a₁.get l = some (CellU.immOf s₁ v χ h₁)) :
    ∃ (s' : LSet) (h' : χ.InStratum s'.join), a'.get l = some (CellU.immOf s' v χ h') ∧
      ∀ x, s₁.mem x → s'.mem x := by
  rcases ResU.Comp.get hc l with ⟨f₁, -, -⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
      ⟨ψ₁, ψ₂, ψ, f₁, -, f, hcc⟩
  · rw [e] at f₁; cases f₁
  · rw [e] at f₁
    cases Option.some.inj f₁
    exact ⟨s₁, h₁, f, fun _ hx => hx⟩
  · rw [e] at f₁; cases f₁
  · rw [e] at f₁
    cases Option.some.inj f₁
    obtain ⟨s', h', hψ, hsub⟩ := compR_imm_grow_left hcc rfl
    exact ⟨s', h', f.trans (congrArg some hψ), hsub⟩

/-- At the resource level: each lifetime of an `imm` cell of the composite comes from an `imm`
cell of an operand, over the same value and witness. -/
theorem compR_get_imm_source {a₁ a₃ a' : WRes} (hc : ResU.CompR a₁ a₃ a') {l : Loc}
    {s : LSet} {v : Val} {χ : WRes} {h : χ.InStratum s.join}
    (e : a'.get l = some (CellU.immOf s v χ h)) (x : Life) (hx : s.mem x) :
    (∃ (s₁ : LSet) (h₁ : χ.InStratum s₁.join), a₁.get l = some (CellU.immOf s₁ v χ h₁) ∧
      s₁.mem x) ∨
    (∃ (s₃ : LSet) (h₃ : χ.InStratum s₃.join), a₃.get l = some (CellU.immOf s₃ v χ h₃) ∧
      s₃.mem x) := by
  rcases ResU.Comp.get hc l with ⟨-, -, f⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, -, f₂, f⟩ |
      ⟨ψ₁, ψ₂, ψ, f₁, f₂, f, hcc⟩
  · rw [e] at f; cases f
  · rw [e] at f
    cases Option.some.inj f
    exact Or.inl ⟨s, h, f₁, hx⟩
  · rw [e] at f
    cases Option.some.inj f
    exact Or.inr ⟨s, h, f₂, hx⟩
  · rw [e] at f
    cases Option.some.inj f
    rcases compR_imm_source_mem hcc hx with ⟨s₁, h₁, rfl, hx₁⟩ | ⟨s₃, h₃, rfl, hx₃⟩
    · exact Or.inl ⟨s₁, h₁, f₁, hx₁⟩
    · exact Or.inr ⟨s₃, h₃, f₂, hx₃⟩

/-- If every lifetime of `s` sits in an `imm` operand cell at `l` over `(v, χ)`, the composite
holds an `imm` cell over `(v, χ)` at `l` containing `s`. -/
theorem compR_get_imm_cover {a₁ a₃ a' : WRes} (hc : ResU.CompR a₁ a₃ a') {l : Loc}
    {s : LSet} {v : Val} {χ : WRes}
    (H : ∀ x, s.mem x →
      (∃ (s₁ : LSet) (h₁ : χ.InStratum s₁.join), a₁.get l = some (CellU.immOf s₁ v χ h₁) ∧
        s₁.mem x) ∨
      (∃ (s₃ : LSet) (h₃ : χ.InStratum s₃.join), a₃.get l = some (CellU.immOf s₃ v χ h₃) ∧
        s₃.mem x)) :
    ∃ (s' : LSet) (h' : χ.InStratum s'.join), a'.get l = some (CellU.immOf s' v χ h') ∧
      ∀ x, s.mem x → s'.mem x := by
  have side : ∀ x, s.mem x → ∃ (s' : LSet) (h' : χ.InStratum s'.join),
      a'.get l = some (CellU.immOf s' v χ h') ∧ s'.mem x := by
    intro x hx
    rcases H x hx with ⟨s₁, h₁, e, hx₁⟩ | ⟨s₃, h₃, e, hx₃⟩
    · obtain ⟨s', h', e', hsub⟩ := compR_get_grow_left hc e
      exact ⟨s', h', e', hsub x hx₁⟩
    · obtain ⟨s', h', e', hsub⟩ := compR_get_grow_left (ResU.CompR.comm hc) e
      exact ⟨s', h', e', hsub x hx₃⟩
  obtain ⟨s', h', e', -⟩ := side s.meet s.meet_mem
  refine ⟨s', h', e', fun x hx => ?_⟩
  obtain ⟨s'', h'', e'', hx''⟩ := side x hx
  rw [e'] at e''
  obtain ⟨hs, -, -⟩ := CellU.immOf_inj (Option.some.inj e'')
  rw [hs]
  exact hx''

/-! ### Flattenings and aliasable walks agree on `imm` cells -/

theorem flat_of_ag_imm {ρ e a σ : WRes} (he : ExS ρ e) (hc : ResU.CompS e a σ) {l : Loc}
    {ψ : CellU Loc Val} (hg : a.get l = some ψ) (hk : ψ.kind = Kind.imm) :
    σ.get l = some ψ := by
  have hex : e.get l = none := by
    cases f : e.get l with
    | none => rfl
    | some ξ => exact absurd (CellU.CompatS.kinds (hc.1 l ξ _ f hg)).1 (ExS.immFree he l ξ f)
  exact comp_get_right hc hex hg

theorem flat_imm_ag {ρ σ a : WRes} (hσ : ResU.Flat ρ σ) (ha : AgW ρ a) {l : Loc}
    {ψ : CellU Loc Val} (e : σ.get l = some ψ) (hk : ψ.kind = Kind.imm) : a.get l = some ψ := by
  obtain ⟨e', a', he', ha', hc'⟩ := hσ
  rw [← AgW.functional ha' ha]
  exact ResU.ag_eq_flat_at_imm he' hc' e hk

theorem ag_imm_flat {ρ σ a : WRes} (hσ : ResU.Flat ρ σ) (ha : AgW ρ a) {l : Loc}
    {ψ : CellU Loc Val} (e : a.get l = some ψ) (hk : ψ.kind = Kind.imm) : σ.get l = some ψ := by
  obtain ⟨e', a', he', ha', hc'⟩ := hσ
  rw [AgW.functional ha' ha] at hc'
  exact flat_of_ag_imm he' hc' e hk

/-! ### 6.48's `imm` half under growth -/

/-- **6.48's `imm` half at the growth clause.** If `ρ ⇝ π` meets the growth clause, so does
`F ● ρ ⇝ F ● π`, whenever both composites are valid. -/
theorem updImmG_frame {F ρ π X Z : WRes} (h : UpdImmG ρ π) (hX : ResU.CompS F ρ X)
    (hZ : ResU.CompS F π Z) (hvX : ResU.Valid X) (hvZ : ResU.Valid Z) : UpdImmG X Z := by
  obtain ⟨σX, hσX⟩ := hvX
  obtain ⟨σZ, hσZ⟩ := hvZ
  obtain ⟨σρ, hσρ⟩ := (ResU.Valid.split hX ⟨σX, hσX⟩).2
  obtain ⟨σπ, hσπ⟩ := (ResU.Valid.split hZ ⟨σZ, hσZ⟩).2
  obtain ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hc⟩ :=
    (ResU.Flat.split hX).mp hσX
  obtain ⟨e₁', e₃, e', a₁', a₃, a', he₁', he₃, hec', ha₁', ha₃, hac', hc'⟩ :=
    (ResU.Flat.split hZ).mp hσZ
  obtain rfl : a₁' = a₁ := AgW.functional ha₁' ha₁
  have haX : AgW X a := (AgW.split hX).mpr ⟨a₁, a₂, ha₁, ha₂, hac⟩
  have haZ : AgW Z a' := (AgW.split hZ).mpr ⟨a₁, a₃, ha₁, ha₃, hac'⟩
  -- a lifetime of a `ρ` cell at `(l, v, χ)` is in an `X` cell there
  have intoX : ∀ (l : Loc) (s : LSet) (v : Val) (χ : WRes) (hs : χ.InStratum s.join) (x : Life),
      a₂.get l = some (CellU.immOf s v χ hs) → s.mem x →
      ∃ (s' : LSet) (h' : χ.InStratum s'.join), σX.get l = some (CellU.immOf s' v χ h') ∧
        s'.mem x := by
    intro l s v χ hs x e hx
    obtain ⟨s', h', e', hsub⟩ := compR_get_grow_left (ResU.CompR.comm hac) e
    exact ⟨s', h', ag_imm_flat hσX haX e' (CellU.kind_immOf _ _ _ _), hsub x hx⟩
  refine ⟨fun l s v χ hs hf => ?_, fun l s' v χ h' hf x hx => ?_⟩
  · -- (→)
    obtain ⟨σ, hσ, eσ⟩ := hf
    have ea : a.get l = some (CellU.immOf s v χ hs) :=
      flat_imm_ag hσ haX eσ (CellU.kind_immOf _ _ _ _)
    obtain ⟨sZ, hZ', eZ, hsub⟩ := compR_get_imm_cover hac' (s := s) (v := v) (χ := χ)
      (fun x hx => by
        rcases compR_get_imm_source hac ea x hx with ⟨s₁, h₁, f₁, hx₁⟩ | ⟨s₂, h₂, f₂, hx₂⟩
        · exact Or.inl ⟨s₁, h₁, f₁, hx₁⟩
        · obtain ⟨s₃, h₃, hsub₃, ⟨σ', hσ', e'⟩⟩ :=
            h.1 l s₂ v χ h₂ ⟨σρ, hσρ, ag_imm_flat hσρ ha₂ f₂ (CellU.kind_immOf _ _ _ _)⟩
          exact Or.inr ⟨s₃, h₃, flat_imm_ag hσ' ha₃ e' (CellU.kind_immOf _ _ _ _), hsub₃ x hx₂⟩)
    exact ⟨sZ, hZ', hsub, σZ, hσZ, ag_imm_flat hσZ haZ eZ (CellU.kind_immOf _ _ _ _)⟩
  · -- (←)
    obtain ⟨σ, hσ, eσ⟩ := hf
    have ea : a'.get l = some (CellU.immOf s' v χ h') :=
      flat_imm_ag hσ haZ eσ (CellU.kind_immOf _ _ _ _)
    rcases compR_get_imm_source hac' ea x hx with ⟨s₁, h₁, f₁, hx₁⟩ | ⟨s₃, h₃, f₃, hx₃⟩
    · obtain ⟨sX, hX', eX, hsub⟩ := compR_get_grow_left hac f₁
      exact Or.inl ⟨sX, hX', ⟨σX, hσX, ag_imm_flat hσX haX eX (CellU.kind_immOf _ _ _ _)⟩,
        hsub x hx₁⟩
    · rcases h.2 l s₃ v χ h₃ ⟨σπ, hσπ, ag_imm_flat hσπ ha₃ f₃ (CellU.kind_immOf _ _ _ _)⟩ x hx₃
        with ⟨s₀, h₀, ⟨σ', hσ', e'⟩, hx₀⟩ | ⟨σ₁, hσ₁, hd⟩
      · obtain ⟨sX, hX', eX, hxX⟩ :=
          intoX l s₀ v χ h₀ x (flat_imm_ag hσ' ha₂ e' (CellU.kind_immOf _ _ _ _)) hx₀
        exact Or.inl ⟨sX, hX', ⟨σX, hσX, eX⟩, hxX⟩
      · refine Or.inr ⟨σX, hσX, DerLt.mono (fun l' s'' v' w' h'' y e'' hy => ?_) hd⟩
        exact intoX l' s'' v' w' h'' y (flat_imm_ag hσ₁ ha₂ e'' (CellU.kind_immOf _ _ _ _)) hy

/-! ### `licFrame_fails`'s configuration, accepted under growth -/

section K7
variable (α β : Life) (t : Val)

theorem agX_not_mut {l : Loc} {b : Life} {v : Val} {χ : WRes} {h : χ.InStratum b}
    {P : Val → SPropS Loc Val b} {hw : P v ⟨χ, h⟩}
    (e : (agX α β t).get l = some (CellU.mutOf b v χ h P hw)) : False := by
  rcases ResU.Comp.get (agX_comp α β t) l with ⟨-, -, f⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, -, f₂, f⟩ |
      ⟨ψ₁, ψ₂, ψ, f₁, -, f, hc⟩
  · rw [e] at f; cases f
  · obtain ⟨-, hψ⟩ := ResU.single_get_eq_some f₁
    rw [e, hψ] at f
    exact CellU.immOf_ne_mutOf (Option.some.inj f).symm
  · rw [e] at f
    cases Option.some.inj f
    exact agK1_not_mut α t f₂
  · rw [e] at f
    cases Option.some.inj f
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some f₁
    have hk := (CellU.CompR.imm_left hc rfl).1
    simp at hk

theorem agZ_not_mut {l : Loc} {b : Life} {v : Val} {χ : WRes} {h : χ.InStratum b}
    {P : Val → SPropS Loc Val b} {hw : P v ⟨χ, h⟩}
    (e : (agZ α β t).get l = some (CellU.mutOf b v χ h P hw)) : False := by
  rcases ResU.Comp.get (agZ_comp α β t) l with ⟨-, -, f⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, -, f₂, f⟩ |
      ⟨ψ₁, ψ₂, ψ, f₁, -, f, hc⟩
  · rw [e] at f; cases f
  · obtain ⟨-, hψ⟩ := ResU.single_get_eq_some f₁
    rw [e, hψ] at f
    exact CellU.immOf_ne_mutOf (Option.some.inj f).symm
  · rw [e] at f
    cases Option.some.inj f
    exact agPi_not_mut α t f₂
  · rw [e] at f
    cases Option.some.inj f
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some f₁
    have hk := (CellU.CompR.imm_left hc rfl).1
    simp at hk

theorem updMut_K7 : ResU.UpdMut (xK7 α β t) (zK7 α β t) := by
  intro l b P
  constructor
  · rintro ⟨v, χ, h, hw, σ, hσ, e⟩
    rw [ResU.Flat.functional hσ (flat_xK7 α β t)] at e
    exact (agX_not_mut α β t e).elim
  · rintro ⟨v, χ, h, hw, σ, hσ, e⟩
    rw [ResU.Flat.functional hσ (flat_zK7 α β t)] at e
    exact (agZ_not_mut α β t e).elim

/-- **`licFrame_fails`'s configuration is accepted under growth.** The frame is a second image
of K1's escrow cell, and its lifetime set grows by `α`. -/
theorem k7_accepted : UpdVG (xK7 α β t) (zK7 α β t) :=
  ⟨⟨updImmG_frame (UpdImmG.of_lic (k1_lic α t)) (xK7_comp α β t) (zK7_comp α β t)
      ⟨_, flat_xK7 α β t⟩ ⟨_, flat_zK7 α β t⟩, updMut_K7 α β t⟩,
    ⟨_, flat_xK7 α β t⟩, ⟨_, flat_zK7 α β t⟩⟩

end K7

end BoCa.Fig16.LicUpd

end

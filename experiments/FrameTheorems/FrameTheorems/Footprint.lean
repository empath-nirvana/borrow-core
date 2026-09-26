import Core.Fundamental

/-!
# FrameTheorems — the footprint of a `wpTS` run

`wpTS ls e Q ρ` quantifies over every frame `ρf` that completes `ρ` to a tagged typed world
`ρf ● ρ`, and returns a run from that world's heap `⟦ρf ● ρ⟧` to a heap `⟦ρf ● ρ′ ● ρ⁺⟧`.  The
frame `ρf` is a factor of both worlds, so the part of the heap it accounts for is the same
before and after the run.  The part `ρ` accounts for changes only where `ρ` holds a location
exclusively: `ρ ↭ ρ′ ● ρ⁺` keeps every `imm` cell of `⦇ρ⦈` (row 5.27's first clause).

* `flat_factor`: the flattening of a composite contains the flattening of each factor, cell by
  cell with the same value, and every location of the composite is a location of a factor.
* `wpTS_footprint`: on the run a `wpTS` exhibits, every location of `⦇ρf⦈` keeps its value;
  every location of the initial heap that `⦇ρ⦈` holds only immutably, or not at all, keeps its
  value; and every location where `⦇ρ⦈` has a `mut` cell stays allocated (row 5.27's second
  clause).  A run changes an existing location only where `⦇ρ⦈` has an `own` or `mut` cell.

The run is the one `wpTS` exhibits: `wpTS` is a total-correctness predicate with an existential
run (row 5.33).  `EveryRun.lean` carries the statement to every run that does not allocate.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.FrameTheorems
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps)

/-! ### The flattening of a factor -/

/-- A cell of a factor of `ρ₁ ◐ ρ₂` reaches the composite with its value, at any cell-level
operation whose clauses compose cells over a common value. -/
theorem comp_get_left_erase {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : ∀ {ψ₁ ψ₂ ψ}, C ψ₁ ψ₂ ψ → ψ.erase = ψ₁.erase ∧ ψ.erase = ψ₂.erase)
    {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.Comp R C ρ₁ ρ₂ ρ) {l : Loc} {ψ₁ : CellU Loc Val}
    (e₁ : ρ₁.get l = some ψ₁) : ∃ ψ, ρ.get l = some ψ ∧ ψ.erase = ψ₁.erase := by
  rcases ResU.Comp.get h l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hc⟩
  · rw [e₁] at f₁; cases f₁
  · rw [e₁] at f₁; cases Option.some.inj f₁; exact ⟨_, f, rfl⟩
  · rw [e₁] at f₁; cases f₁
  · rw [e₁] at f₁; cases Option.some.inj f₁; exact ⟨χ, f, (hC hc).1⟩

theorem comp_get_right_erase {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : ∀ {ψ₁ ψ₂ ψ}, C ψ₁ ψ₂ ψ → ψ.erase = ψ₁.erase ∧ ψ.erase = ψ₂.erase)
    {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.Comp R C ρ₁ ρ₂ ρ) {l : Loc} {ψ₂ : CellU Loc Val}
    (e₂ : ρ₂.get l = some ψ₂) : ∃ ψ, ρ.get l = some ψ ∧ ψ.erase = ψ₂.erase := by
  rcases ResU.Comp.get h l with ⟨-, f₂, -⟩ | ⟨χ, -, f₂, -⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, -, f₂, f, hc⟩
  · rw [e₂] at f₂; cases f₂
  · rw [e₂] at f₂; cases f₂
  · rw [e₂] at f₂; cases Option.some.inj f₂; exact ⟨_, f, rfl⟩
  · rw [e₂] at f₂; cases Option.some.inj f₂; exact ⟨χ, f, (hC hc).2⟩

theorem compS_erase {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompS ψ₁ ψ₂ ψ) :
    ψ.erase = ψ₁.erase ∧ ψ.erase = ψ₂.erase :=
  CellU.CompS.erase h

theorem compR_erase {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompR ψ₁ ψ₂ ψ) :
    ψ.erase = ψ₁.erase ∧ ψ.erase = ψ₂.erase := by
  obtain ⟨h₁, h₂⟩ := CellU.CompR.erase h
  exact ⟨h₂, h₂.trans h₁⟩

/-- `⦇e ● a⦈`'s cell at a location of a factor `e₁` of `e` or `a₁` of `a`. -/
theorem flat_cell_transfer {e₁ e₂ e a₁ a₂ a σ₁ σ : WRes} (hec : ResU.CompS e₁ e₂ e)
    (hac : ResU.CompR a₁ a₂ a) (hσ : ResU.CompS e a σ) (hσ₁ : ResU.CompS e₁ a₁ σ₁) {l : Loc}
    {ψ : CellU Loc Val} (e₀ : σ₁.get l = some ψ) :
    ∃ χ, σ.get l = some χ ∧ χ.erase = ψ.erase := by
  have viaE : ∀ {ψe : CellU Loc Val}, e₁.get l = some ψe →
      ∃ χ, σ.get l = some χ ∧ χ.erase = ψe.erase := fun h => by
    obtain ⟨χe, he, ee⟩ := comp_get_left_erase compS_erase hec h
    obtain ⟨χ, hχ, eχ⟩ := comp_get_left_erase compS_erase hσ he
    exact ⟨χ, hχ, eχ.trans ee⟩
  have viaA : ∀ {ψa : CellU Loc Val}, a₁.get l = some ψa →
      ∃ χ, σ.get l = some χ ∧ χ.erase = ψa.erase := fun h => by
    obtain ⟨χa, ha, ea⟩ := comp_get_left_erase compR_erase hac h
    obtain ⟨χ, hχ, eχ⟩ := comp_get_right_erase compS_erase hσ ha
    exact ⟨χ, hχ, eχ.trans ea⟩
  rcases ResU.Comp.get hσ₁ l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hc⟩
  · rw [e₀] at f; cases f
  · rw [e₀] at f; cases Option.some.inj f; exact viaE f₁
  · rw [e₀] at f; cases Option.some.inj f; exact viaA f₂
  · rw [e₀] at f; cases Option.some.inj f
    obtain ⟨χ', h', e'⟩ := viaE f₁
    exact ⟨χ', h', e'.trans (compS_erase hc).1.symm⟩

/-- **The flattening of a factor.**  `⦇X⦈` and `⦇Y⦈` are defined when `⦇X ● Y⦈` is; each of
their cells is a cell of `⦇X ● Y⦈` with the same value; and every location of `⦇X ● Y⦈` is a
location of `⦇X⦈` or of `⦇Y⦈`. -/
theorem flat_factor {X Y Z σ : WRes} (h : ResU.CompS X Y Z) (hσ : ResU.Flat Z σ) :
    ∃ σX σY, ResU.Flat X σX ∧ ResU.Flat Y σY ∧
      (∀ l ψ, σX.get l = some ψ → ∃ χ, σ.get l = some χ ∧ χ.erase = ψ.erase) ∧
      (∀ l ψ, σY.get l = some ψ → ∃ χ, σ.get l = some χ ∧ χ.erase = ψ.erase) ∧
      (∀ l, σ.get l ≠ none → σX.get l ≠ none ∨ σY.get l ≠ none) := by
  obtain ⟨e₁, e₂, e, a₁, a₂, a, σ₁, σ₂, he₁, he₂, hec, ha₁, ha₂, hac, hc, hσ₁, hσ₂⟩ :=
    ResU.Flat.split_factors h hσ
  refine ⟨σ₁, σ₂, ⟨e₁, a₁, he₁, ha₁, hσ₁⟩, ⟨e₂, a₂, he₂, ha₂, hσ₂⟩,
    fun l ψ e₀ => flat_cell_transfer hec hac hc hσ₁ e₀,
    fun l ψ e₀ => flat_cell_transfer (ResU.CompS.comm hec) (ResU.Comp.comm
      (fun _ _ k => k.symm) (fun _ _ _ k => k.comm) hac) hc hσ₂ e₀, fun l hl => ?_⟩
  by_contra hno
  simp only [not_or, not_not] at hno
  obtain ⟨n₁, n₂⟩ := hno
  obtain ⟨ne₁, na₁⟩ := (ResU.Comp.eq_none_iff hσ₁ l).mp n₁
  obtain ⟨ne₂, na₂⟩ := (ResU.Comp.eq_none_iff hσ₂ l).mp n₂
  have hne : e.get l = none := (ResU.Comp.eq_none_iff hec l).mpr ⟨ne₁, ne₂⟩
  have hna : a.get l = none := (ResU.Comp.eq_none_iff hac l).mpr ⟨na₁, na₂⟩
  exact hl ((ResU.Comp.eq_none_iff hc l).mpr ⟨hne, hna⟩)

/-- A cell of `⦇X⦈` reads its value in every memory `X ● Y` lowers to. -/
theorem lower_of_flat_factor {X Y Z σX : WRes} {μ : Heap} (h : ResU.CompS X Y Z)
    (hμ : ResU.Lower Z μ) (hX : ResU.Flat X σX) {l : Loc} {ψ : CellU Loc Val}
    (e : σX.get l = some ψ) : μ l = some ψ.erase := by
  obtain ⟨σ, hσ, hval⟩ := hμ
  obtain ⟨σX', -, hX', -, hin, -, -⟩ := flat_factor h hσ
  cases ResU.Flat.functional hX hX'
  obtain ⟨χ, hχ, eχ⟩ := hin l ψ e
  rw [hval l, hχ]
  exact congrArg some eχ

/-- A location of a memory `X ● Y` lowers to is a location of `⦇X⦈` or of `⦇Y⦈`. -/
theorem lower_dom_factor {X Y Z : WRes} {μ : Heap} (h : ResU.CompS X Y Z)
    (hμ : ResU.Lower Z μ) {l : Loc} (hl : μ l ≠ none) :
    ∃ σX σY, ResU.Flat X σX ∧ ResU.Flat Y σY ∧ (σX.get l ≠ none ∨ σY.get l ≠ none) := by
  obtain ⟨σ, hσ, hval⟩ := hμ
  obtain ⟨σX, σY, hX, hY, -, -, hdom⟩ := flat_factor h hσ
  refine ⟨σX, σY, hX, hY, hdom l fun h0 => hl ?_⟩
  rw [hval l, h0]; rfl

/-! ### The footprint of a run -/

/-- `ℓ` is held in `⦇ρ⦈` only by `imm` cells, if at all. -/
def ImmOnly (ρ : WRes) (l : Loc) : Prop := ∀ ψ, ρ.FlatAt l ψ → ψ.kind = Kind.imm

/-- What a run from `⟦ρf ● ρ⟧` to `μ′` may do, as a heap relation:
* every location of `⦇ρf⦈` keeps its value;
* every location of the initial heap that `⦇ρ⦈` holds only immutably, or not at all, keeps its
  value;
* every location where `⦇ρ⦈` has a `mut` cell is still allocated. -/
def Footprint (ρf ρ : WRes) (μ μ' : Heap) : Prop :=
  (∀ l ψ, ρf.FlatAt l ψ → μ' l = μ l) ∧
  (∀ l, μ l ≠ none → ImmOnly ρ l → μ' l = μ l) ∧
  (∀ l ψ, ρ.FlatAt l ψ → ψ.kind = Kind.mut → μ' l ≠ none)

/-- A top-level `imm` cell is an `imm` cell of the flattening. -/
theorem immOnly_of_get {ρ : WRes} {l : Loc} {ψ : CellU Loc Val} (e : ρ.get l = some ψ)
    (hk : ψ.kind = Kind.imm) : ImmOnly ρ l := by
  intro χ ⟨σ, hσ, eχ⟩
  obtain ⟨χ', e', k', -, -⟩ := ResU.Flat.get hσ e
  rw [eχ] at e'
  cases Option.some.inj e'
  exact k'.trans hk

/-- A location `⦇ρ⦈` misses is held only immutably. -/
theorem immOnly_of_not_mem {ρ : WRes} {l : Loc} (h : ∀ ψ, ¬ ρ.FlatAt l ψ) : ImmOnly ρ l :=
  fun ψ hψ => absurd hψ (h ψ)

/-- **The footprint of a run.**  On the run a `wpTS` exhibits from the tagged typed world
`ρf ● ρ`, every location of `⦇ρf⦈` keeps its value, every location of the initial heap that
`⦇ρ⦈` holds only immutably or not at all keeps its value, and every location where `⦇ρ⦈` has a
`mut` cell stays allocated.  An existing location changes only where `⦇ρ⦈` has an `own` or
`mut` cell.  The post-condition holds of the result. -/
theorem wpTS_footprint {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp} {ρ : WRes}
    (hw : wpTS ls e Q ρ) {ρf fρ : WRes} {ps : List FrameRec} (hf : ResU.Hash ρf ρ)
    (hc : ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls)) (htg : Tagged fρ ps ls) {μ : Heap}
    (hμ : ResU.Lower fρ μ) :
    ∃ (μ' : Heap) (v : Val), Steps μ e μ' (.val v) ∧ (∃ ls' ρ', Q ls' v ρ') ∧
      Footprint ρf ρ μ μ' := by
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ₀, μ', ps', ls', -, h₂, -, h₅, h₆, h₇, h₈, h₉, hA, -,
    -, -, -, -, hC⟩ := hw ρf fρ ps hf hc hT htg
  cases ResU.Lower.functional h₅ hμ
  -- `π = ρ′ ● ρ⁺` is a factor of the final world
  obtain ⟨bc, hbc, hfbc⟩ := compS_reassoc h₂ h₆
  cases ResU.CompS.functional hbc h₉
  have hframe : ∀ l ψ, ρf.FlatAt l ψ → μ' l = μ l := by
    intro l ψ ⟨σf, hσf, el⟩
    rw [lower_of_flat_factor hc h₅ hσf el]
    obtain ⟨σ'', hσ'', hval''⟩ := h₇
    obtain ⟨σ', -, hσ', -, hin', -, -⟩ := flat_factor h₆ hσ''
    obtain ⟨σf', -, hσf', -, hinf, -, -⟩ := flat_factor h₂ hσ'
    cases ResU.Flat.functional hσf hσf'
    obtain ⟨χ₁, e₁, x₁⟩ := hinf l ψ el
    obtain ⟨χ₂, e₂, x₂⟩ := hin' l χ₁ e₁
    rw [hval'' l, e₂]
    exact congrArg some (x₂.trans x₁)
  refine ⟨μ', v, h₈, ⟨ls', ρ', hC⟩, hframe, fun l hl himm => ?_, fun l ψ hψ hk => ?_⟩
  · obtain ⟨σX, σY, hX, hY, hdom⟩ := lower_dom_factor hc h₅ hl
    rcases hdom with hx | hy
    · obtain ⟨ψ, eψ⟩ := Option.ne_none_iff_exists'.mp hx
      exact hframe l ψ ⟨σX, hX, eψ⟩
    · obtain ⟨ψ, eψ⟩ := Option.ne_none_iff_exists'.mp hy
      have hk : ψ.kind = Kind.imm := himm ψ ⟨σY, hY, eψ⟩
      rcases CellU.rep ψ with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b, w, ξ, hξ, P, hP, rfl⟩
      · simp at hk
      · rw [lower_of_flat_factor (ResU.CompS.comm hc) h₅ hY eψ]
        -- `ρ ↭ π` keeps the cell
        obtain ⟨σπ, hσπ, eπ⟩ := (hA.1.1 l s w ξ hξ).mp ⟨σY, hY, eψ⟩
        exact lower_of_flat_factor (ResU.CompS.comm hfbc) h₇ hσπ eπ
      · simp at hk
  · rcases CellU.rep ψ with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b, w, ξ, hξ, P, hP, rfl⟩
    · simp at hk
    · simp at hk
    · -- `ρ ↭ π` keeps a `mut` cell at the same invariant
      obtain ⟨w', ξ', hξ', hP', σπ, hσπ, eπ⟩ := (hA.1.2 l b P).mp ⟨w, ξ, hξ, hP, hψ⟩
      rw [lower_of_flat_factor (ResU.CompS.comm hfbc) h₇ hσπ eπ]
      simp

end BoCa.Fig16.LogRel.Core.FrameTheorems

end

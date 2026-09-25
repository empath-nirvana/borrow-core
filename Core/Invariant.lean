import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S3_Dynamics.Definitions
import Paper.S5_Model.Definitions
import Paper.S6_1_StandardLemmas.Lemmas
import Support.Lifetimes.Interpretation
import Support.Lifetimes.Substitution
import Support.LogicalRelation.ClosingSubstitutions
import Support.LogicalRelation.Facts
import Support.Model.Algebra
import Support.Model.AlgebraInstances
import Support.Model.Ancestors
import Support.Model.Cells
import Support.Model.Composition
import Support.Model.Empty
import Support.Model.Entailments
import Support.Model.FlatteningCells
import Support.Model.Lifetimes
import Support.Model.Outlives
import Support.Model.Prelude
import Support.Model.Reborrow
import Support.Model.ReborrowFrame
import Support.Model.RelaxedWalks
import Support.Model.Restriction
import Support.Model.Singletons
import Support.Model.Subtraction
import Support.Model.Surgery
import Support.Model.Update
import Support.Model.WalkSplitting
import Support.Model.Walks
import Core.Images
import Core.FrameRecords
import Core.World

/-!
# Core — Invariant  `[spec §3]`

`Support/TypedWorld`'s layer `Invariant`, with records typed at `VTy`.  The family `TW` and its invariant: `mut` cells at any depth, `Mut` positions, coherence, sub-records and lineages, and preservation of the invariant by every step.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- Any step whose `ag` is contained in the old one keeps `ChainInv` — every clause of `ChainInv`
reads `ag(W′)` only through `AgW W′ a` hypotheses. -/
theorem chainInv_of_ag_sub {W W' : WRes} {rs : List FrameRec} (t : ∀ a, AgW W' a → AgW W a)
    (h : ChainInv W rs) : ChainInv W' rs := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun r hr p m S u hc a ha ψ e hk => h1 r hr p m S u hc a (t a ha) ψ e hk,
    fun r hr m u hm a ha => h2 r hr m u hm a (t a ha), h3, h4, fun r hr hv => ?_,
    fun r hr p₀ l₀ S₀ u₀ hc hv => ?_⟩
  · obtain ⟨S, m, u, hR, a, ha, ψ, e, hk⟩ := hv
    obtain ⟨β₀, x₀, c₀, q1, q2, q3, q4, q5⟩ := h5 r hr ⟨S, m, u, hR, a, t a ha, ψ, e, hk⟩
    exact ⟨β₀, x₀, c₀, q1, q2, q3, q4, fun S m u hR a ha => q5 S m u hR a (t a ha)⟩
  · obtain ⟨m, S, u, hc', a, ha, ψ, e, hk⟩ := hv
    obtain ⟨w₀, hw₀, β₀, x₀, c₀, q1, q2, q3, q4, q5⟩ :=
      h6 r hr p₀ l₀ S₀ u₀ hc ⟨m, S, u, hc', a, t a ha, ψ, e, hk⟩
    exact ⟨w₀, fun a ha => hw₀ a (t a ha), β₀, x₀, c₀, q1, q2, q3, q4,
      fun m S u hc a ha => q5 m S u hc a (t a ha)⟩

/-- `ag(ℓ ↦ own(v) ● Z) = ag(Z)`. -/
theorem own_cell_ag {Z W : WRes} {l : Loc} {v : Val}
    (h : ResU.CompS (ResU.single l (CellU.ownOf v)) Z W) (a : WRes) : AgW W a ↔ AgW Z a := by
  constructor
  · intro ha
    obtain ⟨o, z, ho, hz, hc⟩ := (AgW.split h).mp ha
    rw [AgW.functional ho (AgW.single_own l v)] at hc
    rw [ResU.CompR.functional hc (ResU.comp_empty_left z)]
    exact hz
  · intro ha
    exact (AgW.split h).mpr ⟨_, _, AgW.single_own l v, ha, ResU.comp_empty_left a⟩

/-- `ag(ℓ ↦ own(v) ● ρ ● Z) = ag(ℓ ↦ mut(β, v, ρ, P̂) ● Z)`. -/
theorem mut_fold_ag {W X Z ρ W' : WRes} {l : Loc} {v : Val} {b : Life}
    {hstr : ρ.InStratum b} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρ, hstr⟩}
    (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) ρ X) (hW : ResU.CompS X Z W)
    (hW' : ResU.CompS (ResU.single l (CellU.mutOf b v ρ hstr P hw)) Z W') (a : WRes) :
    AgW W a ↔ AgW W' a := by
  constructor
  · intro ha
    obtain ⟨x, z, hx, hz, hxz⟩ := (AgW.split hW).mp ha
    have hx' : AgW ρ x := (own_cell_ag hX x).mp hx
    exact (AgW.split hW').mpr ⟨x, z, AgW.single_mut hx', hz, hxz⟩
  · intro ha
    obtain ⟨m, z, hm, hz, hmz⟩ := (AgW.split hW').mp ha
    exact (AgW.split hW).mpr ⟨m, z, (own_cell_ag hX m).mpr (AgW.single_mut_inv hm), hz, hmz⟩

/-- An `imm` cell of a `○` comes from an `imm` operand over the same value and witness. -/
theorem imm_back_full {a₁ a₂ a : WRes} (h : ResU.CompR a₁ a₂ a) {l : Loc}
    {ψ : CellU Loc Val} (e : a.get l = some ψ) (hk : ψ.kind = Kind.imm) :
    (∃ ψ₁, a₁.get l = some ψ₁ ∧ ψ₁.kind = Kind.imm ∧ ψ₁.erase = ψ.erase ∧ ψ₁.wit = ψ.wit) ∨
    (∃ ψ₂, a₂.get l = some ψ₂ ∧ ψ₂.kind = Kind.imm ∧ ψ₂.erase = ψ.erase ∧ ψ₂.wit = ψ.wit) := by
  rcases ResU.Comp.get h l with ⟨-, -, e'⟩ | ⟨ζ, e₁, -, e'⟩ | ⟨ζ, -, e₂, e'⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁, e₂, e', hC⟩
  · rw [e'] at e; cases e
  · rw [e'] at e; cases e; exact Or.inl ⟨_, e₁, hk, rfl, rfl⟩
  · rw [e'] at e; cases e; exact Or.inr ⟨_, e₂, hk, rfl, rfl⟩
  · rw [e'] at e; cases Option.some.inj e
    obtain ⟨s, hs, hψ⟩ := CellU.imm_eta hk
    rcases CellU.CompR.imm_source hC hψ with ⟨s₁, h₁, e₁'⟩ | ⟨s₂, h₂, e₂'⟩
    · exact Or.inl ⟨_, e₁, by rw [e₁']; rfl, by rw [e₁']; simp, by rw [e₁']; simp⟩
    · exact Or.inr ⟨_, e₂, by rw [e₂']; rfl, by rw [e₂']; simp, by rw [e₂']; simp⟩

theorem imm_fwd_full_l {a₁ a₂ a : WRes} (h : ResU.CompR a₁ a₂ a) {l : Loc}
    {ψ₁ : CellU Loc Val} (e : a₁.get l = some ψ₁) (hk : ψ₁.kind = Kind.imm) :
    ∃ ψ, a.get l = some ψ ∧ ψ.kind = Kind.imm ∧ ψ.erase = ψ₁.erase ∧ ψ.wit = ψ₁.wit :=
  ResU.CompR.get_imm_left h e hk

theorem imm_fwd_full_r {a₁ a₂ a : WRes} (h : ResU.CompR a₁ a₂ a) {l : Loc}
    {ψ₂ : CellU Loc Val} (e : a₂.get l = some ψ₂) (hk : ψ₂.kind = Kind.imm) :
    ∃ ψ, a.get l = some ψ ∧ ψ.kind = Kind.imm ∧ ψ.erase = ψ₂.erase ∧ ψ.wit = ψ₂.wit :=
  ResU.CompR.get_imm_right h e hk

/-- The walks of the two configurations of the end of a borrow, named once:
`W = ℓ ↦ imm(s, v, R) ● Y`, `W′ = (ℓ ↦ own(v) ● R) ● Y`. -/
theorem end_walks {W W' Y X' R : WRes} {l : Loc} {s : LSet} {v : Val}
    {hs : R.InStratum s.join}
    (hc : ResU.CompS (ResU.single l (CellU.immOf s v R hs)) Y W)
    (hX' : ResU.CompS (ResU.single l (CellU.ownOf v)) R X') (hW' : ResU.CompS X' Y W')
    {aW a' : WRes} (haW : AgW W aW) (ha' : AgW W' a') :
    ∃ aσ aY eR aR pR, ExR R eR ∧ AgW R aR ∧ ResU.CompR eR aR pR ∧
      ResU.CompR (ResU.single l (CellU.immOf s v R hs)) pR aσ ∧
      ResU.CompR aσ aY aW ∧ ResU.CompR aR aY a' := by
  obtain ⟨aσ, aY, hσ, hY, hσY⟩ := (AgW.split hc).mp haW
  obtain ⟨eR, aR, pR, heR, haR, hpR, hcp⟩ := AgW.single_imm_inv hσ
  obtain ⟨x', y', hx', hy', hxy'⟩ := (AgW.split hW').mp ha'
  have hx'' : AgW R x' := (own_cell_ag hX' x').mp hx'
  rw [AgW.functional hx'' haR, AgW.functional hy' hY] at hxy'
  exact ⟨aσ, aY, eR, aR, pR, heR, haR, hpR, hcp, hσY, hxy'⟩

/-- A view of `ag(W′)` after the end of a borrow is a view of `ag(W)` over the same witness. -/
theorem end_back {W W' Y X' R : WRes} {l : Loc} {s : LSet} {v : Val}
    {hs : R.InStratum s.join}
    (hc : ResU.CompS (ResU.single l (CellU.immOf s v R hs)) Y W)
    (hX' : ResU.CompS (ResU.single l (CellU.ownOf v)) R X') (hW' : ResU.CompS X' Y W')
    {aW a' : WRes} (haW : AgW W aW) (ha' : AgW W' a') {m : Loc} {ψ : CellU Loc Val}
    (e : a'.get m = some ψ) (hk : ψ.kind ≠ Kind.own) :
    ∃ ψ₀ : CellU Loc Val, aW.get m = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit := by
  obtain ⟨aσ, aY, eR, aR, pR, -, -, hpR, hcp, hσY, hRY⟩ := end_walks hc hX' hW' haW ha'
  rcases back_view hRY e hk with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₁, e₁, k₁, w₁⟩
  · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := lift_view_r hpR e₁ k₁
    obtain ⟨ψ₃, e₃, k₃, w₃⟩ := lift_view_r hcp e₂ k₂
    obtain ⟨ψ₄, e₄, k₄, w₄⟩ := lift_view hσY e₃ k₃
    exact ⟨ψ₄, e₄, k₄, by rw [w₁, ← w₂, ← w₃, ← w₄]⟩
  · obtain ⟨ψ₄, e₄, k₄, w₄⟩ := lift_view_r hσY e₁ k₁
    exact ⟨ψ₄, e₄, k₄, w₁.trans w₄.symm⟩

/-- An `imm` view of `ag(W)` away from `ℓ` survives the end of the borrow at `ℓ`, over the same
value and witness: the only views that go are `ℓ`'s own and `ex(R)_○`'s, which has none. -/
theorem end_fwd_imm {W W' Y X' R : WRes} {l : Loc} {s : LSet} {v : Val}
    {hs : R.InStratum s.join}
    (hc : ResU.CompS (ResU.single l (CellU.immOf s v R hs)) Y W)
    (hX' : ResU.CompS (ResU.single l (CellU.ownOf v)) R X') (hW' : ResU.CompS X' Y W')
    {aW a' : WRes} (haW : AgW W aW) (ha' : AgW W' a') {m : Loc} (hm : m ≠ l)
    {ψ₀ : CellU Loc Val} (e₀ : aW.get m = some ψ₀) (k₀ : ψ₀.kind = Kind.imm) :
    ∃ ψ, a'.get m = some ψ ∧ ψ.kind = Kind.imm ∧ ψ.erase = ψ₀.erase ∧ ψ.wit = ψ₀.wit := by
  obtain ⟨aσ, aY, eR, aR, pR, heR, -, hpR, hcp, hσY, hRY⟩ := end_walks hc hX' hW' haW ha'
  rcases imm_back_full hσY e₀ k₀ with ⟨ψ₁, e₁, k₁, r₁, w₁⟩ | ⟨ψ₁, e₁, k₁, r₁, w₁⟩
  · rcases imm_back_full hcp e₁ k₁ with ⟨ψ₂, e₂, -, -, -⟩ | ⟨ψ₂, e₂, k₂, r₂, w₂⟩
    · exact absurd (ResU.single_get_eq_some e₂).1 hm
    · rcases imm_back_full hpR e₂ k₂ with ⟨ψ₃, e₃, k₃, -, -⟩ | ⟨ψ₃, e₃, k₃, r₃, w₃⟩
      · exact absurd k₃ (ExR.immFree heR m ψ₃ e₃)
      · obtain ⟨ψ, e, k, r, w⟩ := imm_fwd_full_l hRY e₃ k₃
        exact ⟨ψ, e, k, r.trans (r₃.trans (r₂.trans r₁)), w.trans (w₃.trans (w₂.trans w₁))⟩
  · obtain ⟨ψ, e, k, r, w⟩ := imm_fwd_full_r hRY e₁ k₁
    exact ⟨ψ, e, k, r.trans r₁, w.trans w₁⟩

/-- Under `immFrame`, an `imm` view of `ag(W)` reaches `ag(W′)` over the same value and witness. -/
theorem frame_fwd_imm {W X Z R W' a' : WRes} {l : Loc} {v : Val} {α : Life}
    {h : R.InStratum (LSet.singleton α).join}
    (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) R X) (hW : ResU.CompS X Z W)
    (hW' : ResU.CompS (ResU.single l (CellU.immOf (LSet.singleton α) v R h)) Z W')
    (hv : ResU.Valid W) (ha' : AgW W' a') {aW : WRes} (haW : AgW W aW) {m : Loc}
    {ψ₀ : CellU Loc Val} (e₀ : aW.get m = some ψ₀) (k₀ : ψ₀.kind = Kind.imm) :
    ∃ ψ, a'.get m = some ψ ∧ ψ.kind = Kind.imm ∧ ψ.erase = ψ₀.erase ∧ ψ.wit = ψ₀.wit := by
  obtain ⟨eW, aW', r, z, eR, σc, pc, -, haW', -, hrz, -, -, -, hpc, hcp, hcz⟩ :=
    frame_walks hX hW hW' hv ha'
  rw [AgW.functional haW' haW] at hrz
  rcases imm_back_full hrz e₀ k₀ with ⟨ψ₁, e₁, k₁, r₁, w₁⟩ | ⟨ψ₁, e₁, k₁, r₁, w₁⟩
  · obtain ⟨ψ₂, e₂, k₂, r₂, w₂⟩ := imm_fwd_full_r hpc e₁ k₁
    obtain ⟨ψ₃, e₃, k₃, r₃, w₃⟩ := imm_fwd_full_r hcp e₂ k₂
    obtain ⟨ψ, e, k, r', w⟩ := imm_fwd_full_l hcz e₃ k₃
    exact ⟨ψ, e, k, r'.trans (r₃.trans (r₂.trans r₁)), w.trans (w₃.trans (w₂.trans w₁))⟩
  · obtain ⟨ψ, e, k, r', w⟩ := imm_fwd_full_r hcz e₁ k₁
    exact ⟨ψ, e, k, r'.trans r₁, w.trans w₁⟩

/-- Each record's cell is an `imm` view of `ag(W)` over the recorded value and escrow. -/
def LeInv (W : WRes) (rs : List FrameRec) : Prop :=
  ∀ r ∈ rs, ∀ a, AgW W a → ∃ ψ : CellU Loc Val, a.get r.le = some ψ ∧ ψ.kind = Kind.imm ∧
    ψ.erase = r.v ∧ ψ.wit = r.R

theorem lsOf_eta {ψ : CellU Loc Val} {s : LSet} (h : ψ.lsOf = some s) :
    ∃ (v : Val) (χ : WRes) (hs : χ.InStratum s.join), ψ = CellU.immOf s v χ hs := by
  obtain ⟨s', hs', he⟩ := CellU.imm_eta (CellU.kind_of_lsOf h)
  have h' : CellU.lsOf (CellU.immOf s' ψ.erase ψ.wit hs') = some s := he ▸ h
  rw [CellU.lsOf_immOf] at h'
  cases Option.some.inj h'
  exact ⟨_, _, hs', he⟩

theorem lsOf_of_imm {ψ : CellU Loc Val} (h : ψ.kind = Kind.imm) : ∃ s, ψ.lsOf = some s := by
  obtain ⟨s, hs, e⟩ := CellU.imm_eta h
  exact ⟨s, by rw [e, CellU.lsOf_immOf]⟩

/-- `ψ`, if `imm`, has an `imm` counterpart at `x` in `a` over the same value and witness
whose lifetime set contains `ψ`'s. -/
def ICp (a : WRes) (x : Loc) (ψ : CellU Loc Val) : Prop :=
  ψ.kind = Kind.imm → ∃ ζ : CellU Loc Val, a.get x = some ζ ∧ ζ.kind = Kind.imm ∧
    ζ.erase = ψ.erase ∧ ζ.wit = ψ.wit ∧
    ∀ s t, ψ.lsOf = some s → ζ.lsOf = some t → ∀ y, s.mem y → t.mem y

/-- Every cell of `ρ` at `x` has an `imm` counterpart in `a`. -/
def ICpAt (a ρ : WRes) (x : Loc) : Prop := ∀ ψ, ρ.get x = some ψ → ICp a x ψ

def AllICp (a ρ : WRes) : Prop := ∀ x, ICpAt a ρ x

theorem ICp.ls {a : WRes} {x : Loc} {ψ : CellU Loc Val} (h : ICp a x ψ) {s : LSet}
    (hs : ψ.lsOf = some s) {y : Life} (hy : s.mem y) :
    ∃ ζ t, a.get x = some ζ ∧ ζ.lsOf = some t ∧ t.mem y := by
  obtain ⟨ζ, eζ, kζ, -, -, lζ⟩ := h (CellU.kind_of_lsOf hs)
  obtain ⟨t, ht⟩ := lsOf_of_imm kζ
  exact ⟨ζ, t, eζ, ht, lζ s t hs ht y hy⟩

theorem icpAt_left {a₁ a₂ a : WRes} (h : ResU.CompR a₁ a₂ a) (x : Loc) : ICpAt a a₁ x := by
  intro ψ e hk
  obtain ⟨χ, eχ, kχ, rχ, wχ⟩ := ResU.CompR.get_imm_left h e hk
  refine ⟨χ, eχ, kχ, rχ, wχ, fun s t hs ht y hy => ?_⟩
  obtain ⟨v₁, χ₁, h₁, hψ⟩ := lsOf_eta hs
  obtain ⟨v₂, χ₂, h₂, hχ⟩ := lsOf_eta ht
  rw [hψ] at e; rw [hχ] at eχ
  exact ResU.CompR.get_ls_imm h e eχ hy

theorem icpAt_right {a₁ a₂ a : WRes} (h : ResU.CompR a₁ a₂ a) (x : Loc) : ICpAt a a₂ x :=
  icpAt_left (ResU.CompR.comm h) x

theorem icp_trans {a b : WRes} {x : Loc} {ψ : CellU Loc Val} (h₁ : ICp b x ψ)
    (h₂ : ICpAt a b x) : ICp a x ψ := by
  intro hk
  obtain ⟨ζ, eζ, kζ, rζ, wζ, lζ⟩ := h₁ hk
  obtain ⟨ξ, eξ, kξ, rξ, wξ, lξ⟩ := h₂ ζ eζ kζ
  refine ⟨ξ, eξ, kξ, rξ.trans rζ, wξ.trans wζ, fun s t hs ht y hy => ?_⟩
  obtain ⟨u, hu⟩ := lsOf_of_imm kζ
  exact lξ u t hu ht y (lζ s u hs hu y hy)

theorem icpAt_trans {a b ρ : WRes} {x : Loc} (h₁ : ICpAt b ρ x) (h₂ : ICpAt a b x) :
    ICpAt a ρ x := fun ψ e => icp_trans (h₁ ψ e) h₂

theorem icpAt_comp {b ρ₁ ρ₂ ρ : WRes} (h : ResU.CompR ρ₁ ρ₂ ρ) {x : Loc}
    (h₁ : ICpAt b ρ₁ x) (h₂ : ICpAt b ρ₂ x) : ICpAt b ρ x := by
  intro ψ e hk
  obtain ⟨s, hs, hψ⟩ := CellU.imm_eta hk
  have e' := e
  rw [hψ] at e'
  have src : ∃ ζ, b.get x = some ζ ∧ ζ.kind = Kind.imm ∧ ζ.erase = ψ.erase ∧
      ζ.wit = ψ.wit := by
    rcases ResU.CompR.imm_source h e' with ⟨s₁, k₁, e₁⟩ | ⟨s₂, k₂, e₂⟩
    · obtain ⟨ζ, eζ, kζ, rζ, wζ, -⟩ := h₁ _ e₁ (CellU.kind_immOf _ _ _ _)
      exact ⟨ζ, eζ, kζ, by rw [rζ]; simp, by rw [wζ]; simp⟩
    · obtain ⟨ζ, eζ, kζ, rζ, wζ, -⟩ := h₂ _ e₂ (CellU.kind_immOf _ _ _ _)
      exact ⟨ζ, eζ, kζ, by rw [rζ]; simp, by rw [wζ]; simp⟩
  obtain ⟨ζ, eζ, kζ, rζ, wζ⟩ := src
  refine ⟨ζ, eζ, kζ, rζ, wζ, fun s' t hs' ht y hy => ?_⟩
  rcases ResU.CompR.lsOf_inv h e hs' hy with ⟨ξ, t₁, e₁, ht₁, hy₁⟩ | ⟨ξ, t₁, e₁, ht₁, hy₁⟩
  · obtain ⟨ζ', t', eζ', ht', hy'⟩ := (h₁ ξ e₁).ls ht₁ hy₁
    rw [eζ] at eζ'; cases Option.some.inj eζ'
    rw [ht] at ht'; cases Option.some.inj ht'; exact hy'
  · obtain ⟨ζ', t', eζ', ht', hy'⟩ := (h₂ ξ e₁).ls ht₁ hy₁
    rw [eζ] at eζ'; cases Option.some.inj eζ'
    rw [ht] at ht'; cases Option.some.inj ht'; exact hy'

theorem icpAt_bigComp {b : WRes} {x : Loc} :
    ∀ {L : List WRes} {c : WRes}, BigComp CellU.CompatR CellU.CompR L c →
      (∀ σ ∈ L, ICpAt b σ x) → ICpAt b c x
  | [], c, h, _ => by
      cases h
      intro ψ e; rw [PMap.empty_get] at e; cases e
  | σ :: L, c, h, hL => by
      cases h with
      | cons hrest hc =>
          exact icpAt_comp hc (hL σ List.mem_cons_self)
            (icpAt_bigComp hrest (fun τ hτ => hL τ (List.mem_cons_of_mem _ hτ)))

theorem icpAt_of_immFree {b ρ : WRes} (h : ρ.ImmFree) (x : Loc) : ICpAt b ρ x :=
  fun ψ e hk => absurd hk (h x ψ e)

theorem icpAt_none {b ρ : WRes} {x : Loc} (h : ρ.get x = none) : ICpAt b ρ x := by
  intro ψ e; rw [h] at e; cases e

/-- `ag(ρ)` keeps every `imm` cell of `ρ` over its value and witness, and never drops a
lifetime (`AgW.get_imm`, `AgW.get_ls_imm`). -/
theorem icpAt_agW {ρ σ : WRes} (h : AgW ρ σ) (x : Loc) : ICpAt σ ρ x := by
  intro ψ e hk
  obtain ⟨χ, eχ, kχ, rχ, wχ⟩ := AgW.get_imm h e hk
  refine ⟨χ, eχ, kχ, rχ, wχ, fun s t hs ht y hy => ?_⟩
  obtain ⟨v₁, χ₁, h₁, hψ⟩ := lsOf_eta hs
  obtain ⟨v₂, χ₂, h₂, hχ⟩ := lsOf_eta ht
  rw [hψ] at e; rw [hχ] at eχ
  exact AgW.get_ls_imm h e eχ hy

/-- `MutAt ρ ℓ`: a `mut` cell at `ℓ` sits in `ρ`, at the top or inside the witness of a
non-`own` cell.  `[about ours: the depth `ex` and `ag` descend to, named]` -/
inductive MutAt : WRes → Loc → Prop
  | top {ρ : WRes} {l : Loc} {ψ : CellU Loc Val} :
      ρ.get l = some ψ → ψ.kind = Kind.mut → MutAt ρ l
  | nest {ρ : WRes} {l m : Loc} {ψ : CellU Loc Val} :
      ρ.get m = some ψ → ψ.kind ≠ Kind.own → MutAt ψ.wit l → MutAt ρ l

/-- `MutAt` moves along any map of non-`own` cells that keeps kind and witness. -/
theorem MutAt.mono {ρ σ : WRes}
    (t : ∀ m (ψ : CellU Loc Val), ρ.get m = some ψ → ψ.kind ≠ Kind.own →
      ∃ ζ : CellU Loc Val, σ.get m = some ζ ∧ ζ.kind = ψ.kind ∧ ζ.wit = ψ.wit)
    {l : Loc} (h : MutAt ρ l) : MutAt σ l := by
  cases h with
  | top e hk =>
      obtain ⟨ζ, eζ, kζ, -⟩ := t _ _ e (by rw [hk]; simp)
      exact MutAt.top eζ (kζ.trans hk)
  | nest e hk hw =>
      obtain ⟨ζ, eζ, kζ, wζ⟩ := t _ _ e hk
      exact MutAt.nest eζ (kζ ▸ hk) (wζ ▸ hw)

theorem MutAt.of_compS_left {a b c : WRes} (h : ResU.CompS a b c) {l : Loc}
    (hm : MutAt a l) : MutAt c l :=
  MutAt.mono (fun m ψ e _ => by
    obtain ⟨ζ, eζ, kζ, wζ, -⟩ := compS_get_left' h e
    exact ⟨ζ, eζ, kζ, wζ⟩) hm

theorem MutAt.of_compS_right {a b c : WRes} (h : ResU.CompS a b c) {l : Loc}
    (hm : MutAt b l) : MutAt c l := MutAt.of_compS_left (ResU.CompS.comm h) hm

theorem MutAt.of_le {q w : WRes} (h : ResU.Le q w) {l : Loc} (hm : MutAt q l) : MutAt w l := by
  obtain ⟨τ, hτ⟩ := h
  exact MutAt.of_compS_left hτ hm

theorem MutAt.of_del {q : WRes} {m l : Loc} (hm : MutAt (q.del m) l) : MutAt q l :=
  MutAt.mono (fun x ψ e _ => by
    by_cases hx : x = m
    · subst hx; rw [ResU.del_get_self] at e; cases e
    · rw [ResU.del_get_ne _ hx] at e; exact ⟨ψ, e, rfl, rfl⟩) hm

/-- A cell of a `●` comes from an operand with its kind and witness. -/
theorem compS_back {a b c : WRes} (h : ResU.CompS a b c) {m : Loc} {ζ : CellU Loc Val}
    (e : c.get m = some ζ) :
    (∃ ψ : CellU Loc Val, a.get m = some ψ ∧ ψ.kind = ζ.kind ∧ ψ.wit = ζ.wit) ∨
    (∃ ψ : CellU Loc Val, b.get m = some ψ ∧ ψ.kind = ζ.kind ∧ ψ.wit = ζ.wit) := by
  rcases ResU.Comp.get h m with ⟨-, -, e'⟩ | ⟨χ, e₁, -, e'⟩ | ⟨χ, -, e₂, e'⟩ |
      ⟨χ₁, χ₂, χ, e₁, e₂, e', hC⟩
  · rw [e'] at e; cases e
  · rw [e'] at e; cases e; exact Or.inl ⟨_, e₁, rfl, rfl⟩
  · rw [e'] at e; cases e; exact Or.inr ⟨_, e₂, rfl, rfl⟩
  · rw [e'] at e; cases e
    refine Or.inl ⟨_, e₁, ?_, (CellU.CompS.wit hC).1.symm⟩
    rw [CellU.CompS.kind hC]
    obtain ⟨_, _, _, _, _, _, _, h₁, _, _⟩ := hC
    rw [h₁]; rfl

theorem MutAt.split {a b c : WRes} (h : ResU.CompS a b c) {l : Loc} (hm : MutAt c l) :
    MutAt a l ∨ MutAt b l := by
  cases hm with
  | top e hk =>
      rcases compS_back h e with ⟨ψ, eψ, kψ, -⟩ | ⟨ψ, eψ, kψ, -⟩
      · exact Or.inl (MutAt.top eψ (kψ.trans hk))
      · exact Or.inr (MutAt.top eψ (kψ.trans hk))
  | nest e hk hw =>
      rcases compS_back h e with ⟨ψ, eψ, kψ, wψ⟩ | ⟨ψ, eψ, kψ, wψ⟩
      · exact Or.inl (MutAt.nest eψ (kψ ▸ hk) (wψ ▸ hw))
      · exact Or.inr (MutAt.nest eψ (kψ ▸ hk) (wψ ▸ hw))

/-- An `own` cell carries no `mut` cell. -/
theorem not_mutAt_single_own (m : Loc) (v : Val) (l : Loc) :
    ¬ MutAt (ResU.single m (CellU.ownOf v)) l := by
  intro h
  cases h with
  | top e hk => obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e; exact absurd hk (by simp)
  | nest e hk _ => obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e; exact hk rfl

theorem compR_mut_src : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompR ψ₁ ψ₂ ψ →
    ψ.kind = Kind.mut → ψ₁.kind = Kind.mut ∨ ψ₂.kind = Kind.mut := by
  intro ψ₁ ψ₂ ψ h hk
  cases h with
  | same => exact Or.inl hk
  | strict k =>
      rw [CellU.CompS.kind (CellU.compS_spec _ _ k)] at hk; cases hk
  | mutMut => exact Or.inl (by simp)
  | mutOwn => exact Or.inl (by simp)
  | ownMut => exact Or.inr (by simp)
  | immOwn => simp at hk
  | ownImm => simp at hk
  | immMut => simp at hk
  | mutImm => simp at hk

theorem comp_mut_src {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ.kind = Kind.mut → ψ₁.kind = Kind.mut ∨ ψ₂.kind = Kind.mut)
    {a b c : WRes} (h : ResU.Comp R C a b c) {x : Loc} {ψ : CellU Loc Val}
    (e : c.get x = some ψ) (hk : ψ.kind = Kind.mut) :
    (∃ ψ₁ : CellU Loc Val, a.get x = some ψ₁ ∧ ψ₁.kind = Kind.mut) ∨
    (∃ ψ₂ : CellU Loc Val, b.get x = some ψ₂ ∧ ψ₂.kind = Kind.mut) := by
  rcases ResU.Comp.get h x with ⟨-, -, e'⟩ | ⟨χ, e₁, -, e'⟩ | ⟨χ, -, e₂, e'⟩ |
      ⟨χ₁, χ₂, χ, e₁, e₂, e', hCc⟩
  · rw [e'] at e; cases e
  · rw [e'] at e; cases e; exact Or.inl ⟨_, e₁, hk⟩
  · rw [e'] at e; cases e; exact Or.inr ⟨_, e₂, hk⟩
  · rw [e'] at e; cases e
    rcases hC _ _ _ hCc hk with k | k
    · exact Or.inl ⟨_, e₁, k⟩
    · exact Or.inr ⟨_, e₂, k⟩

theorem bigComp_mut_src {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ.kind = Kind.mut → ψ₁.kind = Kind.mut ∨ ψ₂.kind = Kind.mut) :
    ∀ {L : List WRes} {b : WRes}, BigComp R C L b → ∀ {x : Loc} {ψ : CellU Loc Val},
      b.get x = some ψ → ψ.kind = Kind.mut →
      ∃ σ ∈ L, ∃ ψ' : CellU Loc Val, σ.get x = some ψ' ∧ ψ'.kind = Kind.mut
  | [], b, h, x, ψ, e, _ => by cases h; rw [PMap.empty_get] at e; cases e
  | σ :: L, b, h, x, ψ, e, hk => by
      cases h with
      | cons hrest hc =>
          rcases comp_mut_src hC hc e hk with ⟨ψ₁, e₁, k₁⟩ | ⟨ψ₂, e₂, k₂⟩
          · exact ⟨σ, List.mem_cons_self, ψ₁, e₁, k₁⟩
          · obtain ⟨τ, hτ, ψ', e', k'⟩ := bigComp_mut_src hC hrest e₂ k₂
            exact ⟨τ, List.mem_cons_of_mem _ hτ, ψ', e', k'⟩

/-- `ex(ρ)` raises a `mut` cell only from one in `ρ`. -/
theorem exW_mut {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ.kind = Kind.mut → ψ₁.kind = Kind.mut ∨ ψ₂.kind = Kind.mut)
    {ρ σ : WRes} (h : ExW R C ρ σ) :
    ∀ x (ψ : CellU Loc Val), σ.get x = some ψ → ψ.kind = Kind.mut → MutAt ρ x := by
  refine ExW.rec (motive_1 := fun ρ σ _ => ∀ x (ψ : CellU Loc Val), σ.get x = some ψ →
      ψ.kind = Kind.mut → MutAt ρ x)
    (motive_2 := fun ρ w _ => ∀ p ∈ w, ∀ x (ψ : CellU Loc Val), p.2.get x = some ψ →
      ψ.kind = Kind.mut → MutAt ρ x) ?mk ?nil ?cons h
  case mk =>
    intro ρ' σ' nm b w hs hw hb hnm hσ ih x ψ e hk
    rcases comp_mut_src hC hσ e hk with ⟨ψ₁, e₁, k₁⟩ | ⟨ψ₂, e₂, k₂⟩
    · rcases comp_mut_src hC hnm e₁ k₁ with ⟨ψ₃, e₃, k₃⟩ | ⟨ψ₃, e₃, k₃⟩
      · have := (ResU.restrict_eq_some.mp e₃).2; rw [k₃] at this; cases this
      · exact MutAt.top (ResU.restrict_eq_some.mp e₃).1 k₃
    · obtain ⟨τ, hτ, ψ', e', k'⟩ := bigComp_mut_src hC hb e₂ k₂
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hτ
      exact ih p hp x ψ' e' k'
  case nil => intro ρ' p hp; exact absurd hp (by simp)
  case cons =>
    intro ρ' e l w ψ hψ hk he hw ihe ihw p hp x ψ' e' k'
    rcases List.mem_cons.mp hp with rfl | hp
    · exact MutAt.nest hψ (by rw [hk]; simp) (ihe x ψ' e' k')
    · exact ihw p hp x ψ' e' k'

/-- `ag(ρ)` raises a `mut` cell only from one in `ρ`. -/
theorem agW_mut {ρ σ : WRes} (h : AgW ρ σ) :
    ∀ x (ψ : CellU Loc Val), σ.get x = some ψ → ψ.kind = Kind.mut → MutAt ρ x := by
  refine AgW.rec (motive_1 := fun ρ σ _ => ∀ x (ψ : CellU Loc Val), σ.get x = some ψ →
      ψ.kind = Kind.mut → MutAt ρ x)
    (motive_2 := fun ρ w _ => ∀ p ∈ w, ∀ x (ψ : CellU Loc Val), p.2.get x = some ψ →
      ψ.kind = Kind.mut → MutAt ρ x)
    (motive_3 := fun ρ w _ => ∀ p ∈ w, ∀ x (ψ : CellU Loc Val), p.2.get x = some ψ →
      ψ.kind = Kind.mut → MutAt ρ x)
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ' σ' a bm bi wm wi hsm hsi hwm hwi hbm hbi ha hσ ihm ihi x ψ e hk
    rcases comp_mut_src compR_mut_src hσ e hk with ⟨ψ₁, e₁, k₁⟩ | ⟨ψ₂, e₂, k₂⟩
    · rcases comp_mut_src compR_mut_src ha e₁ k₁ with ⟨ψ₃, e₃, k₃⟩ | ⟨ψ₃, e₃, k₃⟩
      · have := (ResU.restrict_eq_some.mp e₃).2; rw [k₃] at this; cases this
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
    · exact MutAt.nest hψ (by rw [hk]; simp) (ihe x ψ' e' k')
    · exact ihw p hp x ψ' e' k'
  case nilI => intro ρ' p hp; exact absurd hp (by simp)
  case consI =>
    intro ρ' q l w ψ hψ hk e a hex hag hc hw iha ihw p hp x ψ' e' k'
    rcases List.mem_cons.mp hp with rfl | hp
    · rcases comp_mut_src compR_mut_src hc e' k' with ⟨ψ₁, e₁, k₁⟩ | ⟨ψ₁, e₁, k₁⟩
      · exact MutAt.nest hψ (by rw [hk]; simp) (exW_mut compR_mut_src hex x ψ₁ e₁ k₁)
      · exact MutAt.nest hψ (by rw [hk]; simp) (iha x ψ₁ e₁ k₁)
    · exact ihw p hp x ψ' e' k'

theorem hSS : ∀ ψ₁ ψ₂ ψ : CellU Loc Val, CellU.CompS ψ₁ ψ₂ ψ → CellU.CompatS ψ₁ ψ₂ := by
  intro ψ₁ ψ₂ ψ h
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, -, e₁, e₂, -⟩ := h
  exact ⟨s₁, s₂, v, ρ, h₁, h₂, e₁, e₂⟩

/-- A `mut` cell at `ℓ` at any depth of `ρ` shows at `ℓ` in `ex(ρ)` or in `ag(ρ)`. -/
theorem mutAt_walk_dom {ρ : WRes} {x : Loc} (h : MutAt ρ x) :
    ∀ {R : CellU Loc Val → CellU Loc Val → Prop}
      {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop},
      (∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → R ψ₁ ψ₂) → ResU.CompLaws C →
      ∀ {e a : WRes}, ExW R C ρ e → AgW ρ a →
      (∃ ζ, e.get x = some ζ) ∨ (∃ ζ, a.get x = some ζ) := by
  induction h with
  | @top ρ l ψ e hk =>
      intro R C hR hC ex a hex ha
      cases hex with
      | mk hs hw hb hnm hσ =>
          obtain ⟨ζ₁, e₁⟩ := comp_some_r hnm (ResU.restrict_get_some e hk)
          exact Or.inl (comp_some hσ e₁)
  | @nest ρ l m ψ e hk hmw ih =>
      intro R C hR hC ex a hex ha
      cases hkk : ψ.kind with
      | own => exact absurd hkk hk
      | imm =>
          obtain ⟨ev, av, p, z, hev, hav, hp, hz⟩ := AgW.imm_wit_le ha e hkk
          rcases ih hRR ResU.compLawsR hev hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
          · obtain ⟨_, h1⟩ := comp_some hp hζ; exact Or.inr (comp_some hz h1)
          · obtain ⟨_, h1⟩ := comp_some_r hp hζ; exact Or.inr (comp_some hz h1)
      | «mut» =>
          obtain ⟨ev, z, hev, hz⟩ := ExW.wit_le hR hC hex e hkk
          obtain ⟨av, z', hav, hz'⟩ := AgW.mut_wit_le ha e hkk
          rcases ih hR hC hev hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
          · exact Or.inl (comp_some hz hζ)
          · exact Or.inr (comp_some hz' hζ)

/-- A top-level `ℓ ↦ own(u)` of a valid resource is borrowed mutably nowhere in it.
`⦇W⦈ = ex(W)_● ● ag(W)`: a `mut` cell at `ℓ` under an `imm` cell lands in `ag(W)`, which is
disjoint from `ex(W)_●`'s `own(u)` (`ex_ag_disjoint`); under a `mut` cell it lands in
`ex(W)_●`'s `⨀`, which `●`s against `W|own`'s `own(u)`, and `●` joins `imm` cells only. -/
theorem not_mutAt_top_own {W : WRes} (hv : ResU.Valid W) {x : Loc} {u : Val}
    (hx : W.get x = some (CellU.ownOf u)) : ¬ MutAt W x := by
  intro hm
  obtain ⟨σ, eW, aW, heW, haW, hc⟩ := hv
  have eo : eW.get x = some (CellU.ownOf u) := ExS.get_of_ne_imm heW hx (by simp)
  have noAg : ∀ ζ, aW.get x = some ζ → False := fun ζ hζ =>
    ex_ag_disjoint ⟨σ, eW, aW, heW, haW, hc⟩ heW haW eo hζ
  cases hm with
  | top e hk => rw [hx] at e; cases Option.some.inj e; exact absurd hk (by simp)
  | @nest _ _ m ψ e hk hmw =>
      cases hkk : ψ.kind with
      | own => exact hk hkk
      | imm =>
          obtain ⟨ev, av, p, z, hev, hav, hp, hz⟩ := AgW.imm_wit_le haW e hkk
          rcases mutAt_walk_dom hmw hRR ResU.compLawsR hev hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
          · obtain ⟨_, h1⟩ := comp_some hp hζ
            obtain ⟨_, h2⟩ := comp_some hz h1
            exact noAg _ h2
          · obtain ⟨_, h1⟩ := comp_some_r hp hζ
            obtain ⟨_, h2⟩ := comp_some hz h1
            exact noAg _ h2
      | «mut» =>
          obtain ⟨av, z, hav, hz⟩ := AgW.mut_wit_le haW e hkk
          cases heW with
          | mk hs hw hb hnm hσ =>
              rename_i nm b w
              obtain ⟨q, hq, hq₁⟩ := List.mem_map.mp ((hs.2 m).mpr ⟨ψ, e, hkk⟩)
              obtain ⟨ψ', hψ', hex'⟩ := ExWits.mem hw q hq
              rw [hq₁, e] at hψ'
              cases Option.some.inj hψ'
              rcases mutAt_walk_dom hmw hSS ResU.compLawsS hex' hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
              · obtain ⟨z', hz'⟩ :=
                  BigComp.mem_factor hSS ResU.compLawsS hb q.2 (List.mem_map.mpr ⟨q, hq, rfl⟩)
                obtain ⟨ζb, hζb⟩ := comp_some hz' hζ
                have hno : (W.restrict Kind.mut).get x = none := by
                  cases e' : (W.restrict Kind.mut).get x with
                  | none => rfl
                  | some χ =>
                      obtain ⟨e'', k''⟩ := ResU.restrict_eq_some.mp e'
                      rw [hx] at e''; cases Option.some.inj e''; exact absurd k'' (by simp)
                have hnm' : nm.get x = some (CellU.ownOf u) := by
                  have hown : (W.restrict Kind.own).get x = some (CellU.ownOf u) :=
                    ResU.restrict_get_some hx (by simp)
                  exact (ResU.CompS.get_left_of_ne_imm hnm hown (by simp)).2
                have := ResU.CompatS.right_eq_none hσ.1 hnm' (by simp)
                rw [hζb] at this; cases this
              · obtain ⟨_, h1⟩ := comp_some hz hζ
                exact noAg _ h1

/-- A cell of `c ∈ reb_β(σ)`, with its lifetimes (`[TR]` p. 5, `reb_α`'s three clauses):
over an `own` or `mut` cell of `σ` it is `imm({β}, …)`; over an `imm` cell `imm(s, v, χ)` it
is `imm(t, v, χ)` with `t ⊆ s`. -/
theorem reb_cell_ls {β : Life} {σ c : WRes} (hr : ResU.Reb β σ c) {m : Loc}
    {ψ : CellU Loc Val} (e : c.get m = some ψ) :
    ((∃ ζ : CellU Loc Val, σ.get m = some ζ ∧ ζ.kind ≠ Kind.imm) ∧
        ψ.lsOf = some (LSet.singleton β)) ∨
    (∃ ζ : CellU Loc Val, σ.get m = some ζ ∧ ζ.kind = Kind.imm ∧ ψ.erase = ζ.erase ∧
      ψ.wit = ζ.wit ∧ ∀ s t, ζ.lsOf = some s → ψ.lsOf = some t → ∀ y, t.mem y → s.mem y) := by
  obtain ⟨-, π, b, hdom, hbig, hle, hbody⟩ := hr
  obtain ⟨⟨l₀, q⟩, hpm, hpl⟩ := List.mem_map.mp ((hdom.2 m).mpr ⟨_, e⟩)
  simp only at hpl
  subst hpl
  have hq := hbody l₀ q hpm
  have hmem : q ∈ π.map Prod.snd := List.mem_map.mpr ⟨_, hpm, rfl⟩
  obtain ⟨b', hb', hle'⟩ := BigComp.leS_of_sublist (List.singleton_sublist.mpr hmem) hbig
  rw [(BigComp.singleton_iff ResU.compLawsS).mp hb'] at hle'
  obtain ⟨ζq, hζq⟩ := hq.1
  obtain ⟨τ, hτ⟩ := hle'.trans hle
  obtain ⟨ζ, hζ⟩ := comp_some hτ hζq
  rcases CellU.rep ζ with ⟨u, rfl⟩ | ⟨s, v, χ, hs, rfl⟩ | ⟨b₀, v, χ, hb₀, P, hw, rfl⟩
  · obtain ⟨hh, he⟩ := hq.2.1 u hζ
    rw [e] at he; cases Option.some.inj he
    exact Or.inl ⟨⟨_, hζ, by simp⟩, CellU.lsOf_immOf _ _ _ _⟩
  · obtain ⟨⟨t, ht, hts, he⟩, -⟩ := hq.2.2.2 s v χ hs hζ
    rw [e] at he; cases Option.some.inj he
    refine Or.inr ⟨_, hζ, CellU.kind_immOf _ _ _ _, by simp, by simp,
      fun s' t' hs' ht' y hy => ?_⟩
    rw [CellU.lsOf_immOf] at hs' ht'
    cases Option.some.inj hs'; cases Option.some.inj ht'
    exact hts y hy
  · obtain ⟨⟨hh, he⟩, -⟩ := hq.2.2.1 b₀ v χ hb₀ P hw hζ
    rw [e] at he; cases Option.some.inj he
    exact Or.inl ⟨⟨_, hζ, by simp⟩, CellU.lsOf_immOf _ _ _ _⟩

/-- A reborrow image carries no `mut` cell its source does not: every cell of it is `imm`
over a witness that is a piece of the source (`own` clause) or a witness of the source's own
cell (`mut`, `imm` clauses). -/
theorem mutAt_image {β : Life} {w₀ c : WRes} (hr : ResU.Reb β w₀ c) {x : Loc}
    (hm : MutAt c x) : MutAt w₀ x := by
  cases hm with
  | top e hk => rw [(reb_cell hr e).1] at hk; cases hk
  | @nest _ _ m ψ e hk hw =>
      obtain ⟨-, hcase⟩ := reb_cell hr e
      rcases hcase with ⟨u, q, h, hown, rfl, hqσ, ζq, hζq⟩ | ⟨ζ, eζ, kζ, wζ⟩ | ⟨ζ, eζ, kζ, wζ⟩
      · rw [CellU.wit_immOf] at hw
        exact MutAt.of_le hqσ (MutAt.of_del hw)
      · exact MutAt.nest eζ (by rw [kζ]; simp) (wζ ▸ hw)
      · exact MutAt.nest eζ (by rw [kζ]; simp) (wζ ▸ hw)

/-- `W(ℓₑ) = imm(s, v, w₀)` makes every `mut` cell of `w₀` one of `W`. -/
theorem mutAt_of_cell {W w₀ : WRes} {le : Loc} {s : LSet} {v : Val}
    {hs : w₀.InStratum s.join} (hle : W.get le = some (CellU.immOf s v w₀ hs)) {x : Loc}
    (hm : MutAt w₀ x) : MutAt W x :=
  MutAt.nest hle (by simp) (by rw [CellU.wit_immOf]; exact hm)

/-- `ag(ρ₀)` of an escrow sits in `ag(W)` — `W(ℓₑ) = imm(s, v, ρ₀)` contributes
`ex(ρ₀)_○ ○ ag(ρ₀)` to `ag(W)`. -/
theorem escrow_icp {W a₁ w₀ : WRes} {le : Loc} {s : LSet} {v : Val}
    {hs : w₀.InStratum s.join} (ha₁ : AgW W a₁)
    (hle : W.get le = some (CellU.immOf s v w₀ hs)) :
    ∃ e₀ a₀, ExR w₀ e₀ ∧ AgW w₀ a₀ ∧ AllICp a₁ a₀ := by
  obtain ⟨a₁', a₂, -, h₂, h12⟩ := (AgW.split (ResU.del_compS hle)).mp ha₁
  obtain ⟨e₀, a₀, p₀, he₀, ha₀, hp₀, hcp₀⟩ := AgW.single_imm_inv h₂
  exact ⟨e₀, a₀, he₀, ha₀, fun x =>
    icpAt_trans (icpAt_right hp₀ x) (icpAt_trans (icpAt_right hcp₀ x) (icpAt_right h12 x))⟩

/-- The walk of a part of a reborrow image, taken at `W(ℓₑ) = imm(s, v, w₀)`.  If every
cell of `d` is a cell of `c ∈ reb_β(w₀)`, then `ag(d) = d ○ b` where every `imm` cell of `b`
has an `imm` counterpart in `ag(W)`: `b` is `⨀` of `ex(χ)_○ ○ ag(χ)` over `d`'s witnesses
`χ`, each a piece of `w₀` or a witness of one of its cells (`[TR]` 6.54's *"every witness is
also in ⦇ρ⦈○"*). -/
theorem img_walk {W₁ a₁ w₀ c d ad : WRes} {le : Loc} {s : LSet} {v : Val}
    {hs : w₀.InStratum s.join} {β : Life} (ha₁ : AgW W₁ a₁)
    (hle : W₁.get le = some (CellU.immOf s v w₀ hs)) (hr : ResU.Reb β w₀ c)
    (hsub : ∀ x (ψ : CellU Loc Val), d.get x = some ψ → c.get x = some ψ) (had : AgW d ad) :
    ∃ d' bi, ResU.CompR d' bi ad ∧ AllICp a₁ bi ∧
      (∀ x (ψ : CellU Loc Val), d'.get x = some ψ → d.get x = some ψ) := by
  obtain ⟨e₀, a₀, he₀, ha₀, icp₀⟩ := escrow_icp ha₁ hle
  have hkind : ∀ x (ψ : CellU Loc Val), d.get x = some ψ → ψ.kind = Kind.imm :=
    fun x ψ e => (reb_cell hr (hsub x ψ e)).1
  -- the `ag` of each witness of `d` sits in `ag(w₀)`
  have witICp : ∀ x (ψ : CellU Loc Val), d.get x = some ψ → ∀ av, AgW ψ.wit av →
      AllICp a₁ av := by
    intro x ψ e av hav
    obtain ⟨-, hcase⟩ := reb_cell hr (hsub x ψ e)
    rcases hcase with ⟨u, q, h, hown, rfl, hqσ, ζq, hζq⟩ | ⟨ζ, eζ, kζ, wζ⟩ | ⟨ζ, eζ, kζ, wζ⟩
    · rw [CellU.wit_immOf] at hav
      obtain ⟨τ, hτ⟩ : ResU.Le (q.del x) w₀ := ResU.Le.trans ⟨_, ResU.del_compS hζq⟩ hqσ
      obtain ⟨y₁, y₂, hy₁, -, hy⟩ := (AgW.split hτ).mp ha₀
      rw [AgW.functional hy₁ hav] at hy
      exact fun z => icpAt_trans (icpAt_left hy z) (icp₀ z)
    · obtain ⟨av', z, hav', hz⟩ := AgW.mut_wit_le ha₀ eζ kζ
      rw [← wζ] at hav'
      rw [AgW.functional hav hav']
      exact fun y => icpAt_trans (icpAt_left hz y) (icp₀ y)
    · obtain ⟨ev', av', p', z, -, hav', hp', hz⟩ := AgW.imm_wit_le ha₀ eζ kζ
      rw [← wζ] at hav'
      rw [AgW.functional hav hav']
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
      have hae : a = d.restrict Kind.imm :=
        ResU.CompR.functional ha (ResU.comp_empty_right _)
      subst hae
      refine ⟨_, bi, hσ, fun y => icpAt_bigComp hbi (fun σ hσm => ?_),
        fun x ψ e => (ResU.restrict_eq_some.mp e).1⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hσm
      obtain ⟨ψ, ev, av, eψ, hev, hav, hc⟩ := AgWitsI.mem hwi p hp
      exact icpAt_comp hc (icpAt_of_immFree (ExR.immFree hev) y) (witICp _ ψ eψ av hav y)

/-- A cell of the image, against `ag(W)`: over an `imm` cell of `w₀` it has an `imm`
counterpart in `ag(W)`; over an `own` or `mut` cell it is `imm({β}, …)`. -/
theorem img_cell {W₁ a₁ w₀ c : WRes} {le : Loc} {s : LSet} {v : Val}
    {hs : w₀.InStratum s.join} {β : Life} (ha₁ : AgW W₁ a₁)
    (hle : W₁.get le = some (CellU.immOf s v w₀ hs)) (hr : ResU.Reb β w₀ c) {x : Loc}
    {ψ : CellU Loc Val} (e : c.get x = some ψ) :
    ICp a₁ x ψ ∨ ((∃ ζ : CellU Loc Val, w₀.get x = some ζ ∧ ζ.kind ≠ Kind.imm) ∧
      ψ.lsOf = some (LSet.singleton β)) := by
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
theorem img_ls {W₁ a₁ w₀ c d ad : WRes} {le : Loc} {s : LSet} {v : Val}
    {hs : w₀.InStratum s.join} {β : Life} (ha₁ : AgW W₁ a₁)
    (hle : W₁.get le = some (CellU.immOf s v w₀ hs)) (hr : ResU.Reb β w₀ c)
    (hsub : ∀ x (ψ : CellU Loc Val), d.get x = some ψ → c.get x = some ψ) (had : AgW d ad)
    {m : Loc} {ψ : CellU Loc Val} (e : ad.get m = some ψ) {t : LSet} (ht : ψ.lsOf = some t)
    {y : Life} (hy : t.mem y) :
    (∃ ζ t', a₁.get m = some ζ ∧ ζ.lsOf = some t' ∧ t'.mem y) ∨
    (y = β ∧ (∃ φ, d.get m = some φ) ∧
      ∃ ζ : CellU Loc Val, w₀.get m = some ζ ∧ ζ.kind ≠ Kind.imm) := by
  obtain ⟨d', bi, hc, hbi, hd'⟩ := img_walk ha₁ hle hr hsub had
  rcases ResU.CompR.lsOf_inv hc e ht hy with ⟨ξ, t₁, e₁, ht₁, hy₁⟩ | ⟨ξ, t₁, e₁, ht₁, hy₁⟩
  · have ed := hd' m ξ e₁
    rcases img_cell ha₁ hle hr (hsub m ξ ed) with hi | ⟨hz, hl⟩
    · exact Or.inl (hi.ls ht₁ hy₁)
    · rw [hl] at ht₁; cases Option.some.inj ht₁
      exact Or.inr ⟨hy₁, ⟨ξ, ed⟩, hz⟩
  · exact Or.inl ((hbi m ξ e₁).ls ht₁ hy₁)

/-- Nested views are shorter than their parents.  At a chain position `ℓ` with parent
`ℓ₀`, every lifetime of the view at `ℓ` in `ag(W)` is shorter than some lifetime of the view
at `ℓ₀`.  This is `[TR]` 6.150's H11 choice (`β ⊏ γᵢ ⊓ γ_b`, taken below every lifetime of the
world) read at the view a `withload` inside a `withload` makes: the inner `β′` is shorter than
the outer view's.  `[about ours: an invariant of the typed world]` -/
def NestLife (W : WRes) (r : FrameRec) : Prop :=
  ∀ l₀ l S u, Chain r.R r.T r.v (some l₀) l S u → ∀ a, AgW W a → ∀ (ψ : CellU Loc Val) s,
    a.get l = some ψ → ψ.lsOf = some s → ∀ x, s.mem x →
    ∃ (ζ : CellU Loc Val) (t : LSet) (y : Life), a.get l₀ = some ζ ∧ ζ.lsOf = some t ∧
      t.mem y ∧ x ⊏ y

/-- `NestLife` along a map that sends lifetimes of `ag(W′)`'s child views to `ag(W)` (or
finds the parent directly), and lifetimes of `ag(W)`'s parent views to `ag(W′)`. -/
theorem nestLife_of_maps {W W' aW : WRes} {r : FrameRec} (hN : NestLife W r)
    (haW : AgW W aW)
    (back : ∀ a', AgW W' a' → ∀ l₀ m S u, Chain r.R r.T r.v (some l₀) m S u →
      ∀ (ψ : CellU Loc Val) s x, a'.get m = some ψ → ψ.lsOf = some s → s.mem x →
      (∃ (ζ : CellU Loc Val) (t : LSet), aW.get m = some ζ ∧ ζ.lsOf = some t ∧ t.mem x) ∨
      (∃ (ζ : CellU Loc Val) (t : LSet) (y : Life), a'.get l₀ = some ζ ∧ ζ.lsOf = some t ∧
        t.mem y ∧ x ⊏ y))
    (fwd : ∀ a', AgW W' a' → ∀ l₀ m S u, Chain r.R r.T r.v (some l₀) m S u →
      ∀ (ζ : CellU Loc Val) t y, aW.get l₀ = some ζ → ζ.lsOf = some t → t.mem y →
      ∃ (ζ' : CellU Loc Val) (t' : LSet), a'.get l₀ = some ζ' ∧ ζ'.lsOf = some t' ∧ t'.mem y) :
    NestLife W' r := by
  intro l₀ m S u hc a' ha' ψ s e hs x hx
  rcases back a' ha' l₀ m S u hc ψ s x e hs hx with ⟨ζ, t, eζ, ht, hxt⟩ | hd
  · obtain ⟨ζ₀, t₀, y, e₀, ht₀, hy, hxy⟩ := hN l₀ m S u hc aW haW ζ t eζ ht x hxt
    obtain ⟨ζ', t', e', ht', hy'⟩ := fwd a' ha' l₀ m S u hc ζ₀ t₀ y e₀ ht₀ hy
    exact ⟨ζ', t', y, e', ht', hy', hxy⟩
  · exact hd

theorem nestLife_of_icp {W W' aW : WRes} {r : FrameRec} (hN : NestLife W r)
    (haW : AgW W aW)
    (back : ∀ a', AgW W' a' → ∀ l₀ m S u, Chain r.R r.T r.v (some l₀) m S u → ICpAt aW a' m)
    (fwd : ∀ a', AgW W' a' → ∀ l₀ m S u, Chain r.R r.T r.v (some l₀) m S u →
      ICpAt a' aW l₀) : NestLife W' r :=
  nestLife_of_maps hN haW
    (fun a' ha' l₀ m S u hc ψ _s _x e hs hx =>
      Or.inl ((back a' ha' l₀ m S u hc ψ e).ls hs hx))
    (fun a' ha' l₀ m S u hc ζ _t _y e ht hy => (fwd a' ha' l₀ m S u hc ζ e).ls ht hy)

/-- A step that keeps `ag` keeps `NestLife`. -/
theorem nestLife_of_ag {W W' : WRes} {r : FrameRec} (t : ∀ a, AgW W' a → AgW W a)
    (hN : NestLife W r) : NestLife W' r :=
  fun l₀ l S u hc a ha => hN l₀ l S u hc a (t a ha)

theorem leInv_of_reb {W W' c : WRes} {rs : List FrameRec} (hvW : ResU.Valid W)
    (hW : ResU.CompS W c W') (il : LeInv W rs) : LeInv W' rs := by
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  intro r' hr' a ha
  obtain ⟨ψ₀, e₀, k₀, r₀, w₀⟩ := il r' hr' aW haW
  obtain ⟨aW', ac, haW', -, hcomp⟩ := (AgW.split hW).mp ha
  rw [AgW.functional haW' haW] at hcomp
  obtain ⟨ψ, e, k, r'', w⟩ := imm_fwd_full_l hcomp e₀ k₀
  exact ⟨ψ, e, k, r''.trans r₀, w.trans w₀⟩

/-- At a `Mut` position a typed escrow holds a `mut` cell (`𝒱⟦Mut @a S⟧`'s
`ℓ ↦ Mut @a 𝒱⟦S⟧`, reached through the `⊗`, `⊕` and `[@a]` clauses). -/
theorem mut_split {δ : LSub} {T : VTy} {v : Val} {m : Loc} {S : VTy} (hp : MutPos T v m S) :
    ∀ {R : WRes}, vShape T δ v R → ∃ ζ : CellU Loc Val, R.get m = some ζ ∧ ζ.kind = Kind.mut := by
  induction hp with
  | «mut» a S l =>
      intro R hR
      obtain ⟨α', -, l'', hk'⟩ := hR
      obtain ⟨hl', -, ⟨b, w', W', hW', Q, hQ, -, rfl, -⟩, -⟩ := pure_sep_iff.mp hk'
      have : l = l'' := by have := congrArg Subtype.val hl'; simpa using this
      subst this
      exact ⟨_, ResU.single_get_self _ _, by simp⟩
  | tensorL _ ih =>
      intro R hR
      obtain ⟨a', b', hk'⟩ := hR
      obtain ⟨he', R₁, R₂, hRR, h₁', -⟩ := pure_sep_iff.mp hk'
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he'
      obtain ⟨ζ, eζ, kζ⟩ := ih h₁'
      obtain ⟨ζ', eζ', kζ', -, -⟩ := compS_get_left' hRR eζ
      exact ⟨ζ', eζ', kζ'.trans kζ⟩
  | tensorR _ ih =>
      intro R hR
      obtain ⟨a', b', hk'⟩ := hR
      obtain ⟨he', R₁, R₂, hRR, -, h₂'⟩ := pure_sep_iff.mp hk'
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he'
      obtain ⟨ζ, eζ, kζ⟩ := ih h₂'
      obtain ⟨ζ', eζ', kζ', -, -⟩ := compS_get_right' hRR eζ
      exact ⟨ζ', eζ', kζ'.trans kζ⟩
  | sumL _ ih =>
      intro R hR
      rcases hR with ⟨b, hk'⟩ | ⟨b, hk'⟩
      · obtain ⟨he', h₁'⟩ := pure_sep_iff.mp hk'
        cases Val.inj₁_inj' he'
        exact ih h₁'
      · obtain ⟨he', -⟩ := pure_sep_iff.mp hk'
        exact (Val.inj₁_ne_inj₂ he').elim
  | sumR _ ih =>
      intro R hR
      rcases hR with ⟨b, hk'⟩ | ⟨b, hk'⟩
      · obtain ⟨he', -⟩ := pure_sep_iff.mp hk'
        exact (Val.inj₁_ne_inj₂ he'.symm).elim
      · obtain ⟨he', h₂'⟩ := pure_sep_iff.mp hk'
        cases Val.inj₂_inj' he'
        exact ih h₂'
  | box _ ih =>
      intro R hR
      obtain ⟨α, -, hb, -⟩ := hR
      exact ih hb
  | mu _ _ ih =>
      intro R hR
      exact ih (vShape_unfold hR).2

/-- A typed reborrow's cell over a `mut` cell sits at a `Mut` position — the `Mut @a S`
clause of `Imm̲` (`[CONF]` Fig. 9, `[TR]` 6.122), carried up through `⊗`, `⊕` and `[@a]`.
`[about ours: a typed reborrow's image against the positions of its type]` -/
theorem image_dom_mut {x : LifeVar} {δ δ' : LSub} :
    ∀ (T : VTy) {v : Val} {c R : WRes}, vShape (T.immReborrow (.var x)) δ' v c →
      vShape T δ v R → ∀ {m : Loc} {ψ : CellU Loc Val}, c.get m = some ψ →
      ∀ {ζ : CellU Loc Val}, R.get m = some ζ → ζ.kind = Kind.mut → ∃ S, MutPos T v m S := by
  intro T v c R hc hR
  revert c
  refine vShape_ind δ (fun T v R => ∀ {c : WRes}, vShape (T.immReborrow (.var x)) δ' v c →
      ∀ {m : Loc} {ψ : CellU Loc Val}, c.get m = some ψ →
      ∀ {ζ : CellU Loc Val}, R.get m = some ζ → ζ.kind = Kind.mut → ∃ S, MutPos T v m S)
    ?_ T v R hR
  intro T v R hR c hc m ψ e ζ eζ kζ
  have hRv : vShape T δ v R := (sF_vShape δ T v R).mpr (sF_mono (fun _ _ _ h => h.1) δ T v R hR)
  cases T with
  | unit =>
      rw [empty_of_pure hc, PMap.empty_get] at e; cases e
  | int w =>
      rw [empty_of_pure hc, PMap.empty_get] at e; cases e
  | sum T₁ T₂ =>
      rcases hc with ⟨a, hk⟩ | ⟨a, hk⟩ <;> rcases hR with ⟨b, hk'⟩ | ⟨b, hk'⟩
      · obtain ⟨he, h₁⟩ := pure_sep_iff.mp hk
        obtain ⟨he', h₁'⟩ := pure_sep_iff.mp hk'
        subst he; cases Val.inj₁_inj' he'
        obtain ⟨S, hS⟩ := h₁'.2 h₁ e eζ kζ
        exact ⟨S, MutPos.sumL hS⟩
      · obtain ⟨he, -⟩ := pure_sep_iff.mp hk
        obtain ⟨he', -⟩ := pure_sep_iff.mp hk'
        subst he; exact (Val.inj₁_ne_inj₂ he').elim
      · obtain ⟨he, -⟩ := pure_sep_iff.mp hk
        obtain ⟨he', -⟩ := pure_sep_iff.mp hk'
        subst he; exact (Val.inj₁_ne_inj₂ he'.symm).elim
      · obtain ⟨he, h₂⟩ := pure_sep_iff.mp hk
        obtain ⟨he', h₂'⟩ := pure_sep_iff.mp hk'
        subst he; cases Val.inj₂_inj' he'
        obtain ⟨S, hS⟩ := h₂'.2 h₂ e eζ kζ
        exact ⟨S, MutPos.sumR hS⟩
  | tensor T₁ T₂ =>
      obtain ⟨a, b, hk⟩ := hc
      obtain ⟨he, c₁, c₂, hcc, h₁, h₂⟩ := pure_sep_iff.mp hk
      obtain ⟨a', b', hk'⟩ := hR
      obtain ⟨he', R₁, R₂, hRR, h₁', h₂'⟩ := pure_sep_iff.mp hk'
      subst he
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he'
      rcases back_some hcc e with ⟨ψ₁, e₁⟩ | ⟨ψ₂, e₂⟩
      · obtain ⟨ζ₁, eζ₁, -⟩ := image_dom T₁ h₁ h₁'.1 e₁
        obtain ⟨ζ', eζ', kζ', -, -⟩ := compS_get_left' hRR eζ₁
        rw [eζ] at eζ'; cases Option.some.inj eζ'
        obtain ⟨S, hS⟩ := h₁'.2 h₁ e₁ eζ₁ (kζ'.symm.trans kζ)
        exact ⟨S, MutPos.tensorL hS⟩
      · obtain ⟨ζ₂, eζ₂, -⟩ := image_dom T₂ h₂ h₂'.1 e₂
        obtain ⟨ζ', eζ', kζ', -, -⟩ := compS_get_right' hRR eζ₂
        rw [eζ] at eζ'; cases Option.some.inj eζ'
        obtain ⟨S, hS⟩ := h₂'.2 h₂ e₂ eζ₂ (kζ'.symm.trans kζ)
        exact ⟨S, MutPos.tensorR hS⟩
  | thunk _ =>
      rw [empty_of_pure hc, PMap.empty_get] at e; cases e
  | ref S =>
      obtain ⟨ζ', eζ', hown⟩ := image_dom (.ref S) hc hRv e
      rw [eζ] at eζ'; cases Option.some.inj eζ'
      obtain ⟨α, -, l', hk⟩ := hc
      obtain ⟨hl, s, w, W, hW, rfl, -, -⟩ := pure_sep_iff.mp hk
      obtain ⟨rfl, -⟩ := ResU.single_get_eq_some e
      obtain ⟨l'', u, hk'⟩ := hR
      obtain ⟨hl', ρa, ρb, hab, hown', -⟩ := pure_sep_iff.mp hk'
      have hl'' : m = l'' := by
        have := congrArg Subtype.val (hl.symm.trans hl'); simpa using this
      subst hl''
      rw [show ρa = ResU.single m (CellU.ownOf u) from hown'] at hab
      have := (ResU.CompS.get_left_of_ne_imm hab (ResU.single_get_self _ _) (by simp)).2
      rw [eζ] at this; cases Option.some.inj this
      exact absurd kζ (by simp)
  | bang S =>
    rw [empty_of_pure hc, PMap.empty_get] at e; cases e
  | imm a S =>
      obtain ⟨α', -, l'', hk'⟩ := hR
      obtain ⟨hl', s', w', W', hW', rfl, -, -⟩ := pure_sep_iff.mp hk'
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some eζ
      exact absurd kζ (by simp)
  | «mut» a S =>
      obtain ⟨α, -, l', hk⟩ := hc
      obtain ⟨hl, s, w, W, hW, rfl, -, -⟩ := pure_sep_iff.mp hk
      obtain ⟨rfl, -⟩ := ResU.single_get_eq_some e
      have hv : v = Val.loc m := hl
      subst hv
      exact ⟨S, MutPos.mut a S m⟩
  | box a T =>
      obtain ⟨α, -, hb, -⟩ := hR
      obtain ⟨S, hS⟩ := hb.2 hc e eζ kζ
      exact ⟨S, MutPos.box hS⟩
  | zero => exact False.elim hc
  | unk =>
      rw [empty_of_pure hc, PMap.empty_get] at e; cases e
  | tvar n => exact hR.elim
  | mu A =>
      obtain ⟨hcl, hG⟩ := hR
      obtain ⟨S, hS⟩ := hG.2 ((vShape_immReborrow_mu_iff (show A.Cl 1 from hcl) _ _ v c).mp hc)
        e eζ kζ
      exact ⟨S, MutPos.mu hcl hS⟩

/-- A cell of a valid world that is neither `imm` nor absent at the top keeps `ag` off its
location. -/
theorem ag_none_of_top {W a : WRes} (hv : ResU.Valid W) (ha : AgW W a) {m : Loc}
    {φ : CellU Loc Val} (e : W.get m = some φ) (hk : φ.kind ≠ Kind.imm) : a.get m = none := by
  obtain ⟨σ, eW, aW, heW, haW, hc⟩ := hv
  cases e' : a.get m with
  | none => rfl
  | some ζ =>
      rw [AgW.functional haW ha] at hc
      exact (ex_ag_disjoint ⟨σ, eW, a, heW, ha, hc⟩ heW ha (ExS.get_of_ne_imm heW e hk) e').elim

theorem lfree_immReborrow {x y : LifeVar} (T : VTy) :
    VFree y (T.immReborrow (.var x)) → y = x ∨ VFree y T :=
  vFree_immReborrow T

/-- A position's pointee type has no free variable its outer type lacks. -/
theorem RefPos.free {T : VTy} {v : Val} {l : Loc} {S : VTy} (h : RefPos T v l S) {y : LifeVar}
    (hy : VFree y S) : VFree y T := by
  by_contra hn
  exact RefPos.not_free h hn hy

/-- At agreeing substitutions, `𝒱⟦Imm̲ 'x T⟧` is one predicate. -/
theorem vShape_immReb_agree {T : VTy} {δ' δ : LSub} (h : AgreeOn T δ' δ) (x : LifeVar)
    (β : Life) :
    vShape (T.immReborrow (.var x)) (δ'.extend x β) = vShape (T.immReborrow (.var x)) (δ.extend x β) := by
  refine vShape_congr _ (fun y hy => ?_)
  rcases lfree_immReborrow _ hy with rfl | hy'
  · rw [find?_extend_self, find?_extend_self]
  · by_cases hxy : x = y
    · subst hxy; rw [find?_extend_self, find?_extend_self]
    · rw [find?_extend_ne _ _ hxy, find?_extend_ne _ _ hxy]; exact h y hy'

/-- A reborrow's view at a root is coherent: the type it puts there is `Imm 'x S` at
`δ[x↦β]`, `S` the root's pointee, and `x ∉ FV(S)`. -/
theorem coh_root {rs : List FrameRec} {r : FrameRec} (hr : r ∈ rs) {x : LifeVar} {β : Life}
    (hx : ¬ VFree x r.T) {m : Loc} {S : VTy} {u : Val} (hpos : RefPos r.T r.v m S)
    (hown : r.R.get m = some (CellU.ownOf u)) : Coh rs m S (r.δ.extend x β) := by
  refine Or.inr ⟨r, hr, none, u, Chain.one hpos hown, fun y hy => ?_⟩
  have hxy : x ≠ y := fun e => RefPos.not_free hpos hx (e ▸ hy)
  exact find?_extend_ne _ _ hxy

/-- …and at a child of a chain position, for a reborrow run at a coherent `δ′`. -/
theorem coh_child {rs : List FrameRec} {r : FrameRec} (hr : r ∈ rs) {p : Option Loc}
    {l₀ : Loc} {S₀ : VTy} {u₀ : Val} (hch : Chain r.R r.T r.v p l₀ S₀ u₀) {δ' : LSub}
    (hag : AgreeOn S₀ δ' r.δ) {x : LifeVar} {β : Life} (hx : ¬ VFree x S₀) {m : Loc}
    {S : VTy} {u : Val} (hpos : RefPos S₀ u₀ m S) (hown : r.R.get m = some (CellU.ownOf u)) :
    Coh rs m S (δ'.extend x β) := by
  refine Or.inr ⟨r, hr, some l₀, u, hch.snoc hpos hown, fun y hy => ?_⟩
  have hxy : x ≠ y := fun e => RefPos.not_free hpos hx (e ▸ hy)
  rw [find?_extend_ne _ _ hxy]
  exact hag y (hpos.free hy)

/-- `XPath ρ p σ`: `σ` is `ρ`, or the witness of a `mut` cell of an `XPath` resource; `p`
lists the `mut` locations passed.  `[about ours: the recursion of `ex`'s third factor, named]` -/
inductive XPath : WRes → List Loc → WRes → Prop
  | nil (ρ : WRes) : XPath ρ [] ρ
  | cons {ρ σ : WRes} {m : Loc} {ψ : CellU Loc Val} {p : List Loc} :
      ρ.get m = some ψ → ψ.kind = Kind.mut → XPath ψ.wit p σ → XPath ρ (m :: p) σ

/-- A non-`imm` cell of a member of a `●`-fold is the fold's. -/
theorem bigComp_get_of_ne_imm {L : List WRes} {b : WRes}
    (hb : BigComp CellU.CompatS CellU.CompS L b) {τ : WRes} (hτ : τ ∈ L) {x : Loc}
    {ζ : CellU Loc Val} (e : τ.get x = some ζ) (hk : ζ.kind ≠ Kind.imm) : b.get x = some ζ := by
  obtain ⟨z, hz⟩ := BigComp.mem_factor hSS ResU.compLawsS hb τ hτ
  exact (ResU.CompS.get_left_of_ne_imm hz e hk).2

/-- Two entries of a `●`-fold at different sites carry no non-`imm` cell at one location. -/
theorem bigComp_two {x : Loc} :
    ∀ {w : List (Loc × WRes)} {b : WRes}, BigComp CellU.CompatS CellU.CompS (w.map Prod.snd) b →
      ∀ {q₁ q₂ : Loc × WRes}, q₁ ∈ w → q₂ ∈ w → q₁.1 ≠ q₂.1 →
      ∀ {ζ₁ ζ₂ : CellU Loc Val}, q₁.2.get x = some ζ₁ → ζ₁.kind ≠ Kind.imm →
      q₂.2.get x = some ζ₂ → ζ₂.kind ≠ Kind.imm → False
  | [], _, _, _, _, h₁, _, _, _, _, _, _, _, _ => absurd h₁ (by simp)
  | a :: w, b, hb, q₁, q₂, h₁, h₂, hne, ζ₁, ζ₂, e₁, k₁, e₂, k₂ => by
      cases hb with
      | cons hrest hc =>
          rcases List.mem_cons.mp h₁ with rfl | h₁' <;> rcases List.mem_cons.mp h₂ with rfl | h₂'
          · exact hne rfl
          · have := bigComp_get_of_ne_imm hrest (List.mem_map.mpr ⟨_, h₂', rfl⟩) e₂ k₂
            rw [ResU.CompatS.right_eq_none hc.1 e₁ k₁] at this; cases this
          · have := bigComp_get_of_ne_imm hrest (List.mem_map.mpr ⟨_, h₁', rfl⟩) e₁ k₁
            rw [ResU.CompatS.right_eq_none hc.1 e₂ k₂] at this; cases this
          · exact bigComp_two hrest h₁' h₂' hne e₁ k₁ e₂ k₂

/-- A non-`imm` cell reached through `mut` witnesses is a cell of `ex(ρ)_●`. -/
theorem xpath_ex {ρ e : WRes} (h : ExS ρ e) :
    ∀ {p : List Loc} {σ : WRes}, XPath ρ p σ → ∀ {x : Loc} {ζ : CellU Loc Val},
      σ.get x = some ζ → ζ.kind ≠ Kind.imm → e.get x = some ζ := by
  refine ExW.rec (motive_1 := fun ρ e _ => ∀ {p : List Loc} {σ : WRes}, XPath ρ p σ →
      ∀ {x : Loc} {ζ : CellU Loc Val}, σ.get x = some ζ → ζ.kind ≠ Kind.imm → e.get x = some ζ)
    (motive_2 := fun ρ w _ => ∀ q ∈ w, ∀ ψ : CellU Loc Val, ρ.get q.1 = some ψ →
      ∀ {p : List Loc} {σ : WRes}, XPath ψ.wit p σ →
      ∀ {x : Loc} {ζ : CellU Loc Val}, σ.get x = some ζ → ζ.kind ≠ Kind.imm → q.2.get x = some ζ)
    ?mk ?nil ?cons h
  case mk =>
    intro ρ σ nm b w hs hw hb hnm hσ ih p τ hp x ζ ex kx
    cases hp with
    | nil => exact ExS.get_of_ne_imm (ExW.mk hs hw hb hnm hσ) ex kx
    | @cons _ _ m ψ q em km hq =>
        obtain ⟨pr, hpr, hpr1⟩ := List.mem_map.mp ((hs.2 m).mpr ⟨ψ, em, km⟩)
        have e₁ := ih pr hpr ψ (hpr1 ▸ em) hq ex kx
        have e₂ := bigComp_get_of_ne_imm hb (List.mem_map.mpr ⟨pr, hpr, rfl⟩) e₁ kx
        exact (ResU.CompS.get_right_of_ne_imm hσ e₂ kx).2
  case nil => intro ρ q hq; exact absurd hq (by simp)
  case cons =>
    intro ρ e l w ψ hψ hk he hw ihe ihw q hq ψ' eψ' p σ hp x ζ ex kx
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [hψ] at eψ'; cases Option.some.inj eψ'
      exact ihe hp ex kx
    · exact ihw q hq ψ' eψ' hp ex kx

/-- …at one path only. -/
theorem xpath_unique {ρ e : WRes} (h : ExS ρ e) :
    ∀ {p₁ : List Loc} {σ₁ : WRes}, XPath ρ p₁ σ₁ → ∀ {p₂ : List Loc} {σ₂ : WRes},
      XPath ρ p₂ σ₂ → ∀ {x : Loc} {ζ₁ ζ₂ : CellU Loc Val},
      σ₁.get x = some ζ₁ → ζ₁.kind ≠ Kind.imm → σ₂.get x = some ζ₂ → ζ₂.kind ≠ Kind.imm →
      p₁ = p₂ := by
  refine ExW.rec (motive_1 := fun ρ e _ => ∀ {p₁ : List Loc} {σ₁ : WRes}, XPath ρ p₁ σ₁ →
      ∀ {p₂ : List Loc} {σ₂ : WRes}, XPath ρ p₂ σ₂ → ∀ {x : Loc} {ζ₁ ζ₂ : CellU Loc Val},
      σ₁.get x = some ζ₁ → ζ₁.kind ≠ Kind.imm → σ₂.get x = some ζ₂ → ζ₂.kind ≠ Kind.imm →
      p₁ = p₂)
    (motive_2 := fun ρ w _ => ∀ q ∈ w, ∃ ψ : CellU Loc Val, ρ.get q.1 = some ψ ∧
      ExS ψ.wit q.2 ∧ ∀ {p₁ : List Loc} {σ₁ : WRes}, XPath ψ.wit p₁ σ₁ →
      ∀ {p₂ : List Loc} {σ₂ : WRes}, XPath ψ.wit p₂ σ₂ → ∀ {x : Loc} {ζ₁ ζ₂ : CellU Loc Val},
      σ₁.get x = some ζ₁ → ζ₁.kind ≠ Kind.imm → σ₂.get x = some ζ₂ → ζ₂.kind ≠ Kind.imm →
      p₁ = p₂)
    ?mk ?nil ?cons h
  case mk =>
    intro ρ σ nm b w hs hw hb hnm hσ ih p₁ σ₁ h₁ p₂ σ₂ h₂ x ζ₁ ζ₂ e₁ k₁ e₂ k₂
    -- a path through `mut` site `m` puts `x` in `b`
    have viaB : ∀ {m : Loc} {ψ : CellU Loc Val} {q : List Loc} {τ : WRes} {ζ : CellU Loc Val},
        ρ.get m = some ψ → ψ.kind = Kind.mut → XPath ψ.wit q τ → τ.get x = some ζ →
        ζ.kind ≠ Kind.imm → ∃ pr ∈ w, pr.1 = m ∧ pr.2.get x = some ζ := by
      intro m ψ q τ ζ em km hq eτ kτ
      obtain ⟨pr, hpr, hpr1⟩ := List.mem_map.mp ((hs.2 m).mpr ⟨ψ, em, km⟩)
      obtain ⟨ψ', eψ', hex, -⟩ := ih pr hpr
      rw [hpr1, em] at eψ'; cases Option.some.inj eψ'
      exact ⟨pr, hpr, hpr1, xpath_ex hex hq eτ kτ⟩
    have topNone : ∀ {ζ : CellU Loc Val}, ρ.get x = some ζ → ζ.kind ≠ Kind.imm →
        b.get x = none := by
      intro ζ eρ kρ
      have enm : nm.get x = some ζ := by
        cases hkk : ζ.kind with
        | own => exact (ResU.CompS.get_left_of_ne_imm hnm (ResU.restrict_get_some eρ hkk) kρ).2
        | imm => exact absurd hkk kρ
        | «mut» => exact (ResU.CompS.get_right_of_ne_imm hnm (ResU.restrict_get_some eρ hkk) kρ).2
      exact ResU.CompatS.right_eq_none hσ.1 enm kρ
    cases h₁ with
    | nil =>
        cases h₂ with
        | nil => rfl
        | cons em km hq =>
            obtain ⟨pr, hpr, -, epr⟩ := viaB em km hq e₂ k₂
            have := bigComp_get_of_ne_imm hb (List.mem_map.mpr ⟨pr, hpr, rfl⟩) epr k₂
            rw [topNone e₁ k₁] at this; cases this
    | @cons _ _ m₁ ψ₁ q₁ em₁ km₁ hq₁ =>
        cases h₂ with
        | nil =>
            obtain ⟨pr, hpr, -, epr⟩ := viaB em₁ km₁ hq₁ e₁ k₁
            have := bigComp_get_of_ne_imm hb (List.mem_map.mpr ⟨pr, hpr, rfl⟩) epr k₁
            rw [topNone e₂ k₂] at this; cases this
        | @cons _ _ m₂ ψ₂ q₂ em₂ km₂ hq₂ =>
            obtain ⟨pr₁, hpr₁, hm₁, epr₁⟩ := viaB em₁ km₁ hq₁ e₁ k₁
            obtain ⟨pr₂, hpr₂, hm₂, epr₂⟩ := viaB em₂ km₂ hq₂ e₂ k₂
            by_cases hm : m₁ = m₂
            · subst hm
              rw [em₁] at em₂; cases Option.some.inj em₂
              have hpp : pr₁ = pr₂ :=
                List.inj_on_of_nodup_map hs.1 hpr₁ hpr₂ (hm₁.trans hm₂.symm)
              subst hpp
              obtain ⟨ψ', eψ', -, ihu⟩ := ih pr₁ hpr₁
              rw [hm₁, em₁] at eψ'; cases Option.some.inj eψ'
              rw [ihu hq₁ hq₂ e₁ k₁ e₂ k₂]
            · exact (bigComp_two hb hpr₁ hpr₂ (by rw [hm₁, hm₂]; exact hm) epr₁ k₁ epr₂ k₂).elim
  case nil => intro ρ q hq; exact absurd hq (by simp)
  case cons =>
    intro ρ e l w ψ hψ hk he hw ihe ihw q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨ψ, hψ, he, ihe⟩
    · exact ihw q hq

theorem not_mutAt_ex_own_aux {x : Loc} {u : Val} {ρ : WRes} (h : MutAt ρ x) :
    ∀ {eρ aρ : WRes}, ExS ρ eρ → AgW ρ aρ → eρ.get x = some (CellU.ownOf u) →
      aρ.get x = none → False := by
  induction h with
  | top e hk =>
      intro eρ aρ he _ ho _
      rw [ExS.get_of_ne_imm he e (by rw [hk]; simp)] at ho
      cases Option.some.inj ho; exact absurd hk (by simp)
  | @nest ρ x m ψ e hk hmw ih =>
      intro eρ aρ he ha ho hn
      cases hkk : ψ.kind with
      | own => exact hk hkk
      | imm =>
          obtain ⟨ev, av, p, z, hev, hav, hp, hz⟩ := AgW.imm_wit_le ha e hkk
          rcases mutAt_walk_dom hmw hRR ResU.compLawsR hev hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
          · obtain ⟨_, h1⟩ := comp_some hp hζ
            obtain ⟨_, h2⟩ := comp_some hz h1
            rw [hn] at h2; cases h2
          · obtain ⟨_, h1⟩ := comp_some_r hp hζ
            obtain ⟨_, h2⟩ := comp_some hz h1
            rw [hn] at h2; cases h2
      | «mut» =>
          obtain ⟨av, z, hav, hz⟩ := AgW.mut_wit_le ha e hkk
          cases he with
          | mk hs hw hb hnm hσ =>
              rename_i nm b w
              obtain ⟨q, hq, hq₁⟩ := List.mem_map.mp ((hs.2 m).mpr ⟨ψ, e, hkk⟩)
              obtain ⟨ψ', hψ', hex'⟩ := ExWits.mem hw q hq
              rw [hq₁, e] at hψ'
              cases Option.some.inj hψ'
              have avn : av.get x = none := by
                cases eav : av.get x with
                | none => rfl
                | some ζ =>
                    obtain ⟨_, h1⟩ := comp_some hz eav
                    rw [hn] at h1; cases h1
              rcases mutAt_walk_dom hmw hSS ResU.compLawsS hex' hav with ⟨ζ, hζ⟩ | ⟨ζ, hζ⟩
              · have kζ : ζ.kind ≠ Kind.imm := ExS.immFree hex' x ζ hζ
                have eb := bigComp_get_of_ne_imm hb (List.mem_map.mpr ⟨q, hq, rfl⟩) hζ kζ
                have eσ := (ResU.CompS.get_right_of_ne_imm hσ eb kζ).2
                rw [ho] at eσ; cases Option.some.inj eσ
                exact ih hex' hav hζ avn
              · rw [avn] at hζ; cases hζ

/-- An `own` cell of `ex(W)_●` is borrowed mutably nowhere in `W`.  `not_mutAt_top_own`
at every depth `ex` descends to. -/
theorem not_mutAt_ex_own {W e : WRes} (hv : ResU.Valid W) (he : ExS W e) {x : Loc} {u : Val}
    (hx : e.get x = some (CellU.ownOf u)) : ¬ MutAt W x := by
  intro hm
  obtain ⟨a, ha⟩ := agW_of_valid hv
  have hn : a.get x = none := by
    cases e' : a.get x with
    | none => rfl
    | some ζ => exact (ex_ag_disjoint hv he ha hx e').elim
  exact not_mutAt_ex_own_aux hm he ha hx hn

/-- `○` keeps the value of either operand, and the witness and non-`own`ness of a non-`own`
operand. -/
theorem CellU.CompR.lift_full {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompR ψ₁ ψ₂ ψ) :
    ψ.erase = ψ₁.erase ∧ (ψ₁.kind ≠ Kind.own → ψ.kind ≠ Kind.own ∧ ψ.wit = ψ₁.wit) := by
  cases h with
  | same => exact ⟨rfl, fun hk => ⟨hk, rfl⟩⟩
  | strict k =>
      obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, e₁, e₂, e₃⟩ := CellU.compS_spec _ _ k
      rw [e₃, e₁]
      exact ⟨by simp, fun _ => ⟨by simp, by simp⟩⟩
  | mutMut => exact ⟨by simp, fun _ => ⟨by simp, by simp⟩⟩
  | mutOwn => exact ⟨rfl, fun hk => ⟨hk, rfl⟩⟩
  | ownMut => exact ⟨by simp, fun hk => absurd (by simp) hk⟩
  | immOwn => exact ⟨rfl, fun hk => ⟨hk, rfl⟩⟩
  | ownImm => exact ⟨by simp, fun hk => absurd (by simp) hk⟩
  | immMut => exact ⟨rfl, fun hk => ⟨hk, rfl⟩⟩
  | mutImm => exact ⟨by simp, fun _ => ⟨by simp, by simp⟩⟩

/-- `Lifts e a`: every cell of `e` has one in `a` at its location, over its value, and a
non-`own` one over its witness.  `[about ours: "is a `○`-part of", pointwise]` -/
def Lifts (e a : WRes) : Prop :=
  ∀ x (ψ : CellU Loc Val), e.get x = some ψ → ∃ ζ : CellU Loc Val, a.get x = some ζ ∧
    ζ.erase = ψ.erase ∧ (ψ.kind ≠ Kind.own → ζ.kind ≠ Kind.own ∧ ζ.wit = ψ.wit)

theorem Lifts.trans {e b a : WRes} (h₁ : Lifts e b) (h₂ : Lifts b a) : Lifts e a := by
  intro x ψ ex
  obtain ⟨ζ, eζ, rζ, wζ⟩ := h₁ x ψ ex
  obtain ⟨ξ, eξ, rξ, wξ⟩ := h₂ x ζ eζ
  refine ⟨ξ, eξ, rξ.trans rζ, fun hk => ?_⟩
  obtain ⟨k₁, w₁⟩ := wζ hk
  obtain ⟨k₂, w₂⟩ := wξ k₁
  exact ⟨k₂, w₂.trans w₁⟩

theorem lifts_left {a₁ a₂ a : WRes} (h : ResU.CompR a₁ a₂ a) : Lifts a₁ a := by
  intro x ψ e
  rcases ResU.Comp.get h x with ⟨e₁, -, -⟩ | ⟨χ, e₁, -, e'⟩ | ⟨χ, e₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, e₁, -, e', hC⟩
  · rw [e] at e₁; cases e₁
  · rw [e] at e₁; cases Option.some.inj e₁; exact ⟨_, e', rfl, fun hk => ⟨hk, rfl⟩⟩
  · rw [e] at e₁; cases e₁
  · rw [e] at e₁; cases Option.some.inj e₁
    exact ⟨χ, e', (CellU.CompR.lift_full hC).1, (CellU.CompR.lift_full hC).2⟩

theorem lifts_right {a₁ a₂ a : WRes} (h : ResU.CompR a₁ a₂ a) : Lifts a₂ a :=
  lifts_left (ResU.CompR.comm h)

/-- `ex(ρ)_○` of a `mut` witness of `ρ` is a `○`-part of `ex(ρ)_○`. -/
theorem exR_mut_wit {ρ e : WRes} (h : ExR ρ e) {m : Loc} {ψ : CellU Loc Val}
    (em : ρ.get m = some ψ) (km : ψ.kind = Kind.mut) : ∃ e', ExR ψ.wit e' ∧ Lifts e' e := by
  cases h with
  | mk hs hw hb hnm hσ =>
      obtain ⟨q, hq, hq₁⟩ := List.mem_map.mp ((hs.2 m).mpr ⟨ψ, em, km⟩)
      obtain ⟨ψ', hψ', hex'⟩ := ExWits.mem hw q hq
      rw [hq₁, em] at hψ'
      cases Option.some.inj hψ'
      obtain ⟨z, hz⟩ := BigComp.mem_factor hRR ResU.compLawsR hb q.2
        (List.mem_map.mpr ⟨q, hq, rfl⟩)
      exact ⟨q.2, hex', (lifts_left hz).trans (lifts_right hσ)⟩

/-- A non-`imm` cell of `ρ` is in `ex(ρ)_○`, over its value, and over its witness if not
`own` (`ExR.get_of_ne_imm`, as `Lifts`). -/
theorem exR_cell {ρ e : WRes} (h : ExR ρ e) {x : Loc} {ψ : CellU Loc Val}
    (ex : ρ.get x = some ψ) (hk : ψ.kind ≠ Kind.imm) : ∃ ζ : CellU Loc Val, e.get x = some ζ ∧
      ζ.erase = ψ.erase ∧ (ψ.kind ≠ Kind.own → ζ.kind ≠ Kind.own ∧ ζ.wit = ψ.wit) := by
  obtain ⟨χ, eχ, rχ, wχ⟩ := ExR.get_of_ne_imm h ex hk
  exact ⟨χ, eχ, rχ, fun hk' => ⟨(wχ hk').2, (wχ hk').1⟩⟩

theorem MutPos.inv_mut {a : Lifetime.Life} {S₀ S : VTy} {v : Val} {l : Loc}
    (h : MutPos (.mut a S₀) v l S) : v = Val.loc l ∧ S = S₀ := by
  cases h; exact ⟨rfl, rfl⟩

theorem MutPos.inv_tensor {T₁ T₂ S : VTy} {v : Val} {l : Loc}
    (h : MutPos (.tensor T₁ T₂) v l S) :
    ∃ v₁ v₂, v = Val.pair v₁ v₂ ∧ (MutPos T₁ v₁ l S ∨ MutPos T₂ v₂ l S) := by
  cases h with
  | tensorL h => exact ⟨_, _, rfl, Or.inl h⟩
  | tensorR h => exact ⟨_, _, rfl, Or.inr h⟩

theorem MutPos.inv_sum {T₁ T₂ S : VTy} {v : Val} {l : Loc} (h : MutPos (.sum T₁ T₂) v l S) :
    (∃ v₁, v = Val.inj₁ v₁ ∧ MutPos T₁ v₁ l S) ∨ (∃ v₂, v = Val.inj₂ v₂ ∧ MutPos T₂ v₂ l S) := by
  cases h with
  | sumL h => exact Or.inl ⟨_, rfl, h⟩
  | sumR h => exact Or.inr ⟨_, rfl, h⟩

theorem MutPos.inv_box {a : Lifetime.Life} {T S : VTy} {v : Val} {l : Loc}
    (h : MutPos (.box a T) v l S) : MutPos T v l S := by
  cases h with
  | box h => exact h

theorem MutPos.inv_mu {A S : VTy} {v : Val} {l : Loc} (h : MutPos (.mu A) v l S) :
    (VTy.mu A).Cl 0 ∧ MutPos (VTy.inst (.mu A) A) v l S := by
  cases h with
  | mu hc h => exact ⟨hc, h⟩

theorem MutPos.free {T : VTy} {v : Val} {l : Loc} {S : VTy} (h : MutPos T v l S) {y : LifeVar}
    (hy : VFree y S) : VFree y T := by
  induction h with
  | «mut» a S l => exact Or.inr hy
  | tensorL _ ih => exact Or.inl (ih hy)
  | tensorR _ ih => exact Or.inr (ih hy)
  | sumL _ ih => exact Or.inl (ih hy)
  | sumR _ ih => exact Or.inr (ih hy)
  | box _ ih => exact Or.inr (ih hy)
  | mu _ _ ih => exact (vFree_inst (ih hy)).elim id id

/-- At a `Mut @a S` position a typed escrow holds `ℓ ↦ mut(b, u, χ, Q̂)` with
`χ ∈ 𝒱⟦S⟧δ(u)` — `ptoMut`'s `ofS Q̂ = 𝒱⟦S⟧δ` read at the cell's own value and witness. -/
theorem mut_split_den {δ : LSub} {T : VTy} {v : Val} {m : Loc} {S : VTy} (hp : MutPos T v m S) :
    ∀ {R : WRes}, vShape T δ v R → ∃ ζ : CellU Loc Val, R.get m = some ζ ∧ ζ.kind = Kind.mut ∧
      vShape S δ ζ.erase ζ.wit := by
  induction hp with
  | «mut» a S l =>
      intro R hR
      obtain ⟨α', -, l'', hk'⟩ := hR
      obtain ⟨hl', P, ⟨b, w', W', hW', Q, hQ, -, rfl, hofs⟩, hsub⟩ := pure_sep_iff.mp hk'
      have : l = l'' := by have := congrArg Subtype.val hl'; simpa using this
      subst this
      refine ⟨_, ResU.single_get_self _ _, by simp, ?_⟩
      rw [CellU.erase_mutOf, CellU.wit_mutOf]
      refine hsub _ _ ?_
      rw [← hofs]
      exact ⟨hW', hQ⟩
  | tensorL _ ih =>
      intro R hR
      obtain ⟨a', b', hk'⟩ := hR
      obtain ⟨he', R₁, R₂, hRR, h₁', -⟩ := pure_sep_iff.mp hk'
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he'
      obtain ⟨ζ, eζ, kζ, dζ⟩ := ih h₁'
      exact ⟨ζ, (ResU.CompS.get_left_of_ne_imm hRR eζ (by rw [kζ]; simp)).2, kζ, dζ⟩
  | tensorR _ ih =>
      intro R hR
      obtain ⟨a', b', hk'⟩ := hR
      obtain ⟨he', R₁, R₂, hRR, -, h₂'⟩ := pure_sep_iff.mp hk'
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he'
      obtain ⟨ζ, eζ, kζ, dζ⟩ := ih h₂'
      exact ⟨ζ, (ResU.CompS.get_right_of_ne_imm hRR eζ (by rw [kζ]; simp)).2, kζ, dζ⟩
  | sumL _ ih =>
      intro R hR
      rcases hR with ⟨b, hk'⟩ | ⟨b, hk'⟩
      · obtain ⟨he', h₁'⟩ := pure_sep_iff.mp hk'
        cases Val.inj₁_inj' he'
        exact ih h₁'
      · obtain ⟨he', -⟩ := pure_sep_iff.mp hk'
        exact (Val.inj₁_ne_inj₂ he').elim
  | sumR _ ih =>
      intro R hR
      rcases hR with ⟨b, hk'⟩ | ⟨b, hk'⟩
      · obtain ⟨he', -⟩ := pure_sep_iff.mp hk'
        exact (Val.inj₁_ne_inj₂ he'.symm).elim
      · obtain ⟨he', h₂'⟩ := pure_sep_iff.mp hk'
        cases Val.inj₂_inj' he'
        exact ih h₂'
  | box _ ih =>
      intro R hR
      obtain ⟨α, -, hb, -⟩ := hR
      exact ih hb
  | mu _ _ ih =>
      intro R hR
      exact ih (vShape_unfold hR).2

theorem not_mut_both {B₁ B₂ X : WRes} (h : ResU.CompS B₁ B₂ X) {l : Loc}
    {ψ₁ ψ₂ : CellU Loc Val} (e₁ : B₁.get l = some ψ₁) (k₁ : ψ₁.kind ≠ Kind.imm)
    (e₂ : B₂.get l = some ψ₂) : False := by
  have := ResU.CompatS.right_eq_none h.1 e₁ k₁
  rw [e₂] at this; cases this

/-- Two `Mut` positions of a typed escrow at one location have one pointee type. -/
theorem mutPos_unique {δ : LSub} :
    ∀ (T : VTy) {v : Val} {R : WRes} {m : Loc} {S₁ S₂ : VTy}, vShape T δ v R →
      MutPos T v m S₁ → MutPos T v m S₂ → S₁ = S₂ := by
  intro T v R m S₁ S₂ hR h₁ h₂
  induction h₁ generalizing R S₂ with
  | «mut» a S₀ l => exact (MutPos.inv_mut h₂).2.symm
  | @tensorL T₁ T₂ v₁ v₂ l S h₁' ih =>
      obtain ⟨v₁', v₂', he, h₂'⟩ := MutPos.inv_tensor h₂
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he
      obtain ⟨a, b, hk⟩ := hR
      obtain ⟨he', R₁, R₂, hRR, hR₁, hR₂⟩ := pure_sep_iff.mp hk
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he'
      rcases h₂' with h₂' | h₂'
      · exact ih hR₁ h₂'
      · obtain ⟨ζ₁, e₁, k₁⟩ := mut_split h₁' hR₁
        obtain ⟨ζ₂, e₂, -⟩ := mut_split h₂' hR₂
        exact (not_mut_both hRR e₁ (by rw [k₁]; simp) e₂).elim
  | @tensorR T₁ T₂ v₁ v₂ l S h₁' ih =>
      obtain ⟨v₁', v₂', he, h₂'⟩ := MutPos.inv_tensor h₂
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he
      obtain ⟨a, b, hk⟩ := hR
      obtain ⟨he', R₁, R₂, hRR, hR₁, hR₂⟩ := pure_sep_iff.mp hk
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he'
      rcases h₂' with h₂' | h₂'
      · obtain ⟨ζ₁, e₁, -⟩ := mut_split h₁' hR₂
        obtain ⟨ζ₂, e₂, k₂⟩ := mut_split h₂' hR₁
        exact (not_mut_both hRR e₂ (by rw [k₂]; simp) e₁).elim
      · exact ih hR₂ h₂'
  | @sumL T₁ T₂ v₁ l S h₁' ih =>
      rcases MutPos.inv_sum h₂ with ⟨v₂, he, h₂'⟩ | ⟨v₂, he, h₂'⟩
      · cases Val.inj₁_inj' he
        rcases hR with ⟨a, hk⟩ | ⟨a, hk⟩
        · obtain ⟨he', hR'⟩ := pure_sep_iff.mp hk
          cases Val.inj₁_inj' he'
          exact ih hR' h₂'
        · obtain ⟨he', -⟩ := pure_sep_iff.mp hk
          exact (Val.inj₁_ne_inj₂ he').elim
      · exact (Val.inj₁_ne_inj₂ he).elim
  | @sumR T₁ T₂ v₁ l S h₁' ih =>
      rcases MutPos.inv_sum h₂ with ⟨v₂, he, h₂'⟩ | ⟨v₂, he, h₂'⟩
      · exact (Val.inj₁_ne_inj₂ he.symm).elim
      · cases Val.inj₂_inj' he
        rcases hR with ⟨a, hk⟩ | ⟨a, hk⟩
        · obtain ⟨he', -⟩ := pure_sep_iff.mp hk
          exact (Val.inj₁_ne_inj₂ he'.symm).elim
        · obtain ⟨he', hR'⟩ := pure_sep_iff.mp hk
          cases Val.inj₂_inj' he'
          exact ih hR' h₂'
  | box _ ih =>
      obtain ⟨α, -, hb, -⟩ := hR
      exact ih hb (MutPos.inv_box h₂)
  | mu _ _ ih => exact ih (vShape_unfold hR).2 (MutPos.inv_mu h₂).2

/-- A `Mut` position and a `Ref` position of a typed escrow have strictly composable
blocks: the `mut` cell, and the `Ref`'s `ℓ ↦ own(u) ● Q` with `Q ∈ 𝒱⟦S⟧δ(u)`. -/
theorem mut_ref_blocks {δ : LSub} :
    ∀ (T : VTy) {v : Val} {R : WRes} {m l : Loc} {S₁ S₂ : VTy}, vShape T δ v R →
      MutPos T v m S₁ → RefPos T v l S₂ →
      ∃ B₁ B₂ X u Q, (∃ ζ : CellU Loc Val, B₁.get m = some ζ ∧ ζ.kind = Kind.mut) ∧
        ResU.CompS (ResU.single l (CellU.ownOf u)) Q B₂ ∧ vShape S₂ δ u Q ∧
        ResU.CompS B₁ B₂ X ∧ ResU.Le X R := by
  intro T v R m l S₁ S₂ hR h₁ h₂
  induction h₁ generalizing R l S₂ with
  | «mut» a S₀ l₀ => cases h₂
  | @tensorL T₁ T₂ v₁ v₂ m₀ S h₁' ih =>
      obtain ⟨v₁', v₂', he, h₂'⟩ := RefPos.inv_tensor h₂
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he
      obtain ⟨a, b, hk⟩ := hR
      obtain ⟨he', R₁, R₂, hRR, hR₁, hR₂⟩ := pure_sep_iff.mp hk
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he'
      rcases h₂' with h₂' | h₂'
      · obtain ⟨B₁, B₂, X, u, Q, hm, hB, hQ, hX, hle⟩ := ih hR₁ h₂'
        exact ⟨B₁, B₂, X, u, Q, hm, hB, hQ, hX, hle.trans (le_of_compS_left hRR)⟩
      · obtain ⟨u, Q, B₂, hB, hQ, ⟨Y₂, hY₂⟩⟩ := own_split T₂ hR₂ h₂'
        obtain ⟨Y₁, hY₁⟩ := ResU.Le.refl R₁
        obtain ⟨X, hX, hle⟩ := sub_comp hY₁ hY₂ hRR
        exact ⟨R₁, B₂, X, u, Q, mut_split h₁' hR₁, hB, hQ, hX, hle⟩
  | @tensorR T₁ T₂ v₁ v₂ m₀ S h₁' ih =>
      obtain ⟨v₁', v₂', he, h₂'⟩ := RefPos.inv_tensor h₂
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he
      obtain ⟨a, b, hk⟩ := hR
      obtain ⟨he', R₁, R₂, hRR, hR₁, hR₂⟩ := pure_sep_iff.mp hk
      obtain ⟨rfl, rfl⟩ := Val.pair_inj' he'
      rcases h₂' with h₂' | h₂'
      · obtain ⟨u, Q, B₂, hB, hQ, ⟨Y₂, hY₂⟩⟩ := own_split T₁ hR₁ h₂'
        obtain ⟨Y₁, hY₁⟩ := ResU.Le.refl R₂
        obtain ⟨X, hX, hle⟩ := sub_comp hY₂ hY₁ hRR
        exact ⟨R₂, B₂, X, u, Q, mut_split h₁' hR₂, hB, hQ, ResU.CompS.comm hX, hle⟩
      · obtain ⟨B₁, B₂, X, u, Q, hm, hB, hQ, hX, hle⟩ := ih hR₂ h₂'
        exact ⟨B₁, B₂, X, u, Q, hm, hB, hQ, hX, hle.trans (le_of_compS_right hRR)⟩
  | @sumL T₁ T₂ v₁ m₀ S h₁' ih =>
      rcases RefPos.inv_sum h₂ with ⟨v₂, he, h₂'⟩ | ⟨v₂, he, h₂'⟩
      · cases Val.inj₁_inj' he
        rcases hR with ⟨a, hk⟩ | ⟨a, hk⟩
        · obtain ⟨he', hR'⟩ := pure_sep_iff.mp hk
          cases Val.inj₁_inj' he'
          exact ih hR' h₂'
        · obtain ⟨he', -⟩ := pure_sep_iff.mp hk
          exact (Val.inj₁_ne_inj₂ he').elim
      · exact (Val.inj₁_ne_inj₂ he).elim
  | @sumR T₁ T₂ v₁ m₀ S h₁' ih =>
      rcases RefPos.inv_sum h₂ with ⟨v₂, he, h₂'⟩ | ⟨v₂, he, h₂'⟩
      · exact (Val.inj₁_ne_inj₂ he.symm).elim
      · cases Val.inj₂_inj' he
        rcases hR with ⟨a, hk⟩ | ⟨a, hk⟩
        · obtain ⟨he', -⟩ := pure_sep_iff.mp hk
          exact (Val.inj₁_ne_inj₂ he'.symm).elim
        · obtain ⟨he', hR'⟩ := pure_sep_iff.mp hk
          cases Val.inj₂_inj' he'
          exact ih hR' h₂'
  | box _ ih =>
      obtain ⟨α, -, hb, -⟩ := hR
      exact ih hb (RefPos.inv_box h₂)
  | mu _ _ ih => exact ih (vShape_unfold hR).2 (RefPos.inv_mu h₂).2

theorem GPos.of_chain {R : WRes} {T : VTy} {v : Val} {p : Option Loc} {l₀ : Loc} {S₀ : VTy}
    {u₀ : Val} (h : Chain R T v p l₀ S₀ u₀) {m : Loc} {S : VTy} (hm : MutPos S₀ u₀ m S) :
    GPos R T v m S := by
  induction h with
  | one hp e => exact GPos.step hp e (GPos.here hm)
  | step hp e _ ih => exact GPos.step hp e (ih hm)

theorem GPos.free {R : WRes} {T : VTy} {v : Val} {m : Loc} {S : VTy} (h : GPos R T v m S)
    {y : LifeVar} (hy : VFree y S) : VFree y T := by
  induction h with
  | here hp => exact hp.free hy
  | step hp _ _ ih => exact hp.free (ih hy)

/-- At a `GPos` a typed piece holds the `mut` cell, its witness typed at the pointee. -/
theorem gpos_mut_cell {δ : LSub} {R : WRes} {T : VTy} {v : Val} {m : Loc} {S : VTy}
    (h : GPos R T v m S) :
    ∀ {P : WRes}, vShape T δ v P →
      (∀ x w, P.get x = some (CellU.ownOf w) → R.get x = some (CellU.ownOf w)) →
      ∃ ζ : CellU Loc Val, P.get m = some ζ ∧ ζ.kind = Kind.mut ∧ vShape S δ ζ.erase ζ.wit := by
  induction h with
  | here hp => intro P hP _; exact mut_split_den hp hP
  | @step T v l S₀ u₀ m S hp e _ ih =>
      intro P hP hag
      obtain ⟨u', Q, B, hB, hQ, hle⟩ := own_split T hP hp
      have eB := (ResU.CompS.get_left_of_ne_imm hB (ResU.single_get_self _ _) (by simp)).2
      have eP := own_of_le hle eB
      rw [hag l u' eP] at e
      cases Option.some.inj e
      have hleQ : ResU.Le Q P := (le_of_compS_right hB).trans hle
      obtain ⟨ζ, eζ, kζ, dζ⟩ := ih hQ (fun x w e' => hag x w (own_of_le hleQ e'))
      obtain ⟨τ, hτ⟩ := hleQ
      exact ⟨ζ, (ResU.CompS.get_left_of_ne_imm hτ eζ (by rw [kζ]; simp)).2, kζ, dζ⟩

/-- A `Mut` position against a `Ref` step whose pointee reaches the same location. -/
theorem gpos_cross {δ : LSub} {R : WRes} {m : Loc} {T : VTy} {v : Val} {P : WRes} {l : Loc}
    {S₀ : VTy} {u₀ : Val} {S₁ S₂ : VTy}
    (hP : vShape T δ v P) (hag : ∀ x w, P.get x = some (CellU.ownOf w) → R.get x = some (CellU.ownOf w))
    (hm : MutPos T v m S₁) (hr : RefPos T v l S₀) (e : R.get l = some (CellU.ownOf u₀))
    (t : GPos R S₀ u₀ m S₂) : False := by
  obtain ⟨B₁, B₂, X, u, Q, ⟨ζ, eζ, kζ⟩, hB, hQ, hX, hle⟩ := mut_ref_blocks T hP hm hr
  have hB₂P : ResU.Le B₂ P := (le_of_compS_right hX).trans hle
  have eB := (ResU.CompS.get_left_of_ne_imm hB (ResU.single_get_self _ _) (by simp)).2
  rw [hag l u (own_of_le hB₂P eB)] at e
  cases Option.some.inj e
  have hQP : ResU.Le Q P := (le_of_compS_right hB).trans hB₂P
  obtain ⟨ξ, eξ, kξ, -⟩ := gpos_mut_cell t hQ (fun x w e' => hag x w (own_of_le hQP e'))
  have eB₂ := (ResU.CompS.get_right_of_ne_imm hB eξ (by rw [kξ]; simp)).2
  exact not_mut_both hX eζ (by rw [kζ]; simp) eB₂

/-- A location of a typed escrow is at one `GPos` pointee type. -/
theorem gpos_unique {δ : LSub} {R : WRes} {T : VTy} {v : Val} {m : Loc} {S₁ : VTy}
    (h₁ : GPos R T v m S₁) :
    ∀ {P : WRes}, vShape T δ v P →
      (∀ x w, P.get x = some (CellU.ownOf w) → R.get x = some (CellU.ownOf w)) →
      ∀ {S₂ : VTy}, GPos R T v m S₂ → S₁ = S₂ := by
  induction h₁ with
  | @here T v m S₁ hp₁ =>
      intro P hP hag S₂ h₂
      cases h₂ with
      | here hp₂ => exact mutPos_unique T hP hp₁ hp₂
      | step hr e t => exact (gpos_cross hP hag hp₁ hr e t).elim
  | @step T v l₁ S₀ u₀ m S₁ hp₁ e₁ t₁ ih =>
      intro P hP hag S₂ h₂
      cases h₂ with
      | here hp₂ => exact (gpos_cross hP hag hp₂ hp₁ e₁ t₁).elim
      | @step _ _ l₂ S₀' u₀' _ _ hp₂ e₂ t₂ =>
          rcases refPos_blocks T hP hp₁ hp₂ with ⟨rfl, rfl⟩ |
              ⟨a₁, a₂, Q₁, Q₂, B₁, B₂, X, hB₁, hQ₁, hB₂, hQ₂, hX, hle⟩
          · rw [e₁] at e₂; cases Option.some.inj e₂
            obtain ⟨w, Q, B, hB, hQ, hle⟩ := own_split T hP hp₁
            have eP := own_of_le hle
              (ResU.CompS.get_left_of_ne_imm hB (ResU.single_get_self _ _) (by simp)).2
            rw [hag l₁ w eP] at e₁; cases Option.some.inj e₁
            have hleQ : ResU.Le Q P := (le_of_compS_right hB).trans hle
            exact ih hQ (fun x w e' => hag x w (own_of_le hleQ e')) t₂
          · have hX₁ : ResU.Le B₁ P := (le_of_compS_left hX).trans hle
            have hX₂ : ResU.Le B₂ P := (le_of_compS_right hX).trans hle
            have eX₁ := (ResU.CompS.get_left_of_ne_imm hB₁ (ResU.single_get_self _ _) (by simp)).2
            have eX₂ := (ResU.CompS.get_left_of_ne_imm hB₂ (ResU.single_get_self _ _) (by simp)).2
            rw [hag _ _ (own_of_le hX₁ eX₁)] at e₁; cases Option.some.inj e₁
            rw [hag _ _ (own_of_le hX₂ eX₂)] at e₂; cases Option.some.inj e₂
            have hleQ₁ : ResU.Le Q₁ P := (le_of_compS_right hB₁).trans hX₁
            have hleQ₂ : ResU.Le Q₂ P := (le_of_compS_right hB₂).trans hX₂
            obtain ⟨ζ₁, eζ₁, kζ₁, -⟩ :=
              gpos_mut_cell t₁ hQ₁ (fun x w e' => hag x w (own_of_le hleQ₁ e'))
            obtain ⟨ζ₂, eζ₂, kζ₂, -⟩ :=
              gpos_mut_cell t₂ hQ₂ (fun x w e' => hag x w (own_of_le hleQ₂ e'))
            exact (not_mut_both hX
              (ResU.CompS.get_right_of_ne_imm hB₁ eζ₁ (by rw [kζ₁]; simp)).2
              (by rw [kζ₁]; simp)
              (ResU.CompS.get_right_of_ne_imm hB₂ eζ₂ (by rw [kζ₂]; simp)).2).elim

theorem DescR.refl (r : FrameRec) : DescR r r := ⟨[], LinPath.nil r⟩

theorem LinPath.snoc {r d : FrameRec} {p : List Loc} (h : LinPath r p d) {e : FrameRec}
    (he : SubRec d e) : LinPath r (p ++ [e.le]) e := by
  induction h with
  | nil r => exact LinPath.cons he (LinPath.nil e)
  | cons hs _ ih => exact LinPath.cons hs (ih he)

theorem DescR.sub {r d e : FrameRec} (h : DescR r d) (he : SubRec d e) : DescR r e := by
  obtain ⟨p, hp⟩ := h
  exact ⟨_, hp.snoc he⟩

theorem LinPath.xpath {r d : FrameRec} {p : List Loc} (h : LinPath r p d) : XPath r.R p d.R := by
  induction h with
  | nil r => exact XPath.nil _
  | @cons r d e p hs _ ih =>
      obtain ⟨-, -, ζ, eζ, kζ, -, wζ⟩ := hs
      exact XPath.cons eζ kζ (wζ ▸ ih)

/-- A sub-record of a typed record is typed: `ptoMut`'s `𝒱⟦S⟧δ` at the `mut` cell. -/
theorem SubRec.typed {r d : FrameRec} (h : SubRec r d) (hR : vShape r.T r.δ r.v r.R)
    (hadm : AdmWf r.T r.δ) : vShape d.T d.δ d.v d.R ∧ AdmWf d.T d.δ := by
  obtain ⟨hδ, hg, ζ, eζ, -, rζ, wζ⟩ := h
  obtain ⟨ζ', eζ', -, dζ'⟩ := gpos_mut_cell hg hR (fun _ _ e => e)
  rw [eζ] at eζ'; cases Option.some.inj eζ'
  refine ⟨?_, fun y hy => ?_⟩
  · rw [hδ, ← rζ, ← wζ]; exact dζ'
  · rw [hδ]; exact hadm y (hg.free hy)

theorem LinPath.typed {r d : FrameRec} {p : List Loc} (h : LinPath r p d)
    (hR : vShape r.T r.δ r.v r.R) (hadm : AdmWf r.T r.δ) :
    vShape d.T d.δ d.v d.R ∧ AdmWf d.T d.δ := by
  induction h with
  | nil r => exact ⟨hR, hadm⟩
  | cons hs _ ih =>
      obtain ⟨h₁, h₂⟩ := hs.typed hR hadm
      exact ih h₁ h₂

theorem FrameRec.ext' {a b : FrameRec} (h₁ : a.le = b.le) (h₂ : a.v = b.v) (h₃ : a.R = b.R)
    (h₄ : a.T = b.T) (h₅ : a.δ = b.δ) : a = b := by
  cases a; cases b; simp_all

/-- Two sub-records of a typed record at one location are one. -/
theorem SubRec.functional {r d₁ d₂ : FrameRec} (hR : vShape r.T r.δ r.v r.R) (h₁ : SubRec r d₁)
    (h₂ : SubRec r d₂) (he : d₁.le = d₂.le) : d₁ = d₂ := by
  obtain ⟨hδ₁, hg₁, ζ₁, e₁, -, r₁, w₁⟩ := h₁
  obtain ⟨hδ₂, hg₂, ζ₂, e₂, -, r₂, w₂⟩ := h₂
  rw [he, e₂] at e₁; cases Option.some.inj e₁
  rw [he] at hg₁
  exact FrameRec.ext' he (r₁.symm.trans r₂) (w₁.symm.trans w₂)
    (gpos_unique hg₁ hR (fun _ _ e => e) hg₂) (hδ₁.trans hδ₂.symm)

theorem LinPath.inv_nil {r e : FrameRec} (h : LinPath r [] e) : e = r := by
  generalize hq : ([] : List Loc) = q at h
  cases h with
  | nil => rfl
  | cons _ _ => cases hq

theorem LinPath.inv_cons {r e : FrameRec} {m : Loc} {p : List Loc} (h : LinPath r (m :: p) e) :
    ∃ d, SubRec r d ∧ d.le = m ∧ LinPath d p e := by
  generalize hq : m :: p = q at h
  cases h with
  | nil => cases hq
  | cons hs t =>
      injection hq with h₁ h₂
      subst h₁; subst h₂
      exact ⟨_, hs, rfl, t⟩

/-- A lineage path names one record. -/
theorem LinPath.functional {r d₁ : FrameRec} {p : List Loc} (h₁ : LinPath r p d₁) :
    vShape r.T r.δ r.v r.R → AdmWf r.T r.δ → ∀ {d₂ : FrameRec}, LinPath r p d₂ → d₁ = d₂ := by
  induction h₁ with
  | nil r => intro _ _ d₂ h₂; exact (h₂.inv_nil).symm
  | @cons r d e p hs _ ih =>
      intro hR hadm d₂ h₂
      obtain ⟨d', hs', hle, t'⟩ := h₂.inv_cons
      have hdd : d = d' := SubRec.functional hR hs hs' hle.symm
      subst hdd
      obtain ⟨h₁, h₂⟩ := hs.typed hR hadm
      exact ih h₁ h₂ t'

/-- `ex(σ)_○` is a `○`-part of every `ag(W)`.  `[about ours]` -/
def ExIn (W σ : WRes) : Prop := ∀ a, AgW W a → ∃ e, ExR σ e ∧ Lifts e a

/-- `ag(W)` holds a non-`own` cell at `m` over value `u` and witness `χ`.  `[about ours]` -/
def NVAt (W : WRes) (m : Loc) (u : Val) (χ : WRes) : Prop :=
  ∀ a, AgW W a → ∃ ψ : CellU Loc Val, a.get m = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.erase = u ∧
    ψ.wit = χ

/-- An `imm` cell of every `ag(W)` over witness `R` puts `ex(R)_○` in `ag(W)`. -/
theorem exIn_of_imm {W R : WRes} {le : Loc}
    (h : ∀ a, AgW W a → ∃ ψ : CellU Loc Val, a.get le = some ψ ∧ ψ.kind = Kind.imm ∧ ψ.wit = R) :
    ExIn W R := by
  intro a ha
  obtain ⟨ψ, e, k, w⟩ := h a ha
  obtain ⟨s, hs, hψ⟩ := CellU.imm_eta k
  rw [hψ] at e
  obtain ⟨ev, av, p, z, hev, -, hp, hz⟩ := AgW.flat_imm_wit_le ha _ _ _ _ _ e
  rw [w] at hev
  exact ⟨ev, hev, (lifts_left hp).trans (lifts_left hz)⟩

/-- A `mut` cell of an escrow in `ag(W)` is in `ag(W)`, and so is its witness's `ex`. -/
theorem exIn_mut {W σ : WRes} (h : ExIn W σ) {m : Loc} {ζ : CellU Loc Val}
    (em : σ.get m = some ζ) (km : ζ.kind = Kind.mut) :
    ExIn W ζ.wit ∧ NVAt W m ζ.erase ζ.wit := by
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨e, he, hl⟩ := h a ha
    obtain ⟨e', he', hl'⟩ := exR_mut_wit he em km
    exact ⟨e', he', hl'.trans hl⟩
  · obtain ⟨e, he, hl⟩ := h a ha
    obtain ⟨χ, eχ, rχ, wχ⟩ := exR_cell he em (by rw [km]; simp)
    obtain ⟨ψ, eψ, rψ, wψ⟩ := hl m χ eχ
    obtain ⟨k₁, w₁⟩ := wχ (by rw [km]; simp)
    obtain ⟨k₂, w₂⟩ := wψ k₁
    exact ⟨ψ, eψ, k₂, rψ.trans rχ, w₂.trans w₁⟩

theorem exIn_support {W σ : WRes} (h : ExIn W σ) {x : Loc} {ζ : CellU Loc Val}
    (ex : σ.get x = some ζ) (hk : ζ.kind ≠ Kind.imm) : ∀ a, AgW W a → ∃ ξ, a.get x = some ξ := by
  intro a ha
  obtain ⟨e, he, hl⟩ := h a ha
  obtain ⟨χ, eχ, -⟩ := exR_cell he ex hk
  obtain ⟨ψ, eψ, -⟩ := hl x χ eχ
  exact ⟨ψ, eψ⟩

/-- Along a lineage from a record whose `ex` is in `ag(W)`: every member's `ex` is too,
and every proper member's location carries a non-`own` cell over its value and witness. -/
theorem exIn_path {W : WRes} {r d : FrameRec} {p : List Loc} (h : LinPath r p d) :
    ExIn W r.R → ExIn W d.R ∧ (p ≠ [] → NVAt W d.le d.v d.R) := by
  induction h with
  | nil r => exact fun hr => ⟨hr, fun hp => absurd rfl hp⟩
  | @cons r d e p hs t ih =>
      intro hr
      obtain ⟨-, -, ζ, eζ, kζ, rζ, wζ⟩ := hs
      obtain ⟨hd, hnv⟩ := exIn_mut hr eζ kζ
      rw [wζ] at hd hnv; rw [rζ] at hnv
      obtain ⟨he, hne⟩ := ih hd
      refine ⟨he, fun _ => ?_⟩
      cases t with
      | nil => exact hnv
      | cons _ _ => exact hne (by simp)

/-- The weakened `LeInv`: every record's location carries a non-`own` cell of `ag(W)` over
the recorded value and escrow.  `[about ours: an invariant of the typed world]` -/
def LeInvW (W : WRes) (rs : List FrameRec) : Prop :=
  ∀ r ∈ rs, ∀ a, AgW W a → ∃ ψ : CellU Loc Val, a.get r.le = some ψ ∧ ψ.kind ≠ Kind.own ∧
    ψ.erase = r.v ∧ ψ.wit = r.R

/-- `LeInv` at the records proper gives `ExIn` and `LeInvW` at every lineage member. -/
theorem lineage_of_leInv {W : WRes} {ps : List FrameRec} (hl : LeInv W ps) {p : FrameRec}
    (hp : p ∈ ps) {d : FrameRec} (hd : DescR p d) :
    ExIn W d.R ∧ ∀ a, AgW W a → ∃ ψ : CellU Loc Val, a.get d.le = some ψ ∧
      ψ.kind ≠ Kind.own ∧ ψ.erase = d.v ∧ ψ.wit = d.R := by
  obtain ⟨q, hq⟩ := hd
  have hex : ExIn W p.R :=
    exIn_of_imm (fun a ha => by
      obtain ⟨ψ, e, k, -, w⟩ := hl p hp a ha
      exact ⟨ψ, e, k, w⟩)
  obtain ⟨hdR, hnv⟩ := exIn_path hq hex
  refine ⟨hdR, ?_⟩
  cases hq with
  | nil =>
      intro a ha
      obtain ⟨ψ, e, k, r, w⟩ := hl p hp a ha
      exact ⟨ψ, e, by rw [k]; simp, r, w⟩
  | cons _ _ => exact hnv (by simp)

theorem TW.valid {W : WRes} {ps rs : List FrameRec} (h : TW W ps rs) : ResU.Valid W := by
  induction h with
  | empty => exact ⟨_, flat_empty⟩
  | alloc _ _ _ _ hv _ => exact hv
  | immFrame _ _ _ _ _ _ _ _ _ hv _ _ => exact hv
  | reb _ _ _ _ _ _ _ _ _ _ hv _ => exact hv
  | rebDeep _ _ _ _ _ _ _ _ _ _ _ hv _ => exact hv
  | mutFold _ _ _ _ hv _ => exact hv
  | mutUnfold _ _ _ _ hv _ => exact hv
  | free _ _ hv _ => exact hv
  | store _ _ _ hv _ => exact hv
  | immEnd _ _ _ _ _ _ hv _ _ _ => exact hv
  | rebEnd _ _ _ _ _ hW _ ih => exact (ResU.Valid.split hW ih).1
  | rebEndDeep _ _ _ _ _ _ hW _ ih => exact (ResU.Valid.split hW ih).1

/-- `NoMut` with the location clause at the records proper only: a sub-record's location is
a `mut` cell of its parent's escrow.  `[about ours: an invariant of the typed world]` -/
def NoMut (W : WRes) (ps rs : List FrameRec) : Prop :=
  (∀ r ∈ ps, ¬ MutAt W r.le) ∧ (∀ r ∈ rs, ∀ l u, r.R.get l = some (CellU.ownOf u) → ¬ MutAt W l)

/-- Where an `imm` view may sit: at a record's cell over its value and escrow, or at a chain
position of a record.  A view at a `Mut` position is a sub-record's cell.
`[about ours: our classification]` -/
def Class (rs : List FrameRec) (m : Loc) (ψ : CellU Loc Val) : Prop :=
  (∃ r ∈ rs, m = r.le ∧ ψ.erase = r.v ∧ ψ.wit = r.R) ∨
  (∃ r ∈ rs, ∃ p S u, Chain r.R r.T r.v p m S u)

/-- Every `imm` view of `ag(W)` is classified by a record.
`[about ours: an invariant of the typed world]` -/
def Coverage (W : WRes) (rs : List FrameRec) : Prop :=
  ∀ a, AgW W a → ∀ m (ψ : CellU Loc Val), a.get m = some ψ → ψ.kind = Kind.imm → Class rs m ψ

/-- The invariant of the typed world.
`[about ours: an invariant of the typed world]` -/
def TI (W : WRes) (ps rs : List FrameRec) : Prop :=
  ChainInv W rs ∧ LeInv W ps ∧ (∀ r₁ ∈ ps, ∀ r₂ ∈ ps, r₁.le = r₂.le → r₁ = r₂) ∧
  (∀ r ∈ rs, ∀ r' ∈ rs, ∀ u, r'.R.get r.le ≠ some (CellU.ownOf u)) ∧
  (∀ r ∈ rs, NestLife W r) ∧ NoMut W ps rs ∧
  (∀ x, x ∈ rs ↔ ∃ p ∈ ps, DescR p x) ∧ Coverage W rs

theorem TI.leInvW {W : WRes} {ps rs : List FrameRec} (h : TI W ps rs) : LeInvW W rs := by
  intro r hr
  obtain ⟨p, hp, hd⟩ := (h.2.2.2.2.2.2.1 r).mp hr
  exact (lineage_of_leInv h.2.1 hp hd).2

theorem TI.exIn {W : WRes} {ps rs : List FrameRec} (h : TI W ps rs) {r : FrameRec}
    (hr : r ∈ rs) : ExIn W r.R := by
  obtain ⟨p, hp, hd⟩ := (h.2.2.2.2.2.2.1 r).mp hr
  exact (lineage_of_leInv h.2.1 hp hd).1

theorem TI.sub {W : WRes} {ps rs : List FrameRec} (h : TI W ps rs) {r d : FrameRec}
    (hr : r ∈ rs) (hd : SubRec r d) : d ∈ rs := by
  obtain ⟨p, hp, hpr⟩ := (h.2.2.2.2.2.2.1 r).mp hr
  exact (h.2.2.2.2.2.2.1 d).mpr ⟨p, hp, hpr.sub hd⟩

/-- The frame's escrow sits in `ex(W)_●` unchanged, and not at `ℓ`. -/
theorem frame_ex {W X Z R eW : WRes} {l : Loc} {v : Val}
    (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) R X) (hW : ResU.CompS X Z W)
    (heW : ExS W eW) :
    ∃ eR, ExS R eR ∧ (∀ x (ζ : CellU Loc Val), eR.get x = some ζ → ζ.kind ≠ Kind.imm →
      eW.get x = some ζ) ∧ eR.get l = none := by
  obtain ⟨eX, eZ, heX, -, heXZ⟩ := (ExS.split hW).mp heW
  obtain ⟨eo, eR, heo, heR, heoR⟩ := (ExS.split hX).mp heX
  rw [ExS.functional heo (ExW.single_own l v)] at heoR
  refine ⟨eR, heR, fun x ζ e k => ?_, ?_⟩
  · exact (ResU.CompS.get_left_of_ne_imm heXZ (ResU.CompS.get_right_of_ne_imm heoR e k).2 k).2
  · exact ResU.CompatS.right_eq_none heoR.1 (ResU.single_get_self _ _) (by simp)

/-- Under `immFrame`, an `own` cell of `ex(R)_●` carries no view of `ag(W′)`. -/
theorem frame_new_root' {W X Z R W' a' : WRes} {l : Loc} {v : Val} {α : Life}
    {h : R.InStratum (LSet.singleton α).join}
    (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) R X) (hW : ResU.CompS X Z W)
    (hW' : ResU.CompS (ResU.single l (CellU.immOf (LSet.singleton α) v R h)) Z W')
    (hv : ResU.Valid W) {m : Loc} {u : Val}
    (heRm : ∀ eR, ExS R eR → eR.get m = some (CellU.ownOf u)) (hml : m ≠ l)
    (ha' : AgW W' a') :
    (∃ ζ, a'.get m = some ζ) ∧
    (∀ ψ, a'.get m = some ψ → ψ.kind ≠ Kind.own → False) ∧
    (∀ aW, AgW W aW → aW.get m = none) := by
  obtain ⟨eW, aW, r, z, eR, σc, pc, heW, haW, hr, hrz, heR, hup, hl, hpc, hcp, hcz⟩ :=
    frame_walks hX hW hW' hv ha'
  have heRm' := heRm eR heR
  obtain ⟨ζW, hζW⟩ := hup m _ heRm'
  have hnone : aW.get m = none := by
    cases e : aW.get m with
    | none => rfl
    | some ζ => exact (ex_ag_disjoint hv heW haW hζW e).elim
  refine ⟨?_, fun ψ e hk => ?_, fun aW' haW' => by rw [AgW.functional haW' haW]; exact hnone⟩
  · obtain ⟨_, e₁⟩ := comp_some hpc heRm'
    obtain ⟨_, e₂⟩ := comp_some_r hcp e₁
    exact comp_some hcz e₂
  · rcases back_view hcz e hk with ⟨ψ₁, e₁, k₁, -⟩ | ⟨ψ₁, e₁, -, -⟩
    · rcases back_view hcp e₁ k₁ with ⟨ψ₂, e₂, -, -⟩ | ⟨ψ₂, e₂, k₂, -⟩
      · exact hml (ResU.single_get_eq_some e₂).1
      · rcases back_view hpc e₂ k₂ with ⟨ψ₃, e₃, k₃, -⟩ | ⟨ψ₃, e₃, -, -⟩
        · rw [heRm'] at e₃; cases e₃; exact k₃ (by simp)
        · obtain ⟨_, e₄⟩ := comp_some hrz e₃
          rw [hnone] at e₄; cases e₄
    · obtain ⟨_, e₄⟩ := comp_some_r hrz e₁
      rw [hnone] at e₄; cases e₄

/-- The last step of a nonempty lineage path. -/
theorem LinPath.last {r d : FrameRec} {p : List Loc} (h : LinPath r p d) (hp : p ≠ []) :
    ∃ d', DescR r d' ∧ SubRec d' d := by
  induction h with
  | nil r => exact absurd rfl hp
  | @cons r d₁ e q hs t ih =>
      cases t with
      | nil => exact ⟨r, DescR.refl r, hs⟩
      | @cons _ d₂ _ q' hs' t' =>
          obtain ⟨d', ⟨q'', hq''⟩, hd'⟩ := ih (by simp)
          exact ⟨d', ⟨_, LinPath.cons hs hq''⟩, hd'⟩

theorem DescR.cases {r d : FrameRec} (h : DescR r d) : d = r ∨ Desc r d := by
  obtain ⟨p, hp⟩ := h
  cases p with
  | nil => exact Or.inl hp.inv_nil
  | cons m q => exact Or.inr ⟨_, by simp, hp⟩

/-- `immFrame` keeps `TI`. -/
theorem ti_frame {W X Z R W' : WRes} {ps rs ds : List FrameRec} {l : Loc} {v : Val}
    {α : Life} {T : VTy} {δ : LSub} {hα : R.InStratum (LSet.singleton α).join}
    (hvW : ResU.Valid W) (hadm : AdmWf T δ)
    (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) R X) (hW : ResU.CompS X Z W)
    (hden : vShape T δ v R)
    (hW' : ResU.CompS (ResU.single l (CellU.immOf (LSet.singleton α) v R hα)) Z W')
    (hv : ResU.Valid W') (hds : ∀ d, d ∈ ds ↔ Desc ⟨l, v, R, T, δ⟩ d) (h : TI W ps rs) :
    TI W' (⟨l, v, R, T, δ⟩ :: ps) (⟨l, v, R, T, δ⟩ :: (ds ++ rs)) := by
  have hlw : LeInvW W rs := h.leInvW
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hle, hid, hio, hN, hM, hmem, hC⟩ := h
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hvW
  obtain ⟨a', ha'⟩ := agW_of_valid hv
  obtain ⟨eR, heR, hRW, hRl⟩ := frame_ex hX hW heW
  -- the new lineage lives in `ex(W)_●`
  have newEx : ∀ d, DescR ⟨l, v, R, T, δ⟩ d → ∀ x (ζ : CellU Loc Val), d.R.get x = some ζ →
      ζ.kind ≠ Kind.imm → eR.get x = some ζ := by
    rintro d ⟨p, hp⟩ x ζ e k
    exact xpath_ex heR hp.xpath e k
  have newNotAg : ∀ d, DescR ⟨l, v, R, T, δ⟩ d → ∀ x (ζ : CellU Loc Val), d.R.get x = some ζ →
      ζ.kind ≠ Kind.imm → aW.get x = none := by
    intro d hd x ζ e k
    cases ea : aW.get x with
    | none => rfl
    | some ξ => exact (ex_ag_disjoint hvW heW haW (hRW x ζ (newEx d hd x ζ e k) k) ea).elim
  have newUnique : ∀ d₁ d₂, DescR ⟨l, v, R, T, δ⟩ d₁ → DescR ⟨l, v, R, T, δ⟩ d₂ →
      ∀ x (ζ₁ ζ₂ : CellU Loc Val), d₁.R.get x = some ζ₁ → ζ₁.kind ≠ Kind.imm →
      d₂.R.get x = some ζ₂ → ζ₂.kind ≠ Kind.imm → d₁ = d₂ := by
    rintro d₁ d₂ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ x ζ₁ ζ₂ e₁ k₁ e₂ k₂
    have hpp := xpath_unique heR hp₁.xpath hp₂.xpath e₁ k₁ e₂ k₂
    subst hpp
    exact hp₁.functional hden hadm hp₂
  have newNotL : ∀ d, DescR ⟨l, v, R, T, δ⟩ d → ∀ ζ : CellU Loc Val, d.R.get l = some ζ →
      ζ.kind ≠ Kind.imm → False := by
    intro d hd ζ e k
    rw [newEx d hd l ζ e k] at hRl; cases hRl
  have newRoot : ∀ d, DescR ⟨l, v, R, T, δ⟩ d → ∀ m u, d.R.get m = some (CellU.ownOf u) →
      ∀ a, AgW W' a → (∃ ζ, a.get m = some ζ) ∧
        (∀ ψ : CellU Loc Val, a.get m = some ψ → ψ.kind ≠ Kind.own → False) := by
    intro d hd m u hm a ha
    have := frame_new_root' hX hW hW' hvW
      (fun eR' heR' => by rw [ExS.functional heR' heR]; exact newEx d hd m _ hm (by simp))
      (fun hml => newNotL d hd (CellU.ownOf u) (by rw [← hml]; exact hm) (by simp)) ha
    exact ⟨this.1, this.2.1⟩
  have newTyped : ∀ d, DescR ⟨l, v, R, T, δ⟩ d → vShape d.T d.δ d.v d.R ∧ AdmWf d.T d.δ :=
    fun d ⟨p, hp⟩ => hp.typed hden hadm
  have mem' : ∀ x, x ∈ (⟨l, v, R, T, δ⟩ :: (ds ++ rs) : List FrameRec) →
      DescR ⟨l, v, R, T, δ⟩ x ∨ x ∈ rs := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Or.inl (DescR.refl _)
    · rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨p, -, hp⟩ := (hds x).mp hx; exact Or.inl ⟨p, hp⟩
      · exact Or.inr hx
  -- a new record's location is not in `ag(W)`
  have newLeNone : ∀ d, DescR ⟨l, v, R, T, δ⟩ d → aW.get d.le = none := by
    intro d hd
    rcases hd.cases with rfl | ⟨p, hp, hpp⟩
    · cases e : aW.get l with
      | none => rfl
      | some ζ =>
          have Wl : W.get l = some (CellU.ownOf v) :=
            (ResU.CompS.get_left_of_ne_imm hW (ResU.CompS.get_left_of_ne_imm hX
              (ResU.single_get_self _ _) (by simp)).2 (by simp)).2
          exact (ex_ag_disjoint hvW heW haW (ExS.get_of_ne_imm heW Wl (by simp)) e).elim
    · obtain ⟨d', hd', -, -, ζ, eζ, kζ, -⟩ := hpp.last hp
      exact newNotAg d' hd' _ ζ eζ (by rw [kζ]; simp)
  -- the transfer for the old records
  have back : ∀ r ∈ rs, ∀ m u, r.R.get m = some (CellU.ownOf u) → ∀ a, AgW W' a →
      ∀ ψ : CellU Loc Val, a.get m = some ψ → ψ.kind ≠ Kind.own →
      ∃ ψ₀ : CellU Loc Val, aW.get m = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit := by
    intro r hr m u hm a ha ψ e hk
    obtain ⟨aW₁, haW₁, ψ₀, e₀, k₀, w₀⟩ := frame_transfer hX hW hW' hvW (h2 r hr m u hm) ha e hk
    rw [AgW.functional haW₁ haW] at e₀
    exact ⟨ψ₀, e₀, k₀, w₀⟩
  -- the `ICp` maps across the frame
  obtain ⟨eW', aW', rw₀, z, eR', σc, pc, heW', haW', hr', hrz, heR', -, hl, hpc, hcp, hcz⟩ :=
    frame_walks hX hW hW' hvW ha'
  rw [AgW.functional haW' haW] at hrz
  have lNone : aW.get l = none := newLeNone _ (DescR.refl _)
  have backI : ∀ m, m ≠ l → ICpAt aW a' m := by
    intro m hm
    exact icpAt_comp hcz (icpAt_comp hcp (icpAt_none (single_ne _ hm))
      (icpAt_comp hpc (icpAt_of_immFree (ExS.immFree heR') m) (icpAt_left hrz m)))
      (icpAt_right hrz m)
  have fwdI : ∀ m, ICpAt a' aW m := by
    intro m
    exact icpAt_comp hrz (icpAt_trans (icpAt_right hpc m)
      (icpAt_trans (icpAt_right hcp m) (icpAt_left hcz m))) (icpAt_right hcz m)
  have tm : ∀ x, MutAt W' x → MutAt W x := by
    intro x hm
    rcases MutAt.split hW' hm with h₁ | h₂
    · cases h₁ with
      | top e hk => obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e; exact absurd hk (by simp)
      | nest e hk hw =>
          obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
          rw [CellU.wit_immOf] at hw
          exact MutAt.of_compS_left hW (MutAt.of_compS_right hX hw)
    · exact MutAt.of_compS_right hW h₂
  have Wl : W.get l = some (CellU.ownOf v) :=
    (ResU.CompS.get_left_of_ne_imm hW
      (ResU.CompS.get_left_of_ne_imm hX (ResU.single_get_self _ _) (by simp)).2 (by simp)).2
  refine ⟨⟨fun x hx => ?_, fun x hx m u hm a ha => ?_, fun x₁ hx₁ x₂ hx₂ m u₁ u₂ hm₁ hm₂ => ?_,
    fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩, fun x hx a ha => ?_,
    fun x₁ hx₁ x₂ hx₂ e => ?_, fun x₁ hx₁ x₂ hx₂ u hu => ?_, fun x hx => ?_, ⟨fun x hx => ?_,
    fun x hx m u hm hmm => ?_⟩, fun x => ?_, ?_⟩
  -- DeepInv
  · rcases mem' x hx with hd | hx
    · intro p m S u hc a ha ψ e hk
      exact ((newRoot x hd m u hc.own a ha).2 ψ e hk).elim
    · intro p m S u hc a ha ψ e hk
      obtain ⟨ψ₀, e₀, k₀, w₀⟩ := back x hx m u hc.own a ha ψ e hk
      obtain ⟨kk, d, o, b₁, b₂⟩ := h1 x hx p m S u hc aW haW ψ₀ e₀ k₀
      obtain ⟨ψ', e', k'⟩ := frame_imm hX hW hW' hvW ha haW e₀ kk
      rw [e] at e'; cases Option.some.inj e'
      refine ⟨k', w₀ ▸ d, w₀ ▸ o, fun hp => w₀ ▸ b₁ hp, fun l₀ hp => ?_⟩
      obtain ⟨ψ₁, e₁, k₁, q, hq, hql, hw⟩ := b₂ l₀ hp
      obtain ⟨ψ₂, e₂, k₂, w₂⟩ := frame_fwd hX hW hW' hvW ha haW e₁ k₁
      exact ⟨ψ₂, e₂, k₂, q, w₂ ▸ hq, hql, w₀.trans hw⟩
  -- support
  · rcases mem' x hx with hd | hx
    · exact (newRoot x hd m u hm a ha).1
    · exact frame_support hX hW hW' hvW (h2 x hx m u hm) ha
  -- escrows own disjoint locations
  · rcases mem' x₁ hx₁ with hd₁ | hx₁ <;> rcases mem' x₂ hx₂ with hd₂ | hx₂
    · exact newUnique x₁ x₂ hd₁ hd₂ m _ _ hm₁ (by simp) hm₂ (by simp)
    · obtain ⟨ζ, hζ⟩ := h2 x₂ hx₂ m u₂ hm₂ aW haW
      rw [newNotAg x₁ hd₁ m _ hm₁ (by simp)] at hζ; cases hζ
    · obtain ⟨ζ, hζ⟩ := h2 x₁ hx₁ m u₁ hm₁ aW haW
      rw [newNotAg x₂ hd₂ m _ hm₂ (by simp)] at hζ; cases hζ
    · exact h3 x₁ hx₁ x₂ hx₂ m u₁ u₂ hm₁ hm₂
  -- typed
  · rcases mem' x hx with hd | hx
    · exact newTyped x hd
    · exact h4 x hx
  -- JointAt
  · rcases mem' x hx with hd | hx
    · rintro ⟨S, m, u, hR, a, ha, ψ, e, hk⟩
      exact ((newRoot x hd m u hR.2 a ha).2 ψ e hk).elim
    · rintro ⟨S, m, u, hR, a, ha, ψ, e, hk⟩
      obtain ⟨ψ₀, e₀, k₀, -⟩ := back x hx m u hR.2 a ha ψ e hk
      obtain ⟨β₀, x₀, c₀, q1, q2, q3, q4, q5⟩ := h5 x hx ⟨S, m, u, hR, aW, haW, ψ₀, e₀, k₀⟩
      refine ⟨β₀, x₀, c₀, q1, q2, q3, q4, fun S' m' u' hR' a₁ ha₁ ψ₁ e₁ hk₁ => ?_⟩
      obtain ⟨ψ₂, e₂, k₂, w₂⟩ := back x hx m' u' hR'.2 a₁ ha₁ ψ₁ e₁ hk₁
      obtain ⟨ζ, eζ, wζ⟩ := q5 S' m' u' hR' aW haW ψ₂ e₂ k₂
      exact ⟨ζ, eζ, w₂.trans wζ⟩
  -- JointDeep
  · rcases mem' x hx with hd | hx
    · rintro p₀ l₀ S₀ u₀ - ⟨m, S, u, hc, a, ha, ψ, e, hk⟩
      exact ((newRoot x hd m u hc.own a ha).2 ψ e hk).elim
    · rintro p₀ l₀ S₀ u₀ hc₀ ⟨m, S, u, hc, a, ha, ψ, e, hk⟩
      obtain ⟨ψ₀, e₀, k₀, -⟩ := back x hx m u hc.own a ha ψ e hk
      obtain ⟨w₀, hw₀, β₀, x₀, c₀, q1, q2, q3, q4, q5⟩ :=
        h6 x hx p₀ l₀ S₀ u₀ hc₀ ⟨m, S, u, hc, aW, haW, ψ₀, e₀, k₀⟩
      refine ⟨w₀, fun a₁ ha₁ => ?_, β₀, x₀, c₀, q1, q2, q3, q4,
        fun m' S' u' hc' a₁ ha₁ ψ₁ e₁ hk₁ => ?_⟩
      · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := hw₀ aW haW
        obtain ⟨ψ₃, e₃, k₃, w₃⟩ := frame_fwd hX hW hW' hvW ha₁ haW e₂ k₂
        exact ⟨ψ₃, e₃, k₃, w₃.trans w₂⟩
      · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := back x hx m' u' hc'.own a₁ ha₁ ψ₁ e₁ hk₁
        obtain ⟨ζ, eζ, wζ⟩ := q5 m' S' u' hc' aW haW ψ₂ e₂ k₂
        exact ⟨ζ, eζ, w₂.trans wζ⟩
  -- LeInv at the records proper
  · rcases List.mem_cons.mp hx with rfl | hx
    · obtain ⟨ψ, e, k, w, r'⟩ := compS_get_left' hW' (ResU.single_get_self _ _)
      obtain ⟨χ, eχ, kχ, rχ, wχ⟩ := AgW.get_imm ha e (k.trans (CellU.kind_immOf _ _ _ _))
      exact ⟨χ, eχ, kχ, by rw [rχ, r']; rfl, by rw [wχ, w]; simp⟩
    · obtain ⟨ψ₀, e₀, k₀, r₀, w₀⟩ := hle x hx aW haW
      obtain ⟨ψ, e, k, r', w⟩ := frame_fwd_imm hX hW hW' hvW ha haW e₀ k₀
      exact ⟨ψ, e, k, r'.trans r₀, w.trans w₀⟩
  -- records proper sit at distinct cells
  · rcases List.mem_cons.mp hx₁ with rfl | hx₁ <;> rcases List.mem_cons.mp hx₂ with rfl | hx₂
    · rfl
    · obtain ⟨ψ, e', -⟩ := hle x₂ hx₂ aW haW
      simp only at e
      rw [← e, lNone] at e'; cases e'
    · obtain ⟨ψ, e', -⟩ := hle x₁ hx₁ aW haW
      simp only at e
      rw [e, lNone] at e'; cases e'
    · exact hid x₁ hx₁ x₂ hx₂ e
  -- no escrow owns a record's location
  · rcases mem' x₁ hx₁ with hd₁ | hx₁ <;> rcases mem' x₂ hx₂ with hd₂ | hx₂
    · rcases hd₁.cases with rfl | ⟨p, hp, hpp⟩
      · exact newNotL x₂ hd₂ _ hu (by simp)
      · obtain ⟨d', hd', -, -, ζ, eζ, kζ, -⟩ := hpp.last hp
        have := newUnique d' x₂ hd' hd₂ _ ζ _ eζ (by rw [kζ]; simp) hu (by simp)
        subst this
        rw [hu] at eζ; cases Option.some.inj eζ; exact absurd kζ (by simp)
    · obtain ⟨ζ, hζ⟩ := h2 x₂ hx₂ _ u hu aW haW
      rw [newLeNone x₁ hd₁] at hζ; cases hζ
    · obtain ⟨ψ, e, -⟩ := hlw x₁ hx₁ aW haW
      rw [newNotAg x₂ hd₂ _ _ hu (by simp)] at e; cases e
    · exact hio x₁ hx₁ x₂ hx₂ u hu
  -- NestLife
  · rcases mem' x hx with hd | hx
    · intro l₀ m S u hc a ha ψ s e hs y hy
      exact ((newRoot x hd m u hc.own a ha).2 ψ e
        (by rw [CellU.kind_of_lsOf hs]; simp)).elim
    · refine nestLife_of_icp (hN x hx) haW (fun a₁ ha₁ l₀ m S u hc => ?_)
        (fun a₁ ha₁ l₀ m S u hc => by rw [AgW.functional ha₁ ha']; exact fwdI l₀)
      rw [AgW.functional ha₁ ha']
      refine backI m (fun hml => ?_)
      obtain ⟨ζ, hζ⟩ := h2 x hx m u hc.own aW haW
      rw [hml, lNone] at hζ; cases hζ
  -- NoMut at the records proper
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact fun hm => not_mutAt_top_own hvW Wl (tm _ hm)
    · exact fun hm => hM.1 x hx (tm _ hm)
  -- NoMut at every escrow's `own` cells
  · rcases mem' x hx with hd | hx
    · exact not_mutAt_ex_own hvW heW (hRW m _ (newEx x hd m _ hm (by simp)) (by simp)) (tm _ hmm)
    · exact hM.2 x hx m u hm (tm _ hmm)
  -- membership
  · constructor
    · intro hx
      rcases mem' x hx with hd | hx
      · exact ⟨_, List.mem_cons_self, hd⟩
      · obtain ⟨p, hp, hpx⟩ := (hmem x).mp hx
        exact ⟨p, List.mem_cons_of_mem _ hp, hpx⟩
    · rintro ⟨p, hp, hpx⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · rcases hpx.cases with rfl | hd
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ ((hds x).mpr hd))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ ((hmem x).mpr ⟨p, hp, hpx⟩))
  -- coverage
  · intro a₁ ha₁ m ψ e hk
    rw [AgW.functional ha₁ ha'] at e
    by_cases hml : m = l
    · subst hml
      obtain ⟨ψ₁, e₁, k₁, w₁, r₁⟩ := compS_get_left' hW' (ResU.single_get_self _ _)
      obtain ⟨χ, eχ, kχ, rχ, wχ⟩ := AgW.get_imm ha' e₁ (k₁.trans (CellU.kind_immOf _ _ _ _))
      rw [e] at eχ; cases Option.some.inj eχ
      exact Or.inl ⟨_, List.mem_cons_self, rfl, by rw [rχ, r₁]; rfl, by rw [wχ, w₁]; simp⟩
    · obtain ⟨ζ, eζ, kζ, rζ, wζ, -⟩ := backI m hml ψ e hk
      rcases hC aW haW m ζ eζ kζ with ⟨r, hr, h₁, h₂, h₃⟩ | ⟨r, hr, p, S, u, hch⟩
      · exact Or.inl ⟨r, List.mem_cons_of_mem _ (List.mem_append_right _ hr), h₁,
          rζ.symm.trans h₂, wζ.symm.trans h₃⟩
      · exact Or.inr ⟨r, List.mem_cons_of_mem _ (List.mem_append_right _ hr), p, S, u, hch⟩

theorem Class.congr {rs : List FrameRec} {m : Loc} {ψ ψ' : CellU Loc Val}
    (he : ψ'.erase = ψ.erase) (hw : ψ'.wit = ψ.wit) (h : Class rs m ψ) : Class rs m ψ' := by
  rcases h with ⟨r, hr, h₁, h₂, h₃⟩ | h
  · exact Or.inl ⟨r, hr, h₁, he.trans h₂, hw.trans h₃⟩
  · exact Or.inr h

theorem coverage_of_icp {W W' aW : WRes} {rs : List FrameRec} (haW : AgW W aW)
    (hC : Coverage W rs) (t : ∀ a', AgW W' a' → ∀ m, ICpAt aW a' m) : Coverage W' rs := by
  intro a' ha' m ψ e hk
  obtain ⟨ζ, eζ, kζ, rζ, wζ, -⟩ := t a' ha' m ψ e hk
  exact (hC aW haW m ζ eζ kζ).congr rζ.symm wζ.symm

/-- A lineage member's `LeInvW` and `ExIn` from `LeInv` at the records proper. -/
theorem leInvW_of {W : WRes} {ps rs : List FrameRec} (hl : LeInv W ps)
    (hmem : ∀ x, x ∈ rs ↔ ∃ p ∈ ps, DescR p x) : LeInvW W rs := by
  intro r hr
  obtain ⟨p, hp, hd⟩ := (hmem r).mp hr
  exact (lineage_of_leInv hl hp hd).2

theorem exIn_of {W : WRes} {ps rs : List FrameRec} (hl : LeInv W ps)
    (hmem : ∀ x, x ∈ rs ↔ ∃ p ∈ ps, DescR p x) {r : FrameRec} (hr : r ∈ rs) : ExIn W r.R := by
  obtain ⟨p, hp, hd⟩ := (hmem r).mp hr
  exact (lineage_of_leInv hl hp hd).1

theorem ti_of_ag {W W' : WRes} {ps rs : List FrameRec} (t : ∀ a, AgW W' a → AgW W a)
    (tm : ∀ x, MutAt W' x → MutAt W x) (h : TI W ps rs) : TI W' ps rs := by
  obtain ⟨h3, hl, hid, hio, hN, hM, hmem, hC⟩ := h
  exact ⟨chainInv_of_ag_sub t h3, fun r hr a ha => hl r hr a (t a ha), hid, hio,
    fun r hr => nestLife_of_ag t (hN r hr), ⟨fun r hr hm => hM.1 r hr (tm _ hm),
    fun r hr l u hl' hm => hM.2 r hr l u hl' (tm _ hm)⟩, hmem, fun a ha => hC a (t a ha)⟩

theorem ti_mutFold {W X Z ρ W' : WRes} {ps rs : List FrameRec} {l : Loc} {v : Val} {b : Life}
    {hstr : ρ.InStratum b} {P : Val → SPropS Loc Val b} {hw : P v ⟨ρ, hstr⟩}
    (hvW : ResU.Valid W) (hX : ResU.CompS (ResU.single l (CellU.ownOf v)) ρ X)
    (hW : ResU.CompS X Z W)
    (hW' : ResU.CompS (ResU.single l (CellU.mutOf b v ρ hstr P hw)) Z W') (h : TI W ps rs) :
    TI W' ps rs := by
  have t := fun a ha => (mut_fold_ag hX hW hW' a).mpr ha
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  have Wl : W.get l = some (CellU.ownOf v) :=
    (ResU.CompS.get_left_of_ne_imm hW
      (ResU.CompS.get_left_of_ne_imm hX (ResU.single_get_self _ _) (by simp)).2 (by simp)).2
  have lNone : aW.get l = none := by
    obtain ⟨σ, eW, aW', heW, haW', hc⟩ := hvW
    rw [AgW.functional haW' haW] at hc
    cases e : aW.get l with
    | none => rfl
    | some ζ =>
        exact (ex_ag_disjoint ⟨σ, eW, aW, heW, haW, hc⟩ heW haW
          (ExS.get_of_ne_imm heW Wl (by simp)) e).elim
  have tm : ∀ x, MutAt W' x → MutAt W x ∨ x = l := by
    intro x hm
    rcases MutAt.split hW' hm with h₁ | h₂
    · cases h₁ with
      | top e hk => exact Or.inr (ResU.single_get_eq_some e).1
      | nest e hk hw' =>
          obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
          rw [CellU.wit_mutOf] at hw'
          exact Or.inl (MutAt.of_compS_left hW (MutAt.of_compS_right hX hw'))
    · exact Or.inl (MutAt.of_compS_right hW h₂)
  obtain ⟨h3, hl, hid, hio, hN, hM, hmem, hC⟩ := h
  refine ⟨chainInv_of_ag_sub t h3, fun r hr a ha => hl r hr a (t a ha), hid, hio,
    fun r hr => nestLife_of_ag t (hN r hr), ⟨fun r hr hm => ?_, fun r hr m u hm hmm => ?_⟩,
    hmem, fun a ha => hC a (t a ha)⟩
  · rcases tm _ hm with h' | h'
    · exact hM.1 r hr h'
    · obtain ⟨ψ, e, -⟩ := hl r hr aW haW
      rw [h', lNone] at e; cases e
  · rcases tm _ hmm with h' | h'
    · exact hM.2 r hr m u hm h'
    · obtain ⟨ζ, e⟩ := h3.2.1 r hr m u hm aW haW
      rw [h', lNone] at e; cases e

/-- A reborrow keeps `NestLife` and `NoMut`. -/
theorem nm_reb_like {W W' c w₀ : WRes} {ps rs : List FrameRec} {le : Loc} {s : LSet} {v : Val}
    {hs : w₀.InStratum s.join} {β : Life}
    (hvW : ResU.Valid W) (hle : W.get le = some (CellU.immOf s v w₀ hs))
    (hreb : ResU.Reb β w₀ c) (hW : ResU.CompS W c W')
    (hN : ∀ r ∈ rs, NestLife W r) (hM : NoMut W ps rs)
    (newOwn : ∀ aW, AgW W aW → ∀ a', AgW W' a' → ∀ r ∈ rs, ∀ l₀ m S u,
      Chain r.R r.T r.v (some l₀) m S u → ∀ u', w₀.get m = some (CellU.ownOf u') →
      (∃ φ, c.get m = some φ) →
      ∃ (ζ : CellU Loc Val) (t : LSet) (y : Life), a'.get l₀ = some ζ ∧ ζ.lsOf = some t ∧
        t.mem y ∧ β ⊏ y) :
    (∀ r ∈ rs, NestLife W' r) ∧ NoMut W' ps rs := by
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  have tm : ∀ x, MutAt W' x → MutAt W x := by
    intro x hm
    rcases MutAt.split hW hm with h₁ | h₂
    · exact h₁
    · exact mutAt_of_cell hle (mutAt_image hreb h₂)
  refine ⟨fun r hr => ?_, ⟨fun r hr hm => hM.1 r hr (tm _ hm),
    fun r hr l u hl hm => hM.2 r hr l u hl (tm _ hm)⟩⟩
  refine nestLife_of_maps (hN r hr) haW (fun a' ha' l₀ m S u hc ψ s' x e hs' hx => ?_)
    (fun a' ha' l₀ m S u hc ζ t y e ht hy => ?_)
  · obtain ⟨aW', ac, haW', hac, hcomp⟩ := (AgW.split hW).mp ha'
    rw [AgW.functional haW' haW] at hcomp
    rcases ResU.CompR.lsOf_inv hcomp e hs' hx with ⟨ξ, t₁, e₁, ht₁, hx₁⟩ |
        ⟨ξ, t₁, e₁, ht₁, hx₁⟩
    · exact Or.inl ⟨ξ, t₁, e₁, ht₁, hx₁⟩
    · rcases img_ls haW hle hreb (fun _ _ e => e) hac e₁ ht₁ hx₁ with hl | ⟨rfl, hφ, ζ, eζ, kζ⟩
      · exact Or.inl hl
      · right
        rcases CellU.rep ζ with ⟨u', rfl⟩ | ⟨s₁, v₁, χ₁, h₁, rfl⟩ | ⟨b₁, v₁, χ₁, h₁, P, hw, rfl⟩
        · exact newOwn aW haW a' ha' r hr l₀ m S u hc u' eζ hφ
        · exact absurd (CellU.kind_immOf _ _ _ _) kζ
        · exact (hM.2 r hr m u hc.own
            (mutAt_of_cell hle (MutAt.top eζ (by simp)))).elim
  · obtain ⟨aW', ac, haW', -, hcomp⟩ := (AgW.split hW).mp ha'
    rw [AgW.functional haW' haW] at hcomp
    exact (icpAt_left hcomp l₀ ζ e).ls ht hy

/-- A reborrow's coverage: a view over an `imm` cell of the escrow copies a classified
cell; one over an `own` cell is at a chain position (`newOwn`); one over a `mut` cell is at a
sub-record's location (`newMut`), where `ag(W′)` holds the sub-record's value and witness. -/
theorem cov_reb_like {W W' c w₀ : WRes} {rs : List FrameRec} {le : Loc} {s : LSet} {v : Val}
    {hs : w₀.InStratum s.join} {β : Life} (hvW : ResU.Valid W)
    (hle : W.get le = some (CellU.immOf s v w₀ hs)) (hreb : ResU.Reb β w₀ c)
    (hW : ResU.CompS W c W') (hC : Coverage W rs) (hLW : LeInvW W' rs)
    (newOwn : ∀ m u, w₀.get m = some (CellU.ownOf u) → (∃ ψ, c.get m = some ψ) →
      ∃ r ∈ rs, ∃ p S u', Chain r.R r.T r.v p m S u')
    (newMut : ∀ m (ζ : CellU Loc Val), w₀.get m = some ζ → ζ.kind = Kind.mut →
      (∃ ψ, c.get m = some ψ) → ∃ d ∈ rs, d.le = m) : Coverage W' rs := by
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  intro a' ha' m ψ e hk
  obtain ⟨aW', ac, haW', hac, hcomp⟩ := (AgW.split hW).mp ha'
  rw [AgW.functional haW' haW] at hcomp
  rcases imm_back_full hcomp e hk with ⟨ψ₁, e₁, k₁, r₁, w₁⟩ | ⟨ψ₁, e₁, k₁, r₁, w₁⟩
  · exact (hC aW haW m ψ₁ e₁ k₁).congr r₁.symm w₁.symm
  · obtain ⟨d', bi, hdb, hbi, hd'⟩ := img_walk haW hle hreb (fun _ _ e => e) hac
    rcases imm_back_full hdb e₁ k₁ with ⟨ψ₂, e₂, k₂, r₂, w₂⟩ | ⟨ψ₂, e₂, k₂, r₂, w₂⟩
    · have ec := hd' m ψ₂ e₂
      rcases img_cell haW hle hreb ec with hi | ⟨⟨ζ, eζ, kζ⟩, -⟩
      · obtain ⟨ξ, eξ, kξ, rξ, wξ, -⟩ := hi k₂
        exact (hC aW haW m ξ eξ kξ).congr (r₁.symm.trans (r₂.symm.trans rξ.symm))
          (w₁.symm.trans (w₂.symm.trans wξ.symm))
      · rcases CellU.rep ζ with ⟨u, rfl⟩ | ⟨s₁, v₁, χ₁, h₁, rfl⟩ | ⟨b₁, v₁, χ₁, h₁, P, hw, rfl⟩
        · exact Or.inr (newOwn m u eζ ⟨_, ec⟩)
        · exact absurd (CellU.kind_immOf _ _ _ _) kζ
        · obtain ⟨d, hd, hdm⟩ := newMut m _ eζ (by simp) ⟨_, ec⟩
          obtain ⟨ψ', e', -, r', w'⟩ := hLW d hd a' ha'
          rw [hdm, e] at e'; cases Option.some.inj e'
          exact Or.inl ⟨d, hd, hdm.symm, r', w'⟩
    · obtain ⟨ξ, eξ, kξ, rξ, wξ, -⟩ := hbi m ψ₂ e₂ k₂
      exact (hC aW haW m ξ eξ kξ).congr (r₁.symm.trans (r₂.symm.trans rξ.symm))
        (w₁.symm.trans (w₂.symm.trans wξ.symm))

/-- A reborrow at any record keeps `TI`. -/
theorem ti_reb {W W' c : WRes} {ps rs : List FrameRec} {r₀ : FrameRec} {le : Loc} {s : LSet}
    {β : Life} {hs : r₀.R.InStratum s.join} {x : LifeVar}
    (hvW : ResU.Valid W) (hr₀ : r₀ ∈ rs) (hle : W.get le = some (CellU.immOf s r₀.v r₀.R hs))
    (hx : ¬ VFree x r₀.T) (hreb : ResU.Reb β r₀.R c)
    (hden : vShape (r₀.T.immReborrow (.var x)) (r₀.δ.extend x β) r₀.v c)
    (hW : ResU.CompS W c W') (hv : ResU.Valid W') (h : TI W ps rs) : TI W' ps rs := by
  obtain ⟨h3, hl, hid, hio, hN, hM, hmem, hC⟩ := h
  have hR₀ := (h3.2.2.2.1 r₀ hr₀).1
  have hl' := leInv_of_reb hvW hW hl
  obtain ⟨hN', hM'⟩ := nm_reb_like hvW hle hreb hW hN hM
    (fun aW haW a' ha' r hr l₀ m S u hc u' hown hφ => by
      have e₁ : r = r₀ := h3.2.2.1 r hr r₀ hr₀ m u u' hc.own hown
      subst e₁
      obtain ⟨φ, eφ⟩ := hφ
      obtain ⟨ζ, eζ, hpos⟩ := image_dom r.T hden hR₀ eφ
      rw [hown] at eζ; cases Option.some.inj eζ
      obtain ⟨S', hS'⟩ := hpos rfl
      exact absurd (chain_unique_rec hR₀ hc (Chain.one hS' hown)).1 (by simp))
  refine ⟨chainInv_reb hvW hr₀ hle hx hreb hden hW hv h3, hl', hid, hio, hN', hM', hmem, ?_⟩
  refine cov_reb_like hvW hle hreb hW hC (leInvW_of hl' hmem) (fun m u eζ ⟨ψ, ec⟩ => ?_)
    (fun m ζ eζ kζ ⟨ψ, ec⟩ => ?_)
  · obtain ⟨ζ', eζ', hpos⟩ := image_dom r₀.T hden hR₀ ec
    rw [eζ] at eζ'; cases Option.some.inj eζ'
    obtain ⟨S, hS⟩ := hpos rfl
    exact ⟨r₀, hr₀, none, S, u, Chain.one hS eζ⟩
  · obtain ⟨S, hS⟩ := image_dom_mut r₀.T hden hR₀ ec eζ kζ
    obtain ⟨p, hp, hpr⟩ := (hmem r₀).mp hr₀
    refine ⟨⟨m, ζ.erase, ζ.wit, S, r₀.δ⟩, (hmem _).mpr ⟨p, hp, hpr.sub ?_⟩, rfl⟩
    exact ⟨rfl, GPos.here hS, ζ, eζ, kζ, rfl, rfl⟩

/-- A reborrow at a chain view of any record keeps `TI`. -/
theorem ti_rebDeep {W W' c : WRes} {ps rs : List FrameRec} {r₀ : FrameRec} {p₀ : Option Loc}
    {l₁ : Loc} {S₀ : VTy} {u₀ : Val} {s : LSet} {w₀ : WRes} {hs : w₀.InStratum s.join}
    {β : Life} {x : LifeVar}
    (hvW : ResU.Valid W) (hr₀ : r₀ ∈ rs) (hch₀ : Chain r₀.R r₀.T r₀.v p₀ l₁ S₀ u₀)
    (hcell : W.get l₁ = some (CellU.immOf s u₀ w₀ hs)) (hx : ¬ VFree x S₀)
    (hreb : ResU.Reb β w₀ c) (hden : vShape (S₀.immReborrow (.var x)) (r₀.δ.extend x β) u₀ c)
    (hβ : W.InStratum β) (hW : ResU.CompS W c W') (hv : ResU.Valid W') (h : TI W ps rs) :
    TI W' ps rs := by
  obtain ⟨h3, hl, hid, hio, hN, hM, hmem, hC⟩ := h
  have hR₀ := (h3.2.2.2.1 r₀ hr₀).1
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  obtain ⟨χ, eχ, kχ, -, wχ⟩ := AgW.get_imm haW hcell (CellU.kind_immOf _ _ _ _)
  rw [CellU.wit_immOf] at wχ
  obtain ⟨-, hw₀den, hw₀own, -, -⟩ :=
    h3.1 r₀ hr₀ p₀ l₁ S₀ u₀ hch₀ aW haW χ eχ (by rw [kχ]; simp)
  rw [wχ] at hw₀den hw₀own
  have hl' := leInv_of_reb hvW hW hl
  obtain ⟨hN', hM'⟩ := nm_reb_like hvW hcell hreb hW hN hM
    (fun aW₁ haW₁ a' ha' r hr l₀ m S u hc u' hown hφ => by
      rw [AgW.functional haW₁ haW] at *
      have e₁ : r = r₀ := h3.2.2.1 r hr r₀ hr₀ m u u' hc.own (hw₀own m u' hown)
      subst e₁
      obtain ⟨φ, eφ⟩ := hφ
      obtain ⟨ζ, eζ, hpos⟩ := image_dom S₀ hden hw₀den eφ
      rw [hown] at eζ; cases Option.some.inj eζ
      obtain ⟨S', hS'⟩ := hpos rfl
      have hl := (chain_unique_rec hR₀ hc (hch₀.snoc hS' (hw₀own m u' hown))).1
      have hl' : l₀ = l₁ := Option.some.inj hl
      subst hl'
      obtain ⟨aW', ac, haW', -, hcomp⟩ := (AgW.split hW).mp ha'
      rw [AgW.functional haW' haW] at hcomp
      obtain ⟨ξ, t, eξ, ht, hy⟩ :=
        (icp_trans (icpAt_agW haW l₀ _ hcell) (icpAt_left hcomp l₀)).ls
          (CellU.lsOf_immOf _ _ _ _) s.meet_mem
      exact ⟨ξ, t, s.meet, eξ, ht, hy, hβ l₀ _ hcell⟩)
  refine ⟨chainInv_rebDeep hvW hr₀ hch₀ hcell hx hreb hden hW hv h3, hl', hid, hio, hN', hM', hmem,
    ?_⟩
  refine cov_reb_like hvW hcell hreb hW hC (leInvW_of hl' hmem) (fun m u eζ ⟨ψ, ec⟩ => ?_)
    (fun m ζ eζ kζ ⟨ψ, ec⟩ => ?_)
  · obtain ⟨ζ', eζ', hpos⟩ := image_dom S₀ hden hw₀den ec
    rw [eζ] at eζ'; cases Option.some.inj eζ'
    obtain ⟨S, hS⟩ := hpos rfl
    exact ⟨r₀, hr₀, some l₁, S, u, hch₀.snoc hS (hw₀own m u eζ)⟩
  · obtain ⟨S, hS⟩ := image_dom_mut S₀ hden hw₀den ec eζ kζ
    have hg : GPos r₀.R r₀.T r₀.v m S := GPos.of_chain hch₀ hS
    obtain ⟨ζ', eζ', kζ', -⟩ := gpos_mut_cell hg hR₀ (fun _ _ e => e)
    obtain ⟨p, hp, hpr⟩ := (hmem r₀).mp hr₀
    refine ⟨⟨m, ζ'.erase, ζ'.wit, S, r₀.δ⟩, (hmem _).mpr ⟨p, hp, hpr.sub ?_⟩, rfl⟩
    exact ⟨rfl, hg, ζ', eζ', kζ', rfl, rfl⟩

/-- A non-`imm` cell reached through `mut` witnesses from a `●`-part of `C` is in `ex(C)_●`. -/
theorem xpath_ex_part {A C e : WRes} (hle : ResU.Le A C) (he : ExS C e) {p : List Loc}
    {σ : WRes} (hp : XPath A p σ) {x : Loc} {ζ : CellU Loc Val} (ex : σ.get x = some ζ)
    (k : ζ.kind ≠ Kind.imm) : e.get x = some ζ := by
  obtain ⟨τ, hτ⟩ := hle
  cases hp with
  | nil => exact ExS.get_of_ne_imm he (ResU.CompS.get_left_of_ne_imm hτ ex k).2 k
  | cons em km hq =>
      have eC := (ResU.CompS.get_left_of_ne_imm hτ em (by rw [km]; simp)).2
      exact xpath_ex he (XPath.cons eC km hq) ex k

/-- `immEnd` keeps `TI`. -/
theorem ti_end {W Y X' W' : WRes} {ps rs ps' rs' : List FrameRec} {r : FrameRec} {s : LSet}
    {hs : r.R.InStratum s.join} (hvW : ResU.Valid W) (hr : r ∈ ps)
    (hc : ResU.CompS (ResU.single r.le (CellU.immOf s r.v r.R hs)) Y W)
    (hX' : ResU.CompS (ResU.single r.le (CellU.ownOf r.v)) r.R X') (hW' : ResU.CompS X' Y W')
    (hv : ResU.Valid W') (hps : ∀ r', r' ∈ ps' ↔ (r' ∈ ps ∧ r' ≠ r))
    (hrs : ∀ d, d ∈ rs' ↔ ∃ p ∈ ps', DescR p d) (h : TI W ps rs) : TI W' ps' rs' := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hle, hled, hio, hN, hM, hmem, hC⟩ := h
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  obtain ⟨a', ha'⟩ := agW_of_valid hv
  have hrR : r ∈ rs := (hmem r).mpr ⟨r, hr, DescR.refl r⟩
  have sub : ∀ d, d ∈ rs' → d ∈ rs := by
    intro d hd
    obtain ⟨p, hp, hpd⟩ := (hrs d).mp hd
    exact (hmem d).mpr ⟨p, ((hps p).mp hp).1, hpd⟩
  -- a record of `rs` not in `rs'` is in `r`'s lineage
  have gone_desc : ∀ d, d ∈ rs → d ∉ rs' → DescR r d := by
    intro d hd hd'
    obtain ⟨p, hp, hpd⟩ := (hmem d).mp hd
    by_cases hpr : p = r
    · subst hpr; exact hpd
    · exact absurd ((hrs d).mpr ⟨p, (hps p).mpr ⟨hp, hpr⟩, hpd⟩) hd'
  -- the lineage's non-`imm` cells are out of `ag(W′)`
  have hleR : ResU.Le r.R W' := (le_of_compS_right hX').trans (le_of_compS_left hW')
  obtain ⟨σ', eW', aW', heW', haW', -⟩ := id hv
  have gone : ∀ d, DescR r d → ∀ x (ζ : CellU Loc Val), d.R.get x = some ζ →
      ζ.kind ≠ Kind.imm → ∀ a, AgW W' a → a.get x = none := by
    rintro d ⟨p, hp⟩ x ζ e k a ha
    have ex := xpath_ex_part hleR heW' hp.xpath e k
    cases ea : a.get x with
    | none => rfl
    | some ξ =>
        rw [AgW.functional ha haW'] at ea
        exact (ex_ag_disjoint hv heW' haW' ex ea).elim
  have ne : ∀ r' ∈ rs', ∀ m u, r'.R.get m = some (CellU.ownOf u) → m ≠ r.le := by
    intro r' hr' m u hm e
    subst e
    exact hio r hrR r' (sub r' hr') u hm
  have back : ∀ a', AgW W' a' → ∀ m (ψ : CellU Loc Val), a'.get m = some ψ →
      ψ.kind ≠ Kind.own →
      ∃ ψ₀ : CellU Loc Val, aW.get m = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit :=
    fun a' ha' m ψ e hk => end_back hc hX' hW' haW ha' e hk
  have fwd : ∀ a', AgW W' a' → ∀ m, m ≠ r.le → ∀ (ψ₀ : CellU Loc Val), aW.get m = some ψ₀ →
      ψ₀.kind = Kind.imm →
      ∃ ψ, a'.get m = some ψ ∧ ψ.kind = Kind.imm ∧ ψ.erase = ψ₀.erase ∧ ψ.wit = ψ₀.wit :=
    fun a' ha' m hm ψ₀ e₀ k₀ => end_fwd_imm hc hX' hW' haW ha' hm e₀ k₀
  have hleI : LeInv W' ps' := by
    intro r' hr' a₁ ha₁
    have hr'' := (hps r').mp hr'
    have hne : r'.le ≠ r.le := fun e => hr''.2 (hled r' hr''.1 r hr e)
    obtain ⟨ψ₀, e₀, k₀, r₀', w₀⟩ := hle r' hr''.1 aW haW
    obtain ⟨ψ, e, k, r₁, w₁⟩ := fwd a₁ ha₁ r'.le hne ψ₀ e₀ k₀
    exact ⟨ψ, e, k, r₁.trans r₀', w₁.trans w₀⟩
  have chainFwd : ∀ r' ∈ rs', ∀ p m S u, Chain r'.R r'.T r'.v p m S u → ∀ a', AgW W' a' →
      ∀ (ψ₀ : CellU Loc Val), aW.get m = some ψ₀ → ψ₀.kind ≠ Kind.own →
      ∃ ψ, a'.get m = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit := by
    intro r' hr' p m S u hch a' ha' ψ₀ e₀ k₀
    obtain ⟨kk, -⟩ := h1 r' (sub r' hr') p m S u hch aW haW ψ₀ e₀ k₀
    obtain ⟨ψ, e, k, -, w⟩ := fwd a' ha' m (ne r' hr' m u hch.own) ψ₀ e₀ kk
    exact ⟨ψ, e, by rw [k]; simp, w⟩
  obtain ⟨aσ, aY, eR, aR, pR, heR, -, hpR, hcp, hσY, hRY⟩ := end_walks hc hX' hW' haW ha'
  have backI : ∀ m, ICpAt aW a' m := fun m =>
    icpAt_comp hRY (icpAt_trans (icpAt_right hpR m)
      (icpAt_trans (icpAt_right hcp m) (icpAt_left hσY m))) (icpAt_right hσY m)
  have fwdI : ∀ m, m ≠ r.le → ICpAt a' aW m := fun m hm =>
    icpAt_comp hσY (icpAt_comp hcp (icpAt_none (single_ne _ hm))
      (icpAt_comp hpR (icpAt_of_immFree (ExR.immFree heR) m) (icpAt_left hRY m)))
      (icpAt_right hRY m)
  have tm : ∀ x, MutAt W' x → MutAt W x := by
    intro x hm
    rcases MutAt.split hW' hm with h₁ | h₂
    · rcases MutAt.split hX' h₁ with h₃ | h₃
      · exact (not_mutAt_single_own _ _ _ h₃).elim
      · exact MutAt.of_compS_left hc
          (MutAt.nest (ResU.single_get_self _ _) (by simp) (by rw [CellU.wit_immOf]; exact h₃))
    · exact MutAt.of_compS_right hc h₂
  refine ⟨⟨fun r' hr' => ?_, fun r' hr' m u hm a₁ ha₁ => ?_,
    fun r₁ hr₁ r₂ hr₂ => h3 r₁ (sub r₁ hr₁) r₂ (sub r₂ hr₂),
    fun r' hr' => h4 r' (sub r' hr'), fun r' hr' => ?_, fun r' hr' => ?_⟩, hleI,
    fun r₁ hr₁ r₂ hr₂ => hled r₁ ((hps r₁).mp hr₁).1 r₂ ((hps r₂).mp hr₂).1,
    fun r₁ hr₁ r₂ hr₂ => hio r₁ (sub r₁ hr₁) r₂ (sub r₂ hr₂), fun r' hr' => ?_,
    ⟨fun r' hr' hm => hM.1 r' ((hps r').mp hr').1 (tm _ hm),
     fun r' hr' l u hl hm => hM.2 r' (sub r' hr') l u hl (tm _ hm)⟩, hrs, ?_⟩
  -- DeepInv
  · have hr'' := sub r' hr'
    intro p m S u hch a₁ ha₁ ψ e hk
    obtain ⟨ψ₀, e₀, k₀, w₀⟩ := back a₁ ha₁ m ψ e hk
    obtain ⟨kk, d, o, b₁, b₂⟩ := h1 r' hr'' p m S u hch aW haW ψ₀ e₀ k₀
    obtain ⟨ψ', e', k', -, -⟩ := fwd a₁ ha₁ m (ne r' hr' m u hch.own) ψ₀ e₀ kk
    rw [e] at e'; cases Option.some.inj e'
    refine ⟨k', w₀ ▸ d, w₀ ▸ o, fun hp => w₀ ▸ b₁ hp, fun l₀ hp => ?_⟩
    obtain ⟨ψ₁, e₁, k₁, q, hq, hql, hw⟩ := b₂ l₀ hp
    obtain ⟨p₀, S₀, u₀, hch₀, -⟩ := chain_last hch l₀ hp
    obtain ⟨ψ₂, e₂, k₂, w₂⟩ := chainFwd r' hr' p₀ l₀ S₀ u₀ hch₀ a₁ ha₁ ψ₁ e₁ k₁
    exact ⟨ψ₂, e₂, k₂, q, w₂ ▸ hq, hql, w₀.trans hw⟩
  -- support, from the lineage
  · exact exIn_support (exIn_of hleI hrs hr') hm (by simp) a₁ ha₁
  -- JointAt
  · have hr'' := sub r' hr'
    rintro ⟨S, m, u, hR, a₁, ha₁, ψ, e, hk⟩
    obtain ⟨ψ₀, e₀, k₀, -⟩ := back a₁ ha₁ m ψ e hk
    obtain ⟨β₀, x₀, c₀, q1, q2, q3, q4, q5⟩ := h5 r' hr'' ⟨S, m, u, hR, aW, haW, ψ₀, e₀, k₀⟩
    refine ⟨β₀, x₀, c₀, q1, q2, q3, q4, fun S' m' u' hR' a₂ ha₂ ψ₁ e₁ hk₁ => ?_⟩
    obtain ⟨ψ₂, e₂, k₂, w₂⟩ := back a₂ ha₂ m' ψ₁ e₁ hk₁
    obtain ⟨ζ, eζ, wζ⟩ := q5 S' m' u' hR' aW haW ψ₂ e₂ k₂
    exact ⟨ζ, eζ, w₂.trans wζ⟩
  -- JointDeep
  · have hr'' := sub r' hr'
    rintro p₀ l₀ S₀ u₀ hc₀ ⟨m, S, u, hch, a₁, ha₁, ψ, e, hk⟩
    obtain ⟨ψ₀, e₀, k₀, -⟩ := back a₁ ha₁ m ψ e hk
    obtain ⟨w₀, hw₀, β₀, x₀, c₀, q1, q2, q3, q4, q5⟩ :=
      h6 r' hr'' p₀ l₀ S₀ u₀ hc₀ ⟨m, S, u, hch, aW, haW, ψ₀, e₀, k₀⟩
    refine ⟨w₀, fun a₂ ha₂ => ?_, β₀, x₀, c₀, q1, q2, q3, q4,
      fun m' S' u' hc' a₂ ha₂ ψ₁ e₁ hk₁ => ?_⟩
    · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := hw₀ aW haW
      obtain ⟨ψ₃, e₃, k₃, w₃⟩ := chainFwd r' hr' p₀ l₀ S₀ u₀ hc₀ a₂ ha₂ ψ₂ e₂ k₂
      exact ⟨ψ₃, e₃, k₃, w₃.trans w₂⟩
    · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := back a₂ ha₂ m' ψ₁ e₁ hk₁
      obtain ⟨ζ, eζ, wζ⟩ := q5 m' S' u' hc' aW haW ψ₂ e₂ k₂
      exact ⟨ζ, eζ, w₂.trans wζ⟩
  -- NestLife
  · have hr'' := sub r' hr'
    refine nestLife_of_icp (hN r' hr'') haW
      (fun a₁ ha₁ l₀ m S u hc => by rw [AgW.functional ha₁ ha']; exact backI m)
      (fun a₁ ha₁ l₀ m S u hcm => ?_)
    rw [AgW.functional ha₁ ha']
    refine fwdI l₀ (fun hl₀ => ?_)
    obtain ⟨p₀, S₀, u₀, hch₀, -⟩ := chain_last hcm l₀ rfl
    have hown := hch₀.own
    rw [hl₀] at hown
    exact hio r hrR r' hr'' u₀ hown
  -- coverage
  · intro a₁ ha₁ m ψ e hk
    obtain ⟨ζ, eζ, kζ, rζ, wζ, -⟩ := backI m ψ (by rw [← AgW.functional ha₁ ha']; exact e) hk
    rcases hC aW haW m ζ eζ kζ with ⟨r', hr', h₁, h₂, h₃⟩ | ⟨r', hr', p, S, u, hch⟩
    · by_cases hin : r' ∈ rs'
      · exact Or.inl ⟨r', hin, h₁, rζ.symm.trans h₂, wζ.symm.trans h₃⟩
      · exfalso
        have hd := gone_desc r' hr' hin
        rcases hd.cases with rfl | ⟨q, hq, hqq⟩
        · have e₁ := (ResU.CompS.get_left_of_ne_imm hW'
            (ResU.CompS.get_left_of_ne_imm hX' (ResU.single_get_self _ _) (by simp)).2
            (by simp)).2
          rw [← h₁] at e₁
          rw [ag_none_of_top hv ha₁ e₁ (by simp)] at e; cases e
        · obtain ⟨d', hd', -, -, ξ, eξ, kξ, -⟩ := hqq.last hq
          rw [h₁, gone d' hd' _ ξ eξ (by rw [kξ]; simp) a₁ ha₁] at e; cases e
    · by_cases hin : r' ∈ rs'
      · exact Or.inr ⟨r', hin, p, S, u, hch⟩
      · exfalso
        have hd := gone_desc r' hr' hin
        rw [gone r' hd _ _ hch.own (by simp) a₁ ha₁] at e; cases e

/-- `rebEnd`/`rebEndDeep` keep `TI`. -/
theorem ti_endReb {W W' c w₀ : WRes} {ps rs : List FrameRec} {le : Loc} {s : LSet} {v : Val}
    {hs : w₀.InStratum s.join} {β : Life}
    (hvW : ResU.Valid W) (hle : W'.get le = some (CellU.immOf s v w₀ hs))
    (hreb : ResU.Reb β w₀ c) (hW : ResU.CompS W' (c.restrictDom w₀.exclPart) W)
    (hβ : W'.InStratum β)
    (hexcl : ∀ r ∈ rs, ∀ u, w₀.get r.le ≠ some (CellU.ownOf u))
    (h : TI W ps rs) : TI W' ps rs := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hle4, hid, hio, hN, hM, hmem, hC⟩ := h
  have hv : ResU.Valid W' := (ResU.Valid.split hW hvW).1
  obtain ⟨aW, haW⟩ := agW_of_valid hvW
  obtain ⟨a', ha'⟩ := agW_of_valid hv
  obtain ⟨a'', acr, ha'', hacr, hcomp⟩ := (AgW.split hW).mp haW
  rw [AgW.functional ha'' ha'] at hcomp
  have crSrc : ∀ x (ψ : CellU Loc Val), (c.restrictDom w₀.exclPart).get x = some ψ →
      c.get x = some ψ ∧ ∃ ζ : CellU Loc Val, w₀.get x = some ζ ∧ ζ.kind ≠ Kind.imm := by
    intro x ψ e
    cases ex : w₀.exclPart.get x with
    | none => rw [ResU.restrictDom_get_of_none ex] at e; cases e
    | some ζ =>
        rw [ResU.restrictDom_get_of_some ex] at e
        exact ⟨e, ζ, (ResU.exclPart_eq_some.mp ex).1, (ResU.exclPart_eq_some.mp ex).2⟩
  obtain ⟨d', bi, hdb, hbi, hd'⟩ :=
    img_walk ha' hle hreb (fun x ψ e => (crSrc x ψ e).1) hacr
  have R1 : ∀ m (ψ : CellU Loc Val), a'.get m = some ψ → ψ.kind ≠ Kind.own →
      ∃ ψ₀ : CellU Loc Val, aW.get m = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit := by
    intro m ψ e hk
    obtain ⟨ψ₀, e₀, k₀, w₀'⟩ := lift_view hcomp e hk
    exact ⟨ψ₀, e₀, k₀, w₀'.symm⟩
  have R3 : ∀ m (ψ₀ : CellU Loc Val), (c.restrictDom w₀.exclPart).get m = none →
      aW.get m = some ψ₀ → ψ₀.kind = Kind.imm →
      ∃ ψ : CellU Loc Val, a'.get m = some ψ ∧ ψ.kind = Kind.imm ∧ ψ.erase = ψ₀.erase ∧
        ψ.wit = ψ₀.wit := by
    intro m ψ₀ hn e₀ k₀
    rcases imm_back_full hcomp e₀ k₀ with ⟨ψ₁, e₁, k₁, r₁, w₁⟩ | ⟨ψ₁, e₁, k₁, r₁, w₁⟩
    · exact ⟨ψ₁, e₁, k₁, r₁, w₁⟩
    · rcases imm_back_full hdb e₁ k₁ with ⟨ψ₂, e₂, -, -, -⟩ | ⟨ψ₂, e₂, k₂, r₂, w₂⟩
      · have := hd' m ψ₂ e₂; rw [hn] at this; cases this
      · obtain ⟨ζ, eζ, kζ, rζ, wζ, -⟩ := hbi m ψ₂ e₂ k₂
        exact ⟨ζ, eζ, kζ, rζ.trans (r₂.trans r₁), wζ.trans (w₂.trans w₁)⟩
  have R4 : ∀ m (ζ : CellU Loc Val) t y, aW.get m = some ζ → ζ.lsOf = some t → t.mem y →
      (∃ (ζ' : CellU Loc Val) (t' : LSet), a'.get m = some ζ' ∧ ζ'.lsOf = some t' ∧ t'.mem y) ∨
      y = β := by
    intro m ζ t y e ht hy
    rcases ResU.CompR.lsOf_inv hcomp e ht hy with h' | ⟨ξ, t₁, e₁, ht₁, hy₁⟩
    · exact Or.inl h'
    · rcases ResU.CompR.lsOf_inv hdb e₁ ht₁ hy₁ with ⟨ξ₂, t₂, e₂, ht₂, hy₂⟩ |
          ⟨ξ₂, t₂, e₂, ht₂, hy₂⟩
      · obtain ⟨ec, ζw, eζw, kζw⟩ := crSrc m ξ₂ (hd' m ξ₂ e₂)
        rcases reb_cell_ls hreb ec with ⟨-, hl⟩ | ⟨ζ₃, eζ₃, kζ₃, -⟩
        · rw [hl] at ht₂; cases Option.some.inj ht₂; exact Or.inr hy₂
        · rw [eζ₃] at eζw; cases Option.some.inj eζw; exact absurd kζ₃ kζw
      · exact Or.inl ((hbi m ξ₂ e₂).ls ht₂ hy₂)
  have R5 : a'.InStratum β := BoCa.Fig16.BoLo.AgW.inStratum ha' β hβ
  have tm : ∀ x, MutAt W' x → MutAt W x := fun x hm => MutAt.of_compS_left hW hm
  have kimm : ∀ r ∈ rs, ∀ p m S u, Chain r.R r.T r.v p m S u → ∀ ψ : CellU Loc Val,
      a'.get m = some ψ → ψ.kind ≠ Kind.own → ψ.kind = Kind.imm := by
    intro r hr p m S u hc ψ e hk
    cases hkk : ψ.kind with
    | own => exact absurd hkk hk
    | imm => rfl
    | «mut» => exact (hM.2 r hr m u hc.own (tm _ (agW_mut ha' m ψ e hkk))).elim
  have hN' : ∀ r ∈ rs, NestLife W' r := by
    intro r hr l₀ m S u hc a₁ ha₁ ψ s' e hs' x hx
    rw [AgW.functional ha₁ ha'] at e ⊢
    obtain ⟨ζ, t, eζ, ht, hxt⟩ := (icpAt_left hcomp m ψ e).ls hs' hx
    obtain ⟨ζ₀, t₀, y, e₀, ht₀, hy, hxy⟩ := hN r hr l₀ m S u hc aW haW ζ t eζ ht x hxt
    rcases R4 l₀ ζ₀ t₀ y e₀ ht₀ hy with ⟨ζ', t', e', ht', hy'⟩ | rfl
    · exact ⟨ζ', t', y, e', ht', hy', hxy⟩
    · exfalso
      have hin : y < s'.meet := (Life.sqsupset_iff _ _).mp (CellU.sqsupset_of_lsOf hs' (R5 m ψ e))
      exact lt_asymm (lt_of_lt_of_le hin (s'.meet_least x hx)) hxy
  have parent : ∀ r ∈ rs, ∀ l₀ m S u, Chain r.R r.T r.v (some l₀) m S u →
      ∀ ψ : CellU Loc Val, a'.get m = some ψ → ψ.kind ≠ Kind.own →
      ∃ ζ : CellU Loc Val, a'.get l₀ = some ζ ∧ ζ.kind ≠ Kind.own := by
    intro r hr l₀ m S u hc ψ e hk
    obtain ⟨s', hs'⟩ := lsOf_of_imm (kimm r hr _ m S u hc ψ e hk)
    obtain ⟨ζ, t, y, eζ, ht, -, -⟩ := hN' r hr l₀ m S u hc a' ha' ψ s' e hs' s'.meet s'.meet_mem
    exact ⟨ζ, eζ, by rw [CellU.kind_of_lsOf ht]; simp⟩
  have hD' : ∀ r ∈ rs, DeepInv W' r := by
    intro r hr p m S u hc a₁ ha₁ ψ e hk
    rw [AgW.functional ha₁ ha'] at e ⊢
    obtain ⟨ψ₀, e₀, k₀, w₀'⟩ := R1 m ψ e hk
    obtain ⟨-, d, o, b₁, b₂⟩ := h1 r hr p m S u hc aW haW ψ₀ e₀ k₀
    refine ⟨kimm r hr p m S u hc ψ e hk, w₀' ▸ d, w₀' ▸ o, fun hp => w₀' ▸ b₁ hp,
      fun l₀ hp => ?_⟩
    subst hp
    obtain ⟨ζ, eζ, kζ⟩ := parent r hr l₀ m S u hc ψ e hk
    obtain ⟨ζ₀, eζ₀, -, wζ⟩ := R1 l₀ ζ eζ kζ
    obtain ⟨ψ₁, e₁, k₁, q, hq, hql, hw⟩ := b₂ l₀ rfl
    rw [eζ₀] at e₁; cases Option.some.inj e₁
    exact ⟨ζ, eζ, kζ, q, wζ ▸ hq, hql, w₀'.trans hw⟩
  have hle' : LeInv W' ps := by
    intro r hr a₁ ha₁
    rw [AgW.functional ha₁ ha']
    obtain ⟨ψ₀, e₀, k₀, r₀, w₀''⟩ := hle4 r hr aW haW
    have hrR : r ∈ rs := (hmem r).mpr ⟨r, hr, DescR.refl r⟩
    have hn : (c.restrictDom w₀.exclPart).get r.le = none := by
      cases ecr : (c.restrictDom w₀.exclPart).get r.le with
      | none => rfl
      | some φ =>
          exfalso
          obtain ⟨-, ζ, eζ, kζ⟩ := crSrc _ _ ecr
          rcases CellU.rep ζ with ⟨u', rfl⟩ | ⟨s₁, v₁, χ₁, h₁, rfl⟩ |
              ⟨b₁, v₁, χ₁, h₁, P, hw, rfl⟩
          · exact hexcl r hrR u' eζ
          · exact kζ (CellU.kind_immOf _ _ _ _)
          · exact hM.1 r hr (tm _ (mutAt_of_cell hle (MutAt.top eζ (by simp))))
    obtain ⟨ψ, e, k, rr, ww⟩ := R3 r.le ψ₀ hn e₀ k₀
    exact ⟨ψ, e, k, rr.trans r₀, ww.trans w₀''⟩
  have h5' : ∀ r ∈ rs, JointAt W' r := by
    intro r hr
    rintro ⟨S, m, u, hR, a₁, ha₁, ψ, e, hk⟩
    rw [AgW.functional ha₁ ha'] at e
    obtain ⟨ψ₀, e₀, k₀, -⟩ := R1 m ψ e hk
    obtain ⟨β₀, x₀, c₀, q1, q2, q3, q4, q5⟩ := h5 r hr ⟨S, m, u, hR, aW, haW, ψ₀, e₀, k₀⟩
    refine ⟨β₀, x₀, c₀, q1, q2, q3, q4, fun S' m' u' hR' a₂ ha₂ ψ₁ e₁ hk₁ => ?_⟩
    rw [AgW.functional ha₂ ha'] at e₁
    obtain ⟨ψ₂, e₂, k₂, w₂⟩ := R1 m' ψ₁ e₁ hk₁
    obtain ⟨ζ, eζ, wζ⟩ := q5 S' m' u' hR' aW haW ψ₂ e₂ k₂
    exact ⟨ζ, eζ, w₂.trans wζ⟩
  have h6' : ∀ r ∈ rs, JointDeep W' r := by
    intro r hr
    rintro p₀ l₀ S₀ u₀ hc₀ ⟨m, S, u, hc, a₁, ha₁, ψ, e, hk⟩
    rw [AgW.functional ha₁ ha'] at e
    obtain ⟨ψ₀, e₀, k₀, -⟩ := R1 m ψ e hk
    obtain ⟨w₁, hw₁, β₀, x₀, c₀, q1, q2, q3, q4, q5⟩ :=
      h6 r hr p₀ l₀ S₀ u₀ hc₀ ⟨m, S, u, hc, aW, haW, ψ₀, e₀, k₀⟩
    obtain ⟨ζ, eζ, kζ⟩ := parent r hr l₀ m S u hc ψ e hk
    obtain ⟨ζ₀, eζ₀, -, wζ⟩ := R1 l₀ ζ eζ kζ
    obtain ⟨ψ₂, e₂, -, w₂⟩ := hw₁ aW haW
    rw [eζ₀] at e₂; cases Option.some.inj e₂
    refine ⟨w₁, fun a₂ ha₂ => ⟨ζ, by rw [AgW.functional ha₂ ha']; exact eζ, kζ, wζ.trans w₂⟩,
      β₀, x₀, c₀, q1, q2, q3, q4, fun m' S' u' hc' a₂ ha₂ ψ₁ e₁ hk₁ => ?_⟩
    rw [AgW.functional ha₂ ha'] at e₁
    obtain ⟨ψ₃, e₃, k₃, w₃⟩ := R1 m' ψ₁ e₁ hk₁
    obtain ⟨ζ', eζ', wζ'⟩ := q5 m' S' u' hc' aW haW ψ₃ e₃ k₃
    exact ⟨ζ', eζ', w₃.trans wζ'⟩
  have h2' : ∀ r ∈ rs, ∀ m u, r.R.get m = some (CellU.ownOf u) → ∀ a, AgW W' a →
      ∃ ζ, a.get m = some ζ :=
    fun r hr m u hm => exIn_support (exIn_of hle' hmem hr) hm (by simp)
  refine ⟨⟨hD', h2', h3, h4, h5', h6'⟩, hle', hid, hio, hN',
    ⟨fun r hr hm => hM.1 r hr (tm _ hm), fun r hr l u hl hm => hM.2 r hr l u hl (tm _ hm)⟩,
    hmem, coverage_of_icp haW hC (fun a₁ ha₁ m => ?_)⟩
  rw [AgW.functional ha₁ ha']
  exact icpAt_left hcomp m

/-- Every `TW` world satisfies `TI`. -/
theorem TW.inv {W : WRes} {ps rs : List FrameRec} (h : TW W ps rs) : TI W ps rs := by
  induction h with
  | empty =>
      refine ⟨⟨fun r hr => absurd hr (by simp), fun r hr => absurd hr (by simp),
        fun r hr => absurd hr (by simp), fun r hr => absurd hr (by simp),
        fun r hr => absurd hr (by simp), fun r hr => absurd hr (by simp)⟩,
        fun r hr => absurd hr (by simp),
        fun r hr => absurd hr (by simp), fun r hr => absurd hr (by simp),
        fun r hr => absurd hr (by simp),
        ⟨fun r hr => absurd hr (by simp), fun r hr => absurd hr (by simp)⟩,
        fun x => ⟨fun hx => absurd hx (by simp), fun ⟨p, hp, _⟩ => absurd hp (by simp)⟩, ?_⟩
      intro a ha m ψ e _
      rw [AgW.functional ha agW_empty, PMap.empty_get] at e; cases e
  | alloc _ _ _ hW _ ih =>
      refine ti_of_ag (fun a ha => alloc_ag hW ha) (fun x hm => ?_) ih
      rcases MutAt.split hW hm with h | h
      · exact h
      · exact (not_mutAt_single_own _ _ _ h).elim
  | immFrame T δ hα hW₀ hadm hX hW hden hW' hv hds ih =>
      exact ti_frame hW₀.valid hadm hX hW hden hW' hv hds ih
  | reb r x hW₀ hr hle hx hreb hden _ hW hv ih =>
      exact ti_reb hW₀.valid hr hle hx hreb hden hW hv ih
  | rebDeep r x hW₀ hr hch hcell hx hreb hden hβ hW hv ih =>
      exact ti_rebDeep hW₀.valid hr hch hcell hx hreb hden hβ hW hv ih
  | mutFold hW₀ hX hW hW' _ ih => exact ti_mutFold hW₀.valid hX hW hW' ih
  | mutUnfold hW₀ hW hX hW' _ ih =>
      refine ti_of_ag (fun a ha => (mut_fold_ag hX hW' hW a).mp ha) (fun x hm => ?_) ih
      rcases MutAt.split hW' hm with h | h
      · rcases MutAt.split hX h with h' | h'
        · exact (not_mutAt_single_own _ _ _ h').elim
        · refine MutAt.nest (ResU.CompS.get_left_of_ne_imm hW (ResU.single_get_self _ _)
            (by simp)).2 (by simp) ?_
          rw [CellU.wit_mutOf]; exact h'
      · exact MutAt.of_compS_right hW h
  | free hW₀ hW _ ih =>
      exact ti_of_ag (fun a ha => (own_cell_ag hW a).mpr ha)
        (fun x hm => MutAt.of_compS_right hW hm) ih
  | store hW₀ hW hW' _ ih =>
      refine ti_of_ag (fun a ha => (own_cell_ag hW a).mpr ((own_cell_ag hW' a).mp ha))
        (fun x hm => ?_) ih
      rcases MutAt.split hW' hm with h | h
      · exact (not_mutAt_single_own _ _ _ h).elim
      · exact MutAt.of_compS_right hW h
  | immEnd r hW₀ hr hc hX' hW' hv hps hrs ih => exact ti_end hW₀.valid hr hc hX' hW' hv hps hrs ih
  | rebEnd r hW₀ hr hle hreb hW hβ ih =>
      exact ti_endReb hW₀.valid hle hreb hW hβ (fun r' hr' u hu => ih.2.2.2.1 r' hr' r hr u hu) ih
  | @rebEndDeep W W' c ps rs r p l₀ S₀ u₀ s w₀ hs β hW₀ hr hch hle hreb hW hβ ih =>
      have hvW := hW₀.valid
      have hexcl : ∀ r' ∈ rs, ∀ u, w₀.get r'.le ≠ some (CellU.ownOf u) := by
        intro r' hr' u hu
        obtain ⟨aW, haW⟩ := agW_of_valid hvW
        obtain ⟨a', ha'⟩ := agW_of_valid (ResU.Valid.split hW hvW).1
        obtain ⟨a'', acr, ha'', -, hcomp⟩ := (AgW.split hW).mp haW
        rw [AgW.functional ha'' ha'] at hcomp
        obtain ⟨χ, eχ, kχ, -, wχ⟩ := AgW.get_imm ha' hle (CellU.kind_immOf _ _ _ _)
        obtain ⟨ψ₀, e₀, k₀, w₀'⟩ := lift_view hcomp eχ (by rw [kχ]; simp)
        obtain ⟨-, -, o, -, -⟩ := ih.1.1 r hr p l₀ S₀ u₀ hch aW haW ψ₀ e₀ k₀
        rw [w₀', wχ, CellU.wit_immOf] at o
        exact ih.2.2.2.1 r' hr' r hr u (o _ u hu)
      exact ti_endReb hvW hle hreb hW hβ hexcl ih

/-- The type a reborrow puts at a `Mut` position is coherent: `Imm̲ 'x (Mut @a S) =
Imm 'x S` at `δ[x↦β]`, against the sub-record at that position. -/
theorem coh_mut {W : WRes} {ps rs : List FrameRec} (hTW : TW W ps rs) {r₀ : FrameRec}
    (hr₀ : r₀ ∈ rs) {x : LifeVar} {β : Life} (hx : ¬ VFree x r₀.T) {m : Loc} {S : VTy}
    (hS : MutPos r₀.T r₀.v m S) : Coh rs m S (r₀.δ.extend x β) := by
  have hR₀ := (hTW.inv.1.2.2.2.1 r₀ hr₀).1
  obtain ⟨ζ, eζ, kζ, -⟩ := mut_split_den hS hR₀
  have hd : SubRec r₀ ⟨m, ζ.erase, ζ.wit, S, r₀.δ⟩ := ⟨rfl, GPos.here hS, ζ, eζ, kζ, rfl, rfl⟩
  refine Or.inl ⟨_, hTW.inv.sub hr₀ hd, rfl, rfl, fun y hy => ?_⟩
  have hxy : x ≠ y := fun e => hx (e ▸ hS.free hy)
  exact find?_extend_ne _ _ hxy

/-- …and below a chain position, for a reborrow run at a coherent `δ′`. -/
theorem coh_mut_child {W : WRes} {ps rs : List FrameRec} (hTW : TW W ps rs) {r : FrameRec}
    (hr : r ∈ rs) {p : Option Loc} {l₀ : Loc} {S₀ : VTy} {u₀ : Val}
    (hch : Chain r.R r.T r.v p l₀ S₀ u₀) {δ' : LSub} (hag : AgreeOn S₀ δ' r.δ) {x : LifeVar}
    {β : Life} (hx : ¬ VFree x S₀) {m : Loc} {S : VTy} (hS : MutPos S₀ u₀ m S) :
    Coh rs m S (δ'.extend x β) := by
  have hR := (hTW.inv.1.2.2.2.1 r hr).1
  have hg : GPos r.R r.T r.v m S := GPos.of_chain hch hS
  obtain ⟨ζ, eζ, kζ, -⟩ := gpos_mut_cell hg hR (fun _ _ e => e)
  have hd : SubRec r ⟨m, ζ.erase, ζ.wit, S, r.δ⟩ := ⟨rfl, hg, ζ, eζ, kζ, rfl, rfl⟩
  refine Or.inl ⟨_, hTW.inv.sub hr hd, rfl, rfl, fun y hy => ?_⟩
  have hxy : x ≠ y := fun e => hx (e ▸ hS.free hy)
  rw [find?_extend_ne _ _ hxy]
  exact hag y (hS.free hy)

/-- A typed record whose escrow has an `ex(R)_●` has a finite lineage. -/
theorem lineage_list {r : FrameRec} (hR : vShape r.T r.δ r.v r.R) (hadm : AdmWf r.T r.δ)
    {eR : WRes} (heR : ExS r.R eR) : ∃ ds : List FrameRec, ∀ d, d ∈ ds ↔ Desc r d := by
  classical
  -- a proper member's location is in `dom(ex(R)_●)`, through its parent's `mut` cell
  have loc_ex : ∀ d, Desc r d → ∃ (d' : FrameRec) (p : List Loc) (ζ : CellU Loc Val),
      LinPath r p d' ∧ SubRec d' d ∧ d'.R.get d.le = some ζ ∧ ζ.kind = Kind.mut ∧
      eR.get d.le = some ζ := by
    rintro d ⟨p, hp, hpd⟩
    obtain ⟨d', ⟨p', hp'⟩, hs⟩ := hpd.last hp
    obtain ⟨-, -, ζ, eζ, kζ, -, -⟩ := id hs
    exact ⟨d', p', ζ, hp', hs, eζ, kζ, xpath_ex heR hp'.xpath eζ (by rw [kζ]; simp)⟩
  have hinj : Set.InjOn FrameRec.le {d | Desc r d} := by
    intro d₁ h₁ d₂ h₂ he
    obtain ⟨d₁', p₁, ζ₁, hp₁, hs₁, e₁, k₁, -⟩ := loc_ex d₁ h₁
    obtain ⟨d₂', p₂, ζ₂, hp₂, hs₂, e₂, k₂, -⟩ := loc_ex d₂ h₂
    rw [he] at e₁
    have hpp := xpath_unique heR hp₁.xpath hp₂.xpath e₁ (by rw [k₁]; simp) e₂ (by rw [k₂]; simp)
    subst hpp
    have hdd := hp₁.functional hR hadm hp₂
    subst hdd
    obtain ⟨hR', -⟩ := hp₁.typed hR hadm
    exact SubRec.functional hR' hs₁ hs₂ he
  obtain ⟨dl, hdl⟩ := eR.finite
  have himg : (FrameRec.le '' {d | Desc r d}).Finite := by
    refine (List.finite_toSet dl).subset ?_
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨-, -, ζ, -, -, -, -, e⟩ := loc_ex d hd
    exact hdl _ (by rw [e]; simp)
  have hfin : {d | Desc r d}.Finite := Set.Finite.of_finite_image himg hinj
  refine ⟨hfin.toFinset.toList, fun d => ?_⟩
  simp

/-- The source memory, from `#`. -/
theorem lower_of_hash {ρf ρ fρ : WRes} (hf : ResU.Hash ρf ρ) (hc : ResU.CompS ρf ρ fρ) :
    ∃ μ, ResU.Lower fρ μ := by
  obtain ⟨σ, μ, hσ, -, hμ⟩ := hash_lower hf
  cases ResU.CompS.functional hσ hc
  exact ⟨μ, hμ⟩

end BoCa.Fig16.LogRel.Core

end

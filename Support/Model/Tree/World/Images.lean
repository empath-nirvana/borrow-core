import Support.Model.Tree.World.Records
import Support.Model.Tree.Port.ClosingSentence

/-!
# The image lemmas of `Core/Images.lean` over the tree carrier

`[spec §62]`. The transfer lemmas the typed world's invariant is proved from, read over
`CellUT K`: a non-`own` cell lifted through `○` and `●` (`lift_view`, `lift_part`,
`back_view`), the walks of a framed world (`frame_walks`, `frame_transfer`), and a reborrow's
image carried into the aliasable walk (`reb_cell`, `reb_transfer_gen`). Each is
`Core/Images.lean`'s proof at the tree carrier's cells; no printed row changes.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa.Fig16.Tree
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
variable {R : CellUT Loc Val K → CellUT Loc Val K → Prop}

theorem comp_get_l {ρ₁ ρ₂ ρ : (ResUT BoCa.Loc BoCa.Val K)} (h : ResUT.Comp R C ρ₁ ρ₂ ρ) {l : Loc} {ψ : CellUT Loc Val K}
    (e₁ : ρ₁.get l = some ψ) (e₂ : ρ₂.get l = none) : ρ.get l = some ψ := by
  have := h.2 l; rw [e₁, e₂] at this; exact this

end BoCa.Fig16.Tree.Wp

namespace BoCa.Fig16.Tree.Wp
open BoCa.Fig16.Tree
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

theorem single_ne {l l' : Loc} (ψ : CellUT Loc Val K) (h : l' ≠ l) : (ResUT.single l ψ).get l' = none :=
  ResUT.single_get_ne ψ h

theorem flat_empty : ResUT.Flat (PMap.empty : (ResUT BoCa.Loc BoCa.Val K)) PMap.empty :=
  ⟨_, _, ExWT.empty_of_all_imm (fun l ψ e => absurd e (by simp)), BoCa.Fig16.Tree.agW_empty,
    ResUT.comp_empty_left _⟩

theorem comp_some {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop}
    {ρ₁ ρ₂ ρ : (ResUT BoCa.Loc BoCa.Val K)} (h : ResUT.Comp R C ρ₁ ρ₂ ρ) {l : Loc} {ψ : CellUT Loc Val K}
    (e : ρ₁.get l = some ψ) : ∃ ζ, ρ.get l = some ζ := by
  have := h.2 l
  rw [e] at this
  cases e2 : ρ₂.get l <;> rw [e2] at this
  · exact ⟨_, this⟩
  · obtain ⟨ζ, hz, -⟩ := this; exact ⟨ζ, hz⟩

/-- A non-`own` cell of an operand of `○` reaches the composite as a non-`own` cell over the
same witness. -/
theorem lift_view {a₁ a₂ a : (ResUT BoCa.Loc BoCa.Val K)} (h : ResUT.CompR a₁ a₂ a) {l : Loc} {ψ₁ : CellUT Loc Val K}
    (e : a₁.get l = some ψ₁) (hk : ψ₁.kind ≠ Kind.own) :
    ∃ ψ, a.get l = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.wit = ψ₁.wit := by
  have := h.2 l
  rw [e] at this
  cases e2 : a₂.get l <;> rw [e2] at this
  · exact ⟨_, this, hk, rfl⟩
  · obtain ⟨ψ, hψ, hC⟩ := this
    refine ⟨ψ, hψ, ?_⟩
    cases hC with
    | same => exact ⟨hk, rfl⟩
    | strict k =>
        have hc := CellUT.compS_spec _ _ k
        exact ⟨by rw [CellUT.CompS.kind hc]; exact fun c => Kind.noConfusion c,
          (CellUT.CompS.wit hc).1⟩
    | mutMut => exact ⟨by simp, by simp⟩
    | mutOwn => exact ⟨hk, rfl⟩
    | ownMut => exact absurd (CellUT.kind_ownOf _) hk
    | immOwn => exact ⟨hk, rfl⟩
    | ownImm => exact absurd (CellUT.kind_ownOf _) hk
    | immMut => exact ⟨hk, rfl⟩
    | mutImm => exact ⟨by rw [CellUT.kind_immOf]; exact fun c => Kind.noConfusion c,
        by rw [CellUT.wit_immOf]; simp⟩

/-- A non-`own` cell of `ψ₁ ○ ψ₂` has the witness of a non-`own` operand. -/
theorem CellUT.CompR.back_view {ψ₁ ψ₂ ψ : CellUT Loc Val K} (h : CellUT.CompR ψ₁ ψ₂ ψ)
    (hk : ψ.kind ≠ Kind.own) :
    (ψ₁.kind ≠ Kind.own ∧ ψ.wit = ψ₁.wit) ∨ (ψ₂.kind ≠ Kind.own ∧ ψ.wit = ψ₂.wit) := by
  cases h with
  | same => exact Or.inl ⟨hk, rfl⟩
  | strict k =>
      have hc := CellUT.compS_spec _ _ k
      exact Or.inl ⟨by rw [(CellUT.CompatS.kinds k).1]; exact fun c => Kind.noConfusion c,
        (CellUT.CompS.wit hc).1⟩
  | mutMut => exact Or.inl ⟨by simp, by simp⟩
  | mutOwn => exact Or.inl ⟨hk, rfl⟩
  | ownMut => exact Or.inr ⟨hk, rfl⟩
  | immOwn => exact Or.inl ⟨hk, rfl⟩
  | ownImm => exact Or.inr ⟨hk, rfl⟩
  | immMut => exact Or.inl ⟨hk, rfl⟩
  | mutImm => exact Or.inr ⟨hk, rfl⟩

/-- …and at the resource level. -/
theorem back_view {a₁ a₂ a : (ResUT BoCa.Loc BoCa.Val K)} (h : ResUT.CompR a₁ a₂ a) {l : Loc} {ψ : CellUT Loc Val K}
    (e : a.get l = some ψ) (hk : ψ.kind ≠ Kind.own) :
    (∃ ψ₁, a₁.get l = some ψ₁ ∧ ψ₁.kind ≠ Kind.own ∧ ψ.wit = ψ₁.wit) ∨
    (∃ ψ₂, a₂.get l = some ψ₂ ∧ ψ₂.kind ≠ Kind.own ∧ ψ.wit = ψ₂.wit) := by
  rcases ResUT.Comp.get h l with ⟨-, -, e'⟩ | ⟨ζ, e₁, -, e'⟩ | ⟨ζ, -, e₂, e'⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁, e₂, e', hC⟩
  · rw [e'] at e; cases e
  · rw [e'] at e; cases e; exact Or.inl ⟨_, e₁, hk, rfl⟩
  · rw [e'] at e; cases e; exact Or.inr ⟨_, e₂, hk, rfl⟩
  · rw [e'] at e; cases e
    rcases CellUT.CompR.back_view hC hk with ⟨k, w⟩ | ⟨k, w⟩
    · exact Or.inl ⟨_, e₁, k, w⟩
    · exact Or.inr ⟨_, e₂, k, w⟩

theorem back_some {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop}
    {a₁ a₂ a : (ResUT BoCa.Loc BoCa.Val K)} (h : ResUT.Comp R C a₁ a₂ a) {l : Loc} {ψ : CellUT Loc Val K}
    (e : a.get l = some ψ) : (∃ ψ₁, a₁.get l = some ψ₁) ∨ (∃ ψ₂, a₂.get l = some ψ₂) := by
  rcases ResUT.Comp.get h l with ⟨-, -, e'⟩ | ⟨ζ, e₁, -, -⟩ | ⟨ζ, -, e₂, -⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁, -, -, -⟩
  · rw [e'] at e; cases e
  · exact Or.inl ⟨_, e₁⟩
  · exact Or.inr ⟨_, e₂⟩
  · exact Or.inl ⟨_, e₁⟩

/-- Forward lift of a non-`own` cell through the right operand. -/
theorem lift_view_r {a₁ a₂ a : (ResUT BoCa.Loc BoCa.Val K)} (h : ResUT.CompR a₁ a₂ a) {l : Loc} {ψ₂ : CellUT Loc Val K}
    (e : a₂.get l = some ψ₂) (hk : ψ₂.kind ≠ Kind.own) :
    ∃ ψ, a.get l = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.wit = ψ₂.wit :=
  lift_view (ResUT.CompR.comm h) e hk

theorem comp_some_r {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop}
    {ρ₁ ρ₂ ρ : (ResUT BoCa.Loc BoCa.Val K)} (h : ResUT.Comp R C ρ₁ ρ₂ ρ) {l : Loc} {ψ : CellUT Loc Val K}
    (e : ρ₂.get l = some ψ) : ∃ ζ, ρ.get l = some ζ := by
  rcases ResUT.Comp.get h l with ⟨-, e₂, -⟩ | ⟨ζ, -, e₂, -⟩ | ⟨ζ, -, -, e'⟩ |
      ⟨ζ₁, ζ₂, ζ, -, -, e', -⟩
  · rw [e₂] at e; cases e
  · rw [e₂] at e; cases e
  · exact ⟨_, e'⟩
  · exact ⟨_, e'⟩

/-- At a valid resource, the exclusive and aliasable walks have disjoint domains:
`⦇ρ⦈ = ex(ρ)_● ● ag(ρ)` is strict, `●` relates `imm` cells only, and `ex(ρ)_●` has
none (`ExST.immFree`, `[TR]` 6.36). -/
theorem ex_ag_disjoint {W e a : (ResUT BoCa.Loc BoCa.Val K)} (hv : ResUT.Valid W) (he : ExST W e) (ha : AgWT W a)
    {l : Loc} {ψ₁ ψ₂ : CellUT Loc Val K} (e₁ : e.get l = some ψ₁) (e₂ : a.get l = some ψ₂) :
    False := by
  obtain ⟨σ, e', a', he', ha', hc⟩ := hv
  rw [ExST.functional he' he] at hc
  rw [AgWT.functional ha' ha] at hc
  rcases ResUT.Comp.get hc l with ⟨e₁', -, -⟩ | ⟨ζ, -, e₂', -⟩ | ⟨ζ, e₁', -, -⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁', -, -, hC⟩
  · rw [e₁'] at e₁; cases e₁
  · rw [e₂'] at e₂; cases e₂
  · rw [e₁'] at e₁; cases e₁
  · rw [e₁'] at e₁; cases e₁
    obtain ⟨s₁, s₂, v, ρ, k₁, k₂, k₃, h₁, -, -⟩ := hC
    exact ExST.immFree he l _ e₁' (by rw [h₁]; rfl)

theorem lift_part {W σ₀ t aW et at' pt : (ResUT BoCa.Loc BoCa.Val K)} {le : Loc} {s : TSet} {v : Val}
    {hs : σ₀.InStratum s} (hle : W.get le = some (CellUT.immOf s v σ₀ hs))
    (ht : ResUT.Le t σ₀) (haW : AgWT W aW) (het : ExRT t et) (hat : AgWT t at')
    (hpt : ResUT.CompR et at' pt) {l : Loc} {ψ : CellUT Loc Val K} (e : pt.get l = some ψ)
    (hk : ψ.kind ≠ Kind.own) :
    ∃ ψ₀, aW.get l = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ₀.wit = ψ.wit := by
  obtain ⟨τ, hτ⟩ := ht
  obtain ⟨a₁, a₂, -, h₂, h12⟩ := (AgWT.split (ResUT.del_compS hle)).mp haW
  obtain ⟨e₀, a₀, p₀, he₀, ha₀, hp₀, hcp₀⟩ := AgWT.single_imm_inv h₂
  have up : ∀ ψ', p₀.get l = some ψ' → ψ'.kind ≠ Kind.own →
      ∃ ψ₀, aW.get l = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ₀.wit = ψ'.wit := by
    intro ψ' e' k'
    obtain ⟨ψ₁, e₁, k₁, w₁⟩ := lift_view_r hcp₀ e' k'
    obtain ⟨ψ₂, e₂, k₂, w₂⟩ := lift_view_r h12 e₁ k₁
    exact ⟨ψ₂, e₂, k₂, w₂.trans w₁⟩
  rcases back_view hpt e hk with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₁, e₁, k₁, w₁⟩
  · obtain ⟨x₁, x₂, hx₁, -, hx⟩ := (ExRT.split_of_compS hτ).mp he₀
    rw [ExRT.functional hx₁ het] at hx
    obtain ⟨ψ₂, e₂, k₂, w₂⟩ := lift_view hx e₁ k₁
    obtain ⟨ψ₃, e₃, k₃, w₃⟩ := lift_view hp₀ e₂ k₂
    obtain ⟨ψ₄, e₄, k₄, w₄⟩ := up ψ₃ e₃ k₃
    exact ⟨ψ₄, e₄, k₄, w₄.trans (w₃.trans (w₂.trans w₁.symm))⟩
  · obtain ⟨y₁, y₂, hy₁, -, hy⟩ := (AgWT.split hτ).mp ha₀
    rw [AgWT.functional hy₁ hat] at hy
    obtain ⟨ψ₂, e₂, k₂, w₂⟩ := lift_view hy e₁ k₁
    obtain ⟨ψ₃, e₃, k₃, w₃⟩ := lift_view_r hp₀ e₂ k₂
    obtain ⟨ψ₄, e₄, k₄, w₄⟩ := up ψ₃ e₃ k₃
    exact ⟨ψ₄, e₄, k₄, w₄.trans (w₃.trans (w₂.trans w₁.symm))⟩

theorem reb_support {W W' c aW a' : (ResUT BoCa.Loc BoCa.Val K)} (hW : ResUT.CompS W c W') (haW : AgWT W aW)
    (ha' : AgWT W' a') {l : Loc} {ψ : CellUT Loc Val K} (e : aW.get l = some ψ) :
    ∃ ζ, a'.get l = some ζ := by
  obtain ⟨σw, σc, hw, -, hcomp⟩ := (AgWT.split hW).mp ha'
  rw [AgWT.functional hw haW] at hcomp
  exact comp_some hcomp e

/-- The walks of the three configurations of an `immFrame` step, named once.
`W = (ℓ ↦ own(v) ● R) ● Z`, `W' = ℓ ↦ imm({α}, v, R) ● Z`. -/
theorem frame_walks {W X Z R W' a' : (ResUT BoCa.Loc BoCa.Val K)} {l : Loc} {v : Val} {α : Life}
    {h : R.InStratum (TSet.single α)}
    (hX : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) R X) (hW : ResUT.CompS X Z W)
    (hW' : ResUT.CompS (ResUT.single l (CellUT.immOf (TSet.single α) v R h)) Z W')
    (hv : ResUT.Valid W) (ha' : AgWT W' a') :
    ∃ eW aW r z eR σc pc, ExST W eW ∧ AgWT W aW ∧ AgWT R r ∧ ResUT.CompR r z aW ∧
      ExST R eR ∧ (∀ m ζ, eR.get m = some ζ → ∃ ζ', eW.get m = some ζ') ∧
      eW.get l = some (CellUT.ownOf v) ∧
      ResUT.CompR eR r pc ∧
      ResUT.CompR (ResUT.single l (CellUT.immOf (TSet.single α) v R h)) pc σc ∧
      ResUT.CompR σc z a' := by
  obtain ⟨σ, eW, aW, heW, haW, -⟩ := hv
  obtain ⟨x, z, hx, hz, hxz⟩ := (AgWT.split hW).mp haW
  obtain ⟨o, r, ho, hr, hor⟩ := (AgWT.split hX).mp hx
  rw [AgWT.functional ho (AgWT.single_own l v)] at hor
  rw [ResUT.CompR.functional hor (ResUT.comp_empty_left r)] at hxz
  obtain ⟨σc, σz, hc, hz', hcz⟩ := (AgWT.split hW').mp ha'
  rw [AgWT.functional hz' hz] at hcz
  obtain ⟨ec, ac, pc, hec, hac, hpc, hcp⟩ := AgWT.single_imm_inv hc
  rw [AgWT.functional hac hr] at hpc
  obtain ⟨eX, eZ, heX, -, heXZ⟩ := (ExST.split hW).mp heW
  obtain ⟨eo, eR, heo, heR, heoR⟩ := (ExST.split hX).mp heX
  rw [ExRT.functional hec (ExST.toExR heR)] at hpc
  rw [ExST.functional heo (ExWT.single_own l v)] at heoR
  refine ⟨eW, aW, r, z, eR, σc, pc, heW, haW, hr, hxz, heR,
    fun m ζ e => ?_, ?_, hpc, hcp, hcz⟩
  · obtain ⟨ζ₁, e₁⟩ := comp_some_r heoR e
    exact comp_some heXZ e₁
  · have e₁ := comp_get_l heoR (ResUT.single_get_self l _) (by
      rcases ResUT.Comp.get heoR l with ⟨e₁, -, -⟩ | ⟨ζ, -, e₂, -⟩ | ⟨ζ, e₁, -, -⟩ |
          ⟨ζ₁, ζ₂, ζ, e₁, e₂, -, hC⟩
      · rw [ResUT.single_get_self] at e₁; cases e₁
      · exact e₂
      · rw [ResUT.single_get_self] at e₁; cases e₁
      · rw [ResUT.single_get_self] at e₁; cases e₁
        obtain ⟨s₁, s₂, v', ρ, k₁, k₂, k₃, h₁, -, -⟩ := hC
        exact absurd h₁ CellUT.ownOf_ne_immOf)
    have hne : (CellUT.ownOf (K := K) (Loc := Loc) v).kind ≠ Kind.imm := by simp
    rcases ResUT.Comp.get heXZ l with ⟨e₃, -, -⟩ | ⟨ζ, e₃, -, e₄⟩ | ⟨ζ, e₃, -, -⟩ |
        ⟨ζ₁, ζ₂, ζ, e₃, -, -, hC⟩
    · rw [e₁] at e₃; cases e₃
    · rw [e₁] at e₃; cases e₃; exact e₄
    · rw [e₁] at e₃; cases e₃
    · rw [e₁] at e₃; cases e₃
      obtain ⟨s₁, s₂, v', ρ, k₁, k₂, k₃, h₁, -, -⟩ := hC
      exact absurd h₁ CellUT.ownOf_ne_immOf

/-- `immFrame` transfers every view at a supported location. -/
theorem frame_transfer {W X Z R W' a' : (ResUT BoCa.Loc BoCa.Val K)} {l : Loc} {v : Val} {α : Life}
    {h : R.InStratum (TSet.single α)}
    (hX : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) R X) (hW : ResUT.CompS X Z W)
    (hW' : ResUT.CompS (ResUT.single l (CellUT.immOf (TSet.single α) v R h)) Z W')
    (hv : ResUT.Valid W) {m : Loc} (hsupp : ∀ aW, AgWT W aW → ∃ ζ, aW.get m = some ζ)
    (ha' : AgWT W' a') {ψ : CellUT Loc Val K} (e : a'.get m = some ψ) (hk : ψ.kind ≠ Kind.own) :
    ∃ aW, AgWT W aW ∧ ∃ ψ₀, aW.get m = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit := by
  obtain ⟨eW, aW, r, z, eR, σc, pc, heW, haW, hr, hrz, heR, hup, hl, hpc, hcp, hcz⟩ :=
    frame_walks hX hW hW' hv ha'
  obtain ⟨ζs, hζs⟩ := hsupp aW haW
  refine ⟨aW, haW, ?_⟩
  rcases back_view hcz e hk with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₁, e₁, k₁, w₁⟩
  · rcases back_view hcp e₁ k₁ with ⟨ψ₂, e₂, -, -⟩ | ⟨ψ₂, e₂, k₂, w₂⟩
    · obtain ⟨rfl, -⟩ := ResUT.single_get_eq_some e₂
      exact (ex_ag_disjoint hv heW haW hl hζs).elim
    · rcases back_view hpc e₂ k₂ with ⟨ψ₃, e₃, -, -⟩ | ⟨ψ₃, e₃, k₃, w₃⟩
      · obtain ⟨ζ', e'⟩ := hup m ψ₃ e₃
        exact (ex_ag_disjoint hv heW haW e' hζs).elim
      · obtain ⟨ψ₄, e₄, k₄, w₄⟩ := lift_view hrz e₃ k₃
        exact ⟨ψ₄, e₄, k₄, w₁.trans (w₂.trans (w₃.trans w₄.symm))⟩
  · obtain ⟨ψ₄, e₄, k₄, w₄⟩ := lift_view_r hrz e₁ k₁
    exact ⟨ψ₄, e₄, k₄, w₁.trans w₄.symm⟩

/-- …support is kept. -/
theorem frame_support {W X Z R W' a' : (ResUT BoCa.Loc BoCa.Val K)} {l : Loc} {v : Val} {α : Life}
    {h : R.InStratum (TSet.single α)}
    (hX : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) R X) (hW : ResUT.CompS X Z W)
    (hW' : ResUT.CompS (ResUT.single l (CellUT.immOf (TSet.single α) v R h)) Z W')
    (hv : ResUT.Valid W) {m : Loc} (hsupp : ∀ aW, AgWT W aW → ∃ ζ, aW.get m = some ζ)
    (ha' : AgWT W' a') : ∃ ζ, a'.get m = some ζ := by
  obtain ⟨eW, aW, r, z, eR, σc, pc, heW, haW, hr, hrz, heR, hup, hl, hpc, hcp, hcz⟩ :=
    frame_walks hX hW hW' hv ha'
  obtain ⟨ζs, hζs⟩ := hsupp aW haW
  rcases back_some hrz hζs with ⟨ψ₁, e₁⟩ | ⟨ψ₁, e₁⟩
  · obtain ⟨_, e₂⟩ := comp_some_r hpc e₁
    obtain ⟨_, e₃⟩ := comp_some_r hcp e₂
    exact comp_some hcz e₃
  · exact comp_some_r hcz e₁

theorem agW_of_valid {W : (ResUT BoCa.Loc BoCa.Val K)} (h : ResUT.Valid W) : ∃ a, AgWT W a := by
  obtain ⟨σ, e, a, -, ha, -⟩ := h; exact ⟨a, ha⟩

theorem Val.inj₁_inj' {a c : Val} (h : Val.inj₁ a = Val.inj₁ c) : a = c := by
  have hv := congrArg Subtype.val h
  simp only [Val.val_inj₁] at hv
  exact Subtype.ext (Expr.inj₁.inj hv)

theorem Val.inj₂_inj' {a c : Val} (h : Val.inj₂ a = Val.inj₂ c) : a = c := by
  have hv := congrArg Subtype.val h
  simp only [Val.val_inj₂] at hv
  exact Subtype.ext (Expr.inj₂.inj hv)

theorem Val.inj₁_ne_inj₂ {a c : Val} (h : Val.inj₁ a = Val.inj₂ c) : False := by
  have hv := congrArg Subtype.val h
  simp only [Val.val_inj₁, Val.val_inj₂] at hv
  exact Expr.noConfusion hv

/-- A cell of a `●`-operand reaches the composite with its kind, witness and value. -/
theorem compS_get_left' {ρ₁ ρ₂ ρ : (ResUT BoCa.Loc BoCa.Val K)} (h : ResUT.CompS ρ₁ ρ₂ ρ) {l : Loc}
    {ψ₁ : CellUT Loc Val K} (e₁ : ρ₁.get l = some ψ₁) :
    ∃ ψ, ρ.get l = some ψ ∧ ψ.kind = ψ₁.kind ∧ ψ.wit = ψ₁.wit ∧ ψ.erase = ψ₁.erase := by
  rcases ResUT.Comp.get h l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
  · rw [e₁] at f₁; cases f₁
  · rw [e₁] at f₁; cases Option.some.inj f₁; exact ⟨_, f, rfl, rfl, rfl⟩
  · rw [e₁] at f₁; cases f₁
  · rw [e₁] at f₁; cases Option.some.inj f₁
    refine ⟨χ, f, ?_, (CellUT.CompS.wit hC).1, (CellUT.CompS.erase hC).1⟩
    rw [CellUT.CompS.kind hC]
    obtain ⟨_, _, _, _, _, _, _, h₁, _, _⟩ := hC
    rw [h₁]; rfl

theorem compS_get_right' {ρ₁ ρ₂ ρ : (ResUT BoCa.Loc BoCa.Val K)} (h : ResUT.CompS ρ₁ ρ₂ ρ) {l : Loc}
    {ψ₂ : CellUT Loc Val K} (e₂ : ρ₂.get l = some ψ₂) :
    ∃ ψ, ρ.get l = some ψ ∧ ψ.kind = ψ₂.kind ∧ ψ.wit = ψ₂.wit ∧ ψ.erase = ψ₂.erase :=
  compS_get_left' (ResUT.CompS.comm h) e₂

/-- A non-`own` cell of an iterated `○` comes from a member, over the same witness. -/
theorem bigComp_back {xs : List (ResUT BoCa.Loc BoCa.Val K)} {b : (ResUT BoCa.Loc BoCa.Val K)}
    (h : BigCompT CellUT.CompatR CellUT.CompR xs b) {l : Loc} {ψ : CellUT Loc Val K}
    (e : b.get l = some ψ) (hk : ψ.kind ≠ Kind.own) :
    ∃ x ∈ xs, ∃ ψ', x.get l = some ψ' ∧ ψ'.kind ≠ Kind.own ∧ ψ.wit = ψ'.wit := by
  induction h generalizing ψ with
  | nil => rw [PMap.empty_get] at e; cases e
  | @cons σ τ ρ σs _ hc ih =>
      rcases back_view hc e hk with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₁, e₁, k₁, w₁⟩
      · exact ⟨σ, List.mem_cons_self .., ψ₁, e₁, k₁, w₁⟩
      · obtain ⟨x, hx, ψ', e', k', w'⟩ := ih e₁ k₁
        exact ⟨x, List.mem_cons_of_mem _ hx, ψ', e', k', w₁.trans w'⟩

/-- `[TR]` p. 5's `ag` row read backwards at a view.  A non-`own` cell of `ag(ρ)` at `ℓ`
comes from one of the row's three factors, over the same witness: `ρ|imm` (then `ρ(ℓ)` is
`imm`), the `mut` family `{ag(ρ′) | ρ(m) = mut(_,_,ρ′,_)}`, or the `imm` family
`{ex(ρ′)_○ ○ ag(ρ′) | ρ(m) = imm(_,_,ρ′)}`. -/
theorem agW_source {ρ σ : (ResUT BoCa.Loc BoCa.Val K)} (h : AgWT ρ σ) {l : Loc} {ψ : CellUT Loc Val K}
    (e : σ.get l = some ψ) (hk : ψ.kind ≠ Kind.own) :
    (∃ ψ₀, ρ.get l = some ψ₀ ∧ ψ₀.kind = Kind.imm ∧ ψ.wit = ψ₀.wit) ∨
    (∃ m ψm a, ρ.get m = some ψm ∧ ψm.kind = Kind.mut ∧ AgWT ψm.wit a ∧
      ∃ ψ', a.get l = some ψ' ∧ ψ'.kind ≠ Kind.own ∧ ψ.wit = ψ'.wit) ∨
    (∃ m ψm ev av p, ρ.get m = some ψm ∧ ψm.kind = Kind.imm ∧ ExRT ψm.wit ev ∧
      AgWT ψm.wit av ∧ ResUT.CompR ev av p ∧
      ∃ ψ', p.get l = some ψ' ∧ ψ'.kind ≠ Kind.own ∧ ψ.wit = ψ'.wit) := by
  cases h with
  | mk hsm hsi hwm hwi hbm hbi ha hσ =>
      rename_i a bm bi wm wi
      rcases back_view hσ e hk with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₁, e₁, k₁, w₁⟩
      · rcases back_view ha e₁ k₁ with ⟨ψ₂, e₂, -, w₂⟩ | ⟨ψ₂, e₂, k₂, w₂⟩
        · obtain ⟨e₃, k₃⟩ := ResUT.restrict_eq_some.mp e₂
          exact Or.inl ⟨ψ₂, e₃, k₃, w₁.trans w₂⟩
        · obtain ⟨x, hx, ψ', e', k', w'⟩ := bigComp_back hbm e₂ k₂
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
          obtain ⟨χ, hχ, hag⟩ := AgWitsMT.mem hwm p hp
          obtain ⟨χ', hχ', kχ'⟩ := (hsm.2 p.1).mp (List.mem_map.mpr ⟨p, hp, rfl⟩)
          rw [hχ] at hχ'; cases Option.some.inj hχ'
          exact Or.inr (Or.inl ⟨p.1, χ, p.2, hχ, kχ', hag, ψ', e', k',
            w₁.trans (w₂.trans w')⟩)
      · obtain ⟨x, hx, ψ', e', k', w'⟩ := bigComp_back hbi e₁ k₁
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        obtain ⟨χ, ev, av, hχ, hex, hag, hc⟩ := AgWitsIT.mem hwi p hp
        obtain ⟨χ', hχ', kχ'⟩ := (hsi.2 p.1).mp (List.mem_map.mpr ⟨p, hp, rfl⟩)
        rw [hχ] at hχ'; cases Option.some.inj hχ'
        exact Or.inr (Or.inr ⟨p.1, χ, ev, av, p.2, hχ, kχ', hex, hag, hc, ψ', e', k',
          w₁.trans w'⟩)

/-- Every cell of `c ∈ reb_β(σ)` is `imm`, and is `reb_β`'s image of `σ`'s cell there
(`[TR]` p. 5's three clauses): an `own` cell becomes `imm({β}, u, q/ℓ)` for a piece `q ≤ σ`
holding `ℓ`; a `mut` cell's witness is kept; an `imm` cell's witness is kept. -/
theorem reb_cell {β : Life} {σ c : (ResUT BoCa.Loc BoCa.Val K)} (hr : ResUT.Reb β σ c) {m : Loc}
    {ψ : CellUT Loc Val K} (e : c.get m = some ψ) :
    ψ.kind = Kind.imm ∧
    ((∃ u q h, σ.get m = some (CellUT.ownOf u) ∧
        ψ = CellUT.immOf (TSet.single β) u (q.del m) h ∧ ResUT.Le q σ ∧
        (∃ ζ, q.get m = some ζ)) ∨
     (∃ ζ, σ.get m = some ζ ∧ ζ.kind = Kind.mut ∧ ψ.wit = ζ.wit) ∨
     (∃ ζ, σ.get m = some ζ ∧ ζ.kind = Kind.imm ∧ ψ.wit = ζ.wit)) := by
  obtain ⟨-, π, b, hdom, hbig, hle, hbody⟩ := hr
  obtain ⟨⟨l₀, q⟩, hpm, hpl⟩ := List.mem_map.mp ((hdom.2 m).mpr ⟨_, e⟩)
  simp only at hpl
  subst hpl
  have hq := hbody l₀ q hpm
  have hmem : q ∈ π.map Prod.snd := List.mem_map.mpr ⟨_, hpm, rfl⟩
  obtain ⟨b', hb', hle'⟩ := BigCompT.leS_of_sublist (List.singleton_sublist.mpr hmem) hbig
  rw [(BigCompT.singleton_iff ResUT.compLawsS).mp hb'] at hle'
  have hqσ : ResUT.Le q σ := hle'.trans hle
  obtain ⟨ζq, hζq⟩ := hq.1
  obtain ⟨τ, hτ⟩ := hqσ
  obtain ⟨ζ, hζ⟩ := comp_some hτ hζq
  rcases CellUT.rep' ζ with ⟨u, rfl⟩ | ⟨s, v, χ, hs, rfl⟩ | ⟨b₀, _, v, χ, hb₀, P, hw, rfl⟩
  · obtain ⟨hh, he⟩ := hq.2.1 u hζ
    rw [e] at he; cases Option.some.inj he
    exact ⟨rfl, Or.inl ⟨u, q, hh, hζ, rfl, ⟨τ, hτ⟩, ζq, hζq⟩⟩
  · obtain ⟨⟨t, ht, -, he⟩, -⟩ := hq.2.2.2 s v χ hs hζ
    rw [e] at he; cases Option.some.inj he
    refine ⟨rfl, Or.inr (Or.inr ⟨_, hζ, rfl, ?_⟩)⟩
    rw [CellUT.wit_immOf, CellUT.wit_immOf]
  · obtain ⟨⟨hh, he⟩, -⟩ := hq.2.2.1 b₀ v χ hb₀ P hw hζ
    rw [e] at he; cases Option.some.inj he
    refine ⟨rfl, Or.inr (Or.inl ⟨_, hζ, rfl, ?_⟩)⟩
    rw [CellUT.wit_immOf, CellUT.wit_mutOf]

/-- The walks of an escrow `σ₀` held at `W(ℓₑ) = imm(s, v, σ₀)`: `ex(σ₀)_○ ○ ag(σ₀)` is
defined (the third factor of `ag(W)`'s row). -/
theorem escrow_walks {W σ₀ aW : (ResUT BoCa.Loc BoCa.Val K)} {le : Loc} {s : TSet} {v : Val}
    {hs : σ₀.InStratum s} (hle : W.get le = some (CellUT.immOf s v σ₀ hs))
    (haW : AgWT W aW) : ∃ e₀ a₀ p₀, ExRT σ₀ e₀ ∧ AgWT σ₀ a₀ ∧ ResUT.CompR e₀ a₀ p₀ := by
  obtain ⟨a₁, a₂, -, h₂, -⟩ := (AgWT.split (ResUT.del_compS hle)).mp haW
  obtain ⟨e₀, a₀, p₀, he₀, ha₀, hp₀, -⟩ := AgWT.single_imm_inv h₂
  exact ⟨e₀, a₀, p₀, he₀, ha₀, hp₀⟩

/-- A view of `ex(σ₀)_○ ○ ag(σ₀)` reaches `ag(W)` (`lift_part` at `t = σ₀`). -/
theorem lift_escrow {W σ₀ aW e₀ a₀ p₀ : (ResUT BoCa.Loc BoCa.Val K)} {le : Loc} {s : TSet} {v : Val}
    {hs : σ₀.InStratum s} (hle : W.get le = some (CellUT.immOf s v σ₀ hs))
    (haW : AgWT W aW) (he₀ : ExRT σ₀ e₀) (ha₀ : AgWT σ₀ a₀) (hp₀ : ResUT.CompR e₀ a₀ p₀)
    {l : Loc} {ψ : CellUT Loc Val K} (e : p₀.get l = some ψ) (hk : ψ.kind ≠ Kind.own) :
    ∃ ψ₀, aW.get l = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ₀.wit = ψ.wit :=
  lift_part hle (ResUT.Le.refl _) haW he₀ ha₀ hp₀ e hk

theorem hRR : ∀ ψ₁ ψ₂ ψ : CellUT Loc Val K, CellUT.CompR ψ₁ ψ₂ ψ → CellUT.CompatR ψ₁ ψ₂ :=
  fun _ _ ψ hc => ⟨ψ, hc⟩

/-- The `reb` step's view transfer, at every root.  At `W′ = W ● c` with
`c ∈ reb_β(σ₀)` and `σ₀` the escrow of an `imm` cell of `W`: every non-`own` cell of
`ag(W′)` either carries the witness of a non-`own` cell of `ag(W)` at the same location, or
sits at an owned cell `ℓ ↦ own(u)` of `σ₀` where `c(ℓ) = imm({β}, u, q/ℓ)` and carries
`q/ℓ`.  `reb_β`'s `mut` and `imm` clauses keep a
witness `ag(W)` already holds (`AgWT.mut_wit_le`, `AgWT.imm_wit_le`, `ExWT.wit_le`), and its
`own` clause's `q/ℓ ≤ σ₀` is `lift_part`'s. -/
theorem reb_transfer_gen {W W' c σ₀ : (ResUT BoCa.Loc BoCa.Val K)} {le : Loc} {s : TSet} {v : Val}
    {hs : σ₀.InStratum s} {β : Life}
    (hle : W.get le = some (CellUT.immOf s v σ₀ hs)) (hr : ResUT.Reb β σ₀ c)
    (hW : ResUT.CompS W c W') {a' : (ResUT BoCa.Loc BoCa.Val K)} (ha' : AgWT W' a') {l : Loc} {ψ : CellUT Loc Val K}
    (e : a'.get l = some ψ) (hk : ψ.kind ≠ Kind.own) :
    (∃ aW, AgWT W aW ∧ ∃ ψ₀, aW.get l = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit) ∨
    (∃ (u : Val) (q : (ResUT BoCa.Loc BoCa.Val K)) (h : (q.del l).InStratum (TSet.single β)),
      σ₀.get l = some (CellUT.ownOf u) ∧
      c.get l = some (CellUT.immOf (TSet.single β) u (q.del l) h) ∧ ψ.wit = q.del l) := by
  obtain ⟨aW, ac, haW, hac, hcomp⟩ := (AgWT.split hW).mp ha'
  rcases back_view hcomp e hk with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₂, e₂, k₂, w₂⟩
  · exact Or.inl ⟨aW, haW, ψ₁, e₁, k₁, w₁⟩
  obtain ⟨e₀, a₀, p₀, he₀, ha₀, hp₀⟩ := escrow_walks hle haW
  have up : ∀ ψ', p₀.get l = some ψ' → ψ'.kind ≠ Kind.own → ψ.wit = ψ'.wit →
      (∃ aW, AgWT W aW ∧ ∃ ψ₀, aW.get l = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit) :=
    fun ψ' e' k' w' => by
      obtain ⟨ψ₀, e₀', k₀, w₀⟩ := lift_escrow hle haW he₀ ha₀ hp₀ e' k'
      exact ⟨aW, haW, ψ₀, e₀', k₀, w'.trans w₀.symm⟩
  rcases agW_source hac e₂ k₂ with ⟨ψ₀, eψ₀, kψ₀, wψ₀⟩ | ⟨m, ψm, a, eψm, kψm, -⟩ |
      ⟨m, ψm, ev, av, p, eψm, kψm, hev, hav, hp, ψ', e', k', w'⟩
  · -- `c|imm` at `ℓ` itself
    obtain ⟨-, hcase⟩ := reb_cell hr eψ₀
    rcases hcase with ⟨u, q, h, hown, rfl, -, -⟩ | ⟨ζ, eζ, kζ, wζ⟩ | ⟨ζ, eζ, kζ, wζ⟩
    · exact Or.inr ⟨u, q, h, hown, eψ₀, by rw [w₂, wψ₀, CellUT.wit_immOf]⟩
    · obtain ⟨χ, eχ, -, hχ⟩ := ExRT.get_of_ne_imm he₀ eζ (by rw [kζ]; exact fun c => Kind.noConfusion c)
      obtain ⟨wχ, kχ⟩ := hχ (by rw [kζ]; exact fun c => Kind.noConfusion c)
      obtain ⟨ψ', e', k', w'⟩ := lift_view hp₀ eχ kχ
      exact Or.inl <| up ψ' e' k' (by rw [w₂, wψ₀, wζ, w', wχ])
    · obtain ⟨χ, eχ, kχ, -, wχ⟩ := AgWT.get_imm ha₀ eζ kζ
      obtain ⟨ψ', e', k', w'⟩ := lift_view_r hp₀ eχ (by rw [kχ]; exact fun c => Kind.noConfusion c)
      exact Or.inl <| up ψ' e' k' (by rw [w₂, wψ₀, wζ, w', wχ])
  · -- the `mut` family of `c`: `c` has no `mut` cell
    exact absurd (reb_cell hr eψm).1 (by rw [kψm]; exact fun c => Kind.noConfusion c)
  · -- the `imm` family of `c`: `ex(w)_○ ○ ag(w)` of one of `c`'s cells
    obtain ⟨-, hcase⟩ := reb_cell hr eψm
    rcases hcase with ⟨u, q, h, hown, rfl, hqσ, ζq, hζq⟩ | ⟨ζ, eζ, kζ, wζ⟩ | ⟨ζ, eζ, kζ, wζ⟩
    · have ht : ResUT.Le (q.del m) σ₀ := ResUT.Le.trans ⟨_, ResUT.del_compS hζq⟩ hqσ
      rw [CellUT.wit_immOf] at hev hav
      obtain ⟨ψ₀, e₀', k₀, w₀⟩ := lift_part hle ht haW hev hav hp e' k'
      exact Or.inl ⟨aW, haW, ψ₀, e₀', k₀, w₂.trans (w'.trans w₀.symm)⟩
    · obtain ⟨ev', z, hev', hz⟩ := ExWT.wit_le hRR ResUT.compLawsR he₀ eζ kζ
      obtain ⟨av', z', hav', hz'⟩ := AgWT.mut_wit_le ha₀ eζ kζ
      rw [wζ] at hev hav
      rw [ExRT.functional hev hev'] at hp
      rw [AgWT.functional hav hav'] at hp
      rcases back_view hp e' k' with ⟨ψ₃, e₃, k₃, w₃⟩ | ⟨ψ₃, e₃, k₃, w₃⟩
      · obtain ⟨ψ₄, e₄, k₄, w₄⟩ := lift_view hz e₃ k₃
        obtain ⟨ψ₅, e₅, k₅, w₅⟩ := lift_view hp₀ e₄ k₄
        exact Or.inl <| up ψ₅ e₅ k₅ (by rw [w₂, w', w₃, w₅, w₄])
      · obtain ⟨ψ₄, e₄, k₄, w₄⟩ := lift_view hz' e₃ k₃
        obtain ⟨ψ₅, e₅, k₅, w₅⟩ := lift_view_r hp₀ e₄ k₄
        exact Or.inl <| up ψ₅ e₅ k₅ (by rw [w₂, w', w₃, w₅, w₄])
    · obtain ⟨ev', av', p', z, hev', hav', hp', hz⟩ := AgWT.imm_wit_le ha₀ eζ kζ
      rw [wζ] at hev hav
      rw [ExRT.functional hev hev', AgWT.functional hav hav'] at hp
      rw [ResUT.CompR.functional hp hp'] at e'
      obtain ⟨ψ₄, e₄, k₄, w₄⟩ := lift_view hz e' k'
      obtain ⟨ψ₅, e₅, k₅, w₅⟩ := lift_view_r hp₀ e₄ k₄
      exact Or.inl <| up ψ₅ e₅ k₅ (by rw [w₂, w', w₅, w₄])

/-- An `imm` cell of a `○`-composite comes from an `imm` operand. -/
theorem imm_back {a₁ a₂ a : (ResUT BoCa.Loc BoCa.Val K)} (h : ResUT.CompR a₁ a₂ a) {l : Loc} {ψ : CellUT Loc Val K}
    (e : a.get l = some ψ) (hk : ψ.kind = Kind.imm) :
    (∃ ψ₁, a₁.get l = some ψ₁ ∧ ψ₁.kind = Kind.imm) ∨
    (∃ ψ₂, a₂.get l = some ψ₂ ∧ ψ₂.kind = Kind.imm) := by
  rcases ResUT.Comp.get h l with ⟨-, -, e'⟩ | ⟨ζ, e₁, -, e'⟩ | ⟨ζ, -, e₂, e'⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁, e₂, e', hC⟩
  · rw [e'] at e; cases e
  · rw [e'] at e; cases e; exact Or.inl ⟨_, e₁, hk⟩
  · rw [e'] at e; cases e; exact Or.inr ⟨_, e₂, hk⟩
  · rw [e'] at e; cases Option.some.inj e
    obtain ⟨s, hs, hψ⟩ := CellUT.imm_eta hk
    rcases CellUT.CompR.imm_source hC hψ with ⟨s₁, h₁, e₁'⟩ | ⟨s₂, h₂, e₂'⟩
    · exact Or.inl ⟨_, e₁, by rw [e₁']; rfl⟩
    · exact Or.inr ⟨_, e₂, by rw [e₂']; rfl⟩

theorem imm_fwd_l {a₁ a₂ a : (ResUT BoCa.Loc BoCa.Val K)} (h : ResUT.CompR a₁ a₂ a) {l : Loc} {ψ₁ : CellUT Loc Val K}
    (e : a₁.get l = some ψ₁) (hk : ψ₁.kind = Kind.imm) :
    ∃ ψ, a.get l = some ψ ∧ ψ.kind = Kind.imm := by
  obtain ⟨χ, eχ, kχ, -, -⟩ := ResUT.CompR.get_imm_left h e hk
  exact ⟨χ, eχ, kχ⟩

theorem imm_fwd_r {a₁ a₂ a : (ResUT BoCa.Loc BoCa.Val K)} (h : ResUT.CompR a₁ a₂ a) {l : Loc} {ψ₂ : CellUT Loc Val K}
    (e : a₂.get l = some ψ₂) (hk : ψ₂.kind = Kind.imm) :
    ∃ ψ, a.get l = some ψ ∧ ψ.kind = Kind.imm := by
  obtain ⟨χ, eχ, kχ, -, -⟩ := ResUT.CompR.get_imm_right h e hk
  exact ⟨χ, eχ, kχ⟩

/-- Under `immFrame` (`[TR]` 6.64), an `imm` cell of `ag(W)` stays `imm` in `ag(W′)`. -/
theorem frame_imm {W X Z R W' a' : (ResUT BoCa.Loc BoCa.Val K)} {l : Loc} {v : Val} {α : Life}
    {h : R.InStratum (TSet.single α)}
    (hX : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) R X) (hW : ResUT.CompS X Z W)
    (hW' : ResUT.CompS (ResUT.single l (CellUT.immOf (TSet.single α) v R h)) Z W')
    (hv : ResUT.Valid W) (ha' : AgWT W' a') {aW : (ResUT BoCa.Loc BoCa.Val K)} (haW : AgWT W aW) {m : Loc}
    {ψ₀ : CellUT Loc Val K} (e₀ : aW.get m = some ψ₀) (k₀ : ψ₀.kind = Kind.imm) :
    ∃ ψ, a'.get m = some ψ ∧ ψ.kind = Kind.imm := by
  obtain ⟨eW, aW', r, z, eR, σc, pc, -, haW', -, hrz, -, -, -, hpc, hcp, hcz⟩ :=
    frame_walks hX hW hW' hv ha'
  rw [AgWT.functional haW' haW] at hrz
  rcases imm_back hrz e₀ k₀ with ⟨ψ₁, e₁, k₁⟩ | ⟨ψ₁, e₁, k₁⟩
  · obtain ⟨ψ₂, e₂, k₂⟩ := imm_fwd_r hpc e₁ k₁
    obtain ⟨ψ₃, e₃, k₃⟩ := imm_fwd_r hcp e₂ k₂
    exact imm_fwd_l hcz e₃ k₃
  · exact imm_fwd_r hcz e₁ k₁

end BoCa.Fig16.Tree.Wp

end

import Support.Model.Tree.Port.Six28to29

/-!
# The printed source over the tree-stratified carrier

`[spec §62]`. `Support/Model/Surgery.lean:31-32`, `Support/Model/Surgery.lean:156-386`, read at `CellUT K`, by the printed proofs.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-- `○` at two `imm` cells over one value and one witness unions the lifetime
sets: the *"by the definition of `○` and `●`"* of `[TR]` 6.51's proof. -/
theorem CellUT.CompR.imm_union {ψ₁ ψ₂ ζ : CellUT Loc Val K} (h : CellUT.CompR ψ₁ ψ₂ ζ)
    {a b : TSet} {v : Val} {χ : ResUT Loc Val K}
    {ha : χ.InStratum a} {hb : χ.InStratum b}
    (e₁ : ψ₁ = CellUT.immOf a v χ ha) (e₂ : ψ₂ = CellUT.immOf b v χ hb) :
    ∃ h' : χ.InStratum (a ∪ b), ζ = CellUT.immOf (a ∪ b) v χ h' := by
  cases h with
  | same ψ =>
      obtain ⟨hab, -, -⟩ := CellUT.immOf_inj (e₁.symm.trans e₂)
      subst hab
      refine ⟨by rw [TSet.union_self]; exact ha, ?_⟩
      rw [e₁]
      exact CellUT.immOf_congr (TSet.union_self a).symm rfl rfl ha _
  | strict k =>
      obtain ⟨s₁, s₂, w, τ, k₁, k₂, k₃, f₁, f₂, f₃⟩ := CellUT.compS_spec _ _ k
      rw [e₁] at f₁; rw [e₂] at f₂
      obtain ⟨hs₁, hv₁, hχ₁⟩ := CellUT.immOf_inj f₁
      obtain ⟨hs₂, -, -⟩ := CellUT.immOf_inj f₂
      subst hs₁; subst hv₁; subst hχ₁; subst hs₂
      exact ⟨k₃, f₃⟩
  | mutMut p q w τ hp hq P Q hP hQ => exact absurd e₁.symm CellUT.immOf_ne_mutOf
  | mutOwn p w τ hp P hP => exact absurd e₁.symm CellUT.immOf_ne_mutOf
  | ownMut p w τ hp P hP => exact absurd e₁ CellUT.ownOf_ne_immOf
  | immOwn s w τ hh => exact absurd e₂ CellUT.ownOf_ne_immOf
  | ownImm s w τ hh => exact absurd e₁ CellUT.ownOf_ne_immOf
  | immMut s w τ hh p hp P hP => exact absurd e₂.symm CellUT.immOf_ne_mutOf
  | mutImm s w τ hh p hp P hP => exact absurd e₁.symm CellUT.immOf_ne_mutOf

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
variable {Loc Val : Type} {K : WCactus}
/-- `σ` and `K` agree away from `ℓ` when `σ = ℓ ↦ ψ ● K`. -/
theorem ResUT.compS_single_get_ne {l l' : Loc} {ψ : CellUT Loc Val K}
    {Kr σ : ResUT Loc Val K} (h : ResUT.CompS (ResUT.single l ψ) Kr σ) (hne : l' ≠ l) :
    σ.get l' = Kr.get l' := by
  rcases ResUT.Comp.get h l' with ⟨e₁, e₂, e⟩ | ⟨ζ, e₁, e₂, e⟩ | ⟨ζ, e₁, e₂, e⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁, e₂, e, -⟩
  · rw [e, e₂]
  · rw [ResUT.single_get_ne ψ hne] at e₁; exact absurd e₁ (by simp)
  · rw [e, e₂]
  · rw [ResUT.single_get_ne ψ hne] at e₁; exact absurd e₁ (by simp)

/-- At `ℓ`, `σ = ℓ ↦ ψ ● K` carries `ψ` and `K` is undefined. -/
theorem ResUT.compS_single_get_self {l : Loc} {ψ : CellUT Loc Val K}
    {Kr σ : ResUT Loc Val K} (h : ResUT.CompS (ResUT.single l ψ) Kr σ)
    (hn : Kr.get l = none) : σ.get l = some ψ := by
  rcases ResUT.Comp.get h l with ⟨e₁, -, -⟩ | ⟨ζ, e₁, -, e⟩ | ⟨ζ, -, e₂, -⟩ |
      ⟨ζ₁, ζ₂, ζ, -, e₂, -, -⟩
  · exact absurd (e₁.symm.trans (ResUT.single_get_self l ψ)) (by simp)
  · rw [e, ← ResUT.single_get_self l ψ, e₁]
  · exact absurd (hn.symm.trans e₂) (by simp)
  · exact absurd (hn.symm.trans e₂) (by simp)

/-- The `own` normal form, `[TR]` 6.39's first display, lines 2–4:

```
⦇ρ ● ℓ↦own(v) ● ρ_v⦈ = ex(ρ)_● ● ex(ℓ↦own(v))_● ● ex(ρ_v)_●
                        ● (ag(ρ) ○ ag(ℓ↦own(v)) ○ ag(ρ_v))
                     = ℓ↦own(v) ● ex(ρ)_● ● ex(ρ_v)_● ● (ag(ρ) ○ ag(ρ_v))
```

`[about ours: `[TR]` 6.39's first display, as a graph — G4]` -/
theorem ResUT.flat_own_normal {l : Loc} {v : Val} {ρ ρv ov w σ : ResUT Loc Val K}
    (hov : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) ρv ov)
    (hw : ResUT.CompS ρ ov w) (hflat : ResUT.Flat w σ) :
    ∃ e₁ e₂ EX a₁ a₂ AG K,
      ExST ρ e₁ ∧ ExST ρv e₂ ∧ ResUT.CompS e₁ e₂ EX ∧
      AgWT ρ a₁ ∧ AgWT ρv a₂ ∧ ResUT.CompR a₁ a₂ AG ∧
      ResUT.CompS EX AG K ∧
      ResUT.CompS (ResUT.single l (CellUT.ownOf v)) K σ := by
  obtain ⟨e₁, e₂', e, a₁, a₂', a, he₁, he₂', hec, ha₁, ha₂', hac, hσ⟩ :=
    (ResUT.Flat.split hw).mp hflat
  obtain ⟨f₁, f₂, hf₁, hf₂, hfc⟩ := (ExST.split hov).mp he₂'
  obtain ⟨g₁, g₂, hg₁, hg₂, hgc⟩ := (AgWT.split hov).mp ha₂'
  rw [ExST.functional hf₁ (ExWT.single_own l v)] at hfc
  rw [AgWT.functional hg₁ (AgWT.single_own l v)] at hgc
  rw [ResUT.CompR.functional hgc (ResUT.comp_empty_left g₂)] at hac
  obtain ⟨y, hy₁, hy₂⟩ :=
    (ResUT.CompS.assoc e₁ (ResUT.single l (CellUT.ownOf v)) f₂ e).mp ⟨_, hfc, hec⟩
  obtain ⟨EX, hEX, hle⟩ :=
    (ResUT.CompS.assoc (ResUT.single l (CellUT.ownOf v)) e₁ f₂ e).mpr
      ⟨y, ResUT.CompS.comm hy₁, hy₂⟩
  obtain ⟨K, hK, hKσ⟩ :=
    (ResUT.CompS.assoc (ResUT.single l (CellUT.ownOf v)) EX a σ).mpr ⟨e, hle, hσ⟩
  exact ⟨e₁, f₂, EX, a₁, g₂, a, K, he₁, hf₂, hEX, ha₁, hg₂, hac, hK, hKσ⟩

/-- `ag` at a singleton `imm` cell, forwards.
`[about ours: `ag`'s printed row evaluated at one `imm` cell]` -/
theorem AgWT.single_imm {l : Loc} {s : TSet} {v : Val} {χ p σ : ResUT Loc Val K}
    {hstr : χ.InStratum s} (hp : ResUT.FlatR χ p)
    (hσ : ResUT.CompR (ResUT.single l (CellUT.immOf s v χ hstr)) p σ) :
    AgWT (ResUT.single l (CellUT.immOf s v χ hstr)) σ := by
  obtain ⟨a, e, ha, he, hae⟩ := hp
  have hk : (CellUT.immOf s v χ hstr).kind = Kind.imm := CellUT.kind_immOf _ _ _ _
  refine G.AgW.mk (wm := []) (wi := [(l, p)])
    (a := ResUT.single l (CellUT.immOf s v χ hstr)) (bm := PMap.empty) (bi := p)
    (ResUT.sites_single_other (by rw [hk]; exact fun c => Kind.noConfusion c))
    (ResUT.sites_single_self hk) G.AgWitsM.nil ?_ G.BigComp.nil (BigCompT.single p) ?_ hσ
  · refine G.AgWitsI.cons (CellUT.immOf s v χ hstr) (ResUT.single_get_self _ _) hk e a
      ?_ ?_ (ResUT.CompR.comm hae) G.AgWitsI.nil
    · rwa [CellUT.wit_immOf]
    · rwa [CellUT.wit_immOf]
  · rw [ResUT.restrict_single_self hk]
    exact ResUT.comp_empty_right _

/-- The four walks of `ρ` and `ρ_v` are undefined at `ℓ`: `[TR]` Lemma 6.34's
*"Unfolding these, we have `ℓ ∉ dom(⦇ρ ● ρ_v⦈)`"*.
`[about ours: the step `[TR]` Lemma 6.34's proof reads off the printed `#`, at
the walks; `[TR]` Lemma 6.29's proof reads the same one]` -/
theorem ResUT.walks_none_of_hash_own {l : Loc} {v : Val}
    {ρ ρv W e a ev av : ResUT Loc Val K}
    (hW : ResUT.CompS ρv (ResUT.single l (CellUT.ownOf v)) W) (hh : ResUT.Hash ρ W)
    (he : ExST ρ e) (ha : AgWT ρ a) (hev : ExST ρv ev) (hav : AgWT ρv av) :
    e.get l = none ∧ a.get l = none ∧ ev.get l = none ∧ av.get l = none := by
  obtain ⟨-, T, hT, σT, eT, aT, hexT, hagT, hcT⟩ := hh
  obtain ⟨e₁, e₂, he₁, he₂, hec⟩ := (ExST.split hT).mp hexT
  obtain ⟨a₁, a₂, ha₁, ha₂, hac⟩ := (AgWT.split hT).mp hagT
  obtain ⟨f₁, f₂, hf₁, hf₂, hfc⟩ := (ExST.split hW).mp he₂
  obtain ⟨b₁, b₂, hb₁, hb₂, hbc⟩ := (AgWT.split hW).mp ha₂
  cases ExST.functional he₁ he
  cases AgWT.functional ha₁ ha
  cases ExST.functional hf₁ hev
  cases AgWT.functional hb₁ hav
  have hownk : (CellUT.ownOf (K := K) (Loc := Loc) v).kind ≠ Kind.imm := by simp
  have hf₂l : f₂.get l = some (CellUT.ownOf v) := by
    rw [ExST.functional hf₂ (ExWT.single_own l v)]
    exact ResUT.single_get_self _ _
  have hevl : ev.get l = none :=
    ResUT.CompatS.right_eq_none (ResUT.CompatS.symm hfc.1) hf₂l hownk
  have he₂l : e₂.get l = some (CellUT.ownOf v) := by
    have := hfc.2 l; rw [hevl, hf₂l] at this; exact this
  have hel : e.get l = none :=
    ResUT.CompatS.right_eq_none (ResUT.CompatS.symm hec.1) he₂l hownk
  have heTl : eT.get l = some (CellUT.ownOf v) := by
    have := hec.2 l; rw [hel, he₂l] at this; exact this
  have haTl : aT.get l = none :=
    ResUT.CompatS.right_eq_none hcT.1 heTl hownk
  have hal : a.get l = none := ((ResUT.Comp.eq_none_iff hac l).mp haTl).1
  have ha₂l : a₂.get l = none := ((ResUT.Comp.eq_none_iff hac l).mp haTl).2
  exact ⟨hel, hal, hevl, ((ResUT.Comp.eq_none_iff hbc l).mp ha₂l).1⟩

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-- `[TR]` Lemma 6.38 (p. 12), as a proposition.
`[as printed]` (the `●`s as graphs, G4; the conclusion's `ρ′ ● ρ⁺/ℓ` asserted to
exist) -/
def ResUT.SixThirtyEight : Prop :=
  ∀ {α : Life} {l : BoCa.Loc} {v : BoCa.Val}
    {ρ ρv ρ' ρp W ρρi ρ'ρp : ResUT BoCa.Loc BoCa.Val K}
    {hv : ρv.InStratum (TSet.single α)},
    ResUT.CompS ρv (ResUT.single l (CellUT.ownOf v)) W →
    ResUT.Hash ρ W →
    ResUT.Hash ρ' ρp →
    ρ.InStratum (TSet.single α) →
    ρ'.InStratum (TSet.single α) →
    (G.restrict CellUT.kind ρp Kind.own) = PMap.empty →
    ResUT.CompS ρ (ResUT.single l (CellUT.immOf (TSet.single α) v ρv hv)) ρρi →
    ResUT.CompS ρ' ρp ρ'ρp →
    ResUT.UpdV ρρi ρ'ρp →
    ∃ Gr, ResUT.CompS ρ' (ρp.del l) Gr ∧ ResUT.Hash Gr W

/-- `[TR]` Lemma 6.38's step 2, *"By H4 and H7"*, the half about `ρ′`:
`ℓ ∉ dom(ρ′)`.
`[about ours: the step `[TR]` Lemma 6.38's proof takes at "By H4 and H7"]` -/
theorem ResUT.six38_no_borrow_in_frame {α : Life} {l : BoCa.Loc} {v : BoCa.Val}
    {ρv ρ' ρp ρ'ρp : ResUT BoCa.Loc BoCa.Val K}
    {hv : ρv.InStratum (TSet.single α)}
    (h4 : ρ'.InStratum (TSet.single α)) (hpp : ResUT.CompS ρ' ρp ρ'ρp)
    (hcl : ρ'ρp.get l = some (CellUT.immOf (TSet.single α) v ρv hv)) :
    ρ'.get l = none := by
  classical
  have key : ∀ (s : TSet) (w : BoCa.Val) (χ : ResUT BoCa.Loc BoCa.Val K)
      (hc : χ.InStratum s),
      (CellUT.immOf s w χ hc).InStratum (TSet.single α) → α ∈ s.set → False := by
    intro s w χ hc hin hmem
    exact Cactus.lt_irrefl _ α (hin α (by simp) α hmem)
  cases hg : ρ'.get l with
  | none => rfl
  | some φ =>
      exfalso
      have hφα : φ.InStratum (TSet.single α) := h4 l φ hg
      rcases ResUT.Comp.get hpp l with ⟨e₁, -, -⟩ | ⟨ψ, e₁, -, e⟩ |
          ⟨ψ, e₁, -, -⟩ | ⟨ψ₁, ψ₂, ψ, e₁, -, e, hC⟩
      · rw [hg] at e₁; exact absurd e₁ (by simp)
      · rw [hg] at e₁
        cases Option.some.inj e₁
        have hφ : φ = CellUT.immOf (TSet.single α) v ρv hv :=
          Option.some.inj (e.symm.trans hcl)
        subst hφ
        exact key _ v ρv hv hφα (by simp)
      · rw [hg] at e₁; exact absurd e₁ (by simp)
      · rw [hg] at e₁
        cases Option.some.inj e₁
        obtain ⟨s₁, s₂, w, χ, k₁, k₂, k₃, f₁, f₂, f₃⟩ := hC
        subst f₁
        obtain ⟨hs, -, -⟩ :=
          CellUT.immOf_inj (Option.some.inj ((f₃ ▸ e).symm.trans hcl))
        obtain ⟨y, hy⟩ := s₁.ne
        have hyα : y = α := by
          have hm : y ∈ (s₁ ∪ s₂).set := Finset.mem_union_left _ hy
          rw [hs] at hm; simpa using hm
        exact key _ w χ k₁ hφα (hyα ▸ hy)

/-- `[TR]` Lemma 6.38 from its third sentence on: the printed hypotheses still in
use, what the first two sentences deliver, and the printed conclusion.
`[about ours: `[TR]` Lemma 6.38's proof from "Then in order to show G1" on]` -/
def ResUT.SixThirtyEightResidual : Prop :=
  ∀ {α : Life} {l : BoCa.Loc} {v : BoCa.Val}
    {ρ ρv ρ' ρp W ρρi ρ'ρp Gr : ResUT BoCa.Loc BoCa.Val K}
    {hv : ρv.InStratum (TSet.single α)},
    ResUT.CompS ρv (ResUT.single l (CellUT.ownOf v)) W →
    ResUT.Hash ρ W →
    ρ.InStratum (TSet.single α) →
    ρ'.InStratum (TSet.single α) →
    (G.restrict CellUT.kind ρp Kind.own) = PMap.empty →
    ResUT.CompS ρ (ResUT.single l (CellUT.immOf (TSet.single α) v ρv hv)) ρρi →
    ResUT.CompS ρ' ρp ρ'ρp →
    ResUT.UpdV ρρi ρ'ρp →
    ResUT.CompS ρ' (ρp.del l) Gr →
    ResUT.Hash Gr (ResUT.single l (CellUT.immOf (TSet.single α) v ρv hv)) →
    ResUT.CompS Gr (ResUT.single l (CellUT.immOf (TSet.single α) v ρv hv)) ρ'ρp →
    ResUT.Hash Gr W

end BoCa.Fig16.Tree

end

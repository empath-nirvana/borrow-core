import Relaxed.FrameRules
import Relaxed.Compatibility

/-!
# Relaxed — Projection

A same-lifetime projection `Imm @a (Ref A ⊗ Ref B) ⊸ Imm @a A` (`ProjSpec`, as in
`experiments/Projection`) against the relaxed typed world, and its refutation at `A = B = 1`.

In the relaxed world `FrameLife` no longer rules out a view at the frame's own lifetime, so
`Projection.no_view_at_tag`'s last step does not go through.  The refutation here uses no
typed-world invariant at all: `frame_view_excluded` is `[TR]` 6.38 (`ResU.six38`) read at a
frame whose borrow is the whole resource.  A resource `π` that the borrow `ℓ ↦ imm({α}, v, ρv)`
updates to (`↭`) holds no cell at a location `ρv` owns, because 6.38 lets the frame end
against `π`, and the frame's end puts `own` cells back at those locations.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Relaxed.Projection
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel
open BoCa.Fig16.LogRel.MutImmCell
open BoCa.Fig16.LogRel.Relaxed
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `[TR]` 6.38 at a frame whose borrow is the whole resource: if `ℓ ↦ imm({α}, v, ρv)` updates
to an own-free `π`, then `π` has no cell at any location `ρv` owns. -/
theorem frame_view_excluded {α : Life} {l m : Loc} {v u : Val} {ρv W π : WRes}
    {hv : ρv.InStratum (LSet.singleton α).join}
    (hW : ResU.CompS ρv (ResU.single l (CellU.ownOf v)) W) (hvW : ResU.Valid W)
    (hupd : ResU.UpdV (ResU.single l (CellU.immOf (LSet.singleton α) v ρv hv)) π)
    (hno : NoOwn π) (hm : ρv.get m = some (CellU.ownOf u))
    {ψ : CellU Loc Val} (hψ : π.get m = some ψ) : False := by
  have hemp : ∀ β : Life, ResU.InStratum β (PMap.empty : WRes) := fun _ l ψ e => by
    rw [PMap.empty_get] at e; cases e
  obtain ⟨G, hG, hGW⟩ := ResU.six38 (ρ := PMap.empty) (ρ' := PMap.empty) hW
    (ResU.hash_symm (ResU.hash_empty_right hvW)) (ResU.hash_symm (ResU.hash_empty_right hupd.2.2))
    (hemp α) (hemp α) hno (compS_empty_left _) (compS_empty_left _) hupd
  cases eq_of_compS_empty_left hG
  have hml : m ≠ l := by
    rintro rfl
    have := ResU.CompatS.right_eq_none hW.1 hm (by simp)
    rw [ResU.single_get_self] at this
    cases this
  have hWm : W.get m = some (CellU.ownOf u) :=
    (ResU.CompS.get_left_of_ne_imm hW hm (by simp)).2
  have hGm := ResU.CompatS.right_eq_none (ResU.CompatS.symm hGW.1) hWm (by simp)
  rw [ResU.del_get_ne _ hml, hψ] at hGm
  cases hGm

/-- The pair type whose first component is projected: `Ref 1 ⊗ Ref 1`. -/
abbrev T0 : Ty := .tensor (.ref .unit) (.ref .unit)

/-- `u`'s first component is the location `m`. -/
def FstLoc (u : Val) (m : Loc) : Prop := ∃ v₂, u = Val.pair (Val.loc m) v₂

/-- `experiments/Projection`'s `ProjSpec` at the relaxed world: from a view `ℓ` of the pair,
`proj ℓ` returns a view of the first component's contents at the same lifetime `@aδ`, and the
location it returns is the first component of the pair `ℓ` holds. -/
def ProjSpec (proj : Loc → Expr) (a : Lifetime.Life) (A B : Ty) : Prop :=
  ∀ (ls : List SRec) (δ : LSub) (ℓ : Loc) (ρ : WRes),
    vP (.imm a (.tensor (.ref A) (.ref B))) ls δ (Val.loc ℓ) ρ →
    wpTS ls (proj ℓ) (fun ls' w ρ' => vP (.imm a A) ls' δ w ρ' ∧
      ∃ m, w = Val.loc m ∧ ∀ ψ : CellU Loc Val, ρ.get ℓ = some ψ → FstLoc ψ.erase m) ρ

/-- `𝒱X⟦Ref 1 ⊗ Ref 1⟧` does not depend on the mode or on `δ`. -/
theorem t0_mode {b b' : Bool} {ls : List SRec} {δ δ' : LSub} {u : Val} {σ : WRes}
    (h : vX wpTS b T0 ls δ u σ) : vX wpTS b' T0 ls δ' u σ := h

/-- A `wpTS` run from a tagged typed world ends in one, the frame absorbing `ρ⁺`. -/
theorem run {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp} {ρ ρf fρ : WRes}
    {ps : List FrameRec} (hw : wpTS ls e Q ρ) (hf : ResU.Hash ρf ρ) (hc : ResU.CompS ρf ρ fρ)
    (hT : TW fρ ps (rsOf ls)) (htg : Tagged fρ ps ls) :
    ∃ (ρ' ρf' fρ' : WRes) (ps' : List FrameRec) (ls' : List SRec) (v : Val),
      Q ls' v ρ' ∧ ResU.Hash ρf' ρ' ∧ ResU.CompS ρf' ρ' fρ' ∧ TW fρ' ps' (rsOf ls') ∧
      Tagged fρ' ps' ls' := by
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', -, h2, -, -, h6, h7, -, -, -, -,
    hT', htg', -, -, hQ⟩ := hw ρf fρ ps hf hc hT htg
  obtain ⟨z, -, hz⟩ := compS_exch h2 h6
  have hv : ResU.Valid fρ'p := by obtain ⟨σ₁, hσ₁, -⟩ := h7; exact ⟨σ₁, hσ₁⟩
  exact ⟨ρ', z, fρ'p, ps', ls', v, hQ, ⟨hz.1, fρ'p, hz, hv⟩, hz, hT', htg'⟩

/-- The post-condition of one allocation at the empty list. -/
def AllocQ (ρ₀ : WRes) (v : Val) : List SRec → Val → WProp := fun ls w ρ =>
  ls = [] ∧ ∃ l, w = Val.loc l ∧ ResU.CompS ρ₀ (ResU.single l (CellU.ownOf v)) ρ

theorem alloc_run (ρ₀ : WRes) (v : Val) :
    wpTS [] (.app (.val (.prim .alloc)) (.val v)) (AllocQ ρ₀ v) ρ₀ :=
  wpTS_alloc [] v _ ρ₀ (fun l ρ₁ ρ₂ h₁ h₂ => by
    subst h₁; exact ⟨rfl, l, rfl, h₂⟩)

theorem vX_ref_unit {b : Bool} {ls : List SRec} {δ : LSub} (l : Loc) :
    vX wpTS b (.ref .unit) ls δ (Val.loc l) (ResU.single l (CellU.ownOf Val.unit)) :=
  ⟨l, Val.unit, PMap.empty, _, compS_empty_left _, ⟨rfl, rfl⟩, _, PMap.empty,
    ResU.comp_empty_right _, rfl, ⟨rfl, rfl⟩⟩

theorem single_own_inStratum (l : Loc) (v : Val) (β : Life) :
    (ResU.single l (CellU.ownOf v) : WRes).InStratum β := fun _ ψ e => by
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e; trivial

/-- **No same-lifetime projection, at the relaxed world.**  No expression `proj` meets
`ProjSpec` at `Imm 'x (Ref 1 ⊗ Ref 1) ⊸ Imm 'x 1`.  The configuration: three allocations from
the empty typed world (`l₂`, `l₁`, `ℓ ↦ (l₁, l₂)`), then `TW.immFrame` at `ℓ` with the frame
lifetime `α` and escrow `ρ₂ = l₂ ↦ () ● l₁ ↦ ()`, the entry of `[TR]` 6.64.  `proj ℓ` runs
from the borrow `ℓ ↦ imm({α}, (l₁, l₂), ρ₂)` read at `'x ↦ α`; its result is a cell at `l₁`,
which `frame_view_excluded` refuses. -/
theorem no_projection (proj : Loc → Expr) (x : LifeVar) (α : Life) :
    ¬ ProjSpec proj (.var x) .unit .unit := by
  intro hspec
  obtain ⟨ρ1, f1, W1, ps1, ls1, -, ⟨rfl, l2, -, hc1⟩, hf1, hW1, hT1, htg1⟩ :=
    run (alloc_run PMap.empty Val.unit) hash_empty (ResU.comp_empty_right _) TW.empty
      (fun x hx => by simp at hx)
  cases eq_of_compS_empty_left hc1
  obtain ⟨ρ2, f2, W2, ps2, ls2, -, ⟨rfl, l1, -, hc2⟩, hf2, hW2, hT2, htg2⟩ :=
    run (alloc_run _ Val.unit) hf1 hW1 hT1 htg1
  set v : Val := Val.pair (Val.loc l1) (Val.loc l2) with hvdef
  obtain ⟨ρ3, f3, W3, ps3, ls3, -, ⟨rfl, ℓ, -, hc3⟩, hf3, hW3, hT3, htg3⟩ :=
    run (alloc_run ρ2 v) hf2 hW2 hT2 htg2
  have hadm : AdmWf T0 LSub.empty := fun y hy => by simp [LFree] at hy
  have hvX : vX wpTS true T0 [] LSub.empty v ρ2 :=
    ⟨Val.loc l1, Val.loc l2, PMap.empty, ρ2, compS_empty_left ρ2, ⟨rfl, rfl⟩, _, _,
      ResU.CompS.comm hc2, vX_ref_unit l1, vX_ref_unit l2⟩
  have hm₁ : ρ2.get l1 = some (CellU.ownOf Val.unit) :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hc2) (ResU.single_get_self _ _)
      (by simp)).2
  -- `[TR]` 6.64's entry at `ℓ`: the frame record `p` and the borrowed world `W′`
  have hα : ρ2.InStratum (LSet.singleton α).join :=
    ResU.CompS.inStratum hc2 (single_own_inStratum _ _ _) (single_own_inStratum _ _ _)
  set ρi : WRes := ResU.single ℓ (CellU.immOf (LSet.singleton α) v ρ2 hα) with hρi
  have hvW3 : ResU.Valid W3 := hash_valid_comp hf3 hW3
  have hvρ3 : ResU.Valid ρ3 := (hash_valid hf3).2
  have hfi : ResU.Hash f3 ρi := ResU.six34 hc3 hf3
  obtain ⟨W', hW', hvW'⟩ := hfi.2
  set p : FrameRec := ⟨ℓ, v, ρ2, T0, LSub.empty⟩ with hpdef
  have hshape : vShape T0 LSub.empty v ρ2 := vX_vShape true T0 hvX
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hvW3
  obtain ⟨eR, heR, -, -⟩ := frame_ex (ResU.CompS.comm hc3) (ResU.CompS.comm hW3) heW
  obtain ⟨ds, hds⟩ := lineage_list (r := p) hshape hadm heR
  set ls' : List SRec := frameList p ds α [] with hls'def
  have hadd : AddAt [] ls' α := addAt_frameList p ds α []
  have hTW : TW W' (p :: ps3) (rsOf ls') := by
    rw [hls'def, rsOf_frameList]
    exact TW.immFrame T0 LSub.empty hα hT3 hadm (ResU.CompS.comm hc3) (ResU.CompS.comm hW3)
      hshape (ResU.CompS.comm hW') hvW' hds
  obtain ⟨hFLnew, -⟩ :=
    frameLife_frame T0 LSub.empty hvW3 (ResU.CompS.comm hc3) (ResU.CompS.comm hW3)
      (ResU.CompS.comm hW') hT3.inv
  have htg : Tagged W' (p :: ps3) ls' := by
    intro y hy
    simp only [hls'def, frameList, List.mem_cons, List.mem_append, List.mem_map] at hy
    rcases hy with rfl | ⟨d, hd, rfl⟩ | hy
    · exact ⟨p, List.mem_cons_self, DescR.refl p, hFLnew⟩
    · obtain ⟨q, hq, hqd⟩ := (hds d).mp hd
      exact ⟨p, List.mem_cons_self, ⟨q, hqd⟩, hFLnew⟩
    · simp at hy
  -- the borrow, read at `'x ↦ α`
  set δ' : LSub := LSub.empty.extend x α with hδ'
  have hp : p ∈ rsOf ls' := by rw [hls'def, rsOf_frameList]; exact List.mem_cons_self
  have hcoh : CohE (rsOf ls') ℓ T0 δ' :=
    ⟨T0, δ', ⟨trivial, trivial⟩, Or.inl ⟨p, hp, rfl, rfl, fun y hy => by
      rw [hpdef] at hy; simp [LFree] at hy⟩⟩
  have hv : vP (.imm (.var x) T0) ls' δ' (Val.loc ℓ) ρi := by
    refine ⟨α, find?_extend_self LSub.empty x α, ℓ, PMap.empty, ρi, compS_empty_left ρi,
      ⟨rfl, rfl, hcoh⟩, LSet.singleton α, v, ρ2, hα, [], rfl, t0_mode hvX, le_refl _,
      fun y => ⟨fun h => by simp at h, fun ⟨hy, hyα⟩ => ?_⟩⟩
    have := hadd.2 y hy (by simp)
    rw [this] at hyα
    exact absurd hyα (lt_irrefl _)
  -- `proj ℓ` runs at the frame `f₃`
  obtain ⟨ρ', ρp, fρ', fρ'p, π, w, μ, μ', ps', ls'', -, -, -, -, -, -, -, h9, hA, hB,
    -, -, -, -, hvw, m, rfl, hfst⟩ :=
    hspec ls' δ' ℓ ρi hv f3 W' (p :: ps3) hfi hW' hTW htg
  -- the location returned is `l₁`
  obtain ⟨v₂', hfst'⟩ := hfst _ (ResU.single_get_self _ _)
  have hmm : m = l1 := by
    rw [CellU.erase_immOf] at hfst'
    have := congrArg Subtype.val hfst'
    simp [hvdef, Val.pair, Val.loc] at this
    exact this.1.symm
  subst hmm
  -- the result is a cell at `l₁` in `π = ρ′ ● ρ⁺`
  obtain ⟨α', -, ℓ', ρ₁, ρ₂, h12, ⟨rfl, hwl, -⟩, s, u, σ, hσ, ls₀, rfl, -, -, -⟩ := hvw
  cases eq_of_compS_empty_left h12
  cases (Val.loc_inj.mp hwl)
  obtain ⟨ψ, eψ, -⟩ := compS_get_left' h9 (ResU.single_get_self _ _)
  have hno : NoOwn π := noOwn_compS h9 (noOwn_single_imm _ _ _ _ _) hB
  exact frame_view_excluded hc3 hvρ3 hA hno hm₁ eψ

end BoCa.Fig16.LogRel.Relaxed.Projection

end

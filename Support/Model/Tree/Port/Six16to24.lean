import Support.Model.Tree.Port.SurgeryA

/-!
# `[TR]` Lemmas 6.16–6.24 over the tree-stratified carrier

`[spec §62]`. `Paper/S6_2_NonStandardLemmas/Lemmas.lean`'s Lemmas 6.16–6.24, by the printed
proofs.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-!
## Lemma 6.16 · `[TR]` p. 8 · `proved`

> If ρ ● ⦇ρ′⦈ defined then ρ ● ρ′ defined.

**Printed proof, transcribed.** `ρ ● ⦇ρ′⦈` is defined iff `ρ` and `⦇ρ′⦈` have disjoint own-or-mut cells and `imm` cells that agree up to lifetimes.  Unravelling `⦇−⦈`, the cells of `ρ′` are a subset of those of `⦇ρ′⦈`, so the same condition holds of `ρ` and `ρ′`.

**Lean.** `BoCa.Fig16.Tree.ResUT.CompatS.of_flat`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.16 (p. 8).  `[as printed]` (G4) -/
theorem ResUT.CompatS.of_flat {ρ ρ' f : ResUT Loc Val K} (hf : ResUT.Flat ρ' f)
    (h : ResUT.CompatS ρ f) : ResUT.CompatS ρ ρ' := by
  intro l ψ ψ' e e'
  obtain ⟨χ, hχ, hk, hv, hw⟩ := hf.get e'
  obtain ⟨k₁, k₂, m₁, m₂⟩ := CellUT.compatS_iff.mp (h l ψ χ e hχ)
  exact CellUT.compatS_iff.mpr ⟨k₁, hk.symm.trans k₂, m₁.trans hv, m₂.trans hw⟩

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-!
## Lemma 6.42 · `[TR]` p. 15 · `proved`

> If ℓ ↦ mut(−, −, −, −) ▸◂ ρ, then ℓ ∉ ρ.

**Printed proof, transcribed.** By definition.

**Lean.** `BoCa.Fig16.Tree.ResUT.compatS_single_mut`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.42 (p. 15).  `[as printed]` -/
theorem ResUT.compatS_single_mut {l : Loc} {b : TSet} [Fact (K.Anti b)] {v : Val}
    {σ : ResUT Loc Val K} {hs : σ.InStratum b} {P : Val → SPropST Loc Val K b}
    {hw : P v ⟨σ, hs⟩} {ρ : ResUT Loc Val K}
    (h : ResUT.CompatS (ResUT.single l (CellUT.mutOf b v σ hs P hw)) ρ) :
    ρ.get l = none :=
  ResUT.compatS_single_not_imm (by simp) h

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-!
## Lemma 6.17 · `[TR]` p. 8 · `proved`

> If ρ # ℓ ↦ mut(α, v, ρ_v, P̂) then ρ ▸◂ ρ_v ● ℓ ↦ own(v)

**Printed proof, transcribed.** Let `ρ_o = ℓ ↦ own(v)` and `ρ_m = ℓ ↦ mut(α, v, ρ_v, P̂)`.  By Lemma 6.9 it is enough that `ρ ● ρ_v ● ρ_o` is defined.  `✓(ρ ● ρ_m)` makes `⦇ρ ● ρ_m⦈ = ex(ρ)_● ● (ρ_m ● ex(ρ_v)_●) ● (ag(ρ) ○ ag(ρ_v))` defined; ignoring `ex(ρ)_●` and `ag(ρ)`, `ρ_m ● ⦇ρ_v⦈` is defined, so `ℓ ∉ dom⦇ρ_v⦈`, so `ρ_o ● ⦇ρ_v⦈` is defined, so `ρ_o ● ρ_v` is defined by Lemma 6.16.  Definedness of `ag(ρ) ○ ag(ρ_v)` makes `ρ` and `ρ_v` agree on `imm` cells up to lifetimes, hence `ρ` and `ρ_o ● ρ_v` (`ρ_o` has no `imm` cell); definedness of `ex(ρ)_● ● (ρ_m ● ex(ρ_v)_●)` makes `ρ` and `ρ_m ● ρ_v` have disjoint own-or-mut cells, hence `ρ` and `ρ_o ● ρ_v` (`ρ_o` and `ρ_m` have the same own-or-mut cells).  Together, `ρ` and `ρ_o ● ρ_v` are composable.

**Lean.** `BoCa.Fig16.Tree.ResUT.compatS_of_hash_mut`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.17 (p. 8).  `[as printed]` (G4) -/
theorem ResUT.compatS_of_hash_mut {ρ ρv w : ResUT Loc Val K} {l : Loc} {α : TSet} [Fact (K.Anti α)] {v : Val}
    {hs : ρv.InStratum α} {P : Val → SPropST Loc Val K α} {hP : P v ⟨ρv, hs⟩}
    (h : ResUT.Hash ρ (ResUT.single l (CellUT.mutOf α v ρv hs P hP)))
    (hw : ResUT.CompS ρv (ResUT.single l (CellUT.ownOf v)) w) : ResUT.CompatS ρ w := by
  obtain ⟨hcompat, ρ', hρ', hval⟩ := h
  have hkey : ResUT.CompatS ρ ρv :=
    ResUT.CompatS.of_valid_mut (ResUT.single_get_self _ _) (by simp) (by simp) hρ' hval
  have hnone : ρ.get l = none := ResUT.compatS_single_mut hcompat.symm
  intro l' ψ χ e f
  rcases hw.get l' with ⟨-, -, g⟩ | ⟨χ', g₁, -, g⟩ | ⟨χ', -, g₂, g⟩ |
      ⟨u₁, u₂, u, -, g₂, -, -⟩
  · rw [g] at f; exact absurd f (by simp)
  · rw [g] at f; cases Option.some.inj f; exact hkey l' _ _ e g₁
  · obtain ⟨rfl, -⟩ := ResUT.single_get_eq_some g₂
    rw [hnone] at e; exact absurd e (by simp)
  · obtain ⟨rfl, -⟩ := ResUT.single_get_eq_some g₂
    rw [hnone] at e; exact absurd e (by simp)

end BoCa.Fig16.Tree
/-!
## Lemma 6.18 · `[TR]` p. 8 · `proved`

> If ρ₁ ▸◂ ρ₂ then ex(ρ₁ ● ρ₂)_● and ex(ρ₁)_● ● ex(ρ₂)_● are Kleene-equal (the left-hand side is defined iff the right-hand side is, and in case both are defined they are equal).

**Printed proof, transcribed.** `ρ₁ ▸◂ ρ₂` makes the own-or-mut cells of `ρ₁` and `ρ₂` disjoint.  Writing `ρ₁₂ = ρ₁ ● ρ₂`, the Kleene equalities
`ex(ρ₁₂)_● = ρ₁₂∣own ● ρ₁₂∣mut ● ⨀_{mut(_,_,ρ′,_)∈ρ₁₂} ex(ρ′)_●`
`= (ρ₁∣own ● ρ₂∣own) ● (ρ₁∣mut ● ρ₂∣mut) ● (⨀_{mut(_,_,ρ′,_)∈ρ₁} ex(ρ′)_●) ● (⨀_{mut(_,_,ρ′,_)∈ρ₂} ex(ρ′)_●)`
`= (ρ₁∣own ● ρ₁∣mut ● ⨀_{…∈ρ₁} ex(ρ′)_●) ● (ρ₂∣own ● ρ₂∣mut ● ⨀_{…∈ρ₂} ex(ρ′)_●) = ex(ρ₁)_● ● ex(ρ₂)_●`.

**Lean.** `BoCa.Fig16.Tree.ExST.split`, tag `[as printed]` — declared in `Paper/S6_1_StandardLemmas/Lemmas.lean`.
-/

namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-!
## Lemma 6.19 · `[TR]` p. 9 · `proved`

> If ⦇ρ⦈_○ defined then ⦇ρ⦈_○ and ⦇ρ⦈_○ ○ ⦇ρ⦈_○ are Kleene-equal.

**Printed proof, transcribed.** By induction on `ρ`, mutual with the statement that `ag(ρ)` and `ag(ρ) ○ ag(ρ)` are Kleene-equal.

**Lean.** `BoCa.Fig16.Tree.ResUT.flatR_idem`, tag `[as printed]`.

**Note.** The `FlatR` hypothesis is unused; `Tree.ResUT.flatR_single_own` inhabits it.
-/
/-- `[TR]` Lemma 6.19 (p. 9).  `[as printed]` -/
theorem ResUT.flatR_idem {ρ σ : ResUT Loc Val K} (_ : ResUT.FlatR ρ σ) :
    ResUT.CompR σ σ σ ∧ ∀ τ, ResUT.CompR σ σ τ → τ = σ :=
  ⟨ResUT.compR_self σ, fun _ hτ => ResUT.CompR.functional hτ (ResUT.compR_self σ)⟩

end BoCa.Fig16.Tree
/-!
## Lemma 6.20 · `[TR]` p. 9 · `proved`

> If ρ₁ ▸◂ ρ₂ then ag(ρ₁ ● ρ₂) and ag(ρ₁) ○ ag(ρ₂) are Kleene-equal.

**Printed proof, transcribed.** `ρ₁ ▸◂ ρ₂` makes the `mut` cells disjoint and the `imm` cells agree up to lifetimes.  With `ρ₁₂ = ρ₁ ● ρ₂`, `ag(ρ₁₂) = ρ₁₂∣imm ○ ◯_{mut(_,_,ρ′,_)∈ρ₁₂} ag(ρ′) ○ ◯_{imm(_,_,ρ′)∈ρ₁₂} ⦇ρ′⦈_○ = (ρ₁∣imm ○ ρ₂∣imm) ○ (◯_{mut∈ρ₁} ag(ρ′) ○ ◯_{mut∈ρ₂} ag(ρ′)) ○ ρ_ag`.  The big composite `ρ_ag` has one component per `imm` cell of `ρ₁₂`, and those are the union up to lifetimes of the `imm` cells of `ρ₁` and of `ρ₂`, so by inclusion–exclusion `ρ_ag = ◯_{ρ₁∖ρ₂} ○ ◯_{ρ₂∖ρ₁} ○ ◯_{ρ₁∩ρ₂}`; by Lemma 6.19 the shared block equals itself composed with itself, so `ρ_ag = ◯_{imm∈ρ₁} ⦇ρ′⦈_○ ○ ◯_{imm∈ρ₂} ⦇ρ′⦈_○`.  Regrouping, `ag(ρ₁ ● ρ₂) = (ρ₁∣imm ○ ◯_{mut∈ρ₁} ag(ρ′) ○ ◯_{imm∈ρ₁} ⦇ρ′⦈_○) ○ (the same for ρ₂) = ag(ρ₁) ○ ag(ρ₂)`.

**Lean.** `BoCa.Fig16.Tree.AgWT.split`, tag `[as printed]` — declared in `Paper/S6_1_StandardLemmas/Lemmas.lean`.
-/

namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-!
## Lemma 6.41 · `[TR]` p. 15 · `proved`

> If ℓ ↦ own(−) ▸◂ ρ, then ℓ ∉ ρ.

**Printed proof, transcribed.** By definition.

**Lean.** `BoCa.Fig16.Tree.ResUT.compatS_single_own`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.41 (p. 15).  `[as printed]` -/
theorem ResUT.compatS_single_own {l : Loc} {v : Val} {ρ : ResUT Loc Val K}
    (h : ResUT.CompatS (ResUT.single l (CellUT.ownOf v)) ρ) : ρ.get l = none :=
  ResUT.compatS_single_not_imm (by simp) h

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
variable {Loc Val : Type} {K : WCactus}
/-!
## Lemma 6.21 · `[TR]` p. 10 · `proved`

> If ρ # ρ_v ● ℓ ↦ own(v) then ρ ▸◂ ℓ ↦ mut(α, v, ρ_v, P̂)

**Printed proof, transcribed.** The hypothesis makes `ρ ● ρ_v ● (ℓ ↦ own(v))` defined, which implies `ℓ ∉ dom(ρ)`, which implies `ρ ▸◂ ℓ ↦ mut(α, v, ρ_v, P̂)`.

**Lean.** `BoCa.Fig16.Tree.ResUT.six21`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.21 (p. 10).  `[as printed]` -/
theorem ResUT.six21 {l : Loc} {b : TSet} [Fact (K.Anti b)] {v : Val} {ρ ρv W : ResUT Loc Val K}
    {hstr : ResUT.InStratum b ρv} {P : Val → SPropST Loc Val K b} {hw : P v ⟨ρv, hstr⟩}
    (hW : ResUT.CompS ρv (ResUT.single l (CellUT.ownOf v)) W) (h : ResUT.Hash ρ W) :
    ResUT.CompatS ρ (ResUT.single l (CellUT.mutOf b v ρv hstr P hw)) := by
  have hρvl : ρv.get l = none := ResUT.compatS_single_own (ResUT.CompatS.symm hW.1)
  have hWl : W.get l = some (CellUT.ownOf v) := by
    rw [ResUT.Comp.get_of_left_none hW hρvl]; exact ResUT.single_get_self _ _
  have hρl : ρ.get l = none :=
    ResUT.CompatS.right_eq_none (ResUT.CompatS.symm h.1) hWl (by simp)
  refine ResUT.Compat.of_disjoint (fun x => ?_)
  by_cases hx : x = l
  · exact Or.inl (hx ▸ hρl)
  · exact Or.inr (ResUT.single_get_ne _ hx)

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
variable {Loc Val : Type} {K : WCactus}
/-!
## Lemma 6.22 · `[TR]` p. 10 · `proved`

> If ρ # ℓ ↦ mut(α, v, ρ_v, P̂) then ρ # ρ_v ● ℓ ↦ own(v)

**Printed proof, transcribed.** Let `ρ_o = ℓ ↦ own(v)`, `ρ_m = ℓ ↦ mut(α, v, ρ_v, P̂)`.  The hypothesis gives `✓(ρ ● ρ_m)`, i.e. `ρ_hyp ≔ ex(ρ)_● ● ex(ρ_v)_● ● ρ_m ● (ag(ρ) ○ ag(ρ_v))` is defined.  `ρ ▸◂ ρ_v ● ρ_o` is Lemma 6.17, so it remains to show `✓(ρ ● ρ_v ● ρ_o)`, i.e. that `ρ_goal ≔ ex(ρ ● ρ_v)_● ● ρ_o ● ag(ρ ● ρ_v)` is defined.  By Lemma 6.17 `ρ ● ρ_v` is defined, so by Lemmas 6.18 and 6.20 `ρ_goal` is defined iff `(ex(ρ)_● ● ex(ρ_v)_●) ● ρ_o ● (ag(ρ) ○ ag(ρ_v))` is.  Since `ρ_o` contains a single `own` cell, that composite is defined iff the same composite with `ρ_m` for `ρ_o` is, which is `ρ_hyp`.

**Lean.** `BoCa.Fig16.Tree.ResUT.six22`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.22 (p. 10).  `[as printed]` -/
theorem ResUT.six22 {l : Loc} {b : TSet} [Fact (K.Anti b)] {v : Val} {ρ ρv W : ResUT Loc Val K}
    {hstr : ResUT.InStratum b ρv} {P : Val → SPropST Loc Val K b} {hw : P v ⟨ρv, hstr⟩}
    (hW : ResUT.CompS ρv (ResUT.single l (CellUT.ownOf v)) W)
    (h : ResUT.Hash ρ (ResUT.single l (CellUT.mutOf b v ρv hstr P hw))) :
    ResUT.Hash ρ W := by
  classical
  have hmk : (CellUT.mutOf b v ρv hstr P hw).kind ≠ Kind.imm := by
    rw [CellUT.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hcompat : ResUT.CompatS ρ W := ResUT.compatS_of_hash_mut h hW
  obtain ⟨σ, hσ⟩ := (ResUT.compS_defined_iff ρ W).mpr hcompat
  refine ⟨hcompat, σ, hσ, ?_⟩
  obtain ⟨-, σm, hσm, hvm⟩ := h
  obtain ⟨F, hF⟩ := hvm
  obtain ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hF'⟩ :=
    (ResUT.Flat.split hσm).mp hF
  obtain ⟨ev, hev, hcev⟩ := ExWT.single_mut_inv he₂
  have havv : AgWT ρv a₂ := AgWT.single_mut_inv ha₂
  have hevl : ev.get l = none := ResUT.compatS_single_mut hcev.1
  obtain ⟨eW, hceW⟩ := (ResUT.compS_defined_iff ev (ResUT.single l (CellUT.ownOf v))).mpr
    (ResUT.Compat.of_disjoint (fun x => by
      by_cases hx : x = l
      · exact Or.inl (hx ▸ hevl)
      · exact Or.inr (ResUT.single_get_ne _ hx)))
  have hEW : ExST W eW := (ExST.split hW).mpr ⟨ev, _, hev, ExWT.single_own l v, hceW⟩
  have hAW : AgWT W a₂ :=
    (AgWT.split hW).mpr ⟨a₂, _, havv, AgWT.single_own l v, ResUT.comp_empty_right a₂⟩
  have he₂l : e₂.get l = some (CellUT.mutOf b v ρv hstr P hw) := by
    rw [ResUT.Comp.get_of_right_none hcev hevl]; exact ResUT.single_get_self _ _
  have hoff : ∀ x, x ≠ l → eW.get x = e₂.get x := by
    intro x hx
    rw [ResUT.Comp.get_of_right_none hceW (ResUT.single_get_ne _ hx),
      ResUT.Comp.get_of_left_none hcev (ResUT.single_get_ne _ hx)]
  obtain ⟨e', hce'⟩ := (ResUT.compS_defined_iff e₁ eW).mpr
    (ResUT.CompatS.symm (ResUT.compatS_congr_of_excl hoff he₂l hmk
      (ResUT.CompatS.symm hec.1)))
  have hoffe : ∀ x, x ≠ l → e'.get x = e.get x :=
    ResUT.compS_agree_off_right hec hce' hoff
  have he₁l : e₁.get l = none :=
    ResUT.CompatS.right_eq_none (ResUT.CompatS.symm hec.1) he₂l hmk
  have hel : e.get l = some (CellUT.mutOf b v ρv hstr P hw) := by
    rw [ResUT.Comp.get_of_left_none hec he₁l]; exact he₂l
  obtain ⟨G, hG⟩ := (ResUT.compS_defined_iff e' a).mpr
    (ResUT.compatS_congr_of_excl hoffe hel hmk hF'.1)
  exact ⟨G, (ResUT.Flat.split hσ).mpr
    ⟨e₁, eW, e', a₁, a₂, a, he₁, hEW, hce', ha₁, hAW, hac, hG⟩⟩

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
variable {Loc Val : Type} {K : WCactus}
/-!
## Lemma 6.23 · `[TR]` p. 10 · `proved`

> If ρ # ρ_v ● ℓ ↦ own(v) then ρ # ℓ ↦ mut(α, v, ρ_v, P̂)

**Printed proof, transcribed.** Analogous to Lemma 6.22.  `ρ ▸◂ ρ_m` is Lemma 6.21, so it remains to show that `ρ_goal ≔ ex(ρ)_● ● ex(ρ_v)_● ● ρ_m ● (ag(ρ) ○ ag(ρ_v))` is defined given `ρ_hyp ≔ ex(ρ ● ρ_v)_● ● ρ_o ● ag(ρ ● ρ_v)`.  The assumption makes `ρ ● ρ_v` defined, so by Lemmas 6.18 and 6.20 `ρ_hyp`'s definedness is that of `ex(ρ)_● ● ex(ρ_v)_● ● ρ_o ● (ag(ρ) ○ ag(ρ_v))`; since `ρ_o` contains a single `own` cell, replacing it by `ρ_m` preserves definedness, which is `ρ_goal`.

**Lean.** `BoCa.Fig16.Tree.ResUT.six23`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.23 (p. 10).  `[as printed]` -/
theorem ResUT.six23 {l : Loc} {b : TSet} [Fact (K.Anti b)] {v : Val} {ρ ρv W : ResUT Loc Val K}
    {hstr : ResUT.InStratum b ρv} {P : Val → SPropST Loc Val K b} {hw : P v ⟨ρv, hstr⟩}
    (hW : ResUT.CompS ρv (ResUT.single l (CellUT.ownOf v)) W) (h : ResUT.Hash ρ W) :
    ResUT.Hash ρ (ResUT.single l (CellUT.mutOf b v ρv hstr P hw)) := by
  classical
  have hok : (CellUT.ownOf (K := K) (Loc := Loc) v).kind ≠ Kind.imm := by simp
  have hcompat : ResUT.CompatS ρ (ResUT.single l (CellUT.mutOf b v ρv hstr P hw)) :=
    ResUT.six21 hW h
  obtain ⟨σ, hσ⟩ :=
    (ResUT.compS_defined_iff ρ (ResUT.single l (CellUT.mutOf b v ρv hstr P hw))).mpr hcompat
  refine ⟨hcompat, σ, hσ, ?_⟩
  obtain ⟨-, σW, hσW, hvW⟩ := h
  obtain ⟨F, hF⟩ := hvW
  obtain ⟨e₁, eW, e, a₁, aW, a, he₁, heW, hec, ha₁, haW, hac, hF'⟩ :=
    (ResUT.Flat.split hσW).mp hF
  obtain ⟨ev, eo, hev, heo, hceW⟩ := (ExST.split hW).mp heW
  obtain ⟨av, ao, hav, hao, hcaW⟩ := (AgWT.split hW).mp haW
  rw [ExST.functional heo (ExWT.single_own l v)] at hceW
  rw [AgWT.functional hao (AgWT.single_own l v)] at hcaW
  obtain rfl : aW = av := ResUT.CompR.functional hcaW (ResUT.comp_empty_right av)
  have hevl : ev.get l = none :=
    ResUT.compatS_single_own (ResUT.CompatS.symm hceW.1)
  obtain ⟨e₂, hce₂⟩ :=
    (ResUT.compS_defined_iff (ResUT.single l (CellUT.mutOf b v ρv hstr P hw)) ev).mpr
      (ResUT.Compat.of_disjoint (fun x => by
        by_cases hx : x = l
        · exact Or.inr (hx ▸ hevl)
        · exact Or.inl (ResUT.single_get_ne _ hx)))
  have hE₂ : ExST (ResUT.single l (CellUT.mutOf b v ρv hstr P hw)) e₂ :=
    ExWT.single_mut hev hce₂
  have hA₂ : AgWT (ResUT.single l (CellUT.mutOf b v ρv hstr P hw)) aW :=
    AgWT.single_mut hav
  have heWl : eW.get l = some (CellUT.ownOf v) := by
    rw [ResUT.Comp.get_of_left_none hceW hevl]; exact ResUT.single_get_self _ _
  have hoff : ∀ x, x ≠ l → e₂.get x = eW.get x := by
    intro x hx
    rw [ResUT.Comp.get_of_left_none hce₂ (ResUT.single_get_ne _ hx),
      ResUT.Comp.get_of_right_none hceW (ResUT.single_get_ne _ hx)]
  obtain ⟨e', hce'⟩ := (ResUT.compS_defined_iff e₁ e₂).mpr
    (ResUT.CompatS.symm (ResUT.compatS_congr_of_excl hoff heWl hok
      (ResUT.CompatS.symm hec.1)))
  have hoffe : ∀ x, x ≠ l → e'.get x = e.get x :=
    ResUT.compS_agree_off_right hec hce' hoff
  have he₁l : e₁.get l = none :=
    ResUT.CompatS.right_eq_none (ResUT.CompatS.symm hec.1) heWl hok
  have hel : e.get l = some (CellUT.ownOf v) := by
    rw [ResUT.Comp.get_of_left_none hec he₁l]; exact heWl
  obtain ⟨G, hG⟩ := (ResUT.compS_defined_iff e' a).mpr
    (ResUT.compatS_congr_of_excl hoffe hel hok hF'.1)
  exact ⟨G, (ResUT.Flat.split hσ).mpr
    ⟨e₁, e₂, e', a₁, aW, a, he₁, hE₂, hce', ha₁, hA₂, hac, hG⟩⟩

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
variable {Loc Val : Type} {K : WCactus}
/-!
## Lemma 6.24 · `[TR]` p. 10 · `proved`

> ρ # ℓ ↦ mut(α, v, ρ_v, P̂) iff ρ # ρ_v ● ℓ ↦ own(v)

**Printed proof, transcribed.** Combine Lemmas 6.22 and 6.23.

**Lean.** `BoCa.Fig16.Tree.ResUT.six24`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.24 (p. 10).  `[as printed]` -/
theorem ResUT.six24 {l : Loc} {b : TSet} [Fact (K.Anti b)] {v : Val} {ρ ρv W : ResUT Loc Val K}
    {hstr : ResUT.InStratum b ρv} {P : Val → SPropST Loc Val K b} {hw : P v ⟨ρv, hstr⟩}
    (hW : ResUT.CompS ρv (ResUT.single l (CellUT.ownOf v)) W) :
    ResUT.Hash ρ (ResUT.single l (CellUT.mutOf b v ρv hstr P hw)) ↔ ResUT.Hash ρ W :=
  ⟨fun h => ResUT.six22 hW h, fun h => ResUT.six23 hW h⟩

end BoCa.Fig16.Tree

end

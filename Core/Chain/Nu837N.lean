import Core.Chain.Rules834N
import Core.NuRel

/-!
# `νX. C` at `SemJN`: the unrolling, `nuIn`, `nuOut`  `[spec §7, §62]`

`docs/new-core/scope-831-interface.md` §12 (F9). `cN (νX. C)` is Core's greatest fixed point
(`Core/NuRel.lean`) at the chain's signature: a candidate below one unfolding of the observation
tree (`cBN`), the leaves read by `vNX` with `X` at the candidate. Here, Core's `cC_nu_iff`:

* `vNX_inst_occ`, `vNX_inst_poly`: `vNX` at the reading `vN S` of `X` is `vN` at `A[S/X]`
  (Core's `vCE_nuEnv`, `vC_inst_envS`), where `X` does not occur and at a polynomial `A`;
* `cBN_unroll`: one unfolding at `𝒞⟦νX. C⟧` is `𝒞⟦C[U(νX. C)/X]⟧` (Core's `cB_unroll`), the
  candidate at `δ₀` and the tree at `δ`, agreeing on the free variables of `νX. C`;
* `cN_nu_iff`: `𝒞⟦νX. C⟧ = 𝒞⟦C[U(νX. C)/X]⟧` at a positive `C`;
* `nuIn_compatN`, `nuOut_compatN` (Core's `nuIn_compatX`, `nuOut_compatX`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

mutual
/-- **Where `X` does not occur, `vNX` is `vN` at the closed type** (Core's `vCE_subst` at an
environment whose variable does not occur). -/
theorem vNX_inst_occ (S : VTy) (P : LocTy → Nat → Val → WRes → Prop) :
    ∀ (A : VTy), ¬ A.Occ 0 → ∀ δ, vNX (ℍ := ℍ) S P A δ = vN (ℍ := ℍ) (VTy.inst S A) δ
  | .unit, _, _ => rfl
  | .zero, _, _ => rfl
  | .unk, _, _ => rfl
  | .int _, _, _ => rfl
  | .opq _, _, _ => rfl
  | .thunk _, _, _ => rfl
  | .mu _, _, _ => rfl
  | .tvar 0, h, _ => absurd rfl h
  | .tvar (_ + 1), _, _ => rfl
  | .tensor A B, h, δ => by
      have h₁ := vNX_inst_occ S P A (fun h' => h (.inl h')) δ
      have h₂ := vNX_inst_occ S P B (fun h' => h (.inr h')) δ
      simp only [VTy.inst] at h₁ h₂ ⊢
      funext Θ n v ρ; simp only [vNX, vN, VTy.subst, h₁, h₂]
  | .sum A B, h, δ => by
      have h₁ := vNX_inst_occ S P A (fun h' => h (.inl h')) δ
      have h₂ := vNX_inst_occ S P B (fun h' => h (.inr h')) δ
      simp only [VTy.inst] at h₁ h₂ ⊢
      funext Θ n v ρ; simp only [vNX, vN, VTy.subst, h₁, h₂]
  | .ref A, h, δ => by
      have h₁ := vNX_inst_occ S P A h δ
      simp only [VTy.inst] at h₁ ⊢
      funext Θ n v ρ; simp only [vNX, vN, VTy.subst, VTy.inst, h₁]
  | .box _ A, h, δ => by
      have h₁ := vNX_inst_occ S P A h δ
      simp only [VTy.inst] at h₁ ⊢
      funext Θ n v ρ; simp only [vNX, vN, VTy.subst, VTy.inst, h₁]
  | .bang A, h, δ => by
      have h₁ := vNX_inst_occ S P A h δ
      simp only [VTy.inst] at h₁ ⊢
      funext Θ n v ρ; simp only [vNX, vN, VTy.subst, VTy.inst, h₁]
  | .fam A, h, δ => by
      have h₁ := vNX_inst_occ S P A h δ
      simp only [VTy.inst] at h₁ ⊢
      funext Θ n v ρ; simp only [vNX, vN, VTy.subst, VTy.inst, h₁]
  | .mut _ A, h, δ => by
      have h₁ := vNX_inst_occ S P A h δ
      simp only [VTy.inst] at h₁ ⊢
      funext Θ n v ρ; simp only [vNX, vN, VTy.subst, VTy.inst, h₁]
  | .imm _ A, h, δ => by
      have h₁ := vOX_inst_occ S P A h δ
      simp only [VTy.inst] at h₁ ⊢
      funext Θ n v ρ; simp only [vNX, vN, VTy.subst, VTy.inst, h₁]
  termination_by structural x => x
/-- The observable view where `X` does not occur. -/
theorem vOX_inst_occ (S : VTy) (P : LocTy → Nat → Val → WRes → Prop) :
    ∀ (A : VTy), ¬ A.Occ 0 → ∀ δ, vOX (ℍ := ℍ) S P A δ = vO (ℍ := ℍ) (VTy.inst S A) δ
  | .unit, _, _ => rfl
  | .zero, _, _ => rfl
  | .unk, _, _ => rfl
  | .int _, _, _ => rfl
  | .opq _, _, _ => rfl
  | .thunk _, _, _ => rfl
  | .mu _, _, _ => rfl
  | .tvar 0, h, _ => absurd rfl h
  | .tvar (_ + 1), _, _ => rfl
  | .tensor A B, h, δ => by
      have h₁ := vOX_inst_occ S P A (fun h' => h (.inl h')) δ
      have h₂ := vOX_inst_occ S P B (fun h' => h (.inr h')) δ
      simp only [VTy.inst] at h₁ h₂ ⊢
      funext Θ n v ρ; simp only [vOX, vO, VTy.subst, h₁, h₂]
  | .sum A B, h, δ => by
      have h₁ := vOX_inst_occ S P A (fun h' => h (.inl h')) δ
      have h₂ := vOX_inst_occ S P B (fun h' => h (.inr h')) δ
      simp only [VTy.inst] at h₁ h₂ ⊢
      funext Θ n v ρ; simp only [vOX, vO, VTy.subst, h₁, h₂]
  | .ref A, h, δ => by
      have h₁ := vOX_inst_occ S P A h δ
      simp only [VTy.inst] at h₁ ⊢
      funext Θ n v ρ; simp only [vOX, vO, VTy.subst, VTy.inst, h₁]
  | .box _ A, h, δ => by
      have h₁ := vOX_inst_occ S P A h δ
      simp only [VTy.inst] at h₁ ⊢
      funext Θ n v ρ; simp only [vOX, vO, VTy.subst, VTy.inst, h₁]
  | .bang A, h, δ => by
      have h₁ := vNX_inst_occ S P A h δ
      simp only [VTy.inst] at h₁ ⊢
      funext Θ n v ρ; simp only [vOX, vO, VTy.subst, VTy.inst, h₁]
  | .fam A, h, δ => by
      have h₁ := vOX_inst_occ S P A h δ
      simp only [VTy.inst] at h₁ ⊢
      funext Θ n v ρ; simp only [vOX, vO, VTy.subst, VTy.inst, h₁]
  | .mut _ A, h, δ => by
      have h₁ := vNX_inst_occ S P A h δ
      simp only [VTy.inst] at h₁ ⊢
      funext Θ n v ρ; simp only [vOX, vO, VTy.subst, VTy.inst, h₁]
  | .imm _ A, h, δ => by
      have h₁ := vOX_inst_occ S P A h δ
      simp only [VTy.inst] at h₁ ⊢
      funext Θ n v ρ; simp only [vOX, vO, VTy.subst, VTy.inst, h₁]
  termination_by structural x => x
end

/-- **At a polynomial type, `vNX` with `X` read as `𝒱⟦S⟧` is `𝒱⟦A[S/X]⟧`** (Core's
`vC_inst_envS`, `vCE_nuEnv`). -/
theorem vNX_inst_poly (S : VTy) (δ : LSub) :
    ∀ {A : VTy}, A.Poly → vNX (ℍ := ℍ) S (vN (ℍ := ℍ) S δ) A δ = vN (ℍ := ℍ) (VTy.inst S A) δ
  | .tensor A B, h => by
      have h₁ := vNX_inst_poly S δ (A := A) h.1
      have h₂ := vNX_inst_poly S δ (A := B) h.2
      simp only [VTy.inst] at h₁ h₂ ⊢
      funext Θ n v ρ; simp only [vNX, vN, VTy.subst, h₁, h₂]
  | .sum A B, h => by
      have h₁ := vNX_inst_poly S δ (A := A) h.1
      have h₂ := vNX_inst_poly S δ (A := B) h.2
      simp only [VTy.inst] at h₁ h₂ ⊢
      funext Θ n v ρ; simp only [vNX, vN, VTy.subst, h₁, h₂]
  | .box _ A, h => by
      have h₁ := vNX_inst_poly S δ (A := A) h
      simp only [VTy.inst] at h₁ ⊢
      funext Θ n v ρ; simp only [vNX, vN, VTy.subst, VTy.inst, h₁]
  | .tvar 0, _ => rfl
  | .tvar (_ + 1), _ => rfl
  | .unit, h | .zero, h | .unk, h | .int _, h | .opq _, h | .thunk _, h | .mu _, h | .ref _, h
  | .imm _ _, h | .mut _ _, h | .bang _, h | .fam _, h => vNX_inst_occ S _ _ h δ

/-- The answer of an effectful observation at `X` read as `𝒱⟦S⟧` is the unrolled row's answer
(Core's `effRet_instT_ans`). -/
theorem retNX_inst (S : VTy) (δ : LSub) :
    ∀ {D : CTy}, D.EffLeaf → retNX (ℍ := ℍ) S (vN (ℍ := ℍ) S δ) D δ = retN (ℍ := ℍ) (D.instT S) δ
  | .ret A, h => by
      have h₁ := vNX_inst_poly S δ (A := A) h
      funext Θ n v ρ; simp only [retNX, retN, CTy.instT, h₁]
  | .eff _ _ _ _ _ _ _ D, h => by
      have h₁ := retNX_inst S δ (D := D) h.2.2
      funext Θ n v ρ; simp only [retNX, retN, CTy.instT, h₁]

/-- The table of a row's layers does not read `X` (Core's `effTab_instT`): the operation types
are closed. -/
theorem tabN_instT (S : VTy) : ∀ (D : CTy) (δ : LSub),
    tabN (ℍ := ℍ) (D.instT S) δ = tabN (ℍ := ℍ) D δ
  | .eff m i q A B fin rc D, δ => by
      have h₁ := tabN_instT S D δ
      funext Θ c; simp only [CTy.instT, tabN, h₁]
  | .ret _, _ | .amp _ _, _ | .arr _ _, _ | .top, _ | .all _ _ _, _ | .nu _, _ => by
      funext Θ c; simp only [CTy.instT, tabN]

/-- `U X` at `𝒞⟦νX. C⟧δ₀` is `𝒱⟦U(νX. C)⟧δ`, at a `δ` agreeing with `δ₀` on `νX. C`. -/
theorem thunkRN_nuCand (C : CTy) {δ₀ δ : LSub} (hag : ∀ y, CFree y C → δ₀.find? y = δ.find? y) :
    thunkRN (nuCand (ℍ := ℍ) C δ₀) = vN (ℍ := ℍ) (.thunk (.nu C)) δ := by
  have h := cN_congr (ℍ := ℍ) (.nu C) (δ := δ₀) (δ' := δ) hag
  funext Θ n v ρ
  simp only [thunkRN, nuCand, vN, h]
  rfl

/-- **One unfolding at `𝒞⟦νX. C⟧` is `𝒞⟦C[U(νX. C)/X]⟧`** (Core's `cB_unroll`), the candidate at
`δ₀` and the tree read at `δ`, agreeing on the free variables of `νX. C`. Under a `∀'x` leaf the
tree is read at `δ[x ↦ α]`, which still agrees with `δ₀` on `νX. C` because `'x` is not free in
`C`. -/
theorem cBN_unroll (C : CTy) (δ₀ : LSub) : ∀ {D : CTy}, D.NuLeaf →
    (∀ x, D.LeafBinds x → ¬ CFree x C) → ∀ (δ : LSub),
    (∀ y, CFree y C → δ₀.find? y = δ.find? y) →
    cBN (ℍ := ℍ) (.thunk (.nu C)) (nuCand (ℍ := ℍ) C δ₀) D δ =
      cN (ℍ := ℍ) (D.instT (.thunk (.nu C))) δ
  | .ret A, hA, _, δ, hag => by
      have hP := thunkRN_nuCand (ℍ := ℍ) C hag
      have h₁ := vNX_inst_poly (ℍ := ℍ) (.thunk (.nu C)) δ (A := A) hA
      funext Θ c n ls e ρ; simp only [cBN, cN, CTy.instT, hP, h₁]
  | .amp D₁ D₂, hD, hfr, δ, hag => by
      have h₁ := cBN_unroll C δ₀ hD.1 (fun x hx => hfr x (Or.inl hx)) δ hag
      have h₂ := cBN_unroll C δ₀ hD.2 (fun x hx => hfr x (Or.inr hx)) δ hag
      funext Θ c n ls e ρ; simp only [cBN, cN, CTy.instT, h₁, h₂]
  | .eff m i q A B fin rc D, hD, _, δ, hag => by
      have hP := thunkRN_nuCand (ℍ := ℍ) C hag
      have h₁ := retNX_inst (ℍ := ℍ) (.thunk (.nu C)) δ (D := D) hD.2.2
      have h₂ := tabN_instT (ℍ := ℍ) (.thunk (.nu C)) D δ
      funext Θ c n ls e ρ; simp only [cBN, cN, CTy.instT, hP, h₁, h₂]
  | .arr A D, hD, hfr, δ, hag => by
      have h₁ := cBN_unroll C δ₀ (D := D) hD.2 hfr δ hag
      funext Θ c n ls e ρ; simp only [cBN, cN, CTy.instT, h₁]
  | .all x b D, hD, hfr, δ, hag => by
      have hag' : ∀ α, ∀ y, CFree y C → δ₀.find? y = (δ.extend x α).find? y := by
        intro α y hy
        have hxy : x ≠ y := fun h => hfr x (Or.inl rfl) (h ▸ hy)
        exact (hag y hy).trans (BoCa.Fig16.LogRel.find?_extend_ne δ α hxy).symm
      have h₁ : ∀ α : Life, cBN (ℍ := ℍ) (.thunk (.nu C)) (nuCand (ℍ := ℍ) C δ₀) D (δ.extend x α) =
          cN (ℍ := ℍ) (D.instT (.thunk (.nu C))) (δ.extend x α) := fun α =>
        cBN_unroll C δ₀ (D := D) hD (fun y hy => hfr y (Or.inr hy)) (δ.extend x α) (hag' α)
      funext Θ c n ls e ρ; simp only [cBN, cN, CTy.instT, h₁]
  | .top, hD, _, _, _ | .nu _, hD, _, _, _ => hD.elim

/-- **`νX. C` is its unrolling**: `𝒞⟦νX. C⟧ = 𝒞⟦C[U(νX. C)/X]⟧` at a positive `C` (Core's
`cC_nu_iff`). -/
theorem cN_nu_iff {C : CTy} (hC : C.NuOk) (δ : LSub) (Θ : LocTy) (c : Loc → Option Life)
    (n : Nat) (ls : List SRec) (e : Expr) (ρ : WRes) :
    cN (ℍ := ℍ) (.nu C) δ Θ c n ls e ρ ↔ cN (ℍ := ℍ) C.unroll δ Θ c n ls e ρ := by
  rw [cN_nu_unfold hC.1, cBN_unroll C δ hC.1.nuLeaf hC.2 δ (fun _ _ => rfl)]

/-- **`nuIn` at `SemJN`** (Core's `nuIn_compatX`): a computation of `C[U(νX. C)/X]` is one of
`νX. C`. -/
theorem nuIn_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {C : CTy} (hC : C.NuOk)
    (h : SemJN (ℍ := ℍ) Δ Γ e (.comp C.unroll)) : SemJN (ℍ := ℍ) Δ Γ e (.comp (.nu C)) :=
  fun δ γ Θ c n ls ρ hδ hΘ hc hlw hg =>
    (cN_nu_iff hC δ Θ c n ls _ ρ).mpr (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)

/-- **`nuOut` at `SemJN`** (Core's `nuOut_compatX`): a computation of `νX. C` is one of
`C[U(νX. C)/X]`. -/
theorem nuOut_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {C : CTy} (hC : C.NuOk)
    (h : SemJN (ℍ := ℍ) Δ Γ e (.comp (.nu C))) : SemJN (ℍ := ℍ) Δ Γ e (.comp C.unroll) :=
  fun δ γ Θ c n ls ρ hδ hΘ hc hlw hg =>
    (cN_nu_iff hC δ Θ c n ls _ ρ).mp (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end

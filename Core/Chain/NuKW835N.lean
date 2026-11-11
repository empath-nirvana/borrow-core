import Core.Chain.RulesKW835N
import Core.Chain.ThenKW835N

/-!
# `νX. C` at `SemJN`: the unrolling, `nuIn`, `nuOut`, `unfold`  `[spec §7, §62]`

`docs/new-core/scope-831-interface.md` §12, `docs/new-core/scope-835-tables.md` §10.12. Core's `ν`
rules (`Core/NuRel.lean`, `Core/Nu.lean`) at the relation at `KW`, step for step. `cN (νX. C)` is
Core's greatest fixed point at the chain's signature: a candidate below one unfolding of the
observation tree (`cBN`), the leaves read by `vNX` with `X` at the candidate.

* `vNX_inst_occ`, `vNX_inst_poly`, `retNX_inst`, `tabN_instT`, `cBN_unroll`, `cN_nu_iff`: Core's
  `cC_nu_iff`; a row's table does not read `X`, at every world.
* `nuIn_compatN`, `nuOut_compatN` (Core's `nuIn_compatX`, `nuOut_compatX`).
* `cBNP_step` (Core's `cB_step`): `F` and `F_Σ` at every floor, by `erwpK_ret_det` and
  `cBNP_eff_det`.
* `node_okP` (Core's `node_ok`), at every `U X` reading `P` the step's states map into: the leaf
  runs `c ()` then maps its answer. At `F_Σ` the run stops
  at the row's table, so the map is bound in by `erwpK_bind_leI` at the worlds whose location
  typing is `OK` (`tabN_downI_OK`, `tabN_ctxClosed_OK`), up to the step's index; the answer is
  mapped at the world it is posted at. `node_okN` is its instance at the candidate.
* `unfoldN_compatN` (Core's `unfold_compatX`): coinduction with the candidate `candNN`.
* `doneLoop_cBN`, `clLoop_cBN`: the `done b` and `closed r` cases of Core's `candR_post`, at one
  unfolding of `Loop_Σ B R` at every candidate (`cBN_effOf`, `vNX_rename`).
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
open BoCa.BoLo (Heap Kont Head)

/-- **`A[S/X]` is `A` at the environment `X ↦ 𝒱⟦S⟧`** (Core's `vC_inst_envS`), in both modes:
Core's substitution law (`vBN_subst`) at the empty environment. -/
theorem vBN_inst_env (S A : VTy) (δ : LSub) (b : Bool) :
    vBN (ℍ := ℍ) none b (VTy.inst S A) δ =
      vBN (ℍ := ℍ) (some (VTy.scons ⟨S, fun b => vBN (ℍ := ℍ) none b S δ⟩ (tEnvN none))) b A δ := by
  rw [vBN_some none, VTy.inst, vBN_subst]
  congr 2
  funext n
  cases n with
  | zero =>
      refine TEntN.ext' (VTy.subst_id _) ?_
      funext b
      show vBN (ℍ := ℍ) (some (tEnvN none)) b S δ = vBN (ℍ := ℍ) none b S δ
      rw [← vBN_some]
  | succ n =>
      refine TEntN.ext' rfl ?_
      funext b; cases b <;> rfl

/-- **Where `X` does not occur, `vNX` is `vN` at the closed type** (Core's `vCE_subst` at an
environment whose variable does not occur). -/
theorem vNX_inst_occ (S : VTy) (P : LocTy → Nat → Val → WRes → Prop) :
    ∀ (A : VTy), ¬ A.Occ 0 → ∀ δ, vNX (ℍ := ℍ) S P A δ = vN (ℍ := ℍ) (VTy.inst S A) δ :=
  fun A h δ => (congrFun (vBN_congr_occ A _ _ (fun n hn => by
    cases n with
    | zero => exact absurd hn h
    | succ n => rfl) true) δ).trans (vBN_inst_env S A δ true).symm

/-- The observable view where `X` does not occur. -/
theorem vOX_inst_occ (S : VTy) (P : LocTy → Nat → Val → WRes → Prop) :
    ∀ (A : VTy), ¬ A.Occ 0 → ∀ δ, vOX (ℍ := ℍ) S P A δ = vO (ℍ := ℍ) (VTy.inst S A) δ :=
  fun A h δ => (congrFun (vBN_congr_occ A _ _ (fun n hn => by
    cases n with
    | zero => exact absurd hn h
    | succ n => rfl) false) δ).trans (vBN_inst_env S A δ false).symm

/-- **At a polynomial type, `vNX` with `X` read as `𝒱⟦S⟧` is `𝒱⟦A[S/X]⟧`** (Core's
`vC_inst_envS`, `vCE_nuEnv`). -/
theorem vNX_inst_poly (S : VTy) (δ : LSub) :
    ∀ {A : VTy}, A.Poly → vNX (ℍ := ℍ) S (vN (ℍ := ℍ) S δ) A δ = vN (ℍ := ℍ) (VTy.inst S A) δ
  | .tensor A B, h => by
      have h₁ := vNX_inst_poly S δ (A := A) h.1
      have h₂ := vNX_inst_poly S δ (A := B) h.2
      simp only [VTy.inst] at h₁ h₂ ⊢
      funext Θ n v ρ; simp only [vNE, VTy.subst, h₁, h₂]
  | .sum A B, h => by
      have h₁ := vNX_inst_poly S δ (A := A) h.1
      have h₂ := vNX_inst_poly S δ (A := B) h.2
      simp only [VTy.inst] at h₁ h₂ ⊢
      funext Θ n v ρ; simp only [vNE, VTy.subst, h₁, h₂]
  | .box _ A, h => by
      have h₁ := vNX_inst_poly S δ (A := A) h
      simp only [VTy.inst] at h₁ ⊢
      funext Θ n v ρ; simp only [vNE, VTy.subst, h₁]
  | .tvar 0, _ => rfl
  | .tvar (_ + 1), _ => rfl
  | .unit, h | .zero, h | .unk, h | .int _, h | .opq _, h | .thunk _, h | .code _ _ _, h | .mu _, h | .ref _, h
  | .imm _ _, h | .mut _ _, h | .bang _, h | .fam _, h => vNX_inst_occ S _ _ h δ

/-- The answer of an effectful observation at `X` read as `𝒱⟦S⟧` is the unrolled row's answer
(Core's `effRet_instT_ans`). -/
theorem retNX_inst (S : VTy) (δ : LSub) :
    ∀ {D : CTy}, D.EffLeaf → retNX (ℍ := ℍ) (nuEnvN S (vN (ℍ := ℍ) S δ)) D δ = retN (ℍ := ℍ) (D.instT S) δ
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
      funext x; simp only [CTy.instT, tabN, h₁]
  | .ret _, _ | .amp _ _, _ | .arr _ _, _ | .top, _ | .all _ _ _, _ | .nuSys _ _ _, _ => by
      funext x; simp only [CTy.instT, tabN]

/-- `U X` at `𝒞⟦νX. C⟧δ₀` is `𝒱⟦U(νX. C)⟧δ`, at a `δ` agreeing with `δ₀` on `νX. C`. -/
theorem thunkRN_nuCand (C : CTy) {δ₀ δ : LSub} (hag : ∀ y, CFree y C → δ₀.find? y = δ.find? y) :
    thunkRN (nuCand (ℍ := ℍ) C δ₀) = vN (ℍ := ℍ) (.thunk (.nu C)) δ := by
  have h := cN_congr (ℍ := ℍ) (.nu C) (δ := δ₀) (δ' := δ) hag
  funext Θ n v ρ
  simp only [thunkRN, nuCand, vNE, h]
  rfl

/-- **One unfolding with `U X` read at `𝒱⟦T⟧` is `𝒞⟦C[T/X]⟧`** (Core's `cB_unroll`): `P` is `𝒱⟦T⟧δ`
at every `δ` agreeing with `δ₀` on the variables `F`, and the tree is read at such a `δ`. Under a
`∀'x` leaf the tree is read at `δ[x ↦ α]`, which still agrees with `δ₀` on `F` because `'x` is not
in `F`. -/
theorem cBNP_unroll (T : VTy) (P : LocTy → Nat → Val → WRes → Prop) (F : LifeVar → Prop)
    (δ₀ : LSub) (hP : ∀ δ : LSub, (∀ y, F y → δ₀.find? y = δ.find? y) → P = vN (ℍ := ℍ) T δ) :
    ∀ {D : CTy}, D.NuLeaf → (∀ x, D.LeafBinds x → ¬ F x) → ∀ (δ : LSub),
    (∀ y, F y → δ₀.find? y = δ.find? y) →
    cBNP (ℍ := ℍ) (nuEnvN T P) D δ = cN (ℍ := ℍ) (D.instT T) δ
  | .ret A, hA, _, δ, hag => by
      have hP' := hP δ hag
      have h₁ := vNX_inst_poly (ℍ := ℍ) T δ (A := A) hA
      funext Θ c n ls e ρ; simp only [cBNP, cN, CTy.instT, hP', h₁]
  | .amp D₁ D₂, hD, hfr, δ, hag => by
      have h₁ := cBNP_unroll T P F δ₀ hP hD.1 (fun x hx => hfr x (Or.inl hx)) δ hag
      have h₂ := cBNP_unroll T P F δ₀ hP hD.2 (fun x hx => hfr x (Or.inr hx)) δ hag
      funext Θ c n ls e ρ; simp only [cBNP, cN, CTy.instT, h₁, h₂]
  | .eff m i q A B fin rc D, hD, _, δ, hag => by
      have hP' := hP δ hag
      have h₁ := retNX_inst (ℍ := ℍ) T δ (D := D) hD.2.2
      have h₂ := tabN_instT (ℍ := ℍ) T D δ
      funext Θ c n ls e ρ; simp only [cBNP, cN, CTy.instT, hP', h₁, h₂]
  | .arr A D, hD, hfr, δ, hag => by
      have h₁ := cBNP_unroll T P F δ₀ hP (D := D) hD.2 hfr δ hag
      funext Θ c n ls e ρ; simp only [cBNP, cN, CTy.instT, h₁]
  | .all x b D, hD, hfr, δ, hag => by
      have hag' : ∀ α, ∀ y, F y → δ₀.find? y = (δ.extend x α).find? y := by
        intro α y hy
        have hxy : x ≠ y := fun h => hfr x (Or.inl rfl) (h ▸ hy)
        exact (hag y hy).trans (BoCa.Fig16.LogRel.find?_extend_ne δ α hxy).symm
      have h₁ : ∀ α : Life, cBNP (ℍ := ℍ) (nuEnvN T P) D (δ.extend x α) =
          cN (ℍ := ℍ) (D.instT T) (δ.extend x α) := fun α =>
        cBNP_unroll T P F δ₀ hP (D := D) hD (fun y hy => hfr y (Or.inr hy)) (δ.extend x α) (hag' α)
      funext Θ c n ls e ρ; simp only [cBNP, cN, CTy.instT, h₁]
  | .top, hD, _, _, _ | .nuSys _ _ _, hD, _, _, _ => hD.elim

/-- **One unfolding at `𝒞⟦νX. C⟧` is `𝒞⟦C[U(νX. C)/X]⟧`** (Core's `cB_unroll`): `cBNP_unroll` at
`U X` read at the candidate `𝒞⟦νX. C⟧δ₀` (`thunkRN_nuCand`), the tree read at `δ` agreeing on the
free variables of `νX. C`. -/
theorem cBN_unroll (C : CTy) (δ₀ : LSub) {D : CTy} (hD : D.NuLeaf)
    (hfr : ∀ x, D.LeafBinds x → ¬ CFree x C) (δ : LSub)
    (hag : ∀ y, CFree y C → δ₀.find? y = δ.find? y) :
    cBN (ℍ := ℍ) (.thunk (.nu C)) (nuCand (ℍ := ℍ) C δ₀) D δ =
      cN (ℍ := ℍ) (D.instT (.thunk (.nu C))) δ :=
  cBNP_unroll _ _ (fun y => CFree y C) δ₀ (fun _ h => thunkRN_nuCand C h) hD hfr δ hag

/-- **`νX. C` is its unrolling**: `𝒞⟦νX. C⟧ = 𝒞⟦C[U(νX. C)/X]⟧` at a positive `C` (Core's
`cC_nu_iff`). -/
theorem cN_nu_iff {C : CTy} (hC : C.NuOk) (δ : LSub) (Θ : LocTy) (c : Loc → Option Life)
    (n : Nat) (ls : List SRec) (e : Expr) (ρ : WRes) :
    cN (ℍ := ℍ) (.nu C) δ Θ c n ls e ρ ↔ cN (ℍ := ℍ) C.unroll δ Θ c n ls e ρ := by
  rw [cN_nu_unfold hC.1, cBN_unroll C δ hC.1.nuLeaf hC.2 δ (fun _ _ => rfl)]

/-! ### A system: the simultaneous unrolling  `[spec §79]` -/

/-- **A polynomial leaf does not read its variables' types** (Core's `vCE_polyN_ty`). -/
theorem vNE_polyN_ty (n : Nat) (η₁ η₂ : Nat → TEntN) (hP : ∀ k, (η₁ k).P = (η₂ k).P)
    (hT : ∀ k, n ≤ k → (η₁ k).ty = (η₂ k).ty) :
    ∀ {A : VTy}, A.PolyN n → vNE (ℍ := ℍ) (some η₁) A = vNE (ℍ := ℍ) (some η₂) A
  | .tensor A B, h => by
      have h₁ := vNE_polyN_ty n η₁ η₂ hP hT (A := A) h.1
      have h₂ := vNE_polyN_ty n η₁ η₂ hP hT (A := B) h.2
      funext δ Θ k v ρ; simp only [vNE, h₁, h₂]
  | .sum A B, h => by
      have h₁ := vNE_polyN_ty n η₁ η₂ hP hT (A := A) h.1
      have h₂ := vNE_polyN_ty n η₁ η₂ hP hT (A := B) h.2
      funext δ Θ k v ρ; simp only [vNE, h₁, h₂]
  | .box _ A, h => by
      have h₁ := vNE_polyN_ty n η₁ η₂ hP hT (A := A) h
      funext δ Θ k v ρ; simp only [vNE, h₁]
  | .tvar k, _ => by funext δ Θ j v ρ; simp only [vNE, tEnvPN, hP]
  | .unit, h | .zero, h | .unk, h | .int _, h | .opq _, h | .thunk _, h | .code _ _ _, h | .mu _, h
  | .ref _, h | .imm _ _, h | .mut _ _, h | .bang _, h | .fam _, h =>
      vBN_congr_occ _ η₁ η₂ (fun k hk =>
        TEntN.ext' (hT k (Nat.le_of_not_lt fun hl => h k hl hk)) (hP k)) true

/-- `U Xⱼ` at the relation's tuple at `δ₀` is `𝒱⟦U νⱼ⟧δ`, at a `δ` agreeing on the system. -/
theorem thunkRN_nuSysCand {m : Nat} (Cs : CTy) (j : Nat) {δ₀ δ : LSub}
    (hag : ∀ y, CFree y Cs → δ₀.find? y = δ.find? y) :
    thunkRN (nuSysCand (ℍ := ℍ) m Cs δ₀ j) = vN (ℍ := ℍ) (.thunk (.nuSys (m + 1) j Cs)) δ := by
  have h := cN_congr (ℍ := ℍ) (.nuSys (m + 1) j Cs) (δ := δ₀) (δ' := δ) hag
  funext Θ n v ρ
  simp only [thunkRN, nuSysCand, vNE, h]
  rfl

/-- **At a polynomial leaf, the relation's tuple is the simultaneous substitution of
`U ν₀, …, U νₘ₊₁`** (Core's `vCE_nuEnvS_at`). -/
theorem vNE_nuEnvNS_at {m : Nat} (Cs : CTy) {δ₀ δ : LSub}
    (hag : ∀ y, CFree y Cs → δ₀.find? y = δ.find? y) {A : VTy} (hA : A.PolyN (m + 2)) :
    vNE (ℍ := ℍ) (nuEnvNS (m + 1) (nuSysCand m Cs δ₀)) A δ
      = vN (ℍ := ℍ) (A.subst (VTy.substL (CTy.sysThunks (m + 1) Cs))) δ := by
  show _ = vBN (ℍ := ℍ) none true _ δ
  rw [vBN_some none, vBN_subst]
  show vNE (ℍ := ℍ) (some (nuEntS (m + 1) _)) A δ = vNE (ℍ := ℍ) (some (substEnvN _ _ δ)) A δ
  rw [vNE_polyN_ty (m + 2) _ _ (fun k => ?_) (fun k hk => ?_) hA]
  · simp only [substEnvN, sysThunks_getD]
    unfold nuEntS
    split
    · funext b
      cases b with
      | false => rfl
      | true =>
          show thunkRN (nuSysCand m Cs δ₀ k) = vBN (ℍ := ℍ) (some (tEnvN none)) true _ δ
          rw [← vBN_some, thunkRN_nuSysCand Cs k hag]
          rfl
    · funext b; cases b <;> rfl
  · simp only [substEnvN, sysThunks_getD, nuEntS, show ¬ k ≤ m + 1 by omega, if_false]
    simp [tEnvN, VTy.subst]

theorem tabN_instTL (Ss : List VTy) : ∀ (D : CTy) (δ : LSub),
    tabN (ℍ := ℍ) (D.instTL Ss) δ = tabN (ℍ := ℍ) D δ
  | .eff m i q A B fin rc D, δ => by
      have h₁ := tabN_instTL Ss D δ
      funext x; simp only [CTy.instTL, tabN, h₁]
  | .ret _, _ | .amp _ _, _ | .arr _ _, _ | .top, _ | .all _ _ _, _ | .nuSys _ _ _, _ => by
      funext x; simp only [CTy.instTL, tabN]

theorem retNX_unrollS {m : Nat} (Cs : CTy) {δ₀ δ : LSub}
    (hag : ∀ y, CFree y Cs → δ₀.find? y = δ.find? y) : ∀ {D : CTy}, D.EffLeafS (m + 2) →
    retNX (ℍ := ℍ) (nuEnvNS (m + 1) (nuSysCand m Cs δ₀)) D δ
      = retN (ℍ := ℍ) (D.instTL (CTy.sysThunks (m + 1) Cs)) δ
  | .ret A, h => by
      funext Θ n v ρ; simp only [retNX, retN, CTy.instTL, vNE_nuEnvNS_at Cs hag h]
  | .eff _ _ _ _ _ _ _ D, h => by
      have h₁ := retNX_unrollS Cs hag (D := D) h.2.2
      funext Θ n v ρ; simp only [retNX, retN, CTy.instTL, h₁]

/-- **One unfolding at the relation's tuple is `𝒞⟦·⟧` at the simultaneous unrolling** (Core's
`cB_unrollS`), the tree read at `δ` agreeing with `δ₀` on the system; under a `∀'x` leaf at
`δ[x ↦ α]`, which still agrees because `'x` is free in no body. -/
theorem cBNP_unrollS {m : Nat} (Cs : CTy) (δ₀ : LSub) : ∀ {D : CTy}, D.NuLeafS (m + 2) →
    (∀ x, D.LeafBinds x → ¬ CFree x Cs) → ∀ (δ : LSub),
    (∀ y, CFree y Cs → δ₀.find? y = δ.find? y) →
    cBNP (ℍ := ℍ) (nuEnvNS (m + 1) (nuSysCand m Cs δ₀)) D δ
      = cN (ℍ := ℍ) (D.instTL (CTy.sysThunks (m + 1) Cs)) δ
  | .ret A, hA, _, δ, hag => by
      funext Θ c n ls e ρ; simp only [cBNP, cN, CTy.instTL, vNE_nuEnvNS_at Cs hag hA]
  | .amp D₁ D₂, hD, hfr, δ, hag => by
      have h₁ := cBNP_unrollS Cs δ₀ hD.1 (fun x hx => hfr x (Or.inl hx)) δ hag
      have h₂ := cBNP_unrollS Cs δ₀ hD.2 (fun x hx => hfr x (Or.inr hx)) δ hag
      funext Θ c n ls e ρ; simp only [cBNP, cN, CTy.instTL, h₁, h₂]
  | .eff nm i q A B fin rc D, hD, _, δ, hag => by
      have h₁ := retNX_unrollS Cs hag (D := D) hD.2.2
      have h₂ := tabN_instTL (CTy.sysThunks (m + 1) Cs) D δ
      funext Θ c n ls e ρ; simp only [cBNP, cN, CTy.instTL, h₁, h₂]
  | .arr A D, hD, hfr, δ, hag => by
      have h₁ := cBNP_unrollS Cs δ₀ (D := D) hD.2 hfr δ hag
      funext Θ c n ls e ρ; simp only [cBNP, cN, CTy.instTL, h₁]
  | .all x b D, hD, hfr, δ, hag => by
      have hag' : ∀ α, ∀ y, CFree y Cs → δ₀.find? y = (δ.extend x α).find? y := by
        intro α y hy
        have hxy : x ≠ y := fun h => hfr x (Or.inl rfl) (h ▸ hy)
        exact (hag y hy).trans (BoCa.Fig16.LogRel.find?_extend_ne δ α hxy).symm
      have h₁ : ∀ α : Life, cBNP (ℍ := ℍ) (nuEnvNS (m + 1) (nuSysCand m Cs δ₀)) D (δ.extend x α) =
          cN (ℍ := ℍ) (D.instTL (CTy.sysThunks (m + 1) Cs)) (δ.extend x α) := fun α =>
        cBNP_unrollS Cs δ₀ (D := D) hD (fun y hy => hfr y (Or.inr hy)) (δ.extend x α) (hag' α)
      funext Θ c n ls e ρ; simp only [cBNP, cN, CTy.instTL, h₁]
  | .top, hD, _, _, _ | .nuSys _ _ _, hD, _, _, _ => hD.elim

/-- **`νᵢ` is its simultaneous unrolling** at the chain (Core's `cC_nuS_iff`).  `[spec §79]` -/
theorem cN_nuS_iff {m i : Nat} {Cs : CTy} (hC : Cs.SysOk (m + 1)) (hi : i ≤ m + 1) (δ : LSub)
    (Θ : LocTy) (c : Loc → Option Life) (n : Nat) (ls : List SRec) (e : Expr) (ρ : WRes) :
    cN (ℍ := ℍ) (.nuSys (m + 1) i Cs) δ Θ c n ls e ρ ↔
      cN (ℍ := ℍ) (CTy.unrollS (m + 1) i Cs) δ Θ c n ls e ρ := by
  rw [cN_nuS_unfold hC.1 hi]
  show _ ↔ cN (ℍ := ℍ) ((Cs.body (m + 1) i).instTL _) δ Θ c n ls e ρ
  rw [cBNP_unrollS Cs δ (hC.1.body i hi) (fun x hx => hC.2 x (CTy.leafBinds_body hi hx)) δ
    (fun _ _ => rfl)]

/-- **`nuIn` at `SemJN`** (Core's `nuIn_compatX`): a computation of `C[U(νX. C)/X]` is one of
`νX. C`. -/
theorem nuIn_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} :
    ∀ {m i : Nat} {C : CTy}, C.SysOkAt m i → SemJN (ℍ := ℍ) Δ Γ e (.comp (CTy.unrollS m i C)) →
      SemJN (ℍ := ℍ) Δ Γ e (.comp (.nuSys m i C))
  | 0, 0, _, hC, h => fun δ γ Θ c n ls ρ hδ hΘ hc hlw hg =>
      (cN_nu_iff hC δ Θ c n ls _ ρ).mpr (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)
  | 0, _ + 1, _, hC, _ => hC.elim
  | _ + 1, _, _, hC, h => fun δ γ Θ c n ls ρ hδ hΘ hc hlw hg =>
      (cN_nuS_iff hC.2 hC.1 δ Θ c n ls _ ρ).mpr (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)

/-- **`nuOut` at `SemJN`** (Core's `nuOut_compatX`): a computation of `νX. C` is one of
`C[U(νX. C)/X]`. -/
theorem nuOut_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} :
    ∀ {m i : Nat} {C : CTy}, C.SysOkAt m i → SemJN (ℍ := ℍ) Δ Γ e (.comp (.nuSys m i C)) →
      SemJN (ℍ := ℍ) Δ Γ e (.comp (CTy.unrollS m i C))
  | 0, 0, _, hC, h => fun δ γ Θ c n ls ρ hδ hΘ hc hlw hg =>
      (cN_nu_iff hC δ Θ c n ls _ ρ).mp (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)
  | 0, _ + 1, _, hC, _ => hC.elim
  | _ + 1, _, _, hC, h => fun δ γ Θ c n ls ρ hδ hΘ hc hlw hg =>
      (cN_nuS_iff hC.2 hC.1 δ Θ c n ls _ ρ).mp (h δ γ Θ c n ls ρ hδ hΘ hc hlw hg)

/-! ### Coiteration -/

/-- **One unfolding is closed under a pure step in front** (Core's `cB_step`), at a `U X`
reading `P` closed down the index. -/
theorem cBNP_step {η : Option (Nat → TEntN)} (hP : EnvDownN η) : ∀ (D : CTy) (δ : LSub) (Θ : LocTy),
    Θ.Down → ∀ (c : Loc → Option Life) (n : Nat) (ls : List SRec) (ρ : WRes) (e e' : Expr),
    (∀ μ, BoCa.BoLo.Step1N (ℍ := ℍ) μ e μ e') →
    cBNP (ℍ := ℍ) η D δ Θ c n ls e' ρ → cBNP (ℍ := ℍ) η D δ Θ c n ls e ρ
  | .ret A, δ, _, hΘ, _, _, _, _, _, _, hs, h => fun lo =>
      erwpK_ret_det hΘ (fun z k v ρ h => vNE_down A η hP δ z.Θ k v ρ h)
        (fun μ => step1Only_of_step1N (hs μ)) (h lo)
  | .arr _ D, δ, Θ, hΘ, _, _, ls, _, _, _, hs, h =>
      fun c' k hk v ρv ρ' hc hv hcon =>
        cBNP_step hP D δ Θ hΘ c' k ls ρ' _ _ (fun μ => (hs μ).plug (Kont.appL .hole v))
          (h c' k hk v ρv ρ' hc hv hcon)
  | .amp C D, δ, Θ, hΘ, c, n, ls, ρ, _, _, hs, h =>
      ⟨cBNP_step hP C δ Θ hΘ c n ls ρ _ _ (fun μ => (hs μ).plug (Kont.appL .hole _)) h.1,
        cBNP_step hP D δ Θ hΘ c n ls ρ _ _ (fun μ => (hs μ).plug (Kont.appL .hole _)) h.2⟩
  | .top, _, _, _, _, _, _, _, _, _, _, h => h
  | .all x _ D, δ, Θ, hΘ, c, n, ls, ρ, _, _, hs, h =>
      fun α hα => cBNP_step hP D (δ.extend x α) Θ hΘ c n ls ρ _ _
        (fun μ => (hs μ).plug (Kont.appL .hole _)) (h α hα)
  | .nuSys _ _ _, _, _, _, _, _, _, _, _, _, _, h => h
  | .eff _ _ _ _ _ _ _ _, _, _, hΘ, _, _, _, _, _, _, hs, h =>
      cBNP_eff_det hP hΘ (fun μ => step1Only_of_step1N (hs μ)) h

/-- Pure steps in front of one unfolding (Core's `cB_pureSteps`). -/
theorem cBNP_pureSteps {η : Option (Nat → TEntN)} (hP : EnvDownN η) (D : CTy) (δ : LSub) {Θ : LocTy}
    (hΘ : Θ.Down) (c : Loc → Option Life) (n : Nat) (ls : List SRec) (ρ : WRes) {e e' : Expr}
    (h : PureSteps e e') (hw : cBNP (ℍ := ℍ) η D δ Θ c n ls e' ρ) :
    cBNP (ℍ := ℍ) η D δ Θ c n ls e ρ := by
  induction h with
  | refl => exact hw
  | tail _ hs ih => exact ih (cBNP_step hP D δ Θ hΘ c n ls ρ _ _ hs hw)

/-- The answer of an effectful observation is the answer type's (Core's `effRetE_ans`). -/
theorem retNX_ans (S : VTy) (P : LocTy → Nat → Val → WRes → Prop) :
    ∀ {D : CTy}, D.EffLeaf → retNX (ℍ := ℍ) (nuEnvN S P) D = vNX (ℍ := ℍ) S P (effAns D)
  | .ret _, _ => by funext δ Θ n v ρ; rfl
  | .eff _ _ _ _ _ _ _ D, h => by
      have h₁ := retNX_ans S P (D := D) h.2.2
      funext δ Θ n v ρ; simp only [retNX, effAns, h₁]

/-- **The candidate**: the codata `unfold step s` at a state `s ∈ 𝒱⟦S⟧` (Core's `candN`), at the
indices up to the step's, at `OK` worlds and views consistent with the resource. -/
def candNN (C : CTy) (g : Val) (S : VTy) (δ : LSub) (kg : Nat) : CandN := fun Θ c j _ e ρ =>
  j ≤ kg ∧ Θ.OK ∧ ConsistentX c ρ ∧ ∃ s, e = (etaN C g s).1 ∧ vN (ℍ := ℍ) S δ Θ j s ρ

theorem candNN_down (C : CTy) (g : Val) (S : VTy) (δ : LSub) (kg : Nat) :
    (candNN (ℍ := ℍ) C g S δ kg).Down :=
  fun _ _ _ _ _ _ _ ⟨hj, hΘ, hc, s, he, hs⟩ =>
    ⟨Nat.le_of_succ_le hj, hΘ, hc, s, he, vN_down S δ _ _ s _ hs⟩

/-- The candidate depends on `δ` only at the state type's free variables (Core's
`candN_congr`). -/
theorem candNN_congr (C : CTy) (g : Val) (S : VTy) {δ₁ δ₂ : LSub}
    (h : ∀ y, VFree y S → δ₁.find? y = δ₂.find? y) (kg : Nat) :
    candNN (ℍ := ℍ) C g S δ₁ kg = candNN (ℍ := ℍ) C g S δ₂ kg := by
  have hv := vN_congr (ℍ := ℍ) S (δ := δ₁) (δ' := δ₂) h
  funext Θ c j ls e ρ
  simp only [candNN, hv]

/-- **The map lemma** (Core's `map_ok`): `map_A (unfold step)` takes a value of `A[S/X]` to one of
`A` with `X` read at `P` (its closed type `T`), on the same resource, by pure steps, when
`unfold step s′` is in `P` for every state `s′ ∈ 𝒱⟦S⟧` up to the step's index. `node_okN` reads `X`
at the candidate (`candNN_wrap`); `nuOutK_compatN` at a code type.  `[spec §68]` -/
theorem map_okN (C : CTy) (g : Val) (S : VTy) (δ : LSub) (kg : Nat) (T : VTy)
    (P : LocTy → Nat → Val → WRes → Prop)
    (hW : ∀ Θ k w σ, k ≤ kg → vN (ℍ := ℍ) S δ Θ k w σ → P Θ k (etaN C g w) σ) :
    ∀ (A : VTy), A.Poly → ∀ (Θ : LocTy) (k : Nat), k ≤ kg → ∀ (w : Val) (σ : WRes),
      vNX (ℍ := ℍ) S (vN (ℍ := ℍ) S δ) A δ Θ k w σ →
      ∃ w', PureSteps (.app (.app (.val (mapV A)) (.val (hN C g))) (.val w)) (.val w') ∧
        vNX (ℍ := ℍ) T P A δ Θ k w' σ
  | .tvar 0, _, Θ, k, hk, w, σ, hw =>
      ⟨etaN C g w, (mapV_var_steps _ w).trans (hN_steps C g w), hW Θ k w σ hk hw⟩
  | .tvar (_ + 1), _, _, _, _, _, _, hw => hw.elim
  | .tensor A B, hP, Θ, k, hk, _, _, hw => by
      obtain ⟨v₁, v₂, σ₁, σ₂, rfl, hc, h₁, h₂⟩ := hw
      obtain ⟨w₁, hs₁, h₁'⟩ := map_okN C g S δ kg T P hW A hP.1 Θ k hk v₁ σ₁ h₁
      obtain ⟨w₂, hs₂, h₂'⟩ := map_okN C g S δ kg T P hW B hP.2 Θ k hk v₂ σ₂ h₂
      exact ⟨.pair w₁ w₂, (mapV_tensor_steps A B _ v₁ v₂).trans (pair_steps hs₁ hs₂),
        w₁, w₂, σ₁, σ₂, rfl, hc, h₁', h₂'⟩
  | .sum A B, hP, Θ, k, hk, _, σ, hw => by
      rcases hw with ⟨v, rfl, h⟩ | ⟨v, rfl, h⟩
      · obtain ⟨w', hs, h'⟩ := map_okN C g S δ kg T P hW A hP.1 Θ k hk v σ h
        exact ⟨.inj₁ w', (mapV_sum₁_steps A B _ v).trans (inj₁_steps hs), Or.inl ⟨w', rfl, h'⟩⟩
      · obtain ⟨w', hs, h'⟩ := map_okN C g S δ kg T P hW B hP.2 Θ k hk v σ h
        exact ⟨.inj₂ w', (mapV_sum₂_steps A B _ v).trans (inj₂_steps hs), Or.inr ⟨w', rfl, h'⟩⟩
  | .box _ A, hP, Θ, k, hk, w, σ, hw => by
      obtain ⟨α, hα, hb, ho⟩ := hw
      obtain ⟨w', hs, h'⟩ := map_okN C g S δ kg T P hW A hP Θ k hk w σ hb
      exact ⟨w', hs, α, hα, h', ho⟩
  | .unit, hP, _, _, _, w, _, hw | .zero, hP, _, _, _, w, _, hw | .thunk _, hP, _, _, _, w, _, hw
  | .code _ _ _, hP, _, _, _, w, _, hw
  | .ref _, hP, _, _, _, w, _, hw | .imm _ _, hP, _, _, _, w, _, hw
  | .mut _ _, hP, _, _, _, w, _, hw | .bang _, hP, _, _, _, w, _, hw
  | .unk, hP, _, _, _, w, _, hw | .mu _, hP, _, _, _, w, _, hw | .int _, hP, _, _, _, w, _, hw
  | .opq _, hP, _, _, _, w, _, hw | .fam _, hP, _, _, _, w, _, hw =>
      ⟨w, mapV_id_steps rfl _ w, by rw [vNX_occ T S P (vN (ℍ := ℍ) S δ) _ hP]; exact hw⟩

/-- `unfold step s′` is in the candidate's `U X` at every state `s′` up to the step's index. -/
theorem candNN_wrap (C : CTy) (g : Val) (S : VTy) (δ : LSub) (kg : Nat) :
    ∀ Θ k w σ, k ≤ kg → vN (ℍ := ℍ) S δ Θ k w σ →
      thunkRN (candNN (ℍ := ℍ) C g S δ kg) Θ k (etaN C g w) σ :=
  fun _ k w σ hk hw _ hE hOK _ hc _ => ⟨hk, hOK, hc, w, rfl, vN_extR S δ k w σ hE hw⟩

/-- **The node lemma** (Core's `node_ok`): when `c ()` runs a computation of `D[S/X]`,
`node_D (unfold step) c` is one unfolding of `D` with `U X` read at `P` (`X`'s closed type `T`),
when every state `s′ ∈ 𝒱⟦S⟧δ` up to the step's index has `unfold step s′` in `P`, at every `δ`
agreeing with `δ₀` on the variables `F`. The tree is read at such a `δ`; under a `∀'x` leaf at
`δ[x ↦ α]`, which still agrees because `'x` is not in `F`. `node_okN` reads `X` at the candidate,
`nuOutK_compatN` at a code type.  `[spec §68]` -/
theorem node_okP (C : CTy) (g : Val) (S : VTy) (kg : Nat) (T : VTy)
    (P : LocTy → Nat → Val → WRes → Prop) (hPd : ∀ Θ n v ρ, P Θ (n + 1) v ρ → P Θ n v ρ)
    (F : LifeVar → Prop) (δ₀ : LSub)
    (hW : ∀ δ : LSub, (∀ y, F y → δ₀.find? y = δ.find? y) → ∀ Θ k w σ, k ≤ kg →
      vN (ℍ := ℍ) S δ Θ k w σ → P Θ k (etaN C g w) σ) :
    ∀ (D : CTy), D.NuLeaf → (∀ x, D.LeafBinds x → ¬ F x) → ∀ (δ : LSub),
      (∀ y, F y → δ₀.find? y = δ.find? y) → ∀ (Θ : LocTy),
      Θ.OK → ∀ (c : Loc → Option Life) (j : Nat), j ≤ kg → ∀ (cv : Val) (M : Expr)
      (ls : List SRec) (ρ : WRes),
      PureSteps (.app (.val cv) (.val .unit)) M → cN (ℍ := ℍ) (D.instT S) δ Θ c j ls M ρ →
      cBNP (ℍ := ℍ) (nuEnvN T P) D δ Θ c j ls
        (.app (.app (.val (nodeV D)) (.val (hN C g))) (.val cv)) ρ
  | .ret A, hA, _, δ, hag, Θ, hΘ, c, j, hj, cv, M, ls, ρ, hc, hM => fun lo => by
      have hΦ : ∀ z : KW, z.Θ.OK → (z.Θ.view z.c).Down := fun z hz => LocTy.view_down hz.1 z.c
      have hDI : ∀ z : KW, (OpTabK.empty : OpTabK KW).DownI (fun z : KW => z.Θ.OK) :=
        fun _ => OpTabK.empty_downI _
      have hTd : (opTableK lo (OpTabK.empty : OpTabK KW)).Down := opTableK_downI (hDI ⟨Θ, c, lo⟩)
      have hQd : ∀ y : KW, PostN.Down (fun k _ v ρ => vNX (ℍ := ℍ) T P A δ y.Θ k v ρ) :=
        fun y k _ v ρ h => vNX_down _ _ hPd A δ y.Θ k v ρ h
      refine erwpK_pureSteps (x := (⟨Θ, c, lo⟩ : KW)) (hΦ _ hΘ) hTd hQd
        (nodeV_ret_steps A _ cv) ?_
      refine erwpK_pureSteps (x := (⟨Θ, c, lo⟩ : KW)) (hΦ _ hΘ) hTd hQd
        (PureSteps.plug (.appR (.val (.lam _)) .hole) hc) ?_
      refine erwpK_bind_leI (V := KW.PostK) (fun _ _ _ h₁ h₂ => KW.PostK.trans h₁ h₂)
        (Φ := fun z : KW => z.Θ.view z.c) (Inv := fun z : KW => z.Θ.OK) hΦ
        (fun _ _ h => by rw [h]) (fun _ _ h hx => by rw [h]; exact hx) (fl := fun z : KW => z.lo)
        (T := fun _ => OpTabK.empty)
        (fun _ _ h => tabLe_postK (fun z : KW => opTableK z.lo (OpTabK.empty : OpTabK KW)) h)
        (Q' := fun z k _ v ρ => vN (ℍ := ℍ) (VTy.inst S A) δ z.Θ k v ρ)
        (.appR (.val (.lam _)) .hole) (fun _ => by simp [Kont.HasHnd])
        (fun _ => by simp [Kont.Catches]) (fun _ _ _ _ _ h => by cases h)
        (fun _ _ _ _ h => by cases h) kg ?_ j hj (⟨Θ, c, lo⟩ : KW) hΘ ls M ρ (hM lo)
      rintro y hy k ls' w σ hk hw
      rw [← vNX_inst_poly S δ hA] at hw
      obtain ⟨w', hs, h'⟩ := map_okN C g S δ kg T P (hW δ hag) A hA y.Θ k hk w σ hw
      have hTy : (opTableK y.lo (OpTabK.empty : OpTabK KW)).Down := opTableK_downI (hDI y)
      refine erwpK_det (x := y) (Φ := fun z : KW => z.Θ.view z.c) (hΦ y hy) hTy hQd
        (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
      have e : Expr.subst 0 w (.app (.app (.val (mapV A)) (.val ((hN C g).shift 1 0))) (.var 0))
          = .app (.app (.val (mapV A)) (.val (hN C g))) (.val w) := by
        simp [Expr.subst, Val.val_shift, Expr.shift_zero, closed_subst (mapV_closed A),
          subst_shift_succ]
      simp only [Kont.plug]
      rw [e]
      exact erwpK_pureSteps (x := y) (Φ := fun z : KW => z.Θ.view z.c) (hΦ y hy) hTy hQd hs (erwpK_val (KW.postK_refl y) h')
  | .eff m i q A B fin rc D, hD, _, δ, hag, Θ, hΘ, c, j, hj, cv, M, ls, ρ, hc, hM => fun lo => by
      have hΦ : ∀ z : KW, z.Θ.OK → (z.Θ.view z.c).Down := fun z hz => LocTy.view_down hz.1 z.c
      have hDI : ∀ z : KW, (tabN (ℍ := ℍ) (.eff m i q A B fin rc D) δ z).DownI
          (fun z : KW => z.Θ.OK) := fun z => tabN_downI_OK _ δ z
      have hR := EffLeaf.ans_poly (C := D) hD.2.2
      have hQd : ∀ y : KW, PostN.Down (fun k _ v ρ => retNX (ℍ := ℍ) (nuEnvN T P) D δ y.Θ k v ρ) :=
        fun y k _ v ρ h => retNX_down (envDownN_nu hPd) D δ y.Θ k v ρ h
      show erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabN (ℍ := ℍ) (.eff m i q A B fin rc D) δ z)) _
        (⟨Θ, c, lo⟩ : KW) j ls _ ρ
      have hTd : (opTableK lo (tabN (ℍ := ℍ) (.eff m i q A B fin rc D) δ ⟨Θ, c, lo⟩)).Down :=
        opTableK_downI (hDI ⟨Θ, c, lo⟩)
      refine erwpK_pureSteps (x := (⟨Θ, c, lo⟩ : KW)) (hΦ _ hΘ) hTd hQd
        (nodeV_eff_steps m i q A B fin D _ cv) ?_
      refine erwpK_pureSteps (x := (⟨Θ, c, lo⟩ : KW)) (hΦ _ hΘ) hTd hQd
        (PureSteps.plug (.appR (.val (.lam _)) .hole) hc) ?_
      have hM₀ : erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
          (fun z => opTableK z.lo (tabN (ℍ := ℍ) (.eff m i q A B fin rc D) δ z))
          (fun z k _ v ρ => retN (ℍ := ℍ) (D.instT S) δ z.Θ k v ρ) (⟨Θ, c, lo⟩ : KW) j ls M ρ := by
        have h' := hM lo
        simp only [tabN_instT] at h'
        exact h'
      refine erwpK_bind_leI (V := KW.PostK) (fun _ _ _ h₁ h₂ => KW.PostK.trans h₁ h₂)
        (Φ := fun z : KW => z.Θ.view z.c) (Inv := fun z : KW => z.Θ.OK) hΦ
        (fun _ _ h => by rw [h]) (fun _ _ h hx => by rw [h]; exact hx) (fl := fun z : KW => z.lo)
        (T := fun z => tabN (ℍ := ℍ) (.eff m i q A B fin rc D) δ z)
        (fun _ _ h => tabLe_postK
          (fun z : KW => opTableK z.lo (tabN (ℍ := ℍ) (.eff m i q A B fin rc D) δ z)) h)
        (Q' := fun z k _ v ρ => retN (ℍ := ℍ) (D.instT S) δ z.Θ k v ρ)
        (.appR (.val (.lam _)) .hole) (fun _ => by simp [Kont.HasHnd])
        (fun _ => by simp [Kont.Catches])
        (fun z => tabN_ctxClosed_OK _ δ _ (fun _ => by simp [Kont.HasHnd]) (by simp [Kont.Catches]) z)
        (fun z m' i' en hT f y ρ' hy => (hDI z).wkI m' i' en hT f y ρ' hy) kg ?_ j hj
        (⟨Θ, c, lo⟩ : KW) hΘ ls M ρ hM₀
      rintro y hy k ls' w σ hk hw
      rw [← retNX_inst S δ hD.2.2, retNX_ans S _ hD.2.2] at hw
      obtain ⟨w', hs, h'⟩ := map_okN C g S δ kg T P (hW δ hag) (effAns D) hR y.Θ k hk w σ hw
      have hTy : (opTableK y.lo (tabN (ℍ := ℍ) (.eff m i q A B fin rc D) δ y)).Down :=
        opTableK_downI (hDI y)
      refine erwpK_det (x := y) (Φ := fun z : KW => z.Θ.view z.c) (hΦ y hy) hTy hQd
        (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
      have e : Expr.subst 0 w (.app (.app (.val (mapV (effAns D))) (.val ((hN C g).shift 1 0)))
          (.var 0)) = .app (.app (.val (mapV (effAns D))) (.val (hN C g))) (.val w) := by
        simp [Expr.subst, Val.val_shift, Expr.shift_zero,
          closed_subst (mapV_closed (effAns D)), subst_shift_succ]
      simp only [Kont.plug]
      rw [e]
      refine erwpK_pureSteps (x := y) (Φ := fun z : KW => z.Θ.view z.c) (hΦ y hy) hTy hQd hs (erwpK_val (KW.postK_refl y) ?_)
      show retNX (ℍ := ℍ) (nuEnvN T P) D δ y.Θ k w' σ
      rw [retNX_ans _ _ hD.2.2]
      exact h'
  | .amp D₁ D₂, hD, hfr, δ, hag, Θ, hΘ, c, j, hj, cv, M, ls, ρ, hc, hM =>
      ⟨cBNP_pureSteps (envDownN_nu hPd) D₁ δ hΘ.1 c j ls ρ (nodeV_amp₁_steps D₁ D₂ _ cv)
        (node_okP C g S kg T P hPd F δ₀ hW D₁ hD.1 (fun x hx => hfr x (Or.inl hx)) δ hag Θ hΘ c j
          hj _ (.app M (.val (.inj₁ .unit))) ls ρ
          ((childV_steps cv _ rfl).trans (PureSteps.plug (.appL .hole _) hc)) hM.1),
       cBNP_pureSteps (envDownN_nu hPd) D₂ δ hΘ.1 c j ls ρ (nodeV_amp₂_steps D₁ D₂ _ cv)
        (node_okP C g S kg T P hPd F δ₀ hW D₂ hD.2 (fun x hx => hfr x (Or.inr hx)) δ hag Θ hΘ c j
          hj _ (.app M (.val (.inj₂ .unit))) ls ρ
          ((childV_steps cv _ rfl).trans (PureSteps.plug (.appL .hole _) hc)) hM.2)⟩
  | .arr A D, hD, hfr, δ, hag, Θ, hΘ, _, j, hj, cv, M, ls, _, hc, hM =>
      fun c' k hk v ρv ρ' hcomp hv hcon =>
        cBNP_pureSteps (envDownN_nu hPd) D δ hΘ.1 c' k ls ρ' (nodeV_arr_steps A D _ cv v)
          (node_okP C g S kg T P hPd F δ₀ hW D hD.2 hfr δ hag Θ hΘ c' k (le_trans hk hj)
            (childA cv v) (.app M (.val v)) ls ρ'
            ((childA_steps cv v).trans (PureSteps.plug (.appL .hole _) hc))
            (hM c' k hk v ρv ρ' hcomp hv hcon))
  | .all x b D, hD, hfr, δ, hag, Θ, hΘ, c, j, hj, cv, M, ls, ρ, hc, hM => fun α hα => by
      have hag' : ∀ y, F y → δ₀.find? y = (δ.extend x α).find? y := by
        intro y hy
        have hxy : x ≠ y := fun h => hfr x (Or.inl rfl) (h ▸ hy)
        exact (hag y hy).trans (BoCa.Fig16.LogRel.find?_extend_ne δ α hxy).symm
      exact cBNP_pureSteps (envDownN_nu hPd) D _ hΘ.1 c j ls ρ (nodeV_all_steps x b D _ cv)
        (node_okP C g S kg T P hPd F δ₀ hW D hD (fun y hy => hfr y (Or.inr hy)) (δ.extend x α) hag'
          Θ hΘ c j hj (childA cv .unit) (.app M (.val .unit)) ls ρ
          ((childA_steps cv .unit).trans (PureSteps.plug (.appL .hole _) hc)) (hM α hα))
  | .top, hD, _, _, _, _, _, _, _, _, _, _, _, _, _, _
  | .nuSys _ _ _, hD, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => hD.elim

/-- **The node lemma at the candidate** (Core's `node_ok`): `node_okP` with `U X` read at the
candidate at `δ`, which is the candidate at every `δ′` agreeing with `δ` on the state type's free
variables (`candNN_congr`). -/
theorem node_okN (C : CTy) (g : Val) (S : VTy) (kg : Nat) :
    ∀ (D : CTy), D.NuLeaf → (∀ x, D.LeafBinds x → ¬ VFree x S) → ∀ (δ : LSub) (Θ : LocTy),
      Θ.OK → ∀ (c : Loc → Option Life) (j : Nat), j ≤ kg → ∀ (cv : Val) (M : Expr)
      (ls : List SRec) (ρ : WRes),
      PureSteps (.app (.val cv) (.val .unit)) M → cN (ℍ := ℍ) (D.instT S) δ Θ c j ls M ρ →
      cBN (ℍ := ℍ) (.thunk (.nu C)) (candNN (ℍ := ℍ) C g S δ kg) D δ Θ c j ls
        (.app (.app (.val (nodeV D)) (.val (hN C g))) (.val cv)) ρ :=
  fun D hD hS δ => node_okP C g S kg _ _ (thunkRN_down (candNN_down C g S δ kg))
    (fun y => VFree y S) δ
    (fun δ' hag Θ k w σ hk hw => by
      rw [candNN_congr C g S hag kg]; exact candNN_wrap C g S δ' kg Θ k w σ hk hw)
    D hD hS δ (fun _ _ => rfl)

/-- **The candidate is a post-fixed point of `νX. C`'s unfolding** (Core's `candN_post`): each
observation path runs the same path of the step and returns its result with every state `s′`
replaced by `unfold step s′`, back in the candidate. -/
theorem candNN_post {C : CTy} (hC : C.NuOk) {S : VTy} (hS : ∀ x, C.LeafBinds x → ¬ VFree x S)
    {δ : LSub} {g : Val} {kg : Nat}
    (hg : ∀ Θ : LocTy, vN (ℍ := ℍ) (.bang (.thunk (.arr S (C.instT S)))) δ Θ kg g PMap.empty) :
    (candNN (ℍ := ℍ) C g S δ kg).Le
      (cBN (ℍ := ℍ) (.thunk (.nu C)) (candNN (ℍ := ℍ) C g S δ kg) C δ) := by
  rintro Θ c j ls e ρ ⟨hj, hΘ, hc, s, rfl, hs⟩
  obtain ⟨-, hthunk⟩ := hg Θ
  have hstep : cN (ℍ := ℍ) (C.instT S) δ Θ c j ls (.app (.val g) (.val s)) ρ :=
    hthunk Θ (LocTy.extR_refl Θ _) hΘ c (consistentX_empty c) ls c j hj s ρ ρ
      (compS_empty_left ρ) hs hc
  cases C with
  | amp C₁ C₂ =>
      have hN := node_okN (ℍ := ℍ) (.amp C₁ C₂) g S kg (.amp C₁ C₂) hC.1 hS δ Θ hΘ c j hj
        (rootV g s) _ ls ρ (rootV_steps g s) hstep
      exact ⟨cBNP_pureSteps (envDownN_nu (thunkRN_down (candNN_down _ g S δ kg))) C₁ δ hΘ.1 c j ls ρ (etaN_obs _ g s _) hN.1,
        cBNP_pureSteps (envDownN_nu (thunkRN_down (candNN_down _ g S δ kg))) C₂ δ hΘ.1 c j ls ρ (etaN_obs _ g s _) hN.2⟩
  | _ => exact hC.1.elim

/-- **`unfold` at `SemJN`** (Core's `unfold_compatX`): `unfold : !U(S ⊸ C[S/X]) ⊸ !U(S ⊸ νX. C)`
at every positive `C` and every `S` in which no lifetime bound by a `∀` leaf of `C` is free. The
step is at every world (`!` owns nothing, `LocTy.extR_empty`); the codata `unfold step s` is in the
candidate at the step's index, which is below `𝒞⟦νX. C⟧` by coinduction. -/
theorem unfoldN_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {C : CTy} (hC : C.NuOk) (S : VTy)
    (hS : C.BindsFresh S) (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val (unfoldV C)) (.val (unfoldTy C S)) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl := gN_deadP hΓ hg
  rw [substAll_closed (unfoldV_closed C)]
  refine cN_ret_of (erwp_val (v := unfoldV C) ?_)
  intro Θ' _ hΘ' _ _ ls' c'' k _ g σ τ hcomp hv hcon
  have hσ : σ = PMap.empty := hv.1
  subst hσ
  obtain rfl := eq_of_compS_empty_left hcomp
  have hg' : ∀ Θ'' : LocTy,
      vN (ℍ := ℍ) (.bang (.thunk (.arr S (C.instT S)))) δ Θ'' k g PMap.empty :=
    fun Θ'' => vN_extR _ δ k g _ (LocTy.extR_empty Θ' Θ'') hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine cN_ret_of ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ g) rfl .hole) ?_
  simp only [Kont.plug]
  rw [unfoldV_subst]
  refine erwp_val (v := hN C g) ⟨rfl, ?_⟩
  intro Θ₂ _ hΘ₂ _ _ ls₂ c₃ k' hk' s ρs ρ₃ hcomp' hs hcon'
  have e₃ := eq_of_compS_empty_left hcomp'
  subst e₃
  refine cN_head (.nu C) δ Θ₂ hΘ₂.1 c₃ k' ls₂ _ .hole _ _ (fun μ => Head.beta μ _ s) rfl ?_
  simp only [Kont.plug]
  rw [hN_subst]
  exact cN_nu_coind (candNN_post hC hS (fun Θ'' => vN_le hk' (hg' Θ''))) Θ₂ c₃ k' ls₂ _ _
    ⟨le_rfl, hΘ₂, hcon', s, rfl, hs⟩

/-! ### `reify`'s loop values at one unfolding

Core's `candR_post` (`Core/DivReify.lean`) cases on the three loop values of its candidate. Its
`done b` and `closed r` cases read no handler; they are stated here at every candidate `Rc`, with
`Rc` holding `closed r` where `closed r`'s *next* answers it. -/

/-- The answer of a row's layers is the answer type's (Core's `effRetE_effOf`). -/
theorem retNX_effOf (S : VTy) (P : LocTy → Nat → Val → WRes → Prop) (δ : LSub) (Θ : LocTy) :
    ∀ (Sg : Row) (A : VTy), retNX (ℍ := ℍ) (nuEnvN S P) (CTy.effOf Sg A) δ Θ = vNX (ℍ := ℍ) S P A δ Θ
  | [], A => by funext k v ρ; simp only [CTy.effOf, retNX]
  | _ :: Sg, A => by funext k v ρ; simp only [CTy.effOf, retNX]; rw [retNX_effOf S P δ Θ Sg A]

/-- **One unfolding at `F_Σ A`** (Core's `cB_effOf`): `erwpK` at every floor at the row's table,
the answer read by `vNX`. Every row, `Div` included. -/
theorem cBN_effOf (S : VTy) (R : CandN) (Sg : Row) (A : VTy) (δ : LSub) (Θ : LocTy)
    (c : Loc → Option Life) (n : Nat) (ls : List SRec) (e : Expr) (ρ : WRes) :
    cBN (ℍ := ℍ) S R (CTy.effOf Sg A) δ Θ c n ls e ρ ↔ ∀ lo : Life,
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c)
        (fun z => opTableK z.lo (tabN (ℍ := ℍ) (CTy.effOf Sg A) δ z))
        (fun z k _ v ρ => vNX (ℍ := ℍ) S (thunkRN R) A δ z.Θ k v ρ) ⟨Θ, c, lo⟩ n ls e ρ := by
  cases Sg with
  | nil => simp only [CTy.effOf, cBNP, tabN]
  | cons o Sg =>
      simp only [CTy.effOf, cBNP, tabN]
      simp only [retNX_effOf]

/-- **A type without the variable reads the same in `νX. C`'s environment** (Core's
`vCE_nuEnv_rename`). -/
theorem vNX_rename (S : VTy) (P : LocTy → Nat → Val → WRes → Prop) (A : VTy) (δ : LSub) :
    vNX (ℍ := ℍ) S P (A.rename Nat.succ) δ = vN (ℍ := ℍ) A δ := by
  rw [vNX_inst_occ S P _ (VTy.not_occ_rename_succ A) δ, VTy.inst_rename_succ]

/-- `inl b` at `A ⊕ X` (Core's `nuAns_inl`). -/
theorem nuAnsN_inl {S : VTy} {P : LocTy → Nat → Val → WRes → Prop} {A : VTy} {δ : LSub}
    {Θ : LocTy} {n : Nat} {b : Val} {ρ : WRes} (h : vN (ℍ := ℍ) A δ Θ n b ρ) :
    vNX (ℍ := ℍ) S P (.sum (A.rename Nat.succ) (.tvar 0)) δ Θ n (Val.inj₁ b) ρ :=
  Or.inl ⟨b, rfl, by rw [vNX_rename]; exact h⟩

/-- `inr L` at `A ⊕ X`, `L` a thunk of the candidate (Core's `nuAns_inr`). -/
theorem nuAnsN_inr {S : VTy} {R : CandN} {A : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {L : Val}
    {ρ : WRes} (h : thunkRN R Θ n L ρ) :
    vNX (ℍ := ℍ) S (thunkRN R) (.sum (A.rename Nat.succ) (.tvar 0)) δ Θ n (Val.inj₂ L) ρ :=
  Or.inr ⟨L, rfl, h⟩

/-- A row's table does not read the answer type. -/
theorem tabN_effOf_ans (Sg : Row) (A B : VTy) (δ : LSub) :
    tabN (ℍ := ℍ) (CTy.effOf Sg A) δ = tabN (ℍ := ℍ) (CTy.effOf Sg B) δ := by
  funext x; rw [tabN_eq, tabN_eq, tabF_effOf_ret]

/-- **`done b` is one unfolding of `Loop_Σ B R` at every candidate** (Core's `candR_post`, the
`done b` case): *next* answers `inl b`; *close* runs the residual `res b`. -/
theorem doneLoop_cBN {Sg : Row} {B R : VTy} {res : Val} (hres : closedAt 0 res.1 = true)
    {δ : LSub} (hresR : ∀ Θ : LocTy, Θ.OK → ∀ c k ls b ρ, vN (ℍ := ℍ) B δ Θ k b ρ →
      ConsistentX c ρ → cN (ℍ := ℍ) (CTy.effOf Sg R) δ Θ c k ls (.app (.val res) (.val b)) ρ)
    {Rc : CandN} (hRc : Rc.Down) {Θ : LocTy} (hΘ : Θ.OK) {c : Loc → Option Life} {n : Nat}
    {ls : List SRec} {b : Val} {ρ : WRes} (hc : ConsistentX c ρ) (hb : vN (ℍ := ℍ) B δ Θ n b ρ) :
    cBN (ℍ := ℍ) (.thunk (CTy.loopEff Sg B R)) Rc (CTy.loopEffBody Sg B R) δ Θ c n ls
      (.val (doneLoop res b)) ρ := by
  have hΦ := LocTy.view_down hΘ.1 c
  constructor
  · refine (cBN_effOf _ Rc Sg _ δ Θ c n ls _ ρ).mpr fun lo => ?_
    refine erwpK_pureSteps (x := (⟨Θ, c, lo⟩ : KW)) (Φ := fun z : KW => z.Θ.view z.c) hΦ
      (opTableK_downI (tabN_downI_OK _ δ _))
      (fun y k _ v ρ h => vNX_down _ _ (thunkRN_down hRc) _ δ y.Θ k v ρ h)
      (doneLoop_next res hres b) ?_
    exact erwpK_val (KW.postK_refl _) (nuAnsN_inl hb)
  · refine (cBN_effOf _ Rc Sg _ δ Θ c n ls _ ρ).mpr fun lo => ?_
    have h := (cN_effOf Sg R δ Θ c n ls _ ρ).mp (hresR Θ hΘ c n ls b ρ hb hc) lo
    simp only [vNX_rename]
    rw [tabN_effOf_ans Sg (R.rename Nat.succ) R δ]
    exact erwpK_pureSteps (x := (⟨Θ, c, lo⟩ : KW)) (Φ := fun z : KW => z.Θ.view z.c) hΦ
      (opTableK_downI (tabN_downI_OK _ δ _)) (fun y k _ v ρ h => vN_down R δ y.Θ k v ρ h)
      (doneLoop_close res hres b) h

/-- **`closed r` is one unfolding of `Loop_Σ B R` at a candidate holding it** (Core's
`candR_post`, the `closed r` case): *next* answers `inr (closed r)`; *close* answers `r`. -/
theorem clLoop_cBN {Sg : Row} {B R : VTy} {δ : LSub} {Rc : CandN} (hRc : Rc.Down) {Θ : LocTy}
    (hΘ : Θ.OK) {c : Loc → Option Life} {n : Nat} {ls : List SRec} {r : Val} {ρ : WRes}
    (hr : vN (ℍ := ℍ) R δ Θ n r ρ) (hcl : thunkRN Rc Θ n (clLoop r) ρ) :
    cBN (ℍ := ℍ) (.thunk (CTy.loopEff Sg B R)) Rc (CTy.loopEffBody Sg B R) δ Θ c n ls
      (.val (clLoop r)) ρ := by
  have hΦ := LocTy.view_down hΘ.1 c
  constructor
  · refine (cBN_effOf _ Rc Sg _ δ Θ c n ls _ ρ).mpr fun lo => ?_
    refine erwpK_pureSteps (x := (⟨Θ, c, lo⟩ : KW)) (Φ := fun z : KW => z.Θ.view z.c) hΦ
      (opTableK_downI (tabN_downI_OK _ δ _))
      (fun y k _ v ρ h => vNX_down _ _ (thunkRN_down hRc) _ δ y.Θ k v ρ h)
      (clLoop_next r) ?_
    exact erwpK_val (KW.postK_refl _) (nuAnsN_inr hcl)
  · refine (cBN_effOf _ Rc Sg _ δ Θ c n ls _ ρ).mpr fun lo => ?_
    simp only [vNX_rename]
    exact erwpK_pureSteps (x := (⟨Θ, c, lo⟩ : KW)) (Φ := fun z : KW => z.Θ.view z.c) hΦ
      (opTableK_downI (tabN_downI_OK _ δ _)) (fun y k _ v ρ h => vN_down R δ y.Θ k v ρ h)
      (clLoop_close r) (erwpK_val (KW.postK_refl _) hr)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end

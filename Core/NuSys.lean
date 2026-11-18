import Core.NuRel

/-!
# Core — the relation at a system of codata equations  `[spec §79]`

`cC`'s clause at `νᵢ(X₀…Xₘ). C₀; …; Cₘ` (`m ≥ 1`) is the `i`-th component of the greatest tuple
of candidates below one unfolding of every body (`cBSys`, `nuEnvS`).  One unfolding is monotone in
each component (`cB_monoS`: `vCE_mono_at` at one variable at a time, every `Xₖ` outside the `Mut`
payloads), so the tuple of the relation's own components is a fixed point (`cC_nuS_unfold`).  At
the relation one unfolding of `Cᵢ` is `cC` at the simultaneous unrolling
`Cᵢ[U ν₀/X₀, …, U νₘ/Xₘ]` (`cB_unrollS`), the environment's types never read (`vCE_polyN_ty`):
`𝒞⟦νᵢ⟧ = 𝒞⟦Cᵢ[U ν⃗/X⃗]⟧` (`cC_nuS_iff`).  Under a `∀` leaf the tree is read at an extension of
`δ`; the candidates agree there because no leaf binder of any body is free in the system
(`CTy.SysOk`'s system-wide freshness).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The spine -/

/-- Each body of a system's spine is an observation tree over its variables. -/
theorem CTy.SysShapeAt.body {n : Nat} : ∀ {k : Nat} {Cs : CTy}, Cs.SysShapeAt n k → ∀ j, j ≤ k →
    (Cs.body k j).NuLeafS n
  | 0, .amp _ _, h, _, _ => h
  | _ + 1, .amp (.amp _ _) _, h, 0, _ => h.1
  | k + 1, .amp _ D, h, j + 1, hj => CTy.SysShapeAt.body (k := k) (Cs := D) h.2 j (by omega)
  | 0, .ret _, h, _, _ | 0, .arr _ _, h, _, _ | 0, .top, h, _, _ | 0, .all _ _ _, h, _, _
  | 0, .nuSys _ _ _, h, _, _ | 0, .eff _ _ _ _ _ _ _ _, h, _, _ => h.elim
  | _ + 1, .ret _, h, _, _ | _ + 1, .arr _ _, h, _, _ | _ + 1, .top, h, _, _
  | _ + 1, .all _ _ _, h, _, _ | _ + 1, .nuSys _ _ _, h, _, _
  | _ + 1, .eff _ _ _ _ _ _ _ _, h, _, _ => h.elim
  | _ + 1, .amp (.ret _) _, h, 0, _ | _ + 1, .amp (.arr _ _) _, h, 0, _
  | _ + 1, .amp .top _, h, 0, _ | _ + 1, .amp (.all _ _ _) _, h, 0, _
  | _ + 1, .amp (.nuSys _ _ _) _, h, 0, _
  | _ + 1, .amp (.eff _ _ _ _ _ _ _ _) _, h, 0, _ => h.1.elim

/-- Each body of an effect-free spine is effect-free. -/
theorem CTy.EffFree.body : ∀ {k : Nat} {Cs : CTy}, Cs.EffFree → ∀ j, (Cs.body k j).EffFree
  | 0, _, h, _ => h
  | _ + 1, .amp _ _, h, 0 => h.1
  | k + 1, .amp _ D, h, j + 1 => CTy.EffFree.body (k := k) (Cs := D) h.2 j
  | _ + 1, .ret _, _, j | _ + 1, .arr _ _, _, j | _ + 1, .top, _, j | _ + 1, .all _ _ _, _, j
  | _ + 1, .nuSys _ _ _, _, j | _ + 1, .eff _ _ _ _ _ _ _ _, _, j => by cases j <;> exact trivial

/-- **`cBSys` is "each component below its body"**, at the system's shape. -/
theorem cBSys_iff (η : Option (Nat → TEnt)) (Rs : Nat → CPred) (δ : LSub) (n : Nat) :
    ∀ (k : Nat) (Cs : CTy) (j₀ : Nat), Cs.SysShapeAt n k →
      (cBSys η k Cs Rs j₀ δ ↔ ∀ j, j ≤ k → (Rs (j₀ + j)).Le (fun ls e => cB η (Cs.body k j) ls δ e))
  | 0, .amp L R, j₀, _ => by
      constructor
      · intro h j hj ls e ρ he
        obtain rfl : j = 0 := by omega
        exact h ls e ρ he
      · intro h ls e ρ he; exact h 0 (Nat.le_refl 0) ls e ρ he
  | k + 1, .amp (.amp L R) D, j₀, hS => by
      have ih := cBSys_iff η Rs δ n k D (j₀ + 1) hS.2
      simp only [cBSys]
      constructor
      · rintro ⟨h0, hr⟩ j hj ls e ρ he
        cases j with
        | zero => exact h0 ls e ρ he
        | succ j =>
            exact (ih.mp hr) j (by omega) ls e ρ (by rwa [show j₀ + (j + 1) = j₀ + 1 + j by omega] at he)
      · intro h
        refine ⟨fun ls e ρ he => h 0 (Nat.zero_le _) ls e ρ he, ih.mpr fun j hj ls e ρ he => ?_⟩
        exact h (j + 1) (by omega) ls e ρ (by rwa [show j₀ + 1 + j = j₀ + (j + 1) by omega] at he)
  | 0, .ret _, _, h | 0, .arr _ _, _, h | 0, .top, _, h | 0, .all _ _ _, _, h
  | 0, .nuSys _ _ _, _, h | 0, .eff _ _ _ _ _ _ _ _, _, h => h.elim
  | _ + 1, .ret _, _, h | _ + 1, .arr _ _, _, h | _ + 1, .top, _, h | _ + 1, .all _ _ _, _, h
  | _ + 1, .nuSys _ _ _, _, h | _ + 1, .eff _ _ _ _ _ _ _ _, _, h => h.elim
  | _ + 1, .amp (.ret _) _, _, h | _ + 1, .amp (.arr _ _) _, _, h | _ + 1, .amp .top _, _, h
  | _ + 1, .amp (.all _ _ _) _, _, h | _ + 1, .amp (.nuSys _ _ _) _, _, h
  | _ + 1, .amp (.eff _ _ _ _ _ _ _ _) _, _, h => h.1.elim

/-! ### Monotone in each component -/

/-- `Rs` with its components below `j` taken from `Rs'`. -/
def hybS (Rs Rs' : Nat → CPred) (j : Nat) : Nat → CPred := fun k => if k < j then Rs' k else Rs k

/-- **A leaf is monotone in each component of the tuple**: `vCE_mono_at` at one variable at a
time, from `Rs` to `Rs'` through the hybrids. -/
theorem vCE_nuEnvS_mono (m : Nat) {Rs Rs' : Nat → CPred} (h : ∀ k, k ≤ m → (Rs k).Le (Rs' k))
    (A : VTy) (hA : A.PolyN (m + 1)) :
    ∀ b ls δ v ρ, vCE (some (nuEnvS m Rs)) b A ls δ v ρ → vCE (some (nuEnvS m Rs')) b A ls δ v ρ := by
  have step : ∀ j, j ≤ m + 1 → ∀ b ls δ v ρ, vCE (some (nuEnvS m Rs)) b A ls δ v ρ →
      vCE (some (nuEnvS m (hybS Rs Rs' j))) b A ls δ v ρ := by
    intro j
    induction j with
    | zero =>
        intro _ b ls δ v ρ hv
        have e : hybS Rs Rs' 0 = Rs := by funext k; simp [hybS]
        rw [e]; exact hv
    | succ j ih =>
        intro hj b ls δ v ρ hv
        refine vCE_mono_at A j _ _ (VTy.noMut_of_polyN hA j (by omega))
          (fun n => by unfold nuEnvS; split <;> rfl) (fun n hn => ?_) (fun b ls v ρ hp => ?_)
          b ls δ v ρ (ih (by omega) b ls δ v ρ hv)
        · unfold nuEnvS; split
          · simp only [hybS]
            by_cases h1 : n < j
            · simp [h1, show n < j + 1 by omega]
            · simp [h1, show ¬ n < j + 1 by omega]
          · rfl
        · have hjm : j ≤ m := by omega
          simp only [nuEnvS, hjm, if_true, hybS, Nat.lt_irrefl, if_false, Nat.lt_succ_self] at hp ⊢
          exact nuP_mono (h j hjm) b ls v ρ hp
  intro b ls δ v ρ hv
  have e : nuEnvS m (hybS Rs Rs' (m + 1)) = nuEnvS m Rs' := by
    funext k; unfold nuEnvS; split
    · simp [hybS, show k < m + 1 by omega]
    · rfl
  rw [← e]; exact step (m + 1) le_rfl b ls δ v ρ hv

theorem effRetE_monoS (m : Nat) {Rs Rs' : Nat → CPred} (h : ∀ k, k ≤ m → (Rs k).Le (Rs' k)) :
    ∀ {D : CTy}, D.EffLeafS (m + 1) → ∀ (δ : LSub) (ls : List SRec) (v : Val),
      Entails (effRetE (some (nuEnvS m Rs)) D δ ls v) (effRetE (some (nuEnvS m Rs')) D δ ls v)
  | .ret A, hA, δ, ls, v => vCE_nuEnvS_mono m h A hA true ls δ v
  | .eff _ _ _ _ _ _ _ D, hD, δ, ls, v => effRetE_monoS m h (D := D) hD.2.2 δ ls v

/-- **One unfolding is monotone in each component of the tuple** (`cB_mono` over `m + 1`
variables). -/
theorem cB_monoS (m : Nat) {Rs Rs' : Nat → CPred} (h : ∀ k, k ≤ m → (Rs k).Le (Rs' k)) :
    ∀ {D : CTy}, D.NuLeafS (m + 1) → ∀ (ls : List SRec) (δ : LSub) (e : Expr),
      Entails (cB (some (nuEnvS m Rs)) D ls δ e) (cB (some (nuEnvS m Rs')) D ls δ e)
  | .ret A, hA, ls, δ, e => wpTS_mono (fun ls' w => vCE_nuEnvS_mono m h A hA true ls' δ w)
  | .amp D₁ D₂, hD, ls, δ, e => fun ρ ⟨h₁, h₂⟩ =>
      ⟨cB_monoS m h hD.1 ls δ _ ρ h₁, cB_monoS m h hD.2 ls δ _ ρ h₂⟩
  | .eff n i q A B fin _ D, hD, ls, δ, e => fun ρ h' =>
      effWp_post (fun ls' v σ hv => effRetE_monoS m h (D := D) hD.2.2 δ ls' v σ hv) h'
  | .arr _ D, hD, ls, δ, e => fun ρ h' v ρ₁ ρ₂ hv hc =>
      cB_monoS m h (D := D) hD.2 ls δ _ ρ₂ (h' v ρ₁ ρ₂ hv hc)
  | .all x _ D, hD, ls, δ, e => fun ρ h' α ρ₁ ρ₂ hα hc =>
      cB_monoS m h (D := D) hD ls (δ.extend x α) _ ρ₂ (h' α ρ₁ ρ₂ hα hc)
  | .top, hD, _, _, _ | .nuSys _ _ _, hD, _, _, _ => hD.elim

/-! ### The greatest fixed point -/

/-- `𝒞⟦νⱼ⟧δ` for each equation `j` of the system `Cs` of `m + 2` equations: the relation's own
tuple. -/
abbrev nuSysRel (m : Nat) (Cs : CTy) (δ : LSub) : Nat → CPred :=
  fun j ls e => cC (.nuSys (m + 1) j Cs) ls δ e

/-- Coinduction: a post-fixed tuple is below the relation, componentwise. -/
theorem nuSysRel_coind {m : Nat} {Cs : CTy} {δ : LSub} {Rs : Nat → CPred}
    (hR : cBSys (some (nuEnvS (m + 1) Rs)) (m + 1) Cs Rs 0 δ) (j : Nat) :
    (Rs j).Le (nuSysRel m Cs δ j) := fun _ _ _ h _ _ => ⟨Rs, hR, h⟩

/-- `out`: a component of the relation is below one unfolding of its body. -/
theorem nuSysRel_out {m : Nat} {Cs : CTy} (hS : Cs.SysShape (m + 1)) (δ : LSub) {j : Nat}
    (hj : j ≤ m + 1) : (nuSysRel m Cs δ j).Le
      (fun ls e => cB (some (nuEnvS (m + 1) (nuSysRel m Cs δ))) (Cs.body (m + 1) j) ls δ e) := by
  intro ls e ρ h
  obtain ⟨Rs, hR, hr⟩ := h hj hS
  have hb := (cBSys_iff _ Rs δ (m + 2) (m + 1) Cs 0 hS).mp hR j hj ls e ρ (by simpa using hr)
  exact cB_monoS (m + 1) (fun k _ => nuSysRel_coind hR k) (hS.body j hj) ls δ e ρ hb

/-- `roll`: one unfolding of a body at the relation is in the relation. -/
theorem nuSysRel_roll {m : Nat} {Cs : CTy} (hS : Cs.SysShape (m + 1)) (δ : LSub) {j : Nat}
    (hj : j ≤ m + 1) : CPred.Le (fun ls e => cB (some (nuEnvS (m + 1) (nuSysRel m Cs δ)))
      (Cs.body (m + 1) j) ls δ e) (nuSysRel m Cs δ j) := by
  let Rs' : Nat → CPred := fun k ls e ρ => k ≤ m + 1 ∧
    cB (some (nuEnvS (m + 1) (nuSysRel m Cs δ))) (Cs.body (m + 1) k) ls δ e ρ
  have hle : ∀ k, k ≤ m + 1 → (nuSysRel m Cs δ k).Le (Rs' k) :=
    fun k hk ls e ρ h => ⟨hk, nuSysRel_out hS δ hk ls e ρ h⟩
  have hR : cBSys (some (nuEnvS (m + 1) Rs')) (m + 1) Cs Rs' 0 δ := by
    refine (cBSys_iff _ Rs' δ (m + 2) (m + 1) Cs 0 hS).mpr fun k hk ls e ρ h => ?_
    rw [Nat.zero_add] at h
    exact cB_monoS (m + 1) hle (hS.body k hk) ls δ e ρ h.2
  intro ls e ρ h
  exact nuSysRel_coind hR j ls e ρ ⟨hj, h⟩

/-- **A component of the relation is one unfolding of its body at the relation.** -/
theorem cC_nuS_unfold {m : Nat} {Cs : CTy} (hS : Cs.SysShape (m + 1)) {i : Nat} (hi : i ≤ m + 1)
    (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes) :
    cC (.nuSys (m + 1) i Cs) ls δ e ρ ↔
      cB (some (nuEnvS (m + 1) (nuSysRel m Cs δ))) (Cs.body (m + 1) i) ls δ e ρ :=
  ⟨nuSysRel_out hS δ hi ls e ρ, nuSysRel_roll hS δ hi ls e ρ⟩

/-! ### The unrolling -/

/-- **The environment's types are never read at a polynomial type** over `n` variables. -/
theorem vCE_polyN_ty (n : Nat) (η₁ η₂ : Nat → TEnt) (hP : ∀ k, (η₁ k).P = (η₂ k).P)
    (hT : ∀ k, n ≤ k → (η₁ k).ty = (η₂ k).ty) :
    ∀ (A : VTy), A.PolyN n → ∀ (b : Bool), vCE (some η₁) b A = vCE (some η₂) b A
  | .tensor A B, h, b => by
      funext ls δ v
      simp only [vCE, vCE_polyN_ty n η₁ η₂ hP hT A h.1 b, vCE_polyN_ty n η₁ η₂ hP hT B h.2 b]
  | .sum A B, h, b => by
      funext ls δ v
      simp only [vCE, vCE_polyN_ty n η₁ η₂ hP hT A h.1 b, vCE_polyN_ty n η₁ η₂ hP hT B h.2 b]
  | .box a A, h, b => by
      funext ls δ v
      simp only [vCE, vCE_polyN_ty n η₁ η₂ hP hT A h b]
  | .tvar k, _, b => by funext ls δ v; simp only [vCE, tEnvP, hP]
  | .unit, h, b | .zero, h, b | .thunk _, h, b | .code _ _ _, h, b | .unk, h, b | .int _, h, b
  | .opq _, h, b | .ref _, h, b | .imm _ _, h, b | .mut _ _, h, b | .bang _, h, b | .fam _, h, b
  | .mu _, h, b =>
      vCE_congr_occ _ _ _ (fun k hk => by
        have hkn : n ≤ k := Nat.le_of_not_lt fun hl => h k hl hk
        exact TEnt.ext' (hT k hkn) (hP k)) b

theorem sysThunks_getD (m : Nat) (Cs : CTy) (k : Nat) :
    VTy.substL (CTy.sysThunks m Cs) k =
      if k ≤ m then .thunk (.nuSys m k Cs) else .tvar (k - (m + 1)) := by
  simp only [VTy.substL, CTy.sysThunks, List.length_map, List.length_range]
  split
  · rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

/-- **The variable `U Xₖ` at the relation's tuple is `𝒱⟦U νₖ⟧`**, the candidates at `δ₀` and the
type read at `δ`, agreeing on the system's free variables. -/
theorem vCE_nuEnvS_at {m : Nat} (Cs : CTy) {δ₀ δ : LSub}
    (hag : ∀ y, CFree y Cs → δ₀.find? y = δ.find? y) (A : VTy) (hA : A.PolyN (m + 2))
    (b : Bool) (ls : List SRec) :
    vCE (some (nuEnvS (m + 1) (nuSysRel m Cs δ₀))) b A ls δ
      = vC b (A.subst (VTy.substL (CTy.sysThunks (m + 1) Cs))) ls δ := by
  rw [vC_eq_some, vCE_subst]
  rw [vCE_polyN_ty (m + 2) _ (substEnv tNil (VTy.substL (CTy.sysThunks (m + 1) Cs)) δ)
    (fun k => ?_) (fun k hk => ?_) A hA b]
  · simp only [substEnv, sysThunks_getD]
    unfold nuEnvS
    split
    · funext b' ls' v ρ
      cases b' with
      | false => rfl
      | true =>
          have hc : ∀ ls'', cC (.nuSys (m + 1) k Cs) ls'' δ₀ = cC (.nuSys (m + 1) k Cs) ls'' δ :=
            fun ls'' => cC_congr (.nuSys (m + 1) k Cs) (fun y hy => hag y hy) ls''
          simp only [nuP, thunkR, vCE, forceE, nuSysRel, hc]
    · funext b' ls' v ρ
      simp [vCE, tEnvP, tEnv]
  · simp only [substEnv, sysThunks_getD, nuEnvS, show ¬ k ≤ m + 1 by omega, if_false]
    simp [tEnv, VTy.subst]

theorem effTab_instTL (Ss : List VTy) (δ : LSub) : ∀ D : CTy, effTab (D.instTL Ss) δ = effTab D δ
  | .eff n i q A B fin _ D => by simp only [CTy.instTL, effTab, effTab_instTL Ss δ D]
  | .ret _ | .amp _ _ | .arr _ _ | .top | .all _ _ _ | .nuSys _ _ _ => by simp [CTy.instTL, effTab]

theorem CTy.divAt_instTL (Ss : List VTy) : ∀ D : CTy, (D.instTL Ss).divAt = D.divAt
  | .eff n i q A B fin _ D => by simp only [CTy.instTL, CTy.divAt, CTy.divAt_instTL Ss D]
  | .ret _ | .amp _ _ | .arr _ _ | .top | .all _ _ _ | .nuSys _ _ _ => by simp [CTy.instTL, CTy.divAt]

theorem effRetE_unrollS {m : Nat} (Cs : CTy) {δ₀ δ : LSub}
    (hag : ∀ y, CFree y Cs → δ₀.find? y = δ.find? y) : ∀ {D : CTy}, D.EffLeafS (m + 2) →
    effRetE (some (nuEnvS (m + 1) (nuSysRel m Cs δ₀))) D δ
      = effRet (D.instTL (CTy.sysThunks (m + 1) Cs)) δ
  | .ret A, hA => by
      funext ls v
      simp only [effRetE, effRet, CTy.instTL, vCE_nuEnvS_at Cs hag A hA]
  | .eff _ _ _ _ _ _ _ D, hD => by
      simp only [effRetE, effRet, CTy.instTL]
      exact effRetE_unrollS Cs hag (D := D) hD.2.2

/-- **One unfolding at the relation's tuple is `cC` at the simultaneous unrolling** (`cB_unroll`
over a system), the candidates at `δ₀` and the tree read at `δ`, agreeing on the system's free
variables; under a `∀'x` leaf at `δ[x ↦ α]`, which still agrees because `'x` is free in no
body. -/
theorem cB_unrollS {m : Nat} (Cs : CTy) (δ₀ : LSub) : ∀ {D : CTy}, D.NuLeafS (m + 2) →
    (∀ x, D.LeafBinds x → ¬ CFree x Cs) → ∀ (δ : LSub),
    (∀ y, CFree y Cs → δ₀.find? y = δ.find? y) → ∀ (ls : List SRec),
    cB (some (nuEnvS (m + 1) (nuSysRel m Cs δ₀))) D ls δ
      = cC (D.instTL (CTy.sysThunks (m + 1) Cs)) ls δ
  | .ret A, hA, _, δ, hag, ls => by
      funext e
      show wpTS ls e (fun ls'' => vCE _ true A ls'' δ)
        = wpTS ls e (fun ls'' => vC true (A.subst _) ls'' δ)
      simp only [vCE_nuEnvS_at Cs hag A hA]
  | .amp D₁ D₂, hD, hfr, δ, hag, ls => by
      funext e ρ
      show (cB _ D₁ ls δ _ ρ ∧ cB _ D₂ ls δ _ ρ)
        = (cC (D₁.instTL _) ls δ _ ρ ∧ cC (D₂.instTL _) ls δ _ ρ)
      rw [cB_unrollS Cs δ₀ hD.1 (fun x hx => hfr x (Or.inl hx)) δ hag ls,
        cB_unrollS Cs δ₀ hD.2 (fun x hx => hfr x (Or.inr hx)) δ hag ls]
  | .eff n i q A B fin rc D, hD, _, δ, hag, ls => by
      funext e
      show effWp _ _ _ ls e = effWp _ _ _ ls e
      rw [effRetE_unrollS Cs hag (D := D) hD.2.2, ← effTab_instTL (CTy.sysThunks (m + 1) Cs) δ D,
        ← CTy.divAt_instTL (CTy.sysThunks (m + 1) Cs) (.eff n i q A B fin rc D)]
      rfl
  | .arr A D, hD, hfr, δ, hag, ls => by
      funext e ρ
      show (∀ v, (vC true A ls δ v ─⋆ cB _ D ls δ (.app e (.val v))) ρ)
        = (∀ v, (vC true A ls δ v ─⋆ cC (D.instTL _) ls δ (.app e (.val v))) ρ)
      rw [cB_unrollS Cs δ₀ hD.2 hfr δ hag ls]
  | .all x c D, hD, hfr, δ, hag, ls => by
      funext e ρ
      have hag' : ∀ α, ∀ y, CFree y Cs → δ₀.find? y = (δ.extend x α).find? y := by
        intro α y hy
        have hxy : x ≠ y := fun h => hfr x (Or.inl rfl) (h ▸ hy)
        exact (hag y hy).trans (find?_extend_ne δ α hxy).symm
      show (∀ α, (⌜LtLife δ c α⌝ ─⋆ cB _ D ls (δ.extend x α) (.app e (.val .unit))) ρ)
        = (∀ α, (⌜LtLife δ c α⌝ ─⋆ cC (D.instTL _) ls (δ.extend x α) (.app e (.val .unit))) ρ)
      refine propext (forall_congr' fun α => ?_)
      rw [cB_unrollS Cs δ₀ (D := D) hD (fun y hy => hfr y (Or.inr hy)) (δ.extend x α) (hag' α) ls]
  | .top, hD, _, _, _, _ | .nuSys _ _ _, hD, _, _, _, _ => hD.elim

/-- A body's leaf binders are among the system's. -/
theorem CTy.leafBinds_body : ∀ {k : Nat} {Cs : CTy} {j : Nat} {x : LifeVar}, j ≤ k →
    (Cs.body k j).LeafBinds x → Cs.SysLeafBinds x k
  | 0, _, _, _, _, h => h
  | _ + 1, .amp _ _, 0, _, _, h => Or.inl h
  | k + 1, .amp _ D, j + 1, _, hj, h => Or.inr (CTy.leafBinds_body (k := k) (Cs := D) (by omega) h)
  | _ + 1, .ret _, _, _, _, h | _ + 1, .arr _ _, _, _, _, h | _ + 1, .top, _, _, _, h
  | _ + 1, .all _ _ _, _, _, _, h | _ + 1, .nuSys _ _ _, _, _, _, h
  | _ + 1, .eff _ _ _ _ _ _ _ _, _, _, _, h => by
      simp [CTy.body, CTy.LeafBinds] at h

/-- **`νᵢ` is its simultaneous unrolling**: `𝒞⟦νᵢ⟧ = 𝒞⟦Cᵢ[U ν₀/X₀, …, U νₘ/Xₘ]⟧`.
`[spec §79]` -/
theorem cC_nuS_iff {m i : Nat} {Cs : CTy} (hC : Cs.SysOk (m + 1)) (hi : i ≤ m + 1)
    (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes) :
    cC (.nuSys (m + 1) i Cs) ls δ e ρ ↔ cC (CTy.unrollS (m + 1) i Cs) ls δ e ρ := by
  rw [cC_nuS_unfold hC.1 hi]
  show _ ↔ cC ((Cs.body (m + 1) i).instTL _) ls δ e ρ
  rw [cB_unrollS Cs δ (hC.1.body i hi) (fun x hx => hC.2 x (CTy.leafBinds_body hi hx)) δ
    (fun _ _ => rfl) ls]

end BoCa.Fig16.LogRel.Core

end

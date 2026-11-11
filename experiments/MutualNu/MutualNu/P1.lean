import Core.Chain.NuKW835N

/-!
# MutualNu P1 — the chain's coiteration over a system (#995, `km-plan.md` §2)

The hardest case of mutual `ν`, against the real chain: the map and node lemmas (`map_okN`,
`node_okP`, `Core/Chain/NuKW835N.lean`) for a system of `n` equations, with a tuple of leaf
predicates `Ps` and the `n` rest-makers held in one tuple `tupV hs` that the map projects.

* `mapVS n`, `nodeVS n`: today's `mapV`/`nodeV` with `U Xₖ` (`k < n`) mapped by the `k`-th handle,
  `projV n k wr` (`FoldP.projV`); at the variable the map takes extra `letpair` steps.
* `envS Ss Ps`: the environment of one unfolding, `Xₖ` read at `Ps k`.
* `cBNPE η`: `cBNP` at an arbitrary environment.
* `map_okNS`, `node_okPS`: per component, the hypothesis on the `k`-th handle only.

The system is given at the Lean level (`n`, the bodies as trees); no former changes.  Out of the
probe: `F_Σ` leaves (`cBNPE`'s `eff` clause is `True` here; their map is the same `map_okNS`), and
the unrolling `cBNPE (envS Ss 𝒱⟦S⃗⟧) D = 𝒞⟦D[S⃗/X⃗]⟧` (simultaneous substitution with
system-wide freshness), which takes the shape of `cBNP_unroll`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace MutualNu.P1
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Fig16.LogRel (LtLife)
open BoCa.Lifetime (LSub LifeVar)
open BoCa.BoLo (Heap Kont Head)
open BoCa.Fig16.LogRel.Core.FoldP (tupV projE projV projE_closed projE_subst)

abbrev P4 := LocTy → Nat → Val → WRes → Prop

/-! ### Positivity over `n` variables -/

/-- Every `Xₖ`, `k < n`, occurs in `A` only under `⊗`, `⊕` and `[@a]`. -/
def PolyN (n : Nat) : VTy → Prop
  | .tensor A B => PolyN n A ∧ PolyN n B
  | .sum A B => PolyN n A ∧ PolyN n B
  | .box _ A => PolyN n A
  | .tvar _ => True
  | A => ∀ k, k < n → ¬ A.Occ k

/-- Observation trees over `n` variables (the probe omits `F_Σ` leaves). -/
def NuLeafS (n : Nat) : CTy → Prop
  | .ret A => PolyN n A
  | .amp C D => NuLeafS n C ∧ NuLeafS n D
  | .arr A D => A.Cl 0 ∧ NuLeafS n D
  | .all _ _ D => NuLeafS n D
  | _ => False

/-! ### The terms -/

def idV : Val := .lam (.val (.lam (.var 0)))

/-- `map_A wr w`, `wr` the tuple of the `n` rest-makers: at `Xₖ` the `k`-th, `projV n k wr`. -/
def mapVS (n : Nat) : VTy → Val
  | .tvar k => if k < n then .lam (.val (.lam (.app (.app (.val (projV n k)) (.var 1)) (.var 0))))
      else idV
  | .tensor A B => .lam (.val (.lam (.letpair (.var 0)
      (.pair (.app (.app (.val (mapVS n A)) (.var 3)) (.var 1))
        (.app (.app (.val (mapVS n B)) (.var 3)) (.var 0))))))
  | .sum A B => .lam (.val (.lam (.case (.var 0)
      (.inj₁ (.app (.app (.val (mapVS n A)) (.var 2)) (.var 0)))
      (.inj₂ (.app (.app (.val (mapVS n B)) (.var 2)) (.var 0))))))
  | .box _ A => mapVS n A
  | _ => idV

theorem projV_closed (n k : Nat) : closedAt 0 (projV n k).1 = true := by
  simp [projV, closedAt, projE_closed n k (e := .var 0) (j := 1) rfl]

theorem mapVS_closed (n : Nat) : ∀ A : VTy, closedAt 0 (mapVS n A).1 = true
  | .tvar k => by
      unfold mapVS; split
      · simp [closedAt, closedAt_mono _ (projV_closed n k) (Nat.zero_le _)]
      · rfl
  | .tensor A B => by
      simp [mapVS, closedAt, closedAt_mono _ (mapVS_closed n A) (Nat.zero_le _),
        closedAt_mono _ (mapVS_closed n B) (Nat.zero_le _)]
  | .sum A B => by
      simp [mapVS, closedAt, closedAt_mono _ (mapVS_closed n A) (Nat.zero_le _),
        closedAt_mono _ (mapVS_closed n B) (Nat.zero_le _)]
  | .box _ A => mapVS_closed n A
  | .unit | .zero | .thunk _ | .code _ _ _ | .ref _ | .imm _ _ | .mut _ _
  | .bang _ | .unk | .mu _ | .int _ | .opq _ | .fam _ => rfl

/-- `node_C wr c`, today's `nodeV` at `mapVS n`. -/
def nodeVS (n : Nat) : CTy → Val
  | .ret A => .lam (.val (.lam
      (bindE (.app (.var 0) (.val .unit)) (.app (.app (.val (mapVS n A)) (.var 2)) (.var 0)))))
  | .amp C D => .lam (.val (.lam (.val (.lam (.case (.var 0)
      (.app (.app (.val (nodeVS n C)) (.var 3))
        (.val (.lam (.app (.app (.var 3) (.val .unit)) (.val (.inj₁ .unit))))))
      (.app (.app (.val (nodeVS n D)) (.var 3))
        (.val (.lam (.app (.app (.var 3) (.val .unit)) (.val (.inj₂ .unit)))))))))))
  | .arr _ D => .lam (.val (.lam (.val (.lam
      (.app (.app (.val (nodeVS n D)) (.var 2))
        (.val (.lam (.app (.app (.var 2) (.val .unit)) (.var 1)))))))))
  | .all _ _ D => .lam (.val (.lam (.val (.lam
      (.app (.app (.val (nodeVS n D)) (.var 2))
        (.val (.lam (.app (.app (.var 2) (.val .unit)) (.var 1)))))))))
  | _ => .lam (.val (.lam (.val .unit)))

theorem nodeVS_closed (n : Nat) : ∀ C : CTy, closedAt 0 (nodeVS n C).1 = true
  | .ret A => by simp [nodeVS, bindE, closedAt, closedAt_mono _ (mapVS_closed n A) (Nat.zero_le _)]
  | .amp C D => by
      simp [nodeVS, closedAt, closedAt_mono _ (nodeVS_closed n C) (Nat.zero_le _),
        closedAt_mono _ (nodeVS_closed n D) (Nat.zero_le _)]
  | .arr _ D => by simp [nodeVS, closedAt, closedAt_mono _ (nodeVS_closed n D) (Nat.zero_le _)]
  | .all _ _ D => by simp [nodeVS, closedAt, closedAt_mono _ (nodeVS_closed n D) (Nat.zero_le _)]
  | .top | .nu _ | .eff _ _ _ _ _ _ _ _ => rfl

/-! ### Reduction -/

section
attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-- The `p`-th of a tuple, by pure steps. -/
theorem projE_tupV_steps : ∀ (vs : List Val) (p : Nat) (a : Val), vs[p]? = some a →
    PureSteps (projE vs.length p (.val (tupV vs))) (.val a)
  | [], _, _, h => by simp at h
  | [b], p, a, h => by
      cases p with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h; exact .refl
      | succ p => simp at h
  | b :: c :: rest, 0, a, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h; subst h
      simp only [List.length_cons, projE, tupV]
      refine (PureSteps.head (fun μ => Head.letpair μ b (tupV (c :: rest)) _) rfl).trans ?_
      simp; exact .refl
  | b :: c :: rest, p + 1, a, h => by
      simp only [List.getElem?_cons_succ] at h
      simp only [List.length_cons, projE, tupV]
      refine (PureSteps.head (fun μ => Head.letpair μ b (tupV (c :: rest)) _) rfl).trans ?_
      rw [FoldP.projE_subst_gen, FoldP.projE_subst_gen]
      simp [subst_shift_succ]
      exact projE_tupV_steps (c :: rest) p a h

/-- `map_{Xₖ} wr w ↦ hs[k] w` at `wr = tupV hs`. -/
theorem mapVS_var_steps {n k : Nat} (hk : k < n) (hs : List Val) (hn : hs.length = n) (a w : Val)
    (ha : hs[k]? = some a) :
    PureSteps (.app (.app (.val (mapVS n (.tvar k))) (.val (tupV hs))) (.val w)) (.app (.val a) (.val w)) := by
  simp only [mapVS, if_pos hk]
  refine (PureSteps.beta_in (.appL .hole w) _ _).trans ?_
  refine (PureSteps.beta _ w).trans ?_
  simp [closed_subst (projV_closed n k), subst_shift_succ]
  refine (PureSteps.beta_in (.appL .hole w) _ _).trans ?_
  rw [projE_subst]
  subst hn
  exact PureSteps.plug (.appL .hole w) (projE_tupV_steps hs k a ha)

theorem mapVS_id_steps {n : Nat} {A : VTy} (hA : mapVS n A = idV) (wr w : Val) :
    PureSteps (.app (.app (.val (mapVS n A)) (.val wr)) (.val w)) (.val w) := by
  rw [hA]
  refine (PureSteps.beta_in (.appL .hole w) _ wr).trans ?_
  refine (PureSteps.beta _ w).trans ?_
  simp; exact .refl

theorem mapVS_tensor_steps (n : Nat) (A B : VTy) (wr v₁ v₂ : Val) :
    PureSteps (.app (.app (.val (mapVS n (.tensor A B))) (.val wr)) (.val (.pair v₁ v₂)))
      (.pair (.app (.app (.val (mapVS n A)) (.val wr)) (.val v₁))
        (.app (.app (.val (mapVS n B)) (.val wr)) (.val v₂))) := by
  refine (PureSteps.beta_in (.appL .hole _) _ wr).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.letpair μ v₁ v₂ _) rfl).trans ?_
  simp [closed_subst (mapVS_closed n A), closed_subst (mapVS_closed n B), subst_shift_succ]
  exact .refl

theorem mapVS_sum₁_steps (n : Nat) (A B : VTy) (wr v : Val) :
    PureSteps (.app (.app (.val (mapVS n (.sum A B))) (.val wr)) (.val (.inj₁ v)))
      (.inj₁ (.app (.app (.val (mapVS n A)) (.val wr)) (.val v))) := by
  refine (PureSteps.beta_in (.appL .hole _) _ wr).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₁ μ v _ _) rfl).trans ?_
  simp [closed_subst (mapVS_closed n A), subst_shift_succ]
  exact .refl

theorem mapVS_sum₂_steps (n : Nat) (A B : VTy) (wr v : Val) :
    PureSteps (.app (.app (.val (mapVS n (.sum A B))) (.val wr)) (.val (.inj₂ v)))
      (.inj₂ (.app (.app (.val (mapVS n B)) (.val wr)) (.val v))) := by
  refine (PureSteps.beta_in (.appL .hole _) _ wr).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₂ μ v _ _) rfl).trans ?_
  simp [closed_subst (mapVS_closed n B), subst_shift_succ]
  exact .refl

theorem nodeVS_ret_steps (n : Nat) (A : VTy) (wr c : Val) :
    PureSteps (.app (.app (.val (nodeVS n (.ret A))) (.val wr)) (.val c))
      (bindE (.app (.val c) (.val .unit)) (.app (.app (.val (mapVS n A)) (.val (wr.shift 1 0)))
        (.var 0))) := by
  refine (PureSteps.beta_in (.appL .hole _) _ wr).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  simp [bindE, closed_subst (mapVS_closed n A), subst_shift_succ]
  exact .refl

theorem nodeVS_amp₁_steps (n : Nat) (C D : CTy) (wr c : Val) :
    PureSteps (.app (.app (.app (.val (nodeVS n (.amp C D))) (.val wr)) (.val c)) (.val (.inj₁ .unit)))
      (.app (.app (.val (nodeVS n C)) (.val wr)) (.val (childV c (.inj₁ .unit)))) := by
  refine (PureSteps.beta_in (.appL (.appL .hole _) _) _ wr).trans ?_
  refine (PureSteps.beta_in (.appL .hole _) _ _).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₁ μ _ _ _) rfl).trans ?_
  simp [childV, closed_subst (nodeVS_closed n C), subst_shift_succ]
  exact .refl

theorem nodeVS_amp₂_steps (n : Nat) (C D : CTy) (wr c : Val) :
    PureSteps (.app (.app (.app (.val (nodeVS n (.amp C D))) (.val wr)) (.val c)) (.val (.inj₂ .unit)))
      (.app (.app (.val (nodeVS n D)) (.val wr)) (.val (childV c (.inj₂ .unit)))) := by
  refine (PureSteps.beta_in (.appL (.appL .hole _) _) _ wr).trans ?_
  refine (PureSteps.beta_in (.appL .hole _) _ _).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₂ μ _ _ _) rfl).trans ?_
  simp [childV, closed_subst (nodeVS_closed n D), subst_shift_succ]
  exact .refl

theorem nodeVS_arr_steps (n : Nat) (A : VTy) (D : CTy) (wr c x : Val) :
    PureSteps (.app (.app (.app (.val (nodeVS n (.arr A D))) (.val wr)) (.val c)) (.val x))
      (.app (.app (.val (nodeVS n D)) (.val wr)) (.val (childA c x))) := by
  refine (PureSteps.beta_in (.appL (.appL .hole _) _) _ wr).trans ?_
  refine (PureSteps.beta_in (.appL .hole _) _ _).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  simp [childA, closed_subst (nodeVS_closed n D), subst_shift_succ]
  exact .refl

theorem nodeVS_all_steps (n : Nat) (x : LifeVar) (b : Lifetime.Life) (D : CTy) (wr c : Val) :
    PureSteps (.app (.app (.app (.val (nodeVS n (.all x b D))) (.val wr)) (.val c)) (.val .unit))
      (.app (.app (.val (nodeVS n D)) (.val wr)) (.val (childA c .unit))) := by
  refine (PureSteps.beta_in (.appL (.appL .hole _) _) _ wr).trans ?_
  refine (PureSteps.beta_in (.appL .hole _) _ _).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  simp [childA, closed_subst (nodeVS_closed n D), subst_shift_succ]
  exact .refl
end

/-! ### The environment of one unfolding, and one unfolding at it -/

/-- `Xₖ` (`k < Ss.length`) stands for `Ss[k]`, read at `Ps k`; the variables above are empty. -/
def envS (Ss : List VTy) (Ps : Nat → P4) : Option (Nat → TEntN) :=
  some fun k => if k < Ss.length then ⟨Ss.getD k .unit, nuPN (Ps k)⟩ else tEnvN none (k - Ss.length)

theorem envS_tvar {Ss : List VTy} {Ps : Nat → P4} {k : Nat} (hk : k < Ss.length) :
    tEnvPN (envS Ss Ps) k true = Ps k := by
  funext Θ j v ρ; simp [tEnvPN, envS, hk, nuPN]

theorem envS_down {Ss : List VTy} {Ps : Nat → P4}
    (hP : ∀ k Θ j v ρ, Ps k Θ (j + 1) v ρ → Ps k Θ j v ρ) : EnvDownN (envS Ss Ps) := by
  intro m b Θ j v ρ h
  by_cases hm : m < Ss.length
  · simp only [tEnvN, envS, hm, if_true] at h ⊢
    cases b
    · trivial
    · exact hP m Θ j v ρ h
  · simp only [tEnvN, envS, hm, if_false] at h ⊢

/-- `cBNP` at the environment `η` (the probe omits `F_Σ`). -/
def cBNPE (η : Option (Nat → TEntN)) : CTy → LSub → CandN
  | .ret A, δ, Θ, c, n, ls, e, ρ => ∀ lo : Life,
      erwpK (ℍ := ℍ) KW.PostK (fun z => z.Θ.view z.c) (fun z => opTableK z.lo OpTabK.empty)
        (fun z k _ v ρ => vNE η A δ z.Θ k v ρ) ⟨Θ, c, lo⟩ n ls e ρ
  | .amp C D, δ, Θ, c, n, ls, e, ρ => cBNPE η C δ Θ c n ls (.app e (.val (Val.inj₁ .unit))) ρ ∧
      cBNPE η D δ Θ c n ls (.app e (.val (Val.inj₂ .unit))) ρ
  | .arr A D, δ, Θ, _, n, ls, e, ρ => ∀ c',
      ∀ k, k ≤ n → ∀ (v : Val) (ρv ρ' : WRes), ResU.CompS ρ ρv ρ' → vNE none A δ Θ k v ρv →
        ConsistentX c' ρ' → cBNPE η D δ Θ c' k ls (.app e (.val v)) ρ'
  | .all x c' D, δ, Θ, c, n, ls, e, ρ =>
      ∀ α, LtLife δ c' α → cBNPE η D (δ.extend x α) Θ c n ls (.app e (.val .unit)) ρ
  | _, _, _, _, _, _, _, _ => True

theorem cBNPE_step {η : Option (Nat → TEntN)} (hη : EnvDownN η) : ∀ (D : CTy) (δ : LSub)
    (Θ : LocTy), Θ.Down → ∀ (c : Loc → Option Life) (n : Nat) (ls : List SRec) (ρ : WRes)
    (e e' : Expr), (∀ μ, BoCa.BoLo.Step1N (ℍ := ℍ) μ e μ e') →
    cBNPE (ℍ := ℍ) η D δ Θ c n ls e' ρ → cBNPE (ℍ := ℍ) η D δ Θ c n ls e ρ
  | .ret A, δ, _, hΘ, _, _, _, _, _, _, hs, h => fun lo =>
      erwpK_ret_det hΘ (fun z k v ρ h => vNE_down A η hη δ z.Θ k v ρ h)
        (fun μ => step1Only_of_step1N (hs μ)) (h lo)
  | .arr _ D, δ, Θ, hΘ, _, _, ls, _, _, _, hs, h =>
      fun c' k hk v ρv ρ' hc hv hcon =>
        cBNPE_step hη D δ Θ hΘ c' k ls ρ' _ _ (fun μ => (hs μ).plug (Kont.appL .hole v))
          (h c' k hk v ρv ρ' hc hv hcon)
  | .amp C D, δ, Θ, hΘ, c, n, ls, ρ, _, _, hs, h =>
      ⟨cBNPE_step hη C δ Θ hΘ c n ls ρ _ _ (fun μ => (hs μ).plug (Kont.appL .hole _)) h.1,
        cBNPE_step hη D δ Θ hΘ c n ls ρ _ _ (fun μ => (hs μ).plug (Kont.appL .hole _)) h.2⟩
  | .all x _ D, δ, Θ, hΘ, c, n, ls, ρ, _, _, hs, h =>
      fun α hα => cBNPE_step hη D (δ.extend x α) Θ hΘ c n ls ρ _ _
        (fun μ => (hs μ).plug (Kont.appL .hole _)) (h α hα)
  | .top, _, _, _, _, _, _, _, _, _, _, h | .nu _, _, _, _, _, _, _, _, _, _, _, h
  | .eff _ _ _ _ _ _ _ _, _, _, _, _, _, _, _, _, _, _, h => h

theorem cBNPE_pureSteps {η : Option (Nat → TEntN)} (hη : EnvDownN η) (D : CTy) (δ : LSub)
    {Θ : LocTy} (hΘ : Θ.Down) (c : Loc → Option Life) (n : Nat) (ls : List SRec) (ρ : WRes)
    {e e' : Expr} (h : PureSteps e e') (hw : cBNPE (ℍ := ℍ) η D δ Θ c n ls e' ρ) :
    cBNPE (ℍ := ℍ) η D δ Θ c n ls e ρ := by
  induction h with
  | refl => exact hw
  | tail _ hs ih => exact ih (cBNPE_step hη D δ Θ hΘ c n ls ρ _ _ hs hw)

/-! ### The hardest case: the map and node lemmas over a tuple -/

/-- Where no `Xₖ` occurs, the two readings agree (`vNX_occ` over `n` variables). -/
theorem vNE_envS_noOcc {n : Nat} {Ss Ts : List VTy} (hSn : Ss.length = n) (hTn : Ts.length = n)
    (Vs Ps : Nat → P4) (A : VTy) (hA : ∀ k, k < n → ¬ A.Occ k) :
    vNE (ℍ := ℍ) (envS Ts Ps) A = vNE (ℍ := ℍ) (envS Ss Vs) A :=
  vBN_congr_occ A _ _ (fun k hk => by
    have hkn : n ≤ k := Nat.le_of_not_lt fun h => hA k h hk
    simp [hSn, hTn, Nat.not_lt.mpr hkn]) true

/-- **The map lemma over a system** (`map_okN` per component): `map_A (tupV hs)` takes a value of
`A` with `Xₖ` read at `Vs k` (the states) to one with `Xₖ` read at `Ps k` (the rests), by pure
steps, when the `k`-th handle takes each state of `Vs k` to a rest in `Ps k`. -/
theorem map_okNS (n : Nat) (Ss Ts : List VTy) (hSn : Ss.length = n) (hTn : Ts.length = n)
    (Vs Ps : Nat → P4) (δ : LSub) (kg : Nat) (hs : List Val) (hn : hs.length = n)
    (eta : Nat → Val → Val)
    (hstep : ∀ k a w, k < n → hs[k]? = some a → PureSteps (.app (.val a) (.val w)) (.val (eta k w)))
    (hW : ∀ k Θ j w σ, k < n → j ≤ kg → Vs k Θ j w σ → Ps k Θ j (eta k w) σ) :
    ∀ (A : VTy), PolyN n A → ∀ (Θ : LocTy) (j : Nat), j ≤ kg → ∀ (w : Val) (σ : WRes),
      vNE (ℍ := ℍ) (envS Ss Vs) A δ Θ j w σ →
      ∃ w', PureSteps (.app (.app (.val (mapVS n A)) (.val (tupV hs))) (.val w)) (.val w') ∧
        vNE (ℍ := ℍ) (envS Ts Ps) A δ Θ j w' σ
  | .tvar k, _, Θ, j, hj, w, σ, hw => by
      by_cases hk : k < n
      · obtain ⟨a, ha⟩ : ∃ a, hs[k]? = some a := ⟨hs[k], List.getElem?_eq_getElem (by omega)⟩
        simp only [vNE, envS_tvar (show k < Ss.length by omega)] at hw
        refine ⟨eta k w, (mapVS_var_steps hk hs hn a w ha).trans (hstep k a w hk ha), ?_⟩
        simp only [vNE, envS_tvar (show k < Ts.length by omega)]
        exact hW k Θ j w σ hk hj hw
      · simp [vNE, tEnvPN, envS, hSn, hk, tEnvN] at hw
  | .tensor A B, hP, Θ, j, hj, _, _, hw => by
      obtain ⟨v₁, v₂, σ₁, σ₂, rfl, hc, h₁, h₂⟩ := hw
      obtain ⟨w₁, hs₁, h₁'⟩ := map_okNS n Ss Ts hSn hTn Vs Ps δ kg hs hn eta hstep hW A hP.1 Θ j hj v₁ σ₁ h₁
      obtain ⟨w₂, hs₂, h₂'⟩ := map_okNS n Ss Ts hSn hTn Vs Ps δ kg hs hn eta hstep hW B hP.2 Θ j hj v₂ σ₂ h₂
      exact ⟨.pair w₁ w₂, (mapVS_tensor_steps n A B _ v₁ v₂).trans (pair_steps hs₁ hs₂),
        w₁, w₂, σ₁, σ₂, rfl, hc, h₁', h₂'⟩
  | .sum A B, hP, Θ, j, hj, _, σ, hw => by
      rcases hw with ⟨v, rfl, h⟩ | ⟨v, rfl, h⟩
      · obtain ⟨w', hs', h'⟩ := map_okNS n Ss Ts hSn hTn Vs Ps δ kg hs hn eta hstep hW A hP.1 Θ j hj v σ h
        exact ⟨.inj₁ w', (mapVS_sum₁_steps n A B _ v).trans (inj₁_steps hs'), Or.inl ⟨w', rfl, h'⟩⟩
      · obtain ⟨w', hs', h'⟩ := map_okNS n Ss Ts hSn hTn Vs Ps δ kg hs hn eta hstep hW B hP.2 Θ j hj v σ h
        exact ⟨.inj₂ w', (mapVS_sum₂_steps n A B _ v).trans (inj₂_steps hs'), Or.inr ⟨w', rfl, h'⟩⟩
  | .box _ A, hP, Θ, j, hj, w, σ, hw => by
      obtain ⟨α, hα, hb, ho⟩ := hw
      obtain ⟨w', hs', h'⟩ := map_okNS n Ss Ts hSn hTn Vs Ps δ kg hs hn eta hstep hW A hP Θ j hj w σ hb
      exact ⟨w', hs', α, hα, h', ho⟩
  | .unit, hP, _, _, _, w, _, hw | .zero, hP, _, _, _, w, _, hw | .thunk _, hP, _, _, _, w, _, hw
  | .code _ _ _, hP, _, _, _, w, _, hw
  | .ref _, hP, _, _, _, w, _, hw | .imm _ _, hP, _, _, _, w, _, hw
  | .mut _ _, hP, _, _, _, w, _, hw | .bang _, hP, _, _, _, w, _, hw
  | .unk, hP, _, _, _, w, _, hw | .mu _, hP, _, _, _, w, _, hw | .int _, hP, _, _, _, w, _, hw
  | .opq _, hP, _, _, _, w, _, hw | .fam _, hP, _, _, _, w, _, hw =>
      ⟨w, mapVS_id_steps rfl _ w, by rw [vNE_envS_noOcc hSn hTn Vs Ps _ hP]; exact hw⟩

/-- **The node lemma over a system** (`node_okP` per component): when `c ()` runs a computation
whose answers read `Xₖ` at the states `Vs k`, `node_D (tupV hs) c` is one unfolding of `D` with
`Xₖ` read at `Ps k`.  Both readings are fixed, so the tree under a `∀` leaf is read at the
extended `δ` with the same tuples. -/
theorem node_okPS (n : Nat) (Ss Ts : List VTy) (hSn : Ss.length = n) (hTn : Ts.length = n)
    (Vs Ps : Nat → P4) (hPd : ∀ k Θ j v ρ, Ps k Θ (j + 1) v ρ → Ps k Θ j v ρ) (kg : Nat)
    (hs : List Val) (hn : hs.length = n) (eta : Nat → Val → Val)
    (hstep : ∀ k a w, k < n → hs[k]? = some a → PureSteps (.app (.val a) (.val w)) (.val (eta k w)))
    (hW : ∀ k Θ j w σ, k < n → j ≤ kg → Vs k Θ j w σ → Ps k Θ j (eta k w) σ) :
    ∀ (D : CTy), NuLeafS n D → ∀ (δ : LSub) (Θ : LocTy), Θ.OK → ∀ (c : Loc → Option Life)
      (j : Nat), j ≤ kg → ∀ (cv : Val) (M : Expr) (ls : List SRec) (ρ : WRes),
      PureSteps (.app (.val cv) (.val .unit)) M → cBNPE (ℍ := ℍ) (envS Ss Vs) D δ Θ c j ls M ρ →
      cBNPE (ℍ := ℍ) (envS Ts Ps) D δ Θ c j ls
        (.app (.app (.val (nodeVS n D)) (.val (tupV hs))) (.val cv)) ρ
  | .ret A, hA, δ, Θ, hΘ, c, j, hj, cv, M, ls, ρ, hc, hM => fun lo => by
      have hΦ : ∀ z : KW, z.Θ.OK → (z.Θ.view z.c).Down := fun z hz => LocTy.view_down hz.1 z.c
      have hDI : ∀ z : KW, (OpTabK.empty : OpTabK KW).DownI (fun z : KW => z.Θ.OK) :=
        fun _ => OpTabK.empty_downI _
      have hTd : (opTableK lo (OpTabK.empty : OpTabK KW)).Down := opTableK_downI (hDI ⟨Θ, c, lo⟩)
      have hQd : ∀ y : KW, PostN.Down (fun k _ v ρ => vNE (ℍ := ℍ) (envS Ts Ps) A δ y.Θ k v ρ) :=
        fun y k _ v ρ h => vNE_down A _ (envS_down hPd) δ y.Θ k v ρ h
      refine erwpK_pureSteps (x := (⟨Θ, c, lo⟩ : KW)) (hΦ _ hΘ) hTd hQd
        (nodeVS_ret_steps n A _ cv) ?_
      refine erwpK_pureSteps (x := (⟨Θ, c, lo⟩ : KW)) (hΦ _ hΘ) hTd hQd
        (PureSteps.plug (.appR (.val (.lam _)) .hole) hc) ?_
      refine erwpK_bind_leI (V := KW.PostK) (fun _ _ _ h₁ h₂ => KW.PostK.trans h₁ h₂)
        (Φ := fun z : KW => z.Θ.view z.c) (Inv := fun z : KW => z.Θ.OK) hΦ
        (fun _ _ h => by rw [h]) (fun _ _ h hx => by rw [h]; exact hx) (fl := fun z : KW => z.lo)
        (T := fun _ => OpTabK.empty)
        (fun _ _ h => tabLe_postK (fun z : KW => opTableK z.lo (OpTabK.empty : OpTabK KW)) h)
        (Q' := fun z k _ v ρ => vNE (ℍ := ℍ) (envS Ss Vs) A δ z.Θ k v ρ)
        (.appR (.val (.lam _)) .hole) (fun _ => by simp [Kont.HasHnd])
        (fun _ => by simp [Kont.Catches]) (fun _ _ _ _ _ h => by cases h)
        (fun _ _ _ _ h => by cases h) kg ?_ j hj (⟨Θ, c, lo⟩ : KW) hΘ ls M ρ (hM lo)
      rintro y hy k ls' w σ hk hw
      obtain ⟨w', hs', h'⟩ := map_okNS n Ss Ts hSn hTn Vs Ps δ kg hs hn eta hstep hW A hA y.Θ k hk w σ hw
      have hTy : (opTableK y.lo (OpTabK.empty : OpTabK KW)).Down := opTableK_downI (hDI y)
      refine erwpK_det (x := y) (Φ := fun z : KW => z.Θ.view z.c) (hΦ y hy) hTy hQd
        (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
      have e : Expr.subst 0 w (.app (.app (.val (mapVS n A)) (.val ((tupV hs).shift 1 0))) (.var 0))
          = .app (.app (.val (mapVS n A)) (.val (tupV hs))) (.val w) := by
        simp [Expr.subst, Val.val_shift, Expr.shift_zero, closed_subst (mapVS_closed n A),
          subst_shift_succ]
      simp only [Kont.plug]
      rw [e]
      exact erwpK_pureSteps (x := y) (Φ := fun z : KW => z.Θ.view z.c) (hΦ y hy) hTy hQd hs'
        (erwpK_val (KW.postK_refl y) h')
  | .amp D₁ D₂, hD, δ, Θ, hΘ, c, j, hj, cv, M, ls, ρ, hc, hM =>
      ⟨cBNPE_pureSteps (envS_down hPd) D₁ δ hΘ.1 c j ls ρ (nodeVS_amp₁_steps n D₁ D₂ _ cv)
        (node_okPS n Ss Ts hSn hTn Vs Ps hPd kg hs hn eta hstep hW D₁ hD.1 δ Θ hΘ c j hj _
          (.app M (.val (.inj₁ .unit))) ls ρ
          ((childV_steps cv _ rfl).trans (PureSteps.plug (.appL .hole _) hc)) hM.1),
       cBNPE_pureSteps (envS_down hPd) D₂ δ hΘ.1 c j ls ρ (nodeVS_amp₂_steps n D₁ D₂ _ cv)
        (node_okPS n Ss Ts hSn hTn Vs Ps hPd kg hs hn eta hstep hW D₂ hD.2 δ Θ hΘ c j hj _
          (.app M (.val (.inj₂ .unit))) ls ρ
          ((childV_steps cv _ rfl).trans (PureSteps.plug (.appL .hole _) hc)) hM.2)⟩
  | .arr A D, hD, δ, Θ, hΘ, _, j, hj, cv, M, ls, _, hc, hM =>
      fun c' k hk v ρv ρ' hcomp hv hcon =>
        cBNPE_pureSteps (envS_down hPd) D δ hΘ.1 c' k ls ρ' (nodeVS_arr_steps n A D _ cv v)
          (node_okPS n Ss Ts hSn hTn Vs Ps hPd kg hs hn eta hstep hW D hD.2 δ Θ hΘ c' k
            (le_trans hk hj) (childA cv v) (.app M (.val v)) ls ρ'
            ((childA_steps cv v).trans (PureSteps.plug (.appL .hole _) hc))
            (hM c' k hk v ρv ρ' hcomp hv hcon))
  | .all x b D, hD, δ, Θ, hΘ, c, j, hj, cv, M, ls, ρ, hc, hM => fun α hα =>
      cBNPE_pureSteps (envS_down hPd) D _ hΘ.1 c j ls ρ (nodeVS_all_steps n x b D _ cv)
        (node_okPS n Ss Ts hSn hTn Vs Ps hPd kg hs hn eta hstep hW D hD (δ.extend x α) Θ hΘ c j hj
          (childA cv .unit) (.app M (.val .unit)) ls ρ
          ((childA_steps cv .unit).trans (PureSteps.plug (.appL .hole _) hc)) (hM α hα))
  | .top, hD, _, _, _, _, _, _, _, _, _, _, _, _ | .nu _, hD, _, _, _, _, _, _, _, _, _, _, _, _
  | .eff _ _ _ _ _ _ _ _, hD, _, _, _, _, _, _, _, _, _, _, _, _ => hD.elim

/-! ### The lexer system's bodies (`scope.md` §6) -/

/-- `Normal = F((1 ⊗ U X₀) ⊕ (U X₁ ⊕ 1)) & F 1`, `InString = F((1 ⊗ U X₁) ⊕ U X₀) & F 1`. -/
abbrev lexNormal : CTy :=
  .amp (.ret (.sum (.tensor .unit (.tvar 0)) (.sum (.tvar 1) .unit))) (.ret .unit)
abbrev lexInString : CTy := .amp (.ret (.sum (.tensor .unit (.tvar 1)) (.tvar 0))) (.ret .unit)

example : NuLeafS 2 lexNormal ∧ NuLeafS 2 lexInString := by
  refine ⟨⟨⟨⟨fun k _ h => h, trivial⟩, trivial, fun k _ h => h⟩, fun k _ h => h⟩,
    ⟨⟨⟨fun k _ h => h, trivial⟩, trivial⟩, fun k _ h => h⟩⟩

end MutualNu.P1

end

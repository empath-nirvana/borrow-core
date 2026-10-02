import FnMut.Core.FoldImm
import FnMut.Core.NuRel
import FnMut.Core.EffRules

/-!
# Core — coiteration on `νX. C`  `[spec §7]`

`νX. C` (`cC`'s `nu` clause, `NuRel.lean`) is observed by projections down its `&`-tree of
observations `F A`; `U X` in an `A` is the rest of the codata.

**The rule.** `unfold : !U(S ⊸ C[S/X]) ⊸ !U(S ⊸ νX. C)` at every positive `C` (`CTy.NuOk`:
a `&` of observation trees whose results are polynomial in `X`).  `unfold step s` is the fixed point

    f = λs. node_C (λs′. f s′) (λ_. step s)

where `node_C wr c` answers an observation path of `C` by running the same path of the step
(`c` runs the step's computation at the node, `childV`) and mapping each state `s′` in the
result to the rest `f s′` (`mapV`, applied with `wr`).  The recursive handle `f` occurs only
in the rest, applied to the next state; the step returns states, never a `νX. C`.  The
recursion is the rule's: the Z combinator (`Fix.lean`) over `fBN C`.

**Soundness** (`unfold_compatX`) is coinduction at the greatest fixed point, with the candidate
`{unfold step s | s ∈ 𝒱⟦S⟧}` (`candN`, `candN_post`).  It uses no approximation of `νX. C` and no
index.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Types -/

/-- `unfold`'s type, `!U(S ⊸ C[S/X]) ⊸ !U(S ⊸ νX. C)`. -/
abbrev unfoldTy (C : CTy) (S : VTy) : VTy :=
  .lolli (.bang (.thunk (.arr S (C.instT S)))) (.bang (.thunk (.arr S (.nu C))))

/-! ### The terms -/

/-- `map_A wr w`: `w` with every state `s` at an `X` position of `A` replaced by `wr s`.  At
`X` `wr w`; at `⊗` and `⊕` componentwise; elsewhere `w`. -/
def mapV : VTy → Val
  | .tvar 0 => .lam (.val (.lam (.app (.var 1) (.var 0))))
  | .tensor A B => .lam (.val (.lam (.letpair (.var 0)
      (.pair (.app (.app (.val (mapV A)) (.var 3)) (.var 1))
        (.app (.app (.val (mapV B)) (.var 3)) (.var 0))))))
  | .sum A B => .lam (.val (.lam (.case (.var 0)
      (.inj₁ (.app (.app (.val (mapV A)) (.var 2)) (.var 0)))
      (.inj₂ (.app (.app (.val (mapV B)) (.var 2)) (.var 0))))))
  | _ => .lam (.val (.lam (.var 0)))

theorem mapV_closed : ∀ A : VTy, closedAt 0 (mapV A).1 = true
  | .tvar 0 => rfl
  | .tensor A B => by
      simp [mapV, closedAt, closedAt_mono _ (mapV_closed A) (Nat.zero_le _),
        closedAt_mono _ (mapV_closed B) (Nat.zero_le _)]
  | .sum A B => by
      simp [mapV, closedAt, closedAt_mono _ (mapV_closed A) (Nat.zero_le _),
        closedAt_mono _ (mapV_closed B) (Nat.zero_le _)]
  | .tvar (_ + 1) | .unit | .zero | .thunk _ | .ref _ | .imm _ _ | .mut _ _ | .box _ _
  | .bang _ | .unk | .mu _ | .int _ | .opq _ | .fam _ => rfl

/-- `λ_. c () o`: the step's computation at the child `o` of the node `c` runs. -/
def childV (c o : Val) : Val := .lam (.app (.app (.val (c.shift 1 0)) (.val .unit)) (.val o))

/-- The answer type of an effectful observation `F_Σ A`: `A`.  `[spec §19]` -/
def effAns : CTy → VTy
  | .ret A => A
  | .eff _ _ _ _ _ C => effAns C
  | _ => .unit

/-- `node_C wr c`: the answer of the observation tree `C` to its observations, with `c ()` the
step's computation at the node.  At `F A` and `F_Σ A`: run `c ()` and map its result with `wr`.
At `C & D`:
`λo. case o {inj₁ _. node_C wr (childV c (inj₁ ())) | inj₂ _. node_D wr (childV c (inj₂ ()))}`. -/
def nodeV : CTy → Val
  | .ret A => .lam (.val (.lam
      (bindE (.app (.var 0) (.val .unit)) (.app (.app (.val (mapV A)) (.var 2)) (.var 0)))))
  | .eff _ _ _ _ _ C => .lam (.val (.lam
      (bindE (.app (.var 0) (.val .unit)) (.app (.app (.val (mapV (effAns C))) (.var 2)) (.var 0)))))
  | .amp C D => .lam (.val (.lam (.val (.lam (.case (.var 0)
      (.app (.app (.val (nodeV C)) (.var 3))
        (.val (.lam (.app (.app (.var 3) (.val .unit)) (.val (.inj₁ .unit))))))
      (.app (.app (.val (nodeV D)) (.var 3))
        (.val (.lam (.app (.app (.var 3) (.val .unit)) (.val (.inj₂ .unit)))))))))))
  | _ => .lam (.val (.lam (.val .unit)))

theorem nodeV_closed : ∀ C : CTy, closedAt 0 (nodeV C).1 = true
  | .ret A => by simp [nodeV, bindE, closedAt, closedAt_mono _ (mapV_closed A) (Nat.zero_le _)]
  | .amp C D => by
      simp [nodeV, closedAt, closedAt_mono _ (nodeV_closed C) (Nat.zero_le _),
        closedAt_mono _ (nodeV_closed D) (Nat.zero_le _)]
  | .eff _ _ _ _ _ C => by
      simp [nodeV, bindE, closedAt, closedAt_mono _ (mapV_closed (effAns C)) (Nat.zero_le _)]
  | .arr _ _ | .top | .all _ _ _ | .nu _ => rfl

/-- The body of `unfold_C = Z (λself. λg. λs. node_C (λs′. λo. self g s′ o) (λ_. g s))`. -/
def fBN (C : CTy) : Expr :=
  .val (.lam (.app (.app (.val (nodeV C))
    (.val (.lam (.val (.lam (.app (.app (.app (.var 4) (.var 3)) (.var 1)) (.var 0)))))))
    (.val (.lam (.app (.var 2) (.var 1))))))

theorem fBN_closed (C : CTy) : closedAt 2 (fBN C) = true := by
  simp [fBN, closedAt, closedAt_mono _ (nodeV_closed C) (Nat.zero_le _)]

/-- The recursive handle. -/
abbrev selfNu (C : CTy) : Val := selfV (fBN C)

theorem selfNu_closed (C : CTy) : closedAt 0 (selfNu C).1 = true := selfV_closed (fBN_closed C)

/-- `λo. self g s o`: the codata `unfold step s`, at `g = step`. -/
def etaN (C : CTy) (g s : Val) : Val :=
  .lam (.app (.app (.app (.val (selfNu C)) (.val (g.shift 1 0))) (.val (s.shift 1 0))) (.var 0))

/-- `λs. λo. self g s o`: `unfold step`, at `g = step`. -/
def hN (C : CTy) (g : Val) : Val :=
  .lam (.val (.lam (.app (.app (.app (.val (selfNu C)) (.val (g.shift 2 0))) (.var 1)) (.var 0))))

/-- `λ_. g s`: the step's computation at the root. -/
def rootV (g s : Val) : Val := .lam (.app (.val (g.shift 1 0)) (.val (s.shift 1 0)))

/-- **`unfold_C = λg. λs. λo. self g s o`**, a closed value. -/
def unfoldV (C : CTy) : Val :=
  .lam (.val (.lam (.val (.lam (.app (.app (.app (.val (selfNu C)) (.var 2)) (.var 1)) (.var 0))))))

theorem unfoldV_closed (C : CTy) : closedAt 0 (unfoldV C).1 = true := by
  simp [unfoldV, closedAt, closedAt_mono _ (selfNu_closed C) (Nat.zero_le _)]

/-! ### Reduction -/

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

theorem unfoldV_subst (C : CTy) (g : Val) :
    Expr.subst 0 g (.val (.lam (.val (.lam (.app (.app (.app (.val (selfNu C)) (.var 2)) (.var 1))
      (.var 0)))))) = .val (hN C g) := by
  simp [hN, closed_subst (selfNu_closed C)]

theorem hN_subst (C : CTy) (g s : Val) :
    Expr.subst 0 s (.val (.lam (.app (.app (.app (.val (selfNu C)) (.val (g.shift 2 0))) (.var 1))
      (.var 0)))) = .val (etaN C g s) := by
  simp [etaN, closed_subst (selfNu_closed C), subst_shift_succ]

/-- `wr s ↦ unfold step s`. -/
theorem hN_steps (C : CTy) (g s : Val) :
    PureSteps (.app (.val (hN C g)) (.val s)) (.val (etaN C g s)) := by
  have := PureSteps.beta (.val (.lam (.app (.app (.app (.val (selfNu C)) (.val (g.shift 2 0)))
    (.var 1)) (.var 0)))) s
  rwa [hN_subst] at this

/-- An observation `o` of `unfold step s` reaches `node_C (unfold step) (λ_. step s) o`. -/
theorem etaN_obs (C : CTy) (g s o : Val) :
    PureSteps (.app (.val (etaN C g s)) (.val o))
      (.app (.app (.app (.val (nodeV C)) (.val (hN C g))) (.val (rootV g s))) (.val o)) := by
  refine (PureSteps.beta _ o).trans ?_
  have e₁ : Expr.subst 0 o (.app (.app (.app (.val (selfNu C)) (.val (g.shift 1 0)))
      (.val (s.shift 1 0))) (.var 0))
      = (Kont.appL (Kont.appL .hole s) o).plug (.app (.val (selfNu C)) (.val g)) := by
    simp [Kont.plug, closed_subst (selfNu_closed C), subst_shift_succ]
  rw [e₁]
  refine (selfV_steps_in (fBN_closed C) _ g).trans ?_
  rw [fixV_eq (fBN_closed C)]
  refine (PureSteps.beta_in (.appL (.appL .hole s) o) _ g).trans ?_
  refine (PureSteps.beta_in (.appL .hole o) _ s).trans ?_
  have hc := selfNu_closed C
  simp only [hN, selfNu] at hc ⊢
  generalize selfV (fBN C) = σ at hc ⊢
  simp [Kont.plug, rootV, closed_subst (nodeV_closed C), closed_subst hc, closed_shift hc,
    subst_shift_succ]
  exact .refl

/-- `map_X wr s ↦ wr s`. -/
theorem mapV_var_steps (wr w : Val) :
    PureSteps (.app (.app (.val (mapV (.tvar 0))) (.val wr)) (.val w)) (.app (.val wr) (.val w)) := by
  refine (PureSteps.beta_in (.appL .hole w) _ wr).trans ?_
  refine (PureSteps.beta _ w).trans ?_
  simp [subst_shift_succ]
  exact .refl

/-- `map_A wr w ↦ w` where `A` has no `X` at a `⊗`/`⊕` position. -/
theorem mapV_id_steps {A : VTy} (hA : mapV A = .lam (.val (.lam (.var 0)))) (wr w : Val) :
    PureSteps (.app (.app (.val (mapV A)) (.val wr)) (.val w)) (.val w) := by
  rw [hA]
  refine (PureSteps.beta_in (.appL .hole w) _ wr).trans ?_
  refine (PureSteps.beta _ w).trans ?_
  simp
  exact .refl

theorem mapV_tensor_steps (A B : VTy) (wr v₁ v₂ : Val) :
    PureSteps (.app (.app (.val (mapV (.tensor A B))) (.val wr)) (.val (.pair v₁ v₂)))
      (.pair (.app (.app (.val (mapV A)) (.val wr)) (.val v₁))
        (.app (.app (.val (mapV B)) (.val wr)) (.val v₂))) := by
  refine (PureSteps.beta_in (.appL .hole _) _ wr).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.letpair μ v₁ v₂ _) rfl).trans ?_
  simp [closed_subst (mapV_closed A), closed_subst (mapV_closed B), subst_shift_succ]
  exact .refl

theorem mapV_sum₁_steps (A B : VTy) (wr v : Val) :
    PureSteps (.app (.app (.val (mapV (.sum A B))) (.val wr)) (.val (.inj₁ v)))
      (.inj₁ (.app (.app (.val (mapV A)) (.val wr)) (.val v))) := by
  refine (PureSteps.beta_in (.appL .hole _) _ wr).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₁ μ v _ _) rfl).trans ?_
  simp [closed_subst (mapV_closed A), subst_shift_succ]
  exact .refl

theorem mapV_sum₂_steps (A B : VTy) (wr v : Val) :
    PureSteps (.app (.app (.val (mapV (.sum A B))) (.val wr)) (.val (.inj₂ v)))
      (.inj₂ (.app (.app (.val (mapV B)) (.val wr)) (.val v))) := by
  refine (PureSteps.beta_in (.appL .hole _) _ wr).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₂ μ v _ _) rfl).trans ?_
  simp [closed_subst (mapV_closed B), subst_shift_succ]
  exact .refl

theorem pair_steps {e₁ e₂ : Expr} {v₁ v₂ : Val} (h₁ : PureSteps e₁ (.val v₁))
    (h₂ : PureSteps e₂ (.val v₂)) : PureSteps (.pair e₁ e₂) (.val (.pair v₁ v₂)) :=
  (PureSteps.plug (.pairL .hole e₂) h₁).trans (PureSteps.plug (.pairR v₁ .hole) h₂)

theorem inj₁_steps {e : Expr} {v : Val} (h : PureSteps e (.val v)) :
    PureSteps (.inj₁ e) (.val (.inj₁ v)) :=
  PureSteps.plug (.inj₁ .hole) h

theorem inj₂_steps {e : Expr} {v : Val} (h : PureSteps e (.val v)) :
    PureSteps (.inj₂ e) (.val (.inj₂ v)) :=
  PureSteps.plug (.inj₂ .hole) h

/-- `node_{F A} wr c ↦ c () to w. map_A wr w`. -/
theorem nodeV_ret_steps (A : VTy) (wr c : Val) :
    PureSteps (.app (.app (.val (nodeV (.ret A))) (.val wr)) (.val c))
      (bindE (.app (.val c) (.val .unit)) (.app (.app (.val (mapV A)) (.val (wr.shift 1 0)))
        (.var 0))) := by
  refine (PureSteps.beta_in (.appL .hole _) _ wr).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  simp [bindE, closed_subst (mapV_closed A), subst_shift_succ]
  exact .refl

/-- `node_{F_Σ A} wr c ↦ c () to w. map_A wr w`. -/
theorem nodeV_eff_steps (n i : UInt32) (q : Qual) (A B : VTy) (C : CTy) (wr c : Val) :
    PureSteps (.app (.app (.val (nodeV (.eff n i q A B C))) (.val wr)) (.val c))
      (bindE (.app (.val c) (.val .unit)) (.app (.app (.val (mapV (effAns C)))
        (.val (wr.shift 1 0))) (.var 0))) := by
  refine (PureSteps.beta_in (.appL .hole _) _ wr).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  simp [bindE, closed_subst (mapV_closed (effAns C)), subst_shift_succ]
  exact .refl

/-- `node_{C & D} wr c (inj₁ ()) ↦ node_C wr (childV c (inj₁ ()))`. -/
theorem nodeV_amp₁_steps (C D : CTy) (wr c : Val) :
    PureSteps (.app (.app (.app (.val (nodeV (.amp C D))) (.val wr)) (.val c)) (.val (.inj₁ .unit)))
      (.app (.app (.val (nodeV C)) (.val wr)) (.val (childV c (.inj₁ .unit)))) := by
  refine (PureSteps.beta_in (.appL (.appL .hole _) _) _ wr).trans ?_
  refine (PureSteps.beta_in (.appL .hole _) _ _).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₁ μ _ _ _) rfl).trans ?_
  simp [childV, closed_subst (nodeV_closed C), subst_shift_succ]
  exact .refl

/-- `node_{C & D} wr c (inj₂ ()) ↦ node_D wr (childV c (inj₂ ()))`. -/
theorem nodeV_amp₂_steps (C D : CTy) (wr c : Val) :
    PureSteps (.app (.app (.app (.val (nodeV (.amp C D))) (.val wr)) (.val c)) (.val (.inj₂ .unit)))
      (.app (.app (.val (nodeV D)) (.val wr)) (.val (childV c (.inj₂ .unit)))) := by
  refine (PureSteps.beta_in (.appL (.appL .hole _) _) _ wr).trans ?_
  refine (PureSteps.beta_in (.appL .hole _) _ _).trans ?_
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.case₂ μ _ _ _) rfl).trans ?_
  simp [childV, closed_subst (nodeV_closed D), subst_shift_succ]
  exact .refl

theorem childV_steps (c o : Val) (ho : closedAt 0 o.1 = true) :
    PureSteps (.app (.val (childV c o)) (.val .unit)) (.app (.app (.val c) (.val .unit)) (.val o)) := by
  refine (PureSteps.beta _ _).trans ?_
  simp [subst_shift_succ, closed_subst ho]
  exact .refl

theorem rootV_steps (g s : Val) :
    PureSteps (.app (.val (rootV g s)) (.val .unit)) (.app (.val g) (.val s)) := by
  refine (PureSteps.beta _ _).trans ?_
  simp [subst_shift_succ]
  exact .refl

theorem cB_pureSteps (η : Option (Nat → TEnt)) (C : CTy) {e e' : Expr} (h : PureSteps e e')
    (ls : List SRec) (δ : LSub) : Entails (cB η C ls δ e') (cB η C ls δ e) := by
  induction h with
  | refl => exact fun _ h => h
  | tail _ hs ih => exact fun ρ h => ih ρ (cB_step η C hs ls δ ρ h)

/-! ### Soundness -/

/-- The environment of `A[S/X]`: the variable `0` is `S`. -/
def envS (S : VTy) (δ : LSub) : Nat → TEnt := VTy.scons ⟨S, fun b ls => vC b S ls δ⟩ tNil

theorem vC_inst_envS (S A : VTy) (δ : LSub) (b : Bool) (ls : List SRec) :
    vC b (VTy.inst S A) ls δ = vCE (some (envS S δ)) b A ls δ := by
  rw [vC_eq_some, VTy.inst, vCE_subst]
  congr 2
  funext n
  cases n with
  | zero =>
      refine TEnt.ext' (VTy.subst_id S) ?_
      funext b ls
      show vCE (some tNil) b S ls δ = vCE none b S ls δ
      rw [← vC_eq_some]
  | succ n => rfl

/-- The candidate: the codata `unfold step s` at a state `s ∈ 𝒱⟦S⟧`. -/
def candN (C : CTy) (g : Val) (S : VTy) (δ : LSub) : CPred := fun ls e ρ =>
  ∃ s, e = .val (etaN C g s) ∧ vC true S ls δ s ρ

/-- At a type without `X`, the two environments agree. -/
theorem vCE_envS_nuEnv {A : VTy} (hA : ¬ A.Occ 0) (S : VTy) (δ : LSub) (C : CTy) (R : CPred)
    (b : Bool) : vCE (some (envS S δ)) b A = vCE (some (nuEnv C R)) b A :=
  vCE_congr_occ A _ _ (fun n hn => by
    cases n with
    | zero => exact absurd hn hA
    | succ n => rfl) b

/-- **The map lemma**: `map_A (unfold step)` takes a value of `A[S/X]` to one of
`A[U(νX. C)/X]` at the candidate, on the same resource, by pure steps. -/
theorem map_ok (C : CTy) (g : Val) (S : VTy) (δ : LSub) :
    ∀ (A : VTy), A.Poly → ∀ (ls : List SRec) (w : Val) (σ : WRes),
      vCE (some (envS S δ)) true A ls δ w σ →
      ∃ w', PureSteps (.app (.app (.val (mapV A)) (.val (hN C g))) (.val w)) (.val w') ∧
        vCE (some (nuEnv C (candN C g S δ))) true A ls δ w' σ
  | .tvar 0, _, _, w, _, hw =>
      ⟨etaN C g w, (mapV_var_steps _ w).trans (hN_steps C g w),
        fun _ hk => ⟨w, rfl, vC_local true S hk hw⟩⟩
  | .tvar (_ + 1), _, _, _, _, hw => hw.elim
  | .tensor A B, hP, ls, _, _, hw => by
      obtain ⟨v₁, v₂, σ₀, σ₃, hc, ⟨hσ₀, rfl⟩, σ₁, σ₂, hc', h₁, h₂⟩ := hw
      obtain ⟨w₁, hs₁, h₁'⟩ := map_ok C g S δ A hP.1 ls v₁ σ₁ h₁
      obtain ⟨w₂, hs₂, h₂'⟩ := map_ok C g S δ B hP.2 ls v₂ σ₂ h₂
      exact ⟨.pair w₁ w₂, (mapV_tensor_steps A B _ v₁ v₂).trans (pair_steps hs₁ hs₂),
        w₁, w₂, σ₀, σ₃, hc, ⟨hσ₀, rfl⟩, σ₁, σ₂, hc', h₁', h₂'⟩
  | .sum A B, hP, ls, _, _, hw => by
      rcases hw with ⟨v, σ₀, σ₃, hc, ⟨hσ₀, rfl⟩, h⟩ | ⟨v, σ₀, σ₃, hc, ⟨hσ₀, rfl⟩, h⟩
      · obtain ⟨w', hs, h'⟩ := map_ok C g S δ A hP.1 ls v σ₃ h
        exact ⟨.inj₁ w', (mapV_sum₁_steps A B _ v).trans (inj₁_steps hs),
          Or.inl ⟨w', σ₀, σ₃, hc, ⟨hσ₀, rfl⟩, h'⟩⟩
      · obtain ⟨w', hs, h'⟩ := map_ok C g S δ B hP.2 ls v σ₃ h
        exact ⟨.inj₂ w', (mapV_sum₂_steps A B _ v).trans (inj₂_steps hs),
          Or.inr ⟨w', σ₀, σ₃, hc, ⟨hσ₀, rfl⟩, h'⟩⟩
  | .unit, hP, _, w, _, hw | .zero, hP, _, w, _, hw | .thunk _, hP, _, w, _, hw
  | .ref _, hP, _, w, _, hw | .imm _ _, hP, _, w, _, hw | .mut _ _, hP, _, w, _, hw
  | .box _ _, hP, _, w, _, hw | .bang _, hP, _, w, _, hw | .unk, hP, _, w, _, hw
  | .mu _, hP, _, w, _, hw | .int _, hP, _, w, _, hw | .opq _, hP, _, w, _, hw
  | .fam _, hP, _, w, _, hw =>
      ⟨w, mapV_id_steps rfl _ w, by rw [← vCE_envS_nuEnv hP]; exact hw⟩

/-- Pure steps in front of an `ewpTS`. -/
theorem ewp_pureSteps {Tb : Table} (hTb : Tb.Mono) {e e' : Expr} (h : PureSteps e e')
    (ls : List SRec) (Q : List SRec → Val → WProp) : Entails (ewpTS ls e' Tb Q) (ewpTS ls e Tb Q) := by
  induction h with
  | refl => exact fun _ h => h
  | tail _ hs ih => exact fun ρ h => ih ρ (ewp_step hTb hs ls Q ρ h)

theorem EffLeaf.ans_poly : ∀ {C : CTy}, C.EffLeaf → (effAns C).Poly
  | .ret _, h => h
  | .eff _ _ _ _ _ C, h => EffLeaf.ans_poly (C := C) h.2.2

theorem effRetE_ans (η : Option (Nat → TEnt)) (δ : LSub) : ∀ {C : CTy}, C.EffLeaf →
    effRetE η C δ = fun ls v => vCE η true (effAns C) ls δ v
  | .ret _, _ => rfl
  | .eff _ _ _ _ _ C, h => effRetE_ans η δ (C := C) h.2.2

theorem effRet_instT_ans (S : VTy) (δ : LSub) : ∀ {C : CTy}, C.EffLeaf →
    effRet (C.instT S) δ = fun ls v => vC true (VTy.inst S (effAns C)) ls δ v
  | .ret _, _ => rfl
  | .eff _ _ _ _ _ C, h => effRet_instT_ans S δ (C := C) h.2.2

/-- **The node lemma**: when `c ()` runs a computation of `D[S/X]`, `node_D (unfold step) c` is
one unfolding of `D` at the candidate. -/
theorem node_ok (C : CTy) (g : Val) (S : VTy) (δ : LSub) :
    ∀ (D : CTy), D.NuLeaf → ∀ (c : Val) (M : Expr) (ls : List SRec) (ρ : WRes),
      PureSteps (.app (.val c) (.val .unit)) M → cC (D.instT S) ls δ M ρ →
      cB (some (nuEnv C (candN C g S δ))) D ls δ
        (.app (.app (.val (nodeV D)) (.val (hN C g))) (.val c)) ρ
  | .ret A, hA, c, M, ls, ρ, hc, hM => by
      show wpTS ls _ _ ρ
      refine wpTS_pureSteps (nodeV_ret_steps A _ c) ls _ ρ ?_
      refine wpTS_pureSteps (PureSteps.plug (.appR (.val (.lam _)) .hole) hc) ls _ ρ ?_
      refine wpTS_bind (.appR (.val (.lam _)) .hole) M ls _ ρ ?_
      refine wpTS_mono (fun ls' w σ hw => ?_) ρ hM
      rw [vC_inst_envS] at hw
      obtain ⟨w', hs, h'⟩ := map_ok C g S δ A hA ls' w σ hw
      refine wpTS_lolli ls' _ w _ σ ?_
      have e : Expr.subst 0 w (.app (.app (.val (mapV A)) (.val ((hN C g).shift 1 0))) (.var 0))
          = .app (.app (.val (mapV A)) (.val (hN C g))) (.val w) := by
        simp [closed_subst (mapV_closed A), subst_shift_succ]
      rw [e]
      exact wpTS_pureSteps hs ls' _ σ (wpTS_val ls' w' _ σ h')
  | .amp D₁ D₂, hD, c, M, ls, ρ, hc, hM =>
      ⟨cB_pureSteps _ D₁ (nodeV_amp₁_steps D₁ D₂ _ c) ls δ ρ
        (node_ok C g S δ D₁ hD.1 _ (.app M (.val (.inj₁ .unit))) ls ρ
          ((childV_steps c _ rfl).trans (PureSteps.plug (.appL .hole _) hc)) hM.1),
       cB_pureSteps _ D₂ (nodeV_amp₂_steps D₁ D₂ _ c) ls δ ρ
        (node_ok C g S δ D₂ hD.2 _ (.app M (.val (.inj₂ .unit))) ls ρ
          ((childV_steps c _ rfl).trans (PureSteps.plug (.appL .hole _) hc)) hM.2)⟩
  | .eff n i q A B D, hD, c, M, ls, ρ, hc, hM => by
      have hR := EffLeaf.ans_poly (C := D) hD.2.2
      show ewpTS ls _ _ (effRetE _ D δ) ρ
      have hM' : ewpTS ls M (opTable (OpTab.ext n i
          ⟨q, B.isZero && q != .lin, fun ls v => vC true A ls δ v, fun ls v => vC true B ls δ v⟩
            (effTab D δ))) (fun ls v => vC true (VTy.inst S (effAns D)) ls δ v) ρ := by
        have h' := hM
        simp only [CTy.instT, cC, effTab_instT, effRet_instT_ans S δ hD.2.2] at h'
        exact h'
      rw [effRetE_ans _ δ hD.2.2]
      refine ewp_pureSteps (opTable_mono _) (nodeV_eff_steps n i q A B D _ c) ls _ ρ ?_
      refine ewp_pureSteps (opTable_mono _) (PureSteps.plug (.appR (.val (.lam _)) .hole) hc)
        ls _ ρ ?_
      refine ewp_frame_plain _ (.appR (.val (.lam _)) .hole) (fun n => by simp [Kont.HasHnd])
        (fun n => by simp [Kont.Catches]) (by simp [Kont.hndNames]) (fun _ => emp)
        (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ _ _ _ _ h => by rw [h.1]; exact noOwn_empty)
        (fun _ _ _ _ _ _ _ h => h.1) _ _ ?_ hM' ⟨rfl, trivial⟩ (ResU.comp_empty_right ρ)
      rintro ls' w σ ⟨σ₁, σ₂, hcσ, hw, hemp, -⟩
      rw [hemp] at hcσ
      obtain rfl := eq_of_compS_empty_left (ResU.CompS.comm hcσ)
      refine ewp_pureSteps (opTable_mono _) (PureSteps.beta _ w) ls' _ _ ?_
      have e : Expr.subst 0 w (.app (.app (.val (mapV (effAns D))) (.val ((hN C g).shift 1 0)))
          (.var 0)) = .app (.app (.val (mapV (effAns D))) (.val (hN C g))) (.val w) := by
        simp [closed_subst (mapV_closed (effAns D)), subst_shift_succ]
      rw [e]
      rw [vC_inst_envS] at hw
      obtain ⟨w', hs, h'⟩ := map_ok C g S δ (effAns D) hR ls' w _ hw
      exact ewp_pureSteps (opTable_mono _) hs ls' _ _ (ewp_val (opTable_mono _) h')

/-- The candidate is a post-fixed point of `νX. C`'s functor: each observation path runs the
same path of the step and returns its result with every state `s′` replaced by
`unfold step s′`, back in the candidate. -/
theorem candN_post {C : CTy} (hC : C.NuOk) {S : VTy} {δ : LSub} {g : Val}
    (hg : ∀ ls, vC true (.bang (.thunk (.arr S (C.instT S)))) ls δ g PMap.empty) :
    (candN C g S δ).Le (nuF C δ (candN C g S δ)) := by
  rintro ls e ρ ⟨s, rfl, hs⟩
  obtain ⟨-, hthunk⟩ := hg ls
  have hstep : cC (C.instT S) ls δ (.app (.val g) (.val s)) ρ :=
    hthunk ls (Ext.refl _ _) s ρ ρ hs (ResU.CompS.comm (ResU.comp_empty_right ρ))
  cases C with
  | amp C₁ C₂ =>
      have hN := node_ok (.amp C₁ C₂) g S δ (.amp C₁ C₂) hC (rootV g s) _ ls ρ
        (rootV_steps g s) hstep
      exact ⟨cB_pureSteps _ C₁ (etaN_obs _ g s _) ls δ ρ hN.1,
        cB_pureSteps _ C₂ (etaN_obs _ g s _) ls δ ρ hN.2⟩
  | _ => exact hC.elim

/-- **`unfold` is sound**: `unfold : !U(S ⊸ C[S/X]) ⊸ !U(S ⊸ νX. C)` at every positive `C`
and every `S`.  `[spec §7]` -/
theorem unfold_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {C : CTy} (hC : C.NuOk) (S : VTy)
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ (.val (unfoldV C)) (unfoldTy C S) := by
  intro δ γ ls ρ _ hg₀
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg₀).2
  subst hρ
  rw [substAll_closed (unfoldV_closed C)]
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ g ρ₁ τ₀ hv₁ hcomp
  have hρ₁ : ρ₁ = PMap.empty := hv₁.1
  subst hρ₁
  have hg : ∀ ls, vC true (.bang (.thunk (.arr S (C.instT S)))) ls δ g PMap.empty := fun ls' =>
    vC_local true _ (ext_empty ls₁ ls') hv₁
  rw [eq_of_compS_empty_left hcomp]
  refine wpTS_lolli _ _ g _ _ ?_
  rw [unfoldV_subst]
  refine wpTS_val _ _ _ _ ⟨rfl, ?_⟩
  intro ls₂ _ s ρ₂ τ hs hc
  rw [eq_of_compS_empty_left hc]
  refine cC_head (.nu C) (fun μ => Head.beta μ _ s) rfl ls₂ δ ρ₂ ?_
  rw [hN_subst]
  exact fun _ => nuRel_coind (candN_post hC hg) ls₂ _ ρ₂ ⟨s, rfl, hs⟩

/-! ### `νX. C` and its unrolling -/

/-- `nuIn`: a computation of `C[U(νX. C)/X]` is one of `νX. C`. -/
theorem nuIn_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {C : CTy} (hC : C.NuOk)
    (h : SemC Δ Γ e C.unroll) : SemC Δ Γ e (.nu C) :=
  fun δ γ ls ρ hδ hΓ => (cC_nu_iff hC ls δ _ ρ).mpr (h δ γ ls ρ hδ hΓ)

/-- `nuOut`: a computation of `νX. C` is one of `C[U(νX. C)/X]`. -/
theorem nuOut_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {C : CTy} (hC : C.NuOk)
    (h : SemC Δ Γ e (.nu C)) : SemC Δ Γ e C.unroll :=
  fun δ γ ls ρ hδ hΓ => (cC_nu_iff hC ls δ _ ρ).mp (h δ γ ls ρ hδ hΓ)

end BoCa.Fig16.LogRel.Core

end

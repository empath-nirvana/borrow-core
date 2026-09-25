import Recursion.Mu

/-!
# Recursion — P-ν: a stream as a greatest fixed point

`St A = νX. F(A ⊗ U X) & F 1`, written out by hand over CBPVWorld's relation, which is imported
unchanged. `stF A R` is `cC`'s `&`, `F`, `⊗` and `U` clauses with the candidate `R` in place of
`cC X` (`stF_cC`). `stRel A` is the greatest fixed point `⋃{R | R ⊆ stF A R}`, written in
`Prop` as `∃ R`; it is a direct fixed point in the computation type, not a packed `∃S` value.

* `stRel_out`/`stRel_roll`: `stRel ↔ stF stRel`.
* `unfoldE`: coiteration `unfold step x : U (St A)` for a closed `step : S ⊸ F(A ⊗ S) & F 1`,
  by the Z combinator. `unfold_sem` is its soundness: the proof is coinduction with the candidate
  `{unfold step s | vC S s}`, the image of the state relation.
* `take2Close_runs`: allocate a `Ref 1` state, unfold, observe `next` twice, then `close`. It
  runs from the empty memory to `()` and the empty memory.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.CBPVWorld.Recursion
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- A candidate interpretation of a computation-type variable, at `cC`'s signature. -/
abbrev CPred := List SRec → LSub → Expr → WProp

/-- `R ⊆ R'` pointwise. -/
def CPred.Le (R R' : CPred) : Prop := ∀ ls δ e, Entails (R ls δ e) (R' ls δ e)

/-! ### The functor and its greatest fixed point -/

/-- `vC true (U X)` at the candidate `R`, for an `X` whose head is `&`: such a thunk is forced as
it stands (`forceE`). -/
def thunkR (R : CPred) (ls : List SRec) (δ : LSub) (v : Val) : WProp := fun ρ =>
  ∀ ls', Ext ls ls' ρ → R ls' δ (.val v) ρ

/-- The postcondition of `next : F(A ⊗ U X)` at the candidate `R`. -/
def nextQ (A : VTy) (R : CPred) (δ : LSub) : List SRec → Val → WProp := fun ls w =>
  ex fun v₁ => ex fun v₂ => ⌜w = .pair v₁ v₂⌝ ⋆ vC true A ls δ v₁ ⋆ thunkR R ls δ v₂

/-- One unfolding of `St A = νX. F(A ⊗ U X) & F 1` at the candidate `R` for `X`: the `next`
observation (`π₁`) and the `close` observation (`π₂`). -/
def stF (A : VTy) (R : CPred) : CPred := fun ls δ e ρ =>
  wpTS ls (.app e (.val (.inj₁ .unit))) (nextQ A R δ) ρ ∧
  wpTS ls (.app e (.val (.inj₂ .unit))) (fun ls' => vC true .unit ls' δ) ρ

/-- `stF` transcribes `cC`: at `R = cC C` it is `cC` at `F(A ⊗ U C) & F 1`, for any `C` forced
as it stands. -/
theorem stF_cC (A : VTy) {C : CTy} (hC : C.isRet = false) (ls : List SRec) (δ : LSub)
    (e : Expr) (ρ : WRes) :
    stF A (cC C) ls δ e ρ ↔ cC (.amp (.ret (.tensor A (.thunk C))) (.ret .unit)) ls δ e ρ := by
  simp only [stF, cC, vC, forceE_of_not_ret hC]
  exact Iff.rfl

theorem stF_mono (A : VTy) {R R' : CPred} (h : R.Le R') : (stF A R).Le (stF A R') := by
  rintro ls δ e ρ ⟨h₁, h₂⟩
  refine ⟨wpTS_mono (fun ls' w => ?_) ρ h₁, h₂⟩
  rintro σ ⟨v₁, v₂, σ₀, σ₃, hc, hp, σ₁, σ₂, hc', hA, hT⟩
  exact ⟨v₁, v₂, σ₀, σ₃, hc, hp, σ₁, σ₂, hc', hA, fun ls'' hk => h _ _ _ _ (hT ls'' hk)⟩

/-- `⟦νX. F(A ⊗ U X) & F 1⟧ = ⋃{R | R ⊆ stF A R}`. -/
def stRel (A : VTy) : CPred := fun ls δ e ρ => ∃ R : CPred, R.Le (stF A R) ∧ R ls δ e ρ

/-- Coinduction. -/
theorem stRel_coind {A : VTy} {R : CPred} (hR : R.Le (stF A R)) : R.Le (stRel A) :=
  fun _ _ _ _ h => ⟨R, hR, h⟩

/-- `out`. -/
theorem stRel_out (A : VTy) : (stRel A).Le (stF A (stRel A)) := by
  rintro ls δ e ρ ⟨R, hR, h⟩
  exact stF_mono A (stRel_coind hR) ls δ e ρ (hR ls δ e ρ h)

/-- `roll`. -/
theorem stRel_roll (A : VTy) : (stF A (stRel A)).Le (stRel A) :=
  stRel_coind (stF_mono A (stRel_out A))

/-- **`out`/`roll`.** -/
theorem stRel_iff (A : VTy) (ls : List SRec) (δ : LSub) (e : Expr) (ρ : WRes) :
    stRel A ls δ e ρ ↔ stF A (stRel A) ls δ e ρ :=
  ⟨stRel_out A ls δ e ρ, stRel_roll A ls δ e ρ⟩

/-! ### Coiteration -/

/-- The step's type, `S ⊸ F(A ⊗ S) & F 1`. -/
abbrev stepC (A S : VTy) : CTy := .arr S (.amp (.ret (.tensor A S)) (.ret .unit))

/-- `λp. let (a, s′) = p in (a, λo. self s′ o)`, under the binders `u, o, s, self` of `unfB`. -/
def unfK : Expr :=
  .letpair (.var 0) (.pair (.var 1) (.val (.lam (.app (.app (.var 7) (.var 1)) (.var 0)))))

/-- The body of `unfold = Z (λself. λs. λo. case o {inj₁ _. (step s π₁) to p. unfK p |
inj₂ _. step s π₂})`. -/
def unfB (st : Val) : Expr :=
  .val (.lam (.case (.var 0)
    (.app (.val (.lam unfK)) (.app (.app (.val st) (.var 2)) (.val (.inj₁ .unit))))
    (.app (.app (.val st) (.var 2)) (.val (.inj₂ .unit)))))

theorem unfB_closed {st : Val} (hst : closedAt 0 st.1 = true) : closedAt 2 (unfB st) = true := by
  have h : ∀ k, closedAt k st.1 = true := fun k => closedAt_mono _ hst (Nat.zero_le k)
  simp [unfB, unfK, closedAt, h]

/-- `λo. self s o` with the recursive handle closed: the stream at state `s`. -/
def etaS (st s : Val) : Val :=
  .lam (.app (.app (.val (selfV (unfB st))) (.val (s.shift 1 0))) (.var 0))

/-- `unfold step x`, open in the state `x` (index 0). -/
def unfoldE (st : Val) : Expr :=
  .val (.lam (.app (.app (.val (selfV (unfB st))) (.var 1)) (.var 0)))

/-! #### Substitution bookkeeping, for a closed handle `S` -/

theorem subst_shift_one (x : Val) (e : Expr) : Expr.subst 0 x (Expr.shift 1 0 e) = e := by
  have h := Expr.subst_shift 0 0 0 x e le_rfl le_rfl
  rwa [Expr.shift_zero] at h

theorem subst_shift_two (x : Val) (e : Expr) :
    Expr.subst 1 x (Expr.shift 2 0 e) = Expr.shift 1 0 e :=
  Expr.subst_shift 1 0 1 x e (by omega) (by omega)

/-- `unfK` with the handle `S` in place of `self`. -/
def unfKS (S : Val) : Expr :=
  .letpair (.var 0) (.pair (.var 1) (.val (.lam (.app (.app (.val S) (.var 1)) (.var 0)))))

/-- The unfolded stream `λo. case o {…}` at handle `S` and state `s`. -/
def strmS (st S s : Val) : Expr :=
  .lam (.case (.var 0)
    (.app (.val (.lam (unfKS S))) (.app (.app (.val st) (.val (s.shift 2 0))) (.val (.inj₁ .unit))))
    (.app (.app (.val st) (.val (s.shift 2 0))) (.val (.inj₂ .unit))))

section closed
variable {st S : Val} (hst : closedAt 0 st.1 = true) (hS : closedAt 0 S.1 = true)
include hst hS

private theorem cl_lemmas :
    (∀ d c, Expr.shift d c st.1 = st.1) ∧ (∀ j x, Expr.subst j x st.1 = st.1) ∧
    (∀ d c, Expr.shift d c S.1 = S.1) ∧ (∀ j x, Expr.subst j x S.1 = S.1) :=
  ⟨fun d c => shift_closedAt st.1 d hst (Nat.zero_le c),
   fun j x => subst_closedAt st.1 x hst (Nat.zero_le j),
   fun d c => shift_closedAt S.1 d hS (Nat.zero_le c),
   fun j x => subst_closedAt S.1 x hS (Nat.zero_le j)⟩

theorem unfB_subst (s : Val) : ((unfB st).subst 1 S).subst 0 s = strmS st S s := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := cl_lemmas hst hS
  simp [unfB, unfK, unfKS, strmS, Expr.subst, h₂, h₃, h₄, Expr.shift_shift]

theorem strm_next (s : Val) :
    ((Expr.app (.val (.lam (unfKS S))) (.app (.app (.val st) (.val (s.shift 2 0)))
      (.val (.inj₁ .unit)))).subst 1 ((Val.inj₁ Val.unit).shift 1 0)).subst 0 Val.unit
      = .app (.val (.lam (unfKS S))) (.app (.app (.val st) (.val s)) (.val (.inj₁ .unit))) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := cl_lemmas hst hS
  simp [unfKS, Expr.subst, h₂, h₄, subst_shift_two, subst_shift_one]

theorem strm_close (s : Val) :
    ((Expr.app (.app (.val st) (.val (s.shift 2 0))) (.val (.inj₂ .unit))).subst 1
      ((Val.inj₂ Val.unit).shift 1 0)).subst 0 Val.unit
      = .app (.app (.val st) (.val s)) (.val (.inj₂ .unit)) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := cl_lemmas hst hS
  simp [Expr.subst, h₂, subst_shift_two, subst_shift_one]

theorem eta_beta (s o : Val) :
    (Expr.app (.app (.val S) (.val (s.shift 1 0))) (.var 0)).subst 0 o
      = .app (.app (.val S) (.val s)) (.val o) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := cl_lemmas hst hS
  simp [Expr.subst, h₄, subst_shift_one]

/-- `unfKS` on a returned pair `(a, s′)` builds `(a, λo. S s′ o)`. -/
theorem unfK_pair (a s' : Val) :
    ((Expr.pair (.var 1) (.val (.lam (.app (.app (.val S) (.var 1)) (.var 0))))).subst 0
      (s'.shift 1 0)).subst 0 a
      = .pair (.val a) (.val (.lam (.app (.app (.val S) (.val (s'.shift 1 0))) (.var 0)))) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := cl_lemmas hst hS
  simp [Expr.subst, h₄, Expr.shift_shift, subst_shift_two]

theorem unfK_beta (w : Val) :
    (unfKS S).subst 0 w = .letpair (.val w)
      (.pair (.var 1) (.val (.lam (.app (.app (.val S) (.var 1)) (.var 0))))) := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := cl_lemmas hst hS
  simp [unfKS, Expr.subst, h₄]

end closed

/-! #### The observations of `unfold step s` -/

section obs
variable {st : Val} (hst : closedAt 0 st.1 = true)
include hst

theorem selfU_closed : closedAt 0 (selfV (unfB st)).1 = true :=
  selfV_closed (unfB_closed hst)

theorem unfoldE_subst (s : Val) : (unfoldE st).subst 0 s = .val (etaS st s) := by
  have hS := selfU_closed hst
  simp [unfoldE, etaS, Expr.subst, subst_closedAt _ (k := 0) (j := 1) _ hS (Nat.zero_le 1)]

/-- An observation `o` of the stream at `s` unrolls the Z combinator and reaches the unfolded
stream `λo. case o {…}` at `s`. -/
theorem obs_run (s o : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (.app (strmS st (selfV (unfB st)) s) (.val o)) Q)
      (wpTS ls (.app (.val (etaS st s)) (.val o)) Q) := by
  have hS := selfU_closed hst
  intro ρ h
  refine wpTS_lolli ls _ o Q ρ ?_
  rw [eta_beta hst hS]
  show wpTS ls ((Kont.appL .hole o).plug (.app (.val (selfV (unfB st))) (.val s))) Q ρ
  refine wpTS_selfV_in (unfB_closed hst) _ s ls Q ρ ?_
  refine wpTS_step (step_in (.appL .hole o) (fun μ => Head.beta μ _ s)) ls Q ρ ?_
  show wpTS ls (.app (((unfB st).subst 1 ((selfV (unfB st)).shift 1 0)).subst 0 s) (.val o)) Q ρ
  rw [val_shift_closed hS, unfB_subst hst hS s]
  exact h

/-- `next` runs the step's `π₁` at `s`, then `unfK`. -/
theorem obs_next (s : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails
      (wpTS ls (.app (.val (.lam (unfKS (selfV (unfB st)))))
        (.app (.app (.val st) (.val s)) (.val (.inj₁ .unit)))) Q)
      (wpTS ls (.app (.val (etaS st s)) (.val (.inj₁ .unit))) Q) := by
  have hS := selfU_closed hst
  intro ρ h
  refine obs_run hst s _ ls Q ρ (wpTS_lolli ls _ _ Q ρ ?_)
  refine wpTS_sum₁ ls Val.unit _ _ Q ρ ?_
  rw [strm_next hst hS s]
  exact h

/-- `close` runs the step's `π₂` at `s`. -/
theorem obs_close (s : Val) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (.app (.app (.val st) (.val s)) (.val (.inj₂ .unit))) Q)
      (wpTS ls (.app (.val (etaS st s)) (.val (.inj₂ .unit))) Q) := by
  have hS := selfU_closed hst
  intro ρ h
  refine obs_run hst s _ ls Q ρ (wpTS_lolli ls _ _ Q ρ ?_)
  refine wpTS_sum₂ ls Val.unit _ _ Q ρ ?_
  rw [strm_close hst hS s]
  exact h

end obs

/-! #### Soundness of coiteration -/

/-- The empty lifetime context is modelled by every substitution. -/
theorem models_empty_any (δ : LSub) : LifeCtx.empty.Models δ := by
  intro x u h
  exact absurd h (by simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind])

/-- The candidate: streams `unfold step s` at a state `s` in `vC S`. It is the image of the
state relation under the unfold — the `∃S` form, used as the proof. -/
def candR (S : VTy) (st : Val) : CPred := fun ls δ e ρ =>
  ∃ s, e = .val (etaS st s) ∧ vC true S ls δ s ρ

section coit
variable {A S : VTy} {st : Val} (hst : closedAt 0 st.1 = true)
  (hsem : SemC LifeCtx.empty [] (.val st) (stepC A S))
include hst hsem

/-- The candidate is a post-fixed point of `stF A`. -/
theorem candR_post : (candR S st).Le (stF A (candR S st)) := by
  have hS := selfU_closed hst
  rintro ls δ e ρ ⟨s, rfl, hs⟩
  have hstep := hsem δ [] ls PMap.empty (models_empty_any δ) (gDenC_nil ls δ)
  rw [show substAll [] (.val st) = .val st from Adequacy.psub_nil 0 _] at hstep
  obtain ⟨h₁, h₂⟩ := hstep s ρ ρ hs (compS_empty_left ρ)
  refine ⟨obs_next hst s ls _ ρ ?_, obs_close hst s ls _ ρ h₂⟩
  refine wpTS_bind (.appR (.val (.lam (unfKS (selfV (unfB st))))) .hole) _ ls _ ρ ?_
  refine wpTS_mono (fun ls' w σ hw => ?_) ρ h₁
  obtain ⟨a, s', σ₀, σ₃, hc, ⟨hσ₀, rfl⟩, σ₁, σ₂, hc', ha, hs'⟩ := hw
  show wpTS ls' (.app (.val (.lam (unfKS (selfV (unfB st))))) (.val (.pair a s'))) _ σ
  refine wpTS_lolli ls' _ _ _ σ ?_
  rw [unfK_beta hst hS]
  refine wpTS_tensor ls' a s' _ _ σ ?_
  rw [unfK_pair hst hS]
  refine wpTS_val ls' (Val.pair a (etaS st s')) _ σ ?_
  exact ⟨a, etaS st s', σ₀, σ₃, hc, ⟨hσ₀, rfl⟩, σ₁, σ₂, hc', ha,
    fun ls'' hk => ⟨s', rfl, vC_local true S hk hs'⟩⟩

/-- **Coiteration is sound.** `unfold step s : U (St A)` for a state `s : S`, given the step's
semantic type `S ⊸ F(A ⊗ S) & F 1` at the empty context — the premise from which `bangThunkV`
promotes it to `!U(…)`. -/
theorem unfold_sem {ls : List SRec} {δ : LSub} {s : Val} {ρ : WRes}
    (hs : vC true S ls δ s ρ) : thunkR (stRel A) ls δ (etaS st s) ρ :=
  fun ls' hk => stRel_coind (candR_post hst hsem) ls' δ _ ρ ⟨s, rfl, vC_local true S hk hs⟩

/-- `x : S ⊨ unfold step x : U (St A)`, at the value substituted for `x`. -/
theorem unfold_semV {ls : List SRec} {δ : LSub} {s : Val} {ρ : WRes}
    (hs : vC true S ls δ s ρ) :
    wpTS ls ((unfoldE st).subst 0 s) (fun ls' => thunkR (stRel A) ls' δ) ρ := by
  rw [unfoldE_subst hst]
  exact wpTS_val ls _ _ ρ (unfold_sem hst hsem hs)

end coit

/-! ### Take two, then close -/

/-- The step on a `Ref 1` state: `λs. ⟨return ((), s), free s⟩`. -/
def stepV : Val :=
  .lam (withPair (.pair (.val .unit) (.var 2)) (.app (.val (.prim .free)) (.var 2)))

theorem stepV_closed : closedAt 0 stepV.1 = true := rfl

/-- `stepV : Ref 1 ⊸ F(1 ⊗ Ref 1) & F 1`, a `CDerives` derivation. -/
theorem stepV_derives :
    CDerives LifeCtx.empty [] (.val stepV) (.comp (stepC .unit (.ref .unit))) :=
  .lam (.withI
    (.ret (.tensorI (.dead (.dead (.right .nil))) (.unitI (by repeat constructor))
      (.var (by repeat constructor))))
    (.ret (.lolliE (.dead (.dead (.left .nil))) (.var (by repeat constructor))
      (.free (by repeat constructor)))))

theorem stepV_sem : SemC LifeCtx.empty [] (.val stepV) (stepC .unit (.ref .unit)) :=
  fundamentalC stepV_derives

/-- `(M to x. N)`, written `(λx. N) M`. -/
abbrev bnd (M N : Expr) : Expr := .app (.val (.lam N)) M

/-- `let (a₂, t₂) = p₂ in a₂; π₂ t₂`. -/
def closeK : Expr := .letpair (.var 0) (.seq (.var 1) (.app (.var 0) (.val (.inj₂ .unit))))

/-- `π₁ t₁ to p₂. closeK`. -/
def next2K : Expr := bnd (.app (.var 0) (.val (.inj₁ .unit))) closeK

/-- `let (a₁, t₁) = p₁ in a₁; next2K`. -/
def next1K : Expr := .letpair (.var 0) (.seq (.var 1) next2K)

/-- The consumer at `t`: `π₁ t to p₁. next1K`. -/
def consumer : Expr := bnd (.app (.var 0) (.val (.inj₁ .unit))) next1K

/-- `alloc () to r. unfold stepV r to t. consumer`. -/
def take2Close : Expr :=
  bnd (.app (.val (.prim .alloc)) (.val .unit)) (bnd (unfoldE stepV) consumer)

/-- `π₁ t to p. N` at a stream `t`: `N` runs at the pair `next` returns. -/
theorem next_bind {A : VTy} {ls : List SRec} {δ : LSub} {t : Val} {ρ : WRes}
    (h : stRel A ls δ (.val t) ρ) (N : Expr) (Q : List SRec → Val → WProp)
    (hN : ∀ ls' a t', Entails (vC true A ls' δ a ⋆ thunkR (stRel A) ls' δ t')
      (wpTS ls' (N.subst 0 (Val.pair a t')) Q)) :
    wpTS ls (bnd (.app (.val t) (.val (.inj₁ .unit))) N) Q ρ := by
  refine wpTS_bind (.appR (.val (.lam N)) .hole) _ ls Q ρ ?_
  refine wpTS_mono (fun ls' w σ hw => ?_) ρ (stRel_out A ls δ _ ρ h).1
  obtain ⟨a, t', σ₀, σ₃, hc, ⟨rfl, rfl⟩, hσ₃⟩ := hw
  rw [eq_of_compS_empty_left hc]
  exact wpTS_lolli ls' N _ Q σ₃ (hN ls' a t' σ₃ hσ₃)

/-- The consumer's two `next`s and its `close`, at any stream of `St 1`. -/
theorem consumer_wp {ls : List SRec} {δ : LSub} {t : Val} {ρ : WRes}
    (h : stRel .unit ls δ (.val t) ρ) : wpTS ls (consumer.subst 0 t) unitQ ρ := by
  have e₀ : consumer.subst 0 t = bnd (.app (.val t) (.val (.inj₁ .unit))) next1K := by
    simp only [consumer, bnd, Expr.subst]
    rfl
  rw [e₀]
  refine next_bind h next1K unitQ (fun ls' a t₁ σ hσ => ?_)
  obtain ⟨σ₁, σ₂, hc, ⟨rfl, rfl⟩, hT⟩ := hσ
  rw [eq_of_compS_empty_left hc]
  have e₁ : next1K.subst 0 (Val.pair Val.unit t₁)
      = .letpair (.val (.pair .unit t₁)) (.seq (.var 1) next2K) := by
    simp only [next1K, Expr.subst]
    rfl
  rw [e₁]
  refine wpTS_tensor ls' Val.unit t₁ _ unitQ σ₂ ?_
  have e₂ : ((Expr.seq (.var 1) next2K).subst 0 (t₁.shift 1 0)).subst 0 Val.unit
      = .seq (.val .unit) (bnd (.app (.val t₁) (.val (.inj₁ .unit))) closeK) := by
    simp [next2K, bnd, Expr.subst, subst_closedAt closeK (k := 1) (j := 1) _ rfl le_rfl,
      subst_shift_one]
  rw [e₂]
  refine wpTS_1 ls' _ unitQ σ₂ ?_
  refine next_bind (hT ls' (Ext.refl ls' σ₂)) closeK unitQ (fun ls'' a t₂ τ hτ => ?_)
  obtain ⟨τ₁, τ₂, hc', ⟨rfl, rfl⟩, hT'⟩ := hτ
  rw [eq_of_compS_empty_left hc']
  have e₃ : closeK.subst 0 (Val.pair Val.unit t₂)
      = .letpair (.val (.pair .unit t₂)) (.seq (.var 1) (.app (.var 0) (.val (.inj₂ .unit)))) := by
    simp [closeK, Expr.subst]
  rw [e₃]
  refine wpTS_tensor ls'' Val.unit t₂ _ unitQ τ₂ ?_
  have e₄ : ((Expr.seq (.var 1) (.app (.var 0) (.val (.inj₂ .unit)))).subst 0
      (t₂.shift 1 0)).subst 0 Val.unit
      = .seq (.val .unit) (.app (.val t₂) (.val (.inj₂ .unit))) := by
    simp [Expr.subst, subst_shift_one]
  rw [e₄]
  exact wpTS_1 ls'' _ unitQ τ₂ (stRel_out .unit ls'' δ _ τ₂ (hT' ls'' (Ext.refl ls'' τ₂))).2

theorem take2Close_wp : wpTS [] take2Close (fun _ v => Fig16.BoLo.pure (v = Val.unit))
    (PMap.empty : WRes) := by
  refine wpTS_bind (.appR (.val (.lam (bnd (unfoldE stepV) consumer))) .hole) _ [] _ _ ?_
  refine wpTS_alloc [] Val.unit _ _ (fun ℓ σ τ hσ hc => ?_)
  rw [eq_of_compS_empty_left hc]
  show wpTS [] (.app (.val (.lam (bnd (unfoldE stepV) consumer))) (.val (.loc ℓ))) _ σ
  refine wpTS_lolli [] _ _ _ σ ?_
  have e : (bnd (unfoldE stepV) consumer).subst 0 (Val.loc ℓ)
      = .app (.val (.lam consumer)) (.val (etaS stepV (.loc ℓ))) := by
    simp only [Expr.subst]
    rw [← unfoldE_subst stepV_closed]
    rfl
  rw [e]
  refine wpTS_lolli [] _ _ _ σ ?_
  have hr : vC true (.ref .unit) [] LSub.empty (.loc ℓ) σ :=
    ⟨ℓ, Val.unit, PMap.empty, σ, compS_empty_left σ, ⟨rfl, rfl⟩, σ, PMap.empty,
      ResU.comp_empty_right σ, hσ, ⟨rfl, rfl⟩⟩
  exact consumer_wp (unfold_sem (A := .unit) stepV_closed stepV_sem hr [] (Ext.refl [] σ))

/-- **Adequacy at the stream**: allocate the state, unfold, take two, close. The run goes from
the empty memory to `()` and the empty memory. -/
theorem take2Close_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem take2Close Adequacy.emptyMem (.val .unit) := by
  obtain ⟨v, hsteps, hv⟩ := theorem32 take2Close (· = Val.unit) take2Close_wp
  subst hv
  exact hsteps

/-- The executable interpreter agrees: `()` and no cell left. -/
theorem take2Close_eval : Programs.unitNoLeak (eval take2Close) = true := by decide

end BoCa.Fig16.LogRel.CBPVWorld.Recursion

end

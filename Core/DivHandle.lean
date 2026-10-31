import Core.DivReify
import Core.EffBoxed

/-!
# Core — `[handle]` of another name around a computation that ticks  `[spec §14, §19]`

`hnd_m H e`, `e` at a row holding `Div` and `m`, `m ≠ Div`.  The handler forwards `tick`: a tick
of `e` stops the whole, its continuation `hnd_m H K[n]`, so the forwarded tick is the coinductive
case.

**The rule** (`effHandleT`, decision 68): every clause of a non-abortive operation **resumes `κ`
in tail position** with an answer it computes from the operation's argument, by a function
`g : !U(A ⊸ F_{Σ_N} B)` of a row `Σ_N ≤ Σ` of must-resume operations; a clause of an abortive
operation is `g : !U(A ⊸ F_Σ R)`.  The clauses are written out from the tuple of the `g`s
(`tailTuple`): `λ(x, κ). (λw. κ.1 w) (g x)` and `λx. g x`.  This is the class that lowers to a
direct call.  `g x` may tick.

**The proof** (`ewp_handle_tail`), at a row holding `Div`: the greatest fixed point of the
handled computations together with the resume frame `κ.1 [·]` around a computation of the clause's
row, `κ` resumed into one segment of the candidate.  The candidate is a least fixed point
(`TailY`), so that the resume frame's `κ` resumes into the candidate itself.  A segment of the
handled computation under the handler is `ewp_handle_or`: the inner tick passes the handler, and
a clause's answer resumes `κ` there.  The resume frame is `cwpF_frame` from the clause's row to
the outer one; the clause's row is of must-resume operations, so the frame holds `κ` through every
stop.  `Closing` is `ewp_handle` at the closing tables.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload hndE hndVal
  kappa kappaC kappaCell kappaAt clauseAt capTag freeE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-! ### Shifts under a closing substitution -/

theorem Expr.shift_shift_cut (d c : Nat) :
    ∀ (e : Expr) (k : Nat), Expr.shift d (k + c) (Expr.shift c k e) = Expr.shift (c + d) k e
  | .var i, k => by
      by_cases h : i < k
      · have h' : i < k + c := by omega
        simp [Expr.shift, h, h']
      · have h' : ¬ (i + c < k + c) := by omega
        simp only [Expr.shift, h, if_false, h']
        congr 1; omega
  | .unit, _ => rfl
  | .pair a b, k => by simp only [Expr.shift, Expr.shift_shift_cut d c a, Expr.shift_shift_cut d c b]
  | .inj₁ a, k => by simp only [Expr.shift, Expr.shift_shift_cut d c a]
  | .inj₂ a, k => by simp only [Expr.shift, Expr.shift_shift_cut d c a]
  | .lam b, k => by
      simp only [Expr.shift]
      rw [show k + c + 1 = (k + 1) + c by omega, Expr.shift_shift_cut d c b (k + 1)]
  | .loc _, _ => rfl
  | .prim _, _ => rfl
  | .seq a b, k => by simp only [Expr.shift, Expr.shift_shift_cut d c a, Expr.shift_shift_cut d c b]
  | .letpair a b, k => by
      simp only [Expr.shift]
      rw [show k + c + 2 = (k + 2) + c by omega, Expr.shift_shift_cut d c a k,
        Expr.shift_shift_cut d c b (k + 2)]
  | .case a b₁ b₂, k => by
      simp only [Expr.shift]
      rw [show k + c + 1 = (k + 1) + c by omega, Expr.shift_shift_cut d c a k,
        Expr.shift_shift_cut d c b₁ (k + 1), Expr.shift_shift_cut d c b₂ (k + 1)]
  | .app f a, k => by simp only [Expr.shift, Expr.shift_shift_cut d c f, Expr.shift_shift_cut d c a]

/-- **A closing substitution under `d` binders of a term shifted past them** is the shifted
closing substitution. -/
theorem Expr.psub_shift (d : Nat) (γ : List Val) :
    ∀ (e : Expr) (c : Nat), Expr.psub (c + d) γ (Expr.shift d c e) = Expr.shift d c (Expr.psub c γ e)
  | .var i, c => by
      by_cases h : i < c
      · have h' : i < c + d := by omega
        simp [Expr.shift, Expr.psub, h, h']
      · have h' : ¬ (i + d < c + d) := by omega
        simp only [Expr.shift, h, if_false, Expr.psub, h']
        rw [show i + d - (c + d) = i - c by omega]
        cases hg : γ[i - c]? with
        | some v =>
            simp only [Expr.val, Val.val_shift]
            have e := Expr.shift_shift_cut d c v.1 0
            simp only [Nat.zero_add] at e
            rw [e]
        | none =>
            simp only [Expr.shift]
            have hl : γ.length ≤ i - c := by
              by_contra hc; push Not at hc; rw [List.getElem?_eq_getElem hc] at hg; cases hg
            rw [if_neg (by omega)]
            congr 1; omega
  | .unit, _ => rfl
  | .pair a b, c => by simp only [Expr.shift, Expr.psub, Expr.psub_shift d γ a, Expr.psub_shift d γ b]
  | .inj₁ a, c => by simp only [Expr.shift, Expr.psub, Expr.psub_shift d γ a]
  | .inj₂ a, c => by simp only [Expr.shift, Expr.psub, Expr.psub_shift d γ a]
  | .lam b, c => by
      simp only [Expr.shift, Expr.psub]
      rw [show c + d + 1 = (c + 1) + d by omega, Expr.psub_shift d γ b (c + 1)]
  | .loc _, _ => rfl
  | .prim _, _ => rfl
  | .seq a b, c => by simp only [Expr.shift, Expr.psub, Expr.psub_shift d γ a, Expr.psub_shift d γ b]
  | .letpair a b, c => by
      simp only [Expr.shift, Expr.psub]
      rw [show c + d + 2 = (c + 2) + d by omega, Expr.psub_shift d γ a c,
        Expr.psub_shift d γ b (c + 2)]
  | .case a b₁ b₂, c => by
      simp only [Expr.shift, Expr.psub]
      rw [show c + d + 1 = (c + 1) + d by omega, Expr.psub_shift d γ a c,
        Expr.psub_shift d γ b₁ (c + 1), Expr.psub_shift d γ b₂ (c + 1)]
  | .app f a, c => by simp only [Expr.shift, Expr.psub, Expr.psub_shift d γ f, Expr.psub_shift d γ a]

/-! ### The clauses -/

/-- The `j`-th component of a right-nested tuple. -/
def pickE : Nat → Expr → Expr
  | 0, t => .letpair t (.var 1)
  | j + 1, t => .letpair t (pickE j (.var 0))

/-- The resume of `κ` (`1`) at `w` (`0`): `κ.1 w`. -/
def resumeB : Expr := .app (.app (.var 1) (.val (Val.inj₁ .unit))) (.var 0)

/-- The clause of the `j`-th operation, from the tuple `Hc` of answering functions: at a
non-abortive operation `λ(x, κ). (λw. κ.1 w) (g x)`, at an abortive one `λx. g x`. -/
def tailClause (j : Nat) (abort : Bool) (Hc : Expr) : Expr :=
  if abort then .lam (.app (pickE j (Hc.shift 1 0)) (.var 0))
  else .lam (.letpair (.var 0) (.app (.val (Val.lam resumeB))
    (.app (pickE j (Hc.shift 3 0)) (.var 1))))

/-- The clauses, from the `j`-th on.  `[spec §14, §19]` -/
def tailTuple : List (Qual × VTy × VTy) → Nat → Expr → Expr
  | [], _, _ => .val .unit
  | (q, _, B) :: E, j, Hc => .pair (tailClause j (B.isZero && q != .lin) Hc) (tailTuple E (j + 1) Hc)

/-- An answering function's type: `!U(A ⊸ F_{Σ_N} B)`, or the clause's `!U(A ⊸ F_Σ R)` at an
abortive operation.  `[spec §14, §19]` -/
def ansTy (S SN : Row) (R : VTy) : Qual × VTy × VTy → VTy
  | (q, A, B) => if (B.isZero && q != .lin) then .bang (.thunk (.arr A (CTy.effOf S R)))
      else .bang (.thunk (.arr A (CTy.effOf SN B)))

/-- The answering functions' tuple's type.  `[spec §14, §19]` -/
def ansesTy (S SN : Row) (R : VTy) : List (Qual × VTy × VTy) → VTy
  | [] => .unit
  | o :: E => .tensor (ansTy S SN R o) (ansesTy S SN R E)

theorem ansTy_persistent (S SN : Row) (R : VTy) (o : Qual × VTy × VTy) :
    (ansTy S SN R o).Persistent := by
  obtain ⟨q, A, B⟩ := o
  simp only [ansTy]; split <;> rfl

theorem ansesTy_persistent (S SN : Row) (R : VTy) :
    ∀ E : List (Qual × VTy × VTy), (ansesTy S SN R E).Persistent
  | [] => rfl
  | o :: E => by
      simp only [VTy.Persistent, VTy.persistent, ansesTy, Bool.and_eq_true]
      exact ⟨ansTy_persistent S SN R o, ansesTy_persistent S SN R E⟩

/-! ### Substitution and steps -/

theorem pickE_psub : ∀ (j k : Nat) (γ : List Val) (t : Expr),
    Expr.psub k γ (pickE j t) = pickE j (Expr.psub k γ t)
  | 0, k, γ, t => by simp [pickE, Expr.psub]
  | j + 1, k, γ, t => by
      simp only [pickE, Expr.psub]
      rw [pickE_psub j (k + 2) γ (.var 0)]
      simp [Expr.psub]

theorem pickE_subst : ∀ (j k : Nat) (s : Val) (t : Expr),
    Expr.subst k s (pickE j t) = pickE j (Expr.subst k s t)
  | 0, k, s, t => by simp [pickE]
  | j + 1, k, s, t => by
      simp only [pickE, Expr.subst]
      rw [pickE_subst j (k + 2) (s.shift 2 0) (.var 0)]
      simp

theorem tailClause_psub (j : Nat) (b : Bool) (γ : List Val) (Hc : Expr) :
    Expr.psub 0 γ (tailClause j b Hc) = tailClause j b (Expr.psub 0 γ Hc) := by
  cases b
  · have e := Expr.psub_shift 3 γ Hc 0
    simp only [Nat.zero_add] at e
    simp only [tailClause, Bool.false_eq_true, if_false, Expr.psub, pickE_psub, e, resumeB,
      Expr.val, Val.lam]
    simp [Val.inj₁, Val.unit, Expr.psub]
  · have e := Expr.psub_shift 1 γ Hc 0
    simp only [Nat.zero_add] at e
    simp only [tailClause, if_true, Expr.psub, pickE_psub, e]
    simp

theorem tailTuple_psub (γ : List Val) (Hc : Expr) :
    ∀ (E : List (Qual × VTy × VTy)) (j : Nat),
      Expr.psub 0 γ (tailTuple E j Hc) = tailTuple E j (Expr.psub 0 γ Hc)
  | [], _ => by simp [tailTuple, Expr.psub, Val.unit]
  | _ :: E, j => by
      simp only [tailTuple, Expr.psub, tailClause_psub, tailTuple_psub γ Hc E (j + 1)]

/-- A clause is a value. -/
theorem isVal_tailClause (j : Nat) (b : Bool) (Hc : Expr) : IsVal (tailClause j b Hc) := by
  cases b <;> simp only [tailClause, Bool.false_eq_true, if_false, if_true] <;> exact .lam

theorem isVal_tailTuple (Hc : Expr) :
    ∀ (E : List (Qual × VTy × VTy)) (j : Nat), IsVal (tailTuple E j Hc)
  | [], _ => .unit
  | _ :: E, j => .pair (isVal_tailClause _ _ _) (isVal_tailTuple Hc E (j + 1))

/-- The `j`-th clause of the tuple. -/
theorem clauseAt_tailTuple (Hc : Expr) :
    ∀ (E : List (Qual × VTy × VTy)) (k j : Nat) (hj : j < E.length),
      clauseAt (tailTuple E k Hc) j = some ⟨tailClause (k + j) (E[j].2.2.isZero && E[j].1 != .lin) Hc,
        isVal_tailClause _ _ _⟩
  | [], _, _, hj => by simp at hj
  | (q, A, B) :: E, k, 0, _ => by
      simp only [tailTuple, clauseAt, Nat.add_zero, dif_pos (isVal_tailClause k _ Hc)]
      rfl
  | (q, A, B) :: E, k, j + 1, hj => by
      simp only [tailTuple, clauseAt]
      rw [clauseAt_tailTuple Hc E (k + 1) j (by simpa using hj)]
      simp only [List.getElem_cons_succ]
      rw [show k + 1 + j = k + (j + 1) by omega]

/-- `pickE j` of a tuple value steps to its `j`-th component. -/
theorem pickE_steps : ∀ (j : Nat) (g r : Val) (vc : Val), vc = Val.pair g r →
    ∀ (gj : Val), (j = 0 → gj = g) → (∀ j', j = j' + 1 → PureSteps (pickE j' (.val r)) (.val gj)) →
      PureSteps (pickE j (.val vc)) (.val gj)
  | 0, g, r, _, rfl, gj, h0, _ => by
      refine (PureSteps.head (fun μ => Head.letpair μ g r _) rfl).trans ?_
      simp [h0 rfl]
      exact .refl
  | j + 1, g, r, _, rfl, gj, _, hs => by
      refine (PureSteps.head (fun μ => Head.letpair μ g r _) rfl).trans ?_
      simp only [pickE_subst, Expr.subst]
      simp [subst_shift_succ]
      exact hs j rfl

/-- **The answering functions**: a tuple of the answering functions' type holds, at each
operation, the function `pickE j` steps to, at the empty resource. -/
theorem ansesTy_at {S SN : Row} {R : VTy} {ls : List SRec} {δ : LSub} :
    ∀ (E : List (Qual × VTy × VTy)) {vc : Val} {ρ : WRes},
      vC true (ansesTy S SN R E) ls δ vc ρ →
      ∀ j (h : j < E.length), ∃ g, PureSteps (pickE j (.val vc)) (.val g) ∧
        vC true (ansTy S SN R E[j]) ls δ g PMap.empty
  | [], _, _, _, j, h => by simp at h
  | o :: E, vc, ρ, h, j, hj => by
      obtain ⟨g, rest, h⟩ := h
      obtain ⟨rfl, ρ₁, ρ₂, hc, hg, hr⟩ := pure_sep_iff.mp h
      have he : ρ₁ = PMap.empty := vP_empty_of_persistent (ansTy_persistent S SN R o) hg
      cases j with
      | zero =>
          exact ⟨g, pickE_steps 0 g rest _ rfl g (fun _ => rfl) (fun _ h => by cases h),
            he ▸ hg⟩
      | succ j =>
          obtain ⟨g', hs, hg'⟩ := ansesTy_at E hr j (by simpa using hj)
          exact ⟨g', pickE_steps (j + 1) g rest _ rfl g' (fun h => by cases h)
            (fun j' h => by cases h; exact hs), by simpa using hg'⟩

/-- The resume frame `(λw. κ.1 w) [·]`. -/
def resK (κ : Val) : Kont :=
  .appR (.val (Val.lam (.app (.app (.val (κ.shift 1 0)) (.val (Val.inj₁ .unit))) (.var 0)))) .hole

theorem resK_plain (κ : Val) :
    (∀ n, (resK κ).HasHnd n = false) ∧ (∀ n, (resK κ).Catches n = false) :=
  ⟨fun n => by simp [resK, Kont.HasHnd], fun n => by simp [resK, Kont.Catches]⟩

theorem resK_steps (κ w : Val) :
    PureSteps ((resK κ).plug (.val w)) (.app (.app (.val κ) (.val (Val.inj₁ .unit))) (.val w)) := by
  refine (PureSteps.beta _ w).trans ?_
  simp [subst_shift_succ]
  exact .refl

/-- A tail clause at `(v, κ)` resumes `κ` with `g v`. -/
theorem tailClause_steps (j : Nat) (vc g v κ : Val)
    (hg : PureSteps (pickE j (.val vc)) (.val g)) :
    PureSteps (.app (tailClause j false (.val vc)) (.val (Val.pair v κ)))
      ((resK κ).plug (.app (.val g) (.val v))) := by
  refine (PureSteps.beta _ _).trans ?_
  refine (PureSteps.head (fun μ => Head.letpair μ v κ _) rfl).trans ?_
  have e : ((Expr.subst 2 ((Val.pair v κ).shift 2 0) (.app (.val (Val.lam resumeB))
      (.app (pickE j ((Expr.val vc).shift 3 0)) (.var 1)))).subst 0 (κ.shift 1 0)).subst 0 v =
      (resK κ).plug (.app (pickE j (.val vc)) (.val v)) := by
    simp [pickE_subst, resumeB, resK, Kont.plug, subst_shift_succ]
  rw [e]
  have := PureSteps.plug ((resK κ).comp (.appL .hole v)) hg
  rw [Kont.plug_comp, Kont.plug_comp] at this
  exact this

/-- A tail clause of an abortive operation at `v` runs `g v`. -/
theorem tailClauseA_steps (j : Nat) (vc g v : Val)
    (hg : PureSteps (pickE j (.val vc)) (.val g)) :
    PureSteps (.app (tailClause j true (.val vc)) (.val v)) (.app (.val g) (.val v)) := by
  refine (PureSteps.beta _ _).trans ?_
  have e : Expr.subst 0 v (.app (pickE j ((Expr.val vc).shift 1 0)) (.var 0)) =
      (Kont.appL .hole v).plug (pickE j (.val vc)) := by
    simp [pickE_subst, Kont.plug, subst_shift_succ]
  rw [e]
  exact PureSteps.plug (.appL .hole v) hg

/-! ### The rows -/

theorem Row.tab_ofEff_ne {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32}
    (δ : LSub) {m i : UInt32} (hm : m ≠ n) :
    Row.tab (Row.ofEff n E 0 fs ++ S) δ m i = Row.tab S δ m i := by
  simp [Row.tab, Row.find_append, Row.find_ofEff_ne n E 0 fs m i hm]

/-- A handled row of another name holds `Div` as the outer row does. -/
theorem Row.divB_ofEff_eq {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32}
    (hnd : n ≠ divEff) : Row.divB (Row.ofEff n E 0 fs ++ S) = Row.divB S := by
  have hf : Row.find (Row.ofEff n E 0 fs ++ S) divEff 0 = Row.find S divEff 0 := by
    rw [Row.find_append, Row.find_ofEff_ne n E 0 fs _ _ (Ne.symm hnd)]; rfl
  cases h : Row.divB S
  · cases h' : Row.divB (Row.ofEff n E 0 fs ++ S)
    · rfl
    · obtain ⟨o, hfo, ho⟩ := Row.divB_find h'
      rw [hf] at hfo
      rw [Row.divB_iff.mpr ⟨o, hfo, ho⟩] at h; cases h
  · obtain ⟨o, hfo, ho⟩ := Row.divB_find h
    exact Row.divB_iff.mpr ⟨o, by rw [hf]; exact hfo, ho⟩

/-- A row of must-resume operations: every entry at `lin`, none abortive. -/
theorem Row.tab_lin {SN : Row} (hLin : ∀ o ∈ SN, o.q = .lin ∧ o.abort = false) (δ : LSub)
    {n i : UInt32} {en : OpEnt} (h : Row.tab SN δ n i = some en) : en.q = .lin ∧ en.abort = false := by
  obtain ⟨o, hf, rfl⟩ := Row.tab_some h
  exact hLin o (Row.find_mem hf).1

/-! ### `κ` in the resume frame -/

theorem KapRelT.same {Tb : Table} {Qout : List SRec → Val → WProp} {en : OpEnt} {Tc : Option OpTab}
    {κ : Val} : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) →
      Entails (KapRelT Tb Qout en Tc ls κ) (KapRelT Tb Qout en Tc ls' κ) :=
  fun _ _ hs σ h => ⟨h.1, fun ls'' he => h.2 ls'' ((ext_of_same hs σ).trans he)⟩

theorem KapRelT.ext {Tb : Table} {Qout : List SRec → Val → WProp} {en : OpEnt} {Tc : Option OpTab}
    {κ : Val} : ∀ ls ls' ρ, Ext ls ls' ρ → KapRelT Tb Qout en Tc ls κ ρ →
      KapRelT Tb Qout en Tc ls' κ ρ :=
  fun _ _ _ he h => ⟨h.1, fun ls'' he' => h.2 ls'' (he.trans he')⟩

/-- The resumption of `κ` at an answer, in the resume frame. -/
theorem kapRelT_resume {Tb : Table} (hTb : Tb.Mono) {Qout : List SRec → Val → WProp} {en : OpEnt}
    {Tc : Option OpTab} {κ : Val} {ls : List SRec} {w : Val} {σ : WRes}
    (h : (en.PB ls w ⋆ KapRelT Tb Qout en Tc ls κ) σ) :
    ewpTS ls ((resK κ).plug (.val w)) Tb Qout σ := by
  obtain ⟨σ₁, σ₂, hc, hw, hk⟩ := h
  exact ewp_pureSteps hTb (resK_steps κ w) _ _ σ
    ((hk.2 ls (Ext.refl ls σ₂)).1 w σ₁ σ (by exact hw) (ResU.CompS.comm hc))

/-- The frame conditions at a row of must-resume operations, for any frame. -/
theorem lin_conds {T : OpTab} (hL : ∀ n i en, T n i = some en → en.q = .lin ∧ en.abort = false)
    (K : Kont) (Fr : List SRec → WProp) :
    (∀ n i en, T n i = some en → en.abort = true → ∀ ls ρ, Fr ls ρ → NoOwn ρ) ∧
    (∀ n i en, T n i = some en → en.q = .unr → ∀ ls ρ, Fr ls ρ → ρ = PMap.empty) ∧
    (∀ n i en, T n i = some en → en.abort = false → en.q ≠ .lin →
      ∀ ls K₁ ρ σ ρ', cancelOK en ls K₁ ρ → Fr ls σ → ResU.CompS ρ σ ρ' →
        cancelOK en ls (K.comp K₁) ρ') :=
  ⟨fun n i en h ha => absurd ha (by simp [(hL n i en h).2]),
   fun n i en h hq => absurd hq (by simp [(hL n i en h).1]),
   fun n i en h _ hq => absurd (hL n i en h).1 hq⟩

/-! ### The handler -/

/-- The handler value of a tail-resuming handler: the clauses written out from the tuple. -/
def tailH (n : UInt32) (E : List (Qual × VTy × VTy)) (vr vc : Val) : Val :=
  hndVal n (qualsVal (E.map Prod.fst)) vr ⟨tailTuple E 0 (.val vc), isVal_tailTuple _ E 0⟩

section
variable {δ : LSub} {S SN : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32}
  {A R : VTy} (hnd : n ≠ divEff) (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n)
  (hlen : E.length ≤ 2 ^ 32) (hSN : RowLe SN S) (hLin : ∀ o ∈ SN, o.q = .lin ∧ o.abort = false)
  {vr vc : Val} {ls₀ : List SRec}
  (hVr : vC true (retTy S A R) ls₀ δ vr PMap.empty)
  (hVc : vC true (ansesTy S SN R E) ls₀ δ vc PMap.empty)

include hnS hlen hVc in
/-- The clause of an operation of the handler, from its entry. -/
theorem tail_clause_of {i : UInt32} {en : OpEnt}
    (hT : Row.tab (Row.ofEff n E 0 fs ++ S) δ n i = some en) :
    ∃ j, ∃ hj : j < E.length, en = OpSig.ent δ ⟨n, UInt32.ofNat (0 + j), E[j].1, E[j].2.1,
      E[j].2.2, fs j, false⟩ ∧
      clauseAt (tailTuple E 0 (.val vc)) i.toNat =
        some ⟨tailClause j en.abort (.val vc), isVal_tailClause _ _ _⟩ ∧
      ∃ g, PureSteps (pickE j (.val vc)) (.val g) ∧
        vC true (ansTy S SN R E[j]) ls₀ δ g PMap.empty := by
  obtain ⟨j, hj, hji, -, rfl⟩ := Row.tab_ofEff_self hnS hlen hT
  obtain ⟨g, hg, hVg⟩ := ansesTy_at E hVc j hj
  refine ⟨j, hj, rfl, ?_, g, hg, hVg⟩
  rw [hji, clauseAt_tailTuple _ E 0 j hj]
  simp [OpSig.ent, OpSig.abort]

include hnd hn0 hnS hlen hSN hLin hVr hVc in
/-- **`Closing` under a tail-resuming handler**: Core's `ewp_handle` at the closing tables; a
clause's answering function is in `Closing` at its must-resume row, under the resume frame. -/
theorem tail_closing (hSd : Row.divB S = true) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : Closing (Row.tab (Row.ofEff n E 0 fs ++ S) δ) (fun ls v => vC true A ls δ v) ls e ρ) :
    Closing (Row.tab S δ) (fun ls v => vC true R ls δ v) ls (hndE (tailH n E vr vc) e) ρ := by
  have hTo := Row.divOK_of_divB hSd δ
  have hTN := Row.divOK_of_le hSN hSd δ
  have hSNle := Row.tab_le δ hSN
  refine ewp_handle _ _ n hn0 ?_ (qualsVal (E.map Prod.fst)) vr _ _ _ (fun _ => none) ?_
    (fun _ _ _ _ _ _ h => by cases h) ?_ ?_ h
  · intro m i hm
    unfold OpTab.closeAt
    rw [Row.tab_ofEff_ne δ hm]
  · intro i en hT ha
    have hk : ¬ (n = divEff ∧ i = 0) := fun h => hnd h.1
    rw [OpTab.closeAt_ne hk] at hT
    rw [capTag_ofEff hnS hlen i en hT]
  · intro ls' v σ hv
    have hf := (hVr.2 ls' (ext_empty' ls₀ ls')) v σ σ hv (compS_empty_left σ)
    have := (cC_effOf_wp S R ls' δ _ σ).mp hf
    rw [hSd] at this
    exact closing_of_cwp this
  · intro i en hT
    have hk : ¬ (n = divEff ∧ i = 0) := fun h => hnd h.1
    rw [OpTab.closeAt_ne hk] at hT
    obtain ⟨j, hj, rfl, hcl, g, hg, hVg⟩ := tail_clause_of hnS hlen hVc hT
    refine ⟨_, hcl, fun ha ls' v κ σ hσ => ?_, fun ha ls' v σ hσ => ?_⟩
    · -- the clause resumes `κ` with `g v`, under the resume frame
      show ewpTS ls' (.app (tailClause j (OpSig.ent δ _).abort (.val vc)) (.pair (.val v) κ.1)) _ _ σ
      rw [ha]
      generalize hEj : E[j] = t at hVg ha hσ
      obtain ⟨q, A', B'⟩ := t
      simp only [OpSig.ent, OpSig.abort] at ha hσ
      simp only [ansTy, ha] at hVg
      obtain ⟨σa, σk, hck, hA', hK⟩ := hσ
      refine ewp_pureSteps (opTable_mono _) (tailClause_steps j vc g v κ hg) _ _ σ ?_
      have hy := (hVg.2 ls' (ext_empty' ls₀ ls')) v σa σa hA' (compS_empty_left σa)
      have hy' := (cC_effOf_wp SN B' ls' δ _ σa).mp hy
      have hyc : Closing (Row.tab SN δ) (fun ls w => vC true B' ls δ w) ls' (.app (.val g) (.val v))
          σa := by
        cases hb : Row.divB SN <;> rw [hb] at hy'
        · exact closing_of_ewp hy'
        · exact closing_of_cwp hy'
      obtain ⟨hW, hU, hK'⟩ := lin_conds (fun _ _ _ h => Row.tab_lin hLin δ h) (resK κ)
        (fun ls => KapRelT (opTable (Row.tab S δ).closeAt) (fun ls v => vC true R ls δ v)
          (OpSig.ent δ ⟨n, UInt32.ofNat (0 + j), q, A', B', fs j, false⟩) none ls κ)
      exact closing_frame hSNle (resK κ) (resK_plain κ).1 (resK_plain κ).2 _ KapRelT.same
        KapRelT.ext hW hU hK' _ _ (fun ls w τ hτ => kapRelT_resume (opTable_mono _) hτ) hyc hK
        hck
    · -- an abortive operation's clause runs `g v`, at the outer row
      show ewpTS ls' (.app (tailClause j (OpSig.ent δ _).abort (.val vc)) (.val v)) _ _ σ
      rw [ha]
      generalize hEj : E[j] = t at hVg ha hσ
      obtain ⟨q, A', B'⟩ := t
      simp only [OpSig.ent, OpSig.abort] at ha hσ
      simp only [ansTy, ha] at hVg
      refine ewp_pureSteps (opTable_mono _) (tailClauseA_steps j vc g v hg) _ _ σ ?_
      have hy := (hVg.2 ls' (ext_empty' ls₀ ls')) v σ σ hσ (compS_empty_left σ)
      have hy' := (cC_effOf_wp S R ls' δ _ σ).mp hy
      rw [hSd] at hy'
      exact closing_of_cwp hy'

end

/-! ### The candidate -/

/-- The handled computations. -/
def tailW₁ (Ti : OpTab) (Qin : List SRec → Val → WProp) (H : Val) : CPred :=
  fun ls x ρ => ∃ e, x = hndE H e ∧ cwp Ti Qin ls e ρ

/-- The resume frame around a computation of the clause's row, `κ` resumed into one segment of
`Z`. -/
def tailW₂ (TN To : OpTab) (Qout : List SRec → Val → WProp) (Z : CPred) : CPred :=
  fun ls x ρ => ∃ (κ : Val) (y : Expr) (en : OpEnt) (ρy ρk : WRes), x = (resK κ).plug y ∧
    cwp TN en.PB ls y ρy ∧ KapRelT (divTab To Qout Z) Qout en none ls κ ρk ∧ ResU.CompS ρy ρk ρ

/-- One step of the candidate. -/
def tailG (Ti TN To : OpTab) (Qin Qout : List SRec → Val → WProp) (H : Val) (Z : CPred) : CPred :=
  fun ls x ρ => tailW₁ Ti Qin H ls x ρ ∨ tailW₂ TN To Qout Z ls x ρ ∨ cwp To Qout ls x ρ

/-- **The candidate**: the least fixed point of `tailG`. -/
def tailY (Ti TN To : OpTab) (Qin Qout : List SRec → Val → WProp) (H : Val) : CPred :=
  fun ls x ρ => ∀ Z : CPred, (∀ ls x ρ, tailG Ti TN To Qin Qout H Z ls x ρ → Z ls x ρ) → Z ls x ρ

section candidate
variable {Ti TN To : OpTab} {Qin Qout : List SRec → Val → WProp} {H : Val}

theorem tailG_mono {Z Z' : CPred} (h : ∀ ls x ρ, Z ls x ρ → Z' ls x ρ) {ls : List SRec} {x : Expr}
    {ρ : WRes} (hg : tailG Ti TN To Qin Qout H Z ls x ρ) : tailG Ti TN To Qin Qout H Z' ls x ρ := by
  rcases hg with hg | ⟨κ, y, en, ρy, ρk, rfl, hy, hk, hc⟩ | hg
  · exact Or.inl hg
  · refine Or.inr (Or.inl ⟨κ, y, en, ρy, ρk, rfl, hy, KapRelT.mono (fun _ _ _ h' => ?_) hk, hc⟩)
    exact ewp_mono (divTab_mono _ _ _) (fun _ _ _ _ hd => divTab_le h (fun _ _ _ h => h) hd)
      (fun _ _ _ h => h) h'
  · exact Or.inr (Or.inr hg)

theorem tailY_fold {ls : List SRec} {x : Expr} {ρ : WRes}
    (h : tailG Ti TN To Qin Qout H (tailY Ti TN To Qin Qout H) ls x ρ) :
    tailY Ti TN To Qin Qout H ls x ρ :=
  fun Z hZ => hZ _ _ _ (tailG_mono (fun _ _ _ hy => hy Z hZ) h)

theorem tailY_unfold {ls : List SRec} {x : Expr} {ρ : WRes} (h : tailY Ti TN To Qin Qout H ls x ρ) :
    tailG Ti TN To Qin Qout H (tailY Ti TN To Qin Qout H) ls x ρ :=
  h _ fun _ _ _ hg => tailG_mono (fun _ _ _ h => tailY_fold h) hg

end candidate

section
variable {δ : LSub} {S SN : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32}
  {A R : VTy} (hnd : n ≠ divEff) (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n)
  (hlen : E.length ≤ 2 ^ 32) (hSN : RowLe SN S) (hLin : ∀ o ∈ SN, o.q = .lin ∧ o.abort = false)
  {vr vc : Val} {ls₀ : List SRec}
  (hVr : vC true (retTy S A R) ls₀ δ vr PMap.empty)
  (hVc : vC true (ansesTy S SN R E) ls₀ δ vc PMap.empty)

include hnd hn0 hnS hlen hSN hLin hVr hVc in
/-- **`[handle]` of another name at clauses that resume in tail position**, at a row holding
`Div`, by coinduction with the candidate `tailY`.  `[spec §14, §19]` -/
theorem cwp_handle_tail (hSd : Row.divB S = true) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : cwp (Row.tab (Row.ofEff n E 0 fs ++ S) δ) (fun ls v => vC true A ls δ v) ls e ρ) :
    cwp (Row.tab S δ) (fun ls v => vC true R ls δ v) ls (hndE (tailH n E vr vc) e) ρ := by
  have hSbd : Row.divB (Row.ofEff n E 0 fs ++ S) = true := by rw [Row.divB_ofEff_eq hnd]; exact hSd
  have hTi := Row.divOK_of_divB hSbd δ
  have hTo := Row.divOK_of_divB hSd δ
  have hTN := Row.divOK_of_le hSN hSd δ
  have hSNle := Row.tab_le δ hSN
  obtain ⟨o, hfo, hto⟩ := Row.divB_find hSd
  have hTo0 : Row.tab S δ divEff 0 = some (o.ent δ) := Row.tab_find hfo
  have hTo0' := OpSig.isTick_ent δ hto
  -- the parts of the candidate, one segment each
  have hc : ∀ ls x ρ, cwp (Row.tab S δ) (fun ls v => vC true R ls δ v) ls x ρ →
      cwpF (Row.tab S δ) (fun ls v => vC true R ls δ v) (tailY (Row.tab (Row.ofEff n E 0 fs ++ S) δ)
        (Row.tab SN δ) (Row.tab S δ) (fun ls v => vC true A ls δ v) (fun ls v => vC true R ls δ v)
        (tailH n E vr vc)) ls x ρ :=
    fun _ _ _ h => cwpF_mono (fun _ _ _ h => tailY_fold (Or.inr (Or.inr h))) (cwp_out h)
  have hW₂ : ∀ ls x ρ, tailW₂ (Row.tab SN δ) (Row.tab S δ) (fun ls v => vC true R ls δ v)
      (tailY (Row.tab (Row.ofEff n E 0 fs ++ S) δ) (Row.tab SN δ) (Row.tab S δ)
        (fun ls v => vC true A ls δ v) (fun ls v => vC true R ls δ v) (tailH n E vr vc)) ls x ρ →
      cwpF (Row.tab S δ) (fun ls v => vC true R ls δ v) (tailY (Row.tab (Row.ofEff n E 0 fs ++ S) δ)
        (Row.tab SN δ) (Row.tab S δ) (fun ls v => vC true A ls δ v) (fun ls v => vC true R ls δ v)
        (tailH n E vr vc)) ls x ρ := by
    rintro ls x ρ ⟨κ, y, en, ρy, ρk, rfl, hy, hk, hcy⟩
    obtain ⟨hW, hU, hK⟩ := lin_conds (fun _ _ _ h => Row.tab_lin hLin δ h) (resK κ)
      (fun ls => KapRelT (divTab (Row.tab S δ) (fun ls v => vC true R ls δ v) _) _ en none ls κ)
    exact cwpF_frame hTN hTo hSNle (resK κ) (resK_plain κ).1 (resK_plain κ).2 _ KapRelT.same
      KapRelT.ext hW hU hK en.PB _ _
      (fun ls y' ρ' ρ₂ ρ'' hy' hF hc' => tailY_fold (Or.inr (Or.inl ⟨κ, y', en, ρ', ρ₂, rfl, hy', hF,
        hc'⟩)))
      (fun ls w σ hσ => kapRelT_resume (divTab_mono _ _ _) hσ)
      (fun ls w σ hσ => closing_of_cwpF (kapRelT_resume (divTab_mono _ _ _) hσ)) hy hk hcy
  have hW₁ : ∀ ls x ρ, tailW₁ (Row.tab (Row.ofEff n E 0 fs ++ S) δ) (fun ls v => vC true A ls δ v)
      (tailH n E vr vc) ls x ρ →
      cwpF (Row.tab S δ) (fun ls v => vC true R ls δ v) (tailY (Row.tab (Row.ofEff n E 0 fs ++ S) δ)
        (Row.tab SN δ) (Row.tab S δ) (fun ls v => vC true A ls δ v) (fun ls v => vC true R ls δ v)
        (tailH n E vr vc)) ls x ρ := by
    rintro ls x ρ ⟨e, rfl, he⟩
    refine ewp_handle_or _ _ _ _ (Table.Const.mono fun _ _ _ _ _ h => h) n hn0 ?_
      (qualsVal (E.map Prod.fst)) vr _ _ _ (fun _ => none) ?_ (fun _ _ _ _ _ _ h => by cases h)
      ?_ ?_ ?_ (cwp_out he)
    · intro m i hm
      unfold OpTab.erase0
      rw [Row.tab_ofEff_ne δ hm]
    · intro i en hT ha
      have hk : ¬ (n = divEff ∧ i = 0) := fun h => hnd h.1
      rw [OpTab.erase0_ne hk] at hT
      rw [capTag_ofEff hnS hlen i en hT]
    · -- a tick passes the handler
      intro ls' t Φ Φ' σ hp
      obtain ⟨K₁, en, rfl, hK₁, hT0, ht, hcont⟩ := tickStop_inv hTi hp
      rw [← Kont.plug_comp]
      refine tickStop_mk hTo0 hTo0' ((hndK (tailH n E vr vc)).comp K₁)
        (by rw [hasHnd_comp, hK₁]; simp [tailH, hndK_hasHnd]; exact hnd) fun ls'' he w hw => ?_
      have ho := hcont ls'' he w hw
      rw [Kont.plug_comp]
      exact ⟨tailY_fold (Or.inl ⟨_, rfl, ho.1⟩),
        tail_closing hnd hn0 hnS hlen hSN hLin hVr hVc hSd ho.2⟩
    · intro ls' v σ hv
      have hf := (hVr.2 ls' (ext_empty' ls₀ ls')) v σ σ hv (compS_empty_left σ)
      have := (cC_effOf_wp S R ls' δ _ σ).mp hf
      rw [hSd] at this
      exact hc _ _ _ this
    · intro i en hT
      have hk : ¬ (n = divEff ∧ i = 0) := fun h => hnd h.1
      rw [OpTab.erase0_ne hk] at hT
      obtain ⟨j, hj, rfl, hcl, g, hg, hVg⟩ := tail_clause_of hnS hlen hVc hT
      refine ⟨_, hcl, fun ha ls' v κ σ hσ => ?_, fun ha ls' v σ hσ => ?_⟩
      · show ewpTS ls' (.app (tailClause j (OpSig.ent δ _).abort (.val vc)) (.pair (.val v) κ.1)) _
          _ σ
        rw [ha]
        generalize hEj : E[j] = t at hVg ha hσ
        obtain ⟨q, A', B'⟩ := t
        have ha' : (B'.isZero && q != .lin) = false := ha
        simp only [ansTy, ha'] at hVg
        obtain ⟨σa, σk, hck, hA', hK⟩ := hσ
        have hA'' : vC true A' ls' δ v σa := hA'
        refine ewp_pureSteps (divTab_mono _ _ _) (tailClause_steps j vc g v κ hg) _ _ σ ?_
        have hy := (hVg.2 ls' (ext_empty' ls₀ ls')) v σa σa hA'' (compS_empty_left σa)
        have hy' := (cC_effOf_wp SN B' ls' δ _ σa).mp hy
        have hyc : cwp (Row.tab SN δ) (OpSig.ent δ ⟨n, UInt32.ofNat (0 + j), q, A', B', fs j, false⟩).PB ls'
            (.app (.val g) (.val v)) σa := by
          cases hb : Row.divB SN <;> rw [hb] at hy'
          · exact cwp_of_ewp hTN.keyNA hy'
          · exact hy'
        exact hW₂ _ _ _ ⟨κ, _, _, σa, σk, rfl, hyc, hK, hck⟩
      · show ewpTS ls' (.app (tailClause j (OpSig.ent δ _).abort (.val vc)) (.val v)) _ _ σ
        rw [ha]
        generalize hEj : E[j] = t at hVg ha hσ
        obtain ⟨q, A', B'⟩ := t
        simp only [OpSig.ent, OpSig.abort] at ha hσ
        simp only [ansTy, ha] at hVg
        refine ewp_pureSteps (divTab_mono _ _ _) (tailClauseA_steps j vc g v hg) _ _ σ ?_
        have hy := (hVg.2 ls' (ext_empty' ls₀ ls')) v σ σ hσ (compS_empty_left σ)
        have hy' := (cC_effOf_wp S R ls' δ _ σ).mp hy
        rw [hSd] at hy'
        exact hc _ _ _ hy'
  refine cwp_coind (W := tailY (Row.tab (Row.ofEff n E 0 fs ++ S) δ) (Row.tab SN δ) (Row.tab S δ)
    (fun ls v => vC true A ls δ v) (fun ls v => vC true R ls δ v) (tailH n E vr vc))
    (fun ls x ρ hy => ?_) (tailY_fold (Or.inl ⟨e, rfl, h⟩))
  rcases tailY_unfold hy with hx | hx | hx
  · exact hW₁ _ _ _ hx
  · exact hW₂ _ _ _ hx
  · exact hc _ _ _ hx

end

section
variable {δ : LSub} {S SN : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32}
  {A R : VTy} (hnd : n ≠ divEff) (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n)
  (hlen : E.length ≤ 2 ^ 32) (hSN : RowLe SN S) (hLin : ∀ o ∈ SN, o.q = .lin ∧ o.abort = false)
  {vr vc : Val} {ls₀ : List SRec}
  (hVr : vC true (retTy S A R) ls₀ δ vr PMap.empty)
  (hVc : vC true (ansesTy S SN R E) ls₀ δ vc PMap.empty)

include hnd hn0 hnS hlen hSN hLin hVr hVc in
/-- **A tail-resuming handler at a row that does not hold `Div`**: Core's `ewp_handle`; a
clause's answering function runs at its must-resume row under the resume frame. -/
theorem ewp_handle_tail (hSd : Row.divB S = false) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : ewpTS ls e (opTable (Row.tab (Row.ofEff n E 0 fs ++ S) δ)) (fun ls v => vC true A ls δ v) ρ) :
    ewpTS ls (hndE (tailH n E vr vc) e) (opTable (Row.tab S δ)) (fun ls v => vC true R ls δ v) ρ := by
  have hSNd : Row.divB SN = false := by
    cases hb : Row.divB SN
    · rfl
    · rw [Row.divB_le hSN hb] at hSd; cases hSd
  have hSNle := Row.tab_le δ hSN
  refine ewp_handle _ _ n hn0 (fun m i hm => Row.tab_ofEff_ne δ hm) (qualsVal (E.map Prod.fst)) vr
    _ _ _ (fun _ => none) (fun i en hT _ => capTag_ofEff hnS hlen i en hT)
    (fun _ _ _ _ _ _ h => by cases h) ?_ ?_ h
  · intro ls' v σ hv
    have hf := (hVr.2 ls' (ext_empty' ls₀ ls')) v σ σ hv (compS_empty_left σ)
    exact (cC_effOf S R ls' δ _ σ hSd).mp hf
  · intro i en hT
    obtain ⟨j, hj, rfl, hcl, g, hg, hVg⟩ := tail_clause_of hnS hlen hVc hT
    refine ⟨_, hcl, fun ha ls' v κ σ hσ => ?_, fun ha ls' v σ hσ => ?_⟩
    · show ewpTS ls' (.app (tailClause j (OpSig.ent δ _).abort (.val vc)) (.pair (.val v) κ.1)) _ _ σ
      rw [ha]
      generalize hEj : E[j] = t at hVg ha hσ
      obtain ⟨q, A', B'⟩ := t
      have ha' : (B'.isZero && q != .lin) = false := ha
      simp only [ansTy, ha'] at hVg
      obtain ⟨σa, σk, hck, hA', hK⟩ := hσ
      have hA'' : vC true A' ls' δ v σa := hA'
      refine ewp_pureSteps (opTable_mono _) (tailClause_steps j vc g v κ hg) _ _ σ ?_
      have hy := (hVg.2 ls' (ext_empty' ls₀ ls')) v σa σa hA'' (compS_empty_left σa)
      have hy' : ewpTS ls' (.app (.val g) (.val v)) (opTable (Row.tab SN δ))
          (OpSig.ent δ ⟨n, UInt32.ofNat (0 + j), q, A', B', fs j, false⟩).PB σa :=
        (cC_effOf SN B' ls' δ _ σa hSNd).mp hy
      obtain ⟨hW, hU, hK'⟩ := lin_conds (fun _ _ _ h => Row.tab_lin hLin δ h) (resK κ)
        (fun ls => KapRel (Row.tab S δ) (fun ls v => vC true R ls δ v)
          (OpSig.ent δ ⟨n, UInt32.ofNat (0 + j), q, A', B', fs j, false⟩) none ls κ)
      exact (ewp_orBot (opTable_mono _)).mp (ewp_frame_plain_or _ _ hSNle Table.bot Table.bot
        Table.bot_const.mono (resK κ) (resK_plain κ).1 (resK_plain κ).2 _ KapRelT.same KapRelT.ext
        hW hU hK' (fun _ _ _ _ _ _ _ h => h.elim) _ _
        (fun ls w τ hτ => (ewp_orBot (opTable_mono _)).mpr (kapRelT_resume (opTable_mono _) hτ))
        ((ewp_orBot (opTable_mono _)).mpr hy') hK hck)
    · show ewpTS ls' (.app (tailClause j (OpSig.ent δ _).abort (.val vc)) (.val v)) _ _ σ
      rw [ha]
      generalize hEj : E[j] = t at hVg ha hσ
      obtain ⟨q, A', B'⟩ := t
      have ha' : (B'.isZero && q != .lin) = true := ha
      simp only [ansTy, ha'] at hVg
      refine ewp_pureSteps (opTable_mono _) (tailClauseA_steps j vc g v hg) _ _ σ ?_
      have hy := (hVg.2 ls' (ext_empty' ls₀ ls')) v σ σ hσ (compS_empty_left σ)
      exact (cC_effOf S R ls' δ _ σ hSd).mp hy

end

/-- **`[handle]` at clauses that resume `κ` in tail position**: `handle_n e with (h_ret, gs)`, the
clauses written out from the answering functions `gs` (`tailTuple`).  At a row holding `Div` the
handled computation's ticks pass the handler (`cwp_handle_tail`); elsewhere it is Core's handler
(`ewp_handle_tail`).  `[spec §14, §19]` -/
theorem handleT_compatC {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {Hr Hc e : Expr} {S SN : Row}
    {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {A R : VTy}
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₁) (hHr : Hr.ValFormIn Γ₁) (hHc : Hc.ValFormIn Γ₁)
    (hc : SemV Δ Γ₁ (.pair Hr Hc) (.tensor (retTy S A R) (ansesTy S SN R E)))
    (hn0 : n ≠ 0) (hnd : n ≠ divEff) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hSN : RowLe SN S) (hLin : ∀ o ∈ SN, o.q = .lin ∧ o.abort = false)
    (he : SemC Δ Γ₂ e (CTy.effOf (Row.ofEff n E 0 fs ++ S) A)) :
    SemC Δ Γ (hndExpr n (E.map Prod.fst) (.pair Hr (tailTuple E 0 Hc)) e) (CTy.effOf S R) := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc12, hg₁, hg₂⟩ := gDenC_split hsp hg
  obtain ⟨hlw₁, hs₁⟩ := gDenC_iff.mp hg₁
  have hρ₁ : ρ₁ = PMap.empty := gSepC_deadP hd hs₁
  subst hρ₁
  rw [eq_of_compS_empty_left hc12]
  have hval : IsVal (substAll γ (.pair Hr Hc)) := isVal_psub_valFormIn hlw₁ (.pair hHr hHc)
  have hH' := hc δ γ ls PMap.empty hδ hg₁
  have hE' := (cC_effOf_wp _ A ls δ _ ρ₂).mp (he δ γ ls ρ₂ hδ hg₂)
  rw [Row.divB_ofEff_eq hnd] at hE'
  show cC _ ls δ (Expr.psub 0 γ (hndExpr n (E.map Prod.fst) (.pair Hr (tailTuple E 0 Hc)) e)) ρ₂
  rw [psub_hndExpr]
  simp only [Expr.psub]
  rw [show Expr.psub 0 γ (tailTuple E 0 Hc) = tailTuple E 0 (substAll γ Hc) from tailTuple_psub γ Hc E 0]
  refine (cC_effOf_wp S R ls δ _ ρ₂).mpr ?_
  have hT₀ : (VTy.tensor (retTy S A R) (ansesTy S SN R E)).Persistent := by
    simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true]
    exact ⟨retTy_persistent S A R, ansesTy_persistent S SN R E⟩
  -- the handler's value, read off `wpTS` at the run's start
  have key : ∀ (ρf fρ : WRes) (ps : List FrameRec), ResU.Hash ρf ρ₂ → ResU.CompS ρf ρ₂ fρ →
      TW fρ ps (rsOf ls) → Tagged fρ ps ls → ∃ ls' vr vc,
        Expr.psub 0 γ Hr = vr.1 ∧ substAll γ Hc = vc.1 ∧
        vC true (retTy S A R) ls' δ vr PMap.empty ∧ vC true (ansesTy S SN R E) ls' δ vc PMap.empty := by
    intro ρf fρ ps hf hcf hT htg
    obtain ⟨ls', ρ', -, hv⟩ := wpTS_val_post (v := ⟨substAll γ (.pair Hr Hc), hval⟩) hH'
      (ResU.hash_empty_right (hash_valid_comp hf hcf)) (ResU.comp_empty_right fρ) hT htg
    have hρ' : ρ' = PMap.empty := vP_empty_of_persistent hT₀ hv
    subst hρ'
    obtain ⟨vr, vc, h⟩ := hv
    obtain ⟨hpair, σ₁, σ₂, -, hVr, hVc⟩ := pure_sep_iff.mp h
    have hσ₁ : σ₁ = PMap.empty := vP_empty_of_persistent (retTy_persistent S A R) hVr
    have hσ₂ : σ₂ = PMap.empty := vP_empty_of_persistent (ansesTy_persistent S SN R E) hVc
    subst hσ₁ hσ₂
    have hHe : substAll γ (.pair Hr Hc) = (Val.pair vr vc).1 := congrArg Subtype.val hpair
    simp only [substAll, Expr.psub, Val.pair] at hHe
    obtain ⟨h₁, h₂⟩ := Expr.pair.inj hHe
    exact ⟨ls', vr, vc, h₁, h₂, hVr, hVc⟩
  cases hSd : Row.divB S <;> rw [hSd] at hE'
  · refine ewp_fold (opTable_mono _) ?_
    intro ρf fρ ps hf hcf hT htg Al k
    obtain ⟨ls', vr, vc, h₁, h₂, hVr, hVc⟩ := key ρf fρ ps hf hcf hT htg
    rw [h₁, h₂]
    exact ewp_unfold (opTable_mono _) (ewp_handle_tail (fs := fs) hnd hn0 hnS hlen hSN hLin hVr hVc
      hSd hE') ρf fρ ps hf hcf hT htg Al k
  · refine cwp_roll (ewp_fold (divTab_mono _ _ _) ?_)
    intro ρf fρ ps hf hcf hT htg Al k
    obtain ⟨ls', vr, vc, h₁, h₂, hVr, hVc⟩ := key ρf fρ ps hf hcf hT htg
    rw [h₁, h₂]
    exact ewp_unfold (divTab_mono _ _ _) (cwp_out (cwp_handle_tail (fs := fs) hnd hn0 hnS hlen hSN
      hLin hVr hVc hSd hE')) ρf fρ ps hf hcf hT htg Al k

/-! ### Closed terms -/

theorem closedAt_shift_add (d : Nat) : ∀ (e : Expr) (k c : Nat), closedAt k e = true →
    closedAt (k + d) (e.shift d c) = true
  | .var i, k, c, h => by
      simp only [closedAt, decide_eq_true_eq] at h
      simp only [Expr.shift]; split <;> simp [closedAt] <;> omega
  | .unit, _, _, _ => rfl
  | .pair a b, k, c, h => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.shift, closedAt, closedAt_shift_add d a k c h.1, closedAt_shift_add d b k c h.2,
        Bool.and_self]
  | .inj₁ a, k, c, h => closedAt_shift_add d a k c h
  | .inj₂ a, k, c, h => closedAt_shift_add d a k c h
  | .lam b, k, c, h => by
      have := closedAt_shift_add d b (k + 1) (c + 1) h
      simp only [Expr.shift, closedAt]; rwa [show k + d + 1 = k + 1 + d by omega]
  | .loc _, _, _, _ => rfl
  | .prim _, _, _, _ => rfl
  | .seq a b, k, c, h => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.shift, closedAt, closedAt_shift_add d a k c h.1, closedAt_shift_add d b k c h.2,
        Bool.and_self]
  | .letpair a b, k, c, h => by
      simp only [closedAt, Bool.and_eq_true] at h
      have hb := closedAt_shift_add d b (k + 2) (c + 2) h.2
      simp only [Expr.shift, closedAt, closedAt_shift_add d a k c h.1, Bool.true_and]
      rwa [show k + d + 2 = k + 2 + d by omega]
  | .case a b₁ b₂, k, c, h => by
      simp only [closedAt, Bool.and_eq_true] at h
      have h₁ := closedAt_shift_add d b₁ (k + 1) (c + 1) h.1.2
      have h₂ := closedAt_shift_add d b₂ (k + 1) (c + 1) h.2
      simp only [Expr.shift, closedAt, closedAt_shift_add d a k c h.1.1, Bool.true_and,
        Bool.and_eq_true]
      rw [show k + d + 1 = k + 1 + d by omega]
      exact ⟨h₁, h₂⟩
  | .app f a, k, c, h => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.shift, closedAt, closedAt_shift_add d f k c h.1, closedAt_shift_add d a k c h.2,
        Bool.and_self]

theorem closedAt_pickE : ∀ (j : Nat) {k : Nat} {t : Expr}, closedAt k t = true →
    closedAt k (pickE j t) = true
  | 0, k, t, h => by simp [pickE, closedAt, h]
  | j + 1, k, t, h => by
      simp only [pickE, closedAt, h, Bool.true_and]
      exact closedAt_pickE j (by simp [closedAt])

theorem closedAt_tailTuple {k : Nat} {Hc : Expr} (h : closedAt k Hc = true) :
    ∀ (E : List (Qual × VTy × VTy)) (j : Nat), closedAt k (tailTuple E j Hc) = true
  | [], _ => rfl
  | (q, _, B) :: E, j => by
      simp only [tailTuple, closedAt, closedAt_tailTuple h E (j + 1), Bool.and_true]
      unfold tailClause
      split
      · have := closedAt_pickE j (closedAt_shift_add 1 Hc k 0 h)
        simp [closedAt, this]
      · have := closedAt_pickE j (closedAt_shift_add 3 Hc k 0 h)
        simp [closedAt, resumeB, this, Val.lam]

/-! ### Shifts of the clauses -/

theorem Expr.shift_shift_comm (k d c : Nat) :
    ∀ (e : Expr) (b : Nat), (e.shift k b).shift d (b + c + k) = (e.shift d (b + c)).shift k b
  | .var i, b => by
      simp only [Expr.shift]
      by_cases h₁ : i < b
      · have h₂ : i < b + c := by omega
        have h₃ : i < b + c + k := by omega
        simp [h₁, h₂, h₃, Expr.shift]
      · by_cases h₂ : i < b + c
        · have h₃ : i + k < b + c + k := by omega
          simp [h₁, h₂, h₃, Expr.shift]
        · have h₃ : ¬ (i + k < b + c + k) := by omega
          have h₄ : ¬ (i + d < b) := by omega
          simp only [h₁, h₂, h₃, h₄, if_false, Expr.shift]
          congr 1; omega
  | .unit, _ => rfl
  | .pair a e, b => by simp only [Expr.shift, Expr.shift_shift_comm k d c a b,
      Expr.shift_shift_comm k d c e b]
  | .inj₁ a, b => by simp only [Expr.shift, Expr.shift_shift_comm k d c a b]
  | .inj₂ a, b => by simp only [Expr.shift, Expr.shift_shift_comm k d c a b]
  | .lam a, b => by
      simp only [Expr.shift]
      have := Expr.shift_shift_comm k d c a (b + 1)
      rw [show b + 1 + c + k = b + c + k + 1 by omega, show b + 1 + c = b + c + 1 by omega] at this
      rw [this]
  | .loc _, _ => rfl
  | .prim _, _ => rfl
  | .seq a e, b => by simp only [Expr.shift, Expr.shift_shift_comm k d c a b,
      Expr.shift_shift_comm k d c e b]
  | .letpair a e, b => by
      simp only [Expr.shift, Expr.shift_shift_comm k d c a b]
      have := Expr.shift_shift_comm k d c e (b + 2)
      rw [show b + 2 + c + k = b + c + k + 2 by omega, show b + 2 + c = b + c + 2 by omega] at this
      rw [this]
  | .case a e₁ e₂, b => by
      simp only [Expr.shift, Expr.shift_shift_comm k d c a b]
      have h₁ := Expr.shift_shift_comm k d c e₁ (b + 1)
      have h₂ := Expr.shift_shift_comm k d c e₂ (b + 1)
      rw [show b + 1 + c + k = b + c + k + 1 by omega, show b + 1 + c = b + c + 1 by omega] at h₁ h₂
      rw [h₁, h₂]
  | .app f a, b => by simp only [Expr.shift, Expr.shift_shift_comm k d c f b,
      Expr.shift_shift_comm k d c a b]

theorem pickE_shift : ∀ (j d c : Nat) (t : Expr),
    Expr.shift d c (pickE j t) = pickE j (Expr.shift d c t)
  | 0, d, c, t => by simp [pickE, Expr.shift]
  | j + 1, d, c, t => by
      simp only [pickE, Expr.shift]
      rw [pickE_shift j d (c + 2) (.var 0)]
      simp [Expr.shift]

theorem tailClause_shift (j : Nat) (b : Bool) (d c : Nat) (Hc : Expr) :
    Expr.shift d c (tailClause j b Hc) = tailClause j b (Hc.shift d c) := by
  cases b
  · have e := Expr.shift_shift_comm 3 d c Hc 0
    simp only [Nat.zero_add] at e
    simp only [tailClause, Bool.false_eq_true, if_false, Expr.shift, pickE_shift]
    rw [show c + 1 + 2 = c + 3 by omega, e]
    simp [resumeB, Expr.shift, Val.lam, Val.inj₁, Val.unit]
  · have e := Expr.shift_shift_comm 1 d c Hc 0
    simp only [Nat.zero_add] at e
    simp only [tailClause, if_true, Expr.shift, pickE_shift]
    rw [e]
    simp [Expr.shift]

theorem tailTuple_shift (d c : Nat) (Hc : Expr) :
    ∀ (E : List (Qual × VTy × VTy)) (j : Nat),
      Expr.shift d c (tailTuple E j Hc) = tailTuple E j (Hc.shift d c)
  | [], _ => by simp [tailTuple, Expr.shift, Val.unit]
  | _ :: E, j => by
      simp only [tailTuple, Expr.shift, tailClause_shift, tailTuple_shift d c Hc E (j + 1)]

end BoCa.Fig16.LogRel.Core

end

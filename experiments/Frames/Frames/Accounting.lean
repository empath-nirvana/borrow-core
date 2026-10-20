import Frames.Runs

/-!
# Frames — each rule's accounting case

One lemma per frame rule: from its premises' accounting (the induction hypotheses of
`accounting`), the rule's elaborated term, at every closing substitution, hands back the slots it
is given. Each lemma names one rule, the run lemmas of `Runs.lean` and the machine's own steps.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Frames
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload ubindE cfinE cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

theorem psub_dtor (k : Nat) (γ : List Val) (T : VTy) : Expr.psub k γ (dtorE T) = dtorE T :=
  psub_closedAt _ γ (dtorAt_closed false T) (Nat.zero_le k)

theorem subst_dtor (j : Nat) (s : Val) (T : VTy) : Expr.subst j s (dtorE T) = dtorE T :=
  subst_closedAt _ s (dtorAt_closed false T) (Nat.zero_le j)

theorem psub_sh (d : Nat) (γ : List Val) (e : Expr) :
    Expr.psub d γ (Expr.shift d 0 e) = Expr.shift d 0 (Expr.psub 0 γ e) := by
  simpa using Expr.psub_shift d γ e 0

/-! ### `core` -/

theorem acc_core (Ps : List VTy) (N : Expr) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (coreE Ps N)) := by
  intro π
  apply rets_of_retsG
  change RetsG (PairQ π) _ (Kont.plug .hole (.app (.val (.lam (Expr.psub 1 γ
    (thenE (.pair (.var 1) (.inj₁ (.var 0))) (.app (dtorE (slotsTy Ps)) (.var 1)) (sh 1 N)))))
    (.val π)))
  refine retsG_beta .hole ?_
  have e : (Expr.psub 1 γ (thenE (.pair (.var 1) (.inj₁ (.var 0))) (.app (dtorE (slotsTy Ps)) (.var 1))
      (sh 1 N))).subst 0 π = ubindE (Val.pair (Val.lam (.pair (π.shift 1 0).1 (.inj₁ (.var 0))))
        (Val.lam (.app (dtorE (slotsTy Ps)) (π.shift 1 0).1))) (Expr.psub 0 γ N) := by
    simp [thenE, ubindE, Expr.psub, Expr.subst, psub_dtor, subst_dtor, sh, psub_sh,
      subst_shift_expr, Val.pair, Val.lam, Expr.val]
  rw [Kont.plug, e]
  refine retsG_ubind (Q₁ := fun _ => True) (retsG_true _ _) (fun v _ => ?_)
  refine retsG_beta .hole ?_
  have e2 : (Expr.pair (π.shift 1 0).1 (.inj₁ (.var 0))).subst 0 v = .val (Val.pair π (Val.inj₁ v)) := by
    simp [Expr.subst, Val.pair, Val.inj₁, Expr.val]
  rw [Kont.plug, e2]
  exact retsG_val ⟨_, rfl⟩

/-! ### `exit` -/

/-- The context of the injection at position `k`. -/
def injK : Nat → Kont
  | 0 => .inj₁ .hole
  | k + 1 => .inj₂ (injK k)

theorem injK_plug : ∀ (k : Nat) (e : Expr), (injK k).plug e = injAt k e
  | 0, _ => rfl
  | k + 1, e => by simp [injK, injAt, Kont.plug, injK_plug k e]

theorem injK_plain : ∀ k, (injK k).Plain = true
  | 0 => rfl
  | k + 1 => by simp [injK, Kont.Plain, injK_plain k]

/-- The injected value. -/
def injV : Nat → Val → Val
  | 0, v => .inj₁ v
  | k + 1, v => .inj₂ (injV k v)

theorem injAt_val : ∀ (k : Nat) (v : Val), injAt k (.val v) = .val (injV k v)
  | 0, _ => rfl
  | k + 1, v => by simp [injAt, injV, injAt_val k v, Val.inj₂, Expr.val]

theorem psub_injAt (j : Nat) (γ : List Val) : ∀ (k : Nat) (e : Expr),
    Expr.psub j γ (injAt k e) = injAt k (Expr.psub j γ e)
  | 0, _ => rfl
  | k + 1, e => by simp [injAt, Expr.psub, psub_injAt j γ k e]

theorem subst_injAt (j : Nat) (s : Val) : ∀ (k : Nat) (e : Expr),
    Expr.subst j s (injAt k e) = injAt k (Expr.subst j s e)
  | 0, _ => rfl
  | k + 1, e => by simp [injAt, Expr.subst, subst_injAt j s k e]

theorem acc_exit (k : Nat) (V : Expr) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (exitE k V)) := by
  intro π
  apply rets_of_retsG
  change RetsG (PairQ π) _ (Kont.plug .hole (.app (.val (.lam (Expr.psub 1 γ
    (.pair (.var 0) (.inj₂ (injAt k (sh 1 V))))))) (.val π)))
  refine retsG_beta .hole ?_
  have e : (Expr.psub 1 γ (.pair (.var 0) (.inj₂ (injAt k (sh 1 V))))).subst 0 π =
      (Kont.pairR π (.inj₂ (injK k))).plug (Expr.psub 0 γ V) := by
    simp [Expr.psub, Expr.subst, psub_injAt, subst_injAt, sh, psub_sh, subst_shift_expr,
      Kont.plug, injK_plug]
  rw [Kont.plug, e]
  refine retsG_plain (by simp [Kont.Plain, injK_plain]) (retsG_true _ _) (fun v _ => ?_)
  have e2 : (Kont.pairR π (.inj₂ (injK k))).plug (.val v) =
      .val (Val.pair π (Val.inj₂ (injV k v))) := by
    simp [Kont.plug, injK_plug, injAt_val, Val.pair, Val.inj₂, Expr.val]
  rw [e2]
  exact retsG_val ⟨_, rfl⟩

/-! ### Calling a premise -/

/-- A premise's frame, closed by `a :: γ`, called on `π`. -/
theorem retsG_call {G : Expr → Prop} {π a : Val} {γ : List Val} {e : Expr}
    (h : Returns (ℍ := ℍ) (substAll (a :: γ) e)) :
    RetsG (ℍ := ℍ) (PairQ π) G (.app (.app (.val (.lam (Expr.psub 1 γ e))) (.val a)) (.val π)) := by
  refine retsG_beta (K := .appL .hole π) ?_
  have := h π
  rw [substAll_cons_psub] at this
  exact retsG_of_rets this

/-! ### `sub` -/

theorem acc_sub {e : Expr} (ih : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ e)) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (subE e)) := by
  intro π
  apply rets_of_retsG
  change RetsG (PairQ π) _ (Kont.plug .hole (.app (.val (.lam (Expr.psub 1 γ
    (.app (sh 1 e) (.var 0))))) (.val π)))
  refine retsG_beta .hole ?_
  have e1 : (Expr.psub 1 γ (.app (sh 1 e) (.var 0))).subst 0 π = .app (substAll γ e) (.val π) := by
    simp [Expr.psub, Expr.subst, sh, psub_sh, subst_shift_expr, substAll]
  rw [Kont.plug, e1]
  exact retsG_of_rets (ih γ π)

/-! ### `case` -/

theorem acc_case {V e₁ e₂ : Expr} (ih₁ : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ e₁))
    (ih₂ : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ e₂)) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (caseE V e₁ e₂)) := by
  intro π
  apply rets_of_retsG
  change RetsG (PairQ π) _ (Kont.plug .hole (.app (.val (.lam (Expr.psub 1 γ
    (.case (sh 1 V)
      (.app (.app (sh 2 (.val (.lam e₁))) (.var 0)) (.var 1))
      (.app (.app (sh 2 (.val (.lam e₂))) (.var 0)) (.var 1)))))) (.val π)))
  refine retsG_beta .hole ?_
  have e1 : (Expr.psub 1 γ (.case (sh 1 V)
      (.app (.app (sh 2 (.val (.lam e₁))) (.var 0)) (.var 1))
      (.app (.app (sh 2 (.val (.lam e₂))) (.var 0)) (.var 1)))).subst 0 π =
      (Kont.case .hole
        (.app (.app (Expr.shift 1 0 (.lam (Expr.psub 1 γ e₁))) (.var 0)) (π.shift 1 0).1)
        (.app (.app (Expr.shift 1 0 (.lam (Expr.psub 1 γ e₂))) (.var 0)) (π.shift 1 0).1)).plug
        (Expr.psub 0 γ V) := by
    simp only [Expr.psub, Expr.subst, sh, Kont.plug, psub_sh, subst_shift_expr]
    simp [Expr.val, Val.lam, Expr.psub, Expr.subst, Expr.subst_shift 1 0 1 _ _ (Nat.zero_le _) (le_refl _)]
  rw [Kont.plug, e1]
  refine retsG_plain (by rfl) (retsG_true _ _) (fun v _ => ?_)
  refine retsG_caseV (fun a _ => ?_) (fun a _ => ?_)
  · have e2 : (Expr.app (.app (Expr.shift 1 0 (.lam (Expr.psub 1 γ e₁))) (.var 0))
        (π.shift 1 0).1).subst 0 a = .app (.app (.val (.lam (Expr.psub 1 γ e₁))) (.val a)) (.val π) := by
      simp [Expr.subst, subst_shift_expr, Expr.val, Val.lam]
    rw [e2]; exact retsG_call (ih₁ (a :: γ))
  · have e2 : (Expr.app (.app (Expr.shift 1 0 (.lam (Expr.psub 1 γ e₂))) (.var 0))
        (π.shift 1 0).1).subst 0 a = .app (.app (.val (.lam (Expr.psub 1 γ e₂))) (.val a)) (.val π) := by
      simp [Expr.subst, subst_shift_expr, Expr.val, Val.lam]
    rw [e2]; exact retsG_call (ih₂ (a :: γ))

/-! ### Drop glue -/

/-- `d` is a chain `X₁; X₂; …; k` ending in `k`. -/
inductive Chain : Expr → Expr → Prop where
  | done (k : Expr) : Chain k k
  | seq (X : Expr) {d k : Expr} : Chain d k → Chain (.seq X d) k

theorem Chain.psub {d k : Expr} (h : Chain d k) (j : Nat) (γ : List Val) :
    Chain (Expr.psub j γ d) (Expr.psub j γ k) := by
  induction h with
  | done => exact .done _
  | seq X _ ih => exact .seq _ ih

theorem Chain.subst {d k : Expr} (h : Chain d k) (j : Nat) (s : Val) :
    Chain (Expr.subst j s d) (Expr.subst j s k) := by
  induction h with
  | done => exact .done _
  | seq X _ ih => exact .seq _ ih

theorem chain_dropCtx : ∀ (Γ : Ctx VTy) (i : Nat) (k : Expr), Chain (dropCtxE Γ i k) k
  | [], _, k => .done k
  | ⟨_, true⟩ :: Γ, i, k => .seq _ (chain_dropCtx Γ (i + 1) k)
  | ⟨_, false⟩ :: Γ, i, k => chain_dropCtx Γ (i + 1) k

theorem retsG_chain {Q : Val → Prop} {G : Expr → Prop} {d k : Expr} (h : Chain d k)
    (hk : RetsG (ℍ := ℍ) Q G k) : RetsG (ℍ := ℍ) Q G d := by
  induction h with
  | done => exact hk
  | seq X _ ih => exact retsG_seq (ih hk)

/-! ### `bind` -/

theorem acc_bind {E : ExitRow} {Γ₂ : Ctx VTy} {eM eN : Expr}
    (ihM : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ eM))
    (ihN : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ eN)) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (bindE E Γ₂ eM eN)) := by
  intro π
  apply rets_of_retsG
  change RetsG (PairQ π) _ (Kont.plug .hole (.app (.val (.lam (Expr.psub 1 γ
    (.app (.val (.lam (.letpair (.var 0)
      (.case (.var 0)
        (.app (.app (sh 5 (.val (.lam eN))) (.var 0)) (.var 2))
        (exitArmE E 2 (dropCtxE Γ₂ 5 (.pair (.var 2) (.inj₂ (.var 0))))))))) (.app (sh 1 eM) (.var 0))))))
    (.val π)))
  refine retsG_beta .hole ?_
  simp [Kont.plug, Expr.psub, Expr.subst, sh, psub_sh, Expr.val, Val.lam,
    subst_shift_succ, Expr.shift_zero]
  refine retsG_plain (K := .appR (.lam _) .hole) rfl (retsG_of_rets (ihM γ π)) ?_
  rintro v ⟨x, rfl⟩
  refine retsG_beta .hole ?_
  simp [Kont.plug, Expr.subst, subst_shift_succ]
  refine retsG_letpair .hole ?_
  simp [Kont.plug, Expr.subst, subst_shift_succ, Expr.shift_zero]
  refine retsG_caseV (fun a _ => ?_) (fun e _ => ?_)
  · have := retsG_call (G := fun _ => False) (π := π) (a := a) (ihN (a :: γ))
    simpa [Expr.subst, subst_shift_expr, Expr.val, Val.lam] using this
  · cases E with
    | nil =>
        simp [exitArmE, absurdE, Expr.psub, Expr.subst]
        refine retsG_plain (K := .pairR π (.inj₂ .hole)) rfl (retsG_true _ _) (fun u _ => ?_)
        exact retsG_val (w := Val.pair π (Val.inj₂ u)) ⟨_, rfl⟩
    | cons l E' =>
        simp only [exitArmE]
        refine retsG_chain (((((((chain_dropCtx Γ₂ 5 _).psub 5 γ).subst 4 _).subst 3 _).subst 1 _).subst 1 _).subst 0 e) ?_
        simp [Expr.psub, Expr.subst]
        exact retsG_val (w := Val.pair π (Val.inj₂ e)) ⟨_, rfl⟩

end BoCa.Fig16.LogRel.Core.Frames

end

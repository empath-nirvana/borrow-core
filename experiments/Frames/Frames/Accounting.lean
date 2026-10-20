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

set_option linter.unusedSimpArgs false

-- The substitution normaliser for elaborated terms: closing substitutions, β's substitutions,
-- and the shifts they cancel.
set_option hygiene false in
macro "fsimp" : tactic => `(tactic| simp [Kont.plug, Expr.psub, Expr.subst, sh, psub_sh, Expr.val,
  Val.lam, subst_shift_succ, Expr.shift_zero, Expr.shift_shift, subst_shift_expr, psub_dtor, subst_dtor, psub_forget, subst_forget])

set_option hygiene false in
macro "fsimp_at" h:ident : tactic => `(tactic| simp [Kont.plug, Expr.psub, Expr.subst, sh, psub_sh,
  Expr.val, Val.lam, subst_shift_succ, Expr.shift_zero, Expr.shift_shift, subst_shift_expr, psub_dtor,
  subst_dtor, psub_forget, subst_forget] at $h:ident)

theorem psub_dtor (k : Nat) (γ : List Val) (T : VTy) : Expr.psub k γ (dtorE T) = dtorE T :=
  psub_closedAt _ γ (dtorAt_closed false T) (Nat.zero_le k)

theorem subst_dtor (j : Nat) (s : Val) (T : VTy) : Expr.subst j s (dtorE T) = dtorE T :=
  subst_closedAt _ s (dtorAt_closed false T) (Nat.zero_le j)

theorem subst_forget (j : Nat) (s : Val) : Expr.subst j s forget = forget := rfl

theorem psub_forget (k : Nat) (γ : List Val) : Expr.psub k γ forget = forget := rfl

theorem psub_i32 (k : Nat) (γ : List Val) (c : UInt32) : Expr.psub k γ (Val.i32 c).1 = (Val.i32 c).1 := rfl

theorem subst_i32 (j : Nat) (s : Val) (c : UInt32) : Expr.subst j s (Val.i32 c).1 = (Val.i32 c).1 := rfl

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

/-- A β step at a value written as an expression. -/
theorem retsG_betaE {Q : Val → Prop} {G : Expr → Prop} (K : Kont) {b e : Expr} (he : IsVal e)
    (h : RetsG (ℍ := ℍ) Q G (K.plug (b.subst 0 ⟨e, he⟩))) :
    RetsG (ℍ := ℍ) Q G (K.plug (.app (.lam b) e)) :=
  retsG_beta (v := ⟨e, he⟩) K h

/-! ### Calling a premise -/

/-- A premise's frame, closed by `a :: γ`, called on `π`. -/
theorem retsG_call {G : Expr → Prop} {π a : Val} {γ : List Val} {e : Expr}
    (h : Returns (ℍ := ℍ) (substAll (a :: γ) e)) :
    RetsG (ℍ := ℍ) (PairQ π) G (.app (.app (.val (.lam (Expr.psub 1 γ e))) (.val a)) (.val π)) := by
  refine retsG_beta (K := .appL .hole π) ?_
  have := h π
  rw [substAll_cons_psub] at this
  exact retsG_of_rets this

/-- A premise's frame under two binders, closed by `s :: i :: γ`, called on `π`. -/
theorem retsG_call2 {G : Expr → Prop} {π i s : Val} {γ : List Val} {e : Expr}
    (h : Returns (ℍ := ℍ) (substAll (s :: i :: γ) e)) :
    RetsG (ℍ := ℍ) (PairQ π) G
      (.app (.app (.app (.val (.lam (.val (.lam (Expr.psub 2 γ e))))) (.val i)) (.val s)) (.val π)) := by
  refine retsG_beta (K := .appL (.appL .hole s) π) ?_
  have e1 : (Expr.val (Val.lam (Expr.psub 2 γ e))).subst 0 i = .val (.lam (Expr.psub 1 (i :: γ) e)) := by
    simp [Expr.val, Val.lam, Expr.subst, Expr.psub_cons 1 i γ e]
  rw [e1]
  exact retsG_call h

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

/-! ### `catch` -/

theorem acc_catch {Γ₂ : Ctx VTy} {eM eH : Expr}
    (ihM : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ eM))
    (ihH : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ eH)) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (catchE Γ₂ eM eH)) := by
  intro π
  apply rets_of_retsG
  change RetsG (PairQ π) _ (Kont.plug .hole (.app (.val (.lam (Expr.psub 1 γ
    (.app (.val (.lam (.letpair (.var 0)
      (.case (.var 0)
        (dropCtxE Γ₂ 5 (.pair (.var 2) (.inj₁ (.var 0))))
        (.case (.var 0)
          (.app (.app (sh 6 (.val (.lam eH))) (.var 0)) (.var 3))
          (dropCtxE Γ₂ 6 (.pair (.var 3) (.inj₂ (.var 0))))))))) (.app (sh 1 eM) (.var 0))))))
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
  · refine retsG_chain (((((((chain_dropCtx Γ₂ 5 _).psub 5 γ).subst 4 _).subst 3 _).subst 1 _).subst 1 _).subst 0 a) ?_
    simp [Expr.psub, Expr.subst]
    exact retsG_val (w := Val.pair π (Val.inj₁ a)) ⟨_, rfl⟩
  · simp [Expr.subst, subst_shift_succ, Expr.shift_zero]
    refine retsG_caseV (fun b _ => ?_) (fun e' _ => ?_)
    · have := retsG_call (G := fun _ => False) (π := π) (a := b) (ihH (b :: γ))
      fsimp; fsimp_at this; exact this
    · refine retsG_chain ((((((((chain_dropCtx Γ₂ 6 _).psub 6 γ).subst 5 _).subst 4 _).subst 2 _).subst 2 _).subst 1 _).subst 0 e') ?_
      fsimp
      exact retsG_val (w := Val.pair π (Val.inj₂ e')) ⟨_, rfl⟩

/-! ### `under` -/

theorem acc_under {Q : VTy} {eM : Expr}
    (ih : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ eM)) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (underE Q eM)) := by
  intro π
  apply rets_of_retsG
  change RetsG (PairQ π) _ (Kont.plug .hole (.app (.val (.lam (Expr.psub 1 γ
    (.letpair (.var 0)
      (thenE (.letpair (.var 0) (.pair (.pair (.var 4) (.var 1)) (.var 0)))
        (.app (dtorE Q) (.var 2))
        (.app (sh 3 eM) (.var 0))))))) (.val π)))
  refine retsG_beta .hole ?_
  simp [thenE, psub_dtor, subst_dtor]
  fsimp
  refine retsG_letpairV (fun q ρ hπ => ?_)
  subst hπ
  fsimp
  refine retsG_ubind (N := Val.lam _) (D := Val.lam _) (Q₁ := PairQ ρ)
    (retsG_of_rets (by simpa [substAll] using ih γ ρ)) (fun v hv => ?_)
  obtain ⟨r, rfl⟩ := hv
  refine retsG_beta .hole ?_
  fsimp
  refine retsG_letpair .hole ?_
  fsimp
  exact retsG_val (w := Val.pair (Val.pair q ρ) r) ⟨_, rfl⟩

/-! ### The unwinding borrow constant hands back its source -/

theorem psub_withborU (k : Nat) (γ : List Val) (T : VTy) :
    Expr.psub k γ (withborUE (dtorE T)) = withborUE (dtorE T) :=
  psub_closedAt _ γ (withborUE_closed (dtorAt_closed false T)) (Nat.zero_le k)

theorem subst_withborU (j : Nat) (s : Val) (T : VTy) :
    Expr.subst j s (withborUE (dtorE T)) = withborUE (dtorE T) :=
  subst_closedAt _ s (withborUE_closed (dtorAt_closed false T)) (Nat.zero_le j)

/-- The answers `(p, b)`: the source `p` handed back beside a result. -/
def SrcQ (p : Val) (y : Val) : Prop := ∃ b, y = Val.pair p b

/-- The answers `(p, b)` with `b` satisfying `Qb`. -/
def PairWith (p : Val) (Qb : Val → Prop) (y : Val) : Prop := ∃ b, y = Val.pair p b ∧ Qb b

/-- `withborU d p f` answers `(p, b)`: the source it was given, beside what the callback answered. -/
theorem retsG_withborU' {G : Expr → Prop} {Qb : Val → Prop} (T : VTy) (p f : Val)
    (hf : RetsG (ℍ := ℍ) Qb (fun _ => False) (.app (.app (.val f) (.val .unit)) (.val p))) :
    RetsG (ℍ := ℍ) (PairWith p Qb) G
      (.app (.app (withborUE (dtorE T)) (.val p)) (.val f)) := by
  change RetsG _ G ((Kont.appL .hole f).plug (.app (.val (.lam (.val (.lam (thenE (.pair (.var 2) (.var 0))
    (.app (dtorE T) (.var 2)) (.app (.app (.var 0) (.val .unit)) (.var 1))))))) (.val p)))
  refine retsG_beta _ ?_
  fsimp
  refine retsG_beta .hole ?_
  simp only [thenE]
  fsimp
  refine retsG_ubind (N := Val.lam _) (D := Val.lam _) (Q₁ := Qb)
    (retsG_mono (G := fun _ => False) (fun _ h => h) (fun _ (h : False) => h.elim)
      (by simpa [Expr.val] using hf)) (fun b hb => ?_)
  refine retsG_beta .hole ?_
  fsimp
  exact retsG_val (w := Val.pair p b) (Q := PairWith p Qb) ⟨_, rfl, hb⟩

/-- `withborU d p f` answers `(p, b)`, whatever the callback does. -/
theorem retsG_withborU {G : Expr → Prop} (T : VTy) (p f : Val) :
    RetsG (ℍ := ℍ) (SrcQ p) G (.app (.app (withborUE (dtorE T)) (.val p)) (.val f)) :=
  retsG_mono (fun _ ⟨b, h, _⟩ => ⟨b, h⟩) (fun _ h => h)
    (retsG_withborU' (Qb := fun _ => True) T p f (retsG_true _ _))

/-! ### `use` -/

theorem acc_use (src : LendSrc) (Ps : List VTy) (N : Expr) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (useE src Ps N)) := by
  intro π
  apply rets_of_retsG
  change RetsG (PairQ π) _ (Kont.plug .hole (.app (.val (.lam (Expr.psub 1 γ
    (.letpair (.var 0)
      (.app (.val (.lam
        (.app (.val (.lam
          (thenE (.letpair (.var 0) (.pair (.pair (.var 1) (.var 5)) (.inj₁ (.var 0))))
            (.app (dtorE (slotsTy Ps)) (.var 3))
            (.app (.app (.var 0) (.var 3)) (.var 1)))))
          (withborUE src.fin))))
        (sh 3 N)))))) (.val π)))
  refine retsG_beta .hole ?_
  simp only [thenE, LendSrc.fin]
  fsimp
  simp only [psub_withborU, subst_withborU]
  refine retsG_letpairV (fun p ρ hπ => ?_)
  subst hπ
  fsimp
  simp only [subst_withborU]
  refine retsG_plain (K := .appR (.lam _) .hole) rfl (retsG_true _ _) (fun f _ => ?_)
  refine retsG_beta .hole ?_
  fsimp
  simp only [subst_withborU]
  change RetsG _ _ (Kont.plug .hole (.app (.val (.lam _)) (.val (withborUV (dtorE src.ty)))))
  refine retsG_beta .hole ?_
  fsimp
  refine retsG_ubind (N := Val.lam _) (D := Val.lam _) (Q₁ := SrcQ p) ?_ (fun y hy => ?_)
  · simpa [withborUV, Expr.val] using retsG_withborU (G := fun _ => False) src.ty p f
  · obtain ⟨b, rfl⟩ := hy
    refine retsG_beta .hole ?_
    fsimp
    refine retsG_letpair .hole ?_
    fsimp
    exact retsG_val (w := Val.pair (Val.pair p ρ) (Val.inj₁ b)) ⟨_, rfl⟩

/-! ### `lend` -/

/-- The answers `(ρ, r)`: the rest of the slots, beside a result. -/
def RestQ (ρ : Val) (y : Val) : Prop := ∃ r, y = Val.pair ρ r

theorem acc_lend (src : LendSrc) {eM : Expr}
    (ih : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ eM)) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (lendE src eM)) := by
  intro π
  apply rets_of_retsG
  show RetsG _ _ (Kont.plug .hole (.app (substAll γ (lendE src eM)) (.val π)))
  simp only [substAll, lendE, Expr.psub, LendSrc.fin]
  refine retsG_betaE .hole π.2 ?_
  fsimp
  simp only [psub_withborU, subst_withborU]
  refine retsG_letpairV (fun p ρ hπ => ?_)
  subst hπ
  fsimp
  simp only [subst_withborU]
  refine retsG_betaE .hole IsVal.lam ?_
  fsimp
  simp only [subst_withborU]
  refine retsG_betaE .hole IsVal.lam ?_
  fsimp
  refine retsG_plain (K := .appR (.lam _) .hole) rfl
    (retsG_withborU' (Qb := RestQ ρ) (f := ⟨_, IsVal.lam⟩) src.ty p ?_) ?_
  · -- the callback, on the slots `(p, ρ)`
    refine retsG_betaE (.appL .hole p) IsVal.unit ?_
    fsimp
    refine retsG_betaE .hole p.2 ?_
    fsimp
    refine retsG_betaE .hole (IsVal.pair p.2 ρ.2) ?_
    fsimp
    refine retsG_plain (K := .appR (.lam _) .hole) rfl
      (retsG_of_rets (by simpa [substAll] using ih γ (Val.pair p ρ))) ?_
    rintro v ⟨r, rfl⟩
    refine retsG_beta .hole ?_
    fsimp
    refine retsG_letpair (v₁ := Val.pair p ρ) (v₂ := r) .hole ?_
    fsimp
    refine retsG_letpair .hole ?_
    fsimp
    refine retsG_beta (.seq .hole _) ?_
    refine retsG_seqU .hole ?_
    exact retsG_val (w := Val.pair ρ r) ⟨_, rfl⟩
  · rintro y ⟨b, rfl, r, rfl⟩
    refine retsG_beta .hole ?_
    fsimp
    refine retsG_letpair (v₁ := p) (v₂ := Val.pair ρ r) .hole ?_
    fsimp
    refine retsG_letpair .hole ?_
    fsimp
    exact retsG_val (w := Val.pair (Val.pair p ρ) r) ⟨_, rfl⟩

/-! ### `new` -/

theorem acc_new (A : VTy) (V : Expr) {eM : Expr}
    (ih : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ eM)) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (newE A V eM)) := by
  intro π
  apply rets_of_retsG
  show RetsG _ _ (Kont.plug .hole (.app (substAll γ (newE A V eM)) (.val π)))
  simp only [substAll, newE, Expr.psub]
  refine retsG_betaE .hole π.2 ?_
  fsimp
  refine retsG_plain (K := .appR (.lam _) .hole) rfl (retsG_true _ _) (fun c _ => ?_)
  refine retsG_beta .hole ?_
  fsimp
  refine retsG_betaE .hole (IsVal.pair c.2 π.2) ?_
  fsimp
  refine retsG_plain (K := .appR (.lam _) .hole) rfl
    (retsG_of_rets (by simpa [substAll] using ih γ (Val.pair c π))) ?_
  rintro y ⟨r, rfl⟩
  refine retsG_beta .hole ?_
  fsimp
  refine retsG_letpair (v₁ := Val.pair c π) (v₂ := r) .hole ?_
  fsimp
  refine retsG_letpair (v₁ := c) (v₂ := π) .hole ?_
  fsimp
  refine retsG_caseV (fun b _ => ?_) (fun e _ => ?_)
  · fsimp
    refine retsG_plain (K := .appR (.lam _) .hole) rfl (retsG_true _ _) (fun a _ => ?_)
    refine retsG_beta .hole ?_
    fsimp
    exact retsG_val (w := Val.pair π (Val.inj₁ (Val.pair b a))) ⟨_, rfl⟩
  · fsimp
    exact retsG_seq (retsG_val (w := Val.pair π (Val.inj₂ e)) ⟨_, rfl⟩)

/-! ### `callBlock` -/

theorem acc_callBlock {Δ : LifeCtx} {b : FBlock} {j : Nat} (hwf : b.Wf Δ)
    (hb : b.Returns (ℍ := ℍ)) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (callE b.v j)) := by
  intro π
  apply rets_of_retsG
  obtain ⟨hcl, ⟨body, hbody⟩, -⟩ := hwf
  show RetsG _ _ (Kont.plug .hole (.app (substAll γ (callE b.v j)) (.val π)))
  simp only [substAll, callE, Expr.psub]
  refine retsG_betaE .hole π.2 ?_
  have hc : ∀ k, Expr.psub k γ b.v.1 = b.v.1 := fun k => psub_closedAt _ γ hcl (Nat.zero_le k)
  have hs : ∀ j (s : Val), Expr.subst j s b.v.1 = b.v.1 := fun j s => subst_closedAt _ s hcl (Nat.zero_le j)
  simp only [Expr.subst, Expr.val, hc, hs, Kont.plug]
  refine retsG_betaE .hole b.v.2 ?_
  generalize hX : Expr.subst 0 b.v (Expr.subst 1 (π.shift 1 0) (Expr.psub 2 γ (.var (j + 2)))) = X
  have e : Expr.subst 0 ⟨b.v.1, b.v.2⟩ (Expr.subst (0 + 1) (Val.shift 1 0 ⟨π.1, π.2⟩)
      (Expr.psub (0 + 1 + 1) γ (((Expr.var 0).app (Expr.var (j + 2))).app (Expr.var 1)))) =
      (Kont.appL (.appR (.val b.v) .hole) π).plug X := by
    rw [← hX]
    simp [Expr.psub, Expr.subst, Kont.plug, Expr.val]
  rw [e]
  refine retsG_plain (K := .appL (.appR (.val b.v) .hole) π) (by rw [hbody]; rfl)
    (retsG_true _ _) (fun a _ => ?_)
  exact retsG_of_rets (hb a π)

/-! ### `loopCount` -/

theorem acc_loopCount {n s₀ eM : Expr}
    (ih : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ eM)) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (loopCountE n s₀ eM)) := by
  intro π
  apply rets_of_retsG
  show RetsG _ _ (Kont.plug .hole (.app (substAll γ (loopCountE n s₀ eM)) (.val π)))
  simp only [substAll, loopCountE, Expr.psub]
  refine retsG_betaE .hole π.2 ?_
  fsimp
  simp only [psub_i32, subst_i32]
  have hSv : IsVal (Expr.psub 0 γ (countStepE eM)) := isVal_psub IsVal.lam 0 γ
  -- the bound `n` and the initial state run first, as any Core code
  change RetsG _ _ ((Kont.appR (.lam _) (.appR (.val (.prim .countTry))
    (.pairR ⟨_, hSv⟩ (.pairL .hole _)))).plug (Expr.psub 0 γ n))
  refine retsG_plain (by simp [Kont.Plain]) (retsG_true _ _) (fun nv _ => ?_)
  change RetsG _ _ ((Kont.appR (.lam _) (.appR (.val (.prim .countTry))
    (.pairR ⟨_, hSv⟩ (.pairR nv (.pairR (Val.i32 0) (.pairR π .hole)))))).plug (Expr.psub 0 γ s₀))
  refine retsG_plain (by simp [Kont.Plain]) (retsG_true _ _) (fun sv _ => ?_)
  -- one turn: the step on `(i, (π, s))` answers `inj₁ (π, s′)` or `inj₂ (π, x)`
  have hf : ∀ (i : UInt32) (s : Val), RestQ π s →
      RetsG (ℍ := ℍ) (CountQ (RestQ π) (RestQ π)) (fun _ => False)
        (.app (.val ⟨_, hSv⟩) (.val (Val.pair (Val.i32 i) s))) := by
    rintro i s ⟨s', rfl⟩
    change RetsG _ _ (Kont.plug .hole (.app (Expr.psub 0 γ (countStepE eM)) _))
    simp only [countStepE, Expr.psub]
    refine retsG_betaE .hole (IsVal.pair (Val.i32 i).2 (IsVal.pair π.2 s'.2)) ?_
    fsimp
    refine retsG_letpair (v₁ := Val.i32 i) (v₂ := Val.pair π s') .hole ?_
    fsimp
    refine retsG_letpair (v₁ := π) (v₂ := s') .hole ?_
    fsimp
    refine retsG_plain (K := .appR (.lam _) .hole) rfl (Q₁ := PairQ π) ?_ ?_
    · have := retsG_call2 (G := fun _ => False) (π := π) (i := Val.i32 i) (s := s') (γ := γ)
        (ih (s' :: Val.i32 i :: γ))
      fsimp_at this; exact this
    rintro y ⟨r, rfl⟩
    refine retsG_beta .hole ?_
    fsimp
    refine retsG_letpair (v₁ := π) (v₂ := r) .hole ?_
    fsimp
    refine retsG_caseV (fun a _ => ?_) (fun x _ => ?_)
    · fsimp
      exact retsG_val (w := Val.inj₁ (Val.pair π a)) (.inl ⟨_, rfl, a, rfl⟩)
    · fsimp
      exact retsG_val (w := Val.inj₂ (Val.pair π x)) (.inr ⟨_, rfl, x, rfl⟩)
  change RetsG _ _ ((Kont.appR (.lam _) .hole).plug (.app (.val (.prim .countTry))
    (.val (Val.pair ⟨_, hSv⟩ (Val.pair nv (Val.pair (Val.i32 0) (Val.pair π sv)))))))
  refine retsG_plain (by simp [Kont.Plain]) (Q₁ := CountQ (RestQ π) (RestQ π)) ?_ ?_
  · by_cases hn : ∃ m, nv = Val.i32 m
    · obtain ⟨m, rfl⟩ := hn
      exact retsG_countTry _ m hf _ 0 (Val.pair π sv) rfl ⟨sv, rfl⟩
    · exact retsG_countTry_stuck (fun ⟨_, m, _, _, h⟩ => hn ⟨m, (pairV_inj (pairV_inj h).2).1⟩)
  · rintro y (⟨s, rfl, s', rfl⟩ | ⟨x, rfl, x', rfl⟩)
    · refine retsG_beta .hole ?_
      fsimp
      refine retsG_case₁ (a := Val.pair π s') .hole ?_
      fsimp
      refine retsG_letpair (v₁ := π) (v₂ := s') .hole ?_
      fsimp
      exact retsG_val (w := Val.pair π (Val.inj₁ (Val.inj₁ s'))) ⟨_, rfl⟩
    · refine retsG_beta .hole ?_
      fsimp
      refine retsG_case₂ (a := Val.pair π x') .hole ?_
      fsimp
      refine retsG_letpair (v₁ := π) (v₂ := x') .hole ?_
      fsimp
      refine retsG_caseV (fun b _ => ?_) (fun e _ => ?_)
      · fsimp
        exact retsG_val (w := Val.pair π (Val.inj₁ (Val.inj₂ b))) ⟨_, rfl⟩
      · fsimp
        exact retsG_val (w := Val.pair π (Val.inj₂ e)) ⟨_, rfl⟩

/-! ### `loopIter` -/

theorem acc_loopIter (S₀ : VTy) {s₀ eM : Expr}
    (ih : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ eM)) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (loopIterE S₀ s₀ eM)) := by
  intro π
  apply rets_of_retsG
  show RetsG _ _ (Kont.plug .hole (.app (substAll γ (loopIterE S₀ s₀ eM)) (.val π)))
  simp only [substAll, loopIterE, Expr.psub]
  refine retsG_betaE .hole π.2 ?_
  fsimp
  have hSv : IsVal (Expr.psub 0 γ (iterStepE S₀ eM)) := isVal_psub IsVal.lam 0 γ
  refine retsG_betaE .hole hSv ?_
  fsimp
  refine retsG_beta (v := Val.prim .iterate) .hole ?_
  fsimp
  change RetsG _ _ ((Kont.appR (.lam _) (.pairR ⟨_, hSv⟩ (.pairR π .hole))).plug (Expr.psub 0 γ s₀))
  refine retsG_plain (by simp [Kont.Plain]) (retsG_true _ _) (fun sv _ => ?_)
  refine retsG_beta (v := Val.pair ⟨_, hSv⟩ (Val.pair π sv)) .hole ?_
  fsimp
  -- the turn and the residual of the step
  have hturn : ∀ s, RestQ π s → RetsG (ℍ := ℍ) (TurnQ (RestQ π) (RestQ π)) (fun _ => False)
      (.app (.app (.val ⟨_, hSv⟩) (.val s)) (.val nextV)) := by
    rintro s ⟨s', rfl⟩
    change RetsG _ _ ((Kont.appL .hole nextV).plug (.app (Expr.psub 0 γ (iterStepE S₀ eM)) _))
    simp only [iterStepE, withPair, Expr.psub]
    refine retsG_betaE _ (IsVal.pair π.2 s'.2) ?_
    fsimp
    refine retsG_letpair (v₁ := π) (v₂ := s') (.appL .hole nextV) ?_
    fsimp
    refine retsG_beta (v := nextV) .hole ?_
    fsimp
    refine retsG_case₁ (a := Val.unit) .hole ?_
    fsimp
    refine retsG_seqU .hole ?_
    refine retsG_plain (K := .appR (.lam _) .hole) rfl (Q₁ := PairQ π) ?_ ?_
    · have := retsG_call (G := fun _ => False) (π := π) (a := s') (γ := γ) (ih (s' :: γ))
      fsimp_at this; exact this
    rintro y ⟨r, rfl⟩
    refine retsG_beta .hole ?_
    fsimp
    refine retsG_letpair (v₁ := π) (v₂ := r) .hole ?_
    fsimp
    refine retsG_caseV (fun a _ => ?_) (fun x _ => ?_)
    · fsimp
      exact retsG_val (w := Val.inj₂ (Val.pair π a)) (.inr ⟨_, rfl, a, rfl⟩)
    · fsimp
      exact retsG_val (w := Val.inj₁ (Val.pair π x)) (.inl ⟨_, rfl, x, rfl⟩)
  have hclose : ∀ s, RestQ π s → RetsG (ℍ := ℍ) (RestQ π) (fun _ => False)
      (.app (.app (.val ⟨_, hSv⟩) (.val s)) (.val closeV)) := by
    rintro s ⟨s', rfl⟩
    change RetsG _ _ ((Kont.appL .hole closeV).plug (.app (Expr.psub 0 γ (iterStepE S₀ eM)) _))
    simp only [iterStepE, withPair, Expr.psub]
    refine retsG_betaE _ (IsVal.pair π.2 s'.2) ?_
    fsimp
    refine retsG_letpair (v₁ := π) (v₂ := s') (.appL .hole closeV) ?_
    fsimp
    refine retsG_beta (v := closeV) .hole ?_
    fsimp
    refine retsG_case₂ (a := Val.unit) .hole ?_
    fsimp
    refine retsG_seqU .hole ?_
    exact retsG_seq (retsG_val (w := Val.pair π Val.unit) ⟨_, rfl⟩)
  change RetsG _ _ ((Kont.appR (.lam _) .hole).plug (.app (.val (.prim .iterate))
    (.val (Val.pair ⟨_, hSv⟩ (Val.pair π sv)))))
  refine retsG_plain (by simp [Kont.Plain]) (Q₁ := IterQ (RestQ π) (RestQ π))
    (retsG_iterate (P := RestQ π) _ hturn hclose ⟨sv, rfl⟩) ?_
  rintro y (⟨x, rfl, x', rfl⟩ | ⟨u, rfl, u', rfl⟩)
  · refine retsG_beta .hole ?_
    fsimp
    refine retsG_case₁ (a := Val.pair π x') .hole ?_
    fsimp
    refine retsG_letpair (v₁ := π) (v₂ := x') .hole ?_
    fsimp
    refine retsG_caseV (fun b _ => ?_) (fun e _ => ?_)
    · fsimp
      exact retsG_val (w := Val.pair π (Val.inj₁ (Val.inj₁ b))) ⟨_, rfl⟩
    · fsimp
      exact retsG_val (w := Val.pair π (Val.inj₂ e)) ⟨_, rfl⟩
  · refine retsG_beta .hole ?_
    fsimp
    refine retsG_case₂ (a := Val.pair π u') .hole ?_
    fsimp
    refine retsG_letpair (v₁ := π) (v₂ := u') .hole ?_
    fsimp
    exact retsG_val (w := Val.pair π (Val.inj₁ (Val.inj₂ Val.unit))) ⟨_, rfl⟩

end BoCa.Fig16.LogRel.Core.Frames

end

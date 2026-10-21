import Core.FramesRuns

/-!
# Core — frames: each rule's accounting case  `[spec §47]`

One lemma per frame rule: from its premises' accounting (the induction hypotheses of
`accounting`), the rule's elaborated term, at every closing substitution, hands back the cells
of the slots it is given. Each lemma names one rule, the run lemmas of `Core/FramesRuns.lean` and
the machine's own steps. What they share is about one term each: the widening of a slot tuple
(`retsG_wid`), `swap` (`retsG_swap`), the drop glue (`retsG_chain`).
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

theorem widE_closed : ∀ ws : List WStep, closedAt 0 (widE ws) = true
  | [] => rfl
  | w :: ws => by
      have h := widE_closed ws
      cases w <;> simp [widE, WStep.apply, closedAt, Expr.val, Val.lam,
        closedAt_mono _ h (Nat.zero_le _)]

theorem psub_widE (k : Nat) (γ : List Val) (ws : List WStep) : Expr.psub k γ (widE ws) = widE ws :=
  psub_closedAt _ γ (widE_closed ws) (Nat.zero_le k)

theorem subst_widE (j : Nat) (s : Val) (ws : List WStep) : Expr.subst j s (widE ws) = widE ws :=
  subst_closedAt _ s (widE_closed ws) (Nat.zero_le j)

theorem relE_closed : ∀ q : CellSt, closedAt 0 q.relE = true
  | .full _ => rfl
  | .sum s t => by
      have h₁ := relE_closed s; have h₂ := relE_closed t
      simp [CellSt.relE, closedAt, Expr.val, Val.lam, closedAt_mono _ h₁ (Nat.zero_le _),
        closedAt_mono _ h₂ (Nat.zero_le _)]

theorem psub_relE (k : Nat) (γ : List Val) (q : CellSt) : Expr.psub k γ q.relE = q.relE :=
  psub_closedAt _ γ (relE_closed q) (Nat.zero_le k)

theorem subst_relE (j : Nat) (s : Val) (q : CellSt) : Expr.subst j s q.relE = q.relE :=
  subst_closedAt _ s (relE_closed q) (Nat.zero_le j)

theorem psub_swap (k : Nat) (γ : List Val) : Expr.psub k γ swap = swap :=
  psub_closedAt _ γ swap_closed (Nat.zero_le k)

-- The substitution normaliser for elaborated terms: closing substitutions, β's substitutions,
-- and the shifts they cancel.
set_option hygiene false in
macro "fsimp" : tactic => `(tactic| simp [Kont.plug, Expr.psub, Expr.subst, sh, psub_sh, Expr.val,
  Val.lam, subst_shift_succ, Expr.shift_zero, Expr.shift_shift, subst_shift_expr, psub_dtor,
  subst_dtor, psub_forget, subst_forget, psub_widE, subst_widE, psub_relE, subst_relE, psub_swap,
  swap_subst])

set_option hygiene false in
macro "fsimp_at" h:ident : tactic => `(tactic| simp [Kont.plug, Expr.psub, Expr.subst, sh, psub_sh,
  Expr.val, Val.lam, subst_shift_succ, Expr.shift_zero, Expr.shift_shift, subst_shift_expr, psub_dtor,
  subst_dtor, psub_forget, subst_forget, psub_widE, subst_widE, psub_relE, subst_relE, psub_swap,
  swap_subst] at $h:ident)

/-! ### The cells of a slot tuple -/

theorem SameCells.refl (π : Val) : SameCells π π := rfl

theorem SameCells.trans {π π' π'' : Val} (h₁ : SameCells π π') (h₂ : SameCells π' π'') :
    SameCells π π'' := Eq.trans h₂ h₁

theorem sameCells_pair {p ρ p' ρ' : Val} (hp : SameCells p p') (hρ : SameCells ρ ρ') :
    SameCells (Val.pair p ρ) (Val.pair p' ρ') := by
  simp only [SameCells, slotCells, Val.pair] at hp hρ ⊢
  rw [hp, hρ]

theorem sameCells_pair_inv {p ρ p' ρ' : Val} (h : SameCells (Val.pair p ρ) (Val.pair p' ρ')) :
    SameCells p p' ∧ SameCells ρ ρ' := by
  simp only [SameCells, slotCells, Val.pair, Expr.pair.injEq] at h
  exact h

theorem sameCells_inj₁ (p : Val) : SameCells (Val.inj₁ p) p := rfl

theorem sameCells_inj₂ (p : Val) : SameCells (Val.inj₂ p) p := rfl

theorem AnsQ.trans {π π' : Val} (h : SameCells π π') {w : Val} (hw : AnsQ π' w) : AnsQ π w := by
  obtain ⟨π'', x, h', hw⟩ := hw
  exact ⟨π'', x, h.trans h', hw⟩

theorem ansQ_inl {π π' : Val} (h : SameCells π π') (x : Val) : AnsQ π (Val.inj₁ (Val.pair π' x)) :=
  ⟨π', x, h, .inl rfl⟩

theorem ansQ_inr {π π' : Val} (h : SameCells π π') (x : Val) : AnsQ π (Val.inj₂ (Val.pair π' x)) :=
  ⟨π', x, h, .inr rfl⟩

/-- An answer that hands back the cells of `π` is `inl (π', a)` or `inr (π', e)`. -/
theorem AnsQ.cases {π w : Val} (h : AnsQ π w) :
    (∃ π' x, SameCells π π' ∧ w = Val.inj₁ (Val.pair π' x)) ∨
      (∃ π' x, SameCells π π' ∧ w = Val.inj₂ (Val.pair π' x)) := by
  obtain ⟨π', x, h, h' | h'⟩ := h
  · exact .inl ⟨π', x, h, h'⟩
  · exact .inr ⟨π', x, h, h'⟩

/-! ### The widening keeps the cells -/

/-- A slot widened by a step: `p` itself or its injection. -/
def WStep.applyV : WStep → Val → Val
  | .keep, v => v
  | .inl, v => Val.inj₁ v
  | .inr, v => Val.inj₂ v

theorem WStep.apply_val (w : WStep) (v : Val) : w.apply (.val v) = .val (w.applyV v) := by
  cases w <;> rfl

theorem WStep.apply_subst (w : WStep) (j : Nat) (s : Val) (e : Expr) :
    Expr.subst j s (w.apply e) = w.apply (Expr.subst j s e) := by
  cases w <;> rfl

theorem WStep.sameCells (w : WStep) (v : Val) : SameCells v (w.applyV v) := by
  cases w <;> rfl

/-- **The widening hands back the cells it is given.** -/
theorem retsG_wid {G : Expr → Prop} : ∀ (ws : List WStep) (π : Val),
    RetsG (ℍ := ℍ) (SameCells π) G (.app (widE ws) (.val π))
  | [], π => by
      refine retsG_beta .hole ?_
      exact retsG_val (SameCells.refl π)
  | w :: ws, π => by
      refine retsG_beta .hole ?_
      simp only [Kont.plug, Expr.subst]
      refine retsG_letpairV (fun p ρ hπ => ?_)
      subst hπ
      simp only [Expr.subst, WStep.apply_subst, subst_widE, subst_shift_succ, Expr.shift_zero]
      fsimp
      rw [WStep.apply_val]
      refine retsG_plain (K := .pairR (w.applyV p) .hole) rfl (retsG_wid ws ρ) (fun v hv => ?_)
      exact retsG_val (w := Val.pair (w.applyV p) v)
        (sameCells_pair (WStep.sameCells w p) hv)

/-! ### `swap` hands back its cell -/

/-- The answers `(c, w)`: the cell `c` handed back beside a content. -/
def CellQ (c : Val) (y : Val) : Prop := ∃ w, y = Val.pair c w

/-- `swap c v` answers `(c, w)`: the cell it was given, beside the old content. -/
theorem retsG_swap {G : Expr → Prop} (c v : Val) :
    RetsG (ℍ := ℍ) (CellQ c) G (.app (.app swap (.val c)) (.val v)) := by
  change RetsG _ G ((Kont.appL .hole v).plug (.app (.val (.lam _)) (.val c)))
  refine retsG_beta _ ?_
  try simp only [BoCa.v0, BoCa.v1, BoCa.v2, BoCa.elet, BoCa.load', BoCa.store']
  try fsimp
  refine retsG_beta .hole ?_
  try simp only [BoCa.v0, BoCa.v1, BoCa.v2, BoCa.elet, BoCa.load', BoCa.store']
  try fsimp
  refine retsG_plain (K := .appR (.lam _) .hole) rfl (retsG_true _ _) (fun w _ => ?_)
  refine retsG_beta .hole ?_
  try simp only [BoCa.v0, BoCa.v1, BoCa.v2, BoCa.elet, BoCa.load', BoCa.store']
  try fsimp
  refine retsG_plain (K := .seq .hole _) (by simp [Kont.Plain]) (retsG_true _ _) (fun u _ => ?_)
  refine retsG_seqv ?_
  try simp only [BoCa.v0, BoCa.v1, BoCa.v2, BoCa.elet, BoCa.load', BoCa.store']
  try fsimp
  exact retsG_val (Q := CellQ c) (w := Val.pair c w) ⟨w, rfl⟩

/-! ### `core` -/

theorem acc_core (Ps : List VTy) (N : Expr) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (coreE Ps N)) := by
  intro π
  apply rets_of_retsG
  change RetsG (AnsQ π) _ (Kont.plug .hole (.app (.val (.lam (Expr.psub 1 γ
    (thenE (.inj₁ (.pair (.var 1) (.var 0))) (.app (dtorE (slotsTy Ps)) (.var 1)) (sh 1 N)))))
    (.val π)))
  refine retsG_beta .hole ?_
  have e : (Expr.psub 1 γ (thenE (.inj₁ (.pair (.var 1) (.var 0))) (.app (dtorE (slotsTy Ps)) (.var 1))
      (sh 1 N))).subst 0 π = ubindE (Val.pair (Val.lam (.inj₁ (.pair (π.shift 1 0).1 (.var 0))))
        (Val.lam (.app (dtorE (slotsTy Ps)) (π.shift 1 0).1))) (Expr.psub 0 γ N) := by
    simp [thenE, ubindE, Expr.psub, Expr.subst, psub_dtor, subst_dtor, sh, psub_sh,
      subst_shift_expr, Val.pair, Val.lam, Expr.val]
  rw [Kont.plug, e]
  refine retsG_ubind (Q₁ := fun _ => True) (retsG_true _ _) (fun v _ => ?_)
  refine retsG_beta .hole ?_
  have e2 : (Expr.inj₁ (.pair (π.shift 1 0).1 (.var 0))).subst 0 v = .val (Val.inj₁ (Val.pair π v)) := by
    simp [Expr.subst, Val.pair, Val.inj₁, Expr.val]
  rw [Kont.plug, e2]
  exact retsG_val (ansQ_inl (SameCells.refl π) v)

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
  change RetsG (AnsQ π) _ (Kont.plug .hole (.app (.val (.lam (Expr.psub 1 γ
    (.inj₂ (.pair (.var 0) (injAt k (sh 1 V))))))) (.val π)))
  refine retsG_beta .hole ?_
  have e : (Expr.psub 1 γ (.inj₂ (.pair (.var 0) (injAt k (sh 1 V))))).subst 0 π =
      (Kont.inj₂ (.pairR π (injK k))).plug (Expr.psub 0 γ V) := by
    simp [Expr.psub, Expr.subst, psub_injAt, subst_injAt, sh, psub_sh, subst_shift_expr,
      Kont.plug, injK_plug]
  rw [Kont.plug, e]
  refine retsG_plain (by simp [Kont.Plain, injK_plain]) (retsG_true _ _) (fun v _ => ?_)
  have e2 : (Kont.inj₂ (.pairR π (injK k))).plug (.val v) =
      .val (Val.inj₂ (Val.pair π (injV k v))) := by
    simp [Kont.plug, injK_plug, injAt_val, Val.pair, Val.inj₂, Expr.val]
  rw [e2]
  exact retsG_val (ansQ_inr (SameCells.refl π) _)

/-- A β step at a value written as an expression. -/
theorem retsG_betaE {Q : Val → Prop} {G : Expr → Prop} (K : Kont) {b e : Expr} (he : IsVal e)
    (h : RetsG (ℍ := ℍ) Q G (K.plug (b.subst 0 ⟨e, he⟩))) :
    RetsG (ℍ := ℍ) Q G (K.plug (.app (.lam b) e)) :=
  retsG_beta (v := ⟨e, he⟩) K h

/-! ### Calling a premise -/

/-- A premise's frame, closed by `a :: γ`, called on `π'`, which holds the cells of `π`. -/
theorem retsG_call {G : Expr → Prop} {π π' a : Val} {γ : List Val} {e : Expr} (hπ : SameCells π π')
    (h : Returns (ℍ := ℍ) (substAll (a :: γ) e)) :
    RetsG (ℍ := ℍ) (AnsQ π) G (.app (.app (.val (.lam (Expr.psub 1 γ e))) (.val a)) (.val π')) := by
  refine retsG_beta (K := .appL .hole π') ?_
  have := h π'
  rw [substAll_cons_psub] at this
  exact retsG_mono (fun _ hw => AnsQ.trans hπ hw) (fun _ h => h) (retsG_of_rets this)

/-- A premise's frame under two binders, closed by `s :: i :: γ`, called on `π'`. -/
theorem retsG_call2 {G : Expr → Prop} {π π' i s : Val} {γ : List Val} {e : Expr}
    (hπ : SameCells π π') (h : Returns (ℍ := ℍ) (substAll (s :: i :: γ) e)) :
    RetsG (ℍ := ℍ) (AnsQ π) G
      (.app (.app (.app (.val (.lam (.val (.lam (Expr.psub 2 γ e))))) (.val i)) (.val s)) (.val π')) := by
  refine retsG_beta (K := .appL (.appL .hole s) π') ?_
  have e1 : (Expr.val (Val.lam (Expr.psub 2 γ e))).subst 0 i = .val (.lam (Expr.psub 1 (i :: γ) e)) := by
    simp [Expr.val, Val.lam, Expr.subst, Expr.psub_cons 1 i γ e]
  rw [e1]
  exact retsG_call hπ h

/-- A premise's frame, closed by `γ`, called on `π'`, which holds the cells of `π`. -/
theorem retsG_call0 {G : Expr → Prop} {π π' : Val} {γ : List Val} {e : Expr} (hπ : SameCells π π')
    (h : Returns (ℍ := ℍ) (substAll γ e)) :
    RetsG (ℍ := ℍ) (AnsQ π) G (.app (substAll γ e) (.val π')) :=
  retsG_mono (fun _ hw => AnsQ.trans hπ hw) (fun _ h => h) (retsG_of_rets (h π'))

/-! ### `sub` -/

theorem acc_sub {e : Expr} (ih : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ e)) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (subE e)) := by
  intro π
  apply rets_of_retsG
  change RetsG (AnsQ π) _ (Kont.plug .hole (.app (.val (.lam (Expr.psub 1 γ
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
  change RetsG (AnsQ π) _ (Kont.plug .hole (.app (.val (.lam (Expr.psub 1 γ
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
    rw [e2]; exact retsG_call (SameCells.refl π) (ih₁ (a :: γ))
  · have e2 : (Expr.app (.app (Expr.shift 1 0 (.lam (Expr.psub 1 γ e₂))) (.var 0))
        (π.shift 1 0).1).subst 0 a = .app (.app (.val (.lam (Expr.psub 1 γ e₂))) (.val a)) (.val π) := by
      simp [Expr.subst, subst_shift_expr, Expr.val, Val.lam]
    rw [e2]; exact retsG_call (SameCells.refl π) (ih₂ (a :: γ))

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
  change RetsG (AnsQ π) _ (Kont.plug .hole (.app (.val (.lam (Expr.psub 1 γ
    (.app (.val (.lam (.case (.var 0)
      (.letpair (.var 0) (.app (.app (sh 5 (.val (.lam eN))) (.var 0)) (.var 1)))
      (exitArmE E (dropCtxE Γ₂ 3 (.inj₂ (.var 0))))))) (.app (sh 1 eM) (.var 0))))))
    (.val π)))
  refine retsG_beta .hole ?_
  simp [Kont.plug, Expr.psub, Expr.subst, sh, psub_sh, Expr.val, Val.lam,
    subst_shift_succ, Expr.shift_zero]
  refine retsG_plain (K := .appR (.lam _) .hole) rfl (retsG_of_rets (ihM γ π)) ?_
  intro v hv
  refine retsG_beta .hole ?_
  simp [Kont.plug, Expr.subst, subst_shift_succ]
  rcases hv.cases with ⟨π', x, hπ, rfl⟩ | ⟨π', x, hπ, rfl⟩
  · refine retsG_case₁ .hole ?_
    fsimp
    refine retsG_letpair .hole ?_
    fsimp
    have := retsG_call (G := fun _ => False) (π := π) (π' := π') (a := x) hπ (ihN (x :: γ))
    fsimp_at this; exact this
  · refine retsG_case₂ .hole ?_
    cases E with
    | nil =>
        simp [exitArmE, absurdE, Expr.psub, Expr.subst]
        refine retsG_letpair .hole ?_
        fsimp
        refine retsG_plain (K := .inj₂ (.pairR π' .hole)) rfl (retsG_true _ _) (fun u _ => ?_)
        exact retsG_val (w := Val.inj₂ (Val.pair π' u)) (ansQ_inr hπ u)
    | cons l E' =>
        simp only [exitArmE]
        refine retsG_chain (((((chain_dropCtx Γ₂ 3 _).psub 3 γ).subst 2 _).subst 1 _).subst 0 _) ?_
        fsimp
        exact retsG_val (w := Val.inj₂ (Val.pair π' x)) (ansQ_inr hπ x)

/-! ### `catch` -/

theorem acc_catch {Γ₂ : Ctx VTy} {eM eH : Expr}
    (ihM : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ eM))
    (ihH : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ eH)) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (catchE Γ₂ eM eH)) := by
  intro π
  apply rets_of_retsG
  change RetsG (AnsQ π) _ (Kont.plug .hole (.app (.val (.lam (Expr.psub 1 γ
    (.app (.val (.lam (.case (.var 0)
      (dropCtxE Γ₂ 3 (.inj₁ (.var 0)))
      (.letpair (.var 0) (.case (.var 0)
        (.app (.app (sh 6 (.val (.lam eH))) (.var 0)) (.var 2))
        (dropCtxE Γ₂ 6 (.inj₂ (.pair (.var 2) (.var 0))))))))) (.app (sh 1 eM) (.var 0))))))
    (.val π)))
  refine retsG_beta .hole ?_
  simp [Kont.plug, Expr.psub, Expr.subst, sh, psub_sh, Expr.val, Val.lam,
    subst_shift_succ, Expr.shift_zero]
  refine retsG_plain (K := .appR (.lam _) .hole) rfl (retsG_of_rets (ihM γ π)) ?_
  intro v hv
  refine retsG_beta .hole ?_
  simp [Kont.plug, Expr.subst, subst_shift_succ]
  rcases hv.cases with ⟨π', x, hπ, rfl⟩ | ⟨π', x, hπ, rfl⟩
  · refine retsG_case₁ .hole ?_
    refine retsG_chain (((((chain_dropCtx Γ₂ 3 _).psub 3 γ).subst 2 _).subst 1 _).subst 0 _) ?_
    fsimp
    exact retsG_val (w := Val.inj₁ (Val.pair π' x)) (ansQ_inl hπ x)
  · refine retsG_case₂ .hole ?_
    fsimp
    refine retsG_letpair .hole ?_
    fsimp
    refine retsG_caseV (fun b _ => ?_) (fun e' _ => ?_)
    · have := retsG_call (G := fun _ => False) (π := π) (π' := π') (a := b) hπ (ihH (b :: γ))
      fsimp; fsimp_at this; exact this
    · refine retsG_chain ((((((((chain_dropCtx Γ₂ 6 _).psub 6 γ).subst 5 _).subst 4 _).subst 3 _).subst 1 _).subst 1 _).subst 0 e') ?_
      fsimp
      exact retsG_val (w := Val.inj₂ (Val.pair π' e')) (ansQ_inr hπ e')

/-! ### Putting a slot back at the head -/

/-- An answer whose slots are `(q, ρ')`, `ρ'` holding the cells of `ρ`, hands back the cells of
`(q, ρ)`. -/
theorem ansQ_cons {q ρ ρ' : Val} (h : SameCells ρ ρ') (a : Val) :
    AnsQ (Val.pair q ρ) (Val.inj₁ (Val.pair (Val.pair q ρ') a)) ∧
      AnsQ (Val.pair q ρ) (Val.inj₂ (Val.pair (Val.pair q ρ') a)) :=
  ⟨ansQ_inl (sameCells_pair (SameCells.refl q) h) a, ansQ_inr (sameCells_pair (SameCells.refl q) h) a⟩

/-! ### `under` -/

theorem acc_under {Q : VTy} {eM : Expr}
    (ih : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ eM)) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (underE Q eM)) := by
  intro π
  apply rets_of_retsG
  change RetsG (AnsQ π) _ (Kont.plug .hole (.app (.val (.lam (Expr.psub 1 γ
    (.letpair (.var 0)
      (thenE (consAnsE 2) (.app (dtorE Q) (.var 2)) (.app (sh 3 eM) (.var 0))))))) (.val π)))
  refine retsG_beta .hole ?_
  simp [thenE, psub_dtor, subst_dtor, consAnsE]
  fsimp
  refine retsG_letpairV (fun q ρ hπ => ?_)
  subst hπ
  fsimp
  refine retsG_ubind (N := Val.lam _) (D := Val.lam _) (Q₁ := AnsQ ρ)
    (retsG_of_rets (by simpa [substAll] using ih γ ρ)) (fun v hv => ?_)
  refine retsG_beta .hole ?_
  fsimp
  rcases hv.cases with ⟨ρ', a, hρ, rfl⟩ | ⟨ρ', a, hρ, rfl⟩
  · refine retsG_case₁ .hole ?_
    fsimp
    refine retsG_letpair .hole ?_
    fsimp
    exact retsG_val (w := Val.inj₁ (Val.pair (Val.pair q ρ') a)) (ansQ_cons hρ a).1
  · refine retsG_case₂ .hole ?_
    fsimp
    refine retsG_letpair .hole ?_
    fsimp
    exact retsG_val (w := Val.inj₂ (Val.pair (Val.pair q ρ') a)) (ansQ_cons hρ a).2

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
  change RetsG (AnsQ π) _ (Kont.plug .hole (.app (.val (.lam (Expr.psub 1 γ
    (.letpair (.var 0)
      (.app (.val (.lam
        (.app (.val (.lam
          (thenE (.letpair (.var 0) (.inj₁ (.pair (.pair (.var 1) (.var 5)) (.var 0))))
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
    exact retsG_val (w := Val.inj₁ (Val.pair (Val.pair p ρ) b)) (ansQ_inl (SameCells.refl _) b)

/-! ### `lend` -/

theorem acc_lend (src : LendSrc) {eM : Expr}
    (ih : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ eM)) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (lendE src eM)) := by
  intro π
  apply rets_of_retsG
  show RetsG _ _ (Kont.plug .hole (.app (substAll γ (lendE src eM)) (.val π)))
  simp only [substAll, lendE, Expr.psub, LendSrc.fin, forgetHeadE, consAnsE]
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
    (retsG_withborU' (Qb := AnsQ ρ) (f := ⟨_, IsVal.lam⟩) src.ty p ?_) ?_
  · -- the callback, on the slots `(p, ρ)`: the inner frame, its head forgotten on both arms
    refine retsG_betaE (.appL .hole p) IsVal.unit ?_
    fsimp
    refine retsG_betaE .hole p.2 ?_
    fsimp
    refine retsG_betaE .hole (IsVal.pair p.2 ρ.2) ?_
    fsimp
    refine retsG_plain (K := .appR (.lam _) .hole) rfl
      (retsG_of_rets (by simpa [substAll] using ih γ (Val.pair p ρ))) ?_
    intro v hv
    refine retsG_beta .hole ?_
    fsimp
    rcases hv.cases with ⟨π'', a, hπ, rfl⟩ | ⟨π'', a, hπ, rfl⟩
    · refine retsG_case₁ .hole ?_
      fsimp
      refine retsG_letpair (v₁ := π'') (v₂ := a) .hole ?_
      fsimp
      refine retsG_letpairV (fun b' ρ' hb => ?_)
      subst hb
      fsimp
      refine retsG_beta (.seq .hole _) ?_
      refine retsG_seqU .hole ?_
      exact retsG_val (w := Val.inj₁ (Val.pair ρ' a)) (ansQ_inl (sameCells_pair_inv hπ).2 a)
    · refine retsG_case₂ .hole ?_
      fsimp
      refine retsG_letpair (v₁ := π'') (v₂ := a) .hole ?_
      fsimp
      refine retsG_letpairV (fun b' ρ' hb => ?_)
      subst hb
      fsimp
      refine retsG_beta (.seq .hole _) ?_
      refine retsG_seqU .hole ?_
      exact retsG_val (w := Val.inj₂ (Val.pair ρ' a)) (ansQ_inr (sameCells_pair_inv hπ).2 a)
  · rintro y ⟨z, rfl, hz⟩
    refine retsG_beta .hole ?_
    fsimp
    refine retsG_letpair (v₁ := p) (v₂ := z) .hole ?_
    fsimp
    rcases hz.cases with ⟨ρ', a, hρ, rfl⟩ | ⟨ρ', a, hρ, rfl⟩
    · refine retsG_case₁ .hole ?_
      fsimp
      refine retsG_letpair .hole ?_
      fsimp
      exact retsG_val (w := Val.inj₁ (Val.pair (Val.pair p ρ') a)) (ansQ_cons hρ a).1
    · refine retsG_case₂ .hole ?_
      fsimp
      refine retsG_letpair .hole ?_
      fsimp
      exact retsG_val (w := Val.inj₂ (Val.pair (Val.pair p ρ') a)) (ansQ_cons hρ a).2

/-! ### `new` -/

theorem acc_new (q : CellSt) (Q' : VTy) (V : Expr) {eM : Expr}
    (ih : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ eM)) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (newE q Q' V eM)) := by
  intro π
  apply rets_of_retsG
  show RetsG _ _ (Kont.plug .hole (.app (substAll γ (newE q Q' V eM)) (.val π)))
  simp only [substAll, newE, endCellE, Expr.psub]
  refine retsG_betaE .hole π.2 ?_
  fsimp
  refine retsG_plain (K := .appR (.lam _) .hole) rfl (retsG_true _ _) (fun c _ => ?_)
  refine retsG_beta .hole ?_
  fsimp
  refine retsG_betaE .hole (IsVal.pair c.2 π.2) ?_
  fsimp
  refine retsG_plain (K := .appR (.lam _) .hole) rfl
    (retsG_of_rets (by simpa [substAll] using ih γ (Val.pair c π))) ?_
  intro y hy
  refine retsG_beta .hole ?_
  fsimp
  rcases hy.cases with ⟨cπ, b, hcπ, rfl⟩ | ⟨cπ, b, hcπ, rfl⟩
  · refine retsG_case₁ .hole ?_
    fsimp
    refine retsG_letpair (v₁ := cπ) (v₂ := b) .hole ?_
    fsimp
    refine retsG_letpairV (fun c' π' hc => ?_)
    subst hc
    fsimp
    refine retsG_plain (K := .appR (.lam _) .hole) rfl (retsG_true _ _) (fun a _ => ?_)
    refine retsG_beta .hole ?_
    fsimp
    exact retsG_val (w := Val.inj₁ (Val.pair π' (Val.pair b a)))
      (ansQ_inl (sameCells_pair_inv hcπ).2 _)
  · refine retsG_case₂ .hole ?_
    fsimp
    refine retsG_letpair (v₁ := cπ) (v₂ := b) .hole ?_
    fsimp
    refine retsG_letpairV (fun c' π' hc => ?_)
    subst hc
    fsimp
    exact retsG_seq (retsG_val (w := Val.inj₂ (Val.pair π' b)) (ansQ_inr (sameCells_pair_inv hcπ).2 _))

/-! ### `swap` -/

theorem acc_swap (V : Expr) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (swapSE V)) := by
  intro π
  apply rets_of_retsG
  show RetsG _ _ (Kont.plug .hole (.app (substAll γ (swapSE V)) (.val π)))
  simp only [substAll, swapSE, Expr.psub]
  refine retsG_betaE .hole π.2 ?_
  fsimp
  refine retsG_letpairV (fun c ρ hπ => ?_)
  subst hπ
  fsimp
  -- the stored value, as any Core code; then `swap`, which hands back its cell
  refine retsG_plain (K := .appR (.lam _) (.appR (.app swap (.val c)) .hole)) rfl
    (retsG_true _ _) (fun v _ => ?_)
  refine retsG_plain (K := .appR (.lam _) .hole) rfl (retsG_swap c v) ?_
  rintro y ⟨w, rfl⟩
  refine retsG_beta .hole ?_
  fsimp
  refine retsG_letpair .hole ?_
  fsimp
  exact retsG_val (w := Val.inj₁ (Val.pair (Val.pair c ρ) w)) (ansQ_inl (SameCells.refl _) w)

/-! ### `caseSlot` -/

theorem acc_caseSlot {e₁ e₂ : Expr} (ih₁ : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ e₁))
    (ih₂ : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ e₂)) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (caseSlotE e₁ e₂)) := by
  intro π
  apply rets_of_retsG
  show RetsG _ _ (Kont.plug .hole (.app (substAll γ (caseSlotE e₁ e₂)) (.val π)))
  simp only [substAll, caseSlotE, Expr.psub]
  refine retsG_betaE .hole π.2 ?_
  fsimp
  refine retsG_letpairV (fun p ρ hπ => ?_)
  subst hπ
  fsimp
  refine retsG_caseV (fun p₁ hp => ?_) (fun p₂ hp => ?_)
  · subst hp
    fsimp
    refine retsG_betaE .hole (IsVal.pair p₁.2 ρ.2) ?_
    fsimp
    have := retsG_call0 (G := fun _ => False) (π := Val.pair (Val.inj₁ p₁) ρ) (π' := Val.pair p₁ ρ)
      (sameCells_pair (sameCells_inj₁ p₁) (SameCells.refl ρ)) (ih₁ γ)
    simpa [substAll] using this
  · subst hp
    fsimp
    refine retsG_betaE .hole (IsVal.pair p₂.2 ρ.2) ?_
    fsimp
    have := retsG_call0 (G := fun _ => False) (π := Val.pair (Val.inj₂ p₂) ρ) (π' := Val.pair p₂ ρ)
      (sameCells_pair (sameCells_inj₂ p₂) (SameCells.refl ρ)) (ih₂ γ)
    simpa [substAll] using this

/-! ### `widen` -/

theorem acc_widen (ws wx : List WStep) {e : Expr}
    (ih : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ e)) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (widenE ws wx e)) := by
  intro π
  apply rets_of_retsG
  show RetsG _ _ (Kont.plug .hole (.app (substAll γ (widenE ws wx e)) (.val π)))
  simp only [substAll, widenE, seqE, Expr.psub]
  refine retsG_betaE .hole π.2 ?_
  fsimp
  refine retsG_plain (K := .appR (.lam _) .hole) rfl
    (retsG_of_rets (by simpa [substAll] using ih γ π)) ?_
  intro v hv
  refine retsG_beta .hole ?_
  fsimp
  rcases hv.cases with ⟨π', a, hπ, rfl⟩ | ⟨π', a, hπ, rfl⟩
  · refine retsG_case₁ .hole ?_
    fsimp
    refine retsG_letpair .hole ?_
    fsimp
    refine retsG_plain (K := .inj₁ (.pairL .hole (.val a))) rfl (retsG_wid ws π') (fun w hw => ?_)
    exact retsG_val (w := Val.inj₁ (Val.pair w a)) (ansQ_inl (hπ.trans hw) a)
  · refine retsG_case₂ .hole ?_
    fsimp
    refine retsG_letpair .hole ?_
    fsimp
    refine retsG_plain (K := .inj₂ (.pairL .hole (.val a))) rfl (retsG_wid wx π') (fun w hw => ?_)
    exact retsG_val (w := Val.inj₂ (Val.pair w a)) (ansQ_inr (hπ.trans hw) a)

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

/-! ### The loops -/

/-- The loop states and exits that hold the cells of `π`: `(π', s)`, `π'` holding them. -/
def CellsQ (π : Val) (y : Val) : Prop := ∃ π' s : Val, y = Val.pair π' s ∧ SameCells π π'

theorem ansQ_count {π w : Val} (h : AnsQ π w) : CountQ (CellsQ π) (CellsQ π) w := by
  rcases h.cases with ⟨π', x, hπ, rfl⟩ | ⟨π', x, hπ, rfl⟩
  · exact .inl ⟨_, rfl, π', x, rfl, hπ⟩
  · exact .inr ⟨_, rfl, π', x, rfl, hπ⟩

theorem acc_loopCount (ws : List WStep) {n s₀ eM : Expr}
    (ih : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ eM)) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (loopCountE ws n s₀ eM)) := by
  intro π
  apply rets_of_retsG
  show RetsG _ _ (Kont.plug .hole (.app (substAll γ (loopCountE ws n s₀ eM)) (.val π)))
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
  -- one turn: the step on `(i, (π', s))` is the turn's answer, `inj₁ (π'', s′)` or `inj₂ (π'', x)`
  have hf : ∀ (i : UInt32) (s : Val), CellsQ π s →
      RetsG (ℍ := ℍ) (CountQ (CellsQ π) (CellsQ π)) (fun _ => False)
        (.app (.val ⟨_, hSv⟩) (.val (Val.pair (Val.i32 i) s))) := by
    rintro i s ⟨π', s', rfl, hπ⟩
    change RetsG _ _ (Kont.plug .hole (.app (Expr.psub 0 γ (countStepE eM)) _))
    simp only [countStepE, Expr.psub]
    refine retsG_betaE .hole (IsVal.pair (Val.i32 i).2 (IsVal.pair π'.2 s'.2)) ?_
    fsimp
    refine retsG_letpair (v₁ := Val.i32 i) (v₂ := Val.pair π' s') .hole ?_
    fsimp
    refine retsG_letpair (v₁ := π') (v₂ := s') .hole ?_
    fsimp
    have := retsG_call2 (G := fun _ => False) (π := π) (π' := π') (i := Val.i32 i) (s := s')
      (γ := γ) hπ (ih (s' :: Val.i32 i :: γ))
    fsimp_at this
    exact retsG_mono (fun _ hw => ansQ_count hw) (fun _ h => h) this
  change RetsG _ _ ((Kont.appR (.lam _) .hole).plug (.app (.val (.prim .countTry))
    (.val (Val.pair ⟨_, hSv⟩ (Val.pair nv (Val.pair (Val.i32 0) (Val.pair π sv)))))))
  refine retsG_plain (by simp [Kont.Plain]) (Q₁ := CountQ (CellsQ π) (CellsQ π)) ?_ ?_
  · by_cases hn : ∃ m, nv = Val.i32 m
    · obtain ⟨m, rfl⟩ := hn
      exact retsG_countTry _ m hf _ 0 (Val.pair π sv) rfl ⟨π, sv, rfl, SameCells.refl π⟩
    · exact retsG_countTry_stuck (fun ⟨_, m, _, _, h⟩ => hn ⟨m, (pairV_inj (pairV_inj h).2).1⟩)
  · rintro y (⟨s, rfl, π', s', rfl, hπ⟩ | ⟨x, rfl, π', x', rfl, hπ⟩)
    · refine retsG_beta .hole ?_
      fsimp
      refine retsG_case₁ (a := Val.pair π' s') .hole ?_
      fsimp
      refine retsG_letpair (v₁ := π') (v₂ := s') .hole ?_
      fsimp
      refine retsG_plain (K := .inj₁ (.pairL .hole (.val (Val.inj₁ s')))) rfl (retsG_wid ws π')
        (fun w hw => ?_)
      exact retsG_val (w := Val.inj₁ (Val.pair w (Val.inj₁ s'))) (ansQ_inl (hπ.trans hw) _)
    · refine retsG_beta .hole ?_
      fsimp
      refine retsG_case₂ (a := Val.pair π' x') .hole ?_
      fsimp
      refine retsG_letpair (v₁ := π') (v₂ := x') .hole ?_
      fsimp
      refine retsG_caseV (fun b _ => ?_) (fun e _ => ?_)
      · fsimp
        exact retsG_val (w := Val.inj₁ (Val.pair π' (Val.inj₂ b))) (ansQ_inl hπ _)
      · fsimp
        exact retsG_val (w := Val.inj₂ (Val.pair π' e)) (ansQ_inr hπ _)

theorem acc_loopIter (ws : List WStep) (S₀ : VTy) {s₀ eM : Expr}
    (ih : ∀ γ : List Val, Returns (ℍ := ℍ) (substAll γ eM)) (γ : List Val) :
    Returns (ℍ := ℍ) (substAll γ (loopIterE ws S₀ s₀ eM)) := by
  intro π
  apply rets_of_retsG
  show RetsG _ _ (Kont.plug .hole (.app (substAll γ (loopIterE ws S₀ s₀ eM)) (.val π)))
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
  have hturn : ∀ s, CellsQ π s → RetsG (ℍ := ℍ) (TurnQ (CellsQ π) (CellsQ π)) (fun _ => False)
      (.app (.app (.val ⟨_, hSv⟩) (.val s)) (.val nextV)) := by
    rintro s ⟨π', s', rfl, hπ⟩
    change RetsG _ _ ((Kont.appL .hole nextV).plug (.app (Expr.psub 0 γ (iterStepE S₀ eM)) _))
    simp only [iterStepE, withPair, Expr.psub]
    refine retsG_betaE _ (IsVal.pair π'.2 s'.2) ?_
    fsimp
    refine retsG_letpair (v₁ := π') (v₂ := s') (.appL .hole nextV) ?_
    fsimp
    refine retsG_beta (v := nextV) .hole ?_
    fsimp
    refine retsG_case₁ (a := Val.unit) .hole ?_
    fsimp
    refine retsG_seqU .hole ?_
    refine retsG_plain (K := .appR (.lam _) .hole) rfl (Q₁ := AnsQ π) ?_ ?_
    · have := retsG_call (G := fun _ => False) (π := π) (π' := π') (a := s') (γ := γ) hπ (ih (s' :: γ))
      fsimp_at this; exact this
    intro y hy
    refine retsG_beta .hole ?_
    fsimp
    rcases hy.cases with ⟨π'', x, hπ', rfl⟩ | ⟨π'', x, hπ', rfl⟩
    · refine retsG_case₁ .hole ?_
      fsimp
      exact retsG_val (w := Val.inj₂ (Val.pair π'' x)) (.inr ⟨_, rfl, π'', x, rfl, hπ'⟩)
    · refine retsG_case₂ .hole ?_
      fsimp
      exact retsG_val (w := Val.inj₁ (Val.pair π'' x)) (.inl ⟨_, rfl, π'', x, rfl, hπ'⟩)
  have hclose : ∀ s, CellsQ π s → RetsG (ℍ := ℍ) (CellsQ π) (fun _ => False)
      (.app (.app (.val ⟨_, hSv⟩) (.val s)) (.val closeV)) := by
    rintro s ⟨π', s', rfl, hπ⟩
    change RetsG _ _ ((Kont.appL .hole closeV).plug (.app (Expr.psub 0 γ (iterStepE S₀ eM)) _))
    simp only [iterStepE, withPair, Expr.psub]
    refine retsG_betaE _ (IsVal.pair π'.2 s'.2) ?_
    fsimp
    refine retsG_letpair (v₁ := π') (v₂ := s') (.appL .hole closeV) ?_
    fsimp
    refine retsG_beta (v := closeV) .hole ?_
    fsimp
    refine retsG_case₂ (a := Val.unit) .hole ?_
    fsimp
    refine retsG_seqU .hole ?_
    exact retsG_seq (retsG_val (w := Val.pair π' Val.unit) ⟨π', Val.unit, rfl, hπ⟩)
  change RetsG _ _ ((Kont.appR (.lam _) .hole).plug (.app (.val (.prim .iterate))
    (.val (Val.pair ⟨_, hSv⟩ (Val.pair π sv)))))
  refine retsG_plain (by simp [Kont.Plain]) (Q₁ := IterQ (CellsQ π) (CellsQ π))
    (retsG_iterate (P := CellsQ π) _ hturn hclose ⟨π, sv, rfl, SameCells.refl π⟩) ?_
  rintro y (⟨x, rfl, π', x', rfl, hπ⟩ | ⟨u, rfl, π', u', rfl, hπ⟩)
  · refine retsG_beta .hole ?_
    fsimp
    refine retsG_case₁ (a := Val.pair π' x') .hole ?_
    fsimp
    refine retsG_letpair (v₁ := π') (v₂ := x') .hole ?_
    fsimp
    refine retsG_caseV (fun b _ => ?_) (fun e _ => ?_)
    · fsimp
      exact retsG_val (w := Val.inj₁ (Val.pair π' (Val.inj₁ b))) (ansQ_inl hπ _)
    · fsimp
      exact retsG_val (w := Val.inj₂ (Val.pair π' e)) (ansQ_inr hπ _)
  · refine retsG_beta .hole ?_
    fsimp
    refine retsG_case₂ (a := Val.pair π' u') .hole ?_
    fsimp
    refine retsG_letpair (v₁ := π') (v₂ := u') .hole ?_
    fsimp
    refine retsG_plain (K := .inj₁ (.pairL .hole (.val (Val.inj₂ Val.unit)))) rfl (retsG_wid ws π')
      (fun w hw => ?_)
    exact retsG_val (w := Val.inj₁ (Val.pair w (Val.inj₂ Val.unit))) (ansQ_inl (hπ.trans hw) _)

end BoCa.Fig16.LogRel.Core.Frames

end

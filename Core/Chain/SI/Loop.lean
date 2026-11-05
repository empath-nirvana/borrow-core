import Core.Chain.SI.Fin
import Core.Fix

/-!
# Step-indexed relation: the unbounded loop

`iterate (f, s)` runs the turn `(f s) next`; at `inr s′` it ticks, and at the tick's answer
*next* goes on as `iterate (f, s′)`, at *close* answers `inr ((f s′) close)`. `ewp_iterate` is the
loop's rule: an invariant `I` of the state, kept by every turn, puts the loop in `ewp` at every
index, by induction on the index (Löb induction): each turn ticks, and a tick is a stop, so the
next turn is owed only at a smaller index. No fuel and no termination: a loop whose ticks are
always answered *next* is in `ewp` and never ends.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- A protocol whose cancel obligations are kept by every context with no handler and no catcher
(`cancelObl_ctx`). -/
def CtxClosed (P : Prot) : Prop :=
  ∀ m i s C, P.perf m i = some s → s.cancel = some C → ∀ K : Kont, (∀ m, K.HasHnd m = false) →
    (∀ m, K.Catches m = false) → ∀ k x σ, C k x σ → C k (K.plug x) σ

/-- A context with no handler and no catcher passes every stop of a `CtxClosed` protocol. -/
theorem bindOK_pure {P : Prot} (hP : CtxClosed P) {K : Kont} (hH : ∀ m, K.HasHnd m = false)
    (hC : ∀ m, K.Catches m = false) : BindOK K emp P P where
  perf := fun m i s hs => ⟨hH m, s, hs, rfl, rfl, fun C' hc' => ⟨C', hc', fun k x σ _ h => by
    rw [dead_plain K hH (hC 0), un_emp_right]; exact hP m i s C' hs hc' K hH hC k x σ h⟩⟩
  rais := fun m i R hR => ⟨hC m, R, hR, fun k v σ _ h => by rwa [un_emp_right]⟩

/-- `iterate (f, s)`. -/
def iterateE (f s : Val) : Expr := .app (.val (.prim .iterate)) (.val (Val.pair f s))

/-- The turn's postcondition: done at `inl x`, in the loop's postcondition, or going on at
`inr s′`, in the invariant. -/
def turnPost (I : Val → Heap → Prop) (QL : Post) : Post := fun k v σ =>
  (∃ x, v = Val.inj₁ x ∧ QL k (Val.inj₁ x) σ) ∨ (∃ s', v = Val.inj₂ s' ∧ I s' σ)

/-- The loop's frame around the turn. -/
def iterK (f : Val) : Kont := .case .hole (.inj₁ (.var 0)) (.app (.val (.lam (iterTurn f))) tickE)

theorem iterNext_eq (f s : Val) :
    iterNext f s = (iterK f).plug (.app (.app (.val f) (.val s)) (.val nextV)) := rfl

theorem iterTurn_subst {f s w : Val} (hf : closedAt 0 f.1 = true) (hs : closedAt 0 s.1 = true) :
    Expr.subst 0 w (Expr.subst 1 (s.shift 1 0) (iterTurn f)) =
      .case (.val w) (.app (.val (.prim .iterate)) (.pair (.val f) (.val s)))
        (.app (.val inrV) (.app (.app (.val f) (.val s)) (.val closeV))) := by
  simp only [iterTurn, Expr.subst, Val.val_shift, shift_closedAt _ _ hf (Nat.zero_le _),
    shift_closedAt _ _ hs (Nat.zero_le _)]
  simp [Expr.subst, subst_closedAt _ _ hf (Nat.zero_le _), subst_closedAt _ _ hs (Nat.zero_le _),
    inrV, closeV, Expr.val]

theorem iterK_case₂ (f s : Val) :
    Expr.subst 0 s (.app (.val (.lam (iterTurn f))) tickE) =
      (Kont.appR (.val (Val.lam (Expr.subst 1 (s.shift 1 0) (iterTurn f)))) .hole).plug
        (performE (.val (opPayload divEff 0 Val.unit))) := by
  simp [Expr.subst, tickE, Kont.plug, performE, opPayload, Val.pair, Val.i32, Val.lam, Expr.val,
    Val.unit, Val.prim]

/-- **The loop rule.** -/
theorem ewp_iterate {P : Prot} {QL : Post} {f : Val} (hf : closedAt 0 f.1 = true)
    {I : Val → Heap → Prop} {ts : OpSpec} (hP : CtxClosed P) (hQL : QL.Down)
    (htick : P.perf divEff 0 = some ts) (htc : ts.cancel = none)
    (hta : ∀ k, ts.PA k Val.unit emp)
    (htb : ∀ k w σ, ts.PB k w σ → (w = nextV ∨ w = closeV) ∧ σ = emp)
    (hIc : ∀ s σ, I s σ → closedAt 0 s.1 = true)
    (hturn : ∀ k s σ, I s σ →
      ewp (ℍ := ℍ) P (turnPost I QL) k (.app (.app (.val f) (.val s)) (.val nextV)) σ)
    (hclose : ∀ k s σ, I s σ →
      ewp (ℍ := ℍ) P QL k (.app (.val inrV) (.app (.app (.val f) (.val s)) (.val closeV))) σ) :
    ∀ n s σ, I s σ → ewp (ℍ := ℍ) P QL n (iterateE f s) σ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s σ hI
  refine ewp_pred fun n₁ hn₁ => ?_
  refine ewp_head (K := .hole) (fun μ => Head.iterate μ f s) rfl ?_
  simp only [Kont.plug_hole]
  rw [iterNext_eq, ← un_emp_right σ]
  refine ewp_bind (iterK f) (bindOK_pure hP (fun m => by simp [iterK, Kont.HasHnd])
    (fun m => by simp [iterK, Kont.Catches])) n₁ _ σ (disj_emp_right σ) ?_ (hturn n₁ s σ hI)
  rintro k hk v σ' - (⟨x, rfl, hx⟩ | ⟨s', rfl, hs'⟩)
  · refine ewp_pred fun k₁ hk₁ => ?_
    refine ewp_head (K := .hole) (fun μ => Head.case₁ μ x _ _) rfl ?_
    rw [un_emp_right]
    exact ewp_val (v := Val.inj₁ x) (hQL _ _ _ (hk₁ ▸ hx))
  · refine ewp_pred fun k₁ hk₁ => ?_
    refine ewp_head (K := .hole) (fun μ => Head.case₂ μ s' _ _) rfl ?_
    simp only [Kont.plug_hole]
    rw [iterK_case₂, un_emp_right, ← un_emp_left σ']
    refine ewp_pred fun k₂ hk₂ => ?_
    refine ewp_perform _ (by simp [Kont.HasHnd]) htick (disj_emp_left σ') (hta k₂) ?_
      (fun C hC => by rw [htc] at hC; cases hC)
    intro j hj w σw _ hb
    obtain ⟨hw, rfl⟩ := htb j w σw hb
    rw [un_emp_right]
    refine ewp_pred fun j₁ hj₁ => ?_
    refine ewp_head (K := .hole) (fun μ => Head.beta μ _ w) rfl ?_
    simp only [Kont.plug_hole]
    rw [iterTurn_subst hf (hIc s' σ' hs')]
    rcases hw with rfl | rfl
    · refine ewp_pred fun j₂ hj₂ => ?_
      refine ewp_head (K := .hole) (fun μ => Head.case₁ μ Val.unit _ _) rfl ?_
      simp only [Kont.plug_hole, Expr.subst, subst_closedAt _ _ hf (Nat.zero_le _),
        subst_closedAt _ _ (hIc s' σ' hs') (Nat.zero_le _)]
      exact ih j₂ (by omega) s' σ' hs'
    · refine ewp_pred fun j₂ hj₂ => ?_
      refine ewp_head (K := .hole) (fun μ => Head.case₂ μ Val.unit _ _) rfl ?_
      simp only [Kont.plug_hole, Expr.subst, subst_closedAt _ _ hf (Nat.zero_le _),
        subst_closedAt _ _ (hIc s' σ' hs') (Nat.zero_le _)]
      have := hclose j₂ s' σ' hs'
      simpa [inrV, closeV, Expr.subst, Expr.val] using this

end BoCa.Fig16.LogRel.Core.Chain.SI

end

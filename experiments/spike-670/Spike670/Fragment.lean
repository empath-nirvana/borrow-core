import Spike670.Closure

/-!
# #670 — slice 1 closed: the derivation-following fragment

`InSlice fuel t`: every node of `t`, down to the conversion's fuel, is one of the nodes slice 1
covers. `slice1_linear`: for such a term, at a well-formed context and with no machine
operations, `conv`'s output consumes exactly the context's live variables, binding each variable
once from the counter.

`D` is `fun _ => True` here: the copies are licensed per node by `copy_slots_persistent` (the
kernel's `Ctx.SplitP` and the masks), which this theorem does not thread (see the report).
-/

namespace Backend2.Spike670
open Backend2 BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check

/-- The nodes slice 1 covers, to a depth. -/
def InSlice : Nat → TExpr → Prop
  | 0, _ => True
  | f + 1, t => match t with
    | .var .. | .unitI .. | .lit .. => True
    | .tensorI _ _ _ _ _ t₁ t₂ => InSlice f t₁ ∧ InSlice f t₂
    | .sumI₁ _ _ _ _ c => InSlice f c
    | .sumE _ _ _ _ _ _ tV t₁ t₂ => InSlice f tV ∧ InSlice f t₁ ∧ InSlice f t₂
    | .tensorE _ _ _ _ _ _ tV tM => InSlice f tV ∧ InSlice f tM
    | .unitE _ _ _ _ tV tM => InSlice f tV ∧ InSlice f tM
    | .zeroE _ _ _ _ tV => InSlice f tV
    | .bind _ _ _ _ _ tM tN => InSlice f tM ∧ InSlice f tN
    | .allE _ _ _ _ _ _ c | .allI _ _ _ _ _ _ c | .nilDead _ _ _ c => InSlice f c
    | .lam _ _ _ _ c | .thunkF _ _ _ c => InSlice f c
    | .app _ _ _ _ _ _ tM => InSlice f tM ∧
        ∀ i' j' A' C' body, headOf 64 tM = .lam i' j' A' C' body → InSlice f body
    | _ => False

/-- **Slice 1.** -/
theorem slice1_linear : ∀ (fuel : Nat) (t : TExpr), InSlice fuel t →
    Spec (fun _ => True) (fun c => conv fuel c t)
  | 0, t, _ => by
    intro ctx s tm s' _ _ h
    simp only at h; rw [conv.eq_def] at h; exact (ok_throw h).elim
  | f + 1, t, hs => by
    intro ctx s tm s' hw hm h
    simp only at h
    have hD : ∀ (m : Masks), ∀ x ∈ bothVars (ctx.zip m.ms), (fun _ => True) x :=
      fun _ _ _ => trivial
    cases t <;> simp only [InSlice] at hs
    case var => exact node_var hw hm h
    case unitI => exact node_unitI hw hm h
    case lit => exact node_lit hw hm h
    case tensorI => exact node_tensorI (slice1_linear f _ hs.1) (slice1_linear f _ hs.2) (hD _) hw hm h
    case sumI₁ => exact node_sumI₁ (slice1_linear f _ hs) hw hm h
    case sumE =>
      exact node_sumE (slice1_linear f _ hs.1) (slice1_linear f _ hs.2.1)
        (slice1_linear f _ hs.2.2) (hD _) hw hm h
    case tensorE =>
      exact node_tensorE (slice1_linear f _ hs.1) (slice1_linear f _ hs.2) (hD _) hw hm h
    case unitE => exact node_unitE (slice1_linear f _ hs.1) (slice1_linear f _ hs.2) (hD _) hw hm h
    case zeroE => exact node_zeroE (slice1_linear f _ hs) (hD _) hw hm h
    case bind => exact node_bind (slice1_linear f _ hs.1) (slice1_linear f _ hs.2) (hD _) hw hm h
    case allE => exact node_allE (slice1_linear f _ hs) hw hm h
    case allI => exact node_allI (slice1_linear f _ hs) hw hm h
    case nilDead => exact node_nilDead (slice1_linear f _ hs) hw hm h
    case lam => exact node_lam (slice1_linear f _ hs) hw hm h
    case thunkF => exact node_thunkF (slice1_linear f _ hs) hw hm h
    case app =>
      exact node_app (slice1_linear f _ hs.1)
        (fun i' j' A' C' body hh => slice1_linear f _ (hs.2 i' j' A' C' body hh)) (hD _) hw hm h
    all_goals exact hs.elim

end Backend2.Spike670

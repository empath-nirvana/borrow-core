import FnMut.Passing

/-!
# FnMut — returned, and bounded by the borrows it captures (requirement 4)

* `retProg`: `mkCounter : !U(I32 ⊸ F([@⊤] U(FnMut^⊤ I32 I32)))` allocates the counter's cell
  and returns the closure, owned.  Called at `10`, the closure is called with `5` and closed:
  `15`.  (`counterProg` stores a closure in a cell.)
* `logProg`: a logger capturing a borrow.  `log : Ref I32` is lent as `ml : Mut 'x I32`; inside a
  scope `'w ⊏ 'x` the logger is made with state `ml`, so it is `[@'w] U(FnMut^'w I32 I32)`:
  it outlives `'w` because its state does (`'w ⊏ 'x`).  Each call adds its argument to the log
  through `ml` (`withswap`); `close` forgets `ml`.  Called with `5` and `7` and closed; after the
  borrow ends the owner frees the log: `12`.
* The bound is the captured borrow's lifetime: the logger's state does not outlive `'x`
  (`logState_not_outlives`), so `[]I` at `'x` over the state, the premise of `d_mkBox`, is
  refused; and no closure value outlives anything except through its box
  (`fnMut_not_outlives`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Returned from a function -/

/-- `λn. mkBox⊤ (alloc n) counterStep to f. f`. -/
def mkCounterV : Val :=
  .lam (mkE .top .i32 .i32 (.app (.val (.prim .alloc)) (.var 0)) counterStep (.var 0))

theorem d_mkCounter : CDerives LifeCtx.empty [] (.val mkCounterV) (.val (.bang (.lolli .i32 FC))) := by
  have hT : LifeCtx.empty.Defines .top := LifeCtx.defines_of_wf rfl
  refine .bangThunkV (persistent_dead .nil) rfl (.lam ?_)
  exact mkBoxC trivial hT (.ref .int) (appP (.var (by csoloP)) (.alloc (by cdeadP)))
    (d_counterStep hT (kill_dead _)) (.ret (.var (by csoloP)))

/-- `mkCounter to mk. mk 10 to f. callBox f 5 to (x, f). close f; x`. -/
def retProg : Expr :=
  bindE (.val mkCounterV) (bindE (.app (.var 0) (i32E 10))
    (elet (i32E 5) (callBoxE 1 0 (bindE (bindE (.var 0) (closeE 0)) (.seq (.var 0) (.var 2))))))

theorem retProg_derives : CDerives LifeCtx.empty [] retProg (.comp (.ret .i32)) := by
  refine bindC (.ret d_mkCounter) ?_
  refine bindC (.ret (appP (d_i32 10 (by cdeadP)) (.bangE (.var (by csoloP))))) ?_
  refine bindC (.ret (d_i32 5 (by cdeadP))) ?_
  refine bindC (unboxC (by csoloP)
    (callC (A := .i32) (B := .i32) (c := .top) trivial (by csoloP) (by csoloP))) ?_
  refine letC (.var (by csoloP)) ?_
  refine bindC (unboxC (by csoloP) (d_close (A := .i32) (B := .i32) (c := .top) trivial
    (by csoloP))) ?_
  exact seqC (.var (by csoloP)) (.ret (.var (by csoloP)))

theorem retProg_runs :
    ∃ n, BoCa.BoLo.Steps Adequacy.emptyMem retProg Adequacy.emptyMem (.val (Val.i32 n)) :=
  runs_i32 retProg_derives

set_option maxRecDepth 100000 in
theorem retProg_eval : i32NoLeak (eval retProg) = some 15 := by decide

/-! ### Capturing a borrow -/

/-- `'w ⊏ 'x` under `Δ₂`. -/
theorem lt_w_x : Δ₂.EntailsLt (.var 1) (.var 0) :=
  BoCa.Programs.entailsLt_of_bound (u := Δ₁.meetOfDom) rfl
    (fun _ _ h => BoCa.Programs.interp_meet_left h)

/-- A callback that captures its context: `thunk Λ. return (λx. body)` at a fresh `'x ⊏ ⊓Δ`,
the captured slots free of `'x`. -/
theorem callbackCap {Δ : LifeCtx} {Γ : Ctx VTy} {body : Expr} {x : LifeVar} {A B : VTy}
    (hΔ : Δ.Ok) (hx : Δ.find? x = none) (hΓx : ∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty)
    (h : CDerives (Δ.extend x Δ.meetOfDom) (⟨A, true⟩ :: ⟨.unit, false⟩ :: Γ) body (.val B)) :
    CDerives Δ Γ (.val (.lam (.val (.lam body)))) (.val (.all x Δ.meetOfDom (.lolli A B))) :=
  .thunkV rfl (.allI (Lifetime.Life.mentions_false_of_wf hx (Lifetime.meetOfDomL_wf Δ.entries))
    (fun _ _ h => hΔ.bound_mentions_false hx h) hΓx (.ret (.lamV h)))

/-- The logger's state: the borrow of the log. -/
abbrev LS : VTy := .mut (.var 0) .i32

/-- Types that outlive `'w` under `Δ₂`: data, and the logger's state. -/
def outW : VTy → Bool
  | .mut (.var 0) .i32 => true
  | A => dataB A

theorem outW_sound {A : VTy} (h : outW A = true) : VOutlives Δ₂ (.var 1) A := by
  by_cases e : A = LS
  · subst e; exact .mut lt_w_x
  · exact outlives_of_dataB (by unfold outW at h; split at h <;> simp_all)

theorem outlives_ctxW {Γ : Ctx VTy} (h : (Γ.all fun s => !s.live || outW s.ty) = true) :
    CtxOutlives Δ₂ Γ (.var 1) := by
  refine ⟨LifeCtx.defines_of_wf rfl, fun s hs hl => outW_sound ?_⟩
  have := List.all_eq_true.mp h s hs
  simpa [hl] using this

/-- `λs. ⟨λa. withswap s (λv. v + a to t. (t, t)) to (s, t). (t, [s]), forget s⟩`. -/
def logStep : Val :=
  .lam (withPair
    (.val (.lam (.letpair (.app (.app withswap (.var 3))
        (.val (.lam (elet (addE (.var 0) (.var 1)) (.pair (.var 0) (.var 0))))))
      (.pair (.var 0) (.var 1)))))
    (.app forget (.var 2)))

/-- The scope `'w`, capturing `ml` (at `3`):

    forget d; mkBox'w ml logStep to lg. callBox lg 5 to (x, lg). callBox lg 7 to (y, lg).
    close lg; [x + y]                                                                  -/
def logInner : Expr :=
  .seq (.app forget (.var 0))
    (mkE (.var 1) .i32 .i32 (.var 3) logStep
      (elet (i32E 5) (callBoxE 1 0
        (elet (i32E 7) (callBoxE 1 0
          (bindE (bindE (.var 0) (closeE 0)) (.seq (.var 0) (addE (.var 6) (.var 2)))))))))

/-- The context the scope's callback is typed in. -/
abbrev ΓL : Ctx VTy := [⟨.ref .unit, false⟩, ⟨LS, true⟩, ⟨.unit, false⟩]

theorem d_logInner :
    CDerives Δ₁ ΓL (lam2 logInner)
      (.val (.all 1 Δ₁.meetOfDom (.lolli (.imm (.var 1) .unit) (.box (.var 1) .i32)))) := by
  refine callbackCap rfl rfl (by intro s hs hl; simp at hs; rcases hs with rfl | rfl | rfl <;>
    simp_all [VFree, Lifetime.Life.mentions]) (.ofRet ?_)
  refine seqC (appP (.var (by csoloP)) (.forgetImm (by cdeadP))) ?_
  refine mkBoxC trivial (LifeCtx.defines_of_wf rfl) (.mut lt_w_x) (.var (by csoloP)) ?_ ?_
  · -- the logger's step
    refine .bangThunkV (persistent_dead (kill_dead _)) rfl (.lam (.withI (.lam ?_) ?_))
    · refine letC (appP (.thunkV rfl (.lam (A := .i32) (C := .ret (.tensor .i32 .i32)) (.ret (bindP (A := .i32) (d_add (pairP (.var (by csoloP))
          (.var (by csoloP))) (by cdeadP)) (pairP (.var (by csoloP)) (.var (by csoloP)))))))
        (appP (.var (by csoloP)) (.withswap (by cdeadP)))) ?_
      exact .ret (pairP (.var (by csoloP)) (.boxI (.var (by csoloP)) (outlives_ctxW (by decide))))
    · exact .ret (appP (.var (by csoloP)) (.forgetMut (by cdeadP)))
  refine bindC (.ret (d_i32 5 (by cdeadP))) ?_
  refine bindC (unboxC (by csoloP)
    (callC (A := .i32) (B := .i32) (c := .var 1) trivial (by csoloP) (by csoloP))) ?_
  refine letC (.var (by csoloP)) ?_
  refine bindC (.ret (d_i32 7 (by cdeadP))) ?_
  refine bindC (unboxC (by csoloP)
    (callC (A := .i32) (B := .i32) (c := .var 1) trivial (by csoloP) (by csoloP))) ?_
  refine letC (.var (by csoloP)) ?_
  refine bindC (unboxC (by csoloP) (d_close (A := .i32) (B := .i32) (c := .var 1) trivial
    (by csoloP))) ?_
  exact seqC (.var (by csoloP)) (.ret (.boxI (d_add (pairP (.var (by csoloP)) (.var (by csoloP)))
    (by cdeadP)) (outlives_ctx (LifeCtx.defines_of_wf rfl) (by decide))))

/-- The borrow `'x` of the log: `alloc () to d. withbor d logInner to (d, t). free d; [t]`. -/
def logBody : Expr :=
  elet (.app (.val (.prim .alloc)) (.val .unit))
    (.letpair (.app (.app withbor (.var 0)) (lam2 logInner))
      (elet (.app (.val (.prim .free)) (.var 1)) (.seq (.var 0) (.var 1))))

theorem d_logCb : CDerives LifeCtx.empty [] (lam2 logBody)
    (.val (.all 0 LifeCtx.empty.meetOfDom (.lolli LS (.box (.var 0) .i32)))) := by
  refine callbackW rfl rfl .nil ?_
  refine bindP (appP (.unitI (by cdeadP)) (.alloc (by cdeadP))) ?_
  refine letP (appP d_logInner (appP (.var (by csoloP))
    (.withbor1 (A := .unit) (B := .i32) 1 (by cdeadP) rfl (fun _ h => h.elim)
      (by simp [VFree]) (by simp [VFree])))) ?_
  refine bindP (appP (.var (by csoloP)) (.free (by cdeadP))) ?_
  exact .seqV (partP_split (.var 0) 0 _) (.var (by csoloP))
    (.boxI (.var (by csoloP)) (outlives_ctx (LifeCtx.defines_of_wf rfl) (by decide)))

/-- `alloc 0 to log. withbor log (Λ'x. λml. logBody) to (log, t). free log`. -/
def logProg : Expr :=
  bindE (.app (.val (.prim .alloc)) (i32E 0))
    (.letpair (.app (.app withbor (.var 0)) (lam2 logBody))
      (bindE (.app (.val (.prim .free)) (.var 1)) (.var 0)))

theorem logProg_derives : CDerives LifeCtx.empty [] logProg (.comp (.ret .i32)) := by
  refine bindC (.ret (appP (d_i32 0 (by cdeadP)) (.alloc (by cdeadP)))) ?_
  refine letC (appP (weak0 d_logCb (by cdead)) (appP (.var (by csoloP))
    (.withbor2 (A := .i32) (B := .i32) 0 (by cdeadP) rfl
      ⟨.top, LifeCtx.defines_of_wf rfl, outlives_of_dataB rfl⟩ (by simp [VFree])
      (by simp [VFree])))) ?_
  refine bindC (.ret (appP (.var (by csoloP)) (.free (by cdeadP)))) ?_
  exact .ret (.var (by csoloP))

theorem logProg_runs :
    ∃ n, BoCa.BoLo.Steps Adequacy.emptyMem logProg Adequacy.emptyMem (.val (Val.i32 n)) :=
  runs_i32 logProg_derives

set_option maxRecDepth 100000 in
/-- The log holds `5 + 7 = 12`: both calls wrote through the captured borrow. -/
theorem logProg_eval : i32NoLeak (eval logProg) = some 12 := by decide

/-! ### The bound -/

/-- A model of `Δ₂`: `'x ↦ 1`, `'w ↦ 2`. -/
theorem models₂ : Δ₂.Models ⟨[(1, 2), (0, 1)]⟩ := by
  intro x u h
  rcases x with _ | _ | x
  · cases h; exact ⟨1, 0, rfl, rfl, Nat.zero_lt_one⟩
  · cases h; exact ⟨2, 1, rfl, rfl, Nat.one_lt_two⟩
  · simp [Δ₂, Δ₁, LifeCtx.find?, LifeCtx.extend, Lifetime.assocFind, LifeCtx.empty] at h

theorem not_lt_x_x : ¬ Δ₂.EntailsLt (.var 0) (.var 0) := by
  intro h
  obtain ⟨m, n, hm, hn, hlt⟩ := h _ models₂
  rw [hm] at hn; cases hn
  exact Nat.lt_irrefl _ hlt

/-- **The logger cannot outlive the borrow it captures.**  Its state `Mut 'x I32` does not
outlive `'x`, so `[]I` at `'x` over a context holding it, the premise of `d_mkBox` at `'x`, is
refused. -/
theorem logState_not_outlives : ¬ VOutlives Δ₂ (.var 0) LS := by
  intro h; cases h with | «mut» h => exact not_lt_x_x h

theorem logState_ctx_not_outlives : ¬ CtxOutlives Δ₂ [⟨LS, true⟩] (.var 0) :=
  fun h => logState_not_outlives (h.2 ⟨LS, true⟩ (by simp) rfl)

/-- **An unboxed closure outlives nothing**: `VOutlives` has no rule at `U C`, so a closure is
stored or lent beyond its creation only as `[@c] U(FnMut^c A B)`, boxed where its state is in
the context. -/
theorem fnMut_not_outlives (Δ : LifeCtx) (a c : Lifetime.Life) (A B : VTy) :
    ¬ VOutlives Δ a (fnMutT c A B) := by
  intro h; cases h

end BoCa.Fig16.LogRel.Core

end

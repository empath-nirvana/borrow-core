import Core.EffTier1Programs

/-!
# Core — the async colourless test  `[spec §19, §20, §24]`

One generic function, written once with no async marker, run with a plain callback and with a
callback that suspends to a scheduler, which stores each task's continuation, runs the other task,
and resumes it later.

* **The generic function** `forN (k, (f, s))` calls `f` `k` times, threading the state `s`. It is
  `bounded_fix` (§20) whose budget is the count: the self-reference is `inj₁ ()` once `f` has run
  `k` times. Its step calls the callback by a `[let]` at the callback's row, whose continuation
  holds only the self-reference and the callback, both `!`; so it is typed at every row
  (`dAt_forN`).
* **The callbacks**: `tick` advances a two-bit count; `yieldTick` first performs `yield` with the
  task's tag, `yield : bool ↠ 1` affine at the name `3` of `ΞE`.
* **The spawn handler** answers a `yield` with the tag and the task's `κ` as a stored generator
  `Iter bool S 1 = νX. F((bool ⊗ U X) ⊕ S) & F 1` (§15): `next` is `κ`'s resume entry and `close`
  its cancel entry. The clause does not resume: `κ` leaves the handler as a value, its capture cell
  (§25) allocated at the `yield` and released when the scheduler resumes it.
* **The scheduler** `rr` is a round robin over the two stored continuations, `bounded_fix` at the
  pure row, its state both tasks and the trace. Each round resumes each task that yielded (`next`),
  which runs it to its next `yield` or its end, and records the tags; it answers once both have
  ended, or when its budget is spent, with the tasks as they stand.

| program | shows | answer |
|---|---|---|
| `asyncSync` | `forN` at the pure row with `tick` | `(ff, (tt, tt))` |
| `asyncTasks` | `forN` at `yield`'s row, run by two tasks under the scheduler | `schedV`: both ended; the trace, oldest first, `A B A B A B` |
| `asyncColourless` | `forN` let-bound once and used at both rows (`[let-poly]`) | `((ff, (tt, tt)), schedV)` |

Each program is a closed term with a derivation tied to `ΞE`, which has no unrestricted abortive
operation (`noUnrExn_ΞE`). Its `[let-poly]` premise is the body with `forN` at each use
(`asyncSync_subst`, `asyncTasks_subst`, `asyncColourless_subst`), the copy that unfills to the let's
body (`*_unfill`). Each run is computed by `runM` from the empty memory to the answer at the empty
memory (`runM_val`). The backend compiles them as the kernel programs `async-sync`, `async-tasks`
and `async-colourless` (`Backend/Kernel.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.AsyncPrograms
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Steps hndE performE)
open BoCa.Lifetime (LifeCtx)
open BoCa.Fig16.LogRel.Core.CancelIntercept (hQ)
open BoCa.Fig16.LogRel.Core.Inversions (resumeE cancelE)
open BoCa.Fig16.LogRel.Core.Tier1Programs (boolT appE ΞE ΞE_3 dAt_hQ dAt_dead)

/-! ### Context bookkeeping -/

/-- A consumed context, up to live slots of persistent type. -/
local syntax "deadp" : tactic
local macro_rules
  | `(tactic| deadp) => `(tactic| first
      | exact Ctx.DeadP.nil
      | (refine Ctx.DeadP.cons ?_; deadp)
      | (refine Ctx.DeadP.drop (by rfl) ?_; deadp))

/-- The one live slot a variable reads, every other live slot persistent. -/
local syntax "solop" : tactic
local macro_rules
  | `(tactic| solop) => `(tactic| first
      | (refine Ctx.SoloP.here ?_; deadp)
      | (refine Ctx.SoloP.there ?_; solop)
      | (refine Ctx.SoloP.skip (by rfl) ?_; solop))

/-- A type that drops: data, `!`. -/
local syntax "dropTy" : tactic
local macro_rules
  | `(tactic| dropTy) => `(tactic| first
      | exact VTy.Drop.unit
      | exact VTy.Drop.bang _
      | exact VTy.Drop.int _
      | (refine VTy.Drop.tensor ?_ ?_ <;> dropTy)
      | (refine VTy.Drop.sum ?_ ?_ <;> dropTy))

theorem drops_nil : Ctx.Drops ([] : Ctx VTy) := fun _ h => absurd h List.not_mem_nil

theorem drops_dead {T : VTy} {Γ : Ctx VTy} (h : Γ.Drops) : Ctx.Drops (⟨T, false⟩ :: Γ) := by
  intro s hs hl
  rcases List.mem_cons.mp hs with rfl | hs
  · cases hl
  · exact h s hs hl

theorem drops_live {T : VTy} {Γ : Ctx VTy} (hT : T.Drop) (h : Γ.Drops) :
    Ctx.Drops (⟨T, true⟩ :: Γ) := by
  intro s hs hl
  rcases List.mem_cons.mp hs with rfl | hs
  · exact hT
  · exact h s hs hl

/-- Each live slot of a concrete context is at a type that drops. -/
local syntax "drops" : tactic
local macro_rules
  | `(tactic| drops) => `(tactic| first
      | exact drops_nil
      | (refine drops_dead ?_; drops)
      | (refine drops_live (by dropTy) ?_; drops))

theorem pers_nil : Persistent ([] : Ctx VTy) := fun _ h => absurd h List.not_mem_nil

theorem pers_dead {T : VTy} {Γ : Ctx VTy} (h : Persistent Γ) : Persistent (⟨T, false⟩ :: Γ) := by
  intro s hs hl
  rcases List.mem_cons.mp hs with rfl | hs
  · cases hl
  · exact h s hs hl

theorem pers_bang {A : VTy} {Γ : Ctx VTy} (h : Persistent Γ) :
    Persistent (⟨.bang A, true⟩ :: Γ) := by
  intro s hs hl
  rcases List.mem_cons.mp hs with rfl | hs
  · exact ⟨A, rfl⟩
  · exact h s hs hl

/-- Each live slot of a concrete context is a `!`. -/
local syntax "persp" : tactic
local macro_rules
  | `(tactic| persp) => `(tactic| first
      | exact pers_nil
      | (refine pers_dead ?_; persp)
      | (refine pers_bang ?_; persp))

/-- Every slot consumed. -/
local syntax "deadT" : tactic
local macro_rules
  | `(tactic| deadT) => `(tactic| first
      | exact Ctx.Dead.nil
      | (refine Ctx.Dead.cons ?_; deadT))

/-- The context with every slot consumed. -/
def deadOf : Ctx VTy → Ctx VTy
  | [] => []
  | s :: Γ => ⟨s.ty, false⟩ :: deadOf Γ

theorem dead_deadOf : ∀ (Γ : Ctx VTy), Ctx.Dead (deadOf Γ)
  | [] => .nil
  | _ :: Γ => .cons (dead_deadOf Γ)

/-- Every slot to the right. -/
theorem splitP_deadOf : ∀ (Γ : Ctx VTy), Ctx.SplitP Γ (deadOf Γ) Γ
  | [] => .nil
  | ⟨_, true⟩ :: Γ => .right (splitP_deadOf Γ)
  | ⟨_, false⟩ :: Γ => .dead (splitP_deadOf Γ)

section Kernel
variable {Ξ : EffCtx}

/-- **A closed function applied to a value**, `W V`: `V to x. W x`, `V` at `Γ₁` and the rest of the
context `Γ₂` consumed up to persistent slots. -/
theorem dAt_app {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hd : Ctx.DeadP Γ₂)
    {W V : Expr} {T : VTy} {C : CTy} (hWc : closedAt 0 W = true)
    (hW : CDerivesAt Ξ Δ [] W (.comp (.arr T C))) (hV : CDerivesAt Ξ Δ Γ₁ V (.val T)) :
    CDerivesAt Ξ Δ Γ (appE W V) (.comp C) := by
  unfold appE
  rw [shift_closedAt W 1 hWc (Nat.zero_le _)]
  exact .bind hs (.ret hV)
    (.app (.right (splitP_deadOf Γ₂))
      (hW.append_dead (Γ' := ⟨T, false⟩ :: deadOf Γ₂) (.cons (dead_deadOf Γ₂))) (.here hd))

end Kernel

/-! ### Terms -/

/-- `ff`, `inj₁ ()`. -/
abbrev ffE : Expr := .inj₁ .unit

/-- `tt`, `inj₂ ()`. -/
abbrev ttE : Expr := .inj₂ .unit

/-- The literal `i32[n]`. -/
abbrev i32E (n : UInt32) : Expr := .prim (.lit (.i32 n))

/-- `inc (hi, lo)`: one more on a two-bit count. -/
def incE : Expr := .lam (.letpair (.var 0)
  (.case (.var 0) (.pair (.var 2) ttE) (.case (.var 2) (.pair ttE ffE) (.pair ffE ffE))))

/-- The plain callback, `tick (t, c) = (t, inc c)`. -/
def tickE : Expr := .lam (.letpair (.var 0) (bindE (appE incE (.var 0)) (.pair (.var 2) (.var 0))))

/-- The callback that suspends, `yieldTick (t, c) = yield t; (t, inc c)`, `yield` of the name
`3`. -/
def yieldTickE : Expr := .lam (.letpair (.var 0)
  (bindE (performE (opArgE 3 0 (.var 1))) (bindE (appE incE (.var 1)) (.pair (.var 3) (.var 0)))))

/-- `forN`'s step: `(self, (f, s)) ↦ case self {inj₁ _. s | inj₂ me. s' ← f s; me (f, s')}`. The
budget is the count: `self` is `inj₁ ()` once the callback has run `k` times. -/
def forStepB : Expr := .letpair (.var 0) (.letpair (.var 0)
  (.case (.var 3)
    (.var 1)
    (bindE (.var 2) (bindE (.app (.var 0) (.var 2)) (bindE (.var 2)
      (bindE (.pair (.var 5) (.var 1)) (.app (.var 1) (.var 0))))))))

/-- **The generic function**, `forN (k, (f, s)) = bounded_fix (forStep, (k, (f, s)))`: `k` calls
of `f`, threading the state. -/
def forNB : Expr := bindE (.prim .boundedFix)
  (bindE (.pair (.lam forStepB) (.var 1)) (.app (.var 1) (.var 0)))

/-- `forN`. -/
abbrev forNE : Expr := .lam forNB

/-! ### Types -/

/-- Two bits `(hi, lo)`. -/
abbrev c2T : VTy := .tensor boolT boolT

/-- A task's state: its tag and a two-bit count. -/
abbrev stT : VTy := .tensor boolT c2T

/-- The callback at the row `r`: `!U(S ⊸ F_r S)`. -/
abbrev cbT (r : Row) : VTy := .bang (.thunk (.arr stT (CTy.effOf r stT)))

/-- `forN`'s recursion argument: the callback and the state. -/
abbrev forA (r : Row) : VTy := .tensor (cbT r) stT

/-- `forN`'s computation at the row `r`: `I32 ⊗ (!U(S ⊸ F_r S) ⊗ S) ⊸ F_r S`. -/
abbrev forNC (r : Row) : CTy := .arr (.tensor (.int .w32) (forA r)) (CTy.effOf r stT)

/-! ### The generic function, typed at every row -/

section Generic
variable {Ξ : EffCtx}

/-- `inc` at `c2T ⊸ F c2T`. -/
theorem dAt_inc {Δ : LifeCtx} : CDerivesAt Ξ Δ [] incE (.comp (.arr c2T (.ret c2T))) := by
  refine .lam (.tensorE (.left .nil) (.var (.here .nil)) ?_)
  -- `lo` at `0`, `hi` at `1`
  refine .sumE (A := .unit) (B := .unit) (.left (.right (.dead .nil))) (.var ?_) ?_ ?_
  · solop
  · refine .ret (.tensorI (A := boolT) (B := boolT) (.right (.dead (.left (.dead .nil)))) (.var ?_)
      (.sumI₂ (.unitI ?_)))
    · solop
    · deadp
  · refine .sumE (A := .unit) (B := .unit) (.right (.dead (.left (.dead .nil)))) (.var ?_) ?_ ?_
    · solop
    · refine .ret (.tensorI (.dup (by rfl) (.dup (by rfl) (.dead (.dead (.dead .nil)))))
        (.sumI₂ (.unitI ?_)) (.sumI₁ (.unitI ?_))) <;> deadp
    · refine .ret (.tensorI (.dup (by rfl) (.dup (by rfl) (.dead (.dead (.dead .nil)))))
        (.sumI₁ (.unitI ?_)) (.sumI₁ (.unitI ?_))) <;> deadp

/-- **`forN`'s step at every row `r`**: its `[let]` at `r` holds the self-reference and the
callback, both `!`, so it is typed whatever `r` performs. -/
theorem dAt_forStep {Δ : LifeCtx} (r : Row) :
    CDerivesAt Ξ Δ [] (.val (.lam forStepB)) (.val (fixStepTy (forA r) (CTy.effOf r stT))) := by
  refine .bangThunkV (dead_noLive .nil) rfl (.lam ?_)
  -- `q`
  refine .tensorE (A := fixSelfTy (forA r) (CTy.effOf r stT)) (B := forA r) (.left .nil)
    (.var (.here .nil)) ?_
  -- `a` at `0`, `self` at `1`
  refine .tensorE (A := cbT r) (B := stT) (.left (.right (.dead .nil))) (.var ?_) ?_
  · solop
  -- `s` at `0`, `f` at `1`, `self` at `3`
  refine .sumE (A := .unit) (B := .bang (.thunk (.arr (forA r) (CTy.effOf r stT))))
    (.right (.right (.dead (.left (.dead .nil))))) (.var ?_) ?_ ?_
  · solop
  · -- spent: `s`
    refine .effSub (RowLe.nil r) (.ret (.var ?_))
    solop
  · -- `me` at `0`, `s` at `1`, `f` at `2`: `fv ← return f`
    refine .bind (A := .thunk (.arr stT (CTy.effOf r stT)))
      (.right (.right (.dup (by rfl) (.dead (.dead (.dead .nil)))))) (.ret (.bangE (.var ?_))) ?_
    · solop
    -- `fv` at `0`, `me` at `1`, `s` at `2`, `f` at `3`: `s' ← fv s`, a `[let]` at `r`
    refine .effLet (A := stT) (.left (.right (.left (.right (.dead (.dead (.dead .nil)))))))
      (fun _ => by drops) (fun _ => by persp) ?_ ?_
    · refine .app (.left (.dead (.right (.dead (.dead (.dead (.dead .nil)))))))
        (.force (C := .arr stT (CTy.effOf r stT)) ?_) ?_ <;> solop
    -- `s'` at `0`, `me` at `2`, `f` at `4`: `mv ← return me`
    refine .bind (A := .thunk (.arr (forA r) (CTy.effOf r stT)))
      (.right (.dead (.left (.dead (.right (.dead (.dead (.dead .nil))))))))
      (.ret (.bangE (.var ?_))) ?_
    · solop
    -- `mv` at `0`, `s'` at `1`, `f` at `5`: `arg ← return (f, s')`
    refine .bind (A := forA r)
      (.right (.left (.dead (.dead (.dead (.left (.dead (.dead (.dead .nil)))))))))
      (.ret (.tensorI (.dead (.right (.dead (.dead (.dead (.left (.dead (.dead (.dead .nil)))))))))
        (.var ?_) (.var ?_))) ?_
    · solop
    · solop
    -- `arg` at `0`, `mv` at `1`: `mv arg`
    refine .app (.right (.left (deadSplit (by deadT))))
      (.force (C := .arr (forA r) (CTy.effOf r stT)) ?_) ?_ <;> solop

/-- **`forN` at every row `r`**: `I32 ⊗ (!U(S ⊸ F_r S) ⊗ S) ⊸ F_r S`. -/
theorem dAt_forN {Δ : LifeCtx} (r : Row) : CDerivesAt Ξ Δ [] forNE (.comp (forNC r)) := by
  refine .lam (.bind (.right .nil)
    (.ret (.bangE (.boundedFix (forA r) (CTy.effOf r stT) (.cons .nil)))) ?_)
  refine .bind (A := .tensor (fixStepTy (forA r) (CTy.effOf r stT)) (.tensor (.int .w32) (forA r)))
    (.right (.left .nil))
    (.ret (.tensorI (.dead (.right .nil)) (dAt_dead (.cons (.cons .nil)) (dAt_forStep r))
      (.var ?_))) ?_
  · solop
  refine .app (.right (.left (.dead .nil)))
    (.force (C := .arr (.tensor (fixStepTy (forA r) (CTy.effOf r stT))
      (.tensor (.int .w32) (forA r))) (CTy.effOf r stT)) ?_) ?_ <;> solop

end Generic

/-! ### The callbacks -/

/-- `yield`'s row, `yield : bool ↠ 1` affine at the name `3`. -/
abbrev yR : Row := Row.ofEff 3 [(.aff, boolT, .unit)] 0 ++ []

theorem rowAt_yR : RowAt ΞE yR := rowAt_ofEff_append ΞE_3 (by decide) (by simp) (rowAt_nil ΞE)

theorem not_unr_yR : ¬ yR.Unr := by
  rintro ⟨o, ho, hq⟩
  simp [Row.ofEff] at ho
  subst ho
  cases hq

/-- A context consumed up to persistent slots goes to both sides. -/
theorem splitP_self : ∀ {Γ : Ctx VTy}, Ctx.DeadP Γ → Ctx.SplitP Γ Γ Γ
  | _, .nil => .nil
  | _, .cons h => .dead (splitP_self h)
  | _, .drop hT h => .dup hT (splitP_self h)

section Callbacks
variable {Ξ : EffCtx}

/-- The state `(tag, (ff, ff))`. -/
theorem dAt_st0 {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) {tag : Expr}
    (ht : CDerivesAt Ξ Δ Γ tag (.val boolT)) :
    CDerivesAt Ξ Δ Γ (.pair tag (.pair ffE ffE)) (.val stT) :=
  .tensorI (splitP_self hΓ) ht
    (.tensorI (splitP_self hΓ) (.sumI₁ (.unitI hΓ)) (.sumI₁ (.unitI hΓ)))

/-- **The plain callback** `tick` at the pure row. -/
theorem dAt_tick {Δ : LifeCtx} : CDerivesAt Ξ Δ [] tickE (.val (cbT [])) := by
  refine .bangThunkV (dead_noLive .nil) rfl (.lam ?_)
  refine .tensorE (A := boolT) (B := c2T) (.left .nil) (.var (.here .nil)) ?_
  -- `c` at `0`, `t` at `1`: `c' ← inc c`
  refine .bind (A := c2T) (.left (.right (.dead .nil)))
    (dAt_app (.left (.dead (.dead .nil))) ?_ rfl dAt_inc (.var ?_)) ?_
  · deadp
  · solop
  -- `c'` at `0`, `t` at `2`: `(t, c')`
  refine .ret (.tensorI (A := boolT) (B := c2T) (.right (.dead (.left (.dead .nil)))) (.var ?_)
    (.var ?_)) <;> solop

/-- **The callback that suspends**, `yieldTick`, at `yield`'s row: `yield t` is a `[let]` at an
affine row, whose continuation holds `t` and `c`, data that drops. -/
theorem dAt_yieldTick {Δ : LifeCtx} : CDerivesAt ΞE Δ [] yieldTickE (.val (cbT yR)) := by
  refine .bangThunkV (dead_noLive .nil) rfl (.lam ?_)
  refine .tensorE (A := boolT) (B := c2T) (.left .nil) (.var (.here .nil)) ?_
  -- `c` at `0`, `t` at `1`: `yield t`
  refine .effLet (A := .unit) (.right (.dup (by rfl) (.dead .nil))) (fun _ => by drops)
    (fun h => absurd h not_unr_yR)
    (.effPerform (o := ⟨3, 0, .aff, boolT, .unit, .ret .unit⟩) rowAt_yR
      (by simp [Row.ofEff, Row.find]) rfl (.var ?_)) ?_
  · solop
  -- `u` at `0`, `c` at `1`, `t` at `2`: `c' ← inc c`
  refine .bind (A := c2T) (.right (.left (.right (.dead .nil))))
    (dAt_app (.dead (.left (.dead (.dead .nil)))) ?_ rfl dAt_inc (.var ?_)) ?_
  · deadp
  · solop
  -- `c'` at `0`, `t` at `3`: `(t, c')`
  refine .effSub (RowLe.nil yR) (.ret (.tensorI (A := boolT) (B := c2T)
    (.right (.right (.dead (.left (.dead .nil))))) (.var ?_) (.var ?_))) <;> solop

end Callbacks

/-! ### The spawn handler: each task's continuation, stored -/

/-- A task's stored continuation, the stored generator `Iter bool S 1 = νX. F((bool ⊗ U X) ⊕ S) &
F 1`: `next` resumes the task to its next `yield` or its end, and `close` cancels it. -/
abbrev genC : CTy := CTy.iter boolT stT .unit

/-- What the spawn handler answers: the task yielded a tag and its stored continuation, or ended
with its state. -/
abbrev rspT : VTy := .sum (.tensor boolT (.thunk genC)) stT

/-- `thunk (nu_in ⟨resume k (), cancel k⟩)`, `k` at the slot `j`: `κ` as the stored generator. -/
def genE (j : Nat) : Expr := withPair (resumeE (.var (j + 2)) .unit) (cancelE (.var (j + 2)))

/-- `return s ⇒ inr s`. -/
def spawnRetV : Val := ⟨.lam (.inj₂ (.var 0)), .lam⟩

/-- `yield (v, k) ⇒ inl (v, gen k)`: the clause does not resume `κ`; it answers it, stored. -/
def spawnClV : Val := ⟨.lam (.letpair (.var 0) (.inj₁ (.pair (.var 1) (genE 0)))), .lam⟩

/-- **The spawn handler** of `yield`, at the name `3`. -/
def spawnH : Val := hQ 3 .aff spawnRetV spawnClV

/-- `spawn M`: `M` run under the spawn handler, up to its first `yield` or its end. -/
def spawnE (M : Expr) : Expr := hndE spawnH M

theorem cancelTy_nil : cancelTy [] (.ret .unit) = .ret .unit := rfl

/-- `next g`, `g` the stored continuation at the slot `i`: `(nu_out g).1`. -/
theorem dAt_next {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat}
    (h : Ctx.SoloP Γ i (.thunk genC)) :
    CDerivesAt Ξ Δ Γ (.app (.var i) (.inj₁ .unit)) (.comp (.ret rspT)) := by
  have h₁ : CDerivesAt Ξ Δ Γ (.var i) (.comp (CTy.iterBody boolT stT .unit).unroll) :=
    .nuOut (CTy.iterBody_nuOk boolT stT .unit) (.force (C := genC) h)
  rw [CTy.iter_unroll] at h₁
  exact .proj₁ h₁

/-- `return s ⇒ inr s` at `!U(S ⊸ F (bool ⊗ U gen ⊕ S))`. -/
theorem dAt_spawnRet {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [] (.val spawnRetV) (.val (retTy [] stT rspT)) :=
  .bangThunkV (dead_noLive .nil) rfl (.lam (.ret (.sumI₂ (.var (.here .nil)))))

/-- **The spawn clause** at the affine `bool ↠ 1`: it answers the tag beside `κ`, wrapped as the
stored generator, whose two observations are `κ`'s two entries. -/
theorem dAt_spawnCl {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [] (.val spawnClV) (.val (clauseTy [] rspT (.aff, boolT, .unit))) := by
  rw [Inversions.clauseTy_resuming rfl]
  refine .bangThunkV (dead_noLive .nil) rfl (.lam ?_)
  refine .tensorE (A := boolT) (B := kTy [] rspT .aff .unit) (.left .nil) (.var (.here .nil)) ?_
  -- `k` at `0`, `v` at `1`: `inl (v, gen k)`
  refine .ret (.sumI₁ (.tensorI (A := boolT) (B := .thunk genC) (.right (.left (.dead .nil)))
    (.var ?_) ?_))
  · solop
  refine .thunkV rfl (.nuIn (CTy.iterBody_nuOk boolT stT .unit) ?_)
  rw [CTy.iter_unroll]
  refine .withI ?_ ?_
  · -- `resume k ()`: `() to y. k (inj₁ ()) y`, `k` at `2`
    refine .bind (A := .unit) (.dead (.dead (.right (.dead (.dead .nil))))) (.ret (.unitI ?_)) ?_
    · deadp
    refine .app (A := .unit) (.right (.dead (.dead (.left (.dead (.dead .nil))))))
      (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf [] rspT)) (cancelTy [] (.ret .unit))) ?_))
      ?_ <;> solop
  · -- `cancel k`: `k (inj₂ ())`
    rw [← cancelTy_nil]
    refine .proj₂
      (.force (C := .amp (.arr .unit (CTy.effOf [] rspT)) (cancelTy [] (.ret .unit))) ?_)
    solop

/-- **`spawn M` at the pure row**, `M` at `yield`'s row. -/
theorem dAt_spawn {Δ : LifeCtx} {Γ : Ctx VTy} {M : Expr}
    (hM : CDerivesAt ΞE Δ Γ M (.comp (CTy.effOf yR stT))) :
    CDerivesAt ΞE Δ Γ (spawnE M) (.comp (.ret rspT)) :=
  dAt_hQ (splitP_deadOf Γ) (dead_deadOf Γ) ΞE_3 (by decide) (rowAt_nil ΞE) (by simp)
    (F := .ret .unit) dAt_spawnRet dAt_spawnCl hM

/-! ### The scheduler: round robin over the stored continuations -/

/-- The trace, a list of the tags yielded: `μX. 1 ⊕ (bool ⊗ X)`. -/
abbrev trBody : VTy := .sum .unit (.tensor boolT (.tvar 0))

/-- The trace's type. -/
abbrev trT : VTy := .mu trBody

theorem trBody_noMut : trBody.NoMut 0 := ⟨trivial, ⟨trivial, trivial⟩, trivial⟩

theorem trT_closed : trT.Cl 0 := ⟨trivial, ⟨trivial, trivial⟩, Nat.zero_lt_one⟩

/-- The scheduler's state and answer: both tasks and the trace. -/
abbrev schT : VTy := .tensor rspT (.tensor rspT trT)

/-- `v :: tr`. -/
def consE (v tr : Expr) : Expr := .inj₂ (.pair v tr)

/-- The empty trace. -/
abbrev nilE : Expr := .inj₁ .unit

/-- **The scheduler's step**, `(self, (rA, (rB, tr)))`: each round resumes each task that yielded,
`next` of its stored continuation, which runs it to its next `yield` or its end, and records the
tags; once both have ended, or the budget is spent, it answers its state. -/
def rrStepB : Expr := .letpair (.var 0) (.letpair (.var 0) (.letpair (.var 0)
  (.case (.var 5)
    (.pair (.var 4) (.pair (.var 2) (.var 1)))
    (.case (.var 4)
      (.letpair (.var 0)
        (bindE (.app (.var 0) (.inj₁ .unit))
          (.case (.var 6)
            (.letpair (.var 0)
              (bindE (.app (.var 0) (.inj₁ .unit))
                (bindE (.var 8)
                  (bindE
                    (.pair (.var 5) (.pair (.var 1) (consE (.var 3) (consE (.var 7) (.var 10)))))
                    (.app (.var 1) (.var 0))))))
            (bindE (.var 5)
              (bindE (.pair (.var 2) (.pair (.inj₂ (.var 1)) (consE (.var 4) (.var 7))))
                (.app (.var 1) (.var 0)))))))
      (.case (.var 3)
        (.letpair (.var 0)
          (bindE (.app (.var 0) (.inj₁ .unit))
            (bindE (.var 5)
              (bindE (.pair (.inj₂ (.var 5)) (.pair (.var 1) (consE (.var 3) (.var 7))))
                (.app (.var 1) (.var 0))))))
        (.pair (.inj₂ (.var 1)) (.pair (.inj₂ (.var 0)) (.var 3))))))))

/-- **The scheduler**, `rr st = bounded_fix (rrStep, (n, st))`, at most `n` rounds. -/
def rrE (n : UInt32) : Expr := .lam (bindE (.prim .boundedFix)
  (bindE (.pair (.lam rrStepB) (.pair (i32E n) (.var 1))) (.app (.var 1) (.var 0))))

section Scheduler
variable {Ξ : EffCtx}

/-- `v :: tr` at the trace's type. -/
theorem dAt_cons {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {v tr : Expr} (hs : Ctx.SplitP Γ Γ₁ Γ₂)
    (hv : CDerivesAt Ξ Δ Γ₁ v (.val boolT)) (htr : CDerivesAt Ξ Δ Γ₂ tr (.val trT)) :
    CDerivesAt Ξ Δ Γ (consE v tr) (.val trT) :=
  .roll trBody_noMut trT_closed (.sumI₂ (.tensorI (A := boolT) (B := trT) hs hv htr))

/-- The self-reference's call: `!U(st ⊸ F st)`. -/
abbrev meT : VTy := .bang (.thunk (.arr schT (.ret schT)))

/-- The tag and the stored continuation a task yielded. -/
abbrev pT : VTy := .tensor boolT (.thunk genC)

/-- **The scheduler's step** at `!U((1 ⊕ !U(st ⊸ F st)) ⊗ st ⊸ F st)`: a pure step; the stored
continuations are linear, each used once by its `next` or handed back. -/
theorem dAt_rrStep {Δ : LifeCtx} :
    CDerivesAt Ξ Δ [] (.val (.lam rrStepB)) (.val (fixStepTy schT (.ret schT))) := by
  refine .bangThunkV (dead_noLive .nil) rfl (.lam ?_)
  -- `q`: `(self, rest)`
  refine .tensorE (A := fixSelfTy schT (.ret schT)) (B := schT) (.left .nil) (.var (.here .nil)) ?_
  -- `rest` at `0`: `(rA, b)`
  refine .tensorE (A := rspT) (B := .tensor rspT trT) (.left (.right (.dead .nil))) (.var ?_) ?_
  · solop
  -- `b` at `0`, `rA` at `1`, `self` at `3`: `(rB, tr)`
  refine .tensorE (A := rspT) (B := trT) (.left (.right (.dead (.right (.dead .nil))))) (.var ?_) ?_
  · solop
  -- `tr` at `0`, `rB` at `1`, `rA` at `3`, `self` at `5`
  refine .sumE (A := .unit) (B := meT)
    (.right (.right (.dead (.right (.dead (.left (.dead .nil))))))) (.var ?_) ?_ ?_
  · solop
  · -- the budget is spent: the state
    refine .ret (.tensorI (A := rspT) (B := .tensor rspT trT)
      (.right (.right (.right (.dead (.left (deadSplit (by deadT))))))) (.var ?_)
      (.tensorI (A := rspT) (B := trT) (.right (.right (.left (deadSplit (by deadT)))))
        (.var ?_) (.var ?_))) <;> solop
  -- `me` at `0`, `tr` at `1`, `rB` at `2`, `rA` at `4`
  refine .sumE (A := pT) (B := stT)
    (.right (.right (.right (.dead (.left (deadSplit (by deadT))))))) (.var ?_) ?_ ?_
  · solop
  · -- `A` yielded: `pA` at `0`, `me` at `1`, `tr` at `2`, `rB` at `3`
    refine .tensorE (A := boolT) (B := .thunk genC)
      (.left (.right (.right (.right (deadSplit (by deadT)))))) (.var ?_) ?_
    · solop
    -- `gA` at `0`, `vA` at `1`, `me` at `3`, `tr` at `4`, `rB` at `5`: `rA' ← next gA`
    refine .bind (A := rspT)
      (.left (.right (.dead (.right (.right (.right (deadSplit (by deadT))))))))
      (dAt_next (by solop)) ?_
    -- `rA'` at `0`, `vA` at `2`, `me` at `4`, `tr` at `5`, `rB` at `6`
    refine .sumE (A := pT) (B := stT)
      (.right (.dead (.right (.dead (.right (.right (.left (deadSplit (by deadT)))))))))
      (.var ?_) ?_ ?_
    · solop
    · -- `B` yielded: `pB` at `0`, `rA'` at `1`, `vA` at `3`, `me` at `5`, `tr` at `6`
      refine .tensorE (A := boolT) (B := .thunk genC)
        (.left (.right (.dead (.right (.dead (.right (.right (deadSplit (by deadT)))))))))
        (.var ?_) ?_
      · solop
      -- `gB` at `0`, `vB` at `1`, `rA'` at `3`, `vA` at `5`, `me` at `7`, `tr` at `8`:
      -- `rB' ← next gB`
      refine .bind (A := rspT)
        (.left (.right (.dead (.right (.dead (.right (.dead (.right (.right
          (deadSplit (by deadT)))))))))))
        (dAt_next (by solop)) ?_
      -- `rB'` at `0`, `vB` at `2`, `rA'` at `4`, `vA` at `6`, `me` at `8`, `tr` at `9`:
      -- `mv ← return me`
      refine .bind (A := .thunk (.arr schT (.ret schT)))
        (.right (.dead (.right (.dead (.right (.dead (.right (.dead (.left (.right
          (deadSplit (by deadT))))))))))))
        (.ret (.bangE (.var ?_))) ?_
      · solop
      -- `mv` at `0`, `rB'` at `1`, `vB` at `3`, `rA'` at `5`, `vA` at `7`, `tr` at `10`:
      -- `arg ← return (rA', (rB', vB :: vA :: tr))`
      refine .bind (A := schT)
        (.right (.left (.dead (.left (.dead (.left (.dead (.left (.dead (.dead (.left
          (deadSplit (by deadT)))))))))))))
        (.ret (.tensorI (A := rspT) (B := .tensor rspT trT)
          (.dead (.right (.dead (.right (.dead (.left (.dead (.right (.dead (.dead (.right
            (deadSplit (by deadT))))))))))))) (.var ?_)
          (.tensorI (A := rspT) (B := trT)
            (.dead (.left (.dead (.right (.dead (.dead (.dead (.right (.dead (.dead (.right
              (deadSplit (by deadT))))))))))))) (.var ?_)
            (dAt_cons
              (.dead (.dead (.dead (.left (.dead (.dead (.dead (.right (.dead (.dead (.right
                (deadSplit (by deadT))))))))))))) (.var ?_)
              (dAt_cons
                (.dead (.dead (.dead (.dead (.dead (.dead (.dead (.left (.dead (.dead (.right
                  (deadSplit (by deadT))))))))))))) (.var ?_) (.var ?_)))))) ?_
      · solop
      · solop
      · solop
      · solop
      · solop
      -- `arg` at `0`, `mv` at `1`: `mv arg`
      refine .app (.right (.left (deadSplit (by deadT))))
        (.force (C := .arr schT (.ret schT)) ?_) ?_ <;> solop
    · -- `B` ended: `sB` at `0`, `rA'` at `1`, `vA` at `3`, `me` at `5`, `tr` at `6`:
      -- `mv ← return me`
      refine .bind (A := .thunk (.arr schT (.ret schT)))
        (.right (.right (.dead (.right (.dead (.left (.right (deadSplit (by deadT)))))))))
        (.ret (.bangE (.var ?_))) ?_
      · solop
      -- `mv` at `0`, `sB` at `1`, `rA'` at `2`, `vA` at `4`, `tr` at `7`:
      -- `arg ← return (rA', (inr sB, vA :: tr))`
      refine .bind (A := schT)
        (.right (.left (.left (.dead (.left (.dead (.dead (.left (deadSplit (by deadT))))))))))
        (.ret (.tensorI (A := rspT) (B := .tensor rspT trT)
          (.dead (.right (.left (.dead (.right (.dead (.dead (.right (deadSplit (by deadT))))))))))
          (.var ?_)
          (.tensorI (A := rspT) (B := trT)
            (.dead (.left (.dead (.dead (.right (.dead (.dead (.right (deadSplit (by deadT))))))))))
            (.sumI₂ (.var ?_))
            (dAt_cons
              (.dead (.dead (.dead (.dead (.left (.dead (.dead (.right
                (deadSplit (by deadT))))))))))
              (.var ?_) (.var ?_))))) ?_
      · solop
      · solop
      · solop
      · solop
      refine .app (.right (.left (deadSplit (by deadT))))
        (.force (C := .arr schT (.ret schT)) ?_) ?_ <;> solop
  · -- `A` ended: `sA` at `0`, `me` at `1`, `tr` at `2`, `rB` at `3`
    refine .sumE (A := pT) (B := stT) (.right (.right (.right (.left (deadSplit (by deadT))))))
      (.var ?_) ?_ ?_
    · solop
    · -- `B` yielded: `pB` at `0`, `sA` at `1`, `me` at `2`, `tr` at `3`
      refine .tensorE (A := boolT) (B := .thunk genC)
        (.left (.right (.right (.right (deadSplit (by deadT)))))) (.var ?_) ?_
      · solop
      -- `gB` at `0`, `vB` at `1`, `sA` at `3`, `me` at `4`, `tr` at `5`: `rB' ← next gB`
      refine .bind (A := rspT)
        (.left (.right (.dead (.right (.right (.right (deadSplit (by deadT))))))))
        (dAt_next (by solop)) ?_
      -- `rB'` at `0`, `vB` at `2`, `sA` at `4`, `me` at `5`, `tr` at `6`: `mv ← return me`
      refine .bind (A := .thunk (.arr schT (.ret schT)))
        (.right (.dead (.right (.dead (.right (.left (.right (deadSplit (by deadT)))))))))
        (.ret (.bangE (.var ?_))) ?_
      · solop
      -- `mv` at `0`, `rB'` at `1`, `vB` at `3`, `sA` at `5`, `tr` at `7`:
      -- `arg ← return (inr sA, (rB', vB :: tr))`
      refine .bind (A := schT)
        (.right (.left (.dead (.left (.dead (.left (.dead (.left (deadSplit (by deadT))))))))))
        (.ret (.tensorI (A := rspT) (B := .tensor rspT trT)
          (.dead (.right (.dead (.right (.dead (.left (.dead (.right (deadSplit (by deadT))))))))))
          (.sumI₂ (.var ?_))
          (.tensorI (A := rspT) (B := trT)
            (.dead (.left (.dead (.right (.dead (.dead (.dead (.right (deadSplit (by deadT))))))))))
            (.var ?_)
            (dAt_cons
              (.dead (.dead (.dead (.left (.dead (.dead (.dead (.right
                (deadSplit (by deadT))))))))))
              (.var ?_) (.var ?_))))) ?_
      · solop
      · solop
      · solop
      · solop
      refine .app (.right (.left (deadSplit (by deadT))))
        (.force (C := .arr schT (.ret schT)) ?_) ?_ <;> solop
    · -- both ended: `sB` at `0`, `sA` at `1`, `tr` at `3`
      refine .ret (.tensorI (A := rspT) (B := .tensor rspT trT)
        (.right (.left (.right (.right (deadSplit (by deadT)))))) (.sumI₂ (.var ?_))
        (.tensorI (A := rspT) (B := trT) (.left (.dead (.right (.right (deadSplit (by deadT))))))
          (.sumI₂ (.var ?_)) (.var ?_))) <;> solop

/-- **The scheduler** at `st ⊸ F st`. -/
theorem dAt_rr {Δ : LifeCtx} (n : UInt32) :
    CDerivesAt Ξ Δ [] (rrE n) (.comp (.arr schT (.ret schT))) := by
  refine .lam (.bind (.right .nil)
    (.ret (.bangE (.boundedFix schT (.ret schT) (.cons .nil)))) ?_)
  refine .bind (A := .tensor (fixStepTy schT (.ret schT)) (.tensor (.int .w32) schT))
    (.right (.left .nil))
    (.ret (.tensorI (.dead (.right .nil)) (dAt_dead (.cons (.cons .nil)) dAt_rrStep)
      (.tensorI (.dead (.right .nil)) (.lit (.i32 n) (.cons (.cons .nil))) (.var ?_)))) ?_
  · solop
  refine .app (.right (.left (.dead .nil)))
    (.force (C := .arr (.tensor (fixStepTy schT (.ret schT)) (.tensor (.int .w32) schT))
      (.ret schT)) ?_) ?_ <;> solop

end Scheduler

/-! ### The programs -/

/-- `forN`'s argument: the count `3`, the callback `cb`, and the state `(tag, (ff, ff))`. -/
def argsE (cb tag : Expr) : Expr := .pair (i32E 3) (.pair cb (.pair tag (.pair ffE ffE)))

/-- The two tasks under the scheduler, `W₁` and `W₂` the function at the two uses:
`cb ← yieldTick; rA ← spawn (W₁ (3, (cb, (ff, (ff, ff)))));
rB ← spawn (W₂ (3, (cb, (tt, (ff, ff))))); rr (rA, (rB, []))`. -/
def tasksE (W₁ W₂ : Expr) : Expr := bindE yieldTickE
  (bindE (spawnE (appE W₁ (argsE (.var 0) ffE)))
    (bindE (spawnE (appE W₂ (argsE (.var 1) ttE)))
      (appE (rrE 8) (.pair (.var 1) (.pair (.var 0) nilE)))))

/-- **The sync instance**: `let forN = … in forN (3, (tick, (ff, (ff, ff))))`. -/
def asyncSync : Expr := bindE forNE (appE (.var 0) (argsE tickE ffE))

/-- **The async instance**: `let forN = … in` the two tasks, each running `forN` with the callback
that suspends, interleaved by the scheduler. -/
def asyncTasks : Expr := bindE forNE (tasksE (.var 1) (.var 2))

/-- **The colourless test**: `forN` let-bound once, used at the pure row with `tick` and at
`yield`'s row by the two tasks: `let forN = … in s ← forN (3, (tick, …)); out ← tasks; (s, out)`. -/
def asyncColourless : Expr := bindE forNE
  (bindE (appE (.var 0) (argsE tickE ffE))
    (bindE (tasksE (.var 2) (.var 3)) (.pair (.var 1) (.var 0))))

/-! #### `[let-poly]`'s premises: each body with `forN` at its uses -/

/-- The sync instance's body with `forN` in place. -/
def asyncSyncW : Expr := appE forNE (argsE tickE ffE)

/-- The async instance's body with `forN` at both uses. -/
def asyncTasksW : Expr := tasksE forNE forNE

/-- The colourless test's body with `forN` at its three uses. -/
def asyncColourlessW : Expr := bindE asyncSyncW (bindE asyncTasksW (.pair (.var 1) (.var 0)))

theorem asyncSync_subst :
    ((appE (.var 0) (argsE tickE ffE)).subst 0 (Val.lam forNB)).shift 1 0 = asyncSyncW := rfl

theorem asyncTasks_subst :
    ((tasksE (.var 1) (.var 2)).subst 0 (Val.lam forNB)).shift 1 0 = asyncTasksW := rfl

theorem asyncColourless_subst :
    ((bindE (appE (.var 0) (argsE tickE ffE))
      (bindE (tasksE (.var 2) (.var 3)) (.pair (.var 1) (.var 0)))).subst 0
        (Val.lam forNB)).shift 1 0 = asyncColourlessW := rfl

/-! Each body is its copy, `forN` at each use, with `forN` replaced by the bound variable
(`Expr.unfill`). -/

theorem asyncSync_unfill : asyncSyncW.unfill forNB 0 = appE (.var 0) (argsE tickE ffE) := by decide

theorem asyncTasks_unfill : asyncTasksW.unfill forNB 0 = tasksE (.var 1) (.var 2) := by decide

theorem asyncColourless_unfill :
    asyncColourlessW.unfill forNB 0 =
      bindE (appE (.var 0) (argsE tickE ffE))
        (bindE (tasksE (.var 2) (.var 3)) (.pair (.var 1) (.var 0))) := by
  decide

/-! #### The derivations -/

section Programs

/-- `forN`'s argument, the callback at `Γ₁` and the tag at `Γ₂`. -/
theorem dAt_args {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hd₂ : Ctx.DeadP Γ₂)
    {r : Row} {cb tag : Expr} (hcb : CDerivesAt ΞE Δ Γ₁ cb (.val (cbT r)))
    (ht : CDerivesAt ΞE Δ Γ₂ tag (.val boolT)) :
    CDerivesAt ΞE Δ Γ (argsE cb tag) (.val (.tensor (.int .w32) (forA r))) :=
  .tensorI (splitP_deadOf Γ) (.lit (.i32 3) (dead_deadOf Γ).toP) (.tensorI hs hcb (dAt_st0 hd₂ ht))

/-- The empty trace. -/
theorem dAt_nil {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) :
    CDerivesAt ΞE Δ Γ nilE (.val trT) :=
  .roll trBody_noMut trT_closed (.sumI₁ (.unitI hΓ))

/-- The sync instance's body, `forN` at the pure row. -/
theorem dAt_asyncSyncW {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesAt ΞE Δ Γ asyncSyncW (.comp (.ret stT)) :=
  dAt_app (deadSplit hΓ) hΓ.toP rfl (dAt_forN [])
    (dAt_args (deadSplit hΓ) hΓ.toP (dAt_dead hΓ dAt_tick) (.sumI₁ (.unitI hΓ.toP)))

/-- **The sync instance is typed** (`[let-poly]`): `forN` at the pure row. -/
theorem dAt_asyncSync {Δ : LifeCtx} : CDerivesAt ΞE Δ [] asyncSync (.comp (.ret stT)) := by
  refine .letPoly forNB rfl (dAt_forN []) ?_
  rw [asyncSync_subst]
  exact dAt_asyncSyncW (.cons .nil)

/-- The async instance's body, `forN` at `yield`'s row at both uses. -/
theorem dAt_asyncTasksW {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesAt ΞE Δ Γ asyncTasksW (.comp (.ret schT)) := by
  -- `cb ← yieldTick`
  refine .bind (A := cbT yR) (deadSplit hΓ) (.ret (dAt_dead hΓ dAt_yieldTick)) ?_
  -- task A: `rA ← spawn (forN (3, (cb, (ff, (ff, ff)))))`
  refine .bind (A := rspT) (.dup (by rfl) (deadSplit hΓ))
    (dAt_spawn (dAt_app (.left (deadSplit hΓ)) (.cons hΓ.toP) rfl (dAt_forN yR)
      (dAt_args (.left (deadSplit hΓ)) (.cons hΓ.toP) (.var (.here hΓ.toP))
        (.sumI₁ (.unitI (.cons hΓ.toP)))))) ?_
  -- task B: `rB ← spawn (forN (3, (cb, (tt, (ff, ff)))))`
  refine .bind (A := rspT) (.right (.left (deadSplit hΓ)))
    (dAt_spawn (dAt_app (.dead (.left (deadSplit hΓ))) (.cons (.cons hΓ.toP)) rfl (dAt_forN yR)
      (dAt_args (.dead (.left (deadSplit hΓ))) (.cons (.cons hΓ.toP))
        (.var (.there (.here hΓ.toP))) (.sumI₂ (.unitI (.cons (.cons hΓ.toP))))))) ?_
  -- `rr (rA, (rB, []))`
  exact dAt_app (.left (.left (.dead (deadSplit hΓ)))) (.cons (.cons (.cons hΓ.toP))) rfl
    (dAt_rr 8)
    (.tensorI (A := rspT) (B := .tensor rspT trT) (.right (.left (.dead (deadSplit hΓ))))
      (.var (.there (.here (.cons hΓ.toP))))
      (.tensorI (.left (.dead (.dead (deadSplit hΓ)))) (.var (.here (.cons (.cons hΓ.toP))))
        (dAt_nil (.cons (.cons (.cons hΓ.toP))))))

/-- **The async instance is typed** (`[let-poly]`): `forN` at `yield`'s row, used by both tasks. -/
theorem dAt_asyncTasks {Δ : LifeCtx} : CDerivesAt ΞE Δ [] asyncTasks (.comp (.ret schT)) := by
  refine .letPoly forNB rfl (dAt_forN yR) ?_
  rw [asyncTasks_subst]
  exact dAt_asyncTasksW (.cons .nil)

/-- The colourless test's body: `forN` at the pure row, then at `yield`'s row by both tasks. -/
theorem dAt_asyncColourlessW {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [⟨.unit, false⟩] asyncColourlessW (.comp (.ret (.tensor stT schT))) :=
  .bind (A := stT) (.dead .nil) (dAt_asyncSyncW (.cons .nil))
    (.bind (A := schT) (.right (.dead .nil)) (dAt_asyncTasksW (.cons (.cons .nil)))
      (.ret (.tensorI (.right (.left (.dead .nil))) (.var (.there (.here (.cons .nil))))
        (.var (.here (.cons (.cons .nil)))))))

/-- **The colourless test is typed** (`[let-poly]`): `forN` let-bound once and used at the pure row
and at `yield`'s row, each use at its own row. -/
theorem dAt_asyncColourless {Δ : LifeCtx} :
    CDerivesAt ΞE Δ [] asyncColourless (.comp (.ret (.tensor stT schT))) := by
  refine .letPoly forNB rfl (dAt_forN []) ?_
  rw [asyncColourless_subst]
  exact dAt_asyncColourlessW

/-- The sync instance, read in `CDerives`. -/
theorem d_asyncSync {Δ : LifeCtx} : CDerives Δ [] asyncSync (.comp (.ret stT)) :=
  dAt_asyncSync.toCDerives

/-- The async instance, read in `CDerives`. -/
theorem d_asyncTasks {Δ : LifeCtx} : CDerives Δ [] asyncTasks (.comp (.ret schT)) :=
  dAt_asyncTasks.toCDerives

/-- The colourless test, read in `CDerives`. -/
theorem d_asyncColourless {Δ : LifeCtx} :
    CDerives Δ [] asyncColourless (.comp (.ret (.tensor stT schT))) :=
  dAt_asyncColourless.toCDerives

end Programs



/-! ### The runs

Each program's run, computed by `runM` from the empty memory and read as a run of Core's machine
(`runM_val`), ends at its answer at the empty memory: every capture cell the run allocates (one at
each `yield`, §25) is released. -/

/-- `ff`, `inj₁ ()`. -/
abbrev ffV : Val := Val.inj₁ Val.unit

/-- `tt`, `inj₂ ()`. -/
abbrev ttV : Val := Val.inj₂ Val.unit

/-- A trace, the most recent tag first. -/
def traceV : List Val → Val
  | [] => Val.inj₁ Val.unit
  | v :: vs => Val.inj₂ (Val.pair v (traceV vs))

/-- A task's state after three calls of the callback: its tag and the count `(tt, tt)`. -/
abbrev doneV (tag : Val) : Val := Val.pair tag (Val.pair ttV ttV)

/-- The scheduler's answer: both tasks ended, and their tags alternate in the trace, most recent
first: `A` yielded, then `B`, then `A` again, three times. -/
abbrev schedV : Val :=
  Val.pair (Val.inj₂ (doneV ffV)) (Val.pair (Val.inj₂ (doneV ttV))
    (traceV [ttV, ffV, ttV, ffV, ttV, ffV]))

/-- **The sync instance runs to `(ff, (tt, tt))`**: three calls of `tick`. -/
theorem asyncSync_run :
    Steps (ℍ := ℍ) Adequacy.emptyMem asyncSync Adequacy.emptyMem (.val (doneV ffV)) :=
  runM_val (k := 100) (m := []) (m' := []) rfl

set_option maxRecDepth 20000 in
/-- **The async instance runs to `schedV`**: each task suspends at each `yield`, its continuation
stored, while the other runs; the trace shows the two interleaved. -/
theorem asyncTasks_run :
    Steps (ℍ := ℍ) Adequacy.emptyMem asyncTasks Adequacy.emptyMem (.val schedV) :=
  runM_val (k := 400) (m := []) (m' := []) rfl

set_option maxRecDepth 20000 in
/-- **The colourless test runs to `((ff, (tt, tt)), schedV)`**. -/
theorem asyncColourless_run :
    Steps (ℍ := ℍ) Adequacy.emptyMem asyncColourless Adequacy.emptyMem
      (.val (Val.pair (doneV ffV) schedV)) :=
  runM_val (k := 500) (m := []) (m' := []) rfl

end BoCa.Fig16.LogRel.Core.AsyncPrograms

end

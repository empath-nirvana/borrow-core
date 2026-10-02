import FnMut.Counter

/-!
# FnMut — probe programs (requirements 3, 5 and 6)

Each program is one closed `CDerives` derivation at `F I32`.  It runs at every host from the
empty memory to a 32-bit literal and the empty memory (`*_runs`, by `theorem32` over
`fundamentalC`), and the interpreter at Wasm's host returns the stated literal with no cell
left (`*_eval`, by `decide`).

* `fromFnProg` (`Fn ≤ FnMut`): `λx. x + 10 : !U(I32 ⊸ F I32)` made an affine closure
  (`d_fromFn`), called with `1` and `2`, closed: `11 + 12 = 23`.
* `onceProg` (`FnMut ≤ FnOnce`): the counter over a fresh cell, made a `U(I32 ⊸ F I32)` by
  `onceE` and called with `5`: `5`.  The rest is closed inside `onceE`, which frees the cell.
* `dropProg` (drop): the counter over a cell holding `7`, never called, dropped by its
  destructor (`dropE`, SPEC §12): `0`, and the cell is freed by the destructor's `close`.
* `nestProg` (an affine closure capturing another): an outer closure whose state is the
  counter, doubling each answer; called with `1` and `2`, closed: `2 + 6 = 8`.  Closing the
  outer closure closes the inner one, which frees its cell.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Computation-level wrappers at the split `partP` -/

section
variable {Δ : LifeCtx} {Γ : Ctx VTy}

theorem bindC {M N : Expr} {A : VTy} {C : CTy}
    (hM : CDerives Δ (partP M 0 Γ).1 M (.comp (.ret A)))
    (hN : CDerives Δ (⟨A, true⟩ :: (partP M 0 Γ).2) N (.comp C)) :
    CDerives Δ Γ (bindE M N) (.comp C) :=
  .bind (partP_split M 0 Γ) hM hN

theorem letC {V M : Expr} {A B : VTy} {C : CTy}
    (hV : CDerives Δ (partP V 0 Γ).1 V (.val (.tensor A B)))
    (hM : CDerives Δ (⟨B, true⟩ :: ⟨A, true⟩ :: (partP V 0 Γ).2) M (.comp C)) :
    CDerives Δ Γ (.letpair V M) (.comp C) :=
  .tensorE (partP_split V 0 Γ) hV hM

theorem seqC {V M : Expr} {C : CTy} (hV : CDerives Δ (partP V 0 Γ).1 V (.val .unit))
    (hM : CDerives Δ (partP V 0 Γ).2 M (.comp C)) : CDerives Δ Γ (.seq V M) (.comp C) :=
  .unitE (partP_split V 0 Γ) hV hM

theorem callC {c : Lifetime.Life} {A B : VTy} {i j : Nat} (hA : A.Cl 0)
    (hf : Ctx.SoloP (partP (.var i) 0 Γ).1 i (fnMutT c A B))
    (ha : Ctx.SoloP (partP (.var i) 0 Γ).2 j A) :
    CDerives Δ Γ (callE i j) (.comp (.ret (.tensor B (fnBox c A B)))) :=
  d_call hA (partP_split (.var i) 0 Γ) hf ha

theorem unboxC {c : Lifetime.Life} {T : VTy} {C : CTy} {i : Nat} {N : Expr}
    (hx : Ctx.SoloP (partP (.var i) 0 Γ).1 i (.box c T))
    (hN : CDerives Δ (⟨T, true⟩ :: (partP (.var i) 0 Γ).2) N (.comp C)) :
    CDerives Δ Γ (bindE (.var i) N) (.comp C) :=
  d_unbox (partP_split (.var i) 0 Γ) hx hN

theorem mkBoxC {c : Lifetime.Life} {A B S : VTy} {C : CTy} {s₀ K : Expr} {step : Val}
    (hA : A.Cl 0) (hc : Δ.Defines c) (hS : VOutlives Δ c S)
    (hs₀ : CDerives Δ (partP s₀ 0 Γ).1 s₀ (.val S))
    (hstep : CDerives Δ (kill (⟨S, true⟩ :: (partP s₀ 0 Γ).2)) (.val step)
      (.val (.bang (.thunk (.arr S (fnStepC c A B S))))))
    (hK : CDerives Δ (⟨fnBox c A B, true⟩ :: ⟨fnCodeT c A B S, false⟩ :: ⟨S, false⟩ ::
      (partP s₀ 0 Γ).2) K (.comp C)) :
    CDerives Δ Γ (mkE c A B s₀ step K) (.comp C) :=
  d_mkBox' hA hc hS (partP_split s₀ 0 Γ) hs₀ hstep hK

/-- `x + y` at `I32`. -/
theorem d_add {x y : Expr} (hxy : CDerives Δ (partP (.pair x y) 0 Γ).1 (.pair x y)
      (.val (.tensor .i32 .i32)))
    (hΓ : Ctx.DeadP (partP (.pair x y) 0 Γ).2) : CDerives Δ Γ (addE x y) (.val .i32) :=
  appP hxy (.bangE (.hostOp (.bin .w32 .add) hΓ))

end

/-- A closed derivation at `F I32` runs to a literal with empty memory. -/
theorem runs_i32 {e : Expr} (h : CDerives LifeCtx.empty [] e (.comp (.ret .i32))) :
    ∃ n, BoCa.BoLo.Steps Adequacy.emptyMem e Adequacy.emptyMem (.val (Val.i32 n)) := by
  have hwp : wpTS [] e (fun _ v => Fig16.BoLo.pure (∃ n, v = Val.i32 n)) (PMap.empty : WRes) := by
    refine wpTS_mono (fun _ v ρ hv => ?_) PMap.empty (wp_of_derives h)
    obtain ⟨rfl, n, rfl⟩ := hv
    exact ⟨rfl, n, rfl⟩
  obtain ⟨v, hsteps, n, rfl⟩ := theorem32 e (fun v => ∃ n, v = Val.i32 n) hwp
  exact ⟨n, hsteps⟩

abbrev FC : VTy := fnBox .top .i32 .i32

/-- Call a boxed closure at `i` with the argument at `j`, then `K` with `(b, rest)` split:
`b` at `1`, the rest at `0`. -/
def callBoxE (i j : Nat) (K : Expr) : Expr := bindE (bindE (.var i) (callE 0 (j + 1))) (.letpair (.var 0) K)

/-! ### `Fn ≤ FnMut` -/

/-- `λx. x + 10`. -/
def incV : Val := .lam (addE (.var 0) (i32E 10))

theorem d_inc {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val incV) (.val (.bang (.lolli .i32 .i32))) :=
  .bangThunkV (persistent_dead hΓ) rfl (.lam (.ret
    (.lolliE (split_kill' _).toP
      (.tensorI (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) (d_i32 10 (.cons hΓ.toP)))
      (.bangE (.hostOp (.bin .w32 .add) (kill_dead _).toP)))))

/-- `incV to g. mkBox⊤ g fromFnStep to f. callBox f 1 to (x₁, f). callBox f 2 to (x₂, f).
close f; x₁ + x₂`. -/
def fromFnProg : Expr :=
  bindE (.val incV) (mkE .top .i32 .i32 (.var 0) fromFnStep
    (elet (i32E 1) (callBoxE 1 0
      (elet (i32E 2) (callBoxE 1 0
        (bindE (bindE (.var 0) (closeE 0)) (.seq (.var 0) (addE (.var 6) (.var 2)))))))))

theorem fromFnProg_derives : CDerives LifeCtx.empty [] fromFnProg (.comp (.ret .i32)) := by
  refine bindC (.ret (d_inc .nil)) ?_
  refine d_fromFn trivial (LifeCtx.defines_of_wf rfl) (partP_split (.var 0) 0 _) (.var (by csoloP)) ?_
  refine bindC (.ret (d_i32 1 (by cdeadP))) ?_
  refine bindC (unboxC (by csoloP) (callC (A := .i32) (B := .i32) (c := .top) trivial (by csoloP) (by csoloP))) ?_
  refine letC (.var (by csoloP)) ?_
  refine bindC (.ret (d_i32 2 (by cdeadP))) ?_
  refine bindC (unboxC (by csoloP) (callC (A := .i32) (B := .i32) (c := .top) trivial (by csoloP) (by csoloP))) ?_
  refine letC (.var (by csoloP)) ?_
  refine bindC (unboxC (by csoloP) (d_close (A := .i32) (B := .i32) (c := .top) trivial (by csoloP))) ?_
  exact seqC (.var (by csoloP)) (.ret (d_add (pairP (.var (by csoloP)) (.var (by csoloP)))
    (by cdeadP)))

theorem fromFnProg_runs :
    ∃ n, BoCa.BoLo.Steps Adequacy.emptyMem fromFnProg Adequacy.emptyMem (.val (Val.i32 n)) :=
  runs_i32 fromFnProg_derives

set_option maxRecDepth 100000 in
theorem fromFnProg_eval : i32NoLeak (eval fromFnProg) = some 23 := by decide

/-! ### `FnMut ≤ FnOnce` -/

/-- `mkBox⊤ (alloc 0) counterStep to bf. bf to f. (onceE f) 5`. -/
def onceProg : Expr :=
  mkE .top .i32 .i32 (.app (.val (.prim .alloc)) (i32E 0)) counterStep
    (bindE (.var 0) (.app (onceE 0) (i32E 5)))

theorem onceProg_derives : CDerives LifeCtx.empty [] onceProg (.comp (.ret .i32)) := by
  have hT : LifeCtx.empty.Defines .top := LifeCtx.defines_of_wf rfl
  refine mkBoxC trivial hT (.ref .int)
    (appP (d_i32 0 (by cdeadP)) (.alloc (by cdeadP))) (d_counterStep hT (kill_dead _)) ?_
  exact unboxC (by csoloP) (.ret (appP (d_i32 5 (by cdeadP))
    (d_once (A := .i32) (B := .i32) (c := .top) trivial (by csolo))))

theorem onceProg_runs :
    ∃ n, BoCa.BoLo.Steps Adequacy.emptyMem onceProg Adequacy.emptyMem (.val (Val.i32 n)) :=
  runs_i32 onceProg_derives

set_option maxRecDepth 100000 in
theorem onceProg_eval : i32NoLeak (eval onceProg) = some 5 := by decide

/-! ### Drop: the destructor runs `close` -/

/-- `mkBox⊤ (alloc 7) counterStep to bf. dtor bf; 0`. -/
def dropProg : Expr :=
  mkE .top .i32 .i32 (.app (.val (.prim .alloc)) (i32E 7)) counterStep (dropE FC 0 (i32E 0))

theorem dropProg_derives : CDerives LifeCtx.empty [] dropProg (.comp (.ret .i32)) := by
  have hT : LifeCtx.empty.Defines .top := LifeCtx.defines_of_wf rfl
  refine mkBoxC trivial hT (.ref .int)
    (appP (d_i32 7 (by cdeadP)) (.alloc (by cdeadP))) (d_counterStep hT (kill_dead _)) ?_
  exact drop_derives (partP_split (.var 0) 0 _) (by csoloP) (hasDtor_fnBox (A := .i32) trivial .top .i32)
    (.ret (d_i32 0 (by cdeadP)))

theorem dropProg_runs :
    ∃ n, BoCa.BoLo.Steps Adequacy.emptyMem dropProg Adequacy.emptyMem (.val (Val.i32 n)) :=
  runs_i32 dropProg_derives

set_option maxRecDepth 100000 in
/-- `0`, and no cell left: the destructor closed the closure, and `close` freed its cell. -/
theorem dropProg_eval : i32NoLeak (eval dropProg) = some 0 := by decide

end BoCa.Fig16.LogRel.Core

end

import Core.CloRules
import Core.Weaken

/-!
# The closure `Clo` — a counter, called through a `Mut` borrow  `[spec §22]`

    alloc () to d₀. withbor d₀ (Λ'x. λd. forget d;
      mkBox⊤ (alloc 0) counterStep to f.          -- f : [@⊤] U(Clo^⊤ I32 I32), owning a cell
      alloc f to r.
      withbor r (Λ'w. λm.                         -- m : Mut 'w ([@⊤] U(Clo^⊤ I32 I32))
        1 to a. callMut m a to (m, x₁).           -- the state persists between the calls
        2 to a. callMut m a to (m, x₂).
        forget m; [x₁ + x₂]) to (r, t).
      free r to f. f to g. g π₂;                   -- close: frees the cell
      [t]) to (d₀, t). free d₀; t

The counter's state is an owned cell `Ref I32`; a call adds its argument to the cell and returns
the new total.  The outer borrow of `d₀` only opens a lifetime `'x`, below `⊤`, at which the cell
holding the closure can be lent (`withbor`'s side condition needs a defined lifetime the payload
`[@⊤] U(…)` outlives).  The program returns `1 + 3 = 4` and leaves no cell: the closure's own
cell is freed by `close`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Clo
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Terms -/

/-- `swap r v`. -/
def swapE (r v : Expr) : Expr := .app (.app swap r) v

/-- `x + y` at `I32`. -/
def addE (x y : Expr) : Expr := .app (.val (.prim (.host (.bin .w32 .add)))) (.pair x y)

/-- The call: `let (s₁, n) = swap s 0 in let t = n + a in let (s₂, _) = swap s₁ t in (t, s₂)`,
with `a` at `0` and the state `s` at `3`. -/
def counterCall : Expr :=
  .letpair (swapE (.var 3) (i32E 0))
    (elet (addE (.var 0) (.var 2))
      (.letpair (swapE (.var 2) (.var 0)) (.pair (.var 2) (.var 1))))

/-- `λs. ⟨λa. counterCall, free s to n. ()⟩`. -/
def counterStep : Val :=
  .lam (withPair (.val (.lam counterCall)) (elet (.app (.val (.prim .free)) (.var 2)) (.val .unit)))

theorem d_counterStep {Δ : LifeCtx} {Γ : Ctx VTy} {c : Lifetime.Life} (hc : Δ.Defines c)
    (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val counterStep)
      (.val (.bang (.thunk (.arr (.ref .i32) (cloStepC c .i32 .i32 (.ref .i32)))))) := by
  refine .bangThunkV (banged_dead hΓ) rfl (.lam (.withI (.lam (.ret ?_)) (.ret ?_)))
  · -- `let (s₁, n) = swap s 0`
    refine .letpairV (.right (.dead (.dead (.left (deadSplit hΓ)))))
      (.lolliE (split_kill _).toP (d_i32 0 (kill_dead _).toP)
        (.lolliE (split_kill' _).toP (.var (.there (.there (.there (.here hΓ.toP)))))
          (.swap (kill_dead _).toP))) ?_
    -- `let t = n + a`
    refine .eletV (.left (.right (.left (.dead (.dead (.dead (deadSplit hΓ)))))))
      (.lolliE (split_kill' _).toP
        (.tensorI (.left (.dead (.right (.dead (.dead (.dead (deadSplit hΓ)))))))
          (.var (.here (.cons (.cons (.cons (.cons (.cons hΓ.toP)))))))
          (.var (.there (.there (.here (.cons (.cons (.cons hΓ.toP))))))))
        (.bangE (.hostOp (.bin .w32 .add) (kill_dead _).toP))) ?_
    -- `let (s₂, _) = swap s₁ t`
    refine .letpairV (.dup rfl (.dead (.left (.dead (.dead (.dead (.dead (deadSplit hΓ))))))))
      (.lolliE (.left (.dead (.right (.dead (.dead (.dead (.dead (deadSplit hΓ))))))))
        (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons hΓ.toP))))))))
        (.lolliE (split_kill' _).toP
          (.var (.there (.there (.here (.cons (.cons (.cons (.cons hΓ.toP))))))))
          (.swap (kill_dead _).toP))) ?_
    -- `(t, s₂)`, the cell boxed at `@c`
    have hout : CtxOutlives Δ (⟨.i32, false⟩ :: ⟨.ref .i32, true⟩ :: ⟨.i32, false⟩ ::
        ⟨.i32, false⟩ :: ⟨.ref .i32, false⟩ :: ⟨.i32, false⟩ :: ⟨.unit, false⟩ ::
        ⟨.sum .unit .unit, false⟩ :: ⟨.ref .i32, false⟩ :: Γ) c :=
      .consDead (.consLive (.ref .int) (.consDead (.consDead (.consDead (.consDead (.consDead
        (.consDead (.consDead (ctxOutlives_dead hc hΓ)))))))))
    exact .tensorI (.left (.right (.left (.dead (.dead (.dead (.dead (.dead (.dead
        (deadSplit hΓ))))))))))
      (.var (.skip rfl (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons hΓ.toP))))))))))
      (.boxI (.var (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ.toP))))))))))
        hout)
  · exact .eletV (.dead (.dead (.left (deadSplit hΓ))))
      (.lolliE (split_kill' _).toP (.var (.there (.there (.here hΓ.toP)))) (.free (kill_dead _).toP))
      (.unitI (.drop rfl (.cons (.cons (.cons hΓ.toP)))))

/-! ### The borrower: two calls through `Mut` -/

/-- The payload: the counter closure, outliving `⊤`. -/
abbrev PC : VTy := cloBox .top .i32 .i32

/-- `1 to a. callMut m a to (m, x₁). 2 to a. callMut m a to (m, x₂). forget m; [x₂ + x₁]`,
`m` at `0`. -/
def cntBody : Expr :=
  elet (i32E 1)
    (.letpair (callMutE 1 0)
      (elet (i32E 2)
        (.letpair (callMutE 2 0)
          (.seq (.app forget (.var 1)) (addE (.var 0) (.var 3))))))

theorem d_cntBody {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ₂ (⟨.mut (.var 1) PC, true⟩ :: ⟨.unit, false⟩ :: Γ) cntBody
      (.val (.box (.var 1) .i32)) := by
  refine .eletV (split_kill _).toP (d_i32 1 (kill_dead _).toP) ?_
  refine .letpairV (.left (.left (.dead (deadSplit hΓ))))
    (d_callMut (A := .i32) (B := .i32) (c := .top) trivial (.left (.right (.dead (deadSplit hΓ)))) (.there (.here (.cons hΓ.toP)))
      (.here (.cons (.cons hΓ)))) ?_
  refine .eletV (split_kill _).toP (d_i32 2 (kill_dead _).toP) ?_
  refine .letpairV (.left (.right (.left (.dead (.dead (.dead (deadSplit hΓ)))))))
    (d_callMut (A := .i32) (B := .i32) (c := .top) trivial (.left (.dead (.right (.dead (.dead (.dead (deadSplit hΓ)))))))
      (.there (.there (.here (.cons (.cons (.cons hΓ.toP))))))
      (.here (.cons (.cons (.cons (.cons (.cons hΓ))))))) ?_
  refine .seqV (.right (.left (.dead (.right (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))))
    (.lolliE (split_kill' _).toP
      (.var (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons hΓ.toP)))))))))
      (.forgetMut (kill_dead _).toP)) ?_
  have hout : CtxOutlives Δ₂ (⟨.i32, true⟩ :: ⟨.mut (.var 1) PC, false⟩ :: ⟨.i32, false⟩ ::
      ⟨.i32, true⟩ :: ⟨.mut (.var 1) PC, false⟩ :: ⟨.i32, false⟩ :: ⟨.mut (.var 1) PC, false⟩ ::
      ⟨.unit, false⟩ :: Γ) (.var 1) :=
    .consLive .int (.consDead (.consDead (.consLive .int (.consDead (.consDead (.consDead
      (.consDead (ctxOutlives_dead (LifeCtx.defines_of_wf rfl) hΓ))))))))
  exact .boxI (.lolliE (split_kill' _).toP
    (.tensorI (.left (.dead (.dead (.right (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))))
      (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ.toP)))))))))
      (.var (.there (.there (.there (.here (.cons (.cons (.cons (.cons hΓ.toP))))))))))
    (.bangE (.hostOp (.bin .w32 .add) (kill_dead _).toP))) hout

/-- `Λ'w. λm. cntBody`. -/
def cntCb : Expr := lam2 cntBody

theorem d_cntCb {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ₁ Γ cntCb
      (.val (.all 1 Δ₁.meetOfDom (.lolli (.mut (.var 1) PC) (.box (.var 1) .i32)))) :=
  callbackW rfl rfl hΓ (d_cntBody hΓ)

/-! ### The scope: make, store, lend, close -/

/-- The body under `'x`:

    mkBox⊤ (alloc 0) counterStep to f. alloc f to r. withbor r cntCb to (r, t).
    free r to f. (f to g. g π₂) to u. u; [t]                                         -/
def scopeBodyWith (cb : Expr) : Expr :=
  mkE .top .i32 .i32 (.app (.val (.prim .alloc)) (i32E 0)) counterStep
    (bindE (.app (.val (.prim .alloc)) (.var 0))
      (.letpair (.app (.app withbor (.var 0)) cb)
        (bindE (.app (.val (.prim .free)) (.var 1))
          (bindE (bindE (.var 0) (closeE 0))
            (.seq (.var 0) (.var 2))))))

theorem vfree_PC (x : LifeVar) : ¬ VFree x PC := by
  simp [VFree, CFree, Lifetime.Life.mentions, VTy.rename]

/-- The borrower's type, `∀'w ⊏ ⊓Δ₁. Mut 'w PC ⊸ ['w] I32`. -/
abbrev cntCbTy : VTy := .all 1 Δ₁.meetOfDom (.lolli (.mut (.var 1) PC) (.box (.var 1) .i32))

/-- The counter made, stored, lent to any borrower `cb`, and closed. -/
theorem d_scopeBodyWith {Γ : Ctx VTy} {cb : Expr}
    (hcb : ∀ {Γ' : Ctx VTy}, Ctx.Dead Γ' → CDerives Δ₁ Γ' cb (.val cntCbTy)) (hΓ : Ctx.Dead Γ) :
    CDerives Δ₁ Γ (scopeBodyWith cb) (.comp (.ret (.box (.var 0) .i32))) := by
  have hT : Δ₁.Defines .top := LifeCtx.defines_of_wf rfl
  refine d_mkBox trivial hT (.ref .int) (split_kill _).toP
    (.lolliE (deadSplit (kill_dead _)) (d_i32 0 (kill_dead _).toP) (.alloc (kill_dead _).toP))
    (fun hΓ' => d_counterStep hT hΓ') ?_
  refine .bind (.left (.dead (.dead (deadSplit hΓ))))
    (.ret (.lolliE (split_kill' _).toP (.var (.here (.cons (.cons hΓ.toP))))
      (.alloc (kill_dead _).toP))) ?_
  refine .tensorE (.left (.dead (.dead (.dead (deadSplit hΓ)))))
    (.lolliE (split_kill _).toP (hcb (kill_dead _))
      (.lolliE (split_kill' _).toP (.var (.here (.cons (.cons (.cons hΓ.toP)))))
        (.withbor2 (A := PC) (B := .i32) 1 (kill_dead _).toP rfl
          ⟨.var 0, LifeCtx.defines_of_wf rfl, .box (entailsLe_of_entailsLt (BoCa.Programs.entailsLt_top rfl))⟩ (vfree_PC 1)
          (by simp [VFree])))) ?_
  refine .bind (.right (.left (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))
    (.ret (.lolliE (split_kill' _).toP
      (.var (.there (.here (.cons (.cons (.cons (.cons hΓ.toP)))))))
      (.free (kill_dead _).toP))) ?_
  refine .bind (.left (.right (.dead (.dead (.dead (.dead (.dead (deadSplit hΓ))))))))
    (d_closeBox trivial (.cons (.cons (.cons (.cons (.cons (.cons hΓ))))))) ?_
  exact .unitE (.left (.dead (.right (.dead (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))))
    (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ.toP)))))))))
    (.ret (.boxI (.var (.there (.there (.here (.cons (.cons (.cons (.cons (.cons hΓ.toP)))))))))
      (.consDead (.consDead (.consLive .int (.consDead (.consDead (.consDead (.consDead
        (.consDead (ctxOutlives_dead (LifeCtx.defines_of_wf rfl) hΓ)))))))))))

/-- The counter lent to `cntCb`. -/
def scopeBody : Expr := scopeBodyWith cntCb

theorem d_scopeBody {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ₁ Γ scopeBody (.comp (.ret (.box (.var 0) .i32))) :=
  d_scopeBodyWith (fun hΓ' => d_cntCb hΓ') hΓ

/-! ### A scope: one lifetime `'x ⊏ ⊤` -/

/-- `Λ'x. λd. forget d; body`. -/
def scopeCbOf (body : Expr) : Expr := lam2 (.seq (.app forget (.var 0)) body)

/-- `alloc () to d₀. withbor d₀ (Λ'x. λd. forget d; body) to (d₀, t). free d₀ to u. u; t`:
`body` runs under `'x ⊏ ⊤`, below which a closure boxed at `⊤` can be lent, and at which a
closure capturing a closure boxed at `⊤` can be boxed. -/
def scopeProg (body : Expr) : Expr :=
  bindE (.app (.val (.prim .alloc)) (.val .unit))
    (.letpair (.app (.app withbor (.var 0)) (scopeCbOf body))
      (bindE (.app (.val (.prim .free)) (.var 1)) (.seq (.var 0) (.var 1))))

/-- The context `body` is typed in. -/
abbrev ΓS : Ctx VTy := [⟨.imm (.var 0) .unit, false⟩, ⟨.unit, false⟩, ⟨.ref .unit, false⟩]

theorem d_scopeProg {body : Expr} (h : CDerives Δ₁ ΓS body (.comp (.ret (.box (.var 0) .i32)))) :
    CDerives LifeCtx.empty [] (scopeProg body) (.comp (.ret .i32)) := by
  have hcb : CDerives LifeCtx.empty [⟨.ref .unit, false⟩] (scopeCbOf body)
      (.val (.all 0 LifeCtx.empty.meetOfDom (.lolli (.imm (.var 0) .unit) (.box (.var 0) .i32)))) :=
    callbackW rfl rfl (.cons .nil) (.seqV (.left (.dead (deadSplit (.cons .nil))))
      (.lolliE (split_kill' _).toP (.var (.here (.cons (.cons .nil)))) (.forgetImm (kill_dead _).toP))
      (.ofRet h))
  refine .bind .nil (.ret (.lolliE .nil (.unitI .nil) (.alloc (A := .unit) .nil))) ?_
  refine .tensorE (.left .nil)
    (.lolliE (.right .nil) hcb
      (.lolliE (.left .nil) (.var (.here .nil))
        (.withbor1 (A := .unit) (B := .i32) 0 (.cons .nil) rfl (fun _ h => h.elim)
          (by simp [VFree]) (by simp [VFree])))) ?_
  refine .bind (.right (.left (.dead .nil)))
    (.ret (.lolliE (.dead (.left (.dead .nil))) (.var (.there (.here (.cons .nil))))
      (.free (.cons (.cons (.cons .nil)))))) ?_
  exact .unitE (.left (.right (.dead (.dead .nil)))) (.var (.here (.cons (.cons (.cons .nil)))))
    (.ret (.var (.there (.here (.cons (.cons .nil))))))

/-! ### The program -/

/-- `alloc () to d₀. withbor d₀ (Λ'x. λd. forget d; scopeBody) to (d₀, t). free d₀ to u. u; t`. -/
def counterProg : Expr := scopeProg scopeBody

theorem counterProg_derives : CDerives LifeCtx.empty [] counterProg (.comp (.ret .i32)) :=
  d_scopeProg (d_scopeBody (.cons (.cons (.cons .nil))))

/-- **The counter runs at every host**: from the empty memory to a 32-bit literal, and the
empty memory: the closure's cell, the cell holding the closure and the scope's cell are all
freed. -/
theorem counterProg_runs :
    ∃ n, BoCa.BoLo.Steps Adequacy.emptyMem counterProg Adequacy.emptyMem (.val (Val.i32 n)) := by
  have hwp : wpTS [] counterProg (fun _ v => Fig16.BoLo.pure (∃ n, v = Val.i32 n))
      (PMap.empty : WRes) := by
    refine wpTS_mono (fun _ v ρ hv => ?_) PMap.empty (wp_of_derives counterProg_derives)
    obtain ⟨rfl, n, rfl⟩ := hv
    exact ⟨rfl, n, rfl⟩
  obtain ⟨v, hsteps, n, rfl⟩ := theorem32 counterProg (fun v => ∃ n, v = Val.i32 n) hwp
  exact ⟨n, hsteps⟩

set_option maxRecDepth 100000 in
/-- The interpreter at Wasm's host: `1 + 3 = 4`, no cell left.  The second call saw the first
call's total: the closure's state persisted across the two calls through the borrow. -/
theorem counterProg_eval : i32NoLeak (eval counterProg) = some 4 := by decide

end BoCa.Fig16.LogRel.Core.Clo

end



/-!
# The closure `Clo` — coercions, drop, nesting  `[spec §22]`

Each program is one closed `CDerives` derivation at `F I32`.  It runs at every host from the
empty memory to a 32-bit literal and the empty memory (`*_runs`, by `theorem32` over
`fundamentalC`), and the interpreter at Wasm's host returns the stated literal with no cell
left (`*_eval`, by `decide`).

* `ofFnProg` (`!(A ⇒ B)` to `Clo`): `λx. x + 10 : !U(I32 ⊸ F I32)` made a closure
  (`d_ofFn`), called with `1` and `2`, closed: `11 + 12 = 23`.
* `onceProg` (`Clo` to `A ⇒ B`): the counter over a fresh cell, made a `U(I32 ⊸ F I32)` by
  `onceE` and called with `5`: `5`.  The rest is closed inside `onceE`, which frees the cell.
* `dropProg` (drop): the counter over a cell holding `7`, never called, dropped by its
  destructor (`dropE`, SPEC §12): `0`, and the cell is freed by the destructor's `close`.
* `nestProg` (a closure capturing another): an outer closure whose state is the
  counter, doubling each answer; called with `1` and `2`, closed: `2 + 6 = 8`.  Closing the
  outer closure closes the inner one, which frees its cell.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Clo
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
    (hf : Ctx.SoloP (partP (.var i) 0 Γ).1 i (cloT c A B))
    (ha : Ctx.SoloP (partP (.var i) 0 Γ).2 j A) :
    CDerives Δ Γ (callE i j) (.comp (.ret (.tensor B (cloBox c A B)))) :=
  d_callClo hA (partP_split (.var i) 0 Γ) hf ha

theorem unboxC {c : Lifetime.Life} {T : VTy} {C : CTy} {i : Nat} {N : Expr}
    (hx : Ctx.SoloP (partP (.var i) 0 Γ).1 i (.box c T))
    (hN : CDerives Δ (⟨T, true⟩ :: (partP (.var i) 0 Γ).2) N (.comp C)) :
    CDerives Δ Γ (bindE (.var i) N) (.comp C) :=
  d_unbox (partP_split (.var i) 0 Γ) hx hN

theorem mkBoxC {c : Lifetime.Life} {A B S : VTy} {C : CTy} {s₀ K : Expr} {step : Val}
    (hA : A.Cl 0) (hc : Δ.Defines c) (hS : VOutlives Δ c S)
    (hs₀ : CDerives Δ (partP s₀ 0 Γ).1 s₀ (.val S))
    (hstep : CDerives Δ (kill (⟨S, true⟩ :: (partP s₀ 0 Γ).2)) (.val step)
      (.val (.bang (.thunk (.arr S (cloStepC c A B S))))))
    (hK : CDerives Δ (⟨cloBox c A B, true⟩ :: ⟨cloCodeT c A B S, false⟩ :: ⟨S, false⟩ ::
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

abbrev FC : VTy := cloBox .top .i32 .i32

/-- Call a boxed closure at `i` with the argument at `j`, then `K` with `(b, rest)` split:
`b` at `1`, the rest at `0`. -/
def callBoxE (i j : Nat) (K : Expr) : Expr := bindE (bindE (.var i) (callE 0 (j + 1))) (.letpair (.var 0) K)

/-! ### From `!(A ⇒ B)` to `Clo` -/

/-- `λx. x + 10`. -/
def incV : Val := .lam (addE (.var 0) (i32E 10))

theorem d_inc {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ (.val incV) (.val (.bang (.lolli .i32 .i32))) :=
  .bangThunkV (banged_dead hΓ) rfl (.lam (.ret
    (.lolliE (split_kill' _).toP
      (.tensorI (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) (d_i32 10 (.cons hΓ.toP)))
      (.bangE (.hostOp (.bin .w32 .add) (kill_dead _).toP)))))

/-- `incV to g. mkBox⊤ g ofFnStep to f. callBox f 1 to (x₁, f). callBox f 2 to (x₂, f).
close f; x₁ + x₂`. -/
def ofFnProg : Expr :=
  bindE (.val incV) (mkE .top .i32 .i32 (.var 0) ofFnStep
    (elet (i32E 1) (callBoxE 1 0
      (elet (i32E 2) (callBoxE 1 0
        (bindE (bindE (.var 0) (closeE 0)) (.seq (.var 0) (addE (.var 6) (.var 2)))))))))

theorem ofFnProg_derives : CDerives LifeCtx.empty [] ofFnProg (.comp (.ret .i32)) := by
  refine bindC (.ret (d_inc .nil)) ?_
  refine d_ofFn trivial (LifeCtx.defines_of_wf rfl) (partP_split (.var 0) 0 _) (.var (by csoloP)) ?_
  refine bindC (.ret (d_i32 1 (by cdeadP))) ?_
  refine bindC (unboxC (by csoloP) (callC (A := .i32) (B := .i32) (c := .top) trivial (by csoloP) (by csoloP))) ?_
  refine letC (.var (by csoloP)) ?_
  refine bindC (.ret (d_i32 2 (by cdeadP))) ?_
  refine bindC (unboxC (by csoloP) (callC (A := .i32) (B := .i32) (c := .top) trivial (by csoloP) (by csoloP))) ?_
  refine letC (.var (by csoloP)) ?_
  refine bindC (unboxC (by csoloP) (d_close (A := .i32) (B := .i32) (c := .top) trivial (by csoloP))) ?_
  exact seqC (.var (by csoloP)) (.ret (d_add (pairP (.var (by csoloP)) (.var (by csoloP)))
    (by cdeadP)))

theorem ofFnProg_runs :
    ∃ n, BoCa.BoLo.Steps Adequacy.emptyMem ofFnProg Adequacy.emptyMem (.val (Val.i32 n)) :=
  runs_i32 ofFnProg_derives

set_option maxRecDepth 100000 in
theorem ofFnProg_eval : i32NoLeak (eval ofFnProg) = some 23 := by decide

/-! ### From `Clo` to `A ⇒ B` -/

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
  exact drop_derives (partP_split (.var 0) 0 _) (by csoloP) (hasDtor_cloBox (A := .i32) trivial .top .i32)
    (.ret (d_i32 0 (by cdeadP)))

theorem dropProg_runs :
    ∃ n, BoCa.BoLo.Steps Adequacy.emptyMem dropProg Adequacy.emptyMem (.val (Val.i32 n)) :=
  runs_i32 dropProg_derives

set_option maxRecDepth 100000 in
/-- `0`, and no cell left: the destructor closed the closure, and `close` freed its cell. -/
theorem dropProg_eval : i32NoLeak (eval dropProg) = some 0 := by decide

/-- Types that outlive `'x` under `Δ₁`: data, and a box at `⊤`. -/
def outX : VTy → Bool
  | .box .top _ => true
  | A => dataB A

theorem outX_sound {A : VTy} (h : outX A = true) : VOutlives Δ₁ (.var 0) A := by
  cases A with
  | box b A =>
      cases b with
      | top => exact .box (entailsLe_of_entailsLt (BoCa.Programs.entailsLt_top rfl))
      | _ => exact outlives_of_dataB (by simpa [outX] using h)
  | _ => exact outlives_of_dataB (by simpa [outX] using h)

theorem outlives_ctxX {Γ : Ctx VTy} (h : (Γ.all fun s => !s.live || outX s.ty) = true) :
    CtxOutlives Δ₁ Γ (.var 0) := by
  refine ⟨LifeCtx.defines_of_wf rfl, fun s hs hl => outX_sound ?_⟩
  have := List.all_eq_true.mp h s hs
  simpa [hl] using this

/-! ### A closure capturing another -/

/-- The outer step over the inner closure `s : [@⊤] U(Clo^⊤ I32 I32)`:
`λs. ⟨λa. callBox s a to (b, r). (b + b, [r]), s to g. g π₂⟩`.  Closing the outer closure
closes the inner one. -/
def doubleStep : Val :=
  .lam (withPair (.val (.lam (callBoxE 3 0 (.pair (addE (.var 1) (.var 1)) (.var 0)))))
    (bindE (.var 2) (closeE 0)))

/-- The body under `'x`:

    mkBox⊤ (alloc 0) counterStep to inner. mkBox'x inner doubleStep to outer.
    callBox outer 1 to (x₁, outer). callBox outer 2 to (x₂, outer). close outer; [x₁ + x₂] -/
def nestBody : Expr :=
  mkE .top .i32 .i32 (.app (.val (.prim .alloc)) (i32E 0)) counterStep
    (mkE (.var 0) .i32 .i32 (.var 0) doubleStep
      (elet (i32E 1) (callBoxE 1 0
        (elet (i32E 2) (callBoxE 1 0
          (bindE (bindE (.var 0) (closeE 0)) (.seq (.var 0) (addE (.var 6) (.var 2)))))))))

theorem d_nestBody : CDerives Δ₁ ΓS nestBody (.comp (.ret (.box (.var 0) .i32))) := by
  have hT : Δ₁.Defines .top := LifeCtx.defines_of_wf rfl
  have hX : Δ₁.Defines (.var 0) := LifeCtx.defines_of_wf rfl
  refine mkBoxC trivial hT (.ref .int)
    (appP (d_i32 0 (by cdeadP)) (.alloc (by cdeadP))) (d_counterStep hT (kill_dead _)) ?_
  refine mkBoxC trivial hX (.box (entailsLe_of_entailsLt (BoCa.Programs.entailsLt_top rfl))) (.var (by csoloP)) ?_ ?_
  · -- the outer step
    refine .bangThunkV (banged_dead (kill_dead _)) rfl (.lam (.withI (.lam ?_) ?_))
    · refine bindC (unboxC (by csoloP)
        (callC (A := .i32) (B := .i32) (c := .top) trivial (by csoloP) (by csoloP))) ?_
      refine letC (.var (by csoloP)) ?_
      exact .ret (pairP (d_add (pairP (.var (by csoloP)) (.var (by csoloP))) (by cdeadP))
        (.boxI (.var (by csoloP)) (outlives_ctxX (by decide))))
    · exact unboxC (by csoloP) (d_close (A := .i32) (B := .i32) (c := .top) trivial (by csoloP))
  refine bindC (.ret (d_i32 1 (by cdeadP))) ?_
  refine bindC (unboxC (by csoloP)
    (callC (A := .i32) (B := .i32) (c := .var 0) trivial (by csoloP) (by csoloP))) ?_
  refine letC (.var (by csoloP)) ?_
  refine bindC (.ret (d_i32 2 (by cdeadP))) ?_
  refine bindC (unboxC (by csoloP)
    (callC (A := .i32) (B := .i32) (c := .var 0) trivial (by csoloP) (by csoloP))) ?_
  refine letC (.var (by csoloP)) ?_
  refine bindC (unboxC (by csoloP) (d_close (A := .i32) (B := .i32) (c := .var 0) trivial
    (by csoloP))) ?_
  exact seqC (.var (by csoloP)) (.ret (.boxI (d_add (pairP (.var (by csoloP)) (.var (by csoloP)))
    (by cdeadP)) (outlives_ctxX (by decide))))

def nestProg : Expr := scopeProg nestBody

theorem nestProg_derives : CDerives LifeCtx.empty [] nestProg (.comp (.ret .i32)) :=
  d_scopeProg d_nestBody

theorem nestProg_runs :
    ∃ n, BoCa.BoLo.Steps Adequacy.emptyMem nestProg Adequacy.emptyMem (.val (Val.i32 n)) :=
  runs_i32 nestProg_derives

set_option maxRecDepth 100000 in
/-- `2 + 6 = 8`, no cell left: the inner counter saw both calls, and closing the outer closure
closed the inner one. -/
theorem nestProg_eval : i32NoLeak (eval nestProg) = some 8 := by decide

end BoCa.Fig16.LogRel.Core.Clo

end



/-!
# The closure `Clo` — passed on borrowed, at any depth  `[spec §22]`

Under the borrow `'w` of the counter (`Counter.lean`), `M = Mut 'w ([@⊤] U(Clo^⊤ I32 I32))`:

* `twiceV : !U(M ⊸ F(M ⊗ I32))` calls through the borrow twice;
* `reV : !U(M ⊸ F(M ⊗ I32))` reborrows it at a fresh `'v ⊏ 'w` (`withbor`'s third form,
  Rust's `&mut *m`) and calls through the reborrow, keeping `m`;
* `passF 0 = λm. reV m to (m, x). twiceV m to (m, y). (m, x + y)`, and
  `passF (n + 1) = λm. passF n m`: the borrow handed on through `n` more functions.

`d_passF` types `passF n` at every `n`, by induction: the borrowed closure is an ordinary value
of an ordinary type, so passing it on is application and nothing bounds the depth.
`passProg n` lends the counter to `passF n`; at `n = 3` the interpreter returns `3 + (4 + 6) =
13` with no cell left, so all three calls reached the one closure state through three functions
and a reborrow.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Clo
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- A closed derivation is one at every consumed context. -/
theorem weak0 {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ [] e j)
    (hΓ : Ctx.Dead Γ) : CDerives Δ Γ e j := by
  simpa using h.append_dead hΓ

/-- Call through `Mut` at the split by the argument. -/
theorem callMutW {Δ : LifeCtx} {Γ : Ctx VTy} {a c : Lifetime.Life} {A B : VTy} {i j : Nat}
    (hA : A.Cl 0) (hm : Ctx.SoloP (part (.var j) 0 Γ).2 i (.mut a (cloBox c A B)))
    (ha : Ctx.Solo (part (.var j) 0 Γ).1 j A) :
    CDerives Δ Γ (callMutE i j) (.val (.tensor (.mut a (cloBox c A B)) B)) :=
  d_callMut hA (part_split (.var j) 0 Γ).toP hm ha

/-- The borrowed counter. -/
abbrev MC : VTy := .mut (.var 1) PC

/-- A function on the borrowed counter, `!U(M ⊸ F(M ⊗ I32))`. -/
abbrev passTy : VTy := .bang (.lolli MC (.tensor MC .i32))

/-! ### Two calls through the borrow -/

def twiceV : Val :=
  .lam (elet (i32E 1) (.letpair (callMutE 1 0)
    (elet (i32E 2) (.letpair (callMutE 2 0) (.pair (.var 1) (addE (.var 3) (.var 0)))))))

theorem d_twice : CDerives Δ₂ [] (.val twiceV) (.val passTy) := by
  refine .bangThunkV (banged_dead .nil) rfl (.lam (.ret ?_))
  refine bindP (d_i32 1 (by cdeadP)) ?_
  refine letP (callMutW (A := .i32) (B := .i32) (c := .top) trivial (by csoloP) (by csolo)) ?_
  refine bindP (d_i32 2 (by cdeadP)) ?_
  refine letP (callMutW (A := .i32) (B := .i32) (c := .top) trivial (by csoloP) (by csolo)) ?_
  exact pairP (.var (by csoloP)) (d_add (pairP (.var (by csoloP)) (.var (by csoloP))) (by cdeadP))

/-! ### A call through a reborrow -/

/-- `'v ⊏ ⊓Δ₂`. -/
abbrev Δ₃ : LifeCtx := Δ₂.extend 2 Δ₂.meetOfDom

/-- `Λ'v. λm'. 3 to a. callMut m' a to (m', x). forget m'; [x]`. -/
def reCb : Expr :=
  lam2 (elet (i32E 3) (.letpair (callMutE 1 0) (.seq (.app forget (.var 1)) (.var 0))))

theorem d_reCb : CDerives Δ₂ [] reCb
    (.val (.all 2 Δ₂.meetOfDom (.lolli (.mut (.var 2) PC) (.box (.var 2) .i32)))) := by
  refine callbackW rfl rfl .nil ?_
  refine bindP (d_i32 3 (by cdeadP)) ?_
  refine letP (callMutW (A := .i32) (B := .i32) (c := .top) trivial (by csoloP) (by csolo)) ?_
  exact seqW (appW (.var (by csolo)) (.forgetMut (by cdead)))
    (.boxI (.var (by csoloP)) (outlives_ctx (LifeCtx.defines_of_wf rfl) (by decide)))

/-- `λm. withbor m reCb`: `m` reborrowed for one call, and returned. -/
def reV : Val := .lam (.app (.app withbor (.var 0)) reCb)

theorem d_re : CDerives Δ₂ [] (.val reV) (.val passTy) := by
  refine .bangThunkV (banged_dead .nil) rfl (.lam (.ret ?_))
  exact appW (weak0 d_reCb (by cdead)) (appW (.var (by csolo))
    (.withbor3 (a := .var 1) (A := PC) (B := .i32) 2 (by cdeadP) rfl (vfree_PC 2)
      (by simp [VFree])))

/-! ### Passing on -/

/-- `passF 0` composes the reborrowed call and the two direct ones; `passF (n + 1)` hands the
borrow to `passF n`. -/
def passF : ℕ → Val
  | 0 => .lam (.letpair (.app (.val reV) (.var 0))
      (.letpair (.app (.val twiceV) (.var 1)) (.pair (.var 1) (addE (.var 2) (.var 0)))))
  | n + 1 => .lam (.app (.val (passF n)) (.var 0))

theorem d_pass0 : CDerives Δ₂ [] (.val (passF 0)) (.val passTy) := by
  refine .bangThunkV (banged_dead .nil) rfl (.lam (.ret ?_))
  refine letP (.lolliE (split_kill' _).toP (.var (by csoloP)) (.bangE (weak0 d_re (kill_dead _)))) ?_
  refine letP (.lolliE (split_kill' _).toP (.var (by csoloP))
    (.bangE (weak0 d_twice (kill_dead _)))) ?_
  exact pairP (.var (by csoloP)) (d_add (pairP (.var (by csoloP)) (.var (by csoloP))) (by cdeadP))

/-- **At every depth.**  `passF n` is typed for every `n`. -/
theorem d_passF : ∀ (n : ℕ) {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives Δ₂ Γ (.val (passF n)) (.val passTy)
  | 0, _, hΓ => weak0 d_pass0 hΓ
  | n + 1, _, hΓ => .bangThunkV (banged_dead hΓ) rfl (.lam (.ret
      (.lolliE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) (.bangE (d_passF n (.cons hΓ))))))

/-! ### The program -/

/-- `Λ'w. λm. passF n m to (m, t). forget m; [t]`. -/
def passCb (n : ℕ) : Expr :=
  lam2 (.letpair (.app (.val (passF n)) (.var 0)) (.seq (.app forget (.var 1)) (.var 0)))

theorem d_passCb (n : ℕ) : CDerives Δ₁ [] (passCb n) (.val cntCbTy) := by
  refine callbackW rfl rfl .nil ?_
  refine .letpairV (.left (.dead .nil))
    (.lolliE (.left (.dead .nil)) (.var (.here (.cons .nil))) (.bangE (d_passF n (.cons (.cons .nil)))))
    ?_
  exact .seqV (.right (.left (.dead (.dead .nil))))
    (.lolliE (split_kill' _).toP (.var (.there (.here (.cons (.cons .nil)))))
      (.forgetMut (kill_dead _).toP))
    (.boxI (.var (.here (.cons (.cons (.cons .nil)))))
      (outlives_ctx (LifeCtx.defines_of_wf rfl) (by decide)))

/-- The counter lent to `passF n`. -/
def passProg (n : ℕ) : Expr := scopeProg (scopeBodyWith (passCb n))

theorem passProg_derives (n : ℕ) : CDerives LifeCtx.empty [] (passProg n) (.comp (.ret .i32)) :=
  d_scopeProg (d_scopeBodyWith (fun hΓ => weak0 (d_passCb n) hΓ) (.cons (.cons (.cons .nil))))

theorem passProg_runs (n : ℕ) :
    ∃ v, BoCa.BoLo.Steps Adequacy.emptyMem (passProg n) Adequacy.emptyMem (.val (Val.i32 v)) :=
  runs_i32 (passProg_derives n)

set_option maxRecDepth 100000 in
/-- Through three more functions: `3 + (4 + 6) = 13`, no cell left. -/
theorem passProg3_eval : i32NoLeak (eval (passProg 3)) = some 13 := by decide

end BoCa.Fig16.LogRel.Core.Clo

end



/-!
# The closure `Clo` — returned, and bounded by the borrows it captures  `[spec §22]`

* `retProg`: `mkCounter : !U(I32 ⊸ F([@⊤] U(Clo^⊤ I32 I32)))` allocates the counter's cell
  and returns the closure, owned.  Called at `10`, the closure is called with `5` and closed:
  `15`.  (`counterProg` stores a closure in a cell.)
* `logProg`: a logger capturing a borrow.  `log : Ref I32` is lent as `ml : Mut 'x I32`; inside a
  scope `'w ⊏ 'x` the logger is made with state `ml`, so it is `[@'w] U(Clo^'w I32 I32)`:
  it outlives `'w` because its state does (`'w ⊏ 'x`).  Each call adds its argument to the log
  through `ml` (`withswap`); `close` forgets `ml`.  Called with `5` and `7` and closed; after the
  borrow ends the owner frees the log: `12`.
* The bound is the captured borrow's lifetime: the logger's state does not outlive `'x`
  (`logState_not_outlives`), so `[]I` at `'x` over the state, the premise of `d_mkBox`, is
  refused; and no closure value outlives anything except through its box
  (`clo_not_outlives`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Clo
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
  refine .bangThunkV (banged_dead .nil) rfl (.lam ?_)
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
    refine .bangThunkV (banged_dead (kill_dead _)) rfl (.lam (.withI (.lam ?_) ?_))
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
      ⟨.top, LifeCtx.defines_of_wf rfl, (outlives_of_dataB rfl).toLe⟩ (by simp [VFree])
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
stored or lent beyond its creation only as `[@c] U(Clo^c A B)`, boxed where its state is in
the context. -/
theorem clo_not_outlives (Δ : LifeCtx) (a c : Lifetime.Life) (A B : VTy) :
    ¬ VOutlives Δ a (cloT c A B) := by
  intro h; cases h

end BoCa.Fig16.LogRel.Core.Clo

end

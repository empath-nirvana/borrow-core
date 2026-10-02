import FnMut.Rules

/-!
# FnMut — a counter, called through a `Mut` borrow (requirements 1 and 5)

    alloc () to d₀. withbor d₀ (Λ'x. λd. forget d;
      mkBox⊤ (alloc 0) counterStep to f.          -- f : [@⊤] U(FnMut^⊤ I32 I32), owning a cell
      alloc f to r.
      withbor r (Λ'w. λm.                         -- m : Mut 'w ([@⊤] U(FnMut^⊤ I32 I32))
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

namespace BoCa.Fig16.LogRel.Core
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
      (.val (.bang (.thunk (.arr (.ref .i32) (fnStepC c .i32 .i32 (.ref .i32)))))) := by
  refine .bangThunkV (persistent_dead hΓ) rfl (.lam (.withI (.lam (.ret ?_)) (.ret ?_)))
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
abbrev PC : VTy := fnBox .top .i32 .i32

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
          ⟨.var 0, LifeCtx.defines_of_wf rfl, .box (BoCa.Programs.entailsLt_top rfl)⟩ (vfree_PC 1)
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

end BoCa.Fig16.LogRel.Core

end

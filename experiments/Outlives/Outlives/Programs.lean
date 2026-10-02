import Outlives.Derives

/-!
# Outlives — two affine-closure programs with no scope, under the relaxed rules

`Core/AffPrograms.lean`'s `counterProg` and `nestProg` each open a scope (`scopeProg`: a cell
allocated and borrowed only to bring a lifetime `'x ⊏ ⊤` into `Δ`):

* `counterProg` lends the cell holding `[@⊤] U(Aff^⊤ I32 I32)` `mut`; `withbor`'s side condition
  asks for a defined lifetime the payload strictly outlives, and under `Δ = ∅` there is none, since
  `[@⊤] T ⊐ ⊤` would need `⊤ ⊏ ⊤`.
* `nestProg` boxes a closure whose state is `[@⊤] U(Aff^⊤ I32 I32)`; the outer closure is boxed at
  `'x`, again because `[@⊤] T ⊐ ⊤` fails.

Under `LDerives` both are typed at `Δ = ∅`, with no scope: `counterTop` lends the cell with the
side condition `[@⊤] U(…) ⊒ ⊤`, and `nestTop` boxes the outer closure at `⊤` through `[]I` at
`[@⊤] U(…) ⊐ ⊤` read with the box rule non-strict. Each runs by `runs_i32L` (adequacy at
`fundamentalL`) and, at Wasm's host, by the interpreter to the same answer as the scoped program
(`4` and `8`) with no cell left. The scope's own cell, allocated, borrowed and freed by
`scopeProg`, is gone.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Outlives
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core.Aff
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Context conditions at the box-relaxed judgment -/

section
variable {Δ : LifeCtx}

theorem ctxOutL_dead {Γ : Ctx VTy} {a : Lifetime.Life} (ha : Δ.Defines a) (hΓ : Ctx.Dead Γ) :
    CtxOutL Δ Γ a :=
  ⟨ha, dead_noLive (P := fun s => VOutL Δ a s.ty) hΓ⟩

theorem CtxOutL.consLive {Γ : Ctx VTy} {a : Lifetime.Life} {T : VTy} (hT : VOutL Δ a T)
    (h : CtxOutL Δ Γ a) : CtxOutL Δ (⟨T, true⟩ :: Γ) a := by
  refine ⟨h.1, fun s hs hl => ?_⟩
  cases hs with
  | head => exact hT
  | tail _ hs' => exact h.2 s hs' hl

/-- Types that outlive `⊤` at the box-relaxed judgment: data, and a box at `⊤`. -/
def outT : VTy → Bool
  | .box .top _ => true
  | A => dataB A

theorem outT_sound {A : VTy} (hT : Δ.Defines .top) (h : outT A = true) : VOutL Δ .top A := by
  cases A with
  | box b A =>
      cases b with
      | top => exact .box (entailsLe_refl hT)
      | _ => exact VOutL.of_vOutlives (outlives_of_dataB (by simpa [outT] using h))
  | _ => exact VOutL.of_vOutlives (outlives_of_dataB (by simpa [outT] using h))

theorem outlives_ctxT {Γ : Ctx VTy} (hT : Δ.Defines .top)
    (h : (Γ.all fun s => !s.live || outT s.ty) = true) : CtxOutL Δ Γ .top := by
  refine ⟨hT, fun s hs hl => outT_sound hT ?_⟩
  have := List.all_eq_true.mp h s hs
  simpa [hl] using this

/-! ### Wrappers at `LDerives` -/

variable {Γ : Ctx VTy}

theorem bindL {M N : Expr} {A : VTy} {C : CTy}
    (hM : LDerives Δ (partP M 0 Γ).1 M (.comp (.ret A)))
    (hN : LDerives Δ (⟨A, true⟩ :: (partP M 0 Γ).2) N (.comp C)) :
    LDerives Δ Γ (bindE M N) (.comp C) :=
  .bind (partP_split M 0 Γ) hM hN

theorem letL {V M : Expr} {A B : VTy} {C : CTy}
    (hV : LDerives Δ (partP V 0 Γ).1 V (.val (.tensor A B)))
    (hM : LDerives Δ (⟨B, true⟩ :: ⟨A, true⟩ :: (partP V 0 Γ).2) M (.comp C)) :
    LDerives Δ Γ (.letpair V M) (.comp C) :=
  .tensorE (partP_split V 0 Γ) hV hM

theorem pairPL {e₁ e₂ : Expr} {A B : VTy} (h₁ : LDerives Δ (partP e₁ 0 Γ).1 e₁ (.val A))
    (h₂ : LDerives Δ (partP e₁ 0 Γ).2 e₂ (.val B)) :
    LDerives Δ Γ (.pair e₁ e₂) (.val (.tensor A B)) :=
  .tensorI (partP_split e₁ 0 Γ) h₁ h₂

/-- `d_packBox` at the box-relaxed `[]I`. -/
theorem d_packBoxL {Γ : Ctx VTy} {c : Lifetime.Life} {A B S : VTy} (hA : A.Cl 0) (hΓ : Ctx.Dead Γ)
    (hc : Δ.Defines c) (hS : VOutL Δ c S) :
    LDerives Δ (⟨affCodeT c A B S, true⟩ :: ⟨S, true⟩ :: Γ) packE (.val (affBox c A B)) :=
  .boxI (.core (d_pack hA hΓ)) (.consLive .bang (.consLive hS (ctxOutL_dead hc hΓ)))

/-- `mkBoxC` at `LDerives`: the closure outlives `@c` when its state does, in the box-relaxed
sense. -/
theorem mkBoxL {c : Lifetime.Life} {A B S : VTy} {C : CTy} {s₀ K : Expr} {step : Val}
    (hA : A.Cl 0) (hc : Δ.Defines c) (hS : VOutL Δ c S)
    (hs₀ : LDerives Δ (partP s₀ 0 Γ).1 s₀ (.val S))
    (hstep : LDerives Δ (kill (⟨S, true⟩ :: (partP s₀ 0 Γ).2)) (.val step)
      (.val (.bang (.thunk (.arr S (affStepC c A B S))))))
    (hK : LDerives Δ (⟨affBox c A B, true⟩ :: ⟨affCodeT c A B S, false⟩ :: ⟨S, false⟩ ::
      (partP s₀ 0 Γ).2) K (.comp C)) :
    LDerives Δ Γ (mkE c A B s₀ step K) (.comp C) :=
  .bind (partP_split s₀ 0 Γ) (.ret hs₀)
    (.bind (split_kill _).toP
      (.ret (.lolliE (deadSplit (kill_dead _)) hstep (.core (.affUnfold hA B S (kill_dead _).toP))))
      (.bind (.left (.left (split_kill _).toP)) (.ret (d_packBoxL hA (kill_dead _) hc hS)) hK))

end

/-! ### The counter, lent `mut` with no scope -/

/-- `d_cntBody` with the borrow's lifetime the first variable: the borrower's body under
`'w ⊏ ⊤`. -/
theorem d_cntBody0 {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ₁ (⟨.mut (.var 0) PC, true⟩ :: ⟨.unit, false⟩ :: Γ) cntBody
      (.val (.box (.var 0) .i32)) := by
  refine .eletV (split_kill _).toP (d_i32 1 (kill_dead _).toP) ?_
  refine .letpairV (.left (.left (.dead (deadSplit hΓ))))
    (d_callMut (A := .i32) (B := .i32) (c := .top) trivial (.left (.right (.dead (deadSplit hΓ))))
      (.there (.here (.cons hΓ.toP))) (.here (.cons (.cons hΓ)))) ?_
  refine .eletV (split_kill _).toP (d_i32 2 (kill_dead _).toP) ?_
  refine .letpairV (.left (.right (.left (.dead (.dead (.dead (deadSplit hΓ)))))))
    (d_callMut (A := .i32) (B := .i32) (c := .top) trivial
      (.left (.dead (.right (.dead (.dead (.dead (deadSplit hΓ)))))))
      (.there (.there (.here (.cons (.cons (.cons hΓ.toP))))))
      (.here (.cons (.cons (.cons (.cons (.cons hΓ))))))) ?_
  refine .seqV (.right (.left (.dead (.right (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))))
    (.lolliE (split_kill' _).toP
      (.var (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons hΓ.toP)))))))))
      (.forgetMut (kill_dead _).toP)) ?_
  have hout : CtxOutlives Δ₁ (⟨.i32, true⟩ :: ⟨.mut (.var 0) PC, false⟩ :: ⟨.i32, false⟩ ::
      ⟨.i32, true⟩ :: ⟨.mut (.var 0) PC, false⟩ :: ⟨.i32, false⟩ :: ⟨.mut (.var 0) PC, false⟩ ::
      ⟨.unit, false⟩ :: Γ) (.var 0) :=
    .consLive .int (.consDead (.consDead (.consLive .int (.consDead (.consDead (.consDead
      (.consDead (ctxOutlives_dead (LifeCtx.defines_of_wf rfl) hΓ))))))))
  exact .boxI (.lolliE (split_kill' _).toP
    (.tensorI (.left (.dead (.dead (.right (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))))
      (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ.toP)))))))))
      (.var (.there (.there (.there (.here (.cons (.cons (.cons (.cons hΓ.toP))))))))))
    (.bangE (.hostOp (.bin .w32 .add) (kill_dead _).toP))) hout

/-- `Λ'w. λm. cntBody` at `∀'w ⊏ ⊤. Mut 'w PC ⊸ ['w] I32`. -/
theorem d_cntCb0 {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ cntCb
      (.val (.all 0 LifeCtx.empty.meetOfDom (.lolli (.mut (.var 0) PC) (.box (.var 0) .i32)))) :=
  callbackW rfl rfl hΓ (d_cntBody0 hΓ)

/-- `scopeBodyWith cntCb` as a whole program: the counter made, stored, lent to `cntCb`, and
closed, under `Δ = ∅`. -/
def counterTop : Expr := scopeBodyWith cntCb

theorem d_counterTopWith {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    LDerives LifeCtx.empty Γ counterTop (.comp (.ret .i32)) := by
  have hT : LifeCtx.empty.Defines .top := LifeCtx.defines_of_wf rfl
  refine .bind (split_kill _).toP
    (.ret (.core (.lolliE (deadSplit (kill_dead _)) (d_i32 0 (kill_dead _).toP)
      (.alloc (kill_dead _).toP)))) ?_
  refine .bind (split_kill _).toP
    (.ret (.core (.lolliE (deadSplit (kill_dead _)) (Aff.d_counterStep hT (kill_dead _))
      (.affUnfold (A := .i32) trivial .i32 (.ref .i32) (kill_dead _).toP)))) ?_
  refine .bind (.left (.left (split_kill _).toP))
    (.ret (d_packBoxL trivial (kill_dead _) hT (VOutL.of_vOutlives (.ref .int)))) ?_
  refine .bind (.left (.dead (.dead (deadSplit hΓ))))
    (.ret (.lolliE (split_kill' _).toP (.var (.here (.cons (.cons hΓ.toP))))
      (.alloc (kill_dead _).toP))) ?_
  refine .tensorE (.left (.dead (.dead (.dead (deadSplit hΓ)))))
    (.lolliE (split_kill _).toP (.core (d_cntCb0 (kill_dead _)))
      (.lolliE (split_kill' _).toP (.var (.here (.cons (.cons (.cons hΓ.toP)))))
        (.withbor2 (A := PC) (B := .i32) 0 (kill_dead _).toP rfl
          ⟨.top, hT, .box (entailsLe_refl hT)⟩ (vfree_PC 0) (by simp [VFree])))) ?_
  refine .bind (.right (.left (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))
    (.ret (.lolliE (split_kill' _).toP
      (.var (.there (.here (.cons (.cons (.cons (.cons hΓ.toP)))))))
      (.free (kill_dead _).toP))) ?_
  refine .bind (.left (.right (.dead (.dead (.dead (.dead (.dead (deadSplit hΓ))))))))
    (.core (d_closeBox trivial (.cons (.cons (.cons (.cons (.cons (.cons hΓ)))))))) ?_
  exact .unitE (.left (.dead (.right (.dead (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))))
    (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ.toP)))))))))
    (.ret (.var (.there (.there (.here (.cons (.cons (.cons (.cons (.cons hΓ.toP))))))))))

theorem counterTop_derives : LDerives LifeCtx.empty [] counterTop (.comp (.ret .i32)) :=
  d_counterTopWith .nil

/-- **The counter runs with no scope**, at every host, to a literal and the empty memory. -/
theorem counterTop_runs :
    ∃ n, BoCa.BoLo.Steps Adequacy.emptyMem counterTop Adequacy.emptyMem (.val (Val.i32 n)) :=
  runs_i32L counterTop_derives

set_option maxRecDepth 100000 in
/-- `1 + 3 = 4`, no cell left: `counterProg`'s answer without its scope. -/
theorem counterTop_eval : i32NoLeak (eval counterTop) = some 4 := by decide

/-! ### A closure capturing a closure, both bounded by `⊤` -/

/-- `nestBody` with the outer closure boxed at `⊤`:

    mkBox⊤ (alloc 0) counterStep to inner. mkBox⊤ inner doubleStep to outer.
    callBox outer 1 to (x₁, outer). callBox outer 2 to (x₂, outer). close outer; x₁ + x₂ -/
def nestTop : Expr :=
  mkE .top .i32 .i32 (.app (.val (.prim .alloc)) (i32E 0)) Aff.counterStep
    (mkE .top .i32 .i32 (.var 0) doubleStep
      (elet (i32E 1) (callBoxE 1 0
        (elet (i32E 2) (callBoxE 1 0
          (bindE (bindE (.var 0) (closeE 0)) (.seq (.var 0) (Aff.addE (.var 6) (.var 2)))))))))

theorem nestTop_derives : LDerives LifeCtx.empty [] nestTop (.comp (.ret .i32)) := by
  have hT : LifeCtx.empty.Defines .top := LifeCtx.defines_of_wf rfl
  refine mkBoxL trivial hT (VOutL.of_vOutlives (.ref .int))
    (.core (appP (d_i32 0 (by cdeadP)) (.alloc (by cdeadP)))) (.core (Aff.d_counterStep hT (kill_dead _))) ?_
  refine mkBoxL trivial hT (.box (entailsLe_refl hT)) (.var (by csoloP)) ?_ ?_
  · -- the outer step: the rest of the inner closure, `[@⊤] U(…)`, boxed at `⊤`
    refine .bangThunkV (persistent_dead (kill_dead _)) rfl (.lam (.withI (.lam ?_) ?_))
    · refine bindL (.core (unboxC (by csoloP)
        (callC (A := .i32) (B := .i32) (c := .top) trivial (by csoloP) (by csoloP)))) ?_
      refine letL (.var (by csoloP)) ?_
      exact .ret (pairPL (.core (Aff.d_add (pairP (.var (by csoloP)) (.var (by csoloP))) (by cdeadP)))
        (.boxI (.var (by csoloP)) (outlives_ctxT hT (by decide))))
    · exact .core (unboxC (by csoloP) (d_close (A := .i32) (B := .i32) (c := .top) trivial (by csoloP)))
  refine .core ?_
  refine bindC (.ret (d_i32 1 (by cdeadP))) ?_
  refine bindC (unboxC (by csoloP)
    (callC (A := .i32) (B := .i32) (c := .top) trivial (by csoloP) (by csoloP))) ?_
  refine letC (.var (by csoloP)) ?_
  refine bindC (.ret (d_i32 2 (by cdeadP))) ?_
  refine bindC (unboxC (by csoloP)
    (callC (A := .i32) (B := .i32) (c := .top) trivial (by csoloP) (by csoloP))) ?_
  refine letC (.var (by csoloP)) ?_
  refine bindC (unboxC (by csoloP) (d_close (A := .i32) (B := .i32) (c := .top) trivial
    (by csoloP))) ?_
  exact seqC (.var (by csoloP)) (.ret (Aff.d_add (pairP (.var (by csoloP)) (.var (by csoloP)))
    (by cdeadP)))

/-- **The nested closure runs with no scope.** -/
theorem nestTop_runs :
    ∃ n, BoCa.BoLo.Steps Adequacy.emptyMem nestTop Adequacy.emptyMem (.val (Val.i32 n)) :=
  runs_i32L nestTop_derives

set_option maxRecDepth 100000 in
/-- `2 + 6 = 8`, no cell left: `nestProg`'s answer without its scope. -/
theorem nestTop_eval : i32NoLeak (eval nestTop) = some 8 := by decide

end BoCa.Fig16.LogRel.Core.Outlives

end

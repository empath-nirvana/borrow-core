import Targets.I.Rejects
import Core.EffCancelTyped

/-!
# The interaction — D3's rejection at Core's kernel (SPEC §27)

`progT` (`Core/EffCancelTyped.lean`): handler `1` cancels the continuation of `perform 1`, whose
region holds a handler of `2` and a finaliser that raises `2`.  Its run ends at a raise of `2` no
handler catches (`progT_run`).  It is typed at a row holding `2` (`d_progT`), and at no row without
one (`not_der_progT`): decision D3.

The inversion reads the program from the outside in, each step by its rule and then the same-term
rules, which only grow rows (`JS.effSub`'s order, `JR.rowLe`):

* `[handle] 1` (`der_hndJ`): the clause tuple at `clausesTy Σ R E fs`, the body at
  `F_{1⟨fs 0⟩, Σ} A`, and the program's row above `Σ`;
* `[handle] 2` (`der_hndJ`) and `[then]` (`der_thenJ`): `perform 1`'s row finds `1`
  (`der_performJ`) and the finaliser's row finds `2` (`der_raiseJ`), so the `[then]`'s premise
  `F ⋈ {2} ≤ Σ(1).fin` puts `2` in the cancel row of `1` at the `[then]`, and `[sub]` up to the body
  of `[handle] 1` keeps it there: `2` is in `fs 0`;
* the clause (`lam_bang`, `der_letpairJ`, `der_app`, `der_lam`): `κ` is bound and its cancel branch
  applied, at `F_{fs 0 ⊕ Σ} 1`, read at the clause's row `Σ` by the same-term rules: `Σ` holds
  `2`.

`progNCrecT`: two finalisers that perform `4`, under a handler of `4` whose clause cancels.  The
second finaliser is a leftover of the cancel of the first one's continuation, so `⋈` puts `4` in
the cancel row of the `4` in the cancel row of `1` (`thenLe_findsRec`); `H₁`'s clause row then holds
such a `4`, and so does the clause row of the outer handler of `4`, its own outer row, which lacks
`4`: no derivation at all (`not_der_progNCrecT`).  Its run ends at a `perform 4` no handler catches
(`progNCrecT_run`, `progNCrecT_stuck`).  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Rej
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeCtx)
open BoCa.Fig16.LogRel.Core.CancelIntercept
open BoCa.BoLo (hndE)

/-! ### The same-term rules grow rows -/

/-- What a computation at `F_Σ Y` is read at through the same-term rules: a row above `Σ` over a
view of `Y`, or, with `Σ` below the empty row, a view of `Y`. -/
def RowCls (S : Row) (Y : VTy) : Jdg → Prop
  | .comp D => ∃ S' Y', D = CTy.effOf S' Y' ∧ RowLe S S' ∧ VView Y Y'
  | .val Y' => RowLe S [] ∧ VView Y Y'

theorem RowCls.step {S : Row} {Y : VTy} {j j' : Jdg} (hs : JS j j') (h : RowCls S Y j) :
    RowCls S Y j' := by
  cases hs with
  | val hv => exact ⟨h.1, h.2.tail hv⟩
  | ret A => exact ⟨[], A, rfl, h.1, h.2⟩
  | ofRet A =>
      obtain ⟨S', Y', he, hle, hY⟩ := h
      obtain ⟨rfl, rfl⟩ := Inst.effOf_inj (S := []) he
      exact ⟨hle, hY⟩
  | effSub S₀ S₁ A hle' =>
      obtain ⟨S', Y', he, hle, hY⟩ := h
      obtain ⟨rfl, rfl⟩ := Inst.effOf_inj he
      exact ⟨_, _, rfl, hle.trans hle', hY⟩
  | nuIn C hC =>
      obtain ⟨S', Y', he, -⟩ := h
      obtain ⟨C₁, C₂, hu⟩ := unroll_amp hC
      exact absurd (hu.symm.trans he) (Inst.effOf_ne_amp S' Y' C₁ C₂).symm
  | nuOut C hC =>
      obtain ⟨S', Y', he, -⟩ := h
      exact absurd he.symm (Inst.effOf_ne_nu S' Y' C)

theorem RowCls.reach {S : Row} {Y : VTy} {j j' : Jdg} (hr : JR j j') (h : RowCls S Y j) :
    RowCls S Y j' := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

/-- **The same-term rules grow rows**: a computation at `F_Σ Y` read at `F_Σ′ Y′` has `Σ ≤ Σ′`. -/
theorem JR.rowLe {S S' : Row} {Y Y' : VTy} (hr : JR (.comp (CTy.effOf S Y)) (.comp (CTy.effOf S' Y'))) :
    RowLe S S' := by
  obtain ⟨S₁, Y₁, he, hle, -⟩ := RowCls.reach hr (S := S) (Y := Y) ⟨S, Y, rfl, RowLe.refl S, .refl⟩
  obtain ⟨rfl, -⟩ := Inst.effOf_inj he
  exact hle

/-- An `&` is read at itself, or at a `ν` that unrolls to it. -/
theorem JR.amp {C₁ C₂ : CTy} {j : Jdg} (hr : JR (.comp (.amp C₁ C₂)) j) :
    j = .comp (.amp C₁ C₂) ∨ ∃ C, j = .comp (.nu C) ∧ C.unroll = .amp C₁ C₂ := by
  induction hr with
  | refl => exact .inl rfl
  | tail _ hs ih =>
      cases hs with
      | val _ => rcases ih with h | ⟨_, h, -⟩ <;> cases h
      | ret _ => rcases ih with h | ⟨_, h, -⟩ <;> cases h
      | ofRet A =>
          rcases ih with h | ⟨_, h, -⟩
          · cases h
          · cases h
      | effSub S S' A _ =>
          rcases ih with h | ⟨C, h, -⟩
          · exact absurd (Jdg.comp.inj h) (Inst.effOf_ne_amp S A C₁ C₂)
          · exact absurd (Jdg.comp.inj h) (Inst.effOf_ne_nu S A C)
      | nuIn C hC =>
          rcases ih with h | ⟨C', h, -⟩
          · exact .inr ⟨C, rfl, Jdg.comp.inj h⟩
          · obtain ⟨D₁, D₂, hu⟩ := unroll_amp hC
            rw [hu] at h
            cases h
      | nuOut C hC =>
          rcases ih with h | ⟨C', h, hC'⟩
          · cases h
          · cases h
            exact .inl (by rw [hC'])

/-- An `&` read at an `&` is that `&`. -/
theorem JR.amp_amp {C₁ C₂ D₁ D₂ : CTy} (hr : JR (.comp (.amp C₁ C₂)) (.comp (.amp D₁ D₂))) :
    D₁ = C₁ ∧ D₂ = C₂ := by
  rcases JR.amp hr with h | ⟨C, h, -⟩
  · cases h; exact ⟨rfl, rfl⟩
  · cases h

/-! ### Inversions at the judgement a rule concludes with -/

/-- `[handle]`'s premises, at its conclusion `j₀`. -/
def HndBase (Δ : LifeCtx) (Γ : Ctx VTy) (n : UInt32) (Q H M : Expr) (j₀ : Jdg) : Prop :=
  ∃ (Γ₁ Γ₂ : Ctx VTy) (S : Row) (E : List (Qual × VTy × VTy)) (fs : Nat → CTy) (A R : VTy),
    Ctx.SplitP Γ Γ₁ Γ₂ ∧ Q = (qualsVal (E.map Prod.fst)).1 ∧
    CDerives Δ Γ₁ H (.val (.tensor (retTy S A R) (clausesTy S R E fs))) ∧
    CDerives Δ Γ₂ M (.comp (CTy.effOf (Row.ofEff n E 0 fs ++ S) A)) ∧
    (∀ o ∈ S, o.n ≠ n) ∧ j₀ = .comp (CTy.effOf S R)

/-- **A handler term is `[handle]`'s, then the same-term rules.** -/
theorem der_hndJ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ (n : UInt32) (Q H M : Expr),
      e = .app (.app (.prim .hnd) (.pair (.prim (.lit (.i32 n))) (.pair Q H))) M →
      ∃ j₀, HndBase Δ Γ n Q H M j₀ ∧ JR j₀ j := by
  induction h with
  | effHandleV hs _ _ hc _ hnS _ he =>
      intro n Q H M he'
      simp only [hndExpr, Expr.val, Val.prim, Val.i32, Expr.app.injEq, Expr.pair.injEq] at he'
      obtain ⟨⟨-, hn, rfl, rfl⟩, rfl⟩ := he'
      simp only [Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at hn
      subst hn
      exact ⟨_, ⟨_, _, _, _, _, _, _, hs, rfl, hc, he, hnS, rfl⟩, .refl⟩
  | force => intro n Q H M he; rcases forceE_var he with h | h <;> simp at h
  | lolliE _ _ hf =>
      intro n Q H M he; simp only [Expr.app.injEq] at he; obtain ⟨rfl, -⟩ := he
      exact (not_der_app_prim hf _ _ rfl id (by decide) (by decide)).elim
  | app _ hM _ =>
      intro n Q H M he; simp only [Expr.app.injEq] at he; obtain ⟨rfl, -⟩ := he
      exact (not_der_app_prim hM _ _ rfl id (by decide) (by decide)).elim
  | allE hM _ | proj₁ hM | proj₂ hM =>
      intro n Q H M he; simp only [Expr.app.injEq] at he; obtain ⟨rfl, -⟩ := he
      exact (not_der_app_prim hM _ _ rfl id (by decide) (by decide)).elim
  | allEV hM _ =>
      intro n Q H M he; simp only [Expr.app.injEq] at he; obtain ⟨rfl, -⟩ := he
      exact (not_der_app_prim hM _ _ rfl id (by decide) (by decide)).elim
  | ret _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he; exact ⟨j₀, hb, hr.tail (JS.ret _)⟩
  | ofRet _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he; exact ⟨j₀, hb, hr.tail (JS.ofRet _)⟩
  | effSub hle _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he
      exact ⟨j₀, hb, hr.tail (JS.effSub _ _ _ hle)⟩
  | nuIn hC _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he; exact ⟨j₀, hb, hr.tail (JS.nuIn _ hC)⟩
  | nuOut hC _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he
      exact ⟨j₀, hb, hr.tail (JS.nuOut _ hC)⟩
  | bangE _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.bang _))⟩
  | boxI _ _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxI _ _))⟩
  | boxE _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxE _ _))⟩
  | immSub _ _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.immS _ _ _))⟩
  | mutSub _ _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.mutS _ _ _))⟩
  | roll _ _ _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.roll _))⟩
  | unroll _ ih =>
      intro n Q H M he; obtain ⟨j₀, hb, hr⟩ := ih n Q H M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.unroll _))⟩
  | _ => intro n Q H M he; cd_at he


/-- `[then]`'s premises, at its conclusion `j₀`. -/
def ThenBase (Δ : LifeCtx) (Γ : Ctx VTy) (D M : Expr) (j₀ : Jdg) : Prop :=
  ∃ (Γ₁ Γ₂ : Ctx VTy) (A B : VTy) (S SM SD : Row), Ctx.SplitP Γ Γ₁ Γ₂ ∧
    RowLe SM S ∧ RowLe SD S ∧
    (∀ n i o o', Row.find SM n i = some o → Row.find S n i = some o' →
      capB o.q o.B = true → ThenLe o.fin SD o'.fin) ∧
    CDerives Δ Γ₁ M (.comp (CTy.effOf SM A)) ∧
    CDerives Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (CTy.effOf SD .unit)) ∧
    j₀ = .comp (CTy.effOf S B)

/-- **A `M then x. N unwind D` is `[then]`'s, then the same-term rules.** -/
theorem der_thenJ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ N D M, e = thenE N D M → ∃ j₀, ThenBase Δ Γ D M j₀ ∧ JR j₀ j := by
  induction h with
  | effThen hs _ _ _ hMS hDS hfin _ hM _ hD _ _ _ =>
      intro N D M he; cases he
      exact ⟨_, ⟨_, _, _, _, _, _, _, hs, hMS, hDS, hfin, hM, hD, rfl⟩, .refl⟩
  | force => intro N D M he; rcases forceE_var he with h | h <;> simp [thenE] at h
  | lolliE _ _ hf =>
      intro N D M he; simp only [thenE, Expr.app.injEq] at he; obtain ⟨rfl, -⟩ := he
      exact (not_der_app_prim hf _ _ rfl id (by decide) (by decide)).elim
  | app _ hM _ =>
      intro N D M he; simp only [thenE, Expr.app.injEq] at he; obtain ⟨rfl, -⟩ := he
      exact (not_der_app_prim hM _ _ rfl id (by decide) (by decide)).elim
  | allE hM _ | proj₁ hM | proj₂ hM =>
      intro N D M he; simp only [thenE, Expr.app.injEq] at he; obtain ⟨rfl, -⟩ := he
      exact (not_der_app_prim hM _ _ rfl id (by decide) (by decide)).elim
  | allEV hM _ =>
      intro N D M he; simp only [thenE, Expr.app.injEq] at he; obtain ⟨rfl, -⟩ := he
      exact (not_der_app_prim hM _ _ rfl id (by decide) (by decide)).elim
  | ret _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he; exact ⟨j₀, hb, hr.tail (JS.ret _)⟩
  | ofRet _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he; exact ⟨j₀, hb, hr.tail (JS.ofRet _)⟩
  | effSub hle _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he
      exact ⟨j₀, hb, hr.tail (JS.effSub _ _ _ hle)⟩
  | nuIn hC _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he; exact ⟨j₀, hb, hr.tail (JS.nuIn _ hC)⟩
  | nuOut hC _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he
      exact ⟨j₀, hb, hr.tail (JS.nuOut _ hC)⟩
  | bangE _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.bang _))⟩
  | boxI _ _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxI _ _))⟩
  | boxE _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxE _ _))⟩
  | immSub _ _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.immS _ _ _))⟩
  | mutSub _ _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.mutS _ _ _))⟩
  | roll _ _ _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.roll _))⟩
  | unroll _ ih =>
      intro N D M he; obtain ⟨j₀, hb, hr⟩ := ih N D M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.unroll _))⟩
  | _ => intro N D M he; cd_terms

/-- `[perform]`'s premises, at its conclusion `j₀`. -/
def PerfBase (n i : UInt32) (j₀ : Jdg) : Prop :=
  ∃ (S : Row) (o : OpSig), Row.find S n i = some o ∧ o.abort = false ∧
    j₀ = .comp (CTy.effOf S o.B)

/-- **A `perform` is `[perform]`'s, then the same-term rules.** -/
theorem der_performJ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ n i V, e = BoCa.BoLo.performE (opArgE n i V) → ∃ j₀, PerfBase n i j₀ ∧ JR j₀ j := by
  induction h with
  | effPerform hf hna _ =>
      intro n i V he
      simp only [BoCa.BoLo.performE, opArgE, Expr.val, Val.prim, Val.i32, Expr.app.injEq,
        Expr.pair.injEq, Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at he
      obtain ⟨-, rfl, rfl, -⟩ := he
      exact ⟨_, ⟨_, _, hf, hna, rfl⟩, .refl⟩
  | force => intro n i V he; rcases forceE_var he with h | h <;> cd_at h
  | lolliE _ _ hf =>
      intro n i V he; simp only [BoCa.BoLo.performE, Expr.app.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (der_prim hf _ rfl).elim
  | app _ hM _ =>
      intro n i V he; simp only [BoCa.BoLo.performE, Expr.app.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (der_prim hM _ rfl).elim
  | allE hM _ | proj₁ hM | proj₂ hM =>
      intro n i V he; simp only [BoCa.BoLo.performE, Expr.app.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (der_prim hM _ rfl).elim
  | allEV hM _ =>
      intro n i V he; simp only [BoCa.BoLo.performE, Expr.app.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (der_prim hM _ rfl).elim
  | ret _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he; exact ⟨j₀, hb, hr.tail (JS.ret _)⟩
  | ofRet _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he; exact ⟨j₀, hb, hr.tail (JS.ofRet _)⟩
  | effSub hle _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.effSub _ _ _ hle)⟩
  | nuIn hC _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he; exact ⟨j₀, hb, hr.tail (JS.nuIn _ hC)⟩
  | nuOut hC _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.nuOut _ hC)⟩
  | bangE _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.bang _))⟩
  | boxI _ _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxI _ _))⟩
  | boxE _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxE _ _))⟩
  | immSub _ _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.immS _ _ _))⟩
  | mutSub _ _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.mutS _ _ _))⟩
  | roll _ _ _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.roll _))⟩
  | unroll _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.unroll _))⟩
  | _ => intro n i V he; cd_at he

/-- `[raise]`'s premises, at its conclusion `j₀`. -/
def RaiseBase (n i : UInt32) (j₀ : Jdg) : Prop :=
  ∃ (S : Row) (o : OpSig) (B : VTy), Row.find S n i = some o ∧ o.abort = true ∧
    j₀ = .comp (CTy.effOf S B)

/-- **A `raise` is `[raise]`'s, then the same-term rules.** -/
theorem der_raiseJ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ n i V, e = BoCa.BoLo.raiseE (opArgE n i V) → ∃ j₀, RaiseBase n i j₀ ∧ JR j₀ j := by
  induction h with
  | effRaise hf ha _ _ =>
      intro n i V he
      simp only [BoCa.BoLo.raiseE, opArgE, Expr.val, Val.prim, Val.i32, Expr.app.injEq,
        Expr.pair.injEq, Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at he
      obtain ⟨-, rfl, rfl, -⟩ := he
      exact ⟨_, ⟨_, _, _, hf, ha, rfl⟩, .refl⟩
  | force => intro n i V he; rcases forceE_var he with h | h <;> cd_at h
  | lolliE _ _ hf =>
      intro n i V he; simp only [BoCa.BoLo.raiseE, Expr.app.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (der_prim hf _ rfl).elim
  | app _ hM _ =>
      intro n i V he; simp only [BoCa.BoLo.raiseE, Expr.app.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (der_prim hM _ rfl).elim
  | allE hM _ | proj₁ hM | proj₂ hM =>
      intro n i V he; simp only [BoCa.BoLo.raiseE, Expr.app.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (der_prim hM _ rfl).elim
  | allEV hM _ =>
      intro n i V he; simp only [BoCa.BoLo.raiseE, Expr.app.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (der_prim hM _ rfl).elim
  | ret _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he; exact ⟨j₀, hb, hr.tail (JS.ret _)⟩
  | ofRet _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he; exact ⟨j₀, hb, hr.tail (JS.ofRet _)⟩
  | effSub hle _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.effSub _ _ _ hle)⟩
  | nuIn hC _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he; exact ⟨j₀, hb, hr.tail (JS.nuIn _ hC)⟩
  | nuOut hC _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.nuOut _ hC)⟩
  | bangE _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.bang _))⟩
  | boxI _ _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxI _ _))⟩
  | boxE _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxE _ _))⟩
  | immSub _ _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.immS _ _ _))⟩
  | mutSub _ _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.mutS _ _ _))⟩
  | roll _ _ _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.roll _))⟩
  | unroll _ ih =>
      intro n i V he; obtain ⟨j₀, hb, hr⟩ := ih n i V he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.unroll _))⟩
  | _ => intro n i V he; cd_at he

/-- `[⊗E]`'s premises, at its conclusion `j₀`. -/
def LetpairBase (Δ : LifeCtx) (Γ : Ctx VTy) (V M : Expr) (j₀ : Jdg) : Prop :=
  ∃ (Γ₁ Γ₂ : Ctx VTy) (A B : VTy) (C : CTy), Ctx.SplitP Γ Γ₁ Γ₂ ∧
    CDerives Δ Γ₁ V (.val (.tensor A B)) ∧
    CDerives Δ (⟨B, true⟩ :: ⟨A, true⟩ :: Γ₂) M (.comp C) ∧ j₀ = .comp C

/-- **A `let (x, y) = V in M` is `[⊗E]`'s, then the same-term rules.** -/
theorem der_letpairJ {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives Δ Γ e j) :
    ∀ V M, e = .letpair V M → ∃ j₀, LetpairBase Δ Γ V M j₀ ∧ JR j₀ j := by
  induction h with
  | tensorE hs hV hM => intro V M he; cases he; exact ⟨_, ⟨_, _, _, _, _, hs, hV, hM, rfl⟩, .refl⟩
  | force => intro V M he; rcases forceE_var he with h | h <;> cases h
  | ret _ ih =>
      intro V M he; obtain ⟨j₀, hb, hr⟩ := ih V M he; exact ⟨j₀, hb, hr.tail (JS.ret _)⟩
  | ofRet _ ih =>
      intro V M he; obtain ⟨j₀, hb, hr⟩ := ih V M he; exact ⟨j₀, hb, hr.tail (JS.ofRet _)⟩
  | effSub hle _ ih =>
      intro V M he; obtain ⟨j₀, hb, hr⟩ := ih V M he
      exact ⟨j₀, hb, hr.tail (JS.effSub _ _ _ hle)⟩
  | nuIn hC _ ih =>
      intro V M he; obtain ⟨j₀, hb, hr⟩ := ih V M he; exact ⟨j₀, hb, hr.tail (JS.nuIn _ hC)⟩
  | nuOut hC _ ih =>
      intro V M he; obtain ⟨j₀, hb, hr⟩ := ih V M he
      exact ⟨j₀, hb, hr.tail (JS.nuOut _ hC)⟩
  | bangE _ ih =>
      intro V M he; obtain ⟨j₀, hb, hr⟩ := ih V M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.bang _))⟩
  | boxI _ _ ih =>
      intro V M he; obtain ⟨j₀, hb, hr⟩ := ih V M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxI _ _))⟩
  | boxE _ ih =>
      intro V M he; obtain ⟨j₀, hb, hr⟩ := ih V M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.boxE _ _))⟩
  | immSub _ _ ih =>
      intro V M he; obtain ⟨j₀, hb, hr⟩ := ih V M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.immS _ _ _))⟩
  | mutSub _ _ ih =>
      intro V M he; obtain ⟨j₀, hb, hr⟩ := ih V M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.mutS _ _ _))⟩
  | roll _ _ _ ih =>
      intro V M he; obtain ⟨j₀, hb, hr⟩ := ih V M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.roll _))⟩
  | unroll _ ih =>
      intro V M he; obtain ⟨j₀, hb, hr⟩ := ih V M he
      exact ⟨j₀, hb, hr.tail (JS.val (VS.unroll _))⟩
  | _ => intro V M he; cd_terms

/-! ### Reading `progT`'s clause -/

/-- A λ-value that is no constant and no pair of computations, read at `A ⊸ D` with `A` no `1`, is
`[⊸I]`'s. -/
theorem lam_arr {Δ : LifeCtx} {Γ : Ctx VTy} {N : Expr} {A : VTy} {D : CTy} {j : Jdg}
    (h : CDerives Δ Γ (.lam N) j) (hj : j = .comp (.arr A D) ∨ j = .val (.thunk (.arr A D)))
    (hA : A ≠ .unit) (hw : ∀ M₁ M₂, Expr.lam N ≠ withPair M₁ M₂) (hc : NotConst (.lam N)) :
    CDerives Δ (⟨A, true⟩ :: Γ) N (.comp D) := by
  have hcls : ∀ {D' : CTy} {Γ' : Ctx VTy}, LamCls Γ' D' j → D' = .arr A D := by
    intro D' Γ' h
    rcases hj with rfl | rfl
    · rcases h with h | h | ⟨-, h⟩
      · cases h; rfl
      · obtain ⟨S, Y, he, -⟩ := h; exact absurd he.symm (effOf_ne_arr S Y A D)
      · obtain ⟨S, Y, he, -⟩ := h; exact absurd he.symm (effOf_ne_arr S Y A D)
    · rcases h with h | h | ⟨-, h⟩
      · cases h
      · exact vview_thunk h
      · exact vview_bang_thunk h
  rcases der_lam h N rfl with ⟨A', D', hN, hl⟩ | ⟨S, B, -, hl⟩ | ⟨_, _, _, _, _, -, hl⟩ |
    ⟨A', -, hl⟩ | ⟨M₁, M₂, hwp⟩ | hx
  · cases hcls hl; exact hN
  · have := hcls hl
    simp only [CTy.arr.injEq] at this
    exact (hA this.1.symm).elim
  · cases hcls hl
  · rcases hj with rfl | rfl
    · rcases hl with ⟨S, Y, he, -⟩ | ⟨-, S, Y, he, -⟩ <;> exact absurd he.symm (effOf_ne_arr S Y A D)
    · rcases hl with hl | ⟨-, hl⟩
      · cases vview_thunk hl
      · cases vview_bang_thunk hl
  · exact (hw M₁ M₂ hwp).elim
  · exact (hc.notAx _ hx).elim

/-- A variable whose slot, in a context below `Γ`, is `Γ`'s slot `0`. -/
theorem varCls_of_le {Δ : LifeCtx} {Γ Γ' : Ctx VTy} {T : VTy} {j : Jdg}
    (hslot : Γ[0]? = some ⟨T, true⟩) (hle : CtxLe Γ' Γ) (h : CDerives Δ Γ' (.var 0) j) :
    VarCls T j := by
  obtain ⟨T', hT', hc⟩ := der_var h 0 rfl
  rw [hle 0 T' hT'] at hslot
  cases hslot
  exact hc

/-- **`κ`'s cancel branch, applied**: at a slot whose type is a view of `!U(C₁ & C₂)`,
`x (inj₂ ())` is read at what the same-term rules reach from `C₂`. -/
theorem kappa_cancel_jr {Δ : LifeCtx} {Γ : Ctx VTy} {C₁ C₂ : CTy} {T : VTy} {j : Jdg}
    (hT : VView (.bang (.thunk (.amp C₁ C₂))) T) (hslot : Γ[0]? = some ⟨T, true⟩)
    (h : CDerives Δ Γ (.app (.var 0) (.val (Val.inj₂ Val.unit))) j) : JR (.comp C₂) j := by
  obtain ⟨j₀, hb, hr⟩ := der_app h (.var 0) (.val (Val.inj₂ Val.unit)) rfl
  rcases hb with ⟨_, _, _, _, hs, -, hf, rfl⟩ | ⟨_, _, _, _, _, he, -⟩ | ⟨_, _, _, _, _, _, he, -⟩ |
    ⟨_, _, _, he, -⟩ | ⟨_, _, _, _, he, -⟩ | ⟨_, _, _, _, he, -⟩ | ⟨_, _, he, -⟩ |
    ⟨D₁, D₂, -, hX, rfl⟩ | ⟨he, -⟩ | he | he | ⟨_, he⟩ | ⟨_, he⟩
  · rcases varCls_of_le hslot (splitP_le_right hs) hf with hc | ⟨C, rfl, -, hr'⟩
    · cases vview_bang_thunk (hT.trans hc)
    · cases vview_bang_thunk hT
      obtain ⟨S, A, he⟩ := JR.comp_val hr'
      exact absurd he (Inst.effOf_ne_amp S A C₁ C₂).symm
  all_goals first
    | (cases he)
    | skip
  · rcases varCls_of_le hslot (CtxLe.refl Γ) hX with hc | ⟨C, rfl, -, hr'⟩
    · obtain ⟨S, Y, he, -⟩ := hc
      exact absurd he.symm (Inst.effOf_ne_amp S Y D₁ D₂)
    · cases vview_bang_thunk hT
      obtain ⟨-, rfl⟩ := JR.amp_amp hr'
      exact hr


theorem vview_bang_thunk_unit {C : CTy} (h : VView (.bang (.thunk C)) .unit) : False := by
  rcases h.hnf (hnf_self (fun _ _ h => by cases h) (fun _ h => by cases h)) with
    h' | ⟨A', hA, h'⟩ | ⟨a, A', h'⟩ | ⟨a, A', h'⟩
  · have := h'.eq_self (fun _ _ h => by cases h) (fun _ h => by cases h); cases this
  · cases hA
    have := h'.eq_of_heads (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
      (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)
      (fun _ h => by cases h)
    cases this
  · cases h'
  · cases h'

/-- **`cancelCT` reads `κ`'s cancel at its row**: at the clause type of an unrestricted operation
`A ↠ B`, `B` no `0`, at the cancel row `F`, the same-term rules reach the clause's `F_Σ R` from
`κ`'s cancel branch `cancelTy Σ F`. -/
theorem cancelCT_jr {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {R A B : VTy} {F : CTy}
    (hB : B.isZero = false)
    (h : CDerives Δ Γ (.val cancelCT) (.val (clauseTy S R (.unr, A, B) F))) :
    JR (.comp (cancelTy S F)) (.comp (CTy.effOf S R)) := by
  have hty : clauseTy S R (.unr, A, B) F =
      .bang (.thunk (.arr (.tensor A (kTy S R .unr B F)) (CTy.effOf S R))) := by
    simp [clauseTy, hB]
  rw [hty] at h
  obtain ⟨-, hb⟩ := lam_bang h (fun h => by cases h) (by not_withPair) (by not_const)
  obtain ⟨j₀, ⟨Γ₁, Γ₂, A', B', C, hs, hV, hB₂, rfl⟩, hr⟩ := der_letpairJ hb _ _ rfl
  have hslotP : (⟨.tensor A (kTy S R .unr B F), true⟩ :: Γ : Ctx VTy)[0]? =
      some ⟨.tensor A (kTy S R .unr B F), true⟩ := rfl
  rcases varCls_of_le hslotP (splitP_le_left hs) hV with hc | ⟨_, hT, -, -⟩
  swap
  · cases hT
  obtain ⟨rfl, rfl⟩ := vview_tensor hc
  have hslotK : (⟨kTy S R .unr B F, true⟩ :: ⟨A, true⟩ :: Γ₂ : Ctx VTy)[0]? =
      some ⟨kTy S R .unr B F, true⟩ := rfl
  obtain ⟨j₁, hb₁, hr₁⟩ := der_app hB₂ _ _ rfl
  have hk : VView (.bang (.thunk (.amp (.arr B (CTy.effOf S R)) (cancelTy S F))))
      (kTy S R .unr B F) := .refl
  refine Relation.ReflTransGen.trans (Relation.ReflTransGen.trans ?_ hr₁) hr
  rcases hb₁ with ⟨Γ₃, Γ₄, A₀, B₀, hs', hY, hX, rfl⟩ | ⟨Γ₃, Γ₄, i, A₀, C₀, hi, hs', hX, hx, rfl⟩ |
    ⟨N', Γ₃, Γ₄, A₀, S₀, C₀, hXe, hs', hM, hN, rfl⟩ | ⟨_, _, _, _, he, -⟩ | ⟨_, _, _, _, he, -⟩ |
    ⟨_, _, _, _, he, -⟩ | ⟨_, _, he, -⟩ | ⟨_, _, he, -⟩ | ⟨he, -⟩ | he | he | ⟨_, he⟩ | ⟨_, he⟩
  · -- `⊸E`: the λ at a `⊸`, its body at `F B₀`
    rcases varCls_of_le hslotK (splitP_le_left hs') hY with hc | ⟨_, hT, -, -⟩
    swap
    · cases hT
    have hA₀ : A₀ ≠ .unit := by rintro rfl; exact vview_bang_thunk_unit (hk.trans hc)
    have hN := lam_arr hX (.inr rfl) hA₀ (by not_withPair) (by not_const)
    exact (kappa_cancel_jr (hk.trans hc) rfl hN).tail (JS.ofRet _)
  · -- `[app]`: the argument at its slot's type
    cases hi
    have hA₀ := splitP_le_right hs' 0 A₀ (soloP_le hx)
    rw [hslotK] at hA₀
    cases hA₀
    have hN := lam_arr hX (.inl rfl) (fun h => by cases h) (by not_withPair) (by not_const)
    exact kappa_cancel_jr hk rfl hN
  · -- `[let]`: the argument returned, its type a view of `κ`'s
    cases hXe
    rcases varCls_of_le hslotK (splitP_le_left hs') hM with ⟨S₁, Y₁, he, hc⟩ | ⟨_, hT, -, -⟩
    swap
    · cases hT
    obtain ⟨-, rfl⟩ := Inst.effOf_inj he
    exact kappa_cancel_jr (hk.trans hc) rfl hN
  all_goals cases he


/-! ### `progT` -/

/-- A cancel row below another finds, at a key the lower one finds, an operation of the upper one,
unless the upper one is `⊤`. -/
theorem finLe_find {F F' : CTy} (h : FinLe F F') {n i : UInt32} {o : OpSig}
    (hf : Row.find F.rowOf n i = some o) : F'.isTop = true ∨ ∃ o', Row.find F'.rowOf n i = some o' := by
  rcases (finLe_iff F F').mp h with h | ⟨-, hle⟩
  · exact .inl h
  · obtain ⟨o', hf', -⟩ := hle n i o hf
    exact .inr ⟨o', hf'⟩

/-- `⊤` is below `⊤` alone. -/
theorem finLe_top_top {F F' : CTy} (h : FinLe F F') (hF : F.isTop = true) : F'.isTop = true := by
  rcases (finLe_iff F F').mp h with h | ⟨h, -⟩
  · exact h
  · rw [hF] at h; cases h

/-- **`progT` has no derivation at a row without `2`** (decision D3).  `[handle] 1`'s body holds
`hnd 2 (perform 1 then x. x unwind raise 2)`: the `[then]`'s premise puts `2` in the cancel row of
`1`, `fs 0`, which `[sub]` up to the body keeps; the clause applies `κ`'s cancel branch, at
`F_{fs 0 ⊕ Σ} 1`, and the same-term rules read it at the clause's row `Σ`, so `Σ` holds `2`, and so
does every row the program is read at. -/
theorem not_der_progT {Δ : LifeCtx} {Γ : Ctx VTy} {S' : Row} {Y : VTy}
    (hS' : ∀ o ∈ S', o.n ≠ 2) : ¬ CDerives Δ Γ progT (.comp (CTy.effOf S' Y)) := by
  intro h
  -- `[handle] 1`
  obtain ⟨j₁, ⟨Γ₁, Γ₂, S, E, fs, A, R, -, hQ, hH, hM, -, rfl⟩, hr₁⟩ :=
    der_hndJ h 1 (qualsVal [.unr]).1 (.pair (.val CancelIntercept.idV) (.pair (.val cancelCT) (.val Val.unit)))
      ((K 2).plug (performU 1)) rfl
  have hSS' : RowLe S S' := JR.rowLe hr₁
  have hE : [Qual.unr] = E.map Prod.fst := Targets.qualsVal_inj hQ
  obtain ⟨⟨q₁, A₁, B₁⟩, rfl⟩ : ∃ e, E = [e] := by
    rcases E with _ | ⟨e, _ | ⟨e', E'⟩⟩
    · simp at hE
    · exact ⟨e, rfl⟩
    · simp at hE
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hE
  subst hE
  -- `[handle] 2`, then the `[then]`
  obtain ⟨j₂, ⟨Γ₃, Γ₄, S₂, E₂, fs₂, A₂, R₂, -, -, -, hM₂, -, rfl⟩, hr₂⟩ :=
    der_hndJ hM 2 (qualsVal [.unr]).1
      (.pair (.val CancelIntercept.idV) (.pair (.val (constC Val.unit)) (.val Val.unit)))
      ((uF (raiseU 2) .hole).plug (performU 1)) rfl
  have hS₂ : RowLe S₂ (Row.ofEff 1 [(.unr, A₁, B₁)] 0 fs ++ S) := JR.rowLe hr₂
  obtain ⟨j₃, ⟨Γ₅, Γ₆, A₃, B₃, S₃, SM, SD, -, hMS, -, hfin, hMp, hDr, rfl⟩, hr₃⟩ :=
    der_thenJ hM₂ (.var 0) (raiseU 2) (performU 1) rfl
  have hS₃ : RowLe S₃ (Row.ofEff 2 E₂ 0 fs₂ ++ S₂) := JR.rowLe hr₃
  -- `perform 1`'s row finds `1`, the finaliser's row finds `2`
  obtain ⟨j₄, ⟨S₄, oM₀, hf₄, ha₄, rfl⟩, hr₄⟩ := der_performJ hMp 1 0 (.val Val.unit) rfl
  obtain ⟨oM, hfM, hleM⟩ := JR.rowLe hr₄ 1 0 oM₀ hf₄
  obtain ⟨j₅, ⟨S₅, oD₀, B₅, hf₅, -, rfl⟩, hr₅⟩ := der_raiseJ hDr 2 0 (.val Val.unit) rfl
  obtain ⟨oD, hfD, -⟩ := JR.rowLe hr₅ 2 0 oD₀ hf₅
  -- `1` from the `[then]` up to `[handle] 1`'s body
  obtain ⟨o₃, hf₃, hle₃⟩ := hMS 1 0 oM hfM
  obtain ⟨o₄, hf₄', hle₄⟩ := hS₃ 1 0 o₃ hf₃
  rw [Row.find_append, Row.find_ofEff_ne 2 E₂ 0 fs₂ 1 0 (by decide), Option.none_or] at hf₄'
  obtain ⟨o₅, hf₅', hle₅⟩ := hS₂ 1 0 o₄ hf₄'
  rw [Row.find_append, show Row.find (Row.ofEff 1 [(.unr, A₁, B₁)] 0 fs) 1 0 =
    some ⟨1, 0, .unr, A₁, B₁, fs 0⟩ from rfl, Option.some_or] at hf₅'
  cases hf₅'
  have hsig : oM₀.Sig ⟨1, 0, .unr, A₁, B₁, fs 0⟩ :=
    hleM.1.trans (hle₃.1.trans (hle₄.1.trans hle₅.1))
  have hB₁ : B₁.isZero = false := by
    have := hsig.abort_eq
    rw [ha₄] at this
    simpa [OpSig.abort] using this.symm
  have hcap₀ : capB oM₀.q oM₀.B = true := by
    rw [hsig.capB_eq]; simp [capB, hB₁]
  have hcapM : capB oM.q oM.B = true := hleM.1.capB_eq ▸ hcap₀
  have hcap₃ : capB o₃.q o₃.B = true := hle₃.1.capB_eq ▸ hcapM
  have hcap₄ : capB o₄.q o₄.B = true := hle₄.1.capB_eq ▸ hcap₃
  -- `2` in the cancel row of `1`, or the cancel row `⊤`
  have h₃₄ : FinLe o₃.fin o₄.fin := hle₄.2 hcap₃
  have h₄₅ : FinLe o₄.fin (fs 0) := hle₅.2 hcap₄
  have hfs : (fs 0).isTop = true ∨ ∃ o₆, Row.find (fs 0).rowOf 2 0 = some o₆ := by
    have hT := hfin 1 0 oM o₃ hfM hf₃ hcapM
    rw [ThenLe] at hT
    rcases hT with hT | ⟨-, -, hT⟩
    · exact .inl (finLe_top_top h₄₅ (finLe_top_top h₃₄ hT))
    · obtain ⟨o', hf', -⟩ := hT 2 0 oD hfD
      rcases finLe_find h₃₄ hf' with h₄ | ⟨o'', hf''⟩
      · exact .inl (finLe_top_top h₄₅ h₄)
      · exact finLe_find h₄₅ hf''
  -- the clause reads `κ`'s cancel at its row
  rcases der_pair hH _ _ rfl with ⟨Γ₇, Γ₈, X₁, X₂, -, -, hcl, hc₁⟩ | he
  swap
  · simp [emptyFamV, Val.arr, Val.pair, Val.loc, Val.i32] at he
  obtain ⟨-, rfl⟩ := vview_tensor hc₁
  rcases der_pair hcl _ _ rfl with ⟨Γ₉, Γ₁₀, X₃, X₄, -, hcan, -, hc₂⟩ | he
  swap
  · simp [emptyFamV, Val.arr, Val.pair, Val.loc, Val.i32] at he
  obtain ⟨rfl, -⟩ := vview_tensor (show VView (.tensor X₃ X₄)
    (.tensor (clauseTy S R (.unr, A₁, B₁) (fs 0)) .unit) from hc₂)
  have hjr := cancelCT_jr hB₁ hcan
  rcases hfs with htop | ⟨o₆, hf₆⟩
  · rw [show cancelTy S (fs 0) = .top by simp [cancelTy, htop]] at hjr
    have := JR.rigid hjr rigid_top
    simp only [Jdg.comp.injEq] at this
    exact effOf_ne_top S R this
  · have hnt : (fs 0).isTop = false := by
      cases ht : (fs 0).isTop
      · rfl
      · have : (fs 0).rowOf = [] := by
          cases hF : fs 0 <;> simp_all [CTy.isTop, CTy.rowOf]
        rw [this] at hf₆; simp [Row.find] at hf₆
    rw [show cancelTy S (fs 0) = CTy.effOf ((fs 0).rowOf ++ S) .unit by
      simp [cancelTy, hnt]] at hjr
    obtain ⟨o₇, hf₇, -⟩ := JR.rowLe hjr 2 0 o₆ (by rw [Row.find_append, hf₆]; rfl)
    obtain ⟨o₈, hf₈, -⟩ := hSS' 2 0 o₇ hf₇
    obtain ⟨hm₈, hn₈, -⟩ := Row.find_mem hf₈
    exact hS' o₈ hm₈ hn₈

/-- **`progT` has no derivation at `F A`**, the empty row's returner. -/
theorem not_der_progT_ret {Δ : LifeCtx} {Γ : Ctx VTy} {Y : VTy} :
    ¬ CDerives Δ Γ progT (.comp (.ret Y)) :=
  not_der_progT (S' := []) (fun _ h => absurd h List.not_mem_nil)


/-- **A cancelling clause tuple reads `κ`'s cancel at its row**: the handler pair
`(λx. x, (cancelCT, ()))` at `[handle]`'s type, its one operation unrestricted `A ↠ B` with `B` no
`0`. -/
theorem cancelPair_jr {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A R A₁ B₁ : VTy} {fs : Nat → CTy}
    (hB₁ : B₁.isZero = false)
    (hH : CDerives Δ Γ (.pair (.val CancelIntercept.idV) (.pair (.val cancelCT) (.val Val.unit)))
      (.val (.tensor (retTy S A R) (clausesTy S R [(.unr, A₁, B₁)] fs)))) :
    JR (.comp (cancelTy S (fs 0))) (.comp (CTy.effOf S R)) := by
  rcases der_pair hH _ _ rfl with ⟨Γ₇, Γ₈, X₁, X₂, -, -, hcl, hc₁⟩ | he
  swap
  · simp [emptyFamV, Val.arr, Val.pair, Val.loc, Val.i32] at he
  obtain ⟨-, rfl⟩ := vview_tensor hc₁
  rcases der_pair hcl _ _ rfl with ⟨Γ₉, Γ₁₀, X₃, X₄, -, hcan, -, hc₂⟩ | he
  swap
  · simp [emptyFamV, Val.arr, Val.pair, Val.loc, Val.i32] at he
  obtain ⟨rfl, -⟩ := vview_tensor (show VView (.tensor X₃ X₄)
    (.tensor (clauseTy S R (.unr, A₁, B₁) (fs 0)) .unit) from hc₂)
  exact cancelCT_jr hB₁ hcan

/-- **`κ`'s cancel read at the clause's row**: the cancel row is no `⊤`, and its operations, ahead
of the row, are below the row. -/
theorem cancelTy_rowLe {S : Row} {F : CTy} {R : VTy}
    (h : JR (.comp (cancelTy S F)) (.comp (CTy.effOf S R))) :
    F.isTop = false ∧ RowLe (F.rowOf ++ S) S := by
  cases hF : F.isTop
  · rw [show cancelTy S F = CTy.effOf (F.rowOf ++ S) .unit by simp [cancelTy, hF]] at h
    exact ⟨rfl, JR.rowLe h⟩
  · rw [show cancelTy S F = .top by simp [cancelTy, hF]] at h
    have := JR.rigid h rigid_top
    simp only [Jdg.comp.injEq] at this
    exact (effOf_ne_top S R this).elim

/-! ### `progNCrecT`: two finalisers that perform the cancelling operation -/

/-- `G` is `⊤`, or finds an operation of `m`. -/
def FindsAt (m : UInt32) (G : CTy) : Prop := G.isTop = true ∨ ∃ y, Row.find G.rowOf m 0 = some y

/-- `G` is `⊤`, or finds a capturable operation of `m`. -/
def FindsCap (m : UInt32) (G : CTy) : Prop :=
  G.isTop = true ∨ ∃ x, Row.find G.rowOf m 0 = some x ∧ capB x.q x.B = true

/-- `G` is `⊤`, or finds a capturable operation of `m` whose own cancel row is `⊤` or finds `m`. -/
def FindsRec (m : UInt32) (G : CTy) : Prop :=
  G.isTop = true ∨ ∃ x, Row.find G.rowOf m 0 = some x ∧ capB x.q x.B = true ∧ FindsAt m x.fin

theorem FindsAt.mono {m : UInt32} {G G' : CTy} (h : FinLe G G') (hG : FindsAt m G) :
    FindsAt m G' := by
  rcases hG with hT | ⟨y, hy⟩
  · exact .inl (finLe_top_top h hT)
  · exact finLe_find h hy

theorem FindsCap.mono {m : UInt32} {G G' : CTy} (h : FinLe G G') (hG : FindsCap m G) :
    FindsCap m G' := by
  rcases hG with hT | ⟨x, hx, hc⟩
  · exact .inl (finLe_top_top h hT)
  · rcases (finLe_iff G G').mp h with h | ⟨-, hle⟩
    · exact .inl h
    · obtain ⟨x', hx', hle'⟩ := hle m 0 x hx
      exact .inr ⟨x', hx', hle'.1.capB_eq ▸ hc⟩

theorem FindsRec.mono {m : UInt32} {G G' : CTy} (h : FinLe G G') (hG : FindsRec m G) :
    FindsRec m G' := by
  rcases hG with hT | ⟨x, hx, hc, hx'⟩
  · exact .inl (finLe_top_top h hT)
  · rcases (finLe_iff G G').mp h with h | ⟨-, hle⟩
    · exact .inl h
    · obtain ⟨x', hx₁, hle'⟩ := hle m 0 x hx
      exact .inr ⟨x', hx₁, hle'.1.capB_eq ▸ hc, hx'.mono (hle'.2 hc)⟩

/-- **The finaliser below a cancel row**: a capturable operation of `m` in `E` puts one in `F ⋈ E`. -/
theorem thenLe_findsCap {m : UInt32} {F T : CTy} {E : Row} (h : ThenLe F E T) {z : OpSig}
    (hz : Row.find E m 0 = some z) (hc : capB z.q z.B = true) : FindsCap m T := by
  rw [ThenLe] at h
  rcases h with h | ⟨-, -, hE⟩
  · exact .inl h
  · obtain ⟨z', hz', hs, -⟩ := hE m 0 z hz
    exact .inr ⟨z', hz', hs.capB_eq ▸ hc⟩

/-- **The leftover clause**: a capturable operation of `m` already in `F`, below a finaliser that
performs one of `m`, gets `m` in its own cancel row in `F ⋈ E`. -/
theorem thenLe_findsRec {m : UInt32} {F T : CTy} {E : Row} (h : ThenLe F E T) (hF : FindsCap m F)
    {z : OpSig} (hz : Row.find E m 0 = some z) : FindsRec m T := by
  rw [ThenLe] at h
  rcases h with h | ⟨hFt, hF', -⟩
  · exact .inl h
  · rcases hF with hT | ⟨x, hx, hc⟩
    · rw [hT] at hFt; cases hFt
    · obtain ⟨x', hx', hs, hle⟩ := hF' m 0 x hx
      refine .inr ⟨x', hx', hs.capB_eq ▸ hc, ?_⟩
      have h₂ := hle hc
      rw [ThenLe] at h₂
      rcases h₂ with h₂ | ⟨-, -, hE⟩
      · exact .inl h₂
      · obtain ⟨y, hy, -⟩ := hE m 0 z hz
        exact .inr ⟨y, hy⟩

/-- **`progNCrecT` has no derivation** (D3, the leftover clause): the first finaliser's `4` is in
the cancel row of `1`, and the second finaliser, which runs in the cancel of that `4`'s
continuation, puts `4` in its cancel row in turn; so `H₁`'s clause row holds a `4` whose cancel row
holds `4`, and so does the clause row of the outer handler of `4`, its own outer row, which lacks
`4`. -/
theorem not_der_progNCrecT {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} : ¬ CDerives Δ Γ progNCrecT j := by
  intro h
  -- the outer `[handle] 4`
  obtain ⟨j₀, ⟨Γa, Γb, S₀, E₀, fs₀, A₀', R₀, -, hQ₀, hH₀, hM₀, hnS₀, rfl⟩, -⟩ :=
    der_hndJ h 4 (qualsVal [.unr]).1
      (.pair (.val CancelIntercept.idV) (.pair (.val cancelCT) (.val Val.unit)))
      (hndE H₁T (hndE (hU 4 CancelIntercept.idV (constC Val.unit))
        (thenU (thenU (performU 1) (performU 4)) (performU 4)))) rfl
  have hE₀ : [Qual.unr] = E₀.map Prod.fst := Targets.qualsVal_inj hQ₀
  obtain ⟨⟨q₀, A₀, B₀⟩, rfl⟩ : ∃ e, E₀ = [e] := by
    rcases E₀ with _ | ⟨e, _ | ⟨e', E'⟩⟩
    · simp at hE₀
    · exact ⟨e, rfl⟩
    · simp at hE₀
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hE₀
  subst hE₀
  -- `[handle] 1`
  obtain ⟨j₁, ⟨Γc, Γd, S₁, E₁, fs₁, A₁', R₁, -, hQ₁, hH₁, hM₁, -, rfl⟩, hr₁⟩ :=
    der_hndJ hM₀ 1 (qualsVal [.unr]).1
      (.pair (.val CancelIntercept.idV) (.pair (.val cancelCT) (.val Val.unit)))
      (hndE (hU 4 CancelIntercept.idV (constC Val.unit))
        (thenU (thenU (performU 1) (performU 4)) (performU 4))) rfl
  have hS₁ : RowLe S₁ (Row.ofEff 4 [(.unr, A₀, B₀)] 0 fs₀ ++ S₀) := JR.rowLe hr₁
  have hE₁ : [Qual.unr] = E₁.map Prod.fst := Targets.qualsVal_inj hQ₁
  obtain ⟨⟨q₁, A₁, B₁⟩, rfl⟩ : ∃ e, E₁ = [e] := by
    rcases E₁ with _ | ⟨e, _ | ⟨e', E'⟩⟩
    · simp at hE₁
    · exact ⟨e, rfl⟩
    · simp at hE₁
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hE₁
  subst hE₁
  -- the inner `[handle] 4`, then the two `[then]`s
  obtain ⟨j₂, ⟨Γe, Γf, S₂, E₂, fs₂, A₂, R₂, -, hQ₂, -, hM₂, -, rfl⟩, hr₂⟩ :=
    der_hndJ hM₁ 4 (qualsVal [.unr]).1
      (.pair (.val CancelIntercept.idV) (.pair (.val (constC Val.unit)) (.val Val.unit)))
      (thenU (thenU (performU 1) (performU 4)) (performU 4)) rfl
  have hS₂ : RowLe S₂ (Row.ofEff 1 [(.unr, A₁, B₁)] 0 fs₁ ++ S₁) := JR.rowLe hr₂
  have hE₂ : [Qual.unr] = E₂.map Prod.fst := Targets.qualsVal_inj hQ₂
  obtain ⟨⟨q₂, A₂', B₂'⟩, rfl⟩ : ∃ e, E₂ = [e] := by
    rcases E₂ with _ | ⟨e, _ | ⟨e', E'⟩⟩
    · simp at hE₂
    · exact ⟨e, rfl⟩
    · simp at hE₂
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hE₂
  subst hE₂
  obtain ⟨j₃, ⟨Γg, Γh, A₃, B₃, S₃, SM₃, SD₃, -, hMS₃, -, hfin₃, hM₃, hD₃, rfl⟩, hr₃⟩ :=
    der_thenJ hM₂ (.var 0) (performU 4) (thenU (performU 1) (performU 4)) rfl
  have hS₃ : RowLe S₃ (Row.ofEff 4 [(.unr, A₂', B₂')] 0 fs₂ ++ S₂) := JR.rowLe hr₃
  obtain ⟨j₄, ⟨Γi, Γj, A₄, B₄, S₄, SM₄, SD₄, -, hMS₄, hDS₄, hfin₄, hM₄, hD₄, rfl⟩, hr₄⟩ :=
    der_thenJ hM₃ (.var 0) (performU 4) (performU 1) rfl
  have hS₄ : RowLe S₄ SM₃ := JR.rowLe hr₄
  -- the operations the three `perform`s find
  obtain ⟨j₅, ⟨S₅, oP₀, hf₅, ha₅, rfl⟩, hr₅⟩ := der_performJ hM₄ 1 0 (.val Val.unit) rfl
  obtain ⟨oP, hfP, hleP⟩ := JR.rowLe hr₅ 1 0 oP₀ hf₅
  obtain ⟨j₆, ⟨S₆, oD₀, hf₆, ha₆, rfl⟩, hr₆⟩ := der_performJ hD₄ 4 0 (.val Val.unit) rfl
  obtain ⟨oD, hfD, hleD⟩ := JR.rowLe hr₆ 4 0 oD₀ hf₆
  obtain ⟨j₇, ⟨S₇, oE₀, hf₇, ha₇, rfl⟩, hr₇⟩ := der_performJ hD₃ 4 0 (.val Val.unit) rfl
  obtain ⟨oE, hfE, -⟩ := JR.rowLe hr₇ 4 0 oE₀ hf₇
  -- `1` from `perform 1` up to `[handle] 1`'s body: unrestricted, its answer no `0`
  obtain ⟨o₄₁, hf₄₁, hle₄₁⟩ := hMS₄ 1 0 oP hfP
  obtain ⟨o₃₁, hf₃₁, hle₃₁⟩ := hS₄ 1 0 o₄₁ hf₄₁
  obtain ⟨o₂₁, hf₂₁, hle₂₁⟩ := hMS₃ 1 0 o₃₁ hf₃₁
  obtain ⟨o₂₁', hf₂₁', hle₂₁'⟩ := hS₃ 1 0 o₂₁ hf₂₁
  rw [Row.find_append, Row.find_ofEff_ne 4 _ 0 fs₂ 1 0 (by decide), Option.none_or] at hf₂₁'
  obtain ⟨o₁, hf₁, hle₁⟩ := hS₂ 1 0 o₂₁' hf₂₁'
  rw [Row.find_append, show Row.find (Row.ofEff 1 [(.unr, A₁, B₁)] 0 fs₁) 1 0 =
    some ⟨1, 0, .unr, A₁, B₁, fs₁ 0⟩ from rfl, Option.some_or] at hf₁
  cases hf₁
  have hsig₁ : oP₀.Sig ⟨1, 0, .unr, A₁, B₁, fs₁ 0⟩ :=
    hleP.1.trans (hle₄₁.1.trans (hle₃₁.1.trans (hle₂₁.1.trans (hle₂₁'.1.trans hle₁.1))))
  have hB₁ : B₁.isZero = false := by
    have := hsig₁.abort_eq
    rw [ha₅] at this
    simpa [OpSig.abort] using this.symm
  have hcap₁ : capB oP₀.q oP₀.B = true := by rw [hsig₁.capB_eq]; simp [capB, hB₁]
  have hcapP : capB oP.q oP.B = true := hleP.1.capB_eq ▸ hcap₁
  have hcap₄₁ : capB o₄₁.q o₄₁.B = true := hle₄₁.1.capB_eq ▸ hcapP
  have hcap₃₁ : capB o₃₁.q o₃₁.B = true := hle₃₁.1.capB_eq ▸ hcap₄₁
  have hcap₂₁ : capB o₂₁.q o₂₁.B = true := hle₂₁.1.capB_eq ▸ hcap₃₁
  have hcap₂₁' : capB o₂₁'.q o₂₁'.B = true := hle₂₁'.1.capB_eq ▸ hcap₂₁
  -- the first finaliser's `4`, up to the inner `[handle] 4`: unrestricted, its answer no `0`
  obtain ⟨d₄, hfd₄, hled₄⟩ := hDS₄ 4 0 oD hfD
  obtain ⟨d₃, hfd₃, hled₃⟩ := hS₄ 4 0 d₄ hfd₄
  obtain ⟨d₂, hfd₂, hled₂⟩ := hMS₃ 4 0 d₃ hfd₃
  obtain ⟨d₁, hfd₁, hled₁⟩ := hS₃ 4 0 d₂ hfd₂
  rw [Row.find_append, show Row.find (Row.ofEff 4 [(.unr, A₂', B₂')] 0 fs₂) 4 0 =
    some ⟨4, 0, .unr, A₂', B₂', fs₂ 0⟩ from rfl, Option.some_or] at hfd₁
  cases hfd₁
  have hsigD : oD₀.Sig ⟨4, 0, .unr, A₂', B₂', fs₂ 0⟩ :=
    hleD.1.trans (hled₄.1.trans (hled₃.1.trans (hled₂.1.trans hled₁.1)))
  have hB₂ : B₂'.isZero = false := by
    have := hsigD.abort_eq
    rw [ha₆] at this
    simpa [OpSig.abort] using this.symm
  have hcapD₀ : capB oD₀.q oD₀.B = true := by rw [hsigD.capB_eq]; simp [capB, hB₂]
  have hcapD : capB oD.q oD.B = true := hleD.1.capB_eq ▸ hcapD₀
  -- the first finaliser puts `4` in the cancel row of `1`; the second, a leftover of that `4`'s
  -- cancel, puts `4` in its cancel row in turn
  have h₄ : FindsCap 4 o₄₁.fin := thenLe_findsCap (hfin₄ 1 0 oP o₄₁ hfP hf₄₁ hcapP) hfD hcapD
  have h₃ : FindsCap 4 o₃₁.fin := h₄.mono (hle₃₁.2 hcap₄₁)
  have h₂ : FindsRec 4 o₂₁.fin := thenLe_findsRec (hfin₃ 1 0 o₃₁ o₂₁ hf₃₁ hf₂₁ hcap₃₁) h₃ hfE
  have h₁ : FindsRec 4 (fs₁ 0) := (h₂.mono (hle₂₁'.2 hcap₂₁)).mono (hle₁.2 hcap₂₁')
  -- `H₁`'s clause row holds a `4` whose cancel row holds `4`
  obtain ⟨hnt₁, hle₁'⟩ := cancelTy_rowLe (cancelPair_jr hB₁ hH₁)
  rcases h₁ with ht | ⟨x₁, hx₁, hcx₁, hfx₁⟩
  · rw [ht] at hnt₁; cases hnt₁
  obtain ⟨x₀, hx₀, hlex₀⟩ := hle₁' 4 0 x₁ (by rw [Row.find_append, hx₁]; rfl)
  have hfx₀ : FindsAt 4 x₀.fin := hfx₁.mono (hlex₀.2 hcx₁)
  have hcx₀ : capB x₀.q x₀.B = true := hlex₀.1.capB_eq ▸ hcx₁
  -- so does the outer handler of `4`'s clause row, its own outer row
  obtain ⟨y₀, hy₀, hley₀⟩ := hS₁ 4 0 x₀ hx₀
  rw [Row.find_append, show Row.find (Row.ofEff 4 [(.unr, A₀, B₀)] 0 fs₀) 4 0 =
    some ⟨4, 0, .unr, A₀, B₀, fs₀ 0⟩ from rfl, Option.some_or] at hy₀
  cases hy₀
  have hB₀ : B₀.isZero = false := by
    have := hley₀.1.capB_eq ▸ hcx₀
    simp only [capB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at this
    exact this.2
  have hfs₀ : FindsAt 4 (fs₀ 0) := hfx₀.mono (hley₀.2 hcx₀)
  obtain ⟨hnt₀, hle₀⟩ := cancelTy_rowLe (cancelPair_jr hB₀ hH₀)
  rcases hfs₀ with ht | ⟨y, hy⟩
  · rw [ht] at hnt₀; cases hnt₀
  obtain ⟨z, hz, -⟩ := hle₀ 4 0 y (by rw [Row.find_append, hy]; rfl)
  obtain ⟨hmz, hnz, -⟩ := Row.find_mem hz
  exact hnS₀ z hmz hnz

/-- **`progNCrecT`'s run ends at an operation no handler catches**: the configuration
`progNCrecT_run` reaches, `ccatch (cfin ⊥ (perform 4))`, takes no step. -/
theorem progNCrecT_stuck {μ μ' : BoCa.BoLo.Heap} {e' : Expr} :
    ¬ BoCa.BoLo.Step1 (ℍ := ℍ) μ ((ccF (cfF (BoCa.BoLo.cancelVal none) .hole)).plug (performU 4))
      μ' e' := by
  show ¬ BoCa.BoLo.Step1 μ ((ccF (cfF (BoCa.BoLo.cancelVal none) .hole)).plug
    (opE false (BoCa.BoLo.opPayload 4 0 Val.unit))) μ' e'
  exact opPlug_no_step (payloadName_opPayload 4 0 Val.unit) (by simp [OpFree, BoCa.BoLo.Kont.HasHnd])

end Targets.Rej

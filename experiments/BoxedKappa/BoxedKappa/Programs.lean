import Frontend.Check.CrossCheck
import BoxedKappa.Handle
import Core.Demonic

/-!
# BoxedKappa — P4 with stored continuations (variant (a)), and the premises at (b)–(d)

`research/effects/src/boxed-kappa-programs.md` has the programs and the hand derivations.

**Variant (a), end to end.** Two tasks, each borrowing its own local across an `await`, are
spawned by a handler of `await` whose clause receives `κ : [@⊤] K` and answers the task
`[@⊤] U Task`, `Task = νX. F(i32 ⊕ [@⊤] U X) & F 1`. A scheduler keeps the tasks in a queue lent
`mut` at a fresh `'q` on each observation of its run-until-empty loop.

* `bc/spawn-handler.bc`: the handler's pair `(h_ret, hs)`, checked by `bcc`'s checker in the kernel
  (`decide +kernel`) at `retTy [] i32 E ⊗ clausesTyB [] E ⊤ [await]` (`handler_shape`): today's
  checker types the clause as a value; only `[handle]` does not accept it.
* `bc/sched-a.bc`: the program as a function of `spawn`, checked the same way (`sched_shape`).
* `spawnBody_sem`: `handle_1 (tb ()) with (h_ret, hs)` by BOXED-κ (`handleV_compatCB`), the
  handled computation's context the boxed code `tb : [@⊤] U(1 ⊸ F_{await} i32)`.
* `prog_sem`: the program applied to `spawn`, by the compatibility lemmas over `fundamentalC` of
  the checked parts. `prog_every_run`: every run from the empty memory continues to an `i32` at
  the empty memory (`theorem32D`). `prog_eval`: the interpreter answers `41130` with no cell left.

**Premises at the other variants.** `ctxOutlives_imm_iff` (b: a captured `Imm 'r` meets the
context premise exactly when `@d ⊏ 'r`), `not_ctxOutlives_imm_self` (c: never at `@d = 'r`),
`not_ansOutlives_thunk` (d: an answer type with a bare `U` fails the answer premise),
`ansOutlives_boxTop` (d's repair). `taskBodyG_nuOk`: the task type is positive at every bound.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.BoxedKappaProgs
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx)
open Frontend.Check (mainOf)

/-- The task's body: `νX. F(i32 ⊕ [@⊤] U X) & F 1`. -/
abbrev taskBody : CTy := .amp (.ret (.sum (.int .w32) (.box .top (.tvar 0)))) (.ret .unit)
abbrev taskT : VTy := .thunk (.nu taskBody)
abbrev elemT : VTy := .box .top taskT
abbrev awaitE : List (Qual × VTy × VTy) := [(.aff, .unit, .unit)]
abbrev awRow : Row := Row.ofEff 1 awaitE 0

/-- `bc/spawn-handler.bc`: the spawn handler's pair. -/
def handlerP : Frontend.Program := bcc_program% "experiments/BoxedKappa/bc/spawn-handler.bc"

set_option maxRecDepth 100000 in
theorem handlerP_checks : (mainOf handlerP).isSome = true := by decide +kernel

def handlerC : Frontend.Check.Checked := (mainOf handlerP).get handlerP_checks

set_option maxRecDepth 100000 in
theorem handler_shape : handlerC.ctx = [] ∧
    handlerC.C = .ret (.tensor (retTy [] (.int .w32) elemT) (clausesTyB [] elemT .top awaitE)) := by
  decide +kernel

/-- `bc/sched-a.bc`: variant (a) as a function of `spawn`. -/
def schedP : Frontend.Program := bcc_program% "experiments/BoxedKappa/bc/sched-a.bc"

set_option maxRecDepth 100000 in
theorem schedP_checks : (mainOf schedP).isSome = true := by decide +kernel

def schedC : Frontend.Check.Checked := (mainOf schedP).get schedP_checks

abbrev codeT : VTy := .thunk (.arr .unit (CTy.effOf (awRow ++ []) (.int .w32)))
abbrev spawnT : VTy := .bang (.thunk (.arr (.box .top codeT) (.ret elemT)))

set_option maxRecDepth 100000 in
theorem sched_shape : schedC.ctx = [] ∧
    schedC.C = .ret (.thunk (.arr spawnT (.ret (.int .w32)))) := by
  decide +kernel

theorem handler_derives : CDerives LifeCtx.empty [] handlerC.e
    (.comp (.ret (.tensor (retTy [] (.int .w32) elemT) (clausesTyB [] elemT .top awaitE)))) := by
  have h := handlerC.deriv
  rwa [handler_shape.1, handler_shape.2] at h

theorem sched_derives : CDerives LifeCtx.empty [] schedC.e
    (.comp (.ret (.thunk (.arr spawnT (.ret (.int .w32)))))) := by
  have h := schedC.deriv
  rwa [sched_shape.1, sched_shape.2] at h

set_option maxRecDepth 100000 in
theorem handler_isValB : BoCa.isValB handlerC.e = true := by decide +kernel

/-- The handler's pair, `(h_ret, hs)`, a value. -/
def handlerV : Val := ⟨handlerC.e, BoCa.isVal_of_isValB _ handler_isValB⟩

theorem handlerV_derives : CDerives LifeCtx.empty [] (.val handlerV)
    (.comp (.ret (.tensor (retTy [] (.int .w32) elemT) (clausesTyB [] elemT .top awaitE)))) :=
  handler_derives

/-! ### A closed value typed at `[]` is typed at a dead context -/

theorem semV_closed_dead {Δ : LifeCtx} {Γ : Ctx VTy} {v : Val} {A : VTy}
    (hcl : closedAt 0 v.1 = true) (hΓ : Ctx.DeadP Γ) (h : SemV Δ [] (.val v) A) :
    SemV Δ Γ (.val v) A := by
  intro δ γ ls ρ hδ hg
  obtain ⟨-, hs⟩ := gDenC_iff.mp hg
  obtain rfl := gSepC_deadP hΓ hs
  have h0 := h δ [] ls PMap.empty hδ (gDenC_nil ls δ)
  rw [substAll_closed hcl] at h0 ⊢
  exact h0

/-! ### `spawn`: BOXED-κ at `@d = ⊤` -/

/-- `u ← return (); c ← return tb; c u`: run the boxed task code `tb : [@⊤] U(1 ⊸ F_{await} i32)`. -/
def runE : Expr := bindE (.val .unit) (bindE (.var 1) (.app (.var 0) (.var 1)))

theorem runE_derives {Δ : LifeCtx} :
    CDerives Δ [⟨.box .top codeT, true⟩] runE (.comp (CTy.effOf (awRow ++ []) (.int .w32))) :=
  .bind (.right .nil) (.ret (.unitI (.cons .nil)))
    (.bind (.right (.left .nil)) (.ret (.boxE (.var (.there (.here .nil)))))
      (.app (.left (.right (.dead .nil))) (.force (.here (.cons (.cons .nil))))
        (.there (.here (.cons .nil)))))

theorem defines_top (Δ : LifeCtx) : Δ.Defines .top := fun _ _ => ⟨_, rfl⟩

theorem entailsLe_top (Δ : LifeCtx) : Δ.EntailsLe .top .top :=
  fun _ _ => ⟨_, _, rfl, rfl, Nat.le_refl _⟩

/-- The task's context outlives `⊤`: it is the boxed code. -/
theorem run_ctxOutlives (Δ : LifeCtx) : CtxOutlives Δ [⟨.box .top codeT, true⟩] .top := by
  refine ⟨defines_top Δ, fun s hs _ => ?_⟩
  simp only [List.mem_singleton] at hs
  subst hs
  exact .box (entailsLe_top Δ)

/-- `await`'s answer, `1`, outlives `⊤`. -/
theorem await_ansOutlives (Δ : LifeCtx) : Row.AnsOutlives Δ .top (awRow ++ []) := by
  intro o ho _
  simp only [awRow, Row.ofEff, List.append_nil, List.mem_singleton] at ho
  subst ho
  exact .unit

/-- The body of `spawn`: `handle_1 (tb ()) with (h_ret, hs)`. -/
def spawnBody : Expr := hndExpr 1 (awaitE.map Prod.fst) (.val handlerV) runE

set_option maxRecDepth 100000 in
theorem handlerV_closed : closedAt 0 handlerV.1 = true := by decide +kernel

/-- **`spawn`'s body, by BOXED-κ** (`handleV_compatCB`): the handled computation's context is the
boxed code, which outlives `⊤`, and `await`'s answer `1` outlives `⊤`. -/
theorem spawnBody_sem :
    SemC LifeCtx.empty [⟨.box .top codeT, true⟩] spawnBody (CTy.effOf [] elemT) :=
  handleV_compatCB (.right .nil) (.cons .nil) (.val handlerV)
    (semV_closed_dead handlerV_closed (.cons .nil) (fundamentalC handlerV_derives)) (by decide)
    (by simp) (by simp) (fundamentalC runE_derives) (run_ctxOutlives _) (await_ansOutlives _)


/-- `spawn = !λtb. handle_1 (tb ()) with (h_ret, hs)`. -/
def spawnV : Val := Val.lam spawnBody

/-- **`spawn`'s type**, `!U([@⊤] U(1 ⊸ F_{await} i32) ⊸ F([@⊤] U Task))`, by BOXED-κ. -/
theorem spawnV_sem : SemV LifeCtx.empty [] (.val spawnV) spawnT :=
  bangThunkV_compatC (fun _ h => by simp at h) rfl (lam_compatC spawnBody_sem)

set_option maxRecDepth 100000 in
theorem spawnV_closed : closedAt 0 spawnV.1 = true := by decide +kernel

/-! ### The program: the scheduler applied to `spawn` -/

/-- `f ← main_sched; s ← return spawn; f s`. -/
def progE : Expr := bindE schedC.e (bindE (.val spawnV) (.app (.var 1) (.var 0)))

abbrev schedFnT : VTy := .thunk (.arr spawnT (.ret (.int .w32)))

/-- **Variant (a), typed**: every part by `CDerives` except `spawn`, which is BOXED-κ. -/
theorem prog_sem : SemC LifeCtx.empty [] progE (.ret (.int .w32)) := by
  refine bind_compatC .nil (fundamentalC sched_derives) ?_
  refine bind_compatC (.right .nil) (semV_closed_dead spawnV_closed (.cons .nil) spawnV_sem) ?_
  exact app_compatC (Γ₁ := [⟨spawnT, false⟩, ⟨schedFnT, true⟩])
    (Γ₂ := [⟨spawnT, true⟩, ⟨schedFnT, false⟩]) (.right (.left .nil))
    (fundamentalC (.force (.there (.here .nil)))) (.here (.cons .nil))

/-- **Variant (a), safe on every run**: every run from the empty memory continues to an `i32` at
the empty memory. -/
theorem prog_every_run {μ₁ : BoLo.Heap} {e₁ : Expr}
    (hs : BoLo.Steps Adequacy.emptyMem progE μ₁ e₁) :
    ∃ n : UInt32, BoLo.Steps μ₁ e₁ Adequacy.emptyMem (.val (Val.i32 n)) := by
  have hwp := prog_sem LSub.empty [] [] PMap.empty Adequacy.models_empty (gDenC_nil _ _)
  rw [show substAll [] progE = progE from Adequacy.psub_nil 0 progE] at hwp
  have hwp' : wpTS [] progE (fun _ v => BoLo.pure (∃ n, v = Val.i32 n)) (PMap.empty : WRes) :=
    wpTS_mono (fun _ v ρ hv => by obtain ⟨rfl, n, rfl⟩ := hv; exact ⟨rfl, n, rfl⟩)
      PMap.empty hwp
  obtain ⟨v, hsteps, n, rfl⟩ := theorem32D progE (fun v => ∃ n, v = Val.i32 n) hwp' hs
  exact ⟨n, hsteps⟩

/-- An `i32` result with no cell left. -/
def outI32 : Outcome → Option UInt32
  | .value ⟨.prim (.lit (.i32 n)), _⟩ false => some n
  | _ => none

set_option maxRecDepth 100000 in
/-- **Variant (a), run**: `41130`, no cell left. Task 2 finishes first (`41`), then task 1
(`130`): the scheduler interleaves them. -/
theorem prog_eval : outI32 (run wasmHost 100000 Mem.empty progE) = some 41130 := by
  decide +kernel


/-! ### The task type is positive at every bound and done-type -/

/-- `Task^d A = νX. F(A ⊕ [@d] U X) & F 1` is positive: `[@d] U X` is a polynomial position
(`VTy.Poly`'s box case, SPEC §22). -/
theorem taskBodyG_nuOk (d : Lifetime.Life) (A : VTy) :
    (CTy.amp (.ret (.sum (A.rename Nat.succ) (.box d (.tvar 0)))) (.ret .unit)).NuOk :=
  ⟨⟨VTy.poly_of_not_occ (VTy.not_occ_rename_succ A), trivial⟩, fun h => h⟩

theorem taskBody_nuOk : taskBody.NuOk := taskBodyG_nuOk .top (.int .w32)

/-! ### BOXED-κ's premises at the variants -/

/-- **Variant (b)**: a handled computation whose context is a captured `k : Imm 'r A` meets
BOXED-κ's context premise at `@d` exactly when `@d` is defined and `Δ ⊨ @d ⊏ 'r`, strictly. -/
theorem ctxOutlives_imm_iff {Δ : LifeCtx} {d r : Lifetime.Life} {A : VTy} :
    CtxOutlives Δ [⟨.imm r A, true⟩] d ↔ Δ.Defines d ∧ Δ.EntailsLt d r := by
  constructor
  · rintro ⟨hd, h⟩
    have h' := h _ (List.mem_singleton.mpr rfl) rfl
    cases h' with
    | imm hr => exact ⟨hd, hr⟩
  · rintro ⟨hd, hr⟩
    refine ⟨hd, fun s hs _ => ?_⟩
    simp only [List.mem_singleton] at hs
    subst hs
    exact .imm hr

/-- **Variant (c)**: at `@d = 'r`, the lifetime of the captured borrow itself, BOXED-κ's context
premise fails at every satisfiable `Δ` that defines `'r`: `Δ ⊨ 'r ⊏ 'r` is false. -/
theorem not_ctxOutlives_imm_self {Δ : LifeCtx} {r : Lifetime.Life} {A : VTy}
    (hsat : ∃ δ, Δ.Models δ) : ¬ CtxOutlives Δ [⟨.imm r A, true⟩] r := by
  intro h
  obtain ⟨-, hlt⟩ := ctxOutlives_imm_iff.mp h
  obtain ⟨δ, hδ⟩ := hsat
  obtain ⟨m, n, hm, hn, hmn⟩ := hlt δ hδ
  rw [hm] at hn
  cases hn
  simp only [Lifetime.SLife.Lt] at hmn
  omega

/-- **Variant (d)**: a row with a non-abortive operation answering a thunk fails BOXED-κ's
answer-type premise at every `@d`: `VOutlivesR` has no case for `U`. -/
theorem not_ansOutlives_thunk {Δ : LifeCtx} {d : Lifetime.Life} {S : Row} {o : OpSig} {C : CTy}
    (ho : o ∈ S) (hna : o.abort = false) (hB : o.B = .thunk C) : ¬ Row.AnsOutlives Δ d S := by
  intro h
  have h' := h o ho hna
  rw [hB] at h'
  cases h'

/-- **Variant (d), the repair**: an answer boxed at `⊤` outlives every defined `@d`. -/
theorem ansOutlives_boxTop {Δ : LifeCtx} {d : Lifetime.Life} {C : CTy} (hd : Δ.Defines d) :
    VOutlives Δ d (.box .top (.thunk C)) :=
  .box fun δ hδ => by
    obtain ⟨m, hm⟩ := hd δ hδ
    exact ⟨m, Lifetime.SLife.top, hm, rfl, by simp [Lifetime.SLife.Le, Lifetime.SLife.top]⟩

end BoCa.Fig16.LogRel.Core.BoxedKappaProgs

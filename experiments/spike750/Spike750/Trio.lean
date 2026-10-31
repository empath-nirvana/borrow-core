import Core.EffCancelTyped
import Core.Closed
import Spike750.Round2

/-!
# #750, level-triggered cancellation under cancel-by-resume

The cancelled state is the task handler's state: a flag cell that the clause of the cancellable
`await` (operation `0`) reads. Live, the clause hands `κ` out to the scheduler (`inr k`).
Cancelled, it resumes `κ` with `inr ()` at once. The canceller does two things: it sets the flag,
then resumes the stopped `κ` with `inr ()`. No clause clears the flag, so the scope stays
cancelled. A shielded wait is an operation of the same name whose clause does not read the flag
(`complete`, operation `2`, `1 ↠^lin 1`).

* **The law** (`await_cancelled`): in every context, at a memory where the flag is cancelled,
  `hnd (n, H) K[await_n]` runs to `hnd (n, H) K[raise_n (1, ())]` with the memory unchanged. The
  memory after the run is the one before it, so the law applies again at the next wait.
* **Typing**: the swallowing example has a `CDerives` derivation (`d_swallow`), so `fundamentalC`
  puts it in the relation, and its row is one `Row.ResumeOC` admits (`resumeOC_swallow`). The
  relation at a row quantifies over every answer at every stop, so no premise reads the
  scheduler's flag.
* **Runs**: the swallowing example, a retry loop, a `must_close` finaliser, and a shielded
  completion wait inside a finaliser. Each is run under the level-triggered scheduler and under
  the one-shot scheduler of round 2.

No rule, step, primitive or `PinLaw` field is added. Every term is a term of the kernel.
-/

namespace Spike750.Trio
open BoCa
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont hndE hndVal raiseE performE opPayload clauseAt capTag
  kappaC)
open BoCa.Lifetime (LifeVar LifeCtx)
open BoCa.Fig16.LogRel.Core.CancelIntercept
open Spike750.Runs (lit storeE dOwn clauseCancelled falsify)
open Spike750.Round2 (awaitF await0 cancelled complete hRetL clauseOut taskL resumeK)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-! ### The cancelled state -/

/-- The flag: `inl ()`, live. -/
def liveV : Val := Val.inj₁ Val.unit

/-- The flag: `inr ()`, cancelled. It is also the answer of a cancel. -/
def cancV : Val := Val.inj₂ Val.unit

/-- The live arm, `λk. inr k`: hand `κ` out to the scheduler. -/
def armLive : Expr := .lam (.inj₂ (.var 0))

/-- The cancelled arm, `λk. (k (inl ())) (inr ())`: resume `κ` with the cancel. -/
def armCanc : Expr := .lam (.app (.app (.var 0) (.val (Val.inj₁ Val.unit))) (.val cancV))

/-- The await clause at the flag cell `s`:
`λ(x, k). (case !s {inl _. λk. inr k | inr _. λk. k.1 (inr ())}) k`. -/
def stickyBody (s : Loc) : Expr :=
  .letpair (.var 0) (.app (.case (.app (.val (.prim .load)) (.val (Val.loc s))) armLive armCanc)
    (.var 0))

/-- The level-triggered await clause. -/
def stickyAwait (s : Loc) : Val := Val.lam (stickyBody s)

/-- `await_n`'s `case` on the answer. -/
def awaitCase (n : UInt32) : Expr := .case (.var 0) (.var 0) (raiseE (opArgE n 1 (.var 0)))

/-- `await_n` around its `perform`: `(λr. case r {…}) [·]`. -/
def awaitK (n : UInt32) : Kont := .appR (.val (Val.lam (awaitCase n))) .hole

theorem awaitE_plug (n : UInt32) :
    awaitE n = (awaitK n).plug (performE (.val (opPayload n 0 Val.unit))) := rfl

/-- The handler frame `hnd H [·]`. -/
def hndK (H : Val) : Kont := .appR (.app (.val (.prim .hnd)) (.val H)) .hole

theorem hndE_plug (H : Val) (e : Expr) : hndE H e = (hndK H).plug e := rfl

private theorem headIn {μ μ' : Heap} {a a' : Expr} (K : Kont) (h : Head (ℍ := ℍ) μ a μ' a') :
    Steps (ℍ := ℍ) μ (K.plug a) μ' (K.plug a') :=
  .one ((Step1.head h).plug K)

private theorem del_upd_none {μ : Heap} {l : Loc} {v : Val} (hl : μ l = none) :
    (μ.upd l v).del l = μ := by
  funext x
  by_cases e : x = l
  · subst e; rw [BoCa.BoLo.Heap.del_same, hl]
  · rw [BoCa.BoLo.Heap.del_other e, BoCa.BoLo.Heap.upd_other e]

/-- **`await = raise cancelled` in a cancelled scope.** Take a handler of `n` whose clause at
operation `0` is the level-triggered clause at the flag cell `s`, operation `0` linear, and a
memory where `s` holds `inr ()` (cancelled). Then in every context `K₀`, and for every `K` free of
`n`, `hnd (n, H) K[await_n]` runs to `hnd (n, H) K[raise_n (1, ())]`. `κ`'s cell is allocated at
a free `ℓ`, any such, and released on the resume, so the memory after the run is the memory
before it. The flag is still cancelled, so the next `await_n` under `H` raises again.
`[spec §29a]` -/
theorem await_cancelled {μ : Heap} {s ℓ : Loc} (hs : μ s = some cancV) (hℓ : μ ℓ = none)
    {n : UInt32} {qs hr hs' : Val} (hc : clauseAt hs'.1 0 = some (stickyAwait s))
    (htag : capTag qs.1 0 = Qual.lin.tag) (hH : closedAt 0 (hndVal n qs hr hs').1 = true)
    {K : Kont} (hK : K.HasHnd n = false) (hKc : closedAt 0 (K.plug .unit) = true) (K₀ : Kont) :
    Steps (ℍ := ℍ) μ (K₀.plug (hndE (hndVal n qs hr hs') (K.plug (awaitE n)))) μ
      (K₀.plug (hndE (hndVal n qs hr hs') (K.plug (raiseE (.val (opPayload n 1 Val.unit)))))) := by
  set H := hndVal n qs hr hs' with hHdef
  set K' := K.comp (awaitK n) with hK'def
  have hK' : K'.HasHnd n = false := by
    rw [hK'def, hasHnd_comp, hK]; rfl
  have hK'c : closedAt 0 (K'.plug .unit) = true := by
    rw [hK'def, Kont.plug_comp, closedAt_plug_iff 0, hKc]
    simp [awaitK, awaitCase, Kont.plug, closedAt, raiseE, opArgE, Expr.val, Val.lam, Val.prim,
      Val.i32]
  have hplug : K'.plug (performE (.val (opPayload n 0 Val.unit))) = K.plug (awaitE n) := by
    rw [hK'def, Kont.plug_comp, awaitE_plug]
  -- `[op]`, the allocation of `κ`'s cell, and `κ`'s β-step.
  have h₁ := catch_cell (ℍ := ℍ) (hr := hr) hℓ Val.unit (q := .lin) (by decide)
    (show clauseAt hs'.1 (0 : UInt32).toNat = some (stickyAwait s) from hc) hK' htag K₀
  rw [hplug] at h₁
  set μ₁ := μ.upd ℓ Val.unit with hμ₁
  have hκc : closedAt 0 (kappaC false ℓ H K') = true := closedAt_kappaC false ℓ hH hK'c
  have hκv : IsVal (kappaC false ℓ H K') := by unfold BoCa.BoLo.kappaC; exact .lam
  let κv : Val := ⟨kappaC false ℓ H K', hκv⟩
  have hκs : κv.shift 1 0 = κv := val_shift_closed hκc 1 0
  have hs₁ : μ₁ s = some cancV := by
    have hne : s ≠ ℓ := fun h => by rw [h, hℓ] at hs; cases hs
    rw [hμ₁, BoCa.BoLo.Heap.upd_other hne]; exact hs
  have hℓ₁ : μ₁ ℓ = some Val.unit := by rw [hμ₁, BoCa.BoLo.Heap.upd_same]
  -- The clause: its β-step, the `let (x, k)`, the read of the flag, the cancelled arm.
  have h₂ : Steps (ℍ := ℍ) μ₁
      (K₀.plug (.app (.val (stickyAwait s)) (.pair (.val Val.unit) (kappaC (cellAff .lin) ℓ H K'))))
      μ₁ (K₀.plug (.app (.app (kappaC false ℓ H K') (.val (Val.inj₁ Val.unit))) (.val cancV))) := by
    have e₁ := headIn (ℍ := ℍ) K₀ (Head.beta μ₁ (stickyBody s) (Val.pair Val.unit κv))
    have e₂ := headIn (ℍ := ℍ) K₀ (Head.letpair μ₁ Val.unit κv
      (.app (.case (.app (.val (.prim .load)) (.val (Val.loc s))) armLive armCanc) (.var 0)))
    have e₃ := headIn (ℍ := ℍ) (K₀.comp (.appL (.case .hole armLive armCanc) κv))
      (Head.load μ₁ s cancV hs₁)
    have e₄ := headIn (ℍ := ℍ) (K₀.comp (.appL .hole κv))
      (Head.case₂ μ₁ Val.unit armLive armCanc)
    have e₅ := headIn (ℍ := ℍ) K₀
      (Head.beta μ₁ (.app (.app (.var 0) (.val (Val.inj₁ Val.unit))) (.val cancV)) κv)
    simp only [Kont.plug_comp, Kont.plug] at e₃ e₄
    have r₁ : (stickyBody s).subst 0 (Val.pair Val.unit κv) =
        .letpair (.val (Val.pair Val.unit κv))
          (.app (.case (.app (.val (.prim .load)) (.val (Val.loc s))) armLive armCanc) (.var 0)) := by
      simp [stickyBody, armLive, armCanc, Expr.subst, Expr.val, Val.pair, Val.loc, Val.prim,
        Val.inj₁, Val.unit, cancV, Val.inj₂]
    have r₂ : ((Expr.app (.case (.app (.val (.prim .load)) (.val (Val.loc s))) armLive armCanc)
        (.var 0)).subst 0 (κv.shift 1 0)).subst 0 Val.unit =
        .app (.case (.app (.val (.prim .load)) (.val (Val.loc s))) armLive armCanc) (.val κv) := by
      rw [hκs]
      simp only [Expr.subst, if_true]
      rw [subst_closedAt κv.1 Val.unit hκc (le_refl 0)]
      simp [armLive, armCanc, Expr.subst, Expr.val, Val.loc, Val.prim, Val.inj₁, Val.unit, cancV,
        Val.inj₂]
    have r₄ : armCanc.subst 0 Val.unit = armCanc := by
      simp [armCanc, Expr.subst, Expr.val, Val.inj₁, Val.unit, cancV, Val.inj₂]
    have r₅ : (Expr.app (.app (.var 0) (.val (Val.inj₁ Val.unit))) (.val cancV)).subst 0 κv =
        .app (.app (.val κv) (.val (Val.inj₁ Val.unit))) (.val cancV) := by
      simp [Expr.subst, Expr.val, Val.inj₁, Val.unit, cancV, Val.inj₂]
    rw [r₁] at e₁
    rw [r₂] at e₂
    rw [r₄] at e₄
    rw [r₅] at e₅
    exact e₁.trans (e₂.trans (e₃.trans (e₄.trans e₅)))
  -- The resume: `κ`'s cell is released and `hnd H K'[inr ()]` runs.
  have h₃ := kappaC_resume (ℍ := ℍ) hℓ₁ false H K' cancV K₀
  rw [hμ₁, del_upd_none hℓ] at h₃
  -- `await_n`'s `case` takes the `inr` arm: `raise_n (1, ())`.
  have h₄ : Steps (ℍ := ℍ) μ (K₀.plug (hndE H (K'.plug (.val cancV)))) μ
      (K₀.plug (hndE H (K.plug (raiseE (.val (opPayload n 1 Val.unit)))))) := by
    have hK'p : ∀ e, K₀.plug (hndE H (K'.plug e)) =
        ((K₀.comp (hndK H)).comp K).plug ((awaitK n).plug e) := by
      intro e; rw [hK'def, Kont.plug_comp, Kont.plug_comp, Kont.plug_comp, hndE_plug]
    have hKp : ∀ e, K₀.plug (hndE H (K.plug e)) = ((K₀.comp (hndK H)).comp K).plug e := by
      intro e; rw [Kont.plug_comp, Kont.plug_comp, hndE_plug]
    rw [hK'p, hKp]
    have e₁ := headIn (ℍ := ℍ) ((K₀.comp (hndK H)).comp K) (Head.beta μ (awaitCase n) cancV)
    have e₂ := headIn (ℍ := ℍ) ((K₀.comp (hndK H)).comp K)
      (Head.case₂ μ Val.unit (.var 0) (raiseE (opArgE n 1 (.var 0))))
    have r₁ : (awaitCase n).subst 0 cancV =
        .case (.val (Val.inj₂ Val.unit)) (.var 0) (raiseE (opArgE n 1 (.var 0))) := by
      simp [awaitCase, Expr.subst, raiseE, opArgE, Expr.val, cancV, Val.inj₂, Val.unit, Val.prim,
        Val.i32]
    have r₂ : (raiseE (opArgE n 1 (.var 0))).subst 0 Val.unit =
        raiseE (.val (opPayload n 1 Val.unit)) := by
      simp [Expr.subst, raiseE, opArgE, Expr.val, Val.unit, Val.prim, Val.i32, opPayload,
        Val.pair]
    rw [r₁] at e₁
    rw [r₂] at e₂
    exact e₁.trans e₂
  exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- **A shielded wait reads no flag.** At operation `2` the handler's clause is `clauseOut`,
whatever the flag holds: the catch hands `κ` out at every memory, the flag's cell untouched. -/
theorem shield_catch {μ : Heap} {ℓ : Loc} (hℓ : μ ℓ = none) {n : UInt32} {qs hr hs' : Val}
    (hc : clauseAt hs'.1 2 = some clauseOut) (htag : capTag qs.1 2 = Qual.lin.tag)
    {K : Kont} (hK : K.HasHnd n = false) (K₀ : Kont) :
    Steps (ℍ := ℍ) μ
      (K₀.plug (hndE (hndVal n qs hr hs') (K.plug (performE (.val (opPayload n 2 Val.unit))))))
      (μ.upd ℓ Val.unit)
      (K₀.plug (.app (.val clauseOut)
        (.pair (.val Val.unit) (kappaC false ℓ (hndVal n qs hr hs') K)))) :=
  catch_cell (ℍ := ℍ) hℓ Val.unit (q := .lin) (by decide)
    (show clauseAt hs'.1 (2 : UInt32).toNat = some clauseOut from hc) hK htag K₀

/-! ### Non-vacuity of the law's premises -/

/-- The task handler of the runs: `await` level-triggered at the flag cell `0`, `cancelled`, and
the shielded `complete`. -/
def hsSticky : Val :=
  Val.pair (stickyAwait 0) (Val.pair clauseCancelled (Val.pair clauseOut Val.unit))

def qsTask : Val := qualsVal [.lin, .aff, .lin]

theorem clauseAt_sticky : clauseAt hsSticky.1 0 = some (stickyAwait 0) := by
  simp only [hsSticky, Val.pair, clauseAt]; rw [dif_pos (stickyAwait 0).2]

theorem clauseAt_shield : clauseAt hsSticky.1 2 = some clauseOut := by
  simp only [hsSticky, Val.pair, clauseAt]; rw [dif_pos clauseOut.2]

theorem capTag_task0 : capTag qsTask.1 0 = Qual.lin.tag := rfl

theorem capTag_task2 : capTag qsTask.1 2 = Qual.lin.tag := rfl

theorem closed_hndSticky : closedAt 0 (hndVal 1 qsTask hRetL hsSticky).1 = true := by decide

/-- The law's premises hold together: the flag cancelled at `0`, `κ`'s cell free at `1`, the empty
context. -/
theorem await_cancelled_inst :
    Steps (ℍ := ℍ) (BoCa.BoLo.Heap.upd (fun _ => none) 0 cancV)
      (hndE (hndVal 1 qsTask hRetL hsSticky) (awaitE 1)) (BoCa.BoLo.Heap.upd (fun _ => none) 0 cancV)
      (hndE (hndVal 1 qsTask hRetL hsSticky) (raiseE (.val (opPayload 1 1 Val.unit)))) :=
  await_cancelled (K := .hole) (K₀ := .hole) (ℓ := 1) (BoCa.BoLo.Heap.upd_same _ _ _)
    (by rw [BoCa.BoLo.Heap.upd_other (by decide)]) clauseAt_sticky capTag_task0 closed_hndSticky
    rfl rfl

/-- `shield_catch`'s premises hold at the same handler, at the flag cancelled. -/
theorem shield_catch_inst :
    Steps (ℍ := ℍ) (BoCa.BoLo.Heap.upd (fun _ => none) 0 cancV)
      (hndE (hndVal 1 qsTask hRetL hsSticky) (performE (.val (opPayload 1 2 Val.unit))))
      (BoCa.BoLo.Heap.upd (BoCa.BoLo.Heap.upd (fun _ => none) 0 cancV) 1 Val.unit)
      (.app (.val clauseOut) (.pair (.val Val.unit)
        (kappaC false 1 (hndVal 1 qsTask hRetL hsSticky) .hole))) :=
  shield_catch (K := .hole) (K₀ := .hole) (by rw [BoCa.BoLo.Heap.upd_other (by decide)])
    clauseAt_shield capTag_task2 rfl

/-! ### Typing: the swallowing example -/

/-- The raise of `3`, unrestricted: the finaliser's error. -/
abbrev raise3 : OpSig := rSig 3

/-- The task's row: `await` at the cancel row `{3}`, which the finaliser's raise puts there, and
`cancelled`. -/
abbrev rowSw : Row := [awaitF (finR 3), cancelled]

/-- `handle_3 (await_1 then x. x unwind raise_3) with {3 _ → ()}`. -/
def swallowInner : Expr :=
  hndExpr 3 [.unr] (.pair (.val CancelIntercept.idV) (.pair (.val (constC Val.unit)) (.val Val.unit)))
    (thenE (.var 0) (raiseU 3) (awaitE 1))

/-- The swallowing example: `swallowInner to u. u; await_1`. -/
def swallowBody : Expr := .app (.val (Val.lam (.seq (.var 0) (awaitE 1)))) swallowInner

/-- The `[then]` inside: `await_1 then x. x unwind raise_3` at `{3, 1⟨{3}⟩, cancelled}`. -/
theorem d_swallowThen {Δ : LifeCtx} :
    CDerives Δ [] (thenE (.var 0) (raiseU 3) (awaitE 1))
      (.comp (CTy.effOf ([raise3] ++ rowSw) .unit)) := by
  refine .effThen (Γ₁ := []) (Γ₂ := []) (A := .unit) (SM := [await0, cancelled])
    (SD := [raise3]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ rfl ?_ ?_ ?_
  · intro o ho
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ho
    rcases ho with rfl | rfl | rfl <;> decide
  · simp [Row.Uniq, rSig, awaitF, cancelled]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    have hF : ∀ X, FinLe (.ret .unit) X := fun X => by
      rw [FinLe]; right; exact ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf] at h⟩
    rcases ho with rfl | rfl
    · exact ⟨awaitF (finR 3), rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => hF _⟩
    · exact ⟨cancelled, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => hF _⟩
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨raise3, rfl, OpSig.LeF.refl _⟩
  · intro n i o o' hf hf' hr
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · obtain rfl : o' = awaitF (finR 3) := Option.some.inj (hf'.symm.trans rfl)
      rw [ThenLe]
      refine Or.inr ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf, awaitF] at h,
        fun n i o h => ?_⟩
      obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
      simp only [List.mem_singleton] at hm
      subst hm
      exact ⟨raise3, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩,
        fun hc => by simp [capB, rSig, VTy.isZero] at hc⟩
    · simp [OpSig.finRead, capB, cancelled, OpSig.awaitB, VTy.isZero] at hr
  · intro _ o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact ⟨fun h => by simp [OpSig.abort, awaitF] at h, fun _ => trivial⟩
    · exact ⟨fun _ => rfl, fun _ => trivial⟩
  · exact .effAwait .nil rfl rfl rfl rfl rfl rfl
  · exact .effSub (RowLe.nil _) (.ret (.var (.here .nil)))
  · exact .effRaise (o := raise3) rfl rfl .unit (.unitI (.cons .nil))

/-- `handle_3` around the `[then]`, at the task's row: `3` is not there, and the finaliser's
raise of `3` is its operation. -/
theorem d_swallowInner {Δ : LifeCtx} :
    CDerives Δ [] swallowInner (.comp (CTy.effOf rowSw .unit)) := by
  exact .effHandleV (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .zero)]) (fs := finsNil)
    .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_idV _ .unit) (.tensorI .nil (d_constC_raise _ (.unitI (.cons .nil)))
      (.unitI .nil)))
    (by decide) (by simp [awaitF, cancelled]) (by simp) rfl d_swallowThen

/-- **The swallowing example is typed** at the task's row: a cancel at the first `await` runs the
finaliser, whose raise of `3` supersedes `cancelled` and is caught inside the task, which then
reaches the second `await`. -/
theorem d_swallow {Δ : LifeCtx} : CDerives Δ [] swallowBody (.comp (CTy.effOf rowSw .unit)) := by
  refine .effLet (Γ₁ := []) (Γ₂ := []) (A := .unit) .nil (fun _ _ hs => absurd hs List.not_mem_nil)
    (fun _ _ hs => absurd hs List.not_mem_nil)
    d_swallowInner ?_
  exact .unitE (.left .nil) (.var (.here .nil))
    (.effAwait (.cons .nil) rfl rfl rfl rfl rfl rfl)

/-- **It is in the relation**, by the fundamental theorem as it stands. -/
theorem sem_swallow {Δ : LifeCtx} : SemC Δ [] swallowBody (CTy.effOf rowSw .unit) :=
  fundamentalC (d_swallow (Δ := Δ))

/-- **Its row is one the relaxed lend admits**: the await's cancel row `{3}` is any cancel row. -/
theorem resumeOC_swallow (x : LifeVar) : Row.ResumeOC rowSw x := Spike750.Round2.resumeOC_two x _

/-! ### `must_close` across a cancellable wait -/

/-- An owned cell is not `VTy.Drop`, so `[let]`'s `hW` refuses `await_n to _. close h` with `h`
live: a cancel's raise at the wait would leave `h` open. -/
theorem not_drops_ref : ¬ Ctx.Drops [⟨.ref (.int .w32), true⟩] := by
  intro h
  have := h ⟨_, true⟩ (List.mem_singleton.mpr rfl) rfl
  cases this

/-- The await row is weak (`cancelled` is affine), so `hW` asks for the drop. -/
theorem rowSw_weak : Row.Weak rowSw := ⟨cancelled, by simp, by decide⟩

/-! ### Termination

`Row.CancelTotal` reads each cancellable operation's cancel row: the finalisers a cancel at it runs
before the task handler's `cancelled` clause. Once a finaliser's raise is caught inside the task,
the task runs code that no cancel row records, up to its next wait. -/

/-- The swallowing task with a `Div` loop after the catch. -/
abbrev rowSwLoop : Row := [awaitF (finR 3), cancelled, tickSig]

/-- **`CancelTotal` holds at it.** The await's cancel row is `{3}`, which has no `Div`, but the
code after the catch may tick without reaching a wait. -/
theorem cancelTotal_swallowLoop : Row.CancelTotal rowSwLoop := by
  intro o ho hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact ⟨rfl, rfl⟩
  · simp [OpSig.finRead, capB, cancelled, OpSig.awaitB, VTy.isZero] at hr
  · exact absurd hr (by decide)

theorem divB_swallowLoop : Row.divB rowSwLoop = true := rfl

/-- **The replacement, under level-triggered cancellation.** A task row whose cancellable waits
have cancel rows `CancelTotal` reads, and which has no `Div` where it has a cancellable wait. At a
row without `Div` the relation is `ewpTS`, a least fixed point, so every path through the task's
stops is finite at every scheduler, the level-triggered one included. -/
def Row.CancelEnds (S : Row) : Prop :=
  Row.CancelTotal S ∧ ((∃ o ∈ S, o.awaitB = true) → Row.divB S = false)

theorem cancelEnds_swallow : Row.CancelEnds rowSw := by
  refine ⟨?_, fun _ => rfl⟩
  intro o ho hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · simp [OpSig.finRead, capB, cancelled, OpSig.awaitB, VTy.isZero] at hr

theorem not_cancelEnds_swallowLoop : ¬ Row.CancelEnds rowSwLoop := by
  intro h
  have := h.2 ⟨awaitF (finR 3), by simp, rfl⟩
  exact absurd this (by decide)

/-! ### Runs

Memory: the flag at `0`, a log cell at `1` (both allocated first), then the lend's cell. The
program answers `(r, log)`: the task's answer `r` (`inl v` done, `inl 7` the `cancelled` clause),
and the log's last value. -/

/-- `(λ_. (λ_. P) (alloc 0)) (alloc live)`, then `(r, free log)` and the flag freed. -/
def withState (P : Expr) : Expr :=
  .app (.val (Val.lam
    (.app (.val (Val.lam
      (.app (.val (Val.lam
        (.app (.val (Val.lam (.app (.val (Val.lam (.pair (.var 2) (.var 1))))
          (.app (.val (.prim .free)) (.val (Val.loc 0))))))
          (.app (.val (.prim .free)) (.val (Val.loc 1))))))
        P)))
      (.app (.val (.prim .alloc)) (lit 0)))))
    (.app (.val (.prim .alloc)) (.val liveV))

/-- The level-triggered cancel: set the flag, then resume the stopped `κ` with `inr ()`. -/
def cancelS (t : Expr) : Expr :=
  .case t (.inj₁ (.var 0))
    (.seq (storeE (.val (Val.loc 0)) (.val cancV)) (resumeK (.var 0) (.val cancV)))

/-- Serve one more hand-out at answer `a`. -/
def serve (a : Expr) (t : Expr) : Expr := .case t (.inj₁ (.var 0)) (resumeK (.var 0) a)

/-- Round 2's one-shot cancel: resume with `inr ()`, the flag left live. -/
def cancel1 (t : Expr) : Expr := serve (.val cancV) t

/-- The task, level-triggered. -/
def taskS (B : Expr) : Expr := taskL qsTask hsSticky B

/-- The task under round 2's scheduler: every `await` handed out. -/
def taskO (B : Expr) : Expr :=
  taskL qsTask (Val.pair clauseOut (Val.pair clauseCancelled (Val.pair clauseOut Val.unit))) B

/-- The answer `(inl i, log)`, no cell left. -/
def answers (e : Expr) (i l : UInt32) : Bool :=
  match eval e with
  | .value ⟨.pair (.inj₁ (.prim (.lit (.i32 a)))) (.prim (.lit (.i32 b))), _⟩ false =>
      a == i && b == l
  | _ => false

/-- The answer `(inl i, log)`, some cell left. -/
def answersLeak (e : Expr) (i l : UInt32) : Bool :=
  match eval e with
  | .value ⟨.pair (.inj₁ (.prim (.lit (.i32 a)))) (.prim (.lit (.i32 b))), _⟩ true =>
      a == i && b == l
  | _ => false

/-! #### 1. The swallowing example re-raises -/

/-- `swallowBody; 5`. -/
def bSwallow : Expr := .app (.val (Val.lam (.seq (.var 0) (lit 5)))) swallowBody

/-- **Level-triggered**: the first `await` is cancelled, the finaliser's raise of `3` is caught,
and the second `await` raises `cancelled` from the flag: the task ends in the `cancelled` clause. -/
theorem swallow_sticky : answers (withState (cancelS (taskS bSwallow))) 7 0 = true := by decide

/-- **One-shot (round 2)**: the second `await` is handed out and answered `inl ()`; the cancel is
lost and the task finishes normally with `5`. -/
theorem swallow_oneShot :
    answers (withState (serve (.val (Val.inj₁ Val.unit)) (cancel1 (taskO bSwallow)))) 5 0 = true := by
  decide

/-! #### 2. A retry loop that catches every error -/

/-- Attempt `j`: `handle_3 ((await_1 then x. x; 5 unwind raise_3)) with {ret v → inl v | 3 _ →
log := j; inr ()}`. -/
def attempt (j : UInt32) : Expr :=
  hndExpr 3 [.unr] (.pair (.val injlV) (.pair
      (.val (Val.lam (.seq (storeE (.val (Val.loc 1)) (lit j)) (.val (Val.inj₂ Val.unit)))))
      (.val Val.unit)))
    (thenE (.seq (.var 0) (lit 5)) (raiseU 3) (awaitE 1))

/-- Two attempts, then give up: `log := 3; await_1; 0`. -/
def bRetry : Expr :=
  .case (attempt 1) (.var 0)
    (.case (attempt 2) (.var 0)
      (.seq (storeE (.val (Val.loc 1)) (lit 3)) (.seq (awaitE 1) (lit 0))))

/-- **Level-triggered**: attempt 1 catches the cancel (log 1); attempt 2's `await` raises it again
and attempt 2 catches it (log 2); the give-up path's `await` raises it, and nothing catches it
(log 3, the `cancelled` clause). -/
theorem retry_sticky : answers (withState (cancelS (taskS bRetry))) 7 3 = true := by decide

/-- **One-shot**: attempt 1 catches the cancel (log 1), and attempt 2's `await` is answered
`inl ()`: attempt 2 succeeds with `5`. -/
theorem retry_oneShot :
    answers (withState (serve (.val (Val.inj₁ Val.unit)) (cancel1 (taskO bRetry)))) 5 1 = true := by
  decide

/-! #### 3. A `must_close` value closed on the cancel exit -/

/-- `(λh. await_1 then x. close h; 5 unwind close h) (alloc 42)`. -/
def bClose : Expr :=
  .app (.val (Val.lam (thenE (.app (.val (Val.lam (lit 5))) (.app (.val (.prim .free)) (.var 1)))
      (.app (.val (Val.lam (.val Val.unit))) (.app (.val (.prim .free)) (.var 1)))
      (awaitE 1))))
    (.app (.val (.prim .alloc)) (lit 42))

/-- **The finaliser closes `h` on the cancel exit**: the `cancelled` clause, no cell left. -/
theorem close_sticky : answers (withState (cancelS (taskS bClose))) 7 0 = true := by decide

/-- The finaliser that waits before it closes: `await_1 to _. close h`. -/
def bCloseLate : Expr :=
  .app (.val (Val.lam (thenE (.app (.val (Val.lam (lit 5))) (.app (.val (.prim .free)) (.var 1)))
      (.app (.val (Val.lam (.app (.val (Val.lam (.val Val.unit)))
        (.app (.val (.prim .free)) (.var 2))))) (awaitE 1))
      (awaitE 1))))
    (.app (.val (.prim .alloc)) (lit 42))

/-- **Waiting before the close leaves `h` open** under level-triggered cancellation: the
finaliser's `await` raises before the close. Typing refuses this finaliser (`not_drops_ref`,
`rowSw_weak`). -/
theorem closeLate_sticky : answersLeak (withState (cancelS (taskS bCloseLate))) 7 0 = true := by
  decide

/-! #### 4. A shielded completion wait inside a finaliser -/

/-- `await_1 then x. x; 5 unwind (complete_1; log := 42)`. -/
def bShield : Expr :=
  thenE (.seq (.var 0) (lit 5))
    (.seq (performE (opArgE 1 2 .unit)) (storeE (.val (Val.loc 1)) (lit 42))) (awaitE 1)

/-- **The shielded wait completes**: after the cancel, the finaliser's `complete` is handed out,
the scheduler answers it (the completion arrived), and the finaliser goes on (log 42) before the
`cancelled` clause. -/
theorem shield_sticky :
    answers (withState (serve (.val Val.unit) (cancelS (taskS bShield)))) 7 42 = true := by decide

/-- The same finaliser with `await` in place of the shielded wait. -/
def bUnshielded : Expr :=
  thenE (.seq (.var 0) (lit 5)) (.seq (awaitE 1) (storeE (.val (Val.loc 1)) (lit 42))) (awaitE 1)

/-- **An unshielded wait in the finaliser raises at once**: the flag is cancelled, so the
finaliser's `await` raises before the write (log 0). -/
theorem unshielded_sticky :
    answers (withState (serve (.val Val.unit) (cancelS (taskS bUnshielded)))) 7 0 = true := by
  decide

#eval falsify (withState (cancelS (taskS bSwallow)))
#eval falsify (withState (cancelS (taskS bRetry)))
#eval falsify (withState (serve (.val Val.unit) (cancelS (taskS bShield))))

end Spike750.Trio

import Core.EffCancelTyped
import Core.Closed
import Core.Decl
import Core.PinFundamental

/-!
# Core — cancellable waits and level-triggered cancellation  `[spec §29a]`

A cancellable wait is an operation marked `rc` (`OpSig.Cancellable`: marked, `1 ↠^lin 1 ⊕ 1`),
performed only by `[await-c]` (`CDerives.effAwait`), which raises the marked cancel target
(`OpSig.CancelTarget`) on the answer `inr ()`. A cancel is a resume with `inr ()`. The marker is
read by typing only: `[perform]` and `[raise]` refuse a marked operation, and the relation and the
machine do not read it (`semC_effOf_rc`).

The cancelled state is the task handler's: level-triggered cancellation needs no kernel rule.

| fact | statement |
|---|---|
| `[await-c]` types `await_n` | `d_await` |
| `[perform]` and `[raise]` refuse the marked pair | `perform_refuses_await`, `raise_refuses_cancelled` |
| R1's cancel-path row | `resumeOC_await`; a marked `tick` is refused (`not_resumeOC_markedTick`), so is another abortive operation (`not_resumeOC_raise`) |
| an `await` row cancels | `Row.cancels_of_await` |
| a value with no derived drop is not held across an `await` by `[let]` | `let_refuses_decl_across_await` |
| `[perform]`/`[raise]` refuse the marked pair at every row that finds it | `not_der_perform_await`, `not_der_raise_cancelled` |
| `effThenDiv` reached: a cancel unwinding through a ticking finaliser; a closed program | `d_thenTickAwait`, `d_thenDivFuel` |
| a cell held across an `await` under a finaliser that frees it is typed | `d_closeOnCancel` |
| in a cancelled scope `await = raise cancelled`, memory unchanged | `await_cancelled`, `await_cancelled_inst` |
| a shielded wait reads no flag | `shield_catch`, `shield_catch_inst` |
| `cancelled_n` is not caught inside the task | `cancelled_not_caught` |
| a finaliser's raise caught inside the task is typed, and in the relation | `d_swallow`, `sem_swallow`, `resumeOC_swallow` |
| `CancelTotal`, `CancelEnds`, decided | `Row.cancelTotalB_iff`, `Row.cancelEndsB_iff`, with examples either way |
| runs under the level-triggered clause, by `eval` | `swallow_sticky`, `retry_sticky`, `close_sticky`, `shield_sticky`, `unshielded_sticky` |
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.AwaitCancel
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont hndE hndVal raiseE performE opPayload clauseAt capTag
  kappaC)
open BoCa.Lifetime (LifeVar LifeCtx)
open BoCa.Fig16.LogRel.Core.CancelIntercept (idV constC raiseU rSig finR d_idV d_constC_raise)
open BoCa.Fig16.LogRel.Core.EffPrograms (Flag)
open BoCa.Programs (alloc' free')
open BoCa.Fig16.LogRel.Core.Inversions (der_performJ der_raiseJ JR.rowLe)

/-! ### The marked pair at the name `1` -/

/-- `await : 1 ↠^lin 1 ⊕ 1`, marked, at the name `1`, its cancel row `F`. -/
def awaitF (F : CTy) : OpSig := ⟨1, 0, .lin, .unit, .sum .unit .unit, F, true⟩

/-- `await` at the empty cancel row. -/
abbrev await0 : OpSig := awaitF (.ret .unit)

/-- `cancelled : 1 ↠^cancel 0`, marked: the cancel target. -/
def cancelled : OpSig := ⟨1, 1, .cancel, .unit, .zero, .ret .unit, true⟩

/-- A shielded wait `complete : 1 ↠^lin 1` at the name `1`, operation `2`: unmarked. -/
def complete : OpSig := ⟨1, 2, .lin, .unit, .unit, .ret .unit, false⟩

/-- `await_1`'s own row. -/
abbrev rowAwait : Row := [await0, cancelled]

theorem cancellable_await (F : CTy) : (awaitF F).Cancellable := ⟨rfl, rfl, rfl⟩

theorem cancelTarget_cancelled : cancelled.CancelTarget := ⟨rfl, rfl, rfl⟩

/-- **`[await-c]` types `await_1`** at its row.  `[spec §29a]` -/
theorem d_await {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (awaitE 1) (.comp (CTy.effOf rowAwait .unit)) :=
  .effAwait hΓ rfl (cancellable_await _) rfl rfl cancelTarget_cancelled

/-- `[perform]`'s premise `hac` fails at the cancellable wait. -/
theorem perform_refuses_await (F : CTy) : ¬ (awaitF F).rc = false := by simp [awaitF]

/-- `[raise]`'s premise `hrc` fails at the cancel target. -/
theorem raise_refuses_cancelled : ¬ cancelled.rc = false := by simp [cancelled]

/-- **`[perform]` refuses the cancellable wait at every row it is read at**: a plain `perform` of
`(1, 0)` has no derivation at a row whose `(1, 0)` is the marked `await`, at any answer. `[sub]`
keeps the marker (`OpSig.Sig`), and `[perform]` asks for none.  `[spec §29a]` -/
theorem not_der_perform_await {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {S : Row} {B : VTy}
    (hS : Row.find S 1 0 = some (awaitF (.ret .unit)) ∨ ∃ F, Row.find S 1 0 = some (awaitF F)) :
    ¬ CDerives Δ Γ (performE (opArgE 1 0 V)) (.comp (CTy.effOf S B)) := by
  intro h
  obtain ⟨j₀, ⟨S₀, o, hf, -, hrc, rfl⟩, hr⟩ := der_performJ h 1 0 V rfl
  obtain ⟨o', hf', hle⟩ := JR.rowLe hr 1 0 o hf
  have hF : ∃ F, Row.find S 1 0 = some (awaitF F) := hS.elim (fun h => ⟨_, h⟩) id
  obtain ⟨F, hF⟩ := hF
  rw [hF] at hf'; cases hf'
  have := hle.1.rc_eq
  rw [hrc] at this; cases this

/-- **`[raise]` refuses the cancel target at every row it is read at**: a plain `raise` of `(1, 1)`
has no derivation at a row whose `(1, 1)` is the marked `cancelled`.  `[spec §29a]` -/
theorem not_der_raise_cancelled {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {S : Row} {B : VTy}
    (hS : Row.find S 1 1 = some cancelled) :
    ¬ CDerives Δ Γ (raiseE (opArgE 1 1 V)) (.comp (CTy.effOf S B)) := by
  intro h
  obtain ⟨j₀, ⟨S₀, o, B₀, hf, -, hrc, rfl⟩, hr⟩ := der_raiseJ h 1 1 V rfl
  obtain ⟨o', hf', hle⟩ := JR.rowLe hr 1 1 o hf
  rw [hS] at hf'; cases hf'
  have := hle.1.rc_eq
  rw [hrc] at this; cases this

theorem not_der_perform_rowAwait {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {B : VTy} :
    ¬ CDerives Δ Γ (performE (opArgE 1 0 V)) (.comp (CTy.effOf rowAwait B)) :=
  not_der_perform_await (.inl rfl)

theorem not_der_raise_rowAwait {Δ : LifeCtx} {Γ : Ctx VTy} {V : Expr} {B : VTy} :
    ¬ CDerives Δ Γ (raiseE (opArgE 1 1 V)) (.comp (CTy.effOf rowAwait B)) :=
  not_der_raise_cancelled rfl

/-- The shielded wait is performed by `[perform]`. -/
theorem d_complete {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) :
    CDerives Δ Γ (performE (opArgE 1 2 (.val .unit))) (.comp (CTy.effOf [complete] .unit)) :=
  .effPerform (o := complete) rfl rfl rfl (.unitI hΓ)

/-! ### R1's row on the cancel path -/

/-- **R1 admits a lend held across the marked pair**, at any cancel row of the wait. -/
theorem resumeOC_await (x : LifeVar) (F : CTy) : Row.ResumeOC [awaitF F, cancelled] x := by
  refine ⟨fun o ho => ?_, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact .inr (.inl ⟨cancellable_await F, rfl, by simp [awaitF], fun h => by simp [awaitF, VFree] at h,
      fun _ _ => .unit, trivial⟩)
  · exact .inr (.inr ⟨cancelTarget_cancelled, rfl, rfl, by decide, awaitF F, rfl,
      cancellable_await F⟩)

/-- `R1` as it was (`Row.ResumeO`) refuses the pair: the answer `1 ⊕ 1`. -/
theorem not_resumeO_await (x : LifeVar) (F : CTy) : ¬ Row.ResumeO [awaitF F, cancelled] x := by
  intro h
  have := (h (awaitF F) (by simp)).2.2.2.1
  simp [awaitF] at this

/-- `Div`'s `tick`, marked. -/
def markedTick : OpSig := { tickSig with rc := true }

/-- **A marked `tick` is refused**: the row holds `Div`. -/
theorem not_resumeOC_markedTick (x : LifeVar) : ¬ Row.ResumeOC [markedTick] x := fun h => by
  have := h.2
  simp [markedTick, Row.divB, CTy.effOf, CTy.divAt, tickSig, tickB, VTy.isUnitB,
    VTy.isNextB, nextTy] at this

/-- An abortive operation that is not a cancel target. -/
def raise2 : OpSig := ⟨2, 1, .cancel, .unit, .zero, .ret .unit, false⟩

/-- **Another abortive operation is refused** (OQ-1 stays closed for it). -/
theorem not_resumeOC_raise (x : LifeVar) : ¬ Row.ResumeOC [awaitF (.ret .unit), raise2] x := by
  intro h
  rcases h.1 raise2 (by simp) with h₁ | h₁ | h₁
  · simp [OpSig.abort, raise2, VTy.isZero] at h₁
  · exact absurd h₁.1.1 (by simp [raise2])
  · exact absurd h₁.1.1 (by simp [raise2])

/-! ### A value with no derived drop across a cancellable wait -/

/-- **A row that admits `[await-c]` at some name cancels**: its cancel target is abortive, so not
`lin`. `[let]`'s `hW` then asks the context held across the wait to be `OwnFree`. -/
theorem Row.cancels_of_await {S : Row} {n : UInt32} {c : OpSig} (hfc : Row.find S n 1 = some c)
    (hc : c.CancelTarget) : S.Cancels := by
  refine ⟨c, (Row.find_mem hfc).1, fun hq => ?_⟩
  have := hc.2.1
  simp [OpSig.abort, hq] at this

/-- **`[let]` refuses a value with no derived drop held across a cancellable wait**: at a row with
a cancel target, `hW` asks for `OwnFree`, which a declared type with no derived drop is not
(`decl_not_ownFree`). The way out is a finaliser that consumes it, on every exit, the cancel
included (`d_closeOnCancel` for a cell).  `[spec §29a]` -/
theorem let_refuses_decl_across_await {S : Row} {n : UInt32} {c : OpSig}
    (hfc : Row.find S n 1 = some c) (hc : c.CancelTarget) {A : VTy} {Γ₂ : Ctx VTy}
    (hm : ⟨declTy A, true⟩ ∈ Γ₂) : ¬ (S.Cancels → Γ₂.OwnFree) := fun hW =>
  decl_not_ownFree A (hW (Row.cancels_of_await hfc hc) _ hm rfl)

/-- A cell is not `OwnFree` either: `[let]` refuses it across the wait in the same way. -/
theorem let_refuses_ref_across_await {S : Row} {n : UInt32} {c : OpSig}
    (hfc : Row.find S n 1 = some c) (hc : c.CancelTarget) (A : VTy) :
    ¬ (S.Cancels → Ctx.OwnFree [⟨.ref A, true⟩]) := fun hW => by
  have := hW (Row.cancels_of_await hfc hc) _ (List.mem_singleton.mpr rfl) rfl
  cases this

theorem not_unrD_rowAwait : ¬ Row.UnrD rowAwait := by
  rintro ⟨o, ho, hu⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · rcases hu with hu | ⟨hc, -⟩
    · cases hu
    · simp [capB, awaitF] at hc
  · rcases hu with hu | ⟨hc, -⟩
    · cases hu
    · simp [capB, cancelled, VTy.isZero] at hc

/-- **A cell held across a cancellable wait, freed on every exit**:
`r ← alloc (inj₁ ()); await_1 then x. drop (free r); x unwind drop (free r)`. The finaliser frees
the cell on the `cancelled` unwind, the continuation on the normal exit.  `[spec §29a]` -/
theorem d_closeOnCancel {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ
      (bindE (.app alloc' (.inj₁ unit'))
        (thenE (.seq (dropB (.app free' (.var 1))) (.var 0)) (dropB (.app free' (.var 1)))
          (awaitE 1)))
      (.comp (CTy.effOf rowAwait .unit)) := by
  refine .bind (A := .ref Flag) (deadSplit hΓ)
    (.ret (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead)))) ?_
  refine CDerives.effThenA (A := .unit) (.right (deadSplit hΓ))
    (by intro o ho; simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
        rcases ho with rfl | rfl <;> decide)
    (by simp [Row.Uniq, awaitF, cancelled]) (fun h => absurd h not_unrD_rowAwait)
    (d_await (Ctx.Dead.cons hΓ)) ?_ ?_
  · refine .unitE (.right (.left (deadSplit hΓ)))
      (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead)) ?_
    exact .effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h) (.ret (.var (by csolo)))
  · show CDerives _ _ _ (.comp (.ret .unit))
    exact .ret (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead))

/-! ### Level-triggered cancellation: the law

The cancelled state is a flag cell that the task handler's `await` clause reads. Live, the clause
hands `κ` out to the scheduler (`inr k`); cancelled, it resumes `κ` with `inr ()` at once. -/

/-- The flag: `inl ()`, live. -/
def liveV : Val := Val.inj₁ Val.unit

/-- The flag: `inr ()`, cancelled. It is also the answer of a cancel. -/
def cancV : Val := Val.inj₂ Val.unit

/-- The live arm, `λk. inr k`. -/
def armLive : Expr := .lam (.inj₂ (.var 0))

/-- The cancelled arm, `λk. (k (inl ())) (inr ())`. -/
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

/-- `await_n` around its `perform`. -/
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

/-- **Law 5c: in a cancelled scope `await = raise cancelled`.** A handler of `n` whose clause at
operation `0` is the level-triggered clause at the flag cell `s`, operation `0` linear, at a memory
where `s` holds `inr ()`: in every context `K₀`, for every `K` free of `n`,
`hnd (n, H) K[await_n]` runs to `hnd (n, H) K[raise_n (1, ())]`. `κ`'s cell is allocated at a free
`ℓ` and released on the resume, so the memory after the run is the one before it, and the next
`await_n` under `H` raises again.  `[spec §19, §29a]` -/
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
  have h₂ : Steps (ℍ := ℍ) μ₁
      (K₀.plug (.app (.val (stickyAwait s)) (.pair (.val Val.unit) (kappaC (cellCancel .lin) ℓ H K'))))
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
  have h₃ := kappaC_resume (ℍ := ℍ) hℓ₁ false H K' cancV K₀
  rw [hμ₁, del_upd_none hℓ] at h₃
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

/-- A clause that hands its continuation out: `λ(x, k). inr k`. -/
def clauseOut : Val := Val.lam (.letpair (.var 0) (.inj₂ (.var 0)))

/-- **A shielded wait reads no flag.** At operation `2` the handler's clause hands `κ` out at every
memory, the flag's cell untouched.  `[spec §29a]` -/
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

/-- **No handler of `n` sits between `await_n`'s raise and the wait's handler**: `[await-c]` raises
in the same context `K` as the wait, and `K` (so `K` around `await_n`'s `case`) is free of `n`, as
`catch_step` required of the wait. With `catch_abort`, the raise is caught by the handler that
caught the wait; that step lemma is not restated here. -/
theorem cancelled_not_caught {K : Kont} {n : UInt32} (hK : K.HasHnd n = false) :
    (K.comp (awaitK n)).HasHnd n = false := by
  rw [hasHnd_comp, hK]; rfl

/-! ### Non-vacuity of the laws' premises -/

/-- The clause for the cancel target: `λ_. inl 7`, "cancelled". -/
def clauseCancelled : Val := Val.lam (.inj₁ (Val.i32 7).1)

/-- The answer clause: `λ(c, v). free c; inl v`. -/
def hRetL : Val :=
  Val.lam (.letpair (.var 0) (.app (.lam (.inj₁ (.var 1))) (.app (.prim .free) (.var 1))))

/-- The task handler: `await` level-triggered at the flag cell `0`, `cancelled`, and the shielded
`complete`. -/
def hsSticky : Val :=
  Val.pair (stickyAwait 0) (Val.pair clauseCancelled (Val.pair clauseOut Val.unit))

def qsTask : Val := qualsVal [.lin, .cancel, .lin]

theorem clauseAt_sticky : clauseAt hsSticky.1 0 = some (stickyAwait 0) := by
  simp only [hsSticky, Val.pair, clauseAt]; rw [dif_pos (stickyAwait 0).2]

theorem clauseAt_shield : clauseAt hsSticky.1 2 = some clauseOut := by
  simp only [hsSticky, Val.pair, clauseAt]; rw [dif_pos clauseOut.2]

theorem capTag_task0 : capTag qsTask.1 0 = Qual.lin.tag := rfl

theorem capTag_task2 : capTag qsTask.1 2 = Qual.lin.tag := rfl

theorem closed_hndSticky : closedAt 0 (hndVal 1 qsTask hRetL hsSticky).1 = true := by decide

/-- `await_cancelled`'s premises hold together: the flag cancelled at `0`, `κ`'s cell free at `1`,
the empty context. -/
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

/-! ### Typing: a finaliser's raise caught inside the task -/

/-- The finaliser's error, `raise 3`, unrestricted. -/
abbrev raise3 : OpSig := rSig 3

/-- The task's row: `await` at the cancel row `{3}`, which the finaliser's raise puts there, and
`cancelled`. -/
abbrev rowSw : Row := [awaitF (finR 3), cancelled]

/-- `handle_3 (await_1 then x. x unwind raise_3) with {3 _ → ()}`. -/
def swallowInner : Expr :=
  hndExpr 3 [.unr] (.pair (.val idV) (.pair (.val (constC Val.unit)) (.val Val.unit)))
    (thenE (.var 0) (raiseU 3) (awaitE 1))

/-- The swallowing example: `swallowInner to u. u; await_1`. -/
def swallowBody : Expr := .app (.val (Val.lam (.seq (.var 0) (awaitE 1)))) swallowInner

/-- The `[then]` inside: `await_1 then x. x unwind raise_3` at `{3, 1⟨{3}⟩, cancelled}`. -/
theorem d_swallowThen {Δ : LifeCtx} :
    CDerives Δ [] (thenE (.var 0) (raiseU 3) (awaitE 1))
      (.comp (CTy.effOf ([raise3] ++ rowSw) .unit)) := by
  refine .effThen (Γ₁ := []) (Γ₂ := []) (A := .unit) (SM := [await0, cancelled])
    (SD := [raise3]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ (by decide) ?_ ?_ ?_
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
    · exact ⟨awaitF (finR 3), rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => hF _⟩
    · exact ⟨cancelled, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => hF _⟩
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
      exact ⟨raise3, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
        fun hc => by simp [capB, rSig, VTy.isZero] at hc⟩
    · simp [OpSig.finRead, capB, cancelled, OpSig.abort, VTy.isZero] at hr
  · intro _ o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact ⟨fun h => by simp [OpSig.abort, awaitF] at h, fun _ => trivial⟩
    · exact ⟨fun _ => rfl, fun _ => trivial⟩
  · exact .effAwait .nil rfl (cancellable_await _) rfl rfl cancelTarget_cancelled
  · exact .effSub (RowLe.nil _) (.ret (.var (.here .nil)))
  · exact .effRaise (o := raise3) rfl rfl rfl .unit (.unitI (.cons .nil))

/-- `handle_3` around the `[then]`, at the task's row. -/
theorem d_swallowInner {Δ : LifeCtx} :
    CDerives Δ [] swallowInner (.comp (CTy.effOf rowSw .unit)) := by
  exact .effHandleV (cs := rcsNil) (Γ₁ := []) (Γ₂ := []) (E := [(.unr, .unit, .zero)])
    (fs := finsNil) .nil .nil (.pair (.val _) (.pair (.val _) (.val _)))
    (.tensorI .nil (d_idV _ .unit) (.tensorI .nil (d_constC_raise _ (.unitI (.cons .nil)))
      (.unitI .nil)))
    (by decide) (by simp [awaitF, cancelled]) (by simp) rfl d_swallowThen

/-- **The swallowing example is typed** at the task's row: a cancel at the first `await` runs the
finaliser, whose raise of `3` supersedes `cancelled` and is caught inside the task, which then
reaches the second `await`, where a level-triggered handler raises `cancelled` again. -/
theorem d_swallow {Δ : LifeCtx} : CDerives Δ [] swallowBody (.comp (CTy.effOf rowSw .unit)) := by
  refine .effLet (Γ₁ := []) (Γ₂ := []) (A := .unit) .nil (fun _ _ hs => absurd hs List.not_mem_nil)
    (fun _ _ hs => absurd hs List.not_mem_nil)
    d_swallowInner ?_
  exact .unitE (.left .nil) (.var (.here .nil))
    (.effAwait (.cons .nil) rfl (cancellable_await _) rfl rfl cancelTarget_cancelled)

/-- **It is in the relation**, by `fundamentalC` as it stands. -/
theorem sem_swallow {Δ : LifeCtx} : SemC (ℍ := ℍ) Δ [] swallowBody (CTy.effOf rowSw .unit) :=
  fundamentalC (d_swallow (Δ := Δ))

/-- **Its row is one R1 admits.** -/
theorem resumeOC_swallow (x : LifeVar) : Row.ResumeOC rowSw x := resumeOC_await x _

end BoCa.Fig16.LogRel.Core.AwaitCancel

namespace BoCa.Fig16.LogRel.Core

/-! ### The cancel row where termination is read -/

/-- A cancel row bounded at every depth: not `⊤`, no `Div`, and so at each entry whose cancel row
typing reads. -/
def CancelTotalC (F : CTy) : Prop :=
  F.isTop = false ∧ Row.divB F.rowOf = false ∧
    ∀ o ∈ F.rowOf, o.finRead = true → CancelTotalC o.fin
termination_by sizeOf F
decreasing_by exact rowOf_fin_lt F (by assumption)

/-- Every entry of the row whose cancel row typing reads has a cancel row bounded at every depth.
A typing-only predicate: the relation does not read a marked operation's cancel row.
`[spec §29a]` -/
def Row.CancelTotal (S : Row) : Prop := ∀ o ∈ S, o.finRead = true → CancelTotalC o.fin

/-- `CancelTotal`, and no `Div` where the row has a cancellable wait. A theorem target, not a
premise of any rule.  `[spec §29a]` -/
def Row.CancelEnds (S : Row) : Prop :=
  Row.CancelTotal S ∧ ((∃ o ∈ S, o.Cancellable) → Row.divB S = false)

/-- `CancelTotalC`, decided. -/
def cancelTotalCB (F : CTy) : Bool :=
  !F.isTop && !Row.divB F.rowOf &&
    F.rowOf.attach.all fun ⟨o, _⟩ => !o.finRead || cancelTotalCB o.fin
termination_by sizeOf F
decreasing_by exact rowOf_fin_lt F (by assumption)

theorem cancelTotalCB_iff (F : CTy) : cancelTotalCB F = true ↔ CancelTotalC F := by
  rw [cancelTotalCB, CancelTotalC]
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_attach, true_implies,
    Subtype.forall, Bool.or_eq_true]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    refine ⟨h₁, h₂, fun o ho hr => ?_⟩
    rcases h₃ o ho with h | h
    · rw [h] at hr; cases hr
    · exact (cancelTotalCB_iff o.fin).mp h
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨⟨h₁, h₂⟩, fun o ho => ?_⟩
    cases hr : o.finRead
    · exact .inl rfl
    · exact .inr ((cancelTotalCB_iff o.fin).mpr (h₃ o ho hr))
termination_by sizeOf F
decreasing_by all_goals exact rowOf_fin_lt F (by assumption)

/-- `Row.CancelTotal`, decided. -/
def Row.cancelTotalB (S : Row) : Bool := S.all fun o => !o.finRead || cancelTotalCB o.fin

theorem Row.cancelTotalB_iff (S : Row) : S.cancelTotalB = true ↔ S.CancelTotal := by
  simp only [Row.cancelTotalB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Row.CancelTotal]
  constructor
  · intro h o ho hr
    rcases h o ho with h | h
    · rw [h] at hr; cases hr
    · exact (cancelTotalCB_iff _).mp h
  · intro h o ho
    cases hr : o.finRead
    · exact .inl rfl
    · exact .inr ((cancelTotalCB_iff _).mpr (h o ho hr))

/-- `Row.CancelEnds`, decided. -/
def Row.cancelEndsB (S : Row) : Bool :=
  S.cancelTotalB && (!S.any (·.cancellableB) || !Row.divB S)

theorem Row.cancelEndsB_iff (S : Row) : S.cancelEndsB = true ↔ S.CancelEnds := by
  simp only [Row.cancelEndsB, Bool.and_eq_true, Row.cancelTotalB_iff, Bool.or_eq_true,
    Bool.not_eq_true', List.any_eq_false, Row.CancelEnds]
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, fun ⟨o, ho, hc⟩ => ?_⟩
    rcases h₂ with h | h
    · exact absurd ((OpSig.cancellableB_iff o).mpr hc) (by simpa using h o ho)
    · exact h
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, ?_⟩
    cases hd : Row.divB S
    · exact .inr rfl
    · left
      intro o ho hc
      have := h₂ ⟨o, ho, (OpSig.cancellableB_iff o).mp (by simpa using hc)⟩
      rw [hd] at this; cases this

end BoCa.Fig16.LogRel.Core

namespace BoCa.Fig16.LogRel.Core.AwaitCancel
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont hndE hndVal raiseE performE opPayload clauseAt capTag
  kappaC)
open BoCa.Lifetime (LifeVar LifeCtx)
open BoCa.Fig16.LogRel.Core.CancelIntercept (idV constC raiseU rSig finR d_idV d_constC_raise)
open BoCa.Fig16.LogRel.Core.EffPrograms (Flag adequacyD_obs)
open BoCa.Programs (alloc' free')

theorem cancelTotalC_nil : CancelTotalC (.ret .unit) := by
  rw [CancelTotalC]; exact ⟨rfl, rfl, fun o ho => by simp [CTy.rowOf] at ho⟩

theorem cancelTotalC_finR3 : CancelTotalC (finR 3) := by
  rw [CancelTotalC]
  refine ⟨rfl, by decide, fun o ho hr => ?_⟩
  simp only [finR, CTy.rowOf_effOf, List.mem_singleton] at ho
  subst ho; simp [OpSig.finRead, capB, rSig, VTy.isZero, OpSig.abort] at hr

theorem not_finRead_cancelled : cancelled.finRead = false := by
  simp [OpSig.finRead, capB, cancelled, VTy.isZero, OpSig.abort]

/-- `CancelTotal` holds where the wait's cancel row is `F 1`. -/
theorem cancelTotal_rowAwait : Row.CancelTotal rowAwait := by
  intro o ho hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact cancelTotalC_nil
  · rw [not_finRead_cancelled] at hr; cases hr

/-- `CancelTotal` fails where the wait's cancel row holds `Div`. -/
theorem not_cancelTotal_divFin :
    ¬ Row.CancelTotal [awaitF (CTy.effOf [tickSig] .unit), cancelled] := by
  intro h
  have h₁ := h (awaitF (CTy.effOf [tickSig] .unit)) (by simp) rfl
  rw [CancelTotalC] at h₁
  exact absurd h₁.2.1 (by simp [awaitF, CTy.rowOf_effOf, Row.divB_tick])

theorem cancelTotal_rowSw : Row.CancelTotal rowSw := by
  intro o ho hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact cancelTotalC_finR3
  · rw [not_finRead_cancelled] at hr; cases hr

/-- `CancelEnds` holds at the swallowing row. -/
theorem cancelEnds_swallow : Row.CancelEnds rowSw := ⟨cancelTotal_rowSw, fun _ => by decide⟩

/-- The swallowing row with a `tick` after the catch. -/
abbrev rowSwLoop : Row := [awaitF (finR 3), cancelled, tickSig]

/-- **`CancelTotal` holds at it, `CancelEnds` does not**: the wait's cancel row has no `Div`, but
the row ticks. -/
theorem cancelTotal_swallowLoop : Row.CancelTotal rowSwLoop := by
  intro o ho hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact cancelTotalC_finR3
  · rw [not_finRead_cancelled] at hr; cases hr
  · simp [OpSig.finRead, capB, tickSig, OpSig.abort] at hr

theorem not_cancelEnds_swallowLoop : ¬ Row.CancelEnds rowSwLoop := by
  intro h
  have := h.2 ⟨awaitF (finR 3), by simp, cancellable_await _⟩
  revert this
  simp [Row.divB, CTy.effOf, CTy.divAt, tickSig, tickB, VTy.isUnitB, VTy.isNextB, awaitF,
    cancelled, finR, rSig, divEff]

/-! ### The scheduler's clause, typed by passing the state along

The immediate scheduler: the handler's answer is `U(Flag ⊸ F Flag)`, the cancelled flag passed in
as the state, as `take n` passes its count (`EffPrograms.takeProg`). Its `await` clause reads the
flag and resumes `κ` with it at once: `inl ()` goes on, `inr ()` cancels. The answer `inl ()` is
"finished", `inr ()` "cancelled". Started at the cancelled flag around the swallowing example, every
`await` raises `cancelled`: the run ends at `inr ()`. -/

/-- The scheduler's answer, the flag passed in: `U(Flag ⊸ F Flag)`. -/
abbrev StR : VTy := .thunk (.arr Flag (.ret Flag))

/-- The handled effect: `await` and its cancel target. -/
abbrev Esched : List (Qual × VTy × VTy) := [(.lin, .unit, .sum .unit .unit), (.cancel, .unit, .zero)]

/-- The cancel rows: `{3}` at `await`, the swallowing finaliser's raise. -/
def fsSched : Nat → CTy := fun j => if j = 0 then finR 3 else .ret .unit

/-- Both operations marked. -/
def csSched : Nat → Bool := fun _ => true

theorem ofEff_sched : Row.ofEff 1 Esched 0 fsSched csSched ++ [] = rowSw := rfl

/-- The answer clause: `λx. return (λc. inj₁ x)`. -/
def hrS : Expr := .val (.lam (.val (.lam (.inj₁ (.var 1)))))

/-- The `await` clause: `λ(v, κ). return (λc. κ.resume c to g. g c)`: the flag is the answer,
`inl ()` going on, `inr ()` the cancel. -/
def clS : Expr :=
  .val (.lam (.letpair (.var 0) (.val (.lam
    (bindE (.app (.app (.var 1) (.val (.inj₁ .unit))) (.var 0)) (.app (.var 0) (.var 1)))))))

/-- The cancel target's clause: `λ_. return (λc. inj₂ ())`. -/
def ccS : Expr := .val (.lam (.val (.lam (.inj₂ unit'))))

def clsS : Expr := .pair clS (.pair ccS (.val .unit))

/-- **The immediate scheduler around the swallowing example, from the cancelled flag.** -/
def stickyScope : Expr :=
  bindE clsS (bindE hrS (bindE (hndTerm 1 [.lin, .cancel] 0 1 swallowBody)
    (bindE (.val (.inj₂ .unit)) (.app (.var 1) (.var 0)))))

theorem flag_persistent : Flag.Persistent := rfl

theorem d_hrS {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ hrS (.val (retTy [] .unit StR)) :=
  .bangThunkV (banged_dead hΓ) rfl (.lam (.ret (.thunkV rfl (.lam (.ret (.sumI₁
    (.var (.skip flag_persistent (.here hΓ.toP)))))))))

theorem d_ccS {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ ccS (.val (clauseTy [] StR (.cancel, .unit, .zero))) :=
  .bangThunkV (banged_dead hΓ) rfl (.lam (.ret (.thunkV rfl (.lam (.ret (.sumI₂
    (.unitI (.drop rfl (.drop rfl hΓ.toP)))))))))

theorem d_clS {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ clS
      (.val (clauseTy [] StR (.lin, .unit, .sum .unit .unit) (finR 3))) := by
  refine .bangThunkV (banged_dead hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  refine .ret (.thunkV rfl (.lam ?_))
  refine .bind (.dup rfl (.left (.right (.dead (deadSplit hΓ)))))
    (.app (.right (.left (.dead (.dead (deadSplit hΓ)))))
      (.proj₁ (.force (C := .amp (.arr (.sum .unit .unit) (CTy.effOf [] StR)) .top)
        (.there (.here (by cdead)))))
      (.here (by cdead))) ?_
  exact .app (.left (.right (.dead (.right (.dead (deadSplit hΓ))))))
    (.force (.here (by cdead))) (.there (.here (.cons (.drop rfl (.cons hΓ.toP)))))

/-- **The immediate scheduler is typed**: a closed `CDerives` derivation at `F Flag`, its handler
at the marked pair (`csSched`). -/
theorem d_stickyScope : CDerives LifeCtx.empty [] stickyScope (.comp (.ret Flag)) := by
  refine .bind .nil (.ret (.tensorI .nil (d_clS .nil)
    (.tensorI .nil (d_ccS .nil) (.unitI .nil)))) ?_
  refine .bind (.right .nil) (.ret (d_hrS (.cons .nil))) ?_
  refine .bind (.left (.left .nil))
    (CDerives.effHandleCs (S := []) (E := Esched) (n := 1) (A := .unit) (R := StR) fsSched csSched
      (.left (.left .nil)) (.left (.right .nil)) (.here (.cons .nil)) (.there (.here .nil))
      (by decide) (by simp) (by simp) rfl
      (by rw [ofEff_sched]
          exact CDerives.append_dead (Γ := []) (Ctx.Dead.cons (Ctx.Dead.cons .nil)) d_swallow)) ?_
  refine .bind (A := Flag) (.right (.dead (.dead .nil))) (.ret (.sumI₂ (.unitI (by cdead)))) ?_
  exact .app (.right (.left (.dead (.dead .nil)))) (.force (.there (.here (by cdead))))
    (.here (by cdead))

/-- Every run of the immediate scheduler around the swallowing example from the cancelled flag
continues to a value (`adequacyD_obs`): the closed instance ends by adequacy. It does not read
`Row.CancelEnds`; the general termination target is open (SPEC §29a). -/
theorem stickyScope_runs {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem stickyScope μ₁ e₁) :
    ∃ v, BoCa.BoLo.Steps μ₁ e₁ Adequacy.emptyMem (.val v) := by
  obtain ⟨v, hv, -⟩ := adequacyD_obs (by decide) d_stickyScope hs
  exact ⟨v, hv⟩

/-- `Support`'s `eval` agrees: the run ends at `inr ()`, "cancelled", no cell left. -/
theorem stickyScope_eval :
    (match eval stickyScope with
      | .value ⟨.inj₂ .unit, _⟩ false => true
      | _ => false) = true := by
  decide

/-! ### `effThenDiv` reached: a finaliser that ticks, under `div_fuel`

`PinLaw.fin` is asserted only at configurations programs reach.
- `d_thenDivFuel`: a closed program at `F 1`, `return () then x. x unwind (tick; ())` under
  `div_fuel`. Its body does not stop, so the finaliser never runs.
- `d_thenTickAwait`: `await_1 then x. x unwind (tick; ())` at the row `{tick, await⟨{tick}⟩,
  cancelled}`. A cancel at the wait unwinds through a finaliser that ticks: the configuration
  `PinFin` asserts. A task body reaches it under `div_fuel`, whose callback is typed at `tick` ahead
  of any `Div`-free row (`divFuelTy`), the task's `await` included; `effHandleV`'s `hdv` only keeps
  `Div` out of the task handler's own row. -/

/-- `tick; ()`. -/
def tickUnit : Expr := .app (.val (.lam (.val .unit))) (performE (opArgE divEff 0 (.val .unit)))

/-- `return () then x. x unwind (tick; ())`. -/
def thenTick : Expr := thenE (.var 0) tickUnit (.val .unit)

/-- The callback `λ_. thenTick`. -/
def thenTickCb : Expr := .val (.lam thenTick)

theorem not_unrD_tick : ¬ Row.UnrD [tickSig] := by
  rintro ⟨o, ho, hu⟩
  simp only [List.mem_singleton] at ho
  subst ho
  rcases hu with hu | ⟨hc, -⟩
  · cases hu
  · simp [capB, tickSig] at hc

theorem d_tickUnit {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesP Δ Γ tickUnit (.comp (CTy.effOf [tickSig] .unit)) := by
  refine .effLet (A := nextTy) (deadSplit hΓ) (fun ⟨o, ho, hq⟩ => ?_) (fun ⟨o, ho, hq⟩ => ?_)
    (.effPerform (o := tickSig) rfl rfl rfl (.unitI hΓ.toP)) ?_
  · simp [tickSig] at ho; subst ho; exact absurd rfl hq
  · simp [tickSig] at ho; subst ho; cases hq
  · exact .effSub (RowLe.nil _) (.ret (.unitI (.drop rfl hΓ.toP)))

/-- **`[then]` with a ticking finaliser is typed**, by `effThenDiv`. -/
theorem d_thenTick {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesP Δ Γ thenTick (.comp (CTy.effOf [tickSig] .unit)) := by
  refine .effThenDiv (A := .unit) (SM := []) (SD := [tickSig]) (deadSplit hΓ)
    (by intro o ho; simp at ho; subst ho; decide) (by simp [Row.Uniq])
    (fun h => absurd h not_unrD_tick) (RowLe.nil _) (RowLe.refl _)
    (fun _ _ _ _ h => by simp [Row.find] at h) (fun _ _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil) (.effSub (RowLe.nil _) (.ret (.unitI hΓ.toP))) ?_ ?_
  · exact .effSub (RowLe.nil _) (.ret (.var (.here hΓ.toP)))
  · exact d_tickUnit (Ctx.Dead.cons hΓ)

/-- `await_1 then x. x unwind (tick; ())`. -/
def thenTickAwait : Expr := thenE (.var 0) tickUnit (awaitE 1)

/-- The row: `tick`, the wait whose cancel row records the ticking finaliser, its cancel target. -/
abbrev rowTickAwait : Row := [tickSig, awaitF (CTy.effOf [tickSig] .unit), cancelled]

/-- **A cancel unwinds through a finaliser that ticks**, typed by `effThenDiv`: the wait is not
capturable (it is `lin`), so `hcap` holds, and `hfin` records `{tick}` in its cancel row. -/
theorem d_thenTickAwait {Δ : LifeCtx} :
    CDerivesP Δ [] thenTickAwait (.comp (CTy.effOf rowTickAwait .unit)) := by
  refine .effThenDiv (Γ₁ := []) (Γ₂ := []) (A := .unit) (SM := [await0, cancelled])
    (SD := [tickSig]) .nil ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl <;> decide
  · simp [Row.Uniq, tickSig, awaitF, cancelled, divEff]
  · intro _ s hs; simp at hs
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    have hF : ∀ X, FinLe (.ret .unit) X := fun X => by
      rw [FinLe]; right; exact ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf] at h⟩
    rcases ho with rfl | rfl
    · exact ⟨awaitF (CTy.effOf [tickSig] .unit), rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
        fun _ => hF _⟩
    · exact ⟨cancelled, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => hF _⟩
  · refine RowLe.of_mem fun o ho => ?_
    simp only [List.mem_singleton] at ho
    subst ho
    exact ⟨tickSig, rfl, OpSig.LeF.refl _⟩
  · intro n i o o' hf hf' hr
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · obtain rfl : o' = awaitF (CTy.effOf [tickSig] .unit) :=
        Option.some.inj (hf'.symm.trans rfl)
      rw [ThenLe]
      refine Or.inr ⟨rfl, fun n i o h => by simp [Row.find, CTy.rowOf, awaitF] at h,
        fun n i o h => ?_⟩
      obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
      simp only [List.mem_singleton] at hm
      subst hm
      exact ⟨tickSig, rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
        fun hc => by simp [capB, tickSig] at hc⟩
    · rw [not_finRead_cancelled] at hr; cases hr
  · intro hu; exact absurd hu not_unrD_tick
  · intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · simp [capB, awaitF]
    · simp [capB, cancelled, VTy.isZero]
  · exact .effAwait .nil rfl (cancellable_await _) rfl rfl cancelTarget_cancelled
  · exact .effSub (RowLe.nil _) (.ret (.var (.here .nil)))
  · exact d_tickUnit (.cons .nil)

/-- `df ← div_fuel; df (thenTickCb, k)`. -/
def thenDivFuel (k : UInt32) : Expr :=
  bindE (.pair thenTickCb (.val (Val.i32 k))) (bindE (.val divFuelV) (.app (.var 0) (.var 1)))

/-- **The witness**: a closed `CDerivesP` derivation at `F 1`, `div_fuel` handling the row, that
uses `effThenDiv` at a finaliser row holding `Div`. -/
theorem d_thenDivFuel (k : UInt32) :
    CDerivesP LifeCtx.empty [] (thenDivFuel k) (.comp (.ret .unit)) := by
  refine .bind .nil (.ret (.tensorI .nil (.thunkV rfl (.lamDead (d_thenTick (.cons .nil))))
    (.lit (.i32 k) .nil))) ?_
  refine .bind (.right .nil)
    (.ret (.bangE (.divFuel [] .unit (fun _ h => absurd h List.not_mem_nil) (.cons .nil)))) ?_
  exact .app (.left (.right .nil))
    (.force (C := .arr (.tensor (.thunk (.arr .unit (CTy.effOf (tickSig :: []) .unit))) (.int .w32))
      (CTy.effOf [] .unit)) (.here (.cons .nil)))
    (.there (.here .nil))

/-- Under `PinLaw`, every run of the witness continues to `()` at the empty memory. -/
theorem thenDivFuel_runs (hPin : PinLaw (ℍ := ℍ)) (k : UInt32) {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps (ℍ := ℍ) Adequacy.emptyMem (thenDivFuel k) μ₁ e₁) :
    Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val .unit) :=
  adequacyD_pin hPin (d_thenDivFuel k) hs

/-! ### Runs

Memory: the flag at `0`, a log cell at `1` (both allocated first), then the lend's cell. The program
answers `(r, log)`: the task's answer `r` (`inl v` done, `inl 7` the `cancelled` clause) and the
log's last value. Each run is `Support`'s `eval`, its flag `false` when no cell is left. -/

/-- An `i32` literal. -/
def lit (n : UInt32) : Expr := (Val.i32 n).1

/-- `store l v`. -/
def storeE (l v : Expr) : Expr := .app (.app (.prim .store) l) v

/-- The owner's finaliser `d = λc. free c`. -/
def dOwn : Expr := .lam (.app (.lam (.app (.lam .unit) (.var 0))) (.app (.prim .free) (.var 0)))

/-- The task under its handler, the lend of a fresh cell holding 10. -/
def taskL (qs hs : Val) (B : Expr) : Expr :=
  .app (.lam (hndE (hndVal 1 qs hRetL hs)
      (.app (.app (withborUE dOwn) (.var 0)) (.lam (.lam B)))))
    (.app (.prim .alloc) (lit 10))

/-- `κ.1 v`. -/
def resumeK (k v : Expr) : Expr := .app (.app k (Val.inj₁ Val.unit).1) v

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

/-- The task, level-triggered. -/
def taskS (B : Expr) : Expr := taskL qsTask hsSticky B

/-- The answer `(inl i, log)`, no cell left. -/
def answers (e : Expr) (i l : UInt32) : Bool :=
  match eval e with
  | .value ⟨.pair (.inj₁ (.prim (.lit (.i32 a)))) (.prim (.lit (.i32 b))), _⟩ false =>
      a == i && b == l
  | _ => false

/-- `swallowBody; 5`. -/
def bSwallow : Expr := .app (.val (Val.lam (.seq (.var 0) (lit 5)))) swallowBody

/-- **The swallowing example re-raises**: the first `await` is cancelled, the finaliser's raise of
`3` is caught, and the second `await` raises `cancelled` from the flag: the task ends in the
`cancelled` clause, every cell freed. -/
theorem swallow_sticky : answers (withState (cancelS (taskS bSwallow))) 7 0 = true := by decide

/-- Attempt `j`: `handle_3 ((await_1 then x. x; 5 unwind raise_3)) with {ret v → inl v | 3 _ →
log := j; inr ()}`. -/
def attempt (j : UInt32) : Expr :=
  hndExpr 3 [.unr] (.pair (.val CancelIntercept.injlV) (.pair
      (.val (Val.lam (.seq (storeE (.val (Val.loc 1)) (lit j)) (.val (Val.inj₂ Val.unit)))))
      (.val Val.unit)))
    (thenE (.seq (.var 0) (lit 5)) (raiseU 3) (awaitE 1))

/-- Two attempts, then give up: `log := 3; await_1; 0`. -/
def bRetry : Expr :=
  .case (attempt 1) (.var 0)
    (.case (attempt 2) (.var 0)
      (.seq (storeE (.val (Val.loc 1)) (lit 3)) (.seq (awaitE 1) (lit 0))))

/-- **A retry that catches every error does not lose the cancel**: each attempt's `await` raises
it again; the give-up path's `await` raises it, and nothing catches it (log 3). -/
theorem retry_sticky : answers (withState (cancelS (taskS bRetry))) 7 3 = true := by decide

/-- `(λh. await_1 then x. close h; 5 unwind close h) (alloc 42)`. -/
def bClose : Expr :=
  .app (.val (Val.lam (thenE (.app (.val (Val.lam (lit 5))) (.app (.val (.prim .free)) (.var 1)))
      (.app (.val (Val.lam (.val Val.unit))) (.app (.val (.prim .free)) (.var 1)))
      (awaitE 1))))
    (.app (.val (.prim .alloc)) (lit 42))

/-- **The finaliser closes `h` on the cancel exit**: the `cancelled` clause, no cell left. -/
theorem close_sticky : answers (withState (cancelS (taskS bClose))) 7 0 = true := by decide

/-- `await_1 then x. x; 5 unwind (complete_1; log := 42)`. -/
def bShield : Expr :=
  thenE (.seq (.var 0) (lit 5))
    (.seq (performE (opArgE 1 2 (.val .unit))) (storeE (.val (Val.loc 1)) (lit 42))) (awaitE 1)

/-- **A shielded wait in a cancelled task's finaliser completes**: the scheduler answers it, and
the finaliser goes on (log 42) before the `cancelled` clause. -/
theorem shield_sticky :
    answers (withState (serve (.val Val.unit) (cancelS (taskS bShield)))) 7 42 = true := by decide

/-- The same finaliser with `await` in place of the shielded wait. -/
def bUnshielded : Expr :=
  thenE (.seq (.var 0) (lit 5)) (.seq (awaitE 1) (storeE (.val (Val.loc 1)) (lit 42))) (awaitE 1)

/-- **An `await` in a cancelled task's finaliser raises at once** (log 0). -/
theorem unshielded_sticky :
    answers (withState (serve (.val Val.unit) (cancelS (taskS bUnshielded)))) 7 0 = true := by
  decide

end BoCa.Fig16.LogRel.Core.AwaitCancel

end

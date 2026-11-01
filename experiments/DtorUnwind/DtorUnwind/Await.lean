import DtorUnwind.Suspend
import DtorUnwind.Lend

/-!
# Stage 6: `borrow mut c { v → …v…; await; …v… }` over the task's own cell

The surface block holds a `mut` view of `c` across a suspension. It elaborates by one rule,
`d_segLend`: the block is cut at the suspension into **segments**, each a lexical lend inside
one run. Between them `c` is owned again, held across the suspension by `[let-dtor]`, so the
captured continuation owns it. After the suspension the next segment re-lends `c` at a fresh
`'x′`, and the view it uses is the new instance:

    segE cb₁ cb₂ M = (c, _) ← withbor c cb₁;                 -- segment 1, at 'x; the lend ends
                     let _ = M in                            -- the suspension, c owned (drop_ctx on unwind)
                       (c, _) ← withbor c cb₂; drop_c c      -- segment 2, at a fresh 'x′
                     unwind drop_ctx

`cbᵢ : ∀'x ⊏ ⊓Δ. Mut 'x A ⊸ ['x] 1`: each segment is lifetime-parametric through `withbor`'s
callback type (`∀I` at the thunk, `∀E` at `withbor`'s `[]`), which is the lifetime-parametric
continuation the question asks for, written as the rest of the block rather than as `κ`'s type.
No view crosses the suspension: a segment's answer type is free of `'x` (`withbor`'s
`hfree₂`), so a view copied or stored to be used after the suspension has no derivation
(`escape_refused`).

A reborrow open across the await is cut the same way: each segment opens the same nest of
lexical lends (`withbor3` inside `withbor2`) and ends it before the suspension
(`d_cbNest`). Nothing spans a stop, so the per-segment relation is the kernel's, at every depth;
the stack-indexed relation of `GhostEnd` is not needed.

No rule is added, and nothing is asserted (no PinLaw, no R1).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DtorUnwind.Await
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.DtorUnwind
open BoCa.Fig16.LogRel.Core.DtorUnwind.Files
open BoCa.Fig16.LogRel.Core.DtorUnwind.Suspend
open BoCa.Fig16.LogRel.Core.DtorUnwind.Lend (deadOwnFree)
open BoCa.BoLo (Heap Steps Step1 Kont freeE performE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Programs (alloc' free' app2)

/-! ### The segmented lend -/

/-- The segments around the suspension `M`, the source at `0`, its destructor `λx. b`. -/
def segE (cb₁ cb₂ b : Expr) (ds : List (Option Expr)) (M : Expr) : Expr :=
  bindE (app2 withbor (.var 0) cb₁)
    (.letpair (.var 0)
      (letDE ds
        (bindE (app2 withbor (.var 2) cb₂)
          (.letpair (.var 0) (bindE (.app (.val (.lam b)) (.var 1)) (.val .unit))))
        M))

/-- The destructors at the suspension: the first segment's unit answer, the source, and dead
slots. -/
def segDs (b : Expr) (k : Nat) : List (Option Expr) :=
  none :: some b :: none :: none :: List.replicate k none

/-- **`d_segLend`: a `mut` borrow block cut at a suspension.** For a lend constant `withbor` at
`Src ⊸ CB ⊸ Src ⊗ (['x]-free) 1`, two segments `cb₁ cb₂ : CB`, a suspension `M` at `Σ`, and a
destructor `λx. b : Src ⊸ F_{Σ_D} 1` that `[let-dtor]` admits at `Σ`: the block is typed. -/
theorem d_segLend {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {Src CB : VTy} {S SD : Row}
    {cb₁ cb₂ b M : Expr}
    (hw : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerives Δ Γ' withbor (.val (.lolli Src (.lolli CB (.tensor Src .unit)))))
    (hcb₁ : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives Δ Γ' cb₁ (.val CB))
    (hcb₂ : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives Δ Γ' cb₂ (.val CB))
    (hb : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' →
      CDerives Δ Γ' (.val (.lam b)) (.comp (.arr Src (CTy.effOf SD .unit))))
    (hNZ : S.NZ) (hUq : S.Uniq) (hUnr : ¬ S.UnrD) (hDS : RowLe SD S)
    (hSDc : ¬ SD.Cancels) (hSDd : Row.divB SD = false)
    (hfin : ∀ n i o, Row.find S n i = some o → o.finRead = true → ThenLe o.fin SD o.fin)
    (hM : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives Δ Γ' M (.comp (CTy.effOf S .unit))) :
    CDerives Δ (⟨Src, true⟩ :: Γ) (segE cb₁ cb₂ b (segDs b Γ.length) M)
      (.comp (CTy.effOf S .unit)) := by
  -- segment 1
  refine .bind (A := .tensor Src .unit) (.left (deadSplit hΓ))
    (.ret (.lolliE (.right (deadSplit hΓ)) (hcb₁ _ (.cons hΓ))
      (.lolliE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) (hw _ (.cons hΓ))))) ?_
  refine .tensorE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ.toP))) ?_
  -- the suspension, the source held by `[let-dtor]`
  have hds : Dtors Δ SD (⟨.unit, true⟩ :: ⟨Src, true⟩ :: ⟨.tensor Src .unit, false⟩ ::
      ⟨Src, false⟩ :: Γ) (segDs b Γ.length) :=
    .pers rfl (.drop hb (.dead (.dead (Files.dtors_dead hΓ))))
  refine CDerives.effLetD (A := .unit) (split_kill _).toP hNZ hUq (fun h => absurd h hUnr) hDS
    hSDc hSDd hfin hds (hM _ (kill_dead _)) ?_
  -- segment 2, at a fresh lifetime
  refine .bind (A := .tensor Src .unit) (.right (.right (.left (.dead (.dead (deadSplit hΓ))))))
    (.ret (.lolliE (.dead (.dead (.right (.dead (.dead (deadSplit hΓ)))))) (hcb₂ _ (by cdead))
      (.lolliE (.dead (.dead (.left (.dead (.dead (deadSplit hΓ))))))
        (.var (.there (.there (.here (by cdead))))) (hw _ (by cdead))))) ?_
  refine .tensorE (.left (.right (.right (.dead (.dead (.dead (deadSplit hΓ)))))))
    (.var (.here (by cdead))) ?_
  refine .effLet (A := .unit) (split_kill' _).toP (fun _ => deadOwnFree (kill_dead _))
    (fun _ => banged_dead (kill_dead _)) ?_ (.effSub (RowLe.nil S) (.ret (.unitI
      (.drop rfl (kill_dead _).toP))))
  exact .effSub hDS (.app (split_kill _).toP (hb _ (kill_dead _))
    (.skip rfl (.here (.cons (.drop rfl (.drop rfl (.cons (.cons (.cons hΓ.toP)))))))))

/-! ### No view crosses the suspension -/

/-- **A view cannot be a segment's answer**: `withbor`'s `hfree₂ : ¬ VFree x B` fails at
`B = Mut 'x A`, so a view copied or stored for use after the suspension has no derivation. -/
theorem escape_refused (A : VTy) : VFree 0 (.mut (.var 0) A) := by
  simp [VFree, Lifetime.Life.mentions]

/-! ### The segments over a file's descriptor -/

/-- `λn. (n + k, ())`. -/
def addK (k : UInt32) : Expr :=
  .val (.lam (.pair (.app (.val (.prim (.host (.bin .w32 .add)))) (.pair (.var 0) (.val (Val.i32 k))))
    (.val .unit)))

theorem d_addK {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (k : UInt32) :
    CDerives Δ Γ (addK k) (.val (.lolli I32 (.tensor I32 .unit))) :=
  .lamV (pairW (appW (pairW (.var (by csolo)) (.lit (.i32 k) (by cdead)))
    (.bangE (.hostOp (.bin .w32 .add) (by cdead)))) (.unitI (by cdead)))

/-- A segment: `Λ. λv. (v′, u) ← withswap v (addK k); u; forget v′; ()`. -/
def cbAdd (k : UInt32) : Expr :=
  .val (.lam (.val (.lam (.letpair (app2 withswap (.var 0) (addK k))
    (.seq (.var 0) (.seq (.app forget (.var 1)) (.val .unit)))))))

abbrev CBm : VTy :=
  .all 0 LifeCtx.empty.meetOfDom (.lolli (.mut (.var 0) I32) (.box (.var 0) .unit))

theorem d_cbAdd {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (k : UInt32) :
    CDerives LifeCtx.empty Γ (cbAdd k) (.val CBm) := by
  refine callbackW ok_empty rfl hΓ ?_
  refine letW (appW (d_addK (by cdead) k) (appW (.var (by csolo)) (.withswap (by cdead)))) ?_
  refine seqW (.var (by csolo)) ?_
  refine seqW (appW (.var (by csolo)) (.forgetMut (by cdead))) ?_
  exact .boxI (.unitI (by cdead)) ⟨LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩

/-- A segment with a reborrow: `Λ. λv. (v′, u) ← withbor v (Λ. λw. (w′, u) ← withswap w (addK k);
u; forget w′; ()); u; forget v′; ()`. -/
def cbNest (k : UInt32) : Expr :=
  .val (.lam (.val (.lam (.letpair
    (app2 withbor (.var 0) (.val (.lam (.val (.lam (.letpair (app2 withswap (.var 0) (addK k))
      (.seq (.var 0) (.seq (.app forget (.var 1)) (.val .unit)))))))))
    (.seq (.var 0) (.seq (.app forget (.var 1)) (.val .unit)))))))

def cbInner (k : UInt32) : Expr :=
  .val (.lam (.val (.lam (.letpair (app2 withswap (.var 0) (addK k))
    (.seq (.var 0) (.seq (.app forget (.var 1)) (.val .unit)))))))

theorem cbNest_eq (k : UInt32) : cbNest k =
    .val (.lam (.val (.lam (.letpair (app2 withbor (.var 0) (cbInner k))
      (.seq (.var 0) (.seq (.app forget (.var 1)) (.val .unit))))))) := rfl

theorem d_cbInner {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (k : UInt32) :
    CDerives D1 Γ (cbInner k)
      (.val (.all 1 D1.meetOfDom (.lolli (.mut (.var 1) I32) (.box (.var 1) .unit)))) := by
  refine callbackW d1_ok rfl hΓ ?_
  refine letW (appW (d_addK (by cdead) k) (appW (.var (by csolo)) (.withswap (by cdead)))) ?_
  refine seqW (.var (by csolo)) ?_
  refine seqW (appW (.var (by csolo)) (.forgetMut (by cdead))) ?_
  exact .boxI (.unitI (by cdead)) ⟨LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩

theorem d_cbNest {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (k : UInt32) :
    CDerives LifeCtx.empty Γ (cbNest k) (.val CBm) := by
  rw [cbNest_eq]
  refine callbackW ok_empty rfl hΓ ?_
  refine letW (.lolliE (split_kill _).toP (d_cbInner (kill_dead _) k)
    (appW (.var (by csolo)) (.withbor3 (a := .var 0) (A := I32) (B := .unit) 1 (by cdead) rfl
      (by simp [VFree]) (by simp [VFree])))) ?_
  refine seqW (.var (by csolo)) ?_
  refine seqW (appW (.var (by csolo)) (.forgetMut (by cdead))) ?_
  exact .boxI (.unitI (by cdead)) ⟨LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩

theorem d_withborI32 (Γ' : Ctx VTy) (hΓ : Ctx.Dead Γ') :
    CDerives LifeCtx.empty Γ' withbor (.val (.lolli File (.lolli CBm (.tensor File .unit)))) :=
  .withbor2 (A := I32) (B := .unit) 0 hΓ.toP rfl
    ⟨.top, LifeCtx.defines_of_wf rfl, (outlives_of_dataB rfl).toLe⟩ (by simp [VFree])
    (by simp [VFree])

/-- The task: `c ← alloc 1; borrow mut c { v → v += 10; M; v += 1 }`, each segment `cb`. -/
def task (cb : UInt32 → Expr) (M : Expr) : Expr :=
  bindE (.app alloc' (.val (Val.i32 1))) (segE (cb 10) (cb 1) dFileB (segDs dFileB 4) M)

theorem d_task {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (hlen : Γ.length = 4) {cb : UInt32 → Expr}
    (hcb : ∀ k (Γ' : Ctx VTy), Ctx.Dead Γ' → CDerives LifeCtx.empty Γ' (cb k) (.val CBm))
    {S : Row} {M : Expr} (hNZ : S.NZ) (hUq : S.Uniq) (hUnr : ¬ S.UnrD) (hDS : RowLe SD S)
    (hfin : ∀ n i o, Row.find S n i = some o → o.finRead = true → ThenLe o.fin SD o.fin)
    (hM : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives LifeCtx.empty Γ' M (.comp (CTy.effOf S .unit))) :
    CDerives LifeCtx.empty Γ (task cb M) (.comp (CTy.effOf S .unit)) := by
  refine .bind (A := File) (deadSplit hΓ)
    (.ret (appW (.lit (.i32 1) (by cdead)) (.alloc (by cdead)))) ?_
  have h := d_segLend (Δ := LifeCtx.empty) hΓ d_withborI32 (hcb 10) (hcb 1) d_dFile hNZ hUq hUnr
    hDS SD_not_cancels SD_divB hfin hM
  rwa [hlen] at h

/-! ### (a) resumed, (c) dropped: the suspension `y` (stage 5) -/

def yM : Expr := performE (opArgE 6 0 (.val .unit))

def awaitProgY (cl : Expr) (cb : UInt32 → Expr) : Expr := withFs (yH cl (task cb yM))

theorem d_awaitProgY {cl : Expr}
    (hcl : ∀ {Γ' : Ctx VTy}, Ctx.Dead Γ' →
      CDerives LifeCtx.empty Γ' cl (.val (clauseTy SD .unit (.cancel, .unit, .unit) Cancel.FD)))
    {cb : UInt32 → Expr}
    (hcb : ∀ k (Γ' : Ctx VTy), Ctx.Dead Γ' → CDerives LifeCtx.empty Γ' (cb k) (.val CBm)) :
    CDerives LifeCtx.empty [] (awaitProgY cl cb) (.comp (.ret .unit)) := by
  refine d_withFsG (S := []) (A := .unit) (by simp) rfl ?_
  exact d_yH (.cons (.cons .nil)) hcl
    (d_task (Γ := [_, _, _, _]) (by cdead) rfl hcb SY_nz SY_uniq SY_not_unrD SD_le_SY hfin_y d_yM)

/-! ### (b) cancelled: the level-triggered scheduler (stage 2) -/

def awaitProgC (cb : UInt32 → Expr) : Expr := withFs (Cancel.sched (task cb (awaitE 1)))

theorem d_awaitProgC {cb : UInt32 → Expr}
    (hcb : ∀ k (Γ' : Ctx VTy), Ctx.Dead Γ' → CDerives LifeCtx.empty Γ' (cb k) (.val CBm)) :
    CDerives LifeCtx.empty [] (awaitProgC cb) (.comp (.ret EffPrograms.Flag)) := by
  refine d_withFsG (S := []) (A := EffPrograms.Flag) (by simp) rfl ?_
  show CDerives _ _ _ (.comp (CTy.effOf SD EffPrograms.Flag))
  exact Cancel.d_schedG (.cons (.cons .nil))
    (d_task (Γ := [_, _, _, _]) (by cdead) rfl hcb Cancel.S2_nz Cancel.S2_uniq
      Cancel.S2_not_unrD Cancel.SD_le_S2 Cancel.hfin_await Cancel.d_awaitM)

/-! ### The six closed programs and their safety -/

theorem d_resume : CDerives LifeCtx.empty [] (awaitProgY clRes cbAdd) (.comp (.ret .unit)) :=
  d_awaitProgY d_clRes (fun k _ h => d_cbAdd h k)
theorem d_drop : CDerives LifeCtx.empty [] (awaitProgY clDrop cbAdd) (.comp (.ret .unit)) :=
  d_awaitProgY d_clDrop (fun k _ h => d_cbAdd h k)
theorem d_cancel :
    CDerives LifeCtx.empty [] (awaitProgC cbAdd) (.comp (.ret EffPrograms.Flag)) :=
  d_awaitProgC (fun k _ h => d_cbAdd h k)
theorem d_resumeNest : CDerives LifeCtx.empty [] (awaitProgY clRes cbNest) (.comp (.ret .unit)) :=
  d_awaitProgY d_clRes (fun k _ h => d_cbNest h k)
theorem d_dropNest : CDerives LifeCtx.empty [] (awaitProgY clDrop cbNest) (.comp (.ret .unit)) :=
  d_awaitProgY d_clDrop (fun k _ h => d_cbNest h k)
theorem d_cancelNest :
    CDerives LifeCtx.empty [] (awaitProgC cbNest) (.comp (.ret EffPrograms.Flag)) :=
  d_awaitProgC (fun k _ h => d_cbNest h k)

/-- The safety statement of `resourceSafety`, at a program. -/
abbrev Safe (e : Expr) : Prop :=
  ∀ {μ₁ : Heap} {e₁ : Expr}, Steps (ℍ := ℍ) Adequacy.emptyMem e μ₁ e₁ →
    (∃ v : Val, Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : Kont) (ℓ : Loc), e₁ = K.plug (freeE (.val (Val.loc ℓ))) → ∃ u, μ₁ ℓ = some u)

theorem resume_safe : Safe (ℍ := ℍ) (awaitProgY clRes cbAdd) :=
  fun hs => resourceSafety (by decide) d_resume hs
theorem drop_safe : Safe (ℍ := ℍ) (awaitProgY clDrop cbAdd) :=
  fun hs => resourceSafety (by decide) d_drop hs
theorem cancel_safe : Safe (ℍ := ℍ) (awaitProgC cbAdd) :=
  fun hs => resourceSafety AwaitCancel.flag_persistent d_cancel hs
theorem resumeNest_safe : Safe (ℍ := ℍ) (awaitProgY clRes cbNest) :=
  fun hs => resourceSafety (by decide) d_resumeNest hs
theorem dropNest_safe : Safe (ℍ := ℍ) (awaitProgY clDrop cbNest) :=
  fun hs => resourceSafety (by decide) d_dropNest hs
theorem cancelNest_safe : Safe (ℍ := ℍ) (awaitProgC cbNest) :=
  fun hs => resourceSafety AwaitCancel.flag_persistent d_cancelNest hs

/-! ### The runs: `with_fs` records the descriptor the file is closed with

The cell starts at `1`; the first segment adds `10` through its view, the second adds `1` through
the fresh one. Resumed, the file closes at `12`: both segments ran, the second on the new view.
Cancelled or dropped, it closes at `11`, on the unwind, after the first segment's lend ended. -/

def logY (cl : Expr) (cb : UInt32 → Expr) : Expr := withLogCell (withFsLog (yH cl (task cb yM)))
def logC (cb : UInt32 → Expr) : Expr := withLogCell (withFsLog (Cancel.sched (task cb (awaitE 1))))

theorem resume_run : logIs (logY clRes cbAdd) 12 = true := by decide
theorem drop_run : logIs (logY clDrop cbAdd) 11 = true := by decide
theorem cancel_run : logIs (logC cbAdd) 11 = true := by decide
theorem resumeNest_run : logIs (logY clRes cbNest) 12 = true := by decide
theorem dropNest_run : logIs (logY clDrop cbNest) 11 = true := by decide
theorem cancelNest_run : logIs (logC cbNest) 11 = true := by decide

end BoCa.Fig16.LogRel.Core.DtorUnwind.Await

end

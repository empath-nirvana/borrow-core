import Targets.Instance.E4

/-!
# The Instance — E5 (nested handlers, in both orders) at `J₁`

`withLog` is a state-passing handler of the linear `log`: its clause answers a state function that
resumes `κ` and applies the function the resumed computation answers to the logged value
(`d_logCl`, decision 59).  `toResult` handles the abortive `exn`.  `body5 = log tt; raise exn ()`.

* **`withLog` outside `toResult`** (`der_p1_J₁`, `runsTo_p1`): typed at the pure row; `log` passes
  `toResult`'s handler and is caught by `withLog`'s around `κ`'s cell (SPEC §25); the resume
  reinstalls both handlers, the raise is caught by `toResult`, and the answer is `(inr (), tt)`.
* **`toResult` outside `withLog`** (`der_p2_J₁`, `runsTo_p2`): `withLog`'s handler is typed at
  `exn`'s row, so its clause's state function is a `[let]` at that row; the raise passes
  `withLog`'s reinstalled handler, which the unwind drops with its state, and the answer is
  `inr ()`.  The `[let]` holds the logged value `b : bool` across the resume, and at a row with an
  `unr` operation `[let]` requires the continuation's context persistent (`!`), which `bool` is not:
  so the typing here is at an affine `exn` (`d_p2`), and `nestedHandlers_J₁` assumes the context has
  no `unr` `exn` signature (`NoUnrExn`, which `ΞA` meets: `noUnrExn_ΞA`).
`[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Head Kont performE raiseE hndE hndVal opPayload kappaCell kappaCBody freeE
  kappaAt capTag)
open BoCa.Lifetime (LifeCtx)
open Targets (EffCtx orowRF orowAlg RowAt CDerivesAt lookEnd)

/-! ### The programs, as our instance writes them -/

/-- `return x ⇒ λs. (x, s)`. -/
def logRetE : Expr := .lam (.lam (.pair (.var 1) (.var 0)))
/-- `log (b, k) ⇒ λs. resume k () to g. g b`. -/
def logClE : Expr :=
  .lam (.letpair (.var 0) (.lam (bindE (resumeE (.var 1) .unit) (appE (.var 0) (.var 3)))))
/-- `withLog`'s handler. -/
def logH : Expr := .pair logRetE (clausesE [logClE])
theorem isVal_logH : IsVal logH := .pair .lam (.pair .lam .unit)
/-- `withLog M = handle log {…} M to g. g ff`, at the name `nl` and the tags `ql`. -/
def withLogE (nl : UInt32) (ql M : Expr) : Expr :=
  bindE ((handleK nl ql logRetE [logClE]).plug M) (appE (.var 0) (.inj₁ .unit))
/-- `toResult M`, at the name `ne` and the tags `qe`. -/
def toResultE (ne : UInt32) (qe M : Expr) : Expr :=
  (handleK ne qe (.lam (.inj₁ (.var 0))) [.lam (.inj₂ .unit)]).plug M
/-- `log tt; raise exn ()`. -/
def body5E (nl ne : UInt32) : Expr :=
  bindE (performE (opArgE nl 0 (.inj₂ .unit))) (raiseE (opArgE ne 0 .unit))

/-- `withLog`'s answer at the row `S`: `U(bool ⊸ F_S (A ⊗ bool))`. -/
def logR (S : Row) (A : VTy) : VTy := .thunk (.arr boolT (CTy.effOf S (.tensor A boolT)))

/-- A row whose operations are not the name `n`'s is below `n`'s signature row before it. -/
theorem rowLe_ofEff_cons {n : UInt32} (E : List (Qual × VTy × VTy)) {T : Row}
    (hT : ∀ o ∈ T, o.n ≠ n) : RowLe T (Row.ofEff n E 0 ++ T) := by
  intro m i o hf
  obtain ⟨hmem, hn, -⟩ := Row.find_mem hf
  have hm : m ≠ n := by rw [← hn]; exact hT o hmem
  rw [Row.find_append, Targets.find_ofEff_other _ hm, Option.none_or]
  exact hf

section Typing
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- E5's first program, as our instance writes it. -/
theorem p1_val (llog le : (orowAlg Ξ).Lab) :
    ((𝕁).withLog llog ((𝕁).toResult le ((𝕁).body5 llog le)) : Expr) =
      withLogE llog.1 (qsOf Ξ llog.1) (toResultE le.1 (qsOf Ξ le.1) (body5E llog.1 le.1)) := rfl
/-- E5's second program, as our instance writes it. -/
theorem p2_val (llog le : (orowAlg Ξ).Lab) :
    ((𝕁).toResult le ((𝕁).withLog llog ((𝕁).body5 llog le)) : Expr) =
      toResultE le.1 (qsOf Ξ le.1) (withLogE llog.1 (qsOf Ξ llog.1) (body5E llog.1 le.1)) := rfl

/-- `return x ⇒ λs. (x, s)`: the state function holds `x`. -/
theorem d_logRet {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (S : Row) (A : VTy) :
    CDerivesAt Ξ Δ Γ logRetE (.val (retTy S A (logR S A))) :=
  d_lamBang hΓ (.effSub (rowLe_nil S) (.ret (.thunkV rfl (.lam (.effSub (rowLe_nil S) (.ret
    (.tensorI (.right (.left (deadSplit hΓ))) (.var (.there (.here hΓ.toP)))
      (.var (.here (.cons hΓ.toP))))))))))

/-- **`log (b, k) ⇒ λs. resume k () to g. g b`** at the row `S`: the state function holds the
linear `k` and `b`; its `[let]` holds `b` across the resume, so `S` has no `unr` operation. -/
theorem d_logCl {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (S : Row) (A : VTy)
    (hU : ¬ S.Unr) :
    CDerivesAt Ξ Δ Γ logClE (.val (clauseTy S (logR S A) (.lin, boolT, .unit))) := by
  rw [clauseTy_resuming rfl]
  refine d_lamBang hΓ (.tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_)
  refine .effSub (rowLe_nil S) (.ret (.thunkV rfl (.lam ?_)))
  refine .effLet (A := logR S A) (.left (.left (.right (.dead (deadSplit hΓ))))) (fun _ => ?_)
    (fun h => absurd h hU)
    ?_ ?_
  · intro s hs hl
    simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | rfl | rfl | hs
    · cases hl
    · cases hl
    · exact .sum .unit .unit
    · cases hl
    · exact dead_noLive (P := fun s => s.ty.Drop) hΓ s hs hl
  · refine .bind (.left (.right (.dead (.dead (deadSplit hΓ)))))
      (.ret (.unitI (.drop rfl (.cons (.cons (.cons hΓ.toP)))))) ?_
    show CDerivesAt Ξ Δ _ (.app (.app (.var 2) (.inj₁ .unit)) (.var 0)) _
    exact .app (.right (.dead (.left (.dead (.dead (deadSplit hΓ))))))
      (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf S (logR S A))) .top)
        (.there (.there (.here (.cons (.cons hΓ.toP)))))))
      (.here (.cons (.cons (.cons (.cons hΓ.toP)))))
  · show CDerivesAt Ξ Δ _ (.app (.lam (.app (.var 1) (.var 0))) (.var 3)) _
    exact .bind (.right (.dead (.dead (.left (.dead (deadSplit hΓ))))))
      (.ret (.var (.there (.there (.there (.here (.cons hΓ.toP)))))))
      (.app (.right (.left (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))
        (.force (C := .arr boolT (CTy.effOf S (.tensor A boolT)))
          (.there (.here (.cons (.cons (.cons (.cons hΓ.toP)))))))
        (.here (.cons (.cons (.cons (.cons (.cons hΓ.toP)))))))

/-- `withLog`'s handler at the row `S`. -/
theorem d_logH {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (S : Row) (A : VTy) (hU : ¬ S.Unr) :
    CDerivesAt Ξ Δ Γ logH (.val (.tensor (retTy S A (logR S A))
      (clausesTy S (logR S A) [(.lin, boolT, .unit)]))) :=
  .tensorI (deadSplit hΓ) (d_logRet hΓ S A) (.tensorI (deadSplit hΓ) (d_logCl hΓ S A hU)
    (.unitI hΓ.toP))

/-- **`withLog M` at the row `S`**, `M` at `log`'s row before `S`. -/
theorem d_withLog {llog : (orowAlg Ξ).Lab} (hl : Ξ llog.1 = [(.lin, boolT, .unit)]) {S : Row}
    (hS : RowAt Ξ S) (hnS : ∀ o ∈ S, o.n ≠ llog.1) (hU : ¬ S.Unr) {A : VTy} {M : Expr}
    (hM : CDerivesAt Ξ LifeCtx.empty [] M
      (.comp (CTy.effOf (Row.ofEff llog.1 [(.lin, boolT, .unit)] 0 ++ S) A))) :
    CDerivesAt Ξ LifeCtx.empty [] (withLogE llog.1 (qsOf Ξ llog.1) M)
      (.comp (CTy.effOf S (.tensor A boolT))) :=
  .effLet .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
    (fun _ => fun _ h => absurd h List.not_mem_nil)
    (d_handleL llog hl hS hnS isVal_logH (d_logH (kill_dead _) S A hU) hM)
    (d_callVar (.sumI₁ (.unitI (.cons .nil))))

/-- **`toResult M` at the row `S`**, `M` at `exn`'s row before `S`. -/
theorem d_toResult {le : (orowAlg Ξ).Lab} {qe : Qual} (he : Ξ le.1 = [(qe, .unit, .zero)])
    (hqe : qe ≠ .lin) {S : Row} (hS : RowAt Ξ S) (hnS : ∀ o ∈ S, o.n ≠ le.1) {A : VTy} {M : Expr}
    (hM : CDerivesAt Ξ LifeCtx.empty [] M
      (.comp (CTy.effOf (Row.ofEff le.1 [(qe, .unit, .zero)] 0 ++ S) A))) :
    CDerivesAt Ξ LifeCtx.empty [] (toResultE le.1 (qsOf Ξ le.1) M)
      (.comp (CTy.effOf S (.sum A .unit))) :=
  d_handleL le he hS hnS isVal_toResultH (d_toResultH (kill_dead _) S A hqe) hM

/-- `log tt; raise exn ()` at every row both signature rows are below. -/
theorem d_body5 {llog le : (orowAlg Ξ).Lab} (hl : Ξ llog.1 = [(.lin, boolT, .unit)]) {qe : Qual}
    (he : Ξ le.1 = [(qe, .unit, .zero)]) (hqe : qe ≠ .lin) {T : Row}
    (h₁ : RowLe (Row.ofEff llog.1 [(.lin, boolT, .unit)] 0 ++ []) T)
    (h₂ : RowLe (Row.ofEff le.1 [(qe, .unit, .zero)] 0 ++ []) T) :
    CDerivesAt Ξ LifeCtx.empty [] (body5E llog.1 le.1) (.comp (CTy.effOf T .unit)) :=
  .effLet (A := .unit) .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
    (fun _ => fun _ h => absurd h List.not_mem_nil)
    (.effSub h₁ (d_performLab llog hl rfl (.sumI₂ (.unitI .nil))))
    (.effSub h₂ (d_raiseLab (.drop rfl .nil) le he hqe .unit))

/-- A signature row's operations are its name's. -/
theorem names_ofEff {n : UInt32} {E : List (Qual × VTy × VTy)} {m : UInt32} (h : n ≠ m) :
    ∀ o ∈ Row.ofEff n E 0 ++ [], o.n ≠ m := by
  intro o ho
  rw [List.append_nil] at ho
  rw [mem_ofEff_n ho]
  exact h

/-- `withLog (toResult body5)` at the pure row. -/
theorem d_p1 {llog le : (orowAlg Ξ).Lab} (hl : Ξ llog.1 = [(.lin, boolT, .unit)]) {qe : Qual}
    (he : Ξ le.1 = [(qe, .unit, .zero)]) (hqe : qe ≠ .lin) (hne : llog.1 ≠ le.1) :
    CDerivesAt Ξ LifeCtx.empty []
      (withLogE llog.1 (qsOf Ξ llog.1) (toResultE le.1 (qsOf Ξ le.1) (body5E llog.1 le.1)))
      (.comp (.ret (.tensor (.sum .unit .unit) boolT))) :=
  d_withLog hl (S := []) (rowAt_nil Ξ) (by simp) (fun ⟨_, h, _⟩ => List.not_mem_nil h)
    (d_toResult he hqe (rowAt_ofEff_lab llog hl) (names_ofEff hne)
      (d_body5 hl he hqe (rowLe_ofEff_cons _ (names_ofEff hne)) (rowLe_append_nil _ _)))

/-- `toResult (withLog body5)` at the pure row, at an affine `exn`: `withLog` at `exn`'s row. -/
theorem d_p2 {llog le : (orowAlg Ξ).Lab} (hl : Ξ llog.1 = [(.lin, boolT, .unit)]) {qe : Qual}
    (he : Ξ le.1 = [(qe, .unit, .zero)]) (hqe : qe = .aff) (hne : llog.1 ≠ le.1) :
    CDerivesAt Ξ LifeCtx.empty []
      (toResultE le.1 (qsOf Ξ le.1) (withLogE llog.1 (qsOf Ξ llog.1) (body5E llog.1 le.1)))
      (.comp (.ret (.sum (.tensor .unit boolT) .unit))) := by
  subst hqe
  refine d_toResult he (by decide) (S := []) (rowAt_nil Ξ) (by simp) ?_
  refine d_withLog hl (rowAt_ofEff_lab le he) (names_ofEff (Ne.symm hne)) ?_ ?_
  · rintro ⟨o, ho, hq⟩
    simp [Row.ofEff] at ho
    subst ho
    cases hq
  · exact d_body5 hl he (by decide) (rowLe_append_nil _ _)
      (rowLe_ofEff_cons _ (names_ofEff (Ne.symm hne)))

end Typing

/-! ### The runs -/

/-- `withLog`'s handler at the name `nl`, at the linear `log`. -/
def wlH (nl : UInt32) : Val :=
  hndVal nl (qualsVal [.lin]) ⟨logRetE, .lam⟩ ⟨clausesE [logClE], .pair .lam .unit⟩

/-- `raise exn ()` at the name `ne`. -/
def raiseU (ne : UInt32) : Expr := raiseE (opArgE ne 0 .unit)

/-- The catch of `log v` in `K` by `withLog`'s handler: the clause applied to `v` and `κ`, whose
cell is still to be allocated. -/
theorem head_wlHop (nl : UInt32) (K : Kont) (v : Val) (hK : K.HasHnd nl = false) (μ : Heap) :
    Head (ℍ := ℍ) μ (hndE (wlH nl) (K.plug (performE (.val (opPayload nl 0 v))))) μ
      (.app (.val ⟨logClE, .lam⟩) (.pair (.val v) (kappaCell false nl (wlH nl) K))) := by
  have hk : kappaAt (capTag (qualsVal [.lin]).1 (0 : UInt32).toNat) nl (wlH nl) K =
      kappaCell false nl (wlH nl) K := by
    simp [capTag, qualsVal, Qual.tag, kappaAt, Val.pair, Val.i32]
  have h := Head.hop (ℍ := ℍ) μ nl 0 (qualsVal [.lin]) ⟨logRetE, .lam⟩
    ⟨clausesE [logClE], .pair .lam .unit⟩ ⟨logClE, .lam⟩ v K
    (clauseAt_clausesE [logClE] 0 .lam rfl) hK
  simp only [wlH] at hk ⊢
  rwa [hk] at h

/-! #### `withLog` outside `toResult` -/

/-- The continuation `log` captures: `toResult`'s frame around the raise. -/
def p1K (ne : UInt32) (qe : Qual) : Kont :=
  (handleK ne (qualsVal [qe]).1 (.lam (.inj₁ (.var 0))) [.lam (.inj₂ .unit)]).comp (bindK (raiseU ne))

/-- Around the allocation of `κ`'s cell. -/
def p1KA (nl ne : UInt32) (qe : Qual) : Kont :=
  (bindK (appE (.var 0) (.inj₁ .unit))).comp (.appR logClE (.pairR ⟨.inj₂ .unit, .inj₂ .unit⟩
    (.appR (.lam (kappaCBody false nl (wlH nl) (p1K ne qe))) .hole)))

/-- Around the release of `κ`'s cell, when the state function resumes `κ`. -/
def p1KF (nl ne : UInt32) (qe : Qual) : Kont :=
  (bindK (appE (.var 0) (.inj₂ .unit))).comp
    (Kont.appL (Kont.seq .hole (kResV (wlH nl) (p1K ne qe))) Val.unit)

/-- Around `toResult`'s catch of the raise, after the resume has reinstalled `withLog`'s handler. -/
def p1K0 (nl : UInt32) : Kont :=
  (bindK (appE (.var 0) (.inj₂ .unit))).comp (handleK nl (qualsVal [.lin]).1 logRetE [logClE])

theorem p1_start (nl ne : UInt32) (qe : Qual) :
    withLogE nl (qualsVal [.lin]).1 (toResultE ne (qualsVal [qe]).1 (body5E nl ne)) =
      (bindK (appE (.var 0) (.inj₁ .unit))).plug (hndE (wlH nl) ((p1K ne qe).plug
        (performE (.val (opPayload nl 0 ⟨.inj₂ .unit, .inj₂ .unit⟩))))) := by
  rfl

theorem p1_segB (nl ne : UInt32) (qe : Qual) (ℓ : Loc) :
    lookEnd 10 ((p1KA nl ne qe).plug (.val (Val.loc ℓ))) =
      (p1KF nl ne qe).plug (freeE (.val (Val.loc ℓ))) := by
  rfl

theorem p1_segC (nl ne : UInt32) (qe : Qual) :
    lookEnd 3 ((p1KF nl ne qe).plug .unit) =
      (p1K0 nl).plug (hndE (toResultV ne (qualsVal [qe])) (raiseE (.val (opPayload ne 0 Val.unit)))) := by
  rfl

theorem p1_segD (nl : UInt32) :
    lookEnd 6 ((p1K0 nl).plug (.app (.val ⟨.lam (.inj₂ .unit), .lam⟩) (.val Val.unit))) =
      .pair (.inj₂ .unit) (.inj₂ .unit) := by
  rfl

/-- **`withLog` outside `toResult` runs around `κ`'s cell to `toResult`'s catch**: `log` passes
`toResult`'s handler and is caught by `withLog`'s, around `κ`'s cell; the state function the clause
answers is applied to `ff` and resumes `κ`, which releases the cell and reinstalls both handlers;
then the raise reaches `toResult`'s handler. -/
theorem cellQuiet_p1 (nl ne : UInt32) (qe : Qual) (hne : ne ≠ nl) :
    CellQuiet (ℍ := ℍ) (withLogE nl (qualsVal [.lin]).1 (toResultE ne (qualsVal [qe]).1 (body5E nl ne)))
      ((p1K0 nl).plug (hndE (toResultV ne (qualsVal [qe])) (raiseE (.val (opPayload ne 0 Val.unit))))) := by
  refine ⟨p1KA nl ne qe, ?_, fun ℓ => ⟨p1KF nl ne qe, ?_, ?_⟩⟩
  · rw [p1_start]
    have hK : (p1K ne qe).HasHnd nl = false := by
      simp [p1K, handleK, hndValE, Kont.HasHnd, Kont.comp, bindK, raiseU, hne]
    have e : (p1KA nl ne qe).plug (allocE Val.unit) = (bindK (appE (.var 0) (.inj₁ .unit))).plug
        (.app (.val ⟨logClE, .lam⟩) (.pair (.val ⟨.inj₂ .unit, .inj₂ .unit⟩)
          (kappaCell false nl (wlH nl) (p1K ne qe)))) := by
      rw [p1KA, Kont.plug_comp]; rfl
    rw [e]
    exact Quiet.head _ (head_wlHop nl (p1K ne qe) _ hK) rfl rfl
  · have h := quiet_of_look (ℍ := ℍ) 10 ((p1KA nl ne qe).plug (.val (Val.loc ℓ))) rfl
    rwa [p1_segB] at h
  · have h := quiet_of_look (ℍ := ℍ) 3 ((p1KF nl ne qe).plug .unit) rfl
    rwa [p1_segC] at h

/-- **`withLog` outside `toResult` runs calmly to `(inr (), tt)`.** -/
theorem calm_p1 (nl ne : UInt32) (qe : Qual) (hne : ne ≠ nl) :
    Calm (ℍ := ℍ) (withLogE nl (qualsVal [.lin]).1 (toResultE ne (qualsVal [qe]).1 (body5E nl ne)))
      (.pair (.inj₂ .unit) (.inj₂ .unit)) := by
  have hB := quiet_hunwind (ℍ := ℍ) (p1K0 nl) ne 0 (qualsVal [qe]) ⟨.lam (.inj₁ (.var 0)), .lam⟩
    ⟨clausesE [.lam (.inj₂ .unit)], .pair .lam .unit⟩ ⟨.lam (.inj₂ .unit), .lam⟩ Val.unit
    (clauseAt_clausesE [.lam (.inj₂ .unit)] 0 .lam rfl)
  have hC := quiet_of_look (ℍ := ℍ) 6
    ((p1K0 nl).plug (.app (.val ⟨.lam (.inj₂ .unit), .lam⟩) (.val Val.unit))) rfl
  rw [p1_segD] at hC
  exact (cellQuiet_p1 nl ne qe hne).calm.trans ((hB.trans hC).calm)

/-! #### `toResult` outside `withLog` -/

/-- Around `withLog`'s handler: `toResult`'s frame and `withLog`'s application to `ff`. -/
def p2K0 (ne : UInt32) (qe : Qual) : Kont :=
  (handleK ne (qualsVal [qe]).1 (.lam (.inj₁ (.var 0))) [.lam (.inj₂ .unit)]).comp
    (bindK (appE (.var 0) (.inj₁ .unit)))

/-- Around the allocation of `κ`'s cell. -/
def p2KA (nl ne : UInt32) (qe : Qual) : Kont :=
  (p2K0 ne qe).comp (.appR logClE (.pairR ⟨.inj₂ .unit, .inj₂ .unit⟩
    (.appR (.lam (kappaCBody false nl (wlH nl) (bindK (raiseU ne)))) .hole)))

/-- Around the release of `κ`'s cell. -/
def p2KF (nl ne : UInt32) (qe : Qual) : Kont :=
  (handleK ne (qualsVal [qe]).1 (.lam (.inj₁ (.var 0))) [.lam (.inj₂ .unit)]).comp
    ((bindK (appE (.var 0) (.inj₂ .unit))).comp
      (Kont.appL (Kont.seq .hole (kResV (wlH nl) (bindK (raiseU ne)))) Val.unit))

/-- Between the raise and `toResult`'s handler: the state function's application and `withLog`'s
reinstalled handler. -/
def p2Kh (nl : UInt32) : Kont :=
  (bindK (appE (.var 0) (.inj₂ .unit))).comp (handleK nl (qualsVal [.lin]).1 logRetE [logClE])

theorem p2_start (nl ne : UInt32) (qe : Qual) :
    toResultE ne (qualsVal [qe]).1 (withLogE nl (qualsVal [.lin]).1 (body5E nl ne)) =
      (p2K0 ne qe).plug (hndE (wlH nl) ((bindK (raiseU ne)).plug
        (performE (.val (opPayload nl 0 ⟨.inj₂ .unit, .inj₂ .unit⟩))))) := by
  rfl

theorem p2_segB (nl ne : UInt32) (qe : Qual) (ℓ : Loc) :
    lookEnd 10 ((p2KA nl ne qe).plug (.val (Val.loc ℓ))) =
      (p2KF nl ne qe).plug (freeE (.val (Val.loc ℓ))) := by
  rfl

theorem p2_segC (nl ne : UInt32) (qe : Qual) :
    lookEnd 3 ((p2KF nl ne qe).plug .unit) =
      hndE (toResultV ne (qualsVal [qe])) ((p2Kh nl).plug (raiseE (.val (opPayload ne 0 Val.unit)))) := by
  rfl

/-- **`toResult` outside `withLog` runs around `κ`'s cell to the raise**: `log` is caught by
`withLog`'s handler around `κ`'s cell; the state function resumes `κ`, which releases the cell and
reinstalls `withLog`'s handler, inside which the raise is performed. -/
theorem cellQuiet_p2 (nl ne : UInt32) (qe : Qual) :
    CellQuiet (ℍ := ℍ) (toResultE ne (qualsVal [qe]).1 (withLogE nl (qualsVal [.lin]).1 (body5E nl ne)))
      (hndE (toResultV ne (qualsVal [qe])) ((p2Kh nl).plug (raiseE (.val (opPayload ne 0 Val.unit))))) := by
  refine ⟨p2KA nl ne qe, ?_, fun ℓ => ⟨p2KF nl ne qe, ?_, ?_⟩⟩
  · rw [p2_start]
    have e : (p2KA nl ne qe).plug (allocE Val.unit) = (p2K0 ne qe).plug
        (.app (.val ⟨logClE, .lam⟩) (.pair (.val ⟨.inj₂ .unit, .inj₂ .unit⟩)
          (kappaCell false nl (wlH nl) (bindK (raiseU ne))))) := by
      rw [p2KA, Kont.plug_comp]; rfl
    rw [e]
    exact Quiet.head _ (head_wlHop nl (bindK (raiseU ne)) _ rfl) rfl rfl
  · have h := quiet_of_look (ℍ := ℍ) 10 ((p2KA nl ne qe).plug (.val (Val.loc ℓ))) rfl
    rwa [p2_segB] at h
  · have h := quiet_of_look (ℍ := ℍ) 3 ((p2KF nl ne qe).plug .unit) rfl
    rwa [p2_segC] at h

/-- **`toResult` outside `withLog` runs calmly to `inr ()`**: the raise passes `withLog`'s handler,
which the unwind drops with its state, and `toResult` answers `inr ()`. -/
theorem calm_p2 (nl ne : UInt32) (qe : Qual) (hne : nl ≠ ne) :
    Calm (ℍ := ℍ) (toResultE ne (qualsVal [qe]).1 (withLogE nl (qualsVal [.lin]).1 (body5E nl ne)))
      (.inj₂ .unit) := by
  have hK : Kont.Catches ne (p2Kh nl) = false := by
    simp [p2Kh, Kont.Catches, handleK, hndValE, Kont.comp, bindK, hne]
  have hB := Quiet.head (ℍ := ℍ) .hole (fun μ => Head.hunwind μ ne 0 (qualsVal [qe])
    ⟨.lam (.inj₁ (.var 0)), .lam⟩ ⟨clausesE [.lam (.inj₂ .unit)], .pair .lam .unit⟩
    ⟨.lam (.inj₂ .unit), .lam⟩ Val.unit (p2Kh nl)
    (clauseAt_clausesE [.lam (.inj₂ .unit)] 0 .lam rfl) hK) rfl rfl
  have hC := quiet_beta (ℍ := ℍ) .hole (.inj₂ .unit) Val.unit
  exact (cellQuiet_p2 nl ne qe).calm.trans ((hB.trans hC).calm)


/-! ### E5 -/

/-- **No `exn` signature of the context is `unr`.** -/
def NoUnrExn (Ξ : EffCtx) : Prop := ∀ n, Ξ n ≠ [(.unr, .unit, .zero)]

/-- `ΞA` is admissible and has no `unr` `exn` signature, so `NoUnrExn` is not vacuous at the
admissible contexts. -/
theorem noUnrExn_ΞA : NoUnrExn ΞA := by
  intro n h
  rcases ΞA_cases n with h0 | h0
  · rw [h0] at h; simp at h
  · rw [h] at h0
    simp [eSigs] at h0

section E5
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- **`withLog` outside `toResult` is typed at `J₁`**, at the pure row. -/
theorem der_p1_J₁ {llog le : (orowAlg Ξ).Lab} (hl : Ξ llog.1 = [(.lin, boolT, .unit)]) {qe : Qual}
    (he : Ξ le.1 = [(qe, .unit, .zero)]) (hqe : qe ≠ .lin) (hne : llog.1 ≠ le.1) :
    (𝕁).der [] ((𝕁).withLog llog ((𝕁).toResult le ((𝕁).body5 llog le)))
      ((𝕁).F (𝕁).EA.unit ((𝕁).Tensor ((𝕁).Sum (𝕁).UnitT (𝕁).UnitT) (𝕁).bool)) := by
  have hd := d_p1 hl he hqe hne
  rw [p1_val]
  exact der_J₁_ret (A := .tensor (.sum .unit .unit) boolT)
    (by simpa using closedAt_of_derives hd.toCDerives) hd

/-- **`toResult` outside `withLog` is typed at `J₁`**, at the pure row, at an affine `exn`. -/
theorem der_p2_J₁ {llog le : (orowAlg Ξ).Lab} (hl : Ξ llog.1 = [(.lin, boolT, .unit)]) {qe : Qual}
    (he : Ξ le.1 = [(qe, .unit, .zero)]) (hqe : qe = .aff) (hne : llog.1 ≠ le.1) :
    (𝕁).der [] ((𝕁).toResult le ((𝕁).withLog llog ((𝕁).body5 llog le)))
      ((𝕁).F (𝕁).EA.unit ((𝕁).Sum ((𝕁).Tensor (𝕁).UnitT (𝕁).bool) (𝕁).UnitT)) := by
  have hd := d_p2 hl he hqe hne
  rw [p2_val]
  exact der_J₁_ret (A := .sum (.tensor .unit boolT) .unit)
    (by simpa using closedAt_of_derives hd.toCDerives) hd

/-- **`withLog` outside `toResult` runs to `(inr (), tt)`**, showing nothing. -/
theorem runsTo_p1 {llog le : (orowAlg Ξ).Lab} (hl : Ξ llog.1 = [(.lin, boolT, .unit)]) {qe : Qual}
    (he : Ξ le.1 = [(qe, .unit, .zero)]) (hne : le.1 ≠ llog.1) :
    (𝕁).RunsTo (𝕁).R₀ ((𝕁).withLog llog ((𝕁).toResult le ((𝕁).body5 llog le)))
      ((𝕁).pair ((𝕁).inr (𝕁).unitV) (𝕁).tt) [] := by
  rw [p1_val, qsOf_eq hl, qsOf_eq he]
  exact runsTo_of_calm (𝕁).R₀ (v := ⟨_, .pair (.inj₂ .unit) (.inj₂ .unit)⟩)
    (calm_p1 llog.1 le.1 qe hne)

/-- **`toResult` outside `withLog` runs to `inr ()`**, showing nothing. -/
theorem runsTo_p2 {llog le : (orowAlg Ξ).Lab} (hl : Ξ llog.1 = [(.lin, boolT, .unit)]) {qe : Qual}
    (he : Ξ le.1 = [(qe, .unit, .zero)]) (hne : llog.1 ≠ le.1) :
    (𝕁).RunsTo (𝕁).R₀ ((𝕁).toResult le ((𝕁).withLog llog ((𝕁).body5 llog le)))
      ((𝕁).inr (𝕁).unitV) [] := by
  rw [p2_val, qsOf_eq hl, qsOf_eq he]
  exact runsTo_of_calm (𝕁).R₀ (v := ⟨_, .inj₂ .unit⟩) (calm_p2 llog.1 le.1 qe hne)

/-- **E5's labels**: a `log` and an `exn` label, at a rich context. -/
theorem labelsAt_E5 (hΞ : AdmEff Ξ) : ∃ ls, (𝕁).LabelsAt [(𝕁).sigLog, (𝕁).sigExn] ls := by
  obtain ⟨ll, -, -, hll, -⟩ := rich_labs hΞ.2.2 (E := [(.lin, boolT, .unit)]) (by simp [eSigs])
  obtain ⟨le, -, -, hle, -⟩ := rich_labs hΞ.2.2 (E := [(.aff, .unit, .zero)]) (by simp [eSigs])
  refine ⟨[ll, le], rfl, ?_, fun k h₁ _ => ?_⟩
  · have hne : ll ≠ le := lab_ne_of_sig (by rw [hll, hle]; simp)
    exact List.nodup_cons.mpr ⟨fun h => hne (List.mem_singleton.mp h), List.nodup_singleton _⟩
  · match k, h₁ with
    | 0, _ => exact (sig_log_iff ll).mpr hll
    | 1, _ => exact (sig_exn_iff le).mpr ⟨.aff, hle, by decide⟩

/-- **E5, nested handlers in both orders, at `J₁`**, at every admissible effect context with no
`unr` `exn` signature. -/
theorem nestedHandlers_J₁ (hΞ : AdmEff Ξ) (hx : NoUnrExn Ξ) : (𝕁).NestedHandlers := by
  refine ⟨labelsAt_E5 hΞ, fun ls hls llog le hlsEq => ?_⟩
  subst hlsEq
  have hl := (sig_log_iff llog).mp (hls.2.2 0 (by simp) (by simp))
  obtain ⟨qe, he, hqe⟩ := (sig_exn_iff le).mp (hls.2.2 1 (by simp) (by simp))
  have hqa : qe = .aff := by
    cases qe with
    | lin => exact absurd rfl hqe
    | aff => rfl
    | unr => exact absurd he (hx le.1)
  have hne : llog.1 ≠ le.1 := fun h => by
    rw [h, he] at hl
    simp at hl
  exact ⟨der_p1_J₁ hl he hqe hne, runsTo_p1 hl he (Ne.symm hne), der_p2_J₁ hl he hqa hne,
    runsTo_p2 hl he hne⟩

end E5

end Targets.Inst

end

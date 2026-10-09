import Targets.Instance.E5
import Targets.Instance.E10
import Targets.Instance.AlgSim
import Targets.Instance.CancelRuns
import Targets.Base.LookMem
import Targets.Instance.FinRaise

/-!
# The Instance — finalisers with effects at `J₁`: `e7b`, a nested cancel, and the witnesses they give

`J₁`'s kernel takes SPEC §27's `[then]`, so a finaliser may raise to a live handler and perform an
operation of one (decisions D2, D3 of 2026-10-08).  Two programs at `J₁`, each typed with the cancel
rows of §27 and run by Core's machine (`runM`):

* **`e7b`** (A's E7b): `handle exn {…} (timeout (body (raise exn ())))`.  `wait`'s cancel row holds
  the finaliser's raise of `exn` (`finRaise`), whose handler is live outside the `timeout`
  (`d_e7b`, at every two labels; `der_e7b_J₁`).
* **`ncAff`**: a `timeout` of `wait₂` around a `timeout` of `wait₁` whose body's finaliser performs
  `wait₂`.  `wait₁`'s cancel row holds `wait₂` (`finWait`, `PendLe` of nothing); the outer handler
  cancels the finaliser's continuation, a cancel nested in a cancel (`d_ncAff`, `der_ncAff_J₁`).

What they show, at every effect context declaring `exn` at `1` and `wait` at `2` and `8` (the
admissible `ΞA` among them):

* **`CfinQuiet` fails** (`not_cfinQuiet_J₁`): `e7b`'s run reaches its finaliser's raise under the
  cancel's `cfin` frame, a `[cfin-raise]` step.
* **A cancel nested in a cancel arises, and S5's trace passes the running finaliser**
  (`ncAff_pend_J₁`): `ncAff`'s run reaches the cancel of `wait₂`'s affine continuation at its cell,
  whose region holds no finaliser and the running finaliser of the cancel of `wait₁`
  (`acts = [pend none]`); from its start, `[cfin-cancel]` then `[cancel]` is a cancel trace that
  takes `pend`, and no trace that reads the region by its finalisers alone follows it.
* **The no-interception condition has teeth** (`finRow_teeth_J₁`): `e7b`'s cancel fires a finaliser
  that meets `FinRow` at no endings without `exn`; its fire, its start and the raise it lets escape
  (`finEnd` of an error) are a prefix of no cancel trace at `noFinRaise`.

`[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Head Kont Steps Step1 Heap performE raiseE hndE hndVal opPayload cancelVal kappaC
  ccatchE)
open BoCa.Lifetime (LifeCtx)
open Targets (EffCtx orowRF orowAlg ORow RowAt rowAt_nil CDerivesAt LMem runM runM_sound)

/-- `wait (_, k) ⇒ cancel k; return (inr ())`: A's `timeoutCl` at our instance. -/
def timeoutClA : Expr := .lam (.letpair (.var 0) (bindE (cancelE (.var 0)) (.inj₂ .unit)))

/-- `timeout M` at the name `nw` and the tags `qw`: `return x ⇒ inl x`, and `timeoutClA`. -/
def timeoutHE (nw : UInt32) (qw M : Expr) : Expr :=
  (handleK nw qw (.lam (.inj₁ (.var 0))) [timeoutClA]).plug M

/-- `(wait (); return tt) then x. return x unwind D` at the name `nw`. -/
def bodyFE (nw : UInt32) (D : Expr) : Expr :=
  (thenK (.var 0) D).plug (bindE (performE (opArgE nw 0 .unit)) (.inj₂ .unit))

section Typing
variable {Ξ : EffCtx}

theorem clauseTy_resF {S : Row} {R A B : VTy} {q : Qual} (F : CTy)
    (h : (B.isZero && q != .lin) = false) :
    clauseTy S R (q, A, B) F = .bang (.thunk (.arr (.tensor A (kTy S R q B F)) (CTy.effOf S R))) := by
  simp [clauseTy, h]

/-- **`wait (_, k) ⇒ cancel k; return (inr ())`** at an affine `1 ↠ 1` whose cancel row `F` holds
operations of the clause's row `S`: `κ`'s cancel at `F_{F ⊕ Σ} 1`, read at `Σ`. -/
theorem d_timeoutClA {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {S : Row} {X : VTy} {F : CTy}
    (hF : F.isTop = false) (hFS : RowLe (F.rowOf ++ S) S) :
    CDerivesAt Ξ Δ Γ timeoutClA (.val (clauseTy S (.sum X .unit) (.aff, .unit, .unit) F)) := by
  rw [clauseTy_resF F rfl]
  refine d_lamBang hΓ (.tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_)
  refine .effLet (A := .unit) (.left (.left (.dead (deadSplit hΓ))))
    (fun _ => fun s hs hl => ?_) (fun _ => fun s hs hl => ?_) ?_ ?_
  · simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | rfl | hs
    · cases hl
    · cases hl
    · cases hl
    · exact dead_noLive (P := fun s => s.ty.Drop) hΓ s hs hl
  · simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | rfl | hs
    · cases hl
    · cases hl
    · cases hl
    · exact dead_noLive (P := fun s => ∃ A, s.ty = .bang A) hΓ s hs hl
  · have hct : cancelTy S F = CTy.effOf (F.rowOf ++ S) .unit := by simp [cancelTy, hF]
    refine .effSub hFS ?_
    rw [← hct]
    exact .proj₂ (.force (C := .amp (.arr .unit (CTy.effOf S (.sum X .unit))) (cancelTy S F))
      (.here (.drop rfl (.cons hΓ.toP))))
  · exact .effSub (rowLe_nil S) (.ret (.sumI₂ (.unitI (.drop rfl (.cons (.cons (.cons hΓ.toP)))))))

end Typing


section Typing2
variable {Ξ : EffCtx}

/-- A one-operation row finds its operation at its key alone. -/
theorem find_ofEff_one {n : UInt32} {e : Qual × VTy × VTy} {fs : Nat → CTy} {m i : UInt32}
    {o : OpSig} (h : Row.find (Row.ofEff n [e] 0 fs) m i = some o) :
    m = n ∧ i = 0 ∧ o = ⟨n, 0, e.1, e.2.1, e.2.2, fs 0⟩ := by
  obtain ⟨rfl, j, hj, rfl, rfl⟩ := Row.find_ofEff n [e] 0 fs m i o h
  obtain rfl : j = 0 := by simp at hj; omega
  exact ⟨rfl, rfl, rfl⟩

/-- **The handler frame at cancel rows**: `[handle]` at a value form, its `j`-th operation's cancel
row `fs j`, the handled row tied to `Ξ` at the empty cancel rows. -/
theorem d_handleKF {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A R : VTy} {n : UInt32} {r : Expr}
    {cs : List Expr} {M : Expr} {fs : Nat → CTy} (hAt : RowAt Ξ (Row.ofEff n (Ξ n) 0 ++ S))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : (Ξ n).length ≤ 2 ^ 32)
    (hv : IsVal (.pair r (clausesE cs)))
    (hc : CDerivesAt Ξ Δ (kill Γ) (.pair r (clausesE cs))
      (.val (.tensor (retTy S A R) (clausesTy S R (Ξ n) fs))))
    (he : CDerivesAt Ξ Δ Γ M (.comp (CTy.effOf (Row.ofEff n (Ξ n) 0 fs ++ S) A))) :
    CDerivesAt Ξ Δ Γ ((handleK n (qsOf Ξ n) r cs).plug M) (.comp (CTy.effOf S R)) :=
  .effHandleV (rowAt_ofEff_fs hAt) (splitP_kill_left Γ) (kill_dead Γ).toP (.val ⟨_, hv⟩) hc hn0
    hnS hlen he

theorem isVal_timeoutHA : IsVal (.pair (.lam (.inj₁ (.var 0))) (clausesE [timeoutClA])) :=
  .pair .lam (.pair .lam .unit)

/-- **`timeout M`** at a label of `wait : 1 ↠ 1` affine, at the row `S`, `wait`'s cancel row `F`
holding operations of `S`. -/
theorem d_timeoutHA {lw : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) {S : Row}
    (hS : RowAt Ξ S) (hnS : ∀ o ∈ S, o.n ≠ lw.1) {X : VTy} {F : CTy} (hF : F.isTop = false)
    (hFS : RowLe (F.rowOf ++ S) S) {M : Expr}
    (hM : CDerivesAt Ξ LifeCtx.empty [] M
      (.comp (CTy.effOf (Row.ofEff lw.1 [(.aff, .unit, .unit)] 0 (fun _ => F) ++ S) X))) :
    CDerivesAt Ξ LifeCtx.empty [] (timeoutHE lw.1 (qsOf Ξ lw.1) M)
      (.comp (CTy.effOf S (.sum X .unit))) := by
  rw [← hlw] at hM
  refine d_handleKF (fs := fun _ => F) (Targets.rowAt_append (rowAt_rowOf lw) hS) lw.2.1 hnS
    lw.2.2.2 isVal_timeoutHA ?_ hM
  rw [hlw]
  refine .tensorI .nil (d_lamBang .nil (.effSub (rowLe_nil S) (.ret (.sumI₁ (.var (.here .nil))))))
    (.tensorI .nil (d_timeoutClA .nil hF hFS) (.unitI .nil))

/-- A row of names other than `n` is below `n`'s signature row at any cancel rows before it. -/
theorem rowLe_ofEff_consF {n : UInt32} (E : List (Qual × VTy × VTy)) (fs : Nat → CTy) {T : Row}
    (hT : ∀ o ∈ T, o.n ≠ n) : RowLe T (Row.ofEff n E 0 fs ++ T) := by
  refine RowLe.of_find fun m i o hf => ?_
  rw [Row.find_append, Row.find_ofEff_ne n E 0 fs m i ?_, Option.none_or]
  · exact hf
  · obtain ⟨hm, rfl, -⟩ := Row.find_mem hf
    exact hT o hm

/-- `wait`'s operation at the cancel row `F`, as the handled row of a `timeout` finds it. -/
theorem find_wait_at (nw : UInt32) (F : CTy) (S : Row) :
    Row.find (Row.ofEff nw [(.aff, .unit, .unit)] 0 (fun _ => F) ++ S) nw 0 =
      some ⟨nw, 0, .aff, .unit, .unit, F⟩ := by
  simp [Row.ofEff, Row.find]

/-- **`(wait (); return tt) then x. return x unwind D`**, at the handled row `wait⟨F⟩ ⊙ S` of a
`timeout`: the finaliser at a row `SD` below it, and `F` above what the finaliser may do when
`wait`'s continuation is cancelled (`[] ⋈ SD ≤ F`). -/
theorem d_bodyFA {lw : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) {S SD : Row}
    {F : CTy} (hNZ : (Row.ofEff lw.1 [(.aff, .unit, .unit)] 0 (fun _ => F) ++ S).NZ)
    (hUq : (Row.ofEff lw.1 [(.aff, .unit, .unit)] 0 (fun _ => F) ++ S).Uniq)
    (hDS : RowLe SD (Row.ofEff lw.1 [(.aff, .unit, .unit)] 0 (fun _ => F) ++ S))
    (hfin : ThenLe (.ret .unit) SD F) {D : Expr}
    (hD : CDerivesAt Ξ LifeCtx.empty [⟨.unit, false⟩] (D.shift 1 0) (.comp (CTy.effOf SD .unit))) :
    CDerivesAt Ξ LifeCtx.empty [] (bodyFE lw.1 D)
      (.comp (CTy.effOf (Row.ofEff lw.1 [(.aff, .unit, .unit)] 0 (fun _ => F) ++ S) boolT)) := by
  show CDerivesAt Ξ LifeCtx.empty []
    (thenE (.var 0) (D.shift 1 0) (bindE (performE (opArgE lw.1 0 .unit)) (.inj₂ .unit))) _
  have hM : CDerivesAt Ξ LifeCtx.empty [] (bindE (performE (opArgE lw.1 0 .unit)) (.inj₂ .unit))
      (.comp (CTy.effOf (Row.ofEff lw.1 [(.aff, .unit, .unit)] 0 ++ []) boolT)) :=
    .effLet (A := .unit) .nil (fun _ => fun _ h => absurd h List.not_mem_nil)
      (fun _ => fun _ h => absurd h List.not_mem_nil) (d_performLab lw hlw rfl (.unitI .nil))
      (.effSub (rowLe_nil _) (.ret (.sumI₂ (.unitI (.drop rfl .nil)))))
  refine .effThen (SM := Row.ofEff lw.1 [(.aff, .unit, .unit)] 0 ++ []) (SD := SD) .nil hNZ hUq
    (fun _ => fun _ h => absurd h List.not_mem_nil) ?_ hDS ?_ ?_ hM
    (.effSub (rowLe_nil _) (.ret (.var (.here .nil)))) hD
  · intro n i o hf
    rw [List.append_nil] at hf
    obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one hf
    refine ⟨_, find_wait_at lw.1 F S, ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
    rw [finLe_iff]
    exact .inr ⟨rfl, RowLe.nil _⟩
  · intro n i o o' hf hf' _
    rw [List.append_nil] at hf
    obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one hf
    rw [find_wait_at lw.1 F S] at hf'
    cases hf'
    exact hfin
  · intro _ o ho
    rw [List.append_nil] at ho
    simp only [Row.ofEff, List.mem_cons, List.not_mem_nil, or_false] at ho
    subst ho
    exact ⟨fun h => by simp [OpSig.abort, VTy.isZero] at h, fun _ => trivial⟩

/-- A's `e7b` at our instance: `handle exnₒ {…} (timeout (body (raise exnₒ ())))`. -/
def e7bE (nw no : UInt32) (qw qo : Expr) : Expr :=
  toResultE no qo (timeoutHE nw qw (bodyFE nw (raiseE (opArgE no 0 .unit))))

/-- The cancel row of `wait` in `e7b`: the finaliser may raise `exnₒ`. -/
abbrev finRaise (no : UInt32) (qo : Qual) : CTy :=
  CTy.effOf [⟨no, 0, qo, .unit, .zero, .ret .unit⟩] .unit

theorem thenLe_finRaise (no : UInt32) (qo : Qual) :
    ThenLe (.ret .unit) (Row.ofEff no [(qo, .unit, .zero)] 0 ++ []) (finRaise no qo) := by
  rw [ThenLe]
  refine .inr ⟨rfl, fun n i o hf => by simp [CTy.rowOf, Row.find] at hf, fun n i o hf => ?_⟩
  rw [List.append_nil] at hf
  obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one hf
  refine ⟨_, by simp [CTy.rowOf, CTy.effOf, Row.find], ⟨rfl, rfl, rfl, rfl, rfl⟩, fun h => ?_⟩
  simp [capB, VTy.isZero] at h

/-- **`e7b` is typed by `J₁`'s kernel**: `wait`'s cancel row holds the finaliser's raise of
`exnₒ`, whose handler is live outside the `timeout`. -/
theorem d_e7b {lw lo : (orowAlg Ξ).Lab} (hlw : Ξ lw.1 = [(.aff, .unit, .unit)]) {qo : Qual}
    (hlo : Ξ lo.1 = [(qo, .unit, .zero)]) (hqo : qo ≠ .lin) (hne : lw.1 ≠ lo.1) :
    CDerivesAt Ξ LifeCtx.empty [] (e7bE lw.1 lo.1 (qsOf Ξ lw.1) (qsOf Ξ lo.1))
      (.comp (.ret (.sum (.sum boolT .unit) .unit))) := by
  have hSlo := rowAt_ofEff_lab lo hlo
  have hnlo : ∀ o ∈ Row.ofEff lo.1 [(qo, .unit, .zero)] 0 ++ [], o.n ≠ lw.1 := names_ofEff hne.symm
  refine d_toResult hlo hqo (S := []) (rowAt_nil Ξ) (by simp) ?_
  refine d_timeoutHA hlw hSlo hnlo (X := boolT) (F := finRaise lo.1 qo) rfl ?_ ?_
  · refine RowLe.of_find fun n i o hf => ?_
    rw [Row.find_append] at hf
    simp only [CTy.rowOf, CTy.effOf] at hf
    rw [List.append_nil]
    by_cases hk : n = lo.1 ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := hk
      simp [Row.find] at hf
      subst hf
      simp [Row.ofEff, Row.find]
    · have : Row.find [⟨lo.1, 0, qo, .unit, .zero, .ret .unit⟩] n i = none := by
        simp only [Row.find, List.find?_cons, List.find?_nil]
        rw [decide_eq_false hk]
      rw [this, Option.none_or, List.append_nil] at hf
      exact hf
  refine d_bodyFA hlw ?_ ?_ (rowLe_ofEff_consF _ _ hnlo) (thenLe_finRaise lo.1 qo) ?_
  · intro o ho
    simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ho
    rcases ho with rfl | rfl
    · exact lw.2.1
    · exact lo.2.1
  · simp [Row.Uniq, Row.ofEff, hne]
  · exact d_raiseLab (.cons .nil) lo hlo hqo .unit

/-- A's `ncAff` at our instance: a `timeout` of `wait₂` around a `timeout` of `wait₁` whose body's
finaliser performs `wait₂`. -/
def ncAffE (n₁ n₂ : UInt32) (q₁ q₂ : Expr) : Expr :=
  timeoutHE n₂ q₂ (timeoutHE n₁ q₁ (bodyFE n₁ (performE (opArgE n₂ 0 .unit))))

/-- The cancel row of `wait₁` in `ncAff`: the finaliser performs `wait₂`, whose own cancel row is
empty. -/
abbrev finWait (n₂ : UInt32) : CTy := CTy.effOf [⟨n₂, 0, .aff, .unit, .unit, .ret .unit⟩] .unit

theorem thenLe_finWait (n₂ : UInt32) :
    ThenLe (.ret .unit) (Row.ofEff n₂ [(.aff, .unit, .unit)] 0 ++ []) (finWait n₂) := by
  rw [ThenLe]
  refine .inr ⟨rfl, fun n i o hf => by simp [CTy.rowOf, Row.find] at hf, fun n i o hf => ?_⟩
  rw [List.append_nil] at hf
  obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one hf
  refine ⟨_, by simp [CTy.rowOf, CTy.effOf, Row.find], ⟨rfl, rfl, rfl, rfl, rfl⟩, fun _ => ?_⟩
  rw [PendLe]
  exact .inr ⟨rfl, fun n i o hf => by simp [CTy.rowOf, Row.find] at hf,
    fun n i o hf => by simp [CTy.rowOf, Row.find] at hf⟩

/-- A one-operation cancel row whose operation the row finds as it is is below the row. -/
theorem rowLe_single_append {o : OpSig} {S : Row} (hS : Row.find S o.n o.i = some o) :
    RowLe ([o] ++ S) S := by
  refine RowLe.of_find fun n i o' hf => ?_
  rw [Row.find_append] at hf
  by_cases hk : n = o.n ∧ i = o.i
  · obtain ⟨rfl, rfl⟩ := hk
    simp [Row.find] at hf
    subst hf
    exact hS
  · have : Row.find [o] n i = none := by
      simp only [Row.find, List.find?_cons, List.find?_nil]
      rw [decide_eq_false hk]
    rw [this, Option.none_or] at hf
    exact hf

/-- **`ncAff` is typed by `J₁`'s kernel**: `wait₁`'s cancel row holds the finaliser's `wait₂`,
whose live handler is the outer `timeout`. -/
theorem d_ncAff {l₁ l₂ : (orowAlg Ξ).Lab} (h₁ : Ξ l₁.1 = [(.aff, .unit, .unit)])
    (h₂ : Ξ l₂.1 = [(.aff, .unit, .unit)]) (hne : l₁.1 ≠ l₂.1) :
    CDerivesAt Ξ LifeCtx.empty [] (ncAffE l₁.1 l₂.1 (qsOf Ξ l₁.1) (qsOf Ξ l₂.1))
      (.comp (.ret (.sum (.sum boolT .unit) .unit))) := by
  have hS₂ := rowAt_ofEff_lab l₂ h₂
  have hn₂ : ∀ o ∈ Row.ofEff l₂.1 [(.aff, .unit, .unit)] 0 ++ [], o.n ≠ l₁.1 := names_ofEff hne.symm
  refine d_timeoutHA h₂ (S := []) (rowAt_nil Ξ) (by simp) (X := .sum boolT .unit) (F := .ret .unit)
    rfl (by simpa [CTy.rowOf] using RowLe.refl ([] : Row)) ?_
  refine d_timeoutHA h₁ hS₂ hn₂ (X := boolT) (F := finWait l₂.1) rfl
    (rowLe_single_append (by simp [Row.ofEff, Row.find])) ?_
  refine d_bodyFA h₁ ?_ ?_ (rowLe_ofEff_consF _ _ hn₂) (thenLe_finWait l₂.1) ?_
  · intro o ho
    simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ho
    rcases ho with rfl | rfl
    · exact l₁.2.1
    · exact l₂.2.1
  · simp [Row.Uniq, Row.ofEff, hne]
  · exact d_performLab l₂ h₂ rfl (.unitI (.cons .nil))

end Typing2


/-! ### The runs -/

/-- The tags of an affine signature. -/
abbrev qA : Expr := (qualsVal [.aff]).1

/-- `e7b` at `wait` of the name `2` and `exn` of the name `1`. -/
abbrev e7b21 : Expr := e7bE 2 1 qA qA

/-- The handler value of `timeout` at the name `n`. -/
def timeoutV (n : UInt32) : Val :=
  ⟨hndValE n qA (.lam (.inj₁ (.var 0))) [timeoutClA], .pair .prim (.pair (qualsVal _).2
    (.pair .lam (.pair .lam .unit)))⟩

/-- The canceller's context in `e7b`: `toResult` of `1`, and the clause's `□; return (inr ())`. -/
def K0b : Kont := (handleK 1 qA (.lam (.inj₁ (.var 0))) [.lam (.inj₂ .unit)]).comp (bindK (.inj₂ .unit))

/-- `e7b`'s cancelled region: the finaliser frame and `□; return tt`. -/
def Kb : Kont := (thenK (.var 0) (raiseE (opArgE 1 0 .unit))).comp (bindK (.inj₂ .unit))

theorem e7b_run5 :
    runM 5 [] e7b21 = ([(1, Val.unit)], K0b.plug (cancelE (kappaC true 1 (timeoutV 2) Kb))) := by
  rfl

theorem e7b_run10 : runM 5 [(1, Val.unit)] (K0b.plug (cancelE (kappaC true 1 (timeoutV 2) Kb))) =
    ([], K0b.plug (Targets.cancelOf Kb)) := by
  rfl

/-- The fired finaliser `λ_. raise exn ()`. -/
def finRaiseV : Val := Val.lam (raiseE (opArgE 1 0 .unit))

/-- Where a cancel-mode finaliser runs in `e7b`: the canceller's context, `ccatch` and `cfin`. -/
def Kfb : Kont := (K0b.comp (ccatchK .hole)).comp (.appR (.app (.prim .cfin) (cancelVal none).1) .hole)

theorem e7b_run12 : runM 2 [] (K0b.plug (Targets.cancelOf Kb)) =
    ([], Kfb.plug (raiseE (.val (opPayload 1 0 Val.unit)))) := by
  rfl

/-- `ncAff` at `wait` of the names `2` (inner) and `8` (outer). -/
abbrev nc28 : Expr := ncAffE 2 8 qA qA

/-- The outer clause's `□; return (inr ())`, the nested cancel's canceller. -/
def K0n : Kont := bindK (.inj₂ .unit)

/-- The outer `wait`'s cancelled region: the inner clause's `□; return (inr ())`, the inner cancel's
delimiter, and its running finaliser's `cfin`. -/
def Kn : Kont :=
  (bindK (.inj₂ .unit)).comp ((ccatchK .hole).comp (.appR (.app (.prim .cfin) (cancelVal none).1) .hole))

theorem nc_run17 :
    runM 17 [] nc28 = ([(1, Val.unit)], K0n.plug (cancelE (kappaC true 1 (timeoutV 8) Kn))) := by
  rfl

theorem nc_run22 : runM 5 [(1, Val.unit)] (K0n.plug (cancelE (kappaC true 1 (timeoutV 8) Kn))) =
    ([], K0n.plug (Targets.cancelOf Kn)) := by
  rfl

section Witness
variable {Ξ : EffCtx}

local notation "𝕁" => ourInst (ℍ := ℍ) orowRF Ξ J₁

/-- A run of Core's machine is a path of our instance's machine, under every runner, at its state. -/
theorem rreach_of_steps (R : (𝕁).Runner) {μ μ' : Heap} {e e' : Expr} {s : R.St}
    (h : Steps (ℍ := ℍ) μ e μ' e') : (𝕁).RReach R ((μ, e), s) ((μ', e'), s) := by
  induction h with
  | refl => exact .refl
  | more h₁ _ ih =>
      obtain ⟨K, a, a', rfl, rfl, hh⟩ := h₁
      exact Relation.ReflTransGen.head ⟨_, .mach (OStep.mach hh)⟩ ih

/-- A run of Core's machine is a run of our instance's machine. -/
theorem reach_of_steps {μ μ' : Heap} {e e' : Expr} (h : Steps (ℍ := ℍ) μ e μ' e') :
    (𝕁).Reach (μ, e) (μ', e') := by
  induction h with
  | refl => exact .refl
  | more h₁ _ ih =>
      obtain ⟨K, a, a', rfl, rfl, hh⟩ := h₁
      exact Relation.ReflTransGen.head ⟨_, OStep.mach hh⟩ ih

/-- `exn` at the name `1`. -/
def labE (h1 : Ξ 1 = Eab) : (orowAlg Ξ).Lab := ⟨1, by decide, by rw [h1]; simp, by rw [h1]; simp⟩

/-- `wait` at a name. -/
def labW (n : UInt32) (hn : n ≠ 0) (h : Ξ n = Ew) : (orowAlg Ξ).Lab :=
  ⟨n, hn, by rw [h]; simp, by rw [h]; simp⟩

theorem qsOf_Ew {n : UInt32} (h : Ξ n = Ew) : qsOf Ξ n = qA := by rw [qsOf, h]; rfl

theorem qsOf_Eab (h : Ξ 1 = Eab) : qsOf Ξ 1 = qA := by rw [qsOf, h]; rfl

/-- **`e7b` is typed by `J₁`**, at every effect context declaring `exn` at `1` and `wait` at `2`. -/
theorem der_e7b_J₁ (h1 : Ξ 1 = Eab) (h2 : Ξ 2 = Ew) :
    (𝕁).der [] e7b21 ((𝕁).F (orowAlg Ξ).unit (OVTy.ofV (.sum (.sum boolT .unit) .unit))) := by
  have hd := d_e7b (lw := labW 2 (by decide) h2) (lo := labE h1) h2 h1 (by decide)
    (show (2 : UInt32) ≠ 1 by decide)
  rw [show (labW 2 (by decide) h2 : (orowAlg Ξ).Lab).1 = 2 from rfl,
    show (labE h1 : (orowAlg Ξ).Lab).1 = 1 from rfl, qsOf_Ew h2, qsOf_Eab h1] at hd
  exact der_J₁_ret (by simpa using closedAt_of_derives hd.toCDerives) hd

/-- `e7b`'s run reaches its finaliser's raise under `cfin`. -/
theorem e7b_reach12 :
    (𝕁).RReach (𝕁).R₀ ((𝕁).rinit (𝕁).R₀ e7b21)
      ((Adequacy.emptyMem, Kfb.plug (raiseE (.val (opPayload 1 0 Val.unit)))), ()) := by
  have h₁ := runM_sound (ℍ := ℍ) 5 [] e7b21
  rw [e7b_run5] at h₁
  have h₂ := runM_sound (ℍ := ℍ) 5 [(1, Val.unit)] (K0b.plug (cancelE (kappaC true 1 (timeoutV 2) Kb)))
  rw [e7b_run10] at h₂
  have h₃ := runM_sound (ℍ := ℍ) 2 [] (K0b.plug (Targets.cancelOf Kb))
  rw [e7b_run12] at h₃
  exact ((rreach_of_steps (𝕁).R₀ h₁).trans (rreach_of_steps (𝕁).R₀ h₂)).trans
    (rreach_of_steps (𝕁).R₀ h₃)

/-- **`CfinQuiet` fails at `J₁`**, at every effect context declaring `exn` at `1` and `wait` at
`2`: `e7b`, typed by `J₁`, reaches its finaliser's raise of `exn` under the cancel's `cfin` frame,
a `[cfin-raise]` step (SPEC §27 types a finaliser that raises to a live handler). -/
theorem not_cfinQuiet_J₁ (h1 : Ξ 1 = Eab) (h2 : Ξ 2 = Ew) : ¬ CfinQuiet (ℍ := ℍ) orowRF Ξ J₁ := by
  intro hq
  refine hq _ ⟨e7b21, _, (𝕁).R₀, (), r₀_respects, der_e7b_J₁ h1 h2, e7b_reach12⟩
    ⟨K0b.comp (ccatchK .hole), cancelVal none, .hole, 1, 0, Val.unit, ?_, rfl⟩
  show Kfb.plug _ = _
  rw [Kfb, Kont.plug_comp]
  rfl

/-- **`ncAff` is typed by `J₁`**, at every effect context declaring `wait` at `2` and `8`. -/
theorem der_ncAff_J₁ (h2 : Ξ 2 = Ew) (h8 : Ξ 8 = Ew) :
    (𝕁).der [] nc28 ((𝕁).F (orowAlg Ξ).unit (OVTy.ofV (.sum (.sum boolT .unit) .unit))) := by
  have hd := d_ncAff (l₁ := labW 2 (by decide) h2) (l₂ := labW 8 (by decide) h8) h2 h8
    (show (2 : UInt32) ≠ 8 by decide)
  rw [show (labW 2 (by decide) h2 : (orowAlg Ξ).Lab).1 = 2 from rfl,
    show (labW 8 (by decide) h8 : (orowAlg Ξ).Lab).1 = 8 from rfl, qsOf_Ew h2, qsOf_Ew h8] at hd
  exact der_J₁_ret (by simpa using closedAt_of_derives hd.toCDerives) hd

/-- The handler of `timeout`, as A's handler. -/
def timeoutHnd : OVal × List OVal := (⟨.lam (.inj₁ (.var 0)), .lam⟩, [⟨timeoutClA, .lam⟩])

theorem captureAt_timeout {n : UInt32} (hn : n ≠ 0) (h : Ξ n = Ew) (K : Kont) (ℓ : Loc) :
    ((𝕁).captureAt .affine (labW n hn h) timeoutHnd K ℓ).1 = kappaC true ℓ (timeoutV n) K := by
  show captureAtE (decide (A.OpClass.affine = .affine)) ℓ n (qsOf Ξ n) (.lam (.inj₁ (.var 0)))
    [timeoutClA] K = _
  rw [qsOf_Ew h]
  unfold captureAtE
  rw [dif_pos (show IsVal (hndValE n qA (.lam (.inj₁ (.var 0))) [timeoutClA]) from (timeoutV n).2)]
  rfl

theorem cancelOf_timeout {n : UInt32} (hn : n ≠ 0) (h : Ξ n = Ew) (K : Kont) :
    (𝕁).cancelOf (labW n hn h) timeoutHnd K = Targets.cancelOf K := by
  show cancelOfE n (qsOf Ξ n) (.lam (.inj₁ (.var 0))) [timeoutClA] K = _
  rw [qsOf_Ew h, cancelOfE_of_val K (timeoutV n).2]

/-- The region of the nested cancel acts as one running finaliser, with nothing kept. -/
theorem kActs_Kn : kActs orowRF Ξ Kn = [.pend none] := by
  show kActs orowRF Ξ (.appR (.lam (.inj₂ .unit)) (.appR (.prim .ccatch)
    (.appR (.app (.prim .cfin) (cancelVal none).1) .hole))) = _
  simp only [kActs, List.nil_append, List.append_nil]
  rw [cfinErrOf_cancelVal]
  rfl

/-- **A cancel nested in a cancel arises at `J₁`, and the cancel trace passes the running
finaliser** (`pend`): at every effect context declaring `wait : 1 ↠ 1` affine at `2` and `8`,
`ncAff` — a `timeout` of `8` around a `timeout` of `2` whose body's finaliser performs `wait` at
`8` — is typed by `J₁`.  Its run reaches the cancel of `8`'s affine continuation at its cell and
that cancel's start, whose region holds no finaliser and one running finaliser of the cancel of
`2` (`acts = [pend none]`).  The run from the start, `[cfin-cancel]` then `[cancel]`, is a cancel
trace that takes `pend`; read by the region's finalisers alone, no cancel trace follows it. -/
theorem ncAff_pend_J₁ (h2 : Ξ 2 = Ew) (h8 : Ξ 8 = Ew) :
    (𝕁).der [] nc28 ((𝕁).F (orowAlg Ξ).unit (OVTy.ofV (.sum (.sum boolT .unit) .unit))) ∧
    ∃ (c₀ c : (𝕁).RConf (𝕁).R₀) (q : List ((𝕁).Event × (𝕁).RConf (𝕁).R₀)),
      (𝕁).RReach (𝕁).R₀ ((𝕁).rinit (𝕁).R₀ nc28) c₀ ∧
      (𝕁).CancelStart c₀ c K0n (labW 8 (by decide) h8) timeoutHnd Kn ∧
      (𝕁).acts Kn = [.pend none] ∧ (𝕁).fins Kn = [] ∧ (𝕁).RPath (𝕁).R₀ c q ∧
      (𝕁).CancelTrace (𝕁).R₀ (𝕁).noFinRaise K0n c [.pend none] none q ∧
      ∀ FR, ¬ (𝕁).CancelTrace (𝕁).R₀ FR K0n c (((𝕁).fins Kn).map .fire) none q := by
  have h₁ := runM_sound (ℍ := ℍ) 17 [] nc28
  rw [nc_run17] at h₁
  have h₂ := runM_sound (ℍ := ℍ) 5 [(1, Val.unit)] (K0n.plug (cancelE (kappaC true 1 (timeoutV 8) Kn)))
  rw [nc_run22] at h₂
  let Kc : Kont := K0n.comp (ccatchK (bindK (.inj₂ .unit)))
  have hs₁ : (𝕁).RStep (𝕁).R₀ ((Adequacy.emptyMem, K0n.plug (Targets.cancelOf Kn)), ()) (.finEnd none)
      ((Adequacy.emptyMem, Kc.plug (raiseE (.val (cancelVal none)))), ()) := by
    have hh := Head.cfcancel (ℍ := ℍ) Adequacy.emptyMem none none .hole rfl
    have ho := OStep.mach (RF := orowRF) (Ξ := Ξ) (K := Kc) hh
    rw [labelOf_cfcancel] at ho
    exact .mach ho
  have hs₂ : (𝕁).RStep (𝕁).R₀ ((Adequacy.emptyMem, Kc.plug (raiseE (.val (cancelVal none)))), ()) .tau
      ((Adequacy.emptyMem, K0n.plug (.val Val.unit)), ()) := by
    have hh := Head.cancel (ℍ := ℍ) Adequacy.emptyMem (bindK (.inj₂ .unit)) rfl
    have ho := ostep_quiet (RF := orowRF) (Ξ := Ξ) K0n hh rfl
    have he : Kc.plug (raiseE (.val (cancelVal none))) =
        K0n.plug (ccatchE ((bindK (.inj₂ .unit)).plug (raiseE (.val (cancelVal none))))) := by
      simp only [Kc, Kont.plug_comp]; rfl
    rw [he]
    exact .mach ho
  refine ⟨der_ncAff_J₁ h2 h8, ((LMem.heap [(1, Val.unit)], K0n.plug (cancelE (kappaC true 1
    (timeoutV 8) Kn))), ()), ((Adequacy.emptyMem, K0n.plug (Targets.cancelOf Kn)), ()),
    [(.finEnd none, ((Adequacy.emptyMem, Kc.plug (raiseE (.val (cancelVal none)))), ())),
     (.tau, ((Adequacy.emptyMem, K0n.plug (.val Val.unit)), ()))],
    rreach_of_steps (𝕁).R₀ h₁, ⟨.inr ⟨(1 : Loc), ?_, reach_of_steps h₂⟩, rfl, ?_⟩, kActs_Kn, rfl,
    .cons hs₁ (.cons hs₂ .nil), .pend hs₁ (.answer hs₂ rfl), ?_⟩
  · show K0n.plug (cancelE (kappaC true 1 (timeoutV 8) Kn)) =
      K0n.plug (cancelE ((𝕁).captureAt .affine (labW 8 _ h8) timeoutHnd Kn (1 : Loc)).1)
    rw [captureAt_timeout]
  · show K0n.plug (Targets.cancelOf Kn) = K0n.plug ((𝕁).cancelOf (labW 8 _ h8) timeoutHnd Kn)
    rw [cancelOf_timeout]
  · intro FR h
    generalize hacts : (((𝕁).fins Kn).map A.Act.fire : List (𝕁).SAct) = as at h
    have has : as = [] := by rw [← hacts]; rfl
    subst has
    cases h

/-! ### The no-interception condition's teeth -/

/-- `e7b`'s finaliser: `raise exn ()`. -/
abbrev raiseX1 : Expr := raiseE (opArgE 1 0 .unit)

/-- `raise exn ()` at a term's subterm. -/
def raise1Shape : Expr → Bool
  | .app (.prim .raise) (.pair (.prim (.lit (.i32 1))) (.pair (.prim (.lit (.i32 0))) .unit)) => true
  | _ => false

/-- After the fire step, the finaliser `raise exn ()` is at no evaluation position. -/
theorem e7b_fired_ne (Kf : Kont) :
    K0b.plug (ccatchE (BoCa.BoLo.cfinE (cancelVal none) (.app (.val finRaiseV) (.val Val.unit)))) ≠
      Kf.plug raiseX1 := by
  intro h
  have := any_evalSubs_plug (p := raise1Shape) Kf (s := raiseX1) rfl
  rw [← h] at this
  revert this
  decide

/-- `raise exn ()` alone takes no step under the runner that answers nothing. -/
theorem no_rstep_raiseX1 {μ : Heap} {ev : (𝕁).Event} {c' : (𝕁).RConf (𝕁).R₀} :
    ¬ (𝕁).RStep (𝕁).R₀ ((μ, raiseX1), ()) ev c' := by
  intro h
  cases h with
  | mach h' =>
      exact no_ostep_op (r := true) (K := .hole) 1 0 (OVal.ofVal Val.unit) rfl
        (by simp [OpFree, Kont.Catches]) h'
  | io _ _ hans _ => exact hans.elim

/-- **The no-interception condition has teeth at `J₁`**: at every effect context declaring `exn`
at `1` and `wait` at `2`, `e7b`, typed by `J₁`, reaches the start of a cancel whose region's
finaliser is `raise exn ()`, which meets the condition at no set of endings that omits `exn`
(no `FinRow` at `noFinRaise`).  The run from the start fires it, starts it, and keeps its raise
(`[cfin-raise]`, `finEnd` of an error); that path is a prefix of no cancel trace at `noFinRaise`.
So S5's no-interception read without its condition fails at `J₁`. -/
theorem finRow_teeth_J₁ (h1 : Ξ 1 = Eab) (h2 : Ξ 2 = Ew) :
    ∃ (c₀ c : (𝕁).RConf (𝕁).R₀) (q : List ((𝕁).Event × (𝕁).RConf (𝕁).R₀)),
      (𝕁).RReach (𝕁).R₀ ((𝕁).rinit (𝕁).R₀ e7b21) c₀ ∧
      (𝕁).CancelStart c₀ c K0b (labW 2 (by decide) h2) timeoutHnd Kb ∧
      (𝕁).fins Kb = [raiseX1] ∧ ¬ (𝕁).FinRow (𝕁).noFinRaise raiseX1 ∧ (𝕁).RPath (𝕁).R₀ c q ∧
      ∀ q', ¬ (𝕁).CancelTrace (𝕁).R₀ (𝕁).noFinRaise K0b c ((𝕁).acts Kb) none (q ++ q') := by
  have h₁ := runM_sound (ℍ := ℍ) 5 [] e7b21
  rw [e7b_run5] at h₁
  have h₂ := runM_sound (ℍ := ℍ) 5 [(1, Val.unit)] (K0b.plug (cancelE (kappaC true 1 (timeoutV 2) Kb)))
  rw [e7b_run10] at h₂
  let c : (𝕁).RConf (𝕁).R₀ := ((Adequacy.emptyMem, K0b.plug (Targets.cancelOf Kb)), ())
  let c₁₁ : (𝕁).RConf (𝕁).R₀ := ((Adequacy.emptyMem,
    K0b.plug (ccatchE (BoCa.BoLo.cfinE (cancelVal none) (.app (.val finRaiseV) (.val Val.unit))))), ())
  let c₁₂ : (𝕁).RConf (𝕁).R₀ := ((Adequacy.emptyMem, Kfb.plug raiseX1), ())
  let c₁₃ : (𝕁).RConf (𝕁).R₀ := ((Adequacy.emptyMem, (K0b.comp (ccatchK .hole)).plug
    (raiseE (.val (cancelVal (BoCa.BoLo.errNext none 1 0 Val.unit))))), ())
  have hs₁ : (𝕁).RStep (𝕁).R₀ c (.fire raiseX1) c₁₁ := by
    have hh := Head.ufinC (ℍ := ℍ) Adequacy.emptyMem (Val.lam (.var 0)) finRaiseV none
      (bindK (.inj₂ .unit)) rfl
    have ho := OStep.mach (RF := orowRF) (Ξ := Ξ) (K := K0b.comp (ccatchK .hole)) hh
    rw [labelOf_fire (not_isVal_plug_raise _ _)] at ho
    have e₁ : (K0b.comp (ccatchK .hole)).plug (BoCa.BoLo.ubindE (Val.pair (Val.lam (.var 0)) finRaiseV)
        ((bindK (.inj₂ .unit)).plug (raiseE (.val (cancelVal none))))) = K0b.plug (Targets.cancelOf Kb) := by
      rw [Kont.plug_comp]; rfl
    have e₂ : (K0b.comp (ccatchK .hole)).plug (BoCa.BoLo.cfinE (cancelVal none)
        (.app (.val finRaiseV) (.val Val.unit))) = c₁₁.1.2 := by
      rw [Kont.plug_comp]; rfl
    rw [e₁, e₂] at ho
    exact .mach ho
  have hs₂ : (𝕁).RStep (𝕁).R₀ c₁₁ .tau c₁₂ := by
    have ho := ostep_quiet (RF := orowRF) (Ξ := Ξ) Kfb (Head.beta (ℍ := ℍ) Adequacy.emptyMem raiseX1
      Val.unit) rfl
    have e₁ : Kfb.plug (.app (.val (Val.lam raiseX1)) (.val Val.unit)) = c₁₁.1.2 := by
      simp only [Kfb, Kont.plug_comp]; rfl
    rw [e₁] at ho
    exact .mach ho
  have hs₃ : (𝕁).RStep (𝕁).R₀ c₁₂ (.finEnd (errOf orowRF Ξ 1 0 Val.unit)) c₁₃ := by
    have hh := Head.cferr (ℍ := ℍ) Adequacy.emptyMem none 1 0 Val.unit .hole (by decide) rfl
    have ho := OStep.mach (RF := orowRF) (Ξ := Ξ) (K := K0b.comp (ccatchK .hole)) hh
    rw [labelOf_cferr _ _ (by decide)] at ho
    have e₁ : (K0b.comp (ccatchK .hole)).plug (BoCa.BoLo.cfinE (cancelVal none)
        (Kont.hole.plug (raiseE (.val (opPayload 1 0 Val.unit))))) = c₁₂.1.2 := by
      simp only [Kont.plug_comp]; rfl
    rw [e₁] at ho
    exact .mach ho
  have herr : ∃ l, errOf orowRF Ξ 1 0 Val.unit = some (l, 0, OVal.ofVal Val.unit) :=
    let ⟨l, hl, _⟩ := errOf_named (RF := orowRF) (Ξ := Ξ) ⟨labE h1, rfl⟩ 0 Val.unit
    ⟨l, hl⟩
  have hacts : (𝕁).acts Kb = [.fire raiseX1] := rfl
  refine ⟨((LMem.heap [(1, Val.unit)], K0b.plug (cancelE (kappaC true 1 (timeoutV 2) Kb))), ()), c,
    [(.fire raiseX1, c₁₁), (.tau, c₁₂), (.finEnd (errOf orowRF Ξ 1 0 Val.unit), c₁₃)],
    rreach_of_steps (𝕁).R₀ h₁, ⟨.inr ⟨(1 : Loc), ?_, reach_of_steps h₂⟩, rfl, ?_⟩, rfl, ?_,
    .cons hs₁ (.cons hs₂ (.cons hs₃ .nil)), ?_⟩
  · show K0b.plug (cancelE (kappaC true 1 (timeoutV 2) Kb)) =
      K0b.plug (cancelE ((𝕁).captureAt .affine (labW 2 _ h2) timeoutHnd Kb (1 : Loc)).1)
    rw [captureAt_timeout]
  · show K0b.plug (Targets.cancelOf Kb) = K0b.plug ((𝕁).cancelOf (labW 2 _ h2) timeoutHnd Kb)
    rw [cancelOf_timeout]
  · -- the finaliser is typed only at a row with `exn`
    rintro ⟨ε, hε, hd⟩
    obtain ⟨-, Θ, hΘ, hds⟩ := der_core_J₁ (Ξ := Ξ) (A := .unit) (fun _ _ h => by cases h) hd
    have hdd := hds (fun _ => []) (models_anyCon_nil hΘ) (envAt_nil Ξ)
    obtain ⟨C, hC, hop⟩ := derAt_raise hdd 1 0 (.unit) rfl
    cases hC
    rw [CTy.hasOp_effOf] at hop
    obtain ⟨o, ho, hn, hi⟩ := hop
    have hops : ∃ o', Row.find ε.ops 1 0 = some o' := by
      have hmem : o ∈ ε.ops := by
        have : orowRF.den Ξ ε (fun _ => []) = ε.ops ++ [] := by
          show ε.ops ++ (match ε.tail with | none => [] | some ρ => (fun _ => ([] : Row)) ρ) = _
          cases ε.tail <;> rfl
        rw [this, List.append_nil] at ho
        exact ho
      exact Row.find_isSome_iff.mpr ⟨o, hmem, hn, hi⟩
    obtain ⟨o', ho'⟩ := hops
    refine (hε (labE h1) 0 ⟨by decide, fun η => ?_⟩).1
    show (Row.find (ε.ops ++ _) 1 (UInt32.ofNat 0)).isSome = true
    rw [Row.find_append, show UInt32.ofNat 0 = 0 from rfl, ho']
    rfl
  · intro q' h
    rw [hacts] at h
    generalize hq : ([(.fire raiseX1, c₁₁), (.tau, c₁₂), (.finEnd (errOf orowRF Ξ 1 0 Val.unit), c₁₃)] ++
      q' : List ((𝕁).Event × (𝕁).RConf (𝕁).R₀)) = Q at h
    cases h with
    | stop => simp at hq
    | @fire _ c₁ c₂ D _ _ Kf q₀ q'' hst hpp hterm hft =>
        simp only [List.cons_append, List.cons.injEq, Prod.mk.injEq] at hq
        obtain ⟨⟨-, rfl⟩, hq⟩ := hq
        rcases q₀ with _ | ⟨x, q₀⟩
        · cases hpp
          exact e7b_fired_ne Kf hterm
        · simp only [List.cons_append, List.cons.injEq] at hq
          obtain ⟨rfl, hq⟩ := hq
          cases hpp with
          | cons _ _ hpp =>
          rcases q₀ with _ | ⟨y, q₀⟩
          · cases hpp
            simp only [List.nil_append] at hq
            subst hq
            obtain ⟨rfl, -⟩ := plug_raise_inj (show Kfb.plug (raiseE (.val (opPayload 1 0 Val.unit))) =
              Kf.plug (raiseE (.val (opPayload 1 0 Val.unit))) from hterm)
            generalize hQ : ((A.Ev.finEnd (errOf orowRF Ξ 1 0 Val.unit), c₁₃) :: q' :
              List ((𝕁).Event × (𝕁).RConf (𝕁).R₀)) = Q at hft
            match hft with
            | .running ha =>
                rw [← hQ] at ha
                cases ha with
                | cons h₁ _ _ hs' _ =>
                    have ht := plug_inj_hole Kfb (h₁.symm.trans (rfl : c₁₂.1.2 = Kfb.plug raiseX1))
                    subst ht
                    exact no_rstep_raiseX1 hs'
            | @A.EffectSystem.FinTrace.ended _ _ _ _ _ _ _ _ qa _ r _ _ ha hend hFE hst' hct =>
                rcases qa with _ | ⟨z, qa⟩
                · simp only [List.nil_append, List.cons.injEq, Prod.mk.injEq] at hQ
                  obtain ⟨⟨hr, -⟩, -⟩ := hQ
                  cases hr
                  obtain ⟨l, hl⟩ := herr
                  rw [hl] at hFE
                  exact hFE
                · simp only [List.cons_append, List.cons.injEq] at hQ
                  obtain ⟨rfl, -⟩ := hQ
                  cases ha with
                  | cons h₁ _ _ hs' _ =>
                      have ht := plug_inj_hole Kfb (h₁.symm.trans (rfl : c₁₂.1.2 = Kfb.plug raiseX1))
                      subst ht
                      exact no_rstep_raiseX1 hs'
          · simp only [List.cons_append, List.cons.injEq] at hq
            obtain ⟨rfl, -⟩ := hq
            cases hpp

end Witness

/-- **`CfinQuiet` fails at `J₁` at the admissible `ΞA`.** -/
theorem not_cfinQuiet_ΞA : ¬ CfinQuiet (ℍ := ℍ) orowRF ΞA J₁ :=
  not_cfinQuiet_J₁ (by simp [ΞA]) (by simp [ΞA])

theorem not_cfinQuiet_admissible : ¬ ∀ Ξ, AdmEff Ξ → CfinQuiet (ℍ := ℍ) orowRF Ξ J₁ :=
  fun h => not_cfinQuiet_ΞA (h ΞA admEff_ΞA)

end Targets.Inst

end

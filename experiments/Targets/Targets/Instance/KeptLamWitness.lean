import Targets.Instance.CancelWitness

/-!
# The Instance — a finaliser that raises a thunk, at an admissible context

Algebraicity at `J₁` is proved given `KeptLamFree` (`Targets/I/AlgJ1.lean`): every error a typed
program's run keeps at a running finaliser's `cfin` frame holds no λ.  A raise's argument is at a
type that drops (`VTy.Drop`), and `!U C` drops, so a finaliser may raise a thunk.

`ΞT` is `ΞA` with one more name, `13`, an abortive affine operation `!U(1 ⊸ F 1) ↠ 0`; it is
admissible (`admEff_ΞT`).  `e7bT` is `e7b` with its finaliser raising `13` at the thunk `λ_. ()`:
typed by `J₁` (SPEC §27's cancel row of `wait` holds the raise, whose handler is live outside the
`timeout`), its run keeps the raise (`[cfin-raise]`), and the kept error holds a λ.  So
**`KeptLamFree` fails at `J₁` at the admissible `ΞT`** (`not_keptLamFree_ΞT`), and algebraicity
given `KeptLamFree` does not reach every admissible effect context.  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Head Kont Steps Step1 Heap performE raiseE hndE hndVal opPayload cancelVal kappaC
  ccatchE)
open BoCa.Lifetime (LifeCtx)
open Targets (EffCtx orowRF orowAlg ORow RowAt rowAt_nil CDerivesAt LMem runM runM_sound)

/-- `!U(1 ⊸ F 1)`, a thunk's type. -/
abbrev thunkT : VTy := .bang (.thunk (.arr .unit (.ret .unit)))

/-- The thunk `λ_. ()`. -/
def thunkV : Val := Val.lam .unit

/-- `ΞA` and the abortive affine `!U(1 ⊸ F 1) ↠ 0` at `13`. -/
def ΞT : EffCtx := fun n => if n = 13 then [(.aff, thunkT, .zero)] else ΞA n

theorem ΞT_cases (n : UInt32) : ΞT n = [(.aff, thunkT, .zero)] ∨ ΞT n = [] ∨ ΞT n ∈ eSigs := by
  unfold ΞT
  split
  · exact .inl rfl
  · rcases ΞA_cases n with h | h
    · exact .inr (.inl h)
    · exact .inr (.inr h)

/-- **`ΞT` is admissible**: `13` is affine, so not a resuming `unr` operation; its signature is
closed in lifetimes; and `ΞA`'s names are kept. -/
theorem admEff_ΞT : AdmEff ΞT := by
  refine ⟨?_, ?_, ?_⟩
  · intro n q A B h hq
    rcases ΞT_cases n with h0 | h0 | h0
    · rw [h0, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      exact absurd hq (by decide)
    · rw [h0] at h; simp at h
    · exact admEff_ΞA.1 n q A B (by
        unfold ΞT at h
        split at h
        · rename_i h13; subst h13; simp [ΞT, eSigs] at h0
        · exact h) hq
  · intro n q A B h x
    rcases ΞT_cases n with h0 | h0 | h0
    · rw [h0, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp [VFree, CFree]
    · rw [h0] at h; simp at h
    · exact admEff_ΞA.2.1 n q A B (by
        unfold ΞT at h
        split at h
        · rename_i h13; subst h13; simp [ΞT, eSigs] at h0
        · exact h) x
  · intro E hE
    obtain ⟨n₁, n₂, h₁, h₂, h₃, h₄, h₅⟩ := admEff_ΞA.2.2 E hE
    have hne : ∀ n, ΞA n = E → n ≠ 13 := by
      intro n hn h13
      subst h13
      rw [← hn] at hE
      simp [ΞA, eSigs] at hE
    refine ⟨n₁, n₂, h₁, h₂, h₃, ?_, ?_⟩
    · rw [ΞT, if_neg (hne n₁ h₄)]; exact h₄
    · rw [ΞT, if_neg (hne n₂ h₅)]; exact h₅

/-! ### Typing -/

section Typing

/-- The thunk `λ_. () : !U(1 ⊸ F 1)`. -/
theorem d_thunkV {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerivesAt ΞT Δ Γ (.val thunkV) (.val thunkT) :=
  d_lamBang hΓ (.ret (.unitI (.drop rfl hΓ.toP)))

/-- `13` at `ΞT`. -/
def lab13 : (orowAlg ΞT).Lab := ⟨13, by decide, by simp [ΞT], by simp [ΞT]⟩

theorem ΞT_13 : ΞT lab13.1 = [(.aff, thunkT, .zero)] := by simp [ΞT, lab13]

theorem ΞT_2 : ΞT 2 = Ew := by simp [ΞT, ΞA, Ew]

/-- `toResult`'s handler at `13`: its clause drops the thunk. -/
theorem d_toResultHT {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (S : Row) (A : VTy) :
    CDerivesAt ΞT Δ Γ toResultH
      (.val (.tensor (retTy S A (.sum A .unit)) (clausesTy S (.sum A .unit) [(.aff, thunkT, .zero)]))) := by
  refine .tensorI (deadSplit hΓ) (d_lamBang hΓ (.effSub (rowLe_nil S) (.ret (.sumI₁
    (.var (.here hΓ.toP)))))) (.tensorI (deadSplit hΓ) ?_ (.unitI hΓ.toP))
  rw [clauseTy_abortive (by decide)]
  exact d_lamBang hΓ (.effSub (rowLe_nil S) (.ret (.sumI₂ (.unitI (.drop rfl hΓ.toP)))))

/-- The raise of `13` at the thunk. -/
theorem d_raiseT {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (B : VTy) :
    CDerivesAt ΞT Δ Γ (raiseE (opArgE 13 0 (.val thunkV)))
      (.comp (CTy.effOf (Row.ofEff 13 [(.aff, thunkT, .zero)] 0 ++ []) B)) :=
  .effRaise (o := ⟨13, 0, .aff, thunkT, .zero, .ret .unit⟩)
    (by rw [← ΞT_13]; exact rowAt_ofEff_lab lab13 ΞT_13) (by simp [Row.ofEff, Row.find])
    (by simp [OpSig.abort, VTy.isZero]) (.bang _) (d_thunkV hΓ)

/-- The cancel row of `wait` in `e7bT`: the finaliser may raise `13`. -/
abbrev finRaiseT : CTy := CTy.effOf [⟨13, 0, .aff, thunkT, .zero, .ret .unit⟩] .unit

theorem thenLe_finRaiseT :
    ThenLe (.ret .unit) (Row.ofEff 13 [(.aff, thunkT, .zero)] 0 ++ []) finRaiseT := by
  rw [ThenLe]
  refine .inr ⟨rfl, fun n i o hf => by simp [CTy.rowOf, Row.find] at hf, fun n i o hf => ?_⟩
  rw [List.append_nil] at hf
  obtain ⟨rfl, rfl, rfl⟩ := find_ofEff_one hf
  refine ⟨_, by simp [CTy.rowOf, CTy.effOf, Row.find], ⟨rfl, rfl, rfl, rfl, rfl⟩, fun h => ?_⟩
  exact absurd h (by simp [capB, VTy.isZero])

/-- `e7b` with its finaliser raising `13` at the thunk. -/
def e7bTE : Expr :=
  toResultE 13 qA (timeoutHE 2 qA (bodyFE 2 (raiseE (opArgE 13 0 (.val thunkV)))))

theorem qsOf_T13 : qsOf ΞT 13 = qA := by simp [qsOf, ΞT]

theorem qsOf_T2 : qsOf ΞT 2 = qA := qsOf_Ew ΞT_2

/-- `wait` at `2` at `ΞT`. -/
def labT2 : (orowAlg ΞT).Lab := labW 2 (by decide) ΞT_2

/-- **`e7bT` is typed by `J₁`'s kernel** at `ΞT`. -/
theorem d_e7bT :
    CDerivesAt ΞT LifeCtx.empty [] e7bTE (.comp (.ret (.sum (.sum boolT .unit) .unit))) := by
  have h13 : ΞT lab13.1 = [(.aff, thunkT, .zero)] := ΞT_13
  have h2 : ΞT labT2.1 = [(.aff, .unit, .unit)] := ΞT_2
  have hSlo : RowAt ΞT (Row.ofEff lab13.1 [(.aff, thunkT, .zero)] 0 ++ []) := rowAt_ofEff_lab lab13 h13
  have hnlo : ∀ o ∈ Row.ofEff lab13.1 [(.aff, thunkT, .zero)] 0 ++ [], o.n ≠ labT2.1 :=
    names_ofEff (show (13 : UInt32) ≠ 2 by decide)
  rw [show e7bTE = toResultE lab13.1 (qsOf ΞT lab13.1)
    (timeoutHE labT2.1 (qsOf ΞT labT2.1) (bodyFE labT2.1 (raiseE (opArgE 13 0 (.val thunkV)))))
    by rw [show lab13.1 = 13 from rfl, show labT2.1 = 2 from rfl, qsOf_T13, qsOf_T2]; rfl]
  refine d_handleL lab13 h13 (S := []) (rowAt_nil ΞT) (by simp) isVal_toResultH
    (d_toResultHT (kill_dead _) [] _) ?_
  refine d_timeoutHA (lw := labT2) h2 hSlo hnlo (X := boolT) (F := finRaiseT) rfl ?_ ?_
  · refine RowLe.of_find fun n i o hf => ?_
    rw [Row.find_append] at hf
    simp only [CTy.rowOf, CTy.effOf] at hf
    rw [List.append_nil]
    by_cases hk : n = 13 ∧ i = 0
    · obtain ⟨rfl, rfl⟩ := hk
      simp [Row.find] at hf
      subst hf
      simp [Row.ofEff, Row.find, lab13]
    · have : Row.find [⟨13, 0, .aff, thunkT, .zero, .ret .unit⟩] n i = none := by
        simp only [Row.find, List.find?_cons, List.find?_nil]
        rw [decide_eq_false hk]
      rw [this, Option.none_or, List.append_nil] at hf
      exact hf
  refine d_bodyFA (lw := labT2) h2 ?_ ?_ (rowLe_ofEff_consF _ _ hnlo) thenLe_finRaiseT ?_
  · intro o ho
    simp only [Row.ofEff, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at ho
    rcases ho with rfl | rfl
    · exact labT2.2.1
    · show (13 : UInt32) ≠ 0; decide
  · simp [Row.Uniq, Row.ofEff, labT2, labW, lab13]
  · exact d_raiseT (.cons .nil) _

end Typing

/-! ### The run -/

/-- The canceller's context in `e7bT`: `toResult` of `13`, and the clause's `□; return (inr ())`. -/
def K0T : Kont := (handleK 13 qA (.lam (.inj₁ (.var 0))) [.lam (.inj₂ .unit)]).comp (bindK (.inj₂ .unit))

/-- Where the finaliser runs: the canceller's context, `ccatch` and `cfin`. -/
def KfT : Kont := (K0T.comp (ccatchK .hole)).comp (.appR (.app (.prim .cfin) (cancelVal none).1) .hole)

theorem e7bT_run12 :
    runM 12 [] e7bTE = ([], KfT.plug (raiseE (.val (opPayload 13 0 thunkV)))) := by rfl

section Witness

local notation "𝕋" => ourInst (ℍ := ℍ) orowRF ΞT J₁

theorem der_e7bT_J₁ :
    (𝕋).der [] e7bTE ((𝕋).F (orowAlg ΞT).unit (OVTy.ofV (.sum (.sum boolT .unit) .unit))) :=
  der_J₁_ret (by simpa using closedAt_of_derives d_e7bT.toCDerives) d_e7bT

/-- **`KeptLamFree` fails at `J₁` at the admissible `ΞT`**: `e7bT`, typed by `J₁`, reaches its
finaliser's raise of `13` under the cancel's `cfin` frame (a `[cfin-raise]` step), and the error
kept there holds the thunk `λ_. ()`. -/
theorem not_keptLamFree_ΞT : ¬ KeptLamFree (ℍ := ℍ) orowRF ΞT J₁ := by
  intro hk
  have h₁ := runM_sound (ℍ := ℍ) 12 [] e7bTE
  rw [e7bT_run12] at h₁
  have hreach : (𝕋).RReach (𝕋).R₀ ((𝕋).rinit (𝕋).R₀ e7bTE)
      ((Adequacy.emptyMem, KfT.plug (raiseE (.val (opPayload 13 0 thunkV)))), ()) :=
    rreach_of_steps (𝕋).R₀ h₁
  have := hk _ ⟨e7bTE, _, (𝕋).R₀, (), r₀_respects, der_e7bT_J₁, hreach⟩
    (K0T.comp (ccatchK .hole)) (cancelVal none) .hole 13 0 thunkV (by
      show KfT.plug _ = _
      rw [KfT, Kont.plug_comp]
      rfl) rfl
  exact absurd this (by decide)

/-- **`KeptLamFree` fails at some admissible effect context.** -/
theorem not_keptLamFree_admissible : ¬ ∀ Ξ, AdmEff Ξ → KeptLamFree (ℍ := ℍ) orowRF Ξ J₁ :=
  fun h => not_keptLamFree_ΞT (h ΞT admEff_ΞT)

end Witness

end Targets.Inst

end

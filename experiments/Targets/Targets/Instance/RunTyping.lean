import Targets.Instance.Checks
import Targets.Base.CoreCancel

/-!
# The Instance — why `LiveOK` needs rows tied to the effect context

`LiveOK RF Ξ J` (`Targets/Instance/Machine.lean`) is the hypothesis of S0's and S4's step laws at
our instance: every configuration a typed closed program reaches under a runner that keeps its
protocol has a closed term and goes on.  A runner answers an operation at the type the effect
context declares, so the configurations a program reaches go on only if the program's row declares
the same type: rows tied to the effect context (decision D1).

`liveOK_needs_tie` (the scope of the tie).  At the admissible context `ΞA`, the name `6` is
`kube : 1 ↠ bool`, linear.  Today's `[perform]` types `perform (6, 0, ())` at the row
`[6.0 : 1 ↠ 1]`, and `lvProg` sequences the answer.  The runner that answers `kube` at its declared
type keeps its protocol; its answer `inj₁ ()` leaves the configuration at `inj₁ (); ()`, stuck, no
answer and no operation.  The row is not tied to `ΞA`, and our instance does not read `lvProg` at
it.  `LiveOK` at today's kernel is proved in `Targets/I/Restricted/InstanceSafety.lean`.

A fired finaliser's run is read platform-free, at the endings a finaliser may raise (`FinAloneAt`,
`Targets/Base/CoreCancel.lean`, decision D3).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload ubindE)
open BoCa.Lifetime (LifeCtx)
open Targets (CDerivesNU RowForm EffCtx orowRF orowAlg ORow TypingJ tier1NU RowAt StuckAt
  stuckAt_seq stuck_no_step stuck_ne_op)

/-! ### `LiveOK`, at a runner that answers at the effect context's type -/

/-- The row `[6.0 : 1 ↠ 1]`, linear: the name `6`, at a type `ΞA` does not give it. -/
def Slv : Row := Row.ofEff 6 [(.lin, .unit, .unit)] 0 ++ []

def εlv : ORow := ⟨Slv, none⟩

theorem nu_Slv : Row.NU Slv := by
  intro n i o h
  have := (Row.find_mem h).1
  simp [Slv, Row.ofEff] at this
  subst this
  simp

/-- `perform (6, 0, ()) to x. x; ()`. -/
def lvProg : Expr := bindE (performE (opArgE 6 0 (.val .unit))) (.seq (.var 0) (.val .unit))

theorem d_lvProgNU : CDerivesNU LifeCtx.empty [] lvProg (.comp (CTy.effOf Slv .unit)) :=
  .effLet (A := .unit) nu_Slv .nil (fun _ _ h => absurd h List.not_mem_nil)
    (fun _ _ h => absurd h List.not_mem_nil)
    (.effPerform (o := ⟨6, 0, .lin, .unit, .unit⟩) nu_Slv rfl rfl (.unitI .nil))
    (.unitE (.left .nil) (.var (.here .nil))
      (.effSub (S := []) nu_Slv (fun _ _ _ h => by simp [Row.find] at h) (.ret (.unitI (.cons .nil)))))

/-- `kube`, the name `6` at `ΞA`: `1 ↠ bool`, linear. -/
def lab6A : (orowAlg ΞA).Lab := ⟨6, by decide, by simp [ΞA], by simp [ΞA]⟩

/-- The runner that answers `kube` with `inj₁ ()`, at its declared type `bool`. -/
def Rkube : (ourInst (ℍ := ℍ) orowRF ΞA tier1Open).Runner :=
  ⟨fun l i => l.1 = 6 ∧ i = 0, Unit, (),
   fun _ l i _ => if l.1 = 6 ∧ i = 0 then some (OVal.ofVal (Val.inj₁ Val.unit), ()) else none⟩

theorem rkube_respects : (Rkube (ℍ := ℍ)).Respects := by
  rintro l i o ⟨hl, rfl⟩ ho
  have hsig : (ourInst (ℍ := ℍ) orowRF ΞA tier1Open).sig l =
      [⟨OVTy.ofV .unit, OVTy.ofV boolT, clsOf .lin boolT⟩] := by
    show (ΞA l.1).map _ = _
    rw [hl]
    rfl
  rw [hsig] at ho
  simp only [List.getElem?_cons_zero, Option.some.injEq] at ho
  subst ho
  refine ⟨rfl, .unit, .sum .unit .unit, fun s v _ => ⟨_, (), ?_, .inl .unit⟩⟩
  simp [Rkube, hl]
  rfl

/-- The configuration the answer leaves: `inj₁ (); ()`. -/
def lvStuck : Heap × Expr := (Adequacy.emptyMem, .seq (Val.inj₁ Val.unit).1 .unit)

/-- Under `Rkube`, `lvProg`'s run reaches `inj₁ (); ()`. -/
theorem lvStuck_reach :
    (ourInst (ℍ := ℍ) orowRF ΞA tier1Open).RReach Rkube
      ((ourInst (ℍ := ℍ) orowRF ΞA tier1Open).rinit Rkube lvProg) (lvStuck, ()) := by
  refine .head ⟨_, .io (K := bindK (.seq (.var 0) (.val .unit))) (l := lab6A) (i := 0)
    (v := (ourInst (ℍ := ℍ) orowRF ΞA tier1Open).unitV) (w := OVal.ofVal (Val.inj₁ Val.unit))
    (s' := ()) rfl rfl ⟨rfl, rfl⟩ rfl⟩ ?_
  exact .single ⟨_, .mach (OStep.mach (K := .hole) (Head.beta _ (.seq (.var 0) (.val .unit))
    (Val.inj₁ Val.unit)))⟩

/-- `[6.0 : 1 ↠ 1]` is not tied to `ΞA`, which declares `6` at `1 ↠ bool`. -/
theorem not_rowAt_Slv : ¬ RowAt ΞA Slv := by
  intro h
  have := (h 6 0 ⟨6, 0, .lin, .unit, .unit⟩ (by simp [Slv, Row.ofEff, Row.find])).2.2
  simp [ΞA, boolT] at this

theorem lvStuck_stuck : StuckAt (ℍ := ℍ) (.seq (Val.inj₁ Val.unit).1 .unit) :=
  stuckAt_seq (by simp [Val.inj₁]) _

theorem not_goesOn_lvStuck : ¬ GoesOn (ℍ := ℍ) orowRF ΞA lvStuck :=
  not_goesOn_stuck lvStuck_stuck .hole Adequacy.emptyMem (fun w h => by
    simp [driveE, driveMark, Kont.plug] at h)

/-- **`LiveOK` needs rows tied to the effect context** (the scope of decision D1): today's kernel
types `lvProg` at `[6.0 : 1 ↠ 1]`, which is not tied to `ΞA`; under `Rkube`, which keeps its
protocol, its run reaches a configuration that does not go on; our instance does not read `lvProg`
at that row. -/
theorem liveOK_needs_tie :
    AdmEff ΞA ∧ CDerivesNU LifeCtx.empty [] lvProg (.comp (CTy.effOf Slv .unit)) ∧ ¬ RowAt ΞA Slv ∧
      (Rkube (ℍ := ℍ)).Respects ∧
      (ourInst (ℍ := ℍ) orowRF ΞA tier1Open).RReach Rkube
        ((ourInst (ℍ := ℍ) orowRF ΞA tier1Open).rinit Rkube lvProg) (lvStuck, ()) ∧
      ¬ GoesOn (ℍ := ℍ) orowRF ΞA lvStuck ∧
      ¬ (ourInst (ℍ := ℍ) orowRF ΞA tier1Open).der [] lvProg
        ((ourInst (ℍ := ℍ) orowRF ΞA tier1Open).F εlv .unit) := by
  refine ⟨admEff_ΞA, d_lvProgNU, not_rowAt_Slv, rkube_respects, lvStuck_reach, not_goesOn_lvStuck,
    ?_⟩
  rintro ⟨hT, -⟩
  obtain ⟨S, A, he, hS⟩ := hT _ (envAt_nil ΞA)
  have he' : CTy.effOf (Slv ++ []) (OVTy.den (fun _ => []) .unit) = CTy.effOf S A := he
  obtain ⟨rfl, -⟩ := effOf_inj he'
  exact not_rowAt_Slv (by simpa using hS)

end Targets.Inst

end

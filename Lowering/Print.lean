import Backend2.Interp
import Lowering.Obligations

/-!
# Lowering — the print's simulation statement  `[spec §53]`

Below the low subset, the print turns a low term into the LIR (`Backend2/Syntax.lean`): closure
conversion, boxing, defunctionalisation, frame slots. It decides no ownership (the low term has it
explicit), so it is proved by a simulation that reads no type (U2). This file states that
simulation and proves what it transfers; it does not prove the simulation.

**The LIR's semantics is its interpreter** (`Backend2/Interp.lean`), a fuelled big-step
evaluator: `lirRun p fuel` runs `main` from the empty state. It is a function of the fuel, so a
run's outcomes are read off it:

- it **faults** when it fails at some fuel with a message other than running out of fuel
  (`outOfFuel`, the one failure of `eval` at fuel `0`, `eval_zero`);
- it **answers** `(v, s)` when it returns them at some fuel.

Every-run safety, termination and leak freedom at the LIR is `LIREveryRun`: no fault, every
answer `()` with no live object, and some answer.

**The simulation** (`SimBy`) relates the source machine's runs to the interpreter's, through a
correspondence `Corr` of values and heaps that the print chooses (U2), which sends `()` to `()`
and the empty memory to a state with no live object. A fault is matched by a source run that
gets stuck, an answer by a source run to a corresponding value and heap, and a source run that
ends by an answer. `PrintSim` asks it of every closed `F 1` checked program whose lowered term is
low. `lir_every_run_of_sem` is the transfer: a closed `F 1` term in the relation whose print is
simulated runs every time at the LIR. `lowered_lir_every_run` and `lowered_lir_every_run_pin`
compose it with the obligations.

The source machine is at any host `ℍ`; the interpreter computes host operations at `lirHost`
(`Backend2/Interp.lean`), so U2 proves the simulation at `ℍ := lirHost`.
-/

noncomputable section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Lowering
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Check Frontend.Check
open BoCa.Lifetime (LifeCtx)
open Backend2 (Prog LV St)

/-! ### The LIR's runs -/

/-- The interpreter's failure when its fuel runs out. -/
def outOfFuel : String := "LIR interpreter: out of fuel"

/-- At fuel `0` the interpreter fails with `outOfFuel`, and that is its only failure there. -/
theorem eval_zero (p : Prog) (rt : Backend2.LTy) (t : Backend2.Tm) (s : St) :
    (Backend2.eval p 0 rt t).run s = .error outOfFuel := by
  rw [Backend2.eval]; rfl

/-- The state a program with no input starts from (`runLIR`'s, with no input and no arguments). -/
def lirInit (p : Prog) : St := { data := p.data }

/-- `main`'s run at `fuel`. -/
def lirRun (p : Prog) (fuel : Nat) : Except String (LV × St) :=
  (Backend2.eval p fuel p.mainTy p.main).run (lirInit p)

/-- The run faults: it fails at some fuel, not for want of fuel. -/
def LIRFaults (p : Prog) : Prop :=
  ∃ fuel msg, lirRun p fuel = .error msg ∧ msg ≠ outOfFuel

/-- The run answers `v` in the state `s`. -/
def LIRAnswers (p : Prog) (v : LV) (s : St) : Prop :=
  ∃ fuel, lirRun p fuel = .ok (v, s)

/-- **Every run at the LIR is safe, ends, and leaves no live object**: no fault, every answer `()`
with no live object, and some answer. -/
structure LIREveryRun (p : Prog) : Prop where
  safe : ¬ LIRFaults p
  answers : ∀ v s, LIRAnswers p v s → v = .unit ∧ s.objs.isEmpty = true
  ends : ∃ s, LIRAnswers p .unit s

/-! ### The simulation -/

/-- A source configuration that is stuck: not a value, and with no step. -/
def Stuck (μ : BoCa.BoLo.Heap) (e : Expr) : Prop :=
  ¬ IsVal e ∧ ∀ μ' e', ¬ BoLo.Step1 (ℍ := ℍ) μ e μ' e'

/-- A correspondence of source and LIR values and heaps: `()` corresponds only to `()`, and the
empty memory only to a state with no live object. -/
structure Corr where
  val : Val → LV → Prop
  heap : BoCa.BoLo.Heap → St → Prop
  unit : ∀ v, val Val.unit v → v = .unit
  empty : ∀ s, heap Adequacy.emptyMem s → s.objs.isEmpty = true

/-- **The print's simulation of one program**, through `R`: the source term `e` from the empty
memory and the LIR program `p` from its initial state. -/
structure SimBy (R : Corr) (e : Expr) (p : Prog) : Prop where
  /-- A fault at the LIR is a stuck source run. -/
  fault : ∀ fuel msg, lirRun p fuel = .error msg → msg ≠ outOfFuel →
    ∃ μ e', BoLo.Steps (ℍ := ℍ) Adequacy.emptyMem e μ e' ∧ Stuck (ℍ := ℍ) μ e'
  /-- An answer at the LIR is a source run to a corresponding value and heap. -/
  answer : ∀ fuel v s, lirRun p fuel = .ok (v, s) →
    ∃ μ w, BoLo.Steps (ℍ := ℍ) Adequacy.emptyMem e μ (.val w) ∧ R.val w v ∧ R.heap μ s
  /-- A source run that ends is matched by an answer. -/
  ends : ∀ μ w, BoLo.Steps (ℍ := ℍ) Adequacy.emptyMem e μ (.val w) →
    ∃ fuel v s, lirRun p fuel = .ok (v, s)

/-- The print of `e` to `p` is simulated, through some correspondence. -/
def PrintSimAt (e : Expr) (p : Prog) : Prop := ∃ R : Corr, SimBy (ℍ := ℍ) R e p

/-- **The print's simulation statement**: for every checked closed `main : F 1` whose lowered term
is low, its print is simulated. -/
def PrintSim (Site : Checked → Expr → Prop) (lower : TExpr → Expr) (print : Checked → Prog) :
    Prop :=
  ∀ c : Checked, c.ctx = [] → c.C = .ret .unit → LowExpr (Site c) 0 (lower c.t) →
    PrintSimAt (ℍ := ℍ) (lower c.t) (print c)

/-! ### The transfer -/

/-- **The transfer**: a closed `F 1` term in the relation, whose print is simulated, runs every
time at the LIR. -/
theorem lir_every_run_of_sem {e : Expr} {p : Prog}
    (hsem : SemC (ℍ := ℍ) LifeCtx.empty [] e (.ret .unit)) (hsim : PrintSimAt (ℍ := ℍ) e p) :
    LIREveryRun p := by
  obtain ⟨R, hR⟩ := hsim
  have answers : ∀ v s, LIRAnswers p v s → v = .unit ∧ s.objs.isEmpty = true := by
    rintro v s ⟨fuel, hrun⟩
    obtain ⟨μ, w, hs, hv, hh⟩ := hR.answer fuel v s hrun
    obtain ⟨rfl, rfl⟩ := steps_from_val (ℍ := ℍ) (v := w) (w := Val.unit) (every_run_of_sem hsem hs)
    exact ⟨R.unit v hv, R.empty s hh⟩
  refine ⟨?_, answers, ?_⟩
  · rintro ⟨fuel, msg, hrun, hmsg⟩
    obtain ⟨μ, e', hs, hnv, hstep⟩ := hR.fault fuel msg hrun hmsg
    cases every_run_of_sem hsem hs with
    | refl => exact hnv Val.unit.2
    | more h _ => exact hstep _ _ h
  · obtain ⟨fuel, v, s, hrun⟩ := hR.ends _ _ (every_run_of_sem hsem (.refl _ _))
    obtain ⟨rfl, -⟩ := answers v s ⟨fuel, hrun⟩
    exact ⟨s, fuel, hrun⟩

/-- **End to end**: a lowering that meets the obligation, lowers into the low subset, and whose
print is simulated, runs every checked closed `main : F 1` with no relaxed rule every time at the
LIR. -/
theorem lowered_lir_every_run {Site : Checked → Expr → Prop} {lower : TExpr → Expr}
    {print : Checked → Prog} (hL : LowerSem (ℍ := ℍ) lower) (hLow : LowersInto Site lower)
    (hP : PrintSim (ℍ := ℍ) Site lower print) (c : Checked) (hp : c.pins = []) (hΓ : c.ctx = [])
    (hC : c.C = .ret .unit) : LIREveryRun (print c) := by
  have hsem := hL c hp
  have hlow := hLow c
  rw [hΓ] at hlow
  have hsim := hP c hΓ hC hlow
  rw [hΓ, hC] at hsem
  exact lir_every_run_of_sem hsem hsim

/-- Under `PinLaw`, with the relative obligation, for every checked closed `main : F 1`. -/
theorem lowered_lir_every_run_pin {Site : Checked → Expr → Prop} {lower : TExpr → Expr}
    {print : Checked → Prog} (hPin : PinLaw (ℍ := ℍ)) (hL : LowerSemRel (ℍ := ℍ) lower)
    (hLow : LowersInto Site lower) (hP : PrintSim (ℍ := ℍ) Site lower print) (c : Checked)
    (hΓ : c.ctx = []) (hC : c.C = .ret .unit) : LIREveryRun (print c) := by
  have hsem := hL c (checked_sem_pin hPin c)
  have hlow := hLow c
  rw [hΓ] at hlow
  have hsim := hP c hΓ hC hlow
  rw [hΓ, hC] at hsem
  exact lir_every_run_of_sem hsem hsim

/-! ### Non-vacuity -/

/-- The LIR program `()`. -/
def unitProg : Prog :=
  { fns := #[], codes := #[], main := .unit, mainTy := .unit, ty := {} }

theorem lirRun_unitProg (fuel : Nat) :
    lirRun unitProg fuel =
      if fuel = 0 then .error outOfFuel else .ok (.unit, lirInit unitProg) := by
  cases fuel with
  | zero => exact eval_zero _ _ _ _
  | succ f =>
    show (Backend2.eval unitProg (f + 1) .unit .unit).run (lirInit unitProg) = _
    rw [Backend2.eval]; rfl

/-- `()` is in the relation at `F 1`. -/
theorem sem_unit : SemC (ℍ := ℍ) LifeCtx.empty [] (.val .unit) (.ret .unit) :=
  fundamentalC (CDerives.ret (CDerives.unitI .nil))

/-- The print of `()` to the LIR's `()` is simulated. -/
theorem printSimAt_unit : PrintSimAt (ℍ := ℍ) (.val .unit) unitProg := by
  refine ⟨⟨fun w v => w = Val.unit ∧ v = .unit, fun μ s => μ = Adequacy.emptyMem ∧
      s = lirInit unitProg, fun _ h => h.2, fun _ h => by rw [h.2]; rfl⟩, ?_, ?_, ?_⟩
  · intro fuel msg hrun hmsg
    rw [lirRun_unitProg] at hrun
    split at hrun
    · cases hrun; exact absurd rfl hmsg
    · cases hrun
  · intro fuel v s hrun
    rw [lirRun_unitProg] at hrun
    split at hrun
    · cases hrun
    · cases hrun; exact ⟨_, Val.unit, .refl _ _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
  · intro _ _ _
    exact ⟨1, _, _, by rw [lirRun_unitProg]; rfl⟩

/-- The transfer's hypotheses hold together: `()` is in the relation and its print is simulated;
it is also low (`lowExpr_unit`). -/
theorem lir_every_run_unit : LIREveryRun unitProg :=
  haveI : HostIs Backend2.lirHost := ⟨⟩
  lir_every_run_of_sem (ℍ := Backend2.lirHost) sem_unit printSimAt_unit

end Lowering

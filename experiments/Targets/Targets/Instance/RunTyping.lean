import Targets.Instance.Checks
import Targets.Base.CoreCancel

/-!
# The Instance — what a typed program does at run time: `FinAlone` and `LiveOK`, as written

Piece 1 added two hypotheses about the configurations a typed program reaches, and left their
discharge to piece 4:

* `FinAlone J` (`Targets/Base/CoreCancel.lean`): a fired finaliser, run alone, ends at a value or
  at a raise of a nonzero name nothing inside it catches.  `finaliserOrder_of` takes it.
* `LiveOK RF Ξ J` (`Targets/Instance/Machine.lean`): every configuration a typed closed program
  reaches under a runner that keeps its protocol has a closed term and goes on.  S0's and S4's
  step laws at our instance take it (`machShape_orow`, `handlerSem_orow`).

**Both fail as written at today's kernel**, for the reason S2 and S3 do (`Instance/Safety.lean`):
the platform or the runner answers an operation at the type *it* declares, and nothing ties that
type to the one the program's row declares.

* `not_finAlone_tier1NU`.  `finProg` performs `1.0 : 1 ↠ 1`, then raises `2.0` under a finaliser
  that sequences the answer, `x; ()`.  `FinAlone` quantifies over every platform that keeps its
  protocol, and `Pmis` keeps it while answering `1.0` at `1 ⊕ 1` with `inj₁ ()`.  The finaliser
  fires, and its run alone stops at `inj₁ (); ()`, which is neither a value nor a raise.  B2's
  adequacy (`AdequateRetAt`) asks `RowLe S P.ops` of the platform; `FinAlone` does not.  Its only
  consumer reads it at the platform with no operation and the pure row (`finAlone_at`).
* `not_liveOK_ΞA`.  At the admissible context `ΞA`, the name `6` is `kube : 1 ↠ bool`, linear.
  Today's `[perform]` types `perform (6, 0, ())` at the row `[6.0 : 1 ↠ 1]` (rows read through
  `RF.den` ask nothing of `Ξ`), and `lvProg` sequences the answer.  The runner that answers `kube`
  at its declared type keeps its protocol; its answer `inj₁ ()` leaves the configuration at
  `inj₁ (); ()`, stuck, no answer and no operation.

Both configurations are reached from a typed closed program in the empty world, by steps of the
machine and answers of a platform or runner that keeps its protocol.

`FinAlone`'s only consumer reads it at the platform with no operation and the pure row
(`finAlone_at`).  That platform-free form, `FinAloneAt`, is what `FinaliserOrder` now takes
(`finaliserOrder_at`), and the mismatch above does not touch it.  Its two halves, stuck redexes and
operations, are taken apart in `Targets/I/Restricted/FinAlone.lean`: B gives the first, and the
second, `FinRowsAt`, is the route's.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload ubindE)
open BoCa.Lifetime (LifeCtx)
open Targets (CDerivesNU RowForm EffCtx orowRF orowAlg ORow TypingJ tier1NU FinAlone Platform
  PStep PSteps Conf StuckAt stuckAt_seq stuck_no_step stuck_ne_op)

/-! ### `FinAlone`, at a platform that answers at another type -/

/-- `1.0 : 1 ↠ 1` linear, and `2.0 : 1 ↠ 0` affine (abortive). -/
def Sfin : Row := Row.ofEff 1 [(.lin, .unit, .unit)] 0 ++ (Row.ofEff 2 [(.aff, .unit, .zero)] 0 ++ [])

theorem nu_Sfin : Row.NU Sfin := by
  intro n i o h
  have := (Row.find_mem h).1
  simp [Sfin, Row.ofEff] at this
  rcases this with rfl | rfl <;> simp [OpSig.abort]

/-- The finaliser: `x; ()`, `x` the answer of `1.0`. -/
def finSeq : Expr := .seq (.var 1) (.val .unit)

/-- `perform (1, 0, ()) to x. (raise (2, 0, ()) then y. y unwind x; ())`. -/
def finProg : Expr :=
  bindE (performE (opArgE 1 0 (.val .unit))) (thenE (.var 0) finSeq (raiseE (opArgE 2 0 (.val .unit))))

/-- **Today's unr-free kernel types `finProg` at `F_Sfin 1`.** -/
theorem d_finProgNU : CDerivesNU LifeCtx.empty [] finProg (.comp (CTy.effOf Sfin .unit)) := by
  have hp : VTy.Persistent .unit := rfl
  refine .effLet (A := .unit) nu_Sfin .nil (fun _ _ h => absurd h List.not_mem_nil)
    (fun _ _ h => absurd h List.not_mem_nil)
    (.effPerform (o := ⟨1, 0, .lin, .unit, .unit⟩) nu_Sfin rfl rfl (.unitI .nil)) ?_
  refine .effThen (A := .unit) nu_Sfin (.right .nil) (by simp [Row.NZ, Sfin, Row.ofEff])
    (by unfold Row.Uniq Sfin; decide) (fun h => absurd h (by simp [Row.Unr, Sfin, Row.ofEff]))
    (.effRaise (o := ⟨2, 0, .aff, .unit, .zero⟩) rfl rfl .unit (.unitI (.cons .nil)))
    (.effSub (S := []) nu_Sfin (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (.var (.here (.drop hp .nil))))) ?_
  refine .unitE (Γ₁ := [⟨.unit, false⟩, ⟨.unit, true⟩]) (Γ₂ := [⟨.unit, false⟩, ⟨.unit, false⟩])
    (.dead (.left .nil)) (.var (.there (.here .nil))) ?_
  exact .effSub (S := []) (by
      intro n i o h
      have := (Row.find_mem h).1
      simp [Sfin, Row.ofEff, Row.abortOnly, OpSig.abort] at this
      obtain ⟨rfl, -, -⟩ := this
      simp [OpSig.abort])
    (fun _ _ _ h => by simp [Row.find] at h) (.ret (.unitI (.cons (.cons .nil))))

/-- A platform that answers `1.0` at `1 ⊕ 1`, with `inj₁ ()`. -/
def Pmis : Platform :=
  ⟨[⟨1, 0, .lin, .unit, .sum .unit .unit⟩], Unit, (),
   fun _ n i _ => if n = 1 ∧ i = 0 then some (Val.inj₁ Val.unit, ()) else none⟩

theorem pmis_respects : Pmis.Respects where
  uniq := List.pairwise_singleton _ _
  nz := by intro o ho; simp [Pmis] at ho; subst ho; decide
  lin := by simp [Pmis, OpSig.abort]
  data := by simp [Pmis]; exact ⟨VTy.DataB.unit 0, VTy.DataB.sum (VTy.DataB.unit 0) (VTy.DataB.unit 0)⟩
  total := by
    intro s o v ho _
    simp only [Pmis, List.mem_singleton] at ho
    subst ho
    exact ⟨Val.inj₁ Val.unit, (), by simp [Pmis]⟩
  typed := by
    intro s s' o v w ho _ hco
    simp only [Pmis, List.mem_singleton] at ho
    subst ho
    simp [Pmis] at hco
    obtain ⟨rfl, -⟩ := hco
    exact .inj₁ .unit

/-- The finaliser value, once `x` is the platform's answer. -/
def finDV : Val := ⟨.lam (.seq (.inj₁ .unit) (.val .unit)), .lam⟩

/-- The return clause value of the `[then]` frame. -/
def finNV : Val := ⟨.lam (.var 0), .lam⟩

/-- The configuration at which the finaliser fires: `ubind (N, D) (raise (2, 0, ()))`. -/
def finFire : Conf Pmis :=
  ⟨Adequacy.emptyMem, ubindE (Val.pair finNV finDV) (raiseE (.val (opPayload 2 0 Val.unit))), ()⟩

theorem finFire_reach : PSteps (ℍ := ℍ) Pmis (Targets.init Pmis finProg) finFire := by
  refine .head (PStep.plat (K := bindK (thenE (.var 0) finSeq (raiseE (opArgE 2 0 (.val .unit)))))
    (o := ⟨1, 0, .lin, .unit, .sum .unit .unit⟩) (v := Val.unit) (w := Val.inj₁ Val.unit) (s' := ())
    rfl rfl (by simp [Pmis])) ?_
  exact .single (PStep.mach ⟨.hole, _, _, rfl, rfl,
    Head.beta _ (thenE (.var 0) finSeq (raiseE (opArgE 2 0 (.val .unit)))) (Val.inj₁ Val.unit)⟩)

/-- The finaliser's run alone: one β, to `inj₁ (); ()`. -/
theorem finD_run :
    Steps (ℍ := ℍ) Adequacy.emptyMem (.app (.val finDV) (.val .unit)) Adequacy.emptyMem
      (.seq (Val.inj₁ Val.unit).1 .unit) :=
  .more ⟨.hole, _, _, rfl, rfl, Head.beta _ _ Val.unit⟩ (.refl _ _)

theorem finD_stuck : StuckAt (ℍ := ℍ) (.seq (Val.inj₁ Val.unit).1 .unit) :=
  stuckAt_seq (by simp [Val.inj₁]) _

/-- **`FinAlone` fails at every typing system that types `finProg`.**  The platform `Pmis` keeps
its protocol and answers `1.0` at `1 ⊕ 1`; the finaliser fires, and its run alone stops at
`inj₁ (); ()`. -/
theorem not_finAlone_of_types {J : TypingJ}
    (h : J.closed finProg (CTy.effOf Sfin .unit)) : ¬ FinAlone (ℍ := ℍ) J := by
  intro hF
  rcases hF Pmis pmis_respects Sfin .unit finProg nu_Sfin h finFire .hole .hole finNV finDV 2 0
      Val.unit finFire_reach rfl rfl Adequacy.emptyMem _ finD_run
      (fun μ t h => stuck_no_step finD_stuck .hole (by simpa using h)) with hv | ⟨K', m, j, w, ht, -⟩
  · exact finD_stuck.not_val hv
  · exact stuck_ne_op finD_stuck .hole K' true (opPayload m j w) (by simpa [opE] using ht)

/-- **`FinAlone`, as written, fails at today's unr-free kernel.** -/
theorem not_finAlone_tier1NU : ¬ FinAlone (ℍ := ℍ) tier1NU :=
  not_finAlone_of_types (fun _ _ => d_finProgNU)

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

/-- **Today's kernel types `lvProg` at our instance**, at `F_{[6.0 : 1 ↠ 1]} 1`, at every effect
context. -/
theorem der_lvProg (Ξ : EffCtx) :
    (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).der [] lvProg
      ((ourInst (ℍ := ℍ) orowRF Ξ tier1Open).F εlv .unit) := by
  refine .inl ⟨[], by simp, fun _ h => absurd h List.not_mem_nil, trivial, fun η _ => ?_⟩
  show CDerivesNU LifeCtx.empty [] lvProg (.comp (CTy.effOf (Slv ++ []) .unit))
  rw [List.append_nil]
  exact d_lvProgNU

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

theorem lvStuck_live : (ourInst (ℍ := ℍ) orowRF ΞA tier1Open).Live lvStuck := by
  refine ⟨lvProg, _, Rkube, (), rkube_respects, der_lvProg ΞA, ?_⟩
  refine .head ⟨_, .io (K := bindK (.seq (.var 0) (.val .unit))) (l := lab6A) (i := 0)
    (v := (ourInst (ℍ := ℍ) orowRF ΞA tier1Open).unitV) (w := OVal.ofVal (Val.inj₁ Val.unit))
    (s' := ()) rfl rfl ⟨rfl, rfl⟩ rfl⟩ ?_
  exact .single ⟨_, .mach (OStep.mach (K := .hole) (Head.beta _ (.seq (.var 0) (.val .unit))
    (Val.inj₁ Val.unit)))⟩

theorem not_goesOn_lvStuck : ¬ GoesOn (ℍ := ℍ) orowRF ΞA lvStuck :=
  not_goesOn_stuck finD_stuck .hole Adequacy.emptyMem (fun w h => by
    simp [driveE, driveMark, Kont.plug] at h)

/-- **`LiveOK`, as written, fails at today's kernel at the admissible context `ΞA`.**  The program
`lvProg` is typed at the row `[6.0 : 1 ↠ 1]`; the runner answers `kube` at its declared type
`bool`, keeping its protocol; the configuration it leaves is stuck. -/
theorem not_liveOK_ΞA : AdmEff ΞA ∧ ¬ LiveOK (ℍ := ℍ) orowRF ΞA tier1Open :=
  ⟨admEff_ΞA, fun h => not_goesOn_lvStuck (h _ lvStuck_live).2⟩

end Targets.Inst

end

import Targets.I.Restricted.Device
import Targets.I.Restricted.CompositeT1
import Targets.I.Restricted.Answering
import Targets.I.Restricted.InstanceProps
import Targets.I.NonVacuity
import Targets.I.Binder
import Targets.Instance.Core

/-!
# The interaction — the combined theorem, done, and tier 1 (RESTRUCTURE §0, §3.4, §3.5)

**The combined theorem** `Combined RF J M Adm c`, at our calculus with row form `RF` and typing
system `J`, world `M`, OQ-56's admissibility `Adm` and the class `c` of rows a lend may span:

* **nothing breaks the effect algebra**: A's properties hold at our instance at **every**
  admissible effect context `Ξ` (`AdmEff`), so the effect algebra holds for whatever effects a
  program declares, not only for the test labels;
* **nothing breaks the borrow calculus**: B's guarantees hold at the composite's typing (its
  reading `J.read`) and world;
* the interaction's option-neutral rules at the world (`Bounds`, `Interface`); what the composite's
  typing must contain (`Pins`); the composite's expressiveness (`Accepts`) and the rejections that
  pin soundness (`Rejects`).

**Done** is `Combined orowRF J₂ W admClosedOp .any` at a named tier-2 typing system `J₂` and a named
world `W`, with `audit_W` (the step-index audit of `W`'s definition).  It is fixed at
`admClosedOp` until OQ-56 is chosen and at `orowRF` until OQ-13's remaining question (the row form)
is answered; a wider `Adm` makes it stronger.  **Tier 1** is the same definition at a typing system
`J₁` with row variables and no spanning rules, at `coreW` and `.abortive`: `Tier1 J₁`.

Neither `J₁`, `J₂` nor `W` is defined: done and tier 1 are OPEN (`Targets/Status.lean`).

**Option-neutral by construction** (finding #5): every conjunct that fixes an option of OQ-8 or
OQ-9 is in the proof device (`Device`, beside done), and no conjunct states `↭`'s borrow content off
the nil slice.

The corollaries (generic): `combined_prog` (the conjuncts that read no world), `i1Prog_of_combined`,
`i2Prog_of_combined` (at `c = .any`), `effSafe_core_of_combined` (Core's form of P2),
`soundnessContractsAR_of_combined` (the SPEC's externs at Core's contract, with the device's
`EmbedsNil`), `not_combined_of_leak` (a reachable leak breaks done).

**The tier-1 reduction**, restricted: the library proved that its tier-1 end state follows from two
open statements (`status_tier1End_of`).  Its proved content is kept, in the new vocabulary: B's
guarantees at today's kernel and `coreB` follow from `Adequate coreB` and, for B5, the
step-for-step simulation `BumpSim` (`tier1Core_guarantees_of`; without B5, from `Adequate coreB`
alone, `tier1Core_B_of`), and the world conjuncts and the device at `coreW` hold
(`tier1Core_world`).  `Tier1Core` itself also needs A's properties at our instance (the Instance's
bridges, OPEN); its `Pins` conjunct is proved (`pins_tier1Open`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms (Flag logOutside failOutside reborrowRaise logInBorrow
  tickAnsProg takeProg storeCancel)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open Targets.Inst (OurTyping ourInst AdmEff tier1Open tier1Open_read)

namespace I

/-! ### The composite's expressiveness -/

/-- **The tier-1 composite programs**, accepted with their answers: the answering `Log` lent as a
borrow and `Fail`, in both orders; logging inside a borrow; a raise inside a reborrow inside a
borrow; a loop whose state owns the log cell; early exit cancelling a producer that holds a cell; a
continuation stored in a cell, taken back and cancelled.  Answers as `Support`'s interpreter
computes them. -/
def CompositeT1 (J : TypingJ) : Prop :=
  AcceptedAt (ℍ := ℍ) J logOutside (.tensor Flag (.sum .zero .unit))
    (Val.pair (Val.inj₂ .unit) (Val.inj₂ .unit)) ∧
  AcceptedAt (ℍ := ℍ) J failOutside (.sum .zero .unit) (Val.inj₂ .unit) ∧
  AcceptedAt (ℍ := ℍ) J logInBorrow (.tensor Flag Flag) (Val.pair (Val.inj₂ .unit) (Val.inj₂ .unit)) ∧
  AcceptedAt (ℍ := ℍ) J reborrowRaise (.sum .zero .unit) (Val.inj₂ .unit) ∧
  AcceptedAt (ℍ := ℍ) J (tickAnsProg 3) Flag (Val.inj₂ .unit) ∧
  AcceptedAt (ℍ := ℍ) J (takeProg 1) Flag (Val.inj₂ .unit) ∧
  AcceptedAt (ℍ := ℍ) J (takeProg 5) Flag (Val.inj₁ .unit) ∧
  AcceptedAt (ℍ := ℍ) J storeCancel .unit Val.unit

/-- **The composite's expressiveness**: the tier-1 programs at every class, the tier-2 programs when
lends may span every unr-free row. -/
def Accepts (J : TypingJ) (c : RowClass) : Prop :=
  CompositeT1 (ℍ := ℍ) J ∧ (c = .any → Tier2Programs (ℍ := ℍ) J)

/-! ### The interaction's rules at the world -/

/-- **How effect rows are read in the borrow world**: the rule of the interaction.  Neutral to OQ-8
and OQ-9 (RESTRUCTURE §3.6). -/
def Bounds (M : SemWorld) : Prop :=
  SliceShapeI M ∧ EffInterp (ℍ := ℍ) M ∧ ShareMono M ∧ AdequateEvery (ℍ := ℍ) M

/-- **The world-level interface**: what the world reaches (I2's preservation of `TW` and `TW.inv`
along runs, over the visible and the held frames), and exclusivity counting what suspensions hold
(P10).  It reads no typing system. -/
def Interface (M : SemWorld) : Prop := Arises M ∧ Exclusive M

/-- **What the composite's typing must contain**: the admissibility bounded below by today's,
today's unr-free rules and outlives judgements, and the answering effects' borrow form (I4, decision
57: "Answering effects are capability arguments and add no copies").  The mechanisms of `J₂` (the
row `∀`, the spanning rules) are not pins: A's schemas require effect polymorphism and `Accepts`
the tier-2 programs, and `RowVarKernel` and `SpanRulesAt` record how our kernel meets them. -/
def Pins {RF : RowForm} (J : OurTyping RF) (Adm : OpAdm) (c : RowClass) : Prop :=
  AdmExtends Adm ∧ ExtendsNU J.read ∧ OutExtends J.read.out ∧ I4a J.read Adm c

/-- The spanning rules at a class, recorded (`J₂`'s mechanism for the tier-2 programs, not a pin):
none beyond today's unwinding constants at `.abortive`, the six spanning rules at `RowSpan Adm`
at `.any`. -/
def SpanRulesAt (J : TypingJ) (Adm : OpAdm) : RowClass → Prop
  | .abortive => True
  | .resumeOnce => SpanRules J (fun Δ x o => Adm Δ x o ∧ (o.abort = true ∨ o.q = .lin))
  | .any => SpanRules J Adm

/-! ### The combined theorem -/

/-- **The combined theorem.** -/
def Combined (RF : RowForm) (J : OurTyping RF) (M : SemWorld) (Adm : OpAdm) (c : RowClass) : Prop :=
  (∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) RF Ξ J).Props) ∧
    B.Guarantees (ℍ := ℍ) J.read M.toBWorld ∧ Bounds (ℍ := ℍ) M ∧ Interface M ∧ Pins J Adm c ∧
    Accepts (ℍ := ℍ) J.read c ∧ Rejects J.read

/-- **Tier 1**: the combined theorem at a typing system `J₁` with row variables and no spanning
rules (A's (E) properties need effect polymorphism at every tier), at Core's world, lends spanning
abortive rows only. -/
def Tier1 (J₁ : OurTyping orowRF) : Prop := Combined (ℍ := ℍ) orowRF J₁ (coreW (ℍ := ℍ)) admClosedOp .abortive

/-- The combined theorem with the freeze binder: the named strengthening, beside done. -/
def CombinedBinder (RF : RowForm) (J : OurTyping RF) (M : SemWorld) (act : StkAct M) (Adm : OpAdm)
    (c : RowClass) : Prop :=
  Combined (ℍ := ℍ) RF J M Adm c ∧ FreezeBinder M act ∧ BinderMachine (ℍ := ℍ)

/-! ### Corollaries of the combined theorem (generic) -/

variable {RF : RowForm} {J : OurTyping RF} {M : SemWorld} {Adm : OpAdm} {c : RowClass}

/-- **The conjuncts of the combined theorem that read no world**: no choice of world makes them
true, so done asserts them of `J₂`.  B5 at closed programs (`ReleasedOnceReuse₀`) reads no world. -/
theorem combined_prog (h : Combined (ℍ := ℍ) RF J M Adm c) :
    (∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) RF Ξ J).Props) ∧ Sound (ℍ := ℍ) J.read ∧
      B.ReleasedOnceReuse₀ (ℍ := ℍ) J.read ∧ B.ExtendsB J.read ∧ Pins J Adm c ∧
      Accepts (ℍ := ℍ) J.read c ∧ Rejects J.read := by
  obtain ⟨hA, ⟨hE, -, -, hS, -, hR, -⟩, -, -, hP, hAc, hRj⟩ := h
  exact ⟨hA, hS, releasedOnceReuse₀_of hR, hE, hP, hAc, hRj⟩

/-- **I1 at the program level**, at `c = .any`: suspensions stored in a cell, moved, and cancelled
(`storeCancel`) or resumed (`at17`). -/
theorem i1Prog_of_combined (h : Combined (ℍ := ℍ) RF J M Adm .any) : I1Prog (ℍ := ℍ) J.read := by
  obtain ⟨-, ⟨-, -, -, hS, -⟩, -, -, -, ⟨⟨-, -, -, -, -, -, -, ⟨hsc, -⟩⟩, h2⟩, -⟩ := h
  obtain ⟨-, -, -, ⟨h17, -⟩, -⟩ := h2 rfl
  exact ⟨typedSound_of_soundness hS (.unit 0) hsc, typedSound_of_soundness hS flag_data h17⟩

/-- **I2 at the program level**, at `c = .any`: lends spanning a once-resuming operation (`at02`,
`at04`) and an affine one whose continuation is cancelled (`at12`). -/
theorem i2Prog_of_combined (h : Combined (ℍ := ℍ) RF J M Adm .any) : I2Prog (ℍ := ℍ) J.read := by
  obtain ⟨-, ⟨-, -, -, hS, -⟩, -, -, -, ⟨-, h2⟩, -⟩ := h
  obtain ⟨⟨h02, -⟩, ⟨h04, -⟩, ⟨h12, -⟩, -, -⟩ := h2 rfl
  exact ⟨typedSound_of_soundness hS flag_data h02,
    typedSound_of_soundness hS (.tensor flag_data flag_data) h04, typedSound_of_soundness hS flag_data h12⟩

/-- **Core's form of P2**, from the combined theorem: `FL`, the empty configuration and adequacy
from every index (`effSafeOfFL`, over `FamEmpty ∧ AdequateEvery`). -/
theorem effSafe_core_of_combined (h : Combined (ℍ := ℍ) RF J M Adm c) : EffSafe (ℍ := ℍ) J.read := by
  obtain ⟨-, ⟨-, hFL, -, -, -, -, -, -, ⟨-, -, hFam, -⟩⟩, ⟨-, -, -, hAE⟩, -⟩ := h
  exact effSafeOfFL M J.read hFL ⟨hFam, hAE⟩

/-- **The SPEC's externs at Core's contract**, from the combined theorem together with the device's
`EmbedsNil` (which is beside done, RESTRUCTURE §3.6): B4′ at W's contract, which Core's contract
gives at row-abortive types through `EmbedsNil` (`contractsW_of_meets`). -/
theorem soundnessContractsAR_of_combined (h : Combined (ℍ := ℍ) RF J M Adm c)
    (hE : EmbedsNil (ℍ := ℍ) M) : SoundnessContractsAR (ℍ := ℍ) J.read := by
  obtain ⟨-, ⟨-, -, -, -, hSC, -⟩, -⟩ := h
  intro P hP Γ γ S A e hAR hd hle hJ hγ
  exact hSC P hP Γ γ S A e hd hle hJ (contractsW_of_meets hE hAR hγ)

/-- **A world whose run-end relation admits a reachable leak does not satisfy the combined theorem**
(FIX-RUN-END §3): `Bounds` holds `EffInterp`, `WBound` holds `DataVals`, and B's guarantees hold
`Adequate`. -/
theorem not_combined_of_leak {α : Life} (hL : RunEnd.LeakAt M α) :
    ¬ Combined (ℍ := ℍ) RF J M Adm c := by
  rintro ⟨-, ⟨-, -, hA, -, -, -, -, -, ⟨-, -, -, hD, -⟩⟩, ⟨-, hE, -⟩, -⟩
  exact RunEnd.not_adequate_of_leak hE hD hL hA

/-! ### The tier-1 reduction, restricted to what is proved -/

/-- **The tier-1 end state at today's kernel and Core's world**, without what today's kernel cannot
meet (A's (E) properties need effect polymorphism) or what is OPEN regardless (`ContUse`;
`Accepts`' runs and `Rejects`' inversions); with the device at `coreW` (I1, I2, I3, I5, P11,
`ConservativeWB`, `EmbedsNil`). -/
def Tier1Core : Prop :=
  (∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).SPropsNoUse) ∧
    B.Guarantees (ℍ := ℍ) tier1Open.read (B.coreB (ℍ := ℍ)) ∧ Bounds (ℍ := ℍ) (coreW (ℍ := ℍ)) ∧
    Interface (coreW (ℍ := ℍ)) ∧ Pins tier1Open admClosedOp .abortive ∧
    Device (ℍ := ℍ) (coreW (ℍ := ℍ)) tier1Open.read admClosedOp .abortive ∧ WBCore (ℍ := ℍ)

/-- **The world conjuncts and the device at `coreW`**: proved. -/
theorem tier1Core_world :
    Bounds (ℍ := ℍ) (coreW (ℍ := ℍ)) ∧ Interface (coreW (ℍ := ℍ)) ∧
      Device (ℍ := ℍ) (coreW (ℍ := ℍ)) tier1Open.read admClosedOp .abortive ∧ WBCore (ℍ := ℍ) := by
  obtain ⟨-, -, -, hF, hSB⟩ := i2_core_abortive (ℍ := ℍ)
  refine ⟨⟨sliceShapeI_core, effInterp_core, shareMono_core, adequateEvery_core⟩,
    ⟨arises_core, exclusive_core⟩, ⟨mono_core, shareResume_core, i3_core, stopVisible_core, hF, ?_,
      i1_core, i5_core, p11_core, conservativeWB_core, embedsNil_core⟩, wbCore⟩
  rw [tier1Open_read]
  exact hSB

/-- **`Pins` at today's kernel over the open types**: the admissibility bounded below by today's,
today's unr-free rules and outlives judgements, and the answering effects' borrow form at the
unr-free rules (`i4a_tier1NU`). -/
theorem pins_tier1Open : Pins tier1Open admClosedOp .abortive := by
  unfold Pins
  rw [tier1Open_read]
  exact ⟨admExtends_closedOp, extendsNU_tier1NU, outExtends_core, i4a_tier1NU⟩

/-- **B's guarantees at today's kernel and BoLo, B5 aside, from adequacy at BoLo**: B0, B1, B3–B4,
B4′, B6, B7 and the bounds.  The library's `status_tier1End_of`'s content, in the new vocabulary. -/
theorem tier1Core_B_of (hA : Adequate (ℍ := ℍ) (B.coreB (ℍ := ℍ))) :
    B.ExtendsB tier1Open.read ∧ FL (B.coreB (ℍ := ℍ)) tier1Open.read ∧ Sound (ℍ := ℍ) tier1Open.read ∧
      B.SoundContracts (ℍ := ℍ) tier1Open.read (B.coreB (ℍ := ℍ)) ∧ B.ExclusiveB (B.coreB (ℍ := ℍ)) ∧
      LifetimeSound (B.coreB (ℍ := ℍ)) tier1Open.read.out ∧ B.WBound (B.coreB (ℍ := ℍ)) := by
  rw [tier1Open_read]
  refine ⟨⟨fun Θ Δ Γ e j h => h, B.borrowRulesClosed_of_rulesClosed extendsNU_tier1NU.2⟩,
    fl_core_tier1NU, soundnessOfFL _ _ fl_core_tier1NU hA, soundContractsOfFL fl_core_tier1NU hA,
    exclusiveB_core, lifetimeSound_core, wBound_core⟩

/-- **B's guarantees at today's kernel and BoLo, from adequacy at BoLo and the step-for-step
simulation**: `tier1Core_B_of` with B5 (`releasedOnceReuse_of_bumpSim`). -/
theorem tier1Core_guarantees_of (hA : Adequate (ℍ := ℍ) (B.coreB (ℍ := ℍ)))
    (hS : BumpSim (ℍ := ℍ)) : B.Guarantees (ℍ := ℍ) tier1Open.read (B.coreB (ℍ := ℍ)) := by
  obtain ⟨h0, h1, h3, h4, h6, h7, hb⟩ := tier1Core_B_of hA
  exact ⟨h0, h1, hA, h3, h4, releasedOnceReuse_of_bumpSim hS h4, h6, h7, hb⟩

/-! ### Tier 1 and B2 at BoLo -/

/-- **Tier 1 fails as written, at every typing system**: its B conjunct holds `Adequate coreB`, whose
drive conjunct fails at a loop type whose body is not positive (`not_adequate_core`). -/
theorem not_tier1 (J₁ : OurTyping orowRF) : ¬ Tier1 (ℍ := ℍ) J₁ :=
  fun h => not_guarantees_core J₁.read h.2.1

/-- **The restricted tier-1 reduction fails as written**, for the same reason. -/
theorem not_tier1Core : ¬ Tier1Core (ℍ := ℍ) := fun h => not_guarantees_core _ h.2.1

/-- **B's guarantees at today's kernel and BoLo, at what B2 gives**: B0, B1; B2's return conjunct at
every platform and its drive conjunct at positive loop bodies; B3 and B4 at the same; B4′ in full
(it reads only the return conjunct); B6, B7 and the bounds. -/
theorem tier1Core_B_nu :
    B.ExtendsB tier1Open.read ∧ FL (B.coreB (ℍ := ℍ)) tier1Open.read ∧
      (∀ P : Platform, P.Respects →
        AdequateRetAt (ℍ := ℍ) (B.coreB (ℍ := ℍ)) P ∧ AdequateDriveAtNu (ℍ := ℍ) (B.coreB (ℍ := ℍ)) P ∧
        SoundRetAt (ℍ := ℍ) tier1Open.read P ∧ SoundDriveAtNu (ℍ := ℍ) tier1Open.read P) ∧
      B.SoundContracts (ℍ := ℍ) tier1Open.read (B.coreB (ℍ := ℍ)) ∧ B.ExclusiveB (B.coreB (ℍ := ℍ)) ∧
      LifetimeSound (B.coreB (ℍ := ℍ)) tier1Open.read.out ∧ B.WBound (B.coreB (ℍ := ℍ)) := by
  rw [tier1Open_read]
  exact ⟨⟨fun Θ Δ Γ e j h => h, B.borrowRulesClosed_of_rulesClosed extendsNU_tier1NU.2⟩,
    fl_core_tier1NU, fun P hP => ⟨adequateRetAt_core P hP, adequateDriveAt_core_nuOk P hP,
      soundRetAt_tier1NU P hP, soundDriveAtNu_tier1NU P hP⟩,
    soundContracts_tier1NU, exclusiveB_core, lifetimeSound_core, wBound_core⟩

/-- **B5 at today's kernel and BoLo, given the step-for-step simulation.** -/
theorem tier1Core_releasedOnceReuse_of_bumpSim (hS : BumpSim (ℍ := ℍ)) :
    B.ReleasedOnceReuse (ℍ := ℍ) tier1Open.read (B.coreB (ℍ := ℍ)) := by
  rw [tier1Open_read]
  exact releasedOnceReuse_tier1NU_of_bumpSim hS

end I

end Targets

end

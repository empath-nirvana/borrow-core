import Targets.Statements.Composition
import Targets.Statements.Lifetimes
import Targets.Statements.Exclusivity
import Targets.Statements.Handlers
import Targets.Statements.Binder

/-!
# Targets — the end state (DESIGN §1.0)

**Done** is `EndStateAt J₂ W Adm RF` proved at a **named** typing system `J₂` (the kernel's
tier-2 judgment, unr-free) and a **named** world `W`, together with the step-index audit of `W`'s
definition (`Targets/Audit.lean`, DESIGN §4.4), at the `Adm` OQ-56 settles and the `RF` OQ-13's
remaining question settles.  `EndState` (the existential) is implied by done and is not done:
decision 7 (no step-indexing) constrains how `W` is defined, and an existential witness has no
definition to audit.

Every [W] conjunct is about the **same** world `M`, and every [prog] conjunct about the **same**
typing system `J`.  Tier 1 and tier 2 are `Guarantees` at two typing systems and two classes of
spanning rows.

**Beside done** (stated, available, not required): `EndStateBinder` (the freeze binder),
`Conservative` (every type), `ReleasedOnceReuse`, `I4Typing`; named-only `CancelCloses` (OQ-57) and
P8.b (OQ-50).

**Corollaries**: `I1Prog`, `I2Prog` (program level), P8.a (`P8a`, which is `ReleasedOnceAll`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms (Flag storeCancel)

/-- **Every guarantee**, for the typing system `J` at the world `M`, with OQ-56's admissibility
`Adm` and the class `c` of rows a lend may span. -/
def Guarantees (J : TypingJ) (M : SemWorld) (Adm : OpAdm) (c : RowClass) : Prop :=
  -- [prog]: the program-level guarantees
  ExtendsNU J ∧ OutExtends J.out ∧ Soundness (ℍ := ℍ) J ∧ SoundnessContracts (ℍ := ℍ) J ∧
  ReleasedOnceAll (ℍ := ℍ) J ∧ EffSafe (ℍ := ℍ) J ∧ NoInterception J ∧
  FinaliserOrder (ℍ := ℍ) J ∧
  -- [W]: the proof device and the laws every W satisfies
  WLaws (ℍ := ℍ) M ∧ FL M J ∧ Adequate (ℍ := ℍ) M ∧
  -- [W]: the interaction interface
  I1 (ℍ := ℍ) M ∧ I2 (ℍ := ℍ) M J.out Adm c ∧ I3 (ℍ := ℍ) M ∧ I5 (ℍ := ℍ) M ∧
  -- [W]: the other properties
  LifetimeSound M J.out ∧ Exclusive M ∧ P11 (ℍ := ℍ) M ∧ ConservativeWB (ℍ := ℍ) M

/-- **The end state at a typing system and a world.**  The row form is safe and is the one the
typing rules use; the admissibility contains R-CLOSEDOP; the typing system holds tier 2's spanning
rules, accepts the tier-2 programs and types answering effects as borrows; and it meets every
guarantee at `M`, lends spanning any unr-free row. -/
def EndStateAt (J : TypingJ) (M : SemWorld) (Adm : OpAdm) (RF : RowForm) : Prop :=
  RowAlgSafe RF ∧ RowLink RF ∧ AdmExtends Adm ∧
  Tier2Pinned J Adm ∧ AcceptsTier2 J ∧ I4a J Adm .any ∧ Guarantees (ℍ := ℍ) J M Adm .any

/-- Some typing system and some world meet it.  Implied by done; not done. -/
def EndState (Adm : OpAdm) (RF : RowForm) : Prop := ∃ J M, EndStateAt (ℍ := ℍ) J M Adm RF

/-- **Tier 1 at σ = []**: every guarantee for Core's typing at Core's relation, lends spanning
abortive rows only. -/
def Tier1End : Prop :=
  RowAlgSafe orowRF ∧ RowLink orowRF ∧ WBCore (ℍ := ℍ) ∧ I4a tier1 admClosedOp .abortive ∧
  Guarantees (ℍ := ℍ) tier1 (coreW (ℍ := ℍ)) admClosedOp .abortive

/-- The end state with the freeze binder: the named strengthening, beside done. -/
def EndStateBinder (J : TypingJ) (M : SemWorld) (act : StkAct M) (Adm : OpAdm) (RF : RowForm) :
    Prop :=
  EndStateAt (ℍ := ℍ) J M Adm RF ∧ FreezeBinder M act ∧ BinderMachine (ℍ := ℍ)

/-- **I1 at the program level**: suspensions stored in a cell, moved, and then cancelled
(`storeCancel`) or resumed (`at17`). -/
def I1Prog (J : TypingJ) : Prop :=
  TypedSound (ℍ := ℍ) J storeCancel .unit ∧ TypedSound (ℍ := ℍ) J at17 Flag

/-- **I2 at the program level**: lends spanning a once-resuming operation (`at02`, `at04`) and an
affine one whose continuation is cancelled (`at12`). -/
def I2Prog (J : TypingJ) : Prop :=
  TypedSound (ℍ := ℍ) J at02 Flag ∧ TypedSound (ℍ := ℍ) J at04 (.tensor Flag Flag) ∧
  TypedSound (ℍ := ℍ) J at12 Flag

end Targets

end

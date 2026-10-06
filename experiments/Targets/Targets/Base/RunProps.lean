import Targets.Base.Typing
import Targets.Base.Machine

/-!
# Base — the statements about runs that mention no world (RESTRUCTURE §0, base)

B's guarantees and the Instance's bridges both read these, so they mention no world and live in
base: T1 (`SoundRetAt`, `SoundDriveAt`, `SoundnessAt`, `Soundness`, `SoundnessContracts`,
`TypedSound`), Core's form of P2 (`EffSafe`), and P2 for driven programs (`EffSafeDrive`,
RESTRUCTURE §4.1).  `Sound` is `Soundness` under the name B's guarantees use (B3, B4).

Literature: [CONF] Theorem 3.2 / Corollary 3.3; Affect §3.2 ("safe e := ∀ e′ σ′. e / ∅ →∗ e′ / σ′
=⇒ e′ ∈ Val ∨ (∃ e″ σ″. e′ / σ′ → e″ / σ″)"); Ahman–Bauer Def. 1 (runners).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- Programs at a div-free answer: safe and terminating, every run ending with the memory empty. -/
def SoundRetAt (J : TypingJ) (P : Platform) : Prop :=
  ∀ (S : Row) (A : VTy) (e : Expr), DivFree S A → RowLe S P.ops →
    J.closed e (CTy.effOf S A) → SafeRuns (ℍ := ℍ) P A e ∧ Terminates (ℍ := ℍ) P A e

/-- Programs that return a loop: every finite prefix of the drive is safe. -/
def SoundDriveAt (J : TypingJ) (P : Platform) : Prop :=
  ∀ (S : Row) (A B : VTy) (e : Expr), A.Data → RowLe S P.ops →
    J.closed e (CTy.effOf S (.thunk (CTy.loopEff S A B))) → SafeDrive (ℍ := ℍ) P A e

/-- T1 at one platform. -/
def SoundnessAt (J : TypingJ) (P : Platform) : Prop :=
  SoundRetAt (ℍ := ℍ) J P ∧ SoundDriveAt (ℍ := ℍ) J P

/-- **T1.** -/
def Soundness (J : TypingJ) : Prop := ∀ P : Platform, P.Respects → SoundnessAt (ℍ := ℍ) J P

/-- T1 with capabilities as externs meeting their contracts (today's I/O presentation,
`ExternsMeet`), together with platform operations, at every row the platform answers. -/
def SoundnessContracts (J : TypingJ) : Prop :=
  ∀ P : Platform, P.Respects → ∀ (Γ : Ctx VTy) (γ : List Val) (S : Row) (A : VTy) (e : Expr),
    DivFree S A → RowLe S P.ops → J.at LifeCtx.empty Γ e (.comp (CTy.effOf S A)) →
    ExternsMeet (ℍ := ℍ) Γ γ →
    SafeRuns (ℍ := ℍ) P A (substAll γ e) ∧ Terminates (ℍ := ℍ) P A (substAll γ e)

/-- A closed program at a data answer that the typing system types and every platform runs
safely to the end. -/
def TypedSound (J : TypingJ) (e : Expr) (A : VTy) : Prop :=
  J.closed e (.ret A) ∧ ∀ P : Platform, P.Respects →
    SafeRuns (ℍ := ℍ) P A e ∧ Terminates (ℍ := ℍ) P A e


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Steps Step1)

/-- **P2**, at unr-free rows (a row with a resuming `unr` operation is covered at tier 1, by Core's
adequacy). -/
def EffSafe (J : TypingJ) : Prop :=
  ∀ e (S : Row) A, Row.NU S → J.closed e (CTy.effOf S A) →
    ∀ μ' e', Steps (ℍ := ℍ) Adequacy.emptyMem e μ' e' →
      IsVal e' ∨ (∃ μ'' e'', Step1 (ℍ := ℍ) μ' e' μ'' e'') ∨ StopsIn S e'


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **B3 and B4** (T1): every well-typed program, under every allocator and every platform that
respects its protocol, is safe, and at a div-free answer terminates with the memory empty. -/
abbrev Sound (J : TypingJ) : Prop := Soundness (ℍ := ℍ) J

/-- **P2 for driven programs**: every configuration the drive of a typed driven program reaches is
a finished drive, takes a step, or stops at an operation of the row. -/
def EffSafeDrive (J : TypingJ) : Prop :=
  ∀ M (S : Row) A, Row.NU S → J.closed M (CTy.effOf S (.sum A (.thunk (CTy.loopEff S A .unit)))) →
    ∀ rc, Relation.ReflTransGen (RStep (ℍ := ℍ) Platform.none) (init _ M, .drive) rc →
      FinalDrive Platform.none A rc ∨ (∃ rc', RStep (ℍ := ℍ) Platform.none rc rc') ∨ StopsIn S rc.1.e


end Targets

end

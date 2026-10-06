import Targets.Defs.Typing
import Targets.Defs.Runs

/-!
# Targets — T1, Soundness (unary), and exactly-once release (DESIGN §3 T1, §2 D9)

**World:** [prog].  The proof route goes through [W] (`FL`, `Adequate`; `SoundnessOfFL`).

Take every well-typed program, every allocator, and every platform that respects its protocol.

* Every run is safe: never stuck, so no use after free, no double release, no unhandled
  operation (`SafeRuns`).
* A program at a div-free answer terminates, every run ending at a value of its type with the
  memory empty, so every owned cell and capability is released, those held inside cancelled
  continuations included (`Terminates`, `Final`).
* A program that returns a loop is driven by the runtime, possibly forever; every finite prefix of
  the drive is safe (`SafeDrive`).
* The same holds with capabilities given as externs meeting their contracts, while the program
  performs platform operations (`SoundnessContracts`).
* Every complete run that reuses no location releases every cell it allocates exactly once
  (`ReleasedOnceAll`, D9).

Termination is claimed only where the answer is div-free.  Main's row holds only platform
operations (`RowLe S P.ops`, every platform operation linear and resuming), so an error must be
handled before the top.  Tier 1 and tier 2 are this theorem at two typing systems.

Literature: [CONF] Theorem 3.2 / Corollary 3.3 (adequacy: "(∅, e) →∗ (∅, v)"); Affect §3.2
("safe e := ∀ e′ σ′. e / ∅ →∗ e′ / σ′ =⇒ e′ ∈ Val ∨ (∃ e″ σ″. e′ / σ′ → e″ / σ″)"); Congard et al.
§3 ("all allocated resources are released by the end of the program, only previously-allocated
resources are released, no resource has been released twice"); Ahman–Bauer Def. 1 (runners).
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

/-- **The machine lemma** (D9): a safe, terminating program releases every cell
exactly once on every complete run that reuses no location. -/
def ReleasedOnceOfSound : Prop :=
  ∀ (P : Platform) (A : VTy) (e : Expr), SafeRuns (ℍ := ℍ) P A e → Terminates (ℍ := ℍ) P A e →
    ∀ cs, PRun (ℍ := ℍ) P (init P e :: cs) → NoReuse (init P e :: cs) →
      (∀ c, (init P e :: cs).getLast? = some c → Final P A c) → ReleasedOnce (init P e :: cs)

/-- **Exactly-once release, a conjunct of done**: every complete run that reuses no location, of
every program T1 covers, externs given as values meeting their contracts included, releases every
cell it allocates exactly once. -/
def ReleasedOnceAll (J : TypingJ) : Prop :=
  ∀ (P : Platform), P.Respects → ∀ (Γ : Ctx VTy) (γ : List Val) (S : Row) (A : VTy) (e : Expr),
    DivFree S A → RowLe S P.ops → J.at LifeCtx.empty Γ e (.comp (CTy.effOf S A)) →
    ExternsMeet (ℍ := ℍ) Γ γ →
    ∀ cs, PRun (ℍ := ℍ) P (init P (substAll γ e) :: cs) →
      NoReuse (init P (substAll γ e) :: cs) →
      (∀ c, (init P (substAll γ e) :: cs).getLast? = some c → Final P A c) →
      ReleasedOnce (init P (substAll γ e) :: cs)

/-- A closed program at a data answer that the typing system types and every platform runs
safely to the end. -/
def TypedSound (J : TypingJ) (e : Expr) (A : VTy) : Prop :=
  J.closed e (.ret A) ∧ ∀ P : Platform, P.Respects →
    SafeRuns (ℍ := ℍ) P A e ∧ Terminates (ℍ := ℍ) P A e

end Targets

end

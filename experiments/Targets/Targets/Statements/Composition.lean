import Targets.Statements.Soundness
import Targets.Statements.EffectSafety
import Targets.Statements.Conservativity
import Targets.Statements.Interface

/-!
# Targets — the generic composition lemmas, as targets (DESIGN §4.1, §1.5)

**World:** generic: each is a statement about every `M` and `J`, proved once.

* `SoundnessOfFL`: `FL M J → Adequate M → Soundness J`.  Soundness is a corollary of FL.
* `SoundnessContractsOfFL`: with externs meeting Core's contracts.  **Corrected** (DESIGN
  §Corrections C2): the design asked `ConservativeWB M` (row-abortive types), but `ExternsMeet`
  admits an extern at any persistent type, `!U(C)` at a resuming row included
  (`VTy.persistent (.bang _) = true`), and taking the extern into W at the nil index needs the
  Kripke order's reflexivity.  The corrected form asks `ExtPre M` and the every-type embedding
  `Conservative M`; `SoundnessContractsOfFLWB` is the design's route, at externs of row-abortive
  type (`SoundnessContractsAR`).
* `EffSafeOfFL`: `FL M J → WLaws M → EffSafe J`.
* `AdequateOfLaws`: `WLaws M → ShareResume M → UpdSeq M → UpdReclaim M → Adequate M` (second
  wave: `wpTS_demonic`'s replay and `theorem32D`'s reclaim over `wpGW`).  The replay composes
  chained runs, platform answers and drive observations by `UpdSeq`, as `wpG_bind` composes two
  runs (`Core/EffWp.lean:910-911`), and empties the garbage by `UpdReclaim`, as `theorem32D` does
  (`Core/Demonic.lean:300-306`).  Both steps read the run-end relation, a field of the world
  (`SemWorld.Upd`), so they are properties of `M.Upd` and named hypotheses, as `ShareResume` is.
  Where `Upd` is Core's at every index they are Core's lemmas (`ResU.UpdV.trans` after
  `updV_frame`; `reclaim`), and both hold (`updSeq_of_core`, `updReclaim_of_core`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `SoundnessContracts` at externs of row-abortive type. -/
def SoundnessContractsAR (J : TypingJ) : Prop :=
  ∀ P : Platform, P.Respects → ∀ (Γ : Ctx VTy) (γ : List Val) (S : Row) (A : VTy) (e : Expr),
    (∀ s ∈ Γ, s.ty.AbortRows) →
    DivFree S A → RowLe S P.ops → J.at LifeCtx.empty Γ e (.comp (CTy.effOf S A)) →
    ExternsMeet (ℍ := ℍ) Γ γ →
    SafeRuns (ℍ := ℍ) P A (substAll γ e) ∧ Terminates (ℍ := ℍ) P A (substAll γ e)

/-- **Soundness is a corollary of FL and adequacy.** -/
def SoundnessOfFL : Prop :=
  ∀ (M : SemWorld) (J : TypingJ), FL M J → Adequate (ℍ := ℍ) M → Soundness (ℍ := ℍ) J

/-- **Soundness with externs, from FL** (corrected: `ExtPre` and the every-type embedding). -/
def SoundnessContractsOfFL : Prop :=
  ∀ (M : SemWorld) (J : TypingJ), FL M J → ExtPre M → Conservative (ℍ := ℍ) M →
    Adequate (ℍ := ℍ) M → SoundnessContracts (ℍ := ℍ) J

/-- **Soundness with externs of row-abortive type, from FL** (the design's route). -/
def SoundnessContractsOfFLWB : Prop :=
  ∀ (M : SemWorld) (J : TypingJ), FL M J → ExtPre M → ConservativeWB (ℍ := ℍ) M →
    Adequate (ℍ := ℍ) M → SoundnessContractsAR (ℍ := ℍ) J

/-- **Effect safety from FL and the laws.** -/
def EffSafeOfFL : Prop :=
  ∀ (M : SemWorld) (J : TypingJ), FL M J → WLaws (ℍ := ℍ) M → EffSafe (ℍ := ℍ) J

/-- **Adequacy from the laws** (second wave), with the run-end relation's sequencing and reclaim
laws. -/
def AdequateOfLaws : Prop :=
  ∀ M : SemWorld, WLaws (ℍ := ℍ) M → ShareResume M → UpdSeq M → UpdReclaim M →
    Adequate (ℍ := ℍ) M

end Targets

end

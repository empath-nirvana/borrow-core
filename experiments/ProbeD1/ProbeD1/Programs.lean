import ProbeD1.Statement34

/-!
# ProbeD1 — the programs, the sample row, the side check, and the arising check (DESIGN §9–§11)

* **Statement 5, the programs.** `semTyping p` is the semantic typing system at W: a judgement
  holds when `SemS` does at every admissible instance of its row context. `GenSelfAccepted p` is
  Targets' `AcceptedAt` (`Targets/I/Programs.lean`) at it, for `genSelf` as built;
  `ReconAccepted p e` the same for the term built for `reconB′`.
* **Statement 6, the sample row.** `ThenRow p`: `[then]` at W at every stack, the row whose case
  "a frozen frame unwinding at a cancel, at an inner affine row" GhostEnd step 3f leaves open.
* **Statement 7, the side check.** Targets' `NotVDenNaturalArises` (`Targets/I/Binder.lean`), as it
  stands.
* **`Probe p`** bundles statement 0's shared lemmas and statements 0–6 at one placement.
  **`Survives e p`** adds `reconB′`'s acceptance at its term `e`, which is fixed and committed here
  before statement 2's proofs start (DESIGN §9.2). W is the placement of least `rank` among those
  whose `Survives` is proved: the cuts order of synthesis §4.2, `cbpv`, then `binder`, then
  `binder0`. It is decided only when every placement of lower rank is refuted by a refutation that
  passes the arising check; a lower-rank placement that is only not derived leaves W provisional,
  and no consequence is drawn for D1's ranking (DESIGN §3). The arising check is `Arising.lean`'s.

Statements only; no proofs.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack TabAtS)
open BoCa.Fig16.LogRel.Core.EffPrograms (Flag)

/-! ### Statement 5: the programs -/

/-- **The semantic typing system at W.** -/
def semTyping (p : Placement) : Targets.TypingJ :=
  ⟨fun Θ Δ Γ e j => ∀ η, Θ.Models η → SemS (ℍ := ℍ) p Δ (Γ η) e (j η), Targets.OutJ.core⟩

/-- **`genSelf` accepted at W**, with its answer `tt` (`genSelf_eval`). -/
def GenSelfAccepted (p : Placement) : Prop :=
  Targets.AcceptedAt (ℍ := ℍ) (semTyping (ℍ := ℍ) p) Targets.genSelf Flag (Val.inj₂ .unit)

/-- **`reconB′` accepted at W**, at the term `e` built for it, with its answer `(tt, ff)`. -/
def ReconAccepted (p : Placement) (e : Expr) : Prop :=
  Targets.AcceptedAt (ℍ := ℍ) (semTyping (ℍ := ℍ) p) e (.tensor Flag Flag)
    (Val.pair (Val.inj₂ .unit) (Val.inj₁ .unit))

/-! ### Statement 6: the sample row -/

/-- **`[then]` at W**, at every stack, the finaliser at the pure row as the kernel's `[then]` types
it (SPEC §24, option A). The intermediate type `A` is the one the premises add, so the row takes
its binder hygiene. -/
def ThenRow (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ Γ₁ Γ₂ : Ctx VTy) (M N D : Expr) (A B : VTy) (S : Row),
    Ctx.SplitP Γ Γ₁ Γ₂ → S.NZ → S.Uniq → (S.Unr → Persistent Γ₂) →
    (∀ x ∈ VTy.binders A, ¬ NsVar x) →
    SemS p Δ Γ₁ M (.comp (CTy.effOf S A)) →
    SemS p Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B)) →
    SemS p Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (.ret .unit)) →
    SemS p Δ Γ (thenE N D M) (.comp (CTy.effOf S B))

/-! ### The probe at one placement -/

/-- **Statements 0–6 at the placement `p`**, with statement 0's shared lemmas. `reconB′`'s
acceptance is stated at its term, fixed before statement 2's proofs start (DESIGN §9.2). -/
def Probe (p : Placement) : Prop :=
  Statement0Shared (ℍ := ℍ) ∧ Statement0 (ℍ := ℍ) p ∧ Statement1 (ℍ := ℍ) p ∧
    Statement2 (ℍ := ℍ) p ∧ Statement3 (ℍ := ℍ) p ∧ Statement4 (ℍ := ℍ) p ∧
    GenSelfAccepted (ℍ := ℍ) p ∧ ThenRow (ℍ := ℍ) p

/-! ### Which placement is W -/

/-- The cuts order (synthesis §4.2): the future-world quantifier at the resume cut's value side
first, at every binder clause next, at `∀` only last. -/
def Placement.rank : Placement → Nat
  | .cbpv => 0
  | .binder => 1
  | .binder0 => 2

/-- **A placement survives**: its probe bundle, and `reconB′` accepted at the term `e` built for
it. W is the surviving placement of least `rank`: decided when every placement of lower rank is
refuted by a refutation that passes the arising check, provisional when one is only not derived
(DESIGN §3, §12.1). -/
def Survives (e : Expr) (p : Placement) : Prop :=
  Probe (ℍ := ℍ) p ∧ ReconAccepted (ℍ := ℍ) p e

end ProbeD1

end

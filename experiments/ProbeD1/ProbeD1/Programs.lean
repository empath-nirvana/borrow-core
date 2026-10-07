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
* **The arising check.** `ArisesAt` is what a configuration refuting one of the statements must
  satisfy, beside every hypothesis of the statement it refutes (DESIGN §11).
* **`Probe p`** bundles statements 0–6 at one placement.

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

/-- **`[then]` at W**, at every stack. The intermediate type `A` is the one the premises add, so the
row takes its binder hygiene. -/
def ThenRow (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ Γ₁ Γ₂ : Ctx VTy) (M N D : Expr) (A B : VTy) (S : Row),
    Ctx.SplitP Γ Γ₁ Γ₂ → S.NZ → S.Uniq → (S.Unr → Persistent Γ₂) →
    (∀ x ∈ VTy.binders A, ¬ NsVar x) →
    SemS p Δ Γ₁ M (.comp (CTy.effOf S A)) →
    SemS p Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B)) →
    SemS p Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (CTy.effOf S.abortOnly .unit)) →
    SemS p Δ Γ (thenE N D M) (.comp (CTy.effOf S B))

/-! ### The arising check -/

/-- **A configuration that arises at W's index**: its world `fρ = ρf ● ρ` a tagged `TW` world at
the records, the stack in shape, every 6.64 entry among `TW`'s records, every 6.65 entry's place a
`mut` cell of the world, and the local part `ρ` consistent with the stack's table (the stack's run
invariant, statement 1). -/
def ArisesAt (σ : LStack) (αs : List Life) (ls : List SRec) (ps : List FrameRec)
    (ρf ρ fρ : WRes) : Prop :=
  TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls ∧ ResU.Hash ρf ρ ∧ ResU.CompS ρf ρ fρ ∧
    StackOK σ αs ∧ (∀ e ∈ σ, ∀ u, e.k = .imm u → ∃ r ∈ ps, r.le = e.l) ∧
    (∀ e ∈ σ, e.k = .mut → ∃ ψ : CellU BoCa.Loc Val, fρ.get e.l = some ψ ∧ ψ.kind = Kind.mut) ∧
    TabAtS σ αs ρ

/-! ### The probe at one placement -/

/-- **Statements 0–6 at the placement `p`.** `reconB′`'s acceptance is stated at its term, once
built (DESIGN §9.2). -/
def Probe (p : Placement) : Prop :=
  Statement0 (ℍ := ℍ) p ∧ Statement1 (ℍ := ℍ) p ∧ Statement2 (ℍ := ℍ) p ∧
    Statement3 (ℍ := ℍ) p ∧ Statement4 (ℍ := ℍ) p ∧ GenSelfAccepted (ℍ := ℍ) p ∧
    ThenRow (ℍ := ℍ) p

end ProbeD1

end

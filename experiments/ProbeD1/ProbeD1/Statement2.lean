import ProbeD1.Statement1

/-!
# ProbeD1 — statement 2: the borrow-constant rows at `σ·y`, and Law 2 for `withload` (DESIGN §6)

* **The spanning rows at W** (`SpanW2Row`, `SpanW1Row`): Targets' `SpanWithbor2` and `SpanWithbor1`
  (`Targets/I/Interface.lean`) at `Adm = admClosedOp`, class `.any`, `O = OutJ.core`, stated at
  `SemS`. The 6.65 row is `genSelf`'s; the 6.64 row is `reconB′`'s two borrows. Their callback is
  read at `σ·y` through the placement's clause (`CallbackExtMut`, `CallbackExtImm`).
* **[TR] 6.150 at a resuming table** (`RebFrameR`): the lift GhostEnd's report lists carry as the
  untranscribed printed lemma in the run-up of the borrow-constant rows. It is stated at Core's
  relation, where the other lifts (`ewpTS_M_frameR`, `ewpTS_I_frameR`, `ewpTS_M_antiFrameR`) are:
  the re-borrowing callback's least fixed point, a stop owing the view kept beside the callback
  (`ptoImm_dup`) and the callback again.
* **`withload` spanning a stop at W** (`SpanLoadRow`): Targets' `SpanWithload` at `SemS`.

Statements only; no proofs.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open Targets (RowSpan admClosedOp RowClass OutJ)

/-! ### The spanning rows at W -/

/-- **`withbor` (2) spanning a stop, at W** (`SpanWithbor2 W OutJ.core admClosedOp .any` at
`SemS`). -/
def SpanW2Row (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A B : VTy) (S : Row) (d : Expr) (x : LifeVar),
    Ctx.DeadP Γ → Δ.find? x = none → (∃ b, Δ.Defines b ∧ OutJ.core.le Δ b A) →
    ¬ VFree x A → ¬ VFree x B → RowSpan admClosedOp Δ x S → RowClass.any.Admits S →
    closedAt 0 d = true →
    SemS p Δ Γ d (.val (.lolli (.ref A) .unit)) →
    SemS p Δ Γ (withborUE d) (.val (withbor2UTy x Δ.meetOfDom A B S))

/-- **`withbor` (1) spanning a stop, at W** (`SpanWithbor1 W OutJ.core admClosedOp .any` at
`SemS`): the 6.64 lend, whose cancel path is the one not built (`CancelImmFrame`, DESIGN §6.2). -/
def SpanW1Row (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (A B : VTy) (S : Row) (d : Expr) (x : LifeVar),
    Ctx.DeadP Γ → Δ.find? x = none → VScoped Δ A →
    ¬ VFree x A → ¬ VFree x B → RowSpan admClosedOp Δ x S → RowClass.any.Admits S →
    closedAt 0 d = true →
    SemS p Δ Γ d (.val (.lolli (.ref A) .unit)) →
    SemS p Δ Γ (withborUE d) (.val (withbor1UTy x Δ.meetOfDom A B S))

/-- **`withload` spanning a stop, at W** (`SpanWithload W OutJ.core admClosedOp .any` at `SemS`). -/
def SpanLoadRow (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) (A B : VTy) (S : Row) (x : LifeVar),
    Ctx.DeadP Γ → Δ.find? x = none → ¬ VFree x A → ¬ VFree x B →
    RowSpan admClosedOp Δ x S → RowClass.any.Admits S →
    SemS p Δ Γ withload (.val (withloadUTy a x Δ.meetOfDom A B S))

/-! ### [TR] 6.150 at a resuming table -/

/-- The view 6.150 consumes: `ℓ ↦ Imm α (И β. ↺_β P̂₀)`, the payload in `R`. -/
def rebView (l : BoCa.Loc) (α : Life) (R : Val → WRes → Prop) (P₀ : Life → Val → WProp) :
    WProp :=
  ptoImm l α (fun v σ => R v σ ∧ fresh (fun b => reborrow b (P₀ b v)) σ)

/-- **One unfolding of the re-borrowing callback** at a resuming table: 6.150's premise
(`wpG_reborrow`'s), its postcondition an answer in `Q` or a stop the table admits, owing the view
again beside the next unfolding. -/
def rebF (Tb : Table) (l : BoCa.Loc) (α : Life) (R : Val → WRes → Prop)
    (P₀ P : Life → Val → WProp) (Q : List SRec → Val → WProp) (X : List SRec → Expr → WProp) :
    List SRec → Expr → WProp :=
  fun ls e => fresh fun b => all fun v => P b v ─⋆ wpG ls e (fun ls' t => box b (fun ρ =>
    valPost Q ls' t ρ ∨ Tb ls' t (fun ls'' e'' => rebView l α R P₀ ⋆ X ls'' e'') ρ))

/-- **The re-borrowing callback**: the least fixed point of `rebF`, written in `Prop` as `ewpTS`
is. -/
def RebRelend (Tb : Table) (l : BoCa.Loc) (α : Life) (R : Val → WRes → Prop)
    (P₀ P : Life → Val → WProp) (Q : List SRec → Val → WProp) (ls : List SRec) (e : Expr) :
    WProp := fun ρ =>
  ∀ X : List SRec → Expr → WProp, (∀ ls e ρ, rebF Tb l α R P₀ P Q X ls e ρ → X ls e ρ) →
    X ls e ρ

/-- **[TR] 6.150 at a resuming table** (Law 2 for `withload`): the view beside the re-borrowing
callback gives the callback's `ewpTS`. The chooser is taken at every list, where
`rebChooseTW_top` supplies it at each resumption's list (the record persists along `Ext`). -/
def RebFrameR : Prop :=
  ∀ (Tb : Table), Tb.Mono → ∀ (l : BoCa.Loc) (α : Life) (R : Val → WRes → Prop)
    (P₀ P : Life → Val → WProp) (Q : List SRec → Val → WProp) (ls : List SRec) (e : Expr),
    (∀ ls', RebChooseTW ls' l R P₀ P) →
    Entails (rebView l α R P₀ ⋆ RebRelend (ℍ := ℍ) Tb l α R P₀ P Q ls e)
      (ewpTS (ℍ := ℍ) ls e Tb Q)

/-! ### The bundle -/

/-- **Statement 2 at the placement `p`**: the two spanning rows the programs use, and 6.150's
lift. `SpanLoadRow` is Law 2 for `withload` at W, stated beside it (DESIGN §6.4). -/
def Statement2 (p : Placement) : Prop :=
  SpanW2Row (ℍ := ℍ) p ∧ SpanW1Row (ℍ := ℍ) p ∧ RebFrameR (ℍ := ℍ)

end ProbeD1

end

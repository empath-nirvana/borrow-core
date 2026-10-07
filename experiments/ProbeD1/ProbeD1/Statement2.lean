import ProbeD1.Statement1

/-!
# ProbeD1 — statement 2: the borrow-constant rows at `σ·y`, and Law 2 for `withload` (DESIGN §6)

* **The spanning rows at W** (`SpanW2Row`, `SpanW1Row`): Targets' `SpanWithbor2` and `SpanWithbor1`
  (`Targets/I/Interface.lean`) at `Adm = admClosedOp`, class `.any`, `O = OutJ.core`, stated at
  `SemS`. The 6.65 row is `genSelf`'s; the 6.64 row is `reconB′`'s two borrows. Their callback is
  read at `σ·y` through the placement's clause (`CallbackExtMut`, `CallbackExtImm`).
* **[TR] 6.150 at a resuming table** (`RebFrameR`): the lift GhostEnd's report lists as the
  untranscribed printed lemma in the run-up of the borrow-constant rows. It is stated at Core's
  relation, where the other lifts (`ewpTS_M_frameR`, `ewpTS_I_frameR`, `ewpTS_M_antiFrameR`) are,
  and shaped as they are: the re-borrowing callback's least fixed point, whose postcondition takes
  back the copy of the view the lift keeps beside it (`ptoImm_dup`) before owing it, with the next
  unfolding, to the continuation at a stop. The chooser is asked at the lists that hold the view's
  record, with its payload input and its image indexed by the list, as `rebChooseTW_top` supplies
  them. Two hypotheses carry what the steps of a resumption read: the payload input along `Ext`
  (`RCarried`) and the record kept on the table's resumption lists (`TabKeepsRec`).
  `RebChooserNonVacuous` shows them, the chooser and the view together at one record whose payload
  is not data.
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
`SemS`): the 6.64 lend, whose cancel path is the one not built (DESIGN §6.2). -/
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

/-- The view 6.150 consumes, at the list `ls`: `ℓ ↦ Imm α (И β. ↺_β P̂₀)`, the payload in `R ls`. -/
def rebView (l : BoCa.Loc) (α : Life) (R : List SRec → Val → WRes → Prop)
    (P₀ : Life → Val → WProp) (ls : List SRec) : WProp :=
  ptoImm l α (fun v σ => R ls v σ ∧ fresh (fun b => reborrow b (P₀ b v)) σ)

/-- **One unfolding of the re-borrowing callback** at a resuming table: 6.150's premise
(`wpG_reborrow`'s), handed the chosen image at the list it starts from; at its end the copy of the
view the lift keeps is handed back (the wand), and the callback answers in `Q` or stops as the
table admits, owing the view at the resumption's list beside the next unfolding. -/
def rebF (Tb : Table) (l : BoCa.Loc) (α : Life) (R : List SRec → Val → WRes → Prop)
    (P₀ : Life → Val → WProp) (P : List SRec → Life → Val → WProp) (Q : List SRec → Val → WProp)
    (X : List SRec → Expr → WProp) : List SRec → Expr → WProp :=
  fun ls e => fresh fun b => all fun v => P ls b v ─⋆ wpG ls e (fun ls' t => box b
    (rebView l α R P₀ ls' ─⋆ fun ρ => valPost Q ls' t ρ ∨
      Tb ls' t (fun ls'' e'' => rebView l α R P₀ ls'' ⋆ X ls'' e'') ρ))

/-- **The re-borrowing callback**: the least fixed point of `rebF`, written in `Prop` as `ewpTS`
is. -/
def RebRelend (Tb : Table) (l : BoCa.Loc) (α : Life) (R : List SRec → Val → WRes → Prop)
    (P₀ : Life → Val → WProp) (P : List SRec → Life → Val → WProp) (Q : List SRec → Val → WProp)
    (ls : List SRec) (e : Expr) : WProp := fun ρ =>
  ∀ X : List SRec → Expr → WProp, (∀ ls e ρ, rebF Tb l α R P₀ P Q X ls e ρ → X ls e ρ) →
    X ls e ρ

/-- **The payload input carried along `Ext`** (6.64's `hQ` form). The lift carries the kept copy
of the view to the run's end by `wpG_frame`, whose `hR` asks the frame carried to every list with
the same members as the start's; such lists are `Ext`-related at every resource, so this gives it.
`R ls = vC false r.T ls r.δ` meets it by `vC_local`. -/
def RCarried (R : List SRec → Val → WRes → Prop) : Prop :=
  ∀ (ls ls' : List SRec) (v : Val) (σ : WRes), Ext ls ls' σ → R ls v σ → R ls' v σ

/-- **The table keeps the view's record on the lists it resumes at** (in the shape of 6.64's
`hTL`, `opTable_extR`). At a stop over a list that holds `r`, whose continuation is owed the view of
`r`'s cell, the table owes it only at lists that still hold `r`; the next unfolding's chooser is
asked at those lists. `opTable` meets it at a table whose answers hold nothing: its share is
quantified over `Ext` at the share's resource (`contShare`), that share holds the view the
continuation is owed, and `Ext` keeps a record relevant to it (`Keeps`, `Rel`). -/
def TabKeepsRec (Tb : Table) (r : FrameRec) (α : Life) (R : List SRec → Val → WRes → Prop)
    (P₀ : Life → Val → WProp) : Prop :=
  ∀ (ls : List SRec) (t : Expr) (X : List SRec → Expr → WProp) (ρ : WRes), r ∈ rsOf ls →
    Tb ls t (fun ls'' e'' => rebView r.le α R P₀ ls'' ⋆ X ls'' e'') ρ →
    Tb ls t (fun ls'' e'' ρ'' => r ∈ rsOf ls'' ∧ (rebView r.le α R P₀ ls'' ⋆ X ls'' e'') ρ'') ρ

/-- **[TR] 6.150 at a resuming table** (Law 2 for `withload`): the view of a record's cell beside
the re-borrowing callback gives the callback's `ewpTS`. Two hypotheses carry what the printed
proof's one run does not meet at a resumption, each from the step that reads it (DESIGN §6.2): the
payload input carried to the run's end list (`RCarried`, for `wpG_frame`), and the record kept on
the lists the table resumes at (`TabKeepsRec`, for the next unfolding's `wpG_reborrow`). The
chooser (6.150's H16) is asked at every list that holds the record, its payload input `R` and its
image `P` read at that list. -/
def RebFrameR : Prop :=
  ∀ (Tb : Table), Tb.Mono → ∀ (r : FrameRec) (α : Life) (R : List SRec → Val → WRes → Prop)
    (P₀ : Life → Val → WProp) (P : List SRec → Life → Val → WProp) (Q : List SRec → Val → WProp)
    (ls : List SRec) (e : Expr),
    RCarried R → TabKeepsRec Tb r α R P₀ →
    r ∈ rsOf ls → (∀ ls', r ∈ rsOf ls' → RebChooseTW ls' r.le (R ls') P₀ (P ls')) →
    Entails (rebView r.le α R P₀ ls ⋆ RebRelend (ℍ := ℍ) Tb r.le α R P₀ P Q ls e)
      (ewpTS (ℍ := ℍ) ls e Tb Q)

/-- **`RebFrameR`'s hypotheses hold together where 6.150 does anything**: at one record whose
payload is not data (its reborrow image is not its type), at a resuming operation table, the
payload input of the program's relation is carried along `Ext`, the table keeps the record, the
chooser is supplied at every list holding the record (`rebChooseTW_top`, at `δ' = r.δ`), and the
view is inhabited. -/
def RebChooserNonVacuous : Prop :=
  ∃ (r : FrameRec) (x : LifeVar) (α : Life) (ls : List SRec) (ρ : WRes) (Tab : OpTab)
    (n i : UInt32) (en : OpEnt),
    r.T.immReborrow (.var x) ≠ r.T ∧ ¬ VFree x r.T ∧ r ∈ rsOf ls ∧
    Tab n i = some en ∧ en.abort = false ∧
    RCarried (fun ls' w σ => vC false r.T ls' r.δ w σ) ∧
    TabKeepsRec (opTable Tab) r α (fun ls' w σ => vC false r.T ls' r.δ w σ)
      (fun β w χ => vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) w χ) ∧
    (∀ ls', r ∈ rsOf ls' →
      RebChooseTW ls' r.le (fun w σ => vC false r.T ls' r.δ w σ)
        (fun β w χ => vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) w χ)
        (fun β w χ => vC true (r.T.immReborrow (.var x)) ls' (r.δ.extend x β) w χ)) ∧
    rebView r.le α (fun ls' w σ => vC false r.T ls' r.δ w σ)
      (fun β w χ => vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) w χ) ls ρ

/-! ### The bundle -/

/-- **Statement 2 at the placement `p`**: the two spanning rows the programs use, and 6.150's
lift. `SpanLoadRow` is Law 2 for `withload` at W, stated beside it (DESIGN §6.2). -/
def Statement2 (p : Placement) : Prop :=
  SpanW2Row (ℍ := ℍ) p ∧ SpanW1Row (ℍ := ℍ) p ∧ RebFrameR (ℍ := ℍ)

end ProbeD1

end

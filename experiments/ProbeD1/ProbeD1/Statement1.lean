import ProbeD1.Statement0

/-!
# ProbeD1 — statement 1: the guard read from `TW` (OQ-45; DESIGN §5)

W's guard is the stack's table `TabAtS`. Statement 1 is that the table is a `TW` invariant at every
depth: it holds at the empty stack, at every part of a resource that has it, at the start of every
lend W's rules open, after every re-lend and every future, and after every run from a `TW` world, at
a return as at a stop. Those make the guard the stack's arising condition read from `TW`'s runs,
not a guard beside `TW`. Then the rows GhostEnd proved at its own guard are re-proved at W: `[lam]`,
`[allI]`, and the derivation `not_gfpAt_below` refutes GFP at (`BelowRow`).

`TabOfTWPointwise` is the draft spec's T-ARISE.0: the table read off one `TW` world, with no run
behind it. It is stated so that its first check can be run (DESIGN §5.2); it is not part of the
bundle.

Statements only; no proofs.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwS vwE stratS ReLend TabAtS innerView)

/-! ### The table as `TW`'s run invariant at every depth -/

/-- At the empty stack the table holds of every resource (`tabAtS_nil`). -/
def TabNil : Prop := ∀ ρ : WRes, TabAtS [] [] ρ

/-- Parts and whole (`tabAtS_comp`). -/
def TabParts : Prop :=
  ∀ (σ : LStack) (αs : List Life) (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
    (TabAtS σ αs ρ ↔ TabAtS σ αs ρ₁ ∧ TabAtS σ αs ρ₂)

/-- **Every run keeps the table, at every depth** (`wpG_tabAtS_one` at every stack; [TR] 6.50 at
the innermost lend's `↓α` and at the outermost lend away from the stack's places). A run of W is
`wpG` at the record list with the stack fixed. -/
def TabRuns : Prop :=
  ∀ (σ : LStack) (αs : List Life) (ls : List SRec) (e : Expr) (Q : List SRec → Expr → WProp)
    (ρ : WRes), StackOK σ αs → TabAtS σ αs ρ → wpG (ℍ := ℍ) ls e Q ρ →
    wpG (ℍ := ℍ) ls e (fun ls' t ρ' => TabAtS σ αs ρ' ∧ Q ls' t ρ') ρ

/-- **The start of a lend, at every depth** (`tabAtS_start_one` at every stack): the callback's
resource below the fresh lend, joined to the lend's view, has the table at `e·σ`. -/
def TabStart : Prop :=
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (e : LEnt) (α : Life)
    (d : Bool) (ρ a R : WRes), StackOK σ αs → FutOK δ σ αs 0 [e] [α] ρ → TabAtS σ αs ρ →
    vwE δ e d α ls a → ResU.CompS ρ a R → TabAtS (e :: σ) (α :: αs) R

/-- **A re-lend keeps the table**: a share strictly above the outermost lend, handed the views at a
re-lend, has the table at the re-lend. -/
def TabRelend : Prop :=
  ∀ (δ : LSub) (σ : LStack) (ds : List Bool) (αs αs' : List Life) (ls : List SRec)
    (ρz ρv R : WRes), StackOK σ αs → ReLend αs' αs → stratS αs ρz → vwS δ [] σ ds αs' ls ρv →
    ResU.CompS ρz ρv R → TabAtS σ αs' R

/-- **A future keeps the table**: an insertion below the resource and a hiding. -/
def TabFut : Prop :=
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (k : Nat) (τ : LStack) (αt : List Life)
    (N : Option (UInt32 → Bool)) (ρ : WRes), StackOK σ αs → FutOK δ σ αs k τ αt ρ →
    TabAtS σ αs ρ → TabAtS (futS k τ N σ) (futL k αt αs) ρ

/-! ### The pointwise reading (the draft spec's T-ARISE.0) -/

/-- `ρ`'s borrow cells sit at a place of a stack entry (at a 6.64 entry, the place of one of
`TW`'s records) or at a place no entry lends: the constraint read off `ps` and `σ` alone. -/
def HeldUnderTW (ρ : WRes) (ps : List FrameRec) (σ : LStack) : Prop :=
  ∀ (m : BoCa.Loc) (ψ : CellU BoCa.Loc Val), ρ.get m = some ψ → ψ.kind ≠ Kind.own →
    (∃ e ∈ σ, e.l = m ∧ ∀ u, e.k = .imm u → ∃ r ∈ ps, r.le = m) ∨ m ∉ σ.map LEnt.l

/-- **T-ARISE.0, pointwise**: every part of a tagged `TW` world, with the stack's 6.64 entries among
`TW`'s records, held under the stack, has the stack's table. -/
def TabOfTWPointwise : Prop :=
  ∀ (fρ ρf ρ : WRes) (ps : List FrameRec) (ls : List SRec) (σ : LStack) (αs : List Life),
    TW fρ ps (rsOf ls) → Tagged fρ ps ls → StackOK σ αs →
    (∀ e ∈ σ, ∀ u, e.k = .imm u → ∃ r ∈ ps, r.le = e.l) →
    ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → HeldUnderTW ρ ps σ → TabAtS σ αs ρ

/-! ### The rows at the guard -/

/-- **`[lam]` at W** (`lam_RLa` at the placement's relation). -/
def LamRow (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (M : Expr) (A : VTy) (C : CTy),
    SemS p Δ (⟨A, true⟩ :: Γ) M (.comp C) → SemS p Δ Γ (.val (.lam M)) (.comp (.arr A C))

/-- **`[allI]` at W** (`allI_RLa` at the placement's relation). Its binder is new to `Δ`, the
freshness `allI_RLa`'s added hypotheses come from (`stackFresh_of_fresh`). -/
def AllIRow (p : Placement) : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (x : LifeVar) (b : Lifetime.Life) (M : Expr) (S : VTy) (C : CTy),
    b.mentions x = false → (∀ y u, Δ.find? y = some u → u.mentions x = false) →
    (∀ s ∈ Γ, s.live = true → ¬ VFree x s.ty) → Δ.find? x = none →
    SemS p (Δ.extend x b) (⟨S, false⟩ :: Γ) M (.comp C) →
    SemS p Δ Γ (.val (.lam M)) (.comp (.all x b C))

/-- `Below.lean`'s stack entry: a `mut` lend of the place `0` at the variable `0`, payload `1`. -/
def belowEnt : LEnt := ⟨0, 0, .unit, .mut, fun _ => true⟩

/-- `Below.lean`'s context `x ⊏ ⊤`. -/
abbrev belowCtx : LifeCtx := LifeCtx.empty.extend 0 .top

/-- `Below.lean`'s term `Λ. λn. return (thunk (return n))`. -/
abbrev belowTerm : Expr := .val (.lam (.val (.lam (.val (.lam (.var 1))))))

/-- `Below.lean`'s type `∀'y ⊏ ⊓Δ. Mut 'y 1 ⊸ F (U (F (Mut 'y 1)))`. -/
abbrev belowType : CTy :=
  .all 1 belowCtx.meetOfDom (.arr (.mut (.var 1) .unit) (.ret (.thunk (.ret (.mut (.var 1) .unit)))))

/-- **The judgement GFP is refuted at** (`not_gfpAt_below`), at W. -/
def BelowRow (p : Placement) : Prop := SemS p belowCtx [] belowTerm (.comp belowType)

/-- **The refuted argument is excluded at W** (`below_excluded` at the placement's relation): at
the stack `[x]`, the `⊸` clause asks nothing of the inner view below the stack's lend. -/
def BelowExcluded (p : Placement) : Prop :=
  ∀ (δ : LSub) (C : CTy) (ls : List SRec) (f : Expr) (v : Val) (α αy : Life) (k : BoCa.Loc),
    αy < α → k ≠ belowEnt.l →
    guardW [belowEnt] [α] (cRL p [belowEnt] δ C [α] ls (.app f (.val v))) (innerView k αy)

/-! ### The bundle -/

/-- **Statement 1 at the placement `p`.** -/
def Statement1 (p : Placement) : Prop :=
  TabNil ∧ TabParts ∧ TabRuns (ℍ := ℍ) ∧ TabStart (ℍ := ℍ) ∧ TabRelend (ℍ := ℍ) ∧ TabFut ∧
    LamRow (ℍ := ℍ) p ∧ AllIRow (ℍ := ℍ) p ∧ BelowRow (ℍ := ℍ) p ∧ BelowExcluded (ℍ := ℍ) p

end ProbeD1

end

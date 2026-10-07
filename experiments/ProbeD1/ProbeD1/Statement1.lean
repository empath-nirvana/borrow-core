import ProbeD1.Statement0
import ProbeD1.Arising

/-!
# ProbeD1 — statement 1: the guard as `TW`'s run invariant (OQ-45; DESIGN §5)

W's guard is the stack's table `TabAtS`. Synthesis §11 asks for the guard read from `TW` (T-ARISE.0,
the table read off one `TW` world). The probe states the sound direction instead: the table holds
at every configuration that arises (`ArisesSound`), because every transition of W's semantics
keeps it. Arising is historical: `TW` records no 6.65 lend (OQ-44), so one world cannot say that a
cell was folded after a lend opened, and the pointwise reading is expected to fail at
`innerView`, where the configuration does not arise. `TabOfTWPointwise` is that pointwise reading,
stated so that its first check can be run; it is not part of the bundle.

* **The transitions keep the table**: the empty stack (`TabNil`), a part (`TabParts`), a run's
  update (`TabUpd`, [TR] 6.50; `TabRuns` its `wpG` form), a lend's start (`TabStart`), a handler
  (`TabHide`).
* **The relation's quantified configurations keep it**: a re-lend (`TabRelend`), a future
  (`TabFut`), the resume composite (`TabResume`).
* **The rows GhostEnd proved at its own guard, re-proved at W**: `[lam]`, `[allI]`, and the
  derivation `not_gfpAt_below` refutes GFP at (`BelowRow`), with its witness excluded
  (`BelowExcluded`).

Statements only; no proofs.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwS vwE stratS ReLend TabAtS innerView)

/-! ### The transitions of W's semantics keep the table -/

/-- At the empty stack the table holds of every resource (`tabAtS_nil`). -/
def TabNil : Prop := ∀ ρ : WRes, TabAtS [] [] ρ

/-- Parts and whole (`tabAtS_comp`). -/
def TabParts : Prop :=
  ∀ (σ : LStack) (αs : List Life) (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
    (TabAtS σ αs ρ ↔ TabAtS σ αs ρ₁ ∧ TabAtS σ αs ρ₂)

/-- **A run's update keeps the table** ([TR] 6.50 at the innermost lend's `↓α` and at the outermost
lend away from the stack's places, `tabAt_updV` twice): `↭` from a resource with the table gives
one with the table. -/
def TabUpd : Prop :=
  ∀ (σ : LStack) (αs : List Life) (ρ π : WRes), StackOK σ αs → TabAtS σ αs ρ →
    ResU.UpdV ρ π → TabAtS σ αs π

/-- **Every run keeps the table, at every depth** (`wpG_tabAtS_one` at every stack): `TabUpd` read
through `wpG`'s run-end conjunct. A run of W is `wpG` at the record list with the stack fixed. -/
def TabRuns : Prop :=
  ∀ (σ : LStack) (αs : List Life) (ls : List SRec) (e : Expr) (Q : List SRec → Expr → WProp)
    (ρ : WRes), StackOK σ αs → TabAtS σ αs ρ → wpG (ℍ := ℍ) ls e Q ρ →
    wpG (ℍ := ℍ) ls e (fun ls' t ρ' => TabAtS σ αs ρ' ∧ Q ls' t ρ') ρ

/-- **The start of a lend, at every depth** (`tabAtS_start_one` at every stack): the callback's
resource below the fresh lend, joined to the lend's view, has the table at `e·σ`. -/
def TabStart : Prop :=
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (e : LEnt) (α : Life)
    (d : Bool) (ρ a R : WRes), StackOK σ αs → OwnOK δ σ αs e α ρ → TabAtS σ αs ρ →
    vwE δ e d α ls a → ResU.CompS ρ a R → TabAtS (e :: σ) (α :: αs) R

/-- **A handler keeps the table**: the table does not read the entries' rows. -/
def TabHide : Prop :=
  ∀ (N : UInt32 → Bool) (σ : LStack) (αs : List Life) (ρ : WRes),
    TabAtS σ αs ρ → TabAtS (hideS N σ) αs ρ

/-! ### The relation's quantified configurations keep the table -/

/-- **A re-lend keeps the table**: a share strictly above the outermost lend, handed the views at a
re-lend, has the table at the re-lend. -/
def TabRelend : Prop :=
  ∀ (δ : LSub) (σ : LStack) (ds : List Bool) (αs αs' : List Life) (ls : List SRec)
    (ρz ρv R : WRes), StackOK σ αs → ReLend αs' αs → stratS αs ρz → vwS δ [] σ ds αs' ls ρv →
    ResU.CompS ρz ρv R → TabAtS σ αs' R

/-- **A future keeps the table**: insertions below the resource and hidings, any number. -/
def TabFut : Prop :=
  ∀ (δ : LSub) (σ σ' : LStack) (αs αs' : List Life) (ρ : WRes), StackOK σ αs →
    Fut δ ρ (σ, αs) (σ', αs') → TabAtS σ αs ρ → TabAtS σ' αs' ρ

/-- **The resume composite keeps the table**: the continuation's share, strictly above the
outermost lend of its stack `σi ++ σo`, handed the views of the re-lent inner entries `σi`, joined
to the handler's answer resource, which has the table at the kept part's future `σo`, has the table
at the continuation's stack. It follows from `TabRelend` at `σi ++ σo` (the views are the inner
entries'), `TabParts`, and `TabStart`'s argument at an empty view for the answer's resource; it is
named because the share's rows call their induction hypothesis there. -/
def TabResume : Prop :=
  ∀ (δ : LSub) (σi σo : LStack) (ds : List Bool) (αi αo : List Life) (ls : List SRec)
    (ρz ρv ρa R R' : WRes),
    StackOK (σi ++ σo) (αi ++ αo) → stratS (αi ++ αo) ρz → vwS δ [] σi ds αi ls ρv →
    TabAtS σo αo ρa → ResU.CompS ρz ρv R → ResU.CompS R ρa R' → TabAtS (σi ++ σo) (αi ++ αo) R'

/-! ### The guard is `TW`'s run invariant -/

/-- **Every configuration that arises has the table** (`Arises ⊆ ArisesAt`): the guard is the
stack's arising condition read from `TW`'s runs, not a guard beside `TW`. -/
def ArisesSound : Prop :=
  ∀ c : Cfg, Arises (ℍ := ℍ) c → ArisesAt c.σ c.αs c.ls c.ps c.ρf c.ρ c.fρ

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
freshness `allI_RLa`'s added hypotheses come from: with `StackJ`'s payload scoping, it is new to
the stack's first-kind variables and free in no payload type. -/
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
  TabNil ∧ TabParts ∧ TabUpd ∧ TabRuns (ℍ := ℍ) ∧ TabStart (ℍ := ℍ) ∧ TabHide ∧
    TabRelend (ℍ := ℍ) ∧ TabFut ∧ TabResume (ℍ := ℍ) ∧ ArisesSound (ℍ := ℍ) ∧
    LamRow (ℍ := ℍ) p ∧ AllIRow (ℍ := ℍ) p ∧ BelowRow (ℍ := ℍ) p ∧ BelowExcluded (ℍ := ℍ) p

end ProbeD1

end

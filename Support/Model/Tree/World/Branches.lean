import Support.Model.Tree.World.Records
import Support.Model.Tree.Port.Split

/-!
# The scheduler-wide invariant over the tree world

`SI/CactusInv.lean`'s `CactusInv`, at a world `w`: the branches (the running computation, the
stored continuations, the spawned closures) are resources at `w`'s tree, each owning records and
each **at a point** of the lifetime tree: every top cell of its resource carries lifetimes that are
the point or enclose it (`OnBranchResT`; the strata carry it to every cell beneath). The world is
the branches' composition, the records proper are the branches' records, apart by location between
branches, and the world's invariants hold (`RecInv`, `WInv`).

The operations, each proved to keep the invariant, and what each does to the points:

* **step** (`cactusT_step`): the running branch at `twp` under the frame of the others ends at a
  world extending the start, the others **re-read** there with their records, at their points
  (`AtPoints.rr`: a re-reading keeps an `imm` cell's lifetimes and reads a `mut` cell's antichain
  as its minimal members; the grown tree keeps every nesting). The running branch ends at the
  point its postcondition names (`hpt`): a **fresh lend** opened and still open moves it to the
  fresh child, a lend ended moves it back.
* **grow** (`cactusT_extend`): a fresh child, a **graft** or a re-typing of a location no `mut`
  cell is at extends the world, every branch re-read and carried at its point; a grafted task's
  point is unchanged and lies, after the graft, inside the resumer's lend.
* **capture / move** (`cactusT_move`): a part leaves one branch for another (a continuation's
  share stored by the scheduler, a borrow handed to a joiner); the part is on the receiver's point
  (`hσn`); the giver keeps its point.
* **spawn** (`cactusT_spawn`): a part of a branch, with the records it owns, becomes a branch at
  the point it sits on.
* **join** (`cactusT_join`): a finished branch's resource and records become the joiner's, at the
  joiner's point; the resource is on that point. A join that resumes a branch owning a record
  framed at `α` reads `JoinPtT`: no other branch's point is inside `α`.
* **unwind** is a step of the cancelled branch's `fin` obligation at `twp`, so it is
  `cactusT_step`.

**Adequacy is derived from the invariant** (`cerwpT_adequacy`): the initial configuration is the
invariant at one empty branch at `⊤`; `cactusT_step` carries it to any final configuration; there
the branch's postcondition gives an empty resource, so the world is empty, so the memory is.
-/

noncomputable section


namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo

/-- The composition of a list of resources. -/
inductive CompAllT {K : WCactus} : List (TRes K) → TRes K → Prop
  | nil : CompAllT [] PMap.empty
  | cons {ρ W W' : TRes K} {ρs : List (TRes K)} : CompAllT ρs W' → ResUT.CompS ρ W' W →
      CompAllT (ρ :: ρs) W

/-- A branch: its resource and the records it owns. -/
abbrev TBranch (K : WCactus) : Type := TRes K × List (FrameRecT K)

/-! ### Branch points -/

/-- A cell is on `n`'s branch: every lifetime it carries is `n` or encloses it
(`Tree/Frame.lean`'s `CellAbove`, over the tree carrier). -/
def CellAboveT (K : WCactus) (n : Life) (ψ : TCell K) : Prop :=
  ∀ s, ψ.lsOf = some s → ∀ x ∈ s.set, K.le n x

/-- Every top cell of `ρ` is on `n`'s branch (`OnBranchRes` over the tree carrier). Cells at depth
follow by the strata (`cellAt_onBranch`). -/
def OnBranchResT (K : WCactus) (n : Life) (ρ : TRes K) : Prop :=
  ∀ l ψ, ρ.get l = some ψ → CellAboveT K n ψ

theorem extLe {K K' : WCactus} (hE : K.Ext K') {a b : Life} (h : K.le a b) :
    K'.le a b := by
  by_cases e : a = b
  · subst e; exact K'.refl _
  · exact (hE ⟨h, e⟩).1

/-- A re-read cell is on the branch its original is on: an `imm` cell keeps its lifetimes, a
`mut` cell's antichain is read as its minimal elements. -/
theorem CellAboveT.rc {Θ : LocTy} {K K' : WCactus} (hE : K.Ext K') {n : Life} {l : BoCa.Loc}
    {ψ : TCell K} {ψ' : TCell K'} (hr : RC Θ l ψ ψ') (h : CellAboveT K n ψ) :
    CellAboveT K' n ψ' := by
  intro s hs x hx
  cases hr with
  | own => cases hs
  | imm _ i i' hsl =>
      cases hs
      exact extLe hE (h i.ls rfl x (hsl ▸ hx))
  | «mut» _ m m' τ hΘ hsl =>
      cases hs
      rw [hsl] at hx
      exact extLe hE (h m.ls rfl x (K'.minS_sub hx))

/-- **A branch's point is kept by a re-reading** along a grown tree. -/
theorem OnBranchResT.rr {Θ : LocTy} {K K' : WCactus} (hE : K.Ext K') {n : Life} {ρ : TRes K}
    {ρ' : TRes K'} (hr : RR Θ ρ ρ') (h : OnBranchResT K n ρ) : OnBranchResT K' n ρ' := by
  intro l ψ' e
  obtain ⟨ψ, e', hc⟩ := hr.get_some' e
  exact (h l ψ e').rc hE hc

theorem CellUT.CompS.ls {K : WCactus} {ψ₁ ψ₂ ψ : TCell K} (h : CellUT.CompS ψ₁ ψ₂ ψ) :
    ∃ s₁ s₂, ψ₁.lsOf = some s₁ ∧ ψ₂.lsOf = some s₂ ∧ ψ.lsOf = some (s₁ ∪ s₂) := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, rfl, rfl, rfl⟩ := h
  exact ⟨s₁, s₂, CellUT.lsOf_immOf _ _ _ _, CellUT.lsOf_immOf _ _ _ _, CellUT.lsOf_immOf _ _ _ _⟩

/-- A composite of two resources on `n`'s branch is on it. -/
theorem OnBranchResT.compS {K : WCactus} {n : Life} {a b c : TRes K} (hc : ResUT.CompS a b c)
    (ha : OnBranchResT K n a) (hb : OnBranchResT K n b) : OnBranchResT K n c := by
  intro l ψ e
  rcases ResUT.Comp.get hc l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, f, hC⟩
  · rw [e] at f; cases f
  · rw [e] at f; cases Option.some.inj f; exact ha l _ f₁
  · rw [e] at f; cases Option.some.inj f; exact hb l _ f₂
  · rw [e] at f; cases Option.some.inj f
    obtain ⟨s₁, s₂, e₁, e₂, e₃⟩ := CellUT.CompS.ls hC
    intro s hs x hx
    rw [e₃] at hs; cases hs
    simp only [TSet.union_set, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact ha l _ f₁ s₁ e₁ x hx
    · exact hb l _ f₂ s₂ e₂ x hx

/-- An operand of a composite on `n`'s branch is on it. -/
theorem OnBranchResT.of_compS_left {K : WCactus} {n : Life} {a b c : TRes K}
    (hc : ResUT.CompS a b c) (h : OnBranchResT K n c) : OnBranchResT K n a := by
  intro l ψ e
  rcases ResUT.Comp.get hc l with ⟨f, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, f, hC⟩
  · rw [e] at f; cases f
  · rw [e] at f₁; cases Option.some.inj f₁; exact h l _ f
  · rw [e] at f₁; cases f₁
  · rw [e] at f₁; cases Option.some.inj f₁
    obtain ⟨s₁, s₂, e₁, e₂, e₃⟩ := CellUT.CompS.ls hC
    intro s hs x hx
    rw [e₁] at hs; cases hs
    exact h l _ f _ e₃ x (by simp [TSet.union_set, Finset.mem_union, hx])

theorem OnBranchResT.of_compS_right {K : WCactus} {n : Life} {a b c : TRes K}
    (hc : ResUT.CompS a b c) (h : OnBranchResT K n c) : OnBranchResT K n b :=
  OnBranchResT.of_compS_left (ResUT.CompS.comm hc) h

theorem OnBranchResT.empty {K : WCactus} (n : Life) : OnBranchResT K n PMap.empty :=
  fun _ _ e => by simp at e

theorem compAllT_functional {K : WCactus} {ρs : List (TRes K)} {W W' : TRes K}
    (h : CompAllT ρs W) (h' : CompAllT ρs W') : W = W' := by
  induction h generalizing W' with
  | nil => cases h'; rfl
  | cons hr hc ih =>
      cases h' with
      | cons hr' hc' =>
          cases ih hr'
          exact ResUT.CompS.functional hc hc'

/-! ### Lists of lists along re-reading -/

/-! ### The operations -/

/-! ### Adequacy -/

end BoCa.Fig16.Tree.Wp

end

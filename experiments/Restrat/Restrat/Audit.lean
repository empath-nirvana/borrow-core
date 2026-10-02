import Paper
import Support
import Core

/-!
# Restrat — the audit of lifetime arithmetic

A scan of every constant declared in a module of `Paper`, `Support` or `Core`, for the ways a
semantic lifetime (`BoCa.Fig16.Life`, which is `ℕᵒᵈ`) can be *computed* rather than compared:
the successor `Life.down` (`↓α ≜ α + 1`, [TR] p. 5), a crossing `OrderDual.toDual` /
`OrderDual.ofDual` (how `+ 1` on a lifetime is written), and an algebraic instance on `αᵒᵈ` (how
`+`, `-` or a numeral at `ℕᵒᵈ` elaborates).  The order and lattice instances (`<`, `≤`, `⊓`, `⊔`,
`⊤`) are comparisons, which every strictly monotone map preserves, and are not reported.

The scan reads each constant's used constants (`Expr.getUsedConstants`).  `auditDefsM` lists the
definitions (their bodies are semantic objects); `auditThmTypesM` the theorems whose *statement*
mentions `↓`.  The `run_meta` below pins both lists: the build fails if either changes.

**Result.**  No definition of the relation, the model, the typed world or `Core` computes a
lifetime.  `↓` is used only as the witness of an existential ("a lifetime strictly below `γ`"),
or in a hypothesis `ρ ∈ Res_{↓α}`, which is the non-strict `α ⊑ @ψ` (`inStratum_down_iff`).
In particular no definition relates an outer lifetime to an inner one by `↓`.
-/

open Lean Meta Elab Command

namespace Restrat.Audit

/-- The modules the audit covers. -/
def inScope (m : Name) : Bool :=
  match m.components.head? with
  | some r => r == `Paper || r == `Support || r == `Core
  | none => false

/-- Is `n` a constant that computes a lifetime rather than comparing two: the successor
`Life.down`, a crossing `OrderDual.toDual`/`OrderDual.ofDual`, or an algebraic instance on
`αᵒᵈ` (how `+`, `-`, `*` or a numeral at `ℕᵒᵈ` would elaborate)?  The order instances on `αᵒᵈ`
(`<`, `≤`, `⊓`, `⊔`, `⊤`, …) are comparisons and lattice operations, which every monotone
injection preserves, and are not reported. -/
def isArith (n : Name) : Bool :=
  n == ``BoCa.Fig16.Life.down || n == ``OrderDual.toDual || n == ``OrderDual.ofDual ||
  (n.getRoot == `OrderDual &&
    ["Add", "Sub", "Mul", "One", "Zero", "OfNat", "NatCast", "Succ", "Pred", "Monoid",
      "Semiring", "Ring", "Group", "SMul", "Pow", "Div"].any fun k =>
        (n.toString.splitOn k).length > 1)

/-- The arithmetic constants `e` uses, read off `Expr.getUsedConstants`. -/
def arithConsts (e : Expr) : Array Name :=
  (e.getUsedConstants.filter isArith).toList.eraseDups.toArray

def mentionsArith (e : Expr) : Bool := !(arithConsts e).isEmpty

def mentionsDown (e : Expr) : Bool :=
  e.getUsedConstants.contains ``BoCa.Fig16.Life.down

/-- Definitions (not theorems) in scope whose body or type mentions lifetime arithmetic, with the
constants found. -/
def auditDefsM : MetaM (Array (Name × Array Name)) := do
  let env ← getEnv
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless inScope m do continue
    let hits := match ci with
      | .defnInfo d => arithConsts d.value ++ arithConsts d.type
      | .opaqueInfo d => arithConsts d.value ++ arithConsts d.type
      | .inductInfo d => arithConsts d.type
      | .ctorInfo d => arithConsts d.type
      | _ => #[]
    unless hits.isEmpty do out := out.push (n, hits)
  return out.qsort (·.1.toString < ·.1.toString)

/-- Theorems in scope whose statement mentions `Life.down`. -/
def auditThmTypesM : MetaM (Array Name) := do
  let env ← getEnv
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless inScope m do continue
    if let .thmInfo d := ci then
      if mentionsDown d.type then out := out.push n
  return out.qsort (·.toString < ·.toString)

end Restrat.Audit

namespace Restrat.Audit

/-- Every definition of `Paper`, `Support` and `Core` that computes a lifetime.

* `Life.down` is `↓` itself ([TR] p. 5).
* `Cell` is the well-founded construction of the strata ([TR] p. 4 row 3); `ofDual` is its
  termination measure, not a lifetime it builds.
* `Core.wpG_I_frameList._f` and `Core.wpG_M_frameList._f` are the structural-recursion
  auxiliaries Lean generates for two *theorems* (`Core/SliceFrames.lean`); `↓γ` there is the
  witness of an existential (a lifetime strictly below `γ`).
* The rest are worked examples and refutation witnesses at numeral lifetimes. -/
def expectedDefs : List String :=
  ["BoCa.Fig16.Cell", "BoCa.Fig16.Life.down",
   "BoCa.Fig16.LogRel.Core.wpG_I_frameList._f", "BoCa.Fig16.LogRel.Core.wpG_M_frameList._f",
   "BoCa.Fig16.LogRel.ViewWitness.ρ₁", "BoCa.Fig16.LogRel.ViewWitness.ρ₂",
   "BoCa.Fig16.SplitExample.sA", "BoCa.Fig16.SplitExample.sB", "BoCa.Fig16.inner",
   "_private.Paper.LiteralReadings.S6_6_ReborrowingEntailments.0.BoCa.Fig16.RebExample.mutCell",
   "_private.Paper.LiteralReadings.S6_6_ReborrowingEntailments.0.BoCa.Fig16.RebExample.mutInv"]

/-- Every theorem whose statement mentions `↓`.  Each is `↓α ⊏ α` ([TR] 6.63), an inequality
`↓a ⊏ b` read as `a ⊑ b`, or a hypothesis `ρ ∈ Res_{↓α}`, which is `Restrat.inStratum_down_iff`'s
non-strict `α ⊑ @ψ` at every borrow cell. -/
def expectedThms : List String :=
  ["BoCa.Fig16.AgW.inStratum_at", "BoCa.Fig16.CellU.not_at_lt_of_inStratum_down",
   "BoCa.Fig16.CellU.wit_inStratum_of_down", "BoCa.Fig16.ExW.inStratum_at",
   "BoCa.Fig16.Life.down_sqsubset", "BoCa.Fig16.Life.le_of_down_lt",
   "BoCa.Fig16.Life.not_lt_of_down_lt", "BoCa.Fig16.ResU.Sub.inStratum",
   "BoCa.Fig16.ResU.flat_inStratum_at", "BoCa.Fig16.ResU.reb_inStratum_down",
   "BoCa.Fig16.ResU.updV_outlives_at", "TR.lemma_6_63"]

end Restrat.Audit

open Restrat.Audit in
run_meta do
  let ds := (← auditDefsM).map (·.1.toString)
  unless ds.qsort (· < ·) == expectedDefs.toArray.qsort (· < ·) do
    throwError m!"the definitions computing a lifetime changed: {ds}"
  let ts := (← auditThmTypesM).map (·.toString)
  unless ts.qsort (· < ·) == expectedThms.toArray.qsort (· < ·) do
    throwError m!"the theorems stating `↓` changed: {ts}"

namespace Restrat
open BoCa.Fig16

/-- `ψ ∈ Cell_{↓α}` is the non-strict `α ⊑ @ψ` at a borrow cell: the hypotheses that state `↓`
restate without it. -/
theorem inStratum_down_iff {Loc Val : Type} (α : Life) (ψ : CellU Loc Val) :
    ψ.InStratum (↓α) ↔ (ψ.kind = Kind.own ∨ α ≤ ψ.at) := by
  have key : ∀ x : Life, (↓α) < x ↔ α ≤ x := fun x => by
    show OrderDual.ofDual x < OrderDual.ofDual α + 1 ↔ OrderDual.ofDual x ≤ OrderDual.ofDual α
    omega
  cases ψ with
  | own v => exact ⟨fun _ => Or.inl rfl, fun _ => trivial⟩
  | imm i =>
      refine (key _).trans ⟨Or.inr, fun h => h.resolve_left (by simp [CellU.kind])⟩
  | «mut» m =>
      refine (key _).trans ⟨Or.inr, fun h => h.resolve_left (by simp [CellU.kind])⟩

theorem resInStratum_down_iff {Loc Val : Type} (α : Life) (ρ : ResU Loc Val) :
    ρ.InStratum (↓α) ↔ ∀ l ψ, ρ.get l = some ψ → ψ.kind = Kind.own ∨ α ≤ ψ.at :=
  forall_congr' fun _ => forall_congr' fun ψ => imp_congr_right fun _ => inStratum_down_iff α ψ

end Restrat

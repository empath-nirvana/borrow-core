import Targets.I.Interface
import Targets.I.Device
import GhostEnd.StackStep

/-!
# ProbeD1 — W's index, its order, and the arising guard (DESIGN §2)

W's index is Targets' `Idx` at the stack `Stk := LStack × List Life`: GhostEnd's lend entries and
their current lifetimes, both innermost first, beside the record list.

* **Futures of the stack.** A value or a continuation may be used deeper than where it was made:
  inside new lends and inside new handlers. A new lend is an entry inserted in the stack: at the
  front when the value moves inside it, at depth `k` when a continuation that ghost-ended its `k`
  innermost entries is resumed inside a lend the resumer opened (between lenders). A new handler
  hides its names from the stack's rows outside it. `FutOK` is the freshness an inserted entry
  meets (6.112's `И`: below the holder's resource; nesting order; new variables and places), and
  `futS`/`futL` the stack and the lifetimes it gives. An inserted entry's variable is drawn from
  the names no program binds (`NsVar`), so it never collides with a binder of the code that runs
  at the future: lifetime variables are names, and the stack binds its entries' variables over
  the reading substitution (`extS`).
* **Hiding.** GhostEnd's stop depth reads each entry's lender row (`depth`). Inside a handler of
  `n` no stop of `n` reaches the lends outside the handler, so the handled body is read at
  `hideS (· == n) σ`.
* **The guard** is the stack's table (`TabAtS`), the run invariant of `TW` at a stack
  (DESIGN statement 1). At the empty stack it holds of every resource.

These are definitions only.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS TabAtS)

/-- W's lend stack: the entries and their current lifetimes, innermost first. -/
abbrev Stk := LStack × List Life

/-- W's index: the record list and the lend stack. -/
abbrev Ix := Targets.Idx Stk

/-- A stack in shape: one lifetime per entry, in nesting order, the variables distinct. -/
def StackOK (σ : LStack) (αs : List Life) : Prop :=
  αs.length = σ.length ∧ List.IsChain (· < ·) αs ∧ (σ.map LEnt.x).Nodup

/-- Hide the names `N` from every entry's row. -/
def hideS (N : UInt32 → Bool) (σ : LStack) : LStack :=
  σ.map fun e => { e with cross := fun n => e.cross n && !N n }

/-- The stack a future gives: the fresh entries `τ` placed at depth `k` (inside the outer part
`σ.drop k`, outside the inner part `σ.take k`), after the names `N` are hidden from the outer part.
At `k = 0` it is a push inside the whole stack. -/
def futS (k : Nat) (τ : LStack) (N : Option (UInt32 → Bool)) (σ : LStack) : LStack :=
  σ.take k ++ τ ++ match N with
    | none => σ.drop k
    | some N => hideS N (σ.drop k)

/-- The lifetimes a future gives, placed the same way. -/
def futL (k : Nat) (αt αs : List Life) : List Life := αs.take k ++ αt ++ αs.drop k

/-- **A fresh insertion.** The entries `τ` at the lifetimes `αt`, placed at depth `k ≤ |σ|`, every
one below the holder's resource `ρ` (6.112's `И`), the whole vector in nesting order (so the inner
part is below `αt`, which is below the outer part); `τ`'s variables new to the stack and to the
reading substitution `extS δ σ αs`, and distinct; `τ`'s places new to the stack. -/
structure FutOK (δ : LSub) (σ : LStack) (αs : List Life) (k : Nat) (τ : LStack)
    (αt : List Life) (ρ : WRes) : Prop where
  len : αt.length = τ.length
  depth_le : k ≤ σ.length
  chain : List.IsChain (· < ·) (futL k αt αs)
  below : ∀ a ∈ αt, ρ.InStratum a
  vars_stack : ∀ e ∈ τ, e.x ∉ σ.map LEnt.x
  vars_sub : ∀ e ∈ τ, (extS δ σ αs).find? e.x = none
  nodup : (τ.map LEnt.x).Nodup
  places : ∀ e ∈ τ, e.l ∉ σ.map LEnt.l

/-- The base of the names a future gives its inserted entries. A program's binders are below it, so
an inserted entry's variable is never one the program binds (`BindersLow`, `Sem.lean`). -/
def nsBase : LifeVar := 2 ^ 32

/-- A variable a future may give an inserted entry. -/
def NsVar (x : LifeVar) : Prop := nsBase ≤ x

/-- Every inserted entry's variable is a future's. -/
def NsFresh (τ : LStack) : Prop := ∀ e ∈ τ, NsVar e.x

/-- The futures a clause quantifies over: every fresh insertion and hiding when `fut`, and only
the stack itself otherwise. -/
def FutQ (fut : Bool) (δ : LSub) (σ : LStack) (αs : List Life) (k : Nat) (τ : LStack)
    (αt : List Life) (N : Option (UInt32 → Bool)) (ρ : WRes) : Prop :=
  if fut then FutOK δ σ αs k τ αt ρ ∧ NsFresh τ else k = 0 ∧ τ = [] ∧ αt = [] ∧ N = none

/-- **W's order** at a resource, read at `δ`: the records by `Ext`; the stack by a fresh insertion
and a hiding. The re-lend of the stack's own lifetimes is not part of it: the `U` clause and the
share hand the dropped views back at a re-lend, and an insertion below the outer part needs that
re-lend to make room. -/
def OrdW (δ : LSub) (i i' : Ix) (ρ : WRes) : Prop :=
  Ext i.1 i'.1 ρ ∧ ∃ k τ αt N, FutOK δ i.2.1 i.2.2 k τ αt ρ ∧ NsFresh τ ∧
    i'.2.1 = futS k τ N i.2.1 ∧ i'.2.2 = futL k αt i.2.2

/-- **The guard**: `P` asked only of a resource consistent with the stack's table. -/
def guardW (σ : LStack) (αs : List Life) (P : WProp) : WProp := fun ρ => TabAtS σ αs ρ → P ρ

mutual
/-- The lifetime variables a value type binds, at every depth. -/
def VTy.binders : VTy → List LifeVar
  | .tensor A B => VTy.binders A ++ VTy.binders B
  | .sum A B => VTy.binders A ++ VTy.binders B
  | .thunk C => CTy.binders C
  | .ref A => VTy.binders A
  | .bang A => VTy.binders A
  | .fam A => VTy.binders A
  | .mu A => VTy.binders A
  | .imm _ A => VTy.binders A
  | .mut _ A => VTy.binders A
  | .box _ A => VTy.binders A
  | .unit | .zero | .unk | .int _ | .opq _ | .tvar _ => []
/-- The lifetime variables a computation type binds, at every depth. -/
def CTy.binders : CTy → List LifeVar
  | .ret A => VTy.binders A
  | .arr A C => VTy.binders A ++ CTy.binders C
  | .amp C D => CTy.binders C ++ CTy.binders D
  | .top => []
  | .all y _ C => y :: CTy.binders C
  | .nu C => CTy.binders C
  | .eff _ _ _ A B C => VTy.binders A ++ VTy.binders B ++ CTy.binders C
end

/-- A pushed entry's variable is not read by the type: neither free in it nor bound in it. -/
def VarsAvoid (C : CTy) (τ : LStack) : Prop :=
  ∀ e ∈ τ, ¬ CFree e.x C ∧ e.x ∉ CTy.binders C

end ProbeD1

end

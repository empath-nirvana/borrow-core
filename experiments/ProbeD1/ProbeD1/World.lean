import Targets.I.Interface
import Targets.I.Device
import GhostEnd.StackStep

/-!
# ProbeD1 — W's index, its order, and the arising guard (DESIGN §2)

W's index is Targets' `Idx` at the stack `Stk := LStack × List Life`: GhostEnd's lend entries and
their current lifetimes, both innermost first, beside the record list.

* **Futures of the stack.** A value or a continuation may be used deeper than where it was made:
  inside new lends and inside new handlers. One step of a future (`FutStep`) inserts a block of
  fresh entries at one depth and hides names from the part outside it: at the front when a value
  moves inside a new lend, at depth `k` when a continuation that ghost-ended its `k` innermost
  entries is resumed inside a lend the resumer opened (between lenders). `FutOK` is the freshness
  a step's entries meet (6.112's `И`: below the holder's resource; nesting order; new variables
  and places; payload types read by the new stack's substitution). A **future** (`Fut`) is
  finitely many steps, so a future of a future is a future by construction: the composite is an
  order-preserving interleaving of the stack with fresh entries, each kept entry's row reduced by
  hiding sets that grow outward.
* **The own lend** (`OwnPush`): the entry a callback's lend pushes, named by its type's outermost
  `∀`, at a lifetime meeting the bound. It is that binder's instance read as the lend the instance
  names, so it is relative to the type, and a clause makes it after a future, never before one.
  Its push is the one-step future at depth `0` when the binder is new to the reading substitution
  (`ownPush_futStep`, `Own.lean`), so a context is carried across it by `MonoG`'s instance
  there (`MonoOwnG`, statement 0).
* **Names.** A step's inserted variables are any that are new to the stack and to the reading
  substitution (`FutOK.vars_stack`, `FutOK.vars_sub`); the clause that quantifies over the future
  asks its own type to avoid them, free and bound (`FutAvoids`). They are not restricted to the
  names no program binds (`NsVar`), so that the own push, named by a program binder, is a future
  (DESIGN §13 step 2). The cost: `BindersLow` does not keep an inserted variable off the binders of
  the code that runs at the future, and `StackJ`'s second kind admits only `NsVar` entries
  (DESIGN §2.2, *Names*).
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

/-- The stack one step of a future gives: the fresh entries `τ` placed at depth `k` (inside the
outer part `σ.drop k`, outside the inner part `σ.take k`), after the names `N` are hidden from the
outer part. At `k = 0` it is a push inside the whole stack. -/
def futS (k : Nat) (τ : LStack) (N : Option (UInt32 → Bool)) (σ : LStack) : LStack :=
  σ.take k ++ τ ++ match N with
    | none => σ.drop k
    | some N => hideS N (σ.drop k)

/-- The lifetimes one step gives, placed the same way. -/
def futL (k : Nat) (αt αs : List Life) : List Life := αs.take k ++ αt ++ αs.drop k

/-- **The freshness of one step.** The entries `τ` at the lifetimes `αt`, placed at depth
`k ≤ |σ|`, every one below the holder's resource `ρ` (6.112's `И`), the whole vector in nesting
order (so the inner part is below `αt`, which is below the outer part); `τ`'s variables new to the
stack and to the reading substitution `extS δ σ αs`, and distinct; `τ`'s places new to the stack;
every variable free in a payload type of `τ` read by the new stack's substitution. -/
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
  pay : ∀ e ∈ τ, ∀ y, VFree y e.T →
    (extS δ (σ.take k ++ τ ++ σ.drop k) (futL k αt αs)).find? y ≠ none

/-- The base of the names no program binds (`BindersLow`, `Sem.lean`). `StackJ`'s second kind
admits a future's entry named by one of them. -/
def nsBase : LifeVar := 2 ^ 32

/-- A name no program binds. -/
def NsVar (x : LifeVar) : Prop := nsBase ≤ x

/-- **One step of a future** at the holder's resource `ρ`, read at `δ`: a fresh insertion at one
depth and a hiding of the part outside it. The inserted variables are any new to the stack and to
the reading substitution; the clause quantifying over the future asks its type to avoid them
(`FutAvoids`). -/
def FutStep (δ : LSub) (ρ : WRes) (s s' : Stk) : Prop :=
  ∃ (k : Nat) (τ : LStack) (αt : List Life) (N : Option (UInt32 → Bool)),
    FutOK δ s.1 s.2 k τ αt ρ ∧ s'.1 = futS k τ N s.1 ∧ s'.2 = futL k αt s.2

/-- **A future of the stack**: finitely many steps. Reflexive and transitive by construction; the
stack it gives is an order-preserving interleaving of `s.1` with fresh entries, each kept entry's
row reduced by hiding sets that grow outward. -/
def Fut (δ : LSub) (ρ : WRes) : Stk → Stk → Prop := Relation.ReflTransGen (FutStep δ ρ)

/-- **The futures a clause quantifies over**: every future when `fut`, the stack itself
otherwise. -/
def FutQ (fut : Bool) (δ : LSub) (ρ : WRes) (s s' : Stk) : Prop :=
  if fut then Fut δ ρ s s' else s' = s

/-- The record extensions a binder clause quantifies over: every `Ext`-future when `fut`, the list
itself otherwise. -/
def ExtQ (fut : Bool) (ls ls' : List SRec) (ρ : WRes) : Prop :=
  if fut then Ext ls ls' ρ else ls' = ls

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

/-- **The entries a future inserted are not read by the computation type `C`**: an entry of `σ'`
whose variable `σ` does not have is neither free nor bound in `C`. -/
def FutAvoids (C : CTy) (σ σ' : LStack) : Prop :=
  ∀ e ∈ σ', e.x ∉ σ.map LEnt.x → ¬ CFree e.x C ∧ e.x ∉ CTy.binders C

/-- The same at a value type. -/
def FutAvoidsV (A : VTy) (σ σ' : LStack) : Prop :=
  ∀ e ∈ σ', e.x ∉ σ.map LEnt.x → ¬ VFree e.x A ∧ e.x ∉ VTy.binders A

/-- **The freshness of a callback's own lend**: the entry `e` at the lifetime `a`, below the
innermost lend and below the holder's resource `ρ` (6.112's `И`), its variable and place new to
the stack, every variable free in its payload type read by the extended stack's substitution. The
variable is the type's binder, which the extended substitution overrides, so nothing is asked of
the reading substitution at it. -/
structure OwnOK (δ : LSub) (σ : LStack) (αs : List Life) (e : LEnt) (a : Life) (ρ : WRes) :
    Prop where
  chain : List.IsChain (· < ·) (a :: αs)
  below : ρ.InStratum a
  var : e.x ∉ σ.map LEnt.x
  place : e.l ∉ σ.map LEnt.l
  pay : ∀ y, VFree y e.T → (extS δ (e :: σ) (a :: αs)).find? y ≠ none

/-- **The own lend at the type `C`**, pushed on the stack `s`: when `C` is `∀'x ⊏ c. C'`, an entry
named `x` (bound nowhere in `C'`) meeting `OwnOK`, at a lifetime meeting the bound. Its variable is
the type's binder. When the binder is new to the reading substitution the push is the one-step
future at depth `0` (`ownPush_futStep`), which the type's own clause does not quantify over
(`FutAvoids` asks the type's binders avoided). -/
def OwnPush (δ : LSub) (C : CTy) (ρ : WRes) (s : Stk) (e : LEnt) (a : Life) : Prop :=
  ∃ (x : LifeVar) (c : Lifetime.Life) (C' : CTy), C = .all x c C' ∧ e.x = x ∧
    x ∉ CTy.binders C' ∧ OwnOK δ s.1 s.2 e a ρ ∧ LtLife (extS δ s.1 s.2) c a

/-- **W's order** at a resource, read at `δ`: the records by `Ext`, the stack by a future. The
re-lend of the stack's own lifetimes is not part of it: the `U` clause and the share hand the
dropped views back at a re-lend, and an insertion below the outer part needs that re-lend to make
room. -/
def OrdW (δ : LSub) (i i' : Ix) (ρ : WRes) : Prop :=
  Ext i.1 i'.1 ρ ∧ Fut δ ρ i.2 i'.2

/-- **The guard**: `P` asked only of a resource consistent with the stack's table. -/
def guardW (σ : LStack) (αs : List Life) (P : WProp) : WProp := fun ρ => TabAtS σ αs ρ → P ρ

end ProbeD1

end

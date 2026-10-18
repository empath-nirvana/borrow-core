import Frontend.Check.Checker

/-!
# Frontend — Elab — the sugar's inference nodes  `[#54, docs/typed-elaboration.md §1.1]`

What the sugar's own inference (`Frontend.Elab.inferV`, `inferC`; `TCx`, `Frontend/Elab/Meta.lean`)
returns for a term: one node per node of the term, each recording

* its span;
* its type, a value or computation type in the checker's own types (`CVTy`, `CCTy`), or `none`
  where it is not known;
* the variables it binds, each with its identity, its type and its class (SPEC §12);
* its effect: `div` when it is a computation that returns a loop (SPEC §14).

A node keeps its source node (`Head`). The sugar reads the root's type. A checked program's types
are the checker's typed term's (`Frontend/Check/TExpr.lean`), not these.
-/

namespace Frontend.Elab
open Frontend.Check

/-- A node's type. -/
inductive Ty where
  | val (A : CVTy)
  | comp (C : CCTy)
  | none
  deriving Inhabited

def Ty.known : Ty → Bool
  | .none => false
  | _ => true

/-- SPEC §12's three classes of value type: persistent (copied and dropped freely), with a
destructor (dropped by the checker), and strictly linear (no destructor: it must be consumed or
handed back). -/
inductive Class where
  | persistent
  | dtor
  | linear
  deriving DecidableEq, Repr, Inhabited

def Class.of (A : CVTy) : Class :=
  if A.persistent then .persistent else if hasDtorB A then .dtor else .linear

def Class.name : Class → String
  | .persistent => "persistent"
  | .dtor => "destructor"
  | .linear => "linear"

/-- A variable a node binds: its name, identity, type and class. -/
structure Binder where
  name : String
  id : Nat
  ty : Option CVTy
  deriving Inhabited

def Binder.cls (b : Binder) : Option Class := b.ty.map Class.of

/-- A computation's effect (SPEC §14). -/
inductive Effect where
  | total
  | div
  deriving DecidableEq, Inhabited

/-- `F (U (loop B R))`: a computation that returns a loop. -/
def returnsLoop : CCTy → Bool
  | .ret (.thunk (.nu (.amp (.ret (.sum _ (.tvar 0))) (.ret _)))) => true
  | _ => false

def Ty.effect : Ty → Effect
  | .comp C => if returnsLoop C then .div else .total
  | _ => .total

/-- A source node. -/
inductive Head where
  | val (v : Val)
  | comp (M : Comp)

instance : Inhabited Head := ⟨.comp (.top Span.none)⟩

def Head.span : Head → Span
  | .val v => v.span
  | .comp M => M.span

/-- An inference node. -/
inductive TNode where
  | mk (head : Head) (ty : Ty) (binders : List Binder) (kids : List TNode)

instance : Inhabited TNode := ⟨.mk default .none [] []⟩

def TNode.head : TNode → Head | .mk h _ _ _ => h
def TNode.ty : TNode → Ty | .mk _ t _ _ => t
def TNode.binders : TNode → List Binder | .mk _ _ bs _ => bs
def TNode.kids : TNode → List TNode | .mk _ _ _ ks => ks
def TNode.span (t : TNode) : Span := t.head.span
def TNode.effect (t : TNode) : Effect := t.ty.effect

end Frontend.Elab

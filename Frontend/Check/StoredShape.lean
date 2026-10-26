import Frontend.Check.Decide

/-!
# Frontend — Check — the record of a stored clause's `StoredAtX` derivation  `[spec §54]`

At `[handle]` and `[handle-boxed]` the checker decides, for each operation whose clause it
classifies `stored`, whether the clause is in the `StoredAtX` grammar (`storedAtXB`,
`Frontend/Check/StoredAtX.lean`), and records the derivation it found on the node's `TInfo`
(`TInfo.sshape`): the codata type `P = νX. C` the clause's answer `R` is shaped by, the template
`Rx` with `R = Rx[U P/X]`, and, for each ν-introduction of the clause, where it is, what it
captures besides `κ` and the clauses' context `Env_N`, and the production of each of its
observations. The record is data the rewriter reads; `storedShapes_sound` states that a record the
checker writes is a derivation of the grammar at the clause the node holds.

The record is defined here, before the typed term, because `TInfo` is a field of every node.
-/

namespace BoCa.Fig16.LogRel.Core.Check
open BoCa BoCa.Fig16.LogRel.Core

/-- The production an observation of a ν-introduction of a stored clause is in (`StoredAtX`):
`κ`-free; the resume `(force κ).1 W` in tail position (`tail`) or bound, `to t. N[t]`; the
close `(force κ).2`. -/
inductive SObs where
  | free
  | resume (tail : Bool)
  | close
  deriving DecidableEq, Repr, Inhabited

/-- A ν-introduction `[boxed[d]] thunkv nu_in T` of a stored clause: the children's indices
(`TExpr.children`) from the clause's body to it; the lifetime it is boxed at, when it is; the
slots it uses that are bound inside the clause, besides `κ` (its captures: `x` and the clause's
own bindings, as indices at the introduction), and how many of the clauses' context `Env_N` it
uses; and the production of each observation of its tree `T`, in the tree's order. -/
structure SIntro where
  path : List Nat
  boxed : Option Lifetime.Life
  caps : List Nat
  env : Nat
  obs : List SObs
  deriving DecidableEq, Repr, Inhabited

/-- **The record of a stored clause's `StoredAtX` derivation**: the body `C` of the codata type
`P = νX. C`; the template `Rx` of the clause's answer, `R = Rx[U P/X]`; whether the answer is
machine-shaped (`Rx` is `X`, or `X` boxed: the answer is the introduction itself), else
observation-shaped (`Rx` is an observation leaf of `C`); and the clause's ν-introductions. -/
structure SShape where
  C : CTy
  Rx : VTy
  machine : Bool
  intros : List SIntro
  deriving DecidableEq

instance : Inhabited SShape := ⟨⟨.top, .unit, false, []⟩⟩

end BoCa.Fig16.LogRel.Core.Check

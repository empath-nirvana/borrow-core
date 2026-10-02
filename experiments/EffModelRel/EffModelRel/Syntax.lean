/-!
# EffModelRel — syntax

An intrinsically typed call-by-push-value calculus: the phase A model of `experiments/EffModel`
with names replaced by de Bruijn indices and typing built into the terms. A term is indexed by
its instance context `Ψ` (the instances it may name), its value context `Γ` and its type.

What the terms carry is what the denotation needs. The rest of phase A's judgement (grades,
independence, rows, T1, scope) is a predicate over these terms (`Moded.lean`), so a law proved
here holds for every term of the larger calculus, moded or not.

- **Ground types** `G` are the types of operation arguments and answers and of capability
  states. Phase A's signatures use only these.
- **Effects** come from a signature `Sig`. An effect has resuming operations `O e` (with a
  continuation qualifier) and abortive operations `A e` (arity 0).
- **Instances are never data.** There is no value type of instances: an instance is a variable
  of `Ψ`, bound by `handle`, `nu`, `lend`, `using` or an instance abstraction, and passed only as
  an instance argument (`iapp`). A resource handle is an instance of the built-in effect `Res`.
- **Rows.** Thunk, function and stream types carry a row (`Rw`): the instances, by level, that
  forcing performs on. The denotation ignores rows; the moded judgement reads them.
-/

namespace EffRel

/-- The structural rules a mode admits: `w` weakening, `c` contraction. -/
structure Mode where
  w : Bool
  c : Bool
deriving DecidableEq, Repr

namespace Mode
def lin : Mode := ⟨false, false⟩
def aff : Mode := ⟨true, false⟩
def rel : Mode := ⟨false, true⟩
def unr : Mode := ⟨true, true⟩
/-- `m ≥ k`: `m` admits every rule `k` does. -/
def ge (m k : Mode) : Bool := (!k.w || m.w) && (!k.c || m.c)
end Mode

/-- Ground types. -/
inductive G where
  | unit
  | int
  | bool
  | void
deriving DecidableEq, Repr

def G.den : G → Type
  | .unit => Unit
  | .int => Int
  | .bool => Bool
  | .void => Empty

/-- A ground value with its type: the contents of a capability cell. -/
abbrev GVal := (g : G) × g.den

/-- An effect signature. It contains one built-in effect, `Res`, whose instances are the handles of
`using` frames: its operations answer `()` at the linear qualifier, it has no abortive operation,
and its bound is linear (`docs/effects-tr` D1.3). -/
structure Sig where
  E : Type
  [deq : DecidableEq E]
  /-- Resuming operations. -/
  O : E → Type
  /-- Abortive operations: arity 0, no continuation. -/
  A : E → Type
  arg : (e : E) → O e → G
  res : (e : E) → O e → G
  /-- The continuation qualifier of a resuming operation. -/
  q : (e : E) → O e → Mode
  aarg : (e : E) → A e → G
  /-- The bound of an effect's continuations: every qualifier, and affine if it may abort. -/
  bnd : E → Mode := fun _ => Mode.unr
  bnd_q : ∀ e o, (bnd e).ge (q e o) = true := by intro e o; simp [Mode.ge, Mode.unr]
  bnd_ab : ∀ e (_ : A e), (bnd e).ge Mode.aff = true := by intro e _; simp [Mode.ge, Mode.unr]
  /-- The built-in effect of resource handles. -/
  Res : E
  /-- Its operation: `use`. -/
  use : O Res
  use_arg : arg Res use = .unit
  res_unit : ∀ o : O Res, res Res o = .unit
  res_lin : ∀ o : O Res, q Res o = ⟨false, false⟩
  res_noab : A Res → False

attribute [instance] Sig.deq

/-- A **row**: the instances a computation may perform on, each paired with the lifetime it is
performed at. Both components are de Bruijn **levels** of the instance context (the position from
its outermost end), so a row written under some instances keeps its meaning under more. A level is
also a lifetime: the extent of the binder of the instance at that level, the outer ones
outliving the inner ones. A thunk's lifetime is the meet of its row's lifetimes (`Rw.life`), and
its effect bound, the join of the bounds of its instances' effects, is recovered from the row by
whoever knows the effects (`docs/effects-tr` D2.5). Rows replace phase B's bounds `Eb`. -/
structure Rw where
  ent : List (Nat × Nat)
deriving DecidableEq, Repr

namespace Rw
/-- The empty row: performs nothing. -/
def nil : Rw := ⟨[]⟩
/-- One instance, at its own lifetime. -/
def one (n : Nat) : Rw := ⟨[(n, n)]⟩
def union (ρ ρ' : Rw) : Rw := ⟨ρ.ent ++ ρ'.ent⟩
/-- The instance levels of a row. -/
def insts (ρ : Rw) : List Nat := ρ.ent.map Prod.fst
/-- The lifetime of a row: the meet of its lifetimes, the innermost level; `none` (`'static`) for
the empty row. -/
def life (ρ : Rw) : Option Nat :=
  ρ.ent.foldr (fun p acc => some (match acc with | some m => max p.2 m | none => p.2)) none
/-- Every instance and lifetime of the row is below level `n`: in scope under `n` instances. -/
def Sc (n : Nat) (ρ : Rw) : Prop := ∀ p ∈ ρ.ent, p.1 < n ∧ p.2 < n
end Rw

mutual
/-- Value types. -/
inductive VTy (S : Sig) : Type where
  | g (g : G)
  | prod (A B : VTy S)
  | sum (A B : VTy S)
  /-- `U` at mode `m`: a suspended computation; forcing it performs the row `b`. -/
  | U (m : Mode) (b : Rw) (C : CTy S)
  /-- An owned capability: a cell with state of type `s` and the co-operations of effect `e`. -/
  | cap (e : S.E) (s : G)
  /-- A stored generator `μX. U(F(A + int × X) & F 1)` whose pull performs the row `b`: pulled, or
  dropped. -/
  | strm (b : Rw) (A : VTy S)

/-- Computation types. -/
inductive CTy (S : Sig) : Type where
  | F (A : VTy S)
  /-- `A ⇒_b C`: after receiving its argument the function performs the row `b`. -/
  | arr (A : VTy S) (b : Rw) (C : CTy S)
  /-- A record of two methods, `C & D`. -/
  | wth (C D : CTy S)
  /-- `Πx:e. C`: a computation abstracted over an instance of `e`; it may perform on the instance
  it receives, which `C` does not mention. -/
  | pi (e : S.E) (C : CTy S)
end

variable {S : Sig}

/-- The pull side of a stream: done with an `A`, or an element and the rest. -/
abbrev VTy.step (b : Rw) (A : VTy S) : VTy S := .sum A (.prod (.g .int) (.strm b A))

/-- What a stream unfolds to: pull it, or drop it. -/
abbrev VTy.strmBody (b : Rw) (A : VTy S) : CTy S := .wth (.F (A.step b)) (.F (.g .unit))

/-- The type of a continuation captured at an operation of qualifier `q`, answer `r`, into
`C`. A continuation that may be dropped (`q.w`) is the pair `⟨resume, cancel⟩`, linear unless it
may also be duplicated; cancelling runs its destructors. One that may not be dropped is just
`resume`, at mode `q`. -/
def ktyB : Bool → Mode → Rw → G → CTy S → VTy S
  | true, q, b, r, C =>
      .U (if q.c then Mode.unr else Mode.lin) Rw.nil (.wth (.arr (.g r) b C) (.F (.g .unit)))
  | false, q, b, r, C => .U q Rw.nil (.arr (.g r) b C)

/-- The continuation of an operation of qualifier `q` and answer `r`, into `C`, whose resumption
performs within `b`. -/
abbrev kty (q : Mode) (b : Rw) (r : G) (C : CTy S) : VTy S := ktyB q.w q b r C

/-- The error a co-operation may answer: an integer code at a **fallible** operation, one whose
qualifier admits weakening, and nothing otherwise (`docs/effects-tr` D1.9, §8.2). -/
abbrev Sig.errG (S : Sig) (e : S.E) (o : S.O e) : G := if (S.q e o).w then .int else .void

/-- An error code as an integer. -/
def errInt : {b : Bool} → (if b then G.int else G.void).den → Int
  | true, n => n
  | false, x => (x : Empty).elim

/-- A co-operation's answer: the operation's answer and the next state, or an error code and
the state the capability keeps. -/
def coRes (S : Sig) (e : S.E) (s : G) (o : S.O e) : VTy S :=
  .sum (.prod (.g (S.res e o)) (.g s)) (.prod (.g (S.errG e o)) (.g s))

/-- de Bruijn variables. -/
inductive Var {α : Type} : List α → α → Type where
  | z : Var (a :: Γ) a
  | s : Var Γ a → Var (b :: Γ) a

inductive Prim where
  | add | sub | lt | eq
deriving DecidableEq, Repr

def Prim.res : Prim → G
  | .add | .sub => .int
  | .lt | .eq => .bool

def Prim.eval : (p : Prim) → Int → Int → (p.res).den
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .lt, a, b => decide (a < b)
  | .eq, a, b => decide (a = b)

mutual
/-- Values. -/
inductive Val (S : Sig) : List S.E → List (VTy S) → VTy S → Type where
  | var : Var Γ A → Val S Ψ Γ A
  | unit : Val S Ψ Γ (.g .unit)
  | int (n : Int) : Val S Ψ Γ (.g .int)
  | bool (b : Bool) : Val S Ψ Γ (.g .bool)
  | pair : Val S Ψ Γ A → Val S Ψ Γ B → Val S Ψ Γ (.prod A B)
  | inl : Val S Ψ Γ A → Val S Ψ Γ (.sum A B)
  | inr : Val S Ψ Γ B → Val S Ψ Γ (.sum A B)
  | thunk (m : Mode) : Cmp S Ψ Γ C → Val S Ψ Γ (.U m b C)
  /-- Roll a stream from a linear thunk of its body. -/
  | fold : Val S Ψ Γ (.U Mode.lin b (A.strmBody b)) → Val S Ψ Γ (.strm b A)

/-- Computations. -/
inductive Cmp (S : Sig) : List S.E → List (VTy S) → CTy S → Type where
  | ret : Val S Ψ Γ A → Cmp S Ψ Γ (.F A)
  /-- `M to x. N`. -/
  | bind : Cmp S Ψ Γ (.F A) → Cmp S Ψ (A :: Γ) C → Cmp S Ψ Γ C
  | lam : Cmp S Ψ (A :: Γ) C → Cmp S Ψ Γ (.arr A b C)
  | app : Cmp S Ψ Γ (.arr A b C) → Val S Ψ Γ A → Cmp S Ψ Γ C
  | force : Val S Ψ Γ (.U m b C) → Cmp S Ψ Γ C
  | rcd : Cmp S Ψ Γ C → Cmp S Ψ Γ D → Cmp S Ψ Γ (.wth C D)
  | prj1 : Cmp S Ψ Γ (.wth C D) → Cmp S Ψ Γ C
  | prj2 : Cmp S Ψ Γ (.wth C D) → Cmp S Ψ Γ D
  /-- `split v as (x, y). M`: `y` is index 0, `x` index 1. -/
  | split : Val S Ψ Γ (.prod A B) → Cmp S Ψ (B :: A :: Γ) C → Cmp S Ψ Γ C
  | case : Val S Ψ Γ (.sum A B) → Cmp S Ψ (A :: Γ) C → Cmp S Ψ (B :: Γ) C → Cmp S Ψ Γ C
  | ite : Val S Ψ Γ (.g .bool) → Cmp S Ψ Γ C → Cmp S Ψ Γ C → Cmp S Ψ Γ C
  | absurd : Val S Ψ Γ (.g .void) → Cmp S Ψ Γ C
  | prim (p : Prim) : Val S Ψ Γ (.g .int) → Val S Ψ Γ (.g .int) → Cmp S Ψ Γ (.F (.g p.res))
  /-- Output to the world. -/
  | emit : Val S Ψ Γ (.g .int) → Cmp S Ψ Γ (.F (.g .unit))
  /-- The algebraic operation `op_x(v; y. M)`, at any computation type. -/
  | op (x : Var Ψ e) (o : S.O e) :
      Val S Ψ Γ (.g (S.arg e o)) → Cmp S Ψ (.g (S.res e o) :: Γ) C → Cmp S Ψ Γ C
  /-- An abortive operation, at any computation type. -/
  | ab (x : Var Ψ e) (a : S.A e) : Val S Ψ Γ (.g (S.aarg e a)) → Cmp S Ψ Γ C
  /-- `ν x. handleAt x H M`: a fresh instance of `e` and a deep handler of it into `C`. A
  resuming clause binds the argument (index 1) and the continuation (index 0); an abortive
  clause binds the argument. -/
  | handle (e : S.E) (b : Rw) (hr : Cmp S Ψ (A :: Γ) C)
      (hop : (o : S.O e) → Cmp S Ψ (kty (S.q e o) b (S.res e o) C :: .g (S.arg e o) :: Γ) C)
      (hab : (a : S.A e) → Cmp S Ψ (.g (S.aarg e a) :: Γ) C)
      (M : Cmp S (e :: Ψ) Γ (.F A)) : Cmp S Ψ Γ C
  /-- A deep handler of an instance already in scope. -/
  | handleAt (x : Var Ψ e) (b : Rw) (hr : Cmp S Ψ (A :: Γ) C)
      (hop : (o : S.O e) → Cmp S Ψ (kty (S.q e o) b (S.res e o) C :: .g (S.arg e o) :: Γ) C)
      (hab : (a : S.A e) → Cmp S Ψ (.g (S.aarg e a) :: Γ) C)
      (M : Cmp S Ψ Γ (.F A)) : Cmp S Ψ Γ C
  /-- `ν x. M`: a fresh instance, handled by nobody yet. -/
  | nu (e : S.E) : Cmp S (e :: Ψ) Γ C → Cmp S Ψ Γ C
  /-- Instance equality, Staton's `?=`. -/
  | ieq (x : Var Ψ e) (y : Var Ψ e') : Cmp S Ψ Γ (.F (.g .bool))
  | ilam : Cmp S (e :: Ψ) Γ C → Cmp S Ψ Γ (.pi e C)
  | iapp : Cmp S Ψ Γ (.pi e C) → Var Ψ e → Cmp S Ψ Γ C
  /-- A new capability with state `v` and closed co-operations, each a state access
  `arg → s → F (coRes)` (the argument is index 1, the state index 0). -/
  | newcap (e : S.E) (s : G)
      (co : (o : S.O e) → Cmp S [] [.g s, .g (S.arg e o)] (.F (coRes S e s o)))
      : Val S Ψ Γ (.g s) → Cmp S Ψ Γ (.F (.cap e s))
  /-- Consume a capability; answer its final state. -/
  | getcap : Val S Ψ Γ (.cap e s) → Cmp S Ψ Γ (.F (.g s))
  /-- Lend a capability to `M` as a fresh instance: run `M` against the comodel. The lend
  **consumes** the capability and answers it back beside `M`'s answer or a co-operation's error
  (BoLo's `withbor` shape, `docs/effects-tr` D1.9). The state is written back when the body ends,
  normally, by a co-operation's error (`inr`), or by a cancel. -/
  | lend : Val S Ψ Γ (.cap e s) → Cmp S (e :: Ψ) Γ (.F A) →
      Cmp S Ψ Γ (.F (.prod (.cap e s) (.sum A (.g .int))))
  /-- Acquire a resource with label `ℓ`, owned by a frame whose destructor frees it. The handle is
  an instance of the built-in effect `Res`; `use` is an operation on it, answered in place by the
  frame (`docs/effects-tr` D1.9). -/
  | using (ℓ : Nat) : Cmp S (S.Res :: Ψ) Γ (.F A) → Cmp S Ψ Γ (.F A)
  /-- Unroll a stream. -/
  | unfold : Val S Ψ Γ (.strm b A) → Cmp S Ψ Γ (A.strmBody b)
  /-- Bounded recursion: `n` unrollings of `M` (the recursive thunk is index 0), then the
  abortive operation `a` on `x` (the kernel's `bounded_fix` and `Exhausted`). -/
  | bfix (x : Var Ψ e) (a : S.A e) (v : Val S Ψ Γ (.g (S.aarg e a))) (n : Nat) :
      Cmp S Ψ (.U Mode.unr b C :: Γ) C → Cmp S Ψ Γ C
end

end EffRel

/-!
# EffModel — syntax

A small call-by-push-value calculus in which

- every value type has a **mode**: the structural rules it admits (adjoint logic's `σ(m)`);
- a computation's effects are a **row of instances**: names generated at run time (Staton's `ν`),
  each bound by a handler (a model) or a runner (a comodel);
- an instance's type carries the **bound** of the continuations its operations capture: which
  structural rules a handler may apply to them, and whether a handler may suspend them.

Variables are names. Test programs bind each name once, so substitution never captures.
-/

namespace EffModel

/-! ## Modes -/

/-- The structural rules a mode admits: `w` weakening, `c` contraction. -/
structure Mode where
  w : Bool
  c : Bool
deriving DecidableEq, Repr, Inhabited

namespace Mode
/-- Linear: neither rule. -/
def lin : Mode := ⟨false, false⟩
/-- Affine: weakening. -/
def aff : Mode := ⟨true, false⟩
/-- Relevant (strict): contraction. -/
def rel : Mode := ⟨false, true⟩
/-- Unrestricted: both. -/
def unr : Mode := ⟨true, true⟩

/-- `m ≥ k`: `σ(m) ⊇ σ(k)`. Adjoint logic's declaration of independence reads it: a thing at
mode `k` may depend only on hypotheses at modes `m ≥ k`. -/
def ge (m k : Mode) : Bool := (!k.w || m.w) && (!k.c || m.c)

/-- The union of two sets of rules. -/
def join (m k : Mode) : Mode := ⟨m.w || k.w, m.c || k.c⟩

/-- The intersection: the rules a pair or a sum admits. -/
def meet (m k : Mode) : Mode := ⟨m.w && k.w, m.c && k.c⟩

def name (m : Mode) : String :=
  match m.w, m.c with
  | false, false => "lin" | true, false => "aff" | false, true => "rel" | true, true => "unr"
end Mode

/-- What a continuation captured at an operation may undergo.

- `req`: the structural rules the handler may apply to the continuation (and so to everything it
  captured). An operation's continuation qualifier is a mode; `req` is the union over the
  operations of an effect.
- `susp`: the handler may keep the continuation past the operation (store it, return it). A
  runner never does: a co-operation answers in place. -/
structure Bound where
  req : Mode
  susp : Bool
deriving DecidableEq, Repr, Inhabited

namespace Bound
/-- Nothing is captured: a runner's instance. -/
def none : Bound := ⟨Mode.lin, false⟩
/-- Everything: a row variable with no bound. -/
def top : Bound := ⟨Mode.unr, true⟩
def join (a b : Bound) : Bound := ⟨a.req.join b.req, a.susp || b.susp⟩
/-- `a ⊑ b`: an instance at bound `a` may stand where `b` is expected. -/
def le (a b : Bound) : Bool := b.req.ge a.req && (!a.susp || b.susp)
end Bound

/-! ## Rows and types -/

/-- A row atom: an instance variable or a row variable. -/
inductive Atom where
  | i (x : String)
  | r (x : String)
deriving DecidableEq, Repr, Inhabited

abbrev Row := List Atom

mutual
/-- Value types. -/
inductive VTy where
  | unit
  | int
  | bool
  | void
  /-- A handle on a resource owned by a `using` frame, whose destructor the frame runs. -/
  | resD
  /-- A relevant token: copyable, never dropped. -/
  | ticket
  | prod (a b : VTy)
  | sum (a b : VTy)
  /-- `U` at mode `m`: a suspended computation, with the effects it performs when run. -/
  | thunk (m : Mode) (ρ : Row) (c : CTy)
  /-- An instance of effect `e`, second class: a parameter or a bound variable, never data. -/
  | inst (e : String) (b : Bound)
  /-- An owned capability: a comodel of `e` with state `s`. Linear: it has no destructor. -/
  | cap (e : String) (s : VTy)
  /-- A stored generator `νX. U ρ (F (A + int × X))`, linear: pulled to its end or dropped. -/
  | stream (ρ : Row) (a : VTy)
  deriving Repr, Inhabited

/-- Computation types. A row sits where effects happen: after a function receives its
argument, after a record is projected. -/
inductive CTy where
  | F (a : VTy)
  /-- `(x : A) ⇒ρ C`; `x` may occur in `ρ` and `C` when `A` is an instance type. -/
  | arr (x : String) (a : VTy) (ρ : Row) (c : CTy)
  /-- A record of two methods, each with its row. -/
  | rcd (ρ₁ : Row) (c₁ : CTy) (ρ₂ : Row) (c₂ : CTy)
  /-- Row abstraction, bounded. -/
  | allR (r : String) (b : Bound) (ρ : Row) (c : CTy)
  deriving Repr, Inhabited
end

/-- Effect signatures: an operation's argument, answer and continuation qualifier. An
operation whose answer is `void` is abortive. -/
structure OpSig where
  name : String
  arg : VTy
  res : VTy
  k : Mode
deriving Repr

def OpSig.abortive (o : OpSig) : Bool := match o.res with | .void => true | _ => false

abbrev Sigs := List (String × List OpSig)

/-- The bound of an instance bound by a handler of an effect with these operations. -/
def boundOf (ops : List OpSig) : Bound :=
  ops.foldl (fun b o => b.join ⟨o.k, !o.abortive⟩) Bound.none

/-! ## Terms -/

inductive Prim where
  | add | sub | lt | eq
deriving DecidableEq, Repr

mutual
inductive Tm where
  -- values
  | var (x : String)
  | unit
  | int (n : Int)
  | bool (b : Bool)
  | pair (a b : Tm)
  | inl (a : Tm) (bt : VTy)
  | inr (aty : VTy) (b : Tm)
  | thunk (m : Mode) (M : Tm)
  /-- A recursive thunk `f`, always unrestricted. -/
  | fix (f : String) (ρ : Row) (c : CTy) (M : Tm)
  -- computations
  | ret (v : Tm)
  /-- `M to x. N`. -/
  | bind (M : Tm) (x : String) (N : Tm)
  | lam (x : String) (a : VTy) (M : Tm)
  | app (M : Tm) (v : Tm)
  | force (v : Tm)
  | rcd (M N : Tm)
  | prj (first : Bool) (M : Tm)
  | split (v : Tm) (x y : String) (M : Tm)
  | case (v : Tm) (x : String) (M : Tm) (y : String) (N : Tm)
  | ite (v : Tm) (M N : Tm)
  | absurd (v : Tm) (c : CTy)
  | prim (p : Prim) (a b : Tm)
  /-- Output to the world: the observable channel. -/
  | emit (v : Tm)
  /-- The algebraic operation `op_x(v; y. M)`, at any computation type. -/
  | op (x o : String) (v : Tm) (y : String) (M : Tm)
  /-- `ν x. handleAt x`: a fresh instance and a deep handler of it into `ρh, C`. -/
  | handle (x e : String) (h : Hnd) (ρh : Row) (c : CTy) (M : Tm)
  /-- A deep handler at an instance already in scope. -/
  | handleAt (x : String) (h : Hnd) (ρh : Row) (c : CTy) (M : Tm)
  /-- `ν x`: a fresh instance, handled by nobody yet. -/
  | nu (x e : String) (b : Bound) (M : Tm)
  /-- Instance equality, Staton's `?=`. -/
  | ieq (x y : String)
  /-- An owned capability: state `v`, co-operations `co`. -/
  | newcap (e : String) (s : VTy) (co : Hnd) (v : Tm)
  /-- Consume a capability; answer its final state. -/
  | getcap (v : Tm)
  /-- Lend capability `c` to `M` as instance `x`: run `M` against the comodel. -/
  | lend (c x : String) (M : Tm)
  /-- Acquire resource `n`, owned by a frame whose destructor frees it. -/
  | using (x : String) (n : Nat) (M : Tm)
  | use (v : Tm)
  | ticket (n : Nat)
  | punch (v : Tm)
  /-- Drop a stream: its destructor cancels the continuations it holds. -/
  | drop (v : Tm)
  | rlam (r : String) (b : Bound) (M : Tm)
  | rapp (M : Tm) (ρ : Row)
  deriving Repr, Inhabited

/-- Handler clauses: a return clause and one clause per operation. A capability's
co-operations use the same shape, with `ret` unused and `k` unused. -/
inductive Hnd where
  | ret (x : String) (M : Tm)
  /-- `o(p, k) ↦ M`, then the remaining clauses. -/
  | cl (o p k : String) (M : Tm) (rest : Hnd)
  deriving Repr, Inhabited
end

/-- Sugar: `perform x.o v`, the generic effect. -/
def perform (x o : String) (v : Tm) : Tm := .op x o v "_r" (.ret (.var "_r"))

/-- Sugar: `M; N` for `M : F unit`. -/
def seq (M N : Tm) : Tm := .bind M "_" N

/-- Sugar: `force f v`. -/
def call (f : Tm) (v : Tm) : Tm := .app (.force f) v

end EffModel

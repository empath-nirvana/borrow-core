import EffModelRel.Denot

/-!
# EffModelRel — observations and contextual equivalence

A closed program of ground type is observed by running its tree against the world: a name
supply, a store of cells and a trace. The observation is the outcome and the trace, with every
name erased. Labels of resources stay, so the order in which destructors run is observable.

- An operation that reaches the top is `unhandled`. The stack unwinds first: the destructors
  `d` it carries run.
- Reading, writing or consuming a dead cell is `stuck`. A moded program never does that
  (`safety_obs`, `UnaryFP.lean`).

**Contextual equivalence.** A context is a closed program with one free variable, the closure
of the hole: the hole's term abstracted over its instances and its values. Two terms are
contextually equivalent when no context of ground type tells them apart.
-/

namespace EffRel

variable {S : Sig}

inductive GV where
  | unit
  | int (n : Int)
  | bool (b : Bool)
deriving DecidableEq, Repr

def G.render : (g : G) → g.den → GV
  | .unit, _ => .unit
  | .int, n => .int n
  | .bool, b => .bool b
  | .void, x => (x : Empty).elim

/-- What the world sees, with names erased. -/
inductive Ev where
  | out (n : Int)
  | acq (ℓ : Nat)
  | use (ℓ : Nat)
  | free (ℓ : Nat)
  | mk
  | fin
deriving DecidableEq, Repr

inductive Outcome where
  | ret (v : GV)
  | unhandled
  | stuck
deriving DecidableEq, Repr

structure Obs where
  out : Outcome
  trace : List Ev
deriving DecidableEq, Repr

/-- The world: the next fresh name, the store, the trace (newest first). -/
structure Wd where
  next : Nat
  store : Nat → Option GVal
  trace : List Ev

def Wd.init : Wd := ⟨0, fun _ => none, []⟩

def Wd.emit (w : Wd) (e : Ev) : Wd := { w with trace := e :: w.trace }

def Wd.set (w : Wd) (c : Nat) (v : Option GVal) : Wd :=
  { w with store := fun c' => if c' = c then v else w.store c' }

/-- Read a cell at a type. -/
def Wd.get (w : Wd) (c : Nat) (g : G) : Option g.den :=
  match w.store c with
  | some ⟨g', v⟩ => if h : g' = g then some (h ▸ v) else none
  | none => none

def Act.exec : {g : G} → Act g → Wd → Option (g.den × Wd)
  | _, .out n, w => some ((), w.emit (.out n))
  | _, .acq ℓ _, w => some ((), w.emit (.acq ℓ))
  | _, .use ℓ _, w => some ((), w.emit (.use ℓ))
  | _, .free ℓ _, w => some ((), w.emit (.free ℓ))
  | _, .new c s, w => some ((), (w.set c (some s)).emit .mk)
  | _, .rd c g, w => (w.get c g).map (fun v => (v, w))
  | _, .wr c s, w => (w.store c).map (fun _ => ((), w.set c (some s)))
  | _, .kill c g, w => (w.get c g).map (fun v => (v, (w.set c none).emit .fin))

/-- An operation reached the top: unwind, running its destructors innermost first. -/
def Wd.unwind : List Dtor → Wd → Obs
  | [], w => ⟨.unhandled, w.trace.reverse⟩
  | δ :: d, w =>
      match δ.act.exec w with
      | some (_, w') => Wd.unwind d w'
      | none => ⟨.stuck, w.trace.reverse⟩

def Tree.obs (render : X → GV) : Tree S X → Wd → Obs
  | .ret x, w => ⟨.ret (render x), w.trace.reverse⟩
  | .op _ _ _ _ _ d, w => w.unwind d
  | .ab _ _ _ _ d, w => w.unwind d
  | .nu k, w => (k w.next).obs render { w with next := w.next + 1 }
  | .act a k, w =>
      match a.exec w with
      | some (y, w') => (k y).obs render w'
      | none => ⟨.stuck, w.trace.reverse⟩

/-- A closed program of ground type `g`. -/
abbrev Prog (S : Sig) (g : G) := Cmp S [] [] (.F (.g g))

def Prog.obs (P : Prog S g) : Obs := (P.den IEnv.nil Env.nil).obs (G.render g) Wd.init

/-! ## The hole: a term closed over its instances and values -/

def arrs : List (VTy S) → CTy S → CTy S
  | [], C => C
  | A :: Γ, C => .arr A Rw.nil (arrs Γ C)

def pis : List S.E → CTy S → CTy S
  | [], C => C
  | e :: Ψ, C => .pi e (pis Ψ C)

def holeTy (Ψ : List S.E) (Γ : List (VTy S)) (C : CTy S) : CTy S := pis Ψ (arrs Γ C)

def curryE : (Γ : List (VTy S)) → (Env Γ → C.den) → (arrs Γ C).den
  | [], f => f Env.nil
  | _ :: Γ, f => fun a => curryE Γ (fun ρ => f (ρ.cons a))

def curryI : (Ψ : List S.E) → (IEnv Ψ → D.den) → (pis Ψ D).den
  | [], f => f IEnv.nil
  | _ :: Ψ, f => fun i => curryI Ψ (fun η => f (η.cons i))

/-- The closure of a term's denotation. -/
def close (f : IEnv Ψ → Env Γ → C.den) : (holeTy Ψ Γ C).den :=
  curryI Ψ (fun η => curryE Γ (f η))

/-- A context: a closed program of ground type over the hole's closure. -/
abbrev Context (S : Sig) (Ψ : List S.E) (Γ : List (VTy S)) (C : CTy S) (g : G) :=
  Cmp S [] [.U Mode.unr Rw.nil (holeTy Ψ Γ C)] (.F (.g g))

def Context.obs (P : Context S Ψ Γ C g) (f : IEnv Ψ → Env Γ → C.den) : Obs :=
  (P.den IEnv.nil (Env.nil.cons (A := .U Mode.unr Rw.nil (holeTy Ψ Γ C)) (close f))).obs (G.render g)
    Wd.init

/-- Contextual equivalence. -/
def CtxEq (M N : Cmp S Ψ Γ C) : Prop :=
  ∀ (g : G) (P : Context S Ψ Γ C g), P.obs M.den = P.obs N.den

end EffRel

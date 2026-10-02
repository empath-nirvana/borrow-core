import EffModelRel.Syntax

/-!
# EffModelRel — the semantic domain

A computation denotes a **tree**: a free model of the effects, with the world's actions as
nodes. There is no fuel and no step index: the language has no general recursion (`bfix` is
bounded), so every term denotes a finite tree, and every definition below is structural.

- `op i e o v k d`: an operation on instance `i`, waiting for its answer; `d` lists the
  destructors of the frames between the operation and the node's eventual handler, innermost
  first. Cancelling the continuation runs `d` and nothing else (decision C).
- `ab i e a v d`: an abortive operation; its handler runs `d` and then its clause.
- `nu k`: a fresh name (an instance, a cell or a resource), Staton's `ν`.
- `act a k`: an action on the world: output, resources, cells.

**Every computation type is a model** (`CTy.opA`, `abA`, `nuA`, `actA`): operations at a function
or record type act pointwise. Handling is the fold of a tree into a model (`Tree.hnd`); a lend is
the state-passing fold of a tree against a comodel (`Tree.runL`).
-/

namespace EffRel

variable {S : Sig}

/-- An action on the world, with the type of its answer. -/
inductive Act : G → Type where
  | out (n : Int) : Act .unit
  | acq (ℓ r : Nat) : Act .unit
  | use (ℓ r : Nat) : Act .unit
  | free (ℓ r : Nat) : Act .unit
  /-- A new cell with its state. -/
  | new (c : Nat) (s : GVal) : Act .unit
  | rd (c : Nat) (g : G) : Act g
  | wr (c : Nat) (s : GVal) : Act .unit
  /-- Consume a cell: answer its state. -/
  | kill (c : Nat) (g : G) : Act g

/-- A destructor held by a frame: free a resource, or write a borrowed state back. -/
inductive Dtor where
  | free (ℓ r : Nat)
  | wb (c : Nat) (s : GVal)

def Dtor.act : Dtor → Act .unit
  | .free ℓ r => .free ℓ r
  | .wb c s => .wr c s

inductive Tree (S : Sig) (X : Type) : Type where
  | ret (x : X)
  | op (i : Nat) (e : S.E) (o : S.O e) (v : (S.arg e o).den) (k : (S.res e o).den → Tree S X)
      (d : List Dtor)
  | ab (i : Nat) (e : S.E) (a : S.A e) (v : (S.aarg e a).den) (d : List Dtor)
  | nu (k : Nat → Tree S X)
  | act {g : G} (a : Act g) (k : g.den → Tree S X)

/-- A stored generator: its pull, done or an element and the rest, and its drop. -/
inductive Strm (S : Sig) (X : Type) : Type where
  | mk (pull : Tree S (X ⊕ (Int × Strm S X))) (drop : Tree S Unit)

/-- The semantics of a capability's co-operations. -/
abbrev CoSem (S : Sig) (e : S.E) (s : G) : Type :=
  (o : S.O e) → (S.arg e o).den → s.den → Tree S (((S.res e o).den × s.den) ⊕ (Int × s.den))

mutual
def VTy.den : VTy S → Type
  | .g g => g.den
  | .prod A B => A.den × B.den
  | .sum A B => A.den ⊕ B.den
  | .U _ C => C.den
  | .cap e s => Nat × CoSem S e s
  | .res => Nat × Nat
  | .strm A => Strm S A.den
def CTy.den : CTy S → Type
  | .F A => Tree S A.den
  | .arr A C => A.den → C.den
  | .wth C D => C.den × D.den
  | .pi _ C => Nat → C.den
end

/-! ## Every computation type is a model -/

def CTy.opA : (C : CTy S) → Nat → (e : S.E) → (o : S.O e) → (S.arg e o).den →
    ((S.res e o).den → C.den) → List Dtor → C.den
  | .F _, i, e, o, v, k, d => Tree.op i e o v k d
  | .arr _ C, i, e, o, v, k, d => fun a => C.opA i e o v (fun y => k y a) d
  | .wth C D, i, e, o, v, k, d =>
      (C.opA i e o v (fun y => (k y).1) d, D.opA i e o v (fun y => (k y).2) d)
  | .pi _ C, i, e, o, v, k, d => fun n => C.opA i e o v (fun y => k y n) d

def CTy.abA : (C : CTy S) → Nat → (e : S.E) → (a : S.A e) → (S.aarg e a).den → List Dtor → C.den
  | .F _, i, e, a, v, d => Tree.ab i e a v d
  | .arr _ C, i, e, a, v, d => fun _ => C.abA i e a v d
  | .wth C D, i, e, a, v, d => (C.abA i e a v d, D.abA i e a v d)
  | .pi _ C, i, e, a, v, d => fun _ => C.abA i e a v d

def CTy.nuA : (C : CTy S) → (Nat → C.den) → C.den
  | .F _, k => Tree.nu k
  | .arr _ C, k => fun a => C.nuA (fun n => k n a)
  | .wth C D, k => (C.nuA (fun n => (k n).1), D.nuA (fun n => (k n).2))
  | .pi _ C, k => fun m => C.nuA (fun n => k n m)

def CTy.actA : (C : CTy S) → {g : G} → Act g → (g.den → C.den) → C.den
  | .F _, _, a, k => Tree.act a k
  | .arr _ C, _, a, k => fun x => C.actA a (fun y => k y x)
  | .wth C D, _, a, k => (C.actA a (fun y => (k y).1), D.actA a (fun y => (k y).2))
  | .pi _ C, _, a, k => fun m => C.actA a (fun y => k y m)

/-- Run destructors, innermost first, then continue. -/
def CTy.dtorsA (C : CTy S) : List Dtor → C.den → C.den
  | [], x => x
  | δ :: d, x => C.actA δ.act (fun _ => C.dtorsA d x)

/-- Run destructors on a tree, innermost first, then continue. -/
def Tree.dtors : List Dtor → Tree S X → Tree S X
  | [], t => t
  | δ :: d, t => .act δ.act (fun _ => Tree.dtors d t)

/-- The destructors as a computation: a continuation's cancel. -/
def dtorsT (d : List Dtor) : Tree S Unit := Tree.dtors d (.ret ())

/-- Monadic bind on trees. -/
def Tree.bind : Tree S X → (X → Tree S Y) → Tree S Y
  | .ret x, f => f x
  | .op i e o v k d, f => .op i e o v (fun y => (k y).bind f) d
  | .ab i e a v d, _ => .ab i e a v d
  | .nu k, f => .nu (fun n => (k n).bind f)
  | .act a k, f => .act a (fun y => (k y).bind f)

/-! ## Folds -/

/-- Sequencing: the fold of a tree into the model `C`. -/
def Tree.bindC (C : CTy S) : Tree S X → (X → C.den) → C.den
  | .ret x, f => f x
  | .op i e o v k d, f => C.opA i e o v (fun y => (k y).bindC C f) d
  | .ab i e a v d, _ => C.abA i e a v d
  | .nu k, f => C.nuA (fun n => (k n).bindC C f)
  | .act a k, f => C.actA a (fun y => (k y).bindC C f)

/-- A clause for effect `e` applied to an operation of effect `e'`, when they agree. -/
def catchOp {C : CTy S} (e : S.E)
    (hop : (o : S.O e) → (S.arg e o).den → ((S.res e o).den → C.den) → List Dtor → C.den)
    (e' : S.E) (o : S.O e') (v : (S.arg e' o).den) (k : (S.res e' o).den → C.den)
    (d : List Dtor) (fwd : C.den) : C.den :=
  if h : e' = e then by subst h; exact hop o v k d else fwd

def catchAb {C : CTy S} (e : S.E) (hab : (a : S.A e) → (S.aarg e a).den → C.den)
    (e' : S.E) (a : S.A e') (v : (S.aarg e' a).den) (d : List Dtor) (fwd : C.den) : C.den :=
  if h : e' = e then by subst h; exact C.dtorsA d (hab a v) else fwd

/-- A deep handler of instance `i` (of effect `e`) into `C`: the fold of a tree into the model
given by the clauses. An abortive operation runs the destructors `d`, then its clause; a
resuming clause receives the continuation and its destructors. -/
def Tree.hnd (C : CTy S) (i : Nat) (e : S.E) (hr : X → C.den)
    (hop : (o : S.O e) → (S.arg e o).den → ((S.res e o).den → C.den) → List Dtor → C.den)
    (hab : (a : S.A e) → (S.aarg e a).den → C.den) : Tree S X → C.den
  | .ret x => hr x
  | .op j e' o v k d =>
      let kk := fun y => (k y).hnd C i e hr hop hab
      if j = i then catchOp e hop e' o v kk d (C.opA j e' o v kk d) else C.opA j e' o v kk d
  | .ab j e' a v d =>
      if j = i then catchAb e hab e' a v d (C.abA j e' a v d) else C.abA j e' a v d
  | .nu k => C.nuA (fun n => (k n).hnd C i e hr hop hab)
  | .act a k => C.actA a (fun y => (k y).hnd C i e hr hop hab)

/-- After a co-operation: resume with the answer and the next state, or, on an error, cancel the
client's continuation (its destructors `d`), write the state back and answer the error. -/
def coK {R : Type} (sg : G) (c : Nat) (d : List Dtor) (rk : R → sg.den → Tree S (X ⊕ Int)) :
    (R × sg.den) ⊕ (Int × sg.den) → Tree S (X ⊕ Int)
  | .inl (y, s') => rk y s'
  | .inr (n, s') => Tree.dtors d (.act (.wr c ⟨sg, s'⟩) (fun _ => .ret (.inr n)))

/-- A co-operation answering an operation of `e'` on the runner of `e`, when they agree: the
co-operation runs on the state; an answer resumes the client in place with the next state; an
error cancels the client's continuation, writes the state back and answers the error. -/
def coStep (e : S.E) (sg : G) (co : CoSem S e sg) (c : Nat) (s : sg.den) (d : List Dtor)
    (e' : S.E) (o : S.O e') (v : (S.arg e' o).den)
    (rk : (S.res e' o).den → sg.den → Tree S (X ⊕ Int)) (fwd : Tree S (X ⊕ Int)) :
    Tree S (X ⊕ Int) :=
  if h : e' = e then by
    subst h
    exact (co o v s).bind (coK sg c d rk)
  else fwd

/-- A lend of cell `c` as instance `i`: the state-passing fold of the client's tree against the
comodel. Every continuation captured inside holds the borrow, so its destructors gain the
write-back of the state at that point. -/
def Tree.runL (i : Nat) (e : S.E) (c : Nat) (sg : G) (co : CoSem S e sg) :
    sg.den → Tree S X → Tree S (X ⊕ Int)
  | s, .ret x => .act (.wr c ⟨sg, s⟩) (fun _ => .ret (.inl x))
  | s, .op j e' o v k d =>
      let fwd := Tree.op j e' o v (fun y => (k y).runL i e c sg co s) (d ++ [.wb c ⟨sg, s⟩])
      if j = i then coStep e sg co c s d e' o v (fun y s' => (k y).runL i e c sg co s') fwd
      else fwd
  | s, .ab j e' a v d => .ab j e' a v (d ++ [.wb c ⟨sg, s⟩])
  | s, .nu k => .nu (fun n => (k n).runL i e c sg co s)
  | s, .act a k => .act a (fun y => (k y).runL i e c sg co s)

/-- A `using` frame owning resource `r` (label `ℓ`): free it on return, and add its destructor
to every continuation captured inside. -/
def Tree.addFin (ℓ r : Nat) : Tree S X → Tree S X
  | .ret x => .act (.free ℓ r) (fun _ => .ret x)
  | .op j e o v k d => .op j e o v (fun y => (k y).addFin ℓ r) (d ++ [.free ℓ r])
  | .ab j e a v d => .ab j e a v (d ++ [.free ℓ r])
  | .nu k => .nu (fun n => (k n).addFin ℓ r)
  | .act a k => .act a (fun y => (k y).addFin ℓ r)

end EffRel

import Std.Data.HashMap
import Std.Data.HashSet
import Backend.Clos.Syntax

/-!
# Backend — closure flow analysis

A 0-CFA over the closure IR: for every call `app f a`, the codes whose closures may be `f`. The
lowering (`Backend/Flat/Lower.lean`) calls a code directly when the set is one code; otherwise
it calls the dispatcher of `f`'s type, which switches on the closure's tag.

The analysis is monovariant and whole-program. Every value is abstracted by its construction
site: a closure by its code, a pair or an injection by the variables it is built from, a
location by the key of its contents (one per `alloc`, one per array). A *key* is a set of such
abstract values: a variable's, a code's answer, or an intermediate one. The constraints are
inclusions between keys, and inclusions guarded by the abstract values of a key (the fields of
the pairs a `letpair` takes apart, the parameters and answers of the closures a call calls, the
contents of the locations a `load` reads). Their least solution is found by iteration.

Everything that calls a closure is a constraint, including what the flat IR's helpers do: `tab`
calls its tabulator, an array's `drop` its consumer, and when `main` returns a loop the entry
drives it and runs the code `fin` on what it finishes with. The analysis over-approximates the
closures that reach each call, so a call of one code is a call of that code on every run: the
closure IR's variables are each bound once and consumed once, and a closure's code does not
change once it is built.
-/

namespace Backend.Clos

/-- A set of abstract values. -/
inductive Key where
  | var (x : Var)
  /-- Code `c`'s answer. -/
  | res (c : Nat)
  | syn (n : Nat)
  /-- The loops the entry drives. -/
  | drive
  deriving BEq, Hashable, Repr, Inhabited

/-- An abstract value. -/
inductive AVal where
  | clos (c : Nat)
  | pair (a b : Key)
  | inj (right : Bool) (a : Key)
  /-- A location whose contents are `k`. -/
  | loc (k : Key)
  deriving BEq, Hashable, Repr

inductive Con where
  | elem (v : AVal) (k : Key)
  | sub (k k' : Key)
  /-- Component `i` of the pairs of `k` is in `k'`. -/
  | proj (k : Key) (i : Nat) (k' : Key)
  /-- The payload of the injections `right` of `k` is in `k'`. -/
  | out (k : Key) (right : Bool) (k' : Key)
  /-- The closures of `f` are called on `a`, answering into `r`. -/
  | app (f a r : Key)
  /-- The contents of the locations of `l` are in `r`. -/
  | load (l r : Key)
  /-- `v` is in the contents of the locations of `l`. -/
  | store (l v : Key)

structure GState where
  next : Nat := 1
  cons : Array Con := #[]

abbrev GM := StateM GState

/-- The empty key: no constraint has it on the right. -/
def Key.none : Key := .syn 0

def freshKey : GM Key := modifyGet fun s => (.syn s.next, { s with next := s.next + 1 })

def emit (c : Con) : GM Unit := modify fun s => { s with cons := s.cons.push c }

/-- A fresh key holding `v`. -/
def holding (v : AVal) : GM Key := do
  let k ← freshKey
  emit (.elem v k)
  pure k

def genPrim : Op → List Var → GM Key
  | .alloc, [v] => do
      let c ← freshKey
      emit (.sub (.var v) c)
      holding (.loc c)
  | .free, [l] | .load, [l] => do
      let r ← freshKey
      emit (.load (.var l) r)
      pure r
  | .store, [l, v] => do emit (.store (.var l) (.var v)); pure .none
  | .swap, [l, v] => do
      let old ← freshKey
      emit (.load (.var l) old)
      emit (.store (.var l) (.var v))
      holding (.pair (.var l) old)
  | .tab, [v] => do
      let f ← freshKey
      emit (.proj (.var v) 1 f)
      let c ← freshKey
      emit (.app f .none c)
      holding (.pair (← holding (.loc c)) .none)
  | .idx, [v] => do
      let h ← freshKey
      emit (.proj (.var v) 0 h)
      let l ← freshKey
      emit (.proj h 0 l)
      holding (.inj false l)
  | .drop, [v] => do
      let f ← freshKey
      emit (.proj (.var v) 0 f)
      let h ← freshKey
      emit (.proj (.var v) 1 h)
      let l ← freshKey
      emit (.proj h 0 l)
      let c ← freshKey
      emit (.load l c)
      emit (.app f c (← freshKey))
      pure .none
  | .io .readByte, [m] => holding (.pair (.var m) .none)
  | .io .writeByte, [p] => do
      let m ← freshKey
      emit (.proj (.var p) 0 m)
      pure m
  | _, _ => pure .none

/-- The constraints of a term; the key of its value. -/
def gen (codes : Array Code) : Tm → GM Key
  | .var x => pure (.var x)
  | .unit | .lit _ => pure .none
  | .pair a b => holding (.pair (.var a) (.var b))
  | .inj r a => holding (.inj r (.var a))
  | .clos c xs => do
      if let some code := codes[c]? then
        for (e, x) in code.env.zip xs do emit (.sub (.var x) (.var e))
      holding (.clos c)
  | .prim op xs => genPrim op xs
  | .app f a => do
      let r ← freshKey
      emit (.app (.var f) (.var a) r)
      pure r
  | .letv x e b => do
      emit (.sub (← gen codes e) (.var x))
      gen codes b
  | .letpair x y p b => do
      emit (.proj (.var p) 0 (.var x))
      emit (.proj (.var p) 1 (.var y))
      gen codes b
  | .case s x b₁ y b₂ => do
      emit (.out (.var s) false (.var x))
      emit (.out (.var s) true (.var y))
      let k₁ ← gen codes b₁
      let k₂ ← gen codes b₂
      let k ← freshKey
      emit (.sub k₁ k)
      emit (.sub k₂ k)
      pure k
  | .copy x x' b => do
      emit (.sub (.var x) (.var x'))
      gen codes b
  | .drop _ b => gen codes b

/-- The program's constraints. -/
def Prog.constraints (p : Prog) : Array Con := Id.run do
  let act : GM Unit := do
    for (c, k) in p.codes.toList.zipIdx do
      emit (.sub (← gen p.codes c.body) (.res k))
    let m ← gen p.codes p.main
    if let some fin := p.fin then
      -- The entry drives the loop `main` returns: `inl r` goes to `fin`, `inr` loops again.
      let loop := Key.drive
      emit (.sub m loop)
      let r ← freshKey
      emit (.app loop .none r)
      emit (.out r true loop)
      if let some code := p.codes[fin]? then emit (.out r false (.var code.param))
  let ((), s) := act.run {}
  return s.cons

abbrev Sets := Std.HashMap Key (Std.HashSet AVal)

def Sets.of (S : Sets) (k : Key) : Std.HashSet AVal := S.getD k {}

/-- Add the abstract values `vs` to `k`; whether anything was new. -/
def addAll (S : Sets) (vs : Std.HashSet AVal) (k : Key) : Sets × Bool :=
  if vs.isEmpty then (S, false) else
  let old := S.of k
  let new := vs.fold (fun acc v => if old.contains v then acc else acc.insert v) old
  if new.size == old.size then (S, false) else (S.insert k new, true)

/-- One pass over the constraints. -/
def step (codes : Array Code) (cs : Array Con) (S : Sets) : Sets × Bool := Id.run do
  let mut S := S
  let mut changed := false
  for c in cs do
    let add (S : Sets) (from_ to : Key) : Sets × Bool := addAll S (S.of from_) to
    match c with
    | .elem v k =>
      let (S', ch) := addAll S (({} : Std.HashSet AVal).insert v) k
      S := S'; changed := changed || ch
    | .sub k k' =>
      let (S', ch) := add S k k'
      S := S'; changed := changed || ch
    | .proj k i k' =>
      for v in S.of k do
        if let .pair a b := v then
          let (S', ch) := add S (if i == 0 then a else b) k'
          S := S'; changed := changed || ch
    | .out k r k' =>
      for v in S.of k do
        if let .inj r' a := v then
          if r == r' then
            let (S', ch) := add S a k'
            S := S'; changed := changed || ch
    | .app f a r =>
      for v in S.of f do
        if let .clos c := v then
          if let some code := codes[c]? then
            let (S', ch) := add S a (.var code.param)
            S := S'; changed := changed || ch
          let (S', ch) := add S (.res c) r
          S := S'; changed := changed || ch
    | .load l r =>
      for v in S.of l do
        if let .loc k := v then
          let (S', ch) := add S k r
          S := S'; changed := changed || ch
    | .store l x =>
      for v in S.of l do
        if let .loc k := v then
          let (S', ch) := add S x k
          S := S'; changed := changed || ch
  return (S, changed)

/-- The least solution, or `none` when it is not reached in `fuel` passes. -/
def solve (codes : Array Code) (cs : Array Con) : Nat → Sets → Option Sets
  | 0, _ => none
  | fuel + 1, S =>
    let (S, changed) := step codes cs S
    if changed then solve codes cs fuel S else some S

/-- The codes of the closures in `k`, in code order. -/
def Sets.codes (S : Sets) (k : Key) : Array Nat :=
  ((S.of k).fold (fun acc v => match v with
    | .clos c => acc.push c
    | _ => acc) #[]).qsort (· < ·)

/-- For every call `app f a`, keyed by `f` (which only the call consumes): the codes whose
closures may be called there, in code order; and the codes of the loops the entry drives. With
no solution, no call's codes are known. -/
def Prog.flowAll (p : Prog) : Std.HashMap Var (Array Nat) × Option (Array Nat) := Id.run do
  let cs := p.constraints
  let some S := solve p.codes cs 100000 {} | return ({}, none)
  let mut out : Std.HashMap Var (Array Nat) := {}
  for c in cs do
    if let .app (.var f) _ _ := c then
      out := out.insert f (S.codes (.var f))
  return (out, if p.fin.isSome then some (S.codes .drive) else none)

/-- For every call `app f a`, keyed by `f`: the codes whose closures may be called there. -/
def Prog.flow (p : Prog) : Std.HashMap Var (Array Nat) := p.flowAll.1

end Backend.Clos

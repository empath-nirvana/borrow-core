import Std.Data.HashMap
import Std.Data.HashSet
import Backend2.Layout

/-!
# Backend2 — the closure flow: a 0-CFA, run once  `[docs/compiler.md §3.1]`

Which closure codes reach a call is not a typing fact: the typed term says a value is a closure of
`A ⊸ C`, not which λ made it. This analysis answers it, once, on the LIR: for every variable that
holds a closure, the set of codes whose closures may be there, as the least solution of the
inclusion constraints of the program's moves:

- a closure made of code `c` holds `c`; a binding, a copy, an argument and its parameter, a result
  and its function's answer move the set they carry;
- a call's set of codes adds, for each code, the move of its argument to that code's parameter and
  of that code's answer to the call's result;
- a closure read out of data (a pair, a sum, a cell, an array) holds the codes its layout's class
  holds (`Backend2/Layout.lean`): the classes are an over-approximation of every flow.

A call whose function variable holds one code is a direct call of that code (`known`); any other
is a call of its class's dispatcher.
-/

namespace Backend2.Flow
open Backend2 Backend2.Lay

/-- A call site: the closure, its argument, the variable its answer goes to, the component. -/
structure Site where
  f : Var
  arg : Option Var
  dst : Option Var
  j : Nat

structure St where
  sets : Std.HashMap Var (Std.HashSet Nat) := {}
  /-- The moves out of each variable. -/
  out : Std.HashMap Var (Array Var) := {}
  /-- The call sites of each function variable. -/
  sites : Std.HashMap Var (Array Site) := {}
  todo : Array Var := #[]

abbrev FM := StateT St Id

def isClos (p : Prog) (x : Var) : Bool :=
  match p.ty[x]? with
  | some (.thunk _) => true
  | _ => false

def addCodes (x : Var) (cs : List Nat) : FM Unit := do
  let s ← get
  let old := s.sets.getD x {}
  let new := cs.foldl (·.insert ·) old
  if new.size != old.size then
    set { s with sets := s.sets.insert x new, todo := s.todo.push x }

def edge (p : Prog) (y x : Var) : FM Unit := do
  if !(isClos p y && isClos p x) then return
  modify fun s => { s with out := s.out.insert y ((s.out.getD y #[]).push x) }
  addCodes x ((← get).sets.getD y {}).toList

/-- `x` is read out of data: it holds its class's codes. -/
def coarse (p : Prog) (L : Layouts) (x : Var) : FM Unit := do
  if isClos p x then addCodes x (L.unionOf (L.node x)).toList

/-- The pseudo-variable of function `fn`'s answer. -/
def retVar (base fn : Nat) : Var := base + fn

/-- The constraints of a term whose value goes to `dst`. -/
def gen (p : Prog) (L : Layouts) (base : Nat) : Nat → Tm → Option Var → FM Unit
  | 0, _, _ => pure ()
  | f + 1, t, dst => do
    match t with
    | .var y => if let some d := dst then edge p y d
    | .clos c env => do
      if let some d := dst then addCodes d [c]
      if let some code := p.codes[c]? then
        for fn in code.fns do
          if let some fd := p.fns[fn]? then
            for (x, y) in env.zip fd.params do edge p x y
    | .app g a => site ⟨g, some a, dst, 0⟩
    | .app0 g => site ⟨g, none, dst, 0⟩
    | .sel g j => site ⟨g, none, dst, j⟩
    | .call fn as => do
      if let some fd := p.fns[fn]? then
        for (x, y) in as.zip fd.params do edge p x y
      if let some d := dst then
        modify fun s => { s with out := s.out.insert (retVar base fn) ((s.out.getD (retVar base fn) #[]).push d) }
        addCodes d ((← get).sets.getD (retVar base fn) {}).toList
    | .prim (.tab fi) as | .prim (.tabLit fi ..) as => do
      if let (some fd, some g) := (p.fns[fi]?, as.head?) then
        if let some pf := fd.params.head? then edge p g pf
    | .prim _ _ => if let some d := dst then coarse p L d
    | .letv x e b => do gen p L base f e (some x); gen p L base f b dst
    | .letpair x y _ b => do coarse p L x; coarse p L y; gen p L base f b dst
    | .case _ x b₁ y b₂ => do
      coarse p L x; coarse p L y
      gen p L base f b₁ dst; gen p L base f b₂ dst
    | .copy x x' b => do edge p x x'; gen p L base f b dst
    | .drop _ b => gen p L base f b dst
    | .unit | .lit _ | .pair .. | .inj .. | .absurd _ => pure ()
where
  site (s : Site) : FM Unit := do
    modify fun st => { st with sites := st.sites.insert s.f ((st.sites.getD s.f #[]).push s) }
    -- The codes already there are taken by the solver, which revisits the variable.
    modify fun st => { st with todo := st.todo.push s.f }

/-- A code joins a call site: its argument to the code's parameter, its answer to the site's. -/
def link (p : Prog) (base : Nat) (s : Site) (c : Nat) : FM Unit := do
  let some code := p.codes[c]? | return
  let some fn := code.fns[s.j]? | return
  let some fd := p.fns[fn]? | return
  if let some a := s.arg then
    if let some prm := fd.params.getLast? then edge p a prm
  if let some d := s.dst then
    let r := retVar base fn
    modify fun st => { st with out := st.out.insert r ((st.out.getD r #[]).push d) }
    addCodes d ((← get).sets.getD r {}).toList

-- UNPROVED: that the solution holds every code that can reach each variable. It should hold
-- because every move of the LIR adds an inclusion (`gen`, `link`) and data falls back to its
-- layout class (`coarse`), itself joined over every move (`Backend2/Layout.lean`). It is not a
-- typing fact: the typed term says a value is a closure of a type, not which λ made it. The
-- loop stops at `fuel` steps with whatever it has. If a code is missing, `known` makes a direct
-- call of the wrong code (`Lower.callTarget`), and a literal's view takes a tabulator for the
-- literal tables' code (`Lower`, `tabLit`).
/-- The least solution. -/
def solve (p : Prog) (base : Nat) (fuel : Nat) : FM Unit := do
  let mut linked : Std.HashSet (Var × Nat × Nat) := {}
  for _ in [0:fuel] do
    let s ← get
    match s.todo.back? with
    | none => return
    | some x =>
      set { s with todo := s.todo.pop }
      let cs := ((← get).sets.getD x {}).toList
      for y in (← get).out.getD x #[] do addCodes y cs
      for st in (← get).sites.getD x #[] do
        for c in cs do
          if !linked.contains (x, st.j, c) then
            linked := linked.insert (x, st.j, c)
            link p base st c

/-- The function body's answer flows to its pseudo-variable. -/
def genFns (p : Prog) (L : Layouts) (base : Nat) : FM Unit := do
  for (fd, i) in p.fns.toList.zipIdx do
    -- The pseudo-variable stands for the answer at its type.
    gen p L base (1 <<< 22) fd.body (if isClosT fd.ret then some (retVar base i) else none)
  gen p L base (1 <<< 22) p.main none
where
  isClosT : LTy → Bool
    | .thunk _ => true
    | _ => false

/-- The solution: each closure variable's codes, and the call sites. -/
def solution (p : Prog) (L : Layouts) : St :=
  let base := p.ty.fold (fun m x _ => max m (x + 1)) 0
  -- The pseudo-variables of the answers are closures where the function answers one.
  let p' := { p with ty := p.fns.toList.zipIdx.foldl (fun m (fd, i) => m.insert (base + i) fd.ret) p.ty }
  (((genFns p' L base) *> solve p' base (1 <<< 26)).run {}).2

/-- The known code of each call's function variable. -/
def known (p : Prog) (L : Layouts) (s : St := solution p L) : Std.HashMap Var Nat := Id.run do
  let mut out : Std.HashMap Var Nat := {}
  for (x, _) in s.sites.toList do
    let cs := s.sets.getD x {}
    if cs.size == 1 then
      if let some c := cs.toList.head? then out := out.insert x c
  return out

end Backend2.Flow

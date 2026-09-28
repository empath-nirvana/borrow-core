import Std.Data.HashMap
import Std.Data.HashSet
import Backend.Clos.Syntax

/-!
# Backend — layout types of the closure IR

The typed erasure: every closure-IR variable, closure code and constructor gets a *layout type*,
the value type as far as its machine representation depends on it, and every layout type gets a
layout (`Backend/README.md`, Representation).

    L ::= any | 1 | i32 | i64 | L ⊗ L | L ⊕ L | fn(L; L, L) | loc L

`fn(A; C, D)` is a closure taking `A`; called on `inl ()` it answers `C`, on `inr ()` `D`, and on
an argument not known at the call `C = D`. This is how a thunk of `C & D` (erased by `withPair`
to `λs. case s {…}`) answers its two projections at two types. `loc A` is a location holding an
`A`: a cell, or an element of an array. `any` is a type no value is built at.

A location's contents change type at `swap` (`Ref A ⊸ B ⊸ Ref B ⊗ A`), so a `loc` type also
names a *cell class*: the locations that may be the same cell, as `swap`'s argument and result
are. The cells of a class are as wide as the widest contents any `loc` type of the class holds.

**Inference.** The types are found by unification over the closure IR, which is closed and
named: every λ of the program is its own code, and a definition is substituted at each use, so
no value-type parameter remains (value types are monomorphic; polymorphism is over lifetimes,
whose arguments are `()`). Unification has no occurs check: the recursive types `μ` and `ν` of
the source are regular trees, as the erasure leaves them. Two code shapes are read specially:

- a code whose body is `case` on its parameter answers the two projections of `&` at the types
  of its two arms (`fn(A; C, D)` with `C`, `D` the arms' types);
- a code whose body passes its parameter to a function in tail position (`λo. f o`, as `unfold`
  forwards an observation) has that function's type.

A call whose argument is a literal injection (after `let`s and copies) is a projection: it
answers the arm's type. The source's typing derivation guarantees that the erasure has these
types; a program for which unification fails is reported, not compiled.

**Layout.** `1` and `any` are no words; `i32`, `i64`, `fn` and `loc` one; a pair is its two
components side by side; a sum is a tag word and the larger of its two payloads. A recursive type
would be infinitely wide, so the fields that close a cycle (the back edges of one depth-first
search over the pair and sum edges) are stored behind a pointer to a heap object of the field's
own layout. A type is *trivial* when copying it is copying its words and dropping it is
nothing: it holds no closure and no such pointer.
-/

namespace Backend.Clos
open BoCa

/-! ### Host operations  `[spec §8]` -/

/-- The width of a host operation's operands. -/
def hostArgWidth : HostOp → Width
  | .bin w _ | .div w _ | .un w _ | .eqz w | .rel w _ => w
  | .wrap => .w64
  | .extend_s | .extend_u => .w32
  | .extend32_s => .w64

/-- The operation takes a pair. -/
def hostBinary : HostOp → Bool
  | .bin .. | .div .. | .rel .. => true
  | _ => false

/-- The type of a host operation's result: an integer, a test (`inr ()` for true), or a partial
operation's `inl n` or `inr ()`. -/
inductive ResKind where
  | int (w : Width)
  | test
  | trapping (w : Width)

def hostResKind : HostOp → ResKind
  | .bin w _ | .un w _ => .int w
  | .div w _ => .trapping w
  | .eqz _ | .rel .. => .test
  | .wrap => .int .w32
  | .extend_s | .extend_u | .extend32_s => .int .w64

/-! ### Layout types -/

/-- A layout type; children are type nodes. -/
inductive LTy where
  | any
  | unit
  | int (w : Width)
  | pair (a b : Nat)
  | sum (a b : Nat)
  /-- `fn(A; C, D)`. -/
  | fn (a c d : Nat)
  /-- A location holding an `a`, of cell class `cls`. -/
  | loc (a cls : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- The pair and sum edges of a type, in field order. -/
def LTy.fields : LTy → List Nat
  | .pair a b | .sum a b => [a, b]
  | _ => []

/-- How a code's body is typed. -/
inductive CodeKind where
  | plain
  /-- The body is `let s = p; case s {…}` on the parameter `p`: the arms answer the two
  projections. -/
  | sel
  /-- The body is `let a = p; let f = …; f a`: it has `f`'s type. -/
  | fwd
  deriving Repr, Inhabited, DecidableEq

structure TState where
  nodes : Array LTy := #[]
  parent : Array Nat := #[]
  /-- The union-find of cell classes. -/
  classes : Array Nat := #[]
  varTy : Std.HashMap Var Nat := {}
  /-- Variables bound to a literal injection: `true` for `inr`. -/
  sel : Std.HashMap Var Bool := {}
  /-- The type of a pair or an injection, by its (first) operand, and of the cell `alloc` or the
  array `tab` makes, by its operand; only the one term consumes the operand. -/
  cons : Std.HashMap Var Nat := {}
  /-- The result type of a call, by its function variable, which only it consumes. -/
  apps : Std.HashMap Var Nat := {}

abbrev TM := StateT TState (Except String)

def newNode (t : LTy) : TM Nat :=
  modifyGet fun s => (s.nodes.size,
    { s with nodes := s.nodes.push t, parent := s.parent.push s.nodes.size })

/-- The representative of `n`. -/
def findIn (parent : Array Nat) (n : Nat) : Nat :=
  go parent.size n
where
  go : Nat → Nat → Nat
    | 0, n => n
    | k + 1, n => let p := parent[n]?.getD n; if p == n then n else go k p

def find (n : Nat) : TM Nat := do
  let r := findIn (← get).parent n
  if r != n then modify fun s => { s with parent := s.parent.set! n r }
  pure r

def link (x y : Nat) : TM Unit := modify fun s => { s with parent := s.parent.set! x y }

def newClass : TM Nat :=
  modifyGet fun s => (s.classes.size, { s with classes := s.classes.push s.classes.size })

/-- The same cell class. -/
def joinClass (c c' : Nat) : TM Unit := do
  let s ← get
  let r := findIn s.classes c
  let r' := findIn s.classes c'
  if r != r' then modify fun s => { s with classes := s.classes.set! r r' }

/-- A location holding `a`, of a new class. -/
def newLoc (a : Nat) : TM Nat := do newNode (.loc a (← newClass))

/-- A type, to depth `k`, for messages. -/
def describe (k : Nat) (n : Nat) : TM String := do
  match k with
  | 0 => pure "…"
  | k + 1 =>
    let n ← find n
    match (← get).nodes[n]! with
    | .any => pure "_"
    | .unit => pure "1"
    | .int .w32 => pure "i32"
    | .int .w64 => pure "i64"
    | .pair a b => pure s!"({← describe k a} * {← describe k b})"
    | .sum a b => pure s!"({← describe k a} + {← describe k b})"
    | .fn a c d => pure s!"fn({← describe k a}; {← describe k c}, {← describe k d})"
    | .loc a _ => pure s!"loc {← describe k a}"

def unifyFuel : Nat := 1 <<< 26

def unify (a b : Nat) : TM Unit := do
  let mut work : List (Nat × Nat) := [(a, b)]
  for _ in [0:unifyFuel] do
    match work with
    | [] => break
    | (x, y) :: rest =>
      work := rest
      let x ← find x
      let y ← find y
      if x != y then
        let s ← get
        match s.nodes[x]!, s.nodes[y]! with
        | .any, _ => link x y
        | _, .any => link y x
        | .unit, .unit => link x y
        | .int w, .int w' =>
          if w == w' then link x y
          else throw s!"layout types: {← describe 4 x} and {← describe 4 y} differ"
        | .pair a b, .pair a' b' => link x y; work := (a, a') :: (b, b') :: work
        | .sum a b, .sum a' b' => link x y; work := (a, a') :: (b, b') :: work
        | .fn a c d, .fn a' c' d' => link x y; work := (a, a') :: (c, c') :: (d, d') :: work
        | .loc a c, .loc a' c' => link x y; joinClass c c'; work := (a, a') :: work
        | _, _ => throw s!"layout types: {← describe 4 x} and {← describe 4 y} differ"
  unless work.isEmpty do throw "layout types: out of fuel"

def tyVar (x : Var) : TM Nat := do
  match (← get).varTy[x]? with
  | some n => pure n
  | none =>
    let n ← newNode .any
    modify fun s => { s with varTy := s.varTy.insert x n }
    pure n

/-- The injection a term ends in, when it is a literal one. -/
def selOf : Tm → TM (Option Bool)
  | .inj r _ => pure (some r)
  | .var y => return (← get).sel[y]?
  | .letv _ _ b | .copy _ _ b | .drop _ b => selOf b
  | _ => pure none

def int32 : TM Nat := newNode (.int .w32)
def unitT : TM Nat := newNode .unit

/-- The type of a saturated primitive, constraining its operands. -/
def primTy : Op → List Var → TM Nat
  | .alloc, [v] => do
      let n ← newLoc (← tyVar v)
      modify fun s => { s with cons := s.cons.insert v n }
      pure n
  | .free, [l] | .load, [l] => do
      let a ← newNode .any
      unify (← tyVar l) (← newLoc a)
      pure a
  | .store, [l, v] => do
      unify (← tyVar l) (← newLoc (← tyVar v))
      unitT
  | .swap, [l, v] => do
      -- The result is the same cell, now holding `v`'s type.
      let a ← newNode .any
      let c ← newClass
      unify (← tyVar l) (← newNode (.loc a c))
      newNode (.pair (← newNode (.loc (← tyVar v) c)) a)
  | .host op, [v] => do
      let w := hostArgWidth op
      let arg ← if hostBinary op then do newNode (.pair (← newNode (.int w)) (← newNode (.int w)))
        else newNode (.int w)
      unify (← tyVar v) arg
      match hostResKind op with
      | .int w => newNode (.int w)
      | .test => do newNode (.sum (← unitT) (← unitT))
      | .trapping w => do newNode (.sum (← newNode (.int w)) (← unitT))
  | .tab, [v] => do
      let a ← newNode .any
      let f ← newNode (.fn (← int32) a a)
      unify (← tyVar v) (← newNode (.pair (← int32) f))
      let n ← newNode (.pair (← newLoc a) (← int32))
      modify fun s => { s with cons := s.cons.insert v n }
      pure n
  | .idx, [v] => do
      let a ← newNode .any
      let l ← newLoc a
      unify (← tyVar v) (← newNode (.pair (← newNode (.pair l (← int32))) (← int32)))
      newNode (.sum l (← unitT))
  | .drop, [v] => do
      let a ← newNode .any
      let r ← newNode .any
      let f ← newNode (.fn a r r)
      unify (← tyVar v) (← newNode (.pair f (← newNode (.pair (← newLoc a) (← int32)))))
      unitT
  | .io .readByte, [m] => do
      let l ← newLoc (← int32)
      unify (← tyVar m) l
      newNode (.pair l (← newNode (.sum (← int32) (← unitT))))
  | .io .writeByte, [p] => do
      let l ← newLoc (← int32)
      unify (← tyVar p) (← newNode (.pair l (← int32)))
      pure l
  | _, _ => throw "layout types: primitive arity"

/-- The type of a term, constraining its variables. `codeTy c` is code `c`'s type. -/
def infer (codeTy : Array Nat) (codes : Array Code) : Tm → TM Nat
  | .var x => tyVar x
  | .unit => unitT
  | .lit (.i32 _) => int32
  | .lit (.i64 _) => newNode (.int .w64)
  | .pair a b => do
      let n ← newNode (.pair (← tyVar a) (← tyVar b))
      modify fun s => { s with cons := s.cons.insert a n }
      pure n
  | .inj r a => do
      let o ← newNode .any
      let t ← tyVar a
      let n ← newNode (if r then .sum o t else .sum t o)
      modify fun s => { s with cons := s.cons.insert a n }
      pure n
  | .clos c xs => do
      let some code := codes[c]? | throw s!"layout types: no code {c}"
      if code.env.length != xs.length then throw s!"layout types: code {c}'s environment"
      for (e, x) in code.env.zip xs do unify (← tyVar e) (← tyVar x)
      pure codeTy[c]!
  | .prim op xs => primTy op xs
  | .app f a => do
      let r ← newNode .any
      let o ← newNode .any
      let t ← tyVar a
      let fn ← match (← get).sel[a]? with
        | some false => newNode (.fn t r o)
        | some true => newNode (.fn t o r)
        | none => newNode (.fn t r r)
      unify (← tyVar f) fn
      modify fun s => { s with apps := s.apps.insert f r }
      pure r
  | .letv x e b => do
      unify (← tyVar x) (← infer codeTy codes e)
      if let some r ← selOf e then modify fun s => { s with sel := s.sel.insert x r }
      infer codeTy codes b
  | .letpair x y p b => do
      unify (← tyVar p) (← newNode (.pair (← tyVar x) (← tyVar y)))
      infer codeTy codes b
  | .case s x b₁ y b₂ => do
      unify (← tyVar s) (← newNode (.sum (← tyVar x) (← tyVar y)))
      let n₁ ← infer codeTy codes b₁
      let n₂ ← infer codeTy codes b₂
      unify n₁ n₂
      pure n₁
  | .copy x x' b => do
      unify (← tyVar x') (← tyVar x)
      if let some r := (← get).sel[x]? then modify fun s => { s with sel := s.sel.insert x' r }
      infer codeTy codes b
  | .drop _ b => infer codeTy codes b

/-- A code of kind `sel`: the scrutinee, and the arms. -/
def Code.selShape? (c : Code) : Option (Var × Var × Tm × Var × Tm) :=
  match c.body with
  | .letv s (.var p) (.case s' x b₁ y b₂) =>
    if p == c.param && s == s' then some (s, x, b₁, y, b₂) else none
  | _ => none

/-- A code of kind `fwd`: the argument, the function, and the term computing it. -/
def Code.fwdShape? (c : Code) : Option (Var × Var × Tm) :=
  match c.body with
  | .letv a (.var p) (.letv f t (.app f' a')) =>
    if p == c.param && f == f' && a == a' then some (a, f, t) else none
  | _ => none

def Code.kind (c : Code) : CodeKind :=
  match c.selShape?, c.fwdShape? with
  | some _, _ => .sel
  | none, some _ => .fwd
  | none, none => .plain

/-- Constrain code `k`'s type `codeTy[k]` by its body. -/
def inferCode (codeTy : Array Nat) (codes : Array Code) (k : Nat) (c : Code) : TM Unit := do
  let self := codeTy[k]!
  let p ← tyVar c.param
  match c.selShape?, c.fwdShape? with
  | some (s, x, b₁, y, b₂), _ =>
    unify (← tyVar s) p
    unify p (← newNode (.sum (← tyVar x) (← tyVar y)))
    let n₁ ← infer codeTy codes b₁
    let n₂ ← infer codeTy codes b₂
    unify self (← newNode (.fn p n₁ n₂))
  | none, some (a, f, t) =>
    unify (← tyVar a) p
    let n ← infer codeTy codes t
    unify (← tyVar f) n
    unify n (← newNode (.fn p (← newNode .any) (← newNode .any)))
    unify self n
    let r ← newNode .any
    modify fun s => { s with apps := s.apps.insert f r }
  | none, none =>
    let r ← infer codeTy codes c.body
    unify self (← newNode (.fn p r r))

/-! ### Layouts -/

/-- The layout types of a program, resolved, with their layouts. -/
structure Types where
  /-- Every node's representative. -/
  rep : Array Nat
  /-- Every representative's type, its children representatives. -/
  shape : Array LTy
  /-- The fields `(n, i)` stored behind a pointer. -/
  boxed : Std.HashSet (Nat × Nat)
  /-- Every representative's width in words. -/
  width : Array Nat
  /-- Every representative's triviality. -/
  trivial : Array Bool
  /-- Every cell class's width: its widest contents. -/
  cellWidth : Std.HashMap Nat Nat
  varTy : Std.HashMap Var Nat
  cons : Std.HashMap Var Nat
  apps : Std.HashMap Var Nat
  codeTy : Array Nat
  /-- `main`'s type. -/
  mainTy : Nat
  /-- The type of the program's value: `main`'s, or `fin`'s answer when `main` returns a loop. -/
  resTy : Nat

namespace Types

def r (T : Types) (n : Nat) : Nat := T.rep[n]?.getD n
def ty (T : Types) (n : Nat) : LTy := T.shape[T.r n]?.getD .any
def words (T : Types) (n : Nat) : Nat := T.width[T.r n]?.getD 0
def triv (T : Types) (n : Nat) : Bool := T.trivial[T.r n]?.getD true
def isBoxed (T : Types) (n i : Nat) : Bool := T.boxed.contains (T.r n, i)

/-- Field `i` of the pair or sum `n`: its type, and whether it is behind a pointer. -/
def field (T : Types) (n i : Nat) : Nat × Bool :=
  (((T.ty n).fields[i]?).getD n, T.isBoxed n i)

/-- The words field `i` of `n` occupies. -/
def fieldWords (T : Types) (n i : Nat) : Nat :=
  let (c, b) := T.field n i
  if b then 1 else T.words c

/-- The words of a cell, or of an array slot, of the location type `n`: its class's width. -/
def cellWords (T : Types) (n : Nat) : Nat :=
  match T.ty n with
  | .loc _ c => T.cellWidth.getD c 0
  | _ => 0

/-- The words a closure of type `n` answers with: the wider of its two answers. -/
def answerWords (T : Types) (n : Nat) : Nat :=
  match T.ty n with
  | .fn _ c d => max (T.words c) (T.words d)
  | _ => 0

end Types

/-- Resolve the unifier's state: representatives, and one depth-first search over the pair and
sum edges, whose back edges are the boxed fields; widths and triviality are computed as each
node finishes. -/
def resolve (s : TState) (codeTy : Array Nat) (mainTy resTy : Nat) : Types := Id.run do
  let n := s.nodes.size
  let rep := (Array.range n).map (findIn s.parent)
  let shape := (Array.range n).map fun i =>
    match s.nodes[rep[i]!]! with
    | .pair a b => LTy.pair rep[a]! rep[b]!
    | .sum a b => .sum rep[a]! rep[b]!
    | .fn a c d => .fn rep[a]! rep[c]! rep[d]!
    | .loc a c => .loc rep[a]! (findIn s.classes c)
    | t => t
  let mut color : Array Nat := Array.replicate n 0
  let mut width : Array Nat := Array.replicate n 0
  let mut trivial : Array Bool := Array.replicate n true
  let mut boxed : Std.HashSet (Nat × Nat) := {}
  for root in [0:n] do
    if rep[root]! != root || color[root]! != 0 then continue
    let mut stack : List (Nat × Nat) := [(root, 0)]
    color := color.set! root 1
    for _ in [0:4 * n + 4] do
      match stack with
      | [] => break
      | (v, i) :: rest =>
        let fs := shape[v]!.fields
        match fs[i]? with
        | some c =>
          stack := (v, i + 1) :: rest
          if color[c]! == 1 then boxed := boxed.insert (v, i)
          else if color[c]! == 0 then
            color := color.set! c 1
            stack := (c, 0) :: stack
        | none =>
          let fw (j : Nat) (c : Nat) : Nat := if boxed.contains (v, j) then 1 else width[c]!
          let ft (j : Nat) (c : Nat) : Bool := !boxed.contains (v, j) && trivial[c]!
          let (w, t) := match shape[v]! with
            | .any | .unit => (0, true)
            | .int _ | .loc .. => (1, true)
            | .fn .. => (1, false)
            | .pair a b => (fw 0 a + fw 1 b, ft 0 a && ft 1 b)
            | .sum a b => (1 + max (fw 0 a) (fw 1 b), ft 0 a && ft 1 b)
          width := width.set! v w
          trivial := trivial.set! v t
          color := color.set! v 2
          stack := rest
  let mut cellWidth : Std.HashMap Nat Nat := {}
  for v in [0:n] do
    if let .loc a c := shape[v]! then
      cellWidth := cellWidth.insert c (max (cellWidth.getD c 0) width[a]!)
  return { rep, shape, boxed, width, trivial, cellWidth, varTy := s.varTy, cons := s.cons,
           apps := s.apps, codeTy, mainTy, resTy }

/-- The layout types of a program. -/
def Prog.types (p : Prog) : Except String Types := do
  let act : TM (Array Nat × Nat × Nat) := do
    let codeTy ← p.codes.mapM fun _ => newNode .any
    for (c, k) in p.codes.toList.zipIdx do inferCode codeTy p.codes k c
    let m ← infer codeTy p.codes p.main
    let res ← match p.fin with
      | none => pure m
      | some c => do
        -- `main` is a loop: on `inl ()` it answers `inl r` or `inr` of the loop again.
        let r ← newNode .any
        let sel ← newNode (.sum (← unitT) (← unitT))
        unify m (← newNode (.fn sel (← newNode (.sum r m)) (← newNode .any)))
        let e ← newNode .any
        unify codeTy[c]! (← newNode (.fn r e e))
        pure e
    pure (codeTy, m, res)
  let ((codeTy, m, res), s) ← act.run {}
  pure (resolve s codeTy m res)

end Backend.Clos

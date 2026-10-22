import Std.Data.HashMap
import Std.Data.HashSet
import Backend2.Syntax

/-!
# Backend2 — frame slots for lent cells  `[spec §35]`

A cell allocated for one lend (`TExpr.lendCell`: `withbor (alloc v) cb`, the LIR's
`Op.allocLent`) is a slot of its function's frame when its owner, the variable the LIR hands
back from the lend, is freed by that function: the LIR consumes every variable exactly once, so
following the owner through the moves of the lend (`lend`'s and `swap`'s pairs, bindings, pairs
taken apart) reaches its one consumer. When that consumer is `free`, the slot's life ends there;
when it is anything else (a call, a closure, the function's answer), the cell stays on the heap.

The lend's callback cannot keep the borrow past the lend (its lifetime is the lend's, `withbor`'s
`'x`), so a slot whose owner is freed in the frame is not read after the frame is given back.
-/

namespace Backend2.Frames
open Backend2

/-- How a variable is consumed, as far as the owner's path needs. -/
inductive Use where
  /-- `letv y (var x)`, or `x` a field of the pair `y` builds (`k` the field). -/
  | moved (y : Var) (k : Option Nat)
  /-- `letv y (op x …)`: `lend`, `relend`, `swap`, `take` answer `(x, …)` in `y`; `put` answers
  `x` itself. -/
  | through (y : Var) (pairs : Bool)
  /-- `letpair a b x`. -/
  | split (a b : Var)
  /-- The `k`-th argument of a direct call of `fn`. -/
  | called (fn k : Nat)
  | freed
  | other

/-- Each variable's consumer in a term. -/
def usesOf : Nat → Tm → Option Var → Std.HashMap Var Use → Std.HashMap Var Use
  | 0, _, _, m => m
  | f + 1, t, dst, m =>
    let set (x : Var) (u : Use) (m : Std.HashMap Var Use) := m.insert x u
    let others (xs : List Var) (m : Std.HashMap Var Use) := xs.foldl (fun m x => m.insert x .other) m
    match t with
    | .var x => match dst with
      | some y => set x (.moved y none) m
      | none => set x .other m
    | .pair a b => match dst with
      | some y => set b (.moved y (some 1)) (set a (.moved y (some 0)) m)
      | none => others [a, b] m
    | .prim op as => match op, as, dst with
      | .free, [x], _ => set x .freed m
      | .allocLent, [x], _ => set x .other m
      | .lend, x :: rest, some y | .relend, x :: rest, some y | .swap, x :: rest, some y
      | .take, x :: rest, some y | .size, x :: rest, some y => others rest (set x (.through y true) m)
      | .put, x :: rest, some y => others rest (set x (.through y false) m)
      | _, as, _ => others as m
    | .inj _ a => set a .other m
    | .clos _ env => others env m
    | .app g a => others [g, a] m
    | .app0 g | .sel g _ => set g .other m
    | .call fn as => as.zipIdx.foldl (fun m (x, k) => set x (.called fn k) m) m
    | .letv x e b => usesOf f b dst (usesOf f e (some x) m)
    | .letpair x y p b => usesOf f b dst (set p (.split x y) m)
    | .case s _ b₁ _ b₂ => usesOf f b₂ dst (usesOf f b₁ dst (set s .other m))
    | .absurd s => set s .other m
    | .copy x _ b => usesOf f b dst (set x .other m)
    | .drop x b => usesOf f b dst (set x .other m)
    | .unit | .lit _ => m

/-- The owner `x` reaches a `free` in the same term. `field` is the component of `x` the owner
is, when `x` is a pair holding it. -/
def freedIn (uses : Std.HashMap Var Use) : Nat → Var → Option Nat → Bool
  | 0, _, _ => false
  | f + 1, x, field => match uses[x]?, field with
    | some .freed, none => true
    | some (.moved y k), none => freedIn uses f y k
    | some (.moved y none), some k => freedIn uses f y (some k)
    | some (.through y true), none => freedIn uses f y (some 0)
    | some (.through y false), none => freedIn uses f y none
    | some (.split a b), some k => freedIn uses f (if k == 0 then a else b) none
    | _, _ => false

/-- The lent cells' variables whose owner is freed in their function: their cells are frame
slots. -/
def framed (p : Prog) : Std.HashSet Var := Id.run do
  let mut out : Std.HashSet Var := {}
  let bodies := p.main :: p.fns.toList.map (·.body)
  for b in bodies do
    let uses := usesOf (1 <<< 22) b none {}
    for x in allocsOf (1 <<< 22) b [] do
      if freedIn uses 4096 x none then out := out.insert x
  return out
where
  /-- The variables `allocLent` binds in a term, not inside other functions. -/
  allocsOf : Nat → Tm → List Var → List Var
    | 0, _, acc => acc
    | f + 1, t, acc => match t with
      | .letv x (.prim .allocLent _) b => allocsOf f b (x :: acc)
      | .letv _ e b => allocsOf f b (allocsOf f e acc)
      | .letpair _ _ _ b | .copy _ _ b | .drop _ b => allocsOf f b acc
      | .case _ _ b₁ _ b₂ => allocsOf f b₂ (allocsOf f b₁ acc)
      | _ => acc


/-- The cells allocated for one lend (`Op.allocLent`) in the program's functions and `main`: their
variables. -/
def lentCells (p : Prog) : List Var :=
  (p.main :: p.fns.toList.map (·.body)).flatMap fun b => framed.allocsOf (1 <<< 22) b []

/-- The array `x` (or its component `field`) is only read before its destructor: it is lent
shared, its size taken, and then destroyed by a generated destructor (`array_dtor`, or
`array_free`'s loop) or freed. -/
def readOnly (p : Prog) (uses : Std.HashMap Var Use) : Nat → Var → Option Nat → Bool
  | 0, _, _ => false
  | f + 1, x, field => match uses[x]?, field with
    | some (.moved y k), none => readOnly p uses f y k
    | some (.moved y none), some k => readOnly p uses f y (some k)
    | some (.through y true), none =>
      -- A lend must be a shared one: its borrow a family of `imm` leaves.
      let shared := match p.ty[y]? with
        | some (.pair _ (.fam (.imm _))) => true
        | some (.pair _ (.int _)) => true
        | _ => false
      shared && readOnly p uses f y (some 0)
    | some (.split a b), some k => readOnly p uses f (if k == 0 then a else b) none
    | some (.called fn k), none =>
      match p.fns[fn]? with
      | some fd => (fd.name == "array_dtor" && k == 0) || (fd.name == "array_free" && k == 1)
      | none => false
    | _, _ => false

end Backend2.Frames

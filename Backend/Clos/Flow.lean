import Std.Data.HashMap
import Std.Data.HashSet
import Backend.Clos.Types

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
contents of the locations a `load` reads). Their least solution is found by a worklist solver
(below).

The analysis reads `&` as the layout types do (`Backend/Clos/Types.lean`): a code whose body
cases on its parameter (`sel`) has two answers, one per arm, and a call whose argument is a
literal injection takes the answer of that arm only; a code that forwards its parameter to a
function (`fwd`, as `unfold` forwards an observation) answers each projection as the closures it
forwards to do. A call on an argument not known at the call takes both answers.

Everything that calls a closure is a constraint, including what the flat IR's helpers do: `tab`
calls its tabulator, an array's `drop` its consumer, and when `main` returns a loop the entry
drives it. The analysis over-approximates the
closures that reach each call, so a call of one code is a call of that code on every run: the
closure IR's variables are each bound once and consumed once, and a closure's code does not
change once it is built.
-/

namespace Backend.Clos

/-- A set of abstract values. -/
inductive Key where
  | var (x : Var)
  /-- Code `c`'s answer when it is called on `inl ()` (`right = false`) or on `inr ()`. A call
  on an argument not known at the call takes both. -/
  | res (c : Nat) (right : Bool)
  | syn (n : Nat)
  /-- The loops the entry drives. -/
  | drive
  /-- The payloads of every `raise` (§19). -/
  | raised
  /-- The payloads of every `perform` (§19). -/
  | performed
  /-- The answers every `perform` may be resumed with: what a `run` passes in an `inl`. -/
  | answered
  deriving BEq, Hashable, Repr, Inhabited

/-- An abstract value. -/
inductive AVal where
  | clos (c : Nat)
  | pair (a b : Key)
  | inj (right : Bool) (a : Key)
  /-- Variant `t` of an `n`-ary sum. -/
  | con (t : Nat) (a : Key)
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
  /-- The payload of the variants `t` of `k` is in `k'`. -/
  | outN (k : Key) (t : Nat) (k' : Key)
  /-- The closures of `f` are called on `a`, answering into `r`: on `inl ()` or `inr ()`
  (`side`), or on an argument not known at the call. -/
  | app (f a r : Key) (side : Option Bool)
  /-- The closures of `f` are called on `a`, the parameter of the `fwd` code `c`: each answers
  `c`'s answers on either side. -/
  | fwd (f a : Key) (c : Nat)
  /-- The contents of the locations of `l` are in `r`. -/
  | load (l r : Key)
  /-- `v` is in the contents of the locations of `l`. -/
  | store (l v : Key)

structure GState where
  next : Nat := 1
  cons : Array Con := #[]
  /-- Variables bound to a literal injection: `true` for `inr` (`Backend/Clos/Types.lean`,
  `TState.sel`). -/
  sel : Std.HashMap Var Bool := {}

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
  | .alloc, [v] | .scopedAlloc _, [v] => do
      let c ← freshKey
      emit (.sub (.var v) c)
      holding (.loc c)
  | .free, [l] | .scopedFree _, [l] | .load, [l] => do
      let r ← freshKey
      emit (.load (.var l) r)
      pure r
  | .store, [l, v] => do emit (.store (.var l) (.var v)); pure .none
  | .swap, [l, v] | .swapSlot, [l, v] => do
      let old ← freshKey
      emit (.load (.var l) old)
      emit (.store (.var l) (.var v))
      holding (.pair (.var l) old)
  | .tab, [v] | .litTab, [v] => do
      let f ← freshKey
      emit (.proj (.var v) 1 f)
      let c ← freshKey
      emit (.app f .none c none)
      holding (.pair (← holding (.loc c)) .none)
  | .idx, [v] => do
      let h ← freshKey
      emit (.proj (.var v) 0 h)
      let l ← freshKey
      emit (.proj h 0 l)
      holding (.inj false l)
  | .split, [v] => do
      -- Both parts, and the family handed back, are the family's abstract values.
      let h ← freshKey
      emit (.proj (.var v) 0 h)
      let r ← holding (.inj false (← holding (.pair h h)))
      emit (.elem (.inj true h) r)
      pure r
  | .nullLoc, [] => do holding (.loc (← freshKey))
  | .dataAddr _, [] => pure .none
  | .drop, [v] => do
      let f ← freshKey
      emit (.proj (.var v) 0 f)
      let h ← freshKey
      emit (.proj (.var v) 1 h)
      let l ← freshKey
      emit (.proj h 0 l)
      let c ← freshKey
      emit (.load l c)
      emit (.app f c (← freshKey) none)
      pure .none
  | .count, [v] => do
      -- The state is the initial one or any answer of `f`, which it is passed with the index.
      let f ← freshKey
      emit (.proj (.var v) 0 f)
      let r₁ ← freshKey
      emit (.proj (.var v) 1 r₁)
      let r₂ ← freshKey
      emit (.proj r₁ 1 r₂)
      let s₀ ← freshKey
      emit (.proj r₂ 1 s₀)
      let st ← freshKey
      emit (.sub s₀ st)
      let r ← freshKey
      emit (.app f (← holding (.pair .none st)) r none)
      emit (.sub r st)
      pure st
  | .countTry, [v] => do
      -- The state is the initial one or the `inl` of an answer of `f`; the loop answers `inl` of
      -- a state, or an answer of `f`.
      let f ← freshKey
      emit (.proj (.var v) 0 f)
      let r₁ ← freshKey
      emit (.proj (.var v) 1 r₁)
      let r₂ ← freshKey
      emit (.proj r₁ 1 r₂)
      let s₀ ← freshKey
      emit (.proj r₂ 1 s₀)
      let st ← freshKey
      emit (.sub s₀ st)
      let r ← freshKey
      emit (.app f (← holding (.pair .none st)) r none)
      emit (.out r false st)
      let res ← holding (.inj false st)
      emit (.sub r res)
      pure res
  | .io .readByte, [m] | .io .clockNow, [m] => holding (.pair (.var m) .none)
  | .io .writeByte, [p] | .io .writeAll, [p] | .io .clockSleep, [p] => do
      let m ← freshKey
      emit (.proj (.var p) 0 m)
      pure m
  | .io .readInto, [p] => do
      let m ← freshKey
      emit (.proj (.var p) 0 m)
      let f ← freshKey
      emit (.proj (.var p) 1 f)
      holding (.pair m (← holding (.pair f .none)))
  | _, _ => pure .none

/-- The injection a term ends in, when it is a literal one (`Backend/Clos/Types.lean`,
`selOf`). -/
def gselOf : Tm → GM (Option Bool)
  | .inj r _ => pure (some r)
  | .var y => return (← get).sel[y]?
  | .letv _ _ b | .copy _ _ b | .drop _ b => gselOf b
  | _ => pure none

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
      emit (.app (.var f) (.var a) r (← get).sel[a]?)
      pure r
  | .letv x e b => do
      emit (.sub (← gen codes e) (.var x))
      if let some r ← gselOf e then modify fun s => { s with sel := s.sel.insert x r }
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
      if let some r := (← get).sel[x]? then modify fun s => { s with sel := s.sel.insert x' r }
      gen codes b
  | .drop _ b => gen codes b
  | .raise p => do
      emit (.sub (.var p) .raised)
      pure .none
  | .con t _ a => holding (.con t (.var a))
  | .when s t _ x b r => do
      emit (.outN (.var s) t (.var x))
      let k₁ ← gen codes b
      let k₂ ← gen codes r
      let k ← freshKey
      emit (.sub k₁ k)
      emit (.sub k₂ k)
      pure k
  | .absurd _ => pure .none
  | .catch _ b | .catchAll b => do
      -- `inl` of the body's value, or `inr` of a payload it raises.
      let kb ← gen codes b
      let k ← holding (.inj false kb)
      emit (.elem (.inj true .raised) k)
      pure k
  | .fin _ dd b => do
      let kb ← gen codes b
      emit (.app (.var dd) .none (← freshKey) none)
      pure kb
  | .reraise p => do
      emit (.sub (.var p) .raised)
      pure .none
  | .perform p => do
      -- A `perform` answers what its handler resumes it with.
      emit (.sub (.var p) .performed)
      pure .answered
  | .run f a => do
      -- The outcome of a code that may suspend: `inl` of its answer, or `inr` of a payload and
      -- a continuation; an `inl` it is passed is an operation's answer.
      emit (.out (.var a) false .answered)
      let r ← freshKey
      emit (.app (.var f) (.var a) r none)
      let k ← holding (.inj false r)
      emit (.elem (.inj true (← holding (.pair .performed .none))) k)
      pure k
  | .await _ _ => pure .none
  | .hnd .. | .ubind .. => pure .none

/-- The program's constraints. `Capture` lowers handlers and finaliser frames (`hnd`, `ubind`)
before any analysis, into calls of their clauses. -/
def Prog.constraints (p : Prog) : Array Con := Id.run do
  let act : GM Unit := do
    for (c, k) in p.codes.toList.zipIdx do
      match c.selShape?, c.fwdShape? with
      | some (sv, x, b₁, y, b₂), _ =>
        -- A `sel` code answers the two projections by its two arms.
        emit (.sub (.var c.param) (.var sv))
        emit (.out (.var sv) false (.var x))
        emit (.out (.var sv) true (.var y))
        emit (.sub (← gen p.codes b₁) (.res k false))
        emit (.sub (← gen p.codes b₂) (.res k true))
      | none, some (a, f, t) =>
        -- A `fwd` code answers each projection as the function it forwards to does.
        emit (.sub (.var c.param) (.var a))
        emit (.sub (← gen p.codes t) (.var f))
        emit (.fwd (.var f) (.var a) k)
      | none, none =>
        let r ← gen p.codes c.body
        emit (.sub r (.res k false))
        emit (.sub r (.res k true))
    let m ← gen p.codes p.main
    if p.drives then
      -- The entry drives the loop `main` returns: `inr` loops again.
      let loop := Key.drive
      emit (.sub m loop)
      let r ← freshKey
      emit (.app loop .none r none)
      emit (.out r true loop)
  let ((), s) := act.run {}
  return s.cons

/-! ### The solver

A worklist solver over the constraints, indexed by the keys they read (difference propagation,
as for inclusion-based points-to analysis). Keys and abstract values are numbered. Each key
holds its values, the keys it flows into (its `sub` edges, and the edges a guarded
constraint adds once one of its values is known), and the guarded constraints that read it.
When a key gains values, only those values are passed on: along each edge, and to each guarded
constraint, which may add edges. An edge added later carries the key's whole set. So each value
crosses each edge once, and the result is the least solution: every value a key holds is
reached from an `elem` along edges, each of which a constraint forces. -/

/-- A guarded constraint, by the key it reads. -/
inductive Use where
  /-- Component `i` of each pair is in `k'`. -/
  | proj (i : Nat) (k' : Nat)
  /-- The payload of each injection `right` is in `k'`. -/
  | out (right : Bool) (k' : Nat)
  /-- The payload of each variant `t` is in `k'`. -/
  | outN (t : Nat) (k' : Nat)
  /-- Each closure is called on `a`, answering into `r` on `side`, or on either. -/
  | app (a r : Nat) (side : Option Bool)
  /-- Each closure is called on `a`, answering into the `fwd` code `c`'s answers. -/
  | fwd (a : Nat) (c : Nat)
  /-- The contents of each location are in `r`. -/
  | load (r : Nat)
  /-- `x` is in the contents of each location. -/
  | store (x : Nat)

/-- An abstract value over numbered keys. -/
inductive NVal where
  | clos (c : Nat)
  | pair (a b : Nat)
  | inj (right : Bool) (a : Nat)
  | con (t : Nat) (a : Nat)
  | loc (k : Nat)
  deriving BEq, Hashable, Inhabited

/-- The numbering of keys: variables first, then the intermediate keys, then the codes'
answers, then the loop driver's. -/
structure KeyNum where
  vars : Nat
  syns : Nat
  codes : Nat

def KeyNum.size (n : KeyNum) : Nat := n.vars + n.syns + 2 * n.codes + 4

def KeyNum.idx (n : KeyNum) : Key → Nat
  | .var x => x
  | .syn m => n.vars + m
  | .res c r => n.vars + n.syns + 2 * c + (if r then 1 else 0)
  | .drive => n.vars + n.syns + 2 * n.codes
  | .raised => n.vars + n.syns + 2 * n.codes + 1
  | .performed => n.vars + n.syns + 2 * n.codes + 2
  | .answered => n.vars + n.syns + 2 * n.codes + 3

/-- The numbering of the keys of the constraints `cs` of a program of `codes` codes. -/
def KeyNum.of (codes : Nat) (cs : Array Con) : KeyNum := Id.run do
  let mut vars := 0
  let mut syns := 0
  let mut codes := codes
  let see (b : Nat × Nat × Nat) : Key → Nat × Nat × Nat
    | .var x => (max b.1 (x + 1), b.2)
    | .syn m => (b.1, max b.2.1 (m + 1), b.2.2)
    | .res c _ => (b.1, b.2.1, max b.2.2 (c + 1))
    | .drive | .raised | .performed | .answered => b
  let seeV (b : Nat × Nat × Nat) : AVal → Nat × Nat × Nat
    | .clos _ => b
    | .pair a c => see (see b a) c
    | .inj _ a | .con _ a | .loc a => see b a
  for c in cs do
    let b := (vars, syns, codes)
    let b := match c with
      | .elem v k => see (seeV b v) k
      | .sub k k' | .proj k _ k' | .out k _ k' | .outN k _ k' | .load k k' | .store k k' =>
        see (see b k) k'
      | .app f a r _ => see (see (see b f) a) r
      | .fwd f a c => see (see (see b f) a) (.res c false)
    (vars, syns, codes) := b
  return ⟨vars, syns, codes⟩

structure Solver where
  num : KeyNum
  valId : Std.HashMap NVal Nat := {}
  vals : Array NVal := #[]
  /-- Every key's values. -/
  set : Array (Array Nat)
  /-- The values of the keys that hold more than `small` of them, as sets. -/
  bigSet : Std.HashMap Nat (Std.HashSet Nat) := {}
  /-- Every key's values not yet passed on. -/
  delta : Array (Array Nat)
  succ : Array (Array Nat)
  /-- The successors of the keys that have more than `small` of them, as sets. -/
  bigSucc : Std.HashMap Nat (Std.HashSet Nat) := {}
  uses : Array (Array Use)
  /-- The keys with values not yet passed on. -/
  work : Array Nat := #[]

def Solver.empty (num : KeyNum) : Solver :=
  { num, set := .replicate num.size #[], delta := .replicate num.size #[],
    succ := .replicate num.size #[], uses := .replicate num.size #[] }

abbrev SM := StateM Solver

/-- Up to this many values or successors, a key's are searched as an array. -/
def small : Nat := 16

/-- `x` is in the array `xs[k]`, whose set is `big[k]` when it is longer than `small`. -/
def inSmallOrBig (xs : Array (Array Nat)) (big : Std.HashMap Nat (Std.HashSet Nat)) (k x : Nat) :
    Bool :=
  if xs[k]!.size ≤ small then xs[k]!.contains x else (big.getD k {}).contains x

/-- `x` added to the array `xs[k]`, and to `big[k]` when it is longer than `small`. The array is
read and pushed to in place: no reference to it is kept. -/
def pushSmallOrBig (xs : Array (Array Nat)) (big : Std.HashMap Nat (Std.HashSet Nat)) (k x : Nat) :
    Array (Array Nat) × Std.HashMap Nat (Std.HashSet Nat) :=
  let n := xs[k]!.size
  let big := if n < small then big
    else if n == small then
      big.insert k ((xs[k]!.foldl (fun (h : Std.HashSet Nat) y => h.insert y) {}).insert x)
    else big.modify k (·.insert x)
  (xs.modify k (·.push x), big)

def keyOf (k : Key) : SM Nat := return (← get).num.idx k

def valOf (v : NVal) : SM Nat := modifyGet fun s =>
  match s.valId[v]? with
  | some i => (i, s)
  | none => let i := s.vals.size; (i, { s with valId := s.valId.insert v i, vals := s.vals.push v })

def NVal.ofAVal : AVal → SM NVal
  | .clos c => pure (.clos c)
  | .pair a b => return .pair (← keyOf a) (← keyOf b)
  | .inj r a => return .inj r (← keyOf a)
  | .con t a => return .con t (← keyOf a)
  | .loc k => return .loc (← keyOf k)

/-- Add value `v` to key `k`. -/
def addVal (k v : Nat) : SM Unit := modify fun s =>
  if inSmallOrBig s.set s.bigSet k v then s else
  let fresh := s.delta[k]!.isEmpty
  let (set, bigSet) := pushSmallOrBig s.set s.bigSet k v
  { s with set, bigSet, delta := s.delta.modify k (·.push v),
           work := if fresh then s.work.push k else s.work }

/-- The edge `k ⊆ k'`: `k'` gets `k`'s values now and later. -/
def addEdge (k k' : Nat) : SM Unit := do
  if k == k' then return
  let known ← modifyGet fun s => (inSmallOrBig s.succ s.bigSucc k k', s)
  if known then return
  modify fun s =>
    let (succ, bigSucc) := pushSmallOrBig s.succ s.bigSucc k k'
    { s with succ, bigSucc }
  for v in (← get).set[k]! do addVal k' v

/-- What the guarded constraint `u` makes of the value `v`. -/
def fire (codes : Array Code) (u : Use) (v : Nat) : SM Unit := do
  match u, (← get).vals[v]! with
  | .proj i k', .pair a b => addEdge (if i == 0 then a else b) k'
  | .out r k', .inj r' a => if r == r' then addEdge a k'
  | .outN t k', .con t' a => if t == t' then addEdge a k'
  | .app a r side, .clos c =>
    if let some code := codes[c]? then addEdge a (← keyOf (.var code.param))
    match side with
    | some right => addEdge (← keyOf (.res c right)) r
    | none =>
      addEdge (← keyOf (.res c false)) r
      addEdge (← keyOf (.res c true)) r
  | .fwd a k, .clos c =>
    if let some code := codes[c]? then addEdge a (← keyOf (.var code.param))
    addEdge (← keyOf (.res c false)) (← keyOf (.res k false))
    addEdge (← keyOf (.res c true)) (← keyOf (.res k true))
  | .load r, .loc k => addEdge k r
  | .store x, .loc k => addEdge x k
  | _, _ => pure ()

/-- The guarded constraint `u` reads key `k`: now and later. -/
def addUse (codes : Array Code) (k : Nat) (u : Use) : SM Unit := do
  modify fun s => { s with uses := s.uses.modify k (·.push u) }
  for v in (← get).set[k]! do fire codes u v

def addCon (codes : Array Code) : Con → SM Unit
  | .elem v k => do addVal (← keyOf k) (← valOf (← NVal.ofAVal v))
  | .sub k k' => do addEdge (← keyOf k) (← keyOf k')
  | .proj k i k' => do addUse codes (← keyOf k) (.proj i (← keyOf k'))
  | .out k r k' => do addUse codes (← keyOf k) (.out r (← keyOf k'))
  | .outN k t k' => do addUse codes (← keyOf k) (.outN t (← keyOf k'))
  | .app f a r side => do addUse codes (← keyOf f) (.app (← keyOf a) (← keyOf r) side)
  | .fwd f a k => do addUse codes (← keyOf f) (.fwd (← keyOf a) k)
  | .load l r => do addUse codes (← keyOf l) (.load (← keyOf r))
  | .store l x => do addUse codes (← keyOf l) (.store (← keyOf x))

/-- Pass on the new values of one key from the worklist; whether there was one. -/
def propagate (codes : Array Code) : SM Bool := do
  let some k := (← get).work.back? | return false
  let d ← modifyGet fun s => (s.delta[k]!, { s with work := s.work.pop, delta := s.delta.set! k #[] })
  let s ← get
  let succ := s.succ[k]!
  let uses := s.uses[k]!
  for v in d do
    for k' in succ do addVal k' v
    for u in uses do fire codes u v
  return true

/-- The least solution: the solver, or `none` when it is not reached in `fuel` steps. -/
def solve (codes : Array Code) (cs : Array Con) (fuel : Nat) : Option Solver := Id.run do
  let act : SM Bool := do
    for c in cs do addCon codes c
    for _ in [0:fuel] do
      if !(← propagate codes) then return true
    return false
  let (done, s) := act.run (.empty (.of codes.size cs))
  if done then some s else none

/-- The codes of the closures in `k`, in code order. -/
def Solver.codes (s : Solver) (k : Key) : Array Nat :=
  ((s.set[s.num.idx k]?.getD #[]).foldl (fun acc v => match s.vals[v]! with
    | .clos c => acc.push c
    | _ => acc) #[]).qsort (· < ·)

/-- For every call `app f a`, keyed by `f` (which only the call consumes): the codes whose
closures may be called there, in code order; and the codes of the loops the entry drives. With
no solution, no call's codes are known. -/
def Prog.flowAll (p : Prog) : Std.HashMap Var (Array Nat) × Option (Array Nat) := Id.run do
  let cs := p.constraints
  let some S := solve p.codes cs (1 <<< 40) | return ({}, none)
  let mut out : Std.HashMap Var (Array Nat) := {}
  for c in cs do
    match c with
    | .app (.var f) .. | .fwd (.var f) .. => out := out.insert f (S.codes (.var f))
    | _ => pure ()
  return (out, if p.drives then some (S.codes .drive) else none)

/-- For every call `app f a`, keyed by `f`: the codes whose closures may be called there. -/
def Prog.flow (p : Prog) : Std.HashMap Var (Array Nat) := p.flowAll.1

end Backend.Clos

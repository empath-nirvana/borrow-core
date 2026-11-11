import Std.Data.HashMap
import Std.Data.HashSet
import Backend2.Syntax

/-!
# Backend2 — layouts from types  `[spec §35]`

Every LIR variable has its `LTy`, so its representation's structure is known; what the type does
not fix is which closure codes reach a closure value, which decides a closure's width (its
code's tag and the widest environment among the codes that can be there). The layout stage reads
both:

- **Layout nodes.** Each variable's type is laid out as a graph of nodes, one per type former,
  made from its `LTy` (`mkV`): `μ` and `ν` close their cycles (a recursive type is the regular
  tree it unrolls to). Nothing is inferred: every node's former is the type's. A node's children
  are made when they are first read (`shapeOf`), and a node whose children are not made yet joins
  a node of its own type without them: the graph holds about one node per representative and
  variable, not one per former of every variable's type.
- **Closure classes.** The places a closure value moves between (a binding, an argument and its
  parameter, a result, a constructor's field, a cell's contents) are joined (`join`), so a value
  and every place it reaches share one node. The closure nodes are then the classes: a class
  holds the codes whose closures reach it, and their functions share its argument and answer
  nodes. A class is the lambda set of the closures at its places.
- **One box a node** (SPEC §35): a recursive type boxes the fields that close its cycles, the back
  edges of one search over the pair and sum fields, or a sum's payload where that boxes fewer
  (`sumBoxes`). The searches run in the representatives' canonical order (`canonicalOrder`), so
  which field of a cycle is boxed follows from the program and the types, not from how the nodes
  are numbered. A closure class that holds itself among its codes' captured values keeps its
  environment on the heap.
- **Sums** (SPEC §43). A sum is a tag word and its payload's words, padded. One arm of a sum may be
  *merged*: the right arm, else the left, when its field is not boxed and its node is a sum (the
  type's `⊕`, read off the node, so a right-nested chain `A ⊕ (B ⊕ (C ⊕ …))` is one tag word). On
  that arm the sum's words are the arm's own words, padded: its tags are the arm's own `[0, T)`,
  and the other arm is the one tag `T`. A sum whose leaves are each empty or a scalar of at most 32
  bits (`u8`, `i32`, `u32`, `f32`), one of them not empty, is *packed*: one word, `tag << 32 | payload`. A
  packed arm is merged only into a packed sum, whose word is then the arm's word.
- **Cells.** A value in a cell takes the bytes of its type: a byte at `u8`, 4 bytes at `i32` and
  `f32` (L-6), its words otherwise. An allocation is as wide as the widest type of its width
  class, the checker's class rooted at the type it allocates at (`Checked.classAt`, SPEC §57),
  which the allocation carries (`Op.alloc`).
-/

namespace Backend2.Lay
open BoCa

/-- A layout node's former; its children are nodes. -/
inductive NK where
  | unit | zero | unk | opq
  | int (w : Width)
  | pair (a b : Nat)
  | sum (a b : Nat)
  /-- An owned cell, a shared and a unique borrow of one: the contents' node. -/
  | ref (c : Nat)
  | imm (c : Nat)
  | mut (c : Nat)
  /-- A family of leaves: the leaf's node (a pointer's). -/
  | fam (l : Nat)
  /-- A closure class: the codes' kind, their argument and their answers (one, or a `&`'s two). -/
  | clos (k : CodeKind) (param : Option Nat) (res : List Nat) (ev : List Nat)
  deriving Inhabited, BEq, Repr

/-- **What a layout node lays out**: a value type, or the closure class of a computation type, each
under the nodes of the type variables bound around it. -/
inductive Src where
  | v (t : LTy) (env : List Nat)
  | c (k : LCTy) (env : List Nat)
  deriving Inhabited

/-- The type a node lays out, as a value type: a closure class's is its closures'. -/
def Src.ty : Src → LTy
  | .v t _ => t
  | .c k _ => .thunk k

/-- A type with its outer `!`s erased: `!A` is represented as `A`. -/
def stripB : LTy → LTy
  | .bang a => stripB a
  | t => t

mutual
/-- Two value types are equal with every `!` erased (`LTy.sameRep`), within `fuel` formers deep;
`false` past it. -/
def eqUB : Nat → LTy → LTy → Bool
  | 0, _, _ => false
  | f + 1, a, b =>
    match stripB a, stripB b with
    | .unit, .unit | .zero, .zero | .unk, .unk => true
    | .int w, .int w' => w == w'
    | .opq o, .opq o' => o == o'
    | .tvar n, .tvar m => n == m
    | .pair a b, .pair c d | .sum a b, .sum c d => eqUB f a c && eqUB f b d
    | .mu a, .mu c | .ref a, .ref c | .imm a, .imm c | .mut a, .mut c | .fam a, .fam c => eqUB f a c
    | .thunk k, .thunk k' => eqUBC f k k'
    | _, _ => false
/-- Two computation types are equal with every `!` erased, within `fuel` formers deep. -/
def eqUBC : Nat → LCTy → LCTy → Bool
  | 0, _, _ => false
  | f + 1, k, k' =>
    match k, k' with
    | .ret a, .ret b => eqUB f a b
    | .arr a c, .arr b d => eqUB f a b && eqUBC f c d
    | .amp c d, .amp c' d' => eqUBC f c c' && eqUBC f d d'
    | .top, .top => true
    | .nu c, .nu d => eqUBC f c d
    | .ev n a c, .ev m b d => n == m && eqUB f a b && eqUBC f c d
    | _, _ => false
end

mutual
/-- A hash of a value type with every `!` erased. -/
def hashUB : LTy → UInt64
  | .unit => 1
  | .zero => 2
  | .unk => 3
  | .opq o => mixHash 4 (hash o)
  | .int w => mixHash 5 (hash w)
  | .tvar n => mixHash 6 (hash n)
  | .pair a b => mixHash 7 (mixHash (hashUB a) (hashUB b))
  | .sum a b => mixHash 8 (mixHash (hashUB a) (hashUB b))
  | .mu a => mixHash 9 (hashUB a)
  | .ref a => mixHash 10 (hashUB a)
  | .imm a => mixHash 11 (hashUB a)
  | .mut a => mixHash 12 (hashUB a)
  | .fam a => mixHash 13 (hashUB a)
  | .thunk k => mixHash 14 (hashUBC k)
  | .bang a => hashUB a
/-- A hash of a computation type with every `!` erased. -/
def hashUBC : LCTy → UInt64
  | .ret a => mixHash 15 (hashUB a)
  | .arr a k => mixHash 16 (mixHash (hashUB a) (hashUBC k))
  | .amp k k' => mixHash 17 (mixHash (hashUBC k) (hashUBC k'))
  | .top => 18
  | .nu k => mixHash 19 (hashUBC k)
  | .ev n e k => mixHash 20 (mixHash (hash n) (mixHash (hashUB e) (hashUBC k)))
end

/-- A hash of a value type's formers down to `depth`, every `!` erased: equal types have one. -/
def hashTop : Nat → LTy → UInt64
  | 0, _ => 0
  | d + 1, t =>
    match stripB t with
    | .pair a b => mixHash 7 (mixHash (hashTop d a) (hashTop d b))
    | .sum a b => mixHash 8 (mixHash (hashTop d a) (hashTop d b))
    | .mu a => mixHash 9 (hashTop d a)
    | .ref a => mixHash 10 (hashTop d a)
    | .imm a => mixHash 11 (hashTop d a)
    | .mut a => mixHash 12 (hashTop d a)
    | .fam a => mixHash 13 (hashTop d a)
    | .thunk _ => 14
    | t => hashUB t

/-- A value type as a key up to its `!`s: two keys are one when their types are equal with every
`!` erased. -/
structure UB where
  t : LTy

instance : BEq UB := ⟨fun a b => eqUB 4096 a.t b.t⟩
instance : Hashable UB := ⟨fun a => hashUB a.t⟩

structure GState where
  nodes : Array NK := #[]
  parent : Array Nat := #[]
  /-- What each node lays out. -/
  src : Array Src := #[]
  /-- The nodes whose children are not made yet (`shapeOf` makes them): each such node's shape is
  read off its type when it is needed. -/
  pend : Array Bool := #[]
  /-- Each closure class's codes (at its representative). -/
  codes : Std.HashMap Nat (List Nat) := {}
  varNode : Std.HashMap Var Nat := {}
  fnRet : Std.HashMap Nat Nat := {}
  /-- The joins left to do: a work list, so that joining recursive nodes terminates. -/
  todo : List (Nat × Nat) := []
  /-- Each stack machine's frame node (SPEC §52): every frame of it is one cell's node, as the
  frames pass through the stack. -/
  frames : Std.HashMap Nat Nat := {}
  /-- Each site's `κ` region's contents node (SPEC §52). -/
  regions : Std.HashMap Nat Nat := {}

abbrev GM := StateT GState (Except String)

def findIn (parent : Array Nat) : Nat → Nat → Nat
  | 0, i => i
  | f + 1, i => let p := parent[i]!; if p == i then i else findIn parent f p

/-- The representative of `i`, compressing the path to it. -/
def find (i : Nat) : GM Nat := do
  let r := findIn (← get).parent (← get).parent.size i
  -- Path compression: every node on the way points at the representative.
  let mut j := i
  for _ in [0:64] do
    let p := (← get).parent[j]!
    if p == j || p == r then break
    modify fun s => { s with parent := s.parent.set! j r }
    j := p
  return r

/-- A new node of `s`: with shape `k`, or with `pending` its children not made yet. -/
def newNode (k : NK) (s : Src) (pending : Bool) : GM Nat := modifyGet fun st =>
  (st.nodes.size, { st with nodes := st.nodes.push k, parent := st.parent.push st.nodes.size,
                            src := st.src.push s, pend := st.pend.push pending })

/-- **The node of a value type** under `env`, the nodes of the type variables bound around it: a
leaf's shape is made at once, any other node's children when they are needed (`shapeOf`). `!A`
is represented as `A`, and a type variable is its binder's node. -/
def mkV (env : List Nat) : LTy → GM Nat
  | .bang a => mkV env a
  | .thunk k => match k with
    | .top => newNode .unit (.c .top []) false
    | k => newNode .unit (.c k env) true
  | .tvar n =>
    match env[n]? with
    | some i => pure i
    | none => throw s!"layout: a free type variable {n}"
  | t@.unit => newNode .unit (.v t []) false
  | t@.zero => newNode .zero (.v t []) false
  | t@.unk => newNode .unk (.v t []) false
  | t@(.opq _) => newNode .opq (.v t []) false
  | t@(.int w) => newNode (.int w) (.v t []) false
  | t => newNode .unit (.v t env) true

/-- The node of what running a closure of `k` answers. -/
def mkR (env : List Nat) (k : LCTy) : GM Nat :=
  match k with
  | .ret a => mkV env a
  | k => mkV env (.thunk k)

mutual
/-- The shape of node `i`, which lays out the value type `t` under `env`: its children's nodes
made. `μX. A` is the node `A` makes with `X` that node itself. -/
def expandV (i : Nat) : Nat → List Nat → LTy → GM NK
  | 0, _, _ => throw "layout: a type too deep"
  | f + 1, env, t =>
    match t with
    | .unit => pure .unit
    | .zero => pure .zero
    | .unk => pure .unk
    | .opq _ => pure .opq
    | .int w => pure (.int w)
    | .pair a b => do return .pair (← mkV env a) (← mkV env b)
    | .sum a b => do return .sum (← mkV env a) (← mkV env b)
    | .ref a => do return .ref (← mkV env a)
    | .imm a => do return .imm (← mkV env a)
    | .mut a => do return .mut (← mkV env a)
    | .fam l => do return .fam (← mkV env l)
    | .mu a => expandV i f (i :: env) a
    | .bang a => expandV i f env a
    | .thunk k => expandC i f env k
    | .tvar n =>
      if env[n]? == some i then pure .unit
      else throw s!"layout: a recursive type that is its variable {n}"
/-- The shape of node `i`, the closure class of `k` under `env`. `U(νX. C)` is the closure node
`C` makes with `U X` that node itself. -/
def expandC (i : Nat) : Nat → List Nat → LCTy → GM NK
  | 0, _, _ => throw "layout: a type too deep"
  | f + 1, env, k =>
    match k with
    | .nu c => expandC i f (i :: env) c
    | .ret a => do return .clos .unit none [← mkV env a] []
    | .arr a c => do
      let x ← mkV env a
      -- The evidence parameters after the argument [spec §71].
      let (es, c) := c.stripEv
      let r ← mkR env c
      return .clos .lam (some x) [r] (← es.mapM fun (_, e) => mkV env e)
    | .amp c d => do return .clos .amp none [← mkR env c, ← mkR env d] []
    | .ev n e c => do
      -- A closure of `F_Σ A` taking its evidence [spec §71]: a `unit` code with evidence
      -- parameters.
      let (es, c) := (LCTy.ev n e c).stripEv
      let .ret a := c | throw "layout: evidence before a closure that is not `F A`"
      let r ← mkV env a
      return .clos .unit none [r] (← es.mapM fun (_, e) => mkV env e)
    | .top => pure .unit
end

/-- **The shape of node `i`'s representative**, its children made the first time it is read. -/
def shapeOf (i : Nat) : GM NK := do
  let r ← find i
  let s ← get
  if !s.pend[r]! then return s.nodes[r]!
  let k ← match s.src[r]! with
    | .v t env => expandV r 4096 env t
    | .c c env => expandC r 4096 env c
  modify fun s => { s with nodes := s.nodes.set! r k, pend := s.pend.set! r false }
  pure k

/-- Two nodes lay out one type under one environment: equal with every `!` erased, each type
variable's node one representative. -/
def sameSrc (a b : Src) : GM Bool := do
  let envEq (e e' : List Nat) : GM Bool := do
    unless e.length == e'.length do return false
    for (x, y) in e.zip e' do
      unless (← find x) == (← find y) do return false
    return true
  match a, b with
  | .v t e, .v t' e' => if eqUB 4096 t t' then envEq e e' else pure false
  | .c k e, .c k' e' => if eqUBC 4096 k k' then envEq e e' else pure false
  | _, _ => pure false

/-- The node of a variable, made from its type the first time. -/
def nodeOfVar (ty : Var → Except String LTy) (x : Var) : GM Nat := do
  match (← get).varNode[x]? with
  | some i => pure i
  | none =>
    let t ← match ty x with
      | .ok t => pure t
      | .error e => throw e
    let i ← mkV [] t
    modify fun s => { s with varNode := s.varNode.insert x i }
    pure i


/-! ### Joining the places a value moves between -/

/-- Join two nodes and, recursively, their children: one representation. -/
def join (a b : Nat) : GM Unit := do
  modify fun s => { s with todo := (a, b) :: s.todo }
  let mut steps := 0
  while true do
    steps := steps + 1
    if steps > 10000000 then throw "layout: joining does not end"
    match (← get).todo with
    | [] => break
    | (x, y) :: rest =>
      modify fun s => { s with todo := rest }
      let rx ← find x
      let ry ← find y
      if rx == ry then continue
      let sx := (← get).src[rx]!
      let sy := (← get).src[ry]!
      -- A node whose children are not made yet, of the other's type: the other's layout, its
      -- children those the other's type makes, so joining them joins no two other nodes.
      let px := (← get).pend[rx]!
      let py := (← get).pend[ry]!
      if (px || py) && (← sameSrc sx sy) then
        modify fun s => { s with parent := if px then s.parent.set! rx ry else s.parent.set! ry rx }
        continue
      let kx ← shapeOf rx
      let ky ← shapeOf ry
      let cs := (← get).codes.getD rx [] ++ (← get).codes.getD ry []
      let ox := sx.ty
      let oy := sy.ty
      modify fun s => { s with parent := s.parent.set! ry rx, codes := (s.codes.erase ry).insert rx cs }
      let more : List (Nat × Nat) ← match kx, ky with
        | .pair a b, .pair c d | .sum a b, .sum c d => pure [(a, c), (b, d)]
        | .ref a, .ref c | .imm a, .imm c | .mut a, .mut c | .fam a, .fam c => pure [(a, c)]
        | .ref a, .imm c | .ref a, .mut c | .imm a, .ref c | .mut a, .ref c
        | .imm a, .mut c | .mut a, .imm c => pure [(a, c)]
        | .clos k p r e, .clos k' p' r' e' =>
          if k != k' || r.length != r'.length || e.length != e'.length then
            throw s!"layout: closures of different kinds joined ({reprStr k} {ox} codes {cs}, {reprStr k'} {oy})"
          let ps := match p, p' with
            | some a, some c => [(a, c)]
            | _, _ => []
          pure (ps ++ r.zip r' ++ e.zip e')
        -- A capability's contents, an opaque host value, is held as the word the extern stores.
        | .opq, .int _ | .int _, .opq => pure []
        | k, k' =>
          if k == k' then pure [] else
          throw s!"layout: a {reprStr k |>.take 40} joined with a {reprStr k' |>.take 40}"
      -- The class's former, whichever node led it: an opaque value over an integer, an owned
      -- cell over a unique borrow over a shared one.
      let rank : NK → Nat
        | .opq | .ref _ => 2
        | .mut _ => 1
        | _ => 0
      if rank ky > rank kx then
        let k : NK := match ky, kx with
          | .opq, _ => .opq
          | .ref _, .ref a | .ref _, .imm a | .ref _, .mut a => .ref a
          | .mut _, .imm a => .mut a
          | _, k => k
        modify fun s => { s with nodes := s.nodes.set! rx k }
      modify fun s => { s with todo := more ++ s.todo }

/-- Join the contents `c` of a cell with a value read from it through `Imm̲` (`load`): where the
reading is the contents' former, as `join`; a pointer read as a shared one; a closure read as
`Unk`, not joined. -/
def joinRe (c v : Nat) : GM Unit := do
  let mut todo : List (Nat × Nat) := [(c, v)]
  let mut seen : Std.HashSet (Nat × Nat) := {}
  for _ in [0:1000000] do
    match todo with
    | [] => return
    | (x, y) :: rest =>
      todo := rest
      let rx ← find x
      let ry ← find y
      if rx == ry || seen.contains (rx, ry) then continue
      seen := seen.insert (rx, ry)
      let kx ← shapeOf rx
      let ky ← shapeOf ry
      match kx, ky with
      | .pair a b, .pair c d | .sum a b, .sum c d => todo := (a, c) :: (b, d) :: todo
      | .ref a, .imm c | .mut a, .imm c | .imm a, .imm c => join a c
      | .fam a, .fam c => todo := (a, c) :: todo
      | .clos .., .unk | .opq, .unk => pure ()
      -- `Tok`'s cell (`ofV`: `Ref 1`) read through `Imm̲`: discarded, `Imm̲ 'b Tok = Unk`.
      | .ref _, .unk => pure ()
      | _, _ => join rx ry
  throw "layout: a reborrowed read too deep"

/-- The class of a closure node: its children. -/
def closOf (i : Nat) : GM (CodeKind × Option Nat × List Nat) := do
  match ← shapeOf i with
  | .clos k p r _ => pure (k, p, r)
  | k => throw s!"layout: a call of a non-closure node {reprStr k |>.take 40}"

/-- The evidence parameters' nodes of a closure class [spec §71]. -/
def closEvOf (i : Nat) : GM (List Nat) := do
  match ← shapeOf i with
  | .clos _ _ _ e => pure e
  | k => throw s!"layout: a call of a non-closure node {reprStr k |>.take 40}"

def childrenOf (i : Nat) : GM NK := shapeOf i


/-! ### The places of a program -/

structure Places where
  p : Prog
  /-- The class each code is in, once a closure of it is built. -/
  codeClass : Std.HashMap Nat Nat := {}

def tyOfL (p : Prog) (x : Var) : Except String LTy :=
  match p.ty[x]? with
  | some t => .ok t
  | none => .error s!"layout: variable x{x} has no type"

/-- The node of function `fn`'s answer. -/
def fnRetNode (p : Prog) (fn : Nat) : GM Nat := do
  match (← get).fnRet[fn]? with
  | some i => pure i
  | none =>
    let some f := p.fns[fn]? | throw s!"layout: no function f{fn}"
    let i ← mkV [] f.ret
    modify fun s => { s with fnRet := s.fnRet.insert fn i }
    pure i

/-- Add code `c` to the class `cls`, joining its functions' parameters and answers with the
class's and the captured values with the closure's. -/
def addCode (p : Prog) (cc : Std.HashMap Nat Nat) (cls : Nat) (c : Nat) (env : List Var) :
    GM (Std.HashMap Nat Nat) := do
  let nv := nodeOfVar (tyOfL p)
  let r ← find cls
  modify fun s => { s with codes := s.codes.insert r ((s.codes.getD r []) ++ [c]) }
  let some code := p.codes[c]? | throw s!"layout: no code c{c}"
  let (k, param, res) ← closOf cls
  for (fn, j) in code.fns.zipIdx do
    let some f := p.fns[fn]? | throw s!"layout: no function f{fn}"
    let envPs := f.params.take env.length
    for (x, y) in env.zip envPs do join (← nv x) (← nv y)
    if k == .lam then
      match param, f.params[env.length]? with
      | some pn, some a => join pn (← nv a)
      | _, _ => throw "layout: a lam code without its argument"
    match res[j]? with
    | some rn => join rn (← fnRetNode p fn)
    | none => throw "layout: a code's component past its class's"
    let evn ← closEvOf cls
    let evPs := f.params.drop (f.params.length - f.evs)
    if evPs.length != evn.length then throw "layout: a code's evidence parameters are not its class's"
    for (x, en) in evPs.zip evn do join (← nv x) en
  match cc[c]? with
  | some other => join cls other; pure cc
  | none => pure (cc.insert c cls)

/-- The places a term's value moves to `dst`, and within it. -/
def walk (p : Prog) : Nat → Std.HashMap Nat Nat → Tm → Nat → GM (Std.HashMap Nat Nat)
  | 0, _, _, _ => throw "layout: a term too deep"
  | f + 1, cc, t, dst => do
  let nv := nodeOfVar (tyOfL p)
  let kid (i : Nat) (k : Nat) : GM Nat := do
    match ← childrenOf i, k with
    | .pair a _, 0 | .sum a _, 0 => pure a
    | .pair _ b, _ | .sum _ b, _ => pure b
    | .ref c, _ | .imm c, _ | .mut c, _ | .fam c, _ => pure c
    | k', _ => throw s!"layout: no child {k} of a {reprStr k' |>.take 40}"
  match t with
  | .var x => join dst (← nv x); pure cc
  | .unit | .lit _ => pure cc
  | .pair a b => do join (← kid dst 0) (← nv a); join (← kid dst 1) (← nv b); pure cc
  | .inj r a => do join (← kid dst (if r then 1 else 0)) (← nv a); pure cc
  | .clos c env => addCode p cc dst c env
  | .app g a => do
    let (_, param, res) ← closOf (← nv g)
    if let some pn := param then join pn (← nv a)
    join dst (res.headD dst); pure cc
  | .app0 g => do
    let (_, _, res) ← closOf (← nv g)
    join dst (res.headD dst); pure cc
  | .sel g j => do
    let (_, _, res) ← closOf (← nv g)
    join dst (res.getD j dst); pure cc
  | .appE g a j ev => do
    let (_, param, res) ← closOf (← nv g)
    if let (some pn, some a) := (param, a) then join pn (← nv a)
    for (x, en) in ev.zip (← closEvOf (← nv g)) do join (← nv x) en
    join dst (res.getD j dst); pure cc
  | .call fn as => do
    let some fd := p.fns[fn]? | throw s!"layout: no function f{fn}"
    for (x, y) in as.zip fd.params do join (← nv x) (← nv y)
    join dst (← fnRetNode p fn); pure cc
  | .prim op as => do
    let a (i : Nat) : GM Nat := do nv (as.getD i 0)
    match op with
    | .alloc _ | .allocLent _ _ => join (← kid dst 0) (← a 0)
    | .free => join dst (← kid (← a 0) 0)
    | .swap => do
      join (← kid (← kid dst 0) 0) (← a 1)
      join (← kid dst 1) (← kid (← a 0) 0)
    | .lend _ => do
      join (← kid dst 0) (← a 0)
      join (← kid (← kid dst 1) 0) (← kid (← a 0) 0)
    | .relend => do join (← kid dst 0) (← a 0); join (← kid dst 1) (← a 0)
    | .load => joinRe (← kid (← a 0) 0) dst
    | .take => do join (← kid dst 0) (← a 0); join (← kid dst 1) (← kid (← a 0) 0)
    | .put => do join (← kid (← a 0) 0) (← a 1); join dst (← a 0)
    | .slotPut => do join (← kid (← kid (← a 0) 0) 0) (← a 2); join dst (← a 0)
    | .slotTake => do
      join (← kid dst 0) (← a 0)
      join (← kid dst 1) (← kid (← kid (← a 0) 0) 0)
    | .size => join (← kid dst 0) (← a 0)
    | .idx _ => join (← kid dst 0) (← kid (← a 0) 0)
    | .split _ => do
      let l ← kid dst 0
      join (← kid l 0) (← a 0); join (← kid l 1) (← a 0); join (← kid dst 1) (← a 0)
    | .replace => do
      join (← kid dst 0) (← a 0)
      let c ← kid (← kid (← a 0) 0) 0
      let o ← kid dst 1
      join (← kid o 0) c; join (← kid o 1) (← a 2); join c (← a 2)
    | .swapSlots => join dst (← a 0)
    | .tab fi | .tabLit fi .. => do
      let some fd := p.fns[fi]? | throw s!"layout: no function f{fi}"
      match fd.params with
      | [pf, pa, _, _] => join (← a 0) (← nv pf); join dst (← nv pa)
      | _ => throw "layout: a tab loop's parameters"
      join dst (← fnRetNode p fi)
    | .roll | .unroll => join dst (← a 0)
    | .framePush m _ | .frameTop m _ => do
      let c ← kid dst 0
      match (← get).frames[m]? with
      | some fn => join fn c
      | none => modify fun s => { s with frames := s.frames.insert m c }
    | .framePut => join (← kid (← a 0) 0) (← a 1)
    | .kappaPut s | .kappaTake s => do
      let c ← match op with
        | .kappaPut _ => a 1
        | _ => kid dst 1
      match (← get).regions[s]? with
      | some r => join r c
      | none => modify fun st => { st with regions := st.regions.insert s c }
    | .io .readByte | .io .clockNow => join (← kid dst 0) (← a 0)
    | .io .writeByte | .io .writeAll | .io .clockSleep => join dst (← kid (← a 0) 0)
    | .io .readInto => do
      join (← kid dst 0) (← kid (← a 0) 0)
      join (← kid (← kid dst 1) 0) (← kid (← a 0) 1)
    | _ => pure ()
    pure cc
  | .letv x e b => do
    let cc ← walk p f cc e (← nv x)
    walk p f cc b dst
  | .letpair x y q b => do
    let n ← nv q
    join (← kid n 0) (← nv x); join (← kid n 1) (← nv y)
    walk p f cc b dst
  | .case sv x b₁ y b₂ => do
    let n ← nv sv
    join (← kid n 0) (← nv x); join (← kid n 1) (← nv y)
    let cc ← walk p f cc b₁ dst
    walk p f cc b₂ dst
  | .absurd _ => pure cc
  | .copy _ x x' b => do join (← nv x) (← nv x'); walk p f cc b dst
  | .consume _ _ b | .abandon _ _ b => walk p f cc b dst

-- UNPROVED: that the closure classes hold every code whose closure can reach each place. It
-- should hold because `walk` joins the two sides of every move a closure makes: a binding, a
-- copy, an argument, an answer, a constructor's field, a cell's contents. It is not a typing fact
-- (the typed term gives a closure's type, not its λ), and the operations `walk` passes over
-- (`| _ => pure ()`) are taken to move no closure. If a code is missing from a class, a call
-- through the class's dispatcher traps, and the class's width is too narrow for the closure.
-- The result is checked on every compile (`Backend2/LayoutCheck.lean`, `checkedLayouts` in
-- `Backend2/Driver.lean`): every pair of places `walk` joins is one node, and every closure's code
-- is in its node's class. A move that both `walk` and the check pass over is not seen.
/-- Every place of the program, joined. -/
def places (p : Prog) : Except String (GState × Nat) := do
  let act : GM Nat := do
    let mut cc : Std.HashMap Nat Nat := {}
    for (fd, i) in p.fns.toList.zipIdx do
      for x in fd.params do let _ ← nodeOfVar (tyOfL p) x
      cc ← walk p (1 <<< 22) cc fd.body (← fnRetNode p i)
    let m ← mkV [] p.mainTy
    let _ ← walk p (1 <<< 22) cc p.main m
    -- Every node a variable, an answer, `main`, a frame or a region reaches has its children.
    let st ← get
    let mut todo : List Nat := st.varNode.fold (fun l _ i => i :: l) [] ++
      st.fnRet.fold (fun l _ i => i :: l) [] ++ [m] ++ st.frames.fold (fun l _ i => i :: l) [] ++
      st.regions.fold (fun l _ i => i :: l) []
    let mut seen : Std.HashSet Nat := {}
    for _ in [0:1 <<< 30] do
      match todo with
      | [] => break
      | x :: rest =>
        todo := rest
        let r ← find x
        if seen.contains r then continue
        seen := seen.insert r
        todo := match ← shapeOf r with
          | .pair a b | .sum a b => a :: b :: todo
          | .ref c | .imm c | .mut c | .fam c => c :: todo
          | .clos _ pa rs es => pa.toList ++ rs ++ es ++ todo
          | _ => todo
    pure m
  let (m, s) ← act.run {}
  pure (s, m)


/-! ### Resolution: classes, boxes, widths -/

/-- The resolved layouts. Nodes are representatives. -/
structure Layouts where
  rep : Array Nat
  shape : Array NK
  /-- **The representatives in their canonical order** (`canonicalOrder`): fixed by the program's
  variables and the types' structure, not by the nodes' numbers. -/
  order : Array Nat := #[]
  /-- Each closure class's codes, in code order: a code's tag is its index there. -/
  union : Std.HashMap Nat (Array Nat)
  /-- The closure classes that keep their environment on the heap. -/
  recCls : Std.HashSet Nat
  /-- The boxed fields `(node, field)`: a pair's or a sum's (the sum's field is its arm's payload). -/
  boxed : Std.HashSet (Nat × Nat)
  width : Array Nat
  trivial : Array Bool
  /-- **A value's bytes in a cell** at each node: `1` at a `u8`, `4` at an `i32` or `f32`, else its
  words' (`repBytes`). -/
  bytes : Array Nat
  /-- The most bytes a value of each type takes in a cell, over the nodes of that type, for each
  type of a width class the program allocates or reserves a static cell at (`Op.alloc`,
  `Prog.statics`), when a node is of it: a width class's types are read through it
  (`Layouts.clsBytes`). A type is keyed with its `!`s erased (`LTy.unbang`): `!A` is represented
  as `A`. -/
  tyBytes : Std.HashMap LTy Nat
  varNode : Std.HashMap Var Nat
  fnRet : Std.HashMap Nat Nat
  mainNode : Nat
  /-- Each code's class, and its functions' environment nodes. -/
  codeClass : Std.HashMap Nat Nat
  codeEnv : Std.HashMap Nat (List Nat)
  /-- Each site's `κ` region's contents node (SPEC §52). -/
  regions : Std.HashMap Nat Nat := {}
  /-- **Each static cell's bytes** (`Prog.statics`): the most bytes of its width
  class's types, each read through `tyBytes` with its `!`s erased. -/
  staticBytes : Array Nat := #[]
  /-- **Each sum node's merged arm** (`0` left, `1` right), whose words are the sum's on that arm:
  its tags the arm's own, the other arm's the one tag after them.  `[spec §43]` -/
  mergeArm : Array (Option Nat) := #[]
  /-- **Each sum node's tags**: its merged arm's and one, or `2`. -/
  tags : Array Nat := #[]
  /-- **The packed sum nodes**: one word, `tag << 32 | payload`, every leaf a scalar of at most 32
  bits or empty. -/
  packed : Array Bool := #[]

namespace Layouts

def r (L : Layouts) (i : Nat) : Nat := L.rep[i]!
def sh (L : Layouts) (i : Nat) : NK := L.shape[L.r i]!
def w (L : Layouts) (i : Nat) : Nat := L.width[L.r i]!
def triv (L : Layouts) (i : Nat) : Bool := L.trivial[L.r i]!
def node (L : Layouts) (x : Var) : Nat := L.r (L.varNode.getD x 0)
def isBoxed (L : Layouts) (i k : Nat) : Bool := L.boxed.contains (L.r i, k)
/-- The words of field `k` of a pair or a sum at `i`: a boxed field is one pointer. -/
def fieldW (L : Layouts) (i k : Nat) : Nat :=
  let c := match L.sh i, k with
    | .pair a _, 0 | .sum a _, 0 => a
    | .pair _ b, _ | .sum _ b, _ => b
    | _, _ => i
  if L.isBoxed i k then 1 else L.w c
def unionOf (L : Layouts) (i : Nat) : Array Nat := L.union.getD (L.r i) #[]
/-- The merged arm of a sum at `i`, if any. -/
def merged (L : Layouts) (i : Nat) : Option Nat := (L.mergeArm[L.r i]?).getD none
/-- A sum at `i` is one packed word. -/
def isPacked (L : Layouts) (i : Nat) : Bool := (L.packed[L.r i]?).getD false
/-- The tags of a sum at `i`. -/
def tagsOf (L : Layouts) (i : Nat) : Nat := (L.tags[L.r i]?).getD 2
def isRec (L : Layouts) (i : Nat) : Bool := L.recCls.contains (L.r i)
def tagOf (L : Layouts) (c : Nat) : Nat :=
  match L.codeClass[c]? with
  | some k => (L.unionOf k).idxOf c
  | none => 0
def envWords (L : Layouts) (c : Nat) : Nat := ((L.codeEnv.getD c []).map L.w).foldl (· + ·) 0
/-- The bytes of a value at node `i` in a cell. -/
def repB (L : Layouts) (i : Nat) : Nat := L.bytes[L.r i]!
/-- The bytes a cell of the width class `cls` holding a value at node `c` takes: the most of the
value's and of each type of the class's (SPEC §57). -/
def clsBytes (L : Layouts) (c : Nat) (cls : List LTy) : Nat :=
  cls.foldl (fun b t => max b (L.tyBytes.getD t.unbang 0)) (L.repB c)

end Layouts

/-- Strongly connected components (Tarjan, iterative): whether each node is on a cycle, and each
node's component.

A root with no successor is its own component, on no cycle, numbered as the search would number
it: the search from it would push it, find no edge and pop it alone. In `resolve`'s graphs every
node that is not a representative is such a root (it has no edge, and no edge reaches it), so the
search proper runs over the representatives only, and the components are those it would find
over all nodes, numbered alike. -/
def sccs (n : Nat) (succ : Array (List Nat)) : Array Bool × Array Nat := Id.run do
  let mut comp : Array Nat := Array.replicate n 0
  let mut ncomp := 0
  let mut index : Array (Option Nat) := Array.replicate n none
  let mut low : Array Nat := Array.replicate n 0
  let mut onStack : Array Bool := Array.replicate n false
  let mut stack : List Nat := []
  let mut cyc : Array Bool := Array.replicate n false
  let mut idx := 0
  let bound := 4 * n + 4 + succ.foldl (· + ·.length) 0
  for root in [0:n] do
    if index[root]!.isSome then continue
    if succ[root]!.isEmpty then
      index := index.set! root (some idx); idx := idx + 1
      comp := comp.set! root ncomp; ncomp := ncomp + 1
      continue
    let mut work : List (Nat × List Nat) := [(root, succ[root]!)]
    index := index.set! root (some idx); low := low.set! root idx; idx := idx + 1
    stack := root :: stack; onStack := onStack.set! root true
    for _ in [0:bound] do
      match work with
      | [] => break
      | (v, c :: cs) :: rest =>
        work := (v, cs) :: rest
        match index[c]! with
        | none =>
          index := index.set! c (some idx); low := low.set! c idx; idx := idx + 1
          stack := c :: stack; onStack := onStack.set! c true
          work := (c, succ[c]!) :: work
        | some ic => if onStack[c]! then low := low.set! v (min low[v]! ic)
      | (v, []) :: rest =>
        work := rest
        if some low[v]! == index[v]! then
          let mut members : List Nat := []
          for _ in [0:n + 1] do
            match stack with
            | u :: st =>
              stack := st; onStack := onStack.set! u false; members := u :: members
              if u == v then break
            | [] => break
          for u in members do comp := comp.set! u ncomp
          ncomp := ncomp + 1
          if members.length > 1 || succ[v]!.contains v then
            for u in members do cyc := cyc.set! u true
        match rest with
        | (u, _) :: _ => low := low.set! u (min low[u]! low[v]!)
        | [] => pure ()
  return (cyc, comp)

/-- The back edges `(v, k)` of one depth-first search from `roots` over `fs`, skipping `skip`. -/
def backEdges (n : Nat) (fs : Nat → Array Nat) (roots : List Nat)
    (skip : Std.HashSet (Nat × Nat)) : Std.HashSet (Nat × Nat) := Id.run do
  let mut color : Array Nat := Array.replicate n 0
  let mut back : Std.HashSet (Nat × Nat) := {}
  let bound := 4 * n + 4 + (List.range n).foldl (fun k v => k + (fs v).size) 0
  for root in roots do
    if color[root]! != 0 then continue
    let mut stack : List (Nat × Nat) := [(root, 0)]
    color := color.set! root 1
    for _ in [0:bound] do
      match stack with
      | [] => break
      | (v, i) :: rest =>
        match (fs v)[i]? with
        | some c =>
          stack := (v, i + 1) :: rest
          if skip.contains (v, i) then continue
          if color[c]! == 1 then back := back.insert (v, i)
          else if color[c]! == 0 then
            color := color.set! c 1
            stack := (c, 0) :: stack
        | none => color := color.set! v 2; stack := rest
  return back


/-- `b` reaches `a` in `fs`, not along `skip`. -/
def reaches (n : Nat) (fs : Nat → Array Nat) (skip : Std.HashSet (Nat × Nat)) (b a : Nat) : Bool :=
  Id.run do
  let mut seen : Std.HashSet Nat := {}
  let mut todo : List Nat := [b]
  for _ in [0:n + 1] do
    match todo with
    | [] => return false
    | v :: rest =>
      todo := rest
      if v == a then return true
      if seen.contains v then continue
      seen := seen.insert v
      for (c, i) in (fs v).toList.zipIdx do
        if !skip.contains (v, i) && !seen.contains c then todo := c :: todo
  return seen.contains a

/-- SPEC §35's rule: in a component of the field graph where one search boxes two fields or more,
a sum's payload is boxed in place of its payload's recursive fields when that boxes fewer: a
tree is one object a node, its children inline. -/
def sumBoxes (order : List Nat) (fs : Nat → Array Nat) (shape : Nat → NK) (comp : Array Nat)
    (back : Std.HashSet (Nat × Nat)) : Std.HashSet (Nat × Nat) := Id.run do
  let n := comp.size
  let mut byComp : Std.HashMap Nat (List (Nat × Nat)) := {}
  for (v, i) in back.toList do
    byComp := byComp.insert comp[v]! ((v, i) :: byComp.getD comp[v]! [])
  let mut out := back
  for (C, es) in byComp.toList do
    if es.length < 2 then continue
    let nodes := order.filter (comp[·]! == C)
    let mut leave : Std.HashSet (Nat × Nat) := {}
    let mut sums : List (Nat × Nat) := []
    for v in nodes do
      for (c, i) in (fs v).toList.zipIdx do
        if comp[c]! != C then leave := leave.insert (v, i)
        else if let .sum .. := shape v then sums := sums ++ [(v, i)]
    if sums.isEmpty then continue
    let mut skip := sums.foldl (·.insert ·) leave
    let mut boxes := backEdges n fs nodes skip
    skip := boxes.fold (·.insert ·) skip
    for (v, i) in sums do
      let c := (fs v)[i]!
      let without := skip.erase (v, i)
      if reaches n fs without c v then boxes := boxes.insert (v, i)
      else skip := without
    if boxes.size < es.length then
      out := es.foldl (·.erase ·) out
      out := boxes.fold (·.insert ·) out
  return out

/-- A node of shape `k` and `w` words is a narrow leaf of a packed sum: empty, or a scalar of at
most 32 bits. -/
def narrowLeaf (k : NK) (w : Nat) : Bool :=
  w == 0 || match k with
    | .int .w8 | .int .w32 | .int .u32 | .int .f32 => true
    | _ => false

/-- **A sum's encoding** (SPEC §43), from its arms: each arm's field boxed (`bx`), its child's shape,
width, packing and tags. The merged arm, the tags, whether it is packed, and its words.
A candidate arm (the right, else the left: not boxed, a sum) is merged unless it is packed and
the other arm is not a narrow leaf, or its tags do not fit 32 bits beside a packed payload.  `[spec §43]` -/
def sumEnc (bx : Nat → Bool) (k : Nat → NK) (w : Nat → Nat) (pk : Nat → Bool) (tg : Nat → Nat) :
    Option Nat × Nat × Bool × Nat :=
  let isSum (j : Nat) : Bool := !bx j && match k j with | .sum .. => true | _ => false
  let fw (j : Nat) : Nat := if bx j then 1 else w j
  let nar (j : Nat) : Bool := !bx j && narrowLeaf (k j) (w j)
  let plain : Option Nat × Nat × Bool × Nat :=
    let p := nar 0 && nar 1 && (fw 0 == 1 || fw 1 == 1)
    (none, 2, p, if p then 1 else 1 + max (fw 0) (fw 1))
  let cand : Option Nat := if isSum 1 then some 1 else if isSum 0 then some 0 else none
  match cand with
  | none => plain
  | some m =>
    let o := 1 - m
    if pk m then
      if nar o && tg m < 0xFFFFFFFF then (some m, tg m + 1, true, 1) else plain
    else (some m, tg m + 1, false, 1 + max (w m - 1) (fw o))

/-- Each node's representative: the root of its tree in `parent`, a forest. -/
def reps (parent : Array Nat) : Array Nat := Id.run do
  let n := parent.size
  -- `0` not yet known; else the representative plus one.
  let mut rep : Array Nat := Array.replicate n 0
  for i in [0:n] do
    if rep[i]! != 0 then continue
    -- Up to the root or a node already known, then the path below it.
    let mut path : Array Nat := #[]
    let mut j := i
    let mut r := i
    for _ in [0:n + 1] do
      if rep[j]! != 0 then r := rep[j]! - 1; break
      let q := parent[j]!
      if q == j then r := j; rep := rep.set! j (j + 1); break
      path := path.push j
      j := q
    for k in path do rep := rep.set! k (r + 1)
  return rep.map (· - 1)

/-- The types of the width classes a term's allocations carry (`Op.alloc`, `Op.allocLent`). -/
def allocTys : Nat → Tm → List LTy
  | 0, _ => []
  | f + 1, t => match t with
    | .prim (.alloc cls) _ | .prim (.allocLent _ cls) _ => cls
    | .letv _ e b => allocTys f e ++ allocTys f b
    | .letpair _ _ _ b | .copy _ _ _ b | .consume _ _ b | .abandon _ _ b => allocTys f b
    | .case _ _ b₁ _ b₂ => allocTys f b₁ ++ allocTys f b₂
    | _ => []

/-- The types of the program's width classes: its allocations' and its static cells'. -/
def clsTysOf (p : Prog) : List LTy :=
  p.statics.toList.flatten ++ (p.main :: p.fns.toList.map (·.body)).flatMap (allocTys (1 <<< 22))

/-- The types a node of `s` is of, each up to its `!`s: the type it lays out and, at a `μ` or a
`ν`, each type it unrolls through to its former. -/
def Src.tys (s : Src) : List LTy := Id.run do
  let mut out : List LTy := []
  let mut cur : Sum LTy LCTy := match s with
    | .v t _ => .inl t
    | .c k _ => .inr k
  for _ in [0:4096] do
    match cur with
    | .inl t =>
      match stripB t with
      | .tvar _ => break
      | .thunk k => cur := .inr k
      | .mu a => out := t :: out; cur := .inl a
      | t => out := t :: out; break
    | .inr k =>
      out := .thunk k :: out
      match k with
      | .nu d => cur := .inr d
      | _ => break
  return out

/-- **The canonical order of the representatives**: depth first, each before its children, from
each variable's node by the variables' order, each function's answer by the functions', `main`'s
node and each site's `κ` region by the sites'; a node's children in its fields' order (a pair's or
a sum's two, a cell's or a family's contents, a closure class's argument then its answers). It
depends on the program and the types' structure, not on how the nodes are numbered. -/
def canonicalOrder (n : Nat) (rep : Array Nat) (shape : Array NK) (s : GState) (mainNode : Nat) :
    Array Nat :=
  Id.run do
  let sorted (m : Std.HashMap Nat Nat) : List Nat :=
    (m.toList.mergeSort (·.1 ≤ ·.1)).map (rep[·.2]!)
  let roots := sorted s.varNode ++ sorted s.fnRet ++ [rep[mainNode]!] ++ sorted s.regions
  let mut seen : Array Bool := Array.replicate n false
  let mut out : Array Nat := #[]
  for root in roots do
    let mut stack : List Nat := [root]
    for _ in [0:4 * n + 4] do
      match stack with
      | [] => break
      | v :: rest =>
        stack := rest
        if seen[v]! then continue
        seen := seen.set! v true
        out := out.push v
        let kids : List Nat := match shape[v]! with
          | .pair a b | .sum a b => [a, b]
          | .ref c | .imm c | .mut c | .fam c => [c]
          | .clos _ pa rs es => pa.toList ++ rs ++ es
          | _ => []
        stack := kids.filter (!seen[·]!) ++ stack
  -- A representative no root reaches (none: every node is made from a root's type) follows.
  for v in [0:n] do
    if rep[v]! == v && !seen[v]! then out := out.push v
  return out

/-- Resolve the joined places: each class's codes, the heap classes, the boxed fields, every
node's width and triviality, and each cell's width, by the checker's cell classes `cells` (each
the types one cell may hold). -/
def resolve (p : Prog) (s : GState) (mainNode : Nat) : Layouts := Id.run do
  let n := s.nodes.size
  let rep := reps s.parent
  let norm (k : NK) : NK := match k with
    | .pair a b => .pair rep[a]! rep[b]!
    | .sum a b => .sum rep[a]! rep[b]!
    | .ref c => .ref rep[c]!
    | .imm c => .imm rep[c]!
    | .mut c => .mut rep[c]!
    | .fam l => .fam rep[l]!
    | .clos k p r e => .clos k (p.map (rep[·]!)) (r.map (rep[·]!)) (e.map (rep[·]!))
    | k => k
  -- A node's shape is its representative's, one value shared.
  let repShape := (Array.range n).map fun i => if rep[i]! == i then norm s.nodes[i]! else .unit
  let shape := (Array.range n).map fun i => repShape[rep[i]!]!
  let order := canonicalOrder n rep repShape s mainNode
  let mut union : Std.HashMap Nat (Array Nat) := {}
  let mut codeClass : Std.HashMap Nat Nat := {}
  for (k, cs) in s.codes.toList do
    let r := rep[k]!
    let all := ((union.getD r #[]).toList ++ cs).eraseDups.mergeSort (· ≤ ·)
    union := union.insert r all.toArray
  for (r, cs) in union.toList do
    for c in cs do codeClass := codeClass.insert c r
  -- Each code's environment: its first function's captured parameters.
  let mut codeEnv : Std.HashMap Nat (List Nat) := {}
  for (code, c) in p.codes.toList.zipIdx do
    let some fn := code.fns.head? | continue
    let some f := p.fns[fn]? | continue
    let k := f.params.length - f.evs - (if code.kind == .lam then 1 else 0)
    codeEnv := codeEnv.insert c ((f.params.take k).map fun x => rep[s.varNode.getD x 0]!)
  let envOf (v : Nat) : List Nat := (union.getD v #[]).toList.flatMap (codeEnv.getD · [])
  let succ := (Array.range n).map fun v =>
    if rep[v]! != v then [] else match shape[v]! with
      | .pair a b | .sum a b => [a, b]
      | .clos .. => envOf v
      | _ => []
  -- UNPROVED: that a boxed field's object and a heap class's environment have one owner, the
  -- value that holds them, so that `Lower` frees them where that value is taken apart and copies
  -- them where it is copied. It should hold because the LIR consumes each variable exactly once
  -- on every path, which `Lint` checks of each program it compiles and nothing proves of
  -- the conversion's output. The choice of fields follows SPEC §35's rule on the type's own
  -- graph: the boxes arise where a `μ` or a closure class holds itself other than through a
  -- `Ref`. If it fails, an object is freed twice or leaks. The boxes and heap classes are checked
  -- to leave no cycle inline and to satisfy the width equations (`LayoutCheck.layoutOk`); the one
  -- owner is not.
  let (cyc, _) := sccs n succ
  let mut recCls : Std.HashSet Nat := {}
  for v in [0:n] do
    if rep[v]! == v && cyc[v]! then
      if let .clos .. := shape[v]! then recCls := recCls.insert v
  let fieldsA : Array (Array Nat) := (Array.range n).map fun v =>
    if recCls.contains v then #[] else succ[v]!.toArray
  let fieldsOf (v : Nat) : Array Nat := fieldsA[v]!
  -- The searches that choose the boxes run in the canonical order: the boxes follow from the
  -- types and the program, not from the nodes' numbers.
  let reps := order.toList
  let isSum (v : Nat) : Bool := match shape[v]! with | .sum .. => true | _ => false
  let roots := reps.filter isSum ++ reps.filter (!isSum ·)
  let back := backEdges n fieldsOf roots {}
  let comp := (sccs n ((Array.range n).map fun v => (fieldsOf v).toList)).2
  let mut boxed : Std.HashSet (Nat × Nat) := sumBoxes reps fieldsOf (shape[·]!) comp back
  let mut color : Array Nat := Array.replicate n 0
  let mut width : Array Nat := Array.replicate n 0
  let mut trivial : Array Bool := Array.replicate n true
  let mut mergeArm : Array (Option Nat) := Array.replicate n none
  let mut tags : Array Nat := Array.replicate n 2
  let mut packed : Array Bool := Array.replicate n false
  let bound := 4 * n + 4 + succ.foldl (· + ·.length) 0
  for root in reps do
    if color[root]! != 0 then continue
    let mut stack : List (Nat × Nat) := [(root, 0)]
    color := color.set! root 1
    for _ in [0:bound] do
      match stack with
      | [] => break
      | (v, i) :: rest =>
        let fs := fieldsOf v
        match fs[i]? with
        | some c =>
          stack := (v, i + 1) :: rest
          if boxed.contains (v, i) then continue
          if color[c]! == 1 then boxed := boxed.insert (v, i)
          else if color[c]! == 0 then
            color := color.set! c 1
            stack := (c, 0) :: stack
        | none =>
          let fw (j c : Nat) : Nat := if boxed.contains (v, j) then 1 else width[c]!
          let ft (j c : Nat) : Bool := !boxed.contains (v, j) && trivial[c]!
          -- Copying or consuming a cell, a borrow or a family is its words alone (`trivial`): an
          -- owned `Ref` or array is never copied or consumed by `copy`/`consume` but inside a value
          -- that owns nothing. `Lint` checks, on every program compiled, each `copy` and `consume`
          -- against its rule's premise (`Lint.copiesAt`, `Lint.consumesAt`): a persistent type, an
          -- `imm` borrow or a family of them at a copy; a persistent type, one with no owned
          -- cell, or a family of borrows at a consume, `!` read off the LIR type; a persistent value
          -- holds no resource (`vP_empty_of_persistent`), a `VTy.OwnFree` one no owned cell
          -- (`vC_noOwn_of_ownFree`), a family of borrows none.
          -- UNPROVED: that a variable's LIR type is the image of its node's checked type (by
          -- construction in `Convert`, not proved), and the stack machines' hand-over of a level's
          -- suspended computation, which no type licenses (`StackKHandOver`, at `genStackMach`).
          -- If either fails, an owned cell is aliased (freed twice) or leaks.
          let (wv, tv) := match shape[v]! with
            | .unit | .zero | .unk => (0, true)
            | .int _ | .opq | .ref _ | .imm _ | .mut _ => (1, true)
            | .fam _ => (2, true)
            | .pair a b => (fw 0 a + fw 1 b, ft 0 a && ft 1 b)
            | .sum a b =>
              let ch (j : Nat) : Nat := if j == 0 then a else b
              let (_, _, _, w) := sumEnc (fun j => boxed.contains (v, j)) (shape[ch ·]!) (width[ch ·]!)
                (packed[ch ·]!) (tags[ch ·]!)
              (w, ft 0 a && ft 1 b)
            | .clos .. =>
              if recCls.contains v then (1, false) else
              let cs := (union.getD v #[]).toList
              (1 + cs.foldl (fun k c => max k (((codeEnv.getD c []).map (width[·]!)).foldl (· + ·) 0)) 0,
               cs.all fun c => (codeEnv.getD c []).all (trivial[·]!))
          width := width.set! v wv
          trivial := trivial.set! v tv
          if let .sum a b := shape[v]! then
            let ch (j : Nat) : Nat := if j == 0 then a else b
            let (m, t, p, _) := sumEnc (fun j => boxed.contains (v, j)) (shape[ch ·]!) (width[ch ·]!)
              (packed[ch ·]!) (tags[ch ·]!)
            mergeArm := mergeArm.set! v m
            tags := tags.set! v t
            packed := packed.set! v p
          color := color.set! v 2
          stack := rest
  -- **Cells.** A value in a cell takes its node's bytes (`repB`): a `u8` one, an `i32` or `f32`
  -- four, any other value its words; so its reads and writes depend on its type alone, whatever
  -- cell holds it. An allocation reserves the most bytes of its width class's types (the checker's
  -- `Checked.classAt` of the type it allocates at, which `Convert` writes on the allocation, SPEC
  -- §57), each read through the most bytes a value of that type takes (`tyBytes`).
  let bytesOf (v : Nat) : Nat := match shape[v]! with
    | .int .w8 => 1
    | .int .w32 | .int .f32 | .int .u32 => 4
    | _ => 8 * width[v]!
  let bytes := (Array.range n).map fun i => bytesOf rep[i]!
  -- Each width class type's most bytes, over the nodes of that type, `!`s erased: a node is of the
  -- type it lays out and, at a `μ` or a `ν`, of each type it unrolls through to its former. The
  -- types are the ones a width class is read at: the allocations' and the static cells'.
  let mut keys : Array LTy := #[]
  let mut seenK : Std.HashSet UB := {}
  for t in clsTysOf p do
    unless seenK.contains ⟨t⟩ do
      seenK := seenK.insert ⟨t⟩
      keys := keys.push t
  let fps := keys.map (hashTop 4)
  let mut most : Array (Option Nat) := Array.replicate keys.size none
  for i in [0:n] do
    for t in (s.src[i]!).tys do
      let h := hashTop 4 t
      for j in [0:keys.size] do
        if fps[j]! == h && eqUB 4096 t keys[j]! then
          most := most.set! j (some (max (most[j]!.getD 0) bytes[i]!))
  let mut tyBytes : Std.HashMap LTy Nat := {}
  for j in [0:keys.size] do
    if let some b := most[j]! then tyBytes := tyBytes.insert keys[j]!.unbang b
  let varNode := s.varNode.fold (fun m x i => m.insert x rep[i]!) {}
  let fnRet := s.fnRet.fold (fun m f i => m.insert f rep[i]!) {}
  return { rep, shape, order, union, recCls, boxed, width, trivial, bytes, tyBytes, varNode,
           fnRet, mainNode := rep[mainNode]!, codeClass, codeEnv,
           regions := s.regions.fold (fun m k i => m.insert k rep[i]!) {},
           staticBytes := p.statics.map fun cls =>
             cls.foldl (fun b t => max b (tyBytes.getD t.unbang 0)) 0,
           mergeArm, tags, packed }

end Backend2.Lay

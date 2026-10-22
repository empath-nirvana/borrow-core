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
  built from its `LTy` (`nodeOf`): `μ` and `ν` close their cycles (a recursive type is the regular
  tree it unrolls to). Nothing is inferred: every node's former is the type's.
- **Closure classes.** The places a closure value moves between (a binding, an argument and its
  parameter, a result, a constructor's field, a cell's contents) are joined (`join`), so a value
  and every place it reaches share one node. The closure nodes are then the classes: a class
  holds the codes whose closures reach it, and their functions share its argument and answer
  nodes. A class is the lambda set of the closures at its places.
- **One box a node** (SPEC §35): a recursive type boxes the fields that close its cycles, the back
  edges of one search over the pair and sum fields, or a sum's payload where that boxes fewer
  (`sumBoxes`). A closure class that holds itself among its codes' captured values keeps its
  environment on the heap.
- **Cells.** A cell is as wide as the widest type its class may hold: the checker's cell
  classes (`Checked.cells`) give the class. A cell whose class holds only integers of one width
  is a slot of that width's bytes: a byte, or 4 bytes for `i32` and `f32` (L-6).
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
  | clos (k : CodeKind) (param : Option Nat) (res : List Nat)
  deriving Inhabited, BEq, Repr

structure GState where
  nodes : Array NK := #[]
  parent : Array Nat := #[]
  /-- Each node's type, for the cell classes' widths. -/
  origin : Array LTy := #[]
  /-- Each closure class's codes (at its representative). -/
  codes : Std.HashMap Nat (List Nat) := {}
  varNode : Std.HashMap Var Nat := {}
  fnRet : Std.HashMap Nat Nat := {}
  /-- The joins left to do: a work list, so that joining recursive nodes terminates. -/
  todo : List (Nat × Nat) := []

abbrev GM := StateT GState (Except String)

def findIn (parent : Array Nat) : Nat → Nat → Nat
  | 0, i => i
  | f + 1, i => let p := parent[i]!; if p == i then i else findIn parent f p

/-- Point every node on the path from `j` at `r`, at most `f` of them. -/
def compress (r : Nat) : Nat → Array Nat → Nat → Array Nat
  | 0, parent, _ => parent
  | f + 1, parent, j =>
    let p := parent[j]!
    if p == j || p == r then parent else compress r f (parent.set! j r) p

/-- The representative of `i`, compressing the path to it: the parent array is taken out of the
state, so that the compression writes it in place. -/
def find (i : Nat) : GM Nat := modifyGet fun s =>
  let parent := s.parent
  let s := { s with parent := #[] }
  let r := findIn parent parent.size i
  (r, { s with parent := compress r parent.size parent i })

def newNode (k : NK) (o : LTy) : GM Nat := modifyGet fun s =>
  (s.nodes.size, { s with nodes := s.nodes.push k, parent := s.parent.push s.nodes.size,
                          origin := s.origin.push o })

def setNode (i : Nat) (k : NK) : GM Unit := modify fun s => { s with nodes := s.nodes.set! i k }

mutual
/-- The nodes of a value type; `env` gives the nodes of the type variables bound around it. -/
def build (fuel : Nat) (env : List Nat) (t : LTy) : GM Nat := do
  match fuel with
  | 0 => throw "layout: a type too deep"
  | f + 1 =>
  match t with
  | .unit => newNode .unit t
  | .zero => newNode .zero t
  | .unk => newNode .unk t
  | .opq _ => newNode .opq t
  | .int w => newNode (.int w) t
  | .pair a b => do
    let x ← build f env a
    let y ← build f env b
    newNode (.pair x y) t
  | .sum a b => do
    let x ← build f env a
    let y ← build f env b
    newNode (.sum x y) t
  | .ref a => do newNode (.ref (← build f env a)) t
  | .imm a => do newNode (.imm (← build f env a)) t
  | .mut a => do newNode (.mut (← build f env a)) t
  | .fam l => do newNode (.fam (← build f env l)) t
  | .tvar n =>
    match env[n]? with
    | some i => pure i
    | none => throw s!"layout: a free type variable {n}"
  | .mu a => do
    -- `μX. A` is the node `A` builds with `X` that node itself.
    let p ← newNode .unit t
    let i ← build f (p :: env) a
    let k := (← get).nodes[i]!
    setNode p k
    modify fun s => { s with parent := s.parent.set! i p }
    pure p
  | .thunk k => buildC f env k
/-- The class node of a closure of `k`. -/
def buildC (fuel : Nat) (env : List Nat) (k : LCTy) : GM Nat := do
  match fuel with
  | 0 => throw "layout: a type too deep"
  | f + 1 =>
  match k with
  | .nu c => do
    -- `U(νX. C)` is the closure node `C` builds with `U X` that node itself.
    let p ← newNode .unit (.thunk k)
    let i ← buildC f (p :: env) c
    setNode p (← get).nodes[i]!
    modify fun s => { s with parent := s.parent.set! i p }
    pure p
  | .ret a => do newNode (.clos .unit none [← build f env a]) (.thunk k)
  | .arr a c => do newNode (.clos .lam (some (← build f env a)) [← repNode f env c]) (.thunk k)
  | .amp c d => do newNode (.clos .amp none [← repNode f env c, ← repNode f env d]) (.thunk k)
  | .top => newNode .unit (.thunk k)
/-- The node of what running a closure of `k` answers. -/
def repNode (fuel : Nat) (env : List Nat) (k : LCTy) : GM Nat := do
  match fuel with
  | 0 => throw "layout: a type too deep"
  | f + 1 =>
  match k with
  | .ret a => build f env a
  | .top => newNode .unit (.thunk k)
  | k => buildC f env k
end

/-- The node of a variable, built from its type the first time. -/
def nodeOfVar (ty : Var → Except String LTy) (x : Var) : GM Nat := do
  match (← get).varNode[x]? with
  | some i => pure i
  | none =>
    let t ← match ty x with
      | .ok t => pure t
      | .error e => throw e
    let i ← build 4096 [] t
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
      let kx := (← get).nodes[rx]!
      let ky := (← get).nodes[ry]!
      let cs := (← get).codes.getD rx [] ++ (← get).codes.getD ry []
      let ox := (← get).origin[rx]!
      let oy := (← get).origin[ry]!
      modify fun s => { s with parent := s.parent.set! ry rx, codes := (s.codes.erase ry).insert rx cs }
      let more : List (Nat × Nat) ← match kx, ky with
        | .pair a b, .pair c d | .sum a b, .sum c d => pure [(a, c), (b, d)]
        | .ref a, .ref c | .imm a, .imm c | .mut a, .mut c | .fam a, .fam c => pure [(a, c)]
        | .ref a, .imm c | .ref a, .mut c | .imm a, .ref c | .mut a, .ref c
        | .imm a, .mut c | .mut a, .imm c => pure [(a, c)]
        | .clos k p r, .clos k' p' r' =>
          if k != k' || r.length != r'.length then
            throw s!"layout: closures of different kinds joined ({reprStr k} {ox} codes {cs}, {reprStr k'} {oy})"
          let ps := match p, p' with
            | some a, some c => [(a, c)]
            | _, _ => []
          pure (ps ++ r.zip r')
        -- A capability's contents, an opaque host value, is held as the word the extern stores.
        | .opq, .int _ | .int _, .opq => pure []
        | k, k' =>
          if k == k' then pure [] else
          throw s!"layout: a {reprStr k |>.take 40} joined with a {reprStr k' |>.take 40}"
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
      let kx := (← get).nodes[rx]!
      let ky := (← get).nodes[ry]!
      match kx, ky with
      | .pair a b, .pair c d | .sum a b, .sum c d => todo := (a, c) :: (b, d) :: todo
      | .ref a, .imm c | .mut a, .imm c | .imm a, .imm c => join a c
      | .fam a, .fam c => todo := (a, c) :: todo
      | .clos .., .unk | .opq, .unk => pure ()
      | _, _ => join rx ry
  throw "layout: a reborrowed read too deep"

/-- The class of a closure node: its children. -/
def closOf (i : Nat) : GM (CodeKind × Option Nat × List Nat) := do
  let r ← find i
  match (← get).nodes[r]! with
  | .clos k p r => pure (k, p, r)
  | k => throw s!"layout: a call of a non-closure node {reprStr k |>.take 40}"

def childrenOf (i : Nat) : GM NK := do
  let r ← find i
  return (← get).nodes[r]!


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
    let i ← build 4096 [] f.ret
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
  | .call fn as => do
    let some fd := p.fns[fn]? | throw s!"layout: no function f{fn}"
    for (x, y) in as.zip fd.params do join (← nv x) (← nv y)
    join dst (← fnRetNode p fn); pure cc
  | .prim op as => do
    let a (i : Nat) : GM Nat := do nv (as.getD i 0)
    match op with
    | .alloc | .allocLent | .staticCell _ => join (← kid dst 0) (← a 0)
    | .free => join dst (← kid (← a 0) 0)
    | .swap => do
      join (← kid (← kid dst 0) 0) (← a 1)
      join (← kid dst 1) (← kid (← a 0) 0)
    | .lend => do
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
  | .copy x x' b => do join (← nv x) (← nv x'); walk p f cc b dst
  | .drop _ b => walk p f cc b dst

/-- Every place of the program, joined. -/
def places (p : Prog) : Except String (GState × Nat) := do
  let act : GM Nat := do
    let mut cc : Std.HashMap Nat Nat := {}
    for (fd, i) in p.fns.toList.zipIdx do
      for x in fd.params do let _ ← nodeOfVar (tyOfL p) x
      cc ← walk p (1 <<< 22) cc fd.body (← fnRetNode p i)
    let m ← build 4096 [] p.mainTy
    let _ ← walk p (1 <<< 22) cc p.main m
    pure m
  let (m, s) ← act.run {}
  pure (s, m)


/-! ### Resolution: classes, boxes, widths -/

/-- The resolved layouts. Nodes are representatives. -/
structure Layouts where
  rep : Array Nat
  shape : Array NK
  /-- Each closure class's codes, in code order: a code's tag is its index there. -/
  union : Std.HashMap Nat (Array Nat)
  /-- The closure classes that keep their environment on the heap. -/
  recCls : Std.HashSet Nat
  /-- The boxed fields `(node, field)`: a pair's or a sum's (the sum's field is its arm's payload). -/
  boxed : Std.HashSet (Nat × Nat)
  width : Array Nat
  trivial : Array Bool
  /-- Each pointer node's cell: its words, or its slot's bytes when it is narrower than a word. -/
  cellWords : Std.HashMap Nat Nat
  slotBytes : Std.HashMap Nat Nat
  varNode : Std.HashMap Var Nat
  fnRet : Std.HashMap Nat Nat
  mainNode : Nat
  /-- Each code's class, and its functions' environment nodes. -/
  codeClass : Std.HashMap Nat Nat
  codeEnv : Std.HashMap Nat (List Nat)

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
def isRec (L : Layouts) (i : Nat) : Bool := L.recCls.contains (L.r i)
def tagOf (L : Layouts) (c : Nat) : Nat :=
  match L.codeClass[c]? with
  | some k => (L.unionOf k).idxOf c
  | none => 0
def envWords (L : Layouts) (c : Nat) : Nat := ((L.codeEnv.getD c []).map L.w).foldl (· + ·) 0

end Layouts

/-- Strongly connected components (Tarjan, iterative): whether each node is on a cycle, and each
node's component. -/
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
def sumBoxes (n : Nat) (fs : Nat → Array Nat) (shape : Nat → NK) (comp : Array Nat)
    (back : Std.HashSet (Nat × Nat)) : Std.HashSet (Nat × Nat) := Id.run do
  let mut byComp : Std.HashMap Nat (List (Nat × Nat)) := {}
  for (v, i) in back.toList do
    byComp := byComp.insert comp[v]! ((v, i) :: byComp.getD comp[v]! [])
  let mut out := back
  for (C, es) in byComp.toList do
    if es.length < 2 then continue
    let nodes := (List.range n).filter (comp[·]! == C)
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

/-- Resolve the joined places: each class's codes, the heap classes, the boxed fields, every
node's width and triviality, and each cell's width, by the checker's cell classes `cells` (each
the types one cell may hold). -/
def resolve (p : Prog) (s : GState) (mainNode : Nat) (cells : List (List LTy)) :
    Layouts := Id.run do
  let n := s.nodes.size
  let rep := (Array.range n).map (findIn s.parent n)
  let norm (k : NK) : NK := match k with
    | .pair a b => .pair rep[a]! rep[b]!
    | .sum a b => .sum rep[a]! rep[b]!
    | .ref c => .ref rep[c]!
    | .imm c => .imm rep[c]!
    | .mut c => .mut rep[c]!
    | .fam l => .fam rep[l]!
    | .clos k p r => .clos k (p.map (rep[·]!)) (r.map (rep[·]!))
    | k => k
  let shape := (Array.range n).map fun i => norm s.nodes[rep[i]!]!
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
    let k := if code.kind == .lam then f.params.length - 1 else f.params.length
    codeEnv := codeEnv.insert c ((f.params.take k).map fun x => rep[s.varNode.getD x 0]!)
  let envOf (v : Nat) : List Nat := (union.getD v #[]).toList.flatMap (codeEnv.getD · [])
  let succ := (Array.range n).map fun v =>
    if rep[v]! != v then [] else match shape[v]! with
      | .pair a b | .sum a b => [a, b]
      | .clos .. => envOf v
      | _ => []
  let (cyc, _) := sccs n succ
  let mut recCls : Std.HashSet Nat := {}
  for v in [0:n] do
    if rep[v]! == v && cyc[v]! then
      if let .clos .. := shape[v]! then recCls := recCls.insert v
  let fieldsA : Array (Array Nat) := (Array.range n).map fun v =>
    if recCls.contains v then #[] else succ[v]!.toArray
  let fieldsOf (v : Nat) : Array Nat := fieldsA[v]!
  let reps := (List.range n).filter fun v => rep[v]! == v
  let isSum (v : Nat) : Bool := match shape[v]! with | .sum .. => true | _ => false
  let roots := reps.filter isSum ++ reps.filter (!isSum ·)
  let back := backEdges n fieldsOf roots {}
  let comp := (sccs n ((Array.range n).map fun v => (fieldsOf v).toList)).2
  let mut boxed : Std.HashSet (Nat × Nat) := sumBoxes n fieldsOf (shape[·]!) comp back
  let mut color : Array Nat := Array.replicate n 0
  let mut width : Array Nat := Array.replicate n 0
  let mut trivial : Array Bool := Array.replicate n true
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
          let (wv, tv) := match shape[v]! with
            | .unit | .zero | .unk => (0, true)
            | .int _ | .opq | .ref _ | .imm _ | .mut _ => (1, true)
            | .fam _ => (2, true)
            | .pair a b => (fw 0 a + fw 1 b, ft 0 a && ft 1 b)
            | .sum a b => (1 + max (fw 0 a) (fw 1 b), ft 0 a && ft 1 b)
            | .clos .. =>
              if recCls.contains v then (1, false) else
              let cs := (union.getD v #[]).toList
              (1 + cs.foldl (fun k c => max k (((codeEnv.getD c []).map (width[·]!)).foldl (· + ·) 0)) 0,
               cs.all fun c => (codeEnv.getD c []).all (trivial[·]!))
          width := width.set! v wv
          trivial := trivial.set! v tv
          color := color.set! v 2
          stack := rest
  -- Cells: the widest type the checker's class of the contents may hold.
  let mut byOrigin : Std.HashMap LTy Nat := {}
  for i in [0:n] do
    let o := s.origin[i]!
    byOrigin := byOrigin.insert o (max (byOrigin.getD o 0) width[rep[i]!]!)
  let mut cellWords : Std.HashMap Nat Nat := {}
  let mut slotBytes : Std.HashMap Nat Nat := {}
  for v in [0:n] do
    let c := match shape[v]! with
      | .ref c | .imm c | .mut c => some c
      | _ => none
    let some c := c | continue
    let ct := match s.origin[v]! with
      | .ref a | .imm a | .mut a => some a
      | _ => none
    let cls : List LTy := match ct with
      | some a => (cells.find? (·.contains a)).getD [a]
      | none => []
    let ws := width[c]! :: cls.map (byOrigin.getD · 0)
    let cw := ws.foldl max 0
    cellWords := cellWords.insert v cw
    let ints := (if cls.isEmpty then [s.origin[c]!] else cls).map fun t => match t with
      | .int .w8 => some 1 | .int .w32 | .int .f32 => some 4 | _ => none
    match ints with
    | some b :: rest => if rest.all (· == some b) then slotBytes := slotBytes.insert v b
    | _ => pure ()
  let varNode := s.varNode.fold (fun m x i => m.insert x rep[i]!) {}
  let fnRet := s.fnRet.fold (fun m f i => m.insert f rep[i]!) {}
  return { rep, shape, union, recCls, boxed, width, trivial, cellWords, slotBytes, varNode,
           fnRet, mainNode := rep[mainNode]!, codeClass, codeEnv }

end Backend2.Lay

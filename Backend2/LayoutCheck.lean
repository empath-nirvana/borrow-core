import Std.Data.HashMap
import Std.Data.HashSet
import Backend2.Layout
import Backend2.Flow

/-!
# Backend2 — the closure classes, checked  `[docs/compiler.md §5.2]`

`Layouts` (`Backend2/Layout.lean`) is computed by a whole-program analysis: it joins the places a
value moves between (`places`, by union-find), and resolves the joined graph into classes, boxes
and widths (`resolve`). The lowering (`Backend2/Lower.lean`) reads the result for every node's
words, copies, drops, boxes, cells and closure dispatch. The analysis is not proved. This module
checks its **result** on every compile (`Backend2/Driver.lean`, `checkedLayouts`): the result is
a solution of the constraints the program generates. It does not run the analysis, and does not
use its solver (`find`, `join`, `walk`, `resolve`); it reads the LIR and the finished `Layouts`
and verifies, each in time near-linear in the program and the layouts (a variable's type is
walked once):

- **Every node is its type's** (`conf`): each variable's node, each function's answer node and
  `main`'s node have, constructor for constructor, the shape `nodeOf`/`build` makes of its `LTy`
  (`Layout.lean` `build`, `nodeOfVar`, `fnRetNode`, `places`), the pairs of formers `join` admits
  sharing a node (a cell with its borrows, an opaque value with an integer).
- **Every move joins its two places** (`walk`): at every site of every function and of `main`,
  each pair of places the analysis's `walk` joins (`Layout.lean` `walk`, every constructor and
  every primitive) has one representative; a read through a shared borrow relates the contents
  and the reading as `joinRe` does (`reCompat`); every `framePush`/`frameTop` of one machine has
  one frame node and every `κ` access of one site one region node, which is `Layouts.regions`.
- **Every closure reaches a class that holds its code** (`walk`, `.clos`): a closure of code `c`
  made at a node is in that node's class's codes (`union`), `c`'s class (`codeClass`) is that
  class, and its captured values are the code's environment nodes (`codeEnv`). Since every move
  joins its places, every closure that reaches a call or a dispatch was made at a node of the
  call's class: the class holds every code that can reach it.
- **Every code of a class fits it** (`codeOk`): its kind is the class's, its functions are the
  class's components, each function's argument and answer are the class's, its environment is
  `codeEnv`; the codes of a class have no repeat and `codeClass` is their inverse.
- **The widths, the boxes and the heap classes are a layout** (`layoutOk`): the fields not boxed,
  and the environments of the classes not on the heap, form an acyclic graph; every node's width
  and triviality are `resolve`'s equations over its children (a boxed field one word, a heap class
  one word); a boxed field is a pair's or a sum's.
- **Every cell holds its contents** (`cellsOk`): each pointer node's cell has its words
  (`cellWords`), at least its contents' width, or a byte or 4-byte slot (`slotBytes`) only where
  its contents are an integer of that width; and where one run-time cell is seen at two pointer
  nodes (a `swap`, a `lend`, a pointer read through a shared borrow) both have one size.

`checkFlow` checks the closure flow (`Backend2/Flow.lean`) the same way: its sets are a solution of
its inclusion constraints, and every direct call it licenses (`known`) is of a variable whose set is
the one code.

The analysis's choices of *which* fields to box and which classes to keep on the heap are not
checked to be minimal: any choice that satisfies the equations is a layout. What stays trusted is
that the lowering reads these facts as it should.
-/

namespace Backend2.LayCheck
open BoCa Backend2 Backend2.Lay

structure CSt where
  /-- Each stack machine's frame cell node, from its first `framePush` or `frameTop`. -/
  frames : Std.HashMap Nat Nat := {}
  /-- Each site's `κ` region node, from its first `kappaPut` or `kappaTake`. -/
  regions : Std.HashMap Nat Nat := {}
  /-- Pairs of pointer nodes at which one run-time cell is seen, and where. -/
  sameCell : Array (Nat × Nat × String) := #[]
  /-- The variables of the program, each with the function it was met in. -/
  vars : Std.HashMap Var String := {}

abbrev CM := StateT CSt (Except String)

section
variable (L : Layouts)

/-- The representative of node `i`. -/
def rp (i : Nat) : CM Nat := do
  match L.rep[i]? with
  | some r => pure r
  | none => throw s!"node {i} is not a node of the layouts"

def shp (i : Nat) : CM NK := do
  let r ← rp L i
  match L.shape[r]? with
  | some k => pure k
  | none => throw s!"node {r} has no shape"

def short (k : NK) : String := (reprStr k |>.take 48).toString

/-- The node of a variable. -/
def nodeOf (x : Var) : CM Nat := do
  match L.varNode[x]? with
  | some i => rp L i
  | none => throw s!"x{x} has no layout node"

/-- The node of function `fn`'s answer. -/
def retOf (fn : Nat) : CM Nat := do
  match L.fnRet[fn]? with
  | some i => rp L i
  | none => throw s!"f{fn} has no answer node"

/-- The value moves between `a` and `b`: one node. -/
def same (w what : String) (a b : Nat) : CM Unit := do
  let ra ← rp L a
  let rb ← rp L b
  unless ra == rb do
    throw s!"{w}: {what}: the value moves between nodes {ra} ({short (← shp L ra)}) and {rb} ({short (← shp L rb)}), which are not joined"

/-- The child `k` of node `i`, as the analysis's places name it (`walk`'s `kid`): a pair's or a
sum's field, a cell's or a family's contents. -/
def kid (w : String) (i k : Nat) : CM Nat := do
  match ← shp L i, k with
  | .pair a _, 0 | .sum a _, 0 => rp L a
  | .pair _ b, _ | .sum _ b, _ => rp L b
  | .ref c, _ | .imm c, _ | .mut c, _ | .fam c, _ => rp L c
  | s, _ => throw s!"{w}: node {← rp L i} ({short s}) has no child {k}"

def pairOf (w : String) (i : Nat) : CM (Nat × Nat) := do
  match ← shp L i with
  | .pair a b => return (← rp L a, ← rp L b)
  | s => throw s!"{w}: node {← rp L i} ({short s}) is not a pair's"

def sumOf (w : String) (i : Nat) : CM (Nat × Nat) := do
  match ← shp L i with
  | .sum a b => return (← rp L a, ← rp L b)
  | s => throw s!"{w}: node {← rp L i} ({short s}) is not a sum's"

def closOf (w : String) (i : Nat) : CM (CodeKind × Option Nat × List Nat) := do
  match ← shp L i with
  | .clos k p r => pure (k, p, r)
  | s => throw s!"{w}: node {← rp L i} ({short s}) is not a closure class"

def isPtr : NK → Bool
  | .ref _ | .imm _ | .mut _ => true
  | _ => false

/-- One run-time cell is seen at the pointer nodes `a` and `b`. -/
def sameCell (w : String) (a b : Nat) : CM Unit := do
  let ra ← rp L a
  let rb ← rp L b
  if ra != rb && isPtr (← shp L ra) && isPtr (← shp L rb) then
    modify fun s => { s with sameCell := s.sameCell.push (ra, rb, w) }

/-! ### Every node is its type's -/

mutual
/-- Node `n` is a layout of the value type `t` (`build`), `env` the nodes of the type variables
bound around it. -/
def conf (w : String) : Nat → List Nat → LTy → Nat → CM Unit
  | 0, _, _, _ => throw s!"{w}: a type too deep"
  | f + 1, env, t, n => do
    let k ← shp L n
    let bad : CM Unit := do
      throw s!"{w}: node {← rp L n} ({short k}) is not a layout of the type {t}"
    match t, k with
    | .unit, .unit | .zero, .zero | .unk, .unk => pure ()
    | .opq _, .opq | .opq _, .int _ | .int _, .opq => pure ()
    | .int a, .int b => if a == b then pure () else bad
    | .pair a b, .pair x y | .sum a b, .sum x y => do
      conf w f env a x
      conf w f env b y
    | .ref a, .ref c | .ref a, .imm c | .ref a, .mut c
    | .imm a, .ref c | .imm a, .imm c | .imm a, .mut c
    | .mut a, .ref c | .mut a, .imm c | .mut a, .mut c
    | .fam a, .fam c => conf w f env a c
    | .tvar i, _ =>
      match env[i]? with
      | some m => if (← rp L m) == (← rp L n) then pure () else bad
      | none => throw s!"{w}: a free type variable {i}"
    | .mu a, _ => conf w f (n :: env) a n
    | .thunk c, _ => confC w f env c n
    | _, _ => bad
/-- Node `n` is the class of a closure of `c` (`buildC`). -/
def confC (w : String) : Nat → List Nat → LCTy → Nat → CM Unit
  | 0, _, _, _ => throw s!"{w}: a type too deep"
  | f + 1, env, c, n => do
    let k ← shp L n
    let bad : CM Unit := do
      throw s!"{w}: node {← rp L n} ({short k}) is not the class of a closure of {c}"
    match c, k with
    | .nu d, _ => confC w f (n :: env) d n
    | .ret a, .clos .unit none [r] => conf w f env a r
    | .arr a d, .clos .lam (some x) [r] => do
      conf w f env a x
      confR w f env d r
    | .amp d e, .clos .amp none [r, s] => do
      confR w f env d r
      confR w f env e s
    | .top, .unit => pure ()
    | _, _ => bad
/-- Node `n` is what running a closure of `c` answers (`repNode`). -/
def confR (w : String) : Nat → List Nat → LCTy → Nat → CM Unit
  | 0, _, _, _ => throw s!"{w}: a type too deep"
  | f + 1, env, c, n => do
    match c with
    | .ret a => conf w f env a n
    | .top =>
      match ← shp L n with
      | .unit => pure ()
      | k => throw s!"{w}: node {← rp L n} ({short k}) is not the answer of a closure of ⊤"
    | c => confC w f env c n
end

/-! ### Every move joins its two places -/

/-- A variable met in `w`: its node. -/
def see (w : String) (x : Var) : CM Nat := do
  modify fun s => if s.vars.contains x then s else { s with vars := s.vars.insert x w }
  nodeOf L x

/-- The contents `c` of a cell and the value `d` read from it through `Imm̲` (`load`) are related
as `joinRe` relates them: one node, or the same former with related children, where a pointer is
read as a shared one with its contents joined, and a closure or an opaque value is read as `Unk`. -/
def reCompat (w : String) (c d : Nat) : CM Unit := do
  let mut todo : List (Nat × Nat) := [(c, d)]
  let mut seen : Std.HashSet (Nat × Nat) := {}
  for _ in [0:1000000] do
    match todo with
    | [] => return
    | (x, y) :: rest =>
      todo := rest
      let rx ← rp L x
      let ry ← rp L y
      if rx == ry || seen.contains (rx, ry) then continue
      seen := seen.insert (rx, ry)
      match ← shp L rx, ← shp L ry with
      | .pair a b, .pair c d | .sum a b, .sum c d => todo := (a, c) :: (b, d) :: todo
      | .ref a, .imm c | .mut a, .imm c | .imm a, .imm c =>
        same L w "a pointer read through a shared borrow: its contents" a c
        sameCell L w rx ry
      | .fam a, .fam c => todo := (a, c) :: todo
      | .clos .., .unk | .opq, .unk => pure ()
      | kx, ky =>
        throw s!"{w}: a read through a shared borrow of contents at node {rx} ({short kx}) as node {ry} ({short ky}): not one node, and not a reading of it"
  throw s!"{w}: a read through a shared borrow too deep"

/-- The places a term's value moves to `dst`, and within it: each pair the analysis joins
(`Layout.lean`, `walk`), checked joined. -/
def walk (p : Prog) (w : String) : Nat → Tm → Nat → CM Unit
  | 0, _, _ => throw s!"{w}: a term too deep"
  | f + 1, t, dst => do
    let nv := see L w
    let eq := same L w
    let kd := kid L w
    match t with
    | .var x => eq "a value to its place" dst (← nv x)
    | .unit | .lit _ | .absurd _ => pure ()
    | .pair a b => do
      let (x, y) ← pairOf L w dst
      eq "a pair's first field" x (← nv a)
      eq "a pair's second field" y (← nv b)
    | .inj r a => do
      let (x, y) ← sumOf L w dst
      eq "an injection's payload" (if r then y else x) (← nv a)
    | .clos c env => do
      let r ← rp L dst
      let _ ← closOf L w r
      let u := L.union.getD r #[]
      unless u.contains c do
        throw s!"{w}: a closure of code c{c} is made at class {r}, whose codes {u.toList} do not hold c{c}"
      unless L.codeClass[c]? == some r do
        throw s!"{w}: a closure of code c{c} is made at class {r}, but c{c}'s class is {L.codeClass[c]?}"
      let some ce := L.codeEnv[c]? | throw s!"{w}: code c{c} has no environment nodes"
      unless ce.length == env.length do
        throw s!"{w}: a closure of code c{c} captures {env.length} values, its environment nodes are {ce.length}"
      for (x, e) in env.zip ce do eq s!"c{c}'s captured value x{x}" e (← nv x)
    | .app g a => do
      match ← closOf L w (← nv g) with
      | (.lam, some pn, [rn]) =>
        eq s!"the argument of x{g}" pn (← nv a)
        eq s!"the answer of x{g}" dst rn
      | _ => throw s!"{w}: x{g} is applied to an argument, and its class is not a function's"
    | .app0 g => do
      match ← closOf L w (← nv g) with
      | (.unit, _, [rn]) => eq s!"the answer of x{g}" dst rn
      | _ => throw s!"{w}: x{g} is run, and its class is not a thunk's"
    | .sel g j => do
      match ← closOf L w (← nv g) with
      | (.amp, _, rs) =>
        let some rn := rs[j]? | throw s!"{w}: component {j} of x{g}, whose class has {rs.length}"
        eq s!"component {j} of x{g}" dst rn
      | _ => throw s!"{w}: a component of x{g} is observed, and its class is not a `&`'s"
    | .call fn as => do
      let some fd := p.fns[fn]? | throw s!"{w}: no function f{fn}"
      unless as.length == fd.params.length do
        throw s!"{w}: f{fn} called on {as.length} arguments for {fd.params.length}"
      for (x, y) in as.zip fd.params do eq s!"f{fn}'s parameter x{y}" (← nv y) (← nv x)
      eq s!"f{fn}'s answer" dst (← retOf L fn)
    | .prim op as => do
      let a (i : Nat) : CM Nat := do
        match as[i]? with
        | some x => nv x
        | none => throw s!"{w}: a primitive without its argument {i}"
      match op with
      | .alloc | .allocLent | .staticCell _ => eq "a new cell's contents" (← kd dst 0) (← a 0)
      | .free => eq "a freed cell's contents" dst (← kd (← a 0) 0)
      | .swap => do
        let np ← kd dst 0
        eq "a swapped-in value" (← kd np 0) (← a 1)
        eq "a swapped-out value" (← kd dst 1) (← kd (← a 0) 0)
        sameCell L s!"{w}: a swap" (← a 0) np
      | .lend => do
        eq "a lend's owner" (← kd dst 0) (← a 0)
        let b ← kd dst 1
        eq "a lend's contents" (← kd b 0) (← kd (← a 0) 0)
        sameCell L s!"{w}: a lend" (← a 0) b
      | .relend => do
        eq "a reborrow's borrow" (← kd dst 0) (← a 0)
        eq "a reborrow" (← kd dst 1) (← a 0)
      | .load => reCompat L s!"{w}: a load" (← kd (← a 0) 0) dst
      | .take => do
        eq "a take's borrow" (← kd dst 0) (← a 0)
        eq "a take's contents" (← kd dst 1) (← kd (← a 0) 0)
      | .put => do
        eq "a put's contents" (← kd (← a 0) 0) (← a 1)
        eq "a put's borrow" dst (← a 0)
      | .slotPut => do
        eq "a slot's contents" (← kd (← kd (← a 0) 0) 0) (← a 2)
        eq "a slot put's array" dst (← a 0)
      | .slotTake => do
        eq "a slot take's array" (← kd dst 0) (← a 0)
        eq "a slot's contents" (← kd dst 1) (← kd (← kd (← a 0) 0) 0)
      | .size => eq "a family's size" (← kd dst 0) (← a 0)
      | .idx _ => eq "an index's leaf" (← kd dst 0) (← kd (← a 0) 0)
      | .split _ => do
        let l ← kd dst 0
        eq "a split's left part" (← kd l 0) (← a 0)
        eq "a split's right part" (← kd l 1) (← a 0)
        eq "a failed split's family" (← kd dst 1) (← a 0)
      | .replace => do
        eq "a replace's family" (← kd dst 0) (← a 0)
        let c ← kd (← kd (← a 0) 0) 0
        let o ← kd dst 1
        eq "a replaced slot's old value" (← kd o 0) c
        eq "a replace's refused value" (← kd o 1) (← a 2)
        eq "a replace's new value" c (← a 2)
      | .swapSlots => eq "a slot swap's family" dst (← a 0)
      | .tab fi | .tabLit fi .. => do
        let some fd := p.fns[fi]? | throw s!"{w}: no function f{fi}"
        match fd.params with
        | [pf, pa, _, _] => do
          eq s!"f{fi}'s function" (← a 0) (← nv pf)
          eq s!"f{fi}'s array" dst (← nv pa)
        | _ => throw s!"{w}: f{fi} is not a tab loop's function"
        eq s!"f{fi}'s answer" dst (← retOf L fi)
      | .roll | .unroll => eq "a fold" dst (← a 0)
      | .framePush m _ | .frameTop m _ => do
        let c ← kd dst 0
        match (← get).frames[m]? with
        | some fn => eq s!"machine {m}'s frame" fn c
        | none => modify fun s => { s with frames := s.frames.insert m c }
      | .framePut => eq "a frame's contents" (← kd (← a 0) 0) (← a 1)
      | .kappaPut s | .kappaTake s => do
        let c ← match op with
          | .kappaPut _ => a 1
          | _ => kd dst 1
        match (← get).regions[s]? with
        | some r => eq s!"site {s}'s κ region" r c
        | none => modify fun st => { st with regions := st.regions.insert s c }
      | .io .readByte | .io .clockNow => eq "a capability" (← kd dst 0) (← a 0)
      | .io .writeByte | .io .writeAll | .io .clockSleep => eq "a capability" dst (← kd (← a 0) 0)
      | .io .readInto => do
        eq "a capability" (← kd dst 0) (← kd (← a 0) 0)
        eq "a read's buffer" (← kd (← kd dst 1) 0) (← kd (← a 0) 1)
      | _ => pure ()
    | .letv x e b => do
      walk p w f e (← nv x)
      walk p w f b dst
    | .letpair x y q b => do
      let (l, r) ← pairOf L w (← nv q)
      eq s!"x{q}'s first field" l (← nv x)
      eq s!"x{q}'s second field" r (← nv y)
      walk p w f b dst
    | .case sv x b₁ y b₂ => do
      let (l, r) ← sumOf L w (← nv sv)
      eq s!"x{sv}'s left payload" l (← nv x)
      eq s!"x{sv}'s right payload" r (← nv y)
      walk p w f b₁ dst
      walk p w f b₂ dst
    | .copy x x' b => do
      eq s!"a copy of x{x}" (← nv x) (← nv x')
      walk p w f b dst
    | .drop x b => do
      let _ ← nv x
      walk p w f b dst

/-! ### Every code of a class fits it -/

/-- Code `c` in the class `R`: its kind and components are the class's, each function's argument
and answer are the class's, and its captured values are `codeEnv`'s. -/
def codeOk (p : Prog) (R c : Nat) : CM Unit := do
  let w := s!"class {R}, code c{c}"
  let (k, prm, res) ← closOf L w R
  let some code := p.codes[c]? | throw s!"{w}: no code c{c}"
  unless code.kind == k do throw s!"{w}: the code's kind is not the class's"
  unless code.fns.length == res.length do
    throw s!"{w}: the code has {code.fns.length} functions, the class {res.length} components"
  let some ce := L.codeEnv[c]? | throw s!"{w}: no environment nodes"
  for (fn, j) in code.fns.zipIdx do
    let some fd := p.fns[fn]? | throw s!"{w}: no function f{fn}"
    let k' := if k == .lam then fd.params.length - 1 else fd.params.length
    unless k' == ce.length do
      throw s!"{w}: f{fn} captures {k'} values, the code's environment nodes are {ce.length}"
    for (y, e) in (fd.params.take k').zip ce do
      same L w s!"f{fn}'s captured parameter x{y}" e (← nodeOf L y)
    if k == .lam then
      match prm, fd.params[k']? with
      | some pn, some y => same L w s!"f{fn}'s argument x{y}" pn (← nodeOf L y)
      | _, _ => throw s!"{w}: a function's code without its argument"
    match res[j]? with
    | some rn => same L w s!"f{fn}'s answer" rn (← retOf L fn)
    | none => throw s!"{w}: component {j} past the class's"

/-! ### The widths, the boxes and the heap classes -/

/-- The words of field `j` (child `c`) of node `v`. -/
def fieldW (v j c : Nat) : CM Nat := do
  if L.boxed.contains (v, j) then return 1
  match L.width[← rp L c]? with
  | some x => pure x
  | none => throw s!"node {c} has no width"

def fieldT (v j c : Nat) : CM Bool := do
  if L.boxed.contains (v, j) then return false
  match L.trivial[← rp L c]? with
  | some x => pure x
  | none => throw s!"node {c} has no triviality"

/-- The children of representative `v` its words hold inline: the fields not boxed, a class's
codes' environments when the class is not on the heap. -/
def inlineKids (v : Nat) : CM (Array Nat) := do
  match ← shp L v with
  | .pair a b | .sum a b => do
    let mut out := #[]
    if !L.boxed.contains (v, 0) then out := out.push (← rp L a)
    if !L.boxed.contains (v, 1) then out := out.push (← rp L b)
    pure out
  | .clos .. =>
    if L.recCls.contains v then return #[]
    let mut out := #[]
    for c in L.union.getD v #[] do
      for e in L.codeEnv.getD c [] do out := out.push (← rp L e)
    pure out
  | _ => pure #[]

/-- The layout equations: no cycle of inline children, and every representative's width and
triviality `resolve`'s over its children. -/
def layoutOk (L : Layouts) : CM Unit := do
  let n := L.rep.size
  for (v, j) in L.boxed.toList do
    unless L.rep[v]? == some v && j < 2 do throw s!"boxed field {v}.{j} is not a representative's"
    match ← shp L v with
    | .pair .. | .sum .. => pure ()
    | s => throw s!"boxed field {v}.{j} of a node that is not a pair's or a sum's ({short s})"
  for v in L.recCls.toList do
    unless L.rep[v]? == some v do throw s!"heap class {v} is not a representative"
    let _ ← closOf L s!"heap class {v}" v
  -- No cycle of inline children: a depth-first search, three colours.
  let mut kids : Array (Array Nat) := Array.replicate n #[]
  let mut edges := 0
  for v in [0:n] do
    if L.rep[v]! == v then
      let ks ← inlineKids L v
      kids := kids.set! v ks
      edges := edges + ks.size
  let mut color : Array UInt8 := Array.replicate n 0
  for root in [0:n] do
    if L.rep[root]! != root || color[root]! != 0 then continue
    let mut stack : List (Nat × Nat) := [(root, 0)]
    color := color.set! root 1
    for _ in [0:2 * (n + edges) + 2] do
      match stack with
      | [] => break
      | (v, i) :: rest =>
        match (kids[v]!)[i]? with
        | some c =>
          stack := (v, i + 1) :: rest
          if color[c]! == 1 then
            throw s!"node {v} holds node {c} inline, which holds it: a cycle with no box"
          if color[c]! == 0 then
            color := color.set! c 1
            stack := (c, 0) :: stack
        | none =>
          color := color.set! v 2
          stack := rest
  -- Widths and triviality.
  for v in [0:n] do
    if L.rep[v]! != v then continue
    let some wv := L.width[v]? | throw s!"node {v} has no width"
    let some tv := L.trivial[v]? | throw s!"node {v} has no triviality"
    let (we, te) ← match ← shp L v with
      | .unit | .zero | .unk => pure (0, true)
      | .int _ | .opq | .ref _ | .imm _ | .mut _ => pure (1, true)
      | .fam _ => pure (2, true)
      | .pair a b => pure ((← fieldW L v 0 a) + (← fieldW L v 1 b), (← fieldT L v 0 a) && (← fieldT L v 1 b))
      | .sum a b => pure (1 + max (← fieldW L v 0 a) (← fieldW L v 1 b), (← fieldT L v 0 a) && (← fieldT L v 1 b))
      | .clos .. =>
        if L.recCls.contains v then pure (1, false) else do
          let mut m := 0
          let mut tr := true
          for c in L.union.getD v #[] do
            let mut s := 0
            for e in L.codeEnv.getD c [] do
              let re ← rp L e
              s := s + L.width[re]!
              tr := tr && L.trivial[re]!
            m := max m s
          pure (1 + m, tr)
    unless wv == we do throw s!"node {v} ({short (← shp L v)}) has width {wv}, its children give {we}"
    unless tv == te do throw s!"node {v} ({short (← shp L v)}) has triviality {tv}, its children give {te}"

/-! ### Every cell holds its contents -/

def slotOf : Width → Option Nat
  | .w8 => some 1
  | .w32 | .f32 => some 4
  | _ => none

def cellsOk (L : Layouts) : CM Unit := do
  for v in [0:L.rep.size] do
    if L.rep[v]! != v then continue
    let c ← match ← shp L v with
      | .ref c | .imm c | .mut c => rp L c
      | _ => continue
    let some cw := L.cellWords[v]? | throw s!"pointer node {v} has no cell size"
    match L.slotBytes[v]? with
    | some b =>
      match ← shp L c with
      | .int x => unless slotOf x == some b do throw s!"pointer node {v}'s cell is a {b}-byte slot, its contents a {reprStr x}"
      | s => throw s!"pointer node {v}'s cell is a {b}-byte slot, its contents not an integer ({short s})"
    | none =>
      unless cw ≥ L.width[c]! do
        throw s!"pointer node {v}'s cell has {cw} words, its contents node {c} has {L.width[c]!}"
  for (a, b, w) in (← get).sameCell do
    unless L.cellWords[a]? == L.cellWords[b]? && L.slotBytes[a]? == L.slotBytes[b]? do
      throw s!"{w}: one cell is seen at pointer nodes {a} ({L.cellWords[a]?} words, slot {L.slotBytes[a]?}) and {b} ({L.cellWords[b]?} words, slot {L.slotBytes[b]?})"

end

/-- Every move of the program: each function's body to its answer, `main`'s to its node. -/
def walkProg (p : Prog) (L : Layouts) : CM Unit := do
  for (fd, i) in p.fns.toList.zipIdx do
    let w := s!"f{i} ({fd.name})"
    for x in fd.params do let _ ← see L w x
    walk L p w (1 <<< 22) fd.body (← retOf L i)
  walk L p "main" (1 <<< 22) p.main (← rp L L.mainNode)

/-- **The closure classes and layouts of a program's LIR are a solution of its constraints**:
every check of this module's header. -/
def check (p : Prog) (L : Layouts) : Except String Unit := do
  let n := L.rep.size
  unless L.shape.size == n && L.width.size == n && L.trivial.size == n do
    throw s!"the layouts' arrays differ in size"
  for i in [0:n] do
    let r := L.rep[i]!
    unless r < n && L.rep[r]! == r do throw s!"node {i}'s representative {r} is not its own"
  let act : CM Unit := do
    -- Every code of a class fits it: first, so that a code's own nodes are reported as its own.
    -- The analysis keeps an entry, empty, at every node it joined: only classes with codes.
    for (R, cs) in L.union.toList do
      if cs.isEmpty then continue
      unless L.rep[R]? == some R do throw s!"class {R} is not a representative"
      let _ ← closOf L s!"class {R}" R
      let mut seen : Std.HashSet Nat := {}
      for c in cs do
        if seen.contains c then throw s!"class {R} holds code c{c} twice"
        seen := seen.insert c
        codeOk L p R c
    walkProg p L
    -- Every node is its type's.
    for (x, w) in (← get).vars.toList do
      let some t := p.ty[x]? | throw s!"{w}: x{x} has no type"
      conf L s!"{w}: x{x}" 4096 [] t (← nodeOf L x)
    for (fd, i) in p.fns.toList.zipIdx do
      conf L s!"f{i} ({fd.name})'s answer" 4096 [] fd.ret (← retOf L i)
    conf L "main's value" 4096 [] p.mainTy (← rp L L.mainNode)
    -- The κ regions are the layouts'.
    for (s, r) in (← get).regions.toList do
      match L.regions[s]? with
      | some r' => same L s!"site {s}" "its κ region" r r'
      | none => throw s!"site {s} has no κ region node"
    -- `codeClass` is the inverse of the classes' codes.
    for (R, cs) in L.union.toList do
      for c in cs do
        unless L.codeClass[c]? == some R do
          throw s!"class {R} holds code c{c}, whose class is {L.codeClass[c]?}"
    for (c, R) in L.codeClass.toList do
      unless (L.union.getD R #[]).contains c do
        throw s!"code c{c}'s class is {R}, whose codes do not hold it"
    layoutOk L
    cellsOk L
  let _ ← act.run {}

/-! ### The closure flow -/

/-- What the flow's check reads. -/
structure FCtx where
  p : Prog
  L : Layouts
  sets : Std.HashMap Var (Std.HashSet Nat)
  /-- The flow's pseudo-variables of the functions' answers start here (`Flow.retVar`). -/
  base : Nat

namespace FCtx
variable (F : FCtx)

def tyOf (x : Var) : Option LTy :=
  if x ≥ F.base then (F.p.fns[x - F.base]?.map (·.ret)) else F.p.ty[x]?

def isClos (x : Var) : Bool := match F.tyOf x with
  | some (.thunk _) => true
  | _ => false

def setOf (x : Var) : Std.HashSet Nat := F.sets.getD x {}

/-- `y`'s codes move to `x`. -/
def sub (w : String) (y x : Var) : Except String Unit := do
  if !(F.isClos y && F.isClos x) then return
  let sx := F.setOf x
  for c in F.setOf y do
    unless sx.contains c do
      throw s!"{w}: code c{c} reaches x{y} and moves to x{x}, whose set does not hold it"

/-- `x` is read out of data: it holds its class's codes. -/
def coarse (w : String) (x : Var) : Except String Unit := do
  if !F.isClos x then return
  let sx := F.setOf x
  let some i := F.L.varNode[x]? | throw s!"{w}: x{x} has no layout node"
  for c in F.L.union.getD (F.L.rep[i]?.getD i) #[] do
    unless sx.contains c do
      throw s!"{w}: x{x} is read out of data and its class holds c{c}, which its set does not"

/-- A call of `g` at component `j`: every code in `g`'s set moves the argument to its parameter
and its answer to the call's. -/
def site (w : String) (dst : Option Var) (g : Var) (arg : Option Var) (j : Nat) :
    Except String Unit := do
  for c in F.setOf g do
    let some code := F.p.codes[c]? | throw s!"{w}: no code c{c}"
    let some fn := code.fns[j]? | throw s!"{w}: code c{c} has no component {j}"
    let some fd := F.p.fns[fn]? | throw s!"{w}: no function f{fn}"
    if let some a := arg then
      let some prm := fd.params.getLast? | throw s!"{w}: f{fn} has no argument"
      F.sub s!"{w}: x{g}'s code c{c}'s argument" a prm
    if let some d := dst then F.sub s!"{w}: x{g}'s code c{c}'s answer" (F.base + fn) d

/-- The flow constraints of a term whose value goes to `dst` (`Flow.gen`). -/
def go (w : String) : Nat → Tm → Option Var → Except String Unit
  | 0, _, _ => throw s!"{w}: a term too deep"
  | f + 1, t, dst => do
    match t with
    | .var y => if let some d := dst then F.sub w y d
    | .clos c env => do
      if let some d := dst then
        unless (F.setOf d).contains c do
          throw s!"{w}: a closure of code c{c} at x{d}, whose set does not hold it"
      let some code := F.p.codes[c]? | throw s!"{w}: no code c{c}"
      for fn in code.fns do
        let some fd := F.p.fns[fn]? | throw s!"{w}: no function f{fn}"
        for (x, y) in env.zip fd.params do F.sub s!"{w}: c{c}'s captured value" x y
    | .app g a => F.site w dst g (some a) 0
    | .app0 g => F.site w dst g none 0
    | .sel g j => F.site w dst g none j
    | .call fn as => do
      let some fd := F.p.fns[fn]? | throw s!"{w}: no function f{fn}"
      for (x, y) in as.zip fd.params do F.sub s!"{w}: f{fn}'s argument" x y
      if let some d := dst then F.sub s!"{w}: f{fn}'s answer" (F.base + fn) d
    | .prim (.tab fi) as | .prim (.tabLit fi ..) as => do
      let some fd := F.p.fns[fi]? | throw s!"{w}: no function f{fi}"
      if let (some g, some pf) := (as.head?, fd.params.head?) then
        F.sub s!"{w}: f{fi}'s function" g pf
    | .prim _ _ => if let some d := dst then F.coarse w d
    | .letv x e b => do
      go w f e (some x)
      go w f b dst
    | .letpair x y _ b => do
      F.coarse w x
      F.coarse w y
      go w f b dst
    | .case _ x b₁ y b₂ => do
      F.coarse w x
      F.coarse w y
      go w f b₁ dst
      go w f b₂ dst
    | .copy x x' b => do
      F.sub w x x'
      go w f b dst
    | .drop _ b => go w f b dst
    | .unit | .lit _ | .pair .. | .inj .. | .absurd _ => pure ()

end FCtx

/-- **The closure flow's sets are a solution of its constraints** (`Backend2/Flow.lean`, `gen`,
`link`, `coarse`): a closure made of code `c` holds `c`; a move (a value to its place, a copy, an
argument to its parameter, a captured value to its function's, an answer to its call's) carries
its set; every code in a call's function's set moves the call's argument to that code's parameter
and its answer to the call's; a closure read out of data holds its class's codes. And every direct
call (`known`) is of a variable whose set is that one code. -/
def checkFlow (p : Prog) (L : Layouts) (sets : Std.HashMap Var (Std.HashSet Nat))
    (known : Std.HashMap Var Nat) : Except String Unit := do
  let F : FCtx := { p, L, sets, base := p.ty.fold (fun m x _ => max m (x + 1)) 0 }
  for (fd, i) in p.fns.toList.zipIdx do
    let dst := match fd.ret with
      | .thunk _ => some (F.base + i)
      | _ => none
    F.go s!"f{i} ({fd.name})" (1 <<< 22) fd.body dst
  F.go "main" (1 <<< 22) p.main none
  for (x, c) in known.toList do
    let s := F.setOf x
    unless s.size == 1 && s.contains c do
      throw s!"a direct call of x{x} at code c{c}, whose set is {s.toList}"

/-! ### Reject tests: the checks refuse wrong layouts

Each perturbation changes one fact of a program's layouts or closure flow as `Lower` would read
it, and is aimed at one family of the checks; the checks must refuse every one, by that family's
refusal (`bcc lir --layout-reject`, `scripts/check-layout-reject.sh`). A perturbation with no
target in a program is `n/a` there. -/

/-- The sorted keys of a map. -/
def sortedKeys {β} (m : Std.HashMap Nat β) : List Nat := (m.toList.map (·.1)).mergeSort (· ≤ ·)

/-- The closure classes with codes, in order. -/
def classes (L : Layouts) : List Nat :=
  (sortedKeys L.union).filter fun R => !(L.union.getD R #[]).isEmpty

def isPtrNK : NK → Bool
  | .ref _ | .imm _ | .mut _ => true
  | _ => false

/-- A fresh node, a copy of node `i`'s representative: its shape, width, triviality and cell. -/
def freshOf (L : Layouts) (i : Nat) : Layouts × Nat :=
  let r := L.r i
  let n := L.rep.size
  let L' := { L with rep := L.rep.push n, shape := L.shape.push L.shape[r]!,
                     width := L.width.push L.width[r]!, trivial := L.trivial.push L.trivial[r]! }
  let L' := match L.cellWords[r]? with
    | some w => { L' with cellWords := L'.cellWords.insert n w }
    | none => L'
  let L' := match L.slotBytes[r]? with
    | some b => { L' with slotBytes := L'.slotBytes.insert n b }
    | none => L'
  (L', n)

/-- The layouts with variable `x`'s node a fresh copy of it. -/
def splitNode (L : Layouts) (x : Var) : Layouts :=
  let (L', n) := freshOf L (L.node x)
  { L' with varNode := L'.varNode.insert x n }

/-- Every `letv x e _` of a term, in the order the checks walk them. -/
def binds : Nat → Tm → List (Var × Tm)
  | 0, _ => []
  | f + 1, t => match t with
    | .letv x e b => (x, e) :: (binds f e ++ binds f b)
    | .letpair _ _ _ b | .copy _ _ b | .drop _ b => binds f b
    | .case _ _ b₁ _ b₂ => binds f b₁ ++ binds f b₂
    | _ => []

def progBinds (p : Prog) : List (Var × Tm) :=
  (p.fns.toList.flatMap fun fd => binds (1 <<< 22) fd.body) ++ binds (1 <<< 22) p.main

/-- The pointer nodes at which the walk sees one run-time cell (`sameCell`). -/
def sameCellPairs (p : Prog) (L : Layouts) : Array (Nat × Nat × String) :=
  match (walkProg p L).run {} with
  | .ok (_, s) => s.sameCell
  | .error _ => #[]

/-- Merge class `b` into class `a` with everything the two classes hold, node for node, as the
analysis would had their closures met (`a`'s width kept): `none` where their nodes are not of one
shape, node for node. -/
def mergeClasses (L : Layouts) (a b : Nat) : Option Layouts := Id.run do
  let mut redir : Std.HashMap Nat Nat := {}
  let mut todo : List (Nat × Nat) := [(a, b)]
  let fd (m : Std.HashMap Nat Nat) (x : Nat) : Nat := Id.run do
    let mut y := L.r x
    for _ in [0:L.rep.size + 1] do
      match m[y]? with
      | some z => y := z
      | none => break
    return y
  for _ in [0:100000] do
    match todo with
    | [] => break
    | (x, y) :: rest =>
      todo := rest
      let rx := fd redir x
      let ry := fd redir y
      if rx == ry then continue
      let kids : Option (List (Nat × Nat)) := match L.shape[rx]!, L.shape[ry]! with
        | .pair u v, .pair u' v' | .sum u v, .sum u' v' => some [(u, u'), (v, v')]
        | .ref u, .ref u' | .imm u, .imm u' | .mut u, .mut u' | .fam u, .fam u' => some [(u, u')]
        | .clos k pa ra, .clos k' pa' ra' =>
          if k == k' && ra.length == ra'.length && pa.isSome == pa'.isSome then
            some ((match pa, pa' with | some u, some u' => [(u, u')] | _, _ => []) ++ ra.zip ra')
          else none
        | kx, ky => if kx == ky then some [] else none
      let some ks := kids | return none
      redir := redir.insert ry rx
      todo := ks ++ todo
  if !todo.isEmpty then return none
  let rep := L.rep.map (fd redir)
  let mut union := L.union
  let mut codeClass := L.codeClass
  for (y, x) in redir.toList do
    let x := fd redir x
    let uy := L.union.getD y #[]
    if uy.isEmpty then continue
    let u := ((union.getD x #[]).toList ++ uy.toList).mergeSort (· ≤ ·)
    union := (union.erase y).insert x u.toArray
    for c in uy do codeClass := codeClass.insert c x
  return some { L with rep, union, codeClass }

/-- The perturbations of the layouts, each named: `none` where the program has no target. -/
def perturbLayouts (p : Prog) (L : Layouts) : List (String × Option Layouts) :=
  let cls := classes L
  let multi := (cls.find? fun R => (L.union.getD R #[]).size ≥ 2).orElse fun _ => cls.head?
  let dropCode := multi.map fun R =>
    let u := L.union.getD R #[]
    { L with union := L.union.insert R (u.erase u[0]!) }
  let dropClassOf := cls.head?.map fun R =>
    let c := (L.union.getD R #[])[0]!
    { L with codeClass := L.codeClass.erase c }
  -- Two classes of one shape, node for node, the second wider: merged at the first's width.
  let merge := Id.run do
    let mut tries := 0
    for a in cls do
      for b in cls do
        if a == b || L.width[b]! ≤ L.width[a]! then continue
        tries := tries + 1
        if tries > 20000 then return none
        if let some L' := mergeClasses L a b then return some L'
    return none
  let width := cls.head?.map fun R => { L with width := L.width.set! R (L.width[R]! + 1) }
  let triv := (cls.find? fun R => !L.trivial[R]! && !L.recCls.contains R).map fun R =>
    { L with trivial := L.trivial.set! R true }
  -- A code's own nodes: its environment, its argument, its answer, each a fresh node.
  let codeOf (R : Nat) : Option (Nat × Nat × Fn) := do
    let c ← (L.union.getD R #[])[0]?
    let code ← p.codes[c]?
    let fn ← code.fns.head?
    let fd ← p.fns[fn]?
    pure (c, fn, fd)
  let envC := cls.findSome? fun R => do
    let (c, _, _) ← codeOf R
    let e ← (L.codeEnv.getD c [])[0]?
    let (L', n) := freshOf L e
    pure { L' with codeEnv := L'.codeEnv.insert c (n :: (L.codeEnv.getD c []).drop 1) }
  let argC := cls.findSome? fun R => do
    let .clos .lam _ _ := L.shape[R]! | none
    let (_, _, fd) ← codeOf R
    let y ← fd.params.getLast?
    pure (splitNode L y)
  let ansC := cls.findSome? fun R => do
    let (_, fn, _) ← codeOf R
    let r ← L.fnRet[fn]?
    let (L', n) := freshOf L r
    pure { L' with fnRet := L'.fnRet.insert fn n }
  let boxes := (L.boxed.toList.mergeSort fun x y => x.1 < y.1 || (x.1 == y.1 && x.2 ≤ y.2))
  let unbox := boxes.head?.map fun b => { L with boxed := L.boxed.erase b }
  let heap := ((L.recCls.toList.mergeSort (· ≤ ·)).head?).map fun R =>
    { L with recCls := L.recCls.erase R }
  let ptrs := (List.range L.rep.size).filter fun v => L.rep[v]! == v && isPtrNK L.shape[v]!
  let cells := ptrs.filter fun v => L.cellWords.getD v 0 > 0 && !L.slotBytes.contains v
  let shrink := cells.head?.map fun v => { L with cellWords := L.cellWords.insert v (L.cellWords.getD v 0 - 1) }
  let slot := (ptrs.find? (L.slotBytes.contains ·)).map fun v =>
    { L with slotBytes := L.slotBytes.insert v (if L.slotBytes.getD v 0 == 1 then 4 else 1) }
  let pairs := sameCellPairs p L
  let twoSizes := pairs[0]?.map fun (a, _, _) =>
    { L with cellWords := L.cellWords.insert a (L.cellWords.getD a 0 + 1) }
  let region := ((sortedKeys L.regions).head?).map fun s =>
    let (L', n) := freshOf L (L.regions.getD s 0)
    { L' with regions := L'.regions.insert s n }
  -- The second frame access of a machine, its frame node a fresh copy.
  let bs := progBinds p
  let frameSites := bs.filterMap fun (x, e) => match e with
    | .prim (.framePush m _) _ | .prim (.frameTop m _) _ => some (m, x)
    | _ => none
  let frame := Id.run do
    let mut seen : Std.HashSet Nat := {}
    for (m, x) in frameSites do
      if seen.contains m then
        let nx := L.node x
        if let .pair a b := L.shape[nx]! then
          let (L', n) := freshOf L a
          return some { L' with shape := L'.shape.set! nx (.pair n b) }
      seen := seen.insert m
    return none
  -- A read through a shared borrow of an integer, its reading a fresh node.
  let reread := (bs.find? fun (x, e) => match e with
      | .prim .load _ => (match L.shape[L.node x]! with | .int _ => true | _ => false)
      | _ => false).map fun (x, _) => splitNode L x
  let shared := Id.run do
    let mut seen : Std.HashMap Nat Var := {}
    let mut out : Option Var := none
    for x in sortedKeys L.varNode do
      let r := L.node x
      if seen.contains r then out := some x; break
      seen := seen.insert r x
    return out
  let split := shared.map (splitNode L)
  [("drop a code from its class", dropCode),
   ("drop a code's class", dropClassOf),
   ("merge two classes of one shape and different widths", merge),
   ("change a class's width", width),
   ("call a class trivial", triv),
   ("move a code's environment node", envC),
   ("move a code's argument node", argC),
   ("move a code's answer node", ansC),
   ("unbox a boxed field", unbox),
   ("keep a heap class's environment inline", heap),
   ("shrink a cell", shrink),
   ("give a slot the wrong width", slot),
   ("give one cell two sizes", twoSizes),
   ("move a κ region's node", region),
   ("move a machine's frame node at one access", frame),
   ("move a reborrowed read's node", reread),
   ("split a variable's node from the places it is joined with", split)]

/-- The perturbations of the closure flow, each named. -/
def perturbFlow (p : Prog) (sets : Std.HashMap Var (Std.HashSet Nat)) (known : Std.HashMap Var Nat) :
    List (String × Option (Std.HashMap Var (Std.HashSet Nat) × Std.HashMap Var Nat)) :=
  let withCodes := (sortedKeys sets).filter fun x => !(sets.getD x {}).isEmpty
  let dropSet := withCodes.head?.map fun x =>
    let s := sets.getD x {}
    let c := (s.toList.mergeSort (· ≤ ·))[0]!
    (sets.insert x (s.erase c), known)
  let several := withCodes.find? fun x => (sets.getD x {}).size ≥ 2
  let wrongKnown := several.map fun x =>
    (sets, known.insert x (((sets.getD x {}).toList.mergeSort (· ≤ ·))[0]!))
  -- A call's answer set without a code its callee's answer holds: the answer link.
  let base := p.ty.fold (fun m x _ => max m (x + 1)) 0
  let isClosV (x : Var) : Bool := match p.ty[x]? with
    | some (.thunk _) => true
    | _ => false
  let answer := (progBinds p).findSome? fun (d, e) => do
    let (g, j) ← match e with
      | .app g _ | .app0 g => some (g, 0)
      | .sel g j => some (g, j)
      | _ => none
    if !isClosV d then none
    let sd := sets.getD d {}
    (sets.getD g {}).toList.findSome? fun c => do
      let code ← p.codes[c]?
      let fn ← code.fns[j]?
      let fd ← p.fns[fn]?
      let .thunk _ := fd.ret | none
      let c' ← (sets.getD (base + fn) {}).toList.find? sd.contains
      pure (sets.insert d (sd.erase c'), known)
  [("drop a code from a variable's flow set", dropSet),
   ("drop a code from a call's answer", answer),
   ("a direct call where several codes reach", wrongKnown)]

end Backend2.LayCheck

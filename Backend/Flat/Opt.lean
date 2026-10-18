import Std.Data.HashMap
import Std.Data.HashSet
import Backend.Flat.Syntax
import Backend.Flat.Interp

/-!
# Backend — the flat IR's specializer  `[spec §41]`

A pass from flat IR to flat IR, run on every program before either target, that makes the loops
of a program loops of their own functions (`Backend/README.md`, *Loops as loops*). The flat IR
from `Lower` runs a loop that may diverge one observation at a time: `drive` calls the codata's
code, which runs one turn of the step and answers the next state, a closure in the loop type's
union, and `drive` passes those words back to itself. Every tag in such a state is a literal
(`Exp.tag`) where it is built. The pass is a partial evaluator that meets those literals with
the tests that take them apart:

- **Inlining** (`inlinable`, `doCall`). A call is replaced by its callee's body, parameters bound
  to the arguments, locals renamed, frame slots moved into the caller's frame, when the callee
  does not call itself, is on the path at most once (twice when a tag it tests is a literal
  argument), and is small, called once, or meets such a tag. A `ret` of the body goes to the
  call's continuation (`Kont`).
- **Known words** (`Ctx`). A local set to an atom is that atom where it is read, and its set is
  made only where a join reads it (`Ctx.lazy`, `Join.mat`); a test of a known word keeps one
  branch; a `switch` case knows its operand, and an `ite` on `eqz x` knows `x = 0` in `then`.
- **Continuations into exits.** When the statements after a call test its results, they are
  copied into each exit of the inlined body where the copies are cheap (`cpsCost`, `kontCost`),
  so that each exit's literal decides the test. Otherwise they follow the call once, and each
  exit tries a copy specialized to what it knows that ends the function in a few statements
  (`tryCopy`); so do the branches of an `ite` or a `switch` whose statements after it test what
  the branches set.
- **Call-pattern specialization** (`specOf`). A call of a function on a cycle of the call graph
  with tags among its arguments is a call of the function's copy for those tags, made once per
  function and pattern. `drive`'s self-call on the next state's tags is then a self tail call of
  the copy for that state.
- **Narrowing.** Sets nothing reads, of words with no effect, are removed (`dropDeadSets`), and so
  are parameters no function reads, at every call (`dropDeadParams`); branches that end in a
  tail call of one function share one, after them (`mergeExits`); locals are renumbered
  (`compact`).

Every run computes what it computed: the pass removes only words no run reads and tests whose
answer is known, and an inlined body runs the same statements in the same order, so the output,
allocations, copies, loads, stores and bounds checks of a run are unchanged. A dispatched call
whose closure's tag becomes a literal is a direct call, and is no longer counted.

The pass is bounded: a function past `budget` statements is built again without copied
continuations (`OState.modest`), a try of a copy stops past `copyWork` statements expanded, a
function has at most `specMax` copies, and nesting stops at `depthMax`.
-/

namespace Backend.Flat.Opt
open BoCa

/-! ### Measures and traversals -/

mutual
/-- `e` with the locals replaced by `σ`, and frame slots moved by `fb` words. -/
def subE (σ : Nat → Exp) (fb : Nat) : Exp → Exp
  | .loc i => σ i
  | .load a o => .load (subE σ fb a) o
  | .load8 a => .load8 (subE σ fb a)
  | .op o as => .op o (subEs σ fb as)
  | .alloc w => .alloc (subE σ fb w)
  | .slot off w => .slot (fb + off) w
  | .getc f => .getc (subE σ fb f)
  | .getv a b c => .getv (subE σ fb a) (subE σ fb b) (subE σ fb c)
  | .now c => .now (subE σ fb c)
  | e => e
def subEs (σ : Nat → Exp) (fb : Nat) : List Exp → List Exp
  | [] => []
  | e :: es => subE σ fb e :: subEs σ fb es
end

mutual
/-- The locals `e` reads. -/
def readsE : Exp → List Nat
  | .loc i => [i]
  | .load a _ | .load8 a | .alloc a | .getc a | .now a => readsE a
  | .op _ as => readsEs as
  | .getv a b c => readsE a ++ readsE b ++ readsE c
  | _ => []
def readsEs : List Exp → List Nat
  | [] => []
  | e :: es => readsE e ++ readsEs es
end

/-- An integer operation, with no trap: its value on literals is the same on every target. -/
def foldable : HostOp → Bool
  | .bin .. | .un .. | .eqz _ | .rel .. | .wrap | .extend_s | .extend_u | .extend32_s | .wrap8
  | .extend8_u => true
  | _ => false

mutual
/-- `e`'s value when it is a literal, or an integer operation on literals. -/
def cval : Exp → Option UInt64
  | .c64 n => some n
  | .c32 n => some n.toUInt64
  | .tag n => some n
  | .op o as =>
    if foldable o then
      match cvals as with
      | some vs => match evalOp o vs with
        | .ok v => some v
        | .error _ => none
      | none => none
    else none
  | _ => none
def cvals : List Exp → Option (List UInt64)
  | [] => some []
  | e :: es => match cval e, cvals es with
    | some v, some vs => some (v :: vs)
    | _, _ => none
end

mutual
/-- `e` has no effect: removing it changes nothing a run observes. -/
def pureE : Exp → Bool
  | .loc _ | .c64 _ | .c32 _ | .data _ | .tag _ | .undef => true
  | .op o as => (match o with | .div .. | .trunc .. => false | _ => true) && pureEs as
  | _ => false
def pureEs : List Exp → Bool
  | [] => true
  | e :: es => pureE e && pureEs es
end

/-- A word that is known where it is read: a literal, a local, a data address. -/
def isAtom : Exp → Bool
  | .loc _ | .c64 _ | .c32 _ | .data _ | .tag _ | .undef => true
  | _ => false

/-- A tag, as a specialization's pattern holds it. -/
def lit? : Exp → Option (Bool × UInt64)
  | .tag n => some (false, n)
  | _ => none

/-- Two atoms are the same word. -/
def atomEq : Exp → Exp → Bool
  | .loc a, .loc b => a == b
  | .c64 a, .c64 b => a == b
  | .c32 a, .c32 b => a == b
  | .data a, .data b => a == b
  | .tag a, .tag b => a == b
  | _, _ => false

def litExp : Bool × UInt64 → Exp
  | (_, n) => .tag n

mutual
def sizeS : Stmt → Nat
  | .ite _ t e => 1 + sizeL t + sizeL e
  | .switch _ cs d => 1 + sizeLL cs + sizeL d
  | .tickBound => 0
  | _ => 1
def sizeL : List Stmt → Nat
  | [] => 0
  | s :: ss => sizeS s + sizeL ss
def sizeLL : List (List Stmt) → Nat
  | [] => 0
  | c :: cs => sizeL c + sizeLL cs
end

mutual
/-- Every path through `s` ends the function: a `ret`, a tail call or a `trap`. -/
def termS : Stmt → Bool
  | .ret _ | .tailCall .. | .trap => true
  | .ite _ t e => termL t && termL e
  | .switch _ cs d => termLL cs && termL d
  | _ => false
def termL : List Stmt → Bool
  | [] => false
  | s :: ss => termS s || termL ss
def termLL : List (List Stmt) → Bool
  | [] => true
  | c :: cs => termL c && termLL cs
end

mutual
/-- `s` contains a `ret` or a tail call. -/
def exitS : Stmt → Bool
  | .ret _ | .tailCall .. => true
  | .ite _ t e => exitL t || exitL e
  | .switch _ cs d => exitLL cs || exitL d
  | _ => false
def exitL : List Stmt → Bool
  | [] => false
  | s :: ss => exitS s || exitL ss
def exitLL : List (List Stmt) → Bool
  | [] => false
  | c :: cs => exitL c || exitLL cs
end

mutual
/-- The functions `s` calls or tail-calls. -/
def calleesS : Stmt → List Nat
  | .call _ f _ | .tailCall f _ => [f]
  | .ite _ t e => calleesL t ++ calleesL e
  | .switch _ cs d => calleesLL cs ++ calleesL d
  | _ => []
def calleesL : List Stmt → List Nat
  | [] => []
  | s :: ss => calleesS s ++ calleesL ss
def calleesLL : List (List Stmt) → List Nat
  | [] => []
  | c :: cs => calleesL c ++ calleesLL cs
end

mutual
/-- The locals `s` sets: a `set`'s and a call's destinations. -/
def setsS : Stmt → List Nat
  | .set i _ => [i]
  | .call ds _ _ => ds
  | .ite _ t e => setsL t ++ setsL e
  | .switch _ cs d => setsLL cs ++ setsL d
  | _ => []
def setsL : List Stmt → List Nat
  | [] => []
  | s :: ss => setsS s ++ setsL ss
def setsLL : List (List Stmt) → List Nat
  | [] => []
  | c :: cs => setsL c ++ setsLL cs
end

/-- The expressions a statement evaluates, outside its branches. -/
def stmtExps : Stmt → List Exp
  | .set _ e | .free e | .unslot e | .out e | .status e => [e]
  | .store a _ v | .store8 a v | .putc a v | .sleep a v => [a, v]
  | .putv a b c => [a, b, c]
  | .ite c _ _ => [c]
  | .switch e _ _ => [e]
  | .call _ _ as | .tailCall _ as => as
  | .ret es => es
  | _ => []

mutual
/-- The locals `s` reads. -/
def readsS : Stmt → List Nat
  | .ite c t e => readsE c ++ readsL t ++ readsL e
  | .switch x cs d => readsE x ++ readsLL cs ++ readsL d
  | s => readsEs (stmtExps s)
def readsL : List Stmt → List Nat
  | [] => []
  | s :: ss => readsS s ++ readsL ss
def readsLL : List (List Stmt) → List Nat
  | [] => []
  | c :: cs => readsL c ++ readsLL cs
end

mutual
/-- The statements an expansion copies to put every exit of `ss` last: for an `ite` or a
`switch` that holds an exit and is not last, the statements after it, once per branch that does
not end the function. -/
def dupL : List Stmt → Nat
  | [] => 0
  | s :: ss => dupS s (sizeL ss) + dupL ss
def dupS (s : Stmt) (after : Nat) : Nat := match s with
  | .ite _ t e =>
    (if after > 0 && (exitL t || exitL e) && !termL t && !termL e then after else 0) +
      dupL t + dupL e
  | .switch _ cs d =>
    (if after > 0 && (exitLL cs || exitL d) then after * (cs.length + 1) else 0) +
      dupLL cs + dupL d
  | _ => 0
def dupLL : List (List Stmt) → Nat
  | [] => 0
  | c :: cs => dupL c + dupLL cs
end

mutual
/-- The `ret`s and tail calls of `ss`. -/
def exitsL : List Stmt → Nat
  | [] => 0
  | s :: ss => exitsS s + exitsL ss
def exitsS : Stmt → Nat
  | .ret _ | .tailCall .. => 1
  | .ite _ t e => exitsL t + exitsL e
  | .switch _ cs d => exitsLL cs + exitsL d
  | _ => 0
def exitsLL : List (List Stmt) → Nat
  | [] => 0
  | c :: cs => exitsL c + exitsLL cs
end

mutual
/-- The locals the tests of `ss` read: `ite` conditions and `switch` operands. -/
def testsL : List Stmt → List Nat
  | [] => []
  | s :: ss => testsS s ++ testsL ss
def testsS : Stmt → List Nat
  | .ite c t e => readsE c ++ testsL t ++ testsL e
  | .switch x cs d => readsE x ++ testsLL cs ++ testsL d
  | _ => []
def testsLL : List (List Stmt) → List Nat
  | [] => []
  | c :: cs => testsL c ++ testsLL cs
end

mutual
/-- The copies `set x := loc y` of `ss`, as `(x, y)`. -/
def copiesL : List Stmt → List (Nat × Nat)
  | [] => []
  | s :: ss => copiesS s ++ copiesL ss
def copiesS : Stmt → List (Nat × Nat)
  | .set x (.loc y) => [(x, y)]
  | .ite _ t e => copiesL t ++ copiesL e
  | .switch _ cs d => copiesLL cs ++ copiesL d
  | _ => []
def copiesLL : List (List Stmt) → List (Nat × Nat)
  | [] => []
  | c :: cs => copiesL c ++ copiesLL cs
end

mutual
/-- For each argument `.loc p` passed bare to parameter `q` of `g`: `(p, g, q)`. -/
def passesS : Stmt → List (Nat × Nat × Nat)
  | .call _ g as | .tailCall g as => as.zipIdx.filterMap fun (a, q) => match a with
    | .loc p => some (p, g, q)
    | _ => none
  | .ite _ t e => passesL t ++ passesL e
  | .switch _ cs d => passesLL cs ++ passesL d
  | _ => []
def passesL : List Stmt → List (Nat × Nat × Nat)
  | [] => []
  | s :: ss => passesS s ++ passesL ss
def passesLL : List (List Stmt) → List (Nat × Nat × Nat)
  | [] => []
  | c :: cs => passesL c ++ passesLL cs
end

mutual
/-- The exits of `ss`: each `ret`'s words, or a tail call's callee. -/
def exitsOfL : List Stmt → List (List Exp ⊕ Nat)
  | [] => []
  | s :: ss => exitsOfS s ++ exitsOfL ss
def exitsOfS : Stmt → List (List Exp ⊕ Nat)
  | .ret es => [.inl es]
  | .tailCall g _ => [.inr g]
  | .ite _ t e => exitsOfL t ++ exitsOfL e
  | .switch _ cs d => exitsOfLL cs ++ exitsOfL d
  | _ => []
def exitsOfLL : List (List Stmt) → List (List Exp ⊕ Nat)
  | [] => []
  | c :: cs => exitsOfL c ++ exitsOfLL cs
end

/-- What a function's exits return at a result position: how many return each literal, and how
many something else. -/
structure Prof where
  lits : List (UInt64 × Nat) := []
  unk : Nat := 0
  deriving Inhabited

def Prof.add (p q : Prof) : Prof :=
  { lits := q.lits.foldl (fun acc (v, c) =>
      match acc.find? (·.1 == v) with
      | some _ => acc.map fun (w, d) => if w == v then (w, min 1000 (d + c)) else (w, d)
      | none => acc ++ [(v, c)]) p.lits,
    unk := min 1000 (p.unk + q.unk) }

/-- Each function's exit profile per result position: its `ret`s, and its tail calls' callees'
profiles (a callee not yet known counts as unknown). -/
def exitProfiles (fns : Array Fn) : Array (Array Prof) := Id.run do
  let exits := fns.map fun f => exitsOfL f.body
  let mut prof : Array (Array Prof) := fns.map fun f => Array.replicate f.results {}
  for _ in [0:4] do
    let mut next := prof
    for (f, k) in fns.toList.zipIdx do
      let mut ps : Array Prof := Array.replicate f.results {}
      for x in exits[k]! do
        match x with
        | .inl es =>
          for (e, r) in es.zipIdx do
            if r < ps.size then
              ps := ps.set! r (ps[r]!.add (match lit? e with
                | some (_, v) => { lits := [(v, 1)] }
                | none => { unk := 1 }))
        | .inr g =>
          let gp := prof.getD g #[]
          for r in [0:ps.size] do
            let q := gp.getD r {}
            ps := ps.set! r (ps[r]!.add (if q.lits.isEmpty && q.unk == 0 then { unk := 1 } else q))
      next := next.set! k ps
    prof := next
  pure prof

/-! ### What the pass knows of each input function -/

structure Info where
  size : Nat
  /-- It calls itself. -/
  selfCall : Bool
  /-- It is in a recursive group of the call graph: a call of it may be a loop. -/
  recur : Bool
  /-- Its call sites in the program. -/
  sites : Nat
  /-- The dispatcher of a closure type: its parameter 0 is the closure's tag. -/
  isApply : Bool
  /-- Its parameters that its body reads. -/
  used : Array Bool
  /-- Its locals set more than once. -/
  multi : Std.HashSet Nat
  /-- The statements inlining it copies to put its exits last (`dupL`). -/
  dup : Nat
  /-- Its exits: `ret`s and tail calls. -/
  exits : Nat
  /-- Its parameters whose word may reach a test of a tag (`tagParams`). -/
  tagged : Array Bool
  /-- What its exits return at each result position (`exitProfiles`). -/
  prof : Array Prof
  deriving Inhabited

/-- The functions on a cycle of the call graph (Tarjan, iteratively). -/
def onCycle (succ : Array (List Nat)) : Array Bool := Id.run do
  let n := succ.size
  let mut index : Array (Option Nat) := Array.replicate n none
  let mut low : Array Nat := Array.replicate n 0
  let mut onStack : Array Bool := Array.replicate n false
  let mut stack : Array Nat := #[]
  let mut cyc : Array Bool := Array.replicate n false
  let mut counter := 0
  for root in [0:n] do
    if index[root]!.isSome then continue
    -- The DFS stack: a node and the successors not yet visited.
    let mut work : Array (Nat × List Nat) := #[(root, succ[root]!)]
    index := index.set! root (some counter); low := low.set! root counter; counter := counter + 1
    stack := stack.push root; onStack := onStack.set! root true
    for _ in [0:1 <<< 26] do
      match work.back? with
      | none => break
      | some (v, ws) =>
        match ws with
        | w :: rest =>
          work := work.set! (work.size - 1) (v, rest)
          if w ≥ n then continue
          match index[w]! with
          | none =>
            index := index.set! w (some counter); low := low.set! w counter
            counter := counter + 1
            stack := stack.push w; onStack := onStack.set! w true
            work := work.push (w, succ[w]!)
          | some iw =>
            if onStack[w]! then low := low.set! v (min low[v]! iw)
        | [] =>
          work := work.pop
          if let some (u, _) := work.back? then low := low.set! u (min low[u]! low[v]!)
          if low[v]! == index[v]!.getD 0 then
            let mut comp : Array Nat := #[]
            for _ in [0:n + 1] do
              match stack.back? with
              | none => break
              | some x =>
                stack := stack.pop; onStack := onStack.set! x false
                comp := comp.push x
                if x == v then break
            if comp.size > 1 then
              for x in comp do cyc := cyc.set! x true
  -- A function that calls itself is on a cycle of one.
  for i in [0:n] do
    if (succ[i]!).contains i then cyc := cyc.set! i true
  pure cyc

/-- A test of a tag: the word itself, `eqz` of it, or its comparison for equality with a literal
(a `case`, a `when`, a `bool`). A test of an arithmetic value (`i < n`) is not one. -/
def tagTested : Exp → Option Nat
  | .loc i => some i
  | .op (.eqz _) [.loc i] => some i
  | .op (.rel _ .eq) [.loc i, .c64 _] | .op (.rel _ .ne) [.loc i, .c64 _] => some i
  | .op (.rel _ .eq) [.loc i, .c32 _] | .op (.rel _ .ne) [.loc i, .c32 _] => some i
  | _ => none

/-- Where a word flows in one function: `(dst, src)` edges between its locals, the results it
returns (`.inr r`), and its callees' parameters and results; and the locals it tests as tags. -/
inductive Node where
  | loc (f i : Nat)
  | res (f r : Nat)
  deriving BEq, Hashable

mutual
def flowS (f : Nat) : Stmt → List (Node × Node) × List Node
  | .set i (.loc j) => ([(.loc f i, .loc f j)], [])
  | .call ds g as =>
    (as.zipIdx.filterMap (fun (a, q) => match a with
        | .loc j => some (.loc g q, .loc f j)
        | _ => none) ++
      ds.zipIdx.map (fun (d, r) => (.loc f d, .res g r)), [])
  | .tailCall g as =>
    (as.zipIdx.filterMap (fun (a, q) => match a with
        | .loc j => some (.loc g q, .loc f j)
        | _ => none) ++
      (List.range 64).map (fun r => (.res f r, .res g r)), [])
  | .ret es =>
    (es.zipIdx.filterMap fun (e, r) => match e with
      | .loc j => some (.res f r, .loc f j)
      | _ => none, [])
  | .ite c t e =>
    let (a, b) := flowL f t
    let (a', b') := flowL f e
    (a ++ a', (match tagTested c with | some i => [.loc f i] | none => []) ++ b ++ b')
  | .switch x cs d =>
    let (a, b) := flowLL f cs
    let (a', b') := flowL f d
    (a ++ a', (match tagTested x with | some i => [.loc f i] | none => []) ++ b ++ b')
  | _ => ([], [])
def flowL (f : Nat) : List Stmt → List (Node × Node) × List Node
  | [] => ([], [])
  | s :: ss =>
    let (a, b) := flowS f s
    let (a', b') := flowL f ss
    (a ++ a', b ++ b')
def flowLL (f : Nat) : List (List Stmt) → List (Node × Node) × List Node
  | [] => ([], [])
  | c :: cs =>
    let (a, b) := flowL f c
    let (a', b') := flowLL f cs
    (a ++ a', b ++ b')
end

/-- For each function, its parameters whose word may reach a test of a tag: in its body or a
callee's, through copies, arguments and results. A literal there makes a specialization fold. -/
def tagParams (fns : Array Fn) : Array (Array Bool) := Id.run do
  let mut srcs : Std.HashMap Node (List Node) := {}
  let mut work : Array Node := #[]
  let mut tested : Std.HashSet Node := {}
  for (fn, f) in fns.toList.zipIdx do
    let (es, ts) := flowL f fn.body
    for (d, s) in es do srcs := srcs.insert d (s :: srcs.getD d [])
    for t in ts do
      if !tested.contains t then tested := tested.insert t; work := work.push t
  for _ in [0:1 <<< 28] do
    match work.back? with
    | none => break
    | some n =>
      work := work.pop
      for s in srcs.getD n [] do
        if !tested.contains s then tested := tested.insert s; work := work.push s
  pure (fns.toList.zipIdx.toArray.map fun (fn, f) =>
    (List.range fn.params).toArray.map fun i => tested.contains (.loc f i))

def infos (fns : Array Fn) : Array Info := Id.run do
  let tp := tagParams fns
  let pr := exitProfiles fns
  let succ := fns.map fun f => (calleesL f.body).eraseDups
  let cyc := onCycle succ
  let mut sites : Array Nat := Array.replicate fns.size 0
  for f in fns do
    for g in calleesL f.body do
      if g < sites.size then sites := sites.set! g (sites[g]! + 1)
  let mut out := #[]
  for (f, k) in fns.toList.zipIdx do
    let rd := readsL f.body
    let mut used := Array.replicate f.params false
    for i in rd do
      if i < f.params then used := used.set! i true
    let mut seen : Std.HashSet Nat := {}
    let mut multi : Std.HashSet Nat := {}
    for i in setsL f.body do
      if seen.contains i || i < f.params then multi := multi.insert i
      seen := seen.insert i
    out := out.push { size := sizeL f.body, selfCall := (succ[k]!).contains k, recur := cyc[k]!,
                      sites := sites[k]!, isApply := f.name == "apply", used, multi,
                      dup := dupL f.body, exits := exitsL f.body,
                      tagged := tp[k]!, prof := pr[k]! }
  pure out

/-- The locals whose word the tests of `rest` read, directly or through copies, or that `rest`
passes to a parameter of a callee whose word reaches a test (`Info.tagged`). -/
def testedIn (info : Array Info) (rest : List Stmt) : Std.HashSet Nat := Id.run do
  let mut t : Std.HashSet Nat := Std.HashSet.ofList (testsL rest)
  for (p, g, q) in passesL rest do
    if ((info[g]?.map (·.tagged.getD q false)).getD false) then t := t.insert p
  let copies := (copiesL rest)
  for _ in [0:8] do
    let mut grew := false
    for (x, y) in copies do
      if t.contains x && !t.contains y then t := t.insert y; grew := true
    if !grew then break
  pure t

mutual
/-- `ss`'s statements, each call also counting its callee's (`sz`), up to `cap + 1`: the
traversal stops there. -/
def expL (sz : Nat → Nat) (cap : Nat) : List Stmt → Nat
  | [] => 0
  | s :: ss =>
    let a := expS sz cap s
    if a > cap then cap + 1 else min (cap + 1) (a + expL sz (cap - a) ss)
def expS (sz : Nat → Nat) (cap : Nat) : Stmt → Nat
  | .ite _ t e =>
    let a := expL sz cap t
    if a + 1 > cap then cap + 1 else min (cap + 1) (1 + a + expL sz (cap - a - 1) e)
  | .switch _ cs d =>
    let a := expLL sz cap cs
    if a + 1 > cap then cap + 1 else min (cap + 1) (1 + a + expL sz (cap - a - 1) d)
  | .call _ g _ | .tailCall g _ => 1 + sz g
  | .tickBound => 0
  | _ => 1
def expLL (sz : Nat → Nat) (cap : Nat) : List (List Stmt) → Nat
  | [] => 0
  | c :: cs =>
    let a := expL sz cap c
    if a > cap then cap + 1 else min (cap + 1) (a + expLL sz (cap - a) cs)
end

/-- The statements `ss` comes to when its calls are inlined once (each call counts its callee's
size), counted up to `cap + 1`: the decisions that read it compare it with bounds below `cap`. -/
def expandedSize (info : Array Info) (ss : List Stmt) (cap : Nat := 1024) : Nat :=
  expL (fun g => (info[g]?.map (·.size)).getD 0) cap ss

/-- The first statements of `ss` up to `cap` statements, and of a longer statement only its own
test: the decisions that read a continuation's tests look at its start. -/
def prefixOf (cap : Nat) (ss : List Stmt) : List Stmt := Id.run do
  let mut out : Array Stmt := #[]
  let mut n := 0
  for s in ss do
    let k := expS (fun _ => 0) cap s
    if n + k ≤ cap then out := out.push s; n := n + k
    else
      match s with
      | .ite c _ _ => out := out.push (.ite c [] [])
      | .switch x _ _ => out := out.push (.switch x [] [])
      | _ => pure ()
      break
  pure out.toList

/-- What copying `rest` into each exit of a call of `f` whose results go to `ds` comes to: where
`rest` first tests one of `ds`, each exit that returns a literal there takes the arm the literal
selects, and every other exit the whole of `rest`. -/
def cpsCost (info : Array Info) (f : Nat) (ds : List Nat) (rest : List Stmt) : Nat := Id.run do
  let inf := info[f]?.getD default
  let whole := inf.exits * expandedSize info rest
  let some j := rest.findIdx? fun s => match s with
      | .ite c _ _ | .switch c _ _ => match tagTested c with
        | some d => ds.contains d
        | none => false
      | _ => false
    | return whole
  let pre := expandedSize info (rest.take j)
  let post := rest.drop (j + 1)
  let some (d, arms) := (match rest[j]? with
      | some (.ite c t e) => (tagTested c).map fun d => (d, fun (v : UInt64) =>
          match cval (subE (fun i => if i == d then .c64 v else .loc i) 0 c) with
          | some b => if b != 0 then t else e
          | none => t ++ e)
      | some (.switch x cs df) => (tagTested x).map fun d => (d, fun (v : UInt64) =>
          match cval (subE (fun i => if i == d then .c64 v else .loc i) 0 x) with
          | some b => cs[b.toNat]?.getD df
          | none => cs.flatten ++ df)
      | _ => none) | return whole
  let r := ds.idxOf d
  let p := inf.prof.getD r {}
  let mut cost := p.unk * expandedSize info rest
  for (v, c) in p.lits do
    cost := cost + c * (pre + expandedSize info (arms v ++ post))
  pure cost

/-! ### The specializer -/

/-- A context: an input function's body being expanded into the output function. -/
structure Ctx where
  /-- The input function. -/
  fn : Nat
  /-- Each of its locals' output local. -/
  ren : Array Nat
  /-- Its locals whose word is known: a literal, a data address, or a stable output local. -/
  vals : Std.HashMap Nat Exp := {}
  /-- Output locals whose word is known here (a `switch` case, an `ite` on `eqz`). -/
  facts : Std.HashMap Nat UInt64 := {}
  /-- Where its frame slots start in the output function's frame. -/
  fbase : Nat := 0
  /-- The input functions being inlined on this path, innermost first. -/
  stack : List Nat := []
  /-- An inlined dispatcher whose tag is a literal: its `tick` is not a dispatched call. -/
  dropTick : Bool := false
  /-- Its locals known (`vals`) whose output local is not set: set only where a join reads it
  (`Join.mat`). -/
  lazy : Std.HashSet Nat := {}
  deriving Inhabited

/-- Where an expanded body's `ret` goes: the output function's own return (`[]`), or a call's
destinations, then (when the continuation was copied into the exits) the statements after the
call in the caller's context. -/
structure Frame where
  ds : List Nat
  dIn : List Nat
  after : Option (Ctx × List Stmt)
  /-- With the continuation copied: the end of the continuation's list (`Join`). -/
  afterJoin : Option (List Stmt × List Frame) := none
  afterMat : List Nat := []
  /-- With no continuation copied: the frame's number, under which its exits' words are
  recorded (`OState.leaves`). -/
  id : Nat := 0
  /-- With no continuation copied: the continuation each exit tries a copy of (`tryCopy`). -/
  join : Option (Ctx × List Stmt × List Frame) := none
  /-- The result positions whose word the continuation tests (`kontTests`). -/
  wants : Std.HashSet Nat := {}
  deriving Inhabited

abbrev Kont := List Frame

/-- The end of a branch of an `ite` or a `switch` whose statements after it are not copied into
it: those statements, of which the branch's end tries a copy, and the locals they read that the
branches set, whose output locals the end sets when the copy is not taken. -/
structure Join where
  copy : Option (List Stmt × Kont) := none
  mat : List Nat := []

/-- A specialization's key: the input function, and its literal parameters. -/
abbrev Pattern := List (Nat × Bool × UInt64)

structure Job where
  out : Nat
  origin : Nat
  pattern : Pattern

structure OState where
  /-- The output functions, by output index; filled as their jobs run. -/
  outFns : Array Fn := #[]
  idOf : Std.HashMap Nat Nat := {}
  specOf : Std.HashMap (Nat × Pattern) Nat := {}
  specN : Std.HashMap Nat Nat := {}
  jobs : Array Job := #[]
  /-- The function being built: its next local, its frame, its statements so far, and its
  output locals that are set more than once. -/
  next : Nat := 0
  frame : Nat := 0
  emitted : Nat := 0
  unstable : Std.HashSet Nat := {}
  /-- The most statements the function may hold while a copy is tried (`tryCopy`); past it the
  try is abandoned. -/
  limit : Nat := 0
  /-- The function is built without copied continuations (it came to more than `budget`
  statements with them): a call's continuation follows it once, and an `ite`'s too. -/
  modest : Bool := false
  /-- The most statements expanded while a copy is tried. -/
  workLimit : Nat := 0
  /-- The statements expanded for the function being built: past `workMax`, nothing more is
  inlined or copied. -/
  work : Nat := 0
  /-- For each expanded call with no continuation copied (by frame number): the words of each
  exit that reached it, or `none` when the call was kept as a call. -/
  leaves : Std.HashMap Nat (Option (List (List Exp))) := {}
  frames : Nat := 0

structure Env where
  fns : Array Fn
  info : Array Info

abbrev OM := ReaderT Env (StateT OState (Except String))

def budget : Nat := 8000
/-- The most statements expanded (copied and inlined, kept or not) for one function. -/
def workMax : Nat := 200000
def specMax : Nat := 256
def depthMax : Nat := 256
/-- A continuation this short is copied into each exit of the call or `ite` before it. -/
def contMax : Nat := 48
/-- A continuation is copied into each exit of a call when the copies come to at most this many
statements. -/
def cpsMax : Nat := 600
/-- The most statements the copy of a continuation into one exit may come to. -/
def copyMax : Nat := 200
/-- The most statements expanded for one try of a copy (`tryCopy`). -/
def copyWork : Nat := 2000

/-- A copy of `rest` is kept where it ends the function in at most half of what `rest` comes to,
or in a few statements: what the exit knows decided most of it. -/
def copyBound (info : Array Info) (rest : List Stmt) : Nat :=
  max contMax (expandedSize info rest / 2)
/-- A function this large is inlined where a literal argument meets a test of its parameter. -/
def mediumMax : Nat := 1500
/-- A function this small is inlined wherever it is called. -/
def smallMax : Nat := 120

def freshN (k : Nat) : OM (List Nat) :=
  modifyGet fun s => (List.range' s.next k, { s with next := s.next + k })

/-- The output function standing for input function `f` called as written. -/
def outOf (f : Nat) : OM Nat := do
  if let some o := (← get).idOf[f]? then return o
  let s ← get
  let o := s.outFns.size
  set { s with outFns := s.outFns.push default, idOf := s.idOf.insert f o,
               jobs := s.jobs.push ⟨o, f, []⟩ }
  return o

/-- The output function for input function `f` at the literal parameters `pat`, when the bound
allows one. -/
def specOf (f : Nat) (pat : Pattern) : OM (Option Nat) := do
  let s ← get
  if let some o := s.specOf[(f, pat)]? then return some o
  let n := s.specN[f]?.getD 0
  if n ≥ specMax then return none
  let o := s.outFns.size
  set { s with outFns := s.outFns.push default, specOf := s.specOf.insert (f, pat) o,
               specN := s.specN.insert f (n + 1), jobs := s.jobs.push ⟨o, f, pat⟩ }
  return some o

def Ctx.look (c : Ctx) (i : Nat) : Exp :=
  match c.vals[i]? with
  | some e => match e with
    | .loc o => match c.facts[o]? with
      | some v => .c64 v
      | none => e
    | _ => e
  | none =>
    let o := c.ren.getD i i
    match c.facts[o]? with
    | some v => .c64 v
    | none => .loc o

def Ctx.sub (c : Ctx) (e : Exp) : Exp := subE c.look c.fbase e

/-- The error that abandons a try of copied continuations whose limit is `l`. -/
def abandon (l : Nat) : String := s!"flat IR: continuations past {l} statements"

/-- The error that abandons a function past `budget` statements, to be built again without
copies (`OState.modest`). -/
def overBudget : String := "flat IR: a function past its budget"

def emit (k : Nat) : OM Unit := do
  let s ← get
  set { s with emitted := s.emitted + k }
  if s.limit > 0 && s.emitted + k > s.limit then throw (abandon s.limit)
  if !s.modest && s.emitted + k > budget then throw overBudget

/-- `act`'s statements when they end every path and come to at most `bound` (and `copyMax`)
statements; otherwise `none`, and nothing `act` did. -/
def tryCopy (bound : Nat) (act : OM (List Stmt)) : OM (Option (List Stmt)) := do
  let s₀ ← get
  if s₀.work > workMax || s₀.modest then return none
  let m := min bound copyMax
  let l := if s₀.limit > 0 then min s₀.limit (s₀.emitted + m) else s₀.emitted + m
  let wl := if s₀.workLimit > 0 then min s₀.workLimit (s₀.work + copyWork) else s₀.work + copyWork
  set { s₀ with limit := l, workLimit := wl }
  try
    let r ← act
    if termL r && sizeL r ≤ m then
      modify fun s => { s with limit := s₀.limit, workLimit := s₀.workLimit }
      return some r
    -- The work done stays counted against `workMax`.
    let w := (← get).work
    set { s₀ with work := w }
    return none
  catch e =>
    if e == abandon l then set { s₀ with work := s₀.work + copyWork }; return none
    throw e

/-- Record that input local `i` now holds `e` (an output expression already set into its output
local): its word is known where it is an atom that cannot change. -/
def Ctx.bindAs (c : Ctx) (i : Nat) (e : Exp) : OM Ctx := do
  -- A literal stays true until `i` is set again (`forget`); a local only while it is not set
  -- again itself.
  let unstable := (← get).unstable
  let stable := match e with
    | .loc o => !unstable.contains o
    | _ => isAtom e
  if stable then return { c with vals := c.vals.insert i e }
  return { c with vals := c.vals.erase i }

def Ctx.forget (c : Ctx) (is : List Nat) : Ctx :=
  { c with vals := is.foldl (fun m i => m.erase i) c.vals,
           facts := is.foldl (fun m i => m.erase (c.ren.getD i i)) c.facts,
           lazy := is.foldl (fun m i => m.erase i) c.lazy }

/-- Input local `i` set to the output expression `e`: an atom is known and its output local not
set (`lazy`); any other word is set. -/
def Ctx.setTo (c : Ctx) (i : Nat) (e : Exp) : OM (Ctx × List Stmt) := do
  let c ← (c.forget [i]).bindAs i e
  if isAtom e && c.vals.contains i then return ({ c with lazy := c.lazy.insert i }, [])
  return (c, [.set (c.ren.getD i i) e])

/-- The sets of the output locals of the locals `is` that are known and not set. -/
def Ctx.materialize (c : Ctx) (is : List Nat) : List Stmt :=
  is.eraseDups.filterMap fun i =>
    if c.lazy.contains i then (c.vals[i]?).map fun e => .set (c.ren.getD i i) e else none

/-- What the `then` branch of an `ite` on `c` knows: `x = 0` for `eqz x`. -/
def Ctx.thenFacts (ctx : Ctx) (c : Exp) : Ctx :=
  match c with
  | .op (.eqz .w64) [.loc o] => { ctx with facts := ctx.facts.insert o 0 }
  | _ => ctx

def Ctx.caseFact (ctx : Ctx) (e : Exp) (k : Nat) : Ctx :=
  match e with
  | .loc o => { ctx with facts := ctx.facts.insert o k.toUInt64 }
  | _ => ctx

/-- The locals `rest` returns, by result position: each `ret` of `rest` passing `.loc d` at
position `r` gives `(d, r)`. -/
def returnsOf (rest : List Stmt) : List (Nat × Nat) :=
  (exitsOfL rest).flatMap fun x => match x with
    | .inl es => es.zipIdx.filterMap fun (e, r) => match e with
      | .loc d => some (d, r)
      | _ => none
    | .inr _ => []

/-- The continuation `k` tests the word returned at result position `r`. -/
def kontTests (k : Kont) (r : Nat) : Bool :=
  match k with
  | [] => false
  | fr :: _ => fr.wants.contains r

/-- The result positions of a call whose results go to `dIn`, with the statements `rest` after
it returning to `k`, that `rest` tests (`tested`), or returns to a continuation that does. -/
def wantsOf (tested : Std.HashSet Nat) (head : List Stmt) (dIn : List Nat) (k : Kont) :
    Std.HashSet Nat :=
  let ret := returnsOf head
  dIn.zipIdx.foldl (fun w (d, r) =>
    if tested.contains d || ret.any (fun (d', r') => d' == d && kontTests k r') then w.insert r
    else w) {}

/-- What a copy of a continuation returning to `k` copies besides itself: the continuations
copied into the exits of the calls it returns to. -/
def kontCost (info : Array Info) : Nat → Kont → Nat
  | 0, _ => 0
  | _, [] => 0
  | n + 1, fr :: k => match fr.after with
    | some (_, rest) => expandedSize info rest + kontCost info n k
    | none => 0

/-- The input function `f`'s body can be inlined from context `ctx`. -/
def inlinable (ctx : Ctx) (f : Nat) (as : List Exp) : OM Bool := do
  let env ← read
  let some fn := env.fns[f]? | return false
  let info := env.info[f]!
  -- A literal argument that a test of the function reads: much of the body folds away.
  let lit := as.zipIdx.any fun (a, i) => (lit? a).isSome && info.tagged.getD i false
  let onStack := ctx.stack.count f
  if info.selfCall || onStack > (if lit then 1 else 0) || ctx.stack.length ≥ depthMax then
    return false
  if fn.name == "entry" || info.dup > smallMax then return false
  if (← get).emitted + info.size > budget || (← get).work > workMax then
    return false
  return info.size ≤ smallMax || info.sites ≤ 1 || (lit && info.size ≤ mediumMax)

mutual

/-- The output statements of the input statements `ss` in context `ctx`, whose exits go to `k`. -/
def simpList : Nat → Ctx → List Stmt → Kont → Join → OM (List Stmt)
  | 0, _, _, _, _ => throw "flat IR: the specializer ran out of fuel"
  | n + 1, ctx₀, ss₀, k, join => do
    let mut out : Array Stmt := #[]
    let mut ctx := ctx₀
    let mut ss := ss₀
    for _ in [0:1 <<< 30] do
      let st₀ ← get
      set { st₀ with work := st₀.work + 1 }
      if st₀.workLimit > 0 && st₀.work + 1 > st₀.workLimit then throw (abandon st₀.limit)
      match ss with
      | [] =>
        -- The end of a branch: a copy of the statements after the branching, specialized to
        -- what this path knows, when it ends the function and is short.
        if let some (jr, jk) := join.copy then
          if let some c ← tryCopy (copyBound (← read).info jr) (simpList n ctx jr jk {}) then
            return out.toList ++ c
        let m := ctx.materialize join.mat
        emit m.length
        return out.toList ++ m
      | s :: rest =>
        match s with
        | .set i e =>
          let (c', st) ← ctx.setTo i (ctx.sub e)
          out := out ++ st.toArray; emit st.length
          ctx := c'
          ss := rest
        | .ret es => return out.toList ++ (← retTo n (es.map ctx.sub) k)
        | .tailCall f as => return out.toList ++ (← doCall n ctx f (as.map ctx.sub) k)
        | .trap => return (out.push .trap).toList
        | .call ds f as =>
          let as' := as.map ctx.sub
          let ctx' := ctx.forget ds
          let ds' := ds.map fun d => ctx.ren.getD d d
          let info := (← read).info
          let head := prefixOf 256 rest
          let tested := (returnsOf head).foldl (fun t (d, r) =>
            if kontTests k r then t.insert d else t) (testedIn info head)
          let wants := wantsOf tested head ds k
          let es := expandedSize info rest
          -- The continuation, when it tests the call's results, is copied into each exit when the
          -- copies are cheap; each copy also copies what the continuations it returns to copy.
          -- Otherwise it follows the call once, and each exit tries a copy of its own (`join`).
          let kc := kontCost info 8 k
          let exits := ((info[f]?.map (·.exits)).getD 1)
          let modest := (← get).modest
          let cps := !rest.isEmpty && (← get).emitted < budget && ds.any tested.contains &&
            (!modest || es ≤ 8) &&
            (exits * (es + kc) ≤ cpsMax || cpsCost info f ds rest + exits * kc ≤ cpsMax)
          let id ← modifyGet fun st => (st.frames, { st with frames := st.frames + 1 })
          let jn := if !rest.isEmpty && ds.any tested.contains then
            some (ctx', rest, k) else none
          if cps then
            let fr : Frame := { ds := ds', dIn := ds, id, after := some (ctx', rest), wants,
                                afterJoin := join.copy, afterMat := join.mat }
            return out.toList ++ (← doCall n ctx f as' (fr :: k))
          let id ← modifyGet fun st => (st.frames, { st with frames := st.frames + 1 })
          let fr : Frame := { ds := ds', dIn := ds, id, join := jn, after := none,
                              wants := if jn.isSome then wants else {} }
          let r ← doCall n ctx f as' (fr :: k)
          out := out ++ r.toArray
          -- Every exit took a copy of the statements after the call: they are not reached.
          if termL r then
            modify fun st => { st with leaves := st.leaves.erase id }
            return out.toList
          ctx := ctx'
          -- The words every exit of the expanded call agrees on are known after it.
          if let some (some exits) := (← get).leaves[id]? then
            for (i, r) in ds.zipIdx do
              match exits.map (·[r]?) with
              | some e :: more =>
                if isAtom e && more.all (fun x => match x with
                    | some e' => atomEq e e'
                    | none => false) then ctx ← ctx.bindAs i e
              | _ => pure ()
          modify fun st => { st with leaves := st.leaves.erase id }
          ss := rest
        | .ite c t e =>
          let c' := ctx.sub c
          match cval c' with
          | some v => ss := (if v != 0 then t else e) ++ rest
          | none =>
            let info := (← read).info
            let push := !rest.isEmpty &&
              (exitL t || exitL e ||
                ((!termL t || !termL e) && (← get).emitted < budget && !(← get).modest &&
                  ((expandedSize info rest ≤ cpsMax / 2 &&
                      (setsL t ++ setsL e).any (testedIn info (prefixOf 256 rest)).contains) ||
                    (expandedSize info rest ≤ contMax && termL rest))))
            if rest.isEmpty || push then
              let t' ← simpList n (ctx.thenFacts c') (t ++ rest) k join
              let e' ← simpList n ctx (e ++ rest) k join
              emit 1
              return (out.push (.ite c' t' e')).toList
            let emitted := (← get).emitted
            let cp := emitted < budget &&
              (setsL t ++ setsL e).any (testedIn info (prefixOf 256 rest)).contains
            let jn : Join := { copy := if cp then some (rest, k) else none,
                               mat := setsL t ++ setsL e }
            let t' ← simpList n (ctx.thenFacts c') t k jn
            let e' ← simpList n ctx e k jn
            out := out.push (.ite c' t' e'); emit 1
            if termL t' && termL e' then return out.toList
            ctx := ctx.forget (setsL t ++ setsL e)
            ss := rest
        | .switch x cs d =>
          let x' := ctx.sub x
          match cval x' with
          | some v => ss := (cs[v.toNat]?.getD d) ++ rest
          | none =>
            let info := (← read).info
            let push := !rest.isEmpty &&
              (exitLL cs || exitL d ||
                ((!termLL cs || !termL d) && (← get).emitted < budget && !(← get).modest &&
                  ((expandedSize info rest * (cs.length + 1) ≤ cpsMax &&
                      (setsLL cs ++ setsL d).any (testedIn info (prefixOf 256 rest)).contains) ||
                    (expandedSize info rest * (cs.length + 1) ≤ 2 * contMax && termL rest))))
            let tail := if rest.isEmpty || push then rest else []
            let emitted := (← get).emitted
            let cp := emitted < budget &&
              (setsLL cs ++ setsL d).any (testedIn info (prefixOf 256 rest)).contains
            let jn : Join := if rest.isEmpty || push then join
              else { copy := if cp then some (rest, k) else none, mat := setsLL cs ++ setsL d }
            let mut cs' : Array (List Stmt) := #[]
            for (c, i) in cs.zipIdx do
              cs' := cs'.push (← simpList n (ctx.caseFact x' i) (c ++ tail) k jn)
            let d' ← simpList n ctx (d ++ tail) k jn
            emit 1
            out := out.push (.switch x' cs'.toList d')
            if rest.isEmpty || push then return out.toList
            if termLL cs'.toList && termL d' then return out.toList
            ctx := ctx.forget (setsLL cs ++ setsL d)
            ss := rest
        | .tick =>
          if !ctx.dropTick then out := out.push .tick; emit 1
          ss := rest
        | .store a o v => out := out.push (.store (ctx.sub a) o (ctx.sub v)); emit 1; ss := rest
        | .store8 a v => out := out.push (.store8 (ctx.sub a) (ctx.sub v)); emit 1; ss := rest
        | .free a => out := out.push (.free (ctx.sub a)); emit 1; ss := rest
        | .unslot a => out := out.push (.unslot (ctx.sub a)); emit 1; ss := rest
        | .out b => out := out.push (.out (ctx.sub b)); emit 1; ss := rest
        | .putc a b => out := out.push (.putc (ctx.sub a) (ctx.sub b)); emit 1; ss := rest
        | .putv a b c =>
          out := out.push (.putv (ctx.sub a) (ctx.sub b) (ctx.sub c)); emit 1; ss := rest
        | .sleep a b => out := out.push (.sleep (ctx.sub a) (ctx.sub b)); emit 1; ss := rest
        | .status c => out := out.push (.status (ctx.sub c)); emit 1; ss := rest
        | .tickCopy => out := out.push .tickCopy; emit 1; ss := rest
        | .tickBound => out := out.push .tickBound; ss := rest
    throw "flat IR: the specializer's statement loop ran out"

/-- A `ret` of the words `es` (output expressions) to `k`. -/
def retTo : Nat → List Exp → Kont → OM (List Stmt)
  | 0, _, _ => throw "flat IR: the specializer ran out of fuel"
  | _ + 1, es, [] => do emit 1; return [.ret es]
  | n + 1, es, fr :: k => do
    let sets := (fr.ds.zip es).map fun (d, e) => Stmt.set d e
    if fr.after.isNone then emit sets.length
    match fr.after with
    | none =>
      if let some (actx, rest, k') := fr.join then
        let mut a := actx
        for (i, e) in fr.dIn.zip es do
          a ← (a.forget [i]).bindAs i (if isAtom e then e else .loc (actx.ren.getD i i))
        if let some c ← tryCopy (copyBound (← read).info rest) (simpList n a rest k' {}) then
          return sets ++ c
      modify fun st =>
        let prev := st.leaves.getD fr.id (some [])
        { st with leaves := st.leaves.insert fr.id (prev.map (· ++ [es])) }
      return sets
    | some (actx, rest) =>
      -- The continuation follows in this exit: an atom is known, any other word set.
      let mut a := actx
      let mut st : Array Stmt := #[]
      for (i, e) in fr.dIn.zip es do
        let (a', s') ← a.setTo i e
        a := a'
        st := st ++ s'.toArray
      return st.toList ++ (← simpList n a rest k { copy := fr.afterJoin, mat := fr.afterMat })

/-- A call of input function `f` on the output expressions `as` from context `ctx`, its results
going to `k`. -/
def doCall : Nat → Ctx → Nat → List Exp → Kont → OM (List Stmt)
  | 0, _, _, _, _ => throw "flat IR: the specializer ran out of fuel"
  | n + 1, ctx, f, as, k => do
    let env ← read
    if ← inlinable ctx f as then
      let fn := env.fns[f]!
      let info := env.info[f]!
      let ls ← freshN (fn.params + fn.locals)
      let st ← get
      set { st with frame := st.frame + fn.frame,
                    unstable := info.multi.fold (fun u i => u.insert (ls.getD i i)) st.unstable }
      let mut c : Ctx := { fn := f, ren := ls.toArray, fbase := st.frame, stack := f :: ctx.stack,
                           dropTick := info.isApply && (cval (as.headD (.loc 0))).isSome }
      let mut pre : Array Stmt := #[]
      for (a, i) in as.zipIdx do
        let (c', st) ← c.setTo i a
        c := c'
        pre := pre ++ st.toArray
      emit pre.size
      return pre.toList ++ (← simpList n c fn.body k {})
    -- Not inlined: a call of the function, or of its specialization at the literal arguments.
    let info := env.info[f]!
    let lits := as.zipIdx.filterMap fun (a, i) =>
      match lit? a with
      | some l => if info.used.getD i false then some (i, l) else none
      | none => none
    let target ← if info.recur && !lits.isEmpty then specOf f lits else pure none
    let (g, args) ← match target with
      | some o => pure (o, as.zipIdx.filterMap fun (a, i) =>
          if lits.any (·.1 == i) then none else some a)
      | none => return ← callTo n (← outOf f) as k
    callTo n g args k

/-- A call of output function `g` on `as`, its results going to `k`. -/
def callTo : Nat → Nat → List Exp → Kont → OM (List Stmt)
  | 0, _, _, _ => throw "flat IR: the specializer ran out of fuel"
  | n + 1, g, as, k => do
    emit 1
    match k with
    | [] => return [.tailCall g as]
    | fr :: k' =>
      let c := Stmt.call fr.ds g as
      match fr.after with
      | none =>
        modify fun st => { st with leaves := st.leaves.insert fr.id none }
        return [c]
      | some (actx, rest) =>

        return c :: (← simpList n actx rest k' { copy := fr.afterJoin, mat := fr.afterMat })

end

/-- The fuel of the specializer: the nesting of inlined bodies and copied continuations. -/
def fuel : Nat := 100000

/-- Run job `j`: build its output function. -/
def runJob (j : Job) : OM Unit := do
  let env ← read
  let fn := env.fns[j.origin]!
  let info := env.info[j.origin]!
  -- The kept parameters are the output function's; the fixed ones and the locals are fresh.
  let kept := (List.range fn.params).filter fun i => !j.pattern.any (·.1 == i)
  let np := kept.length
  modify fun s => { s with next := np, frame := fn.frame, emitted := 0, unstable := {}, work := 0 }
  let mut ren : Array Nat := Array.replicate (fn.params + fn.locals) 0
  for (i, p) in kept.zipIdx do ren := ren.set! i p
  for (i, _, _) in j.pattern do
    let l ← freshN 1
    ren := ren.set! i (l.headD 0)
  for i in [fn.params:fn.params + fn.locals] do
    let l ← freshN 1
    ren := ren.set! i (l.headD 0)
  modify fun s => { s with unstable := info.multi.fold (fun u i => u.insert (ren.getD i i)) {} }
  let mut c : Ctx := { fn := j.origin, ren, stack := [j.origin],
                       dropTick := info.isApply && j.pattern.any (·.1 == 0) }
  for (i, l) in j.pattern do
    c := { c with vals := c.vals.insert i (litExp l), lazy := c.lazy.insert i }
  let s₀ ← get
  let body ← try simpList fuel c fn.body [] {} catch e =>
    if e != overBudget then throw e
    set { s₀ with modest := true }
    simpList fuel c fn.body [] {}
  modify fun s => { s with modest := false }
  let s ← get
  let name := if j.pattern.isEmpty then fn.name else s!"{fn.name}_s{j.out}"
  let f : Fn := { name, params := np, results := fn.results, locals := s.next - np,
                  frame := s.frame, body }
  set { s with outFns := s.outFns.set! j.out f }

/-! ### Narrowing: dead sets and dead parameters -/

mutual
/-- `ss` without the sets of locals in `dead` whose word has no effect. -/
def dropSetsL (dead : Std.HashSet Nat) : List Stmt → List Stmt
  | [] => []
  | s :: ss => match s with
    | .set i e => if dead.contains i && pureE e then dropSetsL dead ss
      else s :: dropSetsL dead ss
    | .ite c t e => .ite c (dropSetsL dead t) (dropSetsL dead e) :: dropSetsL dead ss
    | .switch x cs d => .switch x (dropSetsLL dead cs) (dropSetsL dead d) :: dropSetsL dead ss
    | _ => s :: dropSetsL dead ss
def dropSetsLL (dead : Std.HashSet Nat) : List (List Stmt) → List (List Stmt)
  | [] => []
  | c :: cs => dropSetsL dead c :: dropSetsLL dead cs
end

/-- `f` with the sets of locals no statement reads removed, until none is left. -/
def dropDeadSets (f : Fn) : Fn := Id.run do
  let mut body := f.body
  for _ in [0:64] do
    let rd : Std.HashSet Nat := Std.HashSet.ofList (readsL body)
    let dead : Std.HashSet Nat := Std.HashSet.ofList ((setsL body).filter (!rd.contains ·))
    if dead.isEmpty then break
    let body' := dropSetsL dead body
    if sizeL body' == sizeL body then break
    body := body'
  pure { f with body }

mutual
/-- `s` with each call's arguments at the dead parameters of its callee removed (an argument
with an effect is evaluated first, into a fresh local). -/
def dropArgsS (live : Array (Array Bool)) (fresh : Nat) : Stmt → Nat × List Stmt
  | .call ds g as => dropArgs live fresh g as fun as' => .call ds g as'
  | .tailCall g as => dropArgs live fresh g as fun as' => .tailCall g as'
  | .ite c t e =>
    let (n₁, t') := dropArgsL live fresh t
    let (n₂, e') := dropArgsL live n₁ e
    (n₂, [.ite c t' e'])
  | .switch x cs d =>
    let (n₁, cs') := dropArgsLL live fresh cs
    let (n₂, d') := dropArgsL live n₁ d
    (n₂, [.switch x cs' d'])
  | s => (fresh, [s])
def dropArgsL (live : Array (Array Bool)) (fresh : Nat) : List Stmt → Nat × List Stmt
  | [] => (fresh, [])
  | s :: ss =>
    let (n₁, s') := dropArgsS live fresh s
    let (n₂, ss') := dropArgsL live n₁ ss
    (n₂, s' ++ ss')
def dropArgsLL (live : Array (Array Bool)) (fresh : Nat) : List (List Stmt) → Nat × List (List Stmt)
  | [] => (fresh, [])
  | c :: cs =>
    let (n₁, c') := dropArgsL live fresh c
    let (n₂, cs') := dropArgsLL live n₁ cs
    (n₂, c' :: cs')
/-- The arguments `as` of a call of `g`, the dead ones dropped; `mk` builds the call. -/
def dropArgs (live : Array (Array Bool)) (fresh g : Nat) (as : List Exp)
    (mk : List Exp → Stmt) : Nat × List Stmt :=
  let lv := live.getD g #[]
  let (n, pre, kept) := as.zipIdx.foldl (fun (n, pre, kept) (a, i) =>
    if lv.getD i true then (n, pre, kept ++ [a])
    else if pureE a then (n, pre, kept)
    else (n + 1, pre ++ [Stmt.set n a], kept)) (fresh, [], [])
  (n, pre ++ [mk kept])
end


mutual
/-- The locals `s` reads other than as a bare argument of a call. -/
def readsNotPassedS : Stmt → List Nat
  | .call _ _ as | .tailCall _ as => as.flatMap fun a => match a with
    | .loc _ => []
    | e => readsE e
  | .ite c t e => readsE c ++ readsNotPassedL t ++ readsNotPassedL e
  | .switch x cs d => readsE x ++ readsNotPassedLL cs ++ readsNotPassedL d
  | s => readsEs (stmtExps s)
def readsNotPassedL : List Stmt → List Nat
  | [] => []
  | s :: ss => readsNotPassedS s ++ readsNotPassedL ss
def readsNotPassedLL : List (List Stmt) → List Nat
  | [] => []
  | c :: cs => readsNotPassedL c ++ readsNotPassedLL cs
end

mutual
/-- `ss` with every local `i` renamed `m[i]` (read through `σ`). -/
def renL (σ : Nat → Exp) (m : Array Nat) : List Stmt → List Stmt
  | [] => []
  | s :: ss => renS σ m s :: renL σ m ss
def renS (σ : Nat → Exp) (m : Array Nat) : Stmt → Stmt
  | .set i e => .set (m.getD i i) (subE σ 0 e)
  | .store a o v => .store (subE σ 0 a) o (subE σ 0 v)
  | .store8 a v => .store8 (subE σ 0 a) (subE σ 0 v)
  | .free a => .free (subE σ 0 a)
  | .unslot a => .unslot (subE σ 0 a)
  | .out b => .out (subE σ 0 b)
  | .putc a b => .putc (subE σ 0 a) (subE σ 0 b)
  | .putv a b c => .putv (subE σ 0 a) (subE σ 0 b) (subE σ 0 c)
  | .sleep a b => .sleep (subE σ 0 a) (subE σ 0 b)
  | .ite c t e => .ite (subE σ 0 c) (renL σ m t) (renL σ m e)
  | .switch x cs d => .switch (subE σ 0 x) (renLL σ m cs) (renL σ m d)
  | .call ds g as => .call (ds.map fun d => m.getD d d) g (subEs σ 0 as)
  | .ret es => .ret (subEs σ 0 es)
  | .tailCall g as => .tailCall g (subEs σ 0 as)
  | .status c => .status (subE σ 0 c)
  | s => s
def renLL (σ : Nat → Exp) (m : Array Nat) : List (List Stmt) → List (List Stmt)
  | [] => []
  | c :: cs => renL σ m c :: renLL σ m cs
end

/-- The program with every parameter no function reads removed: a parameter is read when its
function reads it other than by passing it, or passes it to a parameter that is read. -/
def dropDeadParams (fns : Array Fn) (entry : Nat) : Array Fn := Id.run do
  let mut live : Array (Array Bool) := fns.map fun f => Array.replicate f.params false
  -- (callee, parameter) ↦ the (function, parameter) pairs passed to it.
  let mut deps : Std.HashMap (Nat × Nat) (List (Nat × Nat)) := {}
  let mut work : Array (Nat × Nat) := #[]
  for (f, k) in fns.toList.zipIdx do
    for p in readsNotPassedL f.body do
      if p < f.params && !live[k]![p]! then
        live := live.set! k (live[k]!.set! p true); work := work.push (k, p)
    for (p, g, q) in passesL f.body do
      if p < f.params then
        deps := deps.insert (g, q) ((k, p) :: deps.getD (g, q) [])
      -- A local that is not a parameter is read by the call when its parameter is live: it is
      -- kept, as any local the call reads.
  -- The entry's parameters, and any of a function no specializer output reaches, stay.
  if h : entry < live.size then
    live := live.set entry (Array.replicate (fns[entry]!.params) true)
  for _ in [0:1 <<< 26] do
    match work.back? with
    | none => break
    | some (g, q) =>
      work := work.pop
      for (k, p) in deps.getD (g, q) [] do
        if !live[k]![p]! then
          live := live.set! k (live[k]!.set! p true); work := work.push (k, p)
  -- Each function: dead parameters become locals past the live ones, and each call drops the
  -- arguments of its callee's dead parameters.
  let mut out := #[]
  for (f, k) in fns.toList.zipIdx do
    let lv := live[k]!
    let keptPs := (List.range f.params).filter (lv.getD · true)
    let deadPs := (List.range f.params).filter (!lv.getD · true)
    let np := keptPs.length
    let total := f.params + f.locals
    let mut m : Array Nat := Array.replicate total 0
    for (p, i) in keptPs.zipIdx do m := m.set! p i
    for (p, i) in deadPs.zipIdx do m := m.set! p (np + i)
    for i in [f.params:total] do m := m.set! i i
    let σ : Nat → Exp := fun i => .loc (m.getD i i)
    let body := renL σ m f.body
    let (next, body) := dropArgsL live total body
    out := out.push { f with params := np, locals := next - np, body }
  pure out

/-- Two expressions are the same expression. -/
def expEq : Exp → Exp → Bool
  | .loc a, .loc b => a == b
  | .c64 a, .c64 b => a == b
  | .c32 a, .c32 b => a == b
  | .data a, .data b => a == b
  | .tag a, .tag b => a == b
  | .undef, .undef => true
  | .load a o, .load b o' => o == o' && expEq a b
  | .load8 a, .load8 b => expEq a b
  | .op o as, .op o' bs => o == o' && as.length == bs.length && expEqs as bs
  | _, _ => false
where
  expEqs : List Exp → List Exp → Bool
    | [], [] => true
    | a :: as, b :: bs => expEq a b && expEqs as bs
    | _, _ => false

/-- How a branch ends: a tail call of `g` on `as`, a `ret` of `es`, a `trap`, or otherwise. -/
inductive End where
  | tail (g : Nat) (as : List Exp)
  | ret (es : List Exp)
  | trap
  | other

def endOf (ss : List Stmt) : End :=
  match ss.getLast? with
  | some (.tailCall g as) => .tail g as
  | some (.ret es) => .ret es
  | some .trap => .trap
  | _ => .other

/-- The exit the branches `bs` share, when at least two end with it and the rest trap: the callee
(`some g`, or `none` for a `ret`) and its words' expressions in each such branch. -/
def sharedExit (bs : List (List Stmt)) : Option (Option Nat × List (Option (List Exp))) := Id.run do
  let ends := bs.map endOf
  let mut target : Option (Option Nat × Nat) := none
  let mut n := 0
  for e in ends do
    match e, target with
    | .tail g as, none => target := some (some g, as.length); n := n + 1
    | .ret es, none => target := some (none, es.length); n := n + 1
    | .tail g as, some (some g', k) => if g == g' && as.length == k then n := n + 1 else return none
    | .ret es, some (none, k) => if es.length == k then n := n + 1 else return none
    | .trap, _ => pure ()
    | _, _ => return none
  let some (t, _) := target | return none
  if n < 2 then return none
  pure (some (t, ends.map fun e => match e with
    | .tail _ as => some as
    | .ret es => some es
    | _ => none))

/-- `ss` with its last statement replaced by the sets `ts := es`. -/
def endWithSets (ss : List Stmt) (sets : List Stmt) : List Stmt :=
  match ss.getLast? with
  | some (.tailCall ..) | some (.ret _) => ss.dropLast ++ sets
  | _ => ss

/-- The branches `bs` of a branching that is last in its list, its shared exit hoisted after it
when at least two branches end with the same tail call (or both `ret`): each word on which they
differ is set in each branch and passed from a fresh local. The loop of tail calls then has one
back edge. -/
def hoistExit (fresh : Nat) (bs : List (List Stmt)) : Nat × List (List Stmt) × List Stmt :=
  match sharedExit bs with
  | none => (fresh, bs, [])
  | some (t, argss) =>
    let present := argss.filterMap id
    let k := (present.headD []).length
    -- Per word: the expression every branch agrees on, or a fresh local.
    let (fresh', slots) := (List.range k).foldl (fun (n, acc) j =>
      let es := present.map (·.getD j (.c64 0))
      match es with
      | e :: more => if more.all (expEq e ·) then (n, acc ++ [Sum.inl e]) else (n + 1, acc ++ [Sum.inr n])
      | [] => (n, acc ++ [Sum.inl (.c64 0)])) (fresh, [])
    let bs' := (bs.zip argss).map fun (b, a?) => match a? with
      | some as =>
        let sets := (slots.zip as).filterMap fun (sl, e) => match sl with
          | .inr l => some (Stmt.set l e)
          | .inl _ => none
        endWithSets b sets
      | none => b
    let args := slots.map fun sl => match sl with
      | .inl e => e
      | .inr l => .loc l
    let exit := match t with
      | some g => Stmt.tailCall g args
      | none => Stmt.ret args
    (fresh', bs', [exit])

mutual
/-- `ss` with the exits shared by the branches of each last `ite` and `switch` hoisted after it
(`hoistExit`), innermost first. -/
def mergeL (fresh : Nat) : List Stmt → Nat × List Stmt
  | [] => (fresh, [])
  | [s] => mergeLast fresh s
  | s :: ss =>
    let (n₁, s') := mergeInner fresh s
    let (n₂, ss') := mergeL n₁ ss
    (n₂, s' :: ss')
/-- A last statement: its branches merged, then its shared exit hoisted. -/
def mergeLast (fresh : Nat) : Stmt → Nat × List Stmt
  | .ite c t e =>
    let (n₁, t') := mergeL fresh t
    let (n₂, e') := mergeL n₁ e
    match hoistExit n₂ [t', e'] with
    | (n₃, [t'', e''], ex) => (n₃, .ite c t'' e'' :: ex)
    | (n₃, _, _) => (n₃, [.ite c t' e'])
  | .switch x cs d =>
    let (n₁, cs') := mergeLL fresh cs
    let (n₂, d') := mergeL n₁ d
    let (n₃, bs, ex) := hoistExit n₂ (cs' ++ [d'])
    (n₃, .switch x (bs.dropLast) (bs.getLast?.getD d') :: ex)
  | s => (fresh, [s])
/-- A statement that is not last: only its branches merged. -/
def mergeInner (fresh : Nat) : Stmt → Nat × Stmt
  | .ite c t e =>
    let (n₁, t') := mergeL fresh t
    let (n₂, e') := mergeL n₁ e
    (n₂, .ite c t' e')
  | .switch x cs d =>
    let (n₁, cs') := mergeLL fresh cs
    let (n₂, d') := mergeL n₁ d
    (n₂, .switch x cs' d')
  | s => (fresh, s)
def mergeLL (fresh : Nat) : List (List Stmt) → Nat × List (List Stmt)
  | [] => (fresh, [])
  | c :: cs =>
    let (n₁, c') := mergeL fresh c
    let (n₂, cs') := mergeLL n₁ cs
    (n₂, c' :: cs')
end

/-- `f` with its shared exits hoisted (`mergeL`). -/
def mergeExits (f : Fn) : Fn :=
  let (next, body) := mergeL (f.params + f.locals) f.body
  { f with locals := next - f.params, body }

/-- `f` with its locals numbered densely after its parameters, in order of first use. -/
def compact (f : Fn) : Fn := Id.run do
  let mut m : Std.HashMap Nat Nat := {}
  let mut next := f.params
  for i in readsL f.body ++ setsL f.body do
    if i ≥ f.params && !m.contains i then
      m := m.insert i next; next := next + 1
  let total := (readsL f.body ++ setsL f.body).foldl max (f.params + f.locals)
  let mut arr : Array Nat := Array.range (total + 1)
  for (i, j) in m.toList do arr := arr.set! i j
  let body := renL (fun i => .loc (arr.getD i i)) arr f.body
  pure { f with locals := next - f.params, body }

/-- The specialized program: the functions the entry reaches, each expanded, with their
specializations; then narrowed. -/
def optimize (p : Prog) : Except String Prog := do
  let env : Env := { fns := p.fns, info := infos p.fns }
  let act : OM Nat := do
    let e ← outOf p.entry
    for _ in [0:1 <<< 20] do
      let s ← get
      let some j := s.jobs.back? | break
      set { s with jobs := s.jobs.pop }
      runJob j
    pure e
  let (entry, s) ← (act.run env).run {}
  let mut fns := s.outFns.map dropDeadSets
  for _ in [0:3] do fns := (dropDeadParams fns entry).map dropDeadSets
  pure { p with fns := fns.map (compact ∘ mergeExits), entry }

end Backend.Flat.Opt

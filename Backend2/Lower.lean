import Std.Data.HashMap
import Target.Flat.Syntax
import Target.Flat.Host
import Backend2.Layout

/-!
# Backend2 — the LIR to the word IR  `[spec §35, §37, §64]`

Each LIR variable is the words of its layout node (`Backend2/Layout.lean`), held in locals; each
LIR function a word-IR function of its parameters' words, answering its result's words. The
word IR (`Backend/Flat/Syntax.lean`) is target-neutral: the Wasm and LLVM emitters take it.

- **Pairs** are their fields' words; a **sum** a tag word and its payload's, padded, its merged
  arm's words its own and a packed sum one word `tag << 32 | payload` (`Layout.lean`, SPEC §43). A field the
  layout boxes is a pointer to an object holding its words: built by allocating it, taken apart
  by loading and freeing it. A box a `letpair` or a `case` takes apart is a spare box until the
  path's next call, return or arm's end, and the next box of its words built before then is
  built in it (SPEC §64).
- **Closures** are defunctionalized: a closure is its code's tag in its class, then its captured
  values' words, padded to the class's widest. A call of a closure whose class has one code is a
  direct call of that code's function; any other is a call of the class's dispatcher, a `switch`
  on the tag. A class that holds itself keeps its environment on the heap: the word `2t + 1`, or
  an object holding the tag and the captured words.
- **Copies and consumes** are the LIR's, at their layouts: a copy at a type with boxed fields or a
  heap closure is a generated deep copy, counted under `copies` in the counting build; a consume
  frees what the layout allocated.
- **Cells and slots** hold their contents' words, or a slot of a byte or of 4 bytes (`i32`,
  `f32`) where the cell's class holds only integers of that width.
- **Calls in tail position** whose callee answers the caller's words are tail calls.
-/

namespace Backend2.Low
open BoCa Backend.Flat Backend2.Lay

/-- A function generated per layout node. -/
inductive Helper where
  | copy (n : Nat)
  | consume (n : Nat)
  | print (n : Nat)
  /-- A read through `Imm̲`: the contents at node `c` copied to the reading's node `d`. -/
  | reCopy (c d : Nat)
  /-- The dispatcher of a closure class, at its component `j`. -/
  | apply (cls j : Nat)
  /-- The task stack's push and pop (SPEC §52), on the register's address. -/
  | stackPush
  | stackPop
  deriving BEq, Hashable, Inhabited

structure LCtx where
  L : Layouts
  p : Prog
  helperBase : Nat
  counts : Bool
  /-- The offset in the data of each static cell (`Prog.statics`). -/
  staticAt : Array Nat := #[]
  /-- The code of each call's function variable, where the closure flow finds one. -/
  known : Std.HashMap Var Nat := {}
  /-- The codes the closure flow finds at each closure variable (`Backend2/Flow.lean`). -/
  codes : Std.HashMap Var (Std.HashSet Nat) := {}
  /-- The lend scopes whose cell is a frame slot (`Prog.slots`). -/
  slotScopes : Std.HashSet Nat := {}

structure LState where
  locals : Std.HashMap Var (List Nat) := {}
  next : Nat := 0
  /-- The words of the function's frame so far. -/
  frame : Nat := 0
  helpers : Std.HashMap Helper Nat := {}
  queue : Array Helper := #[]
  /-- The locals some variable's layout places an address in (`addrKinds`), and those some
  variable's layout places another word in: a local is a pointer when it is only the first. -/
  ptrVote : Std.HashSet Nat := {}
  intVote : Std.HashSet Nat := {}
  /-- `addrKinds` per representative node, as computed with fuel enough. -/
  kinds : Std.HashMap Nat (List (Option Bool)) := {}
  /-- The spare boxes on the path being lowered (SPEC §64): each a boxed field's object whose
  words a `letpair` or a `case` has loaded and whose free is deferred, as the local holding its
  address and its words. -/
  spare : List (Nat × Nat) := []

abbrev LM := ReaderT LCtx (StateT LState (Except String))

def fnIndex (fn : Nat) : Nat := 1 + fn

def fresh (k : Nat) : LM (List Nat) :=
  modifyGet fun s => (List.range' s.next k, { s with next := s.next + k })

def fresh1 : LM Nat := modifyGet fun s => (s.next, { s with next := s.next + 1 })

def locs (ls : List Nat) : List Exp := ls.map .loc
def zeros (k : Nat) : List Exp := List.replicate k (.c64 0)

def L : LM Layouts := return (← read).L
def nodeV (x : Var) : LM Nat := return (← L).node x
def wordsN (n : Nat) : LM Nat := return (← L).w n
def wordsV (x : Var) : LM Nat := do wordsN (← nodeV x)

/-! ### Addresses -/

/-- Two words' kinds where a sum's arms or a class's codes share them: `none` is padding. -/
def agree : Option Bool → Option Bool → Option Bool
  | none, x => x
  | x, none => x
  | some a, some b => some (a && b)

/-- **Which words of a value at node `n` hold an address** (SPEC §35, typed pointers): a cell's or
a borrow's word, a family's base, a boxed field's pointer (`some true`); a sum's payload word
where the arms agree, padding (`none`) agreeing with either; a closure's captured word where its
class's codes agree. A heap class's word is `2t + 1` or an address, so it is not one. Read off the
layout node, which is the variable's type (`Backend2/Layout.lean`).

It recurses through the node's inline children (`LayCheck.inlineKids`: the fields not boxed, a
class's codes' environments when the class is not on the heap), a graph with no cycle
(`LayCheck.layoutOk`, checked of every program's layouts), so a fuel at least the node's depth
there reaches every leaf. The answer depends on the node's representative alone, and is kept in
`memo` under it; the flag says no fuel ran out below, and only such answers are kept, so a kept
answer is the one any fuel at least the depth gives. Where the fuel runs out, the words are read
as not addresses. -/
def addrKinds (L : Layouts) :
    Nat → Nat → StateM (Std.HashMap Nat (List (Option Bool))) (List (Option Bool) × Bool)
  | 0, n => do
    if let some ks := (← get)[L.r n]? then return (ks, true)
    pure (List.replicate (L.w n) (some false), false)
  | f + 1, n => do
    if let some ks := (← get)[L.r n]? then return (ks, true)
    let pad (k : Nat) (xs : List (Option Bool)) : List (Option Bool) :=
      xs ++ List.replicate (k - xs.length) none
    let (ks, exact) ← match L.sh n with
      | .ref _ | .imm _ | .mut _ => pure ([some true], true)
      | .fam _ => pure ([some true, some false], true)
      | .pair a b => do
        let (x, e₁) ← if L.isBoxed n 0 then pure ([some true], true) else addrKinds L f a
        let (y, e₂) ← if L.isBoxed n 1 then pure ([some true], true) else addrKinds L f b
        pure (x ++ y, e₁ && e₂)
      | .sum a b => do
        if L.isPacked n then pure ([some false], true) else do
        let (x, e₁) ← if L.isBoxed n 0 then pure ([some true], true) else addrKinds L f a
        let (y, e₂) ← if L.isBoxed n 1 then pure ([some true], true) else addrKinds L f b
        -- A merged arm's words are the arm's own, its tag word the sum's.
        let x := if L.merged n == some 0 then x.drop 1 else x
        let y := if L.merged n == some 1 then y.drop 1 else y
        let pw := L.w n - 1
        pure (some false :: List.zipWith agree (pad pw x) (pad pw y), e₁ && e₂)
      | .clos .. =>
        if L.isRec n then pure ([some false], true) else do
        let pw := L.w n - 1
        let mut acc : List (Option Bool) := List.replicate pw none
        let mut ex := true
        for c in (L.unionOf n).toList do
          let mut ws : List (Option Bool) := []
          for e in L.codeEnv.getD c [] do
            let (k, x) ← addrKinds L f e
            ws := ws ++ k
            ex := ex && x
          acc := List.zipWith agree acc (pad pw ws)
        pure (some false :: acc, ex)
      | _ => pure (List.replicate (L.w n) (some false), true)
    if exact then modify (·.insert (L.r n) ks)
    pure (ks, exact)

/-- The locals `ls`, the words of a value at node `n`: each voted a pointer or not by the node. -/
def vote (n : Nat) (ls : List Nat) : LM Unit := do
  let memo ← modifyGet fun s => (s.kinds, { s with kinds := {} })
  let ((ks, _), kinds) := (addrKinds (← read).L 256 n).run memo
  modify fun s => { s with kinds }
  if ks.length != ls.length then return
  for (l, k) in ls.zip ks do
    match k with
    | some true => modify fun s => { s with ptrVote := s.ptrVote.insert l }
    | some false => modify fun s => { s with intVote := s.intVote.insert l }
    | none => pure ()

def vals (x : Var) : LM (List Nat) := do
  match (← get).locals[x]? with
  | some ls => pure ls
  | none => throw s!"word IR: variable x{x} has no locals"

def bindVals (x : Var) (ls : List Nat) : LM Unit := do
  modify fun s => { s with locals := s.locals.insert x ls }
  vote ((← read).L.node x) ls

def helper (h : Helper) : LM Nat := do
  match (← get).helpers[h]? with
  | some i => pure i
  | none =>
    let base := (← read).helperBase
    modifyGet fun s => (base + s.queue.size,
      { s with helpers := s.helpers.insert h (base + s.queue.size), queue := s.queue.push h })

/-- Run `act` as the body of a function of `params` words: the locals beyond them, the frame's
words, and the locals that hold an address (`ptrVote`, `intVote`). -/
def inFnF (params : Nat) (act : LM α) : LM (α × Nat × Nat × List Nat) := do
  let saved ← get
  set { saved with locals := {}, next := params, frame := 0, ptrVote := {}, intVote := {},
                   spare := [] }
  let a ← act
  let st ← get
  let ptrs := st.ptrVote.toList.filter (!st.intVote.contains ·) |>.mergeSort (· ≤ ·)
  modify fun s => { s with locals := saved.locals, next := saved.next, frame := saved.frame,
                           ptrVote := saved.ptrVote, intVote := saved.intVote,
                           spare := saved.spare }
  pure (a, st.next - params, st.frame, ptrs)

def inFn (params : Nat) (act : LM α) : LM (α × Nat × List Nat) := do
  let (a, n, _, ps) ← inFnF params act
  pure (a, n, ps)

/-- The words of a stack's first chunk, and of each later one (SPEC §52). -/
def stackChunk0 : Nat := 256
def stackChunk : Nat := 4096

/-- Where a term's words go: locals, returned (padded to `k` words), or bound to a variable. -/
inductive Dest where
  | to (ls : List Nat)
  | ret (k : Nat)
  | bind (x : Var)

/-- Free the spare boxes (SPEC §64), keeping them listed: at a return, after which nothing on the
path runs, while another path lowered after it may still hold them. -/
def freeSpares : LM (List Stmt) := do
  return (← get).spare.map fun (t, _) => .free (.loc t)

/-- Free the spare boxes (SPEC §64) and forget them: the path goes on past the frees. -/
def dropSpares : LM (List Stmt) := do
  let s ← freeSpares
  modify fun st => { st with spare := [] }
  return s

def emit : Dest → List Exp → LM (List Stmt)
  | .to ls, vs => do
    if ls.length != vs.length then throw s!"word IR: {vs.length} words for {ls.length} locals"
    pure (ls.zip vs |>.map fun (l, e) => .set l e)
  | .ret k, vs => do
    if vs.length > k then throw s!"word IR: {vs.length} words returned for {k}"
    pure ((← freeSpares) ++ [.ret (vs ++ zeros (k - vs.length))])
  | .bind x, vs => do
    let mut ls : Array Nat := #[]
    let mut ss : Array Stmt := #[]
    for v in vs do
      match v with
      | .loc l => ls := ls.push l
      | e =>
        let t ← fresh1
        ss := ss.push (.set t e)
        ls := ls.push t
    bindVals x ls.toList
    return ss.toList

/-! ### Fields -/

def storeAt (a : Exp) (off : Nat) (vs : List Exp) : List Stmt :=
  vs.zipIdx.map fun (e, i) => .store a (off + i) e

def loadAt (a : Exp) (off k : Nat) : LM (List Stmt × List Nat) := do
  let ls ← fresh k
  pure (ls.zipIdx.map (fun (l, i) => .set l (.load a (off + i))), ls)

/-- The child node of a pair or a sum. -/
def child (n k : Nat) : LM Nat := do
  match (← L).sh n, k with
  | .pair a _, 0 | .sum a _, 0 => pure a
  | .pair _ b, _ | .sum _ b, _ => pure b
  | s, _ => throw s!"word IR: no field {k} of {reprStr s |>.take 40}"

/-- Field `k` of `n` built from its words: behind a pointer when it is boxed. With `reuse`, a spare
box of the same words (SPEC §64) holds them, and none is allocated.  `[spec §64]` -/
def putField (n k : Nat) (vs : List Exp) (reuse : Bool := false) : LM (List Stmt × List Exp) := do
  if !(← L).isBoxed n k then return ([], vs)
  let w := max 1 vs.length
  if reuse then
    let sp := (← get).spare
    if let some (t, _) := sp.find? (·.2 == w) then
      modify fun st => { st with spare := sp.erase (t, w) }
      return (storeAt (.loc t) 0 vs, [.loc t])
  let t ← fresh1
  return ([.set t (.alloc (.c64 w.toUInt64))] ++ storeAt (.loc t) 0 vs, [.loc t])

/-- The words of field `k` of `n` from the field's locals: loaded from behind a pointer when boxed,
the object freed when `consume`. With `keep`, its free is deferred instead: the object is a spare
box (SPEC §64), freed at the path's next call or end unless a box of its words is built first.
`[spec §64]` -/
def getField (n k : Nat) (ls : List Nat) (consume : Bool) (keep : Bool := false) :
    LM (List Stmt × List Nat) := do
  if !(← L).isBoxed n k then return ([], ls)
  let c ← child n k
  let p := Exp.loc (ls.headD 0)
  let w ← wordsN c
  let (s, vs) ← loadAt p 0 w
  if consume && keep then
    -- UNPROVED: that the object has one owner, the value taken apart here, so that deferring
    -- its free to the next call, return or arm's end, or building the next box of its words in
    -- it, aliases nothing. It is `Layout.resolve`'s assumption on boxed fields, on which the
    -- free made here otherwise rests too: the LIR consumes each variable once on every path,
    -- which `Lint` checks of each program it compiles. If it fails, a box is written while
    -- another value still reads it.
    let t ← fresh1
    modify fun st => { st with spare := st.spare ++ [(t, max 1 w)],
                                ptrVote := st.ptrVote.insert t }
    return (s ++ [.set t p], vs)
  return (s ++ (if consume then [.free p] else []), vs)

/-- The locals of field `k` of a pair's or a sum's locals. -/
def fieldLocals (n k : Nat) (ls : List Nat) : LM (List Nat) := do
  let L ← L
  match L.sh n with
  | .pair .. =>
    let w₀ := L.fieldW n 0
    pure (if k == 0 then ls.take w₀ else (ls.drop w₀).take (L.fieldW n 1))
  | _ => pure ((ls.drop 1).take (L.fieldW n k))

def mkPair (n : Nat) (a b : List Exp) (reuse : Bool := false) : LM (List Stmt × List Exp) := do
  let (s₁, v₁) ← putField n 0 a reuse
  let (s₂, v₂) ← putField n 1 b reuse
  pure (s₁ ++ s₂, v₁ ++ v₂)

/-- The low half of a word, a packed sum's payload. -/
def low32 (e : Exp) : Exp := and64 e (.c64 0xFFFFFFFF)

/-- The tag of arm `k` of the sum at `n` that is not merged: `k`, or after the merged arm's tags. -/
def armTag (L : Layouts) (n k : Nat) : Nat :=
  match L.merged n with
  | some _ => L.tagsOf n - 1
  | none => k

/-- **A sum's words** at `n` of arm `r` holding `a` (SPEC §43): on a merged arm `a` itself, padded;
else the arm's tag and its field's words, padded, or packed into one word.  `[spec §43]` -/
def mkInj (n : Nat) (r : Bool) (a : List Exp) (reuse : Bool := false) :
    LM (List Stmt × List Exp) := do
  let L ← L
  let k := if r then 1 else 0
  let w := L.w n
  if L.merged n == some k then return ([], a.take w ++ zeros (w - a.length))
  let t := armTag L n k
  let (s, v) ← putField n k a reuse
  if L.isPacked n then
    let tw : Exp := .c64 (t.toUInt64 <<< 32)
    return (s, [match v.head?, t with
      | none, _ => tw
      | some p, 0 => low32 p
      | some p, _ => .op (.bin .w64 .or) [tw, low32 p]])
  pure (s, [.c64 t.toUInt64] ++ v ++ zeros (w - 1 - v.length))

/-- **The test that a sum's words `ls` at `n` are its left arm**: the tag below the left arm's
tags' end. With no arm merged and not packed, the tag word is `0`.  `[spec §43]` -/
def sumLeft (n : Nat) (ls : List Nat) : LM Exp := do
  let L ← L
  let w := Exp.loc (ls.headD 0)
  let pk := L.isPacked n
  let tw (t : Nat) : Exp := .c64 (if pk then t.toUInt64 <<< 32 else t.toUInt64)
  match L.merged n with
  | none => pure (if pk then ltu64 w (tw 1) else eqz64 w)
  -- The right arm merged: its tags first, the left arm the last tag.
  | some 1 => pure (.op (.rel .w64 .ge_u) [w, tw (L.tagsOf n - 1)])
  | some _ => pure (ltu64 w (tw (L.tagsOf n - 1)))

def splitPair (n : Nat) (ls : List Nat) (consume : Bool) (keep : Bool := false) :
    LM (List Stmt × List Nat × List Nat) := do
  let (s₁, a) ← getField n 0 (← fieldLocals n 0 ls) consume keep
  let (s₂, b) ← getField n 1 (← fieldLocals n 1 ls) consume keep
  pure (s₁ ++ s₂, a, b)

/-- **Arm `r`'s words** of the sum's words `ls` at `n`: on a merged arm the sum's own, the arm's
encoding; at a packed sum the low half; else the field's.  `[spec §43]` -/
def payload (n : Nat) (r : Bool) (ls : List Nat) (consume : Bool) (keep : Bool := false) :
    LM (List Stmt × List Nat) := do
  let L ← L
  let k := if r then 1 else 0
  if L.merged n == some k then return ([], ls.take (L.w (← child n k)))
  if L.isPacked n then
    if L.fieldW n k == 0 then return ([], [])
    let t ← fresh1
    return ([.set t (low32 (.loc (ls.headD 0)))], [t])
  getField n k (← fieldLocals n k ls) consume keep

/-- **The words of a value at `c` are those of one at `n`** (SPEC §43): one node, or the same width
and, at every pair and sum along the fields not boxed, the same boxes and, at a sum, the same
merged arm, tags and packing. A read through `Imm̲` relates nodes of different leaves (`joinRe`:
a closure, an opaque value or a cell read as `Unk`, a cell as a borrow), and a leaf of one word
against `Unk`'s none can change a sum's packing or merged arm at the same total width; a leaf's
own words agree when the widths do. Within `fuel` formers deep; `false` past it. -/
def sameEnc (L : Layouts) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | f + 1, c, n =>
    L.r c == L.r n || (L.w c == L.w n &&
      match L.sh c, L.sh n with
      | .pair a b, .pair a' b' | .sum a b, .sum a' b' =>
        let enc := match L.sh c with
          | .sum .. => L.merged c == L.merged n && L.tagsOf c == L.tagsOf n &&
              L.isPacked c == L.isPacked n
          | _ => true
        let fld (k x y : Nat) : Bool :=
          L.isBoxed c k == L.isBoxed n k && (L.isBoxed c k || sameEnc L f x y)
        enc && fld 0 a a' && fld 1 b b'
      | .pair .., _ | .sum .., _ | _, .pair .. | _, .sum .. => false
      | _, _ => true)

/-! ### Cells -/

/-- The contents' node of a pointer node. -/
def contents (n : Nat) : LM Nat := do
  match (← L).sh n with
  | .ref c | .imm c | .mut c => pure c
  | s => throw s!"word IR: not a pointer: {reprStr s |>.take 40}"

/-- The bytes between two slots of the cell at pointer node `n`: its contents' bytes in a cell. -/
def slotStride (n : Nat) : LM Nat := do return (← L).repB (← contents n)

/-- The contents of the cell at `a`, of pointer node `n`, in `k` fresh locals: a byte at `u8`, 4
bytes at `i32` and `f32`, else `k` words (`Layouts.repB`). -/
def loadCell (n : Nat) (a : Exp) (k : Nat) : LM (List Stmt × List Nat) := do
  match (← L).sh (← contents n) with
  | .int .w8 => do let t ← fresh1; return ([.set t (.load8 a)], [t])
  | .int .w32 | .int .f32 | .int .u32 => do let t ← fresh1; return ([.set t (.load32 a)], [t])
  | _ => loadAt a 0 k

def storeCell (n : Nat) (a : Exp) (vs : List Exp) : LM (List Stmt) := do
  match (← L).sh (← contents n) with
  | .int .w8 => return [.store8 a (vs.headD (.c64 0))]
  | .int .w32 | .int .f32 | .int .u32 => return [.store32 a (vs.headD (.c64 0))]
  | _ => return storeAt a 0 vs

/-- The leaf node of a family node. -/
def leafOf (n : Nat) : LM Nat := do
  match (← L).sh n with
  | .fam l => pure l
  | s => throw s!"word IR: not a family: {reprStr s |>.take 40}"

/-! ### Copies and consumes -/

/-- A copy of the words `ls` at node `n`; with `tick`, counted in the counting build (a copy the
LIR makes; a copy inside a generated copy is part of it). -/
def copyVals (n : Nat) (ls : List Nat) (tick : Bool := false) : LM (List Stmt × List Nat) := do
  if (← L).triv n then return ([], ls)
  let ts ← fresh (← wordsN n)
  let tick := if (← read).counts && tick then [Stmt.tickCopy] else []
  return (tick ++ [.call ts (← helper (.copy ((← L).r n))) (locs ls)], ts)

def consumeVals (n : Nat) (ls : List Nat) : LM (List Stmt) := do
  if (← L).triv n then return []
  return [.call [] (← helper (.consume ((← L).r n))) (locs ls)]


/-! ### Closures -/

/-- The class of a closure node. -/
def classOf (n : Nat) : LM (CodeKind × Option Nat × List Nat) := do
  match (← L).sh n with
  | .clos k p r => pure (k, p, r)
  | s => throw s!"word IR: not a closure: {reprStr s |>.take 40}"

/-- The words of a closure of code `c` (at class node `n`) whose captured values are `env`. -/
def closVals (n c : Nat) (env : List Exp) : LM (List Stmt × List Exp) := do
  let L ← L
  let t := L.tagOf c
  if L.isRec n then
    if env.isEmpty then return ([], [.c64 (2 * t + 1).toUInt64])
    let p ← fresh1
    return ([.set p (.alloc (.c64 (1 + env.length).toUInt64)), .store (.loc p) 0 (.c64 t.toUInt64)] ++
      storeAt (.loc p) 1 env, [.loc p])
  return ([], [.c64 t.toUInt64] ++ env ++ zeros (L.w n - 1 - env.length))

/-- The captured values' words of the closure in `ls`, of code `c` at class node `n`: from the
closure's words, or from its heap object, which is freed. -/
def envOf (n c : Nat) (ls : List Nat) : LM (List Stmt × List Exp) := do
  let L ← L
  let ew := L.envWords c
  if L.isRec n then
    if ew == 0 then return ([], [])
    let p := Exp.loc (ls.headD 0)
    let (s, vs) ← loadAt p 1 ew
    return (s ++ [.free p], locs vs)
  return ([], locs ((ls.drop 1).take ew))

/-- The function of component `j` of code `c`. -/
def codeFn (c j : Nat) : LM Nat := do
  match (← read).p.codes[c]? with
  | some code => pure (fnIndex (code.fns.getD j 0))
  | none => throw s!"word IR: no code c{c}"

/-- The function and arguments of a call of the closure in `ls` (class node `n`), at component
`j`, on `args`: the code's function directly when the class has one code, else the dispatcher. -/
def callTarget (n j : Nat) (ls : List Nat) (args : List Exp) (g : Option Var := none) :
    LM (List Stmt × Nat × List Exp) := do
  let L ← L
  let u := L.unionOf n
  let km := (← read).known
  let known := match g with
    | some g => match km[g]? with
      | some c => if u.contains c then some c else none
      | none => none
    | none => none
  let known := if u.size == 1 then u[0]? else known
  if let some c := known then
    let (s, env) ← envOf n c ls
    return (s, ← codeFn c j, env ++ args)
  let tick := if (← read).counts then [Stmt.tick] else []
  return (tick, ← helper (.apply (L.r n) j), locs ls ++ args)

/-! ### Host operations -/

/-- A host operation on its operand's words (§8, §37): its answer's words, at node `n`. -/
def hostVals (o : HostOp) (n : Nat) (ls : List Nat) : LM (List Stmt × List Exp) := do
  -- `U32`/`U64` are held as `I32`/`I64` are, so `reinterpret_u`/`_s` is the word, and an
  -- operation at an unsigned width is its signed sibling's (`machineOp`).  [spec §73]
  let o := machineOp o
  match o with
  | .wrap8 => return ([], [and64 (.loc (ls.headD 0)) (.c64 0xff)])
  | .extend8_u | .reinterpret_i _ | .reinterpret_f _ | .reinterpret_u _ | .reinterpret_s _ =>
    return ([], [.loc (ls.headD 0)])
  | _ => pure ()
  let rawAt (w : Width) (e : Exp) : Exp := match w with
    | .w32 | .w8 | .f32 | .u32 => wrap e
    | .w64 | .f64 | .u64 => e
  let args := ls.map fun l => rawAt (hostArgWidth o) (.loc l)
  let word (w : Width) (e : Exp) : Exp := match w with
    | .w32 | .w8 | .f32 | .u32 => extendU e
    | .w64 | .f64 | .u64 => e
  match hostResKind o, o with
  | .int w, _ => pure ([], [word w (.op o args)])
  | .test, _ => pure ([], [extendU (.op o args)])
  | .trapping w, .div w' d => do
    let t₀ ← fresh1
    let t₁ ← fresh1
    let a := args.headD (.c64 0)
    let b := args.getD 1 (.c64 0)
    let zero := Exp.op (.eqz w') [b]
    let trapC := match d with
      | .div_s =>
        let intMin := match w' with
          | .w32 | .w8 | .f32 | .u32 => Exp.c32 0x80000000 | .w64 | .f64 | .u64 => .c64 0x8000000000000000
        let m1 := match w' with
          | .w32 | .w8 | .f32 | .u32 => Exp.c32 0xFFFFFFFF | .w64 | .f64 | .u64 => .c64 0xFFFFFFFFFFFFFFFF
        or32 zero (and32 (.op (.rel w' .eq) [a, intMin]) (.op (.rel w' .eq) [b, m1]))
      | _ => zero
    -- `inl` the quotient, `inr ()` where the division has no answer: the sum's words at `n`.
    let (_, vr) ← mkInj n true []
    let (_, vl) ← mkInj n false [word w (.op o args)]
    let ts := [t₀, t₁].take vl.length
    let sets (vs : List Exp) : List Stmt := (ts.zip vs).map fun (t, e) => .set t e
    pure ([.ite trapC (sets vr) (sets vl)], locs ts)
  | .trapping w, .trunc i f sx =>
    let t₀ ← fresh1
    let t₁ ← fresh1
    let x := args.headD (.c64 0)
    let (loOp, lo, hi) := truncRange i f sx
    let ok := and32 (.op (.frel f loOp) [x, lo]) (.op (.frel f .lt) [x, hi])
    let (_, vl) ← mkInj n false [word w (.op (.trunc_sat i f sx) [x])]
    let (_, vr) ← mkInj n true []
    let ts := [t₀, t₁].take vl.length
    let sets (vs : List Exp) : List Stmt := (ts.zip vs).map fun (t, e) => .set t e
    pure ([.ite ok (sets vl) (sets vr)], locs ts)
  | .trapping _, _ => throw "word IR: an operation with no answer somewhere that is neither a division nor a trunc"

/-- A division whose divisor is a literal at which it cannot fail (`TExpr.divLit`): the operation
alone, with no test (SPEC §39). A byte's division is the `i32` one, narrowed. -/
def divLitVals (o : HostOp) (byte : Bool) (ls : List Nat) : LM (List Exp) := do
  let (w, _) ← match o with
    | .div w d => pure (w, d)
    | _ => throw "word IR: divLit of a non-division"
  let args := ls.map fun l => match w with
    | .w32 | .w8 | .f32 | .u32 => wrap (.loc l)
    | .w64 | .f64 | .u64 => Exp.loc l
  let q : Exp := match w with
    | .w32 | .w8 | .f32 | .u32 => extendU (.op o args)
    | .w64 | .f64 | .u64 => .op o args
  return [if byte then and64 q (.c64 0xff) else q]


/-- Call `f` on `args`, answering `k` words, to `d`. -/
def lowerCall (pre : List Stmt) (f : Nat) (args : List Exp) (k : Nat) (d : Dest) : LM (List Stmt) := do
  -- The spare boxes are freed before a call (SPEC §64).
  let pre := (← dropSpares) ++ pre
  match d with
  | .ret k' => if k' == k then return pre ++ [.tailCall f args] else pure ()
  | .to ls => if ls.length == k then return pre ++ [.call ls f args] else pure ()
  | .bind _ => pure ()
  let ts ← fresh k
  return pre ++ [.call ts f args] ++ (← emit d (locs ts))

/-! ### Primitives -/

def boundTick : LM (List Stmt) := do
  return if (← read).counts then [.tickBound] else []

def one (x : Var) : LM Exp := return .loc ((← vals x).headD 0)

def ltu32 (a b : Exp) : Exp := .op (.rel .w32 .lt_u) [wrap a, wrap b]

/-- A primitive on its arguments, its value at node `n` to `d`. -/
def lowerPrim (op : Op) (args : List Var) (n : Nat) (d : Dest) : LM (List Stmt) := do
  let arg (i : Nat) : LM (List Nat) := vals (args.getD i 0)
  let argN (i : Nat) : LM Nat := nodeV (args.getD i 0)
  match op with
  -- UNPROVED: that the host operations', `divLit`'s and the I/O operations' arguments and answers
  -- (integers, capabilities, families, and pairs and sums of them) are laid out flat: no field of
  -- theirs boxed. They read and write those words as they are, ignoring `isBoxed`. It should hold
  -- because a field is boxed only on a cycle of the fields (SPEC §35), which their types, holding
  -- no `μ` and no closure, cannot close; that rule is checked on every compile
  -- (`LayoutCheck.boxesOnCycles`). If it fails, a pointer is read as a value.
  | .host o => do
    let (s, vs) ← hostVals o n (← arg 0)
    return s ++ (← emit d vs)
  | .divLit o => do
    let byte := (← L).sh (← argN 0) == .int .w8
    emit d (← divLitVals o byte ((← arg 0) ++ (← arg 1)))
  | .cntLt => do
    let i ← one (args.getD 0 0)
    let k ← one (args.getD 1 0)
    emit d [extendU (ltu64 i k)]
  | .cntSucc => do
    let i ← one (args.getD 0 0)
    emit d [add64 i (.c64 1)]
  | .cntPred => do
    let i ← one (args.getD 0 0)
    emit d [.op (.bin .w64 .sub) [i, .c64 1]]
  | .clampLen => do
    let c ← one (args.getD 0 0)
    let t ← fresh1
    return [.ite (ltu32 c (.c64 0x80000000)) [.set t c] [.set t (.c64 0)]] ++ (← emit d [.loc t])
  | .alloc cls | .allocLent _ cls => do
    -- UNPROVED: that a cell holds, over its life, only types of the width class its allocation
    -- carries (`Checked.classAt` of the type it is allocated at, SPEC §57), so that the class's
    -- most bytes (`Layouts.clsBytes`) hold every value it is given, and a class of values of no
    -- bytes needs no allocation (the address `0`, which every target's `free` skips). It should
    -- hold because the checker's class is closed under every `swap` of the typed term
    -- (`Checked.classAt_alloc`), and only a `swap` changes a cell's type. That a location holds
    -- only its class's types at run time is not proved (`Frontend/Check/TFacts.lean`). If it
    -- fails, a store overruns the cell. A value's bytes and each type's most (`bytes`,
    -- `tyBytes`) are checked on every compile (`LayoutCheck.cellsOk`); the class is not.
    let b := (← L).clsBytes (← contents n) cls
    if b == 0 then return ← emit d [.c64 0]
    let t ← fresh1
    let w := (b + 7) / 8
    let slots := (← read).slotScopes
    let inFrame := match op with
      | .allocLent s _ => slots.contains s
      | _ => false
    let addr ← if inFrame then do
        let off := (← get).frame
        modify fun s => { s with frame := off + w }
        pure (Exp.slot off w)
      else pure (.alloc (.c64 w.toUInt64))
    return [.set t addr] ++ (← storeCell n (.loc t) (locs (← arg 0))) ++ (← emit d [.loc t])
  | .free => do
    let pn ← argN 0
    let a := Exp.loc ((← arg 0).headD 0)
    let (s, vs) ← loadCell pn a (← wordsN (← contents pn))
    -- The owner of a scope whose cell is a frame slot (`Prog.slots`) ends the slot's life.
    let rel := if (← read).p.slots.contains (args.getD 0 0) then Stmt.unslot a else .free a
    return s ++ [rel] ++ (← emit d (locs vs))
  | .release => do
    return [.free (.loc ((← arg 0).headD 0))] ++ (← emit d [])
  | .swap => do
    let pn ← argN 0
    let m := (← arg 0).headD 0
    let (s, old) ← loadCell pn (.loc m) (← wordsN (← contents pn))
    -- The old contents read at their type, the new written at theirs: the answer's cell's.
    let pn' ← child n 0
    return s ++ (← storeCell pn' (.loc m) (locs (← arg 1))) ++ (← emit d (locs (m :: old)))
  | .lend _ | .relend => do
    let ls ← arg 0
    emit d (locs ls ++ locs ls)
  | .load => do
    let pn ← argN 0
    let c ← contents pn
    let (s, vs) ← loadCell pn (.loc ((← arg 0).headD 0)) (← wordsN c)
    let L ← L
    if L.r c == L.r n || (L.triv c && sameEnc L 256 c n) then return s ++ (← emit d (locs vs))
    let ts ← fresh (← wordsN n)
    let tick := if (← read).counts && !L.triv c then [Stmt.tickCopy] else []
    return s ++ tick ++ [.call ts (← helper (.reCopy (L.r c) (L.r n))) (locs vs)] ++ (← emit d (locs ts))
  | .take => do
    let pn ← argN 0
    let m := (← arg 0).headD 0
    let (s, vs) ← loadCell pn (.loc m) (← wordsN (← contents pn))
    return s ++ (← emit d (locs (m :: vs)))
  | .put => do
    let pn ← argN 0
    let m := (← arg 0).headD 0
    return (← storeCell pn (.loc m) (locs (← arg 1))) ++ (← emit d [.loc m])
  | .tab fi | .tabLit fi .. => do
    let gv := args.head?
    let leaf ← leafOf n
    let st ← slotStride leaf
    let fw ← arg 0
    let k := (← arg 1).headD 0
    let b ← fresh1
    let bytes := mul64 (.loc k) (.c64 st.toUInt64)
    let words := shr64 (add64 bytes (.c64 7)) (.c64 3)
    let mk := if st == 0 then [Stmt.set b (.c64 0)] else
      [Stmt.ite (eqz64 (.loc k)) [.set b (.c64 0)] [.set b (.alloc words)]]
    let args := locs fw ++ [.loc b, .loc k, .c64 0, .loc k]
    -- A literal's view (`TExpr.litView`) whose tabulator the closure flow finds to be the literal
    -- tables' code alone: its environment is the literal's offset and length.
    let cx ← read
    let lit : Option Nat := match op, gv, cx.p.lits with
      | .tabLit _, some g, some lc =>
        let cs := cx.codes.getD g {}
        if cs.size == 1 && cs.contains lc then some lc else none
      | _, _, _ => none
    match lit with
    | some c => do
      -- UNPROVED: that the literal tables' class is not on the heap. `envOf` of a heap class frees
      -- its object, and the tabulator's words are then consumed (`consumeVals`) or passed on: one
      -- release too many. It should hold because a class is on the heap only where it holds itself
      -- (SPEC §35), checked on every compile (`LayoutCheck.boxesOnCycles`), and the literal
      -- tables' code captures two integers. A class that also holds a code capturing that class
      -- would be on the heap, and this would fail.
      let ts ← fresh 2
      let gn ← argN 0
      let (es, env) ← envOf gn c fw
      let dr ← consumeVals gn fw
      let off := env.headD (.c64 0)
      let len := env.getD 1 (.c64 0)
      return es ++ [.ite (.op (.rel .w64 .le_u) [.loc k, len])
          (dr ++ [.set (ts.headD 0) (.gep (.data 0) off), .set (ts.getD 1 0) (.loc k)])
          (mk ++ [.call ts (fnIndex fi) args])] ++ (← emit d (locs ts))
    | none => lowerCall mk (fnIndex fi) args 2 d
  | .newArr => do
    let leaf ← leafOf n
    let st ← slotStride leaf
    let k := (← arg 0).headD 0
    let b ← fresh1
    let bytes := mul64 (.loc k) (.c64 st.toUInt64)
    let words := shr64 (add64 bytes (.c64 7)) (.c64 3)
    if st == 0 then return [.set b (.c64 0)] ++ (← emit d [.loc b, .loc k])
    return [.ite (eqz64 (.loc k)) [.set b (.c64 0)] [.set b (.alloc words)]] ++ (← emit d [.loc b, .loc k])
  | .slotPut => do
    let leaf ← leafOf (← argN 0)
    let st ← slotStride leaf
    let a ← arg 0
    let i ← one (args.getD 1 0)
    let addr := Exp.gep (.loc (a.headD 0)) (mul64 i (.c64 st.toUInt64))
    return (← storeCell leaf addr (locs (← arg 2))) ++ (← emit d (locs a))
  | .slotTake => do
    let leaf ← leafOf (← argN 0)
    let st ← slotStride leaf
    let a ← arg 0
    let i ← one (args.getD 1 0)
    let addr := Exp.gep (.loc (a.headD 0)) (mul64 i (.c64 st.toUInt64))
    let (s, vs) ← loadCell leaf addr (← wordsN (← contents leaf))
    return s ++ (← emit d (locs a ++ locs vs))
  | .freeArr => do
    let b := Exp.loc ((← arg 0).headD 0)
    return [.ite (eqz64 b) [] [.free b]] ++ (← emit d [])
  | .size => do
    let a ← arg 0
    emit d (locs a ++ [.loc (a.getD 1 0)])
  | .len => do emit d [.loc ((← arg 0).getD 1 0)]
  | .emptyFam => emit d [.c64 0, .c64 0]
  | .idx check => do
    let leaf ← leafOf (← argN 0)
    let st ← slotStride leaf
    match ← arg 0, ← arg 1 with
    | [b, k], [i] =>
      let addr := Exp.gep (.loc b) (mul64 (.loc i) (.c64 st.toUInt64))
      -- `inl` the slot's address, `inr ()` past the end: the sum's words at `n`.
      let (_, vl) ← mkInj n false [addr]
      if !check then return ← emit d vl
      let (_, vr) ← mkInj n true []
      let ts ← fresh vl.length
      let sets (vs : List Exp) : List Stmt := (ts.zip vs).map fun (t, e) => .set t e
      return (← boundTick) ++ [.ite (ltu64 (.loc i) (.loc k)) (sets vl) (sets vr)] ++
        (← emit d (locs ts))
    | _, _ => throw "word IR: idx of a non-family"
  | .split _ => do
    let leaf ← leafOf (← argN 0)
    let st ← slotStride leaf
    match ← arg 0, ← arg 1 with
    | [b, k], [i] =>
      let pn ← child n 0
      let (s₁, vp) ← mkPair pn [.loc b, .loc i]
        [.gep (.loc b) (mul64 (.loc i) (.c64 st.toUInt64)), .op (.bin .w64 .sub) [.loc k, .loc i]]
      let (s₂, vl) ← mkInj n false vp
      let (s₃, vr) ← mkInj n true [.loc b, .loc k]
      let ts ← fresh vl.length
      let sets (vs : List Exp) : List Stmt := (ts.zip vs).map fun (t, e) => .set t e
      return (← boundTick) ++ [.ite (ltu64 (.loc k) (.loc i)) (s₃ ++ sets vr) (s₁ ++ s₂ ++ sets vl)] ++
        (← emit d (locs ts))
    | _, _ => throw "word IR: split of a non-family"
  | .replace => do
    let leaf ← leafOf (← argN 0)
    let st ← slotStride leaf
    match ← arg 0, ← arg 1 with
    | [b, k], [i] =>
      let x ← arg 2
      let addr := Exp.gep (.loc b) (mul64 (.loc i) (.c64 st.toUInt64))
      let on ← child n 1
      let (sL, old) ← loadCell leaf addr (← wordsN (← contents leaf))
      let sS ← storeCell leaf addr (locs x)
      let (s₁, vl) ← mkInj on false (locs old)
      let (s₂, vr) ← mkInj on true (locs x)
      let ts ← fresh vl.length
      let sets (vs : List Exp) : List Stmt := (ts.zip vs).map fun (t, e) => .set t e
      return (← boundTick) ++ [.ite (ltu64 (.loc i) (.loc k)) (sL ++ sS ++ s₁ ++ sets vl) (s₂ ++ sets vr)] ++
        (← emit d ([.loc b, .loc k] ++ locs ts))
    | _, _ => throw "word IR: replace of a non-family"
  | .swapSlots => do
    let leaf ← leafOf (← argN 0)
    let st ← slotStride leaf
    match ← arg 0, ← arg 1, ← arg 2 with
    | [b, k], [i], [j] =>
      let ai := Exp.gep (.loc b) (mul64 (.loc i) (.c64 st.toUInt64))
      let aj := Exp.gep (.loc b) (mul64 (.loc j) (.c64 st.toUInt64))
      let w ← wordsN (← contents leaf)
      let (l₁, x) ← loadCell leaf ai w
      let (l₂, y) ← loadCell leaf aj w
      let s₁ ← storeCell leaf ai (locs y)
      let s₂ ← storeCell leaf aj (locs x)
      let ok := and32 (and32 (ltu64 (.loc i) (.loc k)) (ltu64 (.loc j) (.loc k)))
        (.op (.rel .w64 .ne) [.loc i, .loc j])
      return (← boundTick) ++ (← boundTick) ++ [.ite ok (l₁ ++ l₂ ++ s₁ ++ s₂) []] ++ (← emit d [.loc b, .loc k])
    | _, _, _ => throw "word IR: swap of a non-family"
  | .roll | .unroll => do emit d (locs (← arg 0))
  | .stackSwap k => do
    let r := Exp.data ((← read).staticAt.getD k 0)
    let h := (← arg 0).headD 0
    let t ← fresh1
    return [.set t (.load r 0), .store r 0 (.loc h)] ++ (← emit d [.loc t])
  | .stackFree => do
    let h := Exp.loc ((← arg 0).headD 0)
    return [.ite (eqz64 h) [] [.free h]] ++ (← emit d [])
  | .framePush _ k => do
    let r := Exp.data ((← read).staticAt.getD k 0)
    let fn ← child n 0
    let w := max 1 (((← L).repB (← contents fn) + 7) / 8)
    let t ← fresh1
    return [.call [t] (← helper .stackPush) [r, .c64 w.toUInt64]] ++ (← emit d [.loc t, .loc t])
  | .frameTop _ k => do
    let r := Exp.data ((← read).staticAt.getD k 0)
    let fn ← child n 0
    let w := max 1 (((← L).repB (← contents fn) + 7) / 8)
    let t ← fresh1
    return [.set t (.op (.bin .w64 .sub) [.load (.load r 0) 0, .c64 (8 * w).toUInt64])] ++
      (← emit d [.loc t, .loc t])
  | .framePut => do
    let pn ← argN 0
    let f := (← arg 0).headD 0
    return (← storeCell pn (.loc f) (locs (← arg 1))) ++ (← emit d [])
  | .framePop k => do
    let r := Exp.data ((← read).staticAt.getD k 0)
    let f := (← arg 0).headD 0
    return [.call [] (← helper .stackPop) [r, .loc f]] ++ (← emit d [])
  | .unreachable => return [.trap] ++ (← emit d (zeros (← wordsN n)))
  | .stackNew s => do
    -- A stack's header (bump, end, chunk), the site's `κ` region, then its first chunk (header and
    -- words), as `stack push` makes one with no region.
    let w ← match (← L).regions[s]? with
      | some r => wordsN r
      | none => pure 0
    let h ← fresh1
    let base := 8 * (3 + w)
    return [.set h (.alloc (.c64 (6 + w + stackChunk0).toUInt64)),
      .store (.loc h) 0 (add64 (.loc h) (.c64 (base + 24).toUInt64)),
      .store (.loc h) 1 (add64 (.loc h) (.c64 (base + 24 + 8 * stackChunk0).toUInt64)),
      .store (.loc h) 2 (add64 (.loc h) (.c64 base.toUInt64)),
      .store (.loc h) (3 + w) (.c64 0), .store (.loc h) (4 + w) (.c64 0),
      .store (.loc h) (5 + w) (.c64 0)] ++ (← emit d [.loc h])
  | .kappaPut s => do
    let some _ := (← L).regions[s]? | throw "word IR: a κ region with no node"
    let h := (← arg 0).headD 0
    return storeAt (.gep (.loc h) (.c64 24)) 0 (locs (← arg 1)) ++ (← emit d [])
  | .kappaTake s => do
    let some r := (← L).regions[s]? | throw "word IR: a κ region with no node"
    let h := (← arg 0).headD 0
    let (st, vs) ← loadAt (.gep (.loc h) (.c64 24)) 0 (← wordsN r)
    return st ++ (← emit d ([.loc h] ++ locs vs))
  | .litByte => do
    let o := (← arg 0).headD 0
    let cnt := (← arg 1).headD 0
    let i := (← arg 2).headD 0
    let r ← fresh1
    return (← boundTick) ++
      [.ite (ltu64 (.loc i) (.loc cnt))
        [.set r (.load8 (.gep (.gep (.data 0) (.loc o)) (.loc i)))]
        [.set r (.c64 0)]] ++ (← emit d [.loc r])
  | .litView _ => throw "word IR: litView is not built yet"
  | .io .readByte => do
    let m := (← arg 0).headD 0
    let b ← fresh1; let t₀ ← fresh1; let t₁ ← fresh1
    -- `inl` the byte, `inr ()` at the input's end: the sum's words at the answer's second field.
    let sn ← child n 1
    let (_, vl) ← mkInj sn false [.loc b]
    let (_, vr) ← mkInj sn true []
    let ts := [t₀, t₁].take vl.length
    let sets (vs : List Exp) : List Stmt := (ts.zip vs).map fun (t, e) => .set t e
    return [.set b (.getc (.load (.loc m) 0)),
      .ite (eq64 (.loc b) (.c64 0xFFFFFFFFFFFFFFFF)) (sets vr) (sets vl)] ++
      (← emit d ([.loc m] ++ locs ts))
  | .io .writeByte => do
    match ← arg 0 with
    | [m, b] => return [.putc (.load (.loc m) 0) (.loc b)] ++ (← emit d [.loc m])
    | _ => throw "word IR: write_byte of a non-pair"
  | .io .writeAll => do
    match ← arg 0 with
    | [m, a, k] => return [.putv (.load (.loc m) 0) (.loc a) (.loc k)] ++ (← emit d [.loc m])
    | _ => throw "word IR: write_all of a non-pair"
  | .io .readInto => do
    match ← arg 0 with
    | [m, a, k] =>
      let r ← fresh1
      return [.set r (.getv (.load (.loc m) 0) (.loc a) (.loc k))] ++
        (← emit d [.loc m, .loc a, .loc k, .loc r])
    | _ => throw "word IR: read_into of a non-pair"
  | .io .clockNow => do
    let m := (← arg 0).headD 0
    let t ← fresh1
    return [.set t (.now (.loc m))] ++ (← emit d [.loc m, .loc t])
  | .io .clockSleep => do
    match ← arg 0 with
    | [m, ns] => return [.sleep (.loc m) (.loc ns)] ++ (← emit d [.loc m])
    | _ => throw "word IR: clock_sleep of a non-pair"


/-! ### Terms -/

/-- A term is a single value form: its words can be bound where they are made. -/
def tmSimple : Tm → Bool
  | .letv .. | .letpair .. | .case .. | .copy .. | .consume .. | .abandon .. | .absurd _ => false
  | _ => true

/-- The term `t`, whose value is at node `n`, its words to `d`. -/
def lowerTm (fuel : Nat) (t : Tm) (n : Nat) (d : Dest) : LM (List Stmt) := do
  match fuel with
  | 0 => throw "word IR: a term too deep"
  | f + 1 =>
  match t with
  | .var x => emit d (locs (← vals x))
  | .unit => emit d []
  | .lit c => emit d [.c64 (match c with
      | .i32 k => k.toUInt64 | .i64 k => k | .u8 k => k.toUInt64 | .f32 k => k.toUInt64 | .f64 k => k
      | .u32 k => k.toUInt64 | .u64 k => k)]
  | .pair a b => do
    let (s, vs) ← mkPair n (locs (← vals a)) (locs (← vals b)) (reuse := true)
    return s ++ (← emit d vs)
  | .inj r a => do
    let (s, vs) ← mkInj n r (locs (← vals a)) (reuse := true)
    return s ++ (← emit d vs)
  | .clos c env => do
    let ws ← env.mapM vals
    let (s, vs) ← closVals n c (locs ws.flatten)
    return s ++ (← emit d vs)
  | .app g a => do
    let gn ← nodeV g
    let (_, _, res) ← classOf gn
    let (pre, fn, args) ← callTarget gn 0 (← vals g) (locs (← vals a)) (some g)
    lowerCall pre fn args (← wordsN (res.headD n)) d
  | .app0 g => do
    let gn ← nodeV g
    let (_, _, res) ← classOf gn
    let (pre, fn, args) ← callTarget gn 0 (← vals g) [] (some g)
    lowerCall pre fn args (← wordsN (res.headD n)) d
  | .sel g j => do
    let gn ← nodeV g
    let (_, _, res) ← classOf gn
    let (pre, fn, args) ← callTarget gn j (← vals g) [] (some g)
    lowerCall pre fn args (← wordsN (res.getD j n)) d
  | .call fn as => do
    let ws ← as.mapM vals
    let some rn := (← L).fnRet[fn]? | throw s!"word IR: no node of f{fn}'s answer"
    lowerCall [] (fnIndex fn) (locs ws.flatten) (← wordsN rn) d
  | .prim op as => lowerPrim op as n d
  | .letv x e b => do
    let xn ← nodeV x
    let s₁ ← if tmSimple e then lowerTm f e xn (.bind x) else do
      let ls ← fresh (← wordsN xn)
      bindVals x ls
      lowerTm f e xn (.to ls)
    return s₁ ++ (← lowerTm f b n d)
  | .letpair x y p b => do
    let pn ← nodeV p
    let (s, a, c) ← splitPair pn (← vals p) true (keep := true)
    bindVals x a
    bindVals y c
    return s ++ (← lowerTm f b n d)
  | .case sv x b₁ y b₂ => do
    let sn ← nodeV sv
    let ls ← vals sv
    -- Each arm starts with the spare boxes held before the `case` and ends by freeing those it
    -- has not used (at a return, `emit` has freed them), so none is held past the join.
    let sp := (← get).spare
    let (s₁, a) ← payload sn false ls true (keep := true)
    bindVals x a
    let t₁ ← lowerTm f b₁ n d
    let e₁ ← dropSpares
    modify fun st => { st with spare := sp }
    let (s₂, c) ← payload sn true ls true (keep := true)
    bindVals y c
    let t₂ ← lowerTm f b₂ n d
    let e₂ ← dropSpares
    let tail (e : List Stmt) : List Stmt := match d with | .ret _ => [] | _ => e
    return [.ite (← sumLeft sn ls) (s₁ ++ t₁ ++ tail e₁) (s₂ ++ t₂ ++ tail e₂)]
  | .absurd _ => return [.trap]
  | .copy _ x x' b => do
    let (s, ls) ← copyVals (← nodeV x) (← vals x) (tick := true)
    bindVals x' ls
    return s ++ (← lowerTm f b n d)
  | .consume _ x b | .abandon _ x b => do
    let s ← consumeVals (← nodeV x) (← vals x)
    return s ++ (← lowerTm f b n d)


/-! ### Generated functions -/

def fPrintDec : Nat := 0

/-- `n` in unsigned decimal. -/
def printDecFn : Backend.Flat.Fn where
  name := "print_dec"
  params := 1
  results := 0
  locals := 0
  body :=
    let n := Exp.loc 0
    [ .ite (.op (.rel .w64 .ge_u) [n, .c64 10])
        [.call [] fPrintDec [.op (.div .w64 .div_u) [n, .c64 10]]] [],
      .out (add64 (.c64 48) (.op (.div .w64 .rem_u) [n, .c64 10])),
      .ret [] ]

/-- `act c` for each code `c` of the closure in `ls` (class node `n`): a `switch` on its tag; at a
heap class, `imm` when the closure is a word `2t + 1`, else a `switch` on its object's tag. -/
def onCode (n : Nat) (ls : List Nat) (act : Nat → LM (List Stmt)) : LM (List Stmt) := do
  let L ← L
  let u := L.unionOf n
  let f := Exp.loc (ls.headD 0)
  if !L.isRec n then
    let cases ← u.toList.mapM act
    return [.switch f cases [.trap]]
  -- `2t + 1`: the code `t` captures nothing.
  let imm ← u.toList.mapM fun c => if L.envWords c == 0 then act c else pure [.trap]
  let heap ← u.toList.mapM fun c => if L.envWords c == 0 then pure [.trap] else act c
  return [.ite (wrap (and64 f (.c64 1)))
    [.switch (shr64 f (.c64 1)) imm [.trap]] [.switch (.load f 0) heap [.trap]]]

/-- A copy of arm `k` of the sum's words `ls` at `n`, as the sum's words. -/
def copyArm (n k : Nat) (ls : List Nat) : LM (List Stmt × List Exp) := do
  let c ← child n k
  let (s₁, vs) ← payload n (k == 1) ls false
  let (s₂, vs) ← copyVals c vs
  let (s₃, out) ← mkInj n (k == 1) (locs vs)
  pure (s₁ ++ s₂ ++ s₃, out)

def consumeArm (n k : Nat) (ls : List Nat) : LM (List Stmt) := do
  let c ← child n k
  let (s₁, vs) ← payload n (k == 1) ls true
  pure (s₁ ++ (← consumeVals c vs))

def printArm (n k : Nat) (ls : List Nat) : LM (List Stmt) := do
  let c ← child n k
  let (s, vs) ← payload n (k == 1) ls false
  let call := [Stmt.call [] (← helper (.print ((← L).r c))) (locs vs)]
  match (← L).sh c with
  | .sum .. => pure (s ++ outStr "(" ++ call ++ outStr ")")
  | _ => pure (s ++ call)

def copyField (n k : Nat) (ls : List Nat) : LM (List Stmt × List Exp) := do
  let c ← child n k
  let (s₁, vs) ← getField n k ls false
  let (s₂, vs) ← copyVals c vs
  let (s₃, out) ← putField n k (locs vs)
  pure (s₁ ++ s₂ ++ s₃, out)

def consumeField (n k : Nat) (ls : List Nat) : LM (List Stmt) := do
  let c ← child n k
  let (s₁, vs) ← getField n k ls true
  pure (s₁ ++ (← consumeVals c vs))

def printField (n k : Nat) (ls : List Nat) (atom : Bool) : LM (List Stmt) := do
  let c ← child n k
  let (s, vs) ← getField n k ls false
  let call := [Stmt.call [] (← helper (.print ((← L).r c))) (locs vs)]
  match (← L).sh c, atom with
  | .sum .., true => pure (s ++ outStr "(" ++ call ++ outStr ")")
  | _, _ => pure (s ++ call)

/-- The captured values' nodes of code `c`. -/
def envNodes (c : Nat) : LM (List Nat) := return (← L).codeEnv.getD c []

def genHelper (h : Helper) : LM Backend.Flat.Fn := do
  let L ← L
  match h with
  | .copy n =>
    let w := L.w n
    let (body, nloc, ptrs) ← inFn w do
      let ps := List.range w
      vote n ps
      match L.sh n with
      | .clos .. =>
        if L.isRec n then
          onCode n ps fun c => do
            let ew := L.envWords c
            if ew == 0 then return [.ret [.loc 0]]
            let (s, vs) ← loadAt (.loc 0) 1 ew
            let mut out : List Stmt := s
            let mut ws : List Exp := []
            let mut off := 0
            for e in ← envNodes c do
              let (s₁, ls) ← copyVals e (vs.drop off |>.take (L.w e))
              out := out ++ s₁; ws := ws ++ locs ls; off := off + L.w e
            let (s₂, vs₂) ← closVals n c ws
            return out ++ s₂ ++ [.ret vs₂]
        else
          onCode n ps fun c => do
            let mut out : List Stmt := []
            let mut ws : List Exp := []
            let mut off := 1
            for e in ← envNodes c do
              let (s₁, ls) ← copyVals e (List.range' off (L.w e))
              out := out ++ s₁; ws := ws ++ locs ls; off := off + L.w e
            return out ++ [.ret ([.loc 0] ++ ws ++ zeros (w - 1 - ws.length))]
      | .pair .. => do
        let (s₁, a) ← copyField n 0 (← fieldLocals n 0 ps)
        let (s₂, b) ← copyField n 1 (← fieldLocals n 1 ps)
        pure (s₁ ++ s₂ ++ [.ret (a ++ b)])
      | .sum .. => do
        let (s₁, a) ← copyArm n 0 ps
        let (s₂, b) ← copyArm n 1 ps
        pure [.ite (← sumLeft n ps) (s₁ ++ [.ret a]) (s₂ ++ [.ret b])]
      | _ => pure [.ret (locs ps)]
    pure { name := "copy", params := w, results := w, locals := nloc, body := body ++ [.trap], ptrs }
  | .consume n =>
    let w := L.w n
    let (body, nloc, ptrs) ← inFn w do
      let ps := List.range w
      vote n ps
      match L.sh n with
      | .clos .. =>
        let s ← onCode n ps fun c => do
          let mut out : List Stmt := []
          if L.isRec n then
            let ew := L.envWords c
            if ew == 0 then return []
            let (s, vs) ← loadAt (.loc 0) 1 ew
            out := s
            let mut off := 0
            for e in ← envNodes c do
              out := out ++ (← consumeVals e (vs.drop off |>.take (L.w e))); off := off + L.w e
            return out ++ [.free (.loc 0)]
          let mut off := 1
          for e in ← envNodes c do
            out := out ++ (← consumeVals e (List.range' off (L.w e))); off := off + L.w e
          return out
        pure (s ++ [.ret []])
      | .pair .. => pure ((← consumeField n 0 (← fieldLocals n 0 ps)) ++
          (← consumeField n 1 (← fieldLocals n 1 ps)) ++ [.ret []])
      | .sum .. => pure [.ite (← sumLeft n ps) (← consumeArm n 0 ps) (← consumeArm n 1 ps), .ret []]
      | _ => pure [.ret []]
    pure { name := "consume", params := w, results := 0, locals := nloc, body, ptrs }
  | .print n =>
    let w := L.w n
    let (body, nloc, ptrs) ← inFn w do
      let ps := List.range w
      vote n ps
      match L.sh n with
      | .unit | .zero => pure (outStr "()")
      | .int .w32 => pure (outStr "i32[" ++ [.call [] fPrintDec [.loc 0]] ++ outStr "]")
      | .int .w64 => pure (outStr "i64[" ++ [.call [] fPrintDec [.loc 0]] ++ outStr "]")
      | .int .w8 => pure (outStr "u8[" ++ [.call [] fPrintDec [.loc 0]] ++ outStr "]")
      | .int .f32 => pure (outStr "f32[" ++ [.call [] fPrintDec [.loc 0]] ++ outStr "]")
      | .int .f64 => pure (outStr "f64[" ++ [.call [] fPrintDec [.loc 0]] ++ outStr "]")
      | .int .u32 => pure (outStr "u32[" ++ [.call [] fPrintDec [.loc 0]] ++ outStr "]")
      | .int .u64 => pure (outStr "u64[" ++ [.call [] fPrintDec [.loc 0]] ++ outStr "]")
      | .clos .. | .unk => pure (outStr "<fun>")
      | .ref _ | .imm _ | .mut _ | .opq => pure (outStr "<loc>")
      | .fam _ => pure (outStr "(<loc>, i32[" ++ [.call [] fPrintDec [.loc 1]] ++ outStr "])")
      | .pair .. => pure (outStr "(" ++ (← printField n 0 (← fieldLocals n 0 ps) false) ++ outStr ", " ++
          (← printField n 1 (← fieldLocals n 1 ps) false) ++ outStr ")")
      | .sum .. => pure [.ite (← sumLeft n ps) (outStr "inl " ++ (← printArm n 0 ps))
          (outStr "inr " ++ (← printArm n 1 ps))]
    pure { name := "print", params := w, results := 0, locals := nloc, body := body ++ [.ret []], ptrs }
  | .reCopy c n =>
    -- The contents at `c` read through `Imm̲` at `n`: a closure or an opaque value is `Unk` (no
    -- words), a pointer the word, a boxed field copied, as `copy` copies.
    let wc := L.w c
    let wn := L.w n
    let (body, nloc, ptrs) ← inFn wc do
      vote c (List.range wc)
      let (s, vs) ← reVals 64 c n (List.range wc)
      pure (s ++ [.ret vs])
    pure { name := "reborrow", params := wc, results := wn, locals := nloc, body := body ++ [.trap], ptrs }
  | .stackPush =>
    -- (register, words) → the frame's address. A stack is its header (bump, end, chunk) and its
    -- first chunk; a chunk is its header (the previous chunk, its bump and end) and its words. A
    -- chunk that cannot hold the frame is followed by a new one.
    let (r, w, h, b, c, sz) := (0, 1, 2, 3, 4, 5)
    let st (a : Exp) (o : Nat) (v : Exp) : Stmt := .store a o v
    let mk : List Stmt :=
      [.set h (.alloc (.c64 (6 + stackChunk0).toUInt64)),
       st (.loc h) 0 (add64 (.loc h) (.c64 48)),
       st (.loc h) 1 (add64 (.loc h) (.c64 (48 + 8 * stackChunk0).toUInt64)),
       st (.loc h) 2 (add64 (.loc h) (.c64 24)),
       st (.loc h) 3 (.c64 0), st (.loc h) 4 (.c64 0), st (.loc h) 5 (.c64 0),
       st (.loc r) 0 (.loc h)]
    let grow : List Stmt :=
      [.ite (ltu64 (.loc w) (.c64 stackChunk.toUInt64)) [.set sz (.c64 stackChunk.toUInt64)] [.set sz (.loc w)],
       .set c (.alloc (add64 (.loc sz) (.c64 3))),
       st (.loc c) 0 (.load (.loc h) 2), st (.loc c) 1 (.loc b), st (.loc c) 2 (.load (.loc h) 1),
       st (.loc h) 2 (.loc c), .set b (add64 (.loc c) (.c64 24)),
       st (.loc h) 1 (add64 (.loc b) (mul64 (.loc sz) (.c64 8)))]
    let body : List Stmt :=
      [.set h (.load (.loc r) 0), .ite (eqz64 (.loc h)) mk [],
       .set b (.load (.loc h) 0),
       .ite (ltu64 (.load (.loc h) 1) (add64 (.loc b) (mul64 (.loc w) (.c64 8)))) grow [],
       st (.loc h) 0 (add64 (.loc b) (mul64 (.loc w) (.c64 8))),
       .ret [.loc b]]
    pure { name := "stack push", params := 2, results := 1, locals := 4, body }
  | .stackPop =>
    -- (register, frame): the frame popped; a chunk left empty, after the first, is freed.
    let (r, f, h, c) := (0, 1, 2, 3)
    let body : List Stmt :=
      [.set h (.load (.loc r) 0), .set c (.load (.loc h) 2),
       .ite (and32 (eq64 (.loc f) (add64 (.loc c) (.c64 24))) (.op (.rel .w64 .ne) [.load (.loc c) 0, .c64 0]))
         [.store (.loc h) 0 (.load (.loc c) 1), .store (.loc h) 1 (.load (.loc c) 2),
          .store (.loc h) 2 (.load (.loc c) 0), .free (.loc c)]
         [.store (.loc h) 0 (.loc f)],
       .ret []]
    pure { name := "stack pop", params := 2, results := 0, locals := 2, body }
  | .apply cls j =>
    let some rn := ((match L.sh cls with | .clos _ _ r => r | _ => [])[j]?) | throw "word IR: an apply's class"
    let (k, param, _) ← classOf cls
    let pw ← match k, param with
      | .lam, some p => pure (L.w p)
      | _, _ => pure 0
    let cw := L.w cls
    let rw := L.w rn
    let (body, nloc, ptrs) ← inFn (cw + pw) do
      let ps := List.range cw
      vote cls ps
      if let some p := param then vote p (List.range' cw pw)
      let arg := locs (List.range' cw pw)
      onCode cls ps fun c => do
        let (s, env) ← envOf cls c ps
        return s ++ [.tailCall (← codeFn c j) (env ++ arg)]
    pure { name := "apply", params := cw + pw, results := rw, locals := nloc, body := body ++ [.trap], ptrs }
where
  /-- The reading of `c`'s words `ls` at `n`, each field by its own reading's function. -/
  reVals (_fuel : Nat) (c n : Nat) (ls : List Nat) : LM (List Stmt × List Exp) := do
    let L ← L
    if L.r c == L.r n then
      let (s, ts) ← copyVals c ls
      return (s, locs ts)
    let sub (c' n' : Nat) (vs : List Nat) : LM (List Stmt × List Exp) := do
      if L.r c' == L.r n' then
        let (s, ts) ← copyVals c' vs
        return (s, locs ts)
      match L.sh c', L.sh n' with
      | .clos .., .unk => return ([], [])
      | .opq, .unk => return ([], [])
      -- `Tok`'s cell (`Ref 1`) read as `Unk`: discarded.
      | .ref _, .unk => return ([], [])
      | _, _ =>
        if L.triv c' && sameEnc L 256 c' n' then return ([], locs vs)
        let ts ← fresh (L.w n')
        return ([.call ts (← helper (.reCopy (L.r c') (L.r n'))) (locs vs)], locs ts)
    match L.sh c, L.sh n with
    | .clos .., .unk => return ([], [])
    | .opq, .unk => return ([], [])
    | .ref _, .unk => return ([], [])
    | .pair .., .pair .. => do
      let (s₀, a, b) ← splitPair c ls false
      let (s₁, va) ← sub (← child c 0) (← child n 0) a
      let (s₂, vb) ← sub (← child c 1) (← child n 1) b
      let (s₃, vs) ← mkPair n va vb
      return (s₀ ++ s₁ ++ s₂ ++ s₃, vs)
    | .sum .., .sum .. => do
      let (sa, a) ← payload c false ls false
      let (sb, b) ← payload c true ls false
      let (s₁, va) ← sub (← child c 0) (← child n 0) a
      let (s₂, vb) ← sub (← child c 1) (← child n 1) b
      let (s₃, vl) ← mkInj n false va
      let (s₄, vr) ← mkInj n true vb
      let ts ← fresh (L.w n)
      let sets (vs : List Exp) : List Stmt := (ts.zip vs).map fun (t, e) => .set t e
      return ([.ite (← sumLeft c ls) (sa ++ s₁ ++ s₃ ++ sets vl) (sb ++ s₂ ++ s₄ ++ sets vr)],
        locs ts)
    | _, _ =>
      let (s, ts) ← copyVals c ls
      return (s, locs ts)


/-! ### Functions and the program -/

/-- The step from "the lend is live" to "the lend is live for the whole of this function", which
every borrow fact cites (SPEC §50): the parameter's lend bit (`Fn.lendEncl`), set only at a source
function, under the named assumption `LendEnclosesFn`. -/
def citeEncl : String :=
  "the lend encloses this function and its owner is not a parameter " ++
  "(a source function's lend bit, `Fn.lendEncl`: `LendEnclosesFn`, `bcc trusted`)"

/-- Why a live borrow's cell is live and as wide as `dereferenceable` says (SPEC §50): no run is
stuck, by the safety theorem the program's form reaches (`adequacyD`; `adequacyD_pin` under
`PinLaw` at a relaxed lend, as `bcc trusted`'s typing line says; `externs_every_run` or
`io_every_run` with externs), and the
cell was allocated at its width class's widest bytes (`WidthClass`, `bcc trusted`). -/
def citeLive : String :=
  "a live borrow points at a live cell (no run stuck: `adequacyD`, or `adequacyD_pin` under " ++
  "`PinLaw`, as `bcc trusted`'s typing line reports, or `externs_every_run`/`io_every_run` " ++
  "with externs; SPEC §13) of its class's widest " ++
  "bytes (`WidthClass`, `bcc trusted`); "

/-- The cited guarantee of a `mut` borrow's facts (SPEC §50). -/
def citeMut : String :=
  "a `mut` lend is unique (`●` is defined where `▶◀` holds, `CellU.CompS.compat`, and `▶◀` " ++
  "relates `imm` cells only, `CellU.CompatS.kinds`); " ++
  citeLive ++ citeEncl

/-- The cited guarantee of an `imm` borrow's facts (SPEC §50). -/
def citeImm : String :=
  "an `imm` lend is not written while live (`▶◀` relates `imm` cells at one value: " ++
  "`CellU.CompatS`; the LIR's writes take a `mut` borrow or the owner); " ++
  citeLive ++ citeEncl

/-- The cited guarantee of a borrowed family's base (SPEC §50): its leaves' mode; the base may be
`0` (an empty family) or in the program's data, so it is neither `nonnull` nor `dereferenceable`. -/
def citeFam (imm : Bool) : String :=
  s!"the leaves of a borrowed family are {if imm then "`imm`" else "`mut`"} borrows: " ++
    (if imm then citeImm else citeMut)

/-- **The facts of a function's parameters** (SPEC §50), read off each parameter's type (its
`LTy`, the checked type; a layout node may be shared by an owner and its borrows, so its shape
does not give the mode): a word that is an `imm` or `mut` borrow of a cell with words is
`noalias`, `nonnull` and `dereferenceable` by the cell's bytes, and `readonly` at `imm`; a
borrowed family's base is `noalias`, and `readonly` at `imm` leaves. A pair's fields are its words
in order (a boxed field one pointer, given none); a sum's words depend on its arm and are given
none. A `!` is read through (`LTy.unbang`): `!A` is represented as `A`.

The kernel's facts hold while the lend is live; LLVM's attributes speak of the whole of the
function's execution. So a parameter gets facts only when its lend bit is set (`Fn.lendEncl`): the
lend encloses the function and its owner is not a parameter. A function the conversion makes has no
bit set, and none of its parameters gets a fact. -/
def paramFacts (fd : Backend2.Fn) : LM (List Backend.Flat.ParamFacts) := do
  let L ← L
  let cellBytes (n : Nat) : Option Nat :=
    match L.sh n with
    | .ref c | .imm c | .mut c => let b := L.repB c; if b == 0 then none else some b
    | _ => none
  let rec walk (fuel off n : Nat) (t : LTy) : List Backend.Flat.ParamFacts :=
    match fuel with
    | 0 => []
    | f + 1 =>
    match t, L.sh n with
    | .mut _, .mut _ | .mut _, .imm _ | .mut _, .ref _ => match cellBytes n with
      | some b => [⟨off, [.noalias, .nonnull, .deref b], citeMut⟩]
      | none => []
    | .imm _, .mut _ | .imm _, .imm _ | .imm _, .ref _ => match cellBytes n with
      | some b => [⟨off, [.noalias, .readonly, .nonnull, .deref b], citeImm⟩]
      | none => []
    | .fam (.imm _), .fam _ => [⟨off, [.noalias, .readonly], citeFam true⟩]
    | .fam (.mut _), .fam _ => [⟨off, [.noalias], citeFam false⟩]
    | .pair ta tb, .pair a b =>
      (if L.isBoxed n 0 then [] else walk f off a ta) ++
        (if L.isBoxed n 1 then [] else walk f (off + L.fieldW n 0) b tb)
    | _, _ => []
  let mut out : List Backend.Flat.ParamFacts := []
  let mut off := 0
  for (x, i) in fd.params.zipIdx do
    let n := L.node x
    if fd.lendEncl[i]? == some true then
      if let some t := (← read).p.ty[x]? then out := out ++ walk 64 off n t.unbang
    off := off + L.w n
  return out

def lowerFn (i : Nat) (fd : Backend2.Fn) : LM Backend.Flat.Fn := do
  let L ← L
  let some rn := L.fnRet[i]? | throw s!"word IR: no node of f{i}'s answer"
  let pws := fd.params.map fun x => L.w (L.node x)
  let total := pws.foldl (· + ·) 0
  let k := L.w rn
  let (body, nloc, frame, ptrs) ← inFnF total do
    let mut off := 0
    for (x, w) in fd.params.zip pws do
      bindVals x (List.range' off w)
      off := off + w
    pure ((← lowerTm (1 <<< 22) fd.body rn (.ret k)) ++ [.trap])
  pure { name := fd.name, params := total, results := k, locals := nloc, frame, body, ptrs,
         facts := ← paramFacts fd, inline := fd.inline }

def countsReport : List Stmt :=
  outStr "allocs " ++ [.call [] fPrintDec [.stat 0]] ++ outStr "\nindirect " ++
    [.call [] fPrintDec [.stat 1]] ++ outStr "\ncopies " ++
    [.call [] fPrintDec [.stat 2]] ++ outStr "\n"

/-- Run `main`, print its value, consume it, print the live count, and with `counts` the run's
counts. -/
def entryFn (fMain : Nat) (exits : Bool) : LM Backend.Flat.Fn := do
  let L ← L
  let n := L.mainNode
  let (body, nloc, ptrs) ← inFn 0 do
    let m ← fresh (L.w n)
    vote n m
    -- With `exits` (SPEC §39), `main`'s value is `inl v`, whose `v` is printed, or `inr ()`, which
    -- prints nothing and ends the run with the exit status `1`.
    let (pr, status) ← if exits then do
        let .sum a _ := L.sh n | throw "word IR: `main`'s value is not `inl v` or `inr ()`"
        let (s, vs) ← payload n false m false
        let left ← sumLeft n m
        pure ([Stmt.ite left (s ++ [.call [] (← helper (.print (L.r a))) (locs vs)] ++ outStr "\n") []],
          [Stmt.ite left [] [.status (.c64 1)]])
      else pure ([Stmt.call [] (← helper (.print (L.r n))) (locs m)] ++ outStr "\n", [])
    let dr ← consumeVals n m
    pure ([Stmt.call m fMain []] ++ pr ++ dr ++ outStr "live " ++ [.call [] fPrintDec [.live]] ++
      outStr "\n" ++ (if (← read).counts then countsReport else []) ++ status ++ [.ret []])
  pure { name := "entry", params := 0, results := 0, locals := nloc, body, ptrs }

/-! ### The `willreturn` class  `[spec §50]` -/

/-- The cited reason a function of the class returns to its caller (SPEC §50). -/
def citeWillreturn : String :=
  "the body is at the empty row (`Fn.emptyRow`, from the checked type): at related arguments it " ++
  "returns under every allocator (`total_open`; `total_open_pin` under `PinLaw`; SPEC §14); " ++
  "a reached call is at related arguments (`total_subrun` at a closed program's plain context; " ++
  "`CallRelated`, `bcc trusted`, otherwise), and the word IR is the LIR's lowering " ++
  "(the faithfulness every native fact rests on); it calls no runtime function but `bc_free` " ++
  "(no allocation, which aborts when `malloc` fails; no I/O, which may block) and only " ++
  "functions of the class; the stack does not overflow (`HostStack`, `bcc trusted`)"

mutual
/-- An expression calls a runtime function: an allocation (`bc_alloc`, which aborts when `malloc`
fails), a read (`bc_getc`, `bc_getv`, which may block) or the clock (`bc_now`). -/
def expRt : Exp → Bool
  | .alloc _ | .getc _ | .getv _ _ _ | .now _ => true
  | .load a _ | .load8 a | .load32 a => expRt a
  | .op _ as => expsRt as
  | .gep a b => expRt a || expRt b
  | _ => false
def expsRt : List Exp → Bool
  | [] => false
  | e :: es => expRt e || expsRt es
end

mutual
/-- A statement stays in the class `C`: it calls no runtime function but `bc_free` (no write,
which may block, no sleep, no exit status) and calls only functions of `C`. -/
def stmtIn (C : Std.HashSet Nat) : Stmt → Bool
  | .set _ e | .free e | .unslot e => !expRt e
  | .store a _ v | .store8 a v | .store32 a v => !expRt a && !expRt v
  | .out _ | .putc _ _ | .putv _ _ _ | .sleep _ _ | .status _ => false
  | .ite c t e => !expRt c && blockIn C t && blockIn C e
  | .switch e cs d => !expRt e && casesIn C cs && blockIn C d
  | .call _ f as | .tailCall f as => C.contains f && !expsRt as
  | .ret es => !expsRt es
  | .tick | .tickCopy | .tickBound | .trap => true
def blockIn (C : Std.HashSet Nat) : List Stmt → Bool
  | [] => true
  | s :: ss => stmtIn C s && blockIn C ss
def casesIn (C : Std.HashSet Nat) : List (List Stmt) → Bool
  | [] => true
  | c :: cs => blockIn C c && casesIn C cs
end

/-- **The `willreturn` class** (SPEC §50): the word IR's functions that are an LIR function whose
body is at the empty row (`Fn.emptyRow`, set from the checked type where the conversion makes the
function; every function the conversion makes for itself leaves it cleared), less every one that
calls a runtime function but `bc_free` or a function outside the class: the greatest such set,
by removing violators until none is left. The word IR's `i + 1` is the LIR's `i` (`printDec` is
the first). -/
def willreturnClass (p : Prog) (fns : Array Backend.Flat.Fn) : Std.HashSet Nat := Id.run do
  let mut C : Std.HashSet Nat := {}
  for (d, i) in p.fns.toList.zipIdx do
    if d.emptyRow then C := C.insert (i + 1)
  for _ in [0:fns.size + 1] do
    let bad := C.toList.filter fun j =>
      !((fns[j]?).map (blockIn C ·.body)).getD false
    if bad.isEmpty then break
    C := bad.foldl (·.erase ·) C
  return C

/-- The word IR of a program at its layouts; with `counts`, the counting build. -/
def lowerProg (p : Prog) (L : Layouts) (known : Std.HashMap Var Nat)
    (codes : Std.HashMap Var (Std.HashSet Nat)) (counts : Bool) : Except String Backend.Flat.Prog := do
  let nf := p.fns.size
  let fMain := 1 + nf
  let pad := (8 - p.data.size % 8) % 8
  -- The static cells after the literals: each as wide as its width class (`Layouts.staticBytes`),
  -- a word at least.
  let words := L.staticBytes.map fun b => max 1 ((b + 7) / 8)
  let staticAt := (words.foldl (fun (acc : Array Nat × Nat) w => (acc.1.push acc.2, acc.2 + 8 * w))
    (#[], p.data.size + pad)).1
  let slotScopes := p.slots.fold (fun s _ sc => s.insert sc) {}
  let ctx : LCtx := { L, p, helperBase := fMain + 2, counts, staticAt, known, codes, slotScopes }
  let act : LM (List Backend.Flat.Fn) := do
    let fns ← p.fns.toList.zipIdx.mapM fun (fd, i) => lowerFn i fd
    let k := L.w L.mainNode
    let (body, nloc, frame, ptrs) ← inFnF 0 do
      pure ((← lowerTm (1 <<< 22) p.main L.mainNode (.ret k)) ++ [.trap])
    let main : Backend.Flat.Fn := { name := "main", params := 0, results := k, locals := nloc, frame, body, ptrs }
    let entry ← entryFn fMain p.exits
    let mut gen : Array Backend.Flat.Fn := #[]
    let mut i := 0
    for _ in [0:100000] do
      let q := (← get).queue
      if h : i < q.size then
        gen := gen.push (← genHelper q[i])
        i := i + 1
      else break
    pure ([printDecFn] ++ fns ++ [main, entry] ++ gen.toList)
  let (fns, _) ← (act.run ctx).run {}
  let fns := fns.toArray
  let C := willreturnClass p fns
  let fns := fns.mapIdx fun j f => if C.contains j then { f with willreturn := some citeWillreturn } else f
  let data := p.data ++ Array.replicate (pad + 8 * words.foldl (· + ·) 0) 0
  pure { fns, entry := fMain + 1, data }

end Backend2.Low

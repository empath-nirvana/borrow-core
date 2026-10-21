import Std.Data.HashMap
import Backend.Flat.Syntax
import Backend.Flat.Host
import Backend2.Layout

/-!
# Backend2 — the LIR to the word IR  `[spec §35, §37]`

Each LIR variable is the words of its layout node (`Backend2/Layout.lean`), held in locals; each
LIR function a word-IR function of its parameters' words, answering its result's words. The
word IR (`Backend/Flat/Syntax.lean`) is target-neutral: the Wasm and LLVM emitters take it.

- **Pairs** are their fields' words; a **sum** a tag word and its payload's, padded. A field the
  layout boxes is a pointer to an object holding its words: built by allocating it, taken apart
  by loading and freeing it.
- **Closures** are defunctionalized: a closure is its code's tag in its class, then its captured
  values' words, padded to the class's widest. A call of a closure whose class has one code is a
  direct call of that code's function; any other is a call of the class's dispatcher, a `switch`
  on the tag. A class that holds itself keeps its environment on the heap: the word `2t + 1`, or
  an object holding the tag and the captured words.
- **Copies and drops** are the LIR's, at their layouts: a copy at a type with boxed fields or a
  heap closure is a generated deep copy, counted under `copies` in the counting build; a drop
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
  | drop (n : Nat)
  | print (n : Nat)
  /-- A read through `Imm̲`: the contents at node `c` copied to the reading's node `d`. -/
  | reCopy (c d : Nat)
  /-- The dispatcher of a closure class, at its component `j`. -/
  | apply (cls j : Nat)
  deriving BEq, Hashable, Inhabited

structure LCtx where
  L : Layouts
  p : Prog
  helperBase : Nat
  counts : Bool
  /-- The offset in the data of the capabilities' static words. -/
  staticBase : Nat
  /-- The code of each call's function variable, where the closure flow finds one. -/
  known : Std.HashMap Var Nat := {}
  /-- The lent cells placed in frame slots (`Backend2/Frames.lean`). -/
  framed : Std.HashSet Var := {}

structure LState where
  locals : Std.HashMap Var (List Nat) := {}
  next : Nat := 0
  /-- The words of the function's frame so far. -/
  frame : Nat := 0
  /-- The locals holding a frame slot's address. -/
  slots : Std.HashSet Nat := {}
  helpers : Std.HashMap Helper Nat := {}
  queue : Array Helper := #[]

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

def vals (x : Var) : LM (List Nat) := do
  match (← get).locals[x]? with
  | some ls => pure ls
  | none => throw s!"word IR: variable x{x} has no locals"

def bindVals (x : Var) (ls : List Nat) : LM Unit :=
  modify fun s => { s with locals := s.locals.insert x ls }

def helper (h : Helper) : LM Nat := do
  match (← get).helpers[h]? with
  | some i => pure i
  | none =>
    let base := (← read).helperBase
    modifyGet fun s => (base + s.queue.size,
      { s with helpers := s.helpers.insert h (base + s.queue.size), queue := s.queue.push h })

/-- Run `act` as the body of a function of `params` words: the locals beyond them. -/
def inFnF (params : Nat) (act : LM α) : LM (α × Nat × Nat) := do
  let saved ← get
  set { saved with locals := {}, next := params, frame := 0, slots := {} }
  let a ← act
  let n := (← get).next
  let fw := (← get).frame
  modify fun s => { s with locals := saved.locals, next := saved.next, frame := saved.frame,
                           slots := saved.slots }
  pure (a, n - params, fw)

def inFn (params : Nat) (act : LM α) : LM (α × Nat) := do
  let (a, n, _) ← inFnF params act
  pure (a, n)

/-- Where a term's words go: locals, returned (padded to `k` words), or bound to a variable. -/
inductive Dest where
  | to (ls : List Nat)
  | ret (k : Nat)
  | bind (x : Var)

def emit : Dest → List Exp → LM (List Stmt)
  | .to ls, vs => do
    if ls.length != vs.length then throw s!"word IR: {vs.length} words for {ls.length} locals"
    -- A frame slot's address moved to another local is a slot's address there too.
    for (l, e) in ls.zip vs do
      if let .loc l' := e then
        if (← get).slots.contains l' then modify fun s => { s with slots := s.slots.insert l }
    pure (ls.zip vs |>.map fun (l, e) => .set l e)
  | .ret k, vs => do
    if vs.length > k then throw s!"word IR: {vs.length} words returned for {k}"
    pure [.ret (vs ++ zeros (k - vs.length))]
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

/-- Field `k` of `n` built from its words: behind a pointer when it is boxed. -/
def putField (n k : Nat) (vs : List Exp) : LM (List Stmt × List Exp) := do
  if !(← L).isBoxed n k then return ([], vs)
  let t ← fresh1
  return ([.set t (.alloc (.c64 (max 1 vs.length).toUInt64))] ++ storeAt (.loc t) 0 vs, [.loc t])

/-- The words of field `k` of `n` from the field's locals: loaded from behind a pointer when boxed,
the object freed when `consume`. -/
def getField (n k : Nat) (ls : List Nat) (consume : Bool) : LM (List Stmt × List Nat) := do
  if !(← L).isBoxed n k then return ([], ls)
  let c ← child n k
  let p := Exp.loc (ls.headD 0)
  let (s, vs) ← loadAt p 0 (← wordsN c)
  return (s ++ (if consume then [.free p] else []), vs)

/-- The locals of field `k` of a pair's or a sum's locals. -/
def fieldLocals (n k : Nat) (ls : List Nat) : LM (List Nat) := do
  let L ← L
  match L.sh n with
  | .pair .. =>
    let w₀ := L.fieldW n 0
    pure (if k == 0 then ls.take w₀ else (ls.drop w₀).take (L.fieldW n 1))
  | _ => pure ((ls.drop 1).take (L.fieldW n k))

def mkPair (n : Nat) (a b : List Exp) : LM (List Stmt × List Exp) := do
  let (s₁, v₁) ← putField n 0 a
  let (s₂, v₂) ← putField n 1 b
  pure (s₁ ++ s₂, v₁ ++ v₂)

def mkInj (n : Nat) (r : Bool) (a : List Exp) : LM (List Stmt × List Exp) := do
  let (s, v) ← putField n (if r then 1 else 0) a
  let pw := (← wordsN n) - 1
  pure (s, [.c64 (if r then 1 else 0)] ++ v ++ zeros (pw - v.length))

def splitPair (n : Nat) (ls : List Nat) (consume : Bool) : LM (List Stmt × List Nat × List Nat) := do
  let (s₁, a) ← getField n 0 (← fieldLocals n 0 ls) consume
  let (s₂, b) ← getField n 1 (← fieldLocals n 1 ls) consume
  pure (s₁ ++ s₂, a, b)

def payload (n : Nat) (r : Bool) (ls : List Nat) (consume : Bool) : LM (List Stmt × List Nat) := do
  let k := if r then 1 else 0
  getField n k (← fieldLocals n k ls) consume

/-! ### Cells -/

/-- The bytes between two slots of the cell at pointer node `n`. -/
def slotStride (n : Nat) : LM Nat := do
  let L ← L
  match L.slotBytes[L.r n]? with
  | some b => pure b
  | none => pure (8 * L.cellWords.getD (L.r n) 1)

/-- The cell at pointer node `n` takes no words. -/
def zeroCell (n : Nat) : LM Bool := do
  let L ← L
  return L.cellWords.getD (L.r n) 1 == 0 && !(L.slotBytes.contains (L.r n))

/-- The contents of the cell at `a`, of pointer node `n`, in `k` fresh locals. -/
def loadCell (n : Nat) (a : Exp) (k : Nat) : LM (List Stmt × List Nat) := do
  let L ← L
  match L.slotBytes[L.r n]? with
  | some 1 => do let t ← fresh1; return ([.set t (.load8 a)], [t])
  | some 4 => do let t ← fresh1; return ([.set t (.load32 a)], [t])
  | _ => loadAt a 0 k

def storeCell (n : Nat) (a : Exp) (vs : List Exp) : LM (List Stmt) := do
  let L ← L
  match L.slotBytes[L.r n]? with
  | some 1 => return [.store8 a (vs.headD (.c64 0))]
  | some 4 => return [.store32 a (vs.headD (.c64 0))]
  | _ => return storeAt a 0 vs

/-- The contents' node of a pointer node. -/
def contents (n : Nat) : LM Nat := do
  match (← L).sh n with
  | .ref c | .imm c | .mut c => pure c
  | s => throw s!"word IR: not a pointer: {reprStr s |>.take 40}"

/-- The leaf node of a family node. -/
def leafOf (n : Nat) : LM Nat := do
  match (← L).sh n with
  | .fam l => pure l
  | s => throw s!"word IR: not a family: {reprStr s |>.take 40}"

/-! ### Copies and drops -/

/-- A copy of the words `ls` at node `n`; with `tick`, counted in the counting build (a copy the
LIR makes; a copy inside a generated copy is part of it). -/
def copyVals (n : Nat) (ls : List Nat) (tick : Bool := false) : LM (List Stmt × List Nat) := do
  if (← L).triv n then return ([], ls)
  let ts ← fresh (← wordsN n)
  let tick := if (← read).counts && tick then [Stmt.tickCopy] else []
  return (tick ++ [.call ts (← helper (.copy ((← L).r n))) (locs ls)], ts)

def dropVals (n : Nat) (ls : List Nat) : LM (List Stmt) := do
  if (← L).triv n then return []
  return [.call [] (← helper (.drop ((← L).r n))) (locs ls)]


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

/-- A host operation on its operand's words (§8, §37): its answer's words. -/
def hostVals (o : HostOp) (ls : List Nat) : LM (List Stmt × List Exp) := do
  match o with
  | .wrap8 => return ([], [and64 (.loc (ls.headD 0)) (.c64 0xff)])
  | .extend8_u | .reinterpret_i _ | .reinterpret_f _ => return ([], [.loc (ls.headD 0)])
  | _ => pure ()
  let rawAt (w : Width) (e : Exp) : Exp := match w with
    | .w32 | .w8 | .f32 => wrap e
    | .w64 | .f64 => e
  let args := ls.map fun l => rawAt (hostArgWidth o) (.loc l)
  let word (w : Width) (e : Exp) : Exp := match w with
    | .w32 | .w8 | .f32 => extendU e
    | .w64 | .f64 => e
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
          | .w32 | .w8 | .f32 => Exp.c32 0x80000000 | .w64 | .f64 => .c64 0x8000000000000000
        let m1 := match w' with
          | .w32 | .w8 | .f32 => Exp.c32 0xFFFFFFFF | .w64 | .f64 => .c64 0xFFFFFFFFFFFFFFFF
        or32 zero (and32 (.op (.rel w' .eq) [a, intMin]) (.op (.rel w' .eq) [b, m1]))
      | _ => zero
    pure ([.ite trapC [.set t₀ (.c64 1), .set t₁ (.c64 0)] [.set t₀ (.c64 0), .set t₁ (word w (.op o args))]],
      [.loc t₀, .loc t₁])
  | .trapping w, .trunc i f sx =>
    let t₀ ← fresh1
    let t₁ ← fresh1
    let x := args.headD (.c64 0)
    let (loOp, lo, hi) := truncRange i f sx
    let ok := and32 (.op (.frel f loOp) [x, lo]) (.op (.frel f .lt) [x, hi])
    pure ([.ite ok [.set t₀ (.c64 0), .set t₁ (word w (.op (.trunc_sat i f sx) [x]))]
            [.set t₀ (.c64 1), .set t₁ (.c64 0)]], [.loc t₀, .loc t₁])
  | .trapping _, _ => throw "word IR: an operation with no answer somewhere that is neither a division nor a trunc"

/-- A division whose divisor is a literal at which it cannot fail (`TExpr.divLit`): the operation
alone, with no test (SPEC §39). A byte's division is the `i32` one, narrowed. -/
def divLitVals (o : HostOp) (byte : Bool) (ls : List Nat) : LM (List Exp) := do
  let (w, _) ← match o with
    | .div w d => pure (w, d)
    | _ => throw "word IR: divLit of a non-division"
  let args := ls.map fun l => match w with
    | .w32 | .w8 | .f32 => wrap (.loc l)
    | .w64 | .f64 => Exp.loc l
  let q : Exp := match w with
    | .w32 | .w8 | .f32 => extendU (.op o args)
    | .w64 | .f64 => .op o args
  return [if byte then and64 q (.c64 0xff) else q]


/-- Call `f` on `args`, answering `k` words, to `d`. -/
def lowerCall (pre : List Stmt) (f : Nat) (args : List Exp) (k : Nat) (d : Dest) : LM (List Stmt) := do
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
  | .host o => do
    let (s, vs) ← hostVals o (← arg 0)
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
  | .clampLen => do
    let c ← one (args.getD 0 0)
    let t ← fresh1
    return [.ite (ltu32 c (.c64 0x80000000)) [.set t c] [.set t (.c64 0)]] ++ (← emit d [.loc t])
  | .alloc | .allocLent => do
    if ← zeroCell n then return ← emit d [.c64 0]
    let t ← fresh1
    let w := max 1 ((← L).cellWords.getD ((← L).r n) 1)
    let fr := (← read).framed
    let inFrame := match op, d with
      | .allocLent, .bind x => fr.contains x
      | _, _ => false
    let addr ← if inFrame then do
        let off := (← get).frame
        modify fun s => { s with frame := off + w, slots := s.slots.insert t }
        pure (Exp.slot off w)
      else pure (.alloc (.c64 w.toUInt64))
    return [.set t addr] ++ (← storeCell n (.loc t) (locs (← arg 0))) ++ (← emit d [.loc t])
  | .staticCell k => do
    let a := Exp.data ((← read).staticBase + 8 * k)
    return (← storeCell n a (locs (← arg 0))) ++ (← emit d [a])
  | .free => do
    let pn ← argN 0
    if ← zeroCell pn then return ← emit d []
    let al := (← arg 0).headD 0
    let a := Exp.loc al
    let (s, vs) ← loadCell pn a (← wordsN (← contents pn))
    let rel := if (← get).slots.contains al then Stmt.unslot a else .free a
    return s ++ [rel] ++ (← emit d (locs vs))
  | .swap => do
    let pn ← argN 0
    let m := (← arg 0).headD 0
    if ← zeroCell pn then return ← emit d ([.loc m] ++ zeros (← wordsN (← contents pn)))
    let (s, old) ← loadCell pn (.loc m) (← wordsN (← contents pn))
    return s ++ (← storeCell pn (.loc m) (locs (← arg 1))) ++ (← emit d (locs (m :: old)))
  | .lend | .relend => do
    let ls ← arg 0
    emit d (locs ls ++ locs ls)
  | .load => do
    let pn ← argN 0
    let c ← contents pn
    if ← zeroCell pn then return ← emit d (zeros (← wordsN n))
    let (s, vs) ← loadCell pn (.loc ((← arg 0).headD 0)) (← wordsN c)
    let L ← L
    if L.r c == L.r n || (L.triv c && L.w c == L.w n) then return s ++ (← emit d (locs vs))
    let ts ← fresh (← wordsN n)
    let tick := if (← read).counts && !L.triv c then [Stmt.tickCopy] else []
    return s ++ tick ++ [.call ts (← helper (.reCopy (L.r c) (L.r n))) (locs vs)] ++ (← emit d (locs ts))
  | .take => do
    let pn ← argN 0
    let m := (← arg 0).headD 0
    if ← zeroCell pn then return ← emit d ([.loc m] ++ zeros (← wordsN (← contents pn)))
    let (s, vs) ← loadCell pn (.loc m) (← wordsN (← contents pn))
    return s ++ (← emit d (locs (m :: vs)))
  | .put => do
    let pn ← argN 0
    let m := (← arg 0).headD 0
    if ← zeroCell pn then return ← emit d [.loc m]
    return (← storeCell pn (.loc m) (locs (← arg 1))) ++ (← emit d [.loc m])
  | .slotOut => do
    -- `swap`'s load, with no store: the slot is left empty.
    let pn ← argN 0
    let m := (← arg 0).headD 0
    if ← zeroCell pn then return ← emit d ([.loc m] ++ zeros (← wordsN (← contents pn)))
    let (s, old) ← loadCell pn (.loc m) (← wordsN (← contents pn))
    return s ++ (← emit d (locs (m :: old)))
  | .slotIn => do
    -- `swap`'s store, with no load: the slot was empty.
    let m := (← arg 0).headD 0
    let rn := n
    if ← zeroCell rn then return ← emit d [.loc m]
    return (← storeCell rn (.loc m) (locs (← arg 1))) ++ (← emit d [.loc m])
  | .tab fi | .tabLit fi .. => do
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
    match op with
    | .tabLit _ => do
      let ts ← fresh 2
      let gn ← argN 0
      let some c := (← L).unionOf gn |>.toList.head? | throw "word IR: tabLit of no code"
      let (es, env) ← envOf gn c fw
      let dr ← dropVals gn fw
      let off := env.headD (.c64 0)
      let len := env.getD 1 (.c64 0)
      return es ++ [.ite (.op (.rel .w64 .le_u) [.loc k, len])
          (dr ++ [.set (ts.headD 0) (add64 (.data 0) off), .set (ts.getD 1 0) (.loc k)])
          (mk ++ [.call ts (fnIndex fi) args])] ++ (← emit d (locs ts))
    | _ => lowerCall mk (fnIndex fi) args 2 d
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
    let addr := add64 (.loc (a.headD 0)) (mul64 i (.c64 st.toUInt64))
    return (← storeCell leaf addr (locs (← arg 2))) ++ (← emit d (locs a))
  | .slotTake => do
    let leaf ← leafOf (← argN 0)
    let st ← slotStride leaf
    let a ← arg 0
    let i ← one (args.getD 1 0)
    let addr := add64 (.loc (a.headD 0)) (mul64 i (.c64 st.toUInt64))
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
      let addr := add64 (.loc b) (mul64 (.loc i) (.c64 st.toUInt64))
      if !check then return ← emit d [.c64 0, addr]
      let t₀ ← fresh1
      let t₁ ← fresh1
      return (← boundTick) ++ [.ite (ltu64 (.loc i) (.loc k))
          [.set t₀ (.c64 0), .set t₁ addr] [.set t₀ (.c64 1), .set t₁ (.c64 0)]] ++
        (← emit d [.loc t₀, .loc t₁])
    | _, _ => throw "word IR: idx of a non-family"
  | .split _ => do
    let leaf ← leafOf (← argN 0)
    let st ← slotStride leaf
    match ← arg 0, ← arg 1 with
    | [b, k], [i] =>
      let pn ← child n 0
      let (s₁, vp) ← mkPair pn [.loc b, .loc i]
        [add64 (.loc b) (mul64 (.loc i) (.c64 st.toUInt64)), .op (.bin .w64 .sub) [.loc k, .loc i]]
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
      let addr := add64 (.loc b) (mul64 (.loc i) (.c64 st.toUInt64))
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
      let ai := add64 (.loc b) (mul64 (.loc i) (.c64 st.toUInt64))
      let aj := add64 (.loc b) (mul64 (.loc j) (.c64 st.toUInt64))
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
  | .litByte => do
    let o := (← arg 0).headD 0
    let cnt := (← arg 1).headD 0
    let i := (← arg 2).headD 0
    let r ← fresh1
    return (← boundTick) ++
      [.ite (ltu64 (.loc i) (.loc cnt))
        [.set r (.load8 (add64 (add64 (.data 0) (.loc o)) (.loc i)))]
        [.set r (.c64 0)]] ++ (← emit d [.loc r])
  | .litView _ => throw "word IR: litView is not built yet"
  | .io .readByte => do
    let m := (← arg 0).headD 0
    let b ← fresh1; let t₀ ← fresh1; let t₁ ← fresh1
    return [.set b (.getc (.load (.loc m) 0)),
      .ite (eq64 (.loc b) (.c64 0xFFFFFFFFFFFFFFFF))
        [.set t₀ (.c64 1), .set t₁ (.c64 0)] [.set t₀ (.c64 0), .set t₁ (.loc b)]] ++
      (← emit d [.loc m, .loc t₀, .loc t₁])
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
  | .letv .. | .letpair .. | .case .. | .copy .. | .drop .. | .absurd _ => false
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
      | .i32 k => k.toUInt64 | .i64 k => k | .u8 k => k.toUInt64 | .f32 k => k.toUInt64 | .f64 k => k)]
  | .pair a b => do
    let (s, vs) ← mkPair n (locs (← vals a)) (locs (← vals b))
    return s ++ (← emit d vs)
  | .inj r a => do
    let (s, vs) ← mkInj n r (locs (← vals a))
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
    let (s, a, c) ← splitPair pn (← vals p) true
    bindVals x a
    bindVals y c
    return s ++ (← lowerTm f b n d)
  | .case sv x b₁ y b₂ => do
    let sn ← nodeV sv
    let ls ← vals sv
    let (s₁, a) ← payload sn false ls true
    let (s₂, c) ← payload sn true ls true
    bindVals x a
    bindVals y c
    let t₁ ← lowerTm f b₁ n d
    let t₂ ← lowerTm f b₂ n d
    return [.ite (eqz64 (.loc (ls.headD 0))) (s₁ ++ t₁) (s₂ ++ t₂)]
  | .absurd _ => return [.trap]
  | .copy x x' b => do
    let (s, ls) ← copyVals (← nodeV x) (← vals x) (tick := true)
    bindVals x' ls
    return s ++ (← lowerTm f b n d)
  | .drop x b => do
    let s ← dropVals (← nodeV x) (← vals x)
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

def copyField (n k : Nat) (ls : List Nat) : LM (List Stmt × List Exp) := do
  let c ← child n k
  let (s₁, vs) ← getField n k ls false
  let (s₂, vs) ← copyVals c vs
  let (s₃, out) ← putField n k (locs vs)
  pure (s₁ ++ s₂ ++ s₃, out)

def dropField (n k : Nat) (ls : List Nat) : LM (List Stmt) := do
  let c ← child n k
  let (s₁, vs) ← getField n k ls true
  pure (s₁ ++ (← dropVals c vs))

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
    let (body, nloc) ← inFn w do
      let ps := List.range w
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
        let (s₁, a) ← copyField n 0 (← fieldLocals n 0 ps)
        let (s₂, b) ← copyField n 1 (← fieldLocals n 1 ps)
        pure [.ite (eqz64 (.loc 0))
          (s₁ ++ [.ret ([.c64 0] ++ a ++ zeros (w - 1 - a.length))])
          (s₂ ++ [.ret ([.c64 1] ++ b ++ zeros (w - 1 - b.length))])]
      | _ => pure [.ret (locs ps)]
    pure { name := "copy", params := w, results := w, locals := nloc, body := body ++ [.trap] }
  | .drop n =>
    let w := L.w n
    let (body, nloc) ← inFn w do
      let ps := List.range w
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
              out := out ++ (← dropVals e (vs.drop off |>.take (L.w e))); off := off + L.w e
            return out ++ [.free (.loc 0)]
          let mut off := 1
          for e in ← envNodes c do
            out := out ++ (← dropVals e (List.range' off (L.w e))); off := off + L.w e
          return out
        pure (s ++ [.ret []])
      | .pair .. => pure ((← dropField n 0 (← fieldLocals n 0 ps)) ++
          (← dropField n 1 (← fieldLocals n 1 ps)) ++ [.ret []])
      | .sum .. => pure [.ite (eqz64 (.loc 0)) (← dropField n 0 (← fieldLocals n 0 ps))
          (← dropField n 1 (← fieldLocals n 1 ps)), .ret []]
      | _ => pure [.ret []]
    pure { name := "drop", params := w, results := 0, locals := nloc, body }
  | .print n =>
    let w := L.w n
    let (body, nloc) ← inFn w do
      let ps := List.range w
      match L.sh n with
      | .unit | .zero => pure (outStr "()")
      | .int .w32 => pure (outStr "i32[" ++ [.call [] fPrintDec [.loc 0]] ++ outStr "]")
      | .int .w64 => pure (outStr "i64[" ++ [.call [] fPrintDec [.loc 0]] ++ outStr "]")
      | .int .w8 => pure (outStr "u8[" ++ [.call [] fPrintDec [.loc 0]] ++ outStr "]")
      | .int .f32 => pure (outStr "f32[" ++ [.call [] fPrintDec [.loc 0]] ++ outStr "]")
      | .int .f64 => pure (outStr "f64[" ++ [.call [] fPrintDec [.loc 0]] ++ outStr "]")
      | .clos .. | .unk => pure (outStr "<fun>")
      | .ref _ | .imm _ | .mut _ | .opq => pure (outStr "<loc>")
      | .fam _ => pure (outStr "(<loc>, i32[" ++ [.call [] fPrintDec [.loc 1]] ++ outStr "])")
      | .pair .. => pure (outStr "(" ++ (← printField n 0 (← fieldLocals n 0 ps) false) ++ outStr ", " ++
          (← printField n 1 (← fieldLocals n 1 ps) false) ++ outStr ")")
      | .sum .. => pure [.ite (eqz64 (.loc 0)) (outStr "inl " ++ (← printField n 0 (← fieldLocals n 0 ps) true))
          (outStr "inr " ++ (← printField n 1 (← fieldLocals n 1 ps) true))]
    pure { name := "print", params := w, results := 0, locals := nloc, body := body ++ [.ret []] }
  | .reCopy c n =>
    -- The contents at `c` read through `Imm̲` at `n`: a closure is `Unk` (no words), a pointer the
    -- word, a boxed field copied, as `copy` copies.
    let wc := L.w c
    let wn := L.w n
    let (body, nloc) ← inFn wc do
      let (s, vs) ← reVals 64 c n (List.range wc)
      pure (s ++ [.ret vs])
    pure { name := "reborrow", params := wc, results := wn, locals := nloc, body := body ++ [.trap] }
  | .apply cls j =>
    let some rn := ((match L.sh cls with | .clos _ _ r => r | _ => [])[j]?) | throw "word IR: an apply's class"
    let (k, param, _) ← classOf cls
    let pw ← match k, param with
      | .lam, some p => pure (L.w p)
      | _, _ => pure 0
    let cw := L.w cls
    let rw := L.w rn
    let (body, nloc) ← inFn (cw + pw) do
      let ps := List.range cw
      let arg := locs (List.range' cw pw)
      onCode cls ps fun c => do
        let (s, env) ← envOf cls c ps
        return s ++ [.tailCall (← codeFn c j) (env ++ arg)]
    pure { name := "apply", params := cw + pw, results := rw, locals := nloc, body := body ++ [.trap] }
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
      | _, _ =>
        if L.triv c' && L.w c' == L.w n' then return ([], locs vs)
        let ts ← fresh (L.w n')
        return ([.call ts (← helper (.reCopy (L.r c') (L.r n'))) (locs vs)], locs ts)
    match L.sh c, L.sh n with
    | .clos .., .unk => return ([], [])
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
      return ([.ite (eqz64 (.loc (ls.headD 0))) (sa ++ s₁ ++ s₃ ++ sets vl) (sb ++ s₂ ++ s₄ ++ sets vr)],
        locs ts)
    | _, _ =>
      let (s, ts) ← copyVals c ls
      return (s, locs ts)


/-! ### Functions and the program -/

def lowerFn (i : Nat) (fd : Backend2.Fn) : LM Backend.Flat.Fn := do
  let L ← L
  let some rn := L.fnRet[i]? | throw s!"word IR: no node of f{i}'s answer"
  let pws := fd.params.map fun x => L.w (L.node x)
  let total := pws.foldl (· + ·) 0
  let k := L.w rn
  let (body, nloc, frame) ← inFnF total do
    let mut off := 0
    for (x, w) in fd.params.zip pws do
      bindVals x (List.range' off w)
      off := off + w
    pure ((← lowerTm (1 <<< 22) fd.body rn (.ret k)) ++ [.trap])
  pure { name := fd.name, params := total, results := k, locals := nloc, frame, body }

def countsReport : List Stmt :=
  outStr "allocs " ++ [.call [] fPrintDec [.stat 0]] ++ outStr "\nindirect " ++
    [.call [] fPrintDec [.stat 1]] ++ outStr "\ncopies " ++
    [.call [] fPrintDec [.stat 2]] ++ outStr "\n"

/-- Run `main`, print its value, drop it, print the live count, and with `counts` the run's
counts. -/
def entryFn (fMain : Nat) : LM Backend.Flat.Fn := do
  let L ← L
  let n := L.mainNode
  let (body, nloc) ← inFn 0 do
    let m ← fresh (L.w n)
    let pr := [Stmt.call [] (← helper (.print (L.r n))) (locs m)] ++ outStr "\n"
    let dr ← dropVals n m
    pure ([Stmt.call m fMain []] ++ pr ++ dr ++ outStr "live " ++ [.call [] fPrintDec [.live]] ++
      outStr "\n" ++ (if (← read).counts then countsReport else []) ++ [.ret []])
  pure { name := "entry", params := 0, results := 0, locals := nloc, body }

/-- The word IR of a program at its layouts; with `counts`, the counting build. -/
def lowerProg (p : Prog) (L : Layouts) (known : Std.HashMap Var Nat) (framed : Std.HashSet Var)
    (counts : Bool) : Except String Backend.Flat.Prog := do
  let nf := p.fns.size
  let fMain := 1 + nf
  let pad := (8 - p.data.size % 8) % 8
  let ctx : LCtx := { L, p, helperBase := fMain + 2, counts, staticBase := p.data.size + pad, known, framed }
  let act : LM (List Backend.Flat.Fn) := do
    let fns ← p.fns.toList.zipIdx.mapM fun (fd, i) => lowerFn i fd
    let k := L.w L.mainNode
    let (body, nloc, frame) ← inFnF 0 do
      pure ((← lowerTm (1 <<< 22) p.main L.mainNode (.ret k)) ++ [.trap])
    let main : Backend.Flat.Fn := { name := "main", params := 0, results := k, locals := nloc, frame, body }
    let entry ← entryFn fMain
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
  let data := p.data ++ Array.replicate (pad + 8 * p.statics) 0
  pure { fns := fns.toArray, entry := fMain + 1, data }

end Backend2.Low

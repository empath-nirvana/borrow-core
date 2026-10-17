import Std.Data.HashMap
import Backend.Clos.Syntax
import Backend.Clos.Types
import Backend.Clos.Flow
import Backend.Flat.Syntax

/-!
# Backend — closure IR to flat IR

The lowering is type-directed (`Backend/Clos/Types.lean`): a closure-IR variable of layout type
`A` is `|A|` locals, and every operation works on its operands' words.

- **Pairs** are their components' words: building one and `letpair` move no data and allocate
  nothing (the pair's locals are split between the two binders).
- **Injections** are a tag word (`0` for `inl`) and the payload, padded to the wider arm; `case`
  tests the tag and binds the payload's words.
- A **boxed field** (one that closes a recursive type) is a pointer to a fresh object holding the
  field's words: building allocates it, and taking it apart loads and frees it.
- **Closures** are defunctionalized: a closure of type `n` is its code's tag in `n`'s union,
  then the captured values' words, padded (`Backend/Clos/Types.lean`), and building one moves the
  captured words into it. A code is a function of its captured values' words and the argument's
  words, returning the answer's words. A call whose code is known, because the flow analysis
  (`Backend/Clos/Flow.lean`) finds one code of the union there or the union has one code, is a direct call of
  that code on the closure's captured words; any other call is a call of the type's dispatcher
  `apply`, a `switch` on the tag whose cases tail-call the codes. There are no function pointers.
  A call in return position whose callee answers exactly the caller's words is a tail call.
- **Owned folds** of a linear shape run by pointer reversal, in constant stack (below).
- **Recursive closure types** keep a heap environment: a closure is the word `2t + 1` when its
  code `t` captures nothing, and otherwise an object holding `t` and the captured values' words.
  Their codes take the closure's word, load the environment into locals and free the object.
- **Cells and array slots** hold their contents' words, `max 1 |A|` words for a cell and `|A|`
  per slot. A scoped cell no suspension crosses is a slot of its function's frame, and a
  capability's cell a word of the program's data (Frame slots, below; `[spec §35]`).
- `copy`, `drop`, the printer, the array primitives, the loop driver and the dispatchers are
  functions generated on demand per layout type (`Helper`); at a trivial type a copy is the words
  themselves and a drop is nothing. Copying or dropping a closure switches on its tag and copies
  or drops that code's captured values; at a recursive closure type, a word `2t + 1` needs
  nothing, and an object is copied or dropped by its code's `closCopy` or `closDrop`.

Function indices: `print_dec`, the closure codes in code order, `main`, the entry, then the
generated helpers in the order they are first asked for.
-/

namespace Backend.Flat
open BoCa Backend.Clos

/-- A function generated per layout type (types are representatives). -/
inductive Helper where
  | copy (n : Nat)
  | drop (n : Nat)
  | print (n : Nat)
  /-- Copy and drop the heap environment of a closure of code `c`, at a recursive closure type. -/
  | closCopy (c : Nat)
  | closDrop (c : Nat)
  /-- `tab` and its loop, at element location type `a` and tabulator type `f`. -/
  | tab (a f : Nat)
  | tabLoop (a f : Nat)
  /-- `drop` of an array and its loop, at element location type `a` and consumer type `f`. -/
  | arrDrop (a f : Nat)
  | arrDropLoop (a f : Nat)
  /-- `count` and its loop, at step type `f` and state type `s` (SPEC §16). -/
  | count (f s : Nat)
  | countLoop (f s : Nat)
  /-- `count_try` and its loop, at step type `f` and state type `s` (SPEC §16). -/
  | countTry (f s : Nat)
  | countTryLoop (f s : Nat)
  /-- Drive a loop of type `n` (SPEC §11). -/
  | drive (n : Nat)
  /-- The dispatcher of the closure type `n`: the closure's words and the argument's, answering
  the code its tag names. -/
  | apply (n : Nat)
  /-- The descent and the ascent of the owned fold whose step is code `c`, by pointer
  reversal. -/
  | foldDown (c : Nat)
  | foldUp (c : Nat)
  deriving BEq, Hashable, Repr, Inhabited

structure Ctx where
  T : Types
  codes : Array Code
  /-- The calls whose code the flow analysis finds, by their function variable. -/
  known : Std.HashMap Var Nat
  /-- The owned folds' steps, by code. -/
  folds : Std.HashMap Nat FoldCode := {}
  /-- The codes whose closures the program builds (`Clos.Prog.liveCodes`). -/
  live : Std.HashSet Nat := {}
  /-- The code of the loops the entry drives, when the flow analysis finds one. -/
  driveKnown : Option Nat := none
  helperBase : Nat
  /-- The literals' code (`Backend.Clos.Prog.litCode`). -/
  litCode : Option Nat := none
  /-- The scoped cells placed in a frame slot (`frameScopes`). -/
  frameScopes : Std.HashSet Nat := {}

structure LState where
  vars : Std.HashMap Var (List Nat) := {}
  next : Nat := 0
  helpers : Std.HashMap Helper Nat := {}
  queue : Array Helper := #[]
  /-- In a code of a recursive closure type, the local holding its environment object (`0` once
  it is reused), and the object's words. -/
  reuse : Option (Nat × Nat) := none
  /-- The words of the function's frame so far: its slots (`Fn.frame`). -/
  frame : Nat := 0
  /-- The function's locals set to a constant where they are made (`emit`): each is set once, so
  it holds that constant wherever it is read. A division by a constant that cannot fail, and a
  `case` on a constant tag, are lowered without their test (SPEC §39). -/
  consts : Std.HashMap Nat UInt64 := {}

abbrev LM := ReaderT Ctx (StateT LState (Except String))

def fPrintDec : Nat := 0
def codeFn (c : Nat) : Nat := 1 + c

/-! ### Locals and types -/

def fresh (k : Nat) : LM (List Nat) :=
  modifyGet fun s => (List.range' s.next k, { s with next := s.next + k })

def fresh1 : LM Nat := modifyGet fun s => (s.next, { s with next := s.next + 1 })

def locs (ls : List Nat) : List Exp := ls.map .loc

def zeros (k : Nat) : List Exp := List.replicate k (.c64 0)

def vty (x : Var) : LM Nat := do
  match (← read).T.varTy[x]? with
  | some n => pure n
  | none => throw s!"flat IR: variable {x} has no type"

def T : LM Types := return (← read).T

def words (n : Nat) : LM Nat := return (← T).words n

def triv (n : Nat) : LM Bool := return (← T).triv n

/-- The locals of `x`. -/
def vals (x : Var) : LM (List Nat) := do
  match (← get).vars[x]? with
  | some ls => pure ls
  | none => throw s!"flat IR: variable {x} is unbound"

def bindVals (x : Var) (ls : List Nat) : LM Unit :=
  modify fun s => { s with vars := s.vars.insert x ls }

/-- Fresh locals for `x`, as wide as its type. -/
def bindFresh (x : Var) : LM (List Nat) := do
  let ls ← fresh (← words (← vty x))
  bindVals x ls
  pure ls

def helper (h : Helper) : LM Nat := do
  let T ← T
  let h := match h with
    | .copy n => .copy (T.r n) | .drop n => .drop (T.r n) | .print n => .print (T.r n)
    | .tab a f => .tab (T.r a) (T.r f) | .tabLoop a f => .tabLoop (T.r a) (T.r f)
    | .arrDrop a f => .arrDrop (T.r a) (T.r f) | .arrDropLoop a f => .arrDropLoop (T.r a) (T.r f)
    | .count f s => .count (T.r f) (T.r s) | .countLoop f s => .countLoop (T.r f) (T.r s)
    | .countTry f s => .countTry (T.r f) (T.r s)
    | .countTryLoop f s => .countTryLoop (T.r f) (T.r s)
    | .drive n => .drive (T.r n) | .apply n => .apply (T.r n)
    | h => h
  match (← get).helpers[h]? with
  | some i => pure i
  | none =>
    let base := (← read).helperBase
    modifyGet fun s => (base + s.queue.size,
      { s with helpers := s.helpers.insert h (base + s.queue.size), queue := s.queue.push h })

/-- Run `act` as the body of a function of `params` words: its locals start after them. The
number of locals beyond the parameters. -/
def inFnF (params : Nat) (act : LM α) : LM (α × Nat × Nat) := do
  let saved ← get
  set { saved with vars := {}, next := params, reuse := none, frame := 0, consts := {} }
  let a ← act
  let n := (← get).next
  let fw := (← get).frame
  modify fun s => { s with vars := saved.vars, next := saved.next, reuse := saved.reuse,
                           frame := saved.frame, consts := saved.consts }
  pure (a, n - params, fw)

/-- `inFnF` for a function with no frame: a helper, which lowers no closure-IR term. -/
def inFn (params : Nat) (act : LM α) : LM (α × Nat) := do
  let (a, n, fw) ← inFnF params act
  if fw != 0 then throw "flat IR: a frame slot in a generated function"
  pure (a, n)

/-! ### Reusing a code's environment object

A code of a recursive closure type receives its closure as an object (Representation). It keeps
the object until it returns, and the first closure of the same width it builds is built in it:
the object is updated in place, as a suspended computation's frame is when it is resumed and
suspends again. The local holding the object is set to `0` once it is reused, and a return frees
it when it is not `0`. -/

/-- The words of a closure of `size` words, built in the environment object when it is still
held, or in a fresh object: the statements that leave its address in `p`. -/
def reuseOrAlloc (size p : Nat) : LM (List Stmt) := do
  let fresh : List Stmt := [.set p (.alloc (.c64 size.toUInt64))]
  match (← get).reuse with
  | some (l, sz) =>
    if sz != size then return fresh
    return [.ite (.op (.eqz .w64) [.loc l]) fresh [.set p (.loc l), .set l (.c64 0)]]
  | none => return fresh

/-- Free the environment object where a path returns, when it is still held. -/
def releaseReuse : LM (List Stmt) := do
  match (← get).reuse with
  | some (l, _) => return [.ite (.op (.eqz .w64) [.loc l]) [] [.free (.loc l)]]
  | none => return []

/-! ### Fields -/

/-- Store the words `vs` at `a + 8·off`. -/
def storeAt (a : Exp) (off : Nat) (vs : List Exp) : List Stmt :=
  vs.zipIdx.map fun (e, i) => .store a (off + i) e

/-- Load `k` words at `a + 8·off` into fresh locals. -/
def loadAt (a : Exp) (off k : Nat) : LM (List Stmt × List Nat) := do
  let ls ← fresh k
  pure (ls.zipIdx.map (fun (l, i) => .set l (.load a (off + i))), ls)

/-- The contents (`k` words) of the cell or slot at `a`, of location type `n`: a byte slot's
byte, or the words. -/
def loadCell (n : Nat) (a : Exp) (k : Nat) : LM (List Stmt × List Nat) := do
  if (← read).T.byteCell n then
    let t ← fresh1
    return ([.set t (.load8 a)], [t])
  loadAt a 0 k

/-- Store `vs` in the cell or slot at `a`, of location type `n`. -/
def storeCell (n : Nat) (a : Exp) (vs : List Exp) : LM (List Stmt) := do
  if (← read).T.byteCell n then return [.store8 a (vs.headD (.c64 0))]
  return storeAt a 0 vs

/-- The bytes between two slots of an array of location type `n`: one for a byte slot, else
the class's words. -/
def slotBytes (T : Types) (n : Nat) : Nat := if T.byteCell n then 1 else 8 * T.cellWords n

/-- Field `i` of `n` built from its words: behind a pointer, a fresh object holding them. -/
def putField (n i : Nat) (vs : List Exp) : LM (List Stmt × List Exp) := do
  let (_, b) := (← T).field n i
  if !b then return ([], vs)
  let t ← fresh1
  return ([.set t (.alloc (.c64 (max 1 vs.length).toUInt64))] ++ storeAt (.loc t) 0 vs, [.loc t])

/-- The words of field `i` of `n` from the field's locals: behind a pointer, loaded (and the
object freed when the field is consumed). -/
def getField (n i : Nat) (ls : List Nat) (consume : Bool) : LM (List Stmt × List Nat) := do
  let (c, b) := (← T).field n i
  if !b then return ([], ls)
  let p := Exp.loc (ls.headD 0)
  let (s, vs) ← loadAt p 0 (← words c)
  return (s ++ (if consume then [.free p] else []), vs)

def mkPair (n : Nat) (a b : List Exp) : LM (List Stmt × List Exp) := do
  let (s₁, v₁) ← putField n 0 a
  let (s₂, v₂) ← putField n 1 b
  pure (s₁ ++ s₂, v₁ ++ v₂)

def mkInj (n : Nat) (r : Bool) (a : List Exp) : LM (List Stmt × List Exp) := do
  let (s, v) ← putField n (if r then 1 else 0) a
  let pw := (← words n) - 1
  pure (s, [.c64 (if r then 1 else 0)] ++ v ++ zeros (pw - v.length))

/-- Variant `k` of the `n`-ary sum `n`: its tag, then the payload, padded. -/
def mkCon (n k : Nat) (a : List Exp) : LM (List Stmt × List Exp) := do
  let (s, v) ← putField n k a
  let pw := (← words n) - 1
  pure (s, [.c64 k.toUInt64] ++ v ++ zeros (pw - v.length))

/-- The fields of a pair's or injection's locals. -/
def fieldLocals (n i : Nat) (ls : List Nat) : LM (List Nat) := do
  let T ← T
  match T.ty n with
  | .pair .. =>
    let w₀ := T.fieldWords n 0
    pure (if i == 0 then ls.take w₀ else (ls.drop w₀).take (T.fieldWords n 1))
  | _ => pure ((ls.drop 1).take (T.fieldWords n i))

/-- The two components of a pair's locals. -/
def splitPair (n : Nat) (ls : List Nat) (consume : Bool) :
    LM (List Stmt × List Nat × List Nat) := do
  let T ← T
  let w₀ := T.fieldWords n 0
  let (s₁, a) ← getField n 0 (ls.take w₀) consume
  let (s₂, b) ← getField n 1 ((ls.drop w₀).take (T.fieldWords n 1)) consume
  pure (s₁ ++ s₂, a, b)

/-- The payload of an injection's locals, read as arm `r`. -/
def payload (n : Nat) (r : Bool) (ls : List Nat) (consume : Bool) : LM (List Stmt × List Nat) := do
  let i := if r then 1 else 0
  getField n i ((ls.drop 1).take ((← T).fieldWords n i)) consume

/-- The payload of an `n`-ary sum's locals, read as variant `k`. -/
def payloadN (n k : Nat) (ls : List Nat) (consume : Bool) : LM (List Stmt × List Nat) := do
  getField n k ((ls.drop 1).take ((← T).fieldWords n k)) consume

/-! ### Closures -/

/-- The words of a closure of code `c` whose captured values are the words `env`: the tag, then
`env`, padded to the type's width; at a recursive closure type, the word `2t + 1` or a fresh
object holding the tag and `env`. -/
def closVals (c : Nat) (env : List Exp) : LM (List Stmt × List Exp) := do
  let T ← T
  let n := T.codeType c
  let t := T.tag c
  if T.isRec n then
    if env.isEmpty then return ([], [.c64 (2 * t + 1).toUInt64])
    let p ← fresh1
    return ((← reuseOrAlloc (1 + env.length) p) ++ [.store (.loc p) 0 (.c64 t.toUInt64)] ++
      storeAt (.loc p) 1 env, [.loc p])
  return ([], [.c64 t.toUInt64] ++ env ++ zeros (T.words n - 1 - env.length))

/-- The function and arguments that call the closure of type `n` in the locals `ls` on the words
`args`. When its code `c` is known (`known`, from the flow analysis, or the union's one code),
`c` directly, on the captured values' words (at a recursive type, on the closure's word);
otherwise the type's dispatcher. -/
def callTarget (n : Nat) (ls : List Nat) (args : List Exp) (known : Option Nat) :
    LM (Nat × List Exp) := do
  let T ← T
  let u := T.union n
  let known := match known with
    | some c => if u.contains c then some c else none
    | none => if u.size == 1 then u[0]? else none
  match known with
  | some c =>
    if T.isRec n then return (codeFn c, .loc (ls.headD 0) :: args)
    return (codeFn c, locs ((ls.drop 1).take (T.envWords c)) ++ args)
  | none => return (← helper (.apply n), locs ls ++ args)

/-- Call the closure of type `n` in the locals `ls` on the words `args`; the results go to
`ds`. -/
def callClosure (ds : List Nat) (n : Nat) (ls : List Nat) (args : List Exp) : LM (List Stmt) := do
  let (g, as) ← callTarget n ls args none
  return [.call ds g as]

/-- `act c` for the code `c` of the closure of type `n` in the locals `ls`: a `switch` on its
tag. At a recursive closure type, `imm` when the closure is a word `2t + 1`, and otherwise a
`switch` on the tag its object holds. -/
def onCode (n : Nat) (ls : List Nat) (imm : List Stmt) (act : Nat → LM (List Stmt)) :
    LM (List Stmt) := do
  let T ← T
  let cases ← (T.union n).toList.mapM act
  let f := Exp.loc (ls.headD 0)
  if !T.isRec n then return [.switch f cases [.trap]]
  return [.ite (wrap (and64 f (.c64 1))) imm [.switch (.load f 0) cases [.trap]]]

/-! ### Copy and drop -/

/-- A copy of the words `ls` of type `n`. -/
def copyVals (n : Nat) (ls : List Nat) : LM (List Stmt × List Nat) := do
  if ← triv n then return ([], ls)
  let ts ← fresh (← words n)
  return ([.call ts (← helper (.copy n)) (locs ls)], ts)

def dropVals (n : Nat) (ls : List Nat) : LM (List Stmt) := do
  if ← triv n then return []
  return [.call [] (← helper (.drop n)) (locs ls)]

/-! ### Terms -/

/-- Where a term's words go: locals, returned (padded to `k` words), or bound to the variable
`x`. -/
inductive Dest where
  | to (ls : List Nat)
  | ret (k : Nat)
  | bind (x : Var)

def emitTo (ls : List Nat) (vs : List Exp) : LM (List Stmt) := do
  if ls.length != vs.length then
    throw s!"flat IR: {vs.length} words for {ls.length} locals"
  pure (ls.zip vs |>.map fun (l, e) => .set l e)

def emit : Dest → List Exp → LM (List Stmt)
  | .to ls, vs => emitTo ls vs
  | .ret k, vs => return (← releaseReuse) ++ [.ret (vs ++ zeros (k - vs.length))]
  | .bind x, vs => do
    -- A word already in a local is held there: every local is set once, where it is made, and
    -- what it held is consumed here. Any other word is set in a fresh local.
    let mut ls : Array Nat := #[]
    let mut ss : Array Stmt := #[]
    for v in vs do
      match v with
      | .loc l => ls := ls.push l
      | e =>
        let t ← fresh1
        ss := ss.push (.set t e)
        ls := ls.push t
        if let .c64 k := e then modify fun s => { s with consts := s.consts.insert t k }
    bindVals x ls.toList
    return ss.toList

/-- The operation answers a float whose NaN Wasm leaves to the implementation: the arithmetic,
which the compiled code makes canonical (SPEC §37). -/
def canonicalises : HostOp → Bool
  | .fbin _ o => match o with | .copysign => false | _ => true
  | .fun1 _ o => match o with | .abs | .neg => false | _ => true
  | .demote | .promote => true
  | _ => false

/-- A float's canonical NaN, as a word. -/
def canonWord : FWidth → Exp
  | .f32 => .c64 0x7FC00000
  | .f64 => .c64 0x7FF8000000000000

/-- A float constant, given by its bits, at a float operation's operand: an `f32` is 32 bits. -/
def fconst (f : FWidth) (b32 : UInt32) (b64 : UInt64) : Exp :=
  match f with
  | .f32 => .c32 b32
  | .f64 => .c64 b64

/-- `trunc`'s range at `f` (Wasm's): the integer part of `x` fits `i` read by `sx` exactly when
`x` compares above the lower bound (`>`, or `≥` where the bound is a float of the format) and
below the upper. Both comparisons are false at a NaN. -/
def truncRange (i : IWidth) (f : FWidth) (sx : Sx) : FRelOp × Exp × Exp :=
  match i, sx, f with
  | .i32, .s, .f64 => (.gt, .c64 0xC1E0000000200000, .c64 0x41E0000000000000)
  | .i32, .s, .f32 => (.ge, .c32 0xCF000000, .c32 0x4F000000)
  | .i64, .s, f => (.ge, fconst f 0xDF000000 0xC3E0000000000000, fconst f 0x5F000000 0x43E0000000000000)
  | .i32, .u, f => (.gt, fconst f 0xBF800000 0xBFF0000000000000, fconst f 0x4F800000 0x41F0000000000000)
  | .i64, .u, f => (.gt, fconst f 0xBF800000 0xBFF0000000000000, fconst f 0x5F800000 0x43F0000000000000)

/-- The integer division `o` on its operands' words `ls` (§8): where Wasm traps, the test that
holds there, and the quotient or remainder's word where it does not. A divisor that is a constant
at which the division has an answer (`LState.consts`) has no test: the bare instruction
(SPEC §39). -/
def divTest (o : HostOp) (ls : List Nat) : LM (Option Exp × Exp) := do
  let (w, d) ← match o with
    | .div w d => pure (w, d)
    | _ => throw "flat IR: not a division"
  let raw (l : Nat) : Exp := match w with
    | .w32 | .w8 | .f32 => wrap (.loc l)
    | .w64 | .f64 => .loc l
  let args := ls.map raw
  let q : Exp := match w with
    | .w32 | .w8 | .f32 => extendU (.op o args)
    | .w64 | .f64 => .op o args
  let minus1 : UInt64 := match w with
    | .w32 | .w8 | .f32 => 0xFFFFFFFF | .w64 | .f64 => 0xFFFFFFFFFFFFFFFF
  let k := ((← get).consts.get? (ls.getD 1 0)).map fun k => match w with
    | .w32 | .w8 | .f32 => k &&& 0xFFFFFFFF | .w64 | .f64 => k
  if let some k := k then
    if k != 0 && (d != .div_s || k != minus1) then return (none, q)
  let a := args.headD (.c64 0)
  let b := args.getD 1 (.c64 0)
  let zero := Exp.op (.eqz w) [b]
  let trapC := match d with
    | .div_s =>
      let intMin := match w with
        | .w32 | .w8 | .f32 => Exp.c32 0x80000000 | .w64 | .f64 => .c64 0x8000000000000000
      let m1 := match w with
        | .w32 | .w8 | .f32 => Exp.c32 0xFFFFFFFF | .w64 | .f64 => .c64 0xFFFFFFFFFFFFFFFF
      or32 zero (and32 (.op (.rel w .eq) [a, intMin]) (.op (.rel w .eq) [b, m1]))
    | _ => zero
  pure (some trapC, q)

/-- A host operation on its operand's words (§8, §37): an integer or a float's bits, a tag, or a
partial operation's tag and integer. A 32-bit value is held zero-extended. -/
def hostVals (o : HostOp) (ls : List Nat) : LM (List Stmt × List Exp) := do
  -- A byte is held zero-extended, as an `i32` is: `wrap8` keeps the low 8 bits, and
  -- `extend8_u` is the word itself. A float is held as its bits, so `reinterpret` is the word.
  match o with
  | .wrap8 => return ([], [and64 (.loc (ls.headD 0)) (.c64 0xff)])
  | .extend8_u | .reinterpret_i _ | .reinterpret_f _ => return ([], [.loc (ls.headD 0)])
  | _ => pure ()
  let rawAt (w : Width) (e : Exp) : Exp := match w with
    | .w32 | .w8 | .f32 => wrap e
    | .w64 | .f64 => e
  let raw (l : Nat) : Exp := rawAt (hostArgWidth o) (.loc l)
  let args := ls.map raw
  let word (w : Width) (e : Exp) : Exp := match w with
    | .w32 | .w8 | .f32 => extendU e
    | .w64 | .f64 => e
  match hostResKind o, o with
  | .int w, _ =>
    match canonicalises o, w.float? with
    | true, some f =>
      -- A NaN result is replaced by the canonical one: `x ≠ x` holds exactly at a NaN.
      let t ← fresh1
      let x := rawAt w (.loc t)
      pure ([.set t (word w (.op o args)), .ite (.op (.frel f .ne) [x, x]) [.set t (canonWord f)] []],
        [.loc t])
    | _, _ => pure ([], [word w (.op o args)])
  | .test, _ => pure ([], [extendU (.op o args)])
  | .trapping _, .div _ _ =>
    let t₀ ← fresh1
    let t₁ ← fresh1
    match ← divTest o ls with
    | (none, q) => return ([], [.c64 0, q])
    | (some trapC, q) =>
      pure ([.ite trapC [.set t₀ (.c64 1), .set t₁ (.c64 0)] [.set t₀ (.c64 0), .set t₁ q]],
        [.loc t₀, .loc t₁])
  | .trapping w, .trunc i f sx =>
    -- Where Wasm's `trunc` traps, `inr ()`; in range, `trunc_sat` is `trunc`.
    let t₀ ← fresh1
    let t₁ ← fresh1
    let x := args.headD (.c64 0)
    let (loOp, lo, hi) := truncRange i f sx
    let ok := and32 (.op (.frel f loOp) [x, lo]) (.op (.frel f .lt) [x, hi])
    pure ([.ite ok [.set t₀ (.c64 0), .set t₁ (word w (.op (.trunc_sat i f sx) [x]))]
            [.set t₀ (.c64 1), .set t₁ (.c64 0)]], [.loc t₀, .loc t₁])
  | .trapping _, _ => throw "flat IR: a trapping operation that is neither a division nor a trunc"

/-- The contents' type of a `loc` type. -/
def locElem (n : Nat) : LM Nat := do
  match (← T).ty n with
  | .loc a _ => pure a
  | _ => throw "flat IR: not a location type"

/-- The cells of the location type `n` take no words: every contents their class holds is of
width `0` (`1`, a closure with nothing captured), and none is a byte. -/
def zeroCell (T : Types) (n : Nat) : Bool := T.cellWords n == 0 && !T.byteCell n

/-- `alloc v`, of the scope `k` when it is a scoped cell's. A cell of no words allocates
nothing: its address is `0`, never read or written. A scoped cell of a scope in `frameScopes`
is the next slot of the function's frame, and no allocation. -/
def lowerAlloc (k : Option Nat) (v : Var) (d : Dest) : LM (List Stmt) := do
  let some n := (← T).cons[v]? | throw "flat IR: an untyped cell"
  if zeroCell (← T) n then return ← emit d [.c64 0]
  let ls ← vals v
  let t ← fresh1
  let w := max 1 ((← T).cellWords n)
  let addr ← match k with
    | some k =>
      if (← read).frameScopes.contains k then do
        let off := (← get).frame
        modify fun s => { s with frame := off + w }
        pure (Exp.slot off w)
      else pure (.alloc (.c64 w.toUInt64))
    | none => pure (.alloc (.c64 w.toUInt64))
  return [.set t addr] ++ (← storeCell n (.loc t) (locs ls)) ++ (← emit d [.loc t])

/-- `free l`, of the scope `k` when it is a scoped cell's: the contents, and the cell freed (a
frame slot's life ended). A cell of no words was never allocated, so nothing is freed. -/
def lowerFree (k : Option Nat) (l : Var) (d : Dest) : LM (List Stmt) := do
  let a ← locElem (← vty l)
  let p := Exp.loc ((← vals l).headD 0)
  let (s, ls) ← loadCell (← vty l) p (← words a)
  let fs := (← read).frameScopes
  let slot := match k with
    | some k => fs.contains k
    | none => false
  let fr : List Stmt :=
    if zeroCell (← T) (← vty l) then [] else if slot then [.unslot p] else [.free p]
  return s ++ fr ++ (← emit d (locs ls))

def lowerPrim : Op → List Var → Dest → LM (List Stmt)
  | .alloc, [v], d => lowerAlloc none v d
  | .scopedAlloc k, [v], d => lowerAlloc (some k) v d
  | .staticCell addr, [v], d => do
      -- A capability's cell: the word at `addr` of the program's data, holding the contents.
      let some n := (← T).cons[v]? | throw "flat IR: an untyped cell"
      if (← T).cellWords n > 1 || (← T).byteCell n then
        throw "flat IR: a capability's cell wider than its word"
      return (← storeCell n (.c64 addr.toUInt64) (locs (← vals v))) ++
        (← emit d [.c64 addr.toUInt64])
  | .free, [l], d => lowerFree none l d
  | .scopedFree k, [l], d => lowerFree (some k) l d
  | .load, [l], d => do
      let a ← locElem (← vty l)
      let p := Exp.loc ((← vals l).headD 0)
      let (s, ls) ← loadCell (← vty l) p (← words a)
      let (c, ls) ← copyVals a ls
      return s ++ c ++ (← emit d (locs ls))
  | .store, [l, v], d => do
      let a ← vty v
      let p := Exp.loc ((← vals l).headD 0)
      let (s, old) ← loadCell (← vty l) p (← words a)
      let dr ← dropVals a old
      let s := if dr.isEmpty then [] else s ++ dr
      return s ++ (← storeCell (← vty l) p (locs (← vals v))) ++ (← emit d [])
  | .swap, [l, v], d => do
      let a ← locElem (← vty l)
      let m := (← vals l).headD 0
      let (s, old) ← loadCell (← vty l) (.loc m) (← words a)
      return s ++ (← storeCell (← vty l) (.loc m) (locs (← vals v))) ++
        (← emit d (locs (m :: old)))
  | .host op, [v], d => do
      let (s, vs) ← hostVals op (← vals v)
      return s ++ (← emit d vs)
  | .tab, [v], d => do
      let T ← T
      let f := (T.field (← vty v) 1).1
      let some n := T.cons[v]? | throw "flat IR: an untyped array"
      let l := (T.field n 0).1
      let ts ← fresh 2
      return [.call ts (← helper (.tab l f)) (locs (← vals v))] ++ (← emit d (locs ts))
  | .litTab, [v], d => do
      -- A literal's view: when the tabulator is the literal code's closure (its tag) and the
      -- length at most the literal's, the array is `(a, n)` in the read-only data, and nothing
      -- is allocated; otherwise `tab`.
      let T ← T
      let f := (T.field (← vty v) 1).1
      let some n := T.cons[v]? | throw "flat IR: an untyped array"
      let l := (T.field n 0).1
      let ts ← fresh 2
      let ws ← vals v
      let tabCall : List Stmt := [.call ts (← helper (.tab l f)) (locs ws)]
      let static? := match (← read).litCode with
        | some c => if (T.union f).contains c && !T.isRec f && T.byteCell l && T.envWords c == 2
            then some c else none
        | none => none
      match static?, ws with
      | some c, len :: tag :: ea :: en :: _ =>
        let fits := and32 (eq64 (.loc tag) (.c64 (T.tag c).toUInt64))
          (.op (.eqz .w32) [ltu64 (.loc en) (.loc len)])
        return [.ite fits [.set (ts.headD 0) (.loc ea), .set (ts.getD 1 0) (.loc len)] tabCall] ++
          (← emit d (locs ts))
      | _, _ => return tabCall ++ (← emit d (locs ts))
  | .litByte, [a, n, i], d => do
      let a := (← vals a).headD 0
      let n := (← vals n).headD 0
      let i := (← vals i).headD 0
      let r ← fresh1
      return [.ite (ltu64 (.loc i) (.loc n)) [.set r (.load8 (add64 (.loc a) (.loc i)))]
        [.set r (.c64 0)]] ++ (← emit d [.loc r])
  | .idx, [v], d => do
      let T ← T
      let h := (T.field (← vty v) 0).1
      let w := slotBytes T (T.field h 0).1
      match ← vals v with
      | [b, n, i] =>
        let t₀ ← fresh1
        let t₁ ← fresh1
        return [.ite (ltu64 (.loc i) (.loc n))
            [.set t₀ (.c64 0), .set t₁ (add64 (.loc b) (mul64 (.loc i) (.c64 w.toUInt64)))]
            [.set t₀ (.c64 1), .set t₁ (.c64 0)]] ++ (← emit d [.loc t₀, .loc t₁])
      | _ => throw "flat IR: idx of a non-array"
  | .split, [v], d => do
      -- `inl ((b, i), (b + i·s, n − i))` when `i ≤ n`, else `inr (b, n)`: no allocation.
      let T ← T
      let some r := T.cons[v]? | throw "flat IR: an untyped split"
      let h := (T.field (← vty v) 0).1
      let w := slotBytes T (T.field h 0).1
      match ← vals v with
      | [b, n, i] =>
        let p := (T.field r 0).1
        let (s₁, vp) ← mkPair p [.loc b, .loc i]
          [add64 (.loc b) (mul64 (.loc i) (.c64 w.toUInt64)), .op (.bin .w64 .sub) [.loc n, .loc i]]
        let (s₂, vl) ← mkInj r false vp
        let (s₃, vr) ← mkInj r true [.loc b, .loc n]
        let ts ← fresh (vl.length)
        let sets (vs : List Exp) : List Stmt := (ts.zip vs).map fun (t, e) => .set t e
        return [.ite (ltu64 (.loc n) (.loc i)) (s₃ ++ sets vr) (s₁ ++ s₂ ++ sets vl)] ++
          (← emit d (locs ts))
      | _ => throw "flat IR: split of a non-array"
  | .nullLoc, [], d => emit d [.c64 0]
  | .drop, [v], d => do
      let T ← T
      let n ← vty v
      let f := (T.field n 0).1
      let l := (T.field (T.field n 1).1 0).1
      return [.call [] (← helper (.arrDrop l f)) (locs (← vals v))] ++ (← emit d [])
  | .count, [v], d => do
      let T ← T
      let n ← vty v
      let f := (T.field n 0).1
      let s := (T.field (T.field (T.field n 1).1 1).1 1).1
      let ts ← fresh (T.words s)
      return [.call ts (← helper (.count f s)) (locs (← vals v))] ++ (← emit d (locs ts))
  | .countTry, [v], d => do
      let T ← T
      let n ← vty v
      let f := (T.field n 0).1
      let s := (T.field (T.field (T.field n 1).1 1).1 1).1
      let r ← match T.ty f with
        | .fn _ c _ => pure c
        | _ => throw "flat IR: count_try's step is not a closure"
      let ts ← fresh (T.words r)
      return [.call ts (← helper (.countTry f s)) (locs (← vals v))] ++ (← emit d (locs ts))
  | .io .readByte, [m], d => do
      let m := (← vals m).headD 0
      let b ← fresh1
      let t₀ ← fresh1
      let t₁ ← fresh1
      return [.set b (.getc (.load (.loc m) 0)),
        .ite (eq64 (.loc b) (.c64 0xFFFFFFFFFFFFFFFF))
          [.set t₀ (.c64 1), .set t₁ (.c64 0)] [.set t₀ (.c64 0), .set t₁ (.loc b)]] ++
        (← emit d [.loc m, .loc t₀, .loc t₁])
  | .io .writeByte, [p], d => do
      match ← vals p with
      | [m, b] => return [.putc (.load (.loc m) 0) (.loc b)] ++ (← emit d [.loc m])
      | _ => throw "flat IR: write_byte of a non-pair"
  | .io .writeAll, [p], d => do
      let T ← T
      let f := (T.field (← vty p) 1).1
      unless T.byteCell (T.field f 0).1 do throw "flat IR: write_all of a view whose slots are not bytes"
      match ← vals p with
      | [m, a, k] => return [.putv (.load (.loc m) 0) (.loc a) (.loc k)] ++ (← emit d [.loc m])
      | _ => throw "flat IR: write_all of a non-pair"
  | .io .clockNow, [m], d => do
      let m := (← vals m).headD 0
      let t ← fresh1
      return [.set t (.now (.loc m))] ++ (← emit d [.loc m, .loc t])
  | .io .clockSleep, [p], d => do
      match ← vals p with
      | [m, ns] => return [.sleep (.loc m) (.loc ns)] ++ (← emit d [.loc m])
      | _ => throw "flat IR: clock_sleep of a non-pair"
  | .io .readInto, [p], d => do
      let T ← T
      let f := (T.field (← vty p) 1).1
      unless T.byteCell (T.field f 0).1 do throw "flat IR: read_into of a view whose slots are not bytes"
      match ← vals p with
      | [m, a, k] =>
        let r ← fresh1
        return [.set r (.getv (.load (.loc m) 0) (.loc a) (.loc k))] ++
          (← emit d [.loc m, .loc a, .loc k, .loc r])
      | _ => throw "flat IR: read_into of a non-pair"
  | _, _, _ => throw "flat IR: primitive arity"

/-- Call the closure `f` on `a`, answering `k` words, of which the first `w` are the result. -/
def lowerCall (f a : Var) (k w : Nat) (d : Dest) : LM (List Stmt) := do
  let (g, args) ← callTarget (← vty f) (← vals f) (locs (← vals a)) ((← read).known[f]?)
  match d with
  | .ret k' => if k' == k then return (← releaseReuse) ++ [.tailCall g args] else pure ()
  | .to ls => if ls.length == k then return [.call ls g args] else pure ()
  | .bind _ => pure ()
  let ts ← fresh k
  return [.call ts g args] ++ (← emit d (locs (ts.take w)))

def lowerTm : Tm → Dest → LM (List Stmt)
  | .var x, d => do emit d (locs (← vals x))
  | .unit, d => emit d []
  | .lit (.i32 n), d => emit d [.c64 n.toUInt64]
  | .lit (.i64 n), d => emit d [.c64 n]
  | .lit (.u8 n), d => emit d [.c64 n.toUInt64]
  | .lit (.f32 n), d => emit d [.c64 n.toUInt64]
  | .lit (.f64 n), d => emit d [.c64 n]
  | .pair a b, d => do
      let some n := (← T).cons[a]? | throw "flat IR: an untyped pair"
      let (s, vs) ← mkPair n (locs (← vals a)) (locs (← vals b))
      return s ++ (← emit d vs)
  | .inj r a, d => do
      let some n := (← T).cons[a]? | throw "flat IR: an untyped injection"
      let (s, vs) ← mkInj n r (locs (← vals a))
      return s ++ (← emit d vs)
  | .con k _ a, d => do
      let some n := (← T).cons[a]? | throw "flat IR: an untyped variant"
      let (s, vs) ← mkCon n k (locs (← vals a))
      return s ++ (← emit d vs)
  | .clos c xs, d => do
      let (s, vs) ← closVals c (locs (← xs.mapM vals).flatten)
      return s ++ (← emit d vs)
  | .prim op xs, d => lowerPrim op xs d
  | .app f a, d => do
      let T ← T
      let some r := T.apps[f]? | throw "flat IR: an untyped call"
      lowerCall f a (T.answerWords (← vty f)) (T.words r) d
  | .letv x e@(.prim (.host o@(.div ..)) [p]) b@(.case s xq b₁ xu b₂), d =>
      if s != x then do
        let se ← lowerTm e (.bind x)
        return se ++ (← lowerTm b d)
      else do
      -- A `case` on a division's answer is the division's own test: the quotient in one arm,
      -- the other where Wasm traps (SPEC §39).
      let d ← match d with
        | .bind z => pure (.to (← bindFresh z))
        | d => pure d
      let (trapC, q) ← divTest o (← vals p)
      let t ← fresh1
      bindVals xq [t]
      let t₁ ← lowerTm b₁ d
      match trapC with
      | none => return [.set t q] ++ t₁
      | some c =>
        bindVals xu []
        let t₂ ← lowerTm b₂ d
        return [.ite c t₂ ([.set t q] ++ t₁)]
  | .letv x e@(.letv y e₁ (.prim (.host o@(.div ..)) [p])) b@(.case s xq b₁ xu b₂), d =>
      if s != x || p != y then do
        let se ← lowerTm e (.bind x)
        return se ++ (← lowerTm b d)
      else do
      -- The same, its operands' pair bound first.
      let se ← lowerTm e₁ (.bind y)
      let d ← match d with
        | .bind z => pure (.to (← bindFresh z))
        | d => pure d
      let (trapC, q) ← divTest o (← vals p)
      let t ← fresh1
      bindVals xq [t]
      let t₁ ← lowerTm b₁ d
      match trapC with
      | none => return se ++ [.set t q] ++ t₁
      | some c =>
        bindVals xu []
        let t₂ ← lowerTm b₂ d
        return se ++ [.ite c t₂ ([.set t q] ++ t₁)]
  | .letv x e b, d => do
      let se ← lowerTm e (.bind x)
      return se ++ (← lowerTm b d)
  | .letpair x y p b, d => do
      let (s, vx, vy) ← splitPair (← vty p) (← vals p) true
      bindVals x vx
      bindVals y vy
      return s ++ (← lowerTm b d)
  | .case s x b₁ y b₂, d => do
      -- Both arms write the same locals.
      let d ← match d with
        | .bind z => pure (.to (← bindFresh z))
        | d => pure d
      let n ← vty s
      let ls ← vals s
      let (s₁, v₁) ← payload n false ls true
      bindVals x v₁
      let t₁ ← lowerTm b₁ d
      let (s₂, v₂) ← payload n true ls true
      bindVals y v₂
      let t₂ ← lowerTm b₂ d
      -- A tag set to a constant where it was made selects its arm (SPEC §39).
      match (← get).consts.get? (ls.headD 0) with
      | some 0 => return s₁ ++ t₁
      | some _ => return s₂ ++ t₂
      | none => return [.ite (eqz64 (.loc (ls.headD 0))) (s₁ ++ t₁) (s₂ ++ t₂)]
  | .when s k _ x b r, d => do
      -- A chain of `when`s on `s` ending in `absurd` is a `switch` on its tag; one ending in
      -- another term is a compare of the tag per arm, then that term.
      let d ← match d with
        | .bind z => pure (.to (← bindFresh z))
        | d => pure d
      let n ← vty s
      let ls ← vals s
      let tag := Exp.loc (ls.headD 0)
      let (s₁, v) ← payloadN n k ls true
      bindVals x v
      let arm := s₁ ++ (← lowerTm b d)
      let rest ← lowerTm r d
      match r, rest with
      | .absurd _, _ =>
        return [.switch tag ((List.range (k + 1)).map fun j => if j == k then arm else [.trap]) [.trap]]
      | .when s' .., [.switch _ cases _] =>
        if s' == s then
          let cases := cases ++ List.replicate (k + 1 - cases.length) [.trap]
          return [.switch tag (cases.set k arm) [.trap]]
        else return [.ite (eq64 tag (.c64 k.toUInt64)) arm rest]
      | _, _ => return [.ite (eq64 tag (.c64 k.toUInt64)) arm rest]
  | .absurd _, d => do
      if let .bind z := d then discard (bindFresh z)
      return [.trap]
  | .copy x x' b, d => do
      let (s, ls) ← copyVals (← vty x) (← vals x)
      bindVals x' ls
      let tk : List Stmt := if s.isEmpty then [] else [.tickCopy]
      return tk ++ s ++ (← lowerTm b d)
  | .drop x b, d => do
      let s ← dropVals (← vty x) (← vals x)
      return s ++ (← lowerTm b d)
  | .raise _, _ | .hnd .., _ | .ubind .., _ | .perform _, _ | .catch .., _ | .fin .., _
  | .catchAll _, _ | .reraise .., _ | .run .., _ | .await .., _ =>
      throw "flat IR: an effect not lowered (`Capture`, `Unwind`)"

/-! ### Owned folds by pointer reversal

The step of `fold_own` or `fold_reuse` at a shape `T` (`FoldCode`) is
`λu. trav T (λw. self g w) u to r. g r`: it recurses into the child at `T`'s recursive
position, then calls the algebra `g` on the node with the child's result there. When `T` is
*linear* (a `⊗` has a recursive position on at most one side) and the node reaches its child
through exactly one pointer, the boxed field at `X` or the cell at `Ref X`, the step is two loops
of tail calls in constant stack (Deutsch–Schorr–Waite). The descent stores each node's words in
its child's object, with the pointer to the child replaced by the pointer to the node's own
object (`0` at the root), and goes on with the child. At a node with no child it calls `g`, and
the ascent loads each stored node back, calls `g` on it with the result at the recursive
position, and frees the object (`fold_own`, whose traversal frees it) or hands it to `g` as the
emptied cell (`fold_reuse`, `Ref 1 ⊗ R`). The object is the child's own, as wide as the node's
words, so the reversal allocates nothing; it is safe because the fold owns the structure: no
other word points into it while the pointers are reversed. -/

/-- The plan of a fold step: the node type `M`, the algebra's type, argument type and result
words, and the code's answer words. -/
structure FoldPlan where
  fc : FoldCode
  m : Nat
  g : Nat
  gVar : Var
  arg : Nat
  res : Nat
  ans : Nat

/-- `F` at the node-side type `n` and the algebra-side type `a` can be reversed: linear, with
the path to each recursive position inline but for its last step (`root` is `M`). -/
def dswOK (T : Types) (M : Nat) : FSh → Nat → Nat → Bool
  | .leaf, _, _ => true
  | .refX, n, _ => match T.ty n with | .loc .. => true | _ => false
  | .varX, _, _ => false
  | .tensor F G, n, a =>
    match T.ty n, T.ty a with
    | .pair .., .pair .. => !(F.hasX && G.hasX) && child F 0 n a && child G 1 n a
    | _, _ => false
  | .sum F G, n, a =>
    match T.ty n, T.ty a with
    | .sum .., .sum .. => child F 0 n a && child G 1 n a
    | _, _ => false
where
  child (F : FSh) (i n a : Nat) : Bool :=
    let (cn, b) := T.field n i
    let ca := (T.field a i).1
    match F with
    | .varX => b && T.r cn == T.r M
    | F => (!F.hasX || !b) && dswOK T M F cn ca

/-- The plan of code `k`'s fold step, when it can be reversed. -/
def foldPlan? (k : Nat) (c : Code) : LM (Option FoldPlan) := do
  let some fc := (← read).folds[k]? | return none
  let T ← T
  let some gVar := c.env[fc.alg]? | return none
  let m := T.r (← vty c.param)
  let g := T.r (← vty gVar)
  let .fn arg rc _ := T.ty g | return none
  let ans := T.answerWords (T.codeType k)
  let res := T.words rc
  if T.answerWords g != res || ans != res then return none
  if !fc.shape.hasX || !dswOK T m fc.shape m arg then return none
  if fc.reuse then
    -- `fold_reuse` has no `X` position, only `Ref X`.
    let rec noVar : FSh → Bool
      | .varX => false
      | .tensor F G | .sum F G => noVar F && noVar G
      | _ => true
    if !noVar fc.shape then return none
  return some ⟨fc, m, g, gVar, T.r arg, res, ans⟩

/-- The code calling the algebra is known when the flow analysis finds one code at the step's
own call of `g`. -/
def algKnown (c : Code) (g : Nat) : LM (Option Nat) := do
  let T ← T
  let ctx ← read
  let calls := callsOf c.body
  return calls.findSome? fun f =>
    if T.r (T.varTy.getD f 0) == g then ctx.known[f]? else none
where
  callsOf : Tm → List Var
    | .app f _ => [f]
    | .letv _ e b => callsOf e ++ callsOf b
    | .letpair _ _ _ b | .copy _ _ b | .drop _ b => callsOf b
    | .case _ _ b₁ _ b₂ => callsOf b₁ ++ callsOf b₂
    | _ => []

/-- `act j` at the recursive position of the node of type `n` in the locals `ls`, `j` the local
holding the pointer to the child's object; `none` at a node with no child. -/
def atSlot (F : FSh) (n : Nat) (ls : List Nat) (act : Option Nat → LM (List Stmt)) :
    LM (List Stmt) := do
  let T ← T
  let sub (Fi : FSh) (i : Nat) (rec : List Nat → LM (List Stmt)) : LM (List Stmt) := do
    if !Fi.hasX then act none else
    let li ← fieldLocals n i ls
    if let .varX := Fi then act li.head? else rec li
  match F with
  | .refX => act ls.head?
  | .tensor F₀ F₁ =>
    if F₀.hasX then sub F₀ 0 fun li => atSlot F₀ (T.field n 0).1 li act
    else sub F₁ 1 fun li => atSlot F₁ (T.field n 1).1 li act
  | .sum F₀ F₁ =>
    return [.ite (eqz64 (.loc (ls.headD 0)))
      (← sub F₀ 0 fun li => atSlot F₀ (T.field n 0).1 li act)
      (← sub F₁ 1 fun li => atSlot F₁ (T.field n 1).1 li act)]
  | _ => act none

/-- Field `i` of the algebra's argument of type `a`, from field `i` of the node of type `n` in the
locals `ls`: the words `r` at a recursive position `X`, and otherwise `rec` of the field's
words. -/
def argField (Fi : FSh) (n a i : Nat) (ls : List Nat) (r : Option (List Exp))
    (rec : List Nat → LM (List Stmt × List Exp)) : LM (List Stmt × List Exp) := do
  let T ← T
  let li ← fieldLocals n i ls
  match Fi, r with
  | .varX, none => pure ([.trap], zeros (T.fieldWords a i))
  | .varX, some r => putField a i r
  | _, _ =>
    let (s₁, vs) ← getField n i li true
    let (s₂, w) ← rec vs
    let wl ← fresh w.length
    let s₃ ← emit (.to wl) w
    let (s₄, w) ← putField a i (locs wl)
    pure (s₁ ++ s₂ ++ s₃ ++ s₄, w)

/-- The algebra's argument, of type `a`, built from the node of type `n` in the locals `ls`
(consumed) with the words `r` at the recursive position and `cell` the emptied cell there
(`fold_reuse`). With `r = none` the recursive position is not reached. -/
def buildArg (reuse : Bool) (F : FSh) (n a : Nat) (ls : List Nat) (r : Option (List Exp))
    (cell : Exp) : LM (List Stmt × List Exp) := do
  let T ← T
  let rec' (Fi : FSh) (i : Nat) (go : Nat → Nat → List Nat → LM (List Stmt × List Exp)) :=
    argField Fi n a i ls r (go (T.field n i).1 (T.field a i).1)
  match F with
  | .leaf => pure ([], locs ls)
  | .refX | .varX =>
    match r with
    | none => pure ([.trap], zeros (T.words a))
    | some r => if reuse then mkPair a [cell] r else pure ([], r)
  | .tensor F₀ F₁ =>
    let (s₀, w₀) ← rec' F₀ 0 fun n a ls => buildArg reuse F₀ n a ls r cell
    let (s₁, w₁) ← rec' F₁ 1 fun n a ls => buildArg reuse F₁ n a ls r cell
    let (s₂, w) ← mkPair a w₀ w₁
    pure (s₀ ++ s₁ ++ s₂, w)
  | .sum F₀ F₁ =>
    let dst ← fresh (T.words a)
    let (s₀, w₀) ← rec' F₀ 0 fun n a ls => buildArg reuse F₀ n a ls r cell
    let (s₀', v₀) ← mkInj a false w₀
    let (s₁, w₁) ← rec' F₁ 1 fun n a ls => buildArg reuse F₁ n a ls r cell
    let (s₁', v₁) ← mkInj a true w₁
    return ([.ite (eqz64 (.loc (ls.headD 0))) (s₀ ++ s₀' ++ (← emit (.to dst) v₀))
      (s₁ ++ s₁' ++ (← emit (.to dst) v₁))], locs dst)

/-- Call a copy of the algebra (in the locals `gl`) on `arg`; its result's words. -/
def callAlg (P : FoldPlan) (known : Option Nat) (gl : List Nat) (arg : List Exp) :
    LM (List Stmt × List Nat) := do
  let (cs, gc) ← copyVals P.g gl
  let (f, as) ← callTarget P.g gc arg known
  let rs ← fresh ((← T).answerWords P.g)
  pure (cs ++ [.call rs f as], rs.take P.res)

/-- The descent: `g`, the stored parent `up`, the node's words. -/
def foldDownFn (k : Nat) (c : Code) (P : FoldPlan) : LM Fn := do
  let T ← T
  let gw := T.words P.g
  let mw := T.words P.m
  let known ← algKnown c P.g
  let (body, nloc) ← inFn (gw + 1 + mw) do
    let gl := List.range gw
    let up := gw
    let node := List.range' (gw + 1) mw
    atSlot P.fc.shape P.m node fun
      | some j => do
        let p ← fresh1
        let (ld, child) ← loadAt (.loc p) 0 mw
        pure ([.set p (.loc j)] ++ ld ++ [.set j (.loc up)] ++ storeAt (.loc p) 0 (locs node) ++
          [.tailCall (← helper (.foldDown k)) (locs gl ++ [.loc p] ++ locs child)])
      | none => do
        let (sa, arg) ← buildArg P.fc.reuse P.fc.shape P.m P.arg node none (.c64 0)
        let (sc, rs) ← callAlg P known gl arg
        pure (sa ++ sc ++ [.tailCall (← helper (.foldUp k)) (locs gl ++ [.loc up] ++ locs rs)])
  pure { name := s!"fold_down{k}", params := gw + 1 + mw, results := P.ans, locals := nloc,
         body := body ++ [.trap] }

/-- The ascent: `g`, the stored node `up` (`0` past the root), the child's result. -/
def foldUpFn (k : Nat) (c : Code) (P : FoldPlan) : LM Fn := do
  let T ← T
  let gw := T.words P.g
  let mw := T.words P.m
  let known ← algKnown c P.g
  let (body, nloc) ← inFn (gw + 1 + P.res) do
    let gl := List.range gw
    let up := Exp.loc gw
    let r := locs (List.range' (gw + 1) P.res)
    let (ld, node) ← loadAt up 0 mw
    let step ← atSlot P.fc.shape P.m node fun
      | some j => do
        let next ← fresh1
        let (sa, arg) ← buildArg P.fc.reuse P.fc.shape P.m P.arg node (some r) up
        let (sc, rs) ← callAlg P known gl arg
        pure ([.set next (.loc j)] ++ sa ++ (if P.fc.reuse then [] else [.free up]) ++ sc ++
          [.tailCall (← helper (.foldUp k)) (locs gl ++ [.loc next] ++ locs rs)])
      | none => pure [.trap]
    pure [.ite (eqz64 up) ((← dropVals P.g gl) ++ [.ret r]) (ld ++ step)]
  pure { name := s!"fold_up{k}", params := gw + 1 + P.res, results := P.ans, locals := nloc,
         body := body ++ [.trap] }

/-! ### Codes, `main` and the entry -/

/-- The words a closure's environment holds, per captured variable. -/
def envWords (c : Code) : LM (List Nat) := c.env.mapM fun x => do words (← vty x)

/-- Code `k` as a function of its captured values' words and the argument's words, answering its
type's `answerWords`. At a recursive closure type it takes the closure's word instead of the
captured values, loads the environment and frees the object. A `sel` code's `case` on the
parameter returns each arm at its own type, padded to the wider. -/
def lowerCode (k : Nat) (c : Code) : LM Fn := do
  let T ← T
  if !(← read).live.contains k then
    -- No closure of this code is built: a stub keeps the function indices.
    return { name := s!"code{k}", params := 0, results := 0, locals := 0, body := [.trap] }
  if let some P ← foldPlan? k c then
    -- An owned fold's step by pointer reversal: the descent from the node `u`.
    let ew := T.envWords k
    let pw := T.words P.m
    let (body, nloc) ← inFn (ew + pw) do
      let mut off := 0
      let mut drops : List Stmt := []
      let mut gl : List Nat := []
      for x in c.env do
        let w ← words (← vty x)
        if x == P.gVar then gl := List.range' off w
        else drops := drops ++ (← dropVals (← vty x) (List.range' off w))
        off := off + w
      pure (drops ++ [.tailCall (← helper (.foldDown k))
        (locs gl ++ [.c64 0] ++ locs (List.range' ew pw))])
    return { name := s!"code{k}", params := ew + pw, results := P.ans, locals := nloc, body }
  let fTy := T.codeTy[k]!
  let (aTy, ans) := match T.ty fTy with
    | .fn a _ _ => (a, T.answerWords fTy)
    | _ => (fTy, 0)
  let pw ← words aTy
  if T.isRec fTy then
    let (body, nloc, frame) ← inFnF (1 + pw) do
      bindVals c.param (List.range' 1 pw)
      let mut unpack : List Stmt := []
      let mut off := 1
      for x in c.env do
        let (s, ls) ← loadAt (.loc 0) off (← words (← vty x))
        bindVals x ls
        unpack := unpack ++ s
        off := off + ls.length
      -- The environment object is reused or freed on each path (`reuseOrAlloc`).
      if !c.env.isEmpty then modify fun st => { st with reuse := some (0, off) }
      let body ← lowerTm c.body (.ret ans)
      pure (unpack ++ body ++ [.trap])
    return { name := s!"code{k}", params := 1 + pw, results := ans, locals := nloc, frame, body }
  let ew := T.envWords k
  let (body, nloc, frame) ← inFnF (ew + pw) do
    let mut off := 0
    for x in c.env do
      let w ← words (← vty x)
      bindVals x (List.range' off w)
      off := off + w
    bindVals c.param (List.range' ew pw)
    pure ((← lowerTm c.body (.ret ans)) ++ [.trap])
  pure { name := s!"code{k}", params := ew + pw, results := ans, locals := nloc, frame, body }

def lowerMain (t : Tm) : LM Fn := do
  let k ← words (← T).mainTy
  let (body, nloc, frame) ← inFnF 0 do
    pure ((← lowerTm t (.ret k)) ++ [.trap])
  pure { name := "main", params := 0, results := k, locals := nloc, frame, body }

/-- The counts of a run, written after the report when they are asked for: allocations,
indirect (dispatched) calls, and copies of a variable at a non-trivial type. -/
def countsReport : List Stmt :=
  outStr "allocs " ++ [.call [] fPrintDec [.stat 0]] ++ outStr "\nindirect " ++
    [.call [] fPrintDec [.stat 1]] ++ outStr "\ncopies " ++
    [.call [] fPrintDec [.stat 2]] ++ outStr "\n"

/-- Run `main` (driving it and running the code `fin` on what it finishes with, when it returns
a loop), print the value, drop it, print the live count, and with `counts` the run's counts. With
`exits`, `main`'s value is `inl v`, whose `v` is printed, or `inr ()`, which prints nothing and
ends the run with exit status `1` (SPEC §39). -/
def entryFn (fMain : Nat) (fin : Option Nat) (counts : Bool) (exits : Bool := false) : LM Fn := do
  let T ← T
  let (body, nloc) ← inFn 0 do
    let m ← fresh (T.words T.mainTy)
    let (run, v) ← match fin with
      | none => pure ([Stmt.call m fMain []], m)
      | some c => do
        let r := match T.ty T.mainTy with
          | .fn _ c _ => match T.ty c with | .sum r _ => r | _ => c
          | _ => T.mainTy
        let rs ← fresh (T.words r)
        let es ← fresh (T.answerWords T.codeTy[c]!)
        -- `fin` captures nothing.
        let (_, fv) ← closVals c []
        let self := if T.isRec (T.codeType c) then fv.take 1 else []
        pure ([Stmt.call m fMain [], .call rs (← helper (.drive T.mainTy)) (locs m),
          .call es (codeFn c) (self ++ locs rs)], es.take (T.words T.resTy))
    let dr ← dropVals T.resTy v
    let (shown, status) ← if exits then do
        let .sum .. := T.ty T.resTy | throw "flat IR: `main`'s value is not `inl v` or `inr ()`"
        let tag := Exp.loc (v.headD 0)
        let (c, _) := T.field T.resTy 0
        let (sg, vs) ← getField T.resTy 0 (← fieldLocals T.resTy 0 v) false
        let pr := sg ++ [Stmt.call [] (← helper (.print c)) (locs vs)]
        pure ([Stmt.ite (eqz64 tag) (pr ++ outStr "\n") []], [Stmt.ite (eqz64 tag) [] [.status (.c64 1)]])
      else pure ([.call [] (← helper (.print T.resTy)) (locs v)] ++ outStr "\n", [])
    pure (run ++ shown ++ dr ++
      outStr "live " ++ [.call [] fPrintDec [.live]] ++ outStr "\n" ++
      (if counts then countsReport else []) ++ status ++ [.ret []])
  pure { name := "entry", params := 0, results := 0, locals := nloc, body }

/-- `printDec n`: `n` in unsigned decimal. -/
def printDecFn : Fn where
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

/-! ### Helpers -/

/-- A copy of field `i` of `n`, from the field's locals. -/
def copyField (n i : Nat) (ls : List Nat) : LM (List Stmt × List Exp) := do
  let (c, _) := (← T).field n i
  let (s₁, vs) ← getField n i ls false
  let (s₂, vs) ← copyVals c vs
  let (s₃, out) ← putField n i (locs vs)
  pure (s₁ ++ s₂ ++ s₃, out)

/-- Drop field `i` of `n`, from the field's locals. -/
def dropField (n i : Nat) (ls : List Nat) : LM (List Stmt) := do
  let (c, _) := (← T).field n i
  let (s₁, vs) ← getField n i ls true
  pure (s₁ ++ (← dropVals c vs))

/-- Print field `i` of `n`; as an `atom` (the operand of `inl`/`inr`), an injection is
parenthesized. -/
def printField (n i : Nat) (ls : List Nat) (atom : Bool) : LM (List Stmt) := do
  let T ← T
  let (c, _) := T.field n i
  let (s, vs) ← getField n i ls false
  let call := [Stmt.call [] (← helper (.print c)) (locs vs)]
  match T.ty c, atom with
  | .sum .., true => pure (s ++ outStr "(" ++ call ++ outStr ")")
  | _, _ => pure (s ++ call)

/-- Split a closure's type: argument, answer type on an unknown argument, answer words. -/
def fnParts (f : Nat) : LM (Nat × Nat × Nat) := do
  let T ← T
  match T.ty f with
  | .fn a c _ => pure (a, c, T.answerWords f)
  | _ => throw "flat IR: not a closure type"

def genHelper (h : Helper) : LM Fn := do
  let T ← T
  match h with
  | .copy n =>
    let w := T.words n
    let (body, nloc) ← inFn w do
      let ps := List.range w
      match T.ty n with
      | .fn .. => do
        if T.isRec n then
          let t ← fresh1
          onCode n ps [.ret [.loc 0]] fun c => do
            if (T.env c).isEmpty then return [.trap]
            return [.call [t] (← helper (.closCopy c)) [.loc 0], .ret [.loc t]]
        else
          onCode n ps [] fun c => do
            let mut s : List Stmt := []
            let mut out : List Nat := []
            let mut off := 1
            for e in T.env c do
              let (s₁, ls) ← copyVals e (List.range' off (T.words e))
              s := s ++ s₁
              out := out ++ ls
              off := off + T.words e
            return s ++ [.ret ([.loc 0] ++ locs out ++ zeros (w - 1 - out.length))]
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
      | .sumN fs => do
        let cases ← (List.range fs.length).mapM fun k => do
          let (s₁, a) ← copyField n k (← fieldLocals n k ps)
          pure (s₁ ++ [.ret ([.c64 k.toUInt64] ++ a ++ zeros (w - 1 - a.length))])
        pure [.switch (.loc 0) cases [.trap]]
      | _ => pure [.ret (locs ps)]
    pure { name := "copy", params := w, results := w, locals := nloc, body := body ++ [.trap] }
  | .drop n =>
    let w := T.words n
    let (body, nloc) ← inFn w do
      let ps := List.range w
      match T.ty n with
      | .fn .. => do
        let s ← onCode n ps [] fun c => do
          if T.isRec n then
            if (T.env c).isEmpty then return [.trap]
            return [.call [] (← helper (.closDrop c)) [.loc 0]]
          let mut s : List Stmt := []
          let mut off := 1
          for e in T.env c do
            s := s ++ (← dropVals e (List.range' off (T.words e)))
            off := off + T.words e
          return s
        pure (s ++ [.ret []])
      | .pair .. => do
        pure ((← dropField n 0 (← fieldLocals n 0 ps)) ++ (← dropField n 1 (← fieldLocals n 1 ps)) ++
          [.ret []])
      | .sum .. => do
        pure [.ite (eqz64 (.loc 0)) (← dropField n 0 (← fieldLocals n 0 ps))
          (← dropField n 1 (← fieldLocals n 1 ps)), .ret []]
      | .sumN fs => do
        let cases ← (List.range fs.length).mapM fun k => do dropField n k (← fieldLocals n k ps)
        pure [.switch (.loc 0) cases [.trap], .ret []]
      | _ => pure [.ret []]
    pure { name := "drop", params := w, results := 0, locals := nloc, body }
  | .print n =>
    let w := T.words n
    let (body, nloc) ← inFn w do
      let ps := List.range w
      match T.ty n with
      | .any => pure [.trap]
      | .unit => pure (outStr "()")
      | .int .w32 => pure (outStr "i32[" ++ [.call [] fPrintDec [.loc 0]] ++ outStr "]")
      | .int .w64 => pure (outStr "i64[" ++ [.call [] fPrintDec [.loc 0]] ++ outStr "]")
      | .int .w8 => pure (outStr "u8[" ++ [.call [] fPrintDec [.loc 0]] ++ outStr "]")
      | .int .f32 => pure (outStr "f32[" ++ [.call [] fPrintDec [.loc 0]] ++ outStr "]")
      | .int .f64 => pure (outStr "f64[" ++ [.call [] fPrintDec [.loc 0]] ++ outStr "]")
      | .fn .. => pure (outStr "<fun>")
      | .loc .. => pure (outStr "<loc>")
      | .pair .. => do
        pure (outStr "(" ++ (← printField n 0 (← fieldLocals n 0 ps) false) ++ outStr ", " ++
          (← printField n 1 (← fieldLocals n 1 ps) false) ++ outStr ")")
      | .sum .. => do
        pure [.ite (eqz64 (.loc 0)) (outStr "inl " ++ (← printField n 0 (← fieldLocals n 0 ps) true))
          (outStr "inr " ++ (← printField n 1 (← fieldLocals n 1 ps) true))]
      -- A suspended computation's state or an operation's payload is never a program's value.
      | .sumN _ => pure [.trap]
    pure { name := "print", params := w, results := 0, locals := nloc, body := body ++ [.ret []] }
  | .closCopy c =>
    let some code := (← read).codes[c]? | throw "flat IR: no code"
    let (body, nloc) ← inFn 1 do
      let ws ← envWords code
      let t ← fresh1
      let mut s : List Stmt := [.set t (.alloc (.c64 (1 + ws.sum).toUInt64)),
        .store (.loc t) 0 (.load (.loc 0) 0)]
      let mut off := 1
      for x in code.env do
        let n ← vty x
        let (s₁, ls) ← loadAt (.loc 0) off (← words n)
        let (s₂, ls) ← copyVals n ls
        s := s ++ s₁ ++ s₂ ++ storeAt (.loc t) off (locs ls)
        off := off + ls.length
      pure (s ++ [.ret [.loc t]])
    pure { name := s!"copy_code{c}", params := 1, results := 1, locals := nloc, body }
  | .closDrop c =>
    let some code := (← read).codes[c]? | throw "flat IR: no code"
    let (body, nloc) ← inFn 1 do
      let mut s : List Stmt := []
      let mut off := 1
      for x in code.env do
        let n ← vty x
        let w ← words n
        if !(← triv n) then
          let (s₁, ls) ← loadAt (.loc 0) off w
          s := s ++ s₁ ++ (← dropVals n ls)
        off := off + w
      pure (s ++ [.free (.loc 0), .ret []])
    pure { name := s!"drop_code{c}", params := 1, results := 0, locals := nloc, body }
  | .tab a f =>
    -- `tab (c, f)`: `len(c)` slots of `|a|` words (a byte each for a byte slot), filled by
    -- `f i` in order. An empty array allocates nothing: its base is `0`.
    let fw := T.words f
    let (body, nloc) ← inFn (1 + fw) do
      let n := Exp.loc 0
      let fls := List.range' 1 fw
      let sz ← fresh1
      let b ← fresh1
      let loop ← helper (.tabLoop a f)
      let dr ← dropVals f fls
      let words : Exp := if T.byteCell a then shr64 (add64 n (.c64 7)) (.c64 3)
        else mul64 n (.c64 (T.cellWords a).toUInt64)
      pure ([.ite (ltu64 n (.c64 0x80000000)) [] [.set 0 (.c64 0)],
        .set sz words,
        .ite (eqz64 (.loc sz)) [.set b (.c64 0)] [.set b (.alloc (.loc sz))],
        .call [] loop ([.loc b] ++ locs fls ++ [.c64 0, n])] ++ dr ++ [.ret [.loc b, n]])
    pure { name := "array_tab", params := 1 + fw, results := 2, locals := nloc, body }
  | .tabLoop a f =>
    -- `b f i n`: slot `i` gets a copy of `f` applied to `i`, for `i < n`.
    let (_, _, k) ← fnParts f
    let w ← words (← locElem a)
    let fw := T.words f
    let fls := List.range' 1 fw
    let i := Exp.loc (1 + fw)
    let n := Exp.loc (2 + fw)
    let (body, nloc) ← inFn (3 + fw) do
      let (cs, fc) ← copyVals f fls
      let rs ← fresh k
      let slot := add64 (.loc 0) (mul64 i (.c64 (slotBytes T a).toUInt64))
      pure [.ite (ltu64 i n)
        (cs ++ (← callClosure rs f fc [i]) ++
          (← storeCell a slot (locs (rs.take w))) ++
          [.tailCall (← helper (.tabLoop a f)) ([.loc 0] ++ locs fls ++ [add64 i (.c64 1), n])])
        [], .ret []]
    pure { name := "array_tab_loop", params := 3 + fw, results := 0, locals := nloc, body }
  | .arrDrop a f =>
    -- `f b n`: each element to a copy of `f`, in order, then the range freed.
    let fw := T.words f
    let fls := List.range fw
    let (body, nloc) ← inFn (fw + 2) do
      pure ([.call [] (← helper (.arrDropLoop a f))
          ([.loc fw] ++ locs fls ++ [.c64 0, .loc (fw + 1)])] ++
        (← dropVals f fls) ++
        -- An empty array, and an array of slots of no words, allocated nothing.
        (if T.cellWords a == 0 && !T.byteCell a then [] else
          [.ite (eqz64 (.loc (fw + 1))) [] [.free (.loc fw)]]) ++ [.ret []])
    pure { name := "array_drop", params := fw + 2, results := 0, locals := nloc, body }
  | .arrDropLoop a f =>
    -- `b f i n`: slot `i`'s contents, moved out, to a copy of `f`, for `i < n`.
    let (_, r, k) ← fnParts f
    let w ← words (← locElem a)
    let fw := T.words f
    let fls := List.range' 1 fw
    let i := Exp.loc (1 + fw)
    let n := Exp.loc (2 + fw)
    let (body, nloc) ← inFn (3 + fw) do
      let (cs, fc) ← copyVals f fls
      let slot := add64 (.loc 0) (mul64 i (.c64 (slotBytes T a).toUInt64))
      let (ls, es) ← loadCell a slot w
      let rs ← fresh k
      pure [.ite (ltu64 i n)
        (cs ++ ls ++ (← callClosure rs f fc (locs es)) ++
          (← dropVals r (rs.take (T.words r))) ++
          [.tailCall (← helper (.arrDropLoop a f)) ([.loc 0] ++ locs fls ++ [add64 i (.c64 1), n])])
        [], .ret []]
    pure { name := "array_drop_loop", params := 3 + fw, results := 0, locals := nloc, body }
  | .count f s =>
    -- `count (f, (n, (i, s)))`: `len(n)`, the loop, then `f` dropped.
    let fw := T.words f
    let sw := T.words s
    let (body, nloc) ← inFn (fw + 2 + sw) do
      let fls := List.range fw
      let n := Exp.loc fw
      let rs ← fresh sw
      pure ([.ite (ltu64 n (.c64 0x80000000)) [] [.set fw (.c64 0)],
        .call rs (← helper (.countLoop f s)) (locs (List.range (fw + 2 + sw)))] ++
        (← dropVals f fls) ++ [.ret (locs rs)])
    pure { name := "count", params := fw + 2 + sw, results := sw, locals := nloc, body }
  | .countLoop f s =>
    -- `f n i s`: while `i < n`, the state goes to a copy of `f` with `i`.
    let (a, _, k) ← fnParts f
    let fw := T.words f
    let sw := T.words s
    let fls := List.range fw
    let n := Exp.loc fw
    let i := Exp.loc (fw + 1)
    let sls := List.range' (fw + 2) sw
    let (body, nloc) ← inFn (fw + 2 + sw) do
      let (cs, fc) ← copyVals f fls
      let (ps, arg) ← mkPair a [i] (locs sls)
      let rs ← fresh k
      pure [.ite (ltu64 i n)
        (cs ++ ps ++ (← callClosure rs f fc arg) ++
          [.tailCall (← helper (.countLoop f s))
            (locs fls ++ [n, add64 i (.c64 1)] ++ locs (rs.take sw))])
        [.ret (locs sls)]]
    pure { name := "count_loop", params := fw + 2 + sw, results := sw, locals := nloc,
           body := body ++ [.trap] }
  | .countTry f s =>
    -- `count_try (f, (n, (i, s)))`: `len(n)`, the loop, then `f` dropped.
    let (_, r, _) ← fnParts f
    let fw := T.words f
    let sw := T.words s
    let rw := T.words r
    let (body, nloc) ← inFn (fw + 2 + sw) do
      let fls := List.range fw
      let n := Exp.loc fw
      let rs ← fresh rw
      pure ([.ite (ltu64 n (.c64 0x80000000)) [] [.set fw (.c64 0)],
        .call rs (← helper (.countTryLoop f s)) (locs (List.range (fw + 2 + sw)))] ++
        (← dropVals f fls) ++ [.ret (locs rs)])
    pure { name := "count_try", params := fw + 2 + sw, results := rw, locals := nloc, body }
  | .countTryLoop f s =>
    -- `f n i s`: while `i < n`, the state goes to a copy of `f` with `i`; its `inl` goes on, its
    -- `inr` is the answer; at the bound, `inl` of the state.
    let (a, r, k) ← fnParts f
    let fw := T.words f
    let sw := T.words s
    let rw := T.words r
    let fls := List.range fw
    let n := Exp.loc fw
    let i := Exp.loc (fw + 1)
    let sls := List.range' (fw + 2) sw
    let (body, nloc) ← inFn (fw + 2 + sw) do
      let (cs, fc) ← copyVals f fls
      let (ps, arg) ← mkPair a [i] (locs sls)
      let rs ← fresh k
      let (s₁, sv) ← payload r false (rs.take rw) true
      let (s₀, ev) ← mkInj r false (locs sls)
      pure [.ite (ltu64 i n)
        (cs ++ ps ++ (← callClosure rs f fc arg) ++
          [.ite (eqz64 (.loc (rs.headD 0)))
            (s₁ ++ [.tailCall (← helper (.countTryLoop f s))
              (locs fls ++ [n, add64 i (.c64 1)] ++ locs (sv.take sw))])
            [.ret (locs (rs.take rw))]])
        (s₀ ++ [.ret ev])]
    pure { name := "count_try_loop", params := fw + 2 + sw, results := rw, locals := nloc,
           body := body ++ [.trap] }
  | .drive n =>
    -- `d`: call `d` on `inl ()` until it answers `inl r`; `inr d'` goes on with `d'`.
    let (a, c, k) ← fnParts n
    let r := (T.field c 0).1
    let nw := T.words n
    let (body, nloc) ← inFn nw do
      let (s₀, sel) ← mkInj a false []
      let rs ← fresh k
      let cv := rs.take (T.words c)
      let (s₁, rv) ← payload c false cv true
      let (s₂, dv) ← payload c true cv true
      let (g, as) ← callTarget n (List.range nw) sel (← read).driveKnown
      pure (s₀ ++ [.call rs g as] ++ [
        .ite (eqz64 (.loc (cv.headD 0))) (s₁ ++ [.ret (locs rv)])
          (s₂ ++ [.tailCall (← helper (.drive n)) (locs dv)])])
    pure { name := "drive", params := nw, results := T.words r, locals := nloc, body := body ++ [.trap] }
  | .foldDown k | .foldUp k =>
    let some c := (← read).codes[k]? | throw "flat IR: no code"
    let some P ← foldPlan? k c | throw "flat IR: not a reversible fold"
    match h with
    | .foldDown _ => foldDownFn k c P
    | _ => foldUpFn k c P
  | .apply n =>
    -- A dispatched call: a `switch` on the closure's tag, each case a tail call of its code.
    let (a, _, k) ← fnParts n
    let nw := T.words n
    let aw := T.words a
    let args := locs (List.range' nw aw)
    let (body, nloc) ← inFn (nw + aw) do
      let f := Exp.loc 0
      let t ← fresh1
      let tagOf : List Stmt := if T.isRec n then
          [.ite (wrap (and64 f (.c64 1))) [.set t (shr64 f (.c64 1))] [.set t (.load f 0)]]
        else [.set t f]
      let cases := (T.union n).toList.map fun c =>
        if T.isRec n then [Stmt.tailCall (codeFn c) (f :: args)]
        else [.tailCall (codeFn c) (locs (List.range' 1 (T.envWords c)) ++ args)]
      pure ([.tick] ++ tagOf ++ [.switch (.loc t) cases [.trap]])
    pure { name := "apply", params := nw + aw, results := k, locals := nloc, body := body ++ [.trap] }

/-- The closure calls of a term, by their function variables. -/
def callsOf : Tm → List Var
  | .app f _ => [f]
  | .letv _ e b => callsOf e ++ callsOf b
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b => callsOf b
  | .case _ _ b₁ _ b₂ | .when _ _ _ _ b₁ b₂ => callsOf b₁ ++ callsOf b₂
  | _ => []

/-- The calls whose code is known, by their function variable: the flow analysis's codes there
that are in the union of the call's closure type are one. Each analysis over-approximates the
codes that reach the call, so their intersection does. -/
def knownCallsOf (T : Types) (flow : Std.HashMap Var (Array Nat)) : Std.HashMap Var Nat :=
  flow.fold (fun m f cs =>
    let u := T.union (T.varTy.getD f 0)
    match cs.filter u.contains with
    | #[c] => m.insert f c
    | _ => m) {}

/-- `knownCallsOf` at the program's types and flow. -/
def knownCalls (p : Clos.Prog) : Std.HashMap Var Nat :=
  match p.types with
  | .error _ => {}
  | .ok T => knownCallsOf T p.flow

/-- The program's closure calls: how many there are, how many call the one code of their type's
union, and how many more a code the flow analysis finds. The rest are dispatched. -/
def callSites (p : Clos.Prog) : Except String (Nat × Nat × Nat) := do
  let T ← p.types
  let known := knownCalls p
  let live := p.liveCodes
  let calls := (p.codes.toList.zipIdx.flatMap fun (c, k) =>
    if live.contains k then callsOf c.body else []) ++ callsOf p.main
  let mut byType := 0
  let mut byFlow := 0
  for f in calls do
    let u := T.union (T.varTy.getD f 0)
    if u.size == 1 then byType := byType + 1
    else if (known[f]?.map u.contains).getD false then byFlow := byFlow + 1
  return (calls.length, byType, byFlow)

/-- The program's owned folds: how many are compiled by pointer reversal, and how many recurse. -/
def foldSites (p : Clos.Prog) : Except String (Nat × Nat) := do
  let T ← p.types
  let ctx : Ctx := { T, codes := p.codes, known := knownCalls p, helperBase := 0,
                     folds := p.folds.foldl (fun m f => m.insert f.code f) {} }
  let act : LM Nat := p.folds.foldlM (fun k f => do
    let some c := p.codes[f.code]? | pure k
    pure (if (← foldPlan? f.code c).isSome then k + 1 else k)) 0
  let (n, _) ← (act.run ctx).run {}
  pure (n, p.folds.length - n)

/-! ### Frame slots  `[spec §35]`

A scoped cell (`Backend.Clos.Op.scopedAlloc`) lives from its `alloc` to its scope's `free`. When
no resumption point of its code lies between them (`Clos.Prog.suspendedScopes`), the cell's life
is inside one call of the code that holds both: a flat-IR function has no loop, a code that may
suspend is copied whole into its resume code where it resumes (`Capture`), and a raise returns
with the cell dropped. Such a cell is a slot of the code's frame (`Exp.slot`), as C and Rust place
a local whose address is taken: no allocation and no live range. A scoped cell whose scope a
suspension crosses is allocated: its address is held in the suspended computation's state, which
outlives the frame. -/

/-- The scoped cells' operations in `t`: each scope's `alloc`s and `free`s. -/
def scopesOf : Tm → List (Nat × Bool)
  | .prim (.scopedAlloc k) _ => [(k, true)]
  | .prim (.scopedFree k) _ => [(k, false)]
  | .letv _ e b => scopesOf e ++ scopesOf b
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b | .catch _ b | .fin _ _ b | .catchAll b
  | .hnd _ _ _ b | .ubind _ _ b => scopesOf b
  | .case _ _ b₁ _ b₂ | .when _ _ _ _ b₁ b₂ => scopesOf b₁ ++ scopesOf b₂
  | _ => []

/-- The scopes whose cells are frame slots: those no suspension crosses. -/
def frameScopes (p : Clos.Prog) : Std.HashSet Nat :=
  let all := (p.main :: p.codes.toList.map (·.body)).flatMap scopesOf
  all.foldl (fun s (k, _) => if p.suspendedScopes.contains k then s else s.insert k) {}

/-- The program's scoped cells: how many are frame slots, and how many are allocated. -/
def scopeSites (p : Clos.Prog) : Nat × Nat :=
  let all := (p.main :: p.codes.toList.map (·.body)).flatMap scopesOf |>.filterMap
    fun (k, a) => if a then some k else none
  let fs := frameScopes p
  let framed := all.filter fs.contains
  (framed.length, all.length - framed.length)

/-- The flat IR of `p`; `types` are `p`'s layout types when they are known already. -/
def lower (p : Clos.Prog) (counts : Bool := false) (types : Option Types := none) :
    Except String Prog := do
  let T ← match types with
    | some T => pure T
    | none => p.types
  let nc := p.codes.size
  let fMain := codeFn nc
  let (flow, drive) := p.flowAll
  let ctx : Ctx := { T, codes := p.codes, known := knownCallsOf T flow, helperBase := fMain + 2,
                     folds := p.folds.foldl (fun m f => m.insert f.code f) {},
                     live := p.liveCodes,
                     driveKnown := match drive with
                       | some #[c] => some c
                       | _ => none,
                     litCode := p.litCode,
                     frameScopes := frameScopes p }
  let act : LM (List Fn) := do
    let codes ← p.codes.toList.zipIdx.mapM fun (c, k) => lowerCode k c
    let main ← lowerMain p.main
    let entry ← entryFn fMain p.fin counts p.exits
    let mut gen : Array Fn := #[]
    for _ in [0:1 <<< 20] do
      let q := (← get).queue
      match q[gen.size]? with
      | some h => gen := gen.push (← genHelper h)
      | none => break
    pure ([printDecFn] ++ codes ++ [main, entry] ++ gen.toList)
  let (fns, _) ← (act.run ctx).run {}
  pure { fns := fns.toArray, entry := fMain + 1, data := p.data }

end Backend.Flat

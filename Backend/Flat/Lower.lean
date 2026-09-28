import Std.Data.HashMap
import Backend.Clos.Syntax
import Backend.Clos.Types
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
- **Closures.** A closure of code `c` with captured values is an object: `c`, then the captured
  values' words. A closure of a code that captures nothing is the word `2c + 1` and allocates
  nothing (an object's address is even). Calling a closure is an indirect call through the table
  at `c`, on the closure and the argument's words, and returns the answer's words; a code with an
  environment loads it into locals and frees the object. A call in return position whose callee
  answers exactly the caller's words is a tail call.
- **Cells and array slots** hold their contents' words, `max 1 |A|` words for a cell and `|A|`
  per slot.
- `copy`, `drop`, the printer, the array primitives and the loop driver are functions generated
  on demand per layout type (`Helper`); at a trivial type a copy is the words themselves and a
  drop is nothing. Copying or dropping a closure of type `T` tests for a word `2c + 1` (nothing to
  do), and otherwise selects the code among the codes of type `T` that capture something, by a
  binary search on `c`, and calls that code's copy or drop directly.

Function indices: `print_dec`, the closure codes in table order, `main`, the entry, then the
generated helpers in the order they are first asked for.
-/

namespace Backend.Flat
open BoCa Backend.Clos

/-- A function generated per layout type (types are representatives). -/
inductive Helper where
  | copy (n : Nat)
  | drop (n : Nat)
  | print (n : Nat)
  /-- Copy and drop a closure of code `c`. -/
  | closCopy (c : Nat)
  | closDrop (c : Nat)
  /-- `tab` and its loop, at element location type `a` and tabulator type `f`. -/
  | tab (a f : Nat)
  | tabLoop (a f : Nat)
  /-- `drop` of an array and its loop, at element location type `a` and consumer type `f`. -/
  | arrDrop (a f : Nat)
  | arrDropLoop (a f : Nat)
  /-- Drive a loop of type `n` (SPEC §11). -/
  | drive (n : Nat)
  deriving BEq, Hashable, Repr, Inhabited

structure Ctx where
  T : Types
  codes : Array Code
  /-- The codes that capture something, by their type (a representative). -/
  envCodes : Std.HashMap Nat (Array Nat)
  helperBase : Nat

structure LState where
  vars : Std.HashMap Var (List Nat) := {}
  next : Nat := 0
  helpers : Std.HashMap Helper Nat := {}
  queue : Array Helper := #[]

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
    | .drive n => .drive (T.r n)
    | h => h
  match (← get).helpers[h]? with
  | some i => pure i
  | none =>
    let base := (← read).helperBase
    modifyGet fun s => (base + s.queue.size,
      { s with helpers := s.helpers.insert h (base + s.queue.size), queue := s.queue.push h })

/-- Run `act` as the body of a function of `params` words: its locals start after them. The
number of locals beyond the parameters. -/
def inFn (params : Nat) (act : LM α) : LM (α × Nat) := do
  let saved ← get
  set { saved with vars := {}, next := params }
  let a ← act
  let n := (← get).next
  modify fun s => { s with vars := saved.vars, next := saved.next }
  pure (a, n - params)

/-! ### Fields -/

/-- Store the words `vs` at `a + 8·off`. -/
def storeAt (a : Exp) (off : Nat) (vs : List Exp) : List Stmt :=
  vs.zipIdx.map fun (e, i) => .store a (off + i) e

/-- Load `k` words at `a + 8·off` into fresh locals. -/
def loadAt (a : Exp) (off k : Nat) : LM (List Stmt × List Nat) := do
  let ls ← fresh k
  pure (ls.zipIdx.map (fun (l, i) => .set l (.load a (off + i))), ls)

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

/-! ### Closures -/

/-- The table index of the closure in `f`: `c` from the word `2c + 1`, or from the object. -/
def codeIndex (f : Nat) : LM (List Stmt × Exp) := do
  let t ← fresh1
  return ([.ite (wrap (and64 (.loc f) (.c64 1))) [.set t (shr64 (.loc f) (.c64 1))]
    [.set t (.load (.loc f) 0)]], .loc t)

/-- Call the closure in `f` on the words `args`; the results go to `ds`. -/
def callClosure (ds : List Nat) (f : Nat) (args : List Exp) : LM (List Stmt) := do
  let (s, c) ← codeIndex f
  return s ++ [.callInd ds c (.loc f :: args)]

/-- `act c` for the code `c` in the local `k`, one of `cs` (sorted): a binary search, of depth
at most `fuel`. -/
def dispatch (k : Nat) (act : Nat → LM (List Stmt)) : Nat → List Nat → LM (List Stmt)
  | _, [] => pure [.trap]
  | _, [c] => act c
  | 0, _ => pure [.trap]
  | fuel + 1, cs => do
    let m := cs.length / 2
    let pivot := cs[m]?.getD 0
    return [.ite (ltu64 (.loc k) (.c64 pivot.toUInt64)) (← dispatch k act fuel (cs.take m))
      (← dispatch k act fuel (cs.drop m))]

/-- For a closure of type `n` in local `0`: nothing when it is a word `2c + 1`, and otherwise
`act c` for its code `c`. -/
def onClosure (n : Nat) (none : List Stmt) (act : Nat → LM (List Stmt)) : LM (List Stmt) := do
  let cs := (((← read).envCodes[(← T).r n]?).getD #[]).toList
  let k ← fresh1
  return [.ite (wrap (and64 (.loc 0) (.c64 1))) none
    ([.set k (.load (.loc 0) 0)] ++ (← dispatch k act cs.length cs))]

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

/-- Where a term's words go: locals, or returned, padded to `k` words. -/
inductive Dest where
  | to (ls : List Nat)
  | ret (k : Nat)

def emit : Dest → List Exp → LM (List Stmt)
  | .to ls, vs => do
    if ls.length != vs.length then
      throw s!"flat IR: {vs.length} words for {ls.length} locals"
    pure (ls.zip vs |>.map fun (l, e) => .set l e)
  | .ret k, vs => pure [.ret (vs ++ zeros (k - vs.length))]

/-- A host operation on its operand's words (§8): an integer, a tag, or a partial operation's
tag and integer. A 32-bit integer is held zero-extended. -/
def hostVals (o : HostOp) (ls : List Nat) : LM (List Stmt × List Exp) := do
  let raw (l : Nat) : Exp := match hostArgWidth o with
    | .w32 => wrap (.loc l)
    | .w64 => .loc l
  let args := ls.map raw
  let word (w : Width) (e : Exp) : Exp := match w with
    | .w32 => extendU e
    | .w64 => e
  match hostResKind o, o with
  | .int w, _ => pure ([], [word w (.op o args)])
  | .test, _ => pure ([], [extendU (.op o args)])
  | .trapping w, .div _ d =>
    let t₀ ← fresh1
    let t₁ ← fresh1
    let a := args.headD (.c64 0)
    let b := args.getD 1 (.c64 0)
    let zero := Exp.op (.eqz w) [b]
    let trapC := match d with
      | .div_s =>
        let intMin := match w with | .w32 => Exp.c32 0x80000000 | .w64 => .c64 0x8000000000000000
        let minus1 := match w with | .w32 => Exp.c32 0xFFFFFFFF | .w64 => .c64 0xFFFFFFFFFFFFFFFF
        or32 zero (and32 (.op (.rel w .eq) [a, intMin]) (.op (.rel w .eq) [b, minus1]))
      | _ => zero
    pure ([.ite trapC [.set t₀ (.c64 1), .set t₁ (.c64 0)]
            [.set t₀ (.c64 0), .set t₁ (word w (.op o args))]], [.loc t₀, .loc t₁])
  | .trapping _, _ => throw "flat IR: a partial operation that is not a division"

/-- The contents' type of a `loc` type. -/
def locElem (n : Nat) : LM Nat := do
  match (← T).ty n with
  | .loc a _ => pure a
  | _ => throw "flat IR: not a location type"

def lowerPrim : Op → List Var → Dest → LM (List Stmt)
  | .alloc, [v], d => do
      let some n := (← T).cons[v]? | throw "flat IR: an untyped cell"
      let ls ← vals v
      let t ← fresh1
      return [.set t (.alloc (.c64 (max 1 ((← T).cellWords n)).toUInt64))] ++
        storeAt (.loc t) 0 (locs ls) ++ (← emit d [.loc t])
  | .free, [l], d => do
      let a ← locElem (← vty l)
      let p := Exp.loc ((← vals l).headD 0)
      let (s, ls) ← loadAt p 0 (← words a)
      return s ++ [.free p] ++ (← emit d (locs ls))
  | .load, [l], d => do
      let a ← locElem (← vty l)
      let p := Exp.loc ((← vals l).headD 0)
      let (s, ls) ← loadAt p 0 (← words a)
      let (c, ls) ← copyVals a ls
      return s ++ c ++ (← emit d (locs ls))
  | .store, [l, v], d => do
      let a ← vty v
      let p := Exp.loc ((← vals l).headD 0)
      let (s, old) ← loadAt p 0 (← words a)
      let dr ← dropVals a old
      let s := if dr.isEmpty then [] else s ++ dr
      return s ++ storeAt p 0 (locs (← vals v)) ++ (← emit d [])
  | .swap, [l, v], d => do
      let a ← locElem (← vty l)
      let m := (← vals l).headD 0
      let (s, old) ← loadAt (.loc m) 0 (← words a)
      return s ++ storeAt (.loc m) 0 (locs (← vals v)) ++ (← emit d (locs (m :: old)))
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
  | .idx, [v], d => do
      let T ← T
      let h := (T.field (← vty v) 0).1
      let w := T.cellWords (T.field h 0).1 * 8
      match ← vals v with
      | [b, n, i] =>
        let t₀ ← fresh1
        let t₁ ← fresh1
        return [.ite (ltu64 (.loc i) (.loc n))
            [.set t₀ (.c64 0), .set t₁ (add64 (.loc b) (mul64 (.loc i) (.c64 w.toUInt64)))]
            [.set t₀ (.c64 1), .set t₁ (.c64 0)]] ++ (← emit d [.loc t₀, .loc t₁])
      | _ => throw "flat IR: idx of a non-array"
  | .drop, [v], d => do
      let T ← T
      let n ← vty v
      let f := (T.field n 0).1
      let l := (T.field (T.field n 1).1 0).1
      return [.call [] (← helper (.arrDrop l f)) (locs (← vals v))] ++ (← emit d [])
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
  | _, _, _ => throw "flat IR: primitive arity"

/-- Call the closure in `f` on the words `args`, answering `k` words, of which the first `w` are
the result. -/
def lowerCall (f : Nat) (args : List Nat) (k w : Nat) (d : Dest) : LM (List Stmt) := do
  let (s, callee) ← codeIndex f
  let args := .loc f :: locs args
  match d with
  | .ret k' => if k' == k then return s ++ [.tailCallInd callee args] else pure ()
  | .to ls => if ls.length == k then return s ++ [.callInd ls callee args] else pure ()
  let ts ← fresh k
  return s ++ [.callInd ts callee args] ++ (← emit d (locs (ts.take w)))

def lowerTm : Tm → Dest → LM (List Stmt)
  | .var x, d => do emit d (locs (← vals x))
  | .unit, d => emit d []
  | .lit (.i32 n), d => emit d [.c64 n.toUInt64]
  | .lit (.i64 n), d => emit d [.c64 n]
  | .pair a b, d => do
      let some n := (← T).cons[a]? | throw "flat IR: an untyped pair"
      let (s, vs) ← mkPair n (locs (← vals a)) (locs (← vals b))
      return s ++ (← emit d vs)
  | .inj r a, d => do
      let some n := (← T).cons[a]? | throw "flat IR: an untyped injection"
      let (s, vs) ← mkInj n r (locs (← vals a))
      return s ++ (← emit d vs)
  | .clos c xs, d => do
      let fields := (← xs.mapM vals).flatten
      let t ← fresh1
      if xs.isEmpty then return ← emit d [.c64 (2 * c + 1).toUInt64]
      return [.set t (.alloc (.c64 (1 + fields.length).toUInt64)),
        .store (.loc t) 0 (.c64 c.toUInt64)] ++ storeAt (.loc t) 1 (locs fields) ++
        (← emit d [.loc t])
  | .prim op xs, d => lowerPrim op xs d
  | .app f a, d => do
      let T ← T
      let some r := T.apps[f]? | throw "flat IR: an untyped call"
      lowerCall ((← vals f).headD 0) (← vals a) (T.answerWords (← vty f)) (T.words r) d
  | .letv x e b, d => do
      let se ← lowerTm e (.to (← bindFresh x))
      return se ++ (← lowerTm b d)
  | .letpair x y p b, d => do
      let (s, vx, vy) ← splitPair (← vty p) (← vals p) true
      bindVals x vx
      bindVals y vy
      return s ++ (← lowerTm b d)
  | .case s x b₁ y b₂, d => do
      let n ← vty s
      let ls ← vals s
      let (s₁, v₁) ← payload n false ls true
      bindVals x v₁
      let t₁ ← lowerTm b₁ d
      let (s₂, v₂) ← payload n true ls true
      bindVals y v₂
      let t₂ ← lowerTm b₂ d
      return [.ite (eqz64 (.loc (ls.headD 0))) (s₁ ++ t₁) (s₂ ++ t₂)]
  | .copy x x' b, d => do
      let (s, ls) ← copyVals (← vty x) (← vals x)
      bindVals x' ls
      return s ++ (← lowerTm b d)
  | .drop x b, d => do
      let s ← dropVals (← vty x) (← vals x)
      return s ++ (← lowerTm b d)

/-! ### Codes, `main` and the entry -/

/-- The words a closure's environment holds, per captured variable. -/
def envWords (c : Code) : LM (List Nat) := c.env.mapM fun x => do words (← vty x)

/-- Code `k` as a function of the closure and the argument's words, answering its type's
`answerWords`. It loads the environment and frees the closure. A `sel` code's `case` on the
parameter returns each arm at its own type, padded to the wider. -/
def lowerCode (k : Nat) (c : Code) : LM Fn := do
  let T ← T
  let fTy := T.codeTy[k]!
  let (aTy, ans) := match T.ty fTy with
    | .fn a _ _ => (a, T.answerWords fTy)
    | _ => (fTy, 0)
  let pw ← words aTy
  let (body, nloc) ← inFn (1 + pw) do
    bindVals c.param (List.range' 1 pw)
    let mut unpack : List Stmt := []
    let mut off := 1
    for x in c.env do
      let (s, ls) ← loadAt (.loc 0) off (← words (← vty x))
      bindVals x ls
      unpack := unpack ++ s
      off := off + ls.length
    let body ← lowerTm c.body (.ret ans)
    pure (unpack ++ (if c.env.isEmpty then [] else [.free (.loc 0)]) ++ body ++ [.trap])
  pure { name := s!"code{k}", params := 1 + pw, results := ans, locals := nloc, body }

def lowerMain (t : Tm) : LM Fn := do
  let k ← words (← T).mainTy
  let (body, nloc) ← inFn 0 do
    pure ((← lowerTm t (.ret k)) ++ [.trap])
  pure { name := "main", params := 0, results := k, locals := nloc, body }

/-- The counts of a run, written after the report when they are asked for: allocations and
indirect calls. -/
def countsReport : List Stmt :=
  outStr "allocs " ++ [.call [] fPrintDec [.stat 0]] ++ outStr "\nindirect " ++
    [.call [] fPrintDec [.stat 1]] ++ outStr "\n"

/-- Run `main` (driving it and running the code `fin` on what it finishes with, when it returns
a loop), print the value, drop it, print the live count, and with `counts` the run's counts. -/
def entryFn (fMain : Nat) (fin : Option Nat) (counts : Bool) : LM Fn := do
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
        pure ([Stmt.call m fMain [], .call rs (← helper (.drive T.mainTy)) (locs m),
          .call es (codeFn c) (.c64 (2 * c + 1).toUInt64 :: locs rs)], es.take (T.words T.resTy))
    let dr ← dropVals T.resTy v
    pure (run ++ [.call [] (← helper (.print T.resTy)) (locs v)] ++ outStr "\n" ++ dr ++
      outStr "live " ++ [.call [] fPrintDec [.live]] ++ outStr "\n" ++
      (if counts then countsReport else []) ++ [.ret []])
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

/-- The fields of a pair's or injection's locals. -/
def fieldLocals (n i : Nat) (ls : List Nat) : LM (List Nat) := do
  let T ← T
  match T.ty n with
  | .pair .. =>
    let w₀ := T.fieldWords n 0
    pure (if i == 0 then ls.take w₀ else (ls.drop w₀).take (T.fieldWords n 1))
  | _ => pure ((ls.drop 1).take (T.fieldWords n i))

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
        let t ← fresh1
        onClosure n [.ret [.loc 0]] fun c => do
          return [.call [t] (← helper (.closCopy c)) [.loc 0], .ret [.loc t]]
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
    let w := T.words n
    let (body, nloc) ← inFn w do
      let ps := List.range w
      match T.ty n with
      | .fn .. => do
        let s ← onClosure n [] fun c => do return [.call [] (← helper (.closDrop c)) [.loc 0]]
        pure (s ++ [.ret []])
      | .pair .. => do
        pure ((← dropField n 0 (← fieldLocals n 0 ps)) ++ (← dropField n 1 (← fieldLocals n 1 ps)) ++
          [.ret []])
      | .sum .. => do
        pure [.ite (eqz64 (.loc 0)) (← dropField n 0 (← fieldLocals n 0 ps))
          (← dropField n 1 (← fieldLocals n 1 ps)), .ret []]
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
      | .fn .. => pure (outStr "<fun>")
      | .loc .. => pure (outStr "<loc>")
      | .pair .. => do
        pure (outStr "(" ++ (← printField n 0 (← fieldLocals n 0 ps) false) ++ outStr ", " ++
          (← printField n 1 (← fieldLocals n 1 ps) false) ++ outStr ")")
      | .sum .. => do
        pure [.ite (eqz64 (.loc 0)) (outStr "inl " ++ (← printField n 0 (← fieldLocals n 0 ps) true))
          (outStr "inr " ++ (← printField n 1 (← fieldLocals n 1 ps) true))]
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
    -- `tab (c, f)`: `len(c)` slots of `|a|` words, filled by `f i` in order.
    let (body, nloc) ← inFn 2 do
      let n := Exp.loc 0
      let sz ← fresh1
      let b ← fresh1
      let loop ← helper (.tabLoop a f)
      let dr ← dropVals f [1]
      pure ([.ite (ltu64 n (.c64 0x80000000)) [] [.set 0 (.c64 0)],
        .set sz (mul64 n (.c64 (T.cellWords a).toUInt64)),
        .ite (eqz64 (.loc sz)) [.set sz (.c64 1)] [],
        .set b (.alloc (.loc sz)),
        .call [] loop [.loc b, .loc 1, .c64 0, n]] ++ dr ++ [.ret [.loc b, n]])
    pure { name := "array_tab", params := 2, results := 2, locals := nloc, body }
  | .tabLoop a f =>
    -- `b f i n`: slot `i` gets a copy of `f` applied to `i`, for `i < n`.
    let (_, _, k) ← fnParts f
    let w ← words (← locElem a)
    let (body, nloc) ← inFn 4 do
      let (cs, fc) ← copyVals f [1]
      let rs ← fresh k
      let slot := add64 (.loc 0) (mul64 (.loc 2) (.c64 (8 * T.cellWords a).toUInt64))
      pure [.ite (ltu64 (.loc 2) (.loc 3))
        (cs ++ (← callClosure rs (fc.headD 1) [.loc 2]) ++
          storeAt slot 0 (locs (rs.take w)) ++
          [.tailCall (← helper (.tabLoop a f)) [.loc 0, .loc 1, add64 (.loc 2) (.c64 1), .loc 3]])
        [], .ret []]
    pure { name := "array_tab_loop", params := 4, results := 0, locals := nloc, body }
  | .arrDrop a f =>
    -- `f b n`: each element to a copy of `f`, in order, then the range freed.
    let (body, nloc) ← inFn 3 do
      pure ([.call [] (← helper (.arrDropLoop a f)) [.loc 1, .loc 0, .c64 0, .loc 2]] ++
        (← dropVals f [0]) ++ [.free (.loc 1), .ret []])
    pure { name := "array_drop", params := 3, results := 0, locals := nloc, body }
  | .arrDropLoop a f =>
    -- `b f i n`: slot `i`'s contents, moved out, to a copy of `f`, for `i < n`.
    let (_, r, k) ← fnParts f
    let w ← words (← locElem a)
    let (body, nloc) ← inFn 4 do
      let (cs, fc) ← copyVals f [1]
      let slot := add64 (.loc 0) (mul64 (.loc 2) (.c64 (8 * T.cellWords a).toUInt64))
      let (ls, es) ← loadAt slot 0 w
      let rs ← fresh k
      pure [.ite (ltu64 (.loc 2) (.loc 3))
        (cs ++ ls ++ (← callClosure rs (fc.headD 1) (locs es)) ++
          (← dropVals r (rs.take (T.words r))) ++
          [.tailCall (← helper (.arrDropLoop a f)) [.loc 0, .loc 1, add64 (.loc 2) (.c64 1), .loc 3]])
        [], .ret []]
    pure { name := "array_drop_loop", params := 4, results := 0, locals := nloc, body }
  | .drive n =>
    -- `d`: call `d` on `inl ()` until it answers `inl r`; `inr d'` goes on with `d'`.
    let (a, c, k) ← fnParts n
    let r := (T.field c 0).1
    let (body, nloc) ← inFn 1 do
      let (s₀, sel) ← mkInj a false []
      let rs ← fresh k
      let cv := rs.take (T.words c)
      let (s₁, rv) ← payload c false cv true
      let (s₂, dv) ← payload c true cv true
      pure (s₀ ++ (← callClosure rs 0 sel) ++ [
        .ite (eqz64 (.loc (cv.headD 0))) (s₁ ++ [.ret (locs rv)])
          (s₂ ++ [.tailCall (← helper (.drive n)) (locs dv)])])
    pure { name := "drive", params := 1, results := T.words r, locals := nloc, body := body ++ [.trap] }

def lower (p : Clos.Prog) (counts : Bool := false) : Except String Prog := do
  let T ← p.types
  let nc := p.codes.size
  let fMain := codeFn nc
  let envCodes := (List.range nc).foldl (fun (m : Std.HashMap Nat (Array Nat)) c =>
      if (p.codes[c]?.map (·.env.isEmpty)).getD true then m
      else let t := T.r T.codeTy[c]!; m.insert t ((m.getD t #[]).push c)) {}
  let ctx : Ctx := { T, codes := p.codes, envCodes, helperBase := fMain + 2 }
  let act : LM (List Fn × Array Nat) := do
    let table := (← (List.range nc).mapM fun c => do
      pure [codeFn c]).flatten
    let codes ← p.codes.toList.zipIdx.mapM fun (c, k) => lowerCode k c
    let main ← lowerMain p.main
    let entry ← entryFn fMain p.fin counts
    let mut gen : Array Fn := #[]
    for _ in [0:1 <<< 20] do
      let q := (← get).queue
      match q[gen.size]? with
      | some h => gen := gen.push (← genHelper h)
      | none => break
    pure ([printDecFn] ++ codes ++ [main, entry] ++ gen.toList, table.toArray)
  let ((fns, table), _) ← (act.run ctx).run {}
  pure { fns := fns.toArray, table, entry := fMain + 1 }

end Backend.Flat

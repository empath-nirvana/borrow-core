import Std.Data.HashMap
import Support.Dynamics.Host
import Backend.Value
import Backend2.Syntax

/-!
# Backend2 — the LIR interpreter

A fuelled interpreter of the LIR over values as trees and a heap of cells and arrays, with a
scripted standard input, the arguments' stream, and collected standard output and error
(SPEC §11, §34). It checks the LIR's discipline as it runs:

- every variable is consumed once on each path: a use consumes it, a consumed variable is not
  used again, and a function returns with its frame empty;
- a `copy` or a `drop` is never of a type that owns a cell (`ref`, an array) or of a `mut`
  borrow: copies and drops are of persistent values and borrows only;
- a cell or slot is read only when written, and written by `put` and `slotPut` only when
  unwritten (the moves of `take`, `replace` and `withswap`), and an array is freed only when
  every slot is unwritten;
- every heap access is to a live object;
- every `stackK` drop is a stack machine's hand-over (`handOverB`, `HandOver`).

Its report is the stages' (`Backend.report`): `main`'s value, then the objects live at the end.
Host operations are `wasmHostAt .negative`'s, as the closure IR's interpreter's, so that output
that depends on a NaN's sign differs here from the golden (SPEC §37).
-/

namespace Backend2
open BoCa

def lirHost : Host := wasmHostAt .negative

/-- A value. -/
inductive LV where
  | unit
  | int (n : UInt64)
  | pair (a b : LV)
  | inj (right : Bool) (a : LV)
  | clos (code : Nat) (env : List LV)
  | loc (a : Nat)
  | fam (base : Nat) (n : UInt32)
  | unk
  deriving Inhabited, Repr

/-- The base of the program's data, in the interpreter's addresses. -/
def dataAt : Nat := 1 <<< 40
/-- The base of the capabilities' static cells. -/
def staticAt : Nat := 1 <<< 41

structure St where
  /-- Each address of a live object: its contents, `none` while unwritten. -/
  mem : Std.HashMap Nat (Option LV) := {}
  /-- The live objects: base and number of addresses. -/
  objs : Std.HashMap Nat Nat := {}
  next : Nat := 16
  frame : Std.HashMap Var LV := {}
  input : List UInt8 := []
  args : List UInt8 := []
  out : ByteArray := .empty
  err : ByteArray := .empty
  data : Array UInt8 := #[]
  /-- The task stacks (SPEC §52): each stack's object, and its frames' cells, the top last. -/
  taskStacks : Std.HashMap Nat (Array Nat) := {}
  /-- The current stack: its object, `0` for none. -/
  cur : Nat := 0
  /-- Each stack's `κ` region, while written (SPEC §52). -/
  regions : Std.HashMap Nat LV := {}

abbrev IM := StateT St (Except String)

def bad (msg : String) : IM α := throw s!"LIR interpreter: {msg}"

/-! ### The frame -/

def bindV (x : Var) (v : LV) : IM Unit := modify fun s => { s with frame := s.frame.insert x v }

def takeV (x : Var) : IM LV := do
  match (← get).frame[x]? with
  | some v => modify (fun s => { s with frame := s.frame.erase x }); pure v
  | none => bad s!"variable x{x} used after it was consumed, or unbound"

def takeAll (xs : List Var) : IM (List LV) := xs.mapM takeV

/-! ### The heap -/

def newObj (n : Nat) : IM Nat := do
  let s ← get
  let b := s.next
  let mut mem := s.mem
  for i in [0:n] do mem := mem.insert (b + i) none
  set { s with mem, objs := s.objs.insert b n, next := b + max n 1 + 1 }
  pure b

def readAt (a : Nat) : IM LV := do
  if a ≥ dataAt && a < staticAt then
    match (← get).data[a - dataAt]? with
    | some b => return .int b.toUInt64
    | none => bad s!"a read past the program's data"
  match (← get).mem[a]? with
  | some (some v) => pure v
  | some none => bad s!"a read of the unwritten address {a}"
  | none => bad s!"a read of the address {a}, which is not live"

def writeAt (a : Nat) (v : Option LV) : IM Unit := do
  match (← get).mem[a]? with
  | some _ => modify fun s => { s with mem := s.mem.insert a v }
  | none => bad s!"a write of the address {a}, which is not live"

def isWritten (a : Nat) : IM Bool := do
  match (← get).mem[a]? with
  | some (some _) => pure true
  | some none => pure false
  | none => bad s!"an access of the address {a}, which is not live"

def freeObj (b : Nat) (n : Nat) : IM Unit := do
  match (← get).objs[b]? with
  | some k =>
    if k != n then bad s!"a free of {n} addresses at an object of {k}"
    let s ← get
    let mut mem := s.mem
    for i in [0:n] do mem := mem.erase (b + i)
    set { s with mem, objs := s.objs.erase b }
  | none => bad s!"a free of {b}, which is not a live object"

/-! ### Host operations -/

def toBit (b : Bool) : UInt64 := if b then 1 else 0

def fbits : (f : FWidth) → UInt64 → f.width.bits
  | .f32, a => a.toUInt32
  | .f64, a => a
def fword : (f : FWidth) → f.width.bits → UInt64
  | .f32, a => UInt32.toUInt64 a
  | .f64, a => a
def ibits : (i : IWidth) → UInt64 → i.width.bits
  | .i32, a => a.toUInt32
  | .i64, a => a
def iword : (i : IWidth) → i.width.bits → UInt64
  | .i32, a => UInt32.toUInt64 a
  | .i64, a => a

/-- A host operation on words (32-bit operands their low halves): its answer, or `none` where
§8's operation has none (`inr ()`). -/
def hostWords : HostOp → List UInt64 → Except String (Option UInt64)
  | .bin .w32 o, [a, b] => .ok (lirHost.bin32 o a.toUInt32 b.toUInt32).toUInt64
  | .bin .w64 o, [a, b] => .ok (lirHost.bin64 o a b)
  | .div .w32 o, [a, b] => .ok ((lirHost.div32 o a.toUInt32 b.toUInt32).map (·.toUInt64))
  | .div .w64 o, [a, b] => .ok (lirHost.div64 o a b)
  | .un .w32 o, [a] => .ok (lirHost.un32 o a.toUInt32).toUInt64
  | .un .w64 o, [a] => .ok (lirHost.un64 o a)
  | .eqz .w32, [a] => .ok (toBit (lirHost.eqz32 a.toUInt32))
  | .eqz .w64, [a] => .ok (toBit (lirHost.eqz64 a))
  | .rel .w32 o, [a, b] => .ok (toBit (lirHost.rel32 o a.toUInt32 b.toUInt32))
  | .rel .w64 o, [a, b] => .ok (toBit (lirHost.rel64 o a b))
  | .wrap, [a] => .ok (lirHost.wrap a).toUInt64
  | .extend_s, [a] => .ok (lirHost.extendS a.toUInt32)
  | .extend_u, [a] => .ok (lirHost.extendU a.toUInt32)
  | .extend32_s, [a] => .ok (lirHost.extend32S a)
  | .wrap8, [a] => .ok (lirHost.wrap8 a.toUInt32).toUInt64
  | .extend8_u, [a] => .ok (lirHost.extend8U a.toUInt8).toUInt64
  | .fbin f o, [a, b] => .ok (fword f (lirHost.fbin f o (fbits f a) (fbits f b)))
  | .fun1 f o, [a] => .ok (fword f (lirHost.fun1 f o (fbits f a)))
  | .frel f o, [a, b] => .ok (toBit (lirHost.frel f o (fbits f a) (fbits f b)))
  | .convert f i sx, [a] => .ok (fword f (lirHost.convert f i sx (ibits i a)))
  | .trunc i f sx, [a] => .ok ((lirHost.trunc i f sx (fbits f a)).map (iword i))
  | .trunc_sat i f sx, [a] => .ok (iword i (lirHost.truncSat i f sx (fbits f a)))
  | .demote, [a] => .ok (lirHost.demote a).toUInt64
  | .promote, [a] => .ok (lirHost.promote a.toUInt32)
  | .reinterpret_i _, [a] | .reinterpret_f _, [a] => .ok a
  | _, _ => .error "LIR interpreter: a host operation's arity"

def liftE (x : Except String α) : IM α := match x with
  | .ok a => pure a
  | .error e => throw e

def isBinary : HostOp → Bool
  | .bin .. | .div .. | .rel .. | .fbin .. | .frel .. => true
  | _ => false

/-- The kind of a host operation's answer: an integer, a test (`inr ()` for true), or a partial
operation's `inl n` or `inr ()`. -/
def resKind : HostOp → Nat
  | .div .. | .trunc .. => 2
  | .eqz _ | .rel .. | .frel .. => 1
  | _ => 0

def hostOp (op : HostOp) (v : LV) : IM LV := do
  let ws ← match v, isBinary op with
    | .pair (.int a) (.int b), true => pure [a, b]
    | .int a, false => pure [a]
    | _, _ => bad s!"a host operation's operand"
  let r ← liftE (hostWords op ws)
  match resKind op, r with
  | 0, some w => pure (.int w)
  | 1, some w => pure (.inj (w != 0) .unit)
  | 2, some w => pure (.inj false (.int w))
  | 2, none => pure (.inj true .unit)
  | _, _ => bad "a host operation with no answer"

/-! ### Types -/

/-- A type that owns a cell (`ref`, an array), or with `mutB` also one that holds a `mut` borrow:
a `drop` may not be at the first, a `copy` at either. -/
def LTy.ownsN (mutB : Bool) : Nat → LTy → Bool
  | 0, _ => false
  | f + 1, t => match t with
    | .ref _ | .fam (.ref _) => true
    | .mut _ | .fam (.mut _) => mutB
    | .pair a b | .sum a b => LTy.ownsN mutB f a || LTy.ownsN mutB f b
    | .mu a | .bang a => LTy.ownsN mutB f a
    | _ => false

/-- The contents read through `Imm̲` at the type `t`: a closure is `Unk` there. -/
def reborrowV : Nat → LTy → LV → LV
  | 0, _, v => v
  | f + 1, t, v => match t, v with
    | .unk, _ => .unk
    | .pair a b, .pair x y => .pair (reborrowV f a x) (reborrowV f b y)
    | .sum a _, .inj false x => .inj false (reborrowV f a x)
    | .sum _ b, .inj true x => .inj true (reborrowV f b x)
    | .mu a, v => reborrowV f (LTy.subst 0 (.mu a) a) v
    | .bang a, v => reborrowV f a v
    | _, v => v

/-! ### Printing -/

def pvOf : Nat → LTy → LV → Except String Backend.PV
  | 0, _, _ => .error "LIR interpreter: a value too deep to print"
  | f + 1, t, v => match t, v with
    | .unit, _ => .ok .unit
    | .int .w32, .int n => .ok (.i32 n.toUInt32)
    | .int .w64, .int n => .ok (.i64 n)
    | .int .w8, .int n => .ok (.u8 n.toUInt8)
    | .int .f32, .int n => .ok (.f32 n.toUInt32)
    | .int .f64, .int n => .ok (.f64 n)
    | .pair a b, .pair x y => return .pair (← pvOf f a x) (← pvOf f b y)
    | .sum a _, .inj false x => return .inj false (← pvOf f a x)
    | .sum _ b, .inj true x => return .inj true (← pvOf f b x)
    | .mu a, v => pvOf f (LTy.subst 0 (.mu a) a) v
    | .bang a, v => pvOf f a v
    | .thunk _, _ | .unk, _ => .ok .fn
    | .ref _, _ | .imm _, _ | .mut _, _ => .ok .loc
    | .fam _, .fam _ n => .ok (.pair .loc (.i32 n))
    | .opq _, _ => .ok .loc
    | t, v => .error s!"LIR interpreter: a value {reprStr v} at {t}"


/-! ### Operations -/

def fdOf (m : LV) : IM (Nat × LV) := do
  let .loc a := m | bad "an I/O operation on a non-cell"
  return (a, ← readAt a)

def emitBytes (fd : UInt64) (bs : List UInt8) : IM Unit := do
  if fd == 2 then modify fun s => { s with err := s.err ++ ⟨bs.toArray⟩ }
  else modify fun s => { s with out := s.out ++ ⟨bs.toArray⟩ }

def ioOp (k : IOKind) (v : LV) : IM LV := do
  match k, v with
  | .readByte, m => do
    let (_, c) ← fdOf m
    let .int fd := c | bad "read_byte on a cell that holds no stream"
    let s ← get
    let fromArgs := fd.toUInt32 == Backend.argsFd
    match (if fromArgs then s.args else s.input) with
    | [] => pure (.pair m (.inj true .unit))
    | b :: bs =>
      set (if fromArgs then { s with args := bs } else { s with input := bs })
      pure (.pair m (.inj false (.int b.toUInt64)))
  | .writeByte, .pair m (.int b) => do
    let (_, c) ← fdOf m
    let .int fd := c | bad "write_byte on a cell that holds no stream"
    emitBytes fd [b.toUInt8]
    pure m
  | .writeAll, .pair m (.fam a n) => do
    let (_, c) ← fdOf m
    let .int fd := c | bad "write_all on a cell that holds no stream"
    let bs ← (List.range n.toNat).mapM fun i => do
      match ← readAt (a + i) with
      | .int b => pure b.toUInt8
      | _ => bad "write_all of a view whose slots are not bytes"
    emitBytes fd bs
    pure m
  | .readInto, .pair m (.fam a n) => do
    let (_, c) ← fdOf m
    let .int fd := c | bad "read_into on a cell that holds no stream"
    let s ← get
    let fromArgs := fd.toUInt32 == Backend.argsFd
    let src := if fromArgs then s.args else s.input
    let bs := src.take n.toNat
    set (if fromArgs then { s with args := src.drop n.toNat } else { s with input := src.drop n.toNat })
    for (b, i) in bs.zipIdx do writeAt (a + i) (some (.int b.toUInt64))
    pure (.pair m (.pair (.fam a n) (.int bs.length.toUInt64)))
  | .clockNow, m => do
    let (_, c) ← fdOf m
    let .int t := c | bad "clock_now on a cell that holds no clock"
    pure (.pair m (.int t))
  | .clockSleep, .pair m (.int ns) => do
    let (a, c) ← fdOf m
    let .int t := c | bad "clock_sleep on a cell that holds no clock"
    writeAt a (some (.int (Backend.sleptNs t ns)))
    pure m
  | _, _ => bad "an I/O operation's argument"

def i32v (n : UInt32) : LV := .int n.toUInt64

def evalOp (ty : Var → IM LTy) (op : Op) (args : List Var) (resTy : LTy) : IM LV := do
  let vs ← takeAll args
  match op, vs with
  | .host o, [v] => hostOp o v
  | .divLit o, [.int a, .int d] => do
    let byte : Bool := match o with | .div .w32 _ => resTy.peel == LTy.int .w8 | _ => false
    match ← liftE (hostWords o [a, d]) with
    | some r => pure (.int (if byte = true then r &&& 0xff else r))
    | none => bad "a division by a literal that has no answer"
  | .alloc _, [v] | .allocLent _ _, [v] => do
    let b ← newObj 1
    writeAt b (some v)
    pure (.loc b)
  | .free, [.loc a] => do
    let v ← readAt a
    if a ≥ staticAt then return v
    freeObj a 1
    pure v
  | .release, [.loc a] => do
    if ← isWritten a then bad "a release of a written cell"
    freeObj a 1
    pure .unit
  | .swap, [.loc a, v] => do
    let old ← readAt a
    writeAt a (some v)
    pure (.pair (.loc a) old)
  | .lend _, [x] | .relend, [x] => pure (.pair x x)
  | .load, [.loc a] => do
    let v ← readAt a
    pure (reborrowV 4096 resTy v)
  | .take, [.loc a] => do
    let v ← readAt a
    writeAt a none
    pure (.pair (.loc a) v)
  | .put, [.loc a, v] => do
    if ← isWritten a then bad "a put into a written cell"
    writeAt a (some v)
    pure (.loc a)
  | .newArr, [.int n] => do
    let n := n.toUInt32
    if n == 0 then return .fam 0 0
    let b ← newObj n.toNat
    pure (.fam b n)
  | .slotPut, [.fam b n, .int i, v] => do
    if i.toUInt32 ≥ n then bad "a slot past the array's end"
    if ← isWritten (b + i.toNat) then bad "a slotPut into a written slot"
    writeAt (b + i.toNat) (some v)
    pure (.fam b n)
  | .slotTake, [.fam b n, .int i] => do
    if i.toUInt32 ≥ n then bad "a slot past the array's end"
    let v ← readAt (b + i.toNat)
    if b < dataAt || b ≥ staticAt then writeAt (b + i.toNat) none
    pure (.pair (.fam b n) v)
  | .freeArr, [.fam b n] => do
    if n == 0 || (b ≥ dataAt && b < staticAt) then return .unit
    for i in [0:n.toNat] do
      if ← isWritten (b + i) then bad "an array freed with a written slot"
    freeObj b n.toNat
    pure .unit
  | .size, [.fam b n] => pure (.pair (.fam b n) (i32v n))
  | .len, [.fam _ n] => pure (i32v n)
  | .idx _, [.fam b n, .int i] =>
    pure (if i.toUInt32 < n then .inj false (.loc (b + i.toNat)) else .inj true .unit)
  | .split _, [.fam b n, .int i] =>
    let i := i.toUInt32
    pure (if i ≤ n then .inj false (.pair (.fam b i) (.fam (b + i.toNat) (n - i)))
      else .inj true (.fam b n))
  | .emptyFam, [] => pure (.fam 0 0)
  | .replace, [.fam b n, .int i, x] => do
    if i.toUInt32 < n then
      let a := b + i.toNat
      let old ← readAt a
      writeAt a (some x)
      pure (.pair (.fam b n) (.inj false old))
    else pure (.pair (.fam b n) (.inj true x))
  | .swapSlots, [.fam b n, .int i, .int j] => do
    if i.toUInt32 < n && j.toUInt32 < n && i != j then
      let x ← readAt (b + i.toNat)
      let y ← readAt (b + j.toNat)
      writeAt (b + i.toNat) (some y)
      writeAt (b + j.toNat) (some x)
    pure (.fam b n)
  | .roll, [v] | .unroll, [v] => pure v
  | .litByte, [.int off, .int n, .int i] => do
    let off := off.toUInt32.toNat; let n := n.toUInt32.toNat
    let i := i.toUInt32
    if i.toNat < n then
      match (← get).data[off + i.toNat]? with
      | some b => pure (.int b.toUInt64)
      | none => bad "a literal's byte past the data"
    else pure (.int 0)
  | .litView _, _ => bad "litView is not built yet"
  | .io k, [v] => ioOp k v
  | .cntLt, [.int i, .int n] =>
    pure (.inj (decide (i.toUInt32 < n.toUInt32)) .unit)
  | .cntSucc, [.int i] => pure (.int ((i + 1) &&& 0xFFFFFFFF))
  | .cntPred, [.int i] => pure (.int ((i - 1) &&& 0xFFFFFFFF))
  | .clampLen, [.int c] => pure (.int (if c.toUInt32 < 0x80000000 then c &&& 0xFFFFFFFF else 0))
  | .stackSwap _, [.int h] => do
    let old := (← get).cur
    if h != 0 && !(← get).taskStacks.contains h.toNat then bad s!"a swap to {h}, which is not a stack"
    modify fun s => { s with cur := h.toNat }
    pure (.int old.toUInt64)
  | .stackNew _, [] => do
    let h ← newObj 1
    writeAt h (some .unit)
    modify fun s => { s with taskStacks := s.taskStacks.insert h #[] }
    pure (.int h.toUInt64)
  | .kappaPut _, [.int h, v] => do
    unless (← get).taskStacks.contains h.toNat do bad s!"a kappaPut to {h}, which is not a stack"
    if (← get).regions.contains h.toNat then bad "a kappaPut into a written region"
    modify fun s => { s with regions := s.regions.insert h.toNat v }
    pure .unit
  | .kappaTake _, [.int h] => do
    match (← get).regions[h.toNat]? with
    | some v => modify (fun s => { s with regions := s.regions.erase h.toNat }); pure (.pair (.int h) v)
    | none => bad s!"a kappaTake of the stack {h}, whose region is empty"
  | .stackFree, [.int h] => do
    if h == 0 then return .unit
    if (← get).regions.contains h.toNat then bad "a free of a stack whose region is written"
    match (← get).taskStacks[h.toNat]? with
    | some fs =>
      if !fs.isEmpty then bad s!"a free of the stack {h}, which holds {fs.size} frames"
      if (← get).cur == h.toNat then bad "a free of the current stack"
      freeObj h.toNat 1
      modify fun s => { s with taskStacks := s.taskStacks.erase h.toNat }
      pure .unit
    | none => bad s!"a free of {h}, which is not a stack"
  | .framePush _ _, [] => do
    if (← get).cur == 0 then
      let h ← newObj 1
      writeAt h (some .unit)
      modify fun s => { s with taskStacks := s.taskStacks.insert h #[], cur := h }
    let h := (← get).cur
    let f ← newObj 1
    modify fun s => { s with taskStacks := s.taskStacks.modify h (·.push f) }
    pure (.pair (.loc f) (.int f.toUInt64))
  | .frameTop _ _, [] => do
    let some fs := (← get).taskStacks[(← get).cur]? | bad "frameTop with no current stack"
    let some f := fs.back? | bad "frameTop of an empty stack"
    pure (.pair (.loc f) (.int f.toUInt64))
  | .framePut, [.loc f, v] => do
    if ← isWritten f then bad "a framePut into a written frame"
    writeAt f (some v)
    pure .unit
  | .framePop _, [.loc f] => do
    let h := (← get).cur
    let some fs := (← get).taskStacks[h]? | bad "framePop with no current stack"
    if fs.back? != some f then bad s!"a pop of the frame {f}, which is not the top"
    if ← isWritten f then bad "a pop of a written frame"
    freeObj f 1
    modify fun s => { s with taskStacks := s.taskStacks.insert h fs.pop }
    pure .unit
  | .unreachable, [] => bad "an unreachable arm reached"
  | op, vs => bad s!"the operation {reprStr op |>.take 40} on {vs.length} values {reprStr vs |>.take 200}"


/-! ### Literals and types -/

def litV : IntLit → LV
  | .i32 n => .int n.toUInt64
  | .i64 n => .int n
  | .u8 n => .int n.toUInt64
  | .f32 n => .int n.toUInt64
  | .f64 n => .int n

def tyIn (p : Prog) (x : Var) : IM LTy := do
  match p.ty[x]? with
  | some t => pure t
  | none => bad s!"variable x{x} has no type"

def peekV (x : Var) : IM LV := do
  match (← get).frame[x]? with
  | some v => pure v
  | none => bad s!"variable x{x} copied after it was consumed, or unbound"

/-! ### The stack machine's hand-over (#746 F3)

A stack machine's `stackK` drop (`DropRule.stackK`) hands a level's suspended computation over
to the machine's `k` at a lower frame: the node is `drop x (let k₂ = clos kc [base] in …)`. -/

/-- The frames of the current task stack, the bottom first. -/
def St.curFrames (s : St) : List Nat := (s.taskStacks.getD s.cur #[]).toList

/-- **The frames a stack machine's `k` over the `i`-th frame of the current stack stands for**:
that frame and those above it, to the top. -/
def St.framesFrom (s : St) (i : Nat) : List Nat := s.curFrames.drop i

/-- **`base` is at or below `a` on the current task stack**, and the frames from the top down to
`a` are written: the frames `clos kc [a]` stands for, each holding a level's state. -/
def TakesOver (s : St) (base a : Nat) : Prop :=
  ∃ i j, i ≤ j ∧ s.curFrames[i]? = some base ∧ s.curFrames[j]? = some a ∧
    ∀ f ∈ s.framesFrom j, ∃ v, s.mem[f]? = some (some v)

/-- **The hand-over at a `stackK` drop of `x` whose body is `b`**, at the state `s`: `b` binds
`clos kc [base]` first, `x` is `clos kc [a]` of the same code, and `base` is at or below `a`
on the current task stack, the frames from the top down to `a` written (`TakesOver`). -/
def HandOver (s : St) (x : Var) : Tm → Prop
  | .letv _ (.clos kc [base]) _ => ∃ a b, s.frame[x]? = some (.clos kc [.int a]) ∧
      s.frame[base]? = some (.int b) ∧ TakesOver s b.toNat a.toNat
  | _ => False

/-- `HandOver`, decided: the LIR interpreter's check at every `stackK` drop. -/
def handOverB (s : St) (x : Var) : Tm → Bool
  | .letv _ (.clos kc [base]) _ =>
    match s.frame[x]?, s.frame[base]? with
    | some (.clos kc' [.int a]), some (.int b) =>
      kc' == kc && match s.curFrames.findIdx? (· == b.toNat), s.curFrames.findIdx? (· == a.toNat) with
        | some i, some j => decide (i ≤ j) && (s.framesFrom j).all fun f => match s.mem[f]? with
          | some (some _) => true
          | _ => false
        | _, _ => false
    | _, _ => false
  | _ => false

/-! ### Terms -/

/-- **A node's own step**: at a `letpair`, `case`, `copy`, `drop` or `abandon`, what `eval` does
before it continues, in tail position, with the sub-term this answers; `none` at any other node.
At a `stackK` drop it checks the hand-over (`handOverB`). -/
def enter (p : Prog) (t : Tm) : IM (Option Tm) := match t with
  | .letpair x y q b => do
    match ← takeV q with
    | .pair a c => bindV x a; bindV y c; pure (some b)
    | v => bad s!"letpair of {reprStr v |>.take 80}"
  | .case sv x b₁ y b₂ => do
    match ← takeV sv with
    | .inj false v => bindV x v; pure (some b₁)
    | .inj true v => bindV y v; pure (some b₂)
    | v => bad s!"case of {reprStr v |>.take 80}"
  | .copy _ x x' b => do
    let t ← tyIn p x
    if t.ownsN true 64 then bad s!"a copy of x{x} at {t}, which owns a cell or holds a mut borrow"
    bindV x' (← peekV x)
    pure (some b)
  | .drop r x b => do
    let t ← tyIn p x
    if t.ownsN false 64 then bad s!"a drop of x{x} at {t}, which owns a cell"
    if r == .stackK && !handOverB (← get) x b then
      bad s!"a drop of x{x} at the rule stack k, where the hand-over does not hold"
    let _ ← takeV x
    pure (some b)
  | .abandon _ x b => do
    let t ← tyIn p x
    if t.ownsN false 64 then bad s!"a drop of x{x} at {t}, which owns a cell"
    let _ ← takeV x
    pure (some b)
  | _ => pure none

/-- The function a closure's call enters, and its arguments. -/
def closEntry (p : Prog) (g : LV) (arg : Option LV) (j : Nat) : IM (Nat × List LV) := do
  let .clos c env := g | bad s!"a call of a non-closure {reprStr g |>.take 80}"
  let some code := p.codes[c]? | bad s!"no code c{c}"
  match code.kind, arg with
  | .lam, some a => pure (code.fns.headD 0, env ++ [a])
  | .unit, none => pure (code.fns.headD 0, env)
  | .amp, none =>
    let some fn := code.fns[j]? | bad s!"no component {j} of c{c}"
    pure (fn, env)
  | k, _ => bad s!"a call of the {reprStr k} code c{c} the wrong way"

/-- **A call node's own step**: at an `app`, `app0`, `sel`, `call` or tabulation, the function it
enters and the arguments (`inr`), or the value at once (`inl`, a literal's table); `none` at any
other node. -/
def callEntry (p : Prog) (t : Tm) : IM (Option (LV ⊕ (Nat × List LV))) := match t with
  | .app g a => do
    let vg ← takeV g
    let va ← takeV a
    return some (.inr (← closEntry p vg (some va) 0))
  | .app0 g => do return some (.inr (← closEntry p (← takeV g) none 0))
  | .sel g j => do return some (.inr (← closEntry p (← takeV g) none j))
  | .call fn as => do return some (.inr (fn, ← takeAll as))
  | .prim (.tab fi) [g, n] => do
    let vg ← takeV g
    let .int k ← takeV n | bad "tab of a non-integer"
    let arr ← if k.toUInt32 == 0 then pure (LV.fam 0 0) else
      pure (LV.fam (← newObj k.toUInt32.toNat) k.toUInt32)
    return some (.inr (fi, [vg, arr, .int 0, .int k]))
  | .prim (.tabLit fi) [g, n] => do
    let vg ← takeV g
    let .int k ← takeV n | bad "tab of a non-integer"
    -- The literal's bytes, where the tabulator is a literal's table (`Prog.lits`) long enough.
    if let .clos c [.int off, .int len] := vg then
      if p.lits == some c && k.toNat ≤ len.toUInt32.toNat then
        return some (.inl (.fam (dataAt + off.toUInt32.toNat) k.toUInt32))
    let arr ← if k.toUInt32 == 0 then pure (LV.fam 0 0) else
      pure (LV.fam (← newObj k.toUInt32.toNat) k.toUInt32)
    return some (.inr (fi, [vg, arr, .int 0, .int k]))
  | _ => pure none

/-- A function's frame on entry: its parameters bound to the arguments. -/
def entryFrame (d : Fn) (args : List LV) : Std.HashMap Var LV :=
  (d.params.zip args).foldl (fun m (x, v) => m.insert x v) {}

mutual
def eval (p : Prog) : Nat → LTy → Tm → IM LV
  | 0, _, _ => bad "out of fuel"
  | f + 1, rt, t => match t with
    | .var x => takeV x
    | .unit => pure .unit
    | .lit c => pure (litV c)
    | .pair a b => do
      let va ← takeV a
      let vb ← takeV b
      pure (.pair va vb)
    | .inj r a => return .inj r (← takeV a)
    | .clos c env => return .clos c (← takeAll env)
    | .app .. | .app0 .. | .sel .. | .call .. | .prim (.tab _) [_, _] | .prim (.tabLit _) [_, _] => do
      match ← callEntry p t with
      | some (.inl v) => pure v
      | some (.inr (fn, args)) => callFn p f fn args
      | none => bad "a call node with no entry"
    | .prim op as => evalOp (tyIn p) op as rt
    | .letv x e b => do
      let v ← eval p f (← tyIn p x) e
      bindV x v
      eval p f rt b
    | .letpair .. | .case .. | .copy .. | .drop .. | .abandon .. => do
      match ← enter p t with
      | some b => eval p f rt b
      | none => bad "a node with no step"
    | .absurd _ => bad "absurd reached"

def callFn (p : Prog) (fuel : Nat) (fn : Nat) (args : List LV) : IM LV := do
  let some d := p.fns[fn]? | bad s!"no function f{fn}"
  if d.params.length != args.length then
    bad s!"f{fn} ({d.name}) of {d.params.length} parameters called on {args.length}"
  let saved := (← get).frame
  modify fun s => { s with frame := entryFrame d args }
  let r ← eval p fuel d.ret d.body
  let rest := (← get).frame
  if !rest.isEmpty then
    bad s!"f{fn} ({d.name}) returns with {rest.toList.map (s!"x{·.1}")} unconsumed"
  modify fun s => { s with frame := saved }
  pure r
end

/-- **The configurations a run reaches**: `Visits p s t s' u` when `eval`, evaluating `t` at the
state `s`, evaluates `u` at `s'` on the way: after a node's own step (`enter`), the bound term
of a `letv`, then its body with the value bound, and a call's function body on its arguments
(`callEntry`, `callFn`). -/
inductive Visits (p : Prog) : St → Tm → St → Tm → Prop
  | here : Visits p s t s t
  | step : (enter p t).run s = .ok (some b, s₁) → Visits p s₁ b s' u → Visits p s t s' u
  | bound : Visits p s e s' u → Visits p s (.letv x e b) s' u
  | body : p.ty[x]? = some tx → (eval p f tx e).run s = .ok (v, s₁) →
      Visits p { s₁ with frame := s₁.frame.insert x v } b s' u → Visits p s (.letv x e b) s' u
  | call : (callEntry p t).run s = .ok (some (.inr (fn, args)), s₁) → p.fns[fn]? = some d →
      d.params.length = args.length →
      Visits p { s₁ with frame := entryFrame d args } d.body s' u → Visits p s t s' u

/-! ### What the hand-over gives

Two facts, and only these: under `HandOver` the frame range of the `k` that takes over contains
the dropped `k`'s (`TakesOver.suffix`, from the order alone); and a `stackK` drop's step, as every
drop's, touches no heap (`enter_stackK_keeps`, with no hypothesis). That every configuration a
converted program reaches at a `stackK` drop is a hand-over, and that the `k` taking over then
releases those frames, is `UNPROVED:` (`Backend2.StackKHandOver`). -/

/-- The frames `clos kc [a]` stands for are a suffix of those `clos kc [base]` stands for. -/
theorem TakesOver.suffix {s : St} {base a : Nat} (h : TakesOver s base a) :
    ∃ i j, s.curFrames[i]? = some base ∧ s.curFrames[j]? = some a ∧
      s.framesFrom j <:+ s.framesFrom i := by
  obtain ⟨i, j, hij, hi, hj, -⟩ := h
  refine ⟨i, j, hi, hj, ?_⟩
  have e : s.framesFrom j = (s.framesFrom i).drop (j - i) := by
    simp only [St.framesFrom, List.drop_drop]; congr 1; omega
  rw [e]; exact List.drop_suffix _ _

/-- The interpreter's check is sound for the hand-over. -/
theorem handOverB_sound {s : St} {x : Var} {b : Tm} (h : handOverB s x b = true) :
    HandOver s x b := by
  unfold handOverB at h
  split at h
  · rename_i kc base _
    unfold HandOver
    split at h
    · rename_i kc' a vb hx hb
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, h⟩ := h
      refine ⟨a, vb, hx, hb, ?_⟩
      split at h
      · rename_i i j hi hj
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
        obtain ⟨hij, hw⟩ := h
        obtain ⟨hi', hpi, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hi
        obtain ⟨hj', hpj, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hj
        refine ⟨i, j, hij, ?_, ?_, ?_⟩
        · simp only [beq_iff_eq] at hpi; simp [List.getElem?_eq_getElem hi', hpi]
        · simp only [beq_iff_eq] at hpj; simp [List.getElem?_eq_getElem hj', hpj]
        · intro f hf
          have := hw f hf
          split at this
          · exact ⟨_, by assumption⟩
          · exact absurd this (by simp)
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The heap, the task stacks and the regions of `s'` are those of `s`. -/
def St.SameHeap (s s' : St) : Prop :=
  s'.mem = s.mem ∧ s'.objs = s.objs ∧ s'.taskStacks = s.taskStacks ∧ s'.regions = s.regions

/-- An action that changes no object, cell, task stack or region when it succeeds. -/
def Keeps (m : IM α) : Prop := ∀ s a s', m.run s = .ok (a, s') → St.SameHeap s s'

theorem Keeps.pure' (a : α) : Keeps (pure a : IM α) := by
  intro s a' s' h; cases h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem Keeps.bind' {m : IM α} {f : α → IM β} (hm : Keeps m) (hf : ∀ a, Keeps (f a)) :
    Keeps (m >>= f) := by
  intro s b s' h
  simp only [StateT.run, bind, StateT.bind, Except.bind] at h
  split at h
  · cases h
  · rename_i a s₁ e
    obtain ⟨h1, h2, h3, h4⟩ := hm s _ _ e
    obtain ⟨g1, g2, g3, g4⟩ := hf _ _ _ _ h
    exact ⟨g1.trans h1, g2.trans h2, g3.trans h3, g4.trans h4⟩

theorem Keeps.bad' (m : String) : Keeps (bad m : IM α) := by
  intro s a s' h
  simp [bad, StateT.run, throw, throwThe, MonadExceptOf.throw, StateT.lift, bind, Except.bind] at h

theorem Keeps.get' : Keeps (get : IM St) := by
  intro s a s' h
  simp [StateT.run, get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure] at h
  obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl, rfl, rfl⟩

theorem Keeps.modify' (f : St → St) (hf : ∀ s, St.SameHeap s (f s)) :
    Keeps (modify f : IM Unit) := by
  intro s a s' h
  simp [StateT.run, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure,
    Except.pure] at h
  obtain ⟨-, rfl⟩ := h; exact hf s

theorem Keeps.tyIn' (p : Prog) (x : Var) : Keeps (tyIn p x) := by
  unfold tyIn; split
  · exact Keeps.pure' _
  · exact Keeps.bad' _

theorem Keeps.takeV' (x : Var) : Keeps (takeV x) := by
  unfold takeV
  refine Keeps.bind' Keeps.get' fun st => ?_
  split
  · exact Keeps.bind' (Keeps.modify' _ fun _ => ⟨rfl, rfl, rfl, rfl⟩) fun _ => Keeps.pure' _
  · exact Keeps.bad' _

/-- The step of a `stackK` drop changes no object, cell, task stack or region; it consumes the
variable alone. It needs no hand-over: the interpreter's every drop is the same step. -/
theorem enter_stackK_keeps {p : Prog} {x : Var} {b : Tm} :
    Keeps (enter p (.drop .stackK x b)) := by
  have tail : Keeps (do let _ ← takeV x; pure (some b) : IM (Option Tm)) :=
    Keeps.bind' (Keeps.takeV' x) fun _ => Keeps.pure' _
  unfold enter
  refine Keeps.bind' (Keeps.tyIn' p x) fun t => ?_
  simp only
  split
  · refine Keeps.bind' (Keeps.bad' _) fun _ => ?_
    exact Keeps.bind' Keeps.get' fun st => by
      split; exact Keeps.bind' (Keeps.bad' _) fun _ => tail; exact tail
  · exact Keeps.bind' Keeps.get' fun st => by
      split; exact Keeps.bind' (Keeps.bad' _) fun _ => tail; exact tail

/-- The state a run of `p` starts at. -/
def St.init (p : Prog) (input args : List UInt8) : St := { input, args, data := p.data }

/-- Run a program: its output and report (`Backend.report`). -/
def runLIR (p : Prog) (fuel : Nat) (input : List UInt8) (args : List UInt8 := []) :
    Except String Backend.Output := do
  let (v, s) ← (eval p fuel p.mainTy p.main).run (St.init p input args)
  if !s.frame.isEmpty then
    throw s!"LIR interpreter: main leaves {s.frame.toList.map (s!"x{·.1}")} unconsumed"
  let pv ← pvOf 4096 p.mainTy v
  let (r, status) := Backend.reportExit p.exits pv s.objs.size
  pure (Backend.Output.mk' s.out s.err r status)

end Backend2

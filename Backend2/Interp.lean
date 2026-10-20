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
- every heap access is to a live object.

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
    | .mu a => LTy.ownsN mutB f a
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
    let byte : Bool := match o with | .div .w32 _ => resTy == LTy.int .w8 | _ => false
    match ← liftE (hostWords o [a, d]) with
    | some r => pure (.int (if byte = true then r &&& 0xff else r))
    | none => bad "a division by a literal that has no answer"
  | .alloc, [v] => do
    let b ← newObj 1
    writeAt b (some v)
    pure (.loc b)
  | .free, [.loc a] => do
    let v ← readAt a
    if a ≥ staticAt then return v
    freeObj a 1
    pure v
  | .swap, [.loc a, v] => do
    let old ← readAt a
    writeAt a (some v)
    pure (.pair (.loc a) old)
  | .lend, [x] | .relend, [x] => pure (.pair x x)
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
    writeAt (b + i.toNat) none
    pure (.pair (.fam b n) v)
  | .freeArr, [.fam b n] => do
    if n == 0 then return .unit
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
  | .litByte off n, [.int i] => do
    let i := i.toUInt32
    if i.toNat < n then
      match (← get).data[off + i.toNat]? with
      | some b => pure (.int b.toUInt64)
      | none => bad "a literal's byte past the data"
    else pure (.int 0)
  | .litView _, _ => bad "litView is not built yet"
  | .io k, [v] => ioOp k v
  | .clampLen, [.int c] => pure (.int (if c.toUInt32 < 0x80000000 then c &&& 0xFFFFFFFF else 0))
  | .staticCell k, [v] => do
    let a := staticAt + k
    modify fun s => { s with mem := s.mem.insert a (some v) }
    pure (.loc a)
  | op, vs => bad s!"the operation {reprStr op |>.take 40} on {vs.length} values {reprStr vs |>.take 200}"


/-! ### Terms -/

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
    | .app g a => do
      let vg ← takeV g
      let va ← takeV a
      callClos p f vg (some va) 0
    | .app0 g => do callClos p f (← takeV g) none 0
    | .sel g j => do callClos p f (← takeV g) none j
    | .call fn as => do callFn p f fn (← takeAll as)
    | .prim op as => evalOp (tyIn p) op as rt
    | .letv x e b => do
      let v ← eval p f (← tyIn p x) e
      bindV x v
      eval p f rt b
    | .letpair x y q b => do
      match ← takeV q with
      | .pair a c => bindV x a; bindV y c; eval p f rt b
      | v => bad s!"letpair of {reprStr v |>.take 80}"
    | .case sv x b₁ y b₂ => do
      match ← takeV sv with
      | .inj false v => bindV x v; eval p f rt b₁
      | .inj true v => bindV y v; eval p f rt b₂
      | v => bad s!"case of {reprStr v |>.take 80}"
    | .absurd _ => bad "absurd reached"
    | .copy x x' b => do
      let t ← tyIn p x
      if t.ownsN true 64 then bad s!"a copy of x{x} at {t}, which owns a cell or holds a mut borrow"
      bindV x' (← peekV x)
      eval p f rt b
    | .drop x b => do
      let t ← tyIn p x
      if t.ownsN false 64 then bad s!"a drop of x{x} at {t}, which owns a cell"
      let _ ← takeV x
      eval p f rt b

def callFn (p : Prog) (fuel : Nat) (fn : Nat) (args : List LV) : IM LV := do
  let some d := p.fns[fn]? | bad s!"no function f{fn}"
  if d.params.length != args.length then
    bad s!"f{fn} ({d.name}) of {d.params.length} parameters called on {args.length}"
  let saved := (← get).frame
  modify fun s => { s with frame := (d.params.zip args).foldl (fun m (x, v) => m.insert x v) {} }
  let r ← eval p fuel d.ret d.body
  let rest := (← get).frame
  if !rest.isEmpty then
    bad s!"f{fn} ({d.name}) returns with {rest.toList.map (s!"x{·.1}")} unconsumed"
  modify fun s => { s with frame := saved }
  pure r

def callClos (p : Prog) (fuel : Nat) (g : LV) (arg : Option LV) (j : Nat) : IM LV := do
  let .clos c env := g | bad s!"a call of a non-closure {reprStr g |>.take 80}"
  let some code := p.codes[c]? | bad s!"no code c{c}"
  match code.kind, arg with
  | .lam, some a => callFn p fuel (code.fns.headD 0) (env ++ [a])
  | .unit, none => callFn p fuel (code.fns.headD 0) env
  | .amp, none =>
    let some fn := code.fns[j]? | bad s!"no component {j} of c{c}"
    callFn p fuel fn env
  | k, _ => bad s!"a call of the {reprStr k} code c{c} the wrong way"
end

/-- Run a program: its output and report (`Backend.report`). -/
def runLIR (p : Prog) (fuel : Nat) (input : List UInt8) (args : List UInt8 := []) :
    Except String Backend.Output := do
  let s₀ : St := { input, args, data := p.data }
  let (v, s) ← (eval p fuel p.mainTy p.main).run s₀
  if !s.frame.isEmpty then
    throw s!"LIR interpreter: main leaves {s.frame.toList.map (s!"x{·.1}")} unconsumed"
  let pv ← pvOf 4096 p.mainTy v
  pure (Backend.Output.mk' s.out s.err (Backend.report pv s.objs.size))

end Backend2

import Std.Data.HashMap
import Support.Dynamics.Host
import Backend.Flat.Syntax
import Backend.Value

/-!
# Backend — flat-IR interpreter

A fuelled interpreter for the flat IR. Memory is a map from word addresses to words, and the
allocator is the specification of `Backend/README.md`: `alloc n` returns a fresh range of `n`
words disjoint from every live range, `free a` takes back the range starting at `a`, and `live`
counts the live ranges. This implementation never reuses an address and leaves a gap after
every range, so it reports what a reusing allocator would hide: a load or store outside a live
range, a read of a word never written, a `free` of anything but the start of a live range.
A function's locals start unwritten too, and a read of one before it is written is an error.
Each call has a frame of fresh addresses, never reused; a frame slot's words are live from its
`slot` to its `unslot` or the call's return (or tail call), so an access to a slot after its
scope or its frame is an error too. Slots are not ranges: `live` does not count them.
Numeric operations are `flatHost`'s: `wasmHost` with a NaN of payload `1` where an arithmetic
float operation answers a NaN, a resolution other than the source's and the closure IR's
(SPEC §37), so that a program whose output depends on that NaN's payload differs from its golden
here. A partial instruction where its operation has no answer is an error.
-/

namespace Backend.Flat
open BoCa

/-- The flat-IR interpreter's host: a NaN of payload `1` at an arithmetic float result.
    `[spec §37]` -/
def flatHost : Host := wasmHostAt .payload

structure FState where
  /-- Every word of a live range; `none` until written. -/
  mem : Std.HashMap Nat (Option UInt64)
  /-- Live ranges: start ↦ length in words. -/
  ranges : Std.HashMap Nat Nat
  next : Nat
  /-- The standard input not yet read. -/
  input : List UInt8
  /-- The arguments not yet read, each followed by `0` (SPEC §34). -/
  args : List UInt8 := []
  out : ByteArray
  err : ByteArray
  /-- Allocations so far. -/
  allocs : Nat := 0
  /-- Dispatched calls so far. -/
  indirect : Nat := 0
  /-- Copies of a variable at a non-trivial type so far. -/
  copies : Nat := 0
  /-- Memory reads so far: each `load` and `load8` evaluated. -/
  loads : Nat := 0
  /-- Memory writes so far: each `store` and `store8` run. -/
  stores : Nat := 0
  /-- Bounds checks so far: each `tickBound` run (the counting build marks every one). -/
  bounds : Nat := 0
  /-- Frame slots started so far (`Exp.slot`). -/
  slotsStarted : Nat := 0
  /-- The end of the read-only data: an address below it is not freed. -/
  staticEnd : Nat := 0
  /-- Live frame slots: start ↦ length in words. They are not ranges: `live` does not count
  them. -/
  slots : Std.HashMap Nat Nat := {}
  /-- The frames of the calls running, innermost first: each one's base address and words. -/
  frames : List (Nat × Nat) := []
  /-- The arguments have been read: the runtime's reservation of their memory, at their first
  read, is counted as one allocation, as `$args` counts it (`Backend/Wasm/Runtime.lean`). -/
  argsRead : Bool := false
  /-- The exit status the run ends with (SPEC §39). -/
  status : UInt32 := 0

abbrev FM := StateT FState (Except String)

def toBit (b : Bool) : UInt64 := if b then 1 else 0

def trapIf : Option UInt64 → Except String UInt64
  | some r => .ok r
  | none => .error "flat IR: trap in a numeric instruction"

/-- A float's bits in a word, and back: an `f32` is the low half.  `[spec §37]` -/
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

/-- A numeric operation on words; 32-bit operands are the low halves. -/
def evalOp : HostOp → List UInt64 → Except String UInt64
  | .bin .w32 o, [a, b] => .ok (flatHost.bin32 o a.toUInt32 b.toUInt32).toUInt64
  | .bin .w64 o, [a, b] => .ok (flatHost.bin64 o a b)
  | .div .w32 o, [a, b] => trapIf ((flatHost.div32 o a.toUInt32 b.toUInt32).map (·.toUInt64))
  | .div .w64 o, [a, b] => trapIf (flatHost.div64 o a b)
  | .un .w32 o, [a] => .ok (flatHost.un32 o a.toUInt32).toUInt64
  | .un .w64 o, [a] => .ok (flatHost.un64 o a)
  | .eqz .w32, [a] => .ok (toBit (flatHost.eqz32 a.toUInt32))
  | .eqz .w64, [a] => .ok (toBit (flatHost.eqz64 a))
  | .rel .w32 o, [a, b] => .ok (toBit (flatHost.rel32 o a.toUInt32 b.toUInt32))
  | .rel .w64 o, [a, b] => .ok (toBit (flatHost.rel64 o a b))
  | .wrap, [a] => .ok (flatHost.wrap a).toUInt64
  | .extend_s, [a] => .ok (flatHost.extendS a.toUInt32)
  | .extend_u, [a] => .ok (flatHost.extendU a.toUInt32)
  | .extend32_s, [a] => .ok (flatHost.extend32S a)
  | .wrap8, [a] => .ok (flatHost.wrap8 a.toUInt32).toUInt64
  | .extend8_u, [a] => .ok (flatHost.extend8U a.toUInt8).toUInt64
  | .fbin f o, [a, b] => .ok (fword f (flatHost.fbin f o (fbits f a) (fbits f b)))
  | .fun1 f o, [a] => .ok (fword f (flatHost.fun1 f o (fbits f a)))
  | .frel f o, [a, b] => .ok (toBit (flatHost.frel f o (fbits f a) (fbits f b)))
  | .convert f i sx, [a] => .ok (fword f (flatHost.convert f i sx (ibits i a)))
  | .trunc i f sx, [a] => trapIf ((flatHost.trunc i f sx (fbits f a)).map (iword i))
  | .trunc_sat i f sx, [a] => .ok (iword i (flatHost.truncSat i f sx (fbits f a)))
  | .demote, [a] => .ok (flatHost.demote a).toUInt64
  | .promote, [a] => .ok (flatHost.promote a.toUInt32)
  | .reinterpret_i _, [a] | .reinterpret_f _, [a] => .ok a
  | _, _ => .error "flat IR: operation arity"

def liftE {α} (x : Except String α) : FM α := match x with
  | .ok a => pure a
  | .error e => throw e

def readWord (a : Nat) : FM UInt64 := do
  match (← get).mem[a]? with
  | some (some w) => pure w
  | some none => throw s!"flat IR: read of an unwritten word at {a}"
  | none => throw s!"flat IR: read outside a live range at {a}"

def writeWord (a : Nat) (w : UInt64) : FM Unit := do
  match (← get).mem[a]? with
  | some _ => modify fun s => { s with mem := s.mem.insert a (some w) }
  | none => throw s!"flat IR: write outside a live range at {a}"

/-- The byte at `a`: byte `a % 8` of the word holding it, which must be written. -/
def readByte (a : Nat) : FM UInt64 := do
  let w ← readWord (a - a % 8)
  pure ((w >>> (8 * (a % 8)).toUInt64) &&& 0xff)

/-- Write the low byte of `v` at `a`, keeping the word's other bytes (`0` in an unwritten word). -/
def writeByte (a : Nat) (v : UInt64) : FM Unit := do
  let wa := a - a % 8
  let old ← match (← get).mem[wa]? with
    | some (some w) => pure w
    | some none => pure 0
    | none => throw s!"flat IR: write outside a live range at {a}"
  let sh := (8 * (a % 8)).toUInt64
  writeWord wa ((old &&& ~~~(0xff <<< sh)) ||| ((v &&& 0xff) <<< sh))

/-- The 4 bytes at `a` (a multiple of 4): half `a % 8 / 4` of the word holding them, which must be
written. -/
def readHalf (a : Nat) : FM UInt64 := do
  if a % 4 != 0 then throw s!"flat IR: a 4-byte read at {a}, not a multiple of 4"
  let w ← readWord (a - a % 8)
  pure ((w >>> (8 * (a % 8)).toUInt64) &&& 0xffffffff)

/-- Write the low 4 bytes of `v` at `a`, keeping the word's other half (`0` in an unwritten word). -/
def writeHalf (a : Nat) (v : UInt64) : FM Unit := do
  if a % 4 != 0 then throw s!"flat IR: a 4-byte write at {a}, not a multiple of 4"
  let wa := a - a % 8
  let old ← match (← get).mem[wa]? with
    | some (some w) => pure w
    | some none => pure 0
    | none => throw s!"flat IR: write outside a live range at {a}"
  let sh := (8 * (a % 8)).toUInt64
  writeWord wa ((old &&& ~~~(0xffffffff <<< sh)) ||| ((v &&& 0xffffffff) <<< sh))

def allocRange (n : Nat) : FM UInt64 := do
  if n == 0 then throw "flat IR: allocation of no words"
  let s ← get
  let a := s.next
  let mem := (List.range n).foldl (fun m i => m.insert (a + 8 * i) none) s.mem
  set { s with mem, ranges := s.ranges.insert a n, next := a + 8 * n + 8,
               allocs := s.allocs + 1 }
  pure a.toUInt64

def freeRange (a : Nat) : FM Unit := do
  let s ← get
  match s.ranges[a]? with
  | some n =>
    let mem := (List.range n).foldl (fun m i => m.erase (a + 8 * i)) s.mem
    set { s with mem, ranges := s.ranges.erase a }
  | none =>
    -- The read-only data is not freed (a literal's view, `litTab`).
    if a < s.staticEnd then pure ()
    else throw s!"flat IR: free of {a}, not the start of a live range"

/-- The slot at word `off` of the current frame, `n` words, starts its life: its address. -/
def startSlot (off n : Nat) : FM UInt64 := do
  let s ← get
  let some (fp, w) := s.frames.head? | throw "flat IR: a slot outside a function"
  if off + n > w then throw s!"flat IR: a slot past its frame of {w} words"
  let a := fp + 8 * off
  if s.slots.contains a then throw s!"flat IR: the slot at {a} is already live"
  let mem := (List.range n).foldl (fun m i => m.insert (a + 8 * i) none) s.mem
  set { s with mem, slots := s.slots.insert a n, slotsStarted := s.slotsStarted + 1 }
  pure a.toUInt64

/-- End the life of the slot at `a`. -/
def endSlot (a : Nat) : FM Unit := do
  let s ← get
  match s.slots[a]? with
  | some n =>
    let mem := (List.range n).foldl (fun m i => m.erase (a + 8 * i)) s.mem
    set { s with mem, slots := s.slots.erase a }
  | none => throw s!"flat IR: unslot of {a}, not a live slot"

/-- End the life of every slot of the current frame: it returns, or tail-calls. -/
def endFrame : FM Unit := do
  let some (fp, w) := (← get).frames.head? | pure ()
  for i in [0:w] do
    if (← get).slots.contains (fp + 8 * i) then endSlot (fp + 8 * i)

/-- The first read of the arguments counts the runtime's reservation of their memory. -/
def readArgs : FM Unit :=
  modify fun s => if s.argsRead then s else { s with argsRead := true, allocs := s.allocs + 1 }

def setLocal (fr : Array (Option UInt64)) (i : Nat) (v : UInt64) : FM (Array (Option UInt64)) :=
  if i < fr.size then pure (fr.set! i (some v)) else throw s!"flat IR: no local {i}"

def setLocals (fr : Array (Option UInt64)) : List Nat → List UInt64 → FM (Array (Option UInt64))
  | [], [] => pure fr
  | i :: is, v :: vs => do setLocals (← setLocal fr i v) is vs
  | _, _ => throw "flat IR: a call's results and its destinations differ in number"

def getLocal (fr : Array (Option UInt64)) (i : Nat) : FM UInt64 :=
  match fr[i]? with
  | some (some v) => pure v
  | some none => throw s!"flat IR: local {i} read before it is written"
  | none => throw s!"flat IR: no local {i}"

mutual
def evalExp (p : Prog) : Nat → Array (Option UInt64) → Exp → FM UInt64
  | 0, _, _ => throw "flat IR: out of fuel"
  | n + 1, fr, e =>
    match e with
    | .loc i => getLocal fr i
    | .c64 k => pure k
    | .c32 k => pure k.toUInt64
    | .load a off => do
        let a ← evalExp p n fr a
        modify fun st => { st with loads := st.loads + 1 }
        readWord (a.toNat + 8 * off)
    | .load8 a => do
        let a ← evalExp p n fr a
        modify fun st => { st with loads := st.loads + 1 }
        readByte a.toNat
    | .load32 a => do
        let a ← evalExp p n fr a
        modify fun st => { st with loads := st.loads + 1 }
        readHalf a.toNat
    | .op o args => do liftE (evalOp o (← evalArgs p n fr args))
    | .alloc w => do allocRange (← evalExp p n fr w).toNat
    | .slot off w => startSlot off w
    | .live => do pure (← get).ranges.size.toUInt64
    | .getc fd => do
        let fd ← evalExp p n fr fd
        let ar := fd == argsFd.toUInt64
        if fd != 0 && !ar then throw s!"flat IR: read from fd {fd}"
        if ar then readArgs
        let s ← get
        match (if ar then s.args else s.input) with
        | [] => pure 0xFFFFFFFFFFFFFFFF
        | b :: bs => do
          set (if ar then { s with args := bs } else { s with input := bs }); pure b.toUInt64
    | .getv fd a k => do
        let fd ← evalExp p n fr fd
        let a ← evalExp p n fr a
        let k ← evalExp p n fr k
        let ar := fd == argsFd.toUInt64
        if fd != 0 && !ar then throw s!"flat IR: read from fd {fd}"
        if ar then readArgs
        let s ← get
        let src := if ar then s.args else s.input
        let bs := src.take k.toNat
        set (if ar then { s with args := src.drop k.toNat } else { s with input := src.drop k.toNat })
        for (b, i) in bs.zipIdx do writeByte (a.toNat + i) b.toUInt64
        pure bs.length.toUInt64
    | .now c => do readWord (← evalExp p n fr c).toNat
    | .stat 0 => do pure (← get).allocs.toUInt64
    | .stat 1 => do pure (← get).indirect.toUInt64
    | .stat _ => do pure (← get).copies.toUInt64
    | .data off => pure (dataBase + off).toUInt64
    | .gep a k => do pure ((← evalExp p n fr a) + (← evalExp p n fr k))

def evalArgs (p : Prog) : Nat → Array (Option UInt64) → List Exp → FM (List UInt64)
  | 0, _, _ => throw "flat IR: out of fuel"
  | _, _, [] => pure []
  | n + 1, fr, e :: es => do
    let v ← evalExp p n fr e
    let vs ← evalArgs p n fr es
    pure (v :: vs)

/-- Call function `f` on `args`, expecting `results` results (`none`: a tail call, whose results
are the caller's). -/
def callFn (p : Prog) : Nat → Nat → List UInt64 → Option Nat → FM (List UInt64)
  | 0, _, _, _ => throw "flat IR: out of fuel"
  | n + 1, f, args, results => do
    let some fn := p.fns[f]? | throw s!"flat IR: no function {f}"
    if args.length != fn.params then throw s!"flat IR: {fn.name} takes {fn.params} arguments"
    if let some k := results then
      if k != fn.results then throw s!"flat IR: {fn.name} answers {fn.results} results, not {k}"
    -- The locals start unwritten, and reading one is an error: the Wasm lowering's
    -- `compactLocals` shares a local's number between locals whose occurrences do not overlap,
    -- which is sound only where each is written before it is read.
    let fr := (args.map some ++ List.replicate fn.locals none).toArray
    -- The frame: a fresh range of addresses, as a stack frame's is when the stack is reused.
    let fp := (← get).next
    modify fun st => { st with next := st.next + (if fn.frame == 0 then 0 else 8 * fn.frame + 8),
                               frames := (fp, fn.frame) :: st.frames }
    let r ← execBlock p n fr fn.body
    endFrame
    modify fun st => { st with frames := st.frames.drop 1 }
    match r with
    | (_, some r) =>
      if r.length != fn.results then throw s!"flat IR: {fn.name} returns {r.length} results"
      pure r
    | (_, none) => throw s!"flat IR: {fn.name} ends without returning"

/-- Run statements; `some r` when one returns `r`. -/
def execBlock (p : Prog) : Nat → Array (Option UInt64) → List Stmt →
    FM (Array (Option UInt64) × Option (List UInt64))
  | 0, _, _ => throw "flat IR: out of fuel"
  | _, fr, [] => pure (fr, none)
  | n + 1, fr, s :: ss => do
    let (fr, r) ← execStmt p n fr s
    match r with
    | some v => pure (fr, some v)
    | none => execBlock p n fr ss

def execStmt (p : Prog) : Nat → Array (Option UInt64) → Stmt → FM (Array (Option UInt64) × Option (List UInt64))
  | 0, _, _ => throw "flat IR: out of fuel"
  | n + 1, fr, s =>
    match s with
    | .set i e => do pure (← setLocal fr i (← evalExp p n fr e), none)
    | .store a off v => do
        let a ← evalExp p n fr a
        let v ← evalExp p n fr v
        modify fun st => { st with stores := st.stores + 1 }
        writeWord (a.toNat + 8 * off) v
        pure (fr, none)
    | .store8 a v => do
        let a ← evalExp p n fr a
        let v ← evalExp p n fr v
        modify fun st => { st with stores := st.stores + 1 }
        writeByte a.toNat v
        pure (fr, none)
    | .store32 a v => do
        let a ← evalExp p n fr a
        let v ← evalExp p n fr v
        modify fun st => { st with stores := st.stores + 1 }
        writeHalf a.toNat v
        pure (fr, none)
    | .free a => do freeRange (← evalExp p n fr a).toNat; pure (fr, none)
    | .unslot a => do endSlot (← evalExp p n fr a).toNat; pure (fr, none)
    | .out b => do
        let b ← evalExp p n fr b
        modify fun st => { st with out := st.out.push b.toUInt8 }
        pure (fr, none)
    | .putv fd a k => do
        let fd ← evalExp p n fr fd
        let a ← evalExp p n fr a
        let k ← evalExp p n fr k
        let bs ← (List.range k.toNat).mapM fun i => readByte (a.toNat + i)
        match fd with
        | 1 => modify fun st => { st with out := bs.foldl (fun o b => o.push b.toUInt8) st.out }
        | 2 => modify fun st => { st with err := bs.foldl (fun o b => o.push b.toUInt8) st.err }
        | _ => throw s!"flat IR: write to fd {fd}"
        pure (fr, none)
    | .sleep c ns => do
        let a ← evalExp p n fr c
        let ns ← evalExp p n fr ns
        let t ← readWord a.toNat
        writeWord a.toNat (sleptNs t ns)
        pure (fr, none)
    | .putc fd b => do
        let fd ← evalExp p n fr fd
        let b ← evalExp p n fr b
        match fd with
        | 1 => modify fun st => { st with out := st.out.push b.toUInt8 }
        | 2 => modify fun st => { st with err := st.err.push b.toUInt8 }
        | _ => throw s!"flat IR: write to fd {fd}"
        pure (fr, none)
    | .ite c t e => do
        if (← evalExp p n fr c) != 0 then execBlock p n fr t else execBlock p n fr e
    | .call ds f args => do
        let rs ← callFn p n f (← evalArgs p n fr args) (some ds.length)
        pure (← setLocals fr ds rs, none)
    | .switch e cs d => do
        match cs[(← evalExp p n fr e).toNat]? with
        | some b => execBlock p n fr b
        | none => execBlock p n fr d
    | .ret es => do pure (fr, some (← evalArgs p n fr es))
    | .tailCall f args => do
        -- The caller's frame is given back before the callee runs.
        let vs ← evalArgs p n fr args
        endFrame
        pure (fr, some (← callFn p n f vs none))
    | .tick => do
        modify fun st => { st with indirect := st.indirect + 1 }
        pure (fr, none)
    | .tickCopy => do
        modify fun st => { st with copies := st.copies + 1 }
        pure (fr, none)
    | .tickBound => do
        modify fun st => { st with bounds := st.bounds + 1 }
        pure (fr, none)
    | .status e => do
        let c ← evalExp p n fr e
        modify fun st => { st with status := c.toUInt32 }
        pure (fr, none)
    | .trap => throw "flat IR: trap"
end

/-- The memory operations of a run: its loads, its stores and its bounds checks; and the frame
slots it started. -/
structure MemCounts where
  loads : Nat
  stores : Nat
  bounds : Nat
  slots : Nat := 0

/-- Run the entry function on the standard input `input`: what it writes, and its memory
operations. -/
def interpMem (fuel : Nat) (p : Prog) (input : List UInt8) (args : List UInt8 := []) :
    Except String (Output × MemCounts) := do
  -- The read-only data, word by word, little-endian; the heap past it.
  let L := p.data.size
  let mem : Std.HashMap Nat (Option UInt64) := (List.range ((L + 7) / 8)).foldl (fun m k =>
    let w := (List.range 8).foldl (fun acc j =>
      acc ||| ((p.data.getD (8 * k + j) 0).toUInt64 <<< (8 * j).toUInt64)) (0 : UInt64)
    m.insert (dataBase + 8 * k) (some w)) {}
  let next := if L == 0 then 8 else staticEnd L + 8
  let (_, s) ← (callFn p fuel p.entry [] (some 0)).run
    { mem, ranges := {}, next, input, args, out := .empty, err := .empty,
      staticEnd := if L == 0 then 0 else staticEnd L }
  pure (⟨s.out, s.err, s.status⟩, { loads := s.loads, stores := s.stores, bounds := s.bounds, slots := s.slotsStarted })

/-- Run the entry function on the standard input `input`: what it writes. -/
def interp (fuel : Nat) (p : Prog) (input : List UInt8) (args : List UInt8 := []) :
    Except String Output :=
  (·.1) <$> interpMem fuel p input args

end Backend.Flat

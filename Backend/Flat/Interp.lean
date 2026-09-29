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
Numeric operations are `wasmHost`'s; an instruction where Wasm traps is an error.
-/

namespace Backend.Flat
open BoCa

structure FState where
  /-- Every word of a live range; `none` until written. -/
  mem : Std.HashMap Nat (Option UInt64)
  /-- Live ranges: start ↦ length in words. -/
  ranges : Std.HashMap Nat Nat
  next : Nat
  /-- The standard input not yet read. -/
  input : List UInt8
  out : ByteArray
  err : ByteArray
  /-- Allocations so far. -/
  allocs : Nat := 0
  /-- Dispatched calls so far. -/
  indirect : Nat := 0
  /-- Copies of a variable at a non-trivial type so far. -/
  copies : Nat := 0

abbrev FM := StateT FState (Except String)

def toBit (b : Bool) : UInt64 := if b then 1 else 0

def trapIf : Option UInt64 → Except String UInt64
  | some r => .ok r
  | none => .error "flat IR: trap in an integer instruction"

/-- A numeric operation on words; 32-bit operands are the low halves. -/
def evalOp : HostOp → List UInt64 → Except String UInt64
  | .bin .w32 o, [a, b] => .ok (wasmHost.bin32 o a.toUInt32 b.toUInt32).toUInt64
  | .bin .w64 o, [a, b] => .ok (wasmHost.bin64 o a b)
  | .div .w32 o, [a, b] => trapIf ((wasmHost.div32 o a.toUInt32 b.toUInt32).map (·.toUInt64))
  | .div .w64 o, [a, b] => trapIf (wasmHost.div64 o a b)
  | .un .w32 o, [a] => .ok (wasmHost.un32 o a.toUInt32).toUInt64
  | .un .w64 o, [a] => .ok (wasmHost.un64 o a)
  | .eqz .w32, [a] => .ok (toBit (wasmHost.eqz32 a.toUInt32))
  | .eqz .w64, [a] => .ok (toBit (wasmHost.eqz64 a))
  | .rel .w32 o, [a, b] => .ok (toBit (wasmHost.rel32 o a.toUInt32 b.toUInt32))
  | .rel .w64 o, [a, b] => .ok (toBit (wasmHost.rel64 o a b))
  | .wrap, [a] => .ok (wasmHost.wrap a).toUInt64
  | .extend_s, [a] => .ok (wasmHost.extendS a.toUInt32)
  | .extend_u, [a] => .ok (wasmHost.extendU a.toUInt32)
  | .extend32_s, [a] => .ok (wasmHost.extend32S a)
  | .wrap8, [a] => .ok (wasmHost.wrap8 a.toUInt32).toUInt64
  | .extend8_u, [a] => .ok (wasmHost.extend8U a.toUInt8).toUInt64
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
  | none => throw s!"flat IR: free of {a}, not the start of a live range"

def setLocal (fr : Array UInt64) (i : Nat) (v : UInt64) : FM (Array UInt64) :=
  if i < fr.size then pure (fr.set! i v) else throw s!"flat IR: no local {i}"

def setLocals (fr : Array UInt64) : List Nat → List UInt64 → FM (Array UInt64)
  | [], [] => pure fr
  | i :: is, v :: vs => do setLocals (← setLocal fr i v) is vs
  | _, _ => throw "flat IR: a call's results and its destinations differ in number"

def getLocal (fr : Array UInt64) (i : Nat) : FM UInt64 :=
  match fr[i]? with
  | some v => pure v
  | none => throw s!"flat IR: no local {i}"

mutual
def evalExp (p : Prog) : Nat → Array UInt64 → Exp → FM UInt64
  | 0, _, _ => throw "flat IR: out of fuel"
  | n + 1, fr, e =>
    match e with
    | .loc i => getLocal fr i
    | .c64 k => pure k
    | .c32 k => pure k.toUInt64
    | .load a off => do readWord ((← evalExp p n fr a).toNat + 8 * off)
    | .load8 a => do readByte (← evalExp p n fr a).toNat
    | .op o args => do liftE (evalOp o (← evalArgs p n fr args))
    | .alloc w => do allocRange (← evalExp p n fr w).toNat
    | .live => do pure (← get).ranges.size.toUInt64
    | .getc fd => do
        let fd ← evalExp p n fr fd
        if fd != 0 then throw s!"flat IR: read from fd {fd}"
        let s ← get
        match s.input with
        | [] => pure 0xFFFFFFFFFFFFFFFF
        | b :: bs => do set { s with input := bs }; pure b.toUInt64
    | .stat 0 => do pure (← get).allocs.toUInt64
    | .stat 1 => do pure (← get).indirect.toUInt64
    | .stat _ => do pure (← get).copies.toUInt64

def evalArgs (p : Prog) : Nat → Array UInt64 → List Exp → FM (List UInt64)
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
    let fr := (args ++ List.replicate fn.locals 0).toArray
    match ← execBlock p n fr fn.body with
    | (_, some r) =>
      if r.length != fn.results then throw s!"flat IR: {fn.name} returns {r.length} results"
      pure r
    | (_, none) => throw s!"flat IR: {fn.name} ends without returning"

/-- Run statements; `some r` when one returns `r`. -/
def execBlock (p : Prog) : Nat → Array UInt64 → List Stmt →
    FM (Array UInt64 × Option (List UInt64))
  | 0, _, _ => throw "flat IR: out of fuel"
  | _, fr, [] => pure (fr, none)
  | n + 1, fr, s :: ss => do
    let (fr, r) ← execStmt p n fr s
    match r with
    | some v => pure (fr, some v)
    | none => execBlock p n fr ss

def execStmt (p : Prog) : Nat → Array UInt64 → Stmt → FM (Array UInt64 × Option (List UInt64))
  | 0, _, _ => throw "flat IR: out of fuel"
  | n + 1, fr, s =>
    match s with
    | .set i e => do pure (← setLocal fr i (← evalExp p n fr e), none)
    | .store a off v => do
        let a ← evalExp p n fr a
        let v ← evalExp p n fr v
        writeWord (a.toNat + 8 * off) v
        pure (fr, none)
    | .store8 a v => do
        let a ← evalExp p n fr a
        let v ← evalExp p n fr v
        writeByte a.toNat v
        pure (fr, none)
    | .free a => do freeRange (← evalExp p n fr a).toNat; pure (fr, none)
    | .out b => do
        let b ← evalExp p n fr b
        modify fun st => { st with out := st.out.push b.toUInt8 }
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
    | .tailCall f args => do pure (fr, some (← callFn p n f (← evalArgs p n fr args) none))
    | .tick => do
        modify fun st => { st with indirect := st.indirect + 1 }
        pure (fr, none)
    | .tickCopy => do
        modify fun st => { st with copies := st.copies + 1 }
        pure (fr, none)
    | .trap => throw "flat IR: trap"
end

/-- Run the entry function on the standard input `input`: what it writes. -/
def interp (fuel : Nat) (p : Prog) (input : List UInt8) : Except String Output := do
  let (_, s) ← (callFn p fuel p.entry [] (some 0)).run { mem := {}, ranges := {}, next := 8, input, out := .empty, err := .empty }
  pure ⟨s.out, s.err⟩

end Backend.Flat

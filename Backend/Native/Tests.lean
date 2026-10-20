import Backend.Flat.Interp
import Backend.Clos.Types

/-!
# Backend — tests of the native target  `[spec §40]`

## The host operations, native against the Lean host

One flat-IR program that applies every host operation (`HostOp`, SPEC §8, §37) to a table of
operands and prints each operand and result in hexadecimal: `bcc hostops flat` runs it at the
flat-IR interpreter, whose operations are `flatHost`'s (`wasmHost` at a NaN resolution), and
`bcc hostops native` built natively; `scripts/compile-native.sh` requires the two outputs to be
equal. The operands are read from standard input (`hostTest`'s second part), so `clang` cannot fold an operation at compile time: what runs is
the instruction the native backend emits. A partial operation is applied only where it has an
answer (the flat IR tests before it divides or truncates, SPEC §39). A NaN answered by a float
operation's arithmetic prints as `nan`, since its sign and payload are not specified; the
operations that act on bits (`abs`, `neg`, `copysign`, `reinterpret`) print theirs.

## Tail calls in constant stack

`tailTest n` loops `n` times through tail calls between functions of different parameters, at
two widths of result: nine words (through the result pointer) and two (by value). `bcc tailcalls
n` builds it natively and runs it on a stack of 64 KiB (`BC_STACK`,
`Backend/Native/Runtime.lean`), where a frame per call would exhaust the stack within a few
thousand calls; its output must be `tailExpected n`.
-/

namespace Backend.Native.Tests
open BoCa Backend.Flat

def ints : List UInt64 :=
  [0, 1, 2, 3, 7, 8, 31, 32, 33, 63, 64, 65, 0x7f, 0x80, 0xff, 0x8000, 0xffff, 0x7fffffff,
   0x80000000, 0xffffffff, 0x100000000, 0x7fffffffffffffff, 0x8000000000000000,
   0xfffffffffffffffe, 0xffffffffffffffff, 0xffffffff80000000, 0xdeadbeefcafebabe,
   0x0123456789abcdef]

def f64s : List UInt64 :=
  [0x0, 0x8000000000000000, 0x3FF0000000000000, 0xBFF0000000000000, 0x3FE0000000000000,
   0x3FF8000000000000, 0x4004000000000000, 0xC004000000000000, 0x400C000000000000,
   0x7FF0000000000000, 0xFFF0000000000000, 0x7FF8000000000000, 0x7FF4000000000001,
   0xFFF8000000000123, 0x7FEFFFFFFFFFFFFF, 0x0000000000000001, 0x41DFFFFFFFC00000,
   0x41E0000000000000, 0xC1E0000000200000, 0xC1E0000000000000, 0x41F0000000000000,
   0x43E0000000000000, 0xC3E0000000000000, 0x43F0000000000000, 0x400D99999999999A,
   0x7E37E43C8800759C]

def f32s : List UInt64 :=
  [0x0, 0x80000000, 0x3F800000, 0xBF800000, 0x3F000000, 0x3FC00000, 0x40200000, 0xC0200000,
   0x40600000, 0x7F800000, 0xFF800000, 0x7FC00000, 0x7FA00001, 0xFFC00123, 0x7F7FFFFF, 0x1,
   0x4EFFFFFF, 0x4F000000, 0xCF000000, 0x4F800000, 0x5F000000, 0xDF000000, 0x5F800000,
   0x406CCCCD]

/-- The operations, each with its arity. -/
def ops : List (HostOp × Nat) :=
  let iw : List Width := [.w32, .w64]
  let fw : List FWidth := [.f32, .f64]
  let iws : List IWidth := [.i32, .i64]
  let sxs : List Sx := [.s, .u]
  iw.flatMap (fun w =>
    ([BinOp.add, .sub, .mul, .and, .or, .xor, .shl, .shr_s, .shr_u, .rotl, .rotr].map
      (fun o => (HostOp.bin w o, 2))) ++
    ([DivOp.div_s, .div_u, .rem_s, .rem_u].map (fun o => (HostOp.div w o, 2))) ++
    ([UnOp.clz, .ctz, .popcnt, .extend8_s, .extend16_s].map (fun o => (HostOp.un w o, 1))) ++
    [(HostOp.eqz w, 1)] ++
    ([RelOp.eq, .ne, .lt_s, .lt_u, .le_s, .le_u, .gt_s, .gt_u, .ge_s, .ge_u].map
      (fun o => (HostOp.rel w o, 2)))) ++
  [(.wrap, 1), (.extend_s, 1), (.extend_u, 1), (.extend32_s, 1), (.wrap8, 1), (.extend8_u, 1)] ++
  fw.flatMap (fun f =>
    ([FBinOp.add, .sub, .mul, .div, .min, .max, .copysign].map (fun o => (HostOp.fbin f o, 2))) ++
    ([FUnOp.abs, .neg, .sqrt, .ceil, .floor, .trunc, .nearest].map
      (fun o => (HostOp.fun1 f o, 1))) ++
    ([FRelOp.eq, .ne, .lt, .gt, .le, .ge].map (fun o => (HostOp.frel f o, 2))) ++
    iws.flatMap (fun i => sxs.flatMap (fun sx =>
      [(HostOp.convert f i sx, 1), (HostOp.trunc i f sx, 1), (HostOp.trunc_sat i f sx, 1)])) ++
    [(HostOp.reinterpret_i f, 1), (HostOp.reinterpret_f f, 1)]) ++
  [(.demote, 1), (.promote, 1)]

/-- The operands of an operation's width. -/
def operands (o : HostOp) : List UInt64 :=
  match Flat.hostArgWidth o with
  | .f32 => f32s
  | .f64 => f64s
  | .w32 => ints.map (· &&& 0xffffffff) ++ [0xdeadbeef00000005]
  | _ => ints

/-- An arithmetic float result, whose NaN's sign and payload are not specified (SPEC §37). -/
def nanFree : HostOp → Option FWidth
  | .fbin f o => match o with | .copysign => none | _ => some f
  | .fun1 f o => match o with | .abs | .neg => none | _ => some f
  | .demote => some .f32
  | .promote => some .f64
  | _ => none

/-- The cases of an operation: its operand tuples where it has an answer. -/
def cases (o : HostOp) (arity : Nat) : List (List UInt64) :=
  let xs := operands o
  let tuples := if arity == 1 then xs.map ([·]) else xs.flatMap fun a => xs.map ([a, ·])
  tuples.filter fun t => match evalOp o t with
    | .ok _ => true
    | .error _ => false

def nm : HostOp → String := fun o => (reprStr o).replace "\n" " "

/-- Write the bytes of `s`. -/
def text (s : String) : List Stmt := outStr s

/-- Function 1: write the word in its parameter as 16 hexadecimal digits. -/
def hexFn : Fn :=
  let digit (j : Nat) : Stmt :=
    let n := and64 (shr64 (.loc 0) (.c64 (60 - 4 * j).toUInt64)) (.c64 15)
    .out (add64 (add64 (.c64 48) n) (mul64 (.op (.rel .w64 .gt_u) [n, .c64 9]) (.c64 39)))
  { name := "hex", params := 1, results := 0, locals := 0,
    body := (List.range 16).map digit ++ [.ret []] }

/-- Function `k`: apply `o` to each case of `arity` words in `[p, e)`, and write a line. -/
def loopFn (k : Nat) (o : HostOp) (arity : Nat) : Fn :=
  let args := (List.range arity).map (Exp.load (.loc 0))
  let show_ : List Stmt := match nanFree o with
    | some f => [.ite (.op (.frel f .ne) [.loc 2, .loc 2]) (text "nan") [.call [] 1 [.loc 2]]]
    | none => [.call [] 1 [.loc 2]]
  { name := s!"case {nm o}", params := 2, results := 0, locals := 1,
    body := [.ite (eq64 (.loc 0) (.loc 1)) [.ret []] [],
      .set 2 (.op o args)] ++
      (List.range arity).flatMap (fun i => [.call [] 1 [.load (.loc 0) i], .out (.c64 32)]) ++
      text "-> " ++ show_ ++ text "\n" ++
      [.tailCall k [add64 (.loc 0) (.c64 (8 * arity).toUInt64), .loc 1]] }

/-- The program and its standard input. -/
def hostTest : Prog × ByteArray := Id.run do
  let blank : Fn := { name := "entry", params := 0, results := 0, locals := 1, body := [] }
  let mut fns : Array Fn := #[blank, hexFn]
  let mut words : Array UInt64 := #[]
  let mut calls : List Stmt := []
  for (o, arity) in ops do
    let k := fns.size
    let cs := cases o arity
    let lo := words.size
    for c in cs do
      for w in c do words := words.push w
    fns := fns.push (loopFn k o arity)
    calls := calls ++ text s!"== {nm o}\n" ++
      [.call [] k [add64 (.loc 0) (.c64 (8 * lo).toUInt64),
        add64 (.loc 0) (.c64 (8 * words.size).toUInt64)]]
  let n8 := (8 * words.size).toUInt64
  let ebody : List Stmt := [.set 0 (.alloc (.c64 words.size.toUInt64)),
      .ite (eq64 (.getv (.c64 0) (.loc 0) (.c64 n8)) (.c64 n8)) [] (text "short input\n" ++ [.ret []])] ++
      calls ++ [.free (.loc 0), .ret []]
  let entry : Fn := { blank with body := ebody }
  fns := fns.set! 0 entry
  let input := words.foldl (fun (b : ByteArray) w =>
    (List.range 8).foldl (fun b j => b.push (w >>> (8 * j).toUInt64).toUInt8) b) ByteArray.empty
  ({ fns, entry := 0 }, input)

/-- `a` loops down `n` (local 0), adding to `acc` (local 1): `a(n, acc)` tail-calls
`b(n - 1, acc + n, 7, 7)`, which tail-calls `a(n, acc + 7·7)`; at `0`, the `results` words
`acc, acc + 1, …`. Functions `k` and `k + 1`. -/
def tailPair (k results : Nat) : List Fn :=
  [{ name := s!"a{results}", params := 2, results, locals := 0,
     body := [.ite (eqz64 (.loc 0))
       [.ret ((List.range results).map fun i => add64 (.loc 1) (.c64 i.toUInt64))] [],
       .tailCall (k + 1) [.op (.bin .w64 .sub) [.loc 0, .c64 1], add64 (.loc 1) (.loc 0),
         .c64 7, .c64 7]] },
   { name := s!"b{results}", params := 4, results, locals := 0,
     body := [.tailCall k [.loc 0, add64 (.loc 1) (mul64 (.loc 2) (.loc 3))]] }]

/-- The loop of `n` turns at nine results and at two; it writes the first and last result of
each, in hexadecimal. -/
def tailTest (n : Nat) : Prog :=
  let entry : Fn :=
    { name := "entry", params := 0, results := 0, locals := 11, body := [
      .call (List.range 9) 2 [.c64 n.toUInt64, .c64 0],
      .call [] 1 [.loc 0], .out (.c64 32), .call [] 1 [.loc 8], .out (.c64 10),
      .call [9, 10] 4 [.c64 n.toUInt64, .c64 0],
      .call [] 1 [.loc 9], .out (.c64 32), .call [] 1 [.loc 10], .out (.c64 10), .ret []] }
  { fns := #[entry, hexFn] ++ (tailPair 2 9).toArray ++ (tailPair 4 2).toArray, entry := 0 }

def hex16 (w : UInt64) : String :=
  let d := String.ofList (Nat.toDigits 16 w.toNat)
  "".pushn '0' (16 - d.length) ++ d

/-- What `tailTest n` writes. -/
def tailExpected (n : Nat) : String :=
  let acc := (n * (n + 1) / 2 + 49 * n).toUInt64
  let line (r : Nat) := s!"{hex16 acc} {hex16 (acc + (r - 1).toUInt64)}\n"
  line 9 ++ line 2

end Backend.Native.Tests

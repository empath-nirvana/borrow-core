import Backend.Wasm.Syntax
import Backend.Wasm.Runtime
import Backend.Flat.Syntax

/-!
# Backend — WAT printer

The module in the WebAssembly text format, in flat (non-folded) instruction syntax. The runtime
of `Backend/Wasm/Runtime.lean` is inserted as written. This is the one step of the pipeline
that no interpreter observes.
-/

namespace Backend.Wasm
open BoCa

def widthName : Width → String
  | .w32 => "i32"
  | .w64 => "i64"
  | .w8 => "i32"
  | .f32 => "f32"
  | .f64 => "f64"

def binName : BinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .and => "and" | .or => "or"
  | .xor => "xor" | .shl => "shl" | .shr_s => "shr_s" | .shr_u => "shr_u"
  | .rotl => "rotl" | .rotr => "rotr"

def divName : DivOp → String
  | .div_s => "div_s" | .div_u => "div_u" | .rem_s => "rem_s" | .rem_u => "rem_u"

def unName : UnOp → String
  | .clz => "clz" | .ctz => "ctz" | .popcnt => "popcnt"
  | .extend8_s => "extend8_s" | .extend16_s => "extend16_s"

def relName : RelOp → String
  | .eq => "eq" | .ne => "ne" | .lt_s => "lt_s" | .lt_u => "lt_u" | .le_s => "le_s"
  | .le_u => "le_u" | .gt_s => "gt_s" | .gt_u => "gt_u" | .ge_s => "ge_s" | .ge_u => "ge_u"

def fwName : FWidth → String
  | .f32 => "f32" | .f64 => "f64"

def iwName : IWidth → String
  | .i32 => "i32" | .i64 => "i64"

def sxName : Sx → String
  | .s => "s" | .u => "u"

def fbinName : FBinOp → String
  | .add => "add" | .sub => "sub" | .mul => "mul" | .div => "div" | .min => "min"
  | .max => "max" | .copysign => "copysign"

def funName : FUnOp → String
  | .abs => "abs" | .neg => "neg" | .sqrt => "sqrt" | .ceil => "ceil" | .floor => "floor"
  | .trunc => "trunc" | .nearest => "nearest"

def frelName : FRelOp → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt" | .gt => "gt" | .le => "le" | .ge => "ge"

/-- The Wasm instruction of each host operation (§8, §37). -/
def opName : HostOp → String
  | .bin w o => widthName w ++ "." ++ binName o
  | .div w o => widthName w ++ "." ++ divName o
  | .un w o => widthName w ++ "." ++ unName o
  | .eqz w => widthName w ++ ".eqz"
  | .rel w o => widthName w ++ "." ++ relName o
  | .wrap => "i32.wrap_i64"
  | .extend_s => "i64.extend_i32_s"
  | .extend_u => "i64.extend_i32_u"
  | .extend32_s => "i64.extend32_s"
  -- The byte's conversions are word operations (`Flat/Lower.lean`, `hostVals`), never emitted.
  | .wrap8 | .extend8_u => "unreachable"
  | .fbin f o => fwName f ++ "." ++ fbinName o
  | .fun1 f o => fwName f ++ "." ++ funName o
  | .frel f o => fwName f ++ "." ++ frelName o
  | .convert f i sx => fwName f ++ ".convert_" ++ iwName i ++ "_" ++ sxName sx
  | .trunc i f sx => iwName i ++ ".trunc_" ++ fwName f ++ "_" ++ sxName sx
  | .trunc_sat i f sx => iwName i ++ ".trunc_sat_" ++ fwName f ++ "_" ++ sxName sx
  | .demote => "f32.demote_f64"
  | .promote => "f64.promote_f32"
  | .reinterpret_i f => iwName f.int ++ ".reinterpret_" ++ fwName f
  | .reinterpret_f f => fwName f ++ ".reinterpret_" ++ iwName f.int

/-- `(param i64 …) (result i64 …)`. -/
def sigText (params results : Nat) : String :=
  (if params > 0 then " (param" ++ String.join (List.replicate params " i64") ++ ")" else "") ++
  (if results > 0 then " (result" ++ String.join (List.replicate results " i64") ++ ")" else "")

def indent (d : Nat) : String := "".pushn ' ' (2 * d)

def printInstr (d : Nat) : Instr → List String
  | .i32Const n => [indent d ++ s!"i32.const {n.toNat}"]
  | .i64Const n => [indent d ++ s!"i64.const {n.toNat}"]
  | .localGet i => [indent d ++ s!"local.get {i}"]
  | .localSet i => [indent d ++ s!"local.set {i}"]
  | .i64Load off => [indent d ++ s!"i64.load offset={off}"]
  | .i64Store off => [indent d ++ s!"i64.store offset={off}"]
  | .i64Load8U => [indent d ++ "i64.load8_u"]
  | .i64Store8 => [indent d ++ "i64.store8"]
  | .num o => [indent d ++ opName o]
  | .call f => [indent d ++ s!"call {f}"]
  | .returnCall f => [indent d ++ s!"return_call {f}"]
  | .ifElse t e =>
      [indent d ++ "if"] ++ printBody (d + 1) t ++ [indent d ++ "else"] ++ printBody (d + 1) e ++
        [indent d ++ "end"]
  | .block b => [indent d ++ "block"] ++ printBody (d + 1) b ++ [indent d ++ "end"]
  | .br k => [indent d ++ s!"br {k}"]
  | .brTable ts k => [indent d ++ "br_table" ++ String.join (ts.map (s!" {·}")) ++ s!" {k}"]
  | .ret => [indent d ++ "return"]
  | .drop => [indent d ++ "drop"]
  | .unreachable => [indent d ++ "unreachable"]
  | .globalGet g => [indent d ++ s!"global.get {g}"]
  | .globalSet g => [indent d ++ s!"global.set {g}"]
  | .countInd => [indent d ++ "global.get $indirect", indent d ++ "i64.const 1",
      indent d ++ "i64.add", indent d ++ "global.set $indirect"]
  | .countCopy => [indent d ++ "global.get $copies", indent d ++ "i64.const 1",
      indent d ++ "i64.add", indent d ++ "global.set $copies"]
where
  printBody (d : Nat) : List Instr → List String
    | [] => []
    | i :: is => printInstr d i ++ printBody d is

def printFunc (f : Func) : List String :=
  let exp := match f.export? with | some n => s!" (export \"{n}\")" | none => ""
  let sig := sigText f.params f.results
  let locals := if f.locals > 0 then
    [indent 2 ++ "(local" ++ String.join (List.replicate f.locals " i64") ++ ")"] else []
  [indent 1 ++ s!"(func {f.name}{exp}{sig}"] ++ locals ++ printInstr.printBody 2 f.body ++
    [indent 1 ++ ")"]

/-- The read-only data segment: the literals' bytes at `Flat.dataBase`, each as `\xx`. -/
def printData (bs : Array UInt8) : List String :=
  if bs.isEmpty then [] else
  let hex (d : Nat) : Char := if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)
  let esc := String.join (bs.toList.map fun b =>
    "\\" ++ (hex (b.toNat / 16)).toString ++ (hex (b.toNat % 16)).toString)
  [indent 1 ++ s!"(data (i32.const {Flat.dataBase}) \"{esc}\")"]

/-- The bytes of the stack, when the module has one: frames of scoped cells only, so a frame is
a few words. -/
def stackBytes : Nat := 1 <<< 20

/-- The module's text. The stack, when the module has one, starts past the read-only data, and
the heap past the stack. -/
def printModule (m : Module) : String :=
  let L := m.data.size
  let staticEnd := if L == 0 then 16384 else Flat.staticEnd L
  let stackTop := staticEnd + (if m.stack then stackBytes else 0)
  let heap := if m.stack then stackTop else if L == 0 then 16376 else staticEnd
  let pages := (stackTop + 8 + 65535) / 65536
  let rt := ((((runtimeWat.replace "(global $heap (mut i32) (i32.const 16376))"
    s!"(global $heap (mut i32) (i32.const {heap}))").replace "STATIC_END"
    (toString staticEnd)).replace "(global $sp (mut i64) (i64.const 0))"
    s!"(global $sp (mut i64) (i64.const {stackTop}))").replace
    "(global $stackLimit i64 (i64.const 0))"
    s!"(global $stackLimit i64 (i64.const {staticEnd}))").replace
    "(memory (export \"memory\") 1)" s!"(memory (export \"memory\") {pages})"
  let lines := ["(module", rt] ++ printData m.data ++ (m.funcs.flatMap printFunc) ++ [")"]
  "\n".intercalate lines ++ "\n"

end Backend.Wasm

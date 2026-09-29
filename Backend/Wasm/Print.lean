import Backend.Wasm.Syntax
import Backend.Wasm.Runtime

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

/-- The Wasm instruction of each host operation (§8). -/
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

/-- The module's text. -/
def printModule (m : Module) : String :=
  let lines := ["(module", runtimeWat] ++ (m.funcs.flatMap printFunc) ++ [")"]
  "\n".intercalate lines ++ "\n"

end Backend.Wasm

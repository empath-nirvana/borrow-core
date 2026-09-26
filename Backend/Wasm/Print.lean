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

def typeName (arity : Nat) : String := s!"$t{arity}"

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
  | .callIndirect k => [indent d ++ s!"call_indirect (type {typeName k})"]
  | .returnCall f => [indent d ++ s!"return_call {f}"]
  | .returnCallIndirect k => [indent d ++ s!"return_call_indirect (type {typeName k})"]
  | .block body => [indent d ++ "block"] ++ printBody (d + 1) body ++ [indent d ++ "end"]
  | .ifElse t e =>
      [indent d ++ "if"] ++ printBody (d + 1) t ++ [indent d ++ "else"] ++ printBody (d + 1) e ++
        [indent d ++ "end"]
  | .br l => [indent d ++ s!"br {l}"]
  | .brTable ls dflt => [indent d ++ "br_table " ++ " ".intercalate (ls.map toString) ++ s!" {dflt}"]
  | .ret => [indent d ++ "return"]
  | .drop => [indent d ++ "drop"]
  | .unreachable => [indent d ++ "unreachable"]
where
  printBody (d : Nat) : List Instr → List String
    | [] => []
    | i :: is => printInstr d i ++ printBody d is

def printFunc (f : Func) : List String :=
  let exp := match f.export? with | some n => s!" (export \"{n}\")" | none => ""
  let params := String.join ((List.replicate f.params " i64").map id)
  let sig := (if f.params > 0 then s!" (param{params})" else "") ++
    (if f.result then " (result i64)" else "")
  let locals := if f.locals > 0 then
    [indent 2 ++ "(local" ++ String.join (List.replicate f.locals " i64") ++ ")"] else []
  [indent 1 ++ s!"(func {f.name}{exp}{sig}"] ++ locals ++ printInstr.printBody 2 f.body ++
    [indent 1 ++ ")"]

/-- The module's text. -/
def printModule (m : Module) : String :=
  let types := (List.range 5).map fun k =>
    indent 1 ++ s!"(type {typeName k} (func" ++
      (if k > 0 then " (param" ++ String.join (List.replicate k " i64") ++ ")" else "") ++
      " (result i64)))"
  let table := [indent 1 ++ s!"(table {m.table.length} funcref)"] ++
    (if m.table.isEmpty then [] else
      [indent 1 ++ "(elem (i32.const 0) func " ++ " ".intercalate m.table ++ ")"])
  let lines := ["(module", runtimeWat] ++ types ++ table ++ (m.funcs.flatMap printFunc) ++ [")"]
  "\n".intercalate lines ++ "\n"

end Backend.Wasm

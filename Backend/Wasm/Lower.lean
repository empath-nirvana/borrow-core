import Backend.Flat.Syntax
import Backend.Wasm.Syntax

/-!
# Backend — flat IR to Wasm

Each flat-IR function `k` is the Wasm function `$f{k}` over `i64` parameters and locals,
returning `i64`. Expressions become stack code in argument order; an address is wrapped to
`i32` before a memory access or a table index. `ite` is `if`/`else`; `switch` is `br_table`
over nested blocks; a tail call is `return_call`/`return_call_indirect`. A function's body
ends in `unreachable`, since every path of a flat-IR function returns. `_start` calls the
entry and discards its result.
-/

namespace Backend.Wasm
open BoCa Backend.Flat

def fname (k : Nat) : String := s!"$f{k}"

def lowerExp (cnt : Bool) : Flat.Exp → List Instr
  | .loc i => [.localGet i]
  | .c64 n => [.i64Const n]
  | .c32 n => [.i32Const n]
  | .load a off => lowerExp cnt a ++ [.num .wrap, .i64Load (8 * off)]
  | .op o args => lowerArgs args ++ [.num o]
  | .call f args => lowerArgs args ++ [.call (fname f)]
  | .callInd f args => lowerArgs args ++ lowerExp cnt f ++ [.num .wrap] ++ countInd cnt ++
      [.callIndirect args.length]
  | .alloc w => lowerExp cnt w ++ [.call "$alloc"]
  | .live => [.call "$live"]
  | .getc fd => lowerExp cnt fd ++ [.call "$getc"]
  | .stat k => [.globalGet (if k == 0 then "$allocs" else "$indirect")]
where
  countInd (cnt : Bool) : List Instr := if cnt then [.countInd] else []
  lowerArgs : List Flat.Exp → List Instr
    | [] => []
    | e :: es => lowerExp cnt e ++ lowerArgs es

/-- `br_table` over `n` arms: arm `k` is reached by branching out of the `k`-th innermost block;
    after arm `k` (not the last) a branch leaves the switch. -/
def switchCode (scrut : List Instr) (arms : List (List Instr)) : List Instr :=
  let n := arms.length
  let inner : List Instr := scrut ++ [.brTable (List.range n) (n - 1)]
  let rec go : Nat → List (List Instr) → List Instr → List Instr
    | _, [], acc => acc
    | _, [a], acc => [.block acc] ++ a
    | k, a :: as, acc => go (k + 1) as ([.block acc] ++ a ++ [.br (n - 1 - k)])
  [.block (go 0 arms inner)]

def lowerStmt (cnt : Bool) : Flat.Stmt → List Instr
  | .set i e => lowerExp cnt e ++ [.localSet i]
  | .store a off v => lowerExp cnt a ++ [.num .wrap] ++ lowerExp cnt v ++ [.i64Store (8 * off)]
  | .free a => lowerExp cnt a ++ [.call "$free"]
  | .eval e => lowerExp cnt e ++ [.drop]
  | .out b => lowerExp cnt b ++ [.call "$putc"]
  | .putc fd b => lowerExp cnt fd ++ lowerExp cnt b ++ [.call "$putfd"]
  | .ite c t e => lowerExp cnt c ++ [.ifElse (lowerBlock t) (lowerBlock e)]
  | .switch s arms => switchCode (lowerExp cnt s) (lowerArms arms)
  | .ret e => lowerExp cnt e ++ [.ret]
  | .tailCall f args => lowerExp.lowerArgs cnt args ++ [.returnCall (fname f)]
  | .tailCallInd f args =>
      lowerExp.lowerArgs cnt args ++ lowerExp cnt f ++ [.num .wrap] ++ lowerExp.countInd cnt ++ [.returnCallIndirect args.length]
  | .trap => [.unreachable]
where
  lowerBlock : List Flat.Stmt → List Instr
    | [] => []
    | s :: ss => lowerStmt cnt s ++ lowerBlock ss
  lowerArms : List (List Flat.Stmt) → List (List Instr)
    | [] => []
    | a :: as => lowerBlock a :: lowerArms as

def lowerFn (cnt : Bool) (k : Nat) (f : Flat.Fn) : Func where
  name := fname k
  params := f.params
  result := true
  locals := f.locals
  body := lowerStmt.lowerBlock cnt f.body ++ [.unreachable]

/-- The module; with `cnt`, every indirect call adds one to the runtime's count. -/
def lowerProg (p : Flat.Prog) (cnt : Bool := false) : Module where
  funcs := p.fns.toList.zipIdx.map (fun (f, k) => lowerFn cnt k f) ++
    [{ name := "$start", params := 0, result := false, locals := 0,
       body := [.call (fname p.entry), .drop], export? := some "_start" }]
  table := p.table.toList.map fname

end Backend.Wasm

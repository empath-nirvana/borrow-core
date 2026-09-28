import Backend.Flat.Syntax
import Backend.Wasm.Syntax

/-!
# Backend — flat IR to Wasm

Each flat-IR function `k` is the Wasm function `$f{k}` over `i64` parameters and locals,
returning its `i64` results (several, as a multi-value function). Expressions become stack code
in argument order; an address is wrapped to `i32` before a memory access or a table index. A
call's results are popped into its destination locals, last first. `ite` is `if`/`else`; a tail
call is `return_call`/`return_call_indirect`, whose callee has the caller's results. A function's
body ends in `unreachable`, since every path of a flat-IR function returns. `_start` calls the
entry.
-/

namespace Backend.Wasm
open BoCa Backend.Flat

def fname (k : Nat) : String := s!"$f{k}"

def lowerExp : Flat.Exp → List Instr
  | .loc i => [.localGet i]
  | .c64 n => [.i64Const n]
  | .c32 n => [.i32Const n]
  | .load a off => lowerExp a ++ [.num .wrap, .i64Load (8 * off)]
  | .op o args => lowerArgs args ++ [.num o]
  | .alloc w => lowerExp w ++ [.call "$alloc"]
  | .live => [.call "$live"]
  | .getc fd => lowerExp fd ++ [.call "$getc"]
  | .stat k => [.globalGet (if k == 0 then "$allocs" else "$indirect")]
where
  lowerArgs : List Flat.Exp → List Instr
    | [] => []
    | e :: es => lowerExp e ++ lowerArgs es

/-- Pop a call's results into `ds`. -/
def popInto (ds : List Nat) : List Instr := ds.reverse.map .localSet

/-- A statement of a function of `res` results; with `cnt`, every indirect call adds one to the
runtime's count. -/
def lowerStmt (cnt : Bool) (res : Nat) : Flat.Stmt → List Instr
  | .set i e => lowerExp e ++ [.localSet i]
  | .store a off v => lowerExp a ++ [.num .wrap] ++ lowerExp v ++ [.i64Store (8 * off)]
  | .free a => lowerExp a ++ [.call "$free"]
  | .out b => lowerExp b ++ [.call "$putc"]
  | .putc fd b => lowerExp fd ++ lowerExp b ++ [.call "$putfd"]
  | .ite c t e => lowerExp c ++ [.ifElse (lowerBlock t) (lowerBlock e)]
  | .call ds f args => lowerExp.lowerArgs args ++ [.call (fname f)] ++ popInto ds
  | .callInd ds f args =>
      lowerExp.lowerArgs args ++ lowerExp f ++ [.num .wrap] ++ count ++
        [.callIndirect args.length ds.length] ++ popInto ds
  | .ret es => lowerExp.lowerArgs es ++ [.ret]
  | .tailCall f args => lowerExp.lowerArgs args ++ [.returnCall (fname f)]
  | .tailCallInd f args =>
      lowerExp.lowerArgs args ++ lowerExp f ++ [.num .wrap] ++ count ++
        [.returnCallIndirect args.length res]
  | .trap => [.unreachable]
where
  count : List Instr := if cnt then [.countInd] else []
  lowerBlock : List Flat.Stmt → List Instr
    | [] => []
    | s :: ss => lowerStmt cnt res s ++ lowerBlock ss

def lowerFn (cnt : Bool) (k : Nat) (f : Flat.Fn) : Func where
  name := fname k
  params := f.params
  results := f.results
  locals := f.locals
  body := lowerStmt.lowerBlock cnt f.results f.body ++ [.unreachable]

/-- The module; with `cnt`, every indirect call adds one to the runtime's count. -/
def lowerProg (p : Flat.Prog) (cnt : Bool := false) : Module where
  funcs := p.fns.toList.zipIdx.map (fun (f, k) => lowerFn cnt k f) ++
    [{ name := "$start", params := 0, results := 0, locals := 0,
       body := [.call (fname p.entry)], export? := some "_start" }]
  table := p.table.toList.map fname

end Backend.Wasm

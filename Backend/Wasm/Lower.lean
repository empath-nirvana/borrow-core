import Backend.Flat.Syntax
import Backend.Wasm.Syntax

/-!
# Backend — flat IR to Wasm

Each flat-IR function `k` is the Wasm function `$f{k}` over `i64` parameters and locals,
returning its `i64` results (several, as a multi-value function). Expressions become stack code
in argument order; an address is wrapped to `i32` before a memory access. A call's results are
popped into its destination locals, last first. `ite` is `if`/`else`; a tail call is
`return_call`, whose callee has the caller's results. `switch` is `br_table` over nested blocks:
case `i` follows the end of block `i` and branches out of the switch. A function's body ends in
`unreachable`, since every path of a flat-IR function returns. `_start` calls the entry.
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
  | .stat k => [.globalGet (if k == 0 then "$allocs" else if k == 1 then "$indirect" else "$copies")]
where
  lowerArgs : List Flat.Exp → List Instr
    | [] => []
    | e :: es => lowerExp e ++ lowerArgs es

/-- Pop a call's results into `ds`. -/
def popInto (ds : List Nat) : List Instr := ds.reverse.map .localSet

/-- `br_table` over `cases`, given the operand's code and the cases' code:

    block                       ;; the switch
      block                     ;; the default
        block                   ;; case k-1
          …
            block               ;; case 0
              e; br_table 0 1 … k-1 k
            end
            case 0; br k
          …
        end
        case k-1; br 1
      end
      default
    end -/
def switchCode (e : List Instr) (cases : List (List Instr)) (dflt : List Instr) : List Instr :=
  let k := cases.length
  let inner := [Instr.block (e ++ [.num .wrap, .brTable (List.range k) k])]
  let blocks := cases.zipIdx.foldl (fun acc (c, i) => [Instr.block (acc ++ c ++ [.br (k - i)])])
    inner
  [.block (blocks ++ dflt)]

/-- A statement; with `cnt`, every dispatched call adds one to the runtime's count. -/
def lowerStmt (cnt : Bool) : Flat.Stmt → List Instr
  | .set i e => lowerExp e ++ [.localSet i]
  | .store a off v => lowerExp a ++ [.num .wrap] ++ lowerExp v ++ [.i64Store (8 * off)]
  | .free a => lowerExp a ++ [.call "$free"]
  | .out b => lowerExp b ++ [.call "$putc"]
  | .putc fd b => lowerExp fd ++ lowerExp b ++ [.call "$putfd"]
  | .ite c t e => lowerExp c ++ [.ifElse (lowerBlock t) (lowerBlock e)]
  | .call ds f args => lowerExp.lowerArgs args ++ [.call (fname f)] ++ popInto ds
  | .switch e cs d => switchCode (lowerExp e) (lowerCases cs) (lowerBlock d)
  | .ret es => lowerExp.lowerArgs es ++ [.ret]
  | .tailCall f args => lowerExp.lowerArgs args ++ [.returnCall (fname f)]
  | .tick => if cnt then [.countInd] else []
  | .tickCopy => if cnt then [.countCopy] else []
  | .trap => [.unreachable]
where
  lowerBlock : List Flat.Stmt → List Instr
    | [] => []
    | s :: ss => lowerStmt cnt s ++ lowerBlock ss
  lowerCases : List (List Flat.Stmt) → List (List Instr)
    | [] => []
    | c :: cs => lowerBlock c :: lowerCases cs

def lowerFn (cnt : Bool) (k : Nat) (f : Flat.Fn) : Func where
  name := fname k
  params := f.params
  results := f.results
  locals := f.locals
  body := lowerStmt.lowerBlock cnt f.body ++ [.unreachable]

/-- The module; with `cnt`, every dispatched call adds one to the runtime's count. -/
def lowerProg (p : Flat.Prog) (cnt : Bool := false) : Module where
  funcs := p.fns.toList.zipIdx.map (fun (f, k) => lowerFn cnt k f) ++
    [{ name := "$start", params := 0, results := 0, locals := 0,
       body := [.call (fname p.entry)], export? := some "_start" }]

end Backend.Wasm

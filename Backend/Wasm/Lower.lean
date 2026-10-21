import Backend.Flat.Syntax
import Backend.Flat.Host
import Backend.Wasm.Syntax
import Std.Data.HashMap

/-!
# Backend — flat IR to Wasm

Each flat-IR function `k` is the Wasm function `$f{k}` over `i64` parameters and locals,
returning its `i64` results (several, as a multi-value function). Expressions become stack code
in argument order; an address is wrapped to `i32` before a memory access. A call's results are
popped into its destination locals, last first. `ite` is `if`/`else`; a tail call is
`return_call`, whose callee has the caller's results. `switch` is `br_table` over nested blocks:
case `i` follows the end of block `i` and branches out of the switch. A function's body ends in
`unreachable`, since every path of a flat-IR function returns. `_start` calls the entry. A
function with a frame (`Flat.Fn.frame`) takes it from the stack on entry and gives it back before
each return and tail call; a frame slot is its base plus the slot's offset.
-/

namespace Backend.Wasm
open BoCa Backend.Flat

def fname (k : Nat) : String := s!"$f{k}"

/-- The float operations' operands and results are a float's bits in the flat IR: an operand is
reinterpreted as a float when pushed, and a float result as its bits (SPEC §37). -/
def floatIn (o : HostOp) : List Instr :=
  match Flat.hostArgWidth o, o with
  | _, .reinterpret_i _ | _, .reinterpret_f _ => []
  | w, _ => match w.float? with
    | some f => [.num (.reinterpret_f f)]
    | none => []

def floatOut (o : HostOp) : List Instr :=
  match Flat.hostResKind o, o with
  | _, .reinterpret_i _ | _, .reinterpret_f _ => []
  | .int w, _ => match w.float? with
    | some f => [.num (.reinterpret_i f)]
    | none => []
  | _, _ => []

def lowerExp (fp : Nat) : Flat.Exp → List Instr
  | .loc i => [.localGet i]
  | .c64 n => [.i64Const n]
  | .c32 n => [.i32Const n]
  | .load a off => lowerExp fp a ++ [.num .wrap, .i64Load (8 * off)]
  | .load8 a => lowerExp fp a ++ [.num .wrap, .i64Load8U]
  | .load32 a => lowerExp fp a ++ [.num .wrap, .i64Load32U]
  | .op o args => lowerOpArgs o args ++ [.num o] ++ floatOut o
  | .alloc w => lowerExp fp w ++ [.call "$alloc"]
  | .slot off _ => [.localGet fp, .i64Const (8 * off).toUInt64, .num (.bin .w64 .add)]
  | .live => [.call "$live"]
  | .getc fd => lowerExp fp fd ++ [.call "$getc"]
  | .getv fd a k => lowerExp fp fd ++ lowerExp fp a ++ lowerExp fp k ++ [.call "$getv"]
  | .now c => lowerExp fp c ++ [.call "$now"]
  | .data off => [.i64Const (dataBase + off).toUInt64]
  | .stat k => [.globalGet (if k == 0 then "$allocs" else if k == 1 then "$indirect" else "$copies")]
where
  lowerArgs : List Flat.Exp → List Instr
    | [] => []
    | e :: es => lowerExp fp e ++ lowerArgs es
  -- A float operand is held as its bits, an integer: each is reinterpreted as it is pushed.
  lowerOpArgs (o : HostOp) : List Flat.Exp → List Instr
    | [] => []
    | e :: es => lowerExp fp e ++ floatIn o ++ lowerOpArgs o es

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

/-- Give the frame of `frame` words at the local `fp` back to the stack: before a return or a
tail call. -/
def popFrame (fp frame : Nat) : List Instr :=
  if frame == 0 then [] else
  [.localGet fp, .i64Const (8 * frame).toUInt64, .num (.bin .w64 .add), .globalSet "$sp"]

/-- A statement of a function whose frame of `frame` words is at the local `fp`; with `cnt`,
every dispatched call adds one to the runtime's count. -/
def lowerStmt (cnt : Bool) (fp frame : Nat) : Flat.Stmt → List Instr
  | .set i e => lowerExp fp e ++ [.localSet i]
  | .store a off v => lowerExp fp a ++ [.num .wrap] ++ lowerExp fp v ++ [.i64Store (8 * off)]
  | .store8 a v => lowerExp fp a ++ [.num .wrap] ++ lowerExp fp v ++ [.i64Store8]
  | .store32 a v => lowerExp fp a ++ [.num .wrap] ++ lowerExp fp v ++ [.i64Store32]
  | .free a => lowerExp fp a ++ [.call "$free"]
  | .unslot _ => []
  | .out b => lowerExp fp b ++ [.call "$putc"]
  | .putc fd b => lowerExp fp fd ++ lowerExp fp b ++ [.call "$putfd"]
  | .putv fd a k => lowerExp fp fd ++ lowerExp fp a ++ lowerExp fp k ++ [.call "$putv"]
  | .sleep c ns => lowerExp fp c ++ lowerExp fp ns ++ [.call "$sleep"]
  | .ite c t e => lowerExp fp c ++ [.ifElse (lowerBlock t) (lowerBlock e)]
  | .call ds f args => (lowerExp.lowerArgs fp args) ++ [.call (fname f)] ++ popInto ds
  | .switch e cs d => switchCode (lowerExp fp e) (lowerCases cs) (lowerBlock d)
  | .ret es => lowerExp.lowerArgs fp es ++ popFrame fp frame ++ [.ret]
  | .tailCall f args => lowerExp.lowerArgs fp args ++ popFrame fp frame ++ [.returnCall (fname f)]
  | .tick => if cnt then [.countInd] else []
  | .tickCopy => if cnt then [.countCopy] else []
  | .tickBound => []
  | .status c => lowerExp fp c ++ [.call "$exit"]
  | .trap => [.unreachable]
where
  lowerBlock : List Flat.Stmt → List Instr
    | [] => []
    | s :: ss => lowerStmt cnt fp frame s ++ lowerBlock ss
  lowerCases : List (List Flat.Stmt) → List (List Instr)
    | [] => []
    | c :: cs => lowerBlock c :: lowerCases cs

/-! ### Reusing locals

A flat-IR function's body is a tree of statements with no back edge (a loop is a tail call), so a
local is live, on any path, only between its first and its last occurrence in the body's order. A
local whose occurrences all come after another's last one may be that one: the locals are
numbered again by these intervals, each in the lowest number free at its first occurrence. Wasm
bounds a function's locals. -/

/-- The depth bound of the traversals below. -/
def occFuel : Nat := 1 <<< 20

/-- The first and last position of each local, the local `i` met at position `n`. -/
def occAt (n i : Nat) (m : Std.HashMap Nat (Nat × Nat)) : Std.HashMap Nat (Nat × Nat) :=
  m.insert i (match m[i]? with | some (a, _) => (a, n) | none => (n, n))

/-- The occurrences of the locals in an expression at position `n`. -/
def occExp (n : Nat) : Nat → Std.HashMap Nat (Nat × Nat) → Flat.Exp → Std.HashMap Nat (Nat × Nat)
  | 0, m, _ => m
  | k + 1, m, e => match e with
    | .loc i => occAt n i m
    | .load a _ | .load8 a | .load32 a | .alloc a | .getc a | .now a => occExp n k m a
    | .op _ args => args.foldl (occExp n k) m
    | .getv a b c => occExp n k (occExp n k (occExp n k m a) b) c
    | _ => m

/-- The occurrences of the locals in a statement, each statement one position on from the last. -/
def occStmt : Nat → Nat × Std.HashMap Nat (Nat × Nat) → Flat.Stmt → Nat × Std.HashMap Nat (Nat × Nat)
  | 0, nm, _ => nm
  | k + 1, (n, m), s =>
    let n := n + 1
    match s with
    | .set i e => (n, occAt n i (occExp n occFuel m e))
    | .store a _ v | .store8 a v | .store32 a v | .putc a v | .sleep a v =>
      (n, occExp n occFuel (occExp n occFuel m a) v)
    | .free a | .unslot a | .out a | .status a => (n, occExp n occFuel m a)
    | .putv a b c => (n, occExp n occFuel (occExp n occFuel (occExp n occFuel m a) b) c)
    | .ite c t e => (t ++ e).foldl (occStmt k) (n, occExp n occFuel m c)
    | .switch e cs d => (cs.flatten ++ d).foldl (occStmt k) (n, occExp n occFuel m e)
    | .call ds _ args => (n, ds.foldl (fun m i => occAt n i m) (args.foldl (occExp n occFuel) m))
    | .ret es | .tailCall _ es => (n, es.foldl (occExp n occFuel) m)
    | _ => (n, m)

/-- An expression with its locals renamed by `f`. -/
def renExp (f : Nat → Nat) : Nat → Flat.Exp → Flat.Exp
  | 0, e => e
  | k + 1, e => match e with
    | .loc i => .loc (f i)
    | .load a o => .load (renExp f k a) o
    | .load8 a => .load8 (renExp f k a)
    | .load32 a => .load32 (renExp f k a)
    | .op o args => .op o (args.map (renExp f k))
    | .alloc a => .alloc (renExp f k a)
    | .getc a => .getc (renExp f k a)
    | .getv a b c => .getv (renExp f k a) (renExp f k b) (renExp f k c)
    | .now a => .now (renExp f k a)
    | e => e

/-- A statement with its locals renamed by `f`. -/
def renStmt (f : Nat → Nat) : Nat → Flat.Stmt → Flat.Stmt
  | 0, s => s
  | k + 1, s =>
    let re := renExp f occFuel
    match s with
    | .set i e => .set (f i) (re e)
    | .store a o v => .store (re a) o (re v)
    | .store8 a v => .store8 (re a) (re v)
    | .store32 a v => .store32 (re a) (re v)
    | .free a => .free (re a)
    | .unslot a => .unslot (re a)
    | .out a => .out (re a)
    | .putc a b => .putc (re a) (re b)
    | .putv a b c => .putv (re a) (re b) (re c)
    | .sleep a b => .sleep (re a) (re b)
    | .ite c t e => .ite (re c) (t.map (renStmt f k)) (e.map (renStmt f k))
    | .switch e cs d => .switch (re e) (cs.map (·.map (renStmt f k))) (d.map (renStmt f k))
    | .call ds g args => .call (ds.map f) g (args.map re)
    | .ret es => .ret (es.map re)
    | .tailCall g es => .tailCall g (es.map re)
    | .status a => .status (re a)
    | s => s

/-- The function with its locals numbered again by their intervals; the parameters keep theirs. -/
def compactLocals (f : Flat.Fn) : Flat.Fn := Id.run do
  let (_, m) := f.body.foldl (occStmt occFuel) (0, {})
  -- The parameters are live from the start.
  let m := (List.range f.params).foldl (fun m i =>
    m.insert i (match m[i]? with | some (_, b) => (0, b) | none => (0, 0))) m
  let ivs := (m.toList.filter (·.1 ≥ f.params)).toArray.qsort (fun a b => a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.1 < b.1))
  -- Each number's last position, among the numbers past the parameters.
  let mut ends : Array Nat := #[]
  let mut to : Std.HashMap Nat Nat := {}
  for (i, (a, b)) in ivs.toList do
    match (ends.zipIdx.toList.find? fun (e, _) => e < a) with
    | some (_, k) => ends := ends.set! k b; to := to.insert i (f.params + k)
    | none => to := to.insert i (f.params + ends.size); ends := ends.push b
  let r (i : Nat) : Nat := if i < f.params then i else to.getD i i
  pure { f with locals := ends.size, body := f.body.map (renStmt r occFuel) }

/-- A function. One with a frame has a local more, `fp`, the frame's base: on entry the frame
is taken from the stack (`$sp` lowered by its size, trapping when it would pass the stack's
end), and every return and tail call gives it back.  `[spec §35]` -/
def lowerFn (cnt : Bool) (k : Nat) (f : Flat.Fn) : Func :=
  let f := compactLocals f
  let fp := f.params + f.locals
  let enter : List Instr := if f.frame == 0 then [] else
    [.globalGet "$sp", .i64Const (8 * f.frame).toUInt64, .num (.bin .w64 .sub), .localSet fp,
     .localGet fp, .globalGet "$stackLimit", .num (.rel .w64 .lt_u), .ifElse [.unreachable] [],
     .localGet fp, .globalSet "$sp"]
  { name := fname k
    params := f.params
    results := f.results
    locals := f.locals + (if f.frame == 0 then 0 else 1)
    body := enter ++ lowerStmt.lowerBlock cnt fp f.frame f.body ++ [.unreachable] }

/-- The module; with `cnt`, every dispatched call adds one to the runtime's count. -/
def lowerProg (p : Flat.Prog) (cnt : Bool := false) : Module where
  funcs := p.fns.toList.zipIdx.map (fun (f, k) => lowerFn cnt k f) ++
    [{ name := "$start", params := 0, results := 0, locals := 0,
       body := [.call (fname p.entry)], export? := some "_start" }]
  data := p.data
  stack := p.fns.any (·.frame > 0)

end Backend.Wasm

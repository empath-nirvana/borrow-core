import Std.Data.HashSet
import Target.Flat.Syntax

/-!
# Scalar replacement of checked plain local cells `[spec §80]`

Only slot offsets supplied by the `withlocal` lowering are candidates. A scalar whose address
is passed to a call, returned, used as data, or crosses control flow remains a frame slot.
This pass neither decides borrowing nor discovers local allocations in erased source terms.
-/
namespace Backend2.LocalSlots
open BoCa Backend.Flat

abbrev EM := StateT (Std.HashSet Nat) (Except Unit)

def addr (as : Std.HashSet Nat) : Exp → Bool
  | .loc x => as.contains x
  | _ => false

/-- Read a known scalar slot, retaining every other expression's evaluation. -/
def expr (as : Std.HashSet Nat) (reg bytes : Nat) : Nat → Exp → Except Unit Exp
  | 0, _ => .error ()
  | f + 1, e => match e with
    | .loc x => if as.contains x then .error () else .ok e
    | .load a off => if addr as a then
        if bytes == 8 && off == 0 then .ok (.loc reg) else .error ()
      else do pure (.load (← expr as reg bytes f a) off)
    | .load8 a => if addr as a then
        if bytes == 1 then .ok (.loc reg) else .error ()
      else do pure (.load8 (← expr as reg bytes f a))
    | .load32 a => if addr as a then
        if bytes == 4 then .ok (.loc reg) else .error ()
      else do pure (.load32 (← expr as reg bytes f a))
    | .op o args => do pure (.op o (← args.mapM (expr as reg bytes f)))
    | .alloc n => do pure (.alloc (← expr as reg bytes f n))
    | .getc fd => do pure (.getc (← expr as reg bytes f fd))
    | .getv fd a n => do pure (.getv (← expr as reg bytes f fd) (← expr as reg bytes f a) (← expr as reg bytes f n))
    | .now a => do pure (.now (← expr as reg bytes f a))
    | .gep a o => do pure (.gep (← expr as reg bytes f a) (← expr as reg bytes f o))
    | _ => .ok e

def narrow (bytes : Nat) (e : Exp) : Exp :=
  if bytes == 1 then .op (.bin .w64 .and) [e, .c64 0xff]
  else if bytes == 4 then .op (.bin .w64 .and) [e, .c64 0xffffffff] else e

/-- One straight-line slot's storage simulation. Unsupported uses keep the original slot. -/
def stmts (off reg bytes : Nat) : List Stmt → EM (List Stmt)
  | [] => pure []
  | s :: rest => do
    let as ← get
    let e : Exp → EM Exp := fun v st => (expr as reg bytes 1024 v).map (fun v => (v, st))
    let out ← match s with
      | .set x (.slot o _) =>
        if o == off then modify (·.insert x); pure []
        else modify (·.erase x); pure [s]
      | .set x v =>
        if addr as v then modify (·.insert x); pure []
        else
          let v ← e v
          modify (·.erase x)
          pure [.set x v]
      | .store a k v =>
        if addr as a then
          if bytes != 8 || k != 0 then throw ()
          pure [.set reg (← e v)]
        else pure [.store (← e a) k (← e v)]
      | .store8 a v =>
        if addr as a then
          if bytes != 1 then throw ()
          pure [.set reg (narrow bytes (← e v))]
        else pure [.store8 (← e a) (← e v)]
      | .store32 a v =>
        if addr as a then
          if bytes != 4 then throw ()
          pure [.set reg (narrow bytes (← e v))]
        else pure [.store32 (← e a) (← e v)]
      | .unslot a => if addr as a then pure [] else pure [.unslot (← e a)]
      | .free a => pure [.free (← e a)]
      | .out v => pure [.out (← e v)]
      | .putc fd v => pure [.putc (← e fd) (← e v)]
      | .putv fd a n => pure [.putv (← e fd) (← e a) (← e n)]
      | .sleep a n => pure [.sleep (← e a) (← e n)]
      | .call ds fn args =>
        let args ← args.mapM e
        modify fun st => ds.foldl (·.erase ·) st
        pure [.call ds fn args]
      | .ret es => pure [.ret (← es.mapM e)]
      | .tailCall fn args => pure [.tailCall fn (← args.mapM e)]
      | .status v => pure [.status (← e v)]
      | .ite .. | .switch .. => throw ()
      | _ => pure [s]
    return out ++ (← stmts off reg bytes rest)

/-- UNPROVED: replacing a checked plain local's nonescaping scalar slot with a register
preserves its stores and reads. The construction scopes every borrow before the cell's free;
`stmts` refuses address observations/calls and control flow, and `narrow` retains store widths.
If this storage simulation fails, a write or read can change a program's answer. -/
def promote (slots : List (Nat × Nat)) (next : Nat) (body : List Stmt) : List Stmt × Nat :=
  slots.foldl (fun (body, next) (off, bytes) =>
    match (stmts off next bytes body).run {} with
    | .ok (body, _) => (body, next + 1)
    | .error _ => (body, next)) (body, next)

end Backend2.LocalSlots

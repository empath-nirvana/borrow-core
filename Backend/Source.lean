import Support.Dynamics.Interpreter
import Backend.Value

/-!
# Backend — the source run

`Support`'s interpreter (`BoCa.step` at `wasmHost`) run to a value, with the number of cells
left in memory: the reference every stage is compared with.
-/

namespace Backend
open BoCa

/-- The observable form of a source value. -/
def pvOfExpr : Expr → PV
  | .unit => .unit
  | .pair a b => .pair (pvOfExpr a) (pvOfExpr b)
  | .inj₁ a => .inj false (pvOfExpr a)
  | .inj₂ a => .inj true (pvOfExpr a)
  | .prim (.lit (.i32 n)) => .i32 n
  | .prim (.lit (.i64 n)) => .i64 n
  | .loc _ => .loc
  | _ => .fn

/-- Run `e` for at most `fuel` steps from `μ`: the value and the final memory. -/
def runSource (fuel : Nat) (μ : Mem) (e : Expr) : Except String (Val × Mem) :=
  match fuel with
  | 0 => .error "source interpreter: out of fuel"
  | n + 1 =>
    match step wasmHost μ e with
    | .value v => .ok (v, μ)
    | .next μ' e' => runSource n μ' e'
    | .stuck r => .error s!"source interpreter: stuck ({repr r})"

/-- The source interpreter's report: the value and the number of cells left. -/
def interpSource (fuel : Nat) (e : Expr) : Except String String := do
  let (v, μ) ← runSource fuel Mem.empty e
  pure (report (pvOfExpr v.1) μ.cells.length)

end Backend

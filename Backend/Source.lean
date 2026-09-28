import Support.Dynamics.Interpreter
import Backend.Value

/-!
# Backend — the source run

`Support`'s interpreter (`BoCa.step` at `wasmHost`) run to a value, with the number of cells
left in memory: the reference every stage is compared with. A program with capabilities
(SPEC §11) runs as `run_io` with the model of every extern, the term `io_every_run` is about.
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
def interpSource (fuel : Nat) (e : Expr) : Except String Output := do
  let (v, μ) ← runSource fuel Mem.empty e
  pure (.mk' .empty .empty (report (pvOfExpr v.1) μ.cells.length))

/-- The bytes of a byte list, most recent first as an output stream holds them. -/
def bytesOf : Expr → Option (List UInt8)
  | .inj₁ .unit => some []
  | .inj₂ (.pair (.prim (.lit (.i32 b))) r) => (bytesOf r).map (b.toUInt8 :: ·)
  | _ => none

/-- The output of a finished model run: `((fd, out), ((fd', err), a))` holds the bytes written to
each stream, most recent first, and `main`'s result `a`. Each stream's bytes go to its
descriptor, then the report of `a`. -/
def ioOutput (v : Val) (μ : Mem) : Except String Output := do
  match v.1 with
  | .pair (.pair (.prim (.lit (.i32 fd₁))) o₁) (.pair (.pair (.prim (.lit (.i32 fd₂))) o₂) a) =>
    let some b₁ := bytesOf o₁ | throw "source interpreter: an output stream is not a byte list"
    let some b₂ := bytesOf o₂ | throw "source interpreter: an output stream is not a byte list"
    let streams := [(fd₁, b₁.reverse), (fd₂, b₂.reverse)]
    let on (fd : UInt32) : ByteArray :=
      ⟨(streams.filter (·.1 == fd)).foldl (fun acc s => acc ++ s.2.toArray) #[]⟩
    pure (.mk' (on 1) (on 2) (report (pvOfExpr a) μ.cells.length))
  | _ => throw "source interpreter: run_io's value is not its outputs and result"

/-- The model run of a program with capabilities (SPEC §11): `run_io[γ] inp` from the empty
memory. -/
def interpIO (fuel : Nat) (e : Expr) : Except String Output := do
  let (v, μ) ← runSource fuel Mem.empty e
  ioOutput v μ

/-- Observe the loop `d` until it finishes: each `next` is `d (inl ())`, which answers `inl r` to
finish with `r` or `inr d'` to go on with `d'`. This is `driveE` without its bound: a run that
finishes after `k` observations is the run of `driveE k` (SPEC §7, §11). -/
def driveSource (fuel : Nat) : Nat → Mem → Val → Except String (Val × Mem)
  | 0, _, _ => .error "source interpreter: out of fuel"
  | n + 1, μ, d => do
    let (w, μ') ← runSource fuel μ (.app (.val d) (.val (.inj₁ .unit)))
    match w with
    | ⟨.inj₁ r, h⟩ => pure (⟨r, by cases h; assumption⟩, μ')
    | ⟨.inj₂ d', h⟩ => driveSource fuel n μ' ⟨d', by cases h; assumption⟩
    | _ => .error "source interpreter: a loop's `next` answered neither `inl` nor `inr`"

/-- The model run of a program that runs until its input ends: `run_io[γ] inp` returns a loop,
which is observed until it finishes. -/
def interpIOLoop (fuel : Nat) (e : Expr) : Except String Output := do
  let (d, μ) ← runSource fuel Mem.empty e
  let (v, μ') ← driveSource fuel fuel μ d
  ioOutput v μ'


end Backend

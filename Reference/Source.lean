import Support.Dynamics.Interpreter
import Target.Value

/-!
# Reference — the source run

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
  | .prim (.lit (.u8 n)) => .u8 n
  | .prim (.lit (.f32 n)) => .f32 n
  | .prim (.lit (.f64 n)) => .f64 n
  | .prim (.lit (.u32 n)) => .u32 n
  | .prim (.lit (.u64 n)) => .u64 n
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
    | .op _ _ _ => .error "source interpreter: an operation no handler catches"

/-! ### The run, executably

`runSource` steps the whole term each time, so a step costs the depth of its evaluation context.
`runFocused` keeps the context as a stack of frames and steps the focus alone: a step of the
focus is a step of the whole term (`plugAll_next`), and moving the focus into or out of a frame
changes nothing, the term being the same. Where the focus does anything but step (it is stuck,
or stops at an operation a frame outside may catch), the whole term takes the step, and the run
goes on from it. `runSource_eq_runFocused` proves the
two equal, so compiled code runs `runFocused` in `runSource`'s place (`@[csimp]`). -/

/-- A frame of the evaluation context the run keeps as a stack: the frames of `step` whose hole
is stepped first, without condition (`[spec §3]`, row 3.37). -/
inductive Frame where
  | pairL   (e₂ : Expr)
  | pairR   (v : Val)
  | inj₁
  | inj₂
  | seq     (e₂ : Expr)
  | letpair (e₂ : Expr)
  | case    (e₁ e₂ : Expr)
  | appR    (f : Expr)

/-- `F[e]`. -/
def Frame.plug : Frame → Expr → Expr
  | .pairL e₂, e    => .pair e e₂
  | .pairR v, e     => .pair v.1 e
  | .inj₁, e        => .inj₁ e
  | .inj₂, e        => .inj₂ e
  | .seq e₂, e      => .seq e e₂
  | .letpair e₂, e  => .letpair e e₂
  | .case e₁ e₂, e  => .case e e₁ e₂
  | .appR f, e      => .app f e

/-- The stack `K`, innermost first, filled with `e`. -/
def plugAll : List Frame → Expr → Expr
  | [], e => e
  | F :: K, e => plugAll K (F.plug e)

theorem Frame.step_next {μ μ' : Mem} {e e' : Expr} (F : Frame)
    (h : step wasmHost μ e = .next μ' e') :
    step wasmHost μ (F.plug e) = .next μ' (F.plug e') := by
  cases F with
  | pairR v => simp only [Frame.plug, step, step_of_isVal wasmHost μ v.2, h]
  | _ => simp only [Frame.plug, step, h]

theorem plugAll_next {μ μ' : Mem} : ∀ (K : List Frame) {e e' : Expr},
    step wasmHost μ e = .next μ' e' → step wasmHost μ (plugAll K e) = .next μ' (plugAll K e')
  | [], _, _, h => h
  | F :: K, _, _, h => plugAll_next K (F.step_next h)

/-- The frame whose hole is the first part of `e` to step, and that part, when it is not a
value. -/
def decomp : Expr → Option (Frame × Expr)
  | .pair a b =>
    if ha : isValB a = true then
      if isValB b then none else some (.pairR ⟨a, isVal_of_isValB a ha⟩, b)
    else some (.pairL b, a)
  | .inj₁ a => if isValB a then none else some (.inj₁, a)
  | .inj₂ a => if isValB a then none else some (.inj₂, a)
  | .seq a b => if isValB a then none else some (.seq b, a)
  | .letpair a b => if isValB a then none else some (.letpair b, a)
  | .case a b c => if isValB a then none else some (.case b c, a)
  | .app f a => if isValB a then none else some (.appR f, a)
  | _ => none

theorem decomp_plug : ∀ {e e₀ : Expr} {F : Frame}, decomp e = some (F, e₀) → F.plug e₀ = e
  | .pair a b, _, _, h => by
      simp only [decomp] at h
      split at h
      · split at h
        · cases h
        · cases h; rfl
      · cases h; rfl
  | .inj₁ _, _, _, h | .inj₂ _, _, _, h | .seq _ _, _, _, h | .letpair _ _, _, _, h
  | .case _ _ _, _, _, h | .app _ _, _, _, h => by
      simp only [decomp] at h
      split at h
      · cases h
      · cases h; rfl
  | .var _, _, _, h | .unit, _, _, h | .lam _, _, _, h | .loc _, _, _, h | .prim _, _, _, h => by
      simp [decomp] at h

/-- `runSource fuel μ (plugAll K e)`, stepping the focus `e` alone. Each move of the focus spends
one of `gas`; when `gas` is spent the run goes on as `runSource`. -/
def runFocus : Nat → Nat → Mem → List Frame → Expr → Except String (Val × Mem)
  | fuel, 0, μ, K, e => runSource fuel μ (plugAll K e)
  | fuel, g + 1, μ, K, e =>
    match valOf? e, K with
    | some _, F :: K' => runFocus fuel g μ K' (F.plug e)
    | some _, [] => runSource fuel μ e
    | none, _ =>
      match decomp e with
      | some (F, e₀) => runFocus fuel g μ (F :: K) e₀
      | none =>
        match fuel with
        | 0 => runSource 0 μ (plugAll K e)
        | n + 1 =>
          match step wasmHost μ e with
          | .next μ' e' => runFocus n g μ' K e'
          | _ =>
            match step wasmHost μ (plugAll K e) with
            | .next μ' e' => runFocus n g μ' [] e'
            | _ => runSource (n + 1) μ (plugAll K e)

theorem runFocus_eq : ∀ (g fuel : Nat) (μ : Mem) (K : List Frame) (e : Expr),
    runFocus fuel g μ K e = runSource fuel μ (plugAll K e)
  | 0, _, _, _, _ => by simp only [runFocus]
  | g + 1, fuel, μ, K, e => by
    unfold runFocus
    split
    · rw [runFocus_eq g]; rfl
    · rfl
    · split
      · rename_i F e₀ hd
        rw [runFocus_eq g, plugAll, decomp_plug hd]
      · split
        · rfl
        · rename_i n
          split
          · rename_i μ' e' hs
            rw [runFocus_eq g]
            conv => rhs; unfold runSource
            rw [plugAll_next _ hs]
          · split
            · rename_i μ' e' hs
              rw [runFocus_eq g]
              conv => rhs; unfold runSource
              rw [hs]; rfl
            · rfl

/-- `runSource`, stepping the focus alone (`runFocus`). -/
def runFocused (fuel : Nat) (μ : Mem) (e : Expr) : Except String (Val × Mem) :=
  runFocus fuel (2 ^ 62) μ [] e

@[csimp] theorem runSource_eq_runFocused : @runSource = @runFocused := by
  funext fuel μ e
  exact (runFocus_eq _ fuel μ [] e).symm

/-- The source interpreter's report: the value and the number of cells left. -/
def interpSource (fuel : Nat) (e : Expr) : Except String Output := do
  let (v, μ) ← runSource fuel Mem.empty e
  pure (.mk' .empty .empty (report (pvOfExpr v.1) μ.cells.length))

/-- The bytes of a byte list, most recent first as an output stream holds them. -/
def bytesOf : Expr → Option (List UInt8)
  | .inj₁ .unit => some []
  | .inj₂ (.pair (.prim (.lit (.u8 b))) r) => (bytesOf r).map (b :: ·)
  | _ => none

/-- The output of a finished model run: `((fd, out), ((fd', err), a))` holds the bytes written to
each stream, most recent first, and `main`'s result `a`. Each stream's bytes go to its
descriptor, then the report of `a`, with `live` cells left. -/
def ioOutputN (v : Val) (live : Nat) (exits : Bool := false) : Except String Output := do
  match v.1 with
  | .pair (.pair (.prim (.lit (.i32 fd₁))) o₁) (.pair (.pair (.prim (.lit (.i32 fd₂))) o₂) a) =>
    let some b₁ := bytesOf o₁ | throw "source interpreter: an output stream is not a byte list"
    let some b₂ := bytesOf o₂ | throw "source interpreter: an output stream is not a byte list"
    let streams := [(fd₁, b₁.reverse), (fd₂, b₂.reverse)]
    let on (fd : UInt32) : ByteArray :=
      ⟨(streams.filter (·.1 == fd)).foldl (fun acc s => acc ++ s.2.toArray) #[]⟩
    let (r, st) := reportExit exits (pvOfExpr a) live
    pure (.mk' (on 1) (on 2) r st)
  | _ => throw "source interpreter: run_io's value is not its outputs and result"

/-- `ioOutputN` at the number of cells `μ` holds. -/
def ioOutput (v : Val) (μ : Mem) (exits : Bool := false) : Except String Output :=
  ioOutputN v μ.cells.length exits

/-- The model run of a program with capabilities (SPEC §11): `run_io[γ] inp` from the empty
memory. -/
def interpIO (fuel : Nat) (e : Expr) (exits : Bool := false) : Except String Output := do
  let (v, μ) ← runSource fuel Mem.empty e
  ioOutput v μ exits

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

/-- A closed term that returns a loop, driven to its end: its value and the cells left. -/
def interpLoop (fuel : Nat) (e : Expr) : Except String Output := do
  let (d, μ) ← runSource fuel Mem.empty e
  let (v, μ') ← driveSource fuel fuel μ d
  pure (.mk' .empty .empty (report (pvOfExpr v.1) μ'.cells.length))

/-- The model run of a program that runs until its input ends: `run_io[γ] inp` returns a loop,
which is observed until it finishes. -/
def interpIOLoop (fuel : Nat) (e : Expr) (exits : Bool := false) : Except String Output := do
  let (d, μ) ← runSource fuel Mem.empty e
  let (v, μ') ← driveSource fuel fuel μ d
  ioOutput v μ' exits


end Backend

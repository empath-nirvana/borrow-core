import Frontend.Parser
import Frontend.Print
import Frontend.Check.Program
import Core.Stdio

/-!
# Frontend — Check — externs and standard I/O  `[spec §11]`

The standard externs, each with its type, its role, its model and its assurance level
(decision 27), and the `run_io` wrapper a program with capability externs is run through.

* **The table** (`stdExterns`). `stdin`, `stdout`, `stderr` are capabilities: cells whose content
  is the stream (file descriptor `0`, `1`, `2` in compiled code). `read_byte`, `write_byte`,
  `write_all` and `read_into` are the operations, lowered to WASI `fd_read`/`fd_write`. `mk_input`, `mk_output`,
  `take_input`, `take_output` are the model's harness and are not compiled. `checkExterns`
  checks a program's extern declarations against the table, by name and by type.
* **`run_io`** (`ioWrapper`). A `main : F (Caps ⊗ A)` whose externs include capabilities is
  wrapped into `run_io : Bytes ⊸ F ((I32 ⊗ Bytes) ⊗ ((I32 ⊗ Bytes) ⊗ A))`: the capabilities are
  made from the input bytes by the harness, `main`'s body runs with them bound to their names,
  and they are taken back. The wrapper is printed as source, parsed and checked like any
  program, so it has a `CDerives` derivation at the context of the operations and the harness.
* **The model run** (`IORun`). The checked wrapper with the model of each extern, chosen by
  type from `stdModel`, and the proofs `io_every_run` asks for: `IORun.every_run` is
  `io_every_run` at it. `bcc interp` runs exactly `IORun.expr`.
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core (Opaque BytesV bytesTy outRep externTy readByteC writeByteC writeAllC
  readIntoC clockNowC clockSleepC mkClockC takeClockC mkInputC
  mkOutputC takeInputC takeOutputC readByteV writeByteV mkInputV mkOutputV takeCapV stdModel
  io_every_run io_loop_every_run ioLoopE bytesVal bytesVal_bytes)

abbrev CVal := BoCa.Val

/-- The assurance ladder of decision 27, for a trusted boundary. -/
inductive Assurance where
  | assumed
  | interpChecked
  | propertyTested
  | typedUnsafe
  | boundaryChecked
  | smtVerified
  | proved
  deriving DecidableEq, Repr

def Assurance.level : Assurance → Nat
  | .assumed => 1
  | .interpChecked => 2
  | .propertyTested => 3
  | .typedUnsafe => 4
  | .boundaryChecked => 5
  | .smtVerified => 6
  | .proved => 7

def Assurance.name : Assurance → String
  | .assumed => "assumed"
  | .interpChecked => "interpreter-checked"
  | .propertyTested => "property-tested"
  | .typedUnsafe => "typed low-level"
  | .boundaryChecked => "boundary-checked"
  | .smtVerified => "semi-automatically verified"
  | .proved => "proved"

def Assurance.render (a : Assurance) : String := s!"{a.name} ({a.level})"

/-- What an extern is. -/
inductive ExternRole where
  /-- A capability: a cell whose content is the stream with this file descriptor; the arguments'
  stream is `0xFFFFFFFF` (SPEC §34). -/
  | cap (fd : Nat)
  /-- The clock: a cell holding the model's time, `i64[0]` (SPEC §34). -/
  | clockCap
  | readByte
  | writeByte
  | writeAll
  | readInto
  | clockNow
  | clockSleep
  /-- The model's harness: no host implementation. -/
  | harness
  deriving DecidableEq, Repr

/-- A standard extern.  `[spec §11]` -/
structure ExternSpec where
  name : String
  ty : CVTy
  role : ExternRole
  /-- The Lean result that proves the model meets the contract. -/
  modelProof : String
  /-- The host implementation and its level; `none` when it is not compiled. -/
  host : Option (String × Assurance)

def ExternSpec.isCap (x : ExternSpec) : Bool :=
  match x.role with
  | .cap _ | .clockCap => true
  | _ => false

/-- The standard externs.  `[spec §11]` -/
def stdExterns : List ExternSpec :=
  [ ⟨"stdin", .ref (.opq .input), .cap 0, "vC_bytes (a cell holding the input)",
      some ("a runtime cell holding fd 0", .assumed)⟩,
    ⟨"stdout", .ref (.opq .output), .cap 1, "vC_outRep (a cell holding (1, nil))",
      some ("a runtime cell holding fd 1", .assumed)⟩,
    ⟨"stderr", .ref (.opq .output), .cap 2, "vC_outRep (a cell holding (2, nil))",
      some ("a runtime cell holding fd 2", .assumed)⟩,
    ⟨"clock", .ref (.opq .clock), .clockCap, "vC_clockRep (a cell holding the time, i64[0])",
      some ("a runtime cell; the time is the host's monotonic clock", .assumed)⟩,
    ⟨"args", .ref (.opq .args), .cap 0xFFFFFFFF,
      "vC_argsRep (a cell holding the arguments, each followed by 0)",
      some ("a runtime cell over the arguments, read once (WASI args_get; libc argv)",
        .interpChecked)⟩,
    ⟨"read_byte", externTy (readByteC (.opq .input)), .readByte, "readByte_meets",
      some ("WASI fd_read of one byte (libc read(2))", .interpChecked)⟩,
    ⟨"write_byte", externTy (writeByteC (.opq .output)), .writeByte, "writeByte_meets",
      some ("WASI fd_write of one byte (libc write(2))", .interpChecked)⟩,
    ⟨"write_all", externTy (writeAllC (.opq .output)), .writeAll, "writeAll_meets",
      some ("WASI fd_write of the view (libc write(2))", .interpChecked)⟩,
    ⟨"read_into", externTy (readIntoC (.opq .input)), .readInto, "readInto_meets",
      some ("WASI fd_read into the view until it is full or the input ends (libc read(2))",
        .interpChecked)⟩,
    ⟨"clock_now", externTy (clockNowC (.opq .clock)), .clockNow, "clockNow_meets",
      some ("WASI clock_time_get of the monotonic clock (libc clock_gettime)", .assumed)⟩,
    ⟨"clock_sleep", externTy (clockSleepC (.opq .clock)), .clockSleep, "clockSleep_meets",
      some ("WASI poll_oneoff on a relative clock subscription (libc nanosleep)", .assumed)⟩,
    ⟨"read_arg", externTy (readByteC (.opq .args)), .readByte, "readArg_meets",
      some ("the arguments read once into memory (WASI args_sizes_get, args_get; libc argv)",
        .interpChecked)⟩,
    ⟨"mk_clock", externTy (mkClockC (.opq .clock)), .harness, "mkClock_meets", none⟩,
    ⟨"mk_args", externTy (mkInputC (.opq .args)), .harness, "mkArgs_meets", none⟩,
    ⟨"take_args", externTy (takeInputC (.opq .args)), .harness, "takeArgs_meets", none⟩,
    ⟨"take_clock", externTy (takeClockC (.opq .clock)), .harness, "takeClock_meets", none⟩,
    ⟨"mk_input", externTy (mkInputC (.opq .input)), .harness, "mkInput_meets", none⟩,
    ⟨"mk_output", externTy (mkOutputC (.opq .output)), .harness, "mkOutput_meets", none⟩,
    ⟨"take_input", externTy (takeInputC (.opq .input)), .harness, "takeInput_meets", none⟩,
    ⟨"take_output", externTy (takeOutputC (.opq .output)), .harness, "takeOutput_meets", none⟩ ]

def findExtern (n : String) : Option ExternSpec := stdExterns.find? (·.name == n)

/-- A program's externs, each matched with the table entry of its name and type. -/
def checkExterns (xs : List (String × CVTy)) : Except String (List ExternSpec) :=
  xs.mapM fun (n, A) => match findExtern n with
    | none => Except.error (s!"extern `{n}` has no implementation (the standard externs are " ++
        ", ".intercalate (stdExterns.map (s!"`{·.name}`")) ++ ")")
    | some x =>
      if A = x.ty then pure x
      else Except.error s!"extern `{n}` has type `{ppVTy A}`, but the standard `{n}` has type `{ppVTy x.ty}`"

/-- The trusted base of a program: each extern, its contract's proof and its host
implementation with its level.  `bcc trusted`.  `[spec §11]` -/
def trustedReport (xs : List (String × CVTy)) : List String :=
  if xs.isEmpty then ["no externs: nothing beyond the compiler and the runtime is trusted"] else
  xs.map fun (n, A) => match findExtern n with
    | none => s!"extern {n} : {ppVTy A}\n  contract: {Assurance.assumed.render}, no model\n" ++
        "  host: none; not compiled"
    | some x =>
      let model := if A = x.ty then s!"model {Assurance.proved.render}, {x.modelProof}"
        else s!"{Assurance.assumed.render}: the type differs from the standard `{ppVTy x.ty}`"
      let host := match x.host with
        | some (d, a) => s!"host: {d}; {a.render}"
        | none => "host: none (the model's harness); not compiled"
      s!"extern {n} : {ppVTy A}\n  contract: {model}\n  {host}"

/-- The capability externs of a program, in declaration order. -/
def capsOf (xs : List ExternSpec) : List ExternSpec := xs.filter (·.isCap)

/-- The right-nested tuple of the capabilities' types. -/
def capsTy : List ExternSpec → CVTy
  | [] => .unit
  | [x] => x.ty
  | x :: xs => .tensor x.ty (capsTy xs)

/-! ### The wrapper -/

def bytesSrc : String := "(mu X. 1 + (u8 * X))"

/-- Rebind the returned capabilities to their names: `let (c₁, r) = …; …`. -/
def rebindCaps : List String → String → String
  | [], _ => ""
  | [n], v => s!"{n} <- return {v};\n    "
  | [n₁, n₂], v => s!"let ({n₁}, {n₂}) = {v};\n    "
  | n :: ns, v => s!"let ({n}, io_rest_{ns.length}) = {v};\n    " ++
      rebindCaps ns s!"io_rest_{ns.length}"

/-- A byte list as a value of `Bytes`, in the source syntax. -/
def bytesLit : List UInt8 → String
  | [] => s!"(roll inl () : {bytesSrc})"
  | b :: bs => s!"(roll inr (u8[{b}], {bytesLit bs}) : {bytesSrc})"

/-- The harness's externs for the clock and the arguments, when `main` declares them (SPEC §34). -/
def clockExterns (caps : List String) : String :=
  (if caps.contains "clock" then
    "extern mk_clock : !(1 => ref clock)\nextern take_clock : !(ref clock => i64)\n" else "") ++
  (if caps.contains "args" then
    s!"extern mk_args : !({bytesSrc} => ref args)\nextern take_args : !(ref args => {bytesSrc})\n"
  else "")

/-- Make the clock and the arguments `main` declares: the clock at time `0`, the arguments a
stream of `args` (SPEC §34). -/
def makeExtra (caps : List String) (args : List UInt8) : String :=
  (if caps.contains "clock" then "clock <- return ((unbang mk_clock) ());\n    " else "") ++
  (if caps.contains "args" then s!"args <- return ((unbang mk_args) {bytesLit args});\n    " else "")

/-- Take back the clock and the arguments `main` declares. -/
def takeExtra (caps : List String) : String :=
  (if caps.contains "clock" then "io_clk <- return ((unbang take_clock) clock);\n    " else "") ++
  (if caps.contains "args" then "io_args <- return ((unbang take_args) args);\n    " else "")

/-- The source of `run_io`: the harness's externs and the wrapped `main`, which is given `args`
as its arguments.  `[spec §11, §34]` -/
def wrapperSrc (caps : List String) (capsT A : CVTy) (body : Comp) (args : List UInt8) : String :=
  let B := bytesSrc
  let out := s!"(i32 * {B})"
  s!"extern mk_input : !({B} => ref input)
extern mk_output : !(i32 => ref output)
extern take_input : !(ref input => {B})
extern take_output : !(ref output => i32 * {B})
{clockExterns caps}
main : {B} -o F ({out} * ({out} * ({ppVTy A}))) =
  fun (io_inp : {B}) ->
    stdin <- return ((unbang mk_input) io_inp);
    stdout <- return ((unbang mk_output) i32[1]);
    stderr <- return ((unbang mk_output) i32[2]);
    {makeExtra caps args}io_r : ({ppVTy capsT}) * ({ppVTy A}) <- ({body.pp 0 6});
    let (io_caps, io_a) = io_r;
    " ++ rebindCaps caps "io_caps" ++ takeExtra caps ++ "io_in <- return ((unbang take_input) stdin);
    io_out <- return ((unbang take_output) stdout);
    io_err <- return ((unbang take_output) stderr);
    return (io_out, (io_err, io_a))
"

/-- Bind the names of a right-nested tuple held in `v`. -/
def destructNames (v : String) : List String → String
  | [] => s!"let () = {v};\n    "
  | [x] => s!"{x} <- return {v};\n    "
  | [x, y] => s!"let ({x}, {y}) = {v};\n    "
  | x :: xs => s!"let ({x}, {v}_t) = {v};\n    " ++ destructNames s!"{v}_t" xs

def tupleNames : List String → String
  | [] => "()"
  | [x] => x
  | x :: xs => s!"({x}, {tupleNames xs})"

/-- The source of `run_io` for a `main` that returns a loop: a loop by `unfold` whose state is
`main`'s loop and the capabilities `main` does not declare. Its `next` observes `main`'s loop and,
when it finishes, takes the outputs back; its `close` closes it and takes them.  `[spec §11]` -/
def loopWrapperSrc (caps : List String) (capsT A B : CVTy) (body : Comp) (args : List UInt8) :
    String :=
  let bs := bytesSrc
  let out := s!"(i32 * {bs})"
  let extra := ["stdin", "stdout", "stderr"].filter (!caps.contains ·)
  let extraT := match extra.map (fun c => if c == "stdin" then "ref input" else "ref output") with
    | [] => "1"
    | [t] => t
    | [t, u] => s!"({t} * {u})"
    | _ => "(ref input * (ref output * ref output))"
  -- With no capabilities, `main`'s loop finishes with `A` itself and hands back `B` (SPEC §14).
  let inner := if caps.isEmpty then s!"U (loop ({ppVTy A}) ({ppVTy B}))"
    else s!"U (loop (({ppVTy capsT}) * ({ppVTy A})) (({ppVTy capsT}) * ({ppVTy B})))"
  let finA := if caps.isEmpty then "io_a <- return io_fin;" else "let (io_caps, io_a) = io_fin;"
  let finB := if caps.isEmpty then "io_b <- return io_fin;" else "let (io_caps, io_b) = io_fin;"
  let st := s!"({inner}) * {extraT}"
  let res := s!"({out} * ({out} * ({ppVTy A})))"
  let res' := s!"({out} * ({out} * ({ppVTy B})))"
  let dx := destructNames "io_x" extra
  let rc := rebindCaps caps "io_caps"
  let ex := tupleNames extra
  s!"extern mk_input : !({bs} => ref input)
extern mk_output : !(i32 => ref output)
extern take_input : !(ref input => {bs})
extern take_output : !(ref output => i32 * {bs})
{clockExterns caps}
main : {bs} -o F (U (loop {res} {res'})) =
  fun (io_inp : {bs}) ->
    stdin <- return ((unbang mk_input) io_inp);
    stdout <- return ((unbang mk_output) i32[1]);
    stderr <- return ((unbang mk_output) i32[2]);
    {makeExtra caps args}io_l : {inner} <- ({body.pp 0 6});
    io_step : !U ({st} -o F ({res} + ({st})) & F {res'}) <- return (!thunkv fun (io_s : {st}) ->
      < let (io_it, io_x) = io_s;
        {dx}io_o <- (nu_out (force io_it)).1;
        case io_o \{
          inl io_fin ->
            {finA}
            {rc}{takeExtra caps}io_in <- return ((unbang take_input) stdin);
            io_out <- return ((unbang take_output) stdout);
            io_err <- return ((unbang take_output) stderr);
            return (inl (io_out, (io_err, io_a)))
        | inr io_rest -> return (inr (io_rest, {ex}))
        },
        let (io_it, io_x) = io_s;
        {dx}io_fin <- (nu_out (force io_it)).2;
        {finB}
        {rc}{takeExtra caps}io_in <- return ((unbang take_input) stdin);
        io_out <- return ((unbang take_output) stdout);
        io_err <- return ((unbang take_output) stderr);
        return (io_out, (io_err, io_b)) >);
    io_f <- return (unbang (unfold[loop {res} {res'}, {st}] io_step));
    io_s0 : {st} <- return (io_l, {ex});
    return (thunkv nu_in < (nu_out (force io_f io_s0)).1, (nu_out (force io_f io_s0)).2 >)
"

/-- A checked program run by `run_io`: its externs, its capabilities, and `main`'s result type
`A`. A program with capability externs, or a `main` with no externs that returns a loop (its
capabilities are none, and its loop is `U (loop A B)`). -/
structure IOMain where
  externs : List ExternSpec
  caps : List ExternSpec
  A : CVTy
  /-- `some B` when `main` returns a loop `U (loop (Caps * A) (Caps * B))` (or `U (loop A B)`
  with no capabilities), run until it finishes (SPEC §11, §14). -/
  loopB : Option CVTy

/-- The externs of a checked `main`, and, when it has capabilities, its result type after them. -/
def ioMainOf (p : Program) (c : Checked) : Except String (Option IOMain) := do
  let ds := p.decls.toArray
  let xs ← match externs ds with
    | .ok xs => pure xs
    | .error e => throw e.render
  -- A `main` with no externs that returns a loop is driven too, with no capabilities (SPEC §14).
  if xs.isEmpty then
    match c.C with
    | .ret (.thunk (.nu (.amp (.ret (.sum A (.tvar 0))) (.ret B)))) =>
      return if c.C = .ret (.thunk (.loop A B)) then some ⟨[], [], A, some B⟩ else none
    | _ => return none
  let specs ← checkExterns xs
  let caps := capsOf specs
  if caps.isEmpty then
    throw ("a program with externs must declare a capability (`stdin`, `stdout`, `stderr`, " ++
      "`clock` or `args`)")
  let names := caps.map (·.name)
  if names.eraseDups.length != names.length then throw "a capability is declared twice"
  let T₀ := capsTy caps
  let shape := s!"`main` must have type `F (Caps * A)`, or `F (U (loop (Caps * A) (Caps * B)))` " ++
    s!"to run until it finishes, with `Caps` = `{ppVTy T₀}`, its capabilities in declaration order"
  match c.C with
  | .ret (.tensor T A) =>
    if T = T₀ then pure (some ⟨specs, caps, A, none⟩) else throw shape
  | .ret (.thunk (.nu (.amp (.ret (.sum (.tensor T A) (.tvar 0))) (.ret (.tensor T' B))))) =>
    if c.C = .ret (.thunk (.loop (.tensor T A) (.tensor T' B))) ∧ T = T₀ ∧ T' = T₀ then
      pure (some ⟨specs, caps, A, some B⟩)
    else throw shape
  | _ => throw shape

/-- The wrapped program: the declarations other than `main` and the capabilities, the
harness's externs, and `run_io` as `main`.  `[spec §11]` -/
def ioWrapper (p : Program) (m : IOMain) (args : List UInt8 := []) : Except String Program := do
  let some body := p.decls.findSome? (fun | .main _ _ M => some M | _ => none)
    | throw "no `main`"
  let keep := p.decls.filter fun
    | .main .. => false
    | .extern _ n _ => !(m.caps.any (·.name == n.name))
    | _ => true
  let src := match m.loopB with
    | none => wrapperSrc (m.caps.map (·.name)) (capsTy m.caps) m.A body args
    | some B => loopWrapperSrc (m.caps.map (·.name)) (capsTy m.caps) m.A B body args
  match parseProgram src (resolve := false) with
  | .ok w => pure ⟨keep ++ w.decls⟩
  | .error e => throw s!"run_io: {e.render}\n{src}"

/-! ### The model run -/

/-- The model of an extern, by its type. -/
def modelFor (T : CVTy) : Option CVal := (stdModel.find? (fun p => decide (p.1 = T))).map (·.2)

theorem modelFor_mem {T : CVTy} {v : CVal} (h : modelFor T = some v) : (T, v) ∈ stdModel := by
  unfold modelFor at h
  cases hf : stdModel.find? (fun p => decide (p.1 = T)) with
  | none => rw [hf] at h; cases h
  | some q =>
    rw [hf] at h
    cases h
    have hq := List.find?_some hf
    simp only [decide_eq_true_eq] at hq
    rw [← hq]
    exact List.mem_of_find?_eq_some hf

/-- Every extern given its model, with the proof `io_every_run` asks for. -/
def modelsOf : (Γ : Ctx CVTy) →
    Option { γ : List CVal // List.Forall₂ (fun s v => s.live = true ∧ (s.ty, v) ∈ stdModel) Γ γ }
  | [] => some ⟨[], .nil⟩
  | s :: Γ =>
    if hl : s.live = true then
      match hm : modelFor s.ty with
      | some v => (modelsOf Γ).map fun ⟨γ, h⟩ => ⟨v :: γ, .cons ⟨hl, modelFor_mem hm⟩ h⟩
      | none => none
    else none

/-- `run_io`'s type: `Bytes ⊸ F R`, or `Bytes ⊸ F (U (Loop R R'))` when `main` runs until it
finishes. -/
def ioType (loops : Bool) (R R' : CVTy) : CCTy :=
  if loops then .arr bytesTy (.ret (.thunk (.loop R R'))) else .arr bytesTy (.ret R)

/-- `run_io` checked, with the model of every extern: the object of `io_every_run` and
`io_loop_every_run`. -/
structure IORun where
  c : Checked
  loops : Bool
  R : CVTy
  R' : CVTy
  hC : c.C = ioType loops R R'
  hR : R.Persistent
  hR' : R'.Persistent
  N : CExpr
  he : c.e = .lam N
  γ : List CVal
  hγ : List.Forall₂ (fun s v => s.live = true ∧ (s.ty, v) ∈ stdModel) c.ctx γ

/-- The expression `bcc interp` runs: `run_io[γ] inp`. -/
def IORun.expr (r : IORun) (inp : List UInt8) : Expr :=
  .app (BoCa.Fig16.LogRel.substAll r.γ r.c.e) (.val (bytesVal inp))

section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- **The model run is safe and leak-free**: for a `main` that does not loop, every run of
`IORun.expr`, from the empty memory and under every allocator, continues to a value of
`run_io`'s result type at the empty memory. `io_every_run` at the checked wrapper.
`[spec §11, §13]` -/
theorem IORun.every_run (r : IORun) (hp : r.c.pins = []) (hl : r.loops = false) (inp : List UInt8)
    {μ₁ : BoCa.BoLo.Heap} {e₁ : Expr}
    (hs : BoCa.BoLo.Steps BoCa.Adequacy.emptyMem (r.expr inp) μ₁ e₁) :
    ∃ v : CVal, BoCa.BoLo.Steps μ₁ e₁ BoCa.Adequacy.emptyMem (.val v) ∧
      ∃ ls δ, BoCa.Fig16.LogRel.Core.vCE none true r.R ls δ v BoCa.Fig16.PMap.empty := by
  have h := r.c.deriv hp
  rw [r.hC, ioType, hl] at h
  exact io_every_run h r.hR r.hγ (bytesVal_bytes inp) hs

/-- **The model run of a program that runs until its input ends**: for every `n`, every run of
`run_io[γ] inp` observed at most `n` times, from the empty memory and under every allocator,
continues to a value at the empty memory. `io_loop_every_run` at the checked wrapper; a run of
`bcc interp` that finishes after `k` observations is the run of the `k`-th prefix.
`[spec §11, §13]` -/
theorem IORun.loop_every_run (r : IORun) (hp : r.c.pins = []) (hl : r.loops = true)
    (inp : List UInt8) (n : ℕ)
    {μ₁ : BoCa.BoLo.Heap} {e₁ : Expr}
    (hs : BoCa.BoLo.Steps BoCa.Adequacy.emptyMem
      (BoCa.Fig16.LogRel.substAll r.γ (ioLoopE r.N inp n)) μ₁ e₁) :
    ∃ v : CVal, BoCa.BoLo.Steps μ₁ e₁ BoCa.Adequacy.emptyMem (.val v) ∧
      ∃ ls δ, BoCa.Fig16.LogRel.Core.vCE none true (.sum r.R r.R') ls δ v
        BoCa.Fig16.PMap.empty := by
  have h := r.c.deriv hp
  rw [r.hC, ioType, hl, show r.c.t.erase = _ from r.he] at h
  exact io_loop_every_run h r.hR r.hR' r.hγ inp n hs

end

/-- Check the wrapper and give every extern its model. The wrapper holds `main`'s printed core,
checked already with its explicit copies (`clone(x)`, printed as `x`), so implicit copies are not
checked again; and at the program's counts `cnts`, which its printed core does not record
(SPEC §53). -/
def ioRunOf (w : Program) (cnts : CntTable := {}) : Except String IORun := do
  let r ← match checkProgram w (copies := false) (cnts := some cnts) with
    | .ok r => pure r
    | .error e => throw s!"run_io:{e.render}"
  let some c := r.main | throw "run_io: no main"
  let persistErr (R : CVTy) : String :=
    s!"`main`'s result `{ppVTy R}` must be persistent to be printed after the run"
  match he : c.e with
  | .lam N =>
    match modelsOf c.ctx with
    | none => throw "run_io: an extern has no model"
    | some ⟨γ, hγ⟩ =>
      match c.C with
      | .arr _ (.ret (.thunk (.nu (.amp (.ret (.sum R (.tvar 0))) (.ret R'))))) =>
        if hC : c.C = ioType true R R' then
          if hR : R.persistent = true then
            if hR' : R'.persistent = true then pure ⟨c, true, R, R', hC, hR, hR', N, he, γ, hγ⟩
            else throw (persistErr R')
          else throw (persistErr R)
        else throw "run_io: wrong type"
      | .arr _ (.ret R) =>
        if hC : c.C = ioType false R .unit then
          if hR : R.persistent = true then pure ⟨c, false, R, .unit, hC, hR, rfl, N, he, γ, hγ⟩
          else throw (persistErr R)
        else throw "run_io: wrong type"
      | _ => throw "run_io: wrong type"
  | _ => throw "run_io: `main` is not a function"

end Frontend.Check

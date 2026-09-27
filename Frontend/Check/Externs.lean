import Frontend.Parser
import Frontend.Print
import Frontend.Check.Program
import Core.Stdio

/-!
# Frontend — Check — externs and standard I/O  `[spec §11]`

The standard externs, each with its type, its role, its model and its assurance level
(decision 27), and the `run_io` wrapper a program with capability externs is run through.

* **The table** (`stdExterns`). `stdin`, `stdout`, `stderr` are capabilities: cells whose content
  is the stream (file descriptor `0`, `1`, `2` in compiled code). `read_byte` and `write_byte`
  are the operations, lowered to WASI `fd_read`/`fd_write`. `mk_input`, `mk_output`,
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
open BoCa.Fig16.LogRel.Core (Opaque BytesV bytesTy outRep externTy readByteC writeByteC mkInputC
  mkOutputC takeInputC takeOutputC readByteV writeByteV mkInputV mkOutputV takeCapV stdModel
  io_every_run)

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
  | .typedUnsafe => "typed-unsafe"
  | .boundaryChecked => "boundary-checked"
  | .smtVerified => "semi-automatically verified"
  | .proved => "proved"

def Assurance.render (a : Assurance) : String := s!"{a.name} ({a.level})"

/-- What an extern is. -/
inductive ExternRole where
  /-- A capability: a cell whose content is the stream with this file descriptor. -/
  | cap (fd : Nat)
  | readByte
  | writeByte
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
  | .cap _ => true
  | _ => false

/-- The standard externs.  `[spec §11]` -/
def stdExterns : List ExternSpec :=
  [ ⟨"stdin", .ref (.opq .input), .cap 0, "vC_bytes (a cell holding the input)",
      some ("a runtime cell holding fd 0", .assumed)⟩,
    ⟨"stdout", .ref (.opq .output), .cap 1, "vC_outRep (a cell holding (1, nil))",
      some ("a runtime cell holding fd 1", .assumed)⟩,
    ⟨"stderr", .ref (.opq .output), .cap 2, "vC_outRep (a cell holding (2, nil))",
      some ("a runtime cell holding fd 2", .assumed)⟩,
    ⟨"read_byte", externTy (readByteC (.opq .input)), .readByte, "readByte_meets",
      some ("WASI fd_read of one byte (libc read(2))", .interpChecked)⟩,
    ⟨"write_byte", externTy (writeByteC (.opq .output)), .writeByte, "writeByte_meets",
      some ("WASI fd_write of one byte (libc write(2))", .interpChecked)⟩,
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

def bytesSrc : String := "(mu X. 1 + (i32 * X))"

/-- Rebind the returned capabilities to their names: `let (c₁, r) = …; …`. -/
def rebindCaps : List String → String → String
  | [], _ => ""
  | [n], v => s!"{n} <- return {v};\n    "
  | [n₁, n₂], v => s!"let ({n₁}, {n₂}) = {v};\n    "
  | n :: ns, v => s!"let ({n}, io_rest_{ns.length}) = {v};\n    " ++
      rebindCaps ns s!"io_rest_{ns.length}"

/-- The source of `run_io`: the harness's externs and the wrapped `main`.  `[spec §11]` -/
def wrapperSrc (caps : List String) (capsT A : CVTy) (body : Comp) : String :=
  let B := bytesSrc
  let out := s!"(i32 * {B})"
  s!"extern mk_input : !({B} => ref input)
extern mk_output : !(i32 => ref output)
extern take_input : !(ref input => {B})
extern take_output : !(ref output => i32 * {B})

main : {B} -o F ({out} * ({out} * ({ppVTy A}))) =
  fun (io_inp : {B}) ->
    stdin <- return ((unbang mk_input) io_inp);
    stdout <- return ((unbang mk_output) i32[1]);
    stderr <- return ((unbang mk_output) i32[2]);
    io_r : ({ppVTy capsT}) * ({ppVTy A}) <- ({body.pp 0 6});
    let (io_caps, io_a) = io_r;
    " ++ rebindCaps caps "io_caps" ++ "io_in <- return ((unbang take_input) stdin);
    io_out <- return ((unbang take_output) stdout);
    io_err <- return ((unbang take_output) stderr);
    return (io_out, (io_err, io_a))
"

/-- A checked program with capability externs: its externs, and `main`'s result type `A`. -/
structure IOMain where
  externs : List ExternSpec
  caps : List ExternSpec
  A : CVTy

/-- The externs of a checked `main`, and, when it has capabilities, its result type after them. -/
def ioMainOf (p : Program) (c : Checked) : Except String (Option IOMain) := do
  let ds := p.decls.toArray
  let xs ← match externs ds with
    | .ok xs => pure xs
    | .error e => throw e.render
  if xs.isEmpty then return none
  let specs ← checkExterns xs
  let caps := capsOf specs
  if caps.isEmpty then
    throw "a program with externs must declare a capability (`stdin`, `stdout` or `stderr`)"
  let names := caps.map (·.name)
  if names.eraseDups.length != names.length then throw "a capability is declared twice"
  match c.C with
  | .ret (.tensor T A) =>
    if T = capsTy caps then pure (some ⟨specs, caps, A⟩)
    else Except.error (s!"`main` must have type `F (Caps * A)` with `Caps` = " ++
      s!"`{ppVTy (capsTy caps)}`, its capabilities in declaration order")
  | _ => throw s!"`main` must have type `F (Caps * A)` with `Caps` = `{ppVTy (capsTy caps)}`"

/-- The wrapped program: the declarations other than `main` and the capabilities, the
harness's externs, and `run_io` as `main`.  `[spec §11]` -/
def ioWrapper (p : Program) (m : IOMain) : Except String Program := do
  let some body := p.decls.findSome? (fun | .main _ _ M => some M | _ => none)
    | throw "no `main`"
  let keep := p.decls.filter fun
    | .main .. => false
    | .extern _ n _ => !(m.caps.any (·.name == n.name))
    | _ => true
  let src := wrapperSrc (m.caps.map (·.name)) (capsTy m.caps) m.A body
  match parseProgram src with
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

/-- `run_io` checked, with the model of every extern: the object of `io_every_run`. -/
structure IORun where
  c : Checked
  R : CVTy
  hC : c.C = .arr bytesTy (.ret R)
  hR : R.Persistent
  γ : List CVal
  hγ : List.Forall₂ (fun s v => s.live = true ∧ (s.ty, v) ∈ stdModel) c.ctx γ

/-- A byte list as a value of `Bytes`. -/
def bytesVal : List UInt8 → CVal
  | [] => .inj₁ .unit
  | b :: bs => .inj₂ (.pair (.i32 b.toUInt32) (bytesVal bs))

theorem bytesVal_bytes : ∀ bs, BytesV (bytesVal bs)
  | [] => .nil
  | b :: bs => .cons b.toUInt32 (bytesVal_bytes bs)

/-- The expression `bcc interp` runs: `run_io[γ] inp`. -/
def IORun.expr (r : IORun) (inp : List UInt8) : Expr :=
  .app (BoCa.Fig16.LogRel.substAll r.γ r.c.e) (.val (bytesVal inp))

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ] in
/-- **The model run is safe and leak-free**: every run of `IORun.expr`, from the empty memory and
under every allocator, continues to a value of `run_io`'s result type at the empty memory.
`io_every_run` at the checked wrapper.  `[spec §11, §13]` -/
theorem IORun.every_run (r : IORun) (inp : List UInt8) {μ₁ : BoCa.BoLo.Heap} {e₁ : Expr}
    (hs : BoCa.BoLo.Steps BoCa.Adequacy.emptyMem (r.expr inp) μ₁ e₁) :
    ∃ v : CVal, BoCa.BoLo.Steps μ₁ e₁ BoCa.Adequacy.emptyMem (.val v) ∧
      ∃ ls δ, BoCa.Fig16.LogRel.Core.vCE none true r.R ls δ v BoCa.Fig16.PMap.empty := by
  have h := r.c.deriv
  rw [r.hC] at h
  exact io_every_run h r.hR r.hγ (bytesVal_bytes inp) hs

/-- Check the wrapper and give every extern its model. -/
def ioRunOf (w : Program) : Except String IORun := do
  let r ← match checkProgram w with
    | .ok r => pure r
    | .error e => throw s!"run_io:{e.render}"
  let some c := r.main | throw "run_io: no main"
  match hC : c.C with
  | .arr A (.ret R) =>
    if hA : A = bytesTy then
      if hR : R.persistent = true then
        match modelsOf c.ctx with
        | some ⟨γ, hγ⟩ => pure ⟨c, R, by rw [hC, hA], hR, γ, hγ⟩
        | none => throw "run_io: an extern has no model"
      else throw s!"`main`'s result `{ppVTy R}` must be persistent to be printed after the run"
    else throw "run_io: wrong input type"
  | _ => throw "run_io: wrong type"

end Frontend.Check

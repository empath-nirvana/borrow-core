import Frontend.Parser
import Frontend.Print
import Frontend.Elab.Subst
import Frontend.Elab.Instances
import Frontend.Elab.Divisions

/-!
# Frontend — Elab — effects and handlers  `[spec §18, §19, §20, §21, §30, §32, §34, §38, §39]`

An effect declares operations, each **answering** (`fn`) or **control** (`ctl`, with the
structural qualifier of its continuation: cancellable by default, must resume at `linear ctl`,
unrestricted at `multi ctl`). An effect is one or the other. This pass resolves every operation to
the handler that serves it, before the rest of the sugar; it knows no effect by name.

* **Answering effects** are capabilities (§18): `handler h(s: S) for E { op(x) -> e }` gives each
  clause as a function over a `mut` borrow of the state,

      fn h__op<'l>(c: mut 'l S, x: A) -> mut 'l S * B = let r = modify c { s -> M; (s, r) }; (c, r)

  `with h(e) { S }` is a borrow block of the state's cell whose callback's parameter is the
  capability, and an operation call `op(v)` is a call of the innermost handler's clause on it,
  which hands it back. The capability is threaded as a `let mut` variable is.
* **Control effects** are the kernel's (§19). Each `with h(args) { S }` of a control handler is a
  handler site with a static name `n` of its own, and an operation is resolved lexically to the
  innermost site of its instance: `perform[n.i](v)`, or `abort[n.i](v)` for an abortive operation
  (answer `0` at a qualifier with weakening). The site becomes the kernel's `handle[n]` with the
  handler's clauses, assembled where the types are known (`VSugar.hndCtl`, `Frontend/Sugar.lean`).
  A handler may perform the operations of its own row (`with E₂[…]` after `for`), which resolve to
  the sites around its `with`. Its clauses are `!` code, and what they use is passed to them
  (§21): a handler whose operations are all abortive runs its clauses after it, and one whose
  operations resume has a state, its parameters and the capabilities its clauses use; `k(v)`
  resumes.
* **Instances** (§38). An instance is an effect at its type arguments, read off an operation's
  argument's type and a template call's arguments' at the declaration's own types, before this
  pass (`Instances.table`, `Env.table`). An operation goes to the innermost handler of its
  instance, or of the name it is performed at (`n.op(v)`, `with n = h(…)`); a row's entries are
  slots, named or not, that a copy relabels its sites as (`slotsOf`), so an operation of a
  template is resolved at the template's types and instantiation cannot reroute it.
* **A function's row** is the set of effect instances it performs: the operations it calls, and
  the rows of the functions it calls, less those a `with` inside it handles. It is inferred in
  declaration order; a written row (`fn f(…) -> T with E[A]`) is a promise that the inferred row is
  within it, and gives the type arguments of an effect the function performs directly. A function
  with a row is elaborated once per assignment of its effects to what serves them in scope (the
  handlers of its answering effects, the sites of its control effects), as a generic function is
  once per instance (decision 45): the copy `f__…` takes the capabilities first and hands them back
  first, and its type has the sites' operations as its row, `A ⇒ F[n.i …] B`. A call of `f` is a
  call of that copy, bound before the value it is in, so that it is a computation of its own.
* **A recursive group** (§20, §21) is the bounded fixed point of its generator, taken at the
  record of its members, each taking the copy's capabilities first as any copy does; a call of a
  member inside it is a direct call of the self-reference. A layer is a transformer of the
  generator, applied before the fixed point.
* **An effectful block** (§30) is a closure written as an argument at a parameter of function
  type whose body performs control operations: it is elaborated where it is written, its
  operations resolved to the sites around it, and the call is a call of the callee's copy at the
  block's row (`blockCall`, `copyFor`'s blocks): the parameter's type is `!U(A -o F[row] B)` there,
  a call of it is an effectful call (`blockParamCall`), and it is only called or passed on.
* **A handler whose clause takes `k` out of a box** (`unbox k`) receives it boxed at `top`, BOXED-κ
  (§28, `HInfo.boxK`).

* **A block that uses capabilities** (an answering handler's state, a `for`'s threaded variables)
  takes them first and hands them back first; the callee's copy passes them at each call of the
  block parameter (§32, `Blk.caps`).
* **A handler's lifetime parameters** are the meet of the lifetimes in scope at each `with`
  (§32, `HInfo.lives`).
* **The platform** (§34). A handler whose state is lent, `handler h(&mut s: S)`, gives each
  clause the capability itself (`HSig.lent`). An answering operation may take lifetime parameters,
  which its clause takes after the capability's. The effects of the system interface that `main`
  performs are served by the platform's handlers (`platformEffects`, `platformMain`) on the cells
  `main` holds: such a capability is the cell (`HSig.cell`), threaded by name, and each operation
  lends it to its clause. A task of a handler that keeps its continuation boxed at its lifetime
  (`Env.gives`) is given the capabilities its body uses, lent for the borrow block around it
  (`Cx.givenC`).
* **Integer division** (§39). A division that can fail at its operands' width raises
  `Fail[DivError]`: the walk that reads the instances decides it, and it is written as the checked
  division and a `raise` before rows are inferred (`Frontend/Elab/Divisions.lean`); `lib/arith.bc`
  is elaborated first for it when the program does not include it (`elaborate`'s `divLib`). A
  `Fail[DivError]` that `main` performs and handles nowhere is served by `main_div_error` around
  the rest of `main` from its first statement that performs it (`divMain`, `splitDiv`).

What is not provided, with the message that says so: an operation inside a closure or block that
is not run in place, other than an effectful block; a block parameter stored; a function with a
row passed as a value (effectful callbacks, #161); a lend `&mut x` in the arguments of a call that threads a capability; an operation of an answering
effect inside a clause; an effect with both kinds of operation; type parameters on an answering
effect; an unrestricted operation that answers `never` (`multi ctl`: an abortive operation is
cancellable, decision 63); a function with a row whose result is a computation (a loop or a
generator).
-/

namespace Frontend.Elab.Effects
open Frontend.Check (CVTy)

/-! ### What is declared -/

/-- An effect: its type parameters and its operations. -/
structure EffSig where
  name : String
  tps : List String
  ops : List OpDecl

/-- The effect's operations are answering. -/
def EffSig.answering (e : EffSig) : Bool := e.ops.all (·.kind == .fn)

/-- The operation `decl`, the `idx`-th of the effect `eff`. -/
structure OpSig where
  eff : String
  idx : Nat
  decl : OpDecl

/-- An answering handler: its name, its effect, its state and its clauses. With `lent`, each
clause is given the state lent, `mut 'l S`, rather than its value (SPEC §34). -/
structure HSig where
  name : String
  eff : String
  st : Ident
  S : VTy
  clauses : List Clause
  sp : Span
  lent : Bool := false
  /-- At a use: the capability is the state's cell itself, `ref S`, owned and threaded by name,
  and each operation lends it for its clause (SPEC §34). `main`'s platform capabilities. -/
  cell : Bool := false

/-- The key of a capability's handler in a copy's name: a cell's copies are its own. -/
def HSig.key (h : HSig) : String := if h.cell then h.name ++ "_cell" else h.name

/-- An instance of an effect: its type arguments, when they are determined (SPEC §38). In a
function's row it is a **slot**, with its name when the row names it (`with src: Kube`): two
slots are two entries, whatever their type arguments are at a use. An operation performed at a
named handler (`src.op(…)`) is the instance named so. -/
structure Inst where
  eff : String
  args : Option (List VTy)
  name : Option String := none
  deriving BEq

/-- A function's type and value taken apart: its lifetime parameters (outermost first), its
parameter's type, its result type, its parameter's name and its body. `!` or not. -/
structure FnParts where
  bang : Bool
  lives : List (Ident × Life)
  P : VTy
  T : VTy
  p : Ident
  body : Comp

/-- A function with a non-empty row: its declaration and the effect instances it performs. A
member of a recursive group (SPEC §20) names its group and its index there. -/
structure FSig where
  name : String
  row : List Inst
  decl : Decl
  group : Option (String × Nat) := none

/-- A recursive group (SPEC §20): the functions of one strongly connected component of the calls,
each taken apart (`FnParts`), in declaration order. The group is named by its first member. -/
structure RGroup where
  name : String
  members : List (String × FnParts)
  sp : Span
  /-- The type parameters of a generic group (SPEC §15, §20), each member's: its generator and its
  copies are templates in them, instantiated where a copy is called.  `[spec §31]` -/
  tps : List Ident := []
  /-- The lifetime parameters of the group, each member's (SPEC §15, §20): its generator and its
  copies are generic in them, outside the capabilities' lifetimes.  `[spec §31]` -/
  lives : List (Ident × Life) := []

/-- What the elaboration knows, each declared before the point being elaborated. -/
structure Env where
  /-- The functions of the libraries included, whose elaboration is not reported. -/
  lib : List String := []
  effs : List EffSig := []
  ops : List OpSig := []
  handlers : List HSig := []
  chandlers : List CHandler := []
  fns : List FSig := []
  /-- The recursive groups declared so far. -/
  groups : List RGroup := []
  /-- The written type of every function declared so far, for its parameters' types. -/
  sigs : List (String × VTy) := []
  /-- The layers declared so far (SPEC §20), each with its declaration. -/
  layers : List (String × Decl) := []
  /-- Inside `with L { … }` of layers (SPEC §20), innermost first: the recursive groups called are
  driven by `bounded` over their generator transformed by them, and a call of a member performs
  the layers' rows too. A copy's body is outside them: they apply to the calls written inside. -/
  inLayers : List String := []
  /-- The recursive functions another function has the name of (SPEC §20): a call of one of these
  names is rejected, since a recursive group is found by name, before the types that choose among
  templates of one name are known.  `[spec §31]` -/
  clashes : List String := []
  /-- The functions declared so far that have no row, each with its declaration: a call that passes
  one an effectful block uses its copy at the block's row (`blockCall`).  `[spec §30]` -/
  plain : List (String × Decl) := []
  /-- In a copy made for effectful blocks: each block parameter and the effect instances its
  block performs, which a call of it performs (`rowV`).  `[spec §30]` -/
  cbRows : List (String × List Inst) := []
  /-- The functions declared so far that take computation parameters (SPEC §33): for each, its
  computation parameters by index, with their names and their provided rows. A call of one is a
  call of its copy for its arguments (`blockCall`); it is never used as written.  `[spec §33]` -/
  comps : List (String × List (Nat × String × List (Ident × List VTy))) := []
  /-- The type arguments recorded at each call of an operation or a template, typed where the
  types are known (`Instances.table`).  `[spec §38]` -/
  table : Instances.Table := {}
  /-- The typing context of the program's declarations.  `[spec §38]` -/
  scope : Option TCx := none
  /-- The declaration whose code is being elaborated (`Instances.ownerKey`) and its type
  parameters: the frame in which the table's types, the sites' and the rows' are read.
  `[spec §38]` -/
  owner : String := ""
  ownerTps : List String := []

/-- A capability in scope: the answering effect it serves, the variable holding its `mut 'l S`
borrow, the lifetime `'l`, and the handler. Or the variable a `for`'s site of an iteration effect
threads through its operation (`thr`, the name of its type parameter `W`): passed and handed back
as a capability is, and given to the operation with its argument, which answers it again. -/
structure Cap where
  eff : String
  var : String
  life : String
  h : HSig
  thr : Option String := none
  /-- In a copy made for effectful blocks: a capability a block uses (SPEC §32). A handler or a
  `for` of its effect inside the copy does not shadow it: the block's operations go to where the
  block was written.  `[spec §32]` -/
  blk : Bool := false
  /-- The handler's name, `with n = h(…)`, or a named slot's of the copy's row (SPEC §38). -/
  name : Option String := none
  /-- In a copy: the capability of a slot of its row, which are unordered (SPEC §38). -/
  slot : Bool := false

/-- The variable holding a copy's capability of `e` (and of the slot named `x`), and its
lifetime's name: one per effect and slot. `e` has its first letter lowered (an effect's name starts
with a capital, so no two effects share it); a slot's name follows the length of `e`'s, which
says where `e` ends. -/
def capKey (e : String) (x : Option String) : String := match x with
  | none => "_" ++ e.decapitalize
  | some x => s!"n{e.length}_{e.decapitalize}_{x}"
def capVar (e : String) (x : Option String) : String := "fx_c" ++ capKey e x
def capLife (e : String) (x : Option String) : String := "fx_l" ++ capKey e x

/-- A capability's type: `mut 'l S`, or the threaded variable's `W`. -/
def Cap.ty (sp : Span) (c : Cap) : VTy := match c.thr with
  | some W => .name sp W
  | none => if c.h.cell then .ref sp c.h.S else .mut sp (.var sp c.life) c.h.S

/-- A handler site of a control effect in scope: the effect, the site's static name, and the
effect's type arguments there. -/
structure Site where
  eff : String
  n : Nat
  args : List VTy
  /-- A `for`'s site of an iteration effect: the variable it threads through the operation and
  the name of its type, `(w, W)`; the operation `op(x: A)` is `A * W ~> W` there. -/
  thr : Option (String × String) := none
  /-- The `with`, or the function whose copy was given the site. -/
  sp : Span
  /-- What serves it, for the reports: the handler's name, or `the caller`. -/
  what : String
  /-- The handler's name, `with n = h(…)`, or a named slot's (SPEC §38). -/
  name : Option String := none
  /-- In a copy, or in a control handler's clauses: the site serving a slot of the row, whose
  type arguments in the frame of the code being elaborated are these. Slots are unordered: an
  operation that two of them could serve is ambiguous (SPEC §38). -/
  slot : Option (List VTy) := none

/-- The type arguments an operation is resolved against at the site: the slot's, in a copy. -/
def Site.at (s : Site) : List VTy := s.slot.getD s.args

/-- The variable a `for`'s site threads. -/
def Site.thrVar (s : Site) : Option String := match s.thr with
  | some (w, _) => some w
  | none => none

/-- The generator of a recursive group being elaborated (SPEC §20): its members, the site `e` of
the exhaustion effect, and the variable `self` holding the self-reference `1 + !U(1 ⊸ R)`
(`bounded_fix`'s at the record `R` of the members). -/
structure RSelf where
  members : List String
  e : Nat
  self : String
  /-- Each member's computation type in `R`, `E ⊗ Pⱼ ⊸ F_Σ (E ⊗ Tⱼ)`: the type of its self-call. -/
  Cs : List CTy
  /-- The environment `E`: the capabilities the group's copy takes and hands back. -/
  env : List Cap
  /-- The sites the copy serves its row's control effects at, by effect. -/
  served : List Site
  /-- Under a heap driver: a call of itself is a call of the self-reference `fx_rself{j}` of the
  group's machine source, which the typed elaboration turns into a request (`recMachine`). -/
  deep : Bool := false

/-- A report for `bcc check` (SPEC §18, #126). A line of its kind (`effect`, `row`, `lowering`,
`call`) says what the elaboration did. A handler site says what it is, its static name and its
operations, and its operations' lowering is rendered from the kinds the checker gives their
clauses at the `handle` nodes of that name (`Frontend/Check/Program.lean`, SPEC §19). -/
inductive Report where
  | line (kind msg : String)
  | site (n : Nat) (head : String) (ops : List String) (tail : String)
  deriving BEq, Inhabited

/-- The state of the elaboration: counters for fresh names and site names, the reports for
`bcc check`, and the copies made (finished ones in `made`, in the order they were finished). -/
structure St where
  fresh : Nat := 0
  site : Nat := 1
  reports : Array (Span × Report) := #[]
  made : Array (String × Decl) := #[]
  started : List String := []
  /-- Elaborating a library declaration: nothing is reported. -/
  quiet : Bool := false
  /-- The sites that observe their computation one turn at a time: a `for`'s site of an iteration
  effect and a stored generator's (SPEC §15). A counted loop whose body performs a resuming
  operation of one of them is a div loop, one turn per observation; of any other site, a total
  loop at the row (SPEC §16, *Effectful bodies*). -/
  perTurn : List Nat := []
  /-- The ports of each copy made for computation parameters (SPEC §33), by the copy's name: per
  parameter index, the site of each provided effect, and whether it is the copy's own (a `with`
  inside it) rather than one of its row's.  `[spec §33]` -/
  ports : List (String × List (Nat × List (Site × Bool))) := []
  /-- The capabilities `main` lends to the platform's handlers (SPEC §34). -/
  platform : List String := []
  /-- `main` is served `Fail[DivError]` by `main_div_error` (SPEC §39): it answers `inr ()` when a
  division's error reached it, which the runtime reports as the exit status. -/
  exits : Bool := false
  /-- The key of each copy made (`DefKey`), for the checker's `use` nodes. -/
  keys : Array DefKey := #[]

abbrev EM := StateT St (Except Error)

def fresh (pre : String) : EM String :=
  modifyGet fun s => (s!"{pre}{s.fresh}", { s with fresh := s.fresh + 1 })

/-- A fresh static name for a handler site. -/
def freshSite : EM Nat := modifyGet fun s => (s.site, { s with site := s.site + 1 })

/-- A report for `bcc check` (SPEC §18, #126): its kind (`effect`, `row`, `lowering`, `call`) and
its text, at `sp`. -/
def report (sp : Span) (kind : String) (msg : String) : EM Unit :=
  modify fun s => if s.quiet then s else { s with reports := s.reports.push (sp, .line kind msg) }

/-- A handler site's report: `head`, then each operation of `ops` with its clause's lowering,
then `tail`. -/
def reportSite (sp : Span) (n : Nat) (head : String) (ops : List String) (tail : String) : EM Unit :=
  modify fun s => if s.quiet then s else { s with reports := s.reports.push (sp, .site n head ops tail) }

/-- Record a copy's key, once. -/
def recordKey (k : DefKey) : EM Unit :=
  modify fun s => if s.keys.any (·.name == k.name) then s else { s with keys := s.keys.push k }

/-- The handler that serves `main` a division's error it handles nowhere (SPEC §39). -/
def mainDivHandler : String := "main_div_error"

/-- `m` with nothing reported when `q`: the code of `main`'s handler of a division's error. -/
def quietIf {α} (q : Bool) (m : EM α) : EM α := do
  if !q then return ← m
  let q₀ := (← get).quiet
  modify fun s => { s with quiet := true }
  let r ← m
  modify fun s => { s with quiet := q₀ }
  pure r

/-- The depth bound for the traversals below. -/
def fuel : Nat := 1 <<< 16

/-- The name of an answering handler's clause for `op`. -/
def clauseName (h op : String) : String := h ++ "__" ++ op

/-- The name of the copy of `f` for the keys `ks` (handlers and site names). -/
def copyName (f : String) (ks : List String) : String := f ++ "__" ++ "_".intercalate ks

def Env.eff? (env : Env) (x : String) : Option EffSig := env.effs.find? (·.name == x)
def Env.op? (env : Env) (x : String) : Option OpSig := env.ops.find? (·.decl.name.name == x)
def Env.fn? (env : Env) (x : String) : Option FSig := env.fns.find? (·.name == x)
def Env.handler? (env : Env) (x : String) : Option HSig := env.handlers.find? (·.name == x)
def Env.chandler? (env : Env) (x : String) : Option CHandler :=
  env.chandlers.find? (·.name.name == x)

/-- The effect is answering. -/
def Env.answering (env : Env) (e : String) : Bool := ((env.eff? e).map (·.answering)).getD false

/-- The effect is an **iteration effect** (SPEC §15): its one operation is control, resumes, and
answers `()`. A `for` over a call of a function that performs one handles it, and a stored
generator is such a call's pull view. The structure decides it, not the effect's name. -/
def Env.iterEff (env : Env) (e : String) : Bool :=
  match env.eff? e with
  | some sig => match sig.ops with
    | [o] => o.kind != .fn && (match o.res with | .unit _ => true | _ => false)
    | _ => false
  | none => false

/-- The **exhaustion effect** (SPEC §20): the first declared effect with no type parameters whose
one operation is abortive and takes no argument (`Exhausted` of `lib/rec.bc`). `bounded`, the
default driver of a recursion, performs it when the budget of depth is spent. The structure
decides it, not the effect's name. -/
def Env.exhEff? (env : Env) : Option EffSig :=
  env.effs.find? fun e => e.tps.isEmpty && match e.ops with
    | [o] => (match o.res with | .zero _ => true | _ => false) && o.kind != .ctl .lin &&
        o.kind != .fn && o.params.isEmpty
    | _ => false

/-- The function `x` is a **heap driver** of recursion (SPEC §20): its written type is
`!(!(A => B + A * (K + 1)) * (!(K * B => B + A * (K + 1)) * A) => U (loop B 1))`, a loop over a
group's machine, its `start` and `resume` (`deep` of `lib/rec.bc`). `with x { M }` drives the
recursive groups `M` calls by it. The structure decides it, not the name. -/
def Env.driver? (env : Env) (x : String) : Bool :=
  match env.sigs.lookup x with
  | some (.bang _ (.lolli _ (.tensor _ (.bang _ (.lolli _ _ (.sum _ _ (.tensor _ _ (.sum _ _ (.unit _))))))
      (.tensor _ (.bang _ (.lolli _ (.tensor _ _ _) (.sum _ _ _))) _)) (.thunk _ (.loop _ _ (.unit _))))) => true
  | _ => false

/-- A written type is a **layer**'s (SPEC §20): `!(!(A => B) * A => B)`, `A` and `B` its two type
parameters. A layer is a transformer of a recursion's generator: `with x { M }` applies it to the
recursive groups `M` calls, before their fixed point is taken; its body runs around each call a
member makes of the group, `call(a)` the call itself. The structure decides it, not the name. -/
def isLayerTy (tps : List String) : VTy → Bool
  | .bang _ (.lolli _ (.tensor _ (.bang _ (.lolli _ (.name _ a) (.name _ b))) (.name _ a')) (.name _ b')) =>
    tps == [a, b] && a == a' && b == b' && a != b
  | _ => false

/-- The layer `x`'s declaration. -/
def Env.layer? (env : Env) (x : String) : Option Decl := env.layers.lookup x

/-- The budget of depth `bounded` gives a recursion (SPEC §20): calibrated against the wasm stack
`wasmtime` is run with (`Backend.wasmStackBytes`, 64 MiB), so that a recursion at the budget leaves
room for the finalisers its unwind runs. Provisional (`docs/rec-effect/bounded-deep.md`). -/
def recBudget : Nat := 10000

/-- `U (pull A B R)`, written: the type of a stored generator. -/
def isPullTy : VTy → Bool
  | .thunk _ (.pull ..) => true
  | _ => false

/-- The provided row of a parameter's written type: `(A => B with E…)` or `!(A => B with E…)`, a
computation parameter's (SPEC §33).  `[spec §33]` -/
def provOf : VTy → Option (List (Ident × List VTy))
  | .rowed _ _ r | .bang _ (.rowed _ _ r) => some r.rowEffs
  | _ => none

/-- A parameter's written type with its provided row taken off: the function type it is.
`[spec §33]` -/
def unrowed : VTy → VTy
  | .rowed _ F _ => F
  | .bang sp (.rowed _ F _) => .bang sp F
  | A => A

/-- The parameter tuple's type of a function type as written, under its `!` and lifetimes. -/
def paramTyOf : VTy → Option VTy
  | .bang _ A | .all _ _ _ A => paramTyOf A
  | .lolli _ P _ => some P
  | _ => none

/-- The components of a call's argument tuple, each with whether its parameter's written type is
a stored generator's (`U (pull A B R)`). -/
def Env.pullArgs (env : Env) (f : String) (W : Val) : List (Val × Bool) :=
  match (env.sigs.lookup f).bind paramTyOf with
  | some P => go fuel P W
  | none => [(W, false)]
where
  go : Nat → VTy → Val → List (Val × Bool)
    | k + 1, .tensor _ A B, .pair _ V W => (V, isPullTy A) :: go k B W
    | _, P, W => [(W, isPullTy P)]

/-- An operation's parameter tuple type (`1` with no parameters). -/
def tupleTy (sp : Span) : List VTy → VTy
  | [] => .unit sp
  | [A] => A
  | A :: As => .tensor sp A (tupleTy sp As)

/-- The operation is abortive: answer `0` at a qualifier with weakening. -/
def _root_.Frontend.OpDecl.abortive (o : OpDecl) : Bool :=
  (match o.res with | .zero _ => true | _ => false) && (match o.kind with
    | .ctl .lin => false
    | .ctl _ => true
    | .fn => false)

/-- The qualifier of a control operation. -/
def _root_.Frontend.OpDecl.qual (o : OpDecl) : Qual := match o.kind with
  | .ctl q => q
  | .fn => .cancel

/-- The operations of a site, at its type arguments: `(q, A, B)` per operation, in order. -/
def Env.siteOps (env : Env) (s : Site) : List (Qual × VTy × VTy) :=
  match env.eff? s.eff with
  | none => []
  | some e =>
    let σ : TySubst := e.tps.zip s.args
    e.ops.map fun o =>
      let A := (tupleTy o.name.span (o.params.map (·.2))).subst σ
      match s.thr with
      | some (_, W) => (o.qual, .tensor o.name.span A (.name o.name.span W), .name o.name.span W)
      | none => (o.qual, A, o.res.subst σ)

/-- The row entries of the sites `ss`, in order: `n.i q A ~> B`, each site once (two slots of a
row may be served by one site, SPEC §38). -/
def Env.rowOf (env : Env) (ss : List Site) : Row :=
  let ss := ss.foldl (fun acc s => if acc.any (·.n == s.n) then acc else acc ++ [s]) []
  ss.foldr (fun s r =>
    ((env.siteOps s).zipIdx).foldr (fun ((q, A, B), i) r => .cons s.n i q A B r) r) .nil

/-! ### Type arguments -/

/-- First-order matching of a type `P` whose names `tps` are unknowns against `A`; `same` decides
two types without unknowns equal (expanding abbreviations, when it can). -/
def matchTyBy (same : VTy → VTy → Bool) (tps : List String) (σ : TySubst) (P A : VTy) :
    Option TySubst :=
  go fuel σ P A
where
  go : Nat → TySubst → VTy → VTy → Option TySubst
    | 0, _, _, _ => none
    | k + 1, σ, P, A =>
      let both (P₁ A₁ P₂ A₂ : VTy) : Option TySubst := do go k (← go k σ P₁ A₁) P₂ A₂
      match P, A with
      | .name _ x, A =>
        if tps.contains x then
          match σ.lookup x with
          | some B => if same B A then some σ else none
          | none => some ((x, A) :: σ)
        else if same P A then some σ else none
      | .tensor _ P₁ P₂, .tensor _ A₁ A₂ => both P₁ A₁ P₂ A₂
      | .sum _ P₁ P₂, .sum _ A₁ A₂ => both P₁ A₁ P₂ A₂
      | .lolli _ P₁ P₂, .lolli _ A₁ A₂ => both P₁ A₁ P₂ A₂
      | .bang _ P', .bang _ A' => go k σ P' A'
      | .ref _ P', .ref _ A' => go k σ P' A'
      | .array _ P', .array _ A' => go k σ P' A'
      | .app _ P₁ P₂, .app _ A₁ A₂ => both P₁ A₁ P₂ A₂
      | .lapp _ P' a, .lapp _ A' b => if a.strip == b.strip then go k σ P' A' else none
      | P, A => if same P A then some σ else none

/-- `matchTyBy` with types compared as written. -/
def matchTy (tps : List String) (σ : TySubst) (P A : VTy) : Option TySubst :=
  matchTyBy (fun a b => a.strip == b.strip) tps σ P A

/-- The type names `A` mentions among `tps`. -/
def mentions (tps : List String) (A : VTy) : Bool :=
  tps.any fun x => (A.subst [(x, .unk .none)]).strip != A.strip

/-- Every type parameter among `tps` that `A` mentions is given by `σ`: `A.subst σ` is determined,
whatever names the types `σ` gives are written with (an enclosing function's type parameter may
have the name of one of `tps`). -/
def solvedBy (tps : List String) (σ : TySubst) (A : VTy) : Bool :=
  tps.all fun x => !mentions [x] A || (σ.lookup x).isSome

/-! ### Rows -/

/-- The name a call applies: `f(…)`, `f[A](…)`, `f ['x](…)`. -/
def headName : Val → Option String
  | .var _ f | .defApp _ f _ => some f
  | .inst _ V _ | .unbang _ V => headName V
  | _ => none

/-- The type arguments `As`, as types of the frame of the code being elaborated: the
declarations in scope, and its declaration's type parameters as placeholders.  `[spec §38]` -/
def Env.keyOf (env : Env) (As : List VTy) : Option (List CVTy) := do
  let c ← env.scope
  As.mapM (Instances.frame c env.ownerTps).elabV

/-- Two lists of type arguments are one instance's: equal as types, or, when they are not types of
the frame, as written.  `[spec §38]` -/
def Env.sameArgs (env : Env) (a b : List VTy) : Bool :=
  a.length == b.length && match env.keyOf a, env.keyOf b with
    | some x, some y => x == y
    | _, _ => a.map VTy.strip == b.map VTy.strip

/-- An instance as the messages write it. -/
def instText (e : String) (As : List VTy) : String :=
  if As.isEmpty then s!"`{e}`" else s!"`{e}[{", ".intercalate (As.map (VTy.pp · 0))}]`"

/-- An instance of `e` added to a row: one entry per instance (an effect at its type arguments,
with its name). An instance whose type arguments are not known is an entry of its own until the
function's row is settled (`Env.settle`, `Env.slotOf`).  `[spec §38]` -/
def Env.addInst (env : Env) (r : List Inst) (i : Inst) : List Inst :=
  let same (j : Inst) : Bool := j.eff == i.eff && j.name == i.name && match j.args, i.args with
    | some a, some b => env.sameArgs a b
    | none, none => true
    | _, _ => false
  if r.any same then r else r ++ [i]

/-- A function's inferred row with no written row, settled (SPEC §38): an instance whose type
arguments are not known is the one entry of its effect (and name) whose are, at the place of the
earlier of the two; with none, they are not determined; with two, it is ambiguous. -/
def Env.settle (sp : Span) (f : String) (r : List Inst) : Except Error (List Inst) := do
  let mut out := r
  for u in r do
    if u.args.isSome then continue
    let ds := out.filter fun d => d.eff == u.eff && d.name == u.name && d.args.isSome
    match ds with
    | [d] =>
      let iu := out.idxOf u
      let id := out.idxOf d
      out := if iu < id then (out.erase d).set iu d else out.erase u
    | [] => throw ⟨sp, s!"`{f}` performs `{u.eff}`, and its type arguments are not determined: " ++
        s!"write them, `with {u.eff}[…]`"⟩
    | ds => throw ⟨sp, s!"`{f}` performs `{u.eff}` at type arguments not known here, and " ++
        s!"{", ".intercalate (ds.map fun d => instText d.eff (d.args.getD []))} too: ascribe its " ++
        "argument (`(e : T)`), write its row, or perform it at a named handler (SPEC §38)"⟩
  pure out

def Env.union (env : Env) (a b : List Inst) : List Inst := b.foldl env.addInst a

/-- The effect `e` taken off a row, every instance of it. -/
def without (r : List Inst) (e : String) : List Inst := r.filter (·.eff != e)

/-- A handler of the instance `e[args]` named `nm` handles the entry `j`: its effect, at its type
arguments (any, when either is not known), unnamed or named `nm`.  `[spec §38]` -/
def Env.handles (env : Env) (e : String) (args : Option (List VTy)) (nm : Option String) (j : Inst) :
    Bool :=
  j.eff == e && (j.name.isNone || j.name == nm) && match args, j.args with
    | some a, some b => env.sameArgs a b
    | _, _ => true

/-- A row less what a handler of `e[args]` named `nm` handles. -/
def Env.withoutInst (env : Env) (r : List Inst) (e : String) (args : Option (List VTy))
    (nm : Option String) : List Inst :=
  r.filter (!env.handles e args nm ·)

/-- The provided instances `es` (a computation parameter's, SPEC §33) taken off a row: an entry
of a provided effect at its type arguments, or whose type arguments are not known.
`[spec §38]` -/
def Env.withoutAll (env : Env) (r : List Inst) (es : List (Ident × List VTy)) : List Inst :=
  r.filter fun i => !es.any fun (e, As) => e.name == i.eff && i.args.all (env.sameArgs As)

/-- What a call of `g` performs: its row, and for a member of a recursive group the rows of the
layers in scope (`inLayers`). -/
def Env.callRow (env : Env) (g : FSig) : List Inst :=
  if g.group.isNone then g.row
  else env.inLayers.foldl (fun r L => env.union r (((env.fn? L).map (·.row)).getD [])) g.row

/-- The type arguments recorded at the call at `sp` of the code being elaborated
(`Instances.table`).  `[spec §38]` -/
def Env.recorded (env : Env) (sp : Span) : Option (List VTy) :=
  env.table[Instances.key env.owner sp]?

/-- What the call at `sp` of `g` performs: `g`'s row at the call's type arguments, a slot that
mentions `g`'s type parameters undetermined when they are not known. Each slot stays an entry of
its own.  `[spec §38]` -/
def Env.callRowAt (env : Env) (sp : Span) (g : FSig) : List Inst :=
  let row := env.callRow g
  match g.decl with
  | .def_ _ _ ps@(_ :: _) _ _ _ =>
    let tps := ps.map (·.name)
    let σ? : Option TySubst := (env.recorded sp).map (tps.zip ·)
    row.map fun i => match i.args with
      | some As =>
        if As.any (mentions tps) then { i with args := σ?.map fun σ => As.map (·.subst σ) } else i
      | none => i
  | _ => row

/-- The instance an operation call of `o` at `sp` performs (at the handler named `nm`): its
effect's type arguments, `[]` when it takes none, else those recorded at the call.
`[spec §38]` -/
def Env.opInst (env : Env) (o : OpSig) (sp : Span) (nm : Option String := none) : Inst :=
  ⟨o.eff, match env.eff? o.eff with
    | some e => if e.tps.isEmpty then some [] else env.recorded sp
    | none => none, nm⟩

/-- The instances a control handler's own row adds at a `with`: determined when its patterns
mention none of the handler's type parameters. -/
def handlerRow (h : CHandler) : List Inst :=
  let tps := h.tps.map (·.name)
  h.row.map fun (e, As) => ⟨e.name, if As.any (mentions tps) then none else some As, none⟩

/-- The type arguments of the effect a control handler `ch` handles at `with ch[As] { M }`, `inner`
being what `M` performs: those the written arguments give; else those of the instance of the
effect that `M` performs (unnamed, or named `nm`), when it performs one. `none` when they are not
determined, or `M` performs two (`withCtl` asks for them).  `[spec §38]` -/
def Env.handledArgs (env : Env) (ch : CHandler) (As : List VTy) (nm : Option String)
    (inner : List Inst) : Option (List VTy) := do
  let tps := ch.tps.map (·.name)
  let σ : TySubst := tps.zip As
  let effArgs := ch.effArgs.map (·.subst σ)
  if ch.effArgs.all (solvedBy tps σ) then return effArgs
  let mine := inner.filter fun j => j.eff == ch.eff.name && (j.name.isNone || j.name == nm)
  let Bs ← (mine.filterMap (·.args)).head?
  guard (mine.all fun j => j.args.all (env.sameArgs Bs))
  guard (Bs.length == ch.effArgs.length)
  let σ' ← (ch.effArgs.zip Bs).foldlM (fun σ (Pt, B) => matchTy tps σ Pt B) σ
  let effArgs := ch.effArgs.map (·.subst σ')
  if ch.effArgs.all (solvedBy tps σ') then some effArgs else none

/-- A call of a function that performs an iteration effect (SPEC §15): the callee's name, its
signature, the instance of the iteration effect, and the callee and argument as written. -/
def Env.iterCall? (env : Env) : Val → Option (String × FSig × Inst × Val × Val)
  | .app _ f W => do
    let x ← headName f
    let g ← env.fn? x
    let i ← g.row.find? (env.iterEff ·.eff)
    pure (x, g, i, f, W)
  | _ => none

/-- The components of a call's argument tuple against the parameter tuple type `P` as written:
each with its parameter's type. -/
def argComps : Nat → VTy → Val → List (VTy × Val)
  | k + 1, .tensor _ A B, .pair _ V W => (A, V) :: argComps k B W
  | _, P, W => [(P, W)]

/-- The names of a function's parameters, in order, read off its body `body` as the parser binds
them from the parameter tuple `p`: `let (x, io_pN) = p; let (y, z) = io_pN; …`, or none; a `p`
the parser did not generate is the one parameter itself (`Parser.paramVar`). -/
def paramNamesIn (p : String) (body : Comp) : List String :=
  if !p.startsWith "io_p" then [p] else go fuel p body
where
  go : Nat → String → Comp → List String
    | 0, _, _ => []
    | k + 1, p, M => match M with
      | .letPair _ x y (.var _ q) N =>
        if q != p then [] else
        match N with
        | .letPair _ _ _ (.var _ r) _ =>
          if r == y.name && y.name.startsWith "io_p" then x.name :: go k y.name N
          else [x.name, y.name]
        | _ => [x.name, y.name]
      | .bind _ x none (.ret _ (.var _ q)) _ => if q == p then [x.name] else []
      | _ => []

/-- The names of a function's parameters (`paramNamesIn`). -/
def paramNames (f : FnParts) : List String := paramNamesIn f.p.name f.body

mutual
/-- The effects a value performs, outside the `with`s that handle them. A call of a function
performing an iteration effect, as an argument at a stored generator's parameter, is the stored
generator: it does not perform the iteration effect. -/
def rowV (env : Env) : Nat → Val → List Inst
  | 0, _ => []
  | n + 1, V => match V with
    | .app _ (.app _ (.sugar _ (.handle h _ As nm)) P) (.thunkv _ (.lam _ _ _ M)) =>
      let inner := rowC env n M
      let inner := match env.handler? h, env.chandler? h with
        | some hs, _ => env.withoutInst inner hs.eff (some []) nm
        | none, some ch =>
          -- The clauses run in the scope of the `with`: the answering effects they perform are
          -- its own, as its row's control effects are (SPEC §39).
          let cl := ch.clauses.foldl (fun r c => env.union r (rowC env n c.body)) (rowC env n ch.ret.2.2)
          env.union (env.union (env.withoutInst inner ch.eff.name (env.handledArgs ch As nm inner) nm)
            (handlerRow ch)) (cl.filter (env.answering ·.eff))
        | none, none =>
          if env.driver? h then match env.exhEff? with
            | some e => without inner e.name
            | none => inner
          else if (env.layer? h).isSome then env.union inner ((env.fn? h).map (·.row) |>.getD [])
          else inner
      env.union (rowV env n P) inner
    -- `x.op(W)`: the operation at the handler named `x` (SPEC §38).
    | .app sp (.sugar _ (.named x op)) W =>
      env.union ((env.op? op).toList.map (env.opInst · sp (some x))) (rowV env n W)
    | .app sp f W =>
      let head := match headName f with
        | some x => match env.op? x, env.fn? x with
          | some o, _ => [env.opInst o sp]
          | none, some g => env.callRowAt sp g
          | none, none => rowV env n f
        | none => rowV env n f
      -- An argument at a computation parameter performs what the callee provides there in the
      -- callee (SPEC §33): the callee's row has it when the callee passes it on.
      let args := match headName f with
        | some x =>
          let cps := (env.comps.lookup x).getD []
          (env.pullArgs x W).zipIdx.foldl (fun r ((V, pull), j) =>
            let rV := pullRow env n pull V
            env.union r (match cps.find? (·.1 == j) with
              | some (_, _, es) => env.withoutAll rV es
              | none => rV)) []
        | none => rowV env n W
      env.union head args
    | .var _ x => match env.fn? x with
      | some g => env.callRow g
      | none => (env.cbRows.lookup x).getD []
    | .pair _ V W => env.union (rowV env n V) (rowV env n W)
    | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
    | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V | .mark _ _ V => rowV env n V
    | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => rowC env n M
    | _ => []

/-- The effects a computation performs, outside the `with`s that handle them. -/
def rowC (env : Env) : Nat → Comp → List Inst
  | 0, _ => []
  | n + 1, M => match M with
    | .ret _ V | .absurd _ V => rowV env n V
    -- A copy of a block parameter is the block parameter (`Cx.copy`).
    | .bind _ x A (.ret _ V) N =>
      match V.copyOf?.bind fun y => List.lookup y env.cbRows with
      | some r => rowC { env with cbRows := (x.name, r) :: env.cbRows } n N
      | none => match A with
        | some A => env.union (pullRow env n (isPullTy A) V) (rowC env n N)
        | none => env.union (rowV env n V) (rowC env n N)
    | .bind _ _ _ M N | .with_ _ M N => env.union (rowC env n M) (rowC env n N)
    | .letUnit _ V M | .letPair _ _ _ V M => env.union (rowV env n V) (rowC env n M)
    | .case _ V _ M _ N =>
      env.union (rowV env n V) (env.union (rowC env n M) (rowC env n N))
    | .loop _ _ src V M N =>
      -- A `for` over a call that performs an iteration effect handles it.
      let src := match src, env.iterCall? V with
        | .each _, some (_, _, i, _, _) => without (rowV env n V) i.eff
        | _, _ => rowV env n V
      env.union src (env.union (rowC env n M) (rowC env n N))
    | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
    | .nuOut _ M | .ascribe _ M _ => rowC env n M
    | _ => []

/-- The effects of a value at a position of type `pull` (`pull`): a call performing an iteration
effect there is its stored generator, which handles it. -/
def pullRow (env : Env) : Nat → Bool → Val → List Inst
  | 0, _, _ => []
  | n + 1, pull, V => match pull, env.iterCall? V with
    | true, some (_, _, i, _, _) => without (rowV env n V) i.eff
    | _, _ => rowV env n V
end

/-! ### Building terms -/

def _root_.Frontend.Life.vars : Life → List String
  | .var _ x => [x]
  | .meet _ a b | .join _ a b => a.vars ++ b.vars
  | _ => []

mutual
/-- The lifetime variables a type mentions. -/
def _root_.Frontend.VTy.lifeVars : VTy → List String
  | .tensor _ A B | .sum _ A B | .lolli _ A B => A.lifeVars ++ B.lifeVars
  | .thunk _ C => C.lifeVars
  | .ref _ A | .bang _ A | .mu _ _ A | .array _ A => A.lifeVars
  | .imm _ a A | .mut _ a A | .box _ a A | .view _ a A | .arrayImm _ a A | .arrayMut _ a A =>
    a.vars ++ A.lifeVars
  | .all _ _ b A => b.vars ++ A.lifeVars
  | .sized _ D S A => D.lifeVars ++ S.lifeVars ++ A.lifeVars
  | .fam _ _ a _ => a.vars
  | .app _ G A => G.lifeVars ++ A.lifeVars
  | .lapp _ G a => G.lifeVars ++ a.vars
  | _ => []

def _root_.Frontend.CTy.lifeVars : CTy → List String
  | .ret _ A | .delay _ A | .stream _ A => A.lifeVars
  | .arr _ A C => A.lifeVars ++ C.lifeVars
  | .amp _ C D => C.lifeVars ++ D.lifeVars
  | .all _ _ b C => b.vars ++ C.lifeVars
  | .nu _ _ C => C.lifeVars
  | .iter _ A R R' | .pull _ A R R' => A.lifeVars ++ R.lifeVars ++ R'.lifeVars
  | .loop _ A B => A.lifeVars ++ B.lifeVars
  | .eff _ _ A => A.lifeVars
  | _ => []
end

/-- The right-nested sum of the types `As`: `A₁ + (A₂ + (… + Aₙ))`, `A₁` alone. -/
def sumTys (sp : Span) : List VTy → VTy
  | [] => .zero sp
  | [A] => A
  | A :: As => .sum sp A (sumTys sp As)

/-- `V` at the summand `j` of a right-nested sum of `n` summands (`sumTys`). -/
def injAt (sp : Span) : Nat → Nat → Val → Val
  | _, 0, V | _, 1, V => V
  | 0, _, V => .inl sp V
  | j + 1, n + 1, V => .inr sp (injAt sp j n V)

/-- The right-nested record of the computation types `Cs`: `C₁ & (C₂ & (… & Cₙ))`, `C₁` alone. -/
def ampTys (sp : Span) : List CTy → CTy
  | [] => .top sp
  | [C] => C
  | C :: Cs => .amp sp C (ampTys sp Cs)

/-- The right-nested record of the computations `Ms` (`ampTys`). -/
def withAll (sp : Span) : List Comp → Comp
  | [] => .top sp
  | [M] => M
  | M :: Ms => .with_ sp M (withAll sp Ms)

/-- The field `j` of `M`, a right-nested record of `n` fields (`ampTys`). -/
def projAt (sp : Span) : Nat → Nat → Comp → Comp
  | _, 0, M | _, 1, M => M
  | 0, _, M => .proj sp true M
  | j + 1, n + 1, M => projAt sp j n (.proj sp false M)

/-- The tuple of the variables `xs`: `()` when there are none. -/
def paramsTuple (sp : Span) : List String → Val
  | [] => .unit sp
  | [x] => .var sp x
  | x :: xs => .pair sp (.var sp x) (paramsTuple sp xs)

/-- `(c₁, (…, (cₙ, V)))`. -/
def capsTuple (sp : Span) (cs : List Cap) (V : Val) : Val :=
  cs.foldr (fun c W => .pair sp (.var sp c.var) W) V

/-- `mut 'l₁ S₁ * (… * A)`. -/
def capsTy (sp : Span) (cs : List Cap) (A : VTy) : VTy :=
  cs.foldr (fun c B => .tensor sp (c.ty sp) B) A

/-- `let (c₁, r₁) = t; …; let (cₙ, x) = rₙ₋₁; N`: the capabilities bound again from `t`, and
`x` to the rest. -/
def unpack (sp : Span) : List Cap → String → String → Comp → EM Comp
  | [], x, t, N => pure (.bind sp ⟨x, sp⟩ none (.ret sp (.var sp t)) N)
  | [c], x, t, N => pure (.letPair sp ⟨c.var, sp⟩ ⟨x, sp⟩ (.var sp t) N)
  | c :: cs, x, t, N => do
    let r ← fresh "fx_r"
    pure (.letPair sp ⟨c.var, sp⟩ ⟨r, sp⟩ (.var sp t) (← unpack sp cs x r N))

/-- `t <- M; K`, with the bindings `M` begins with moved before it (they bind fresh names, or
capabilities that `K` binds again), so that the head of the binding is one statement. -/
def bindFlat (sp : Span) (t : String) (A : Option VTy) : Comp → Comp → Comp
  | .bind sp' a B M N, K => .bind sp' a B M (bindFlat sp t A N K)
  | .letPair sp' x y V M, K => .letPair sp' x y V (bindFlat sp t A M K)
  | .letUnit sp' V M, K => .letUnit sp' V (bindFlat sp t A M K)
  | M, K => .bind sp ⟨t, sp⟩ A M K

/-- A terminal that leaves a loop: `break`, `break e`, `continue`, or `return e` from a loop's
body. -/
def isExit : Val → Bool
  | .sugar _ .brk | .app _ (.sugar _ .brk) _ | .app _ (.sugar _ .retE) _ | .sugar _ .cont => true
  | _ => false

/-- A binding put before a value: the computation that follows it is its argument. A call's
binding says what it binds, so that the value it is the whole of takes the call's place
(`trRet`, `trBind`). -/
inductive Bind where
  /-- `x <- M; N` (`bindFlat` when `flat`): the call's answer is `x`. -/
  | one (sp : Span) (x : String) (A : Option VTy) (M : Comp) (flat : Bool)
  /-- `t <- M; let (c₁, …, x) = t; N` (`bindFlat` when `flat`): the call hands back the
  capabilities `cs` first, then its answer `x`; `post` comes before `N`. -/
  | caps (sp : Span) (t : String) (A : Option VTy) (M : Comp) (cs : List Cap) (x : String)
      (flat : Bool) (post : Comp → Comp)
  /-- Any other binding. -/
  | k (f : Comp → EM Comp)

/-- `x <- M; N`, flattened (`bindFlat`) when `flat`. -/
def Bind.bindAt (sp : Span) (x : String) (A : Option VTy) (M N : Comp) (flat : Bool) : Comp :=
  if flat then bindFlat sp x A M N else .bind sp ⟨x, sp⟩ A M N

def Bind.run : Bind → Comp → EM Comp
  | .one sp x A M flat, N => pure (Bind.bindAt sp x A M N flat)
  | .caps sp t A M cs x flat post, N => do
    pure (Bind.bindAt sp t A M (← unpack sp cs x t (post N)) flat)
  | .k f, N => f N

def chain : List Bind → Comp → EM Comp
  | [], M => pure M
  | b :: bs, M => do b.run (← chain bs M)

/-- A computation may loop: it has a `while` or `loop`, or a `for` whose source is not a count
`a..b` (a loop over a view is total too, but its source's type is not known here). -/
def mayLoop : Nat → Comp → Bool
  | 0, _ => true
  | k + 1, M => match M with
    | .loop _ _ (.each _) (.app _ (.sugar _ .count) _) B N => mayLoop k B || mayLoop k N
    | .loop .. => true
    | .bind _ _ _ M N | .with_ _ M N => mayLoop k M || mayLoop k N
    | .letUnit _ _ M | .letPair _ _ _ _ M | .lam _ _ _ M | .lamL _ _ _ M => mayLoop k M
    | .case _ _ _ M _ N => mayLoop k M || mayLoop k N
    | _ => false

/-- `w <- perform[n.i] (V, w)`: an operation at a `for`'s site, which threads `w`. -/
def threadedPerform (sp : Span) (n i : Nat) (V : Val) (w : String) : Bind := .k fun N =>
  pure (.bind sp ⟨w, sp⟩ none (.perform sp n i (.pair sp V (.var sp w))) N)

/-- The plain calls of a value, bound first in the order its evaluation runs them in (leftmost
first), so that an effectful call lifted out of it keeps its place among them. A call is bound
whole, its arguments' calls in it: its evaluation runs them first, and the typed elaboration then
types each where the call's parameter gives it the type it expects (`nil()` in `cons(7, nil())`).
A sugar form (an operator, `*e`, a borrow block) is not a call and stays where it is.
`[spec §31]` -/
def liftCalls : Nat → Val → StateT (List Bind) EM Val
  | 0, V => pure V
  | n + 1, V => match V with
    | .app sp f W => do
      match f with
      | .sugar .. | .app _ (.sugar ..) _ =>
        pure (.app sp f (← liftCalls n W))
      | _ =>
        let x ← (fresh "fx_n" : EM String)
        modify (· ++ [.one sp x none (.ret sp (.app sp f W)) false])
        pure (.var sp x)
    | .pair sp V W => do pure (.pair sp (← liftCalls n V) (← liftCalls n W))
    | .inl sp V => do pure (.inl sp (← liftCalls n V))
    | .inr sp V => do pure (.inr sp (← liftCalls n V))
    | .ascribe sp V A => do pure (.ascribe sp (← liftCalls n V) A)
    | .roll sp V => do pure (.roll sp (← liftCalls n V))
    | .unroll sp V => do pure (.unroll sp (← liftCalls n V))
    | .boxed sp l V => do pure (.boxed sp l (← liftCalls n V))
    | .unbox sp V => do pure (.unbox sp (← liftCalls n V))
    | V => pure V

mutual
/-- The names a value refers to, as variables or `def`s applied. -/
def refsV : Nat → Val → List String
  | 0, _ => []
  | n + 1, V => match V with
    | .var _ x | .defApp _ x _ => [x]
    | .pair _ V W | .app _ V W => refsV n V ++ refsV n W
    | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
    | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V | .mark _ _ V => refsV n V
    | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => refsC n M
    | _ => []

/-- The names a computation refers to. -/
def refsC : Nat → Comp → List String
  | 0, _ => []
  | n + 1, M => match M with
    | .ret _ V | .absurd _ V | .perform _ _ _ V | .abort _ _ _ V => refsV n V
    | .bind _ _ _ M N | .with_ _ M N => refsC n M ++ refsC n N
    | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
    | .nuOut _ M | .ascribe _ M _ => refsC n M
    | .handle _ _ _ hr hc M => refsV n hr ++ refsV n hc ++ refsC n M
    | .letUnit _ V M | .letPair _ _ _ V M => refsV n V ++ refsC n M
    | .case _ V _ M _ N | .loop _ _ _ V M N => refsV n V ++ refsC n M ++ refsC n N
    | .unwind _ _ _ M D N => refsC n M ++ refsC n D ++ refsC n N
    | .withbor2r _ _ _ _ _ _ _ _ M => refsC n M
    | .force .. | .top _ => []
end

mutual
/-- The value takes `k` out of a box, `unbox k`, outside nothing. -/
def unboxesV (k : String) : Nat → Val → Bool
  | 0, _ => false
  | n + 1, V => match V with
    | .unbox _ (.var _ x) => x == k
    | .pair _ V W | .app _ V W => unboxesV k n V || unboxesV k n W
    | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
    | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V | .mark _ _ V => unboxesV k n V
    | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => unboxesC k n M
    | _ => false

/-- The computation takes `k` out of a box (`unboxesV`). -/
def unboxesC (k : String) : Nat → Comp → Bool
  | 0, _ => false
  | n + 1, M => match M with
    | .ret _ V | .absurd _ V | .perform _ _ _ V | .abort _ _ _ V => unboxesV k n V
    -- A copy of the continuation is the continuation (`Cx.copy`).
    | .bind _ x _ (.ret _ V@(.var ..)) N | .bind _ x _ (.ret _ V@(.clone ..)) N
    | .bind _ x _ (.ret _ V@(.ascribe ..)) N =>
      if V.copyOf? == some k then unboxesC x.name n N else unboxesV k n V || unboxesC k n N
    | .bind _ _ _ M N | .with_ _ M N => unboxesC k n M || unboxesC k n N
    | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
    | .nuOut _ M | .ascribe _ M _ => unboxesC k n M
    | .handle _ _ _ hr hc M => unboxesV k n hr || unboxesV k n hc || unboxesC k n M
    | .letUnit _ V M | .letPair _ _ _ V M => unboxesV k n V || unboxesC k n M
    | .case _ V _ M _ N | .loop _ _ _ V M N => unboxesV k n V || unboxesC k n M || unboxesC k n N
    | .unwind _ _ _ M D N => unboxesC k n M || unboxesC k n D || unboxesC k n N
    | .withbor2r _ _ _ _ _ _ _ _ M => unboxesC k n M
    | .force .. | .top _ => false
end

/-! ### Elaborating a body -/

/-- In a layer's body made for a member of a group (SPEC §20): the name of its `call` parameter,
the variable holding the function of the self-reference, and the member's field. -/
structure LCall where
  name : String
  g : String
  j : Nat
  rs : RSelf

/-- In a clause of a control handler's operation that resumes (SPEC §19): its continuation `k`,
which `k(v)` resumes. A handler with a state (`stateful`) answers a function of its state: the
state is its parameters `params` and the capabilities its clauses use (`Cx.caps`), passed to the
continuation's answer at a resume; the capabilities come back beside the answer. -/
structure ResumeK where
  k : String
  params : List String
  stateful : Bool

/-- The context of an elaboration: what is declared, the capabilities and handler sites in scope,
and, in a function's copy, the capabilities its `return e` from inside a loop hands back. -/
structure Cx where
  env : Env
  caps : List Cap
  sites : List Site := []
  fnCaps : List Cap := []
  /-- In the generator of a recursive group (SPEC §20): its members, its environment, the site
  of the exhaustion effect, and the variable holding the self-reference. -/
  recSelf : Option RSelf := none
  /-- Inside `with d { … }` of a heap driver `d` (SPEC §20): the recursive groups called are driven
  by it. -/
  driver : Option String := none
  /-- In a layer's body made for a member: its `call`, the member's call through the
  self-reference. -/
  layerCall : Option LCall := none
  /-- In a clause of an operation that resumes: its continuation. -/
  resume : Option ResumeK := none
  /-- In a copy made for effectful blocks (SPEC §30): each block parameter, the sites its
  block's control operations were resolved to where the block was written, and the capabilities
  it uses, passed with it at each call (SPEC §32). -/
  cbs : List (String × List Site × List Cap) := []
  /-- In a copy made for computation parameters (SPEC §33): each parameter's port for each effect
  it provides, the site its argument performs that effect at, and whether the site is a `with`
  of the copy (named by the port) rather than one of the copy's row.  `[spec §33]` -/
  ports : List (String × Site × Bool) := []

/-- `x <- return y`, a copy: when `y` is a name the elaboration gives a meaning of its own (a
block parameter, a computation parameter's port, a clause's continuation, a layer's `call`), the
context in which `x` is that thing in `y`'s place. A thing is identified by its binder, followed
through its copies, never by its name (SPEC §41, #617). -/
def Cx.copy (cx : Cx) (x y : String) : Option Cx :=
  let cbs := (cx.cbs.lookup y).map fun e => (x, e) :: cx.cbs
  let ports := cx.ports.filterMap fun (z, p, own) => if z == y then some (x, p, own) else none
  let resume := cx.resume.bind fun rk => if rk.k == y then some { rk with k := x } else none
  let layer := cx.layerCall.bind fun lc => if lc.name == y then some { lc with name := x } else none
  if cbs.isNone && resume.isNone && layer.isNone then none else
  some { cx with
    cbs := cbs.getD cx.cbs
    ports := ports ++ cx.ports
    resume := resume.orElse fun _ => cx.resume
    layerCall := layer.orElse fun _ => cx.layerCall
    env := match cx.env.cbRows.lookup y with
      | some r => { cx.env with cbRows := (x, r) :: cx.env.cbRows }
      | none => cx.env }

/-- What a call of `g` performs here: its row, and for a member of a recursive group the rows of
the layers its recursion runs under. -/
def Cx.rowOf (cx : Cx) (g : FSig) : List Inst := cx.env.callRow g

/-- What the call of `g` at `sp` performs here (`Env.callRowAt`). -/
def Cx.rowAt (cx : Cx) (sp : Span) (g : FSig) : List Inst := cx.env.callRowAt sp g

/-- The capability serving the answering instance `i`: the handler named as it is, when it is
named; else the innermost handler of its effect. Of a copy's slots, which are unordered, the one
slot of the effect, or the one unnamed slot (`Cx.capAt` reports two).  `[spec §38]` -/
def Cx.capFor (cx : Cx) (i : Inst) : Option Cap :=
  let cands := cx.caps.filter (·.eff == i.eff)
  match i.name with
  | some x => cands.find? (·.name == some x)
  | none => match cands with
    | c :: _ =>
      if !c.slot then some c else
      match cands.filter (·.slot) with
      | [d] => some d
      | ds => match ds.filter (·.name.isNone) with
        | [d] => some d
        | _ => some c
    | [] => none

/-- The capabilities of `cx` for the effects `row`, in the order of `cx.caps`: each the
capability an instance of `row` is served by, and a block's of its effect. -/
def Cx.need (cx : Cx) (row : List Inst) : List Cap :=
  cx.caps.filter fun c => row.any fun i => i.eff == c.eff && (c.blk || match cx.capFor i with
    | some d => d.var == c.var
    | none => true)

/-- The capabilities of `cx` for the effects `row`, in the order of `row`: those a copy for them
takes first. -/
def Cx.needIn (cx : Cx) (row : List Inst) : List Cap :=
  (row.filterMap cx.capFor).foldl (fun acc c => if acc.any (·.var == c.var) then acc else acc ++ [c]) []

def Cx.needV (cx : Cx) (V : Val) : List Cap := cx.need (rowV cx.env fuel V)
def Cx.needC (cx : Cx) (M : Comp) : List Cap := cx.need (rowC cx.env fuel M)

/-- `V` calls a layer's `call` (SPEC §20), or resumes a clause's continuation (SPEC §19). -/
def Cx.lcallV (cx : Cx) (V : Val) : Bool :=
  (match cx.layerCall with
    | some lc => (refsV fuel V).contains lc.name
    | none => false) ||
  (match cx.resume with
    | some rk => (refsV fuel V).contains rk.k
    | none => false)

/-- The control effects of `row`. -/
def Cx.ctl (cx : Cx) (row : List Inst) : List Inst := row.filter (!cx.env.answering ·.eff)

def Cx.ctlV (cx : Cx) (V : Val) : Bool := !(cx.ctl (rowV cx.env fuel V)).isEmpty
def Cx.ctlC (cx : Cx) (M : Comp) : Bool := !(cx.ctl (rowC cx.env fuel M)).isEmpty

/-- A control handler whose clauses keep its continuation boxed at its lifetime parameter (a
task of `spawn_in`): the body it handles outlives the `with`, so it is given the capabilities it
uses (SPEC §34). -/
def Env.gives (env : Env) (h : String) : Bool :=
  match env.chandler? h, env.eff? (((env.chandler? h).map (·.eff.name)).getD "") with
  | some ch, some eff => !ch.lps.isEmpty && eff.ops.any fun o => !o.abortive && ch.clauses.any fun c =>
      c.name.name == o.name.name && !c.params.isEmpty && unboxesC c.params.getLast!.name fuel c.body
  | _, _ => false

mutual
/-- The capabilities the tasks spawned in a value are given (`Env.gives`), outside nested borrow
blocks and closures: the innermost borrow block around a spawn lends them for its tasks. -/
def Cx.givenV (cx : Cx) : Nat → Val → List Cap
  | 0, _ => []
  | n + 1, V => match V with
    | .app _ (.app _ (.sugar _ (.handle h _ _ _)) P) (.thunkv _ (.lam _ _ _ M)) =>
      if cx.env.gives h then cx.needC M else cx.givenV n P ++ cx.givenC n M
    | .app _ (.app _ (.sugar _ (.borrow ..)) _) _ => []
    | .app _ f W | .pair _ f W => cx.givenV n f ++ cx.givenV n W
    | .inl _ V | .inr _ V | .ascribe _ V _ | .roll _ V | .unroll _ V | .boxed _ _ V
    | .unbox _ V | .unbang _ V | .inst _ V _ | .sub _ V _ | .shorten _ _ _ _ V | .mark _ _ V => cx.givenV n V
    | .run _ M => cx.givenC n M
    | _ => []
/-- `Cx.givenV` of a computation. -/
def Cx.givenC (cx : Cx) : Nat → Comp → List Cap
  | 0, _ => []
  | n + 1, M => match M with
    | .ret _ V | .absurd _ V => cx.givenV n V
    | .bind _ _ _ M N | .with_ _ M N => cx.givenC n M ++ cx.givenC n N
    | .letUnit _ V M | .letPair _ _ _ V M => cx.givenV n V ++ cx.givenC n M
    | .case _ V _ M _ N => cx.givenV n V ++ cx.givenC n M ++ cx.givenC n N
    | .loop _ _ _ V M N => cx.givenV n V ++ cx.givenC n M ++ cx.givenC n N
    | _ => []
end

/-- The capability of the effect `e` in scope. -/
def Cx.capOf (cx : Cx) (e : String) : Option Cap := cx.caps.find? (·.eff == e)

/-- The site of the control effect `e` in scope. -/
def Cx.siteOf (cx : Cx) (e : String) : Option Site := cx.sites.find? (·.eff == e)

def notInClosure (sp : Span) (e : String) : Error :=
  ⟨sp, s!"an operation of `{e}` is performed inside a closure or block that is not run in place: " ++
    "it cannot reach its handler (effectful callbacks, #161)"⟩

/-- The site serving the control instance `i` here (SPEC §38): the handler named as it is, when
it is named; else the innermost handler of its instance. When its type arguments are not known
here, or no handler in scope has them, the innermost handler of its effect, if all of those in
scope are one instance; with `strict`, its type arguments are checked against the handler's. A
copy's slots are unordered: of two that could serve it, the one that is not named, else it is
ambiguous. -/
def Cx.serve (cx : Cx) (sp : Span) (what : String) (i : Inst) (strict : Bool := true) :
    Except Error Site := do
  let env := cx.env
  let cands := cx.sites.filter (·.eff == i.eff)
  let some s₀ := cands.head?
    | throw ⟨sp, s!"{what} performs `{i.eff}`, but no handler of `{i.eff}` is in scope here"⟩
  let check (s : Site) : Except Error Unit := do
    if let some As := i.args then
      unless env.sameArgs As s.at do
        throw ⟨sp, s!"{what} performs {instText i.eff As}, but the handler of `{i.eff}` in scope " ++
          s!"is at {instText i.eff s.args}"⟩
  let pick (ss : List Site) : Except Error Site := do
    let some s := ss.head? | throw ⟨sp, "internal error: no site"⟩
    if s.slot.isNone then return s
    match ss.filter (·.slot.isSome) with
    | [t] => pure t
    | ts => match ts.filter (·.name.isNone) with
      | [t] => pure t
      | _ => throw ⟨sp, s!"{what} performs {instText i.eff s.at}, which two entries of the row " ++
          s!"could serve ({", ".intercalate (ts.map fun t => (t.name.map (s!"`{·}`")).getD "unnamed")}): " ++
          "perform it at a named one (`n.op(…)`, SPEC §38)"⟩
  if let some x := i.name then
    let some s := cands.find? (·.name == some x)
      | throw ⟨sp, s!"{what} performs `{i.eff}` at the handler named `{x}`, but no handler of " ++
          s!"`{i.eff}` named `{x}` is in scope here"⟩
    check s
    return s
  let ofInst := match i.args with
    | some As => cands.filter fun s => env.sameArgs As s.at
    | none => []
  if !ofInst.isEmpty then return ← pick ofInst
  if cands.all fun s => env.sameArgs s.at s₀.at then
    let s ← pick cands
    if strict then check s
    return s
  let shown := cands.foldl (fun acc s => if acc.any (env.sameArgs s.at ·) then acc else acc ++ [s.at]) []
  let inScope := ", ".intercalate (shown.map (instText i.eff))
  match i.args with
  | some As => throw ⟨sp, s!"{what} performs {instText i.eff As}, and no handler of it is in scope " ++
      s!"here (handlers of {inScope} are)"⟩
  | none => throw ⟨sp, s!"{what} performs `{i.eff}` at type arguments not known here, and handlers " ++
      s!"of {inScope} are in scope: ascribe its argument (`(e : T)`), or perform it at a named " ++
      "handler (`n.op(…)`, SPEC §38)"⟩

/-- The capability serving the answering instance `i` here (`Cx.capFor`), or why there is none.
`[spec §38]` -/
def Cx.capAt (cx : Cx) (sp : Span) (what : String) (i : Inst) : Except Error Cap := do
  let cands := cx.caps.filter (·.eff == i.eff)
  if let some x := i.name then
    let some c := cands.find? (·.name == some x)
      | throw ⟨sp, s!"{what} performs `{i.eff}` at the handler named `{x}`, but no handler of " ++
          s!"`{i.eff}` named `{x}` is in scope here"⟩
    return c
  let some c := cx.capFor i
    | throw ⟨sp, s!"{what} performs `{i.eff}`, but no handler of `{i.eff}` is in scope here"⟩
  if c.slot then
    let ts := cands.filter (·.slot)
    if ts.length > 1 && (ts.filter (·.name.isNone)).length != 1 then
      throw ⟨sp, s!"{what} performs `{i.eff}`, which two entries of the row could serve: perform it " ++
        "at a named one (`n.op(…)`, SPEC §38)"⟩
  pure c

def fnParts (sp : Span) (name : String) (A : VTy) (V : Val) : Except Error FnParts := do
  let (bang, A, V) : Bool × VTy × Comp ← match A, V with
    | .bang _ A, .bangThunkv _ M => pure (true, A, M)
    | A, .thunkv _ M => pure (false, A, M)
    | _, _ => throw ⟨sp, s!"`{name}` performs an operation, and is not a function"⟩
  let rec go : Nat → VTy → Comp → Except Error (List (Ident × Life) × VTy × VTy × Ident × Comp)
    | 0, _, _ => throw ⟨sp, "internal error: a function nested too deeply"⟩
    | n + 1, .all _ _ b A, .lamL _ a _ (.ret _ (.thunkv _ M)) => do
      let (ls, r) ← go n A M
      pure ((a, b) :: ls, r)
    | _ + 1, .lolli _ P T, .lam _ p _ body => pure ([], P, T, p, body)
    | _ + 1, .thunk .., _ =>
      throw ⟨sp, s!"`{name}` performs an operation, and its result is a computation (a loop or a " ++
        "generator): not provided"⟩
    | _ + 1, _, _ => throw ⟨sp, s!"`{name}` performs an operation, and its form is not a function's"⟩
  let (lives, P, T, p, body) ← go fuel A V
  pure ⟨bang, lives, P, T, p, body⟩

/-- A function's result type, when it mentions none of its own lifetime parameters: the type of
a call's result, whatever the call's lifetimes. -/
def closedResult (g : Decl) : Option VTy :=
  match g with
  -- A template's result may mention its type parameters: its instance's is not known here.
  | .def_ _ _ (_ :: _) _ _ _ => none
  | .def_ sp n _ A V _ => match fnParts sp n.name A V with
    | .ok f => if f.T.lifeVars.any (f.lives.map (·.1.name)).contains then none else some f.T
    | .error _ => none
  | _ => none

/-- A function type and value put together from its parts; its result at the row `row` (`F[row]`)
when the row is not empty. -/
def FnParts.build (sp : Span) (f : FnParts) (row : Row := .nil) : VTy × Val :=
  let arrow : VTy := match row with
    | .nil => .lolli sp f.P f.T
    | row => .thunk sp (.arr sp f.P (.eff sp row f.T))
  let rec inner : List (Ident × Life) → VTy × Comp
    | [] => (arrow, .lam sp f.p f.P f.body)
    | (a, b) :: ls =>
      let (T, M) := inner ls
      (.all sp a b T, .lamL sp a b (.ret sp (.thunkv sp M)))
  let (T, M) := inner f.lives
  if f.bang then (.bang sp T, .bangThunkv sp M) else (T, .thunkv sp M)

/-! ### Effectful blocks  `[spec §30]` -/

/-- The component `j` of a right-nested tuple type of `n` components. -/
def compAt : Nat → VTy → Nat → Option VTy
  | 0, _, _ => none
  | 1, P, j => if j == 0 then some P else none
  | n + 1, .tensor _ A B, j => if j == 0 then some A else compAt n B (j - 1)
  | _, _, _ => none

/-- A right-nested tuple type of `n` components with the components `rs` (by index from `j`)
replaced. -/
def setComps : Nat → VTy → Nat → List (Nat × VTy) → VTy
  | 0, P, _, _ => P
  | 1, P, j, rs => (rs.lookup j).getD P
  | n + 1, .tensor sp A B, j, rs => .tensor sp ((rs.lookup j).getD A) (setComps n B (j + 1) rs)
  | _, P, _, _ => P

/-- A block parameter's written function type at the row `row`: `!(A => B)` is
`!U(A -o F[row] B)`, and `A => B` is `U(A -o F[row] B)`. -/
def rowedFnTy (row : Row) : VTy → Option VTy
  | .bang sp (.lolli lsp A B) => some (.bang sp (.thunk lsp (.arr lsp A (.eff lsp row B))))
  | .lolli sp A B => some (.thunk sp (.arr sp A (.eff sp row B)))
  | _ => none

/-- A block parameter's written function type at the row `row`, taking the capabilities `cs`
first and handing them back first: `!U(C * A -o F[row] (C * B))`.  `[spec §32]` -/
def rowedCapFnTy (row : Row) (cs : List Cap) : VTy → Option VTy
  | .bang sp (.lolli lsp A B) =>
    some (.bang sp (.thunk lsp (.arr lsp (capsTy lsp cs A) (.eff lsp row (capsTy lsp cs B)))))
  | .lolli sp A B => some (.thunk sp (.arr sp (capsTy sp cs A) (.eff sp row (capsTy sp cs B))))
  | _ => none

/-- The variable `w` of type `W` that a `for`'s site of the iteration effect `e` threads, as a
capability. -/
def threadCap (sp : Span) (e w W : String) : Cap :=
  ⟨e, w, "", ⟨"", e, ⟨"", sp⟩, .unit sp, [], sp, false, false⟩, some W, false, none, false⟩

/-- The capability of an enclosing `let mut` variable `x` that a block writes (SPEC §41, rule R3):
passed with the block at each call and handed back, as a `for`'s threaded variable is, its type a
parameter of the copy. -/
def mutCap (sp : Span) (x : String) : Cap := threadCap sp ("mut " ++ x) x ("IoMut_" ++ x)

/-- A capability of a `let mut` variable a block writes (`mutCap`). -/
def Cap.isMut (c : Cap) : Bool := c.eff.startsWith "mut "

/-- A closure marked with the enclosing `let mut` variables it writes (`VSugar.writes`), and the
closure. -/
def stripWrites : Val → List String × Val
  | .app _ (.sugar _ (.writes xs)) V => (xs, V)
  | V => ([], V)

/-- A closure that writes the enclosing `let mut` variable `x` and is not given at a block
parameter of a call (SPEC §41, rule R3). -/
def escapingWriter (sp : Span) (x : String) : Error :=
  ⟨sp, s!"this closure assigns `{x}`, a `let mut` variable of the body it is written in, and is " ++
    "not given at a block parameter of a call, which would pass it in and back out at each call: " ++
    "a closure that assigns is called where it is given (SPEC §41, rule R3)"⟩

/-- The sites `ss` and those of `extra` not among them, by static name. -/
def addSites (ss extra : List Site) : List Site :=
  extra.foldl (fun acc s => if acc.any (·.n == s.n) then acc else acc ++ [s]) ss

/-- An effectful block given at the parameter `j` of a call (SPEC §30): the sites its control
operations go to, and the capabilities it uses (an answering handler's state, or the variables a
`for`'s site threads), passed with it at each call and handed back (SPEC §32).  `[spec §32]` -/
structure Blk where
  j : Nat
  ss : List Site
  caps : List Cap := []
  /-- At a computation parameter (SPEC §33): the effects the callee provides. The block's
  operations of them go to the callee's port, not to the sites where it is written.
  `[spec §33]` -/
  prov : List (Ident × List VTy) := []
  /-- The control effects the block performs, in the order of its row, provided ones among them:
  its parameter's row lists their sites in this order, as the block's synthesized type does.
  `[spec §33]` -/
  order : List String := []

/-- A capability as a copy takes it: an answering handler's at the copy's own names, a `for`'s
threaded variable as it is.  `[spec §32]` -/
def Cap.canon (sp : Span) (c : Cap) : Cap := match c.thr with
  -- A `let mut` variable is the copy's own variable, named so that no local of the copy is it.
  | some W => if c.isMut then { threadCap sp c.eff ("fx_m_" ++ c.var) W with blk := true }
    else { threadCap sp c.eff c.var W with blk := true }
  | none => ⟨c.eff, capVar c.eff c.name, capLife c.eff c.name, c.h, none, true, c.name, false⟩


/-- The capabilities `cs` and those of `extra` for effects not among them. -/
def addCaps (cs extra : List Cap) : List Cap :=
  extra.foldl (fun acc c => if acc.any (·.eff == c.eff) then acc else acc ++ [c]) cs

/-- A block as a copy of the callee sees it: the type of a `for`'s threaded variable that it uses
is a type parameter of the copy, renamed (`W` to `Wb`) unless the copy's own row is served at that
`for`'s site (`own`), so that it is not the caller's parameter of the same name.  `[spec §32]` -/
def Blk.inCopy (own : List Site) (b : Blk) : Blk :=
  let isNew (s : Site) : Bool := !own.any (·.n == s.n)
  let renamed : List String := b.ss.filterMap fun s => if isNew s then s.thr.map (·.2) else none
  { b with
    ss := b.ss.map fun s => match s.thr with
      | some (w, W) => if isNew s then { s with thr := some (w, W ++ "b") } else s
      | none => s
    caps := b.caps.map fun c => match c.thr with
      | some W => if renamed.contains W then { c with thr := some (W ++ "b") } else c
      | none => c }

/-- The capabilities of a copy: those of its row, then those its blocks use; one of the row's
that a block uses too is the block's (`blk`).  `[spec §32]` -/
def withBlkCaps (cs bc : List Cap) : List Cap :=
  (addCaps cs bc).map fun c => if bc.any (·.eff == c.eff) then { c with blk := true } else c

/-- A copy's capabilities and sites from what serves the slots of its callee's row `row`: `hs` the
handlers of its answering slots and `ss` the sites of its control slots, each in the row's order
(SPEC §38). Each capability is at the copy's own variable, named as its slot; each site is
relabelled as the slot it serves, at the slot's type arguments in the callee's frame, so that an
operation of the body is resolved at the callee's types. The copy's row is at the slot's types
when they mention the callee's type parameters `tps`, and otherwise at the site's as the caller
writes them, which are the same types. -/
def slotsOf (sp : Span) (row : List Inst) (tps : List String) (hs : List HSig) (ss : List Site)
    (answering : String → Bool) : List Cap × List Site := Id.run do
  let mut cs : List Cap := []
  let mut out : List Site := []
  let mut ia := 0
  let mut ic := 0
  for i in row do
    if answering i.eff then
      if let some h := hs[ia]? then
        cs := cs ++ [⟨i.eff, capVar i.eff i.name, capLife i.eff i.name, h, none, false, i.name, true⟩]
      ia := ia + 1
    else
      if let some s := ss[ic]? then
        if let some (w, W) := s.thr then cs := cs ++ [threadCap sp i.eff w W]
        let args := match i.args with
          | some As => if As.any (mentions tps) then As else s.args
          | none => s.args
        out := out ++ [{ s with sp, what := "the caller", name := i.name, slot := some (i.args.getD s.args),
                                args }]
      ic := ic + 1
  return (cs, out)

/-- The capabilities the blocks `blks` use, in the order of the blocks. -/
def blkCaps (blks : List Blk) : List Cap := blks.foldl (fun acc b => addCaps acc b.caps) []

/-- The key of a copy for its blocks: `b{j}n{n}…` per block parameter `j`, followed by the
answering handlers whose capabilities the block uses, and `m{i}` for each `let mut` variable it
writes, by position: the copy takes them as parameters of types of its own (`mutCap`), so the
caller's names are not the copy's (SPEC §41, R3). -/
def blockKeys (bs : List Blk) : List String :=
  bs.map fun b => s!"b{b.j}" ++ String.join (b.ss.map fun s => s!"n{s.n}") ++
    String.join ((b.caps.filter (·.thr.isNone)).map fun c => c.h.key) ++
    String.join (((b.caps.filter (·.isMut)).zipIdx).map fun (_, i) => s!"m{i}")

/-- The sites, as the reports name them. -/
def sitesText (ss : List Site) : String :=
  ", ".intercalate (ss.map fun s => s!"the site {s.n} of `{s.eff}`")

/-- Where a block performs and what it uses, as the reports say it: `at the site …`, and `with the
capabilities of …`.  `[spec §32]` -/
def blockText (ss : List Site) (cs : List Cap) : String :=
  let atS := if ss.isEmpty then "" else s!"at {sitesText ss}"
  let ans := cs.filter (·.thr.isNone)
  let wc := if ans.isEmpty then "" else
    "with the capabilities of " ++ ", ".intercalate (ans.map fun c => s!"`{c.eff}`")
  ", ".intercalate ([atS, wc].filter (!·.isEmpty))

/-- A copy's function with its block parameters `blks` (by index) at their blocks' rows: the
parameters' types `!U(A -o F[row] B)`, the parameters by name with their sites, and the sites of
every block, beside the copy's own (`ss`). -/
def withBlocks (env : Env) (sp : Span) (name : String) (f : FnParts) (ss : List Site)
    (blks : List Blk) (ports : List (Nat × List (Site × Bool)) := []) :
    Except Error (FnParts × List (String × List Site × List Cap) × List Site) := do
  if blks.isEmpty then return (f, [], ss)
  let names := paramNames f
  let n := names.length
  let mut reps : List (Nat × VTy) := []
  let mut named : List (String × List Site × List Cap) := []
  for b in blks do
    let some x := names[b.j]? | throw ⟨sp, s!"internal error: the parameter {b.j} of `{name}`"⟩
    let some A := compAt n f.P b.j | throw ⟨sp, s!"internal error: the parameter `{x}` of `{name}`"⟩
    let cs := b.caps.map (·.canon sp)
    -- At a computation parameter, the block performs what is provided at its ports (SPEC §33),
    -- its sites in the order of its row.
    let pss := ((ports.lookup b.j).getD []).map (·.1)
    let all := addSites b.ss pss
    let bss := if pss.isEmpty then b.ss else
      addSites (b.order.filterMap fun e => all.find? (·.eff == e)) all
    let some A' := rowedCapFnTy (env.rowOf bss) cs (unrowed A)
      | throw ⟨sp, s!"internal error: the block parameter `{x}` of `{name}`"⟩
    reps := reps ++ [(b.j, A')]
    named := named ++ [(x, bss, cs)]
  let all := blks.foldl (fun acc b => addSites acc b.ss) ss
  pure ({ f with P := setComps n f.P 0 reps }, named, all)

/-- The environment of a copy's body with its block parameters' rows (`rowV`): the sites' effects,
and the answering effects whose capabilities the blocks use. -/
def Env.withBlocks (env : Env) (named : List (String × List Site × List Cap)) : Env :=
  { env with cbRows := named.map fun (x, ss, cs) =>
      (x, ss.map (fun s => (⟨s.eff, some s.args, none⟩ : Inst)) ++
        (cs.filter (·.thr.isNone)).map fun c => (⟨c.eff, none, none⟩ : Inst)) }

/-- The effectful blocks a call of `x` passes (SPEC §30): each component `j` of its argument tuple
at a parameter of a function type that is a closure written here whose body performs control
operations, or a block parameter of the copy being elaborated; each with the sites its operations
go to, the innermost handlers of their effects where the block is written. -/
def blockArgs (cx : Cx) (x : String) (W : Val) : Except Error (List Blk) := do
  let some P := (cx.env.sigs.lookup x).bind paramTyOf | return []
  let cps := (cx.env.comps.lookup x).getD []
  let mut out : List Blk := []
  for ((A, V₀), j) in (argComps fuel P W).zipIdx do
    -- A closure that writes enclosing `let mut` variables takes them first and hands them back
    -- first, as a block's capabilities (SPEC §41, rule R3).
    let (ws, V) := stripWrites V₀
    if (rowedFnTy .nil (unrowed A)).isNone then
      if let x :: _ := ws then throw (escapingWriter V₀.span x)
      continue
    -- A computation parameter's argument (SPEC §33): what the callee provides is served at its
    -- ports, the rest where the argument is written.
    let prov := ((cps.find? (·.1 == j)).map (·.2.2)).getD []
    let isComp := (cps.find? (·.1 == j)).isSome
    if let some e := prov.find? fun (e, _) => cx.env.answering e.name then
      throw ⟨e.1.span, s!"`{x}` provides the answering effect `{e.1.name}` to its parameter: not " ++
        "provided (a provided effect is a control effect, SPEC §33)"⟩
    match V with
    | .var _ v =>
      if let some (ss, cs) := cx.cbs.lookup v then
        if isComp then
          throw ⟨V.span, s!"`{v}` is a block parameter, passed on to the computation parameter " ++
            s!"of `{x}`: not provided (its operations are at the ports of the function it was " ++
            "given to, SPEC §33)"⟩
        out := out ++ [{ j, ss, caps := cs }]
        continue
    | _ => pure ()
    -- A closure written here, or a function named here (a call of it in a block, `etaArgs`).
    let row₀ := match V with
      | .thunkv _ M | .bangThunkv _ M => rowC cx.env fuel M
      | V => rowV cx.env fuel V
    let row := cx.env.withoutAll row₀ prov
    let ctl := cx.ctl row
    -- The capabilities it uses (an answering handler's state, a `for`'s threaded variables, the
    -- `let mut` variables it writes) are passed with it at each call (SPEC §32, §41).
    let cs := cx.need row ++ ws.map (mutCap V₀.span)
    if ctl.isEmpty && cs.isEmpty && !isComp then continue
    match V with
    | .thunkv .. | .bangThunkv .. => pure ()
    | V => if !isComp && ((headName V).bind cx.env.fn?).isNone then continue
    let mut ss : List Site := []
    for i in ctl do
      let s ← cx.serve V.span "this block" i
      ss := addSites ss [s]
    out := out ++ [⟨j, ss, cs, prov, (cx.ctl row₀).map (·.eff)⟩]
  pure out

/-- The arguments of a call of `x` with each function named at a parameter of function type a
block that calls it, `!{ a -> g(a) }` (or `{ a -> g(a) }`), when the function has a row or the
parameter is a computation parameter (SPEC §33): passing `g` and passing `{ a -> g(a) }` are one
thing. A block parameter of the copy being elaborated is passed on as it is.  `[spec §33]` -/
def etaArgs (cx : Cx) (x : String) (W : Val) : EM Val := do
  let some P := (cx.env.sigs.lookup x).bind paramTyOf | return W
  let cps := (cx.env.comps.lookup x).getD []
  let comps := argComps fuel P W
  if !comps.any (fun (A, V) => (rowedFnTy .nil (unrowed A)).isSome && match V with
      | .thunkv .. | .bangThunkv .. => false
      | _ => true) then return W
  let mut vs : List Val := []
  for ((A, V), j) in comps.zipIdx do
    let isComp := cps.any (·.1 == j)
    let named := match V with
      | .var _ v => (cx.cbs.lookup v).isNone
      | .defApp .. => true
      | _ => false
    let rowed := ((headName V).bind cx.env.fn?).isSome
    if (rowedFnTy .nil (unrowed A)).isSome && named && (isComp || rowed) then
      let a ← fresh "fx_e"
      let sp := V.span
      let body : Comp := .lam sp ⟨a, sp⟩ (holeTy sp) (.ret sp (.app sp V (.var sp a)))
      vs := vs ++ [match unrowed A with
        | .bang .. => .bangThunkv sp body
        | _ => .thunkv sp body]
    else vs := vs ++ [V]
  let rec tuple : List Val → Val
    | [] => W
    | [V] => V
    | V :: Vs => .pair V.span V (tuple Vs)
  pure (tuple vs)

/-- The environment in which `rowC` reads whether a computation reaches a call of the parameter `x`
performing `e` outside a `with` of `e`: no operation, no function's row and no handler's own row
counts, and `x` performs `e` (SPEC §33).  `[spec §33]` -/
def Env.onlyParam (env : Env) (x e : String) (As : List VTy) : Env :=
  { env with ops := [], fns := [], cbRows := [(x, [⟨e, some As, none⟩])],
             chandlers := env.chandlers.map fun h => { h with row := [] } }

/-- `M` calls the parameter `x` performing `e`, outside a `with` of `e` in it. -/
def reachesParam (env : Env) (x e : String) (As : List VTy) (M : Comp) : Bool :=
  (rowC (env.onlyParam x e As) fuel M).any (·.eff == e)

/-- The static name of a `with` of `e` around `M` in a copy made for computation parameters
(SPEC §33): the port of the parameters whose calls of `e` it serves, when `M` calls one. A port
that is a site of the copy's row is not a `with`'s, and two ports are not one site's.
`[spec §33]` -/
def Cx.portIn (cx : Cx) (sp : Span) (h e : String) (M : Comp) : Except Error (Option Nat) := do
  let mut out : Option (String × Nat) := none
  for (x, p, own) in cx.ports do
    if p.eff != e || !reachesParam cx.env x e p.args M then continue
    unless own do
      throw ⟨sp, s!"`with {h}` serves `{e}` for a call of the computation parameter `{x}`, which " ++
        s!"is called elsewhere outside a handler of `{e}`, where the caller serves it: the effect a " ++
        "computation parameter provides is served at one site of the function, until a port can be " ++
        "relabelled (SPEC §33 *Open*)"⟩
    match out with
    | some (y, n) =>
      unless n == p.n do
        throw ⟨sp, s!"`with {h}` serves `{e}` for the computation parameters `{y}` and `{x}`, which " ++
          "provide it at two ports: not provided until a port can be relabelled (SPEC §33 *Open*)"⟩
    | none => out := some (x, p.n)
  pure (out.map (·.2))

/-- The capabilities of a copy made for the handlers `hs`, one per answering effect of `effs`. -/
def copyCaps (effs : List String) (hs : List HSig) : List Cap :=
  (effs.zip hs).map fun (e, h) => ⟨e, capVar e none, capLife e none, h, none, false, none, false⟩

/-- A body taking the capabilities `cs` first: `fx_pp : mut 'l₁ S₁ * (… * P)`, taken apart into
the capabilities and the original parameter `p`. -/
def takeCaps (sp : Span) (cs : List Cap) (f : FnParts) (body : Comp) : EM FnParts := do
  let pp ← fresh "fx_pp"
  let body ← unpack sp cs f.p.name pp body
  let lives := (cs.filter (fun c => c.thr.isNone && !c.h.cell)).map fun c =>
    ((⟨c.life, sp⟩ : Ident), Life.top sp)
  pure { f with lives := lives ++ f.lives, P := capsTy sp cs f.P, T := capsTy sp cs f.T,
                p := ⟨pp, sp⟩, body }

/-- A `with`, a `for` over a call that performs an iteration effect, a stored generator, or a call
of a function with a computation parameter, in a value, outside nothing: the elaboration must
reach it. -/
def withInV (env : Env) : Nat → Val → Bool
  | 0, _ => false
  | k + 1, V => match V with
    | .app _ (.app _ (.sugar _ (.handle ..)) _) _ => true
    | .app _ f W =>
      let pull := match headName f with
        | some x => (env.pullArgs x W).any fun (V, p) => p && (env.iterCall? V).isSome
        | none => false
      -- A call of a function with a computation parameter is a call of its copy (SPEC §33).
      let comp := match headName f with
        | some x => (env.comps.lookup x).isSome
        | none => false
      pull || comp || withInV env k f || withInV env k W
    | .pair _ f W => withInV env k f || withInV env k W
    | .inl _ V | .inr _ V | .ascribe _ V _ | .roll _ V | .unroll _ V | .boxed _ _ V
    | .unbox _ V | .unbang _ V | .inst _ V _ | .sub _ V _ | .shorten _ _ _ _ V | .mark _ _ V => withInV env k V
    | .run _ M | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M => withInC k M
    | _ => false
where
  withInC : Nat → Comp → Bool
    | 0, _ => false
    | k + 1, M => match M with
      | .ret _ V | .absurd _ V => withInV env k V
      | .bind _ _ (some A) (.ret _ V) N =>
        (isPullTy A && (env.iterCall? V).isSome) || withInV env k V || withInC k N
      | .bind _ _ _ M N | .with_ _ M N => withInC k M || withInC k N
      | .letUnit _ V M | .letPair _ _ _ V M => withInV env k V || withInC k M
      | .loop _ _ src V M N => (src matches .each _ && (env.iterCall? V).isSome) || withInV env k V ||
        withInC k M || withInC k N
      | .case _ V _ M _ N => withInV env k V || withInC k M || withInC k N
      | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
      | .nuOut _ M | .ascribe _ M _ => withInC k M
      | _ => false

/-- A `return e` of a loop's body in a value, outside nested computations. -/
def retIn : Nat → Val → Bool
  | 0, _ => false
  | k + 1, V => match V with
    | .app _ (.sugar _ .retE) _ => true
    | .app _ f W | .pair _ f W => retIn k f || retIn k W
    | .inl _ V | .inr _ V | .ascribe _ V _ => retIn k V
    | _ => false

/-- The plain calls of `V` that perform no effect, lifted (`liftCalls`), in the order its
evaluation runs them in; an effectful call stays, its arguments' plain calls lifted. -/
def liftPlain (cx : Cx) : Nat → Val → StateT (List Bind) EM Val
  | 0, V => pure V
  | k + 1, V => match V with
    | .app sp f W =>
      match f with
      | .sugar .. | .app _ (.sugar ..) _ => do pure (.app sp f (← liftPlain cx k W))
      | _ =>
        if !(cx.needV V).isEmpty || cx.ctlV V || cx.lcallV V then do
          pure (.app sp f (← liftPlain cx k W))
        else liftCalls k V
    | .pair sp V W => do pure (.pair sp (← liftPlain cx k V) (← liftPlain cx k W))
    | .inl sp V => do pure (.inl sp (← liftPlain cx k V))
    | .inr sp V => do pure (.inr sp (← liftPlain cx k V))
    | .ascribe sp V A => do pure (.ascribe sp (← liftPlain cx k V) A)
    | .roll sp V => do pure (.roll sp (← liftPlain cx k V))
    | .unroll sp V => do pure (.unroll sp (← liftPlain cx k V))
    | .boxed sp l V => do pure (.boxed sp l (← liftPlain cx k V))
    | .unbox sp V => do pure (.unbox sp (← liftPlain cx k V))
    | V => pure V

/-- A lend in the arguments of a call that threads a capability is not provided. -/
def noLend (sp : Span) (what : String) (W : Val) : EM Unit := do
  if W.lends then
    throw ⟨sp, s!"a place is lent (`&mut x`) in the arguments of {what}, which also threads a " ++
      "capability: lend it in a call of its own"⟩

/-- `bindParams`: the parameters `xs` bound from the tuple `p`. -/
def bindParams (sp : Span) (p : String) : List Ident → Comp → EM Comp
  | [], M => pure (.letUnit sp (.var sp p) M)
  | [x], M => pure (if x.name == p then M else .bind sp x none (.ret sp (.var sp p)) M)
  | [x, y], M => pure (.letPair sp x y (.var sp p) M)
  | x :: xs, M => do
    let r ← fresh "fx_p"
    pure (.letPair sp x ⟨r, sp⟩ (.var sp p) (← bindParams sp r xs M))

/-- A computation with `f` applied at each terminal reached through tail positions. -/
def wrapTerms (f : Comp → Comp) : Comp → Comp
  | .bind sp x A M N => .bind sp x A M (wrapTerms f N)
  | .letUnit sp V M => .letUnit sp V (wrapTerms f M)
  | .letPair sp x y V M => .letPair sp x y V (wrapTerms f M)
  | .case sp V x M y N => .case sp V x (wrapTerms f M) y (wrapTerms f N)
  | .loop sp ℓ src V M N => .loop sp ℓ src V M (wrapTerms f N)
  | T => f T

/-- `x <- return V'; N` after the bindings `bs` of `V'`'s calls. A value that is one call's answer
binds `x` as the call's binding does: `x` is the call's answer.  `[spec §18]` -/
def bindValue (sp : Span) (x : Ident) (A : Option VTy) (rsp : Span) (bs : List Bind) (V' : Val)
    (N : Comp) : EM Comp := do
  match bs.getLast?, V' with
  | some (.one bsp y B M flat), .var _ z =>
    if y == z then return ← chain (bs.dropLast ++ [.one bsp x.name (A <|> B) M flat]) N
  | some (.caps bsp t B M cs y flat post), .var _ z =>
    if y == z && (A.isNone || B.isNone) then
      let B' := B <|> A.map (capsTy sp cs)
      return ← chain (bs.dropLast ++ [.caps bsp t B' M cs x.name flat post]) N
  | _, _ => pure ()
  chain bs (.bind sp x A (.ret rsp V') N)

mutual
/-- `M` with its operations resolved, handing the capabilities `cs` back beside its result: each
terminal answering `v` answers `(c₁, (…, (cₙ, v)))`. With `wrap := false` (the body of a loop,
which threads the capabilities by name), the terminals are kept, and the capabilities are only
bound again. A `with` inside is elaborated either way. -/
def trC : Nat → Cx → List Cap → Bool → Comp → EM Comp
  | 0, _, _, _, M => throw ⟨M.span, "internal error: a body nested too deeply"⟩
  | n + 1, cx, cs, wrap, M => do
    match M with
    | .ret sp V@(.app _ f W) =>
      -- A call of a function with a row in tail position, whose capabilities are the ones this
      -- computation hands back: its answer is this one's, and is answered as it is.
      let self := match cx.recSelf, headName f with
        | some rs, some x => rs.members.contains x
        | _, _ => false
      match headName f, wrap && !self with
      | some x, true =>
        match cx.env.fn? x with
        | some g =>
          let row := cx.rowAt V.span g
          let used := cx.need row
          -- A call passing effectful blocks is a call of the copy at their rows (`blockCall`).
          let blks ← (blockArgs cx x W : Except Error _)
          if !W.lends && used.map (·.var) == cs.map (·.var) && blks.isEmpty then
            let (bs, W') ← trV n cx cs W
            let name ← copyFor n cx sp x g row []
            let f' : Val := match f with
              | .defApp fsp _ As => .defApp fsp name As
              | _ => .var f.span name
            report sp "call" (s!"{x} → `{name}`, in tail position: its answer is this one's")
            return ← chain bs (.ret sp (.app sp f' (capsTuple sp used W')))
          else trRet n cx cs wrap sp V
        | none => trRet n cx cs wrap sp V
      | _, _ => trRet n cx cs wrap sp V
    | .ret sp V => trRet n cx cs wrap sp V
    | .bind sp x A M N => trBind n cx cs wrap sp x A M N
    | .letUnit sp V M =>
      let (bs, V') ← trV n cx cs V
      chain bs (.letUnit sp V' (← trC n cx cs wrap M))
    | .letPair sp x y V M =>
      let (bs, V') ← trV n cx cs V
      chain bs (.letPair sp x y V' (← trC n cx cs wrap M))
    | .case sp V x M y N =>
      let (bs, V') ← trV n cx cs V
      chain bs (.case sp V' x (← trC n cx cs wrap M) y (← trC n cx cs wrap N))
    | .loop sp ℓ src V M N =>
      match src, cx.env.iterCall? V with
      | .each x, some (g, gs, i, f, W) =>
        if (cx.ctl (rowC cx.env fuel M)).isEmpty && !mayLoop fuel M then
          forSite n cx cs wrap sp ℓ x g gs i f W M N
        else
          -- A body that performs a control operation would hold the continuation across it,
          -- which has no destructor (its cancel performs at the site's row), and one that loops
          -- cannot be a clause, which is total: the `for` drains the stored generator instead.
          let (bs, V') ← pullSite n cx cs sp g gs i f W
          report sp "lowering" (s!"for over {g}: its body performs a control operation or " ++
            "loops, so it drains the stored generator")
          chain bs (.loop sp ℓ src V' (← trC n cx [] false M) (← trC n cx cs wrap N))
      | _, _ =>
        let (bs, V') ← trV n cx cs V
        -- The body rebinds the capabilities it uses by name, and the loop threads them.
        chain bs (.loop sp ℓ src V' (← trC n cx [] false M) (← trC n cx cs wrap N))
    | .absurd sp V =>
      let (bs, V') ← trV n cx cs V
      chain bs (.absurd sp V')
    -- A function's code: a `with` inside it is elaborated.
    | .lam sp x A M => pure (.lam sp x A (← trC n cx cs wrap M))
    | .lamL sp x b M => pure (.lamL sp x b (← trC n cx cs wrap M))
    | .with_ sp M N =>
      if let some c := (cx.needC M ++ cx.needC N).head? then
        throw ⟨sp, s!"an operation of `{c.eff}` is performed here, in a form that does not " ++
          "thread its capability"⟩
      pure (.with_ sp (← trC n cx [] false M) (← trC n cx [] false N))
    | .proj sp i M => do pure (.proj sp i (← trInner n cx M))
    | .app sp M y => do pure (.app sp (← trInner n cx M) y)
    | .inst sp M a => do pure (.inst sp (← trInner n cx M) a)
    | .nuIn sp M => do pure (.nuIn sp (← trInner n cx M))
    | .nuOut sp M => do pure (.nuOut sp (← trInner n cx M))
    | .ascribe sp M C => do pure (.ascribe sp (← trInner n cx M) C)
    | T =>
      if let some c := (cx.needC T).head? then
        throw ⟨T.span, s!"an operation of `{c.eff}` is performed here, in a form that does not " ++
          "thread its capability"⟩
      if !wrap || cs.isEmpty then return T
      let rv ← fresh "fx_t"
      pure (.bind T.span ⟨rv, T.span⟩ none T
        (.ret T.span (capsTuple T.span cs (.var T.span rv))))

/-- `x <- M; N` of `trC`. -/
def trBind : Nat → Cx → List Cap → Bool → Span → Ident → Option VTy → Comp → Comp → EM Comp
  | 0, _, _, _, sp, _, _, _, _ => throw ⟨sp, "internal error: a body nested too deeply"⟩
  | n + 1, cx, cs, wrap, sp, x, A, M, N => do
    -- `x <- return y`, a copy of a block parameter, a continuation or a layer's `call`.
    if let some y := (match M with | .ret _ V => V.copyOf? | _ => none) then
      if let some cx' := cx.copy x.name y then
        return .bind sp x A M (← trC n cx' cs wrap N)
    -- `x : pull A B R <- return g(W)`: the stored generator of the call.
    if let (some A', .ret rsp V) := (A, M) then
      if let (true, some (g, gs, i, f, W)) := (isPullTy A', cx.env.iterCall? V) then
        let (bs, V') ← pullSite n cx cs rsp g gs i f W
        return ← chain bs (.bind sp x A (.ret rsp V') (← trC n cx cs wrap N))
    let csM := cx.needC M
    let N' ← trC n cx cs wrap N
    if csM.isEmpty then
      if let .ret rsp V := M then
        -- A value: its effectful calls bound before the binding, which keeps its form.
        let (bs, V') ← trV n cx [] V
        bindValue sp x A rsp bs V' N'
      else pure (.bind sp x A (← trC n cx [] false M) N')
    else if let .ret rsp V := M then
      let (bs, V') ← trV n cx cs V
      bindValue sp x A rsp bs V' N'
    else
      -- `M` hands back the capabilities it uses, which are bound again for `N`.
      let t ← fresh "fx_b"
      let M' ← trC n cx csM true M
      let body ← unpack sp csM x.name t N'
      pure (bindFlat sp t (A.map (capsTy sp csM)) M' body)

/-- A computation under a form that does not thread capabilities: its control operations
resolved; an answering one is not provided there. -/
def trInner : Nat → Cx → Comp → EM Comp
  | 0, _, M => throw ⟨M.span, "internal error: a body nested too deeply"⟩
  | n + 1, cx, M => do
    if let some c := (cx.needC M).head? then
      throw ⟨M.span, s!"an operation of `{c.eff}` is performed here, in a form that does not " ++
        "thread its capability"⟩
    trC n cx [] false M

/-- A terminal `return V` of `trC`. -/
def trRet : Nat → Cx → List Cap → Bool → Span → Val → EM Comp
  | 0, _, _, _, sp, _ => throw ⟨sp, "internal error: a body nested too deeply"⟩
  | n + 1, cx, cs, wrap, sp, V => do
    let (bs, V') ← trV n cx cs V
    let plain := isExit V' || !wrap || cs.isEmpty
    -- A value that is one call's answer is the call, in tail position: its answer is this one's
    -- when it hands back the capabilities this computation hands back, or none are. A binding
    -- annotated with the call's type (whose type is not known otherwise) ascribes the call's value, or,
    -- at a computation, stays.
    let typed : Option VTy → Comp → Option Comp
      | none, M => some M
      | some A, .ret rsp W => some (.ret rsp (.ascribe rsp W A))
      | some _, _ => none
    match bs.getLast?, V' with
    | some (.one _ x A M _), .var _ y =>
      if let (true, some M') := (x == y && plain, typed A M) then return ← chain bs.dropLast M'
    | some (.caps _ _ A M cs' x _ _), .var _ y =>
      if let (true, some M') := (x == y && ((cs'.isEmpty && plain) ||
          (wrap && cs'.map (·.var) == cs.map (·.var))), typed A M) then
        return ← chain bs.dropLast M'
    | _, _ => pure ()
    let T := if plain then Comp.ret sp V' else .ret sp (capsTuple sp cs V')
    chain bs T

/-- A value with its effectful calls lifted out before it, as bindings (that thread the
capabilities `cs` when they use them); the value refers to their results. Every plain call
evaluated before an effectful one is lifted too, so the calls keep their order. -/
def trV : Nat → Cx → List Cap → Val → EM (List Bind × Val)
  | 0, _, _, V => throw ⟨V.span, "internal error: a value nested too deeply"⟩
  | n + 1, cx, cs, V => do
    let row := rowV cx.env fuel V
    let needs := !(cx.need row).isEmpty || !(cx.ctl row).isEmpty
    -- An effect with no handler in scope is reported where it is performed (`goV`).
    let unhandled := row.any fun i => (cx.capOf i.eff).isNone && (cx.siteOf i.eff).isNone
    -- A `return e` from a loop's body hands the copy's capabilities back too (`plainApp`).
    let ret := !cx.fnCaps.isEmpty && retIn fuel V
    -- A layer's `call` is the member's call, which threads the environment.
    let lcall := cx.lcallV V
    -- A closure that writes is given at a block parameter, or refused (`goV`).
    let writes := V.anySugar (· matches .writes _)
    -- A call of a block parameter whose block takes capabilities passes them (`blockParamCall`).
    let cbCall := cx.cbs.any fun (y, _, bcs) => !bcs.isEmpty && Frontend.Check.mentionsV y V
    if !needs && !unhandled && !ret && !lcall && !writes && !cbCall && !withInV cx.env fuel V then
      return ([], V)
    let (V, pre) ← if needs || lcall then (liftPlain cx fuel V).run [] else pure (V, [])
    let (bs, V') ← goV n cx cs V
    pure (pre ++ bs, V')

/-- `trV` below the lifting of plain calls. -/
def goV : Nat → Cx → List Cap → Val → EM (List Bind × Val)
  | 0, _, _, V => throw ⟨V.span, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, V => match V with
    | .app sp (.app sp₂ (.sugar ksp (.handle h l As nm)) P) (.thunkv tsp (.lam lsp b A M)) =>
      match cx.env.handler? h, cx.env.chandler? h with
      | some hs, _ => withBlk k cx cs sp sp₂ ksp hs l P tsp lsp b A M nm
      | none, some ch => withCtl k cx cs sp ksp ch As P M nm
      | none, none =>
        if cx.env.driver? h then do
          -- `with d { M }` of a heap driver: `M`, its recursive groups driven by `d`.
          report ksp "lowering" s!"with {h}: the recursive groups called in its body are driven by `{h}`"
          let M' ← trC k { cx with driver := some h } [] false M
          let r ← fresh "fx_v"
          let bind : Bind := .one sp r none M' true
          pure ([bind], .var sp r)
        else if (cx.env.layer? h).isSome then do
          -- `with L { M }` of a layer: `M`, its recursive groups' generators transformed by `L`.
          report ksp "lowering" (s!"with {h}: a layer; the recursive groups called in its body are " ++
            s!"the fixed points of their generators transformed by `{h}`")
          let cxL : Cx := { cx with env := { cx.env with inLayers := h :: cx.env.inLayers } }
          let csM := cx.need (rowV cx.env fuel V)
          let M' ← trC k cxL csM true M
          let t ← fresh "fx_b"
          let r ← fresh "fx_v"
          let bind : Bind := .caps sp t none M' csM r true id
          pure ([bind], .var sp r)
        else throw ⟨ksp, s!"no handler `{h}` is declared before this `with`"⟩
    | .app sp (.app sp₂ (.sugar ksp k'@(.borrow ..)) P) (.thunkv tsp (.lam lsp b A M)) => do
      let (bsP, P') ← goV k cx cs P
      -- The capabilities a task spawned in the block is given are lent for the block, which
      -- bounds its tasks; they go with the task and are not handed back (SPEC §34).
      let given₀ := cx.givenC fuel M
      let given := given₀.foldl (fun acc c => if acc.any (·.var == c.var) then acc else acc ++ [c]) []
      if let some c := given.find? fun c => (given₀.filter (·.var == c.var)).length > 1 then
        throw ⟨ksp, s!"two tasks spawned in this block are given the capability of `{c.eff}`: a " ++
          "capability is lent to one task at a time, which holds it until it ends (SPEC §34 *Open*)"⟩
      if !given.isEmpty then
        let mut lent : List Cap := []
        for c in given do
          lent := lent ++ [{ c with life := ← fresh "fx_gl", h := { c.h with cell := false } }]
        let cx' : Cx := { cx with caps := cx.caps.map fun c => (lent.find? (·.var == c.var)).getD c }
        let csM := (cx'.needC M).filter fun c => !lent.any (·.var == c.var)
        report ksp "lowering" (s!"borrow block: the tasks spawned in it are given the capabilities of " ++
          ", ".intercalate (lent.map fun c => s!"`{c.eff}`") ++ ", lent for the block")
        let M' ← trC k cx' csM true M
        let blk := Val.app sp (.app sp₂ (.sugar ksp k') P') (.thunkv tsp (.lam lsp b A M'))
        let (bsH, hv) ← reborrowed k sp ksp blk lent
        let (bsB, V) ← blockResult k cx sp hv csM
        return (bsP ++ bsH ++ bsB, V)
      let csM := cx.needC M
      let ctl := cx.ctlC M
      if csM.isEmpty && !ctl then
        let M' ← trC k cx [] false M
        return (bsP, .app sp (.app sp₂ (.sugar ksp k') P') (.thunkv tsp (.lam lsp b A M')))
      let M' ← trC k cx csM true M
      let blk := Val.app sp (.app sp₂ (.sugar ksp k') P') (.thunkv tsp (.lam lsp b A M'))
      blockResult k cx sp blk csM
    -- A closure that writes and is not given at a block parameter (SPEC §41, rule R3).
    | .app sp (.sugar _ (.writes xs)) _ => throw (escapingWriter sp (xs.headD "?"))
    -- `y.op(W)`: the operation at the handler named `y` (SPEC §38).
    | .app sp (.sugar osp (.named y x)) W => do
      let some o := cx.env.op? x
        | throw ⟨osp, s!"`{x}` is not an operation: `{y}.{x}(…)` performs an operation at the " ++
            s!"handler named `{y}`"⟩
      if cx.env.answering o.eff then opCall k cx cs sp x o W (some y) else ctlCall k cx cs sp x o W (some y)
    | .app sp f W => do
      match headName f with
      | some x =>
        if let some rs := cx.recSelf then
          if let some j := rs.members.idxOf? x then
            return ← selfCall k cx cs sp rs x j W
        if let some lc := cx.layerCall then
          if lc.name == x then
            return ← layerSelfCall k cx cs sp lc W
        if let some rk := cx.resume then
          if rk.k == x then
            return ← resumeCall k cx cs sp rk W
        -- A call of a block parameter of a copy made for effectful blocks (SPEC §30).
        if let some (ss, bcs) := cx.cbs.lookup x then
          return ← blockParamCall k cx cs sp f x ss bcs W
        -- An argument at a stored generator's parameter: the stored generator of the call.
        let (bP, W) ← pullArgsV k cx cs x W
        -- Effectful blocks passed: a call of the callee's copy at their rows (SPEC §30); a
        -- function named at a block's parameter is the block that calls it (SPEC §33).
        if (cx.env.op? x).isNone then
          let W ← etaArgs cx x W
          let blks ← (blockArgs cx x W : Except Error _)
          if !blks.isEmpty then
            let g? : Option FSig := match cx.env.fn? x with
              | some g => some g
              | none => (cx.env.plain.lookup x).map fun d => { name := x, row := [], decl := d }
            if let some g := g? then
              let (b, V') ← blockCall k cx cs sp f x g W blks
              return (bP ++ b, V')
        let (b, V') ← match cx.env.op? x, cx.env.fn? x with
          | some o, _ =>
            if cx.env.answering o.eff then opCall k cx cs sp x o W none else ctlCall k cx cs sp x o W none
          | none, some g => fnCall k cx cs sp f x g W
          | none, none => plainApp k cx cs sp f W
        pure (bP ++ b, V')
      | none => plainApp k cx cs sp f W
    | .var sp x => do
      if (cx.cbs.lookup x).isSome then
        throw ⟨sp, s!"`{x}` is a block parameter given an effectful block: it can only be called, " ++
          "or passed on to a block parameter of a call; a block is not stored (SPEC §30)"⟩
      if let some rk := cx.resume then
        if rk.k == x && rk.stateful then
          throw ⟨sp, s!"the continuation `{x}` of a handler with a state is passed as a value: it " ++
            "can only be resumed, `{x}(v)`, or dropped"⟩
      if let some lc := cx.layerCall then
        if lc.name == x then
          throw ⟨sp, s!"`{x}`, the call a layer runs around, is passed as a value: it can only be called"⟩
      if (cx.env.comps.lookup x).isSome then
        throw ⟨sp, s!"`{x}` takes a computation parameter and is passed as a value: it can only be " ++
          "called (SPEC §33)"⟩
      match cx.env.fn? x with
      | some g =>
        if g.group.isSome then
          throw ⟨sp, s!"`{x}` is recursive and is passed as a value: it can only be called " ++
            "(effectful callbacks, #161)"⟩
        throw ⟨sp, s!"`{x}` performs `{", ".intercalate (g.row.map (·.eff))}` and is passed as a " ++
          "value: it can only be called (effectful callbacks, #161)"⟩
      | none => pure ([], V)
    | .pair sp V W => do
      let (b₁, V') ← goV k cx cs V
      let (b₂, W') ← goV k cx cs W
      pure (b₁ ++ b₂, .pair sp V' W')
    | .inl sp V => do let (b, V') ← goV k cx cs V; pure (b, .inl sp V')
    | .inr sp V => do let (b, V') ← goV k cx cs V; pure (b, .inr sp V')
    | .ascribe sp V A => do let (b, V') ← goV k cx cs V; pure (b, .ascribe sp V' A)
    | .roll sp V => do let (b, V') ← goV k cx cs V; pure (b, .roll sp V')
    | .unroll sp V => do let (b, V') ← goV k cx cs V; pure (b, .unroll sp V')
    | .boxed sp l V => do let (b, V') ← goV k cx cs V; pure (b, .boxed sp l V')
    | .unbox sp V => do let (b, V') ← goV k cx cs V; pure (b, .unbox sp V')
    | .unbang sp V => do let (b, V') ← goV k cx cs V; pure (b, .unbang sp V')
    | .inst sp V l => do let (b, V') ← goV k cx cs V; pure (b, .inst sp V' l)
    | .sub sp V l => do let (b, V') ← goV k cx cs V; pure (b, .sub sp V' l)
    | .shorten sp m σ l V => do let (b, V') ← goV k cx cs V; pure (b, .shorten sp m σ l V')
    | .mark sp m V => do let (b, V') ← goV k cx cs V; pure (b, .mark sp m V')
    | .run sp M => do
      let csM := cx.needC M
      if csM.isEmpty && !cx.ctlC M then return ([], .run sp (← trC k cx [] false M))
      let M' ← trC k cx csM true M
      let t ← fresh "fx_b"
      let r ← fresh "fx_v"
      let bind : Bind := .caps sp t none M' csM r true id
      pure ([bind], .var sp r)
    | .thunk sp M | .thunkv sp M | .bangThunk sp M | .bangThunkv sp M => do
      let row := rowC cx.env fuel M
      match (cx.need row).head?, (cx.ctl row).head? with
      | some c, _ => throw (notInClosure sp c.eff)
      | none, some i => if (cx.siteOf i.eff).isSome then throw (notInClosure sp i.eff) else
          throw ⟨sp, s!"an operation of `{i.eff}` is performed inside a closure or block that is " ++
            s!"not run in place, and no handler of `{i.eff}` is in scope"⟩
      | none, none =>
        -- A closure sees no capability and no site of the enclosing body; a `with` inside it is
        -- its own.
        let M' ← trC k { cx with caps := [], sites := [], fnCaps := [] } [] false M
        pure ([], match V with
          | .thunk .. => .thunk sp M' | .thunkv .. => .thunkv sp M'
          | .bangThunk .. => .bangThunk sp M' | _ => .bangThunkv sp M')
    | V => pure ([], V)

/-- The value of a borrow block whose body hands back the capabilities `csM` beside its result:
the capabilities bound again after it; the block's value is `(place, result)` again. A block
whose body performs a control operation is bound before the value it is in, so that its
elaboration may make it a computation (an unwinding borrow, SPEC §19). -/
def blockResult : Nat → Cx → Span → Val → List Cap → EM (List Bind × Val)
  | 0, _, sp, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | _ + 1, _, sp, blk, csM => do
    let t ← fresh "fx_b"
    let pl ← fresh "fx_pl"
    let q ← fresh "fx_q"
    let r ← fresh "fx_v"
    if csM.isEmpty then
      let bind : Bind := .k fun N =>
        pure (.bind sp ⟨t, sp⟩ none (.ret sp blk) (.letPair sp ⟨pl, sp⟩ ⟨q, sp⟩ (.var sp t) N))
      return ([bind], .pair sp (.var sp pl) (.var sp q))
    let bind : Bind := .k fun N => do
      let rest ← unpack sp csM r q N
      pure (.bind sp ⟨t, sp⟩ none (.ret sp blk) (.letPair sp ⟨pl, sp⟩ ⟨q, sp⟩ (.var sp t) rest))
    pure ([bind], .pair sp (.var sp pl) (.var sp r))

/-- The call of member `j` through the function `g` of a self-reference, on `W` with the
environment: `f <- return unbang g; z <- return (); a <- return (E, W); (force f z).j a`. -/
def memberCall (sp : Span) (rs : RSelf) (j : Nat) (g f z a : String) (W : Val) : Comp :=
  .bind sp ⟨f, sp⟩ none (.ret sp (.mark sp (.selfCall j rs.members.length) (.unbang sp (.var sp g))))
    (.bind sp ⟨z, sp⟩ none (.ret sp (.unit sp))
      (.bind sp ⟨a, sp⟩ none (.ret sp (capsTuple sp rs.env W))
        (.app sp (projAt sp j rs.members.length (.app sp (.force sp ⟨f, sp⟩) ⟨z, sp⟩)) ⟨a, sp⟩)))

/-- `g(W)` of a member `g` of the recursive group whose generator is being elaborated (SPEC §20):
a direct call of the self-reference, `case self { inl _ ⇒ abort[e.0] () | inr f ⇒ (force f ()).j
(E, W) }`, `j` the member's field of the record the fixed point is taken at, and `E` the
environment, the capabilities the group threads, handed back beside the answer. When the budget
is spent (`self` is `inl ()`) it performs the exhaustion effect's operation. Bound before the value
it is in. -/
def selfCall : Nat → Cx → List Cap → Span → RSelf → String → Nat → Val → EM (List Bind × Val)
  | 0, _, _, sp, _, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, rs, x, j, W => do
    if rs.deep then
      let (b, W') ← goV k cx cs W
      report sp "call" s!"{x} → a request of the group's machine, driven by the heap driver"
      return (b, .app sp (.var sp s!"fx_rself{j}") W')
    -- A call of itself inside a handler of an effect its row performs: each level would need a
    -- copy whose sites are the level's own, without end (decision 57).
    let through (e : String) : Error :=
      ⟨sp, s!"`{x}` calls itself inside a handler of `{e}`, an effect its recursion " ++
        s!"performs: each level's `{e}` would go to the level's own handler, a site per level " ++
        "without end (recursion through a site, decision 57; generative labels, #173)"⟩
    for s₀ in rs.served do
      if let .ok s := cx.serve sp "" ⟨s₀.eff, some s₀.at, s₀.name⟩ (strict := false) then
        if s.n != s₀.n then throw (through s₀.eff)
    for c in rs.env do
      if let some c' := cx.capOf c.eff then
        if c'.h.key != c.h.key || c'.var != c.var then throw (through c.eff)
    noLend sp s!"`{x}`" W
    let (b, W') ← goArgs k cx cs W
    let t ← fresh "fx_b"
    let r ← fresh "fx_v"
    let u ← fresh "fx_u"
    let g ← fresh "fx_g"
    let f ← fresh "fx_f"
    let z ← fresh "fx_z"
    let a ← fresh "fx_a"
    let n := rs.members.length
    let C := (rs.Cs[j]?).getD (.top sp)
    let res : CTy := match C with
      | .arr _ _ R => R
      | C => C
    report sp "call" (s!"{x} → the group's self-reference, called directly" ++
      (if rs.env.isEmpty then "" else ", passing the capabilities") ++
      s!"; at the end of the budget abort[{rs.e}.0]")
    let call : Comp := .case sp (.var sp rs.self) ⟨u, sp⟩
      (.ascribe sp (.abort sp rs.e 0 (.unit sp)) res) ⟨g, sp⟩
      (memberCall sp rs j g f z a W')
    let bind : Bind := .caps sp t none call rs.env r false id
    pure (b ++ [bind], .var sp r)

/-- `k(W)` in a clause of an operation that resumes (SPEC §19): the continuation resumed,
`(force k).1 W`. In a handler with a state, its answer is a function of the state, applied to the
current state: the parameters are passed on, and the capabilities come back beside the answer. -/
def resumeCall : Nat → Cx → List Cap → Span → ResumeK → Val → EM (List Bind × Val)
  | 0, _, _, sp, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, rk, W => do
    let (b, W') ← goV k cx cs W
    let a ← fresh "fx_ka"
    let r ← fresh "fx_v"
    let res : Comp := .app sp (.proj sp true (.force sp ⟨rk.k, sp⟩)) ⟨a, sp⟩
    report sp "call" (s!"{rk.k} → the continuation resumed" ++
      (if rk.stateful then ", at the handler's state" else ""))
    if !rk.stateful then
      return (b ++ [.one sp a none (.ret sp W') false, .one sp r none res false], .var sp r)
    let g ← fresh "fx_kg"
    let sv ← fresh "fx_ks"
    let t ← fresh "fx_kt"
    let st : Val := capsTuple sp cx.caps (paramsTuple sp rk.params)
    let bind : List Bind := [.one sp a none (.ret sp W') false, .one sp g none res false,
      .one sp sv none (.ret sp st) false,
      .caps sp t none (.app sp (.force sp ⟨g, sp⟩) ⟨sv, sp⟩) cx.caps r false id]
    pure (b ++ bind, .var sp r)

/-- `call(W)` in a layer's body made for member `j` (SPEC §20): the member's call through the
self-reference, passing the environment and binding it again after. -/
def layerSelfCall : Nat → Cx → List Cap → Span → LCall → Val → EM (List Bind × Val)
  | 0, _, _, sp, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, lc, W => do
    noLend sp s!"`{lc.name}`" W
    let (b, W') ← goV k cx cs W
    let t ← fresh "fx_b"
    let r ← fresh "fx_v"
    let f ← fresh "fx_f"
    let z ← fresh "fx_z"
    let a ← fresh "fx_a"
    report sp "call" s!"{lc.name} → the member's call, through the self-reference"
    let bind : Bind := .caps sp t none (memberCall sp lc.rs lc.j lc.g f z a W') lc.rs.env r false id
    pure (b ++ [bind], .var sp r)

/-- A plain application, its parts elaborated. `return e` from a loop's body in a copy hands the
capabilities back too. -/
def plainApp : Nat → Cx → List Cap → Span → Val → Val → EM (List Bind × Val)
  | 0, _, _, sp, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, f, W => do
    if let .sugar _ .retE := f then
      let (b, W') ← goV k cx cs W
      return (b, .app sp f (capsTuple sp cx.fnCaps W'))
    let (b₁, f') ← goV k cx cs f
    let (b₂, W') ← goV k cx cs W
    pure (b₁ ++ b₂, .app sp f' W')

/-- `op(W)` of an answering effect: a call of the innermost handler's clause on the capability,
which hands it back. -/
def opCall : Nat → Cx → List Cap → Span → String → OpSig → Val → Option String →
    EM (List Bind × Val)
  | 0, _, _, sp, _, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, x, o, W, nm => do
    if (cx.capFor (cx.env.opInst o sp nm)).isNone && nm.isNone then
      throw ⟨sp, s!"the operation `{x}` of `{o.eff}` is performed here, but no handler of " ++
          s!"`{o.eff}` is in scope"⟩
    let c ← (cx.capAt sp s!"the operation `{x}`" (cx.env.opInst o sp nm) : Except Error Cap)
    noLend sp s!"the operation `{x}`" W
    let (b, W') ← goV k cx cs W
    let t ← fresh "fx_b"
    let r ← fresh "fx_v"
    if c.h.cell then
      -- The capability is the cell: the operation lends it to the clause (SPEC §34).
      let l ← fresh "fx_ol"
      let m ← fresh "fx_om"
      let q ← fresh "fx_oq"
      let m₂ ← fresh "fx_om"
      let call := Val.app sp (.var sp (clauseName c.h.name x)) (.pair sp (.var sp m) W')
      report sp "call" (s!"{x} ({o.eff}) → `{clauseName c.h.name x}`, on the cell `{c.var}` " ++
        "lent to it")
      let lc : Cap := { c with life := l, h := { c.h with cell := false } }
      -- The clause's answer is ascribed unless it names the operation's lifetime parameters,
      -- which the call instantiates.
      let ann := if o.decl.lives.isEmpty then some (capsTy sp [lc] o.decl.res) else none
      let inner : Comp := .bind sp ⟨q, sp⟩ ann (.ret sp call)
        (.letPair sp ⟨m₂, sp⟩ ⟨r, sp⟩ (.var sp q) (.ret sp (.var sp r)))
      let blk : Val := .app sp (.app sp (.sugar sp (.borrow .mut l)) (.var sp c.var))
        (.thunkv sp (.lam sp ⟨m, sp⟩ (holeTy sp) inner))
      let bind : Bind := .caps sp t none (.ret sp blk) [c] r false id
      return (b ++ [bind], .var sp r)
    let call := Val.app sp (.var sp (clauseName c.h.name x)) (.pair sp (.var sp c.var) W')
    report sp "call" (s!"{x} ({o.eff}) → `{clauseName c.h.name x}`, on the state of `{c.h.name}`" ++
      ((c.name.map (s!" named `{·}`")).getD ""))
    let bind : Bind := .caps sp t (if o.decl.lives.isEmpty then some (capsTy sp [c] o.decl.res) else none)
      (.ret sp call) [c] r false id
    pure (b ++ [bind], .var sp r)

/-- `op(W)` of a control effect: the kernel's operation, at the static name of the innermost site
of its effect, bound before the value it is in. -/
def ctlCall : Nat → Cx → List Cap → Span → String → OpSig → Val → Option String →
    EM (List Bind × Val)
  | 0, _, _, sp, _, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, x, o, W, nm => do
    let s ← (cx.serve sp s!"the operation `{x}`" (cx.env.opInst o sp nm) (strict := false) :
      Except Error Site)
    let (b, W') ← goV k cx cs W
    let r ← fresh "fx_v"
    let abortive := o.decl.abortive
    report sp "call" (s!"{x} ({o.eff}) → {if abortive then "abort" else "perform"}[{s.n}.{o.idx}], " ++
      s!"handled by {s.what} at {s.sp.start.render}" ++
      (if abortive then ": abortive, it never resumes" else ""))
    let bind : Bind := if abortive then
        -- What follows an abort does not run.
        .k fun _ => pure (.abort sp s.n o.idx W')
      else match s.thrVar with
        -- A `for`'s site threads its variable through the operation, which answers it again.
        | some w => threadedPerform sp s.n o.idx W' w
        | none => .one sp r none (.perform sp s.n o.idx W') false
    let v : Val := if abortive || s.thr.isSome then .unit sp else .var sp r
    pure (b ++ [bind], v)

/-- `f(W)` of a function with a row: a call of its copy for what serves its effects in scope,
which takes the capabilities first and hands them back first, bound before the value it is in. -/
def fnCall : Nat → Cx → List Cap → Span → Val → String → FSig → Val → EM (List Bind × Val)
  | 0, _, _, sp, _, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, f, x, g, W => do
    if cx.env.clashes.contains x then
      throw ⟨sp, s!"`{x}` is recursive and another function is named `{x}` too: a call of it is " ++
        "not provided (two modules may declare templates of one name, chosen by the arguments' " ++
        "types, only when none of them is recursive)"⟩
    let row := cx.rowAt sp g
    let used := cx.needIn row
    -- A named slot with no handler of its name here is reported where its copy is made.
    let named := row.any fun i => i.name.isSome && (cx.capFor i).isNone
    if used.isEmpty && (cx.ctl row).isEmpty && !named then return ← plainApp k cx cs sp f W
    noLend sp s!"`{x}`" W
    let (b, W') ← goV k cx cs W
    let name ← copyFor k cx sp x g row []
    let f' : Val := match f with
      | .defApp fsp _ As => .defApp fsp name As
      | _ => .var f.span name
    let t ← fresh "fx_b"
    let r ← fresh "fx_v"
    report sp "call" (s!"{x} → `{name}`" ++
      (if used.isEmpty then "" else ", passing the capabilities"))
    -- The binding is annotated when the result's type is known here, so that what follows is
    -- typed whatever the call's lifetimes.
    let ann := if used.isEmpty then none else (closedResult g.decl).map (capsTy sp used)
    -- When the result's type is not known here (a template's instance), the capabilities are
    -- bound again at their own types, which are.
    let N' (N : Comp) : Comp := if ann.isSome || used.isEmpty then N else
      used.foldr (fun c K => .bind sp ⟨c.var, sp⟩ (some (c.ty sp))
        (.ret sp (.var sp c.var)) K) N
    let bind : Bind := .caps sp t ann (.ret sp (.app sp f' (capsTuple sp used W'))) used r false N'
    pure (b ++ [bind], .var sp r)

/-- A call's arguments elaborated, a block parameter passed on as it is (SPEC §30). -/
def goArgs : Nat → Cx → List Cap → Val → EM (List Bind × Val)
  | 0, _, _, V => throw ⟨V.span, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, V => match V with
    | .var _ x => if (cx.cbs.lookup x).isSome then pure ([], V) else goV k cx cs V
    | .pair sp V W => do
      let (b₁, V') ← goArgs k cx cs V
      let (b₂, W') ← goArgs k cx cs W
      pure (b₁ ++ b₂, .pair sp V' W')
    | V => goV k cx cs V

/-- `f(W)` of a block parameter `f` of a copy made for effectful blocks (SPEC §30): a call of a value
whose type has the block's row, bound before the value it is in. -/
def blockParamCall : Nat → Cx → List Cap → Span → Val → String → List Site → List Cap → Val →
    EM (List Bind × Val)
  | 0, _, _, sp, _, _, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, f, x, ss, bcs, W => do
    -- A computation parameter's provided effects are served here by the site of its port
    -- (SPEC §33).
    for (y, p, _) in cx.ports do
      if y != x then continue
      match cx.siteOf p.eff with
      | some s =>
        unless s.n == p.n do
          throw ⟨sp, s!"`{x}` is called here, where `{p.eff}` is served by {s.what}, the site " ++
            s!"{s.n}, but it is called elsewhere where `{p.eff}` is served by the site {p.n}: the " ++
            "effect a computation parameter provides is served at one site of the function, until a port " ++
            "can be relabelled (SPEC §33 *Open*)"⟩
      | none => throw ⟨sp, s!"`{x}` performs `{p.eff}`, but no handler of `{p.eff}` is in scope here"⟩
    let (b, W') ← goV k cx cs W
    let r ← fresh "fx_v"
    let provd := (cx.ports.filter (·.1 == x)).map (·.2.1)
    let lexical := ss.filter fun s => !provd.any (·.n == s.n)
    report sp "call" (s!"{x} → the block" ++
      (if lexical.isEmpty then "" else s!", performing at {sitesText lexical}") ++
      (if provd.isEmpty then "" else s!", its {", ".intercalate (provd.map (s!"`{·.eff}`"))} " ++
        s!"served here by {sitesText provd}") ++
      (if bcs.isEmpty then "" else ", passing the capabilities"))
    if bcs.isEmpty then
      let bind : Bind := .one sp r none (.ret sp (.app sp f W')) false
      return (b ++ [bind], .var sp r)
    -- The capabilities the block uses are passed with the call and handed back (SPEC §32).
    let t ← fresh "fx_b"
    let bind : Bind := .caps sp t none (.ret sp (.app sp f (capsTuple sp bcs W'))) bcs r false id
    pure (b ++ [bind], .var sp r)

/-- `g(W)` passing effectful blocks `blks` (SPEC §30): each block written here is elaborated where
it is written, its operations resolved to the sites around it; the call is a call of `g`'s copy at
the blocks' rows (and for what serves `g`'s own row), bound before the value it is in. -/
def blockCall : Nat → Cx → List Cap → Span → Val → String → FSig → Val → List Blk →
    EM (List Bind × Val)
  | 0, _, _, sp, _, _, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, f, x, g, W, blks => do
    noLend sp s!"`{x}`" W
    let some P := (cx.env.sigs.lookup x).bind paramTyOf
      | throw ⟨sp, s!"internal error: the parameters of `{x}`"⟩
    -- At a computation parameter, the copy names the ports the block performs its provided
    -- effects at: the copy is made first (SPEC §33).
    let early := blks.any (!·.prov.isEmpty)
    let row := cx.rowAt sp g
    let name₀ ← if early then copyFor k cx sp x g row blks else pure ""
    let stP ← get
    let ports : List (Nat × List (Site × Bool)) := if early then ((stP.ports.lookup name₀).getD []) else []
    let mut bs : List Bind := []
    let mut vs : List Val := []
    for ((_, V₀), j) in (argComps fuel P W).zipIdx do
      if let some blk := blks.find? (·.j == j) then
        let V := (stripWrites V₀).2
        -- A block sees the sites where it is written, and the capabilities it uses, which it takes
        -- first and hands back first (SPEC §32); at a computation parameter, the ports of what
        -- the callee provides (SPEC §33).
        let pss := ((ports.lookup j).getD []).map (·.1)
        let cxB : Cx := { cx with caps := blk.caps, fnCaps := [],
                                  sites := pss ++ cx.sites.filter fun s =>
                                    !pss.any fun p => p.eff == s.eff && cx.env.sameArgs p.args s.at }
        let body (M : Comp) : EM Comp := do
          if blk.caps.isEmpty then return ← trC k cxB [] false M
          match M with
          | .lam lsp y _ M₀ =>
            let pp ← fresh "fx_pp"
            let M₀' ← trC k cxB blk.caps true M₀
            pure (.lam lsp ⟨pp, lsp⟩ (holeTy lsp) (← unpack lsp blk.caps y.name pp M₀'))
          | M => throw ⟨M.span, "internal error: a block that uses a capability is not a function"⟩
        match V with
        | .thunkv tsp M => vs := vs ++ [.thunkv tsp (← body M)]
        | .bangThunkv tsp M => vs := vs ++ [.bangThunkv tsp (← body M)]
        | V => vs := vs ++ [V]
      else
        let (b, V') ← goV k cx cs V₀
        bs := bs ++ b
        vs := vs ++ [V']
    let rec tuple : List Val → Val
      | [] => W
      | [V] => V
      | V :: Vs => .pair V.span V (tuple Vs)
    let W' := tuple vs
    let used := addCaps (cx.needIn row) (blkCaps blks)
    let name ← if early then pure name₀ else copyFor k cx sp x g row blks
    -- A copy that takes `let mut` variables is generic in their types too, which the call's
    -- arguments give: its type arguments are all inferred.
    let f' : Val := match f with
      | .defApp fsp _ As => if (blkCaps blks).any (·.isMut) then .var f.span name else .defApp fsp name As
      | _ => .var f.span name
    let t ← fresh "fx_b"
    let r ← fresh "fx_v"
    let blkT := blks.map fun b =>
      let ps := (ports.lookup b.j).getD []
      if ps.isEmpty then "its block " ++ blockText b.ss b.caps
      else "its computation performing " ++ ", ".intercalate (
        (if b.ss.isEmpty && b.caps.isEmpty then [] else [blockText b.ss b.caps]) ++
        ps.map fun (p, _) => s!"`{p.eff}` at the port {p.n} of `{x}`")
    report sp "call" (s!"{x} → `{name}`, " ++ ", ".intercalate blkT ++
      (if used.isEmpty then "" else ", passing the capabilities"))
    -- A `let mut` variable's type is a parameter of the copy, known where it is bound.
    let typed := used.filter (!·.isMut)
    let ann := if used.isEmpty || typed.length != used.length then none
      else (closedResult g.decl).map (capsTy sp used)
    let N' (N : Comp) : Comp := if ann.isSome || typed.isEmpty then N else
      typed.foldr (fun c K => .bind sp ⟨c.var, sp⟩ (some (c.ty sp))
        (.ret sp (.var sp c.var)) K) N
    let bind : Bind := .caps sp t ann (.ret sp (.app sp f' (capsTuple sp used W'))) used r false N'
    pure (bs ++ [bind], .var sp r)

/-- `with h(P) { 'l, c -> M }` of an answering handler: a borrow block of the state's cell whose
callback's parameter `c` is the capability. -/
def withBlk : Nat → Cx → List Cap → Span → Span → Span → HSig → String → Val → Span → Span →
    Ident → VTy → Comp → Option String → EM (List Bind × Val)
  | 0, _, _, sp, _, _, _, _, _, _, _, _, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, sp₂, ksp, hs, l, P, tsp, lsp, b, A, M, nm => do
    let (bsP, P') ← goV k cx cs P
    let place ← match P' with
      | .lend _ x .mut => pure (Val.var x.span x.name)
      | .lend lsp' _ .imm => throw ⟨lsp', "a handler's state is lent `&mut`"⟩
      | V => pure (.app V.span (.sugar V.span (.call "alloc")) V)
    let cap : Cap := ⟨hs.eff, b.name, l, hs, none, false, nm, false⟩
    -- An enclosing handler of the effect stays reachable by its name (SPEC §38).
    let cx' : Cx := { cx with caps := cap :: cx.caps.filter (fun c => c.blk || c.eff != hs.eff ||
      (c.name.isSome && c.name != nm)) }
    let csM := cx'.needC M
    let outer := csM.filter (·.var != cap.var)
    let where_ := match P' with
      | .lend _ x _ => s!"lent from `{x.name}`"
      | _ => "in a cell scoped to the block"
    report ksp "lowering" (s!"with {((nm.map (· ++ " = ")).getD "")}{hs.name} ({hs.eff}): a borrow block of its state ({where_}); its " ++
      "operations are calls of the clauses on the capability")
    -- The body hands back the enclosing capabilities it uses; its own is dropped at its end.
    let body ← trC k cx' outer true M
    let blk := Val.app sp (.app sp₂ (.sugar ksp (.borrow .mut l)) place)
      (.thunkv tsp (.lam lsp b A body))
    -- The block answers its result alone, the scoped cell dropped, unless it is lent from a
    -- place or hands back the variables its body assigns (`Val.rebinds`).
    let alone := (match P' with | .lend .. => false | _ => true) && !M.boundNames.contains "io_bt"
    if outer.isEmpty && !cx.ctlC M && !alone then return (bsP, blk)
    let (bs, V') ← blockResult k cx sp blk outer
    match alone, V' with
    | true, .pair _ _ r => pure (bsP ++ bs, r)
    | _, _ => pure (bsP ++ bs, V')

/-- `with h[As](P) { M }` of a control handler: a handler site with a static name of its own. The
handled effect's type arguments are the ones written, or the ones the body performs; the
handler's own row is resolved to the sites around the `with`. The site is assembled with its
clauses where the types are known (`VSugar.hndCtl`). -/
def withCtl : Nat → Cx → List Cap → Span → Span → CHandler → List VTy → Val → Comp →
    Option String → EM (List Bind × Val)
  | 0, _, _, sp, _, _, _, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, ksp, ch, As, P, M, nm => do
    let tps := ch.tps.map (·.name)
    let e := ch.eff.name
    -- The handler's clauses are elaborated in its own frame (SPEC §38).
    let envH : Env := { cx.env with owner := Instances.ownerKey ch.name.name ch.name.span,
                                    ownerTps := tps }
    if M.boundNames.contains "io_bt" then
      throw ⟨ksp, s!"the body of `with {ch.name.name}` assigns a `let mut` variable declared " ++
        "outside it, or lends a place declared outside it: a control handler's body may be " ++
        "abandoned, and does not hand them back; bind what the block answers instead"⟩
    let some eff := cx.env.eff? e | throw ⟨ksp, s!"internal error: the effect `{e}`"⟩
    -- A clause that takes its continuation out of a box receives it boxed (BOXED-κ, SPEC §28):
    -- it keeps the continuation in what it answers, a stored task.
    let boxK := eff.ops.any fun o => !o.abortive && ch.clauses.any fun c =>
      c.name.name == o.name.name && !c.params.isEmpty && unboxesC c.params.getLast!.name fuel c.body
    -- The capabilities the body uses are reborrowed for it, each at a lifetime of its own, so that
    -- they come back when the body is abandoned. A body whose continuation the clauses keep boxed
    -- at the handler's lifetime (a task of `spawn_in`) outlives the `with`: it is given the
    -- capabilities it uses, which go with the task (SPEC §34).
    let given := boxK && !ch.lps.isEmpty
    let mut csM : List Cap := []
    for c in cx.needC M do
      if c.thr.isSome then
        throw ⟨ksp, s!"the body of `with {ch.name.name}` performs `{c.eff}` of an enclosing `for`, " ++
          "which threads its variables through the operation: a control handler's body may be " ++
          "abandoned, and does not hand them back; not provided"⟩
      if given && c.h.cell then
        throw ⟨ksp, s!"the task spawned here is given the capability of `{c.eff}`, which it holds " ++
          "across its suspensions: spawn it inside a borrow block, which lends the capability for " ++
          "the tasks it bounds (SPEC §34)"⟩
      if given then
        report ksp "lowering" (s!"with {ch.name.name}: its body is given the capability of `{c.eff}`, " ++
          "which goes with the task it answers")
      else
        -- A cell is lent for the body: the body has the borrow (SPEC §34).
        csM := csM ++ [{ c with life := ← fresh "fx_rl", h := { c.h with cell := false } }]
    -- A computation parameter's argument takes its capabilities at the copy's lifetimes: one
    -- called in a body that is lent them anew cannot be given them (SPEC §33 *Open*).
    for (x, _, bcs) in cx.cbs do
      if !cx.ports.any (·.1 == x) then continue
      if let some c := bcs.find? (·.thr.isNone) then
        if (refsC fuel M).contains x && csM.any (·.eff == c.eff) then
          throw ⟨ksp, s!"the computation parameter `{x}` uses the capability of `{c.eff}` and is " ++
            s!"called inside `with {ch.name.name}`, whose body is lent the capability anew: not " ++
            "provided (SPEC §33 *Open*)"⟩
    -- Written type arguments, in the order of the handler's type parameters.
    if As.length > tps.length then
      throw ⟨ksp, s!"`{ch.name.name}` takes {tps.length} type argument(s)"⟩
    let mut σ : TySubst := tps.zip As
    -- The handled effect's type arguments from what the body performs. Its static name is its
    -- own, or the port of the computation parameters whose calls it serves (SPEC §33).
    let n ← match ← (cx.portIn ksp ch.name.name e M : Except Error _) with
      | some p => pure p
      | none => freshSite
    -- The instance it handles: at the written type arguments; else the one instance of its effect
    -- the body performs, unnamed or named as this handler (SPEC §38).
    if !(ch.effArgs.all (solvedBy tps σ)) then
      let mine := (rowC cx.env fuel M).filter fun j => j.eff == e && (j.name.isNone || j.name == nm)
      let known := mine.filterMap (·.args)
      if let some Bs := known.head? then
        if let some Cs := known.find? (!cx.env.sameArgs Bs ·) then
          throw ⟨ksp, s!"the body of `with {ch.name.name}` performs {instText e Bs} and {instText e Cs}: " ++
            s!"write the type arguments of the instance it handles, `with {ch.name.name}[…]`, or name " ++
            "the handler of the other (SPEC §38)"⟩
        unless Bs.length == ch.effArgs.length do
          throw ⟨ksp, s!"internal error: `{e}`'s type arguments"⟩
        for (Pt, B) in ch.effArgs.zip Bs do
          match matchTy tps σ Pt B with
          | some σ' => σ := σ'
          | none => throw ⟨ksp, s!"`with {ch.name.name}` handles `{e}[{", ".intercalate
              (ch.effArgs.map (VTy.pp · 0))}]`, but its body performs `{e}[{", ".intercalate
              (Bs.map (VTy.pp · 0))}]`"⟩
    -- The handler's own row, at the sites around the `with`: each entry served by the innermost
    -- handler of its instance there.
    let mut outer : List Site := []
    for (e₂, Ps) in ch.row do
      unless (cx.siteOf e₂.name).isSome do
        throw ⟨ksp, s!"`{ch.name.name}` performs `{e₂.name}`, and no handler of `{e₂.name}` is " ++
            "in scope at this `with`"⟩
      let Ps' := Ps.map (·.subst σ)
      let s ← (cx.serve ksp s!"`{ch.name.name}`"
        ⟨e₂.name, if Ps.all (solvedBy tps σ) then some Ps' else none, none⟩ (strict := false) :
        Except Error Site)
      for (Pt, B) in Ps.zip s.args do
        match matchTy tps σ Pt B with
        | some σ' => σ := σ'
        | none => throw ⟨ksp, s!"`{ch.name.name}` performs `{e₂.name}` at a type other than the " ++
            s!"handler of `{e₂.name}` in scope here"⟩
      outer := outer ++ [s]
    -- The clauses see the sites of the handler's row as the entries they serve, at the handler's
    -- own types (SPEC §38).
    let outerR : List Site := (outer.zip ch.row).map fun (s, (_, Ps)) => { s with slot := some Ps, name := none }
    let effArgs := ch.effArgs.map (·.subst σ)
    if !(ch.effArgs.all (solvedBy tps σ)) then
      throw ⟨ksp, s!"the type arguments of `{e}` at this `with` are not determined: write them, " ++
        s!"`with {ch.name.name}[{", ".intercalate tps}](…)`"⟩
    let site : Site := { eff := e, n, args := effArgs, sp := ksp, name := nm,
                         what := s!"`with {((nm.map (· ++ " = ")).getD "")}{ch.name.name}`" }
    let ents := cx.env.siteOps site
    -- `main`'s handler of a division's error is reported by `divMain`, as the platform's handlers
    -- of the system interface are by `platformMain`.
    let plat := ch.name.name == mainDivHandler
    quietIf plat <| reportSite ksp n s!"with {ch.name.name} ({e}): a handler, the static name {n}"
      ((((cx.env.eff? e).map (·.ops)).getD []).map (·.name.name))
      (if boxK then "; the clauses receive the continuation boxed at " ++
        (match ch.lps.head? with
          | some (a, _) => s!"its lifetime `'{a.name}`, the meet of the lifetimes in scope here"
          | none => "`top`") ++ " (BOXED-κ), so what they answer may keep it" else "")
    -- The body, with this site innermost for `e`.
    let cxB : Cx := { cx with sites := site :: cx.sites,
                              caps := cx.caps.map fun c => (csM.find? (·.var == c.var)).getD c }
    let M' ← trC k cxB [] false M
    let (rx, rA, rM) := ch.ret
    for c in ch.clauses do
      unless eff.ops.any (·.name.name == c.name.name) do
        throw ⟨c.name.span, s!"`{c.name.name}` is not an operation of `{e}`"⟩
    let rest := tps.filter fun x => (σ.lookup x).isNone
    -- The handler's type parameters the site leaves open are named apart from the enclosing
    -- function's, so that instantiating a template cannot capture them (SPEC §38).
    let ren : TySubst := rest.filterMap fun x =>
      if cx.env.ownerTps.contains x then some (x, .name sp (x ++ "'")) else none
    let σr : TySubst := σ ++ ren
    let rest := rest.map fun x => if (ren.lookup x).isSome then x ++ "'" else x
    -- Every operation abortive: each clause runs at most once and never resumes, so the clauses
    -- run after the handler (SPEC §19, *Abortive clauses*). The site answers the body's value
    -- `inl x` or an operation's argument `inr (inj_i v)`, and a `case` on that runs the return
    -- clause or the operation's, in the scope of the `with`: they use the handler's arguments,
    -- whatever their types, and the capabilities in scope, as any code there does.
    if !eff.ops.isEmpty && eff.ops.all (·.abortive) then
      let nOps := eff.ops.length
      let pay := sumTys sp (ents.map (·.2.1))
      let p ← fresh "fx_p"
      let injCls : List Val := (List.range nOps).map fun j =>
        .thunkv sp (.lam sp ⟨p, sp⟩ (holeTy sp) (.ret sp (.inr sp (injAt sp j nOps (.var sp p)))))
      let xr ← fresh "fx_ax"
      -- The site binds the handler's arguments to its parameters before the body runs, and answers
      -- them beside its own answer, for the clauses after it.
      let info : HInfo := ⟨ch.name.name, n, ents, rest, σ,
        ch.params.map (fun (x, A) => (x.name, A.subst σr)), rA.subst σr, .sum sp (rA.subst σr) pay,
        some (ch.res.subst σr), false, ch.lps.map (·.1.name),
        { n, eff := e, args := effArgs, handler := ch.name.name, slot := nm, ents }⟩
      let clsV := injCls.foldr (fun c t => Val.pair sp c t) (.unit sp)
      let (bsP, P') ← goV k cx cs P
      let hnd : Val := .app sp (.app sp (.app sp (.app sp (.sugar ksp (.hndCtl info)) P')
        (.thunkv sp (.lam sp ⟨xr, sp⟩ rA (.ret sp (.inl sp (.var sp xr)))))) clsV) (.thunk sp M')
      let (bsH, hv) ← reborrowed k sp ksp hnd csM
      let rn ← fresh "fx_ar"
      let pv ← fresh "fx_hp"
      let rv : Val := .var sp rn
      let params : Bind := .k fun N => do
        pure (.bind sp ⟨pv, sp⟩ none (.ret sp hv)
          (← bindParams sp pv (ch.params.map (·.1) ++ [⟨rn, sp⟩]) N))
      -- The clauses, after the handler.
      let ev ← fresh "fx_ae"
      let mut arms : List (String × Comp) := []
      for o in eff.ops do
        let some c := ch.clauses.find? (·.name.name == o.name.name)
          | throw ⟨ch.name.span, s!"the handler `{ch.name.name}` has no clause for `{o.name.name}`"⟩
        unless c.params.length == o.params.length do
          throw ⟨c.name.span, s!"the clause `{c.name.name}` of `{ch.name.name}` takes " ++
            s!"{o.params.length} name(s): the operation's parameters"⟩
        let q ← fresh "fx_aq"
        arms := arms ++ [(q, ← bindParams c.name.span q c.params (c.body.subst σr))]
      let rec dispatch : Nat → String → List (String × Comp) → Comp
        | _, v, [(q, N)] => .bind sp ⟨q, sp⟩ none (.ret sp (.var sp v)) N
        | m + 1, v, (q, N) :: rest =>
          let y := v ++ "r"
          .case sp (.var sp v) ⟨q, sp⟩ N ⟨y, sp⟩ (dispatch m y rest)
        | _, v, _ => .absurd sp (.var sp v)
      let after : Comp := .case sp rv rx (rM.subst σr) ⟨ev, sp⟩ (dispatch (nOps + 1) ev arms)
      -- Its operations are the handler's row's, at the sites around the `with`.
      let cxA : Cx := { cx with env := envH,
                                sites := outerR ++ cx.sites.filter fun s => !outer.any (·.eff == s.eff) }
      let csA := cxA.needC after
      let after' ← quietIf plat (trC k cxA csA true after)
      let t ← fresh "fx_b"
      let r ← fresh "fx_v"
      quietIf plat <| report ksp "lowering" (s!"with {ch.name.name}: every operation abortive, so its clauses run " ++
        "after the handler, in the scope of the `with`")
      -- Its type is the handler's answer, which the typed elaboration names `fx_res{n}`.
      let resT : VTy := capsTy sp csA (.name sp s!"fx_res{n}")
      let bind : Bind := .caps sp t (some resT) after' csA r true id
      return (bsP ++ bsH ++ [params, bind], .var sp r)
    -- The capabilities the clauses use: the handler holds them between operations, in its state.
    let csCl := cx.need (ch.clauses.foldl (fun r c => envH.union r (rowC envH fuel c.body))
      (rowC envH fuel rM))
    if let some c := csCl.find? (fun c => csM.any (·.var == c.var)) then
      throw ⟨ksp, s!"the body of `with {ch.name.name}` and its clauses both use the capability of " ++
        s!"`{c.eff}`: the handler holds it between operations, so the body cannot (not provided)"⟩
    if let some c := csCl.find? (·.thr.isSome) then
      throw ⟨ksp, s!"the clauses of `with {ch.name.name}` perform `{c.eff}` of an enclosing `for`: " ++
        "not provided"⟩
    -- A handler with a state (SPEC §19, *Handler state*): a parameter that is not `!`, or a
    -- capability its clauses use. Its clauses run at each operation, so what they use is passed to
    -- them: the site answers a function of the state, `U (S' ⊗ P ⊸ F (S' ⊗ R))`, each clause and
    -- the return clause a thunk of it, and a resume `k(v)` applies the continuation's answer to the
    -- current state. The state is the capabilities `S'` and the parameters `P`: a resume passes the
    -- parameters on, and the capabilities come back with the answer.
    let stateful := !csCl.isEmpty || ch.params.any fun (_, A) => !(match A with | .bang .. => true | _ => false)
    if stateful && boxK then
      throw ⟨ksp, s!"a clause of `{ch.name.name}` keeps its continuation boxed, and the handler has a " ++
        "state (a parameter that is not `!`, or a capability its clauses use): not provided"⟩
    if stateful then
      let pNames := ch.params.map (·.1.name)
      let Pt : VTy := tupleTy sp (ch.params.map fun (_, A) => A.subst σr)
      let Rv := ch.res.subst σr
      let St : VTy := capsTy sp csCl Pt
      -- The function of the state runs where the `with` is, and resumes or cancels the
      -- continuation there, whose row is the row at the `with` (`[handle]`, SPEC §19): its row is
      -- the handler's own row and every other site in scope (#514).
      let others := (cx.sites.foldl (fun acc s => if acc.any (·.n == s.n) then acc else acc ++ [s]) []).filter
        fun s => !outer.any (·.n == s.n)
      let rowO := cx.env.rowOf (outer ++ others)
      let Ans : VTy := capsTy sp csCl Rv
      let ansT : VTy := .thunk sp (.arr sp St (match rowO with
        | .nil => .ret sp Ans
        | r => .eff sp r Ans))
      let cxS (rk : Option ResumeK) : Cx := { env := envH, caps := csCl, sites := outerR, resume := rk }
      let stThunk (body : Comp) : EM Val := do
        let sv ← fresh "fx_hs"
        let ps ← fresh "fx_hq"
        let inner ← unpack sp csCl ps sv (← bindParams sp ps (ch.params.map (·.1)) body)
        pure (.thunkv sp (.lam sp ⟨sv, sp⟩ St inner))
      let rM' ← trC k (cxS none) csCl true (rM.subst σr)
      let hr : Val := .thunkv sp (.lam sp rx rA (.ret sp (← stThunk rM')))
      let mut cls : List Val := []
      for o in eff.ops do
        let some c := ch.clauses.find? (·.name.name == o.name.name)
          | throw ⟨ch.name.span, s!"the handler `{ch.name.name}` has no clause for `{o.name.name}`"⟩
        let abortive := o.abortive
        let want := o.params.length + (if abortive then 0 else 1)
        unless c.params.length == want do
          throw ⟨c.name.span, s!"the clause `{c.name.name}` of `{ch.name.name}` takes {want} " ++
            s!"name(s): the operation's parameters{if abortive then "" else ", then its continuation"}"⟩
        let csp := c.name.span
        let p ← fresh "fx_p"
        let kv := c.params.getLast!
        let rk : Option ResumeK := if abortive then none else some ⟨kv.name, pNames, true⟩
        let body ← trC k (cxS rk) csCl true (c.body.subst σr)
        let th : Comp := .ret csp (← stThunk body)
        let body ← if abortive then bindParams csp p c.params th else do
          let q ← fresh "fx_q"
          pure (.letPair csp ⟨q, csp⟩ kv (.var csp p) (← bindParams csp q c.params.dropLast th))
        cls := cls ++ [.thunkv csp (.lam csp ⟨p, csp⟩ (holeTy csp) body)]
      let info : HInfo := ⟨ch.name.name, n, ents, rest, σ, [], rA.subst σr, ansT, none, false,
        ch.lps.map (·.1.name),
        { n, eff := e, args := effArgs, handler := ch.name.name, slot := nm, ents,
          state := ch.params.map fun (x, A) => (x.name, A.subst σr) }⟩
      let (bsP, P') ← goV k cx cs P
      let pv ← fresh "fx_hp"
      let args : Bind := .one sp pv none (.ret sp P') false
      let clsV := cls.foldr (fun c t => Val.pair sp c t) (.unit sp)
      let hnd : Val := .app sp (.app sp (.app sp (.app sp (.sugar ksp (.hndCtl info)) (.unit sp))
        hr) clsV) (.thunk sp M')
      let (bsH, gv) ← reborrowed k sp ksp hnd csM
      -- The site's answer applied to the initial state; the capabilities bound again after.
      let g ← fresh "fx_hg"; let sv ← fresh "fx_hs"; let t ← fresh "fx_ht"
      let r ← fresh "fx_v"
      let run : List Bind := [.one sp g none (.ret sp gv) false,
        .one sp sv none (.ret sp (capsTuple sp csCl (.var sp pv))) false,
        .caps sp t none (.app sp (.force sp ⟨g, sp⟩) ⟨sv, sp⟩) csCl r false id]
      report ksp "lowering" (s!"with {ch.name.name}: a handler with a state, its parameters" ++
        (if csCl.isEmpty then "" else " and the capabilities its clauses use") ++
        ", passed to each clause and to the continuation at each resume")
      return (bsP ++ [args] ++ bsH ++ run, .var sp r)
    -- The clauses run outside the handler: their operations go to the sites of the handler's row.
    let cxH : Cx := { env := envH, caps := [], sites := outerR }
    let rM' ← trC k cxH [] false (rM.subst σr)
    let mut cls : List Val := []
    for o in eff.ops do
      let some c := ch.clauses.find? (·.name.name == o.name.name)
        | throw ⟨ch.name.span, s!"the handler `{ch.name.name}` has no clause for `{o.name.name}`"⟩
      let abortive := o.abortive
      let want := o.params.length + (if abortive then 0 else 1)
      unless c.params.length == want do
        throw ⟨c.name.span, s!"the clause `{c.name.name}` of `{ch.name.name}` takes {want} " ++
          s!"name(s): the operation's parameters{if abortive then "" else ", then its continuation"}"⟩
      let rk : Option ResumeK := if abortive then none else some ⟨c.params.getLast!.name, [], false⟩
      let body ← trC k { cxH with resume := rk } [] false (c.body.subst σr)
      let csp := c.name.span
      let p ← fresh "fx_p"
      let body ← if abortive then bindParams csp p c.params body else do
        let xs := c.params.dropLast
        let kv := c.params.getLast!
        let q ← fresh "fx_q"
        pure (.letPair csp ⟨q, csp⟩ kv (.var csp p) (← bindParams csp q xs body))
      cls := cls ++ [.thunkv csp (.lam csp ⟨p, csp⟩ (holeTy csp) body)]
    let info₀ : HInfo := ⟨ch.name.name, n, ents, rest, σ,
      ch.params.map fun (x, A) => (x.name, A.subst σr), rA.subst σr, ch.res.subst σr, none, false, [],
      { n, eff := e, args := effArgs, handler := ch.name.name, slot := nm, ents }⟩
    let info : HInfo := { info₀ with boxK := boxK, lives := ch.lps.map (·.1.name) }
    let (bsP, P') ← goV k cx cs P
    let clsV := cls.foldr (fun c t => Val.pair sp c t) (.unit sp)
    let hnd : Val := .app sp (.app sp (.app sp (.app sp (.sugar ksp (.hndCtl info)) P')
      (.thunkv sp (.lam sp rx rA rM'))) clsV) (.thunk sp M')
    let (bsH, rv) ← reborrowed k sp ksp hnd csM
    pure (bsP ++ bsH, rv)

/-- The handler site `hnd` bound before the value it is in, inside `borrow mut c { 'l, c -> … }`
for each capability `c` of `csM` its body uses, innermost last (`withCtl`): each block hands the
capability back beside the result, and the capabilities are bound again after it. -/
def reborrowed : Nat → Span → Span → Val → List Cap → EM (List Bind × Val)
  | 0, sp, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | _ + 1, sp, ksp, hnd, csM => do
    let r ← fresh "fx_v"
    if csM.isEmpty then
      let bind : Bind := .one sp r none (.ret sp hnd) false
      return ([bind], .var sp r)
    let mut blk : Comp := .ret sp hnd
    for c in csM.reverse do
      let l := c.life
      let t ← fresh "fx_rb"
      let inner : Comp := .bind sp ⟨t, sp⟩ none blk (.ret sp (.var sp t))
      blk := .ret sp (.app sp (.app sp (.sugar ksp (.borrow .mut l)) (.var sp c.var))
        (.thunkv sp (.lam sp ⟨c.var, sp⟩ (holeTy sp) inner)))
    let bind : Bind := .k fun N => do
      -- The capabilities bound again from the nested pairs `(c₁, (c₂, … r))`.
      let rec unwrap : List Cap → String → Comp → EM Comp
        | [], v, K => pure (.bind sp ⟨r, sp⟩ none (.ret sp (.var sp v)) K)
        | c :: cs, v, K => do
          let w ← fresh "fx_rw"
          pure (.letPair sp ⟨c.var, sp⟩ ⟨w, sp⟩ (.var sp v) (← unwrap cs w K))
      let t ← fresh "fx_rt"
      match blk with
      | .ret _ V => pure (.bind sp ⟨t, sp⟩ none (.ret sp V) (← unwrap csM t N))
      | B => pure (.bind sp ⟨t, sp⟩ none B (← unwrap csM t N))
    pure ([bind], .var sp r)

/-- `for x in g(W) { M }; N`, `g` performing the iteration effect `i` (SPEC §15): a handler site
of its own for `i`, whose operation threads a variable `w` (the copy of `g` for the site takes it
first and hands it back first, and `op(v)` is `w <- perform[n.0] (v, w)` in it). The site is
assembled where the types are known (`VSugar.forSite`): `w` is then the tuple of the variables the
body reads or assigns, and the body is the operation's clause. The body runs outside the site:
its operations go to the sites around the `for`. -/
def forSite : Nat → Cx → List Cap → Bool → Span → Option Ident → Ident → String → FSig → Inst →
    Val → Val → Comp → Comp → EM Comp
  | 0, _, _, _, sp, _, _, _, _, _, _, _, _, _ => throw ⟨sp, "internal error: a body nested too deeply"⟩
  | k + 1, cx, cs, wrap, sp, ℓ, x, gname, g, i, f, W, M, N => do
    let some As := i.args
      | throw ⟨sp, s!"`{gname}` performs `{i.eff}`, and its type arguments are not determined: " ++
          s!"write them, `with {i.eff}[…]`"⟩
    if let some c := (cx.need (without g.row i.eff)).head? then
      throw ⟨sp, s!"`{gname}` uses the capability of `{c.eff}`: a `for` over a function that " ++
        "performs an iteration effect and uses a capability is not provided"⟩
    let n ← freshSite
    modify fun s => { s with perTurn := n :: s.perTurn }
    let w := s!"fx_w{n}"
    let Wn := s!"fx_W{n}"
    let site : Site := { eff := i.eff, n, args := As, sp, what := "the `for`", thr := some (w, Wn) }
    let tcap := threadCap sp i.eff w Wn
    let cxF : Cx := { cx with sites := site :: cx.sites.filter (·.eff != i.eff),
                              caps := tcap :: cx.caps.filter (fun c => c.blk || c.eff != i.eff) }
    let (bP, W) ← pullArgsV k cx cs gname W
    let (bs, W') ← trV k cx cs W
    let bs := bP ++ bs
    let name ← copyFor k cxF sp gname g (cx.rowOf g) []
    let f' : Val := match f with
      | .defApp fsp _ Ts => .defApp fsp name Ts
      | _ => .var f.span name
    let T := match (cx.env.siteOps { site with thr := none }).head? with
      | some (_, A, _) => A
      | none => .unit sp
    let opName := (((cx.env.eff? i.eff).map (·.ops)).getD [] |>.head?.map (·.name.name)).getD "?"
    let siteR : SiteRec := { n, eff := i.eff, args := As, handler := gname, kind := .forSite,
                             ents := cx.env.siteOps { site with thr := none } }
    reportSite sp n s!"for over {gname} ({i.eff}): a handler, the static name {n}" [opName]
      ("; the body is its clause, the variables the body uses threaded through the operation; " ++
        "`break` and `return` cancel the continuation")
    report sp "call" s!"{gname} → `{name}`, threading the `for`'s variables"
    let M' ← trC k cx [] false M
    let N' ← trC k cx cs wrap N
    let call := Val.app sp f' (capsTuple sp [tcap] W')
    chain bs (.loop sp ℓ (.each x) (.app sp (.sugar sp (.forSite ⟨n, T, w, gname, siteR⟩)) call) M' N')

/-- The stored generator of `g(W)`, `g` performing the iteration effect `i` (SPEC §15): a handler
site of its own for `i`, assembled where the types are known (`VSugar.pullSite`), whose clause
keeps the continuation as the rest of the stored generator. -/
def pullSite : Nat → Cx → List Cap → Span → String → FSig → Inst → Val → Val →
    EM (List Bind × Val)
  | 0, _, _, sp, _, _, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, gname, g, i, f, W => do
    let some As := i.args
      | throw ⟨sp, s!"`{gname}` performs `{i.eff}`, and its type arguments are not determined: " ++
          s!"write them, `with {i.eff}[…]`"⟩
    if let some c := (cx.need (without g.row i.eff)).head? then
      throw ⟨sp, s!"`{gname}` uses the capability of `{c.eff}`: its stored generator would hold " ++
        "the capability, which is not provided"⟩
    let n ← freshSite
    modify fun s => { s with perTurn := n :: s.perTurn }
    let site : Site := { eff := i.eff, n, args := As, sp, what := "the stored generator" }
    let cxP : Cx := { cx with sites := site :: cx.sites.filter (·.eff != i.eff),
                              caps := cx.caps.filter (fun c => c.blk || c.eff != i.eff) }
    let (bP, W) ← pullArgsV k cx cs gname W
    let (bs, W') ← goV k cx cs W
    let bs := bP ++ bs
    let name ← copyFor k cxP sp gname g (cx.rowOf g) []
    let f' : Val := match f with
      | .defApp fsp _ Ts => .defApp fsp name Ts
      | _ => .var f.span name
    let T := match (cx.env.siteOps site).head? with
      | some (_, A, _) => A
      | none => .unit sp
    let opName := (((cx.env.eff? i.eff).map (·.ops)).getD [] |>.head?.map (·.name.name)).getD "?"
    let siteR : SiteRec := { n, eff := i.eff, args := As, handler := gname, kind := .pullSite,
                             ents := cx.env.siteOps site }
    reportSite sp n s!"stored generator of {gname} ({i.eff}): a handler, the static name {n}" [opName]
      ("; its clause keeps the continuation as the rest, resumed by the next observation and " ++
        "cancelled by `close`")
    report sp "call" s!"{gname} → `{name}`, stored"
    -- Bound before the value it is in: making the stored generator is a computation.
    let v ← fresh "fx_g"
    let pv : Val := .app sp (.sugar sp (.pullSite ⟨n, T, "", gname, siteR⟩)) (.app sp f' W')
    let bind : Bind := .one sp v none (.ret sp pv) false
    pure (bs ++ [bind], .var sp v)

/-- The arguments of a call of `x` with each call at a stored generator's parameter that performs
an iteration effect replaced by its stored generator (`pullSite`). -/
def pullArgsV : Nat → Cx → List Cap → String → Val → EM (List Bind × Val)
  | 0, _, _, _, W => pure ([], W)
  | k + 1, cx, cs, x, W => do
    let comps := cx.env.pullArgs x W
    if !comps.any (fun (V, p) => p && (cx.env.iterCall? V).isSome) then return ([], W)
    let mut bs : List Bind := []
    let mut vs : List Val := []
    for (V, p) in comps do
      match p, cx.env.iterCall? V with
      | true, some (g, gs, i, f, W₁) =>
        let (b, V') ← pullSite k cx cs V.span g gs i f W₁
        bs := bs ++ b
        vs := vs ++ [V']
      | _, _ => vs := vs ++ [V]
    let rec tuple : List Val → Val
      | [] => W
      | [V] => V
      | V :: Vs => .pair V.span V (tuple Vs)
    pure (bs, tuple vs)

/-- The copy of `g` for what serves its effects at a call in `cx`, made once. -/
def copyFor : Nat → Cx → Span → String → FSig → List Inst → List Blk → EM String
  | 0, _, sp, _, _, _, _ => throw ⟨sp, "internal error: copies nested too deeply"⟩
  | k + 1, cx, sp, x, g, row, blks => do
    if let (some (gn, _), some d) := (g.group, cx.driver) then
      unless blks.isEmpty do
        throw ⟨sp, s!"`{x}` is given an effectful block under the heap driver `{d}`: not provided"⟩
      return ← deepCopy k { cx.env with inLayers := [] } sp gn d x
    let mut hs : List HSig := []
    let mut ss : List Site := []
    let mut keys : List String := []
    -- Each slot of the row served here, in the row's order (SPEC §38): an answering slot by a
    -- capability of its own.
    let mut taken : List String := []
    for i in row do
      if cx.env.answering i.eff then
        let c ← (cx.capAt sp s!"`{x}`" i : Except Error Cap)
        if taken.contains c.var then
          throw ⟨sp, s!"`{x}` performs `{i.eff}` at two entries of its row, which one handler would " ++
            "serve: name the handlers as its row names the entries (`with n = h(…)`, SPEC §38)"⟩
        taken := taken ++ [c.var]
        hs := hs ++ [c.h]
        keys := keys ++ [c.h.key]
      else
        let s ← (cx.serve sp s!"`{x}`" i : Except Error Site)
        ss := ss ++ [s]
        keys := keys ++ [s!"n{s.n}"]
    if keys.isEmpty && blks.isEmpty then return x
    keys := keys ++ blockKeys blks
    if let some (gn, _) := g.group then
      let env := { cx.env with inLayers := [] }
      let nm ← groupCopy k env sp gn (cx.rowOf g) cx.env.inLayers hs ss (keys ++ cx.env.inLayers) x blks
      recordKey (.copy nm x (keys ++ cx.env.inLayers))
      return nm
    recordKey (.copy (copyName x keys) x keys)
    copyOf k { cx.env with inLayers := [] } sp g hs ss (copyName x keys) blks

/-- The layer `L` made for the group `G` (SPEC §20): a transformer of its generator, applied before
the fixed point (Cook and Palsberg's generator transformers). It answers the generator that runs the
given one on the self-reference wrapped: `T(gen)(self) = gen(wrap self)`, where `wrap` keeps a
spent budget (`inl ()`) and wraps the function `g` of a live one so that each member's call runs
`L`'s body at the member's types, its `call(a)` the member's call through `g`. The environment `E`
holds what `L` uses besides what the group does. -/
def layerCopy : Nat → Env → Span → String → RGroup → List Cap → List Site → RSelf → VTy → CTy →
    List (Ident × Life) → List Ident → List String → EM String
  | 0, _, sp, _, _, _, _, _, _, _, _, _, _ => throw ⟨sp, "internal error: copies nested too deeply"⟩
  | k + 1, env, gsp, L, G, cs, ss, rs, selfT, R, lives, tps, keys => do
    let name := copyName (L ++ "__" ++ G.name) keys
    let some (.def_ lsp ln [A, B] LT LV _) := env.layer? L
      | throw ⟨gsp, s!"internal error: the layer `{L}`"⟩
    let f ← (fnParts lsp ln.name LT LV : Except Error FnParts)
    let .letPair _ callN y (.var _ p₀) M := f.body
      | throw ⟨lsp, s!"the layer `{L}` takes its parameters as `(call, a)`"⟩
    unless p₀ == f.p.name do throw ⟨lsp, s!"the layer `{L}` takes its parameters as `(call, a)`"⟩
    let q := (← get).quiet
    if env.lib.contains L then modify fun s => { s with quiet := true }
    let gv ← fresh "fx_lg"
    let mut fields : List Comp := []
    for ((_, fm), j) in G.members.zipIdx do
      let σ : TySubst := [(A.name, fm.P), (B.name, fm.T)]
      let cxL : Cx := { env := { env with owner := Instances.ownerKey ln.name ln.span,
                                          ownerTps := [A.name, B.name] },
                        caps := cs, sites := ss, fnCaps := cs, layerCall := some ⟨callN.name, gv, j, rs⟩ }
      let body ← trC k cxL cs true (M.subst σ)
      let pp ← fresh "fx_pp"
      fields := fields ++ [.lam gsp ⟨pp, gsp⟩ (capsTy gsp cs fm.P) (← unpack gsp cs y.name pp body)]
    let sv ← fresh "fx_ls"; let qv ← fresh "fx_lq"; let self ← fresh "fx_lself"
    let u ← fresh "fx_lu"; let e ← fresh "fx_le"; let z ← fresh "fx_lz"; let self₂ ← fresh "fx_lself"
    let sf ← fresh "fx_lf"; let yv ← fresh "fx_ly"
    let P : VTy := .tensor gsp selfT (.unit gsp)
    let genT : VTy := .bang gsp (.thunk gsp (.arr gsp P R))
    let wrapped : Val := .inr gsp (.bangThunkv gsp (.lam gsp ⟨z, gsp⟩ (.unit gsp)
      (.letUnit gsp (.var gsp z) (withAll gsp fields))))
    let inner : Comp := .lam gsp ⟨qv, gsp⟩ P (.letPair gsp ⟨self, gsp⟩ ⟨u, gsp⟩ (.var gsp qv)
      (.bind gsp ⟨self₂, gsp⟩ (some selfT)
        (.case gsp (.var gsp self) ⟨e, gsp⟩ (.ret gsp (.inl gsp (.var gsp e))) ⟨gv, gsp⟩ (.ret gsp wrapped))
        (.bind gsp ⟨sf, gsp⟩ none (.ret gsp (.unbang gsp (.var gsp sv)))
          (.bind gsp ⟨yv, gsp⟩ none (.ret gsp (.pair gsp (.var gsp self₂) (.var gsp u)))
            (.app gsp (.force gsp ⟨sf, gsp⟩) ⟨yv, gsp⟩)))))
    let tf : FnParts := ⟨true, lives, genT, genT, ⟨sv, gsp⟩, .ret gsp (.bangThunkv gsp inner)⟩
    let (tA, tV) := tf.build gsp
    report gsp "lowering" (s!"layer {L} for the group {", ".intercalate rs.members}: `{name}`, a " ++
      "transformer of its generator, applied before the fixed point")
    modify fun s => { s with quiet := q }
    let mk : Mark := if tps.isEmpty then .none else .template .none
    modify fun s => { s with made := s.made.push (name, .def_ gsp ⟨name, gsp⟩ tps tA tV mk) }
    pure name

/-- The copy of the recursive group `gn` for the answering handlers `hs` and the sites `ss` (keys
`keys`), made once (SPEC §20): the group is the bounded fixed point of its **generator**, taken at
the record of its members, `R = &ⱼ (E ⊗ Pⱼ ⊸ F_Σ (E ⊗ Tⱼ))`. The generator `gn__step__…` takes
the self-reference `1 + !U(1 ⊸ R)` and answers the record of the members' bodies, each taking the
environment `E` (the capabilities the group uses, as every copy takes them) first and handing it
back first; a call of a member inside it is a direct call of the self-reference (`selfCall`). A
member's copy is `(bounded_fix[1, R] (gen, (budget, ()))).j`, the budget `recBudget`; it has the
type a copy of the member has, so a call of it is a call of a copy. Answers the copy of `x`. -/
def groupCopy : Nat → Env → Span → String → List Inst → List String → List HSig → List Site →
    List String → String → List Blk → EM String
  | 0, _, sp, _, _, _, _, _, _, _, _ => throw ⟨sp, "internal error: copies nested too deeply"⟩
  | k + 1, env, sp, gn, row, layers, hs, ss, keys, x, blks => do
    let blks := blks.map (·.inCopy ss)
    let name := copyName x keys
    let stepName := copyName (gn ++ "__step") keys
    let st ← get
    if st.made.any (·.1 == stepName) || st.started.contains stepName then return name
    modify fun s => { s with started := stepName :: s.started }
    -- A library's recursion is not reported, as its copies are not (`copyOf`).
    let q := (← get).quiet
    if env.lib.contains gn then modify fun s => { s with quiet := true }
    let some G₀ := env.groups.find? (·.name == gn) | throw ⟨sp, s!"internal error: the group `{gn}`"⟩
    let some exh := env.exhEff? | throw ⟨sp, s!"internal error: the exhaustion effect"⟩
    let some e := ss.find? (·.eff == exh.name)
      | throw ⟨sp, s!"`{x}` is recursive: its depth is bounded, and no handler of `{exh.name}` is in scope here"⟩
    -- Effectful blocks (SPEC §30): the member's block parameters at their rows.
    if !blks.isEmpty && G₀.members.length > 1 then
      throw ⟨sp, s!"`{x}` is given an effectful block, and is a member of a recursive group of " ++
        "several functions: not provided"⟩
    let mut G := G₀
    let mut named : List (String × List Site × List Cap) := []
    let mut ssAll := ss
    if let [(mn, f)] := G₀.members then
      let (f', nm, all) ← (withBlocks env sp x f ss blks : Except Error _)
      G := { G₀ with members := [(mn, f')] }
      named := nm
      ssAll := all
    let env := { env.withBlocks named with ownerTps := G.tps.map (·.name) }
    let gsp := G.sp
    -- The environment: the capabilities, in the order of the row, as `copyOf` takes them; the
    -- sites relabelled as the slots they serve (SPEC §38).
    let (cs, ssR) := slotsOf gsp row (G.tps.map (·.name)) hs ss env.answering
    -- The capabilities the blocks use, after the row's (SPEC §32).
    let cs := withBlkCaps cs ((blkCaps blks).map (·.canon gsp))
    -- The group's own type parameters, then the type of each variable a `for`'s site threads.
    let tps : List Ident := G.tps ++ (((ss.filterMap (·.thr)).map (·.2)) ++
      ((cs.filterMap (·.thr)).filter fun W => !(ss.filterMap (·.thr)).any (·.2 == W))).map
        fun W => ⟨W, gsp⟩
    let tArgs : List VTy := tps.map fun t => .name gsp t.name
    let lives : List (Ident × Life) := G.lives ++
      (cs.filter (·.thr.isNone)).map fun c => ((⟨c.life, gsp⟩ : Ident), Life.top gsp)
    let rowR := env.rowOf (ssR ++ (ssAll.filter fun s => !ss.any (·.n == s.n)).map fun s =>
      { s with sp := gsp, what := "the caller" })
    let ss := ssR
    let n := G.members.length
    let Cs : List CTy := G.members.map fun (_, f) =>
      .arr gsp (capsTy gsp cs f.P) (.eff gsp rowR (capsTy gsp cs f.T))
    let R := ampTys gsp Cs
    let selfT : VTy := .sum gsp (.unit gsp) (.bang gsp (.thunk gsp (.arr gsp (.unit gsp) R)))
    let self := "fx_self"
    let rs : RSelf := ⟨G.members.map (·.1), e.n, self, Cs, cs, ss, false⟩
    let cx : Cx := { env, caps := cs, sites := ss, fnCaps := cs, recSelf := some rs, cbs := named }
    -- The generator's record: each member's body, taking the environment first.
    let mut fields : List Comp := []
    for (mn, f) in G.members do
      let owner := match (env.fn? mn).map (·.decl) with
        | some (.def_ _ m _ _ _ _) => Instances.ownerKey m.name m.span
        | _ => env.owner
      let body ← trC k { cx with env := { cx.env with owner } } cs true f.body
      if cs.isEmpty then
        fields := fields ++ [.lam gsp f.p f.P body]
      else
        let pp ← fresh "fx_pp"
        fields := fields ++ [.lam gsp ⟨pp, gsp⟩ (capsTy gsp cs f.P) (← unpack gsp cs f.p.name pp body)]
    let ps ← fresh "fx_rsp"
    let pu ← fresh "fx_ru"
    let P : VTy := .tensor gsp selfT (.unit gsp)
    let gen : Comp := .lam gsp ⟨ps, gsp⟩ P
      (.letPair gsp ⟨self, gsp⟩ ⟨pu, gsp⟩ (.var gsp ps) (.letUnit gsp (.var gsp pu) (withAll gsp fields)))
    -- `!U (P -o R)`, under the capabilities' lifetimes when there are any.
    let genT : VTy := .bang gsp (.thunk gsp (.arr gsp P R))
    let genV : Val := .bangThunkv gsp gen
    let (sA, sV) : VTy × Val := match lives.foldr (fun (a, b) (T, V) =>
        (VTy.all gsp a b T, Val.thunkv gsp (.lamL gsp a b (.ret gsp V)))) (genT, genV) with
      | (T@(.all ..), .thunkv _ M) => (.bang gsp T, .bangThunkv gsp M)
      | TV => TV
    report gsp "lowering" (s!"recursive group {", ".intercalate (G.members.map (·.1))}: the generator " ++
      s!"`{stepName}`, the record of its members" ++
      (if cs.isEmpty then "" else ", each taking the capabilities as its environment") ++
      String.join (named.map fun (b, bss, bcs) => s!", its block `{b}` {blockText bss bcs}") ++
      s!"; each member's copy is bounded_fix of it at the budget {recBudget}, its calls of itself " ++
      s!"direct calls of the self-reference, the exhaustion effect at the site {e.n}")
    let mk : Mark := if tps.isEmpty then .none else .template .none
    modify fun s => { s with made := s.made.push (stepName, .def_ gsp ⟨stepName, gsp⟩ tps sA sV mk) }
    -- The layers, innermost first: each a transformer of the generator.
    let mut trs : List String := []
    for L in layers do
      trs := trs ++ [← layerCopy k env gsp L G cs ss rs selfT R lives tps keys]
    -- Each member's copy: `(bounded_fix[1, R] (Lₙ(… L₁(gen))), (budget, ()))).j`.
    let genRef : Val := if tps.isEmpty then .var gsp stepName else .defApp gsp stepName tArgs
    for ((mn, f), j) in G.members.zipIdx do
      let p ← fresh "fx_rp"
      let sv ← fresh "fx_rst"
      let fb ← fresh "fx_rbf"
      let fa ← fresh "fx_rba"
      let inst : Val := lives.foldl (fun V (a, _) => .inst gsp V (.var gsp a.name))
        (if lives.isEmpty then genRef else .unbang gsp genRef)
      let mut tv := sv
      let mut applied : List (String × Val) := []
      for t in trs do
        let tv' ← fresh "fx_rst"
        let tref : Val := if tps.isEmpty then .var gsp t else .defApp gsp t tArgs
        let tinst : Val := lives.foldl (fun V (a, _) => .inst gsp V (.var gsp a.name))
          (if lives.isEmpty then tref else .unbang gsp tref)
        applied := applied ++ [(tv', .app gsp tinst (.var gsp tv))]
        tv := tv'
      let arg : Val := .pair gsp (.var gsp tv)
        (.pair gsp (.const gsp (.lit (.i32 (UInt32.ofNat recBudget)))) (.unit gsp))
      let fixC : Comp :=
          (.bind gsp ⟨fb, gsp⟩ none (.ret gsp (.unbang gsp (.const gsp (.boundedFix (.unit gsp) R))))
            (.bind gsp ⟨fa, gsp⟩ none (.ret gsp arg)
              (.app gsp (projAt gsp j n (.app gsp (.force gsp ⟨fb, gsp⟩) ⟨fa, gsp⟩)) ⟨p, gsp⟩)))
      let body : Comp :=
        .bind gsp ⟨sv, gsp⟩ none (.ret gsp inst) (applied.foldr (fun (y, V) K =>
          .bind gsp ⟨y, gsp⟩ none (.ret gsp V) K) fixC)
      let drv : FnParts := ⟨true, lives, capsTy gsp cs f.P, capsTy gsp cs f.T, ⟨p, gsp⟩, body⟩
      let (dA, dV) := drv.build gsp rowR
      let dn := copyName mn keys
      modify fun s => { s with made := s.made.push (dn, .def_ gsp ⟨dn, gsp⟩ tps dA dV mk) }
    modify fun s => { s with quiet := q }
    pure name

/-- The copy of the recursive group `gn` driven by the heap driver `d`, made once (SPEC §20): the
machine's source `gn__mach_src`, a function of the members' self-references whose result runs a
member's body on its tagged argument (the typed elaboration turns it into the machine
`gn__mach`, `recMachine`), and per member `x__d`, `d` of the machine on the member's argument, a
loop. Answers the copy of `x`. -/
def deepCopy : Nat → Env → Span → String → String → String → EM String
  | 0, _, sp, _, _, _ => throw ⟨sp, "internal error: copies nested too deeply"⟩
  | k + 1, env, sp, gn, d, x => do
    let name := s!"{x}__{d}"
    let src := s!"{gn}__mach_src"
    let mach := s!"{gn}__mach"
    let st ← get
    if st.made.any (·.1 == src) || st.started.contains src then return name
    modify fun s => { s with started := src :: s.started }
    let some G := env.groups.find? (·.name == gn) | throw ⟨sp, s!"internal error: the group `{gn}`"⟩
    let some exh := env.exhEff? | throw ⟨sp, s!"internal error: the exhaustion effect"⟩
    let gsp := G.sp
    let some g₀ := env.fn? x | throw ⟨sp, s!"internal error: `{x}`"⟩
    -- A generic group: its source and its members' copies are templates in its type parameters,
    -- and each instance of the source is made into the machine of that instance (`recMachine`).
    -- `[spec §31]`
    let tArgs : List VTy := G.tps.map fun t => .name gsp t.name
    let mk : Mark := if G.tps.isEmpty then .none else .template .none
    let machV : Val := if G.tps.isEmpty then .var gsp mach else .defApp gsp mach tArgs
    if let some i := g₀.row.find? (·.eff != exh.name) then
      throw ⟨sp, s!"`{x}` performs `{i.eff}`: a recursion that performs an effect is not provided " ++
        s!"under the heap driver `{d}`"⟩
    let A := sumTys gsp (G.members.map (·.2.P))
    let some (_, f₀) := G.members.head? | throw ⟨gsp, "internal error: an empty group"⟩
    let B := f₀.T
    if let some (y, _) := G.members.find? (·.2.T.strip != B.strip) then
      throw ⟨sp, s!"`{y}` answers a type other than `{x}`'s: members with different result types " ++
        s!"are not provided under the heap driver `{d}`"⟩
    let rs : RSelf := ⟨G.members.map (·.1), 0, "", [], [], [], true⟩
    let cx : Cx := { env, caps := [], recSelf := some rs }
    let mut bodies : List (Ident × Comp) := []
    for (_, f) in G.members do
      let body ← trC k cx [] true f.body
      let xi ← fresh "fx_ra"
      bodies := bodies ++ [(⟨xi, gsp⟩, .bind gsp f.p none (.ret gsp (.var gsp xi)) body)]
    let fa ← fresh "fx_rarg"
    let rec dispatch : Nat → String → List (Ident × Comp) → EM Comp
      | _, _, [] => throw ⟨gsp, "internal error: an empty group"⟩
      | _, v, [(xi, B₁)] => pure (.bind gsp xi none (.ret gsp (.var gsp v)) B₁)
      | 0, _, _ => throw ⟨gsp, "internal error: a group nested too deeply"⟩
      | n + 1, v, (xi, B₁) :: rest => do
        let y ← fresh "fx_rq"
        pure (.case gsp (.var gsp v) xi B₁ ⟨y, gsp⟩ (← dispatch n y rest))
    let body ← dispatch (G.members.length + 1) fa bodies
    -- `fx_rs ↦ (fx_rself0, …) bound; return !thunkv fun (fx_rarg : A) -> body`.
    let selfTy (f : FnParts) : VTy := .bang gsp (.lolli gsp f.P B)
    let selfs := G.members.zipIdx.map fun ((_, f), j) => (s!"fx_rself{j}", selfTy f)
    let ps ← fresh "fx_rs"
    let inner : Val := .bangThunkv gsp (.lam gsp ⟨fa, gsp⟩ A body)
    let srcBody ← bindParams gsp ps (selfs.map fun (y, _) => ⟨y, gsp⟩) (.ret gsp inner)
    let srcF : FnParts := ⟨true, [], tupleTy gsp (selfs.map (·.2)), .bang gsp (.lolli gsp A B),
      ⟨ps, gsp⟩, srcBody⟩
    let (sA, sV) := srcF.build gsp
    report gsp "lowering" (s!"recursive group {", ".intercalate (G.members.map (·.1))} under `{d}`: " ++
      s!"the machine `{mach}`, its pending calls frames in `{d}`'s buffer")
    modify fun s => { s with made := s.made.push (src, .def_ gsp ⟨src, gsp⟩ G.tps sA sV mk) }
    for ((mn, f), j) in G.members.zipIdx do
      let p ← fresh "fx_dp"
      let ms ← fresh "fx_ms"; let mr ← fresh "fx_mr"
      let call : Val := .app gsp (.var gsp d) (.pair gsp (.var gsp ms) (.pair gsp (.var gsp mr)
        (.ascribe gsp (injAt gsp j G.members.length (.var gsp p)) A)))
      let body : Comp := .letPair gsp ⟨ms, gsp⟩ ⟨mr, gsp⟩ machV (.ret gsp call)
      let drv : FnParts := ⟨true, [], f.P, B, ⟨p, gsp⟩, body⟩
      let (dA, dV) := drv.build gsp
      let dn := s!"{mn}__{d}"
      modify fun s => { s with made := s.made.push (dn, .def_ gsp ⟨dn, gsp⟩ G.tps dA dV mk) }
    pure name

/-- The copy `name` of `g` for the answering handlers `hs` and the sites `ss`, made once: its body
elaborated with their capabilities as parameters and their operations as its row. -/
def copyOf : Nat → Env → Span → FSig → List HSig → List Site → String → List Blk →
    EM String
  | 0, _, sp, _, _, _, _, _ => throw ⟨sp, "internal error: copies nested too deeply"⟩
  | k + 1, env, sp, g, hs, ss, name, blks => do
    let blks := blks.map (·.inCopy ss)
    let st ← get
    if st.made.any (·.1 == name) || st.started.contains name then return name
    modify fun s => { s with started := name :: s.started }
    let .def_ dsp n ps A V mk := g.decl
      | throw ⟨sp, s!"internal error: `{g.name}` is not a function"⟩
    -- The body is elaborated in its own frame (SPEC §38).
    let env := { env with owner := Instances.ownerKey n.name n.span, ownerTps := ps.map (·.name) }
    let q := (← get).quiet
    if env.lib.contains g.name then modify fun s => { s with quiet := true }
    let f ← (fnParts dsp n.name A V : Except Error FnParts)
    -- Computation parameters (SPEC §33): the port of each provided effect, a site of the copy's
    -- row when the copy calls the parameter outside a handler of it, else a `with`'s of its own.
    let names := paramNames f
    let mut ports : List (Nat × List (Site × Bool)) := []
    let mut cxPorts : List (String × Site × Bool) := []
    for b in blks do
      if b.prov.isEmpty then continue
      let some x := names[b.j]? | throw ⟨sp, s!"internal error: the parameter {b.j} of `{g.name}`"⟩
      let mut ps : List (Site × Bool) := []
      for (e, As) in b.prov do
        if reachesParam env x e.name As f.body then
          let some s := ss.find? (·.eff == e.name)
            | throw ⟨sp, s!"internal error: `{g.name}` passes `{e.name}` of `{x}` on, unserved"⟩
          ps := ps ++ [({ s with sp := dsp, what := "the caller" }, false)]
        else
          let p ← freshSite
          ps := ps ++ [({ eff := e.name, n := p, args := As, sp := dsp,
                          what := s!"`{g.name}`'s handler of `{e.name}` around `{x}`" }, true)]
      ports := ports ++ [(b.j, ps)]
      cxPorts := cxPorts ++ ps.map fun (s, own) => (x, s, own)
    modify fun st => { st with ports := (name, ports) :: st.ports }
    -- The capabilities, in the order of the row: an answering handler's, and the variable a
    -- `for`'s site threads (whose type is a parameter of the copy, `W`); the sites relabelled as
    -- the slots they serve (SPEC §38).
    let (cs, ssR) := slotsOf dsp g.row (ps.map (·.name)) hs ss env.answering
    -- Effectful blocks (SPEC §30): the block parameters at their rows.
    let (f, named, ssAll) ← (withBlocks env dsp g.name f ssR blks ports : Except Error _)
    let env := env.withBlocks named
    -- The capabilities the blocks use, after the row's (SPEC §32).
    let cs := withBlkCaps cs ((blkCaps blks).map (·.canon dsp))
    let tps : List Ident := (((ss.filterMap (·.thr)).map (·.2)) ++
      ((cs.filterMap (·.thr)).filter fun W => !(ss.filterMap (·.thr)).any (·.2 == W))).map
        fun W => ⟨W, dsp⟩
    let ss := ssR
    let cx : Cx := { env, caps := cs, sites := ss, fnCaps := cs, cbs := named, ports := cxPorts }
    let body ← trC k cx cs true f.body
    let f' ← if cs.isEmpty then pure { f with body } else takeCaps dsp cs f body
    let (A', V') := f'.build dsp (env.rowOf (ssAll.map fun s => { s with sp := dsp, what := "the caller" }))
    let portText (b : String) : List String :=
      (cxPorts.filter (·.1 == b)).map fun (_, p, own) =>
        s!"its `{p.eff}` at the port {p.n}" ++
          (if own then ", served by its `with` here" else ", passed on to the caller")
    let hText := (cs.filter (fun c => c.thr.isNone && !c.blk)).map fun c =>
      c.h.name ++ ((c.name.map (s!" as `{·}`")).getD "")
    report dsp "lowering" (s!"copy `{name}`: `{g.name}` for " ++ ", ".intercalate
      ((if hText.length == hs.length then hText else hs.map (·.name)) ++
        ss.map (fun s => s!"the site {s.n} of `{s.eff}`" ++ ((s.name.map (s!" as `{·}`")).getD "")) ++
        named.map fun (b, bss, bcs) =>
          let lex := bss.filter fun s => !cxPorts.any fun (y, p, _) => y == b && p.n == s.n
          ", ".intercalate ((s!"its block `{b}`" ++
            (if lex.isEmpty && bcs.isEmpty then "" else " " ++ blockText lex bcs)) :: portText b)))
    modify fun s => { s with quiet := q }
    -- A copy that threads a `for`'s variable is generic in its type.
    let mk' := match tps, ps, mk with
      | [], _, mk => mk
      | _, [], mk => .template mk
      | _, _, mk => mk
    modify fun s => { s with made := s.made.push (name, .def_ dsp ⟨name, n.span⟩ (ps ++ tps) A' V' mk') }
    pure name
end

/-! ### Answering handlers -/

/-- The clause of the answering handler `h` for the operation `o`:
`fn h__op<'l, 'b, …>(c: mut 'l S, x: A, …) -> mut 'l S * B`, `'b, …` the operation's lifetime
parameters, whose body runs the clause on the state by `modify` (`withswap`) and hands the borrow
back; or, for a handler whose state is lent (SPEC §34), runs the clause on the borrow itself and
hands back the borrow it ends with. -/
def clauseDef (env : Env) (h : HSig) (o : OpDecl) (c : Clause) : EM Decl := do
  let sp := c.name.span
  unless c.params.length == o.params.length do
    throw ⟨sp, s!"the clause `{c.name.name}` of `{h.name}` takes {c.params.length} parameters, " ++
      s!"and the operation {o.params.length}"⟩
  if let some e := (rowC env fuel c.body).head? then
    throw ⟨sp, s!"the clause `{c.name.name}` of `{h.name}` performs an operation of `{e.eff}`: a " ++
      "clause of an answering handler is code over the handler's state, and performs no operation"⟩
  let l := "fx_l"
  let cv := "fx_c"
  let st := h.st.name
  let v ← fresh "fx_v"
  let w ← fresh "fx_w"
  -- The clause's answer at the operation's result type; a terminal that lends a place is bound
  -- first, since a lend cannot be in an annotated binding, and any other computation is bound
  -- at that type.
  let body := wrapTerms (fun T =>
    let hand := Comp.ret T.span (.pair T.span (.var T.span st) (.var T.span v))
    match T with
    | .ret _ V => if V.lends then
        .bind T.span ⟨w, T.span⟩ none T
          (.bind T.span ⟨v, T.span⟩ (some o.res) (.ret T.span (.var T.span w)) hand)
      -- A value is handed on as itself, at the operation's result type.
      else .ret T.span (.pair T.span (.var T.span st) (.ascribe T.span V o.res))
    | _ => .bind T.span ⟨v, T.span⟩ (some o.res) T hand) c.body
  let modifyV : Val := .app sp (.app sp (.sugar sp (.borrow .modify "")) (.var sp cv))
    (.thunkv sp (.lam sp h.st (.name sp "_") body))
  let b ← fresh "fx_b"
  let r ← fresh "fx_r"
  -- A lent state is the capability itself: the clause runs with the state's name bound to the
  -- borrow, and hands back the borrow it ends with (SPEC §34). Otherwise the clause runs on the
  -- state's value, swapped out of the lent cell (`modify`).
  let inner : Comp := if h.lent then .bind sp h.st none (.ret sp (.var sp cv)) body else
    .bind sp ⟨b, sp⟩ none (.ret sp modifyV)
      (.letPair sp ⟨cv, sp⟩ ⟨r, sp⟩ (.var sp b) (.ret sp (.pair sp (.var sp cv) (.var sp r))))
  -- One parameter is the component itself (`Parser.paramVar`).
  let p ← match c.params with
    | [x] => pure x.name
    | _ => fresh "fx_p"
  let inner ← bindParams sp p c.params inner
  let pp ← fresh "fx_pp"
  let cap : Cap := ⟨h.eff, cv, l, h, none, false, none, false⟩
  let P := tupleTy sp (o.params.map (·.2))
  let f : FnParts := ⟨true, (⟨l, sp⟩, .top sp) :: o.lives, capsTy sp [cap] P, capsTy sp [cap] o.res, ⟨pp, sp⟩,
    .letPair sp ⟨cv, sp⟩ ⟨p, sp⟩ (.var sp pp) inner⟩
  let (A, V) := f.build sp
  pure (.def_ sp ⟨clauseName h.name c.name.name, sp⟩ [] A V .none)

/-! ### Programs -/

/-- A computation has a `while` or a `loop` outside nested closures. -/
def hasWhile : Nat → Comp → Bool
  | 0, _ => false
  | k + 1, M => match M with
    | .loop _ _ .while_ _ _ _ | .loop _ _ .forever _ _ _ => true
    | .loop _ _ _ _ B N => hasWhile k B || hasWhile k N
    | .bind _ _ _ M N | .with_ _ M N => hasWhile k M || hasWhile k N
    | .letUnit _ _ M | .letPair _ _ _ _ M | .lam _ _ _ M | .lamL _ _ _ M => hasWhile k M
    | .case _ _ _ M _ N => hasWhile k M || hasWhile k N
    | .unwind _ _ _ M D N => hasWhile k M || hasWhile k D || hasWhile k N
    | _ => false

/-- The recursive groups of the definitions `ds` (SPEC §20): each strongly connected component of
the calls among them that has a call in it (a function that calls itself, or functions that call
one another), its members in declaration order. -/
def recGroupsOf (ds : List (String × Val)) : List (List String) := Id.run do
  let names := ds.map (·.1)
  let succ : List (String × List String) :=
    ds.map fun (x, V) => (x, (refsV fuel V).eraseDups.filter names.contains)
  let succOf (x : String) : List String := (succ.lookup x).getD []
  -- `reach x` is every name a chain of calls from `x` reaches.
  let reach (x : String) : List String := Id.run do
    let mut seen : List String := []
    let mut todo := succOf x
    for _ in [0:names.length * names.length + 1] do
      match todo with
      | [] => break
      | y :: rest =>
        todo := rest
        if !seen.contains y then
          seen := y :: seen
          todo := todo ++ succOf y
    return seen
  let reaches := names.map fun x => (x, reach x)
  let r (x : String) : List String := (reaches.lookup x).getD []
  let mut out : List (List String) := []
  for x in names do
    if (r x).contains x && !out.any (·.contains x) then
      out := out ++ [names.filter fun y => (r x).contains y && (r y).contains x]
  return out

/-- The computation parameters of a function as written (SPEC §33): each parameter whose type has
a provided row, by index, with its name and the row.  `[spec §33]` -/
def compParamsOf (sp : Span) (name : String) (A : VTy) (V : Val) :
    List (Nat × String × List (Ident × List VTy)) :=
  match fnParts sp name A V with
  | .error _ => []
  | .ok f =>
    let names := paramNames f
    names.zipIdx.filterMap fun (x, j) => do
      let es ← provOf (← compAt names.length f.P j)
      pure (j, x, es)

/-- A `for` over a call of one of the parameters `xs`, outside nested closures: its span.
`[spec §33]` -/
def forOverParam (xs : List String) : Nat → Comp → Option Span
  | 0, _ => none
  | k + 1, M => match M with
    | .loop sp _ src V B N =>
      if (match src, V with | .each _, .app _ f _ => (headName f).any xs.contains | _, _ => false) then some sp
      else (forOverParam xs k B).orElse fun _ => forOverParam xs k N
    | .bind _ x _ (.ret _ V) N =>
      if V.copyOf?.any xs.contains then forOverParam (x.name :: xs) k N else forOverParam xs k N
    | .bind _ _ _ M N | .with_ _ M N | .case _ _ _ M _ N =>
      (forOverParam xs k M).orElse fun _ => forOverParam xs k N
    | .letUnit _ _ M | .letPair _ _ _ _ M | .lam _ _ _ M | .lamL _ _ _ M => forOverParam xs k M
    | _ => none

/-- The names a declaration defines. -/
def Decl.defName : Decl → Option String
  | .def_ _ n _ _ _ _ => some n.name
  | _ => none

/-- The mark of a definition without its written row, and the row. -/
def splitRow : Mark → List (Ident × List VTy) × Mark
  | .row es m _ => (es, m)
  | m => ([], m)

/-- The names of a written row's entries (SPEC §38), one per entry. -/
def rowNames : Mark → List (Option String)
  | .row es _ ns => es.zipIdx.map fun (_, j) => (ns[j]?).join.map (·.name)
  | _ => []

/-- The entry of a written row (`written`, its entries' names `names`) that the instance `i` a
function performs is: the entry named as it is, when it is named; else the one of its type
arguments, or the only one of its effect (SPEC §38). Two entries that could be it, neither of them
the one unnamed, are ambiguous. `none` when the row lists no entry of its effect. -/
def Env.slotOf (env : Env) (sp : Span) (f : String) (written : List (Ident × List VTy))
    (names : List (Option String)) (i : Inst) : Except Error (Option Inst) := do
  let ents := written.zipIdx.filterMap fun ((e, As), j) =>
    if e.name == i.eff then some (As, (names[j]?).join) else none
  if ents.isEmpty then return none
  let slot (e : List VTy × Option String) : Inst := ⟨i.eff, some e.1, e.2⟩
  if let some x := i.name then
    let some e := ents.find? (·.2 == some x)
      | throw ⟨sp, s!"`{f}` performs `{i.eff}` at `{x}`, which its written row does not name"⟩
    return some (slot e)
  let pickOne (es : List (List VTy × Option String)) (what : String) : Except Error Inst := do
    match es with
    | [e] => pure (slot e)
    | es => match es.filter (·.2.isNone) with
      | [e] => pure (slot e)
      | _ => throw ⟨sp, s!"`{f}` performs {what}, which two entries of its written row could be: " ++
          "ascribe its argument (`(e : T)`), or perform it at a named entry (`n.op(…)`, SPEC §38)"⟩
  match i.args with
  | some As =>
    match ents.filter (env.sameArgs As ·.1) with
    | [] =>
      match ents with
      | [e] => return some (slot e)
      | _ => throw ⟨sp, s!"`{f}` performs {instText i.eff As}, which its written row does not list"⟩
    | es => return some (← pickOne es (instText i.eff As))
  | none =>
    if let [e] := ents then return some (slot e)
    return some (← pickOne ents s!"`{i.eff}` at type arguments not known here")

/-- A written row lists each entry once: two entries of one instance are named, and differently
(SPEC §38). -/
def Env.checkWritten (env : Env) (sp : Span) (f : String) (written : List (Ident × List VTy))
    (names : List (Option String)) : Except Error Unit := do
  let ents := written.zipIdx.map fun ((e, As), j) => (e.name, As, (names[j]?).join)
  for ((e, As, x), j) in ents.zipIdx do
    for (e', As', x') in ents.drop (j + 1) do
      if e == e' && x == x' && As.length == As'.length && env.sameArgs As As' then
        throw ⟨sp, s!"`{f}` lists {instText e As} twice in its written row" ++
          (if x.isNone then ": name the entries (`with a: E, b: E`, SPEC §38)" else "")⟩

/-- Anything for this pass to do: an effect, a handler or a written row. -/
def hasEffects (ds : List Decl) : Bool :=
  ds.any fun
    | .effect .. | .handler .. | .chandler .. => true
    | .def_ _ _ _ _ V mk => (match mk with | .row .. => true | _ => false) ||
      V.anySugar (· matches .writes _)
    | .main _ _ M => M.anySugar (· matches .writes _)
    | _ => false

/-- The recursive group of the definitions `ms` declared (SPEC §20): each member a function of the
group's row, the union of what its members' bodies perform and the exhaustion effect, which
`bounded`, its default driver, performs when the budget of depth is spent. A call of a member is a
call of its copy for what serves that row (`groupCopy`). -/
def defineGroup (env : Env) (ms : List (Span × Ident × List Ident × VTy × Val × Mark)) : EM Env := do
  let some (sp₀, n₀, tps₀, _, _, _) := ms.head? | throw ⟨Span.none, "internal error: an empty group"⟩
  -- A generic group: every member generic in the same type parameters, each call of a member
  -- inside the group at them (SPEC §15, §20).
  if let some (_, n, _, _, _, _) := ms.find? (fun (_, _, tps, _, _, _) =>
      tps.map (·.name) != tps₀.map (·.name)) then
    throw ⟨n.span, s!"`{n.name}` and `{n₀.name}` call one another and take different type " ++
      "parameters: a recursive group's members are generic in the same type parameters"⟩
  let some exh := env.exhEff?
    | throw ⟨n₀.span, s!"`{n₀.name}` calls itself{if ms.length > 1 then " through " ++
        ", ".intercalate (ms.map (·.2.1.name)) else ""}: a recursion's depth is bounded, and its " ++
        "exhaustion effect is in `lib/rec.bc`: `include rec`"⟩
  let mut parts : List (String × FnParts) := []
  let mut row : List Inst := []
  for (sp, n, _, A, V, mk) in ms do
    let f ← (fnParts sp n.name A V : Except Error FnParts)
    if let some (_, f₀) := parts.head? then
      unless f.lives.map (·.1.name) == f₀.lives.map (·.1.name) do
        throw ⟨n.span, s!"`{n.name}` and `{n₀.name}` call one another and take different " ++
          "lifetime parameters: a recursive group's members take the same lifetime parameters"⟩
    unless f.bang do
      throw ⟨n.span, s!"`{n.name}` is recursive and is not a persistent function"⟩
    if hasWhile fuel f.body then
      throw ⟨n.span, s!"`{n.name}` is recursive and its body has a `while` or a `loop`, so it is " ++
        "div: the `Exhausted` of its budget would be performed inside its loop, and a handler around " ++
        "a div computation is not provided"⟩
    let (written, _) := splitRow mk
    let env := { env with owner := Instances.ownerKey n.name n.span, ownerTps := tps₀.map (·.name) }
    (env.checkWritten n.span n.name written (rowNames mk) : Except Error Unit)
    let inferred := rowV env fuel V
    for i in inferred do
      unless written.isEmpty || written.any (·.1.name == i.eff) do
        throw ⟨n.span, s!"`{n.name}` performs `{i.eff}`, which its written row does not list"⟩
    let mine ← if written.isEmpty then pure inferred else
      inferred.filterMapM fun i => (env.slotOf n.span n.name written (rowNames mk) i : Except Error _)
    for i in mine do
      row := env.addInst row i
    unless written.isEmpty || written.any (·.1.name == exh.name) do
      throw ⟨n.span, s!"`{n.name}` is recursive, so it performs `{exh.name}` when its depth runs out, " ++
        "which its written row does not list"⟩
    parts := parts ++ [(n.name, f)]
  -- The group's row settled once, over its members (SPEC §38).
  row ← (Env.settle n₀.span n₀.name row : Except Error _)
  row := env.addInst row ⟨exh.name, some [], none⟩
  let G : RGroup := ⟨n₀.name, parts, sp₀, tps₀, ((parts.head?).map (·.2.lives)).getD []⟩
  report sp₀ "row" (s!"{", ".intercalate (parts.map (·.1))}: " ++
    ", ".intercalate (row.map (·.eff)) ++ s!" (a recursive group: the fixed point of its " ++
    s!"generator, driven by `bounded` at the budget {recBudget})")
  let mut env := { env with groups := env.groups ++ [G] }
  for ((x, _), (sp, n, ps, A, V, mk)) in parts.zip ms do
    env := { env with fns := env.fns ++ [{ name := x, row, decl := .def_ sp n ps A V mk,
                                             group := some (G.name, (parts.map (·.1)).idxOf x) }] }
  pure env

/-! ### `|>`  `[spec §33]` -/

/-- What the pass knows of the program for `|>`: its handlers' names, and each function's
written type. -/
structure PipeEnv where
  handlers : List String
  sigs : List (String × VTy)

/-- `e |> s` (SPEC §33): a handler stage `h[…](…)` is `with h[…](…) { e }`; a function stage
`f(a, …)` whose first parameter is a computation parameter takes `e` suspended, `f(!{ () -> e },
a, …)` (`{ () -> e }` at a parameter that is not `!`); any other function takes `e` first,
`f(e, a, …)` (decision 50). -/
def pipeStage (pe : PipeEnv) (sp : Span) (e s : Val) : EM Val := do
  let (head, args) : Val × Option Val := match s with
    | .app _ h@(.var ..) P | .app _ h@(.defApp ..) P => (h, some P)
    | h => (h, none)
  let (x, As) ← match head with
    | .var _ x => pure (x, [])
    | .defApp _ x As => pure (x, As)
    | _ => throw ⟨s.span, "the right of `|>` is a handler or a function, applied to its other " ++
        "arguments"⟩
  if pe.handlers.contains x then
    let l ← fresh "fx_pipel"
    let b ← fresh "fx_pipec"
    let P := args.getD (.unit sp)
    if P.lends then
      throw ⟨P.span, s!"the handler `{x}` of this `|>` is given a lent place: write `with {x}(…) \{ … }`, " ++
        "which hands the place back"⟩
    return .app sp (.app sp (.sugar s.span (.handle x l As none)) P)
      (.thunkv sp (.lam sp ⟨b, sp⟩ (holeTy sp) (.ret sp e)))
  let first : Option VTy := ((pe.sigs.lookup x).bind paramTyOf).map fun
    | .tensor _ A _ => A
    | A => A
  let e' ← match first with
    | some A@(.rowed ..) | some A@(.bang _ (.rowed ..)) =>
      match unrowed A with
      | .bang _ (.lolli _ (.unit _) _) | .lolli _ (.unit _) _ =>
        let u ← fresh "fx_pipeu"
        let body : Comp := .lam sp ⟨u, sp⟩ (holeTy sp) (.letUnit sp (.var sp u) (.ret sp e))
        pure (match A with | .bang .. => Val.bangThunkv sp body | _ => .thunkv sp body)
      | _ => throw ⟨s.span, s!"the first parameter of `{x}` is a computation parameter that takes " ++
          "an argument: `|>` passes it a computation of none"⟩
    | _ => pure e
  pure (.app sp head (match args with
    | none | some (.unit _) => e'
    | some P => .pair sp e' P))

mutual
/-- `V` with each `e |> s` in it elaborated (`pipeStage`), innermost first. -/
def pipesV (pe : PipeEnv) : Nat → Val → EM Val
  | 0, V => pure V
  | k + 1, V => match V with
    | .app sp (.sugar _ .pipe) (.pair _ e s) => do
      pipeStage pe sp (← pipesV pe k e) (← pipesV pe k s)
    | .pair sp V W => do pure (.pair sp (← pipesV pe k V) (← pipesV pe k W))
    | .inl sp V => do pure (.inl sp (← pipesV pe k V))
    | .inr sp V => do pure (.inr sp (← pipesV pe k V))
    | .thunk sp M => do pure (.thunk sp (← pipesC pe k M))
    | .thunkv sp M => do pure (.thunkv sp (← pipesC pe k M))
    | .bangThunk sp M => do pure (.bangThunk sp (← pipesC pe k M))
    | .bangThunkv sp M => do pure (.bangThunkv sp (← pipesC pe k M))
    | .unbang sp V => do pure (.unbang sp (← pipesV pe k V))
    | .boxed sp a V => do pure (.boxed sp a (← pipesV pe k V))
    | .unbox sp V => do pure (.unbox sp (← pipesV pe k V))
    | .sub sp V a => do pure (.sub sp (← pipesV pe k V) a)
    | .roll sp V => do pure (.roll sp (← pipesV pe k V))
    | .unroll sp V => do pure (.unroll sp (← pipesV pe k V))
    | .run sp M => do pure (.run sp (← pipesC pe k M))
    | .mark sp m V => do pure (.mark sp m (← pipesV pe k V))
    | .app sp V W => do pure (.app sp (← pipesV pe k V) (← pipesV pe k W))
    | .inst sp V a => do pure (.inst sp (← pipesV pe k V) a)
    | .ascribe sp V A => do pure (.ascribe sp (← pipesV pe k V) A)
    | .shorten sp m s a V => do pure (.shorten sp m s a (← pipesV pe k V))
    | V => pure V

/-- `M` with each `e |> s` in it elaborated. -/
def pipesC (pe : PipeEnv) : Nat → Comp → EM Comp
  | 0, M => pure M
  | k + 1, M => match M with
    | .ret sp V => do pure (.ret sp (← pipesV pe k V))
    | .bind sp x A M N => do pure (.bind sp x A (← pipesC pe k M) (← pipesC pe k N))
    | .lam sp x A M => do pure (.lam sp x A (← pipesC pe k M))
    | .app sp M x => do pure (.app sp (← pipesC pe k M) x)
    | .with_ sp M N => do pure (.with_ sp (← pipesC pe k M) (← pipesC pe k N))
    | .proj sp i M => do pure (.proj sp i (← pipesC pe k M))
    | .letUnit sp V M => do pure (.letUnit sp (← pipesV pe k V) (← pipesC pe k M))
    | .letPair sp x y V M => do pure (.letPair sp x y (← pipesV pe k V) (← pipesC pe k M))
    | .case sp V x M y N => do
      pure (.case sp (← pipesV pe k V) x (← pipesC pe k M) y (← pipesC pe k N))
    | .absurd sp V => do pure (.absurd sp (← pipesV pe k V))
    | .lamL sp x b M => do pure (.lamL sp x b (← pipesC pe k M))
    | .inst sp M a => do pure (.inst sp (← pipesC pe k M) a)
    | .nuIn sp M => do pure (.nuIn sp (← pipesC pe k M))
    | .nuOut sp M => do pure (.nuOut sp (← pipesC pe k M))
    | .ascribe sp M C => do pure (.ascribe sp (← pipesC pe k M) C)
    | .loop sp ℓ src V M N => do pure (.loop sp ℓ src (← pipesV pe k V) (← pipesC pe k M) (← pipesC pe k N))
    | .perform sp n i V => do pure (.perform sp n i (← pipesV pe k V))
    | .abort sp n i V => do pure (.abort sp n i (← pipesV pe k V))
    | .handle sp n st hr hc M => do
      let hr' ← pipesV pe k hr
      let hc' ← pipesV pe k hc
      pure (.handle sp n st hr' hc' (← pipesC pe k M))
    | .unwind sp x A M D N => do
      pure (.unwind sp x A (← pipesC pe k M) (← pipesC pe k D) (← pipesC pe k N))
    | M => pure M
end

/-- The declarations with each `|>` in them elaborated (SPEC §33).  `[spec §33]` -/
def resolvePipes (ds : List Decl) : EM (List Decl) := do
  let pe : PipeEnv := ⟨ds.flatMap fun
      | .handler _ n .. => [n.name]
      | .chandler _ h => [h.name.name]
      | _ => [],
    ds.filterMap fun
      | .def_ _ n _ A _ _ => some (n.name, A)
      | _ => none⟩
  let cl (c : Clause) : EM Clause := do pure { c with body := ← pipesC pe fuel c.body }
  ds.mapM fun
    | .def_ sp n ps A V mk => do pure (.def_ sp n ps A (← pipesV pe fuel V) mk)
    | .main sp C M => do pure (.main sp C (← pipesC pe fuel M))
    | .handler sp n st S e cs l => do pure (.handler sp n st S e (← cs.mapM cl) l)
    | .chandler sp h => do
      let (rx, rA, rM) := h.ret
      pure (.chandler sp { h with ret := (rx, rA, ← pipesC pe fuel rM), clauses := ← h.clauses.mapM cl })
    | d => pure d

/-! ### The platform  `[spec §34]` -/

/-- The system interface's effects, in the order `main`'s handlers nest (the first outermost):
each with its capability, `main`'s extern, and the platform's handler that serves it on the
capability's cell. -/
def platformEffects : List (String × String × String) :=
  [("Stdin", "stdin", "wasi_stdin"), ("Stdout", "stdout", "wasi_stdout"),
   ("Stderr", "stderr", "wasi_stderr"), ("Clock", "clock", "wasi_clock"),
   ("Args", "args", "wasi_args")]

/-- The capabilities of the system interface, in `main`'s order. -/
def platformCaps : List String := platformEffects.map (·.2.1)

/-- `main`'s platform capabilities (SPEC §34): each effect of the system interface its body
performs, served by the platform's handler on the capability's cell, which `main` holds and
threads by name; each operation lends it to the clause. A body that names a capability as a value
and performs its effect is rejected: the capability is the effect's. -/
def platformMain (env : Env) (sp : Span) (M : Comp) : EM (List Cap) := do
  let row := rowC env fuel M
  let mut caps : List Cap := []
  for (e, cap, h) in platformEffects do
    unless row.any (·.eff == e) do continue
    let some hs := env.handler? h | continue
    unless hs.eff == e && hs.lent do continue
    if (M.lentNames true).contains cap then
      throw ⟨sp, s!"`main` uses `{cap}` as a value and performs `{e}`, which the platform serves " ++
        s!"on `{cap}`: use one or the other (SPEC §34)"⟩
    caps := caps ++ [⟨e, cap, "", { hs with cell := true }, none, false, none, false⟩]
    report sp "lowering" (s!"main: `{e}` is served by the platform's `{h}` on the cell `{cap}`, " ++
      "which each operation lends")
  pure caps

/-! ### A division's error at `main`  `[spec §39]` -/

/-- The instance a division raises, `Fail[DivError]`, unnamed. -/
def Env.isDivInst (env : Env) (i : Inst) : Bool :=
  i.eff == "Fail" && i.name.isNone && match i.args with
    | some As => env.sameArgs As [Instances.divErrorTy]
    | none => false

/-- `main`'s body split at the first statement of its spine that performs `Fail[DivError]`: the
statements before it, as a context, and the rest. A call in that statement whose argument is a
call that performs none (`f(read_input())`) has its argument bound before it, in the context: the
argument is evaluated first either way. -/
def splitDiv (env : Env) : Nat → Comp → (Comp → Comp) × Comp
  | 0, M => (id, M)
  | k + 1, M =>
    let perf (M : Comp) : Bool := (rowC env fuel M).any env.isDivInst
    let perfV (V : Val) : Bool := (rowV env fuel V).any env.isDivInst
    -- The argument of the statement's call, bound first.
    let lift (V : Val) (rest : Val → Comp) : Option ((Comp → Comp) × Comp) :=
      match V with
      | .app asp f W@(.app ..) =>
        if perfV W then none else
          let a : Ident := ⟨s!"fx_ma{asp.start.line}_{asp.start.col}", asp⟩
          some (fun H => .bind asp a none (.ret asp W) H, rest (.app asp f (.var asp a.name)))
      | _ => none
    match M with
    | .bind sp x A M₁ N =>
      if perf M₁ then
        match M₁ with
        | .ret rsp V => (lift V fun V' => .bind sp x A (.ret rsp V') N).getD (id, M)
        | _ => (id, M)
      else
        let (K, R) := splitDiv env k N
        (fun H => .bind sp x A M₁ (K H), R)
    | .letPair sp x y V N =>
      if perfV V then (lift V fun V' => .letPair sp x y V' N).getD (id, M) else
        let (K, R) := splitDiv env k N
        (fun H => .letPair sp x y V (K H), R)
    | .letUnit sp V N =>
      if perfV V then (id, M) else
        let (K, R) := splitDiv env k N
        (fun H => .letUnit sp V (K H), R)
    | .loop sp ℓ src V M₁ N =>
      if perfV V || perf M₁ then (id, M) else
        let (K, R) := splitDiv env k N
        (fun H => .loop sp ℓ src V M₁ (K H), R)
    | M => (id, M)

/-- `main` with `main_div_error` (`lib/arith.bc`) around its body when the body performs
`Fail[DivError]` and handles it nowhere (SPEC §39), as the platform's handlers serve the system
interface (SPEC §34): a division's error unwinds what `main` built, the handler writes it on
standard error, and `main` answers `inr ()`, which the runtime reports as a failing exit status.
`main : F A` becomes `main : F (A + 1)`. The handler is around the rest of the body from its
first statement that performs it: what comes before (reading the input, which loops over a
capability `main` holds) runs outside it, as it cannot fail. A handler of `Fail[DivError]` inside
`main` is innermost, as any is. -/
def divMain (env : Env) (sp : Span) (C : CTy) (M : Comp) : EM (CTy × Comp) := do
  unless (rowC env fuel M).any env.isDivInst do return (C, M)
  let some _ := env.chandler? mainDivHandler | return (C, M)
  let A ← match C with
    | .ret _ A => pure A
    | _ => throw ⟨sp, "`main` returns a loop and a division's error may reach it: handle " ++
        "`Fail[DivError]` in `main` (`with default(…) { … }`); `main_div_error` around a loop is " ++
        "not provided (SPEC §39)"⟩
  let (K, M) := splitDiv env fuel M
  if let some c := ["stdin", "stdout", "stderr"].find? (M.lentNames true).contains then
    throw ⟨sp, s!"`main` uses the cell `{c}` and a division's error may reach it: " ++
      s!"`{mainDivHandler}` would abandon the cell; handle `Fail[DivError]` in `main` " ++
      "(`with default(…) { … }`), or perform the stream's effect instead of naming its cell " ++
      "(SPEC §39, §34)"⟩
  report sp "lowering" (s!"main: `Fail[DivError]` is served by `{mainDivHandler}`: a division's " ++
    "error unwinds, is written on standard error, and the program exits with status 1")
  modify fun s => { s with exits := true }
  let x ← fresh "fx_l"
  let b ← fresh "fx_c"
  let W : Val := .app sp (.app sp (.sugar sp (.handle mainDivHandler x [] none)) (.unit sp))
    (.thunkv sp (.lam sp ⟨b, sp⟩ (.name sp "_") M))
  pure (.ret sp (.sum sp A (.unit sp)), K (.ret sp W))

/-- What `elaborate` gives: the declarations, the reports for `bcc check`, the sites observed one
turn at a time, the capabilities `main` lends to the platform, whether `main` answers `inr ()` on a
division's error (SPEC §39), and whether `divLib` and `platform` were elaborated with the
program. -/
structure Result where
  decls : List Decl
  reports : List (Span × Report)
  perTurn : List Nat
  platform : List String
  exits : Bool := false
  withDivLib : Bool := false
  withPlatform : Bool := false
  keys : List DefKey := []

/-- The program with its effects elaborated, and the reports for `bcc check`: the effect and
handler declarations are removed, each answering handler's clauses become functions, each
function with a row is replaced by its copies for what serves it where it is called, each `with`
of an answering handler becomes a borrow block, and each of a control handler a handler site.

`divLib` is `lib/arith.bc` with what it includes, when the program does not include it: it is
elaborated first when a division can fail, which raises its `Fail[DivError]` (SPEC §39), and left
out otherwise.
`platform` is `lib/wasi.bc` when the program does not include it: it is elaborated just before
`main` when `main` is served by `main_div_error`, whose clause writes on standard error.
`[spec §18, §19, §39]` -/
def elaborate (ds : List Decl) (lib : List String := []) (hide : List Decl := [])
    (divLib : List Decl := []) (platform : List Decl := []) : Except Error Result := do
  -- `|>`, before the rest (SPEC §33).
  let ds ← match (resolvePipes ds).run {} with
    | .ok (ds, _) => pure ds
    | .error e => throw e
  -- The divisions that can fail, at their operands' width, written to raise (SPEC §39).
  let fd := if ds.any Divisions.Decl.hasCandidate then some (Instances.found ds) else none
  let withDivLib := !divLib.isEmpty && fd.any (!·.divs.isEmpty)
  -- The module and what it includes come first, a declaration the program also includes once.
  let ds := if withDivLib then divLib ++ ds.filter (!divLib.contains ·) else ds
  let fd := if withDivLib then some (Instances.found ds) else fd
  let ds := match fd with
    | some fd => Divisions.rewrite fd.divs ds
    | none => ds
  -- The recursive groups among the functions, the included libraries' among them (SPEC §20).
  -- A name two functions have (templates of one name in two modules, chosen by the arguments'
  -- types): only one that calls itself takes part in a recursive group.
  let dup (x : String) : Bool :=
    (ds.filter fun | .def_ _ m _ _ _ _ => m.name == x | _ => false).length ≥ 2
  let member (x : String) (V : Val) : Bool := !dup x || (refsV fuel V).contains x
  let groups := recGroupsOf (ds.filterMap fun
    | .def_ _ n _ _ V _ => if member n.name V then some (n.name, V) else none
    | _ => none)
  if !hasEffects ds && groups.isEmpty then return { decls := ds, reports := [], perTurn := [], platform := [] }
  let names := ds.filterMap Decl.defName
  let go : EM (List Decl × Bool) := do
    let table := match fd with
      | some fd => fd.table
      | none => Instances.table ds
    let mut env : Env := { lib, table, scope := some (TCx.ofScope ds true) }
    -- A division whose operands' width the walk could not read is taken to be able to fail.
    for (owner, sp) in (fd.map (·.unknown)).getD [] |>.reverse do
      unless lib.contains ((owner.splitOn "@").headD "") do
        report sp "lowering" ("a division whose operands' width is not known where effects are " ++
          "resolved: it raises `Fail[DivError]` when it fails, as an integer division; ascribing " ++
          "an operand gives its width (SPEC §39)")
    let mut out : Array Decl := #[]
    -- The declarations `hide` holds (the system interface's, the platform's and the I/O
    -- library's, SPEC §34) are not reported, and leave the reports of what follows as they were.
    let mut restore : Option Bool := none
    let mut todo : List Decl := ds
    let mut spliced := false
    for _ in [0:ds.length + platform.length + 1] do
      let d :: rest := todo | break
      todo := rest
      -- The platform, for `main_div_error`'s standard error, just before `main` (SPEC §39).
      if let .main msp _ M := d then
        let envM := { env with owner := Instances.ownerKey "main" msp, ownerTps := [] }
        if !spliced && !platform.isEmpty && (env.chandler? mainDivHandler).isSome &&
            (rowC envM fuel M).any env.isDivInst then
          spliced := true
          todo := platform ++ d :: rest
          continue
      if let some q := restore then modify fun s => { s with quiet := q }
      restore := none
      if hide.contains d then
        restore := some (← get).quiet
        modify fun s => { s with quiet := true }
      match d with
      | .effect sp e tps ops =>
        if (env.eff? e.name).isSome then throw ⟨e.span, s!"the effect `{e.name}` is declared twice"⟩
        for o in ops do
          if (env.op? o.name.name).isSome || names.contains o.name.name then
            throw ⟨o.name.span, s!"`{o.name.name}` is already declared: an operation's name is its own"⟩
        let sig : EffSig := ⟨e.name, tps.map (·.name), ops⟩
        unless sig.answering || ops.all (·.kind != .fn) do
          throw ⟨e.span, s!"`{e.name}` has both answering (`fn`) and control (`ctl`) operations: " ++
            "an effect has one kind"⟩
        if sig.answering && !tps.isEmpty then
          throw ⟨e.span, s!"`{e.name}` is answering and takes type parameters: not provided"⟩
        if let some o := ops.find? (fun o => o.abortive && o.kind == .ctl .unr) then
          throw ⟨o.name.span, s!"`{o.name.name}` is `multi ctl` and answers `never`: an " ++
            "operation that never resumes is cancellable, `ctl` (decision 63)"⟩
        env := { env with effs := env.effs ++ [sig],
                          ops := env.ops ++ (ops.zipIdx.map fun (o, i) => ⟨e.name, i, o⟩) }
        report sp "effect" (s!"{e.name}: " ++ ", ".intercalate (ops.map fun o =>
          s!"{o.name.name}{match o.kind with
            | .fn => ""
            | .ctl q => s!" (ctl, {match q with | .lin => "must-resume" | .cancel => "cancellable" | .unr => "unrestricted"}{
                if o.abortive then ", abortive" else ""})"}"))
      | .handler sp h st S e cs lent =>
        let some eff := env.eff? e.name
          | throw ⟨e.span, s!"no effect `{e.name}` is declared before this handler"⟩
        unless eff.answering do
          throw ⟨e.span, s!"`{e.name}` has control operations: its handler is written " ++
            s!"`handler {h.name}[…](…) for {e.name}[…] -> R \{ return(x: A) -> …; op(…) -> … }`"⟩
        let hs : HSig := ⟨h.name, e.name, st, S, cs, sp, lent, false⟩
        for o in eff.ops do
          unless cs.any (·.name.name == o.name.name) do
            throw ⟨sp, s!"the handler `{h.name}` has no clause for `{o.name.name}`"⟩
        for c in cs do
          let some o := eff.ops.find? (·.name.name == c.name.name)
            | throw ⟨c.name.span, s!"`{c.name.name}` is not an operation of `{e.name}`"⟩
          out := out.push (← clauseDef env hs o c)
        env := { env with handlers := env.handlers ++ [hs] }
        report sp "lowering" (s!"handler {h.name} ({e.name}): call — each clause resumes once, in " ++
          "tail position (fun): a direct call on the lent " ++
          (if lent then "capability, its state lent to the clause" else "state (withswap)") ++
          ", with no allocation and no dispatch")
      | .chandler _ ch =>
        let some eff := env.eff? ch.eff.name
          | throw ⟨ch.eff.span, s!"no effect `{ch.eff.name}` is declared before this handler"⟩
        if eff.answering then
          throw ⟨ch.eff.span, s!"`{ch.eff.name}` is answering: its handler is written " ++
            s!"`handler {ch.name.name}(s: S) for {ch.eff.name} \{ op(x) -> … }`"⟩
        unless ch.effArgs.length == eff.tps.length do
          throw ⟨ch.eff.span, s!"`{ch.eff.name}` takes {eff.tps.length} type argument(s)"⟩
        -- A handler's lifetime parameter is the meet of the lifetimes in scope at each `with`
        -- (SPEC §32): a bound on it is not provided.
        for (a, b) in ch.lps do
          match b with
          | .top _ => pure ()
          | _ => throw ⟨a.span, s!"the lifetime parameter `'{a.name}` of the handler " ++
              s!"`{ch.name.name}` has a bound: a handler's lifetime is the meet of the lifetimes in " ++
              "scope at each `with`, and a bound on it is not provided"⟩
        env := { env with chandlers := env.chandlers ++ [ch] }
      | .def_ sp n ps A V mk =>
        env := { env with sigs := (n.name, A) :: env.sigs, owner := Instances.ownerKey n.name n.span,
                          ownerTps := ps.map (·.name) }
        if isLayerTy (ps.map (·.name)) A then
          env := { env with layers := (n.name, .def_ sp n ps A V mk) :: env.layers }
        modify fun s => { s with quiet := lib.contains n.name }
        -- Computation parameters (SPEC §33): a call of the function is a call of its copy for its
        -- arguments, and a call of such a parameter performs what it provides.
        let cps := compParamsOf sp n.name A V
        if !cps.isEmpty then
          if (groups.find? (·.contains n.name)).isSome && member n.name V then
            throw ⟨n.span, s!"`{n.name}` is recursive and takes a computation parameter: not provided " ++
              "(SPEC §33)"⟩
          if let some f := (fnParts sp n.name A V).toOption then
            if let some fsp := forOverParam (cps.map (·.2.1)) fuel f.body then
              throw ⟨fsp, s!"a `for` over a call of a computation parameter of `{n.name}`: not " ++
                "provided (its loop's variables would be threaded through the argument, SPEC §33 " ++
                "*Open*); handle the parameter's iteration effect with a handler, `f(()) |> h`"⟩
          env := { env with comps := (n.name, cps) :: env.comps }
        if let some G := (groups.find? (·.contains n.name)).filter fun _ => member n.name V then
          -- A recursive function is found by its name, before the types that choose among
          -- templates of one name are known: a call of a name it shares is rejected (`fnCall`).
          if dup n.name then
            if env.clashes.contains n.name then
              throw ⟨n.span, s!"`{n.name}` is declared twice, and calls itself"⟩
            env := { env with clashes := n.name :: env.clashes }
          -- A member of a recursive group: the group is declared at its last member.
          if G.getLast? == some n.name then
            env ← defineGroup env (ds.filterMap fun
              | .def_ sp' m ps' A' V' mk' =>
                if G.contains m.name && member m.name V' then some (sp', m, ps', A', V', mk')
                else none
              | _ => none)
          continue
        let names := rowNames mk
        let (written, mk) := splitRow mk
        (env.checkWritten n.span n.name written names : Except Error Unit)
        let envR := if cps.isEmpty then env else
          { env with cbRows := cps.map fun (_, x, es) => (x, es.map fun (e, As) => ⟨e.name, some As, none⟩) }
        let row := rowV envR fuel V
        for i in row do
          unless written.isEmpty || written.any (·.1.name == i.eff) do
            throw ⟨n.span, s!"`{n.name}` performs `{i.eff}`, which its written row does not list"⟩
        -- A division's instance is always known: a written row lists it as it lists any other.
        if !written.isEmpty && row.any env.isDivInst &&
            !written.any (fun (e, As) => e.name == "Fail" && env.sameArgs As [Instances.divErrorTy]) then
          throw ⟨n.span, s!"`{n.name}` raises `Fail[DivError]`, a division's error (SPEC §39), which " ++
            "its written row does not list"⟩
        -- Each instance's entry: the written one it is (SPEC §38), or as inferred, its type arguments
        -- from its argument's type or from what the function calls.
        let mut row' : List Inst := []
        if written.isEmpty then row' ← (Env.settle n.span n.name row : Except Error _)
        for i in if written.isEmpty then [] else row do
          match ← (env.slotOf n.span n.name written names i : Except Error _) with
          | some j =>
            let k := ((env.eff? i.eff).map (·.tps.length)).getD 0
            unless (j.args.getD []).length == k do
              throw ⟨n.span, s!"`{i.eff}` takes {k} type argument(s)"⟩
            row' := env.addInst row' j
          | none => throw ⟨n.span, s!"`{n.name}` performs `{i.eff}`, which its written row does not list"⟩
        let d₀ : Decl := .def_ sp n ps A V mk
        -- A row on a value that is not a function: a function with a row used as a value, which
        -- is reported as such.
        if !row'.isEmpty && (fnParts sp n.name A V).toOption.isNone then
          discard (trV fuel { env, caps := [] } [] V)
        if !row'.isEmpty then
          env := { env with fns := env.fns ++ [{ name := n.name, row := row', decl := d₀ }] }
          report sp "row" (s!"{n.name}: " ++ ", ".intercalate (row'.map fun i =>
            ((i.name.map (· ++ ": ")).getD "") ++ match i.args with
            | some (_ :: _) => s!"{i.eff}[{", ".intercalate ((i.args.getD []).map (VTy.pp · 0))}]"
            | _ => i.eff))
        else if !cps.isEmpty then
          -- Used only through its copies (`blockCall`).
          env := { env with plain := (n.name, d₀) :: env.plain }
        else
          env := { env with plain := (n.name, d₀) :: env.plain }
          let before := (← get).made.size
          let (bs, V') ← trV fuel { env, caps := [] } [] V
          unless bs.isEmpty do throw ⟨V.span, "internal error: a definition's value was taken apart"⟩
          out := out ++ ((← get).made.extract before).map (·.2)
          out := out.push (.def_ sp n ps A V' mk)
      | .main sp C M =>
        env := { env with owner := Instances.ownerKey "main" sp, ownerTps := [] }
        modify fun s => { s with quiet := false }
        let before := (← get).made.size
        let (C, M) ← divMain env sp C M
        let pcs ← platformMain env sp M
        modify fun s => { s with platform := pcs.map (·.var) }
        let M' ← trC fuel { env, caps := pcs } [] false M
        out := out ++ ((← get).made.extract before).map (·.2)
        out := out.push (.main sp C M')
      | d => out := out.push d
    pure (out.toList, spliced)
  match go.run {} with
  | .ok ((ds, spliced), st) =>
    pure { decls := ds, reports := st.reports.toList, perTurn := st.perTurn, platform := st.platform,
           exits := st.exits, withDivLib, withPlatform := spliced,
           keys := st.keys.toList }
  | .error e => throw e

end Frontend.Elab.Effects

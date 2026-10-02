import Frontend.Parser
import Frontend.Print
import Frontend.Elab.Subst

/-!
# Frontend — Elab — effects and handlers  `[spec §18, §19, §20, §21, §22]`

An effect declares operations, each **answering** (`fn`) or **control** (`ctl`, with the
structural qualifier of its continuation: affine by default, `linear ctl`, `multi ctl`). An effect
is one or the other. This pass resolves every operation to the handler that serves it, before the
rest of the sugar; it knows no effect by name.

* **Answering effects** are capabilities (§18): `handler h(s: S) for E { op(x) -> e }` gives each
  clause as a function over a `mut` borrow of the state,

      fn h__op<'l>(c: mut 'l S, x: A) -> mut 'l S * B = let r = modify c { s -> M; (s, r) }; (c, r)

  `with h(e) { S }` is a borrow block of the state's cell whose callback's parameter is the
  capability, and an operation call `op(v)` is a call of the innermost handler's clause on it,
  which hands it back. The capability is threaded as a `let mut` variable is.
* **Control effects** are the kernel's (§19). Each `with h(args) { S }` of a control handler is a
  handler site with a static name `n` of its own, and an operation is resolved lexically to the
  innermost site of its effect: `perform[n.i](v)`, or `abort[n.i](v)` for an abortive operation
  (answer `0` at a qualifier with weakening). The site becomes the kernel's `handle[n]` with the
  handler's clauses, assembled where the types are known (`VSugar.hndCtl`, `Frontend/Sugar.lean`).
  A handler may perform the operations of its own row (`with E₂[…]` after `for`), which resolve to
  the sites around its `with`. Its clauses are `!` code, and what they use is passed to them
  (§21): a handler whose operations are all abortive runs its clauses after it, and one whose
  operations resume has a state, its parameters and the capabilities its clauses use; `k(v)`
  resumes.
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

* **A computation parameter** (§22) is a parameter of a function type. A call that passes a
  callback there, a closure or a function with a row, is a call of the function's copy for the
  callback's profile: the callback is a closure value, its `!` code (`cbCode`), which takes its
  capabilities and its environment first and hands them back, and its environment, the variables
  it captures, a type parameter of the copy (`cbCopyOf`). Its provided effects are at the
  function's ports, and a `with` around a call of it is named by the port; the rest tunnel. A
  computation parameter is called (`cbParamCall`), or passed on as it is (`cbCall`).
* **`e |> g(a, …)`** (decision 50) is `with g(a, …) { e }` for a handler, `g({ _ -> e }, a, …)`
  when `g`'s first parameter is a computation parameter, and `g(e, a, …)` otherwise (`pipeOf`).

What is not provided, with the message that says so: an operation inside a closure or block that
is not run in place nor passed at a computation parameter, and a function with a row passed as a
value elsewhere (a stored callback, R6 of decision 57); a callback that binds a variable it
captures again; a provided answering effect; a provided effect that resumes, of a callback called
outside the callee's handlers of it (R2c); two ports of one effect under one site; a recursion that
passes a new callback at each level; a lend `&mut x` in the arguments of a call that threads a
capability; an operation of an answering effect inside a clause; an effect with both kinds of
operation; type parameters on an answering effect; a function with a row whose result is a
computation (a loop or a generator).
-/

namespace Frontend.Elab.Effects

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

/-- An answering handler: its name, its effect, its state and its clauses. -/
structure HSig where
  name : String
  eff : String
  st : Ident
  S : VTy
  clauses : List Clause
  sp : Span

/-- An instance of an effect: its type arguments, when they are determined. -/
structure Inst where
  eff : String
  args : Option (List VTy)
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

/-- A **computation parameter** of a function (SPEC §22): a parameter whose written type is a
function type, `!(A => B)` or `A => B`. Its index in the parameter tuple, its name, the argument
and result types of its function type as written, whether it is `!`, and its **provided row**, the
effects the function serves for the callback passed there (written `x: A => B with E₁, …`). -/
structure CParam where
  idx : Nat
  name : String
  A : VTy
  B : VTy
  bang : Bool
  prov : List (Ident × List VTy)

/-- A recursive group (SPEC §20): the functions of one strongly connected component of the calls,
each taken apart (`FnParts`), in declaration order. The group is named by its first member. -/
structure RGroup where
  name : String
  members : List (String × FnParts)
  sp : Span

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
  /-- Every function declared so far, as written (its marks without rows): a function with a
  computation parameter is copied for the callbacks passed to it (SPEC §22). -/
  defs : List (String × Decl) := []
  /-- The computation parameters of each function that has one (SPEC §22). -/
  cparams : List (String × List CParam) := []
  /-- The names of the externs declared so far: not captured by a callback. -/
  externs : List String := []
  /-- The number of parameters of each `fn` declared so far. -/
  arity : List (String × Nat) := []
  /-- The effects that stand for a callback's environment in a copy (SPEC §22): answering, served
  by the environment's capability. -/
  envEffs : List String := []

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
  /-- A callback's environment (SPEC §22): the tuple of the variables it captures, of the type
  `thr`, passed and handed back as a capability is; `some true` when the callback assigns one of
  them. -/
  env : Option Bool := none

/-- A capability's type: `mut 'l S`, or the threaded variable's `W`. -/
def Cap.ty (sp : Span) (c : Cap) : VTy := match c.thr with
  | some W => .name sp W
  | none => .mut sp (.var sp c.life) c.h.S

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
  served : List (String × Nat)
  /-- Under a heap driver: a call of itself is a call of the self-reference `fx_rself{j}` of the
  group's machine source, which the typed elaboration turns into a request (`recMachine`). -/
  deep : Bool := false
  /-- The computation parameters of the member the group's copy was made for, each passed the
  copy's callback (SPEC §22): the member's index, and the positions and names of the parameters.
  A call of that member passes them on. -/
  cbArgs : List (Nat × List (Nat × String)) := []
  /-- When made for callbacks (SPEC §22), the record's fields are generic in the lifetimes of the
  capabilities, named so here, so that a callback that calls the group calls it with the
  capabilities it holds: the fields' row and results. -/
  poly : List String := []
  rowR : Row := .nil
  Ts : List VTy := []

/-- The state of the elaboration: counters for fresh names and site names, the reports for
`bcc check`, and the copies made (finished ones in `made`, in the order they were finished). -/
structure St where
  fresh : Nat := 0
  site : Nat := 1
  /-- The ports (SPEC §22): the static name at which a callback performs an effect `E` that the
  function `f` provides it, one per `(f, E)`. -/
  ports : List ((String × String) × Nat) := []
  reports : Array (Span × String) := #[]
  made : Array (String × Decl) := #[]
  started : List String := []
  /-- Elaborating a library declaration: nothing is reported. -/
  quiet : Bool := false

abbrev EM := StateT St (Except Error)

def fresh (pre : String) : EM String :=
  modifyGet fun s => (s!"{pre}{s.fresh}", { s with fresh := s.fresh + 1 })

/-- A fresh static name for a handler site. -/
def freshSite : EM Nat := modifyGet fun s => (s.site, { s with site := s.site + 1 })

/-- The port of the effect `e` provided by the function `f` (SPEC §22), made on first use. -/
def portOf (f e : String) : EM Nat := do
  if let some n := (← get).ports.lookup (f, e) then return n
  let n ← freshSite
  modify fun s => { s with ports := ((f, e), n) :: s.ports }
  pure n

/-- A report for `bcc check` (SPEC §18, #126): its kind (`effect`, `row`, `lowering`, `call`) and
its text, at `sp`. -/
def report (sp : Span) (kind : String) (msg : String) : EM Unit :=
  modify fun s => if s.quiet then s else { s with reports := s.reports.push (sp, kind ++ " " ++ msg) }

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

/-- The effect is answering (an environment's effect is, SPEC §22). -/
def Env.answering (env : Env) (e : String) : Bool :=
  env.envEffs.contains e || ((env.eff? e).map (·.answering)).getD false

/-- The computation parameters of the function `x`. -/
def Env.cparamsOf (env : Env) (x : String) : List CParam := (env.cparams.lookup x).getD []

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

/-- The parameter tuple's type of a function type as written, under its `!` and lifetimes. -/
def paramTyOf : VTy → Option VTy
  | .bang _ A | .all _ _ _ A => paramTyOf A
  | .lolli _ P _ => some P
  | _ => none

/-- The first `n` components of a right-nested tuple type, the last one the rest. -/
def splitTy : Nat → VTy → List VTy
  | 0, _ => []
  | 1, A => [A]
  | n + 1, .tensor _ A B => A :: splitTy n B
  | _, A => [A]

/-- The `n` components of a right-nested tuple, when it has them. -/
def splitVal : Nat → Val → Option (List Val)
  | 0, .unit _ => some []
  | 0, _ => none
  | 1, V => some [V]
  | n + 1, .pair _ V W => (splitVal n W).map (V :: ·)
  | _, _ => none

/-- A right-nested tuple of the values `Vs` (`()` when there are none). -/
def tupleOf (sp : Span) : List Val → Val
  | [] => .unit sp
  | [V] => V
  | V :: Vs => .pair sp V (tupleOf sp Vs)

/-- The names of a `fn`'s parameters, as the parser binds them from the tuple `p`
(`Parser.bindParams`): `let () = p`, `x <- return p`, `let (x, y) = p`, or `let (x, r) = p` with
`r` a generated name holding the rest. -/
def paramNames (p : String) : Nat → Comp → Option (List Ident)
  | 0, _ => none
  | _ + 1, .letUnit _ (.var _ q) _ => if q == p then some [] else none
  | _ + 1, .bind _ x _ (.ret _ (.var _ q)) _ _ => if q == p then some [x] else none
  | k + 1, .letPair _ x y (.var _ q) M =>
    if q != p then none
    else if y.name.startsWith "io_p" then (paramNames y.name k M).map (x :: ·)
    else some [x, y]
  | _ + 1, _ => none

/-- A written function type: its argument and result types, and whether it is `!`. -/
def fnTyOf : VTy → Option (VTy × VTy × Bool)
  | .bang _ (.lolli _ A B) => some (A, B, true)
  | .lolli _ A B => some (A, B, false)
  | .bang _ (.thunk _ (.arr _ A (.ret _ B))) => some (A, B, true)
  | .thunk _ (.arr _ A (.ret _ B)) => some (A, B, false)
  | _ => none

/-- The components of a call's argument tuple, each with whether its parameter's written type is
a stored generator's (`U (pull A B R)`), and the effects its parameter provides (SPEC §22). -/
def Env.argsOf (env : Env) (f : String) (W : Val) : List (Val × Bool × List String) :=
  match (env.sigs.lookup f).bind paramTyOf with
  | some P =>
    let byArity : Option (List (Val × Bool × List String)) := do
      let n ← env.arity.lookup f
      let Vs ← splitVal n W
      let Ps := splitTy n P
      let cps := env.cparamsOf f
      pure ((Vs.zip Ps).zipIdx.map fun ((V, A), k) =>
        (V, isPullTy A, ((cps.find? (·.idx == k)).map fun cp => cp.prov.map (·.1.name)).getD []))
    byArity.getD (go fuel P W)
  | none => [(W, false, [])]
where
  go : Nat → VTy → Val → List (Val × Bool × List String)
    | k + 1, .tensor _ A B, .pair _ V W => (V, isPullTy A, []) :: go k B W
    | _, P, W => [(W, isPullTy P, [])]

/-- The components of a call's argument tuple, each with whether its parameter's written type is
a stored generator's (`U (pull A B R)`). -/
def Env.pullArgs (env : Env) (f : String) (W : Val) : List (Val × Bool) :=
  (env.argsOf f W).map fun (V, p, _) => (V, p)

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
  | .fn => .aff

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

/-- The row entries of the sites `ss`, in order: `n.i q A ~> B`. -/
def Env.rowOf (env : Env) (ss : List Site) : Row :=
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
      | P, A => if same P A then some σ else none

/-- `matchTyBy` with types compared as written. -/
def matchTy (tps : List String) (σ : TySubst) (P A : VTy) : Option TySubst :=
  matchTyBy (fun a b => a.strip == b.strip) tps σ P A

/-- The type names `A` mentions among `tps`. -/
def mentions (tps : List String) (A : VTy) : Bool :=
  tps.any fun x => (A.subst [(x, .unk .none)]).strip != A.strip

/-! ### Rows -/

/-- The name a call applies: `f(…)`, `f[A](…)`, `f ['x](…)`. -/
def headName : Val → Option String
  | .var _ f | .defApp _ f _ => some f
  | .inst _ V _ | .unbang _ V => headName V
  | _ => none

/-- An instance of `e` added to a row: one instance per effect, a determined one winning. -/
def addInst (r : List Inst) (i : Inst) : List Inst :=
  match r.find? (·.eff == i.eff) with
  | none => r ++ [i]
  | some j => if j.args.isNone && i.args.isSome then r.map (fun k => if k.eff == i.eff then i else k)
    else r

def union (a b : List Inst) : List Inst := b.foldl addInst a

def without (r : List Inst) (e : String) : List Inst := r.filter (·.eff != e)

/-- What a call of `g` performs: its row, and for a member of a recursive group the rows of the
layers in scope (`inLayers`). -/
def Env.callRow (env : Env) (g : FSig) : List Inst :=
  if g.group.isNone then g.row
  else env.inLayers.foldl (fun r L => union r (((env.fn? L).map (·.row)).getD [])) g.row

/-- The instance an operation call of `o` performs: determined when its effect takes no type. -/
def Env.opInst (env : Env) (o : OpSig) : Inst :=
  ⟨o.eff, match env.eff? o.eff with
    | some e => if e.tps.isEmpty then some [] else none
    | none => none⟩

/-- The instances a control handler's own row adds at a `with`: determined when its patterns
mention none of the handler's type parameters. -/
def handlerRow (h : CHandler) : List Inst :=
  let tps := h.tps.map (·.name)
  h.row.map fun (e, As) => ⟨e.name, if As.any (mentions tps) then none else some As⟩

/-- A call of a function that performs an iteration effect (SPEC §15): the callee's name, its
signature, the instance of the iteration effect, and the callee and argument as written. -/
def Env.iterCall? (env : Env) : Val → Option (String × FSig × Inst × Val × Val)
  | .app _ f W => do
    let x ← headName f
    let g ← env.fn? x
    let i ← g.row.find? (env.iterEff ·.eff)
    pure (x, g, i, f, W)
  | _ => none

/-- An instance at the type arguments `σ`. -/
def Inst.subst (σ : TySubst) (i : Inst) : Inst := { i with args := i.args.map (·.map (·.subst σ)) }

/-- The type parameters of the function `x`, as declared. -/
def Env.tpsOf (env : Env) (x : String) : List String :=
  match env.defs.lookup x with
  | some (.def_ _ _ ps _ _ _) => ps.map (·.name)
  | _ => []

mutual
/-- The effects a value performs, outside the `with`s that handle them. A call of a function
performing an iteration effect, as an argument at a stored generator's parameter, is the stored
generator: it does not perform the iteration effect. What a callback performs at a computation
parameter that provides it is the callee's (SPEC §22). -/
def rowV (env : Env) : Nat → Val → List Inst
  | 0, _ => []
  | n + 1, V => match V with
    | .app _ (.app _ (.sugar _ (.handle h _ _)) P) (.thunkv _ (.lam _ _ _ M)) =>
      let inner := rowC env n M
      let inner := match env.handler? h, env.chandler? h with
        | some hs, _ => without inner hs.eff
        | none, some ch => union (without inner ch.eff.name) (handlerRow ch)
        | none, none =>
          if env.driver? h then match env.exhEff? with
            | some e => without inner e.name
            | none => inner
          else if (env.layer? h).isSome then union inner ((env.fn? h).map (·.row) |>.getD [])
          else inner
      union (rowV env n P) inner
    | .app _ f W =>
      let head := match headName f with
        | some x => match env.op? x, env.fn? x with
          | some o, _ => [env.opInst o]
          | none, some g =>
            let σ := callSubst env n f x W
            (env.callRow g).map (·.subst σ)
          | none, none => rowV env n f
        | none => rowV env n f
      let args := match headName f with
        | some x => (env.argsOf x W).foldl (fun r (V, pull, prov) =>
            union r ((pullRow env n pull V).filter fun i => !prov.contains i.eff)) []
        | none => rowV env n W
      union head args
    | .var _ x => match env.fn? x with
      | some g => env.callRow g
      | none => []
    | .pair _ V W => union (rowV env n V) (rowV env n W)
    | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
    | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => rowV env n V
    | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => rowC env n M
    | _ => []

/-- The effects a computation performs, outside the `with`s that handle them. -/
def rowC (env : Env) : Nat → Comp → List Inst
  | 0, _ => []
  | n + 1, M => match M with
    | .ret _ V | .absurd _ V => rowV env n V
    | .bind _ _ (some A) (.ret _ V) N _ => union (pullRow env n (isPullTy A) V) (rowC env n N)
    | .bind _ _ _ M N _ | .with_ _ M N => union (rowC env n M) (rowC env n N)
    | .letUnit _ V M | .letPair _ _ _ V M => union (rowV env n V) (rowC env n M)
    | .case _ V _ M _ N =>
      union (rowV env n V) (union (rowC env n M) (rowC env n N))
    | .for_ _ _ V M N =>
      -- A `for` over a call that performs an iteration effect handles it.
      let src := match env.iterCall? V with
        | some (_, _, i, _, _) => without (rowV env n V) i.eff
        | none => rowV env n V
      union src (union (rowC env n M) (rowC env n N))
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

/-- The type parameters of `x` that a call `f(W)` of it determines for the effects (SPEC §22):
written, `x[T, …](…)`, or read off the instances of what the callbacks at its computation
parameters perform, against the rows those parameters provide. -/
def callSubst (env : Env) : Nat → Val → String → Val → TySubst
  | 0, _, _, _ => []
  | n + 1, f, x, W =>
    let tps := env.tpsOf x
    if tps.isEmpty then [] else
    let σ₀ : TySubst := match f with
      | .defApp _ _ As => if As.length == tps.length then tps.zip As else []
      | _ => []
    let cps := env.cparamsOf x
    (env.argsOf x W).zipIdx.foldl (fun σ ((V, _, _), k) =>
      match cps.find? (·.idx == k) with
      | some cp =>
        let r := rowV env n V
        cp.prov.foldl (fun σ (e, Ps) => match r.find? (·.eff == e.name) with
          | some ⟨_, some Bs⟩ => (Ps.zip Bs).foldl (fun σ (P, B) => (matchTy tps σ P B).getD σ) σ
          | _ => σ) σ
      | none => σ) σ₀
end

/-- A value is a callback for a computation parameter (SPEC §22): a closure, a function with a row,
or a computation parameter of the copy being elaborated (`cbs`). -/
def cbArg? (env : Env) (cbs : List String) : Val → Option (Option (Ident × Comp))
  | .thunkv _ (.lam _ x _ M) | .bangThunkv _ (.lam _ x _ M) => some (some (x, M))
  | V => match headName V with
    | some g => if cbs.contains g || (env.fn? g).isSome then some none else none
    | none => none

/-- A call of `x` that passes a callback at a computation parameter (SPEC §22): `x` has a
computation parameter that provides an effect, or one whose argument performs one. -/
def Env.isCbCall (env : Env) (cbs : List String) (x : String) (W : Val) : Bool :=
  let cps := env.cparamsOf x
  !cps.isEmpty && (cps.any (!·.prov.isEmpty) ||
    (env.argsOf x W).zipIdx.any fun ((V, _, _), k) =>
      cps.any (·.idx == k) && (cbArg? env cbs V).isSome && !(rowV env fuel V).isEmpty)

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
  | [], x, t, N => pure (.bind sp ⟨x, sp⟩ none (.ret sp (.var sp t)) N false)
  | [c], x, t, N => pure (.letPair sp ⟨c.var, sp⟩ ⟨x, sp⟩ (.var sp t) N)
  | c :: cs, x, t, N => do
    let r ← fresh "fx_r"
    pure (.letPair sp ⟨c.var, sp⟩ ⟨r, sp⟩ (.var sp t) (← unpack sp cs x r N))

/-- `t <- M; K`, with the bindings `M` begins with moved before it (they bind fresh names, or
capabilities that `K` binds again), so that the head of the binding is one statement. -/
def bindFlat (sp : Span) (t : String) (A : Option VTy) : Comp → Comp → Comp
  | .bind sp' a B M N lin, K => .bind sp' a B M (bindFlat sp t A N K) lin
  | .letPair sp' x y V M, K => .letPair sp' x y V (bindFlat sp t A M K)
  | .letUnit sp' V M, K => .letUnit sp' V (bindFlat sp t A M K)
  | M, K => .bind sp ⟨t, sp⟩ A M K false

/-- A terminal that leaves a loop: `break`, `break e`, `continue`, or `return e` from a loop's
body. -/
def isExit : Val → Bool
  | .sugar _ .brk | .app _ (.sugar _ .brk) _ | .app _ (.sugar _ .retE) _ | .sugar _ .cont => true
  | _ => false

/-- A binding put before a value: the computation that follows it is its argument. -/
abbrev Bind := Comp → EM Comp

def chain : List Bind → Comp → EM Comp
  | [], M => pure M
  | b :: bs, M => do b (← chain bs M)

/-- A computation may loop: it has a `while` or `loop`, or a `for` whose source is not a count
`a..b` (a loop over a view is total too, but its source's type is not known here). -/
def mayLoop : Nat → Comp → Bool
  | 0, _ => true
  | k + 1, M => match M with
    | .for_ _ _ (.app _ (.sugar _ .count) _) B N => mayLoop k B || mayLoop k N
    | .for_ .. => true
    | .bind _ _ _ M N _ | .with_ _ M N => mayLoop k M || mayLoop k N
    | .letUnit _ _ M | .letPair _ _ _ _ M | .lam _ _ _ M | .lamL _ _ _ M => mayLoop k M
    | .case _ _ _ M _ N => mayLoop k M || mayLoop k N
    | _ => false

/-- `w <- perform[n.i] (V, w)`: an operation at a `for`'s site, which threads `w`. -/
def threadedPerform (sp : Span) (n i : Nat) (V : Val) (w : String) : Bind := fun N =>
  pure (.bind sp ⟨w, sp⟩ none (.perform sp n i (.pair sp V (.var sp w))) N false)

/-- The plain calls of a value, bound first in the order its evaluation runs them in (innermost
and leftmost first), so that an effectful call lifted out of it keeps its place among them. A
sugar form (an operator, `*e`, a borrow block) is not a call and stays where it is. -/
def liftCalls : Nat → Val → StateT (List Bind) EM Val
  | 0, V => pure V
  | n + 1, V => match V with
    | .app sp f W => do
      match f with
      | .sugar .. | .app _ (.sugar ..) _ =>
        pure (.app sp f (← liftCalls n W))
      | _ =>
        let f' ← liftCalls n f
        let W' ← liftCalls n W
        let x ← (fresh "fx_n" : EM String)
        modify (· ++ [fun N => pure (.bind sp ⟨x, sp⟩ none (.ret sp (.app sp f' W')) N false)])
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
    | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => refsV n V
    | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => refsC n M
    | _ => []

/-- The names a computation refers to. -/
def refsC : Nat → Comp → List String
  | 0, _ => []
  | n + 1, M => match M with
    | .ret _ V | .absurd _ V | .perform _ _ _ V | .abort _ _ _ V => refsV n V
    | .bind _ _ _ M N _ | .with_ _ M N => refsC n M ++ refsC n N
    | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
    | .nuOut _ M | .ascribe _ M _ | .handle _ _ _ _ M => refsC n M
    | .letUnit _ V M | .letPair _ _ _ V M => refsV n V ++ refsC n M
    | .case _ V _ M _ N | .for_ _ _ V M N => refsV n V ++ refsC n M ++ refsC n N
    | .unwind _ _ _ M D N => refsC n M ++ refsC n D ++ refsC n N
    | .force .. | .top _ => []
end

mutual
/-- The variables a value refers to that the names `bd` do not bind (free variables). -/
def fvV : Nat → List String → Val → List String
  | 0, _, _ => []
  | n + 1, bd, V => match V with
    | .var _ x | .defApp _ x _ => if bd.contains x then [] else [x]
    | .lend _ x _ => if bd.contains x.name then [] else [x.name]
    | .pair _ V W | .app _ V W => fvV n bd V ++ fvV n bd W
    | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
    | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => fvV n bd V
    | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => fvC n bd M
    | _ => []

/-- The free variables of a computation. -/
def fvC : Nat → List String → Comp → List String
  | 0, _, _ => []
  | n + 1, bd, M =>
    let v (x : Ident) : List String := if bd.contains x.name then [] else [x.name]
    match M with
    | .ret _ V | .absurd _ V | .perform _ _ _ V | .abort _ _ _ V => fvV n bd V
    | .bind _ x _ M N _ => fvC n bd M ++ fvC n (x.name :: bd) N
    | .force _ x => v x
    | .lam _ x _ M => fvC n (x.name :: bd) M
    | .app _ M x => fvC n bd M ++ v x
    | .with_ _ M N => fvC n bd M ++ fvC n bd N
    | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M | .nuOut _ M | .ascribe _ M _ =>
      fvC n bd M
    | .letUnit _ V M => fvV n bd V ++ fvC n bd M
    | .letPair _ x y V M => fvV n bd V ++ fvC n (x.name :: y.name :: bd) M
    | .case _ V x M y N => fvV n bd V ++ fvC n (x.name :: bd) M ++ fvC n (y.name :: bd) N
    | .for_ _ x V M N => fvV n bd V ++ fvC n (x.name :: bd) M ++ fvC n bd N
    | .handle _ _ hr hc M => v hr ++ v hc ++ fvC n bd M
    | .unwind _ x _ M D N => fvC n bd M ++ fvC n bd D ++ fvC n (x.name :: bd) N
    | .top _ => []
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

/-- A computation parameter in a copy made for the callback passed at it (SPEC §22): its variable,
bound to the callback's code; the ports of its provided control effects; what a call of it
performs (the provided effects, the tunneled ones and its environment's effect); and the
capabilities the code takes, in order, its environment last. -/
structure CbParam where
  name : String
  ports : List (String × Nat)
  row : List Inst
  caps : List Cap

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
  /-- In a copy made for callbacks (SPEC §22): its computation parameters. -/
  cbs : List CbParam := []
  /-- In a copy made for callbacks: the ports of the function's provided effects, by effect. -/
  ports : List (String × Nat) := []

/-- What a call of `g` performs here: its row, and for a member of a recursive group the rows of
the layers its recursion runs under. -/
def Cx.rowOf (cx : Cx) (g : FSig) : List Inst := cx.env.callRow g

/-- The computation parameter `x` of the copy being elaborated. -/
def Cx.cb? (cx : Cx) (x : String) : Option CbParam := cx.cbs.find? (·.name == x)

/-- The capabilities of `cx` for the effects `row`, in the order of `cx.caps`. -/
def Cx.need (cx : Cx) (row : List Inst) : List Cap := cx.caps.filter (fun c => row.any (·.eff == c.eff))

/-- The capabilities of `cx` for the effects `row`, in the order of `row`: those a copy for them
takes first. -/
def Cx.needIn (cx : Cx) (row : List Inst) : List Cap := row.filterMap fun i => cx.caps.find? (·.eff == i.eff)

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

/-- `V` is a call that passes a callback, or calls a computation parameter (SPEC §22). -/
def Cx.cbCallV (cx : Cx) (V : Val) : Bool :=
  match V with
  | .app _ f W => match headName f with
    | some x => (cx.cb? x).isSome || cx.env.isCbCall (cx.cbs.map (·.name)) x W
    | none => false
  | _ => false

/-- The control effects of `row`. -/
def Cx.ctl (cx : Cx) (row : List Inst) : List Inst := row.filter (!cx.env.answering ·.eff)

def Cx.ctlV (cx : Cx) (V : Val) : Bool := !(cx.ctl (rowV cx.env fuel V)).isEmpty
def Cx.ctlC (cx : Cx) (M : Comp) : Bool := !(cx.ctl (rowC cx.env fuel M)).isEmpty

/-- The capability of the effect `e` in scope. -/
def Cx.capOf (cx : Cx) (e : String) : Option Cap := cx.caps.find? (·.eff == e)

/-- The site of the control effect `e` in scope. -/
def Cx.siteOf (cx : Cx) (e : String) : Option Site := cx.sites.find? (·.eff == e)

def notInClosure (sp : Span) (e : String) : Error :=
  ⟨sp, s!"an operation of `{e}` is performed inside a closure or block that is not run in place, " ++
    "nor passed at a function's computation parameter (SPEC §22): it cannot reach its handler " ++
    "(a stored callback, R6 of decision 57, is not built)"⟩

/-- The site serving the control instance `i` here, its type arguments checked against the
instance's when both are determined. -/
def Cx.serve (cx : Cx) (sp : Span) (what : String) (i : Inst) : Except Error Site := do
  let some s := cx.siteOf i.eff
    | throw ⟨sp, s!"{what} performs `{i.eff}`, but no handler of `{i.eff}` is in scope here"⟩
  if let some As := i.args then
    unless As.map VTy.strip == s.args.map VTy.strip do
      throw ⟨sp, s!"{what} performs `{i.eff}[{", ".intercalate (As.map (VTy.pp · 0))}]`, but the " ++
        s!"handler of `{i.eff}` in scope is at `{i.eff}[{", ".intercalate (s.args.map (VTy.pp · 0))}]`"⟩
  pure s

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

/-- The variable `w` of type `W` that a `for`'s site of the iteration effect `e` threads, as a
capability. -/
def threadCap (sp : Span) (e w W : String) : Cap :=
  ⟨e, w, "", ⟨"", e, ⟨"", sp⟩, .unit sp, [], sp⟩, some W, none⟩

/-- The capabilities of a copy made for the handlers `hs`, one per answering effect of `effs`. -/
def copyCaps (effs : List String) (hs : List HSig) : List Cap :=
  (effs.zip hs).map fun (e, h) => ⟨e, "fx_c_" ++ e.toLower, "fx_l_" ++ e.toLower, h, none, none⟩

/-- A body taking the capabilities `cs` first: `fx_pp : mut 'l₁ S₁ * (… * P)`, taken apart into
the capabilities and the original parameter `p`. -/
def takeCaps (sp : Span) (cs : List Cap) (f : FnParts) (body : Comp) : EM FnParts := do
  let pp ← fresh "fx_pp"
  let body ← unpack sp cs f.p.name pp body
  let lives := (cs.filter (·.thr.isNone)).map fun c => ((⟨c.life, sp⟩ : Ident), Life.top sp)
  pure { f with lives := lives ++ f.lives, P := capsTy sp cs f.P, T := capsTy sp cs f.T,
                p := ⟨pp, sp⟩, body }

/-- A `with`, a `for` over a call that performs an iteration effect, or a stored generator, in a
value, outside nothing: the elaboration must reach it. -/
def withInV (env : Env) : Nat → Val → Bool
  | 0, _ => false
  | k + 1, V => match V with
    | .app _ (.app _ (.sugar _ (.handle ..)) _) _ => true
    | .app _ f W =>
      let pull := match headName f with
        | some x => (env.pullArgs x W).any fun (V, p) => p && (env.iterCall? V).isSome
        | none => false
      let cb := match headName f with
        | some x => env.isCbCall [] x W
        | none => false
      pull || cb || withInV env k f || withInV env k W
    | .pair _ f W => withInV env k f || withInV env k W
    | .inl _ V | .inr _ V | .ascribe _ V _ | .roll _ V | .unroll _ V | .boxed _ _ V
    | .unbox _ V | .unbang _ V | .inst _ V _ | .sub _ V _ | .shorten _ _ _ _ V => withInV env k V
    | .run _ M | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M => withInC k M
    | _ => false
where
  withInC : Nat → Comp → Bool
    | 0, _ => false
    | k + 1, M => match M with
      | .ret _ V | .absurd _ V => withInV env k V
      | .bind _ _ (some A) (.ret _ V) N _ =>
        (isPullTy A && (env.iterCall? V).isSome) || withInV env k V || withInC k N
      | .bind _ _ _ M N _ | .with_ _ M N => withInC k M || withInC k N
      | .letUnit _ V M | .letPair _ _ _ V M => withInV env k V || withInC k M
      | .for_ _ _ V M N => (env.iterCall? V).isSome || withInV env k V || withInC k M || withInC k N
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

/-- `V` has, outside nested computations, a call that passes a callback or calls a computation
parameter (SPEC §22). -/
def cbIn (cx : Cx) : Nat → Val → Bool
  | 0, _ => false
  | k + 1, V => cx.cbCallV V || match V with
    | .app _ f W | .pair _ f W => cbIn cx k f || cbIn cx k W
    | .inl _ V | .inr _ V | .ascribe _ V _ | .roll _ V | .unroll _ V | .boxed _ _ V | .unbox _ V
    | .unbang _ V | .inst _ V _ | .sub _ V _ | .shorten _ _ _ _ V => cbIn cx k V
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
        if !(cx.needV V).isEmpty || cx.ctlV V || cx.lcallV V || cx.cbCallV V then do
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
  | [x], M => pure (.bind sp x none (.ret sp (.var sp p)) M false)
  | [x, y], M => pure (.letPair sp x y (.var sp p) M)
  | x :: xs, M => do
    let r ← fresh "fx_p"
    pure (.letPair sp x ⟨r, sp⟩ (.var sp p) (← bindParams sp r xs M))

/-- A computation with `f` applied at each terminal reached through tail positions. -/
def wrapTerms (f : Comp → Comp) : Comp → Comp
  | .bind sp x A M N lin => .bind sp x A M (wrapTerms f N) lin
  | .letUnit sp V M => .letUnit sp V (wrapTerms f M)
  | .letPair sp x y V M => .letPair sp x y V (wrapTerms f M)
  | .case sp V x M y N => .case sp V x (wrapTerms f M) y (wrapTerms f N)
  | .for_ sp x V M N => .for_ sp x V M (wrapTerms f N)
  | T => f T

/-- A name made of `s`, its characters other than letters, digits and `_` replaced by `_`. -/
def sanitize (s : String) : String := s.map fun c => if c.isAlphanum || c == '_' then c else '_'

/-- The effect that stands for the environment of the callback at the parameter `k` of the copy
`name` (SPEC §22). -/
def envEffName (name : String) (k : Nat) : String := s!"fx_env_{name}_{k}"

/-- A handler with no name, for capabilities that are not a handler's state. -/
def noHandler (sp : Span) : HSig := ⟨"", "", ⟨"", sp⟩, .unit sp, [], sp⟩

/-- The handler that relabels a provided effect's port (SPEC §22, R2c): each clause performs its
operation again at the site around the `with`, and the return clause answers the body's value. -/
def relabelHandler (sp : Span) (eff : EffSig) : CHandler :=
  let targs : List VTy := eff.tps.map (.name sp ·)
  { name := ⟨s!"fx_relabel_{eff.name}", sp⟩, tps := (eff.tps ++ ["FX_RA"]).map (⟨·, sp⟩),
    params := [], eff := ⟨eff.name, sp⟩, effArgs := targs, row := [(⟨eff.name, sp⟩, targs)],
    res := .name sp "FX_RA", ret := (⟨"fx_rx", sp⟩, .name sp "FX_RA", .ret sp (.var sp "fx_rx")),
    clauses := eff.ops.map fun o =>
      let xs : List Ident := o.params.zipIdx.map fun (_, i) => ⟨s!"fx_ro{i}", sp⟩
      ⟨o.name, xs, .ret sp (.app sp (.var sp o.name.name) (tupleOf sp (xs.map fun x => .var sp x.name)))⟩ }

/-- A callback's specification for the copy made for it (SPEC §22): its computation parameter,
what it performs that the callee does not provide (its tunneled row), and whether it assigns a
variable it captures. -/
structure CbSpec where
  cp : CParam
  T : List Inst
  assigns : Bool
  /-- The port of each provided effect the callback performs at one: the callee's, for a closure
  written at the call; a computation parameter passed on keeps its own (`cbCall`). -/
  ports : List (String × Nat)

/-- A callback's capabilities in its code's order: by effect, so that a callback passed on has the
type the callee's parameter expects whatever the order of either function's row. -/
def codeOrder (cs : List Cap) : List Cap := cs.mergeSort fun a b => decide (a.eff ≤ b.eff)

/-- A callback's row in its code's order: by static name. -/
def siteOrder (ss : List Site) : List Site := ss.mergeSort fun a b => decide (a.n ≤ b.n)

mutual
/-- A closure in `V` refers to one of `xs` (a callback that calls back into a recursive group). -/
def closureRefsV (xs : List String) : Nat → Val → Bool
  | 0, _ => false
  | n + 1, V => match V with
    | .thunkv _ M | .bangThunkv _ M | .thunk _ M | .bangThunk _ M =>
      (refsC fuel M).any xs.contains || closureRefsC xs n M
    | .pair _ V W | .app _ V W => closureRefsV xs n V || closureRefsV xs n W
    | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
    | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V => closureRefsV xs n V
    | .run _ M => closureRefsC xs n M
    | _ => false

/-- A closure in `M` refers to one of `xs`. -/
def closureRefsC (xs : List String) : Nat → Comp → Bool
  | 0, _ => false
  | n + 1, M => match M with
    | .ret _ V | .absurd _ V | .perform _ _ _ V | .abort _ _ _ V => closureRefsV xs n V
    | .bind _ _ _ M N _ | .with_ _ M N => closureRefsC xs n M || closureRefsC xs n N
    | .letUnit _ V M | .letPair _ _ _ V M => closureRefsV xs n V || closureRefsC xs n M
    | .case _ V _ M _ N | .for_ _ _ V M N =>
      closureRefsV xs n V || closureRefsC xs n M || closureRefsC xs n N
    | .lam _ _ _ M | .app _ M _ | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M
    | .nuOut _ M | .ascribe _ M _ | .handle _ _ _ _ M => closureRefsC xs n M
    | .unwind _ _ _ M D N => closureRefsC xs n M || closureRefsC xs n D || closureRefsC xs n N
    | _ => false
end

/-- The capabilities a copy takes for the row `Rc`, in its order: an answering handler's state, the
variable a `for`'s site threads, and an enclosing callback's environment (`envMut`, each a type
parameter of the copy, `FX_Ek`); and those type parameters. -/
def rowCaps (env : Env) (dsp : Span) (Rc : List Inst) (hs : List HSig) (ss : List Site)
    (envMut : List (String × Bool)) : List Cap × List Ident := Id.run do
  let mut extra : List Ident := []
  let mut caps : List Cap := []
  for i in Rc do
    if let some m := envMut.lookup i.eff then
      let W := s!"FX_E{caps.length}"
      extra := extra ++ [⟨W, dsp⟩]
      caps := caps ++ [⟨i.eff, "fx_c_" ++ sanitize i.eff, "", noHandler dsp, some W, some m⟩]
    else if env.answering i.eff then
      if let some h := hs.find? (·.eff == i.eff) then
        caps := caps ++ [⟨i.eff, "fx_c_" ++ i.eff.toLower, "fx_l_" ++ i.eff.toLower, h, none, none⟩]
    else if let some s := ss.find? (·.eff == i.eff) then
      if let some (w, W) := s.thr then caps := caps ++ [threadCap dsp i.eff w W]
  return (caps, extra)

/-- The computation parameters of a function's copy made for callbacks (SPEC §22), the callbacks
`specs`: each one's environment capability (`fx_ek`, of the type parameter `FX_Wk`), the parameter
types `Ps` with each such parameter at its code's type, the parameters as the copy's body sees
them, and their rows as functions of the copy. `x` is the function (its ports), `name` the copy. -/
def cbSetup (env : Env) (dsp : Span) (x name : String) (σ : TySubst) (caps : List Cap)
    (ss : List Site) (specs : List CbSpec) (pnames : List Ident) (Ps : List VTy) :
    EM (List Cap × List VTy × List CbParam × List FSig) := do
  let mut cbps : List CbParam := []
  let mut envCaps : List Cap := []
  let mut Ps := Ps
  let mut cbF : List FSig := []
  for c in specs do
    let eEff := envEffName name c.cp.idx
    let ec : Cap := ⟨eEff, s!"fx_e{c.cp.idx}", "", noHandler dsp, some s!"FX_W{c.cp.idx}", some c.assigns⟩
    envCaps := envCaps ++ [ec]
    let ports : List Site := c.cp.prov.filterMap fun (e, Pe) => (c.ports.lookup e.name).map fun pn =>
      ⟨e.name, pn, Pe.map (·.subst σ), none, dsp, s!"`{x}`"⟩
    let tun := c.T.filterMap fun i => if env.answering i.eff then none else ss.find? (·.eff == i.eff)
    let codeCaps := codeOrder (caps.filter fun cc => c.T.any (·.eff == cc.eff)) ++ [ec]
    let codeCaps' := codeCaps.map fun cc =>
      if cc.thr.isSome then cc else { cc with life := "fx_k_" ++ cc.eff.toLower }
    let lives := (codeCaps'.filter (·.thr.isNone)).map fun cc => ((⟨cc.life, dsp⟩ : Ident), Life.top dsp)
    let codeF : FnParts := ⟨true, lives, capsTy dsp codeCaps' (c.cp.A.subst σ),
      capsTy dsp codeCaps' (c.cp.B.subst σ), ⟨"_", dsp⟩, .top dsp⟩
    let (codeT, _) := codeF.build dsp (env.rowOf (siteOrder (ports ++ tun)))
    Ps := Ps.set c.cp.idx codeT
    let pname := (pnames.getD c.cp.idx ⟨"?", dsp⟩).name
    let rowCb : List Inst := ports.map (fun s => ⟨s.eff, some s.args⟩) ++ c.T ++ [⟨eEff, some []⟩]
    cbps := cbps ++ [⟨pname, ports.map fun s => (s.eff, s.n), rowCb, codeCaps⟩]
    cbF := cbF ++ [{ name := pname, row := rowCb, decl := .main dsp (.top dsp) (.top dsp) }]
  pure (envCaps, Ps, cbps, cbF)

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
      -- A call that passes a callback, or of a computation parameter, is elaborated as a value.
      let self := self || cx.cbCallV V
      match headName f, wrap && !self with
      | some x, true =>
        match cx.env.fn? x with
        | some g =>
          let used := cx.need (cx.rowOf g)
          if !W.lends && used.map (·.var) == cs.map (·.var) then
            let (bs, W') ← trV n cx cs W
            let name ← copyFor n cx sp x g
            let f' : Val := match f with
              | .defApp fsp _ As => .defApp fsp name As
              | _ => .var f.span name
            report sp "call" (s!"{x} → `{name}`, in tail position: its answer is this one's")
            return ← chain bs (.ret sp (.app sp f' (capsTuple sp used W')))
          else trRet n cx cs wrap sp V
        | none => trRet n cx cs wrap sp V
      | _, _ => trRet n cx cs wrap sp V
    | .ret sp V => trRet n cx cs wrap sp V
    | .bind sp x A M N lin => trBind n cx cs wrap sp x A M N lin
    | .letUnit sp V M =>
      let (bs, V') ← trV n cx cs V
      chain bs (.letUnit sp V' (← trC n cx cs wrap M))
    | .letPair sp x y V M =>
      let (bs, V') ← trV n cx cs V
      chain bs (.letPair sp x y V' (← trC n cx cs wrap M))
    | .case sp V x M y N =>
      let (bs, V') ← trV n cx cs V
      chain bs (.case sp V' x (← trC n cx cs wrap M) y (← trC n cx cs wrap N))
    | .for_ sp x V M N =>
      match cx.env.iterCall? V with
      | some (g, gs, i, f, W) =>
        if (cx.ctl (rowC cx.env fuel M)).isEmpty && !mayLoop fuel M then
          forSite n cx cs wrap sp x g gs i f W M N
        else
          -- A body that performs a control operation would hold the continuation across it,
          -- which has no destructor (its cancel performs at the site's row), and one that loops
          -- cannot be a clause, which is total: the `for` drains the stored generator instead.
          let (bs, V') ← pullSite n cx cs sp g gs i f W
          report sp "lowering" (s!"for over {g}: its body performs a control operation or " ++
            "loops, so it drains the stored generator")
          chain bs (.for_ sp x V' (← trC n cx [] false M) (← trC n cx cs wrap N))
      | none =>
        let (bs, V') ← trV n cx cs V
        -- The body rebinds the capabilities it uses by name, and the loop threads them.
        chain bs (.for_ sp x V' (← trC n cx [] false M) (← trC n cx cs wrap N))
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
        (.ret T.span (capsTuple T.span cs (.var T.span rv))) false)

/-- `x <- M; N` of `trC`. -/
def trBind : Nat → Cx → List Cap → Bool → Span → Ident → Option VTy → Comp → Comp → Bool → EM Comp
  | 0, _, _, _, sp, _, _, _, _, _ => throw ⟨sp, "internal error: a body nested too deeply"⟩
  | n + 1, cx, cs, wrap, sp, x, A, M, N, lin => do
    -- `x : pull A B R <- return g(W)`: the stored generator of the call.
    if let (some A', .ret rsp V) := (A, M) then
      if let (true, some (g, gs, i, f, W)) := (isPullTy A', cx.env.iterCall? V) then
        let (bs, V') ← pullSite n cx cs rsp g gs i f W
        return ← chain bs (.bind sp x A (.ret rsp V') (← trC n cx cs wrap N) lin)
    -- A callback's environment rebuilt at a terminal of its code (`cbCode`): its variables, the
    -- code of a computation parameter among them, as values.
    if x.name.startsWith "fx_cenv" then
      return .bind sp x A M (← trC n cx cs wrap N) lin
    let csM := cx.needC M
    let N' ← trC n cx cs wrap N
    if csM.isEmpty then
      if let .ret rsp V := M then
        -- A value: its effectful calls bound before the binding, which keeps its form.
        let (bs, V') ← trV n cx [] V
        chain bs (.bind sp x A (.ret rsp V') N' lin)
      else pure (.bind sp x A (← trC n cx [] false M) N' lin)
    else if let .ret rsp V := M then
      let (bs, V') ← trV n cx cs V
      chain bs (.bind sp x A (.ret rsp V') N' lin)
    else
      -- `M` hands back the capabilities it uses, which are bound again for `N`.
      let t ← fresh "fx_b"
      let M' ← trC n cx csM true M
      let v ← fresh "fx_v"
      let N'' := if lin then .bind sp x none (.ret sp (.var sp v)) N' lin else N'
      let body ← if lin then unpack sp csM v t N'' else unpack sp csM x.name t N'
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
    let T := if isExit V' || !wrap then Comp.ret sp V' else .ret sp (capsTuple sp cs V')
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
    -- A layer's `call` is the member's call, which threads the environment; so does a call that
    -- passes a callback, or calls a computation parameter (SPEC §22).
    let lcall := cx.lcallV V || cbIn cx fuel V
    if !needs && !unhandled && !ret && !lcall && !withInV cx.env fuel V then return ([], V)
    let (V, pre) ← if needs || lcall then (liftPlain cx fuel V).run [] else pure (V, [])
    let (bs, V') ← goV n cx cs V
    pure (pre ++ bs, V')

/-- `trV` below the lifting of plain calls. -/
def goV : Nat → Cx → List Cap → Val → EM (List Bind × Val)
  | 0, _, _, V => throw ⟨V.span, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, V => match V with
    | .app sp (.app sp₂ (.sugar ksp (.handle h l As)) P) (.thunkv tsp (.lam lsp b A M)) =>
      match cx.env.handler? h, cx.env.chandler? h with
      | some hs, _ => withBlk k cx cs sp sp₂ ksp hs l P tsp lsp b A M
      | none, some ch => withCtl k cx cs sp ksp ch As P M none
      | none, none =>
        if cx.env.driver? h then do
          -- `with d { M }` of a heap driver: `M`, its recursive groups driven by `d`.
          report ksp "lowering" s!"with {h}: the recursive groups called in its body are driven by `{h}`"
          let M' ← trC k { cx with driver := some h } [] false M
          let r ← fresh "fx_v"
          let bind : Bind := fun N => pure (bindFlat sp r none M' N)
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
          let bind : Bind := fun N => do pure (bindFlat sp t none M' (← unpack sp csM r t N))
          pure ([bind], .var sp r)
        else throw ⟨ksp, s!"no handler `{h}` is declared before this `with`"⟩
    | .app sp (.app sp₂ (.sugar ksp k'@(.borrow ..)) P) (.thunkv tsp (.lam lsp b A M)) => do
      let (bsP, P') ← goV k cx cs P
      let csM := cx.needC M
      let ctl := cx.ctlC M
      if csM.isEmpty && !ctl then
        let M' ← trC k cx [] false M
        return (bsP, .app sp (.app sp₂ (.sugar ksp k') P') (.thunkv tsp (.lam lsp b A M')))
      let M' ← trC k cx csM true M
      let blk := Val.app sp (.app sp₂ (.sugar ksp k') P') (.thunkv tsp (.lam lsp b A M'))
      blockResult k cx sp blk csM
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
        -- A computation parameter called, and a call that passes a callback (SPEC §22).
        if let some cb := cx.cb? x then
          return ← cbParamCall k cx cs sp cb W
        if cx.env.isCbCall (cx.cbs.map (·.name)) x W then
          return ← cbCall k cx cs sp f x W
        -- An argument at a stored generator's parameter: the stored generator of the call.
        let (bP, W) ← pullArgsV k cx cs x W
        let (b, V') ← match cx.env.op? x, cx.env.fn? x with
          | some o, _ => if cx.env.answering o.eff then opCall k cx cs sp x o W else ctlCall k cx cs sp x o W
          | none, some g => fnCall k cx cs sp f x g W
          | none, none => plainApp k cx cs sp f W
        pure (bP ++ b, V')
      | none => plainApp k cx cs sp f W
    | .var sp x => do
      if let some rk := cx.resume then
        if rk.k == x && rk.stateful then
          throw ⟨sp, s!"the continuation `{x}` of a handler with a state is passed as a value: it " ++
            "can only be resumed, `{x}(v)`, or dropped"⟩
      if let some lc := cx.layerCall then
        if lc.name == x then
          throw ⟨sp, s!"`{x}`, the call a layer runs around, is passed as a value: it can only be called"⟩
      if (cx.cb? x).isSome then
        throw ⟨sp, s!"the callback `{x}` is used as a value: a computation parameter is second class, " ++
          "and can only be called or passed at a computation parameter (SPEC §22)"⟩
      match cx.env.fn? x with
      | some g =>
        if g.group.isSome then
          throw ⟨sp, s!"`{x}` is recursive and is passed as a value: it can only be called, or " ++
            "passed at a function's computation parameter (SPEC §22)"⟩
        throw ⟨sp, s!"`{x}` performs `{", ".intercalate (g.row.map (·.eff))}` and is passed as a " ++
          "value: it can only be called, or passed at a function's computation parameter (SPEC §22)"⟩
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
    | .run sp M => do
      let csM := cx.needC M
      if csM.isEmpty && !cx.ctlC M then return ([], .run sp (← trC k cx [] false M))
      let M' ← trC k cx csM true M
      let t ← fresh "fx_b"
      let r ← fresh "fx_v"
      let bind : Bind := fun N => do pure (bindFlat sp t none M' (← unpack sp csM r t N))
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
      let bind : Bind := fun N =>
        pure (.bind sp ⟨t, sp⟩ none (.ret sp blk) (.letPair sp ⟨pl, sp⟩ ⟨q, sp⟩ (.var sp t) N) false)
      return ([bind], .pair sp (.var sp pl) (.var sp q))
    let bind : Bind := fun N => do
      let rest ← unpack sp csM r q N
      pure (.bind sp ⟨t, sp⟩ none (.ret sp blk) (.letPair sp ⟨pl, sp⟩ ⟨q, sp⟩ (.var sp t) rest) false)
    pure ([bind], .pair sp (.var sp pl) (.var sp r))

/-- The call of member `j` through the function `g` of a self-reference, on `W` with the
environment: `f <- return unbang g; z <- return (); a <- return (E, W); (force f z).j a`. -/
def memberCall (sp : Span) (rs : RSelf) (j : Nat) (g f z a : String) (W : Val)
    (lives : List String := []) : Comp :=
  let field := projAt sp j rs.members.length (.app sp (.force sp ⟨f, sp⟩) ⟨z, sp⟩)
  .bind sp ⟨f, sp⟩ none (.ret sp (.unbang sp (.var sp g)))
    (.bind sp ⟨z, sp⟩ none (.ret sp (.unit sp))
      (.bind sp ⟨a, sp⟩ none (.ret sp (capsTuple sp rs.env W))
        (.app sp (lives.foldl (fun M l => .inst sp M (.var sp l)) field) ⟨a, sp⟩)
        false) false) false

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
    for (e, n) in rs.served do
      if let some s := cx.siteOf e then
        if s.n != n then throw (through e)
    for c in rs.env do
      if let some c' := cx.capOf c.eff then
        if c'.h.name != c.h.name || c'.var != c.var then throw (through c.eff)
    noLend sp s!"`{x}`" W
    -- The callbacks of the member the group's copy was made for are passed on as they are: a
    -- recursion that passes another callback there would need a copy per level (SPEC §22).
    let (b, W') ← match rs.cbArgs.lookup j, cx.env.arity.lookup x with
      | some pos, some na => do
        let some comps := splitVal na W
          | throw ⟨sp, s!"`{x}` takes {na} arguments: write them one by one"⟩
        let mut bs : List Bind := []
        let mut vs : List Val := []
        for (V, i) in comps.zipIdx do
          match pos.lookup i, V with
          | some pn, .var _ y =>
            unless y == pn do
              throw ⟨V.span, s!"`{x}` calls itself with a callback other than its own `{pn}`: a " ++
                "recursion holds the callbacks it was entered with, in its generator, and a new one at " ++
                "each level is not provided (SPEC §22)"⟩
            -- The generator holds the code: the call passes `()` in its place.
            vs := vs ++ [.unit V.span]
          | some pn, _ =>
            throw ⟨V.span, s!"`{x}` calls itself with a callback other than its own `{pn}`: a " ++
              "recursion holds the callbacks it was entered with, in its generator, and a new one at " ++
              "each level is not provided (SPEC §22)"⟩
          | none, _ =>
            let (b, V') ← goV k cx cs V
            bs := bs ++ b
            vs := vs ++ [V']
        pure (bs, tupleOf sp vs)
      | _, _ => goV k cx cs W
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
    -- Fields generic in the capabilities' lifetimes are called at those the capabilities have here.
    let cur := rs.env.map fun c => (cx.capOf c.eff).getD c
    let lives := if rs.poly.isEmpty then [] else (cur.filter (·.thr.isNone)).map (·.life)
    let res : CTy := if rs.poly.isEmpty then res else
      .eff sp rs.rowR (capsTy sp cur ((rs.Ts[j]?).getD (.unit sp)))
    let call : Comp := .case sp (.var sp rs.self) ⟨u, sp⟩
      (.ascribe sp (.abort sp rs.e 0 (.unit sp)) res) ⟨g, sp⟩
      (memberCall sp rs j g f z a W' lives)
    let bind : Bind := fun N => do
      pure (.bind sp ⟨t, sp⟩ none call (← unpack sp rs.env r t N) false)
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
      let bind : Bind := fun N => pure (.bind sp ⟨a, sp⟩ none (.ret sp W') (.bind sp ⟨r, sp⟩ none res N false) false)
      return (b ++ [bind], .var sp r)
    let g ← fresh "fx_kg"
    let sv ← fresh "fx_ks"
    let t ← fresh "fx_kt"
    let st : Val := capsTuple sp cx.caps (paramsTuple sp rk.params)
    let bind : Bind := fun N => do
      let after ← unpack sp cx.caps r t N
      pure (.bind sp ⟨a, sp⟩ none (.ret sp W') (.bind sp ⟨g, sp⟩ none res
        (.bind sp ⟨sv, sp⟩ none (.ret sp st) (.bind sp ⟨t, sp⟩ none (.app sp (.force sp ⟨g, sp⟩) ⟨sv, sp⟩)
          after false) false) false) false)
    pure (b ++ [bind], .var sp r)

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
    let bind : Bind := fun N => do
      pure (.bind sp ⟨t, sp⟩ none (memberCall sp lc.rs lc.j lc.g f z a W') (← unpack sp lc.rs.env r t N) false)
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
def opCall : Nat → Cx → List Cap → Span → String → OpSig → Val → EM (List Bind × Val)
  | 0, _, _, sp, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, x, o, W => do
    let some c := cx.capOf o.eff
      | throw ⟨sp, s!"the operation `{x}` of `{o.eff}` is performed here, but no handler of " ++
          s!"`{o.eff}` is in scope"⟩
    noLend sp s!"the operation `{x}`" W
    let (b, W') ← goV k cx cs W
    let t ← fresh "fx_b"
    let r ← fresh "fx_v"
    let call := Val.app sp (.var sp (clauseName c.h.name x)) (.pair sp (.var sp c.var) W')
    report sp "call" s!"{x} ({o.eff}) → `{clauseName c.h.name x}`, on the state of `{c.h.name}`"
    let bind : Bind := fun N => do
      pure (.bind sp ⟨t, sp⟩ (some (capsTy sp [c] o.decl.res)) (.ret sp call)
        (← unpack sp [c] r t N) false)
    pure (b ++ [bind], .var sp r)

/-- `op(W)` of a control effect: the kernel's operation, at the static name of the innermost site
of its effect, bound before the value it is in. -/
def ctlCall : Nat → Cx → List Cap → Span → String → OpSig → Val → EM (List Bind × Val)
  | 0, _, _, sp, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, x, o, W => do
    let s ← (cx.serve sp s!"the operation `{x}`" (cx.env.opInst o) : Except Error Site)
    let (b, W') ← goV k cx cs W
    let r ← fresh "fx_v"
    let abortive := o.decl.abortive
    report sp "call" (s!"{x} ({o.eff}) → {if abortive then "abort" else "perform"}[{s.n}.{o.idx}], " ++
      s!"handled by {s.what} at {s.sp.start.render}" ++
      (if abortive then ": abortive, it never resumes" else ""))
    let bind : Bind := if abortive then
        -- What follows an abort does not run.
        fun _ => pure (.abort sp s.n o.idx W')
      else match s.thrVar with
        -- A `for`'s site threads its variable through the operation, which answers it again.
        | some w => threadedPerform sp s.n o.idx W' w
        | none => fun N => pure (.bind sp ⟨r, sp⟩ none (.perform sp s.n o.idx W') N false)
    let v : Val := if abortive || s.thr.isSome then .unit sp else .var sp r
    pure (b ++ [bind], v)

/-- `f(W)` of a function with a row: a call of its copy for what serves its effects in scope,
which takes the capabilities first and hands them back first, bound before the value it is in. -/
def fnCall : Nat → Cx → List Cap → Span → Val → String → FSig → Val → EM (List Bind × Val)
  | 0, _, _, sp, _, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, f, x, g, W => do
    let used := cx.needIn (cx.rowOf g)
    if used.isEmpty && (cx.ctl (cx.rowOf g)).isEmpty then return ← plainApp k cx cs sp f W
    noLend sp s!"`{x}`" W
    let (b, W') ← goV k cx cs W
    let name ← copyFor k cx sp x g
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
        (.ret sp (.var sp c.var)) K false) N
    let bind : Bind := fun N => do
      pure (.bind sp ⟨t, sp⟩ ann (.ret sp (.app sp f' (capsTuple sp used W')))
        (← unpack sp used r t (N' N)) false)
    pure (b ++ [bind], .var sp r)

/-- `with h(P) { 'l, c -> M }` of an answering handler: a borrow block of the state's cell whose
callback's parameter `c` is the capability. -/
def withBlk : Nat → Cx → List Cap → Span → Span → Span → HSig → String → Val → Span → Span →
    Ident → VTy → Comp → EM (List Bind × Val)
  | 0, _, _, sp, _, _, _, _, _, _, _, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, sp₂, ksp, hs, l, P, tsp, lsp, b, A, M => do
    let (bsP, P') ← goV k cx cs P
    let place ← match P' with
      | .lend _ x .mut => pure (Val.var x.span x.name)
      | .lend lsp' _ .imm => throw ⟨lsp', "a handler's state is lent `&mut`"⟩
      | V => pure (.app V.span (.sugar V.span (.call "alloc")) V)
    let cap : Cap := ⟨hs.eff, b.name, l, hs, none, none⟩
    let cx' : Cx := { cx with caps := cap :: cx.caps.filter (·.eff != hs.eff) }
    let csM := cx'.needC M
    let outer := csM.filter (·.eff != hs.eff)
    let where_ := match P' with
      | .lend _ x _ => s!"lent from `{x.name}`"
      | _ => "in a cell scoped to the block"
    report ksp "lowering" (s!"with {hs.name} ({hs.eff}): a borrow block of its state ({where_}); its " ++
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
def withCtl : Nat → Cx → List Cap → Span → Span → CHandler → List VTy → Val → Comp → Option Nat →
    EM (List Bind × Val)
  | 0, _, _, sp, _, _, _, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, ksp, ch, As, P, M, forced => do
    let tps := ch.tps.map (·.name)
    let e := ch.eff.name
    if M.boundNames.contains "io_bt" then
      throw ⟨ksp, s!"the body of `with {ch.name.name}` assigns a `let mut` variable declared " ++
        "outside it, or lends a place declared outside it: a control handler's body may be " ++
        "abandoned, and does not hand them back; bind what the block answers instead"⟩
    let some eff := cx.env.eff? e | throw ⟨ksp, s!"internal error: the effect `{e}`"⟩
    -- The capabilities the body uses are reborrowed for it, each at a lifetime of its own, so that
    -- they come back when the body is abandoned.
    let mut csM : List Cap := []
    for c in cx.needC M do
      -- A callback's environment is passed in, and comes back with each call; it is not lent. It
      -- holds what the callback captures, which the callback does not bind again (`cbCall`).
      if c.env.isSome then continue
      if c.thr.isSome then
        throw ⟨ksp, s!"the body of `with {ch.name.name}` performs `{c.eff}` of an enclosing `for`, " ++
          "which threads its variables through the operation: a control handler's body may be " ++
          "abandoned, and does not hand them back; not provided"⟩
      csM := csM ++ [{ c with life := ← fresh "fx_rl" }]
    -- Written type arguments, in the order of the handler's type parameters.
    if As.length > tps.length then
      throw ⟨ksp, s!"`{ch.name.name}` takes {tps.length} type argument(s)"⟩
    let mut σ : TySubst := tps.zip As
    -- The handled effect's type arguments from what the body performs. A site whose body calls a
    -- computation parameter that is provided `e` is named by its port (SPEC §22).
    let called : List Nat := (cx.cbs.filter fun (cb : CbParam) => (refsC fuel M).contains cb.name).filterMap fun (cb : CbParam) => cb.ports.lookup e
    let n ← match forced, called.eraseDups with
      | some p, _ => pure p
      | none, [p] => pure p
      | none, [] => freshSite
      | none, _ =>
        throw ⟨ksp, s!"the body of `with {ch.name.name}` calls callbacks provided `{e}` at two ports: one " ++
          "handler cannot serve both (two ports under one site; `rename` would, not built)"⟩
    if let some i := (rowC cx.env fuel M).find? (·.eff == e) then
      if let some Bs := i.args then
        unless Bs.length == ch.effArgs.length do
          throw ⟨ksp, s!"internal error: `{e}`'s type arguments"⟩
        for (Pt, B) in ch.effArgs.zip Bs do
          match matchTy tps σ Pt B with
          | some σ' => σ := σ'
          | none => throw ⟨ksp, s!"`with {ch.name.name}` handles `{e}[{", ".intercalate
              (ch.effArgs.map (VTy.pp · 0))}]`, but its body performs `{e}[{", ".intercalate
              (Bs.map (VTy.pp · 0))}]`"⟩
    -- The handler's own row, at the sites around the `with`.
    let mut outer : List Site := []
    for (e₂, Ps) in ch.row do
      let some s := cx.siteOf e₂.name
        | throw ⟨ksp, s!"`{ch.name.name}` performs `{e₂.name}`, and no handler of `{e₂.name}` is " ++
            "in scope at this `with`"⟩
      for (Pt, B) in Ps.zip s.args do
        match matchTy tps σ Pt B with
        | some σ' => σ := σ'
        | none => throw ⟨ksp, s!"`{ch.name.name}` performs `{e₂.name}` at a type other than the " ++
            s!"handler of `{e₂.name}` in scope here"⟩
      outer := outer ++ [s]
    let effArgs := ch.effArgs.map (·.subst σ)
    if effArgs.any (mentions tps) then
      throw ⟨ksp, s!"the type arguments of `{e}` at this `with` are not determined: write them, " ++
        s!"`with {ch.name.name}[{", ".intercalate tps}](…)`"⟩
    let site : Site := { eff := e, n, args := effArgs, sp := ksp, what := s!"`with {ch.name.name}`" }
    let ents := cx.env.siteOps site
    report ksp "lowering" (s!"with {ch.name.name} ({e}): a handler, the static name {n}; " ++
      ", ".intercalate (((cx.env.eff? e).map (·.ops)).getD [] |>.map fun o =>
        s!"{o.name.name} {if o.abortive then "abortive: a branch per call (final ctl)"
          else match o.qual with
            | .lin => "linear: resumed exactly once"
            | .aff => "affine: resumed or cancelled"
            | .unr => "unrestricted: its continuation copied"}"))
    -- The body, with this site innermost for `e`.
    let cxB : Cx := { cx with sites := site :: cx.sites.filter (·.eff != e),
                              caps := cx.caps.map fun c => (csM.find? (·.var == c.var)).getD c }
    let M' ← trC k cxB [] false M
    let (rx, rA, rM) := ch.ret
    for c in ch.clauses do
      unless eff.ops.any (·.name.name == c.name.name) do
        throw ⟨c.name.span, s!"`{c.name.name}` is not an operation of `{e}`"⟩
    let rest := tps.filter fun x => (σ.lookup x).isNone
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
        ch.params.map (fun (x, A) => (x.name, A.subst σ)), rA.subst σ, .sum sp (rA.subst σ) pay,
        some (ch.res.subst σ)⟩
      let clsV := injCls.foldr (fun c t => Val.pair sp c t) (.unit sp)
      let (bsP, P') ← goV k cx cs P
      let hnd : Val := .app sp (.app sp (.app sp (.app sp (.sugar ksp (.hndCtl info)) P')
        (.thunkv sp (.lam sp ⟨xr, sp⟩ rA (.ret sp (.inl sp (.var sp xr)))))) clsV) (.thunk sp M')
      let (bsH, hv) ← reborrowed k sp ksp hnd csM
      let rn ← fresh "fx_ar"
      let pv ← fresh "fx_hp"
      let rv : Val := .var sp rn
      let params : Bind := fun N => do
        pure (.bind sp ⟨pv, sp⟩ none (.ret sp hv)
          (← bindParams sp pv (ch.params.map (·.1) ++ [⟨rn, sp⟩]) N) false)
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
        arms := arms ++ [(q, ← bindParams c.name.span q c.params (c.body.subst σ))]
      let rec dispatch : Nat → String → List (String × Comp) → Comp
        | _, v, [(q, N)] => .bind sp ⟨q, sp⟩ none (.ret sp (.var sp v)) N false
        | m + 1, v, (q, N) :: rest =>
          let y := v ++ "r"
          .case sp (.var sp v) ⟨q, sp⟩ N ⟨y, sp⟩ (dispatch m y rest)
        | _, v, _ => .absurd sp (.var sp v)
      let after : Comp := .case sp rv rx (rM.subst σ) ⟨ev, sp⟩ (dispatch (nOps + 1) ev arms)
      -- Its operations are the handler's row's, at the sites around the `with`.
      let cxA : Cx := { cx with sites := outer ++ cx.sites.filter fun s => !outer.any (·.eff == s.eff) }
      let csA := cxA.needC after
      let after' ← trC k cxA csA true after
      let t ← fresh "fx_b"
      let r ← fresh "fx_v"
      report ksp "lowering" (s!"with {ch.name.name}: every operation abortive, so its clauses run " ++
        "after the handler, in the scope of the `with`")
      -- Its type is the handler's answer, which the typed elaboration names `fx_res{n}`.
      let resT : VTy := capsTy sp csA (.name sp s!"fx_res{n}")
      let bind : Bind := fun N => do pure (bindFlat sp t (some resT) after' (← unpack sp csA r t N))
      return (bsP ++ bsH ++ [params, bind], .var sp r)
    -- The capabilities the clauses use: the handler holds them between operations, in its state.
    let csCl := cx.need (ch.clauses.foldl (fun r c => union r (rowC cx.env fuel c.body))
      (rowC cx.env fuel rM))
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
    if stateful then
      let pNames := ch.params.map (·.1.name)
      let Pt : VTy := tupleTy sp (ch.params.map fun (_, A) => A.subst σ)
      let Rv := ch.res.subst σ
      let St : VTy := capsTy sp csCl Pt
      let rowO := cx.env.rowOf outer
      let Ans : VTy := capsTy sp csCl Rv
      let ansT : VTy := .thunk sp (.arr sp St (match rowO with
        | .nil => .ret sp Ans
        | r => .eff sp r Ans))
      let cxS (rk : Option ResumeK) : Cx := { env := cx.env, caps := csCl, sites := outer, resume := rk }
      let stThunk (body : Comp) : EM Val := do
        let sv ← fresh "fx_hs"
        let ps ← fresh "fx_hq"
        let inner ← unpack sp csCl ps sv (← bindParams sp ps (ch.params.map (·.1)) body)
        pure (.thunkv sp (.lam sp ⟨sv, sp⟩ St inner))
      let rM' ← trC k (cxS none) csCl true (rM.subst σ)
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
        let body ← trC k (cxS rk) csCl true (c.body.subst σ)
        let th : Comp := .ret csp (← stThunk body)
        let body ← if abortive then bindParams csp p c.params th else do
          let q ← fresh "fx_q"
          pure (.letPair csp ⟨q, csp⟩ kv (.var csp p) (← bindParams csp q c.params.dropLast th))
        cls := cls ++ [.thunkv csp (.lam csp ⟨p, csp⟩ (holeTy csp) body)]
      let info : HInfo := ⟨ch.name.name, n, ents, rest, σ, [], rA.subst σ, ansT, none⟩
      let (bsP, P') ← goV k cx cs P
      let pv ← fresh "fx_hp"
      let args : Bind := fun N => pure (.bind sp ⟨pv, sp⟩ none (.ret sp P') N false)
      let clsV := cls.foldr (fun c t => Val.pair sp c t) (.unit sp)
      let hnd : Val := .app sp (.app sp (.app sp (.app sp (.sugar ksp (.hndCtl info)) (.unit sp))
        hr) clsV) (.thunk sp M')
      let (bsH, gv) ← reborrowed k sp ksp hnd csM
      -- The site's answer applied to the initial state; the capabilities bound again after.
      let g ← fresh "fx_hg"; let sv ← fresh "fx_hs"; let t ← fresh "fx_ht"
      let r ← fresh "fx_v"
      let run : Bind := fun N => do
        let after ← unpack sp csCl r t N
        pure (.bind sp ⟨g, sp⟩ none (.ret sp gv)
          (.bind sp ⟨sv, sp⟩ none (.ret sp (capsTuple sp csCl (.var sp pv)))
            (.bind sp ⟨t, sp⟩ none (.app sp (.force sp ⟨g, sp⟩) ⟨sv, sp⟩) after false) false) false)
      report ksp "lowering" (s!"with {ch.name.name}: a handler with a state, its parameters" ++
        (if csCl.isEmpty then "" else " and the capabilities its clauses use") ++
        ", passed to each clause and to the continuation at each resume")
      return (bsP ++ [args] ++ bsH ++ [run], .var sp r)
    -- The clauses run outside the handler: their operations go to the sites of the handler's row.
    let cxH : Cx := { env := cx.env, caps := [], sites := outer }
    let rM' ← trC k cxH [] false (rM.subst σ)
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
      let body ← trC k { cxH with resume := rk } [] false (c.body.subst σ)
      let csp := c.name.span
      let p ← fresh "fx_p"
      let body ← if abortive then bindParams csp p c.params body else do
        let xs := c.params.dropLast
        let kv := c.params.getLast!
        let q ← fresh "fx_q"
        pure (.letPair csp ⟨q, csp⟩ kv (.var csp p) (← bindParams csp q xs body))
      cls := cls ++ [.thunkv csp (.lam csp ⟨p, csp⟩ (holeTy csp) body)]
    let info : HInfo := ⟨ch.name.name, n, ents, rest, σ,
      ch.params.map fun (x, A) => (x.name, A.subst σ), rA.subst σ, ch.res.subst σ, none⟩
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
      let bind : Bind := fun N => pure (.bind sp ⟨r, sp⟩ none (.ret sp hnd) N false)
      return ([bind], .var sp r)
    let mut blk : Comp := .ret sp hnd
    for c in csM.reverse do
      let l := c.life
      let t ← fresh "fx_rb"
      let inner : Comp := .bind sp ⟨t, sp⟩ none blk (.ret sp (.var sp t)) false
      blk := .ret sp (.app sp (.app sp (.sugar ksp (.borrow .mut l)) (.var sp c.var))
        (.thunkv sp (.lam sp ⟨c.var, sp⟩ (holeTy sp) inner)))
    let bind : Bind := fun N => do
      -- The capabilities bound again from the nested pairs `(c₁, (c₂, … r))`.
      let rec unwrap : List Cap → String → Comp → EM Comp
        | [], v, K => pure (.bind sp ⟨r, sp⟩ none (.ret sp (.var sp v)) K false)
        | c :: cs, v, K => do
          let w ← fresh "fx_rw"
          pure (.letPair sp ⟨c.var, sp⟩ ⟨w, sp⟩ (.var sp v) (← unwrap cs w K))
      let t ← fresh "fx_rt"
      match blk with
      | .ret _ V => pure (.bind sp ⟨t, sp⟩ none (.ret sp V) (← unwrap csM t N) false)
      | B => pure (.bind sp ⟨t, sp⟩ none B (← unwrap csM t N) false)
    pure ([bind], .var sp r)

/-- `for x in g(W) { M }; N`, `g` performing the iteration effect `i` (SPEC §15): a handler site
of its own for `i`, whose operation threads a variable `w` (the copy of `g` for the site takes it
first and hands it back first, and `op(v)` is `w <- perform[n.0] (v, w)` in it). The site is
assembled where the types are known (`VSugar.forSite`): `w` is then the tuple of the variables the
body reads or assigns, and the body is the operation's clause. The body runs outside the site:
its operations go to the sites around the `for`. -/
def forSite : Nat → Cx → List Cap → Bool → Span → Ident → String → FSig → Inst → Val → Val →
    Comp → Comp → EM Comp
  | 0, _, _, _, sp, _, _, _, _, _, _, _, _ => throw ⟨sp, "internal error: a body nested too deeply"⟩
  | k + 1, cx, cs, wrap, sp, x, gname, g, i, f, W, M, N => do
    let some As := i.args
      | throw ⟨sp, s!"`{gname}` performs `{i.eff}`, and its type arguments are not determined: " ++
          s!"write them, `with {i.eff}[…]`"⟩
    if let some c := (cx.need (without g.row i.eff)).head? then
      throw ⟨sp, s!"`{gname}` uses the capability of `{c.eff}`: a `for` over a function that " ++
        "performs an iteration effect and uses a capability is not provided"⟩
    let n ← freshSite
    let w := s!"fx_w{n}"
    let Wn := s!"fx_W{n}"
    let site : Site := { eff := i.eff, n, args := As, sp, what := "the `for`", thr := some (w, Wn) }
    let tcap := threadCap sp i.eff w Wn
    let cxF : Cx := { cx with sites := site :: cx.sites.filter (·.eff != i.eff),
                              caps := tcap :: cx.caps.filter (·.eff != i.eff) }
    let (bP, W) ← pullArgsV k cx cs gname W
    let (bs, W') ← trV k cx cs W
    let bs := bP ++ bs
    let name ← copyFor k cxF sp gname g
    let f' : Val := match f with
      | .defApp fsp _ Ts => .defApp fsp name Ts
      | _ => .var f.span name
    let T := match (cx.env.siteOps { site with thr := none }).head? with
      | some (_, A, _) => A
      | none => .unit sp
    let opName := (((cx.env.eff? i.eff).map (·.ops)).getD [] |>.head?.map (·.name.name)).getD "?"
    report sp "lowering" (s!"for over {gname} ({i.eff}): a handler, the static name {n}; " ++
      s!"{opName} affine: the body is its clause, the variables the body uses threaded through " ++
      "the operation; `break` and `return` cancel the continuation")
    report sp "call" s!"{gname} → `{name}`, threading the `for`'s variables"
    let M' ← trC k cx [] false M
    let N' ← trC k cx cs wrap N
    let call := Val.app sp f' (capsTuple sp [tcap] W')
    chain bs (.for_ sp x (.app sp (.sugar sp (.forSite ⟨n, T, w, gname⟩)) call) M' N')

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
    let site : Site := { eff := i.eff, n, args := As, sp, what := "the stored generator" }
    let cxP : Cx := { cx with sites := site :: cx.sites.filter (·.eff != i.eff),
                              caps := cx.caps.filter (·.eff != i.eff) }
    let (bP, W) ← pullArgsV k cx cs gname W
    let (bs, W') ← goV k cx cs W
    let bs := bP ++ bs
    let name ← copyFor k cxP sp gname g
    let f' : Val := match f with
      | .defApp fsp _ Ts => .defApp fsp name Ts
      | _ => .var f.span name
    let T := match (cx.env.siteOps site).head? with
      | some (_, A, _) => A
      | none => .unit sp
    report sp "lowering" (s!"stored generator of {gname} ({i.eff}): a handler, the static name " ++
      s!"{n}; its clause keeps the continuation (affine) as the rest, resumed by the next " ++
      "observation and cancelled by `close`")
    report sp "call" s!"{gname} → `{name}`, stored"
    -- Bound before the value it is in: making the stored generator is a computation.
    let v ← fresh "fx_g"
    let pv : Val := .app sp (.sugar sp (.pullSite ⟨n, T, "", gname⟩)) (.app sp f' W')
    let bind : Bind := fun N => pure (.bind sp ⟨v, sp⟩ none (.ret sp pv) N false)
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

/-- `cb(W)`, a computation parameter called in the copy made for its callback (SPEC §22, R2a): the
callback's code applied to its capabilities, its environment and `W`, which hands the capabilities
and the environment back; bound before the value it is in. A provided effect whose innermost site
here is not its port, because the call is outside the function's handlers of it, is relabelled
first (R2c): the call runs under a site of the port whose clauses raise again at the site around
it. That needs the effect's operations abortive. -/
def cbParamCall : Nat → Cx → List Cap → Span → CbParam → Val → EM (List Bind × Val)
  | 0, _, _, sp, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, cb, W => do
    let x := cb.name
    let stray := cb.ports.filter fun (e, p) => match cx.siteOf e with
      | some s => s.n != p
      | none => true
    if let some (e, p) := stray.head? then
      let some eff := cx.env.eff? e | throw ⟨sp, s!"internal error: the effect `{e}`"⟩
      if (cx.siteOf e).isNone then
        throw ⟨sp, s!"`{x}` is provided `{e}`, and is called here outside every handler of `{e}`"⟩
      unless eff.ops.all (·.abortive) do
        throw ⟨sp, s!"`{x}` is provided `{e}`, whose operations resume, and is called here outside " ++
          s!"the handlers of `{e}` that serve it: its port would be relabelled to the handler around " ++
          "this call, which needs the callback inlined or a `rename` primitive (R2c, not built)"⟩
      report sp "lowering" (s!"{x}: called outside a handler of the {e} it is provided, under a site " ++
        s!"of its port {p} whose clauses raise again at the handler around it (R2c)")
      return ← withCtl k cx cs sp sp (relabelHandler sp eff) [] (.unit sp)
        (.ret sp (.app sp (.var sp x) W)) (some p)
    noLend sp s!"`{x}`" W
    let used := cx.need cb.row
    let (b, W') ← goV k cx cs W
    let t ← fresh "fx_b"
    let r ← fresh "fx_v"
    report sp "call" (s!"{x} → the callback's code, a closure value: called with its environment " ++
      "and capabilities, which it hands back")
    -- The capabilities bound again at their own types.
    let N' (N : Comp) : Comp := used.foldr (fun c K => if c.thr.isSome then K else
      .bind sp ⟨c.var, sp⟩ (some (c.ty sp)) (.ret sp (.var sp c.var)) K false) N
    let bind : Bind := fun N => do
      pure (.bind sp ⟨t, sp⟩ none (.ret sp (.app sp (.var sp x) (capsTuple sp used W')))
        (← unpack sp used r t (N' N)) false)
    pure (b ++ [bind], .var sp r)

/-- The code of a callback passed at a computation parameter (SPEC §22, R2a): `!` code that takes
its capabilities and its environment first and hands them back first,

    !(∀'k₁ … 'kₙ. caps ⊗ (Env ⊗ A) ⊸ F[ports ∪ tunneled] (caps ⊗ (Env ⊗ B)))

`Env` the tuple of the variables `vars` it captures, bound again inside and rebuilt at each
terminal. Its provided effects are at the callee's ports (`ports`); the rest resolve where it is
written. Its lifetimes and its parameter's type are filled where the types are known
(`VSugar.cbCode`). -/
def cbCode : Nat → Cx → Span → Ident → Comp → List Cap → Cap → List String → List Site → EM Val
  | 0, _, sp, _, _, _, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, sp, x, M, caps, envCap, vars, ports => do
    let caps := caps.map fun c => if c.thr.isSome then c else { c with life := "fx_k_" ++ c.eff.toLower }
    let lives := (caps.filter (·.thr.isNone)).map (·.life)
    let ev ← fresh "fx_cenv"
    let cs := caps ++ [{ envCap with var := ev }]
    let envT := tupleOf sp (vars.map (Val.var sp ·))
    let ct ← fresh "fx_ct"
    -- Each terminal hands the environment back as the body leaves it.
    let M₁ := wrapTerms (fun T => .bind T.span ⟨ct, T.span⟩ none T
      (.bind T.span ⟨ev, T.span⟩ none (.ret T.span envT) (.ret T.span (.var T.span ct)) false) false) M
    let sites := ports ++ cx.sites.filter fun s => !ports.any (·.eff == s.eff)
    let cxc : Cx := { cx with caps := cs, sites, fnCaps := [] }
    let body ← trC k cxc cs true M₁
    let body ← bindParams sp ev (vars.map (⟨·, sp⟩)) body
    let q ← fresh "fx_cq"
    let body ← unpack sp cs x.name q body
    pure (.app sp (.sugar sp (.cbCode ⟨lives⟩)) (.thunkv sp (.lam sp ⟨q, sp⟩ (holeTy sp) body)))

/-- `x(W)` of a function with computation parameters, passing a callback at one (SPEC §22, R2a): a
call of the copy of `x` made for what serves its row and its callbacks' tunneled rows here, and
for each callback's profile (`cbCopyOf`). Each callback is passed as a closure value: its code
(`cbCode`), and its environment, the tuple of the variables it captures, passed beside the
capabilities and handed back with them, its variables bound again after. A function passed by
name, and a computation parameter passed on, are the closure that calls them. -/
def cbCall : Nat → Cx → List Cap → Span → Val → String → Val → EM (List Bind × Val)
  | 0, _, _, sp, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, f, x, W => do
    let some d := cx.env.defs.lookup x | throw ⟨sp, s!"internal error: `{x}` is not a function"⟩
    let tps := cx.env.tpsOf x
    let cps := cx.env.cparamsOf x
    let some n := cx.env.arity.lookup x | throw ⟨sp, s!"internal error: the arity of `{x}`"⟩
    noLend sp s!"`{x}`" W
    let (bP, W₀) ← pullArgsV k cx cs x W
    let some comps := splitVal n W₀
      | throw ⟨sp, s!"`{x}` takes {n} arguments: write them one by one, `{x}(a, b, …)`"⟩
    let cbNames := cx.cbs.map (·.name)
    let σ := callSubst cx.env fuel f x W₀
    -- The callbacks: a closure as written, or a function passed by name as the closure that calls
    -- it (`fresh`); or a computation parameter of this copy passed on as it is, its code, its
    -- environment and the ports of its provided effects (`passed`).
    let mut specs : List (CbSpec × Option (Ident × Comp × List String) × Option CbParam) := []
    for cp in cps do
      let V := comps.getD cp.idx (.unit sp)
      let cl? := cbArg? cx.env cbNames V
      if cl?.isNone && cp.prov.isEmpty then continue
      if cl?.isNone && (headName V).isNone then
        throw ⟨V.span, s!"the argument at `{cp.name}` of `{x}`, which `{x}` provides " ++
          ", ".intercalate (cp.prov.map (·.1.name)) ++ ", is a closure or a function"⟩
      let prov := cp.prov.map (·.1.name)
      for e in prov do
        if cx.env.answering e then
          throw ⟨V.span, s!"`{x}` provides `{e}` at `{cp.name}`: a provided answering effect is not " ++
            "provided (SPEC §22)"⟩
      -- A computation parameter passed on.
      if let (.var _ _, some cb) := (V, cx.cb? (headName V |>.getD "")) then
        let envEff := (cb.caps.getLast?.map (·.eff)).getD ""
        let ports := cb.ports.filter fun (e, _) => prov.contains e
        let T := cb.row.filter fun i => i.eff != envEff && !ports.any (·.1 == i.eff)
        let assigns := ((cx.capOf envEff).bind (·.env)).getD false
        specs := specs ++ [(⟨cp, T, assigns, ports⟩, none, some cb)]
        continue
      let mut y : Ident := ⟨"", V.span⟩
      let mut M : Comp := .top V.span
      let mut written := false
      match cl? with
      | some (some (y', M')) => y := y'; M := M'; written := true
      | _ =>
        y := ⟨← fresh "fx_cx", V.span⟩
        M := .ret V.span (.app V.span V (.var V.span y.name))
      let T := (rowC cx.env fuel M).filter fun i => !prov.contains i.eff
      -- A closure that performs nothing, at a parameter that provides nothing, is passed as written.
      if written && prov.isEmpty && T.isEmpty then continue
      let globals := cx.env.sigs.map (·.1) ++ cx.env.ops.map (·.decl.name.name) ++ cx.env.externs
      let fv := (fvC fuel [y.name] M).eraseDups
      let vars := fv.filter fun v => !globals.contains v && !cx.caps.any (·.var == v)
      -- A callback that calls the recursive group being elaborated takes its self-reference.
      let vars := match cx.recSelf with
        | some rs => if fv.any rs.members.contains && !rs.deep then vars ++ [rs.self] else vars
        | none => vars
      -- Its environment comes back from each call, but not out of the blocks around the call: a
      -- variable it captures is not bound again in it.
      if let some v := vars.find? M.boundNames.contains then
        throw ⟨V.span, s!"this callback binds `{v}` again, a variable it captures: an assignment or a " ++
          "shadowing `let` of a captured variable in a callback is not provided; keep such state in " ++
          "a handler's capability, or rename the inner variable (SPEC §22)"⟩
      let assigns := false
      let mut ports : List (String × Nat) := []
      for e in prov do ports := ports ++ [(e, ← portOf x e)]
      specs := specs ++ [(⟨cp, T, assigns, ports⟩, some (y, M, vars), none)]
    -- A computation parameter passed on performs its provided effects that the callee does not
    -- provide at its own ports: the call runs under a site of that port whose clauses raise again
    -- at the handler around it, unless that handler is the port's (R2c).
    for (c, _, cb?) in specs do
      if let some cb := cb? then
        for (e, p) in cb.ports do
          if c.ports.any (·.1 == e) then continue
          match cx.siteOf e with
          | some s => if s.n == p then continue
          | none => throw ⟨sp, s!"`{cb.name}` is provided `{e}`, and is passed here outside every handler of `{e}`"⟩
          let some eff := cx.env.eff? e | throw ⟨sp, s!"internal error: the effect `{e}`"⟩
          unless eff.ops.all (·.abortive) do
            throw ⟨sp, s!"`{cb.name}` is provided `{e}`, whose operations resume, and is passed to `{x}`, " ++
              s!"which does not provide it, outside the handlers of `{e}` that serve it: its port would " ++
              "be relabelled, which needs the callback inlined or a `rename` primitive (R2c, not built)"⟩
          report sp "lowering" (s!"{x}: passed `{cb.name}`, provided {e}, outside its handler, under a " ++
            s!"site of its port {p} whose clauses raise again at the handler around it (R2c)")
          return ← withCtl k cx cs sp sp (relabelHandler sp eff) [] (.unit sp) (.ret sp (.app sp f W)) (some p)
    -- What the copy performs: the function's own row, and what its callbacks tunnel.
    let own := ((cx.env.fn? x).map (·.row)).getD [] |>.map (·.subst σ)
    let Rc := specs.foldl (fun r (c, _) => union r c.T) own
    -- What serves it here.
    let mut hs : List HSig := []
    let mut ss : List Site := []
    let mut keys : List String := []
    let mut envMut : List (String × Bool) := []
    for i in Rc do
      if cx.env.answering i.eff then
        let some c := cx.capOf i.eff
          | throw ⟨sp, s!"`{x}` performs `{i.eff}`, but no handler of `{i.eff}` is in scope here"⟩
        match c.env with
        | some m => envMut := envMut ++ [(i.eff, m)]; keys := keys ++ ["e"]
        | none => hs := hs ++ [c.h]; keys := keys ++ [c.h.name]
      else
        let s ← (cx.serve sp s!"`{x}`" i : Except Error Site)
        ss := ss ++ [s]
        keys := keys ++ [s!"n{s.n}"]
    -- A callback that tunnels one of the callee's ports was written inside the callee's own
    -- handler of it: the recursion through a site of decision 57.
    let myPorts := (← get).ports.filterMap fun ((g, _), p) => if g == x then some p else none
    if let some (c, _) := specs.find? fun (c, cl?, _) => cl?.isSome && c.T.any fun i =>
        ss.any fun s => s.eff == i.eff && myPorts.contains s.n then
      throw ⟨sp, s!"`{x}` is passed a callback at `{c.cp.name}` that performs an effect at the handler " ++
        s!"inside `{x}` that serves its callbacks: each level would need a copy whose sites are its own, " ++
        "without end (recursion through a site, decision 57; generative labels, #173)"⟩
    let σkeys := tps.filterMap fun t => (σ.lookup t).map fun T => sanitize (T.pp 0)
    let specKeys := specs.map fun (c, _) => s!"k{c.cp.idx}" ++
      String.join (c.T.map fun i => "_" ++ i.eff) ++ String.join (c.ports.map fun (_, p) => s!"_p{p}") ++
      (if c.assigns then "_m" else "")
    let name := copyName x (keys ++ σkeys ++ specKeys)
    -- The capabilities as this call holds them: those of the copy's row, then each callback's
    -- environment, a passed parameter's its own.
    let used := cx.needIn Rc
    let mut envCaps : List Cap := []
    for (c, cl?, cb?) in specs do
      match cl?, cb? with
      | _, some cb =>
        let some ec := cx.caps.find? (·.eff == ((cb.caps.getLast?.map (·.eff)).getD ""))
          | throw ⟨sp, s!"internal error: the environment of `{cb.name}`"⟩
        envCaps := envCaps ++ [ec]
      | _, none =>
        let v ← fresh "fx_env"
        let ec : Cap := ⟨envEffName name c.cp.idx, v, "", noHandler sp, some s!"FX_W{c.cp.idx}", some c.assigns⟩
        envCaps := envCaps ++ [ec]
    let allCaps := used ++ envCaps
    -- Each callback's code.
    let mut codes : List (Nat × Val) := []
    for ((c, cl?, cb?), ec) in specs.zip envCaps do
      match cl?, cb? with
      | some (y, M, vars), _ =>
        let codeCaps := codeOrder (used.filter fun cc => c.T.any (·.eff == cc.eff))
        let mut ports : List Site := []
        for (e, Ps) in c.cp.prov do
          let args := Ps.map (·.subst σ)
          if args.any (mentions tps) then
            throw ⟨sp, s!"the type arguments of the `{e.name}` that `{x}` provides at `{c.cp.name}` are " ++
              s!"not determined here: write them, `{x}[…](…)`"⟩
          if let some pn := c.ports.lookup e.name then
            let site : Site := ⟨e.name, pn, args, none, sp, s!"`{x}`"⟩
            ports := ports ++ [site]
        codes := codes ++ [(c.cp.idx, ← cbCode k cx sp y M codeCaps ec vars ports)]
      | none, some cb =>
        -- Passed η-expanded at its lifetimes, `!thunkv Fun 'y₁ … return f ['y₁] …`: checked against
        -- the parameter's type, whose binders are numbered where it was written.
        let ls := (cb.caps.filter (·.thr.isNone)).zipIdx.map fun (_, i) => s!"fx_y{i}"
        let rec eta : List String → Val → Val
          | [], V => V
          | l :: rest, V => .thunkv sp (.lamL sp ⟨l, sp⟩ (.top sp) (.ret sp (eta rest (.inst sp V (.var sp l)))))
        let code : Val := match ls with
          | [] => .var sp cb.name
          | l :: rest => .bangThunkv sp (.lamL sp ⟨l, sp⟩ (.top sp)
              (.ret sp (eta rest (.inst sp (.var sp cb.name) (.var sp l)))))
        codes := codes ++ [(c.cp.idx, code)]
      | none, none => pure ()
    let name ← match (cx.env.fn? x).bind (·.group) with
      | some (gn, _) =>
        if !cx.env.inLayers.isEmpty then
          throw ⟨sp, s!"`{x}` is recursive, is passed a callback and runs under a layer: not provided"⟩
        groupCopy k { cx.env with inLayers := [] } sp gn Rc [] hs ss (keys ++ σkeys ++ specKeys) x
          (specs.map (·.1)) envMut
      | none => cbCopyOf k cx.env sp x d σ Rc hs ss envMut (specs.map (·.1)) name
    -- The call.
    let mut bs : List Bind := bP
    let mut args : List Val := []
    for (V, i) in comps.zipIdx do
      match codes.lookup i with
      | some code => args := args ++ [code]
      | none =>
        let (b, V') ← goV k cx cs V
        bs := bs ++ b
        args := args ++ [V']
    for ((_, cl?, _), ec) in specs.zip envCaps do
      if let some (_, _, vars) := cl? then
        let envB : Bind := fun N =>
          pure (.bind sp ⟨ec.var, sp⟩ none (.ret sp (tupleOf sp (vars.map (Val.var sp ·)))) N false)
        bs := bs ++ [envB]
    let t ← fresh "fx_b"
    let r ← fresh "fx_v"
    report sp "call" (s!"{x} → `{name}`" ++ (if used.isEmpty then "" else ", passing the capabilities") ++
      "; " ++ ", ".intercalate (specs.map fun (c, cl?, _) => s!"the callback at `{c.cp.name}` " ++
        (if cl?.isSome then "a closure value (its code and its environment)" else "passed on as it is")) ++
      ": one body per profile")
    let after (N : Comp) : EM Comp := do
      -- Each environment taken apart again: its variables as the callback leaves them.
      let mut K := N
      for ((_, cl?, _), ec) in (specs.zip envCaps).reverse do
        if let some (_, _, vars) := cl? then
          K ← bindParams sp ec.var (vars.map (⟨·, sp⟩)) K
      -- The capabilities bound again at their own types.
      pure (used.foldr (fun c K => if c.thr.isSome then K else
        .bind sp ⟨c.var, sp⟩ (some (c.ty sp)) (.ret sp (.var sp c.var)) K false) K)
    let call : Val := .app sp (.var f.span name) (capsTuple sp allCaps (tupleOf sp args))
    let bind : Bind := fun N => do
      pure (.bind sp ⟨t, sp⟩ none (.ret sp call) (← unpack sp allCaps r t (← after N)) false)
    pure (bs ++ [bind], .var sp r)

/-- The copy `name` of `x` made for callbacks (SPEC §22, R2a), once per (function, what serves its
row, the profile of each callback): `x`'s body at the type arguments `σ`, taking first the
capabilities of the row `Rc` (its own and its callbacks' tunneled rows) and each callback's
environment, and handing them back first. Each callback's parameter has the type of its code,

    !(∀'k₁ …. caps ⊗ (W ⊗ A) ⊸ F[ports ∪ tunneled] (caps ⊗ (W ⊗ B)))

`W` a type parameter of the copy, so one body serves every callback of the profile, whatever it
captures. A `with` of a provided effect around a call of the parameter is named by its port. -/
def cbCopyOf : Nat → Env → Span → String → Decl → TySubst → List Inst → List HSig → List Site →
    List (String × Bool) → List CbSpec → String → EM String
  | 0, _, sp, _, _, _, _, _, _, _, _, _ => throw ⟨sp, "internal error: copies nested too deeply"⟩
  | k + 1, env, sp, x, d, σ, Rc, hs, ss, envMut, specs, name => do
    let st ← get
    if st.made.any (·.1 == name) || st.started.contains name then return name
    modify fun s => { s with started := name :: s.started }
    let .def_ dsp dn ps A V mk := d | throw ⟨sp, s!"internal error: `{x}` is not a function"⟩
    let q := (← get).quiet
    if env.lib.contains x then modify fun s => { s with quiet := true }
    let ps := ps.filter fun p => (σ.lookup p.name).isNone
    let f ← (fnParts dsp dn.name (A.subst σ) (V.subst σ) : Except Error FnParts)
    let some pnames := paramNames f.p.name fuel f.body
      | throw ⟨dsp, s!"internal error: the parameters of `{x}`"⟩
    -- The capabilities, in the order of the row, then each callback's environment.
    let (caps, extraTps) := rowCaps env dsp Rc hs ss envMut
    let thrTps : List Ident := (ss.filterMap (·.thr)).map fun (_, W) => ⟨W, dsp⟩
    let ss' := ss.map fun s => { s with sp := dsp, what := "the caller" }
    let (envCaps, Ps, cbps, cbF) ← cbSetup env dsp x name σ caps ss' specs pnames
      (splitTy pnames.length f.P)
    let allCaps := caps ++ envCaps
    let effs' := envCaps.map (·.eff) ++ envMut.map (·.1) ++ env.envEffs
    let env' : Env := { env with fns := cbF ++ env.fns, inLayers := [], envEffs := effs' }
    let portsAll := (cbps.flatMap (·.ports)).eraseDups
    let cx : Cx := { env := env', caps := allCaps, sites := ss', fnCaps := allCaps, cbs := cbps, ports := portsAll }
    let body ← trC k cx allCaps true f.body
    let f' ← takeCaps dsp allCaps { f with P := tupleTy dsp Ps } body
    let (A', V') := f'.build dsp (env.rowOf ss')
    report dsp "lowering" (s!"copy `{name}`: `{x}` for " ++ ", ".intercalate
      ((hs.map (·.name)) ++ (ss.map fun s => s!"the site {s.n} of `{s.eff}`") ++
        (specs.map fun c => s!"the callback at `{c.cp.name}`" ++
          (if c.cp.prov.isEmpty then "" else
            s!" (provided {", ".intercalate (c.cp.prov.map (·.1.name))} at its port)"))) ++
      "; each callback a closure value, its environment a type parameter")
    modify fun s => { s with quiet := q }
    let base := match mk with
      | .template m => m
      | m => m
    let tps' := ps ++ thrTps ++ extraTps ++ specs.map fun c => (⟨s!"FX_W{c.cp.idx}", dsp⟩ : Ident)
    -- Its identity, with the same lifetime parameters and parameter type: a call passes its
    -- argument through it, so that the callbacks' `∀` code is checked against the parameter's type.
    let (iA, iV) := ({ f' with T := f'.P, body := .ret dsp (.var dsp f'.p.name) } : FnParts).build dsp
    let idName := name ++ "__id"
    modify fun s => { s with made := s.made.push (idName, .def_ dsp ⟨idName, dn.span⟩ tps' iA iV (.template base)) }
    modify fun s => { s with made := s.made.push (name, .def_ dsp ⟨name, dn.span⟩ tps' A' V' (.template base)) }
    pure name

/-- The copy of `g` for what serves its effects at a call in `cx`, made once. -/
def copyFor : Nat → Cx → Span → String → FSig → EM String
  | 0, _, sp, _, _ => throw ⟨sp, "internal error: copies nested too deeply"⟩
  | k + 1, cx, sp, x, g => do
    if let (some (gn, _), some d) := (g.group, cx.driver) then
      return ← deepCopy k { cx.env with inLayers := [] } sp gn d x
    let mut hs : List HSig := []
    let mut ss : List Site := []
    let mut keys : List String := []
    let row := cx.rowOf g
    for i in row do
      if cx.env.answering i.eff then
        let some c := cx.capOf i.eff
          | throw ⟨sp, s!"`{x}` performs `{i.eff}`, but no handler of `{i.eff}` is in scope here"⟩
        hs := hs ++ [c.h]
        keys := keys ++ [c.h.name]
      else
        let s ← (cx.serve sp s!"`{x}`" i : Except Error Site)
        ss := ss ++ [s]
        keys := keys ++ [s!"n{s.n}"]
    if keys.isEmpty then return x
    if let some (gn, _) := g.group then
      let env := { cx.env with inLayers := [] }
      return ← groupCopy k env sp gn row cx.env.inLayers hs ss (keys ++ cx.env.inLayers) x [] []
    copyOf k { cx.env with inLayers := [] } sp g hs ss (copyName x keys)

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
      let cxL : Cx := { env, caps := cs, sites := ss, fnCaps := cs,
                        layerCall := some ⟨callN.name, gv, j, rs⟩ }
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
            (.app gsp (.force gsp ⟨sf, gsp⟩) ⟨yv, gsp⟩) false) false) false))
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
    List String → String → List CbSpec → List (String × Bool) → EM String
  | 0, _, sp, _, _, _, _, _, _, _, _, _ => throw ⟨sp, "internal error: copies nested too deeply"⟩
  | k + 1, env, sp, gn, row, layers, hs, ss, keys, x, cbx, envMut => do
    let name := copyName x keys
    let stepName := copyName (gn ++ "__step") keys
    let st ← get
    if st.made.any (·.1 == stepName) || st.started.contains stepName then return name
    modify fun s => { s with started := stepName :: s.started }
    let some G := env.groups.find? (·.name == gn) | throw ⟨sp, s!"internal error: the group `{gn}`"⟩
    let some exh := env.exhEff? | throw ⟨sp, s!"internal error: the exhaustion effect"⟩
    let some e := ss.find? (·.eff == exh.name)
      | throw ⟨sp, s!"`{x}` is recursive: its depth is bounded, and no handler of `{exh.name}` is in scope here"⟩
    let gsp := G.sp
    -- The environment: the capabilities, in the order of the row, as `copyOf` takes them, and the
    -- environments of the callbacks passed to `x` (SPEC §22).
    let (cs₀, extraTps) := rowCaps env gsp row hs ss envMut
    let ss := ss.map fun s => { s with sp := gsp, what := "the caller" }
    let some jx := (G.members.map (·.1)).idxOf? x | throw ⟨sp, s!"internal error: `{x}`"⟩
    let some (_, fx) := G.members[jx]? | throw ⟨sp, s!"internal error: `{x}`"⟩
    if !cbx.isEmpty && !layers.isEmpty then
      throw ⟨sp, s!"`{x}` is recursive, is passed a callback and runs under a layer: not provided"⟩
    let pnames ← if cbx.isEmpty then pure [] else match paramNames fx.p.name fuel fx.body with
      | some ns => pure ns
      | none => throw ⟨sp, s!"internal error: the parameters of `{x}`"⟩
    let (envCaps, Psx, cbps, cbF) ← cbSetup env gsp x name [] cs₀ ss cbx pnames
      (splitTy pnames.length fx.P)
    let cs := cs₀ ++ envCaps
    -- The callbacks' code is captured by the generator, which takes it first: the members' types
    -- in `R` hold `()` in its place, so that `R` has no `∀` of the code's lifetimes.
    let cbPos : List Nat := cbx.map (·.cp.idx)
    let codeNames : List String := cbPos.map fun i => (pnames.getD i ⟨"?", gsp⟩).name
    -- Each member's parameters named as `x`'s computation parameters are passed the same callbacks
    -- (a parser's error callback, passed down): the positions and names, by member.
    let cbOf : List (List (Nat × String)) := G.members.map fun (_, f) =>
      if cbx.isEmpty then [] else
      match paramNames f.p.name fuel f.body with
      | some ns => ns.zipIdx.filterMap fun (y, i) => if codeNames.contains y.name then some (i, y.name) else none
      | none => []
    let Pof (j : Nat) (f : FnParts) : VTy :=
      let pos := (cbOf[j]?).getD []
      if pos.isEmpty then f.P else
      let ns := ((paramNames f.p.name fuel f.body).getD []).length
      tupleTy gsp ((splitTy ns f.P).zipIdx.map fun (A, i) => if pos.any (·.1 == i) then VTy.unit gsp else A)
    let tps : List Ident := (ss.filterMap (·.thr)).map (fun (_, W) => (⟨W, gsp⟩ : Ident)) ++ extraTps ++
      cbx.map fun c => (⟨s!"FX_W{c.cp.idx}", gsp⟩ : Ident)
    let tArgs : List VTy := tps.map fun t => .name gsp t.name
    let lives : List (Ident × Life) :=
      (cs.filter (·.thr.isNone)).map fun c => ((⟨c.life, gsp⟩ : Ident), Life.top gsp)
    let rowR := env.rowOf ss
    let n := G.members.length
    -- Made for callbacks, the fields are generic in the capabilities' lifetimes (`RSelf.poly`).
    -- So are they when a member passes a callback that calls the group (recursion through values):
    -- its call holds the capabilities at the callee's lifetimes. Then the generator is made in each
    -- member's copy, where the record's type is written.
    let poly := !cbx.isEmpty || G.members.any fun (_, f) => closureRefsC (G.members.map (·.1)) fuel f.body
    let polyL : List String := if !poly then [] else
      (cs.filter (·.thr.isNone)).map fun c => "fx_g_" ++ c.eff.toLower
    let csP : List Cap := if !poly then cs else
      cs.map fun c => if c.thr.isSome then c else { c with life := "fx_g_" ++ c.eff.toLower }
    let Cs : List CTy := G.members.zipIdx.map fun ((_, f), j) =>
      polyL.foldr (fun x C => .all gsp ⟨x, gsp⟩ (.top gsp) C)
        (.arr gsp (capsTy gsp csP (Pof j f)) (.eff gsp rowR (capsTy gsp csP f.T)))
    let R := ampTys gsp Cs
    let selfT : VTy := .sum gsp (.unit gsp) (.bang gsp (.thunk gsp (.arr gsp (.unit gsp) R)))
    let self := "fx_self"
    let rs : RSelf := ⟨G.members.map (·.1), e.n, self, Cs, cs, ss.map (fun s => (s.eff, s.n)), false,
      (cbOf.zipIdx.filterMap fun (pos, j) => if pos.isEmpty then none else some (j, pos)),
      polyL, rowR, G.members.map (·.2.T)⟩
    let effs' := envCaps.map (·.eff) ++ envMut.map (·.1) ++ env.envEffs
    let env' : Env := { env with envEffs := effs' }
    let cx : Cx := { env := env', caps := csP, sites := ss, fnCaps := csP, recSelf := some rs }
    let portsAll := (cbps.flatMap (·.ports)).eraseDups
    -- The generator's record: each member's body, taking the environment first.
    let mut fields : List Comp := []
    for ((_, f), j) in G.members.zipIdx do
      let pos := (cbOf[j]?).getD []
      let cxj : Cx := if !pos.isEmpty then
          { cx with env := { env' with fns := cbF ++ env'.fns }, cbs := cbps, ports := portsAll }
        else cx
      let body ← trC k cxj csP true f.body
      -- A member passed the callbacks takes `()` in their place, and its parameters are bound with
      -- the code the generator captured.
      let (pn, body) ← if !pos.isEmpty then do
          let q ← fresh "fx_rq"
          let pj := (paramNames f.p.name fuel f.body).getD []
          let vs ← pj.mapM fun _ => fresh "fx_ra"
          let full := tupleOf gsp (vs.zipIdx.map fun (v, i) =>
            match pos.lookup i with
            | some y => Val.var gsp y
            | none => .var gsp v)
          let rebuilt := Comp.bind gsp f.p none (.ret gsp full) body false
          pure (q, ← bindParams gsp q (vs.map (⟨·, gsp⟩)) rebuilt)
        else pure (f.p.name, body)
      let field ← if cs.isEmpty then pure (Comp.lam gsp ⟨pn, gsp⟩ (Pof j f) body)
        else do
          let pp ← fresh "fx_pp"
          pure (.lam gsp ⟨pp, gsp⟩ (capsTy gsp csP (Pof j f)) (← unpack gsp csP pn pp body))
      fields := fields ++ [polyL.foldr (fun x M => .lamL gsp ⟨x, gsp⟩ (.top gsp) M) field]
    let ps ← fresh "fx_rsp"
    let pu ← fresh "fx_ru"
    let P : VTy := .tensor gsp selfT (.unit gsp)
    let gen : Comp := .lam gsp ⟨ps, gsp⟩ P
      (.letPair gsp ⟨self, gsp⟩ ⟨pu, gsp⟩ (.var gsp ps) (.letUnit gsp (.var gsp pu) (withAll gsp fields)))
    -- `!U (P -o R)`, under the capabilities' lifetimes when there are any; taking the callbacks'
    -- code first when there are any.
    let genT₀ : VTy := .bang gsp (.thunk gsp (.arr gsp P R))
    let (genT, genV) : VTy × Val := (genT₀, .bangThunkv gsp gen)
    let (sA, sV) : VTy × Val := match lives.foldr (fun (a, b) (T, V) =>
        (VTy.all gsp a b T, Val.thunkv gsp (.lamL gsp a b (.ret gsp V)))) (genT, genV) with
      | (T@(.all ..), .thunkv _ M) => (.bang gsp T, .bangThunkv gsp M)
      | TV => TV
    report gsp "lowering" (s!"recursive group {", ".intercalate (G.members.map (·.1))}: the generator " ++
      s!"`{stepName}`, the record of its members" ++
      (if cs.isEmpty then "" else ", each taking the capabilities as its environment") ++
      s!"; each member's copy is bounded_fix of it at the budget {recBudget}, its calls of itself " ++
      s!"direct calls of the self-reference, the exhaustion effect at the site {e.n}")
    let mk : Mark := if tps.isEmpty then .none else .template .none
    -- With callbacks, the generator is made in the member's copy, where it captures their code:
    -- `!` code, which a `!` closure may hold. The record `R` holds none of it.
    if !poly then
      modify fun s => { s with made := s.made.push (stepName, .def_ gsp ⟨stepName, gsp⟩ tps sA sV mk) }
    -- The layers, innermost first: each a transformer of the generator.
    let mut trs : List String := []
    for L in layers do
      trs := trs ++ [← layerCopy k env gsp L G cs ss rs selfT R lives tps keys]
    -- Each member's copy: `(bounded_fix[1, R] (Lₙ(… L₁(gen))), (budget, ()))).j`.
    let genRef : Val := if tps.isEmpty then .var gsp stepName else .defApp gsp stepName tArgs
    for ((mn, f), j) in G.members.zipIdx do
      -- Made for callbacks, only the member passed them has a copy: the others have no code to
      -- give the generator.
      if !cbx.isEmpty && j != jx then continue
      let p ← fresh "fx_rp"
      let sv ← fresh "fx_rst"
      let fb ← fresh "fx_rbf"
      let fa ← fresh "fx_rba"
      let inst₀ : Val := lives.foldl (fun V (a, _) => .inst gsp V (.var gsp a.name))
        (if lives.isEmpty then genRef else .unbang gsp genRef)
      -- With callbacks: the generator applied to their code, taken from the argument, which the
      -- recursion is entered with `()` in its place.
      let vs ← pnames.mapM fun _ => fresh "fx_rv"
      let p' ← fresh "fx_rp"
      let inst : Val := if !poly then inst₀ else genV
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
      let pe := if cbx.isEmpty then p else p'
      let fixC : Comp :=
          (.bind gsp ⟨fb, gsp⟩ none (.ret gsp (.unbang gsp (.const gsp (.boundedFix (.unit gsp) R))))
            (.bind gsp ⟨fa, gsp⟩ none (.ret gsp arg)
              (.app gsp ((lives.map (·.1.name)).foldl (fun M l => if polyL.isEmpty then M else .inst gsp M (.var gsp l))
                (projAt gsp j n (.app gsp (.force gsp ⟨fb, gsp⟩) ⟨fa, gsp⟩))) ⟨pe, gsp⟩) false)
            false)
      let body : Comp :=
        .bind gsp ⟨sv, gsp⟩ (if poly then some genT else none) (.ret gsp inst) (applied.foldr (fun (y, V) K =>
          .bind gsp ⟨y, gsp⟩ none (.ret gsp V) K false) fixC) false
      -- The argument taken apart: the code out, `()` in its place.
      let body ← if cbx.isEmpty then pure body else do
        let q ← fresh "fx_rq"
        let codesOut : List (String × String) :=
          (cbPos.zip codeNames).map fun (i, c) => (vs.getD i "?", c)
        let entry := capsTuple gsp cs (tupleOf gsp (vs.zipIdx.map fun (v, i) =>
          if cbPos.contains i then Val.unit gsp else .var gsp v))
        let K := codesOut.foldr (fun (v, c) K => Comp.bind gsp ⟨c, gsp⟩ none (.ret gsp (.var gsp v)) K false)
          (.bind gsp ⟨p', gsp⟩ none (.ret gsp entry) body false)
        let K ← bindParams gsp q (vs.map (⟨·, gsp⟩)) K
        unpack gsp cs q p K
      let Pj := if cbx.isEmpty then f.P else tupleTy gsp Psx
      let drv : FnParts := ⟨true, lives, capsTy gsp cs Pj, capsTy gsp cs f.T, ⟨p, gsp⟩, body⟩
      let (dA, dV) := drv.build gsp rowR
      let dn := copyName mn keys
      -- A member passed callbacks takes its argument through its identity (`cbCopyOf`).
      if j == jx && !cbx.isEmpty then
        let (iA, iV) := ({ drv with T := drv.P, body := .ret gsp (.var gsp p) } : FnParts).build gsp
        modify fun s => { s with made := s.made.push (dn ++ "__id", .def_ gsp ⟨dn ++ "__id", gsp⟩ tps iA iV mk) }
      modify fun s => { s with made := s.made.push (dn, .def_ gsp ⟨dn, gsp⟩ tps dA dV mk) }
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
    if let some i := g₀.row.find? (·.eff != exh.name) then
      throw ⟨sp, s!"`{x}` performs `{i.eff}`: a recursion that performs an effect is not provided " ++
        s!"under the heap driver `{d}`"⟩
    let A := sumTys gsp (G.members.map (·.2.P))
    let some (_, f₀) := G.members.head? | throw ⟨gsp, "internal error: an empty group"⟩
    let B := f₀.T
    if let some (y, _) := G.members.find? (·.2.T.strip != B.strip) then
      throw ⟨sp, s!"`{y}` answers a type other than `{x}`'s: members with different result types " ++
        s!"are not provided under the heap driver `{d}`"⟩
    let rs : RSelf := ⟨G.members.map (·.1), 0, "", [], [], [], true, [], [], .nil, []⟩
    let cx : Cx := { env, caps := [], recSelf := some rs }
    let mut bodies : List (Ident × Comp) := []
    for (_, f) in G.members do
      let body ← trC k cx [] true f.body
      let xi ← fresh "fx_ra"
      bodies := bodies ++ [(⟨xi, gsp⟩, .bind gsp f.p none (.ret gsp (.var gsp xi)) body false)]
    let fa ← fresh "fx_rarg"
    let rec dispatch : Nat → String → List (Ident × Comp) → EM Comp
      | _, _, [] => throw ⟨gsp, "internal error: an empty group"⟩
      | _, v, [(xi, B₁)] => pure (.bind gsp xi none (.ret gsp (.var gsp v)) B₁ false)
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
    modify fun s => { s with made := s.made.push (src, .def_ gsp ⟨src, gsp⟩ [] sA sV .none) }
    for ((mn, f), j) in G.members.zipIdx do
      let p ← fresh "fx_dp"
      let ms ← fresh "fx_ms"; let mr ← fresh "fx_mr"
      let call : Val := .app gsp (.var gsp d) (.pair gsp (.var gsp ms) (.pair gsp (.var gsp mr)
        (.ascribe gsp (injAt gsp j G.members.length (.var gsp p)) A)))
      let body : Comp := .letPair gsp ⟨ms, gsp⟩ ⟨mr, gsp⟩ (.var gsp mach) (.ret gsp call)
      let drv : FnParts := ⟨true, [], f.P, B, ⟨p, gsp⟩, body⟩
      let (dA, dV) := drv.build gsp
      let dn := s!"{mn}__{d}"
      modify fun s => { s with made := s.made.push (dn, .def_ gsp ⟨dn, gsp⟩ [] dA dV .none) }
    pure name

/-- The copy `name` of `g` for the answering handlers `hs` and the sites `ss`, made once: its body
elaborated with their capabilities as parameters and their operations as its row. -/
def copyOf : Nat → Env → Span → FSig → List HSig → List Site → String → EM String
  | 0, _, sp, _, _, _, _ => throw ⟨sp, "internal error: copies nested too deeply"⟩
  | k + 1, env, sp, g, hs, ss, name => do
    let st ← get
    if st.made.any (·.1 == name) || st.started.contains name then return name
    modify fun s => { s with started := name :: s.started }
    let .def_ dsp n ps A V mk := g.decl
      | throw ⟨sp, s!"internal error: `{g.name}` is not a function"⟩
    let q := (← get).quiet
    if env.lib.contains g.name then modify fun s => { s with quiet := true }
    let f ← (fnParts dsp n.name A V : Except Error FnParts)
    -- The capabilities, in the order of the row: an answering handler's, and the variable a
    -- `for`'s site threads (whose type is a parameter of the copy, `W`).
    let cs : List Cap := g.row.filterMap fun i =>
      if env.answering i.eff then
        (hs.find? (·.eff == i.eff)).map fun h => ⟨i.eff, "fx_c_" ++ i.eff.toLower, "fx_l_" ++ i.eff.toLower, h, none, none⟩
      else (ss.find? (·.eff == i.eff)).bind fun s => s.thr.map fun (w, W) => threadCap dsp i.eff w W
    let tps : List Ident := (ss.filterMap (·.thr)).map fun (_, W) => ⟨W, dsp⟩
    let ss := ss.map fun s => { s with sp := dsp, what := "the caller" }
    let cx : Cx := { env, caps := cs, sites := ss, fnCaps := cs }
    let body ← trC k cx cs true f.body
    let f' ← if cs.isEmpty then pure { f with body } else takeCaps dsp cs f body
    let (A', V') := f'.build dsp (env.rowOf ss)
    report dsp "lowering" (s!"copy `{name}`: `{g.name}` for " ++ ", ".intercalate
      ((hs.map (·.name)) ++ ss.map fun s => s!"the site {s.n} of `{s.eff}`"))
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
`fn h__op<'l>(c: mut 'l S, x: A, …) -> mut 'l S * B`, whose body runs the clause on the state by
`modify` (`withswap`) and hands the borrow back. -/
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
  -- first, since a lend cannot be in an annotated binding.
  let body := wrapTerms (fun T =>
    let hand := Comp.ret T.span (.pair T.span (.var T.span st) (.var T.span v))
    match T with
    | .ret _ V => if V.lends then
        .bind T.span ⟨w, T.span⟩ none T
          (.bind T.span ⟨v, T.span⟩ (some o.res) (.ret T.span (.var T.span w)) hand false) false
      else .bind T.span ⟨v, T.span⟩ (some o.res) T hand false
    | _ => .bind T.span ⟨v, T.span⟩ (some o.res) T hand false) c.body
  let modifyV : Val := .app sp (.app sp (.sugar sp (.borrow .modify "")) (.var sp cv))
    (.thunkv sp (.lam sp h.st (.name sp "_") body))
  let b ← fresh "fx_b"
  let r ← fresh "fx_r"
  let inner : Comp := .bind sp ⟨b, sp⟩ none (.ret sp modifyV)
    (.letPair sp ⟨cv, sp⟩ ⟨r, sp⟩ (.var sp b) (.ret sp (.pair sp (.var sp cv) (.var sp r)))) false
  let p ← fresh "fx_p"
  let inner ← bindParams sp p c.params inner
  let pp ← fresh "fx_pp"
  let cap : Cap := ⟨h.eff, cv, l, h, none, none⟩
  let P := tupleTy sp (o.params.map (·.2))
  let f : FnParts := ⟨true, [(⟨l, sp⟩, .top sp)], capsTy sp [cap] P, capsTy sp [cap] o.res, ⟨pp, sp⟩,
    .letPair sp ⟨cv, sp⟩ ⟨p, sp⟩ (.var sp pp) inner⟩
  let (A, V) := f.build sp
  pure (.def_ sp ⟨clauseName h.name c.name.name, sp⟩ [] A V .none)

/-! ### Programs -/

/-- A computation has a `while` or a `loop` outside nested closures. -/
def hasWhile : Nat → Comp → Bool
  | 0, _ => false
  | k + 1, M => match M with
    | .for_ _ _ (.app _ (.sugar _ .while_) _) _ _ => true
    | .for_ _ _ _ B N => hasWhile k B || hasWhile k N
    | .bind _ _ _ M N _ | .with_ _ M N => hasWhile k M || hasWhile k N
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

/-- The names a declaration defines. -/
def Decl.defName : Decl → Option String
  | .def_ _ n _ _ _ _ => some n.name
  | _ => none

/-- The marks of a definition taken apart: its written row, the provided rows of its computation
parameters (SPEC §22), and the rest. -/
def splitMarks : Mark → List (Ident × List VTy) × List (String × List (Ident × List VTy)) × Mark
  | .row es m => let (r, p, m') := splitMarks m; (es ++ r, p, m')
  | .provides x es m => let (r, p, m') := splitMarks m; (r, (x.name, es) :: p, m')
  | .template m => let (r, p, m') := splitMarks m; (r, p, .template m')
  | m => ([], [], m)

/-- The mark of a definition without its written row, and the row. -/
def splitRow (m : Mark) : List (Ident × List VTy) × Mark :=
  let (r, _, m') := splitMarks m
  (r, m')

/-- Anything for this pass to do: an effect, a handler or a written row. -/
def hasEffects (ds : List Decl) : Bool :=
  ds.any fun
    | .effect .. | .handler .. | .chandler .. => true
    | .def_ _ _ _ _ _ mk => (match mk with | .row .. | .provides .. => true | _ => false)
    | _ => false

/-- The recursive group of the definitions `ms` declared (SPEC §20): each member a function of the
group's row, the union of what its members' bodies perform and the exhaustion effect, which
`bounded`, its default driver, performs when the budget of depth is spent. A call of a member is a
call of its copy for what serves that row (`groupCopy`). -/
def defineGroup (env : Env) (ms : List (Span × Ident × VTy × Val × Mark)) : EM Env := do
  let some (sp₀, n₀, _, _, _) := ms.head? | throw ⟨Span.none, "internal error: an empty group"⟩
  let some exh := env.exhEff?
    | throw ⟨n₀.span, s!"`{n₀.name}` calls itself{if ms.length > 1 then " through " ++
        ", ".intercalate (ms.map (·.2.1.name)) else ""}: a recursion's depth is bounded, and its " ++
        "exhaustion effect is in `lib/rec.bc`: `include rec`"⟩
  let mut parts : List (String × FnParts) := []
  let mut row : List Inst := []
  for (sp, n, A, V, mk) in ms do
    let f ← (fnParts sp n.name A V : Except Error FnParts)
    unless f.lives.isEmpty do
      throw ⟨n.span, s!"`{n.name}` is recursive and takes lifetime parameters: not provided"⟩
    unless f.bang do
      throw ⟨n.span, s!"`{n.name}` is recursive and is not a persistent function"⟩
    if hasWhile fuel f.body then
      throw ⟨n.span, s!"`{n.name}` is recursive and its body has a `while` or a `loop`, so it is " ++
        "div: the `Exhausted` of its budget would be performed inside its loop, and a handler around " ++
        "a div computation is not provided"⟩
    let (written, _) := splitRow mk
    -- A computation parameter performs what it is provided (SPEC §22).
    let cbF : List FSig := (env.cparamsOf n.name).filterMap fun cp => if cp.prov.isEmpty then none else
      some { name := cp.name, row := cp.prov.map fun (e, As) => ⟨e.name, some As⟩, decl := .main sp (.top sp) (.top sp) }
    for i in rowV { env with fns := cbF ++ env.fns } fuel V do
      unless written.isEmpty || written.any (·.1.name == i.eff) do
        throw ⟨n.span, s!"`{n.name}` performs `{i.eff}`, which its written row does not list"⟩
      let i ← match written.find? (·.1.name == i.eff), i.args with
        | some (_, As), _ => pure ⟨i.eff, some As⟩
        | none, some _ => pure i
        | none, none => throw ⟨n.span, s!"`{n.name}` performs `{i.eff}`, and its type arguments " ++
            s!"are not determined: write them, `with {i.eff}[…]`"⟩
      row := addInst row i
    unless written.isEmpty || written.any (·.1.name == exh.name) do
      throw ⟨n.span, s!"`{n.name}` is recursive, so it performs `{exh.name}` when its depth runs out, " ++
        "which its written row does not list"⟩
    parts := parts ++ [(n.name, f)]
  row := addInst row ⟨exh.name, some []⟩
  let G : RGroup := ⟨n₀.name, parts, sp₀⟩
  report sp₀ "row" (s!"{", ".intercalate (parts.map (·.1))}: " ++
    ", ".intercalate (row.map (·.eff)) ++ s!" (a recursive group: the fixed point of its " ++
    s!"generator, driven by `bounded` at the budget {recBudget})")
  let mut env := { env with groups := env.groups ++ [G] }
  for ((x, _), (sp, n, A, V, mk)) in parts.zip ms do
    env := { env with fns := env.fns ++ [{ name := x, row, decl := .def_ sp n [] A V mk,
                                             group := some (G.name, (parts.map (·.1)).idxOf x) }] }
  pure env

/-- `e |> g(a, …)` resolved (decision 50, SPEC §22): `with g(a, …) { e }` when `g` is a handler, a
heap driver or a layer; `g({ _ -> e }, a, …)` when `g`'s first parameter is a computation
parameter, `e` suspended; `g(e, a, …)` otherwise. -/
def pipeOf (env : Env) (sp : Span) (e g : Val) (k : Nat) : Val :=
  let (f, W?) : Val × Option Val := match g with
    | .app _ f W => (f, some W)
    | f => (f, none)
  let h := headName f
  let isHandler := match h with
    | some x => (env.handler? x).isSome || (env.chandler? x).isSome || env.driver? x ||
        (env.layer? x).isSome
    | none => false
  if isHandler then
    let (x, As) := match f with
      | .defApp _ x As => (x, As)
      | _ => (h.getD "", [])
    .app sp (.app sp (.sugar sp (.handle x s!"fx_pl{k}" As)) (W?.getD (.unit sp)))
      (.thunkv sp (.lam sp ⟨s!"fx_pc{k}", sp⟩ (holeTy sp) (.ret sp e)))
  else
    let first := match h with
      | some x => (env.cparamsOf x).any (·.idx == 0)
      | none => false
    let e' : Val := if first then .thunkv sp (.lam sp ⟨s!"fx_pu{k}", sp⟩ (holeTy sp) (.ret sp e)) else e
    let args : Val := match W? with
      | none | some (.unit _) => e'
      | some W => .pair sp e' W
    .app sp f args

mutual
/-- A value with its pipes resolved (`pipeOf`). -/
def pipesV (env : Env) : Nat → Val → Val
  | 0, V => V
  | n + 1, V => match V with
    | .app sp (.sugar _ .pipe) (.pair _ e g) => pipeOf env sp (pipesV env n e) (pipesV env n g) n
    | .pair sp V W => .pair sp (pipesV env n V) (pipesV env n W)
    | .app sp V W => .app sp (pipesV env n V) (pipesV env n W)
    | .inl sp V => .inl sp (pipesV env n V)
    | .inr sp V => .inr sp (pipesV env n V)
    | .unbang sp V => .unbang sp (pipesV env n V)
    | .boxed sp a V => .boxed sp a (pipesV env n V)
    | .unbox sp V => .unbox sp (pipesV env n V)
    | .sub sp V a => .sub sp (pipesV env n V) a
    | .roll sp V => .roll sp (pipesV env n V)
    | .unroll sp V => .unroll sp (pipesV env n V)
    | .inst sp V a => .inst sp (pipesV env n V) a
    | .ascribe sp V A => .ascribe sp (pipesV env n V) A
    | .shorten sp m σ a V => .shorten sp m σ a (pipesV env n V)
    | .thunk sp M => .thunk sp (pipesC env n M)
    | .thunkv sp M => .thunkv sp (pipesC env n M)
    | .bangThunk sp M => .bangThunk sp (pipesC env n M)
    | .bangThunkv sp M => .bangThunkv sp (pipesC env n M)
    | .run sp M => .run sp (pipesC env n M)
    | V => V

/-- A computation with its pipes resolved. -/
def pipesC (env : Env) : Nat → Comp → Comp
  | 0, M => M
  | n + 1, M => match M with
    | .ret sp V => .ret sp (pipesV env n V)
    | .bind sp x A M N lin => .bind sp x A (pipesC env n M) (pipesC env n N) lin
    | .lam sp x A M => .lam sp x A (pipesC env n M)
    | .app sp M x => .app sp (pipesC env n M) x
    | .with_ sp M N => .with_ sp (pipesC env n M) (pipesC env n N)
    | .proj sp i M => .proj sp i (pipesC env n M)
    | .letUnit sp V M => .letUnit sp (pipesV env n V) (pipesC env n M)
    | .letPair sp x y V M => .letPair sp x y (pipesV env n V) (pipesC env n M)
    | .case sp V x M y N => .case sp (pipesV env n V) x (pipesC env n M) y (pipesC env n N)
    | .absurd sp V => .absurd sp (pipesV env n V)
    | .lamL sp x b M => .lamL sp x b (pipesC env n M)
    | .inst sp M a => .inst sp (pipesC env n M) a
    | .nuIn sp M => .nuIn sp (pipesC env n M)
    | .nuOut sp M => .nuOut sp (pipesC env n M)
    | .ascribe sp M C => .ascribe sp (pipesC env n M) C
    | .for_ sp x V M N => .for_ sp x (pipesV env n V) (pipesC env n M) (pipesC env n N)
    | .perform sp k i V => .perform sp k i (pipesV env n V)
    | .abort sp k i V => .abort sp k i (pipesV env n V)
    | .handle sp k hr hc M => .handle sp k hr hc (pipesC env n M)
    | .unwind sp x A M D N => .unwind sp x A (pipesC env n M) (pipesC env n D) (pipesC env n N)
    | M => M
end

/-- A declaration has a pipe `e |> g(…)` (decision 50). -/
def hasPipe : Decl → Bool
  | .def_ _ _ _ _ V _ => (pipesV {} fuel V) != V
  | .main _ _ M => (pipesC {} fuel M) != M
  | _ => false

/-- The program with its effects elaborated, and the reports for `bcc check`: the effect and
handler declarations are removed, each answering handler's clauses become functions, each
function with a row is replaced by its copies for what serves it where it is called, each `with`
of an answering handler becomes a borrow block, and each of a control handler a handler site.
`[spec §18, §19]` -/
def elaborate (ds : List Decl) (lib : List String := []) :
    Except Error (List Decl × List (Span × String)) := do
  -- The recursive groups among the program's own functions (SPEC §20).
  let groups := recGroupsOf (ds.filterMap fun
    | .def_ _ n [] _ V _ => if lib.contains n.name then none else some (n.name, V)
    | _ => none)
  if let some (sp, n) := ds.findSome? (fun
      | .def_ sp n (_ :: _) _ V _ => if (refsV fuel V).contains n.name then some (sp, n.name) else none
      | _ => none) then
    throw ⟨sp, s!"`{n}` is generic and calls itself: a generic recursive function is not provided"⟩
  if !hasEffects ds && groups.isEmpty && !ds.any hasPipe then return (ds, [])
  let names := ds.filterMap Decl.defName
  let go : EM (List Decl) := do
    let mut env : Env := { lib }
    let mut out : Array Decl := #[]
    for d in ds do
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
        env := { env with effs := env.effs ++ [sig],
                          ops := env.ops ++ (ops.zipIdx.map fun (o, i) => ⟨e.name, i, o⟩) }
        report sp "effect" (s!"{e.name}: " ++ ", ".intercalate (ops.map fun o =>
          s!"{o.name.name}{match o.kind with
            | .fn => ""
            | .ctl q => s!" (ctl, {match q with | .lin => "linear" | .aff => "affine" | .unr => "unrestricted"}{
                if o.abortive then ", abortive" else ""})"}"))
      | .handler sp h st S e cs =>
        let some eff := env.eff? e.name
          | throw ⟨e.span, s!"no effect `{e.name}` is declared before this handler"⟩
        unless eff.answering do
          throw ⟨e.span, s!"`{e.name}` has control operations: its handler is written " ++
            s!"`handler {h.name}[…](…) for {e.name}[…] -> R \{ return(x: A) -> …; op(…) -> … }`"⟩
        let hs : HSig := ⟨h.name, e.name, st, S, cs, sp⟩
        for o in eff.ops do
          unless cs.any (·.name.name == o.name.name) do
            throw ⟨sp, s!"the handler `{h.name}` has no clause for `{o.name.name}`"⟩
        for c in cs do
          let some o := eff.ops.find? (·.name.name == c.name.name)
            | throw ⟨c.name.span, s!"`{c.name.name}` is not an operation of `{e.name}`"⟩
          out := out.push (← clauseDef env hs o c)
        env := { env with handlers := env.handlers ++ [hs] }
        report sp "lowering" (s!"handler {h.name} ({e.name}): call — each clause resumes once, in " ++
          "tail position (fun): a direct call on the lent state (withswap), with no allocation and " ++
          "no dispatch")
      | .chandler _ ch =>
        let some eff := env.eff? ch.eff.name
          | throw ⟨ch.eff.span, s!"no effect `{ch.eff.name}` is declared before this handler"⟩
        if eff.answering then
          throw ⟨ch.eff.span, s!"`{ch.eff.name}` is answering: its handler is written " ++
            s!"`handler {ch.name.name}(s: S) for {ch.eff.name} \{ op(x) -> … }`"⟩
        unless ch.effArgs.length == eff.tps.length do
          throw ⟨ch.eff.span, s!"`{ch.eff.name}` takes {eff.tps.length} type argument(s)"⟩
        env := { env with chandlers := env.chandlers ++ [ch] }
      | .def_ sp n ps A V mk =>
        let V := pipesV env fuel V
        env := { env with sigs := (n.name, A) :: env.sigs }
        let (_, provs, mkS) := splitMarks mk
        env := { env with defs := (n.name, .def_ sp n ps A V mkS) :: env.defs }
        -- Its computation parameters (SPEC §22): those whose written type is a function type.
        let mut cps : List CParam := []
        if let .ok fp := fnParts sp n.name A V then
          if let some names := paramNames fp.p.name fuel fp.body then
            let Ts := splitTy names.length fp.P
            cps := ((names.zip Ts).zipIdx).filterMap fun ((x, T), k) =>
              (fnTyOf T).map fun (a, b, bang) => ⟨k, x.name, a, b, bang, (provs.lookup x.name).getD []⟩
            env := { env with arity := (n.name, names.length) :: env.arity }
        for (x, _) in provs do
          unless cps.any (·.name == x) do
            throw ⟨n.span, s!"`{x}` is given a provided row, and is not a parameter of `{n.name}` " ++
              "whose type is a function type"⟩
        unless cps.isEmpty do
          env := { env with cparams := (n.name, cps) :: env.cparams }
        if isLayerTy (ps.map (·.name)) A then
          env := { env with layers := (n.name, .def_ sp n ps A V mk) :: env.layers }
        modify fun s => { s with quiet := lib.contains n.name }
        if let some G := groups.find? (·.contains n.name) then
          -- A member of a recursive group: the group is declared at its last member.
          if G.getLast? == some n.name then
            env ← defineGroup env (ds.filterMap fun
              | .def_ sp' m _ A' V' mk' => if G.contains m.name then some (sp', m, A', V', mk') else none
              | _ => none)
          continue
        let (written, mk) := splitRow mk
        -- A computation parameter performs what it is provided, at the function's ports.
        let cbF : List FSig := cps.filterMap fun cp => if cp.prov.isEmpty then none else
          some { name := cp.name, row := cp.prov.map fun (e, As) => ⟨e.name, some As⟩, decl := .def_ sp n ps A V mk }
        let row := rowV { env with fns := cbF ++ env.fns } fuel V
        for i in row do
          unless written.isEmpty || written.any (·.1.name == i.eff) do
            throw ⟨n.span, s!"`{n.name}` performs `{i.eff}`, which its written row does not list"⟩
        -- Each instance's type arguments: written, or from what the function calls.
        let mut row' : List Inst := []
        for i in row do
          match written.find? (·.1.name == i.eff) with
          | some (_, As) =>
            let k := ((env.eff? i.eff).map (·.tps.length)).getD 0
            unless As.length == k do
              throw ⟨n.span, s!"`{i.eff}` takes {k} type argument(s)"⟩
            row' := row' ++ [⟨i.eff, some As⟩]
          | none => match i.args with
            | some _ => row' := row' ++ [i]
            | none => throw ⟨n.span, s!"`{n.name}` performs `{i.eff}`, and its type arguments are " ++
                s!"not determined: write them, `with {i.eff}[…]`"⟩
        let d₀ : Decl := .def_ sp n ps A V mk
        -- A row on a value that is not a function: a function with a row used as a value, which
        -- is reported as such.
        if !row'.isEmpty && (fnParts sp n.name A V).toOption.isNone then
          discard (trV fuel { env, caps := [] } [] V)
        if !row'.isEmpty then
          env := { env with fns := env.fns ++ [{ name := n.name, row := row', decl := d₀ }] }
          report sp "row" (s!"{n.name}: " ++ ", ".intercalate (row'.map fun i =>
            match i.args with
            | some (_ :: _) => s!"{i.eff}[{", ".intercalate ((i.args.getD []).map (VTy.pp · 0))}]"
            | _ => i.eff))
        else if cps.any (!·.prov.isEmpty) then
          -- It provides effects to a callback: it is elaborated only as its copies (SPEC §22).
          pure ()
        else
          let before := (← get).made.size
          let (bs, V') ← trV fuel { env, caps := [] } [] V
          unless bs.isEmpty do throw ⟨V.span, "internal error: a definition's value was taken apart"⟩
          out := out ++ ((← get).made.extract before).map (·.2)
          out := out.push (.def_ sp n ps A V' mk)
      | .main sp C M =>
        let M := pipesC env fuel M
        modify fun s => { s with quiet := false }
        let before := (← get).made.size
        let M' ← trC fuel { env, caps := [] } [] false M
        out := out ++ ((← get).made.extract before).map (·.2)
        out := out.push (.main sp C M')
      | .extern sp x A =>
        env := { env with externs := x.name :: env.externs }
        out := out.push (.extern sp x A)
      | d => out := out.push d
    pure out.toList
  match go.run {} with
  | .ok (ds, st) => pure (ds, st.reports.toList)
  | .error e => throw e

end Frontend.Elab.Effects

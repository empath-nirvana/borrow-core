import Frontend.Parser
import Frontend.Print
import Frontend.Elab.Subst

/-!
# Frontend — Elab — effects and handlers  `[spec §18, §19]`

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
  the sites around its `with`.
* **A function's row** is the set of effect instances it performs: the operations it calls, and
  the rows of the functions it calls, less those a `with` inside it handles. It is inferred in
  declaration order; a written row (`fn f(…) -> T with E[A]`) is a promise that the inferred row is
  within it, and gives the type arguments of an effect the function performs directly. A function
  with a row is elaborated once per assignment of its effects to what serves them in scope (the
  handlers of its answering effects, the sites of its control effects), as a generic function is
  once per instance (decision 45): the copy `f__…` takes the capabilities first and hands them back
  first, and its type has the sites' operations as its row, `A ⇒ F[n.i …] B`. A call of `f` is a
  call of that copy, bound before the value it is in, so that it is a computation of its own.

What is not provided, with the message that says so: an operation inside a closure or block that
is not run in place, and a function with a row passed as a value (effectful callbacks, #161); a
lend `&mut x` in the arguments of a call that threads a capability; an operation of an answering
effect inside a clause; an effect with both kinds of operation; type parameters on an answering
effect; a function with a row whose result is a computation (a loop or a generator).
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

/-- A recursive group (SPEC §20): the functions of one strongly connected component of the calls,
each taken apart (`FnParts`), in declaration order, and their common result type. The group is
named by its first member. -/
structure RGroup where
  name : String
  members : List (String × FnParts)
  B : VTy
  sp : Span

/-- The step of a recursive group being elaborated: its members, the static name `m` of its `rec`
site, the site `e` of the exhaustion effect, and the variable `self` holding the self-reference
`1 + !U(A ⊸ C)` (`bounded_fix`'s, SPEC §20). -/
structure RSelf where
  members : List String
  m : Nat
  e : Nat
  self : String
  /-- The type of a self-call inside the step, `F[m.0 …, row] B`: the type the exhaustion
  effect's operation is ascribed there. -/
  C : CTy
  /-- The group's argument, the sum of its members' parameter types. -/
  A : VTy
  /-- The sites the copy serves its row's control effects at, by effect. -/
  served : List (String × Nat)

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

/-- The state of the elaboration: counters for fresh names and site names, the reports for
`bcc check`, and the copies made (finished ones in `made`, in the order they were finished). -/
structure St where
  fresh : Nat := 0
  site : Nat := 1
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

mutual
/-- The effects a value performs, outside the `with`s that handle them. A call of a function
performing an iteration effect, as an argument at a stored generator's parameter, is the stored
generator: it does not perform the iteration effect. -/
def rowV (env : Env) : Nat → Val → List Inst
  | 0, _ => []
  | n + 1, V => match V with
    | .app _ (.app _ (.sugar _ (.handle h _ _)) P) (.thunkv _ (.lam _ _ _ M)) =>
      let inner := rowC env n M
      let inner := match env.handler? h, env.chandler? h with
        | some hs, _ => without inner hs.eff
        | none, some ch => union (without inner ch.eff.name) (handlerRow ch)
        | none, none => inner
      union (rowV env n P) inner
    | .app _ f W =>
      let head := match headName f with
        | some x => match env.op? x, env.fn? x with
          | some o, _ => [env.opInst o]
          | none, some g => g.row
          | none, none => rowV env n f
        | none => rowV env n f
      let args := match headName f with
        | some x => (env.pullArgs x W).foldl (fun r (V, pull) => union r (pullRow env n pull V)) []
        | none => rowV env n W
      union head args
    | .var _ x => match env.fn? x with
      | some g => g.row
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

/-! ### Elaborating a body -/

/-- The context of an elaboration: what is declared, the capabilities and handler sites in scope,
and, in a function's copy, the capabilities its `return e` from inside a loop hands back. -/
structure Cx where
  env : Env
  caps : List Cap
  sites : List Site := []
  fnCaps : List Cap := []
  /-- In the step of a recursive group (SPEC §20): the group's members, the static name of its
  `rec` site and of the site of the exhaustion effect, and the variable holding the
  self-reference. -/
  recSelf : Option RSelf := none

/-- The capabilities of `cx` for the effects `row`, in the order of `cx.caps`. -/
def Cx.need (cx : Cx) (row : List Inst) : List Cap := cx.caps.filter (fun c => row.any (·.eff == c.eff))

/-- The capabilities of `cx` for the effects `row`, in the order of `row`: those a copy for them
takes first. -/
def Cx.needIn (cx : Cx) (row : List Inst) : List Cap := row.filterMap fun i => cx.caps.find? (·.eff == i.eff)

def Cx.needV (cx : Cx) (V : Val) : List Cap := cx.need (rowV cx.env fuel V)
def Cx.needC (cx : Cx) (M : Comp) : List Cap := cx.need (rowC cx.env fuel M)

/-- The control effects of `row`. -/
def Cx.ctl (cx : Cx) (row : List Inst) : List Inst := row.filter (!cx.env.answering ·.eff)

def Cx.ctlV (cx : Cx) (V : Val) : Bool := !(cx.ctl (rowV cx.env fuel V)).isEmpty
def Cx.ctlC (cx : Cx) (M : Comp) : Bool := !(cx.ctl (rowC cx.env fuel M)).isEmpty

/-- The capability of the effect `e` in scope. -/
def Cx.capOf (cx : Cx) (e : String) : Option Cap := cx.caps.find? (·.eff == e)

/-- The site of the control effect `e` in scope. -/
def Cx.siteOf (cx : Cx) (e : String) : Option Site := cx.sites.find? (·.eff == e)

def notInClosure (sp : Span) (e : String) : Error :=
  ⟨sp, s!"an operation of `{e}` is performed inside a closure or block that is not run in place: " ++
    "it cannot reach its handler (effectful callbacks, #161)"⟩

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
  ⟨e, w, "", ⟨"", e, ⟨"", sp⟩, .unit sp, [], sp⟩, some W⟩

/-- The capabilities of a copy made for the handlers `hs`, one per answering effect of `effs`. -/
def copyCaps (effs : List String) (hs : List HSig) : List Cap :=
  (effs.zip hs).map fun (e, h) => ⟨e, "fx_c_" ++ e.toLower, "fx_l_" ++ e.toLower, h, none⟩

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
      pull || withInV env k f || withInV env k W
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

/-- The plain calls of `V` that perform no effect, lifted (`liftCalls`), in the order its
evaluation runs them in; an effectful call stays, its arguments' plain calls lifted. -/
def liftPlain (cx : Cx) : Nat → Val → StateT (List Bind) EM Val
  | 0, V => pure V
  | k + 1, V => match V with
    | .app sp f W =>
      match f with
      | .sugar .. | .app _ (.sugar ..) _ => do pure (.app sp f (← liftPlain cx k W))
      | _ =>
        if !(cx.needV V).isEmpty || cx.ctlV V then do pure (.app sp f (← liftPlain cx k W))
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
          let used := cx.need g.row
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
    if !needs && !unhandled && !ret && !withInV cx.env fuel V then return ([], V)
    let (V, pre) ← if needs then (liftPlain cx fuel V).run [] else pure (V, [])
    let (bs, V') ← goV n cx cs V
    pure (pre ++ bs, V')

/-- `trV` below the lifting of plain calls. -/
def goV : Nat → Cx → List Cap → Val → EM (List Bind × Val)
  | 0, _, _, V => throw ⟨V.span, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, V => match V with
    | .app sp (.app sp₂ (.sugar ksp (.handle h l As)) P) (.thunkv tsp (.lam lsp b A M)) =>
      match cx.env.handler? h, cx.env.chandler? h with
      | some hs, _ => withBlk k cx cs sp sp₂ ksp hs l P tsp lsp b A M
      | none, some ch => withCtl k cx cs sp ksp ch As P M
      | none, none => throw ⟨ksp, s!"no handler `{h}` is declared before this `with`"⟩
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
        -- An argument at a stored generator's parameter: the stored generator of the call.
        let (bP, W) ← pullArgsV k cx cs x W
        let (b, V') ← match cx.env.op? x, cx.env.fn? x with
          | some o, _ => if cx.env.answering o.eff then opCall k cx cs sp x o W else ctlCall k cx cs sp x o W
          | none, some g => fnCall k cx cs sp f x g W
          | none, none => plainApp k cx cs sp f W
        pure (bP ++ b, V')
      | none => plainApp k cx cs sp f W
    | .var sp x => do
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

/-- `g(W)` of a member `g` of the recursive group whose step is being elaborated (SPEC §20): the
group's `rec` operation, `perform[m.0] (self', inj_j W)` with the self-reference `self'`, or the
exhaustion effect's operation when the budget is spent (`self` is `inl ()`). Bound before the value
it is in. -/
def selfCall : Nat → Cx → List Cap → Span → RSelf → String → Nat → Val → EM (List Bind × Val)
  | 0, _, _, sp, _, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, rs, x, j, W => do
    -- A call of itself inside a handler of an effect its row performs: each level would need a
    -- copy whose sites are the level's own, without end (decision 57).
    for (e, n) in rs.served do
      if let some s := cx.siteOf e then
        if s.n != n then
          throw ⟨sp, s!"`{x}` calls itself inside a handler of `{e}`, an effect its recursion " ++
            s!"performs: each level's `{e}` would go to the level's own handler, a site per level " ++
            "without end (recursion through a site, decision 57; generative labels, #173)"⟩
    let (b, W') ← goV k cx cs W
    let r ← fresh "fx_v"
    let u ← fresh "fx_u"
    let g ← fresh "fx_g"
    report sp "call" (s!"{x} → perform[{rs.m}.0], the group's `rec`; at the end of the budget " ++
      s!"abort[{rs.e}.0]")
    let call : Comp := .case sp (.var sp rs.self) ⟨u, sp⟩
      (.ascribe sp (.abort sp rs.e 0 (.unit sp)) rs.C) ⟨g, sp⟩
      (.perform sp rs.m 0 (.pair sp (.var sp g)
        (.ascribe sp (injAt sp j rs.members.length W') rs.A)))
    let bind : Bind := fun N => pure (.bind sp ⟨r, sp⟩ none call N false)
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
    let used := cx.needIn g.row
    if used.isEmpty && (cx.ctl g.row).isEmpty then return ← plainApp k cx cs sp f W
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
    let cap : Cap := ⟨hs.eff, b.name, l, hs, none⟩
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
def withCtl : Nat → Cx → List Cap → Span → Span → CHandler → List VTy → Val → Comp →
    EM (List Bind × Val)
  | 0, _, _, sp, _, _, _, _, _ => throw ⟨sp, "internal error: a value nested too deeply"⟩
  | k + 1, cx, cs, sp, ksp, ch, As, P, M => do
    let tps := ch.tps.map (·.name)
    let e := ch.eff.name
    if M.boundNames.contains "io_bt" then
      throw ⟨ksp, s!"the body of `with {ch.name.name}` assigns a `let mut` variable declared " ++
        "outside it, or lends a place declared outside it: a control handler's body may be " ++
        "abandoned, and does not hand them back; bind what the block answers instead"⟩
    -- The capabilities the body uses are reborrowed for it, each at a lifetime of its own, so that
    -- they come back when the body is abandoned.
    let mut csM : List Cap := []
    for c in cx.needC M do
      if c.thr.isSome then
        throw ⟨ksp, s!"the body of `with {ch.name.name}` performs `{c.eff}` of an enclosing `for`, " ++
          "which threads its variables through the operation: a control handler's body may be " ++
          "abandoned, and does not hand them back; not provided"⟩
      csM := csM ++ [{ c with life := ← fresh "fx_rl" }]
    -- Written type arguments, in the order of the handler's type parameters.
    if As.length > tps.length then
      throw ⟨ksp, s!"`{ch.name.name}` takes {tps.length} type argument(s)"⟩
    let mut σ : TySubst := tps.zip As
    -- The handled effect's type arguments from what the body performs.
    let n ← freshSite
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
    -- The clauses run outside the handler: their operations go to the sites of the handler's row.
    let cxH : Cx := { env := cx.env, caps := [], sites := outer }
    let some eff := cx.env.eff? e | throw ⟨ksp, s!"internal error: the effect `{e}`"⟩
    let (rx, rA, rM) := ch.ret
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
      let body ← trC k cxH [] false (c.body.subst σ)
      let csp := c.name.span
      let p ← fresh "fx_p"
      let body ← if abortive then bindParams csp p c.params body else do
        let xs := c.params.dropLast
        let kv := c.params.getLast!
        let q ← fresh "fx_q"
        pure (.letPair csp ⟨q, csp⟩ kv (.var csp p) (← bindParams csp q xs body))
      cls := cls ++ [.thunkv csp (.lam csp ⟨p, csp⟩ (holeTy csp) body)]
    for c in ch.clauses do
      unless eff.ops.any (·.name.name == c.name.name) do
        throw ⟨c.name.span, s!"`{c.name.name}` is not an operation of `{e}`"⟩
    let rest := tps.filter fun x => (σ.lookup x).isNone
    let info : HInfo := ⟨ch.name.name, n, ents, rest, σ,
      ch.params.map fun (x, A) => (x.name, A.subst σ), rA.subst σ, ch.res.subst σ⟩
    let (bsP, P') ← goV k cx cs P
    let clsV := cls.foldr (fun c t => Val.pair sp c t) (.unit sp)
    let hnd : Val := .app sp (.app sp (.app sp (.app sp (.sugar ksp (.hndCtl info)) P')
      (.thunkv sp (.lam sp rx rA rM'))) clsV) (.thunk sp M')
    let r ← fresh "fx_v"
    if csM.isEmpty then
      let bind : Bind := fun N => pure (.bind sp ⟨r, sp⟩ none (.ret sp hnd) N false)
      return (bsP ++ [bind], .var sp r)
    -- `borrow mut c { 'l, c -> HND }` for each capability `c`, innermost last; each block hands
    -- the capability back beside the result.
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
    pure (bsP ++ [bind], .var sp r)

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

/-- The copy of `g` for what serves its effects at a call in `cx`, made once. -/
def copyFor : Nat → Cx → Span → String → FSig → EM String
  | 0, _, sp, _, _ => throw ⟨sp, "internal error: copies nested too deeply"⟩
  | k + 1, cx, sp, x, g => do
    let mut hs : List HSig := []
    let mut ss : List Site := []
    let mut keys : List String := []
    for i in g.row do
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
      unless hs.isEmpty do
        throw ⟨sp, s!"`{x}` is recursive and uses the capability of `{(hs.head?.map (·.eff)).getD "?"}`: not provided"⟩
      return ← groupCopy k cx.env sp gn ss keys x
    copyOf k cx.env sp g hs ss (copyName x keys)

/-- The copy of the recursive group `gn` for the sites `ss` (keys `keys`), made once (SPEC §20):
its step and a driver per member. The step `gn__step__…` takes the self-reference and the argument
of a member, tagged by the member, and runs that member's body under a handler of the group's
`rec` site, whose clause calls the self-reference and resumes with its answer (or cancels the
continuation when the call unwinds). A member's copy is `bounded_fix` of the step at the budget
`recBudget`. Answers the copy of `x`. -/
def groupCopy : Nat → Env → Span → String → List Site → List String → String → EM String
  | 0, _, sp, _, _, _, _ => throw ⟨sp, "internal error: copies nested too deeply"⟩
  | k + 1, env, sp, gn, ss, keys, x => do
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
    let m ← freshSite
    let ss := ss.map fun s => { s with sp := gsp, what := "the caller" }
    let rowR := env.rowOf ss
    let A := sumTys gsp (G.members.map (·.2.P))
    let B := G.B
    let C : CTy := .eff gsp rowR B
    let selfFn : VTy := .bang gsp (.thunk gsp (.arr gsp A C))
    let selfT : VTy := .sum gsp (.unit gsp) selfFn
    let self := "fx_self"
    let rs : RSelf := ⟨G.members.map (·.1), m, e.n, self,
      .eff gsp (.cons m 0 .aff (.tensor gsp selfFn A) B rowR) B, A, ss.map fun s => (s.eff, s.n)⟩
    let cx : Cx := { env, caps := [], sites := ss, recSelf := some rs }
    -- The members' bodies, dispatched on the member's tag.
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
    let handled ← dispatch (G.members.length + 1) fa bodies
    -- The clause: `rec((g, a), k) = b <- force g a unwind (k.2); k.1 b`.
    let q ← fresh "fx_rcq"; let w ← fresh "fx_rcw"; let kk ← fresh "fx_rck"
    let gv ← fresh "fx_rcg"; let av ← fresh "fx_rca"; let gf ← fresh "fx_rcf"; let bv ← fresh "fx_rcb"
    let clause : Comp :=
      .letPair gsp ⟨w, gsp⟩ ⟨kk, gsp⟩ (.var gsp q)
        (.letPair gsp ⟨gv, gsp⟩ ⟨av, gsp⟩ (.var gsp w)
          (.bind gsp ⟨gf, gsp⟩ none (.ret gsp (.unbang gsp (.var gsp gv)))
            (.unwind gsp ⟨bv, gsp⟩ none (.app gsp (.force gsp ⟨gf, gsp⟩) ⟨av, gsp⟩)
              (.proj gsp false (.force gsp ⟨kk, gsp⟩))
              (.app gsp (.proj gsp true (.force gsp ⟨kk, gsp⟩)) ⟨bv, gsp⟩)) false))
    let rx ← fresh "fx_rr"
    let info : HInfo := ⟨"rec", m, [(.aff, .tensor gsp selfFn A, B)], [], [], [], B, B⟩
    let hnd : Val := .app gsp (.app gsp (.app gsp (.app gsp (.sugar gsp (.hndCtl info)) (.unit gsp))
      (.thunkv gsp (.lam gsp ⟨rx, gsp⟩ B (.ret gsp (.var gsp rx)))))
      (.pair gsp (.thunkv gsp (.lam gsp ⟨q, gsp⟩ (holeTy gsp) clause)) (.unit gsp)))
      (.thunk gsp handled)
    let pp ← fresh "fx_rsp"
    let step : FnParts := ⟨true, [], .tensor gsp selfT A, B, ⟨pp, gsp⟩,
      .letPair gsp ⟨self, gsp⟩ ⟨fa, gsp⟩ (.var gsp pp) (.ret gsp hnd)⟩
    let (sA, sV) := step.build gsp rowR
    report gsp "lowering" (s!"recursive group {", ".intercalate (G.members.map (·.1))}: the step " ++
      s!"`{stepName}` under a handler of its `rec`, the static name {m}; each member's copy is " ++
      s!"bounded_fix of it at the budget {recBudget}, the exhaustion effect at the site {e.n}")
    modify fun s => { s with made := s.made.push (stepName, .def_ gsp ⟨stepName, gsp⟩ [] sA sV .none) }
    -- Each member's copy: `bounded_fix (step, (budget, inj_j p))`.
    for ((mn, f), j) in G.members.zipIdx do
      let p ← fresh "fx_rp"
      let fb ← fresh "fx_rbf"
      let fa' ← fresh "fx_rba"
      let arg : Val := .pair gsp (.var gsp stepName)
        (.pair gsp (.const gsp (.lit (.i32 (UInt32.ofNat recBudget))))
          (.ascribe gsp (injAt gsp j G.members.length (.var gsp p)) A))
      let body : Comp :=
        .bind gsp ⟨fb, gsp⟩ none (.ret gsp (.unbang gsp (.const gsp (.boundedFix A C))))
          (.bind gsp ⟨fa', gsp⟩ none (.ret gsp arg) (.app gsp (.force gsp ⟨fb, gsp⟩) ⟨fa', gsp⟩) false)
          false
      let drv : FnParts := ⟨true, [], f.P, B, ⟨p, gsp⟩, body⟩
      let (dA, dV) := drv.build gsp rowR
      let dn := copyName mn keys
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
        (hs.find? (·.eff == i.eff)).map fun h => ⟨i.eff, "fx_c_" ++ i.eff.toLower, "fx_l_" ++ i.eff.toLower, h, none⟩
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
  let cap : Cap := ⟨h.eff, cv, l, h, none⟩
  let P := tupleTy sp (o.params.map (·.2))
  let f : FnParts := ⟨true, [(⟨l, sp⟩, .top sp)], capsTy sp [cap] P, capsTy sp [cap] o.res, ⟨pp, sp⟩,
    .letPair sp ⟨cv, sp⟩ ⟨p, sp⟩ (.var sp pp) inner⟩
  let (A, V) := f.build sp
  pure (.def_ sp ⟨clauseName h.name c.name.name, sp⟩ [] A V .none)

/-! ### Programs -/

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

/-- The mark of a definition without its written row, and the row. -/
def splitRow : Mark → List (Ident × List VTy) × Mark
  | .row es m => (es, m)
  | m => ([], m)

/-- Anything for this pass to do: an effect, a handler or a written row. -/
def hasEffects (ds : List Decl) : Bool :=
  ds.any fun
    | .effect .. | .handler .. | .chandler .. => true
    | .def_ _ _ _ _ _ mk => (match mk with | .row .. => true | _ => false)
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
      throw ⟨n.span, s!"`{n.name}` is recursive and its body has a `while` or a `loop`: a loop " ++
        "inside a recursion is not provided; write the loop as a recursion, or in a function of " ++
        "its own"⟩
    if let some (_, B) := parts.head? then
      unless B.T.strip == f.T.strip do
        throw ⟨n.span, s!"`{n.name}` is in a recursive group with `{(parts.head?.map (·.1)).getD "?"}`, and its result " ++
          s!"type differs from theirs: a group's members answer one type"⟩
    let (written, _) := splitRow mk
    for i in rowV env fuel V do
      unless written.isEmpty || written.any (·.1.name == i.eff) do
        throw ⟨n.span, s!"`{n.name}` performs `{i.eff}`, which its written row does not list"⟩
      let i ← match written.find? (·.1.name == i.eff), i.args with
        | some (_, As), _ => pure ⟨i.eff, some As⟩
        | none, some _ => pure i
        | none, none => throw ⟨n.span, s!"`{n.name}` performs `{i.eff}`, and its type arguments " ++
            s!"are not determined: write them, `with {i.eff}[…]`"⟩
      if env.answering i.eff then
        throw ⟨n.span, s!"`{n.name}` is recursive and uses the capability of `{i.eff}`: not provided"⟩
      if let some e := env.eff? i.eff then
        if e.ops.any (!·.abortive) then
          throw ⟨n.span, s!"`{n.name}` is recursive and performs `{i.eff}`, whose operations " ++
            "resume: a recursion's continuation is cancelled at an abortive row only (not provided)"⟩
      row := addInst row i
    unless written.isEmpty || written.any (·.1.name == exh.name) do
      throw ⟨n.span, s!"`{n.name}` is recursive, so it performs `{exh.name}` when its depth runs out, " ++
        "which its written row does not list"⟩
    parts := parts ++ [(n.name, f)]
  row := addInst row ⟨exh.name, some []⟩
  let some (_, f₀) := parts.head? | throw ⟨sp₀, "internal error: an empty group"⟩
  let G : RGroup := ⟨n₀.name, parts, f₀.T, sp₀⟩
  report sp₀ "rec" (s!"{", ".intercalate (parts.map (·.1))}: a recursive group; its calls of itself " ++
    s!"are its `rec`, driven by bounded_fix at the budget {recBudget}; " ++
    s!"row {", ".intercalate (row.map (·.eff))}")
  let mut env := { env with groups := env.groups ++ [G] }
  for ((x, _), (sp, n, A, V, mk)) in parts.zip ms do
    env := { env with fns := env.fns ++ [{ name := x, row, decl := .def_ sp n [] A V mk,
                                             group := some (G.name, (parts.map (·.1)).idxOf x) }] }
  pure env

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
  if !hasEffects ds && groups.isEmpty then return (ds, [])
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
        env := { env with sigs := (n.name, A) :: env.sigs }
        modify fun s => { s with quiet := lib.contains n.name }
        if let some G := groups.find? (·.contains n.name) then
          -- A member of a recursive group: the group is declared at its last member.
          if G.getLast? == some n.name then
            env ← defineGroup env (ds.filterMap fun
              | .def_ sp' m _ A' V' mk' => if G.contains m.name then some (sp', m, A', V', mk') else none
              | _ => none)
          continue
        let (written, mk) := splitRow mk
        let row := rowV env fuel V
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
        else
          let before := (← get).made.size
          let (bs, V') ← trV fuel { env, caps := [] } [] V
          unless bs.isEmpty do throw ⟨V.span, "internal error: a definition's value was taken apart"⟩
          out := out ++ ((← get).made.extract before).map (·.2)
          out := out.push (.def_ sp n ps A V' mk)
      | .main sp C M =>
        modify fun s => { s with quiet := false }
        let before := (← get).made.size
        let M' ← trC fuel { env, caps := [] } [] false M
        out := out ++ ((← get).made.extract before).map (·.2)
        out := out.push (.main sp C M')
      | d => out := out.push d
    pure out.toList
  match go.run {} with
  | .ok (ds, st) => pure (ds, st.reports.toList)
  | .error e => throw e

end Frontend.Elab.Effects

import Std.Data.HashMap
import Backend2.Syntax
import Backend2.Debug
import Frontend.Check.Kinds
import Frontend.Check.Cells

/-!
# Backend2 — closure conversion of the typed term  `[spec §3, §10]`

`Checked.t`, the typed term the checker returns, to the LIR (`Backend2/Syntax.lean`). The
conversion follows the derivation node by node:

- **Contexts.** The conversion carries the node's context: at each slot, the LIR variable that
  holds it when it is live, `none` when it is dead. A binder pushes a live slot (its type is the
  node's binder type) or a dead one, as the node's rule does (`TExpr.children`'s scopes).
- **Ownership from the masks.** At a split (`TExpr.masks?`) the masks say which slots each part
  uses: a slot both use is copied (`Ctx.SplitP`'s `dup`, a persistent slot), a slot one uses
  moves to it, a live slot neither uses is dropped there (`Ctx.DeadP`'s `drop`, persistent).
  At a leaf every live slot but the one it reads is dropped (`Ctx.SoloP`, `Ctx.DeadP`). No copy
  and no drop is inferred from occurrences.
- **Closures.** A node that makes a λ-value (`lam`, `thunkF`, `allI`, `withI`, …) is a closure of a
  code of its own, capturing the live slots of its context. A thunk of a λ-value, `ret`,
  dereliction, the lifetime box and the lifetime coercions are the value they are over.
- **Constants** are read from their nodes: applied to their arguments (a spine of `lolliE`
  nodes) each is its operation (`expand`); used as a value it is a closure of a code that applies
  it.
- **Specialisation.** A `use` node's body is converted once per key (`useKey`): its value's
  term is kept as a template over the slots it reads, and each later use instantiates it, so the
  codes it makes are made once.
- **Derived nodes** are read: `divLit` is its division with no error arm, `litFn` a literal's
  table in the program's data, `walk` a counted walk whose reads are in range, `dtor` the drop of
  its type.
- **Effects** are erased by handler law where the checked facts license it (SPEC §47); at the
  machine operations, the stored-continuation sites, a computation answers its outcome and is
  converted as a state machine with its continuation (`convK`), and a `handle` node is a drive
  (`convDrive`, SPEC §49).
-/

namespace Backend2
open BoCa BoCa.Fig16.LogRel.Core BoCa.Fig16.LogRel.Core.Check

/-- A slot of the context: its variable when live. -/
abbrev Ctx := List (Option Var)

/-- A `use` body converted once: the term of its value, over the variables of the slots it
reads (by slot), and its type. -/
structure Template where
  slots : List (Nat × Var)
  tm : Tm
  deriving Inhabited

/-- How an extern of `main` is implemented (SPEC §11, §34), in declaration order. -/
inductive Ext where
  /-- A capability's cell, holding the stream's descriptor: a word of the program's data. -/
  | cap (fd : Nat)
  /-- The clock's cell (SPEC §34). -/
  | clock
  /-- An operation. -/
  | io (k : IOKind)
  deriving Inhabited, BEq

/-- The payload of a row: its abortive operations, each key once with its argument's type, in the
row's order (`Types.payOf`'s list).  `[spec §47]` -/
abbrev Pay := List ((UInt32 × UInt32) × LTy)

/-- An operation's key: its name and index. -/
abbrev Key := UInt32 × UInt32

/-- **The outcome of a computation** at a row with machine operations (`Types.outcomeTy`,
SPEC §49): its type, the value's type `r`, the abortive payload `pay` and the machine operations
`ms` (key, argument, answer), each in the row's order. -/
structure OutInfo where
  ty : LTy
  r : LTy
  pay : Pay
  /-- Each machine operation's key, argument, answer, and its cancel row's payload (`none` at
  `⊤`). -/
  ms : List (Key × LTy × LTy × Option Pay)
  /-- The machine operations at the qualifier `unr`, whose continuation may be copied. -/
  unrs : List Key := []
  deriving Inhabited

/-- **A frame of a machine's continuation** (SPEC §49): what is done, inside one machine, with the
value of the computation being converted, up to the machine's own answer. Each frame owns the
next `own` of the continuation's arguments (the variables of its context). -/
inductive Frame where
  /-- `x <- [·]; N`: `N` is the join `fn`, on every argument and the value. -/
  | letF (fn : Nat) (own : Nat)
  /-- `[·] then x. N unwind D`: `N` the join `fnN`; `D` the finaliser `fnD`, on the frame's own
  arguments, answering at its row's payload `pd`. -/
  | thenF (fnN fnD : Nat) (own : Nat) (pd : Pay)
  /-- Arguments dropped when the machine is cancelled; a forwarding drive's handler values. -/
  | dropF (own : Nat)
  /-- **The level's state cell** (SPEC §50), the bottom frame of a machine whose state is a cell
  passed on (`Mach.cell`): its one argument is `inl ()` until the machine first suspends, then
  `inr c`, the cell, which each later suspension writes in place and the machine's answer
  releases. -/
  | cellF
  /-- **The level's frame on the task stack** (SPEC §52), the bottom frame of a stack machine
  (`Mach.stack`): its arguments are the frame's cell, reserved when the level starts, and the
  stack's depth there. The level's answer, abort or cancel pops it. -/
  | stackF
  /-- A stored site's stack (SPEC §52), held by a forwarding point: freed when it is cancelled. -/
  | stackH
  deriving Inhabited, BEq

def Frame.own : Frame → Nat
  | .letF _ k | .thenF _ _ k _ | .dropF k => k
  | .cellF | .stackH => 1
  | .stackF => 2

abbrev Kont := List Frame

/-- **A resumption point** of a machine (SPEC §49): the operation it suspends at; at a call
point the callee's suspended computation's type `kTy`, the callee's abortive payload `cPay` and the
step function (`step`, on the arguments and the callee's outcome); the arguments' types; the
continuation; the function `mk` that builds the machine's suspended computation from the callee's
and the arguments. -/
structure MPoint where
  op : Key
  kTy : Option LTy
  cPay : Option Pay
  argTys : List LTy
  step : Option Nat
  kont : Kont
  mkFn : Nat
  /-- At a call point: the callee's outcome, and whether its step is the machine's own (a step
  function made by `pointK`, `site` its index) rather than a drive's. -/
  callee : Option OutInfo := none
  site : Nat := 0
  inline : Bool := false
  /-- At a call point: the step's parameter that receives the callee's outcome (the layouts'
  classes of its suspended computations decide a stack machine, SPEC §52). -/
  outVar : Option Var := none
  /-- At a stored site's forwarding point (SPEC §52): the index among its arguments of the site's
  stack, which is made current around the resume and cancel of the callee's `k`. -/
  swapAt : Option Nat := none
  deriving Inhabited

/-- A machine being converted: its outcome and its resumption points. -/
structure Mach where
  info : OutInfo
  points : Array MPoint := #[]
  /-- The calls in tail position at its own outcome, each a function on the callee's outcome:
  the identity when the machine has no other point (a wrapper passes its callee's outcome on),
  else the step of a point. -/
  tails : Array (Nat × OutInfo) := #[]
  /-- The machine's number among the machines begun, in conversion order. -/
  start : Nat := 0
  /-- Its body takes its continuation (`withMachineK`), so its state cell can be passed on. -/
  threadable : Bool := false
  /-- With its state cell passed on (`Frame.cellF`, SPEC §50): the state's type at its one
  operation. -/
  cell : Option LTy := none
  /-- **A stack machine** (SPEC §52): its levels' frames on the task stack, the frame's state type. -/
  stack : Option LTy := none
  deriving Inhabited

/-- A closure a stored-continuation site's clause builds, a variant of its task body's code
(SPEC §49): its own code, the function that builds the variant, and its captured values' types. -/
structure SiteVar where
  code : Nat
  mkFn : Nat
  envTys : List LTy
  deriving Inhabited

structure CState where
  next : Nat := 0
  ty : Std.HashMap Var LTy := {}
  fns : Array Fn := #[]
  codes : Array Code := #[]
  uses : Std.HashMap String Template := {}
  data : Array UInt8 := #[]
  /-- The literal tables' codes, with their bytes' offset and length in the data. -/
  lits : Option Nat := none
  /-- What the conversion read of the typed term, by rule and fact (`bcc lir --census`). -/
  reads : Std.HashMap String Nat := {}
  /-- The static cells in the data after the literals, each with its width class (none: one word):
  the capabilities' cells and the stack register. -/
  statics : Array (List LTy) := #[]
  /-- **The width classes** (`Checked.classAt`, SPEC §57): for each type a cell is allocated at
  (lifetimes erased), every type its cells may hold, at LIR types. -/
  classes : List (VTy × List LTy) := []
  /-- **The lend scopes** (`TExpr.lendScope`, SPEC §57): the scopes numbered so far; the scope whose
  `lendCell` is converted next, when its `rel` holds; the scope whose owner is bound next (by the
  `letpair` that takes its pair apart); and each owner bound, its variable and scope. -/
  scopes : Nat := 0
  scopeCell : Option Nat := none
  scopeOwner : Option Nat := none
  owners : Std.HashMap Var Nat := {}
  /-- While a `use` template is renamed (`renameTm`): each of its scopes' number in the copy. -/
  scopeCopy : Std.HashMap Nat Nat := {}
  /-- The `array_new` converted next is a literal's view's (`TExpr.litView`, SPEC §57). -/
  litPending : Bool := false
  /-- Record the type formers the layouts are read from (`readFormers`). -/
  census : Bool := false
  /-- The destructors of `μ` types, generated once per type (`genDtor`). -/
  dtors : Std.HashMap String Nat := {}
  /-- The variables bound to `unfold step` (a `bind` whose bound computation is an `unfoldStep`
  node, SPEC §57), and their copies and captures: the `f` a `nuEta` node may call (SPEC §45). -/
  unfolds : Std.HashSet Var := {}
  /-- Inside a walk whose step reads its view at its index (`TExpr.walk`'s `read`, SPEC §46). -/
  walkRead : Bool := false
  /-- Converting a walk's read (`TExpr.walkGet`) inside such a walk: its index is in range. -/
  inRange : Bool := false
  /-- **The direct calls the checked facts license**  `[spec §47]`: at each static name, for each
  of its operations, whether every `handle` node of the name classifies its clause `tail`, its
  names meet condition 2 at the program's flow record (`cond2B`, `Checked.flows`), and the nodes
  hold one closed clause for it (`Backend2/Driver.lean`, `directFacts`). -/
  direct : Std.HashMap UInt32 (List Bool) := {}
  /-- The function of each directly called clause, by its operation, with the payload of its
  handler's outer row: the clause's work, its resumes removed (`TailResumesAt`). -/
  works : Std.HashMap (UInt32 × Nat) (Nat × List ((UInt32 × UInt32) × LTy) × Option OutInfo) := {}
  /-- **The `[handle-last]` works called where their operation is performed** (SPEC §64,
  `Backend2/Driver.lean`, `lastFacts`), by operation: the work's function, the payload of its row
  `Σ_W` and the exit's argument's type. -/
  lasts : Std.HashMap (UInt32 × Nat) (Nat × List ((UInt32 × UInt32) × LTy) × LTy) := {}
  /-- `main`'s I/O externs by its context slot, each with its type: the persistent closures a
  rule-written handler's code may read, made again where that code runs (`ioCtx`). -/
  mainIO : Array (Option (IOKind × VTy)) := #[]
  /-- The `handle`, `perform` and `raise` nodes erased (`bcc lir --erasure`). -/
  erased : Std.HashMap String Nat := {}
  /-- **The program's machine operations** (SPEC §49, `Backend2/Driver.lean`, `machineOps`). -/
  mach : MachSet := {}
  /-- The machines being converted, innermost first. -/
  machs : List Mach := []
  /-- The machines converted, each with its suspended computations' codes by operation. -/
  done : Array (Mach × List (Key × Nat)) := #[]
  /-- The calls in tail position made points: each one's function, its parameter (the callee's
  outcome), the callee's outcome and its machine (an index of `done`). -/
  tailSites : Array (Nat × Var × OutInfo × Nat) := #[]
  /-- While a stored-continuation site's clauses are converted: the closure types of its answer
  and its task body's key (SPEC §49). -/
  siteMerge : Option (List LTy × String) := none
  /-- The closures of each task body's code, by the body's key and the closure type. -/
  merges : Std.HashMap String (Array SiteVar) := {}
  merged : Array String := #[]
  /-- The stored-continuation sites converted inside the closure body being converted: their
  answer's closure types and task bodies' keys. -/
  sitesIn : List (List LTy × String) := []
  /-- The machines begun so far (`Mach.start`). -/
  begun : Nat := 0
  /-- **The machines whose state cell is passed on** (SPEC §50), by `Mach.start`, with their state's
  type: read off a first conversion's layouts (`Backend2/Driver.lean`, `lirOf`). -/
  threaded : Std.HashMap Nat LTy := {}
  /-- **The stack machines** (SPEC §52), by `Mach.start`, with their frame's state type: read off a
  first conversion's machines and layouts (`Backend2/Driver.lean`, `lirOf`). -/
  stacked : Std.HashMap Nat LTy := {}
  /-- The static word that holds the current stack, once a stack machine or a site uses it. -/
  stackReg : Option Nat := none
  /-- The callees' suspended computations a stack machine's points drop (`genStackMach`,
  `Prog.stackKs`). -/
  stackKs : Std.HashSet Var := {}
  /-- **The runtime answers every tick**  `[spec §62]`: `main` is a loop the runtime drives (SPEC
  §11), its value `reify` of its body, and that `reify` is the typed term's one handler of `Div`
  (no other `reify` and no `div_fuel` node: `Backend2/Driver.lean`, `divRuntime`). A tick is then
  answered *next*, where it is performed. -/
  divRt : Bool := false

abbrev CM := StateT CState (Except String)

def fresh (t : LTy) : CM Var := modifyGet fun s =>
  (s.next, { s with next := s.next + 1, ty := s.ty.insert s.next t })

def tyOf (x : Var) : CM LTy := do
  match (← get).ty[x]? with
  | some t => pure t
  | none => throw s!"LIR: variable {x} has no type"

def freshLike (x : Var) : CM Var := do fresh (← tyOf x)

/-- `freshLike`, the variable's mark (`unfolds`) kept. -/
def freshMarked (x : Var) : CM Var := do
  let x' ← freshLike x
  if (← get).unfolds.contains x then modify fun st => { st with unfolds := st.unfolds.insert x' }
  return x'

/-- Record that the conversion read a fact of the typed term. -/
def readFact (k : String) : CM Unit :=
  modify fun s => { s with reads := s.reads.insert k (s.reads.getD k 0 + 1) }

/-- The width class of a cell allocated at `A` (`Checked.classAt`, SPEC §57); none at a type the
checker allocates no cell at. -/
def classOf (A : VTy) : CM (List LTy) := do
  let A := A.eraseLife
  return (((← get).classes.find? (·.1 == A)).map (·.2)).getD []

/-- A new lend scope: its number. -/
def newScope : CM Nat := modifyGet fun s => (s.scopes, { s with scopes := s.scopes + 1 })

/-- The variable `x` is bound to the pair's first component a `letpair` takes apart: the owner of
the scope whose lend was converted last (`scopeOwner`), if any. -/
def markOwner (x : Var) : CM Unit := do
  if let some s := (← get).scopeOwner then
    modify fun st => { st with scopeOwner := none, owners := st.owners.insert x s }

def lift (r : Except String α) : CM α := match r with
  | .ok a => pure a
  | .error e => throw e

mutual
/-- The formers of a value type, each once. -/
def formersV (acc : List String) : VTy → List String
  | .tensor A B => formersV (formersV ("V.tensor" :: acc) A) B
  | .sum A B => formersV (formersV ("V.sum" :: acc) A) B
  | .thunk C => formersC ("V.thunk" :: acc) C
  | .ref A => formersV ("V.ref" :: acc) A
  | .imm _ A => formersV ("V.imm" :: acc) A
  | .mut _ A => formersV ("V.mut" :: acc) A
  | .box _ A => formersV ("V.box" :: acc) A
  | .bang A => formersV ("V.bang" :: acc) A
  | .mu A => formersV ("V.mu" :: acc) A
  | .fam A => formersV ("V.fam" :: acc) A
  | .unit => "V.unit" :: acc
  | .zero => "V.zero" :: acc
  | .unk => "V.unk" :: acc
  | .tvar _ => "V.tvar" :: acc
  | .int _ => "V.int" :: acc
  | .opq _ => "V.opq" :: acc
/-- The formers of a computation type, each once. -/
def formersC (acc : List String) : CTy → List String
  | .ret A => formersV ("C.ret" :: acc) A
  | .arr A C => formersC (formersV ("C.arr" :: acc) A) C
  | .amp C D => formersC (formersC ("C.amp" :: acc) C) D
  | .all _ _ C => formersC ("C.all" :: acc) C
  | .nu C => formersC ("C.nu" :: acc) C
  | .eff _ _ _ A B fin _ C => formersC (formersC (formersV (formersV ("C.eff" :: acc) A) B) fin) C
  | .top => "C.top" :: acc
end

/-- Record the formers a layout is read from (in the census's run). -/
def readFormers (fs : List String) : CM Unit := do
  if (← get).census then
    for f in fs.eraseDups do readFact s!"{f}:layout"

def vty (A : VTy) : CM LTy := do readFormers (formersV [] A); lift (ofV (← get).mach A)
def cty (C : CTy) : CM LCTy := do readFormers (formersC [] C); lift (ofC (← get).mach C)

/-- The type of a node's value: a value type's, `F A`'s `A`, and otherwise the closure the
computation's λ-value is. -/
def repJ (j : Jdg) : CM LTy := do
  match j with
  | .val A => vty A
  | .comp (.ret A) => vty A
  | .comp C@(.eff ..) => do
    -- `F_Σ R`'s value: `R`, or `R ⊕ P` (SPEC §47).
    match ← cty C with
    | .ret a => pure a
    | k => throw s!"LIR: a row's computation type at {k}"
  | .comp .top => pure .unit
  | .comp C => return .thunk (← cty C)

/-- `ls` is the value of a term: bind it to a fresh variable of type `t` unless it is a
variable already. -/
def bindTm (e : Tm) (t : LTy) (k : Var → CM Tm) : CM Tm := do
  match e with
  | .var x => k x
  | _ =>
    let x ← fresh t
    return .letv x e (← k x)

def drops (xs : List Var) (b : Tm) : Tm := xs.foldr (fun x b => .drop x b) b

def live (ctx : Ctx) : List Var := ctx.filterMap id

/-- At a leaf that reads the slot `keep` (or none): every other live slot dropped. -/
def leaf (ctx : Ctx) (keep : Option Nat) (b : Tm) : Tm :=
  let others := (ctx.zipIdx.filter fun (_, i) => some i != keep).filterMap (·.1)
  drops others b

/-- The context at a split, by its masks: the parts' contexts and the copies and drops made at the
split. -/
def splitCtx (ctx : Ctx) (m : Masks) (rule : String := "?") : CM ((Tm → Tm) × Ctx × Ctx) := do
  if m.ms.length != ctx.length then
    throw s!"LIR: masks of {m.ms.length} slots at a context of {ctx.length}"
  let mut pre : List (Tm → Tm) := []
  let mut c₁ : Array (Option Var) := #[]
  let mut c₂ : Array (Option Var) := #[]
  for (s, (a, b)) in ctx.zip m.ms do
    match s, a, b with
    | none, false, false => c₁ := c₁.push none; c₂ := c₂.push none
    | none, _, _ => throw "LIR: a mask uses a dead slot"
    | some x, true, true =>
      let x' ← freshLike x
      if (← get).unfolds.contains x then modify fun st => { st with unfolds := st.unfolds.insert x' }
      pre := (fun t => .copy x x' t) :: pre
      c₁ := c₁.push (some x); c₂ := c₂.push (some x')
    | some x, true, false => c₁ := c₁.push (some x); c₂ := c₂.push none
    | some x, false, true => c₁ := c₁.push none; c₂ := c₂.push (some x)
    | some x, false, false =>
      pre := (fun t => .drop x t) :: pre
      c₁ := c₁.push none; c₂ := c₂.push none
  readFact s!"{rule}:masks"
  return (fun t => pre.foldl (fun t f => f t) t, c₁.toList, c₂.toList)

/-- Register a function. -/
def addFn (f : Fn) : CM Nat := modifyGet fun s => (s.fns.size, { s with fns := s.fns.push f })

/-- Reserve a function's index, to be set by `setFn` (a recursive helper calls itself). -/
def reserveFn (name : String) : CM Nat := addFn { name, params := [], body := .unit, ret := .unit }

def setFn (i : Nat) (f : Fn) : CM Unit := modify fun s => { s with fns := s.fns.set! i f }

def addCode (c : Code) : CM Nat := modifyGet fun s => (s.codes.size, { s with codes := s.codes.push c })

/-- The environment of a closure made in `ctx`: its live slots, and the context its code sees,
each live slot renamed to the code's parameter. -/
def envOf (ctx : Ctx) : CM (List Var × List Var × Ctx) := do
  let mut outer : Array Var := #[]
  let mut inner : Array Var := #[]
  let mut ctx' : Array (Option Var) := #[]
  for s in ctx do
    match s with
    | some x =>
      let x' ← freshLike x
      if (← get).unfolds.contains x then modify fun st => { st with unfolds := st.unfolds.insert x' }
      outer := outer.push x; inner := inner.push x'; ctx' := ctx'.push (some x')
    | none => ctx' := ctx'.push none
  return (outer.toList, inner.toList, ctx'.toList)

/-- A closure's body converted with no site's clauses around it; the stored-continuation sites it
holds are answered with it. -/
def outsideSite (act : CM α) : CM (α × List (List LTy × String)) := do
  let m := (← get).siteMerge
  let outer := (← get).sitesIn
  modify fun s => { s with siteMerge := none, sitesIn := [] }
  let r ← act
  let inner := (← get).sitesIn
  modify fun s => { s with siteMerge := m, sitesIn := outer ++ inner }
  return (r, inner)

/-- **A closure of code `c` over `outer`**: a variant of a task body's code (SPEC §49,
`genMerges`) when it is of a closure type of a stored-continuation site's answer and either a
clause of the site builds it, or its body holds the site (a stored generator before its first
observation). -/
def closOf (c : Nat) (k : LCTy) (outer : List Var) (inner : List (List LTy × String)) : CM Tm := do
  let key? : Option String := match (← get).siteMerge with
    | some (tys, key) => if tys.any (·.sameRep (.thunk k)) then some key else none
    | none => none
  let key? := key?.orElse fun _ =>
    (inner.find? fun (tys, _) => tys.any (·.sameRep (.thunk k))).map (·.2)
  match key? with
  | some key =>
    let g := s!"{key}|{k.unbang}"
    let mk ← reserveFn "task variant"
    let v : SiteVar := { code := c, mkFn := mk, envTys := ← outer.mapM tyOf }
    modify fun s => { s with merges := s.merges.insert g ((s.merges.getD g #[]).push v),
                             merged := if s.merges.contains g then s.merged else s.merged.push g }
    readFact "effHandleV:task body"
    return .call mk outer
  | none => return .clos c outer

/-- A closure of the closure type `k`, made in `ctx`, of a code of one function: `lam` when
`param` gives its argument's type, `unit` otherwise; `body` converts its body at the code's
context (its argument's slot pushed when it has one). -/
def mkClos (name : String) (ctx : Ctx) (k : LCTy) (param : Option LTy) (ret : LTy)
    (body : Ctx → CM Tm) : CM Tm := do
  let (outer, inner, ctx') ← envOf ctx
  let fi ← reserveFn name
  match param with
  | some pt =>
    let p ← fresh pt
    let (b, sites) ← outsideSite (body (some p :: ctx'))
    setFn fi { name, params := inner ++ [p], body := b, ret }
    let c ← addCode { kind := .lam, fns := [fi], ty := k }
    closOf c k outer sites
  | none =>
    let (b, sites) ← outsideSite (body ctx')
    setFn fi { name, params := inner, body := b, ret }
    let c ← addCode { kind := .unit, fns := [fi], ty := k }
    closOf c k outer sites

/-- A closure of a `&`: one function per component over one environment. -/
def mkAmp (name : String) (ctx : Ctx) (k : LCTy) (rets : List LTy)
    (bodies : List (Ctx → CM Tm)) : CM Tm := do
  let (outer, _, _) ← envOf ctx
  let mut fis : Array Nat := #[]
  let mut sites : List (List LTy × String) := []
  for (b, r) in bodies.zip rets do
    let (_, inner, ctx') ← envOf ctx
    let fi ← reserveFn name
    let (t, ss) ← outsideSite (b ctx')
    sites := sites ++ ss
    setFn fi { name, params := inner, body := t, ret := r }
    fis := fis.push fi
  let c ← addCode { kind := .amp, fns := fis.toList, ty := k }
  closOf c k outer sites

/-- The argument and answer of a closure type `A ⊸ F B`, through a `!`. -/
def arrowOf (t : LTy) : CM (LTy × LTy) :=
  match t.peel with
  | .thunk (.arr a (.ret b)) => pure (a, b)
  | _ => throw s!"LIR: not a function type: {t}"

/-- The answer of running a closure of type `t` (through a `!`): its argument's type and its
answer's, for a `lam` code; its answer's for a `unit` one. -/
def answerOf (t : LTy) : CM (Option LTy × LTy) :=
  match t.peel with
  | .thunk k => do
    match k.whnf 8 with
    | .arr a c => return (some a, ← repC c)
    | .ret a => return (none, a)
    | k => throw s!"LIR: a closure of {k} is not called"
  | _ => throw s!"LIR: a call of a non-closure: {t}"
where
  repC : LCTy → CM LTy
    | .ret a => pure a
    | .top => pure .unit
    | k => pure (.thunk k)

/-- Apply the closure `f` to `args` in turn, each call a closure call of the type it has. -/
def applyAll (f : Var) : List Var → CM Tm
  | [] => pure (.var f)
  | [a] => return .app f a
  | a :: as => do
    let (_, r) ← answerOf (← tyOf f)
    bindTm (.app f a) r fun g => applyAll g as

/-! ### Small terms -/

def i32T : LTy := .int .w32
def boolT : LTy := .sum .unit .unit

def lit32 (n : UInt32) (k : Var → CM Tm) : CM Tm := do
  let x ← fresh i32T
  return .letv x (.lit (.i32 n)) (← k x)

/-- `x` copied: `k x x'`. -/
def dup (x : Var) (k : Var → Var → CM Tm) : CM Tm := do
  let x' ← freshLike x
  return .copy x x' (← k x x')

/-- The host operation `op` on the pair `(a, b)`, its answer of type `t`. -/
def bin (op : HostOp) (a b : Var) (t : LTy) (k : Var → CM Tm) : CM Tm := do
  let p ← fresh (.pair (← tyOf a) (← tyOf b))
  let r ← fresh t
  return .letv p (.pair a b) (.letv r (.prim (.host op) [p]) (← k r))

/-- `yes` when `a < b` (unsigned), else `no`; `a` and `b` consumed. -/
def ifLt (a b : Var) (yes no : CM Tm) : CM Tm := do
  let c ← fresh boolT
  let u₁ ← fresh .unit
  let u₂ ← fresh .unit
  return .letv c (.prim .cntLt [a, b]) (.case c u₁ (.drop u₁ (← no)) u₂ (.drop u₂ (← yes)))

def add1 (i : Var) (k : Var → CM Tm) : CM Tm := do
  let j ← fresh i32T
  return .letv j (.prim .cntSucc [i]) (← k j)

def letpairM (p : Var) (k : Var → Var → CM Tm) : CM Tm := do
  match (← tyOf p).peel with
  | .pair a b =>
    let x ← fresh a
    let y ← fresh b
    return .letpair x y p (← k x y)
  | t => throw s!"LIR: letpair of a non-pair: {t}"

def unitThen (b : Tm) : CM Tm := do
  let u ← fresh .unit
  return .letv u b (.drop u .unit)

/-! ### Rows and their payloads  `[spec §47]`

A computation at the row `Σ` answers `R ⊕ P` when `Σ` has abortive operations, `P` the payload of
their arguments (`Backend2/Types.lean`, `payOf`), and `R` otherwise. The payload is read off the
row a node carries; each operation is a summand, at its index among the row's abortive
operations. -/

def rowPay (S : Row) : CM Pay := do
  let mut acc : Pay := []
  let last := (← get).mach.last
  for o in S do
    if acc.any (·.1 == (o.n, o.i)) then continue
    if o.abort then
      acc := acc ++ [((o.n, o.i), ← vty o.A)]
    else if let some t := last[(o.n, o.i)]? then
      -- A `[handle-last]` operation's cancel, a way out to its node (SPEC §64, `cancelSummand`).
      acc := acc ++ [((o.n, o.i), t)]
  return acc

/-- The payload's type: `none` at no operation. -/
def payTy (p : Pay) : Option LTy := payOf p

/-- The value type of a computation answering `a` at the payload `p`. -/
def resTy (a : LTy) (p : Pay) : LTy :=
  match payTy p with
  | none => a
  | some t => .sum a t

/-- The payload `p` holding `v` at the summand `j`. -/
def injectPay (p : Pay) (j : Nat) (v : Var) (k : Var → CM Tm) : CM Tm := do
  match p, j with
  | [_], _ => k v
  | _ :: rest, 0 => do
    let w ← fresh (← lift (Option.elim (payTy p) (.error "LIR: an empty payload") .ok))
    return .letv w (.inj false v) (← k w)
  | _ :: rest, j + 1 =>
    injectPay rest j v fun r => do
      let w ← fresh (← lift (Option.elim (payTy p) (.error "LIR: an empty payload") .ok))
      return .letv w (.inj true r) (← k w)
  | [], _ => throw "LIR: an operation outside its row's payload"

/-- Take the payload `x` of `p` apart: `k j v` at the summand `j`, its argument `v`. -/
def casePay (p : Pay) (x : Var) (k : Nat → Var → CM Tm) : CM Tm := do
  match p with
  | [] => throw "LIR: an empty payload"
  | [_] => k 0 x
  | (_, t) :: rest => do
    let a ← fresh t
    let b ← fresh (← lift (Option.elim (payTy rest) (.error "LIR: an empty payload") .ok))
    return .case x a (← k 0 a) b (← casePay rest b fun j v => k (j + 1) v)

/-- The index of an operation's key among a payload's summands. -/
def payIdx (p : Pay) (key : UInt32 × UInt32) : Option Nat := p.findIdx? (·.1 == key)

/-- A payload `x` of `p` as one of `q`: each operation at its own summand of `q`, which holds it
(the row `Σ ⊆ Σ'`, `RowLe`).  `[spec §47]` -/
def coercePay (p q : Pay) (x : Var) (k : Var → CM Tm) : CM Tm := do
  if p.map (·.1) == q.map (·.1) then return ← k x
  casePay p x fun j v => do
    let some key := (p[j]?).map (·.1) | throw "LIR: a payload's summand"
    let some j' := payIdx q key | throw s!"LIR: a raise of {key} where its row does not hold it"
    injectPay q j' v k

/-- The answer `r` of a computation answering `a` at the payload `p`, as one at `q`: a value
handed on as `inl`, an abort's payload re-injected.  `[spec §47]` -/
def coerceRes (a : LTy) (p q : Pay) (r : Var) : CM Tm := do
  if p.map (·.1) == q.map (·.1) then return .var r
  match payTy p, payTy q with
  | none, none => return .var r
  | none, some _ => return .inj false r
  | some pT, some _ => do
    let x ← fresh a; let e ← fresh pT
    return .case r x (.inj false x) e (← coercePay p q e fun e' => pure (.inj true e'))
  | some _, none => throw "LIR: an abort where the row holds no abortive operation"

/-- The type of component `j` of a `&` closure (through a `!`). -/
def selTy (t : LTy) (j : Nat) : CM LTy := do
  match t.peel with
  | .thunk k =>
    match k.whnf 8, j with
    | .amp k₁ _, 0 => repK k₁
    | .amp _ k₂, _ => repK k₂
    | k, _ => throw s!"LIR: an observation of a closure of {k}"
  | _ => throw s!"LIR: an observation of a non-closure: {t}"
where
  repK : LCTy → CM LTy
    | .ret a => pure a
    | .top => pure .unit
    | k => pure (.thunk k)

/-! ### Machines  `[spec §49]`

A computation at a row with machine operations answers its **outcome** (`Types.outcomeTy`): its
value, an abort's payload, or a suspension at a machine operation, the operation's argument beside
the suspended computation `k`, a closure of `(B ⊸ F O) & F (1 ⊕ P)`: resumed with the answer it
answers the outcome again, cancelled it unwinds and answers `()` or the first error its finalisers
raised (§19 *Cancels*).

A **machine** is the code of one function whose answer is an outcome, with the joins and steps
its conversion makes (`convK`). Each resumption point of the machine is a variant of its
**state**, per operation: the variables live there and, at a call point, the callee's `k`. So a
caller's state holds its callee's `k`, and the machine's `k` is one closure of one code per
operation (`genMach`): its resume entry switches on the state and continues at the point, its
cancel entry unwinds the point's frames innermost first. -/

namespace OutInfo
/-- The suspended computation at an operation answering `b`, cancelled at the payload `cp`. -/
def kTy (o : OutInfo) (b : LTy) (cp : Option Pay) : LTy :=
  .thunk (.amp (.arr b (.ret o.ty)) (.ret (cancelResTy cp)))
/-- The suspensions' summands: each machine operation's argument and `k`. -/
def sPay (o : OutInfo) : Pay := o.ms.map fun (k, a, b, cp) => (k, .pair a (o.kTy b cp))
def sTy (o : OutInfo) : LTy := (payTy o.sPay).getD .unit
/-- The exits: an abort's payload or a suspension. -/
def xTy (o : OutInfo) : LTy := match payTy o.pay with
  | none => o.sTy
  | some p => .sum p o.sTy
/-- The outcome unrolled. -/
def body (o : OutInfo) : LTy := .sum o.r o.xTy
def keys (o : OutInfo) : List Key × List Key := (o.pay.map (·.1), o.ms.map (·.1))
end OutInfo

/-- The machine operations of a row, each key once with its argument and answer types, in the
row's order.  `[spec §49]` -/
def rowMs (S : Row) : CM (List (Key × LTy × LTy × Option Pay)) := do
  let ms := (← get).mach
  if ms.isEmpty then return []
  let mut acc : List (Key × LTy × LTy × Option Pay) := []
  for o in S do
    if !o.abort && ms.contains (o.n, o.i) && !(acc.any (·.1 == (o.n, o.i))) then
      -- A linear `κ`'s cancel branch is at `⊤` whatever the operation's cancel row (SPEC §25): it
      -- is resumed, never cancelled (read off the operation's qualifier).
      let cp ← if o.q == .lin then pure none else lift (ofFin ms o.fin)
      acc := acc ++ [((o.n, o.i), ← vty o.A, ← vty o.B, cp.map dedupPay)]
  return acc

/-- The outcome of a computation answering `r` at the row `S`; `none` when `S` has no machine
operation. The outcome unrolls to its body (checked).  `[spec §49]` -/
def outInfo? (r : LTy) (S : Row) : CM (Option OutInfo) := do
  let ms ← rowMs S
  if ms.isEmpty then return none
  let pay ← rowPay S
  let ty := outcomeTy r pay ms
  let unrs := (S.filter fun o => o.q == .unr).map fun o => (o.n, o.i)
  let o : OutInfo := { ty, r, pay, ms, unrs }
  match ty with
  | .mu b => unless (LTy.unrollMu b).sameRep o.body do throw s!"LIR: the outcome {ty} does not unroll to {o.body}"
  | _ => throw "LIR: an outcome that is not a μ"
  return some o

/-- The row and value type of `F_Σ R`, through `∀`s. -/
def effParts : CTy → Option (Row × VTy)
  | .eff n i q A B fin c C => (effParts C).map fun (S, R) => (⟨n, i, q, A, B, fin, c⟩ :: S, R)
  | .ret R => some ([], R)
  | .all _ _ C => effParts C
  | _ => none

/-- A computation type through its `∀`s, which the LIR erases (SPEC §44). -/
def stripAll : CTy → CTy
  | .all _ _ C => stripAll C
  | C => C

def outInfoC (C : CTy) : CM (Option OutInfo) := do
  match effParts C with
  | some (S, R) => if S.isEmpty then pure none else outInfo? (← vty R) S
  | none => pure none

def outInfoJ : Jdg → CM (Option OutInfo)
  | .comp C => outInfoC C
  | .val _ => pure none

/-- The outcome whose type is `ty` (a `ν`'s observation, its `X` substituted), at the row `S`. -/
def outInfoTy (ty : LTy) (S : Row) : CM (Option OutInfo) := do
  match ty.peel with
  | .mu b =>
    match LTy.unrollMu b with
    | .sum r _ => do
      let some o ← outInfo? r S | return none
      unless o.ty.sameRep ty do throw s!"LIR: an outcome's type {ty} is not its row's {o.ty}"
      return some o
    | _ => return none
  | _ => return none

/-! #### The outcome's forms -/

def outExit (F : OutInfo) (x : Var) : CM Tm := do
  let w ← fresh F.body
  return .letv w (.inj true x) (.prim .roll [w])

/-- The machine answers the value `x`. -/
def outValue (F : OutInfo) (x : Var) : CM Tm := do
  let w ← fresh F.body
  return .letv w (.inj false x) (.prim .roll [w])

/-- The machine answers the abort `e`, at its payload. -/
def outAbort (F : OutInfo) (e : Var) : CM Tm := do
  match payTy F.pay with
  | none => throw "LIR: an abort at a row with no abortive operation"
  | some _ =>
    let x ← fresh F.xTy
    return .letv x (.inj false e) (← outExit F x)

/-- The machine suspends at `op` with the argument `v` and its suspended computation `k`. -/
def outSusp (F : OutInfo) (op : Key) (v k : Var) : CM Tm := do
  let some j := F.ms.findIdx? (·.1 == op)
    | throw s!"LIR: a suspension at {op} where the machine's row does not hold it"
  let s ← fresh (.pair (← tyOf v) (← tyOf k))
  return .letv s (.pair v k) (← injectPay F.sPay j s fun w => do
    match payTy F.pay with
    | none => outExit F w
    | some _ =>
      let x ← fresh F.xTy
      return .letv x (.inj true w) (← outExit F x))

/-- A non-outcome result `r` (answering `a` at the payload `p`) as one of `target` (an outcome),
or of the payload `q`.  `[spec §47, §49]` -/
def toResult (a : LTy) (p : Pay) (target : Option OutInfo) (q : Pay) (r : Var) : CM Tm := do
  match target with
  | none => coerceRes a p q r
  | some O =>
    match payTy p with
    | none => outValue O r
    | some pT =>
      let x ← fresh a; let e ← fresh pT
      let some pO := payTy O.pay | throw "LIR: an abort where the row holds no abortive operation"
      let e' ← fresh pO
      return .case r x (← outValue O x) e
        (.letv e' (← coercePay p O.pay e fun v => pure (.var v)) (← outAbort O e'))

/-! #### Continuations -/

/-- The level's cell `s` (`Frame.cellF`'s argument, `1 + ref S`) released, then `b`: nothing at
`inl ()`, the cell freed at `inr c` (its contents were taken when the machine resumed). -/
def releaseOpt (s : Var) (b : Tm) : CM Tm := do
  let .sum uT cT := (← tyOf s).peel | throw "LIR: a level's cell that is not `1 + ref S`"
  let u ← fresh uT; let c ← fresh cT; let r ← fresh .unit
  return .letv r (.case s u (.var u) c (.prim .release [c])) (.drop r b)

/-- `K` and its arguments without the level's cell (`Frame.cellF`) or frame (`Frame.stackF`), at
the bottom, and that frame's arguments. -/
def stripCell (K : Kont) (args : List Var) : Kont × List Var × List Var :=
  match K.getLast?, args.getLast? with
  | some .cellF, some s => (K.dropLast, args.dropLast, [s])
  | some .stackF, some _ =>
    if args.length ≥ 2 then (K.dropLast, args.take (args.length - 2), args.drop (args.length - 2))
    else (K, args, [])
  | _, _ => (K, args, [])

/-- The static word that holds the current stack (SPEC §52), reserved the first time. -/
def stackRegister : CM Nat := do
  match (← get).stackReg with
  | some k => pure k
  | none =>
    let k := (← get).statics.size
    modify fun s => { s with statics := s.statics.push [], stackReg := some k }
    pure k

/-- The level's frame `f` (at depth `d`) popped, then `b`. -/
def popThen (f d : Var) (b : Tm) : CM Tm := do
  let k ← stackRegister
  let u ← fresh .unit
  return .letv u (.prim (.framePop k) [f]) (.drop u (.drop d b))

/-- A stored site's stack `h` freed, then `b`. -/
def freeStackThen (h : Var) (b : Tm) : CM Tm := do
  let u ← fresh .unit
  return .letv u (.prim .stackFree [h]) (.drop u b)

/-- The value `x` handed to the continuation `K` over its arguments: the innermost frame's join,
or the machine's answer (its cell released, or its frame popped, first). -/
def applyK (F : OutInfo) : Kont → List Var → Var → CM Tm
  | [], [], x => outValue F x
  | [], _, _ => throw "LIR: a machine's answer with arguments left"
  | [.cellF], [c], x => do releaseOpt c (← outValue F x)
  | .cellF :: _, _, _ => throw "LIR: a level's cell above the bottom of its continuation"
  | [.stackF], [f, d], x => do popThen f d (← outValue F x)
  | .stackF :: _, _, _ => throw "LIR: a level's frame above the bottom of its continuation"
  | .stackH :: _, _, _ => throw "LIR: a value at a site's stack"
  | .letF fn _ :: _, args, x | .thenF fn _ _ _ :: _, args, x => pure (.call fn (args ++ [x]))
  | .dropF _ :: _, _, _ => throw "LIR: a value at a frame that only drops"

/-- The abort `e` (at the machine's payload) through `K`: each frame's arguments dropped, a
finaliser run, its own abort superseding (`then_fin`, `unwind_prefix`); then the machine's
answer. -/
def abortK (F : OutInfo) : Kont → List Var → Var → CM Tm
  | [], _, e => outAbort F e
  | f :: rest, args, e => do
    let own := args.take f.own
    let more := args.drop f.own
    match f with
    | .thenF _ fnD _ pd =>
      let d ← fresh (resTy .unit pd)
      match payTy pd with
      | none => return .letv d (.call fnD own) (.drop d (← abortK F rest more e))
      | some pdT =>
        let some pF := payTy F.pay | throw "LIR: a finaliser's abort where the row holds none"
        let e' ← fresh pF; let u ← fresh .unit; let e₂ ← fresh pdT
        let sup ← coercePay pd F.pay e₂ fun v => pure (.var v)
        return .letv d (.call fnD own) (.letv e' (.case d u (.drop u (.var e)) e₂ (.drop e sup))
          (← abortK F rest more e'))
    | .cellF => match own with
      | [c] => releaseOpt c (← abortK F rest more e)
      | _ => throw "LIR: a level's cell frame without its cell"
    | .stackF => match own with
      | [fr, d] => popThen fr d (← abortK F rest more e)
      | _ => throw "LIR: a level's frame without its cell"
    | .stackH => match own with
      | [h] => freeStackThen h (← abortK F rest more e)
      | _ => throw "LIR: a site's stack frame without its stack"
    | _ => return drops own (← abortK F rest more e)

/-- The cancel of `K`, `err` the error kept so far (`1 ⊕ P`, `cp` the cancel row's payload `P`):
each frame's arguments dropped, a finaliser run under the cancel, the first error kept (§19
*Cancels*, `[cfin-raise]`); a finaliser's error is one of the cancel row's (§27). -/
def cancelK (cp : Pay) : Kont → List Var → Var → CM Tm
  | [], _, err => pure (.var err)
  | f :: rest, args, err => do
    let own := args.take f.own
    let more := args.drop f.own
    match f with
    | .thenF _ fnD _ pd =>
      let d ← fresh (resTy .unit pd)
      match payTy cp, payTy pd with
      | _, none => return .letv d (.call fnD own) (.drop d (← cancelK cp rest more err))
      | none, some _ => throw "LIR: a finaliser's error outside its operation's cancel row"
      | some pF, some pdT =>
        let err' ← fresh (resTy .unit cp)
        let u₀ ← fresh .unit; let e₀ ← fresh pF
        let u₁ ← fresh .unit; let e₁ ← fresh pdT; let u₂ ← fresh .unit; let e₂ ← fresh pdT
        let sup ← coercePay pd cp e₁ fun v => pure (.inj true v)
        let kept : Tm := .case err u₀ (.case d u₁ (.drop u₁ (.inj false u₀)) e₁ (.drop u₀ sup))
          e₀ (.case d u₂ (.drop u₂ (.inj true e₀)) e₂ (.drop e₂ (.inj true e₀)))
        return .letv d (.call fnD own) (.letv err' kept (← cancelK cp rest more err'))
    | .cellF => match own with
      | [c] => releaseOpt c (← cancelK cp rest more err)
      | _ => throw "LIR: a level's cell frame without its cell"
    | .stackF => match own with
      | [fr, d] => popThen fr d (← cancelK cp rest more err)
      | _ => throw "LIR: a level's frame without its cell"
    | .stackH => match own with
      | [h] => freeStackThen h (← cancelK cp rest more err)
      | _ => throw "LIR: a site's stack frame without its stack"
    | _ => return drops own (← cancelK cp rest more err)

/-! #### Resumption points -/

def curMach : CM OutInfo := do
  match (← get).machs with
  | m :: _ => pure m.info
  | [] => throw "LIR: a machine's computation outside a machine"

/-- Register a resumption point of the current machine; its `mk` function, set by `genMach`. -/
def newPoint (op : Key) (kTy : Option LTy) (cPay : Option Pay) (argTys : List LTy) (step : Option Nat)
    (K : Kont) (callee : Option OutInfo := none) (inline : Bool := false)
    (outVar : Option Var := none) (swapAt : Option Nat := none) : CM Nat := do
  let mk ← reserveFn s!"suspend {op.1}.{op.2}"
  let pt : MPoint := { op, kTy, cPay, argTys, step, kont := K, mkFn := mk, callee,
                       site := step.getD 0, inline, outVar, swapAt }
  match (← get).machs with
  | m :: rest =>
    let m' : Mach := { m with points := m.points.push pt }
    modify fun s => { s with machs := m' :: rest }
  | [] => throw "LIR: a suspension outside a machine"
  return mk

/-- The answer `b` and cancel row's payload of the machine operation `op` at a machine. -/
def opAnswer (F : OutInfo) (op : Key) : CM (LTy × Option Pay) := do
  match F.ms.find? (·.1 == op) with
  | some (_, _, b, cp) => pure (b, cp)
  | none => throw s!"LIR: a suspension at {op} where the machine's row does not hold it"

/-- `F.kTy` at the operation `op`. -/
def kTyAt (F : OutInfo) (op : Key) : CM LTy := do
  let (b, cp) ← opAnswer F op
  return F.kTy b cp

/-- **A `perform` of a machine operation**, `K` its continuation: the machine suspends here, its
state the continuation's arguments (`[op]`, the continuation the rest of the machine).  -/
def performK (K : Kont) (args : List Var) (op : Key) (v : Var) : CM Tm := do
  let F ← curMach
  -- With the level's cell passed on, the state is the other arguments; `mk` takes the cell's
  -- argument last (`genMach`).
  let (K', args', _) := stripCell K args
  let mk ← newPoint op none none (← args'.mapM tyOf) none K'
  let k ← fresh (← kTyAt F op)
  modify fun st => { st with erased := st.erased.insert "suspend" (st.erased.getD "suspend" 0 + 1) }
  return .letv k (.call mk args) (← outSusp F op v k)

/-- The cell `c` released, then `b`. -/
def releaseThen (c : Var) (b : Tm) : CM Tm := do
  let u ← fresh .unit
  return .letv u (.prim .release [c]) (.drop u b)

/-- A step's reuse of its machine's state cell (SPEC §49): the cell `cell`, its contents taken,
of the operation `op`; the points of the machine, each with the function that builds its
suspended computation in a given cell (`mkCells`). -/
structure Reuse where
  cell : Var
  op : Key
  pts : List MPoint
  mkCells : Std.HashMap Nat Nat

/-- The step at a call point: the callee's outcome `o` (of `M`) taken apart. A value goes to `K`,
an abort through `K`'s frames, a suspension suspends the machine at this point, its state the
callee's `k` and `K`'s arguments. With `reuse` (the resume entry of a machine whose state is a cell), a suspension
again at the cell's operation writes the cell in place. -/
def stepTm (F : OutInfo) (K : Kont) (args : List Var) (o : Var) (M : OutInfo) (stepFn : Nat)
    (reuse : Option Reuse := none) : CM Tm := do
  let w ← fresh M.body; let x ← fresh M.r; let ex ← fresh M.xTy
  let (K', args', _) := stripCell K args
  let argTys ← args'.mapM tyOf
  -- With a cell to reuse: released where the machine does not suspend again at its operation.
  let released (b : Tm) : CM Tm := match reuse with
    | some r => releaseThen r.cell b
    | none => pure b
  let abortArm (e : Var) : CM Tm := do
    let some pF := payTy F.pay | throw "LIR: an abort where the machine's row holds none"
    let e' ← fresh pF
    released (.letv e' (← coercePay M.pay F.pay e fun v => pure (.var v)) (← abortK F K args e'))
  let suspArms (s : Var) : CM Tm := casePay M.sPay s fun j sv => do
    let some (op, _, b, cp) := M.ms[j]? | throw "LIR: a suspension's summand"
    letpairM sv fun v k => do
      let k' ← fresh (← kTyAt F op)
      match reuse with
      | none =>
        let mk ← newPoint op (some (M.kTy b cp)) cp argTys (some stepFn) K' (callee := some M)
          (inline := true) (outVar := some o)
        return .letv k' (.call mk (k :: args)) (← outSusp F op v k')
      | some r =>
        let some p := r.pts.find? fun p => p.site == stepFn && p.op == op
          | throw "LIR: a call point's suspension"
        if op == r.op then
          let some mc := r.mkCells[p.mkFn]? | throw "LIR: a state cell's point"
          return .letv k' (.call mc (r.cell :: k :: args)) (← outSusp F op v k')
        releaseThen r.cell (.letv k' (.call p.mkFn (k :: args)) (← outSusp F op v k'))
  let exits ← match payTy M.pay with
    | none => suspArms ex
    | some pT => do
      let e ← fresh pT; let s ← fresh M.sTy
      pure (Tm.case ex e (← abortArm e) s (← suspArms s))
  return .letv w (.prim .unroll [o]) (.case w x (← released (← applyK F K args x)) ex exits)

/-- Why a call point's step is inlined (SPEC §50): it is the machine's code after the call, one code
with the machine (SPEC §49), a function only so that the resume entry can enter it again. -/
def stepInline : String :=
  "a call point's step: the machine's code after the call, one code with its machine (SPEC §49)"

/-- **A call point**: `e` answers the callee's outcome (of `M`), handed to `K`: a step function,
which the resume entry calls again, so the callee's `k` is in the machine's state and the machine
is one code. In tail position at the machine's own outcome the step is made when the machine is
complete (`withMachine`): a machine with that call and no other point passes its callee's
outcome on; a call that closes a loop of tail calls passes it on too (`tailPass`). -/
def pointK (K : Kont) (args : List Var) (e : Tm) (M : OutInfo) : CM Tm := do
  let F ← curMach
  if K.isEmpty && args.isEmpty && M.ty.sameRep F.ty && M.keys == F.keys then
    let fn ← reserveFn "tail"
    let o ← fresh M.ty
    match (← get).machs with
    | m :: rest =>
      let m' : Mach := { m with tails := m.tails.push (fn, M) }
      modify fun s => { s with machs := m' :: rest }
    | [] => throw "LIR: a call point outside a machine"
    return .letv o e (.call fn [o])
  let o ← fresh M.ty
  let stepFn ← reserveFn "step"
  let argPs ← args.mapM freshLike
  let oP ← fresh M.ty
  let body ← stepTm F K argPs oP M stepFn
  setFn stepFn { name := "step", params := argPs ++ [oP], body, ret := F.ty, inline := some stepInline }
  readFact "machine:call point"
  return .letv o e (.call stepFn (args ++ [o]))

/-- A result that is not an outcome (`a` at the payload `p`) handed to `K`. -/
def resultK (K : Kont) (args : List Var) (e : Tm) (a : LTy) (p : Pay) : CM Tm := do
  let F ← curMach
  match payTy p with
  | none => bindTm e a fun x => applyK F K args x
  | some pT =>
    let r ← fresh (.sum a pT); let x ← fresh a; let e₀ ← fresh pT
    let some pF := payTy F.pay | throw "LIR: an abort where the machine's row holds none"
    let e' ← fresh pF
    return .letv r e (.case r x (← applyK F K args x) e₀
      (.letv e' (← coercePay p F.pay e₀ fun v => pure (.var v)) (← abortK F K args e')))

/-! #### The machine's codes -/

def tupleTy : List LTy → LTy
  | [] => .unit
  | [t] => t
  | t :: ts => .pair t (tupleTy ts)

/-- The variables as a right-nested tuple. -/
def mkTuple : List Var → (Var → CM Tm) → CM Tm
  | [], k => do let u ← fresh .unit; return .letv u .unit (← k u)
  | [x], k => k x
  | x :: xs, k => mkTuple xs fun r => do
    let p ← fresh (.pair (← tyOf x) (← tyOf r))
    return .letv p (.pair x r) (← k p)

/-- A right-nested tuple of the types `tys` taken apart. -/
def untuple (v : Var) : List LTy → (List Var → CM Tm) → CM Tm
  | [], k => do return .drop v (← k [])
  | [_], k => k [v]
  | _ :: ts, k => letpairM v fun x r => untuple r ts fun xs => k (x :: xs)

/-- **A stored site's stack made current** (SPEC §52) around a run of the callee's `k` (`run`, the
binding of its answer), at a forwarding point that holds the stack (`MPoint.swapAt`): the stack
swapped in before the run and out after it, the arguments then handed on with the stack the
register held. Elsewhere the run alone. -/
def aroundRun (p : MPoint) (args : List Var) (run : Tm → Tm) (rest : List Var → CM Tm) : CM Tm := do
  match p.swapAt with
  | none => return run (← rest args)
  | some i =>
    let some sh := args[i]? | throw "LIR: a forwarding point's stack"
    let k ← stackRegister
    let prev ← fresh (.int .w64); let sh' ← fresh (.int .w64)
    return .letv prev (.prim (.stackSwap k) [sh])
      (run (.letv sh' (.prim (.stackSwap k) [prev]) (← rest (args.set i sh'))))

/-- The resume of a point's variant `fs` with the answer `y`. -/
def resumeTm (F : OutInfo) (p : MPoint) (fs : List Var) (y : Var) (reuse : Option Reuse := none)
    (slot : Option Var := none) : CM Tm := do
  -- The level's cell passed on (SPEC §50): the point's continuation goes on with `inr c`, so a
  -- later suspension writes the cell in place and the machine's answer releases it.
  if let some sl := slot then
    match p.kTy, fs, p.step with
    | some kT, k :: args, some stepFn => do
      let krT ← selTy kT 0
      let (_, mT) ← answerOf krT
      let kr ← fresh krT; let o ← fresh mT
      return .letv kr (.sel k 0) (.letv o (.app kr y) (.call stepFn (args ++ [sl, o])))
    | none, args, _ => return ← applyK F (p.kont ++ [.cellF]) (args ++ [sl]) y
    | _, _, _ => throw "LIR: a resumption point's state"
  let released (b : Tm) : CM Tm := match reuse with
    | some r => releaseThen r.cell b
    | none => pure b
  match p.kTy, fs, p.step with
  | some kT, k :: args, some stepFn => do
    let krT ← selTy kT 0
    let (_, mT) ← answerOf krT
    let kr ← fresh krT; let o ← fresh mT
    match reuse, p.callee, p.inline with
    | some _, some M, true =>
      -- The step in place: a suspension again at this operation reuses the cell.
      return .letv kr (.sel k 0) (.letv o (.app kr y) (← stepTm F p.kont args o M stepFn reuse))
    | _, _, _ =>
      released (← aroundRun p args (fun t => .letv kr (.sel k 0) (.letv o (.app kr y) t))
        fun args => pure (.call stepFn (args ++ [o])))
  | none, args, _ => released (← applyK F p.kont args y)
  | _, _, _ => throw "LIR: a resumption point's state"

/-- The cancel of a point's variant `fs`, `cp` the operation's cancel row's payload: the callee's
`k` cancelled first, then the point's frames. -/
def cancelTm (cp : Pay) (p : MPoint) (fs : List Var) : CM Tm := do
  match p.kTy, fs with
  | some kT, k :: args => do
    let cT ← selTy kT 1
    let c ← fresh cT; let err ← fresh (resTy .unit cp)
    let coerced ← coerceRes .unit (p.cPay.getD []) cp c
    aroundRun p args (fun t => .letv c (.sel k 1) t) fun args => do
      return .letv err coerced (← cancelK cp p.kont args err)
  | none, args => do
    let u ← fresh .unit
    match payTy cp with
    | none => return .letv u .unit (← cancelK cp p.kont args u)
    | some _ =>
      let err ← fresh (resTy .unit cp)
      return .letv u .unit (.letv err (.inj false u) (← cancelK cp p.kont args err))
  | _, _ => throw "LIR: a resumption point's state"

/-- The state of machine `m` at its operation `op`: one variant per point, each its suspended
callee's computation (at a call point) and its arguments. -/
def machStateTy (m : Mach) (op : Key) : LTy :=
  let ps := m.points.toList.filter (·.op == op)
  let fieldsOf (p : MPoint) : List LTy := p.kTy.toList ++ p.argTys
  (payTy (ps.zipIdx.map fun (p, i) => ((0, i.toUInt32), tupleTy (fieldsOf p)))).getD .unit

/-- **The codes of a machine**, once its points are known: per operation, its state (one variant
per point), the suspended computation's `&` code (`resume`, `cancel`), the resume code that
switches on the state, and each point's `mk`.  `[spec §49]` -/
def genMach (m : Mach) (cellOps : List Key := []) : CM (List (Key × Nat)) := do
  let F := m.info
  let mut kcs : List (Key × Nat) := []
  for (op, _, b, cp) in F.ms do
    let ps := m.points.toList.filter (·.op == op)
    let cT := cancelResTy cp
    if ps.isEmpty then continue
    let fieldsOf (p : MPoint) : List LTy := p.kTy.toList ++ p.argTys
    let stPay : Pay := ps.zipIdx.map fun (p, i) => ((0, i.toUInt32), tupleTy (fieldsOf p))
    let stTy := machStateTy m op
    -- **The level's cell passed on** (SPEC §50), at the state's type the first conversion read.
    let threaded := m.cell.isSome
    if threaded && !(m.cell.any (·.sameRep stTy)) then
      throw "LIR: a level's cell whose state differs from the first conversion's"
    -- **A state cell** where the machine's state holds its own suspended computation (its closure
    -- class holds itself: a recursion through a resumption point, a clause resuming `κ` before it
    -- answers; `cellPass`). The state is a cell, allocated when the machine first suspends and
    -- written in place each time it suspends again at the operation; its suspended computation
    -- is a word. Otherwise the state is the closure's environment, as it always is at `unr`, whose
    -- suspended computation may be copied (§19).
    -- UNPROVED: that a state cell has one owner, the suspended computation `k` that holds it, so
    -- that a resume may write it in place and a cancel or the machine's answer may release it.
    -- It should hold because `k` is resumed or cancelled at most once where the operation is not
    -- `unr` (the row's qualifier, read: `OutInfo.unrs`). Which operations get a cell (`cellOps`,
    -- `threaded`) is read off the layouts' recursive closure classes (`cellPass`, `threadedOf`),
    -- which is not a typing fact. If it fails, a resumed copy of `k` reads a state written by
    -- another, or a released cell.
    let cellMode := threaded || (cellOps.contains op && !F.unrs.contains op)
    let envTy : LTy := if cellMode then .ref stTy else stTy
    let slotTy : LTy := .sum .unit envTy
    let rres ← reserveFn s!"resume {op.1}.{op.2}"
    let rc ← addCode { kind := .lam, fns := [rres], ty := .arr b (.ret F.ty) }
    let kres ← reserveFn s!"resume entry {op.1}.{op.2}"
    let kcan ← reserveFn s!"cancel {op.1}.{op.2}"
    let kc ← addCode { kind := .amp, fns := [kres, kcan], ty := .amp (.arr b (.ret F.ty)) (.ret cT) }
    kcs := kcs ++ [(op, kc)]
    let s₀ ← fresh envTy
    setFn kres { name := s!"resume entry {op.1}.{op.2}", params := [s₀], body := .clos rc [s₀],
                 ret := .thunk (.arr b (.ret F.ty)) }
    let mut mkCells : Std.HashMap Nat Nat := {}
    if cellMode then
      readFact "machine:state cell"
      unless threaded do
        for p in ps do mkCells := mkCells.insert p.mkFn (← reserveFn s!"suspend in place {op.1}.{op.2}")
    -- The state, out of the environment or out of its cell.
    let withState (e : Var) (k : Option Var → Var → CM Tm) : CM Tm := do
      if cellMode then
        let pr ← fresh (.pair envTy stTy); let c ← fresh envTy; let st ← fresh stTy
        return .letv pr (.prim .take [e]) (.letpair c st pr (← k (some c) st))
      else k none e
    let s₁ ← fresh envTy; let y ← fresh b
    let rb ← withState s₁ fun c st => casePay stPay st fun i fv => do
      let some p := ps[i]? | throw "LIR: a machine's point"
      let reuse : Option Reuse := c.map fun c => { cell := c, op, pts := m.points.toList, mkCells }
      untuple fv (fieldsOf p) fun fs => do
        match threaded, c with
        | true, some c =>
          let sl ← fresh slotTy
          return .letv sl (.inj true c) (← resumeTm F p fs y (slot := some sl))
        | _, _ => resumeTm F p fs y reuse
    setFn rres { name := s!"resume {op.1}.{op.2}", params := [s₁, y], body := rb, ret := F.ty }
    let s₂ ← fresh envTy
    -- At a cancel row `⊤` (a linear operation) the cancel entry is never run (`rowMs`), so it is
    -- `unreachable` and its state is not discarded.
    let cb ← match cp with
      | none => do
        let u ← fresh cT
        pure (.letv u (.prim .unreachable []) (.var u))
      | some cp => withState s₂ fun c st => do
        let arms ← casePay stPay st fun i fv => do
          let some p := ps[i]? | throw "LIR: a machine's point"
          untuple fv (fieldsOf p) fun fs => cancelTm cp p fs
        match c with
        | some c => releaseThen c arms
        | none => pure arms
    setFn kcan { name := s!"cancel {op.1}.{op.2}", params := [s₂], body := cb, ret := cT }
    for (p, i) in ps.zipIdx do
      let xs ← (fieldsOf p).mapM fresh
      -- With the level's cell passed on, `mk` takes the cell's argument last: the cell is
      -- allocated at the level's first suspension and written in place at each later one.
      let sl ← fresh slotTy
      let body ← mkTuple xs fun t => injectPay stPay i t fun st => do
        if threaded then
          let u ← fresh .unit; let c ← fresh envTy; let c₁ ← fresh envTy; let c₂ ← fresh envTy
          return .case sl u (.drop u (.letv c₁ (.prim (.alloc []) [st]) (.clos kc [c₁])))
            c (.letv c₂ (.prim .put [c, st]) (.clos kc [c₂]))
        else if cellMode then
          let c ← fresh envTy
          return .letv c (.prim (.alloc []) [st]) (.clos kc [c])
        else pure (.clos kc [st])
      setFn p.mkFn { name := s!"suspend {op.1}.{op.2}", params := xs ++ (if threaded then [sl] else []),
                     body, ret := F.kTy b cp }
      if let some mc := mkCells[p.mkFn]? then
        let c ← fresh envTy
        let xs ← (fieldsOf p).mapM fresh
        let body ← mkTuple xs fun t => injectPay stPay i t fun st => do
          let c' ← fresh envTy
          return .letv c' (.prim .put [c, st]) (.clos kc [c'])
        setFn mc { name := s!"suspend in place {op.1}.{op.2}", params := c :: xs, body,
                   ret := F.kTy b cp }
  readFact "machine:state"
  return kcs

/-- **The codes of a stack machine** (SPEC §52): its levels' frames are on the task stack, each
level's reserved when it starts (`Frame.stackF`), so a call point's state is first order, the
callee's `k` left out (its frame is the one above), and a level's `k` is its frame's address.

- Each point's `mk` writes the state into the level's frame, which stays on the stack, and answers
  `k` at the frame; at a call point the callee's `k`, at the frame above, is dropped.
- `k`'s resume entry is a loop from the top of the stack down to its own frame, the *base*
  (`kappa_resume_steps` with the nesting kept as positions): the top frame's level continues at
  its point with the answer (`stack continue`); a level that answers has popped its frame, and the
  frame below, at its call of it, continues with the value (`stack return`) or its abort (`stack
  unwind`); a suspension of any level suspends `k` again at the base, the frames below it as they
  were, which is the identity that `step_i (susp (p, point_i k')) = susp (p, point_i k')` asks of
  them. When the base's level has answered, its answer is `k`'s.
- `k`'s cancel entry pops the frames from the top down to the base, each frame's continuation
  unwound under the cancel, the first error kept (`kappa_cancel_steps`, `cancel_prefix`):
  innermost first.
- A frame below a finished level is at a call of it, and the top frame at a `perform`: the other
  arms of the continue and return entries are `unreachable`. -/
def genStackMach (m : Mach) (S : LTy) : CM (List (Key × Nat)) := do
  let F := m.info
  let ps := m.points.toList
  let some p₀ := ps.head? | return []
  let op := p₀.op
  unless ps.all (·.op == op) do throw "LIR: a stack machine with points at two operations"
  let (b, cp) ← opAnswer F op
  let stPay : Pay := ps.zipIdx.map fun (p, i) => ((0, i.toUInt32), tupleTy p.argTys)
  let stTy := (payTy stPay).getD .unit
  unless stTy.sameRep S do throw "LIR: a stack machine's frame differs from the first conversion's"
  let reg ← stackRegister
  let fT : LTy := .ref stTy
  let aT : LTy := .int .w64
  let cT := cancelResTy cp
  readFact "machine:stack frame"
  let rres ← reserveFn s!"stack resume {op.1}.{op.2}"
  let rc ← addCode { kind := .lam, fns := [rres], ty := .arr b (.ret F.ty) }
  let kres ← reserveFn s!"stack resume entry {op.1}.{op.2}"
  let kcan ← reserveFn s!"stack cancel {op.1}.{op.2}"
  let kc ← addCode { kind := .amp, fns := [kres, kcan], ty := .amp (.arr b (.ret F.ty)) (.ret cT) }
  let contY ← reserveFn "stack continue"
  let contV ← reserveFn "stack return"
  let contA ← reserveFn "stack unwind"
  let rstep ← reserveFn "stack step"
  let cstep ← reserveFn "stack cancel step"
  -- The top frame: its cell and its address.
  let top (k : Var → Var → CM Tm) : CM Tm := do
    let fa ← fresh (.pair fT aT); let f ← fresh fT; let a ← fresh aT
    return .letv fa (.prim (.frameTop m.start reg) []) (.letpair f a fa (← k f a))
  -- `yes` when the address `a` is the base's, else `no`; both consumed.
  let ifBase (a base : Var) (yes no : CM Tm) : CM Tm := do
    let pr ← fresh (.pair aT aT); let c ← fresh boolT; let u₁ ← fresh .unit; let u₂ ← fresh .unit
    return .letv pr (.pair a base) (.letv c (.prim (.host (.rel .w64 .eq)) [pr])
      (.case c u₁ (.drop u₁ (← no)) u₂ (.drop u₂ (← yes))))
  let never (t : LTy) : CM Tm := do
    let u ← fresh t
    return .letv u (.prim .unreachable []) (.var u)
  -- A frame's state taken out, and `k` on the point, the frame and its fields.
  let atFrame (f : Var) (k : MPoint → Var → List Var → CM Tm) : CM Tm := do
    let pr ← fresh (.pair fT stTy); let f' ← fresh fT; let st ← fresh stTy
    let arms ← casePay stPay st fun i fv => do
      let some p := ps[i]? | throw "LIR: a stack machine's point"
      untuple fv p.argTys fun args => k p f' args
    return .letv pr (.prim .take [f]) (.letpair f' st pr arms)
  -- The entries that continue a frame (its cell and address): at a `perform` with the answer, at a
  -- call with the callee's value, at a call with the callee's abort.
  let y₀ ← fresh b; let f₀ ← fresh fT; let a₀ ← fresh aT
  let bY ← atFrame f₀ fun p f args => do
    if p.kTy.isSome then return ← never F.ty
    applyK F (p.kont ++ [.stackF]) (args ++ [f, a₀]) y₀
  setFn contY { name := "stack continue", params := [f₀, a₀, y₀], body := bY, ret := F.ty }
  let r₁ ← fresh F.r; let f₁ ← fresh fT; let a₁ ← fresh aT
  let bV ← atFrame f₁ fun p f args => do
    if p.kTy.isNone then return ← never F.ty
    applyK F (p.kont ++ [.stackF]) (args ++ [f, a₁]) r₁
  setFn contV { name := "stack return", params := [f₁, a₁, r₁], body := bV, ret := F.ty }
  let pF? := payTy F.pay
  if let some pF := pF? then
    let e₂ ← fresh pF; let f₂ ← fresh fT; let a₂ ← fresh aT
    let bA ← atFrame f₂ fun p f args => do
      let some M := p.callee | return ← never F.ty
      let e' ← fresh pF
      return .letv e' (← coercePay M.pay F.pay e₂ fun v => pure (.var v))
        (← abortK F (p.kont ++ [.stackF]) (args ++ [f, a₂]) e')
    setFn contA { name := "stack unwind", params := [f₂, a₂, e₂], body := bA, ret := F.ty }
  else
    setFn contA { name := "stack unwind", params := [], body := ← never F.ty, ret := F.ty }
  -- The step of the loop: the outcome of the level whose frame was at `a`, the frames down to the
  -- base left to continue.
  let base₃ ← fresh aT; let a₃ ← fresh aT; let o₃ ← fresh F.ty
  let w ← fresh F.body; let x ← fresh F.r; let ex ← fresh F.xTy
  let base₃' ← fresh aT
  let below (arm : Var → Var → CM Tm) (here : CM Tm) : CM Tm :=
    ifBase a₃ base₃' (do return .drop base₃ (← here)) (top fun f a => do
      let o' ← fresh F.ty
      let a' ← fresh aT
      return .copy a a' (.letv o' (← arm f a) (.call rstep [base₃, a', o'])))
  let valArm ← below (fun f a => pure (.call contV [f, a, x])) (outValue F x)
  let suspArms (sv : Var) : CM Tm := casePay F.sPay sv fun j pv => do
    let some (key, _, _, _) := F.ms[j]? | throw "LIR: a suspension's summand"
    letpairM pv fun v k' => do
      let k₂ ← fresh (F.kTy b cp)
      -- A level's suspended computation, dropped for the machine's own over the base: as at a
      -- point's `mk` below (`Prog.stackKs`).
      modify fun st => { st with stackKs := st.stackKs.insert k' }
      return .drop a₃ (.drop base₃' (.drop k' (.letv k₂ (.clos kc [base₃]) (← outSusp F key v k₂))))
  let exits ← match pF? with
    | none => suspArms ex
    | some pT => do
      let e ← fresh pT; let sv ← fresh F.sTy
      pure (Tm.case ex e (← below (fun f a => pure (.call contA [f, a, e])) (outAbort F e)) sv
        (← suspArms sv))
  setFn rstep { name := "stack step", params := [base₃, a₃, o₃],
                body := .copy base₃ base₃' (.letv w (.prim .unroll [o₃]) (.case w x valArm ex exits)),
                ret := F.ty }
  -- `k` at its base: its resume entry, and its resume.
  let base₄ ← fresh aT
  setFn kres { name := s!"stack resume entry {op.1}.{op.2}", params := [base₄],
               body := .clos rc [base₄], ret := .thunk (.arr b (.ret F.ty)) }
  let base₅ ← fresh aT; let y₅ ← fresh b; let o₅ ← fresh F.ty
  let b₅ ← top fun f a => do
    let a' ← fresh aT
    return .copy a a' (.letv o₅ (.call contY [f, a, y₅]) (.call rstep [base₅, a', o₅]))
  setFn rres { name := s!"stack resume {op.1}.{op.2}", params := [base₅, y₅], body := b₅, ret := F.ty }
  -- The cancel: the frames from the top down to the base, each unwound under the cancel.
  let base₆ ← fresh aT
  match cp with
  | none =>
    setFn kcan { name := s!"stack cancel {op.1}.{op.2}", params := [base₆], body := .drop base₆ .unit,
                 ret := cT }
    setFn cstep { name := "stack cancel step", params := [], body := ← never cT, ret := cT }
  | some cpP =>
    let errT := resTy .unit cpP
    let base₇ ← fresh aT; let base₇' ← fresh aT; let err₇ ← fresh errT
    let bC ← top fun f a => do
      let err' ← fresh errT; let a' ← fresh aT
      let arms ← atFrame f fun p f' args =>
        cancelK cpP (p.kont ++ [.stackF]) (args ++ [f', a']) err₇
      return .copy a a' (.letv err' arms
        (← ifBase a base₇' (do return .drop base₇ (.var err')) (pure (.call cstep [base₇, err']))))
    setFn cstep { name := "stack cancel step", params := [base₇, err₇], body := .copy base₇ base₇' bC,
                  ret := errT }
    let u ← fresh .unit; let err₀ ← fresh errT
    let start : Tm := match payTy cpP with
      | none => .var u
      | some _ => .inj false u
    setFn kcan { name := s!"stack cancel {op.1}.{op.2}", params := [base₆],
                 body := .letv u .unit (.letv err₀ start (.call cstep [base₆, err₀])), ret := cT }
  -- Each point's `mk`: the state into the level's frame, and `k` at it.
  for (p, i) in ps.zipIdx do
    let kv? ← p.kTy.mapM fresh
    let xs ← p.argTys.mapM fresh
    let f ← fresh fT; let a ← fresh aT
    let body ← mkTuple xs fun t => injectPay stPay i t fun sv => do
      let u ← fresh .unit
      return .letv u (.prim .framePut [f, sv]) (.drop u (.clos kc [a]))
    -- UNPROVED: that dropping a level's suspended computation (`kv` here, `k'` in the step) leaks
    -- nothing. Its type is a closure, which no typing rule lets a term discard; the drop rests on
    -- the stack machine's call points calling a level of the machine itself (`stackedOf`), so that
    -- it is a closure of this machine's `kc` over a stack address alone, the state it stands for
    -- being in the level's frame on the task stack. `Lint` checks every other drop by its type,
    -- and lets these through by `Prog.stackKs`. If it fails, the level's state is leaked.
    let body ← match kv? with
      | some kv => do
        modify fun st => { st with stackKs := st.stackKs.insert kv }
        pure (Tm.drop kv body)
      | none => pure body
    setFn p.mkFn { name := s!"suspend {op.1}.{op.2}", params := kv?.toList ++ xs ++ [f, a], body,
                   ret := F.kTy b cp }
  readFact "machine:state"
  return [(op, kc)]

/-- The machine begun last (`withMachine`, `withMachineK`), its body `t` converted: its tail
calls' functions, then its codes. -/
def finishMachine (F : OutInfo) (t : Tm) : CM Tm := do
  -- The tail calls: a machine with one and no other point passes its callee's outcome on (its
  -- `k` is the callee's); otherwise each is a point, so the machine's `k` is one code.
  let mut wrapped : Array (Nat × Var × OutInfo) := #[]
  match (← get).machs with
  | m :: _ =>
    let wrapper := m.tails.size == 1 && m.points.isEmpty
    for (fn, M) in m.tails do
      let oP ← fresh M.ty
      if wrapper then
        readFact "machine:tail call"
        setFn fn { name := "tail", params := [oP], body := .var oP, ret := F.ty }
      else
        let body ← stepTm F [] [] oP M fn
        readFact "machine:call point"
        setFn fn { name := "step", params := [oP], body, ret := F.ty, inline := some stepInline }
        wrapped := wrapped.push (fn, oP, M)
  | [] => throw "LIR: a machine's stack"
  match (← get).machs with
  | m :: rest =>
    modify fun s => { s with machs := rest }
    if m.cell.isSome && !m.tails.isEmpty then
      throw "LIR: a level's cell passed on at a machine with calls in tail position"
    let kcs ← match m.stack with
      | some S => genStackMach m S
      | none => genMach m
    let i := (← get).done.size
    modify fun s => { s with done := s.done.push (m, kcs),
                             tailSites := s.tailSites ++ wrapped.map fun (fn, o, M) => (fn, o, M, i) }
  | [] => throw "LIR: a machine's stack"
  return t

/-- Convert `act` as the body of a machine of the outcome `F`, then make its codes. -/
def withMachine (F : OutInfo) (act : CM Tm) : CM Tm := do
  let start := (← get).begun
  modify fun s => { s with begun := s.begun + 1, machs := { info := F, start } :: s.machs }
  finishMachine F (← act)

/-- **A machine whose body takes its continuation** (SPEC §49, §50): `act K args` converts the body,
its value handed to `K`. Where a first conversion found the machine's state a cell
(`CState.threaded`), the continuation's bottom frame is the level's cell (`Frame.cellF`), `inl ()`
at the start: the machine's first suspension allocates the cell, each later one writes it in
place, and the machine's answer releases it. Otherwise `K` and its arguments are empty. -/
def withMachineK (F : OutInfo) (act : Kont → List Var → CM Tm) : CM Tm := do
  let start := (← get).begun
  let stack := (← get).stacked[start]?
  let th := (← get).threaded[start]?
  let cell := if stack.isSome then none else th
  modify fun s => { s with begun := s.begun + 1,
                           machs := { info := F, start, threadable := true, cell, stack } :: s.machs }
  let t ← match stack, cell with
    | some S, _ => do
      -- The level's frame reserved on the task stack (SPEC §52), and its address.
      let reg ← stackRegister
      let fa ← fresh (.pair (.ref S) (.int .w64)); let f ← fresh (.ref S); let a ← fresh (.int .w64)
      pure (Tm.letv fa (.prim (.framePush start reg) []) (.letpair f a fa (← act [.stackF] [f, a])))
    | none, some stT => do
      readFact "machine:level cell passed on"
      let u ← fresh .unit; let s₀ ← fresh (.sum .unit (.ref stT))
      pure (Tm.letv u .unit (.letv s₀ (.inj false u) (← act [.cellF] [s₀])))
    | none, none => act [] []
  finishMachine F t

/-! ### Loops generated per site -/

/-- `tab (c, f)` (`array_new`, SPEC §9): an array of `len(c)` slots, slot `i` holding `f i`. -/
def genTab (aT fT : LTy) (p : Var) : CM Tm := do
  let fi ← reserveFn "tab"
  let f ← fresh fT; let a ← fresh aT; let i ← fresh i32T; let n ← fresh i32T
  let body ← dup i fun i i₁ => dup n fun n n₁ =>
    ifLt i₁ n₁
      (dup f fun f f' => dup i fun i i' => do
        let (_, eT) ← answerOf fT
        bindTm (.app f' i') eT fun v => dup i fun i i'' => do
          let a' ← fresh aT
          return .letv a' (.prim .slotPut [a, i'', v]) (← add1 i fun i₂ => pure (.call fi [f, a', i₂, n])))
      (pure (.drop f (.drop i (.drop n (.var a)))))
  setFn fi { name := "tab", params := [f, a, i, n], body, ret := aT }
  letpairM p fun c f => do
    let n ← fresh i32T
    -- A literal's view's tabulation (`TExpr.litView`): the view may be the literal's bytes.
    let lit := (← get).litPending
    modify fun s => { s with litPending := false }
    return .letv n (.prim .clampLen [c]) (.prim ((if lit then Op.tabLit else Op.tab) fi) [f, n])

/-- `drop (f, a)` (`array_free`): each slot's contents to `f`, in order, then the array freed. -/
def genArrFree (fT aT : LTy) (p : Var) : CM Tm := do
  let fi ← reserveFn "array_free"
  let f ← fresh fT; let a ← fresh aT; let i ← fresh i32T; let n ← fresh i32T
  let (some eT, _) ← answerOf fT | throw "LIR: array_free's consumer takes no argument"
  let body ← dup i fun i i₁ => dup n fun n n₁ =>
    ifLt i₁ n₁
      (dup i fun i i' => do
        let pr ← fresh (.pair aT eT)
        let a' ← fresh aT; let v ← fresh eT
        return .letv pr (.prim .slotTake [a, i']) (.letpair a' v pr (← dup f fun f f' => do
          let u ← fresh .unit
          return .letv u (.app f' v) (.drop u (← add1 i fun i₂ => pure (.call fi [f, a', i₂, n]))))))
      (do return .drop f (.drop i (.drop n (← unitThen (.prim .freeArr [a])))))
  setFn fi { name := "array_free", params := [f, a, i, n], body, ret := .unit }
  letpairM p fun f a => do
    let pr ← fresh (.pair aT i32T)
    let a' ← fresh aT; let n ← fresh i32T
    return .letv pr (.prim .size [a]) (.letpair a' n pr (← lit32 0 fun z => pure (.call fi [f, a', z, n])))

/-- `count_fold (f, (n, (i, s)))` (SPEC §16): `f` at `i, …, len(n) − 1`, threading `s`. -/
def genCount (fT sT : LTy) (p : Var) : CM Tm := do
  let fi ← reserveFn "count_fold"
  let f ← fresh fT; let n ← fresh i32T; let i ← fresh i32T; let st ← fresh sT
  let body ← dup i fun i i₁ => dup n fun n n₁ =>
    ifLt i₁ n₁
      (dup f fun f f' => dup i fun i i' => do
        let q ← fresh (.pair i32T sT)
        let st' ← fresh sT
        return .letv q (.pair i' st) (.letv st' (.app f' q)
          (← add1 i fun i₂ => pure (.call fi [f, n, i₂, st']))))
      (pure (.drop f (.drop n (.drop i (.var st)))))
  setFn fi { name := "count_fold", params := [f, n, i, st], body, ret := sT }
  letpairM p fun f r => letpairM r fun c r₂ => letpairM r₂ fun i st => do
    let n ← fresh i32T
    return .letv n (.prim .clampLen [c]) (.call fi [f, n, i, st])

/-- `count_try (f, (n, (i, s)))` (SPEC §16): `f` at `i, …, len(n) − 1` while it answers `inl` of
the next state; its first `inr` is the answer, else `inl` of the last state. -/
def genCountTry (fT sT eT : LTy) (p : Var) : CM Tm := do
  let fi ← reserveFn "count_try"
  let f ← fresh fT; let n ← fresh i32T; let i ← fresh i32T; let st ← fresh sT
  let rT : LTy := .sum sT eT
  let body ← dup i fun i i₁ => dup n fun n n₁ =>
    ifLt i₁ n₁
      (dup f fun f f' => dup i fun i i' => do
        let q ← fresh (.pair i32T sT)
        let r ← fresh rT
        let s' ← fresh sT; let e ← fresh eT
        return .letv q (.pair i' st) (.letv r (.app f' q)
          (.case r s' (← add1 i fun i₂ => pure (.call fi [f, n, i₂, s']))
            e (.drop f (.drop n (.drop i (.inj true e)))))))
      (pure (.drop f (.drop n (.drop i (.inj false st)))))
  setFn fi { name := "count_try", params := [f, n, i, st], body, ret := rT }
  letpairM p fun f r => letpairM r fun c r₂ => letpairM r₂ fun i st => do
    let n ← fresh i32T
    return .letv n (.prim .clampLen [c]) (.call fi [f, n, i, st])

/-- A borrow `withbor`'s way (SPEC §1): `(x, f [] x)`, the owner `src` lent as the borrow the
callback `cb` (a `∀` closure, its instantiation erased: SPEC §44) is given, by `op` (`lend`,
`relend`). -/
def genLend (op : Op) (src : Var) (cbT : LTy) (call : Var → CM Tm) : CM Tm := do
  let (some bT, rT) ← answerOf cbT | throw "LIR: a borrow's callback takes no borrow"
  let pr ← fresh (.pair (← tyOf src) bT)
  let o ← freshLike src; let b ← fresh bT
  let r ← fresh rT
  readFact "lend"
  return .letv pr (.prim op [src]) (.letpair o b pr (.letv r (← call b) (.pair o r)))

/-- The call of a borrow's callback `cb` on `b`: `cb [] b`, its instantiation erased (SPEC §44). -/
def callCb (cb : Var) (b : Var) : CM Tm := pure (.app cb b)

/-- `withload x f` (SPEC §1): `f () (load x)`, the contents read at the callback's argument type. -/
def genWithload (x : Var) (cbT : LTy) (call : Var → CM Tm) : CM Tm := do
  let (some vT, _) ← answerOf cbT | throw "LIR: withload's callback takes no argument"
  let v ← fresh vT
  return .letv v (.prim .load [x]) (← call v)

/-- `withswap x f` (SPEC §1): `let (y, z) = f (load x); store x y; (x, z)`, the load's copy and the
store's drop of the old contents cancelled: the contents moved out, and `y` moved in. -/
def genWithswap (m : Var) (fT : LTy) (call : Var → CM Tm) : CM Tm := do
  let (some aT, rT) ← answerOf fT | throw "LIR: withswap's function takes no argument"
  let .pair yT zT := rT.peel | throw "LIR: withswap's function answers no pair"
  let mT ← tyOf m
  let pr ← fresh (.pair mT aT)
  let m' ← fresh mT; let old ← fresh aT
  let r ← fresh rT
  let y ← fresh yT; let z ← fresh zT
  let m'' ← fresh mT
  return .letv pr (.prim .take [m]) (.letpair m' old pr (.letv r (← call old)
    (.letpair y z r (.letv m'' (.prim .put [m', y]) (.pair m'' z)))))

/-! ### Folds (SPEC §6)

`fold_own`, `fold_reuse` and `fold_imm` read their node's shape `F` and result `R`: the fold is a
function generated for the node, recursive on its own, which traverses the unrolled value at the
shape (`travO`, `travR`, `travK` of `Core/`) and applies the algebra. -/

inductive FoldKind where
  | own | reuse | imm
  deriving BEq

/-- The traversal of `w` (of the unrolling at the shape `F`), the recursive positions by `recur`:
its term and its type. `g` is the algebra, copied for each recursive call. -/
def travF (k : FoldKind) (recV recL : Nat) (g : Var) : FShape → Var → CM (Tm × LTy)
  | .leaf _, w => return (.var w, ← tyOf w)
  | .refX, w => do
    let (_, rT) ← answerOf' (← tyOf g)
    let g' ← freshLike g
    match k with
    | .own => do
      let .ref cT := (← tyOf w).peel | throw "LIR: fold_own at a `Ref X` that is not a cell"
      let c ← fresh cT
      return (.copy g g' (.letv c (.prim .free [w]) (.call recV [g', c])), rT)
    | .reuse => do
      let .ref cT := (← tyOf w).peel | throw "LIR: fold_reuse at a `Ref X` that is not a cell"
      let u ← fresh .unit
      let pr ← fresh (.pair (.ref .unit) cT)
      let c ← fresh (.ref .unit); let v ← fresh cT
      let r ← fresh rT
      return (.copy g g' (.letv u .unit (.letv pr (.prim .swap [w, u]) (.letpair c v pr
        (.letv r (.call recV [g', v]) (.pair c r))))), .pair (.ref .unit) rT)
    | .imm => return (.copy g g' (.call recL [g', w]), rT)
  | .varX, w => do
    let (_, rT) ← answerOf' (← tyOf g)
    let g' ← freshLike g
    return (.copy g g' (.call recV [g', w]), rT)
  | .tensor F G, w => do
    let .pair aT bT := (← tyOf w).peel | throw "LIR: a fold's shape `⊗` at a non-pair"
    let a ← fresh aT; let b ← fresh bT
    let (ta, ra) ← travF k recV recL g F a
    let (tb, rb) ← travF k recV recL g G b
    let x ← fresh ra; let y ← fresh rb
    return (.letpair a b w (.letv x ta (.letv y tb (.pair x y))), .pair ra rb)
  | .sum F G, w => do
    let .sum aT bT := (← tyOf w).peel | throw "LIR: a fold's shape `⊕` at a non-sum"
    let a ← fresh aT; let b ← fresh bT
    let (ta, ra) ← travF k recV recL g F a
    let (tb, rb) ← travF k recV recL g G b
    let x ← fresh ra; let y ← fresh rb
    return (.case w a (.letv x ta (.inj false x)) b (.letv y tb (.inj true y)), .sum ra rb)
where
  /-- The algebra's answer (its `∀` at `fold_imm` erased: SPEC §44). -/
  answerOf' (gT : LTy) : CM (Option LTy × LTy) := answerOf gT

/-- The recursive functions of a fold at the node's shape `F`: on a value of `μX. T` (`recV`), and
at `fold_imm` on a borrow of one (`recL`, whose cell's contents it reads as `Imm̲`). `muT` is the
type of the values `recV` folds, `gT` the algebra's. -/
def genFoldFns (k : FoldKind) (F : FShape) (muT cellT gT : LTy) : CM (Nat × Nat) := do
  let recV ← reserveFn "fold"
  let recL ← if k == .imm then reserveFn "fold_imm" else pure recV
  let .mu body := muT.peel | throw s!"LIR: a fold over a non-μ type: {muT}"
  let g ← fresh gT
  let u ← fresh muT
  let w ← fresh body.unrollMu
  let (tt, rT) ← travF k recV recL g F w
  let r ← fresh rT
  let ans := Tm.app g r
  let (_, R) ← answerOf gT
  setFn recV { name := "fold", params := [g, u], ret := R,
               body := .letv w (.prim .unroll [u]) (.letv r tt ans) }
  if k == .imm then
    let g₂ ← fresh gT
    let l ← fresh (.imm cellT)
    -- `fold_imm`'s values are `Imm̲` of the structure: the borrow's contents read as `muT`.
    let v ← fresh muT
    setFn recL { name := "fold_imm", params := [g₂, l], ret := R,
                 body := .letv v (.prim .load [l]) (.call recV [g₂, v]) }
  return (recV, recL)

/-! ### Codata (SPEC §7)

`unfold`'s node gives its body `C` and state `S`. `unfold g s` is a closure over `(g, s)` of a code
for `νX. C`; an observation runs `g s` along its path (`nodeV`'s `childV`, the step run at the
observation's leaf) and maps each state at an `X` of the answer to `unfold g` of it (`mapV`). -/

/-- The type variable `n` occurs at a `⊗`/`⊕` position of `a`. -/
def occursAt (n : Nat) : LTy → Bool
  | .tvar m => m == n
  | .pair a b | .sum a b => occursAt n a || occursAt n b
  | .bang a => occursAt n a
  | _ => false

def occ0 (a : LTy) : Bool := occursAt 0 a

/-- `t` (the step's type at `a`) with each state at an `X` of `a` replaced by the codata type; `t`
read through a `!` (`peel`) where `a` is taken apart, and a `!` of `a` read through. -/
def substState : LTy → LTy → LTy → LTy
  | .tvar 0, _, c => c
  | .bang a, t, c => substState a t c
  | .pair a b, t, c => match t.peel with
    | .pair x y => .pair (substState a x c) (substState b y c)
    | _ => t
  | .sum a b, t, c => match t.peel with
    | .sum x y => .sum (substState a x c) (substState b y c)
    | _ => t
  | _, t, _ => t

/-- A step of an observation's path: a component, or an argument. -/
inductive PathStep where
  | sel (j : Nat)
  | arg (x : Var)

mutual
/-- The answer of the observation tree `C` at the path `steps`, over the step `g` and the state
`s` (consumed): at an `F A` leaf the step run and its states mapped; else a closure of the rest of
the tree. `obs` is the code of `unfold g s` itself. -/
def nodeAt (fuel : Nat) (obs : Nat) (C : LCTy) (Cv : CTy) (steps : List PathStep) (g s : Var) :
    CM Tm := do
  match fuel with
  | 0 => throw "LIR: an observation tree too deep"
  | fuel + 1 =>
  match C, stripAll Cv with
  | .ret A, Cv' => do
    let (_, stT) ← answerOf (← tyOf g)
    let g' ← freshLike g
    let st ← fresh stT
    -- An observation at an outcome (an effectful step, SPEC §49): the step's outcome is a call
    -- point of the observation's machine, its value mapped by a join.
    let nu ← nuTyOf obs
    let leaf? ← match effParts Cv' with
      | some (S, Rv) => do
        match ← outInfoTy (LTy.subst 0 nu A) S with
        | some F => pure (some (S, Rv, F))
        | none => pure none
      | none => pure none
    match leaf? with
    | some (S, Rv, F) =>
      withMachine F do
        let rPre ← vty Rv
        let t ← runPath fuel st steps fun r => do
          let some M ← outInfoTy (← tyOf r) S | throw "LIR: an observation's step at no outcome"
          let fnMap ← reserveFn "observe map"
          let gP ← freshLike g
          let xP ← fresh M.r
          let v ← fresh F.r
          let mb ← mapStates fuel obs rPre gP xP
          setFn fnMap { name := "observe map", params := [gP, xP], body := .letv v mb (← outValue F v),
                        ret := F.ty }
          readFact "unfoldN:machine"
          pointK [.letF fnMap 1] [g] (.var r) M
        return .copy g g' (.letv st (.app g' s) t)
    | none =>
      let t ← runPath fuel st steps fun r => mapStates fuel obs A g r
      return .copy g g' (.letv st (.app g' s) t)
  | .amp C₁ C₂, Cv' => do
    let (Cv₁, Cv₂) ← match Cv' with
      | .amp a b => pure (a, b)
      | _ => throw "LIR: an observation tree's `&` at a type that is not one"
    let nu ← nuTyOf obs
    let k : LCTy := LCTy.subst 0 nu (.amp C₁ C₂)
    let ctx : Ctx := [some g, some s] ++ (steps.filterMap fun | .arg x => some (some x) | _ => none)
    let r₁ ← resOf (LCTy.subst 0 nu C₁)
    let r₂ ← resOf (LCTy.subst 0 nu C₂)
    mkAmp "observe" ctx k [r₁, r₂] [
      fun ctx' => bodyAt fuel obs C₁ Cv₁ (steps ++ [.sel 0]) ctx',
      fun ctx' => bodyAt fuel obs C₂ Cv₂ (steps ++ [.sel 1]) ctx']
  | .arr A D, Cv' => do
    let Dv ← match Cv' with
      | .arr _ d => pure d
      | _ => throw "LIR: an observation tree's `⊸` at a type that is not one"
    let ctx : Ctx := [some g, some s] ++ (steps.filterMap fun | .arg x => some (some x) | _ => none)
    let nu ← nuTyOf obs
    mkClos "observe" ctx (LCTy.subst 0 nu (.arr A D)) (some (LTy.subst 0 nu A))
      (← resOf (LCTy.subst 0 nu D)) fun ctx' => do
      match ctx' with
      | some x :: rest => bodyAt fuel obs D Dv (steps ++ [.arg x]) (rest ++ [some x])
      | _ => throw "LIR: an observation's argument"
  | C, _ => throw s!"LIR: an observation tree at {C}"
/-- `nodeAt` in a code whose context holds `g`, `s` and the path's arguments, in that order. -/
def bodyAt (fuel : Nat) (obs : Nat) (C : LCTy) (Cv : CTy) (steps : List PathStep) (ctx : Ctx) :
    CM Tm := do
  match fuel, ctx with
  | 0, _ => throw "LIR: an observation tree too deep"
  | fuel + 1, some g :: some s :: args =>
    -- The path's arguments, renamed to the code's parameters.
    let mut as := args.filterMap id
    let mut steps' : Array PathStep := #[]
    for st in steps do
      match st, as with
      | .arg _, a :: rest => steps' := steps'.push (.arg a); as := rest
      | .sel j, _ => steps' := steps'.push (.sel j)
      | .arg _, [] => throw "LIR: an observation's arguments"
    nodeAt fuel obs C Cv steps'.toList g s
  | _, _ => throw "LIR: an observation's environment"
/-- Run the path on the step's answer `st`. -/
def runPath (fuel : Nat) (st : Var) : List PathStep → (Var → CM Tm) → CM Tm
  | [], k => k st
  | .sel j :: rest, k => do
    let t ← selTy (← tyOf st) j
    bindTm (.sel st j) t fun r => runPath fuel r rest k
  | .arg x :: rest, k => do
    let (_, t) ← answerOf (← tyOf st)
    bindTm (.app st x) t fun r => runPath fuel r rest k
/-- `map_A (unfold g) w`: each state at an `X` (`#0`) of `A` the codata `unfold g` of it; `g`
consumed. -/
def mapStates (fuel : Nat) (obs : Nat) (A : LTy) (g w : Var) : CM Tm := do
  match fuel with
  | 0 => throw "LIR: a codata answer too deep"
  | fuel + 1 =>
  match A with
  | .tvar 0 => return .clos obs [g, w]
  | .bang a => mapStates fuel obs a g w
  | .pair a b => do
    if !(occ0 a || occ0 b) then return .drop g (.var w)
    letpairM w fun x y => dup g fun g g' => do
      let x' ← fresh (← mappedTy obs x a)
      let y' ← fresh (← mappedTy obs y b)
      return .letv x' (← mapStates fuel obs a g x) (.letv y' (← mapStates fuel obs b g' y) (.pair x' y'))
  | .sum a b => do
    if !(occ0 a || occ0 b) then return .drop g (.var w)
    let .sum xT yT := (← tyOf w).peel | throw "LIR: a codata answer's sum"
    let x ← fresh xT; let y ← fresh yT
    let x' ← fresh (← mappedTy obs x a)
    let y' ← fresh (← mappedTy obs y b)
    let g₁ ← freshLike g
    let g₂ ← freshLike g
    return .copy g g₁ (.copy g g₂ (.drop g (.case w
      x (.letv x' (← mapStates fuel obs a g₁ x) (.drop g₂ (.inj false x')))
      y (.letv y' (← mapStates fuel obs b g₂ y) (.drop g₁ (.inj true y'))))))
  | _ => return .drop g (.var w)
/-- The closure type of the codata of the code `obs`. -/
def nuTyOf (obs : Nat) : CM LTy := do
  match (← get).codes[obs]? with
  | some c => pure (.thunk c.ty)
  | none => throw "LIR: no codata code"
/-- The result type of an observation subtree. -/
def resOf : LCTy → CM LTy
  | .ret A => pure A
  | k => pure (.thunk k)
/-- The type of `w`'s value once mapped at `a`. -/
def mappedTy (obs : Nat) (w : Var) (a : LTy) : CM LTy := do
  let t ← tyOf w
  if occ0 a then return substState a t (← nuTyOf obs)
  return t
end

/-- The code of `unfold g s` at the body `C` (a `&` of observation trees, `CTy.NuOk`), its step
of type `gT` and state of type `sT`. -/
def genUnfold (C : LCTy) (Cv : CTy) (gT sT : LTy) : CM Nat := do
  let .amp C₁ C₂ := C | throw s!"LIR: unfold at a body that is not a `&`: {C}"
  let .amp Cv₁ Cv₂ := stripAll Cv | throw "LIR: unfold at a body that is not a `&`"
  let obs ← addCode { kind := .amp, fns := [], ty := .nu C }
  let nu : LTy := .thunk (.nu C)
  let mut fis : Array Nat := #[]
  for (Cj, Cvj, j) in [(C₁, Cv₁, 0), (C₂, Cv₂, 1)] do
    let g ← fresh gT
    let st ← fresh sT
    let fi ← reserveFn "observe"
    let b ← nodeAt 64 obs Cj Cvj [.sel j] g st
    setFn fi { name := "observe", params := [g, st], body := b, ret := ← resOf (LCTy.subst 0 nu Cj) }
    fis := fis.push fi
  modify fun s => { s with codes := s.codes.set! obs { kind := .amp, fns := fis.toList, ty := .nu C } }
  readFact "unfoldN:body"
  return obs

/-! ### `bounded_fix`  `[spec §48]` -/

/-- **`bounded_fix (s, (k, a))`** (SPEC §20): its machine step (`Head.boundedFix`), `s` run on
`(self_k, a)`, `self_0 = inl ()` and `self_{j+1} = inr (λx. bounded_fix (s, (j, x)))`, the budget
read unsigned and counted down. The self-reference is a closure of a code of its own over `s` and
`j`, whose call is `bounded_fix (s, (j, x))` again: a step that calls it in tail position is a loop
of tail calls with its budget, and one that calls it elsewhere a native recursion bounded by it
(§20, §21).  `[spec §48]` -/
def genFix (sT : LTy) (p : Var) : CM Tm := do
  let fi ← reserveFn "bounded_fix"
  let (some qT, rT) ← answerOf sT | throw "LIR: bounded_fix's step takes no argument"
  let .pair selfOT aT := qT.peel | throw "LIR: bounded_fix's step does not take `(self, a)`"
  let .sum _ selfT := selfOT.peel | throw "LIR: bounded_fix's self-reference is not `1 ⊕ U(A ⊸ C)`"
  let .thunk selfK := selfT.peel | throw "LIR: bounded_fix's self-reference is not a closure"
  let si ← reserveFn "bounded_fix self"
  let s₁ ← fresh sT; let k₁ ← fresh i32T; let x ← fresh aT
  setFn si { name := "bounded_fix self", params := [s₁, k₁, x], body := .call fi [s₁, k₁, x],
             ret := rT }
  let c ← addCode { kind := .lam, fns := [si], ty := selfK }
  let s ← fresh sT; let k ← fresh i32T; let a ← fresh aT
  let body ← dup s fun s s' => dup k fun k k' => lit32 0 fun z => do
    let self ← fresh selfOT
    let k₂ ← fresh i32T; let cl ← fresh selfT
    let yes : Tm := .letv k₂ (.prim .cntPred [k]) (.letv cl (.clos c [s', k₂]) (.inj true cl))
    let u ← fresh .unit
    let no : Tm := .drop s' (.drop k (.letv u .unit (.inj false u)))
    let test ← ifLt z k' (pure yes) (pure no)
    let q ← fresh qT
    return .letv self test (.letv q (.pair self a) (.app s q))
  setFn fi { name := "bounded_fix", params := [s, k, a], body, ret := rT }
  letpairM p fun s r => letpairM r fun k a => pure (.call fi [s, k, a])

/-! ### `Div`'s loops under the runtime  `[spec §62]` -/

/-- **`iterate (f, s)` under the runtime** (SPEC §14, §62): the loop `iterate`'s machine step
unrolls (`Head.iterate`, `iter_step`), its back edge a tail call. A turn `(f s).1` answers
`inl b`, finished, or `inr s′`, after which `iterate` ticks; the runtime answers the tick *next*
(`tail_resumes` at its clause `λ((), κ). κ next`; `drive_reify_tick`), so the turn's `case` on the
answer goes on with `iterate (f, s′)` (`iterK_inr`, `turnK_next`): the close `(f s′).2` is never
observed. `inl b` is the node's answer (`iterK_inl`). An abort of the row's payload `pay` is
handed on. `ansT` is the node's answer `B ⊕ R` at `pay`.  `[spec §62]` -/
def genIter (fT ansT : LTy) (pay : Pay) (p : Var) : CM Tm := do
  let fi ← reserveFn "iterate"
  let f ← fresh fT
  let (some sT, gT) ← answerOf fT | throw "LIR: iterate's step takes no state"
  let s ← fresh sT
  let xT ← selTy gT 0
  let valT ← match payTy pay, ansT with
    | none, t => pure t
    | some _, .sum t _ => pure t
    | some _, t => throw s!"LIR: iterate's answer at a row with aborts: {t}"
  let .sum _ _ := valT | throw s!"LIR: iterate's answer is not `B ⊕ R`: {valT}"
  let body ← dup f fun f f' => do
    let g ← fresh gT
    let x ← fresh xT
    let turn (o : Var) : CM Tm := do
      let .sum oB oS := (← tyOf o) | throw "LIR: iterate's turn does not answer `B ⊕ S`"
      let b ← fresh oB; let s' ← fresh oS
      let w ← fresh valT
      let done : Tm := match payTy pay with
        | none => .drop f (.letv w (.inj false b) (.var w))
        | some _ => .drop f (.letv w (.inj false b) (.inj false w))
      return .case o b done s' (.call fi [f, s'])
    let rest ← match payTy pay with
      | none => turn x
      | some pT => do
        let .sum oT _ := (← tyOf x) | throw "LIR: iterate's turn at a row with aborts"
        let o ← fresh oT; let e ← fresh pT
        pure (.case x o (← turn o) e (.drop f (.inj true e)))
    return .letv g (.app f' s) (.letv x (.sel g 0) rest)
  setFn fi { name := "iterate", params := [f, s], body, ret := ansT }
  letpairM p fun f s => pure (.call fi [f, s])

/-! ### The fallback at a stored loop: `tick` a machine operation  `[spec §64]`

Where the typed term has a `reify` other than `main`'s (a stored loop: the loop value of a stored
generator, of a block that loops, an argument at a loop's type), its observations suspend at each
tick, so `Div`'s `tick` is a machine operation of the program (`Backend2/Driver.lean`,
`machineOps`): a computation at a row that holds `Div` is a machine (SPEC §49), `iterate`'s back
edge suspends there (`genIterK`), and each `reify` is a drive of its computation's outcome with
`reifyH`'s clauses (`genReify`). -/

/-- The value `x` as an answer of `F_Σ A`: the outcome's value at a row with machine operations
(`O`), else `x`, or `inl x` beside the row's payload. -/
def valueAt (O : Option OutInfo) (p : Pay) (x : Var) : CM Tm := do
  match O with
  | some F => outValue F x
  | none => match payTy p with
    | none => pure (.var x)
    | some _ => pure (.inj false x)

/-- The type of `F_Σ A`'s answer at the row `S`: its outcome, or `A ⊕ P`, or `A`. -/
def answerTyAt (a : LTy) (S : Row) : CM (Option OutInfo × LTy) := do
  match ← outInfo? a S with
  | some F => pure (some F, F.ty)
  | none => pure (none, resTy a (← rowPay S))

/-- **`iterate (f, s)` at a row whose `tick` is a machine operation**  `[spec §14, §64]`: a
machine per node. A turn `(f s).1` answers `inl b`, finished with `inl b`, or `inr s′`, after which
`iterate` performs `tick`, a suspension; resumed with *next* it goes on with `iterate (f, s′)`, with *close*
it closes, `(f s′).2`, its residual `inr r` (`Head.iterate`, `iter_step`, `iterK_inr`,
`turnK_next`). The turn's own suspensions are the machine's, at a call point. -/
def genIterK (fT : LTy) (S : Row) (B R St : LTy) (p : Var) : CM Tm := do
  let valT : LTy := .sum B R
  let some F ← outInfo? valT S | throw "LIR: iterate at a row with no machine operation"
  let some Mt ← outInfo? (.sum B St) S | throw "LIR: iterate's turn"
  let some Mc ← outInfo? R S | throw "LIR: iterate's close"
  let fi ← reserveFn "iterate"
  let f ← fresh fT; let s ← fresh St
  let (_, gT) ← answerOf fT
  let body ← withMachine F do
    -- After the turn: finished, or a tick before the next.
    let fA ← reserveFn "iterate turn"
    let fA₁ ← fresh fT; let x ← fresh (.sum B St)
    -- After the tick: *next* goes on, *close* closes.
    let fB ← reserveFn "iterate tick"
    let fB₁ ← fresh fT; let s₁ ← fresh St; let n ← fresh boolT
    -- After the close: the residual.
    let fC ← reserveFn "iterate close"
    let r ← fresh R
    let rv ← fresh valT
    setFn fC { name := "iterate close", params := [r], body := .letv rv (.inj true r) (← outValue F rv),
               ret := F.ty }
    let un ← fresh .unit; let uc ← fresh .unit
    let g₁ ← fresh gT
    let closeTm ← pointK [.letF fC 0] [] (.letv g₁ (.app fB₁ s₁) (.sel g₁ 1)) Mc
    setFn fB { name := "iterate tick", params := [fB₁, s₁, n],
               body := .case n un (.drop un (.call fi [fB₁, s₁])) uc (.drop uc closeTm), ret := F.ty }
    let b ← fresh B; let v ← fresh valT; let s' ← fresh St; let u ← fresh .unit
    let tickTm ← performK [.letF fB 2] [fA₁, s'] (divName, 0) u
    setFn fA { name := "iterate turn", params := [fA₁, x],
               body := .case x b (.drop fA₁ (.letv v (.inj false b) (← outValue F v))) s'
                 (.letv u .unit tickTm), ret := F.ty }
    let f' ← freshLike f; let g ← fresh gT
    let turn ← pointK [.letF fA 1] [f] (.letv g (.app f' s) (.sel g 0)) Mt
    pure (.copy f f' turn)
  setFn fi { name := "iterate", params := [f, s], body, ret := F.ty }
  readFact "iterate:machine"
  letpairM p fun f s => pure (.call fi [f, s])

/-- **A stored loop's `reify`, a drive** (`reify_res`, SPEC §14, §64): a closure that runs its
computation `t ()`, whose outcome (at `tick, Σ`) the drive `reifyR`/`reifyC` takes apart
(`Core/DivReify.lean`): a value `inl b` is `inl b`, `inr r` the loop `closed r`; a suspension at
`tick` with its suspended computation `k` is the loop `tickLoop k` (`reifyC`), whose *next*
resumes `k` with *next* and drives again, and whose *close* resumes it with *close*, drives, and
closes what that answers (`closeKV`); a suspension at one of `Σ`'s machine operations suspends the
drive (forwarding), and an abort of `Σ`'s is handed on. The first answer is made a loop: `done b`
(`rkV`). `res : !U(B ⊸ F_Σ R)` is the residual of a result.  `[spec §64]` -/
def genReify (S : Row) (B R : VTy) (resV : Tm) (resT : LTy) (jT : LTy) : CM Tm := do
  let bT ← vty B; let rT ← vty R
  let loopT ← vty (.thunk (CTy.loopEff S B R))
  let .thunk loopK := loopT | throw "LIR: a loop's type"
  let (OB, nextT) ← answerTyAt (.sum bT loopT) S   -- `F_Σ(B ⊕ U Loop)`, an observation's answer
  let (OR, closeT) ← answerTyAt rT S               -- `F_Σ R`
  let (OL, mkT) ← answerTyAt loopT S               -- `F_Σ U Loop`, `reify`'s answer
  let pS ← rowPay S
  let some T ← outInfo? (.sum bT rT) (tickSig :: S) | throw "LIR: a reified computation's outcome"
  -- The loops' codes: `done b`, `closed r`, `tickLoop k`; one function per observation.
  let cDoneN ← reserveFn "done next"; let cDoneC ← reserveFn "done close"
  let cDone ← addCode { kind := .amp, fns := [cDoneN, cDoneC], ty := loopK }
  let cClN ← reserveFn "closed next"; let cClC ← reserveFn "closed close"
  let cCl ← addCode { kind := .amp, fns := [cClN, cClC], ty := loopK }
  let cTkN ← reserveFn "tick next"; let cTkC ← reserveFn "tick close"
  let cTk ← addCode { kind := .amp, fns := [cTkN, cTkC], ty := loopK }
  let drive ← reserveFn "reify drive"
  let kT ← kTyAt T (divName, 0)
  let wrapM (O : Option OutInfo) (act : CM Tm) : CM Tm := match O with
    | some F => withMachine F act
    | none => act
  -- `done b`: *next* finishes with `b`; *close* hands back `res b`.
  do
    let b ← fresh bT; let rs ← fresh resT; let w ← fresh (.sum bT loopT)
    setFn cDoneN { name := "done next", params := [b, rs], ret := nextT,
                   body := .drop rs (.letv w (.inj false b) (← wrapM OB (valueAt OB pS w))) }
    let b ← fresh bT; let rs ← fresh resT
    setFn cDoneC { name := "done close", params := [b, rs], ret := closeT, body := .app rs b }
  -- `closed r`: *next* skips, `closed r` again; *close* hands back `r`.
  do
    let r ← fresh rT; let l ← fresh loopT; let w ← fresh (.sum bT loopT)
    setFn cClN { name := "closed next", params := [r], ret := nextT,
                 body := .letv l (.clos cCl [r]) (.letv w (.inj true l) (← wrapM OB (valueAt OB pS w))) }
    let r ← fresh rT
    setFn cClC { name := "closed close", params := [r], ret := closeT, body := ← wrapM OR (valueAt OR pS r) }
  -- `tickLoop k`: *next* resumes `k` with *next* and drives; *close* resumes it with *close*,
  -- drives, and closes what that answers.
  do
    let k ← fresh kT; let rs ← fresh resT
    let kr ← fresh (← selTy kT 0); let o ← fresh T.ty
    let u ← fresh .unit; let nx ← fresh boolT
    setFn cTkN { name := "tick next", params := [k, rs], ret := nextT,
                 body := .letv kr (.sel k 0) (.letv u .unit (.letv nx (.inj false u)
                   (.letv o (.app kr nx) (.call drive [rs, o])))) }
    let k ← fresh kT; let rs ← fresh resT; let rs' ← freshLike rs
    let kr ← fresh (← selTy kT 0); let o ← fresh T.ty
    let u ← fresh .unit; let cl ← fresh boolT
    let x ← fresh nextT
    -- What the drive answers, closed: `inl b` hands back `res b`, `inr L` closes `L`.
    let closeOf (rs : Var) (x : Var) : CM Tm := do
      let b ← fresh bT; let l ← fresh loopT
      return .case x b (.app rs b) l (.drop rs (.sel l 1))
    let body ← match OB with
      | none => match payTy pS with
        | none => closeOf rs' x
        | some pT => do
          -- The drive's abort is handed on as the close's.
          let x' ← fresh (.sum bT loopT); let e ← fresh pT
          pure (Tm.case x x' (← closeOf rs' x') e (.drop rs' (.inj true e)))
      | some FB => do
        let some FR := OR | throw "LIR: a stored loop's close"
        withMachine FR do
          let fj ← reserveFn "tick close join"
          let rsJ ← fresh resT; let xJ ← fresh (.sum bT loopT)
          setFn fj { name := "tick close join", params := [rsJ, xJ], body := ← closeOf rsJ xJ,
                     ret := FR.ty }
          pointK [.letF fj 1] [rs'] (.var x) FB
    setFn cTkC { name := "tick close", params := [k, rs], ret := closeT,
                 body := .copy rs rs' (.letv kr (.sel k 0) (.letv u .unit (.letv cl (.inj true u)
                   (.letv o (.app kr cl) (.letv x (.call drive [rs, o]) body))))) }
  -- The drive: the reified computation's outcome `o` taken apart.
  do
    let rs ← fresh resT; let o ← fresh T.ty
    let dbody : CM Tm := do
      let w ← fresh T.body; let v ← fresh T.r; let ex ← fresh T.xTy
      let b ← fresh bT; let r ← fresh rT
      let l₁ ← fresh loopT; let w₁ ← fresh (.sum bT loopT); let w₂ ← fresh (.sum bT loopT)
      let valArm : Tm := .drop rs (.case v b (.letv w₁ (.inj false b) (← valueAt OB pS w₁))
        r (.letv l₁ (.clos cCl [r]) (.letv w₂ (.inj true l₁) (← valueAt OB pS w₂))))
      let abortArm (e : Var) : CM Tm := do
        match OB with
        | some FB =>
          let some pF := payTy FB.pay | throw "LIR: a stored loop's abort"
          let e' ← fresh pF
          return .drop rs (.letv e' (← coercePay T.pay FB.pay e fun x => pure (.var x)) (← outAbort FB e'))
        | none => return .drop rs (← coercePay T.pay pS e fun x => pure (.inj true x))
      let suspArms (sv : Var) : CM Tm := casePay T.sPay sv fun j pv => do
        let some (key, _, bK, cpK) := T.ms[j]? | throw "LIR: a suspension's summand"
        letpairM pv fun a k => do
          if key == (divName, 0) then
            -- `reifyC`: the loop at the tick.
            let l ← fresh loopT; let w ← fresh (.sum bT loopT)
            return .drop a (.letv l (.clos cTk [k, rs]) (.letv w (.inj true l) (← valueAt OB pS w)))
          let some FB := OB | throw "LIR: a stored loop forwards a suspension where its row has no machine operation"
          -- Forwarding: the drive suspends at `key`, resumed by resuming `k` and driving again.
          let mk ← newPoint key (some (T.kTy bK cpK)) cpK [resT] (some drive) [.dropF 1]
          let k' ← fresh (← kTyAt FB key)
          readFact "reify:forward"
          return .letv k' (.call mk [k, rs]) (← outSusp FB key a k')
      let exits ← match payTy T.pay with
        | none => suspArms ex
        | some pT => do
          let e ← fresh pT; let sv ← fresh T.sTy
          pure (Tm.case ex e (← abortArm e) sv (← suspArms sv))
      return .letv w (.prim .unroll [o]) (.case w v valArm ex exits)
    setFn drive { name := "reify drive", params := [rs, o], body := ← wrapM OB dbody, ret := nextT }
  -- The closure `reify_res`: `t ()` driven; its first answer made a loop (`rkV`).
  readFact "reify:stored, a drive"
  modify fun st => { st with erased := st.erased.insert "machine" (st.erased.getD "machine" 0 + 1) }
  let some (tkT, _) := (match jT.peel with
      | .thunk (.arr a k) => some (a, k)
      | _ => none) | throw s!"LIR: reify's type {jT}"
  let mkFn ← reserveFn "reify"
  let rs ← fresh resT; let tk ← fresh tkT
  let rs₁ ← freshLike rs; let o ← fresh T.ty; let x ← fresh nextT; let tu ← fresh .unit
  let rkOf (rs : Var) (x : Var) : CM Tm := do
    let b ← fresh bT; let l ← fresh loopT; let ld ← fresh loopT
    return .case x b (.letv ld (.clos cDone [b, rs]) (← valueAt OL pS ld)) l (.drop rs (← valueAt OL pS l))
  let mkBody ← match OB, OL with
    | none, none => match payTy pS with
      | none => do pure (Tm.letv tu .unit (.letv o (.app tk tu) (.letv x (.call drive [rs₁, o]) (← rkOf rs x))))
      | some pT => do
        let x' ← fresh (.sum bT loopT); let e ← fresh pT
        pure (Tm.letv tu .unit (.letv o (.app tk tu) (.letv x (.call drive [rs₁, o])
          (.case x x' (← rkOf rs x') e (.drop rs (.inj true e))))))
    | some FB, some FL => withMachine FL do
        let fj ← reserveFn "reify join"
        let rsJ ← fresh resT; let xJ ← fresh (.sum bT loopT)
        setFn fj { name := "reify join", params := [rsJ, xJ], body := ← rkOf rsJ xJ, ret := FL.ty }
        let pt ← pointK [.letF fj 1] [rs] (.call drive [rs₁, o]) FB
        pure (Tm.letv tu .unit (.letv o (.app tk tu) pt))
    | _, _ => throw "LIR: a stored loop's observations and its making at different rows"
  setFn mkFn { name := "reify", params := [rs, tk], body := .copy rs rs₁ mkBody, ret := mkT }
  let c ← addCode { kind := .lam, fns := [mkFn], ty := .arr tkT (.ret mkT) }
  let rv ← fresh resT
  return .letv rv resV (.clos c [rv])

/-- **`tick` under the runtime** (SPEC §62): its clause `λ((), κ). κ next` resumes in tail position
with the literal *next* (`tail_resumes`), and `drive_reify_tick` (`Core/DivDrive.lean`) is the
runtime's drive of `main`'s loop answering it so. The perform's argument `v` is dropped and *next*
is its value, at the row's payload `p`. -/
def tickTm (v : Var) (p : Pay) : CM Tm := do
  readFact "effPerform:tick at the runtime"
  modify fun st => { st with erased := st.erased.insert "perform" (st.erased.getD "perform" 0 + 1) }
  let u ← fresh .unit
  let nx ← fresh boolT
  match payTy p with
  | none => return .drop v (.letv u .unit (.inj false u))
  | some _ => return .drop v (.letv u .unit (.letv nx (.inj false u) (.inj false nx)))

/-- The tick's handler is the runtime (`divRt`), or the perform is outside the fragment. -/
def tickAtRuntime : CM Unit := do
  unless (← get).divRt do
    throw "LIR: a tick whose handler is not the runtime (a stored loop's `reify`) is outside the pure fragment"

/-! ### Destructors (SPEC §12)

`dtor A` (the checker's `dtorE A`, at an owned value that goes unused) is the destructor its type
gives (`Core/Dtor.lean`, `dtorAt`): nothing at a forgettable type, componentwise, a cell freed
and its contents destroyed, a `μ` by an owned fold, `close` at codata, `array_free` at an array.
A `μ` whose body is in the fold class `P` (SPEC §6) gets one function per closed `μ` type it
unrolls to (memoized by the type, so a binder nested in another, which names the outer one, is
its own function calling the outer's), and an array of recursive data one loop function that
destroys each element and then frees the buffer once (`freeArr`), as Rust drops a `Vec`. -/

mutual
/-- The destructor of `A` on `x`: a term of type `1`. -/
def genDtor (fuel : Nat) (A : VTy) (x : Var) : CM Tm := do
  match fuel with
  | 0 => throw "LIR: a destructor's type too deep"
  | f + 1 =>
  match A with
  | .tensor A B => letpairM x fun a b => do
      let u ← fresh .unit
      return .letv u (← genDtor f A a) (.drop u (← genDtor f B b))
  | .sum A B => do
    let .sum aT bT := (← tyOf x).peel | throw "LIR: a destructor's sum"
    let a ← fresh aT; let b ← fresh bT
    return .case x a (← genDtor f A a) b (← genDtor f B b)
  | .ref A => do
    let c ← fresh (← vty A)
    return .letv c (.prim .free [x]) (← genDtor f A c)
  | .box _ A => genDtor f A x
  | .mu T => do
    -- UNPROVED: that the function generated here from the type frees exactly the cells the
    -- kernel's destructor `dtorE (.mu T)` frees (`foldOwn`, or `foldOwnG` outside `FShape`, at
    -- results `1`), in some order, and observes nothing else. It is read off the type the
    -- checker's `dtor` node carries, not compiled from `dtorE`'s term; a mismatch shows as a leak
    -- or a double free in `live`, and as a disagreement with the source stage.
    let key := ppVT (.mu T) (← get).mach
    let fi ← match (← get).dtors[key]? with
      | some fi => pure fi
      | none => do
        let fi ← reserveFn "dtor"
        modify fun s => { s with dtors := s.dtors.insert key fi }
        let u ← fresh (← vty (.mu T))
        let w ← fresh (← vty (VTy.inst (.mu T) T))
        let body ← dtorShape f fi (toFShape T) T w
        setFn fi { name := "dtor", params := [u], ret := .unit,
                   body := .letv w (.prim .unroll [u]) body }
        pure fi
    return .call fi [x]
  | .thunk (.nu (.amp _ (.ret R))) => do
    let rT ← selTy (← tyOf x) 1
    let r ← fresh rT
    return .letv r (.sel x 1) (← genDtor f R r)
  | .thunk C => do
    if let .nu (.amp _ D) := stripAll C then
      if (← outInfoC D).isSome then
        throw "LIR: the destructor of codata whose close may suspend is outside the fragment"
    return .sel x 1
  | .fam (.ref A) => do
    let aT ← tyOf x
    let .fam (.ref eT) := aT.peel | throw "LIR: an array's destructor"
    let fi ← reserveFn "array_dtor"
    let a ← fresh aT; let i ← fresh i32T; let n ← fresh i32T
    let body ← dup i fun i i₁ => dup n fun n n₁ =>
      ifLt i₁ n₁
        (dup i fun i i' => do
          let pr ← fresh (.pair aT eT)
          let a' ← fresh aT; let v' ← fresh eT
          let u ← fresh .unit
          return .letv pr (.prim .slotTake [a, i']) (.letpair a' v' pr
            (.letv u (← genDtor f A v') (.drop u (← add1 i fun i₂ => pure (.call fi [a', i₂, n]))))))
        (do return .drop i (.drop n (.prim .freeArr [a])))
    setFn fi { name := "array_dtor", params := [a, i, n], body, ret := .unit }
    let pr ← fresh (.pair aT i32T)
    let a' ← fresh aT; let n' ← fresh i32T
    return .letv pr (.prim .size [x]) (.letpair a' n' pr (← lit32 0 fun z => pure (.call fi [a', z, n'])))
  | _ => return .drop x .unit

/-- The destructor at a `μ` body's shape, recursive positions by the type's own destructor `fi`. -/
def dtorShape (fuel : Nat) (fi : Nat) (F : FShape) (T : VTy) (w : Var) : CM Tm := do
  match fuel with
  | 0 => throw "LIR: a destructor's shape too deep"
  | f + 1 =>
  match F with
  | .leaf A => genDtor f (VTy.inst (.mu T) A) w
  | .refX => do
    let c ← fresh (← vty (.mu T))
    return .letv c (.prim .free [w]) (.call fi [c])
  | .varX => return .call fi [w]
  | .tensor F G => letpairM w fun a b => do
      let u ← fresh .unit
      return .letv u (← dtorShape f fi F T a) (.drop u (← dtorShape f fi G T b))
  | .sum F G => do
    let .sum aT bT := (← tyOf w).peel | throw "LIR: a destructor's sum"
    let a ← fresh aT; let b ← fresh bT
    return .case w a (← dtorShape f fi F T a) b (← dtorShape f fi G T b)
end

/-! ### Blocks (SPEC §5, §42) -/

/-- A block's allocation at its shape: each leaf a cell. -/
def allocTree (v : Var) (rT : LTy) (σ : Shape) : CM Tm := do
  match rT.peel, σ with
  | .pair a b, .node σ₁ σ₂ => letpairM v fun x y => do
      let x' ← fresh a; let y' ← fresh b
      return .letv x' (← allocTree x a σ₁) (.letv y' (← allocTree y b σ₂) (.pair x' y'))
  | .ref _, .leaf A => return .prim (.alloc (← classOf A)) [v]
  | t, _ => throw s!"LIR: a block's handle at {t}"

/-- A block's release at its shape. -/
def freeTree (v : Var) (vT : LTy) : CM Tm := do
  match (← tyOf v).peel, vT with
  | .pair _ _, .pair a b => letpairM v fun x y => do
      let x' ← fresh a; let y' ← fresh b
      return .letv x' (← freeTree x a) (.letv y' (← freeTree y b) (.pair x' y'))
  | .ref _, _ => return .prim .free [v]
  | _, .bang b => freeTree v b
  | t, _ => throw s!"LIR: a block's handle at {t}"

/-- Lend each leaf of the handle `v` at the borrow tree `bT`: the term binds `k`'s owners and
borrows. -/
def lendTree (m : Bool) (v : Var) (bT : LTy) (k : Var → Var → CM Tm) : CM Tm := do
  match (← tyOf v).peel, bT with
  | .pair _ _, .bang b => lendTree m v b k
  | .pair _ _, .pair ba bb =>
    letpairM v (fun x y => lendTree m x ba (fun ox bx => lendTree m y bb (fun oy byy => do
      let o ← fresh (.pair (← tyOf ox) (← tyOf oy))
      let b ← fresh (.pair ba bb)
      return .letv o (.pair ox oy) (.letv b (.pair bx byy) (← k o b)))))
  | _, _ =>
    let vT ← tyOf v
    let pr ← fresh (.pair vT bT)
    let o ← fresh vT; let b ← fresh bT
    return .letv pr (.prim (.lend m) [v]) (.letpair o b pr (← k o b))

/-- A block borrow (`withborS`, `withborF2`): every leaf lent, the borrows handed to the callback at
one lifetime; `(handle, answer)`. -/
def genLendTree (m : Bool) (src : Var) (cbT : LTy) (call : Var → CM Tm) : CM Tm := do
  let (some bT, rT) ← answerOf cbT | throw "LIR: a block borrow's callback takes no borrow"
  readFact "lend"
  lendTree m src bT fun o b => do
    let r ← fresh rT
    return .letv r (← call b) (.pair o r)

/-! ### Externs -/

/-- An I/O operation's closure at its extern's type: `λm. op m`, its `Λ`s erased (SPEC §44). -/
def ioClos (fuel : Nat) (k : IOKind) (t : LTy) : CM Tm := do
  match fuel, t.peel with
  | 0, _ => throw "LIR: an extern's type too deep"
  | _, .thunk (.arr a (.ret b)) =>
    mkClos "extern" [] (.arr a (.ret b)) (some a) b fun ctx => do
      match ctx with
      | some p :: _ => return .prim (.io k) [p]
      | _ => throw "LIR: an extern's argument"
  | _, _ => throw s!"LIR: an I/O extern at {t}"

/-! ### The conversion -/

/-- The value a closure of `k` answers when it is run. -/
def repK : LCTy → CM LTy
  | .ret a => pure a
  | .arr _ k => repK k
  | .top => pure .unit
  | k => pure (.thunk k)

/-- The type of a constant's answer after `n` of its arguments. -/
def satTy (t : LTy) : Nat → CM LTy
  | 0 => pure t
  | n + 1 => do
    let (_, r) ← answerOf t
    satTy r n

/-- The literal tables' code (`TExpr.litFn`), made once: `λi. byte i` over the environment
`(off, n)`, the `n` bytes at `off` in the program's data, `0` past the end.  `[spec §45]` -/
def litCode : CM Nat := do
  if let some c := (← get).lits then return c
  let fi ← reserveFn "literal"
  let o ← fresh i32T; let n ← fresh i32T; let i ← fresh i32T
  setFn fi { name := "literal", params := [o, n, i], body := .prim .litByte [o, n, i], ret := .int .w8 }
  let c ← addCode { kind := .lam, fns := [fi], ty := .arr i32T (.ret (.int .w8)) }
  modify fun s => { s with lits := some c }
  return c

/-- The number of arguments a constant takes before its operation runs; `none` at a node that is
not a constant. -/
def constArity : TExpr → Option Nat
  | .alloc .. | .free .. | .copy .. | .forgetImm .. | .forgetMut .. | .forgetUnk .. | .hostOp ..
  | .arrNew .. | .arrFree .. | .arrSize .. | .arrReplace .. | .arrLen .. | .arrGet .. | .arrCopy ..
  | .arrForget .. | .countFold .. | .countTry .. | .sliceGetM .. | .sliceLenM .. | .sliceSplitI ..
  | .sliceSplitM .. | .sliceReplaceM .. | .sliceSwapM .. | .dtor .. | .foldImm .. | .foldOwn ..
  | .foldOwnG .. | .foldReuse .. | .unfoldN .. | .allocS .. | .freeS .. | .boundedFix .. | .iterate .. => some 1
  | .swap .. | .withbor1 .. | .withbor2 .. | .withbor3 .. | .withload .. | .withswap ..
  | .sliceBorrowM .. | .sliceBorrowI .. | .withborSM .. | .withborSI .. | .withborF2M ..
  | .withborF2I .. | .withbor1U .. | .withbor2U .. | .withbor3U .. | .withloadU ..
  | .sliceBorrowMU .. | .sliceBorrowIU .. => some 2
  | .sliceEmptyI .. | .sliceEmptyM .. | .arrEmpty .. => some 0
  | _ => none

/-- The nodes whose value is their child's: `ret`, a thunk of a λ-value, dereliction, the lifetime
box and the lifetime coercions, `ν`'s two coercions. -/
def transparent? : TExpr → Option TExpr
  | .bangE _ _ _ t | .boxI _ _ _ _ t | .boxE _ _ _ _ t | .immSub _ _ _ _ _ t | .mutSub _ _ _ _ _ t
  | .ofRet _ _ _ t | .ret _ _ _ t | .thunkV _ _ _ t | .bangThunkV _ _ _ t | .nuIn _ _ _ t
  | .nuOut _ _ _ t => some t
  -- The derived nodes over a term the conversion reads as it reads the term (SPEC §57).
  | .lendScope _ _ _ t | .litView _ _ t | .unfoldStep _ _ t => some t
  | _ => none

/-- A function position's head through transparent nodes, and through a `use` whose body is a
constant (nothing is shared there). -/
def headOf : Nat → TExpr → TExpr
  | 0, t => t
  | f + 1, t => match transparent? t with
    | some c => headOf f c
    | none => match t with
      | .use _ _ _ _ _ _ b =>
        let h := headOf f b
        if (constArity h).isSome then h else t
      | _ => t

/-- The nodes of a typed term, to a bound. -/
def tsize : Nat → TExpr → Nat
  | 0, _ => 0
  | f + 1, t => 1 + (t.children.map (fun (_, c) => tsize f c)).foldl (· + ·) 0

/-- A `use` body small enough to be converted at its use when it is applied there: the old
backend's substitution of a small definition, with no copy of a large one (#509). -/
def inlineBound : Nat := 200

/-- A function position that is a λ once its lifetime abstractions are instantiated: `allEV`/`allE`
of `allI`, through transparent nodes and a small `use`; the λ, and the dead slots the `allI`s push.
Applying it is the λ's body at the arguments, with no closure made. -/
def lamOf : Nat → TExpr → Option (Nat × TExpr)
  | 0, _ => none
  | f + 1, t => match transparent? t with
    | some c => lamOf f c
    | none => match t with
      | .lam .. => some (0, t)
      | .use _ _ _ _ _ _ b => if tsize (inlineBound + 1) b ≤ inlineBound then lamOf f b else none
      | .allEV _ _ _ _ _ _ c | .allE _ _ _ _ _ _ c => match allIOf f c with
        | some body => (lamOf f body).map fun (k, l) => (k + 1, l)
        | none => none
      | _ => none
where
  allIOf : Nat → TExpr → Option TExpr
    | 0, _ => none
    | f + 1, t => match transparent? t with
      | some c => allIOf f c
      | none => match t with
        | .allI _ _ _ _ _ _ body => some body
        | .use _ _ _ _ _ _ b => if tsize (inlineBound + 1) b ≤ inlineBound then allIOf f b else none
        | _ => none

/-- The arguments of a spine of call-by-value applications, outermost first, with each split's
masks; and the function. -/
def spineOf : Nat → TExpr → List (Masks × TExpr) × TExpr
  | f + 1, .lolliE _ _ _ _ u ta tf =>
    let (as, h) := spineOf f tf
    ((u, ta) :: as, h)
  | _, t => ([], t)

mutual
/-- The type holds a closure. -/
def holdsClos : Nat → LTy → Bool
  | 0, _ => true
  | f + 1, t => match t with
    | .thunk _ => true
    | .pair a b | .sum a b => holdsClos f a || holdsClos f b
    | .mu a | .ref a | .imm a | .mut a | .fam a | .bang a => holdsClos f a
    | _ => false
/-- A value of the type takes a closure as an argument: a higher-order function, or a value holding
one. -/
def takesClos : Nat → LTy → Bool
  | 0, _ => true
  | f + 1, t => match t with
    | .thunk k => takesClosK f k
    | .pair a b | .sum a b => takesClos f a || takesClos f b
    | .bang a => takesClos f a
    | _ => false
def takesClosK : Nat → LCTy → Bool
  | 0, _ => true
  | f + 1, k => match k with
    | .arr a k => holdsClos f a || takesClosK f k
    | .nu k => takesClosK f k
    | .amp k₁ k₂ => takesClosK f k₁ || takesClosK f k₂
    | .ret a => takesClos f a
    | .top => false
end

/-- The key of a `use`: the declaration, its type arguments and the elaborator's key. -/
def useKey (decl : Nat) (targs : List VTy) (info : TInfo) (j : Jdg) (ms : MachSet) : String :=
  s!"{decl}|{", ".intercalate (targs.map (ppVT · ms))}|{reprStr info.key}|{ppJ j ms}"

/-- A scope of a `use` template in the copy being made (`renameTm`): a scope of its own. -/
def copyScope (s : Nat) : CM Nat := do
  match (← get).scopeCopy[s]? with
  | some s' => pure s'
  | none =>
    let s' ← newScope
    modify fun st => { st with scopeCopy := st.scopeCopy.insert s s' }
    pure s'

/-- Rename every variable a term binds to a fresh one, and its free ones by `m`; each lend scope a
scope of its own, its owner the renamed variable. -/
def renameTm (m : Std.HashMap Var Var) : Tm → CM Tm
  | .var x => return .var (m.getD x x)
  | .unit => pure .unit
  | .lit c => pure (.lit c)
  | .pair a b => return .pair (m.getD a a) (m.getD b b)
  | .inj r a => return .inj r (m.getD a a)
  | .clos c env => return .clos c (env.map fun x => m.getD x x)
  | .app f a => return .app (m.getD f f) (m.getD a a)
  | .app0 f => return .app0 (m.getD f f)
  | .sel f j => return .sel (m.getD f f) j
  | .call fn as => return .call fn (as.map fun x => m.getD x x)
  | .prim op as => do
    let op ← match op with
      | .allocLent s cls => pure (Op.allocLent (← copyScope s) cls)
      | op => pure op
    return .prim op (as.map fun x => m.getD x x)
  | .letv x e b => do
    let x' ← freshLike x
    return .letv x' (← renameTm m e) (← renameTm (m.insert x x') b)
  | .letpair x y p b => do
    let x' ← freshLike x; let y' ← freshLike y
    if let some s := (← get).owners[x]? then
      let s' ← copyScope s
      modify fun st => { st with owners := st.owners.insert x' s' }
    return .letpair x' y' (m.getD p p) (← renameTm ((m.insert x x').insert y y') b)
  | .case s x b₁ y b₂ => do
    let x' ← freshLike x; let y' ← freshLike y
    return .case (m.getD s s) x' (← renameTm (m.insert x x') b₁) y' (← renameTm (m.insert y y') b₂)
  | .absurd s => return .absurd (m.getD s s)
  | .copy x x' b => do
    let x'' ← freshLike x'
    return .copy (m.getD x x) x'' (← renameTm (m.insert x' x'') b)
  | .drop x b => return .drop (m.getD x x) (← renameTm m b)

/-- **`κ`'s code** at the clause `idx` of a drive (SPEC §49): a `&` closure over the handled
computation's suspended `k` and the handler's values, `kT` its type (`kTy`). Its resume entry
resumes `k` with the answer and drives the outcome again (`driveFn`): the handler is deep. Its
cancel entry cancels `k`, every frame of the region unwound, and answers at `κ`'s cancel type
(`cancelTy`: the outcome `cM` or the payload `cPay`); at `⊤` (a linear `κ`) it is never run.

With `swap` (SPEC §52), the last handler value is the site's stack, made current around each run
of `k` and freed by a cancel. With `region` too (the site's tag), `κ`'s environment is that stack
alone: `k` and the other handler values are in the stack's `κ` region (`Op.kappaTake`), which the
drive writes when the computation suspends there again. -/
def genKap (n : UInt32) (idx : Nat) (kT : LTy) (T : OutInfo) (outTy : LTy) (driveFn : Nat)
    (hvTys : List LTy) (cM : Option OutInfo) (cPay : Pay) (region : Option Nat := none)
    (swap : Bool := false) : CM Nat := do
  let .thunk kL := kT.peel | throw s!"LIR: κ's type {kT}"
  let .amp (.arr bT (.ret oT)) cK := kL | throw s!"LIR: κ's type {kT}"
  unless oT.sameRep outTy do throw s!"LIR: κ resumes to {oT}, the handler answers {outTy}"
  let (_, cpIn) ← opAnswer T (n, idx.toUInt32)
  let kIn ← kTyAt T (n, idx.toUInt32)
  let hTy : LTy := .int .w64
  let kapR ← reserveFn s!"kappa {n}.{idx}"
  let rc ← addCode { kind := .lam, fns := [kapR], ty := .arr bT (.ret oT) }
  let kres ← reserveFn s!"kappa {n}.{idx} resume entry"
  let kcan ← reserveFn s!"kappa {n}.{idx} cancel"
  let kc ← addCode { kind := .amp, fns := [kres, kcan], ty := kL }
  -- The environment's variables, and `k` and the handler's values out of them: with a region, the
  -- stack alone, the rest taken out of its region.
  let envOf (body : Var → List Var → CM Tm) : CM (List Var × Tm) := do
    match region with
    | some s =>
      let rTys := kIn :: hvTys.dropLast
      let stT := tupleTy rTys
      let h ← fresh hTy
      let pr ← fresh (.pair hTy stT); let h' ← fresh hTy; let st ← fresh stT
      let b ← untuple st rTys fun xs => match xs with
        | k :: hv => body k (hv ++ [h'])
        | [] => throw "LIR: κ's region"
      return ([h], .letv pr (.prim (.kappaTake s) [h]) (.letpair h' st pr b))
    | none =>
      let k ← fresh kIn; let hv ← hvTys.mapM fresh
      return (k :: hv, ← body k hv)
  let env₀ : List LTy := if region.isSome then [hTy] else kIn :: hvTys
  let e₀ ← env₀.mapM fresh
  setFn kres { name := s!"kappa {n}.{idx} resume entry", params := e₀,
               body := .clos rc e₀, ret := .thunk (.arr bT (.ret oT)) }
  -- The site's stack made current around each run of `k` (`run` binds the run, `rest` gets the
  -- stack it answers).
  let aroundK (hv : List Var) (run : Tm → Tm) (rest : List Var → Option Var → CM Tm) : CM Tm := do
    if swap then
      let some sh := hv.getLast? | throw "LIR: κ's stack"
      let reg ← stackRegister
      let prev ← fresh (.int .w64); let sh' ← fresh (.int .w64)
      return .letv prev (.prim (.stackSwap reg) [sh])
        (run (.letv sh' (.prim (.stackSwap reg) [prev]) (← rest hv.dropLast (some sh'))))
    else return run (← rest hv none)
  let y ← fresh bT
  let (ps₁, b₁) ← envOf fun k hv => do
    let kr ← fresh (← selTy kIn 0); let o ← fresh T.ty
    aroundK hv (fun t => .letv kr (.sel k 0) (.letv o (.app kr y) t)) fun hv sh =>
      pure (.call driveFn (hv ++ sh.toList ++ [o]))
  setFn kapR { name := s!"kappa {n}.{idx}", params := ps₁ ++ [y], body := b₁, ret := oT }
  let freeSh (sh : Option Var) (t : Tm) : CM Tm := match sh with
    | some h => freeStackThen h t
    | none => pure t
  match cK with
  | .top =>
    let (ps₂, b₂) ← envOf fun k hv => do
      if swap then
        let some sh := hv.getLast? | throw "LIR: κ's stack"
        freeStackThen sh (Tm.drop k (drops hv.dropLast .unit))
      else pure (Tm.drop k (drops hv .unit))
    setFn kcan { name := s!"kappa {n}.{idx} cancel", params := ps₂, body := b₂, ret := .unit }
  | .ret cT' =>
    let want := match cM with
      | some O => O.ty
      | none => resTy .unit cPay
    unless cT'.sameRep want do throw s!"LIR: κ's cancel answers {cT'}, its row {want}"
    let (ps₂, b₂) ← envOf fun k hv => do
      let cv ← fresh (cancelResTy cpIn)
      let body ← toResult .unit (cpIn.getD []) cM cPay cv
      aroundK hv (fun t => .letv cv (.sel k 1) t) fun hv sh => do
        freeSh sh (drops hv body)
    setFn kcan { name := s!"kappa {n}.{idx} cancel", params := ps₂, body := b₂, ret := cT' }
  | k => throw s!"LIR: κ's cancel branch at {k}"
  return kc

/-- **One code per task body**  `[spec §49]`: the closures of one closure type that the clauses of
the stored-continuation sites of one task body build (a task's or a stored generator's value:
finished, or pending on `κ`) are variants of one code, its environment a sum of theirs, each
component a `case` on it that calls the variant's own function. A representation of the closure
type, with the same observations: a value of it is one code, as a coroutine of one body is one
type. A body built once is its own code. -/
def genMerges : CM Unit := do
  for g in (← get).merged do
    let vs := (← get).merges.getD g #[]
    let some v₀ := vs[0]? | continue
    let some c₀ := (← get).codes[v₀.code]? | throw "LIR: a task variant's code"
    if vs.size == 1 then
      let xs ← v₀.envTys.mapM fresh
      setFn v₀.mkFn { name := "task variant", params := xs, body := .clos v₀.code xs, ret := .thunk c₀.ty }
      continue
    readFact "effHandleV:task body code"
    let stPay : Pay := vs.toList.zipIdx.map fun (v, i) => ((0, i.toUInt32), tupleTy v.envTys)
    let stTy := (payTy stPay).getD .unit
    let mut fns : Array Nat := #[]
    for (f₀, j) in c₀.fns.zipIdx do
      let some d₀ := (← get).fns[f₀]? | throw "LIR: a task variant's function"
      let fi ← reserveFn "task"
      let st ← fresh stTy
      let a? ← match c₀.kind, d₀.params.getLast? with
        | .lam, some p => pure (some (← freshLike p))
        | _, _ => pure none
      let body ← casePay stPay st fun i fv => do
        let some v := vs[i]? | throw "LIR: a task variant"
        let some c := (← get).codes[v.code]? | throw "LIR: a task variant's code"
        untuple fv v.envTys fun fs => pure (.call (c.fns.getD j 0) (fs ++ a?.toList))
      setFn fi { name := "task", params := st :: a?.toList, body, ret := d₀.ret }
      fns := fns.push fi
    let m ← addCode { kind := c₀.kind, fns := fns.toList, ty := c₀.ty }
    for (v, i) in vs.toList.zipIdx do
      let xs ← v.envTys.mapM fresh
      let body ← mkTuple xs fun t => injectPay stPay i t fun w => pure (.clos m [w])
      setFn v.mkFn { name := "task variant", params := xs, body, ret := .thunk c₀.ty }

/-- The keys of the `def`s a term uses (`use` nodes, their bodies not entered): a handled
computation's task body, as copies of one `def` at several sites share it (`DefKey.body`).  -/
def useKeys : Nat → TExpr → List String
  | 0, _ => []
  | f + 1, t => match t with
    | .use info _ name _ targs _ _ =>
      [s!"{(info.key.map (·.body)).getD name}[{", ".intercalate (targs.map (ppVT ·))}]"]
    | t => t.children.flatMap fun (_, c) => useKeys f c

/-- The closure types at the `⊗` and `⊕` positions of a value type, a `ν` also unrolled (its
closures are of its unrolling, `nuIn`). -/
def closTys : Nat → LTy → List LTy
  | 0, _ => []
  | f + 1, t => match t with
    | .thunk k => [t, .thunk (k.whnf 8)]
    | .pair a b | .sum a b => closTys f a ++ closTys f b
    | .bang a => closTys f a
    | _ => []

/-- A join of the current machine, its body made by `body` at the context `c₂` renamed with the
value pushed and the continuation's arguments renamed. -/
def joinWith (c₂ : Ctx) (A : VTy) (args : List Var) (body : Ctx → List Var → CM Tm) : CM Nat := do
  let F ← curMach
  let (_, inner, c₂') ← envOf c₂
  let args' ← args.mapM freshMarked
  let x ← fresh (← vty A)
  let fn ← reserveFn "join"
  let b ← body (some x :: c₂') args'
  setFn fn { name := "join", params := inner ++ args' ++ [x], body := b, ret := F.ty }
  return fn

/-- The computation nodes a machine's conversion takes apart with its continuation (`convK`):
at an outcome, each is converted inside a machine.  `[spec §49]` -/
def machNode : TExpr → Bool
  | .effLet .. | .effThen .. | .bind .. | .sumE .. | .tensorE .. | .unitE .. | .zeroE .. | .effSub ..
  | .effRaise .. | .effPerform .. | .nilDead .. | .lendR .. => true
  | .lendScope _ _ _ t => machNode t
  | _ => false

/-- The outside of the pure fragment. -/
def outside (t : TExpr) : CM α :=
  throw s!"LIR: `{ruleName t}` is outside the pure fragment (N2 and later)"

/-- **A lent cell's scope** (`TExpr.lendScope`, SPEC §57): `act` converts it. Where its `rel` holds
(the owner released on every path), its cell is allocated for the scope (`scopeCell`), whose owner
the `letpair` that takes the lend's pair apart binds (`markOwner`); the program's slots are
chosen from these (`Backend2/Driver.lean`, `slotsOf`). -/
def withScope (rel : Bool) (act : CM Tm) : CM Tm := do
  if rel then
    let s ← newScope
    modify fun st => { st with scopeCell := some s }
  let r ← act
  modify fun st => { st with scopeCell := none, scopeOwner := none }
  return r

/-- **A literal's view** (`TExpr.litView`, SPEC §57): `act` converts it, its tabulation a `tabLit`. -/
def withLitView (act : CM Tm) : CM Tm := do
  modify fun st => { st with litPending := true }
  let r ← act
  modify fun st => { st with litPending := false }
  return r

set_option maxHeartbeats 4000000 in
mutual
/-- **The conversion of a node** at its context: the term of its value. -/
def conv (fuel : Nat) (ctx : Ctx) (t : TExpr) : CM Tm := do
  match fuel with
  | 0 => throw "LIR: the typed term is too deep"
  | fuel + 1 =>
  readFact s!"{ruleName t}:node"
  -- A computation at an outcome, in a value's position: a machine of its own.  [spec §49]
  if machNode t && !(← get).mach.isEmpty then
    if let some M ← outInfoJ t.jdg then return ← subMachine fuel ctx t M
  match t with
  | .var _ _ i _ =>
    match ctx[i]? with
    | some (some x) => return leaf ctx (some i) (.var x)
    | _ => throw s!"LIR: variable {i} is not live"
  | .unitI .. | .topI .. => return leaf ctx none .unit
  | .lit _ _ c => return leaf ctx none (.lit c)
  | .tensorI _ j _ _ u t₁ t₂ => do
    let (pre, c₁, c₂) ← splitCtx ctx u "tensorI"
    let rT ← repJ j
    let .pair aT bT := rT.peel | throw "LIR: a pair at a non-pair type"
    return pre (← bindTm (← conv fuel c₁ t₁) aT fun a => do
      bindTm (← conv fuel c₂ t₂) bT fun b => pure (.pair a b))
  | .sumI₁ _ j _ _ c => do
    let .sum aT _ := (← repJ j).peel | throw "LIR: an injection at a non-sum"
    bindTm (← conv fuel ctx c) aT fun a => pure (.inj false a)
  | .sumI₂ _ j _ _ c => do
    let .sum _ bT := (← repJ j).peel | throw "LIR: an injection at a non-sum"
    bindTm (← conv fuel ctx c) bT fun a => pure (.inj true a)
  | .thunkF _ j _ c | .bangThunkF _ j _ c => do
    let .thunk k := (← repJ j).peel | throw "LIR: a thunk at a non-closure type"
    mkClos "thunk" ctx k none (← repK k) fun ctx' => convBody fuel (none :: ctx') c
  | .lam _ j A _ c => do
    let .thunk k := (← repJ j).peel | throw "LIR: a λ at a non-closure type"
    let (_, r) ← answerOf (.thunk k)
    mkClos "lam" ctx k (some (← vty A)) r fun ctx' => convBody fuel ctx' c
  | .lamDead _ j _ _ c => do
    let .thunk k := (← repJ j).peel | throw "LIR: a λ at a non-closure type"
    let (_, r) ← answerOf (.thunk k)
    mkClos "lam" ctx k (some .unit) r fun ctx' => do
      match ctx' with
      | some p :: rest => return .drop p (← convBody fuel (none :: rest) c)
      | _ => throw "LIR: a dead λ's parameter"
  | .allI _ _ _ _ _ _ c => do
    -- `Λ. M` is `M` (`allI_inst`)  [spec §44]: its body erases to a λ-value, so the binder's slot
    -- is dead and no instantiation runs code.
    unless c.isLam do throw "outside the pure fragment: a Λ whose body is not a λ-value (SPEC §44)"
    readFact "allI:body a λ-value"
    conv fuel (none :: ctx) c
  | .withI _ j _ _ tM tN => do
    let .thunk k := (← repJ j).peel | throw "LIR: a `&` at a non-closure type"
    let r₁ ← selTy (.thunk k) 0
    let r₂ ← selTy (.thunk k) 1
    readFact "withI:code kind"
    mkAmp "with" ctx k [r₁, r₂] [fun ctx' => convBody fuel (none :: none :: ctx') tM,
      fun ctx' => convBody fuel (none :: none :: ctx') tN]
  | .effLet _ _ A B S u tM tN => do
    match payTy (← rowPay S) with
    | none => convBind fuel ctx A u tM tN
    | some pT => do
      -- `M to x. N` at a row with abortive operations: `N` on a value, the abort handed on, `N`'s
      -- context dropped (`effLet`'s `hW`), the branch per call of SPEC §19 (`abort_to`).
      readFact "effLet:row"
      let (pre, c₁, c₂) ← splitCtx ctx u "effLet"
      let aT ← vty A
      let m ← fresh (.sum aT pT); let x ← fresh aT; let e ← fresh pT
      return pre (.letv m (← conv fuel c₁ tM)
        (.case m x (← conv fuel (some x :: c₂) tN) e (drops (live c₂) (.inj true e))))
  | .effSub _ _ S S' A c => do
    -- `[sub]`: the payload of `Σ` as one of `Σ'`.  [spec §47]
    readFact "effSub:rows"
    let p ← rowPay S; let q ← rowPay S'
    let a ← vty A
    bindTm (← conv fuel ctx c) (resTy a p) fun r => coerceRes a p q r
  | .effRaise _ _ S o _ c => do
    -- `raise`: the abort at its operation's summand, handed to the handler's join (`catch_abort`,
    -- `abort_absorbs`).  [spec §47]
    readFact "effRaise:op"
    modify fun st => { st with erased := st.erased.insert "raise" (st.erased.getD "raise" 0 + 1) }
    let p ← rowPay S
    let some j := payIdx p (o.n, o.i) | throw s!"LIR: a raise of ({o.n}, {o.i}) outside its row"
    bindTm (← conv fuel ctx c) (← vty o.A) fun v => injectPay p j v fun w => pure (.inj true w)
  | .effPerform _ _ S o c => do
    if o.n == divName && !(← get).mach.contains (o.n, o.i) then
      -- `tick` under the runtime: *next* where it is performed.  [spec §62]
      tickAtRuntime
      let p ← rowPay S
      return ← bindTm (← conv fuel ctx c) .unit fun v => tickTm v p
    -- `perform` of a `[handle-last]` operation: a direct call of its work; `inl y` answers `y`
    -- where it is performed, `inr z` (or a raise from the work) leaves for the node at the
    -- operation's cancel summand, the finalisers between run on the way (`last_resume_direct`,
    -- `last_cancel_direct`, `lastFacts`).  [spec §64]
    if let some (fi, phW, xT) := (← get).lasts[(o.n, o.i.toNat)]? then
      return ← lastPerform fuel ctx S o fi phW xT c
    -- `perform` of a tail-resumptive clause: a direct call of the clause's work (`tail_resumes`,
    -- `TailResumesAt.subst_kappa`, `tail_clause_names`, `Checked.unhandledNames`).  [spec §47]
    if (← get).mach.contains (o.n, o.i) then
      throw s!"LIR: `effPerform` of the machine operation ({o.n}, {o.i}) outside a machine"
    let some (fi, ph, _) := (← get).works[(o.n, o.i.toNat)]?
      | throw s!"LIR: `effPerform` of ({o.n}, {o.i}) with no direct call is outside the pure fragment (N3)"
    readFact "effPerform:direct call"
    modify fun st => { st with erased := st.erased.insert "perform" (st.erased.getD "perform" 0 + 1) }
    let p ← rowPay S
    unless ph.all fun k => (payIdx p k.1).isSome do
      throw s!"LIR: `effPerform` of ({o.n}, {o.i}) at a row that does not hold its clause's aborts is outside the pure fragment"
    let bT ← vty o.B
    bindTm (← conv fuel ctx c) (← vty o.A) fun v => do
      let r ← fresh (resTy bT ph)
      return .letv r (.call fi [v]) (← coerceRes bT ph p r)
  | .effThen _ _ A _ S SM SD u tM tN tD => do
    -- `M then x. N unwind D`: `N` on a value; on an abort the finaliser `D`, then the abort, or
    -- the finaliser's own, handed on (`then_ret`, `then_fin`, `unwind_prefix`).  [spec §47]
    readFact "effThen:rows"
    let (pre, c₁, c₂) ← splitCtx ctx u "effThen"
    let pm ← rowPay SM; let ps ← rowPay S; let pd ← rowPay SD
    let aT ← vty A
    match payTy pm with
    | none => return pre (← bindTm (← conv fuel c₁ tM) aT fun x => conv fuel (some x :: c₂) tN)
    | some pmT =>
      let m ← fresh (.sum aT pmT); let x ← fresh aT; let e ← fresh pmT
      let d ← fresh (resTy .unit pd)
      let dTm ← conv fuel (none :: c₂) tD
      let pass ← coercePay pm ps e fun e' => pure (.inj true e')
      let fin ← match payTy pd with
        | none => pure (Tm.letv d dTm (.drop d pass))
        | some pdT => do
          let w ← fresh .unit; let e₂ ← fresh pdT
          pure (Tm.letv d dTm (.case d w (.drop w pass) e₂
            (.drop e (← coercePay pd ps e₂ fun e' => pure (.inj true e')))))
      return pre (.letv m (← conv fuel c₁ tM) (.case m x (← conv fuel (some x :: c₂) tN) e fin))
  | .effHandleV _ _ S E fs n A R u ks site _ tc te =>
    convHandle fuel ctx S E fs n A R u ks site tc te
  | .effHandleVB _ _ S E fs n A R _ u ks site _ tc te =>
    convHandle fuel ctx S E fs n A R u ks site tc te (boxed := true)
  | .bind _ _ A _ u tM tN => convBind fuel ctx A u tM tN
  | .force _ j i C => do
    match ctx[i]? with
    | some (some x) =>
      match C with
      | .ret _ | .eff .. => return leaf ctx (some i) (.app0 x)
      | _ => return leaf ctx (some i) (.var x)
    | _ => throw s!"LIR: forced variable {i} is not live"
  | .app _ j i _ _ u tM => do
    let (pre, c₁, c₂) ← splitCtx ctx u "app"
    let some (some x) := c₂[i]? | throw s!"LIR: the argument {i} is not live"
    let rest := leaf c₂ (some i)
    match headOf 64 tM with
    | .lam _ _ _ _ body => return pre (rest (← conv fuel (some x :: c₁) body))
    | _ => do
      let f ← fresh (← repJ tM.jdg)
      return pre (rest (.letv f (← conv fuel c₁ tM) (.app f x)))
  | .proj₁ _ _ _ _ c | .proj₂ _ _ _ _ c => do
    let j := match t with | .proj₂ .. => 1 | _ => 0
    let fT ← repJ c.jdg
    bindTm (← conv fuel ctx c) fT fun f => pure (.sel f j)
  | .unitE _ _ _ u tV tM => do
    let (pre, c₁, c₂) ← splitCtx ctx u "unitE"
    return pre (← bindTm (← conv fuel c₁ tV) .unit fun v => return .drop v (← conv fuel c₂ tM))
  | .tensorE _ _ A B _ u tV tM => do
    let (pre, c₁, c₂) ← splitCtx ctx u "tensorE"
    let aT ← vty A
    let bT ← vty B
    return pre (← bindTm (← conv fuel c₁ tV) (.pair aT bT) fun p => do
      let x ← fresh aT; let y ← fresh bT
      markOwner x
      return .letpair x y p (← conv fuel (some y :: some x :: c₂) tM))
  | .sumE _ _ A B _ u tV t₁ t₂ => do
    let (pre, c₁, c₂) ← splitCtx ctx u "sumE"
    let aT ← vty A
    let bT ← vty B
    return pre (← bindTm (← conv fuel c₁ tV) (.sum aT bT) fun sv => do
      let x ← fresh aT; let y ← fresh bT
      return .case sv x (← conv fuel (some x :: c₂) t₁) y (← conv fuel (some y :: c₂) t₂))
  | .zeroE _ _ _ u tV => do
    let (pre, c₁, _) ← splitCtx ctx u "zeroE"
    return pre (← bindTm (← conv fuel c₁ tV) .zero fun v => pure (.absurd v))
  | .allE _ _ _ _ _ _ c | .allEV _ _ _ _ _ _ c => do
    -- An instantiation is its operand.  [spec §44]
    readFact s!"{ruleName t}:erased"
    conv fuel ctx c
  | .roll _ j _ c => do
    bindTm (← conv fuel ctx c) (← repJ c.jdg) fun x => pure (.prim .roll [x])
  | .unroll _ j _ c => do
    bindTm (← conv fuel ctx c) (← repJ c.jdg) fun x => pure (.prim .unroll [x])
  | .lolliE .. => convSpine fuel ctx t
  | .use info j _ decl targs _ body => convUse fuel ctx info j decl targs body
  | .litFn _ _ bs _ => do
    let off := (← get).data.size
    modify fun s => { s with data := s.data ++ (bs.map (·.toUInt8)).toArray }
    let c ← litCode
    readFact "litFn:bytes"
    return leaf ctx none (← lit32 off.toUInt32 fun o => lit32 bs.length.toUInt32 fun n =>
      pure (.clos c [o, n]))
  | .divLit _ j op c inner => convDivLit fuel ctx j op c inner
  | .lendCell _ _ _ c => convLendCell fuel ctx t c
  | .lendScope _ _ rel c => withScope rel (conv fuel ctx c)
  | .litView _ _ c => withLitView (conv fuel ctx c)
  | .walk _ _ _ read c => do
    -- A walk whose step reads its view at its index (`walkReadB`): its read has no test.  [spec §46]
    let old := (← get).walkRead
    if read then readFact "walk:read"
    modify fun s => { s with walkRead := read }
    let r ← conv fuel ctx c
    modify fun s => { s with walkRead := old }
    return r
  | .walkGet _ _ _ c => do
    -- The read of a walk's view at its index: below the bound (`walk_index_lt`), the bound the
    -- view's length, so the read answers its leaf (`walk_get_leaf`, `walk_get_split`).  [spec §46]
    let ok := (← get).walkRead
    let old := (← get).inRange
    modify fun s => { s with inRange := ok }
    let r ← conv fuel ctx c
    modify fun s => { s with inRange := old }
    return r
  | .selfCall _ _ _ _ c => conv fuel ctx c
  | .nuEta _ _ f s c => do
    -- The η-thunk of codata is the codata it observes (`nuEta_var`, `nuEta_unfold`)  [spec §45]:
    -- with no state, the variable itself; at `f = unfold step`, the call `f s`, made here.
    match ctx[f]?, s with
    | some (some fv), none =>
      readFact "nuEta:eta"
      return leaf ctx (some f) (.var fv)
    | some (some fv), some si =>
      match ctx[si]? with
      | some (some sv) =>
        -- `f`'s slot is bound by a `bind` whose bound computation is an `unfoldStep` node (SPEC
        -- §57), read where the `bind` is converted and kept with the slot's variable as the
        -- conversion renames it (`CState.unfolds`: a split's copy, a closure's parameter): the
        -- η-thunk is the call `f s` made now (`nuEta_unfold`).
        if (← get).unfolds.contains fv then
          readFact "nuEta:unfold call"
          let others := (ctx.zipIdx.filter fun (_, k) => k != f && k != si).filterMap (·.1)
          return drops others (.app fv sv)
        else conv fuel ctx c
      | _ => conv fuel ctx c
    | _, _ => conv fuel ctx c
  | .nilDead _ _ _ c => do
    -- `[nil-dead]` (SPEC §29): the term at the empty context, the context's slots consumed.
    readFact "nilDead:context"
    return drops (live ctx) (← conv fuel [] c)
  | .effHandleT _ _ S _ E fs n _ A R u _ _ tc te =>
    -- The tail-resuming rule's clauses (`tailKind`): each tail-resumptive operation's answering
    -- function called where it is performed (`tail_resume_direct`), made first (`prepWorks`).
    -- [spec §64]
    convHandle fuel ctx S E fs n A R u (E.map ClauseKinds.tailKind) none tc te (rule := true)
  | .effHandleL _ _ S _ E fs _ n A R u _ _ tc te => convHandleL fuel ctx S E fs n A R u tc te
  | .reify _ j S B R tr => do
    -- A stored loop's `reify` (`main`'s, when the runtime answers every tick, is `runtimeMain`'s):
    -- a drive, at a program whose `tick` is a machine operation.  [spec §64]
    unless (← get).mach.contains (divName, 0) do outside t
    let resT ← repJ tr.jdg
    let resV ← conv fuel [] tr
    return leaf ctx none (← genReify S B R resV resT (← repJ j))
  | .lendR .. | .lendLoopR .. | .divFuel .. | .letPoly .. => outside t
  | t =>
    match transparent? t with
    | some c => conv fuel ctx c
    | none =>
      match constArity t with
      | some _ => return leaf ctx none (← constClos fuel t)
      | none => throw s!"LIR: no conversion for `{ruleName t}`"

/-- `x <- M; N`: `M`'s value bound, then `N`. -/
def convBind (fuel : Nat) (ctx : Ctx) (A : VTy) (u : Masks) (tM tN : TExpr) : CM Tm := do
  let (pre, c₁, c₂) ← splitCtx ctx u "bind"
  let unf := tM matches .unfoldStep ..
  return pre (← bindTm (← conv fuel c₁ tM) (← vty A) fun x => do
    if unf then
      readFact "bind:unfold step"
      modify fun st => { st with unfolds := st.unfolds.insert x }
    conv fuel (some x :: c₂) tN)

/-- **A machine's computation**  `[spec §49]`: `t`'s value handed to the continuation `K` over its
arguments `args`, the term answering the current machine's outcome. A `[let]` or `[then]` at an
outcome makes its body a join of the machine and converts its premise with the frame pushed, so a
suspension inside the premise suspends the whole machine, its state the variables live there and
nothing nested; the arms of a `case` take `K` each. A `perform` of a machine operation suspends
the machine (`performK`), a `raise` unwinds `K` (`abortK`), and any other computation at an
outcome is a call point (`pointK`). A computation at no outcome is converted as §47 converts it,
its value or abort handed to `K`. -/
def convK (fuel : Nat) (ctx : Ctx) (t : TExpr) (K : Kont) (args : List Var) : CM Tm := do
  match fuel with
  | 0 => throw "LIR: the typed term is too deep"
  | fuel + 1 =>
  match ← outInfoJ t.jdg with
  | none =>
    match t.jdg with
    | .comp C =>
      match effParts C with
      | some (S, R) => resultK K args (← conv fuel ctx t) (← vty R) (← rowPay S)
      | none => throw s!"LIR: a machine's computation at {ppJ t.jdg}"
    | .val _ => throw "LIR: a machine's computation at a value"
  | some M =>
  match t with
  | .effLet _ _ A _ _ u tM tN => do
    let (pre, c₁, c₂) ← splitCtx ctx u "effLet"
    let inner := unSubK 8 tM
    if (← outInfoJ inner.jdg).isNone then
      -- A premise that cannot suspend: `N` in place, an abort through `K`.
      let some (S, _) := (match inner.jdg with | .comp C => effParts C | _ => none)
        | throw "LIR: a `[let]`'s premise is not a returner"
      let p ← rowPay S
      let aT ← vty A
      match payTy p with
      | none =>
        return pre (← bindTm (← conv fuel c₁ inner) aT fun x => convK fuel (some x :: c₂) tN K args)
      | some pT =>
        let F ← curMach
        let some pF := payTy F.pay | throw "LIR: an abort where the machine's row holds none"
        let r ← fresh (.sum aT pT); let x ← fresh aT; let e ← fresh pT; let e' ← fresh pF
        return pre (.letv r (← conv fuel c₁ inner) (.case r x (← convK fuel (some x :: c₂) tN K args)
          e (drops (live c₂) (.letv e' (← coercePay p F.pay e fun v => pure (.var v))
            (← abortK F K args e')))))
    readFact "effLet:machine join"
    let fn ← joinFn fuel c₂ A tN K args
    let own := live c₂
    return pre (← convK fuel c₁ tM (.letF fn own.length :: K) (own ++ args))
  | .effThen _ _ A _ _ _ SD u tM tN tD => do
    readFact "effThen:machine join"
    let (pre, c₁, c₂) ← splitCtx ctx u "effThen"
    unless (← rowMs SD).isEmpty do
      throw "LIR: a finaliser that may suspend is outside the fragment"
    let fn ← joinFn fuel c₂ A tN K args
    let pd ← rowPay SD
    let (_, inner, cD) ← envOf c₂
    let fnD ← reserveFn "finaliser"
    let dTm ← conv fuel (none :: cD) tD
    setFn fnD { name := "finaliser", params := inner, body := dTm, ret := resTy .unit pd }
    let own := live c₂
    return pre (← convK fuel c₁ tM (.thenF fn fnD own.length pd :: K) (own ++ args))
  | .bind _ _ A _ u tM tN => do
    let (pre, c₁, c₂) ← splitCtx ctx u "bind"
    let unf := tM matches .unfoldStep ..
    return pre (← bindTm (← conv fuel c₁ tM) (← vty A) fun x => do
      if unf then
        readFact "bind:unfold step"
        modify fun st => { st with unfolds := st.unfolds.insert x }
      convK fuel (some x :: c₂) tN K args)
  | .sumE _ _ A B _ u tV t₁ t₂ => do
    let (pre, c₁, c₂) ← splitCtx ctx u "sumE"
    let aT ← vty A; let bT ← vty B
    return pre (← bindTm (← conv fuel c₁ tV) (.sum aT bT) fun sv => do
      let x ← fresh aT; let y ← fresh bT
      return .case sv x (← convK fuel (some x :: c₂) t₁ K args)
        y (← convK fuel (some y :: c₂) t₂ K args))
  | .tensorE _ _ A B _ u tV tM => do
    let (pre, c₁, c₂) ← splitCtx ctx u "tensorE"
    let aT ← vty A; let bT ← vty B
    return pre (← bindTm (← conv fuel c₁ tV) (.pair aT bT) fun p => do
      let x ← fresh aT; let y ← fresh bT
      markOwner x
      return .letpair x y p (← convK fuel (some y :: some x :: c₂) tM K args))
  | .unitE _ _ _ u tV tM => do
    let (pre, c₁, c₂) ← splitCtx ctx u "unitE"
    return pre (← bindTm (← conv fuel c₁ tV) .unit fun v => return .drop v (← convK fuel c₂ tM K args))
  | .zeroE _ _ _ u tV => do
    let (pre, c₁, _) ← splitCtx ctx u "zeroE"
    return pre (← bindTm (← conv fuel c₁ tV) .zero fun v => pure (.absurd v))
  | .effSub _ _ _ _ _ c => do
    readFact "effSub:rows"
    convK fuel ctx c K args
  | .effRaise _ _ _ o _ c => do
    readFact "effRaise:op"
    modify fun st => { st with erased := st.erased.insert "raise" (st.erased.getD "raise" 0 + 1) }
    let F ← curMach
    let some j := payIdx F.pay (o.n, o.i) | throw s!"LIR: a raise of ({o.n}, {o.i}) outside its row"
    bindTm (← conv fuel ctx c) (← vty o.A) fun v => injectPay F.pay j v fun e => abortK F K args e
  | .effPerform _ _ S o c => do
    if o.n == divName && !(← get).mach.contains (o.n, o.i) then
      -- `tick` under the runtime: *next* where it is performed, handed to `K`.  [spec §62]
      tickAtRuntime
      let p ← rowPay S
      return ← bindTm (← conv fuel ctx c) .unit fun v => do
        resultK K args (← tickTm v p) boolT p
    if let some (fi, phW, xT) := (← get).lasts[(o.n, o.i.toNat)]? then
      -- `[handle-last]`'s work called where its operation is performed, in a machine: `inl y`
      -- handed to `K`, `inr z` or a raise from the work through `K`'s frames to the node at the
      -- operation's cancel summand.  [spec §64]
      readFact "effPerform:last direct call"
      modify fun st => { st with erased := st.erased.insert "perform" (st.erased.getD "perform" 0 + 1) }
      let F ← curMach
      let some jc := payIdx F.pay (o.n, o.i)
        | throw s!"LIR: `effPerform` of ({o.n}, {o.i}) at a machine without its cancel summand"
      let bT ← vty o.B
      let leave (w : Var) : CM Tm := injectPay F.pay jc w fun e => abortK F K args e
      return ← bindTm (← conv fuel ctx c) (← vty o.A) fun v => do
        let bx ← fresh (.sum bT xT); let y ← fresh bT; let z ← fresh xT
        match payTy phW with
        | none =>
          return .letv bx (.call fi [v]) (.case bx y (← applyK F K args y) z (← leave z))
        | some pwT =>
          let r ← fresh (.sum (.sum bT xT) pwT); let e ← fresh pwT
          let sT := LTy.sum xT pwT
          let wz ← fresh sT; let we ← fresh sT
          return .letv r (.call fi [v]) (.case r bx (.case bx y (← applyK F K args y) z
            (.letv wz (.inj false z) (← leave wz))) e (.letv we (.inj true e) (← leave we)))
    if (← get).mach.contains (o.n, o.i) then
      readFact "effPerform:machine"
      bindTm (← conv fuel ctx c) (← vty o.A) fun v => performK K args (o.n, o.i) v
    else
      -- A direct call (SPEC §47), its answer handed to `K`.
      let some (fi, ph, wm) := (← get).works[(o.n, o.i.toNat)]?
        | throw s!"LIR: `effPerform` of ({o.n}, {o.i}) with no direct call is outside the fragment"
      readFact "effPerform:direct call"
      modify fun st => { st with erased := st.erased.insert "perform" (st.erased.getD "perform" 0 + 1) }
      let bT ← vty o.B
      bindTm (← conv fuel ctx c) (← vty o.A) fun v => match wm with
        | some W => pointK K args (.call fi [v]) W
        | none => resultK K args (.call fi [v]) bT ph
  | .nilDead _ _ _ c => do
    readFact "nilDead:context"
    return drops (live ctx) (← convK fuel [] c K args)
  | .lendR _ _ _ _ T _ _ td tM => do
    -- `[lend-R]` (SPEC §29): §19's unwinding borrow at a resuming row. The owner is lent as the
    -- callback's view; the callback's value `b` gives `(r, b)`; a cancel of the machine inside the
    -- callback runs the finaliser `d` on the owner. The owner's cell stays where it is: the
    -- machine's state holds its location.
    readFact "lendR:machine"
    let F ← curMach
    let some (some r) := ctx[0]? | throw "LIR: a relaxed lend's owner is not live"
    let rT ← tyOf r
    let .pair _ bT := M.r.peel | throw "LIR: a relaxed lend's answer is not a pair"
    let mT : LTy := .mut (← vty T)
    let fnD ← reserveFn "lend finaliser"
    let oD ← fresh rT
    let dT ← repJ td.jdg
    let f ← fresh dT
    let du ← fresh .unit
    setFn fnD { name := "lend finaliser", params := [oD],
                body := .letv f (← conv fuel [] td) (.letv du (.app f oD) (.var du)), ret := .unit }
    let fnN ← reserveFn "join"
    let oN ← fresh rT; let argsN ← args.mapM freshLike; let b ← fresh bT
    let pv ← fresh (.pair rT bT)
    setFn fnN { name := "join", params := [oN] ++ argsN ++ [b],
                body := .letv pv (.pair oN b) (← applyK F K argsN pv), ret := F.ty }
    let pr ← fresh (.pair rT mT); let o ← fresh rT; let m ← fresh mT
    let body ← convK fuel [some m] tM (.thenF fnN fnD 1 [] :: K) (o :: args)
    readFact "lend"
    return leaf ctx (some 0) (.letv pr (.prim (.lend true) [r]) (.letpair o m pr body))
  | .lendScope _ _ rel c => withScope rel (convK fuel ctx c K args)
  | .litView _ _ c => withLitView (convK fuel ctx c K args)
  | .unfoldStep _ _ c => convK fuel ctx c K args
  | .app _ _ i _ _ u tM =>
    match headOf 64 tM with
    | .lam _ _ _ _ body => if true then pointAt fuel ctx t K args M else do
      -- A λ applied in place: its body in the machine (β).
      let (pre, c₁, c₂) ← splitCtx ctx u "app"
      let some (some x) := c₂[i]? | throw s!"LIR: the argument {i} is not live"
      return pre (leaf c₂ (some i) (← convK fuel (some x :: c₁) body K args))
    | _ => pointAt fuel ctx t K args M
  | .lolliE .. =>
    let (as, h) := spineOf 4096 t
    match lamOf 64 h, as with
    | some (k, .lam _ _ _ _ body), [(u, ta)] => if true then pointAt fuel ctx t K args M else do
      -- A λ applied in place to one argument: its body in the machine (β).
      readFact "lolliE:beta"
      let (pre, cA, cF) ← splitCtx ctx u "lolliE"
      let aT ← repJ ta.jdg
      return pre (← bindTm (← conv fuel cA ta) aT fun a =>
        convK fuel (some a :: (List.replicate k none ++ cF)) body K args)
    | _, _ => pointAt fuel ctx t K args M
  | _ => pointAt fuel ctx t K args M

/-- A call point of the current machine at `t`. -/
def pointAt (fuel : Nat) (ctx : Ctx) (t : TExpr) (K : Kont) (args : List Var) (M : OutInfo) :
    CM Tm := do
  pointK K args (← conv fuel ctx t) M

/-- A computation through its `[sub]`s. -/
def unSubK : Nat → TExpr → TExpr
  | f + 1, .effSub _ _ _ _ _ c => unSubK f c
  | _, t => t

/-- **A join of a machine**: the body `N` of a `[let]` or `[then]`, a function of its context's
live variables, the continuation's arguments and the value, answering the machine's outcome. -/
def joinFn (fuel : Nat) (c₂ : Ctx) (A : VTy) (tN : TExpr) (K : Kont) (args : List Var) : CM Nat :=
  joinWith c₂ A args fun ctx' args' => convK fuel ctx' tN K args'

/-- **A tail-resumptive clause's work in a machine** (SPEC §49): `convWork`'s paths, at a handler
whose outer row has machine operations, each resume's answer handed to `K`; the premise of a
`[let]` on a path converted in the machine with the rest of the path its join. -/
def convWorkK (fuel : Nat) (k : Nat) (ctx : Ctx) (t : TExpr) (K : Kont) (args : List Var) :
    CM Tm := do
  match fuel with
  | 0 => throw "LIR: the typed term is too deep"
  | fuel + 1 =>
  let F ← curMach
  if resumeB k t then
    match t.unSub with
    | .app _ _ y _ _ u _ => do
      let (pre, c₁, c₂) ← splitCtx ctx u "app"
      let some (some yv) := c₂[y]? | throw "LIR: a resume's answer is not live"
      return pre (drops (live c₁) (leaf c₂ (some y) (← applyK F K args yv)))
    | _ => throw "LIR: a resume"
  match t with
  | .bind _ _ A _ u tM tN | .effLet _ _ A _ _ u tM tN =>
    if tailLeafB k tM && returns0B tN then
      let (pre, c₁, c₂) ← splitCtx ctx u "bind"
      return pre (drops (live c₂) (← convWorkK fuel k c₁ tM K args))
    else if aliasOf 64 tM == some k then
      let (pre, c₁, c₂) ← splitCtx ctx u "bind"
      let some (some kv) := c₁[k]? | throw "LIR: an alias of a continuation that is not live"
      return pre (leaf c₁ (some k) (← convWorkK fuel 0 (some kv :: c₂) tN K args))
    else
      let (pre, c₁, c₂) ← splitCtx ctx u "bind"
      let fn ← joinWith c₂ A args fun ctx' args' => convWorkK fuel (k + 1) ctx' tN K args'
      let own := live c₂
      return pre (← convK fuel c₁ tM (.letF fn own.length :: K) (own ++ args))
  | .sumE _ _ A B _ u tV t₁ t₂ => do
    let (pre, c₁, c₂) ← splitCtx ctx u "sumE"
    let aT ← vty A; let bT ← vty B
    return pre (← bindTm (← conv fuel c₁ tV) (.sum aT bT) fun sv => do
      let x ← fresh aT; let y ← fresh bT
      return .case sv x (← convWorkK fuel (k + 1) (some x :: c₂) t₁ K args)
        y (← convWorkK fuel (k + 1) (some y :: c₂) t₂ K args))
  | .tensorE _ _ A B _ u tV tM => do
    let (pre, c₁, c₂) ← splitCtx ctx u "tensorE"
    let aT ← vty A; let bT ← vty B
    return pre (← bindTm (← conv fuel c₁ tV) (.pair aT bT) fun pv => do
      let x ← fresh aT; let y ← fresh bT
      return .letpair x y pv (← convWorkK fuel (k + 2) (some y :: some x :: c₂) tM K args))
  | .unitE _ _ _ u tV tM => do
    let (pre, c₁, c₂) ← splitCtx ctx u "unitE"
    return pre (← bindTm (← conv fuel c₁ tV) .unit fun v => return .drop v (← convWorkK fuel k c₂ tM K args))
  | .effSub _ _ _ _ _ c => convWorkK fuel k ctx c K args
  | .lendScope _ _ _ c | .litView _ _ c | .unfoldStep _ _ c => convWorkK fuel k ctx c K args
  | _ => throw s!"LIR: a tail-resumptive clause's path at `{ruleName t}` ends in no resume"

/-- A computation at an outcome, in a value's position: a function of its context, the body of a
machine of its own.  `[spec §49]` -/
def subMachine (fuel : Nat) (ctx : Ctx) (t : TExpr) (M : OutInfo) : CM Tm := do
  let (outer, inner, ctx') ← envOf ctx
  let fn ← reserveFn "machine"
  let body ← withMachineK M (convK fuel ctx' t)
  setFn fn { name := "machine", params := inner, body, ret := M.ty }
  readFact "machine:body"
  return .call fn outer

/-- A code's body: at an outcome, the code's function is the machine, `self` the code's closure
type.  `[spec §49]` -/
def convBody (fuel : Nat) (ctx : Ctx) (t : TExpr) : CM Tm := do
  if machNode t && !(← get).mach.isEmpty then
    if let some M ← outInfoJ t.jdg then
      readFact "machine:body"
      return ← withMachineK M (convK fuel ctx t)
  conv fuel ctx t

/-- A clause applied to `a` inside a drive's machine: a λ's body converted in the machine. -/
def applyToK (fuel : Nat) (ctx : Ctx) (tF : TExpr) (a : Var) : CM Tm := do
  match lamOf 64 tF with
  | some (k, .lam _ _ _ _ body) => convK fuel (some a :: (List.replicate k none ++ ctx)) body [] []
  | _ => applyTo fuel ctx tF a

/-- **A `handle` node as a drive**  `[spec §49]`: the handled computation is a machine of its own
(`handled`), and the drive takes its outcome apart, read from the node: a value goes to `h_ret`
(`[ret]`), an abort of the node's operation to its clause (`catch_abort`), an abort of `Σ`'s on
outward (`fwd_abort`); a suspension at one of the node's operations runs its clause on the
argument and `κ` (`[op]`): a closure of the suspended computation and the handler's values,
whose resume entry resumes the computation and drives its outcome again (the handler is deep) and
whose cancel entry cancels it (`kappa_cancel_steps`); a suspension at one of `Σ`'s machine
operations suspends the drive (forwarding), resumed by resuming the computation and driving
again. The handler's values are the drive's parameters. -/
def convDrive (fuel : Nat) (S : Row) (E : List (Qual × VTy × VTy)) (fs : Nat → CTy) (n : UInt32)
    (R : VTy) (ks : List ClauseKinds.HKind) (site : Option HSite) (c₂ : Ctx) (te : TExpr)
    (T : OutInfo) (cR : Ctx) (tR : TExpr)
    (parts : Array (Ctx × TExpr)) (tailCtx : Ctx) (tupleAt : Option Nat) (boxed : Bool := false) :
    CM Tm := do
  readFact "effHandleV:machine"
  modify fun st => { st with erased := st.erased.insert "machine" (st.erased.getD "machine" 0 + 1) }
  let rT ← vty R
  let outM ← outInfo? rT S
  let outPay ← rowPay S
  let outTy : LTy := match outM with
    | some O => O.ty
    | none => resTy rT outPay
  -- The handled computation: a machine of its own.
  let (bOuter, bInner, bCtx) ← envOf c₂
  let bodyFn ← reserveFn s!"handled {n}"
  let bBody ← withMachineK T (convK fuel bCtx te)
  setFn bodyFn { name := s!"handled {n}", params := bInner, body := bBody, ret := T.ty }
  -- The handler's values: the drive's parameters.
  let ctxs : List Ctx := cR :: parts.toList.map (·.1) ++ [tailCtx]
  let mut hvOuter : List Var := []
  let mut hvInner : List Var := []
  let mut cs' : Array Ctx := #[]
  for c in ctxs do
    let (o, i, c') ← envOf c
    hvOuter := hvOuter ++ o; hvInner := hvInner ++ i; cs' := cs'.push c'
  let hvTys ← hvInner.mapM tyOf
  let driveFn ← reserveFn s!"drive {n}"
  let oP ← fresh T.ty
  let ctxs' := cs'.toList
  -- **The site's stack** (SPEC §52): where the program has stack machines, a stored-continuation
  -- site runs its handled computation on a stack of its own, made current around each run (the
  -- first, `κ`'s resume and cancel, a forwarding point's) and swapped out after it. The drive takes
  -- it after the handler's values, and `κ` holds it as its last; it is made at the first frame
  -- reserved (`0` until then) and freed where the computation answers, aborts or is cancelled.
  let stored := ks.any fun k => k.kind == .stored
  -- No operation of the node is `unr`: a copied `κ` would hold the stack twice (SPEC §52).
  let siteSw := stored && boxed && E.all (·.1 != .unr) && !(← get).stacked.isEmpty
  let shP? : Option Var ← if siteSw then do readFact "effHandleV:site stack"; pure (some (← fresh (.int .w64)))
    else pure none
  let shTys : List LTy := if siteSw then [.int .w64] else []
  let kHvTys := hvTys ++ shTys
  let freeSh (b : Tm) : CM Tm := match shP? with
    | some h => freeStackThen h b
    | none => pure b
  -- **`κ` in the site's stack** (SPEC §52): at a site with a stack, the first operation whose
  -- clause keeps `κ` (`stored`) and whose `κ` is not `unr` keeps `κ`'s environment but the stack in
  -- the stack's `κ` region: the stack is made at the first run, holding the region, and `κ` is the
  -- stack. Each suspension there writes the region, `κ`'s resume entry takes it out, and the stack's
  -- free ends it. One operation: a region shared by two would join their computations' classes.
  let cellAt : Option Nat ← do
    let mut out : Option Nat := none
    for (k, j) in ks.zipIdx do
      if out.isSome then break
      let some o := E[j]? | continue
      if siteSw && k.kind == .stored && o.1 != .unr && T.ms.any (·.1 == (n, j.toUInt32)) then
        out := some j
    pure out
  let siteTag ← fresh .unit
  if cellAt.isSome then readFact "effHandleV:kappa region"
  let dropAll (keep : Option Nat) (b : Tm) : Tm :=
    drops ((ctxs'.zipIdx.filter fun (_, i) => some i != keep).flatMap fun (c, _) => live c) b
  let clauseApp (cc : Ctx) (c : TExpr) (a : Var) : CM Tm :=
    match outM with
    | some _ => applyToK fuel cc c a
    | none => applyTo fuel cc c a
  -- Clause `idx` applied to `a`: written in place, or a component of the clauses' value (the last
  -- context, `tupleAt` the index of its first clause), taken apart and called.
  let applyClause (idx : Nat) (a : Var) : CM Tm := do
    match tupleAt with
    | some s₀ =>
      if idx ≥ s₀ then
        let some [tv] := (ctxs'.getLast?).map live | throw "LIR: the clauses' value"
        let keep := ctxs'.length - 1
        let rec proj : Nat → Nat → Var → CM Tm
          | 0, _, _ => throw "LIR: the clauses' value too deep"
          | f + 1, i, v => do
            match (← tyOf v).peel with
            | .pair cT rT =>
              let x ← fresh cT; let y ← fresh rT
              if i == 0 then return .letpair x y v (.drop y (.app x a))
              else return .letpair x y v (.drop x (← proj f (i - 1) y))
            | t => throw s!"LIR: a clause of the clauses' value at {t}"
        return dropAll (some keep) (← proj 64 (idx - s₀) tv)
      else pure ()
    | none => pure ()
    match ctxs'[idx + 1]?, parts[idx]? with
    | some cc, some (_, c) => return dropAll (some (idx + 1)) (← clauseApp cc c a)
    | _, _ => throw "LIR: a clause"
  let abortOut (key : Key) (v : Var) : CM Tm := do
    let some j' := payIdx outPay key | throw s!"LIR: an abort of {key} outside the handler's row"
    injectPay outPay j' v fun e => match outM with
      | some O => outAbort O e
      | none => pure (.inj true e)
  let dbody : CM Tm := do
    let w ← fresh T.body; let a ← fresh T.r; let ex ← fresh T.xTy
    let some cR' := ctxs'[0]? | throw "LIR: the return clause"
    let retArm ← freeSh (dropAll (some 0) (← clauseApp cR' tR a))
    let abortArms (e : Var) : CM Tm := casePay T.pay e fun j v => do
      let some (key, _) := T.pay[j]? | throw "LIR: a payload's summand"
      if key.1 == n then freeSh (← applyClause key.2.toNat v)
      else freeSh (dropAll none (← abortOut key v))
    let suspArms (sv : Var) : CM Tm := casePay T.sPay sv fun j pv => do
      let some (key, _, bT, cpT) := T.ms[j]? | throw "LIR: a suspension's summand"
      letpairM pv fun v k => do
        if key.1 == n then
          let idx := key.2.toNat
          let some o := E[idx]? | throw "LIR: an operation"
          let kT ← vty (kTy S R o.1 o.2.2 (fs idx))
          let cancelC := cancelTy S (fs idx)
          let cM ← outInfoC cancelC
          let cPay ← match effParts cancelC with
            | some (Sc, _) => rowPay Sc
            | none => pure []
          let inCell := cellAt == some idx
          let kap ← genKap n idx kT T outTy driveFn kHvTys cM cPay
            (region := if inCell then some siteTag else none) (swap := siteSw)
          -- `κ` holds the suspended computation and a copy of each of the handler's values.
          let hvAll := ctxs'.flatMap live
          let mut copies : List (Tm → Tm) := []
          let mut hvC : List Var := []
          for x in hvAll do
            let x' ← freshLike x
            copies := copies ++ [fun (t : Tm) => Tm.copy x x' t]
            hvC := hvC ++ [x']
          let kv ← fresh kT
          let pr ← fresh (.pair (← tyOf v) kT)
          readFact "effHandleV:kappa"
          let body ← applyClause idx pr
          let t : Tm ← match inCell, shP? with
            | true, some sh => do
              -- The environment written into the stack's region; `κ` is the stack.
              mkTuple (k :: hvC) fun st => do
                let sh' ← fresh (.int .w64); let u ← fresh .unit
                return .copy sh sh' (.letv u (.prim (.kappaPut siteTag) [sh', st])
                  (.drop u (.letv kv (.clos kap [sh]) (.letv pr (.pair v kv) body))))
            | _, _ => pure (.letv kv (.clos kap (k :: hvC ++ shP?.toList)) (.letv pr (.pair v kv) body))
          return copies.foldr (fun (f : Tm → Tm) (t : Tm) => f t) t
        else
          let some O := outM
            | throw "LIR: a suspension forwarded where the handler's row has no machine operation"
          -- The slot is part of the point's state: resumed, the drive gets it back; cancelled, its
          -- cell is released (`Frame.cellF`).
          -- The site's stack too: made current around the callee's resume and cancel
          -- (`MPoint.swapAt`), and freed by a cancel (`Frame.stackH`).
          let shK : List Frame := if siteSw then [.stackH] else []
          let mk ← newPoint key (some (T.kTy bT cpT)) cpT (hvTys ++ shTys) (some driveFn)
            ([.dropF hvTys.length] ++ shK)
            (swapAt := if siteSw then some hvTys.length else none)
          let k' ← fresh (← kTyAt O key)
          readFact "effHandleV:forward"
          return .letv k' (.call mk (k :: ctxs'.flatMap live ++ shP?.toList)) (← outSusp O key v k')
    let exits ← match payTy T.pay with
      | none => suspArms ex
      | some pT => do
        let e ← fresh pT; let sv ← fresh T.sTy
        pure (Tm.case ex e (← abortArms e) sv (← suspArms sv))
    return .letv w (.prim .unroll [oP]) (.case w a retArm ex exits)
  -- A stored-continuation site (a clause keeps `κ`): the closures its clauses answer are its task
  -- body's code (`genMerges`), keyed by the handler and the `def`s its handled computation uses.
  let saved := (← get).siteMerge
  if stored then
    let keys := useKeys 64 te
    let key ← if keys.isEmpty then do
        let i := (← get).next
        pure s!"site {n} #{i}"
      else pure s!"{(site.map (·.handler)).getD ""}|{" ".intercalate keys}"
    modify fun st => { st with siteMerge := some (closTys 64 rT, key),
                               sitesIn := st.sitesIn ++ [(closTys 64 rT, key)] }
  let dTm ← match outM with
    | some O => withMachine O dbody
    | none => dbody
  modify fun st => { st with siteMerge := saved }
  setFn driveFn { name := s!"drive {n}", params := hvInner ++ shP?.toList ++ [oP],
                  body := dTm, ret := outTy }
  let o ← fresh T.ty
  -- The first run: on a stack of its own (none yet) when the site has one.
  let run (rest : List Var → CM Tm) : CM Tm := do
    match shP? with
    | some _ =>
      let reg ← stackRegister
      let z ← fresh (.int .w64); let prev ← fresh (.int .w64); let sh ← fresh (.int .w64)
      -- With a region, the stack is made here, holding it; else at its first frame.
      let mk : Tm := if cellAt.isSome then .prim (.stackNew siteTag) [] else .lit (.i64 0)
      return .letv z mk (.letv prev (.prim (.stackSwap reg) [z])
        (.letv o (.call bodyFn bOuter) (.letv sh (.prim (.stackSwap reg) [prev]) (← rest [sh]))))
    | none => return .letv o (.call bodyFn bOuter) (← rest [])
  run fun shs => return .call driveFn (hvOuter ++ shs ++ [o])

/-- The function `tF` applied to `a`: a λ's body at `a` (through transparent nodes and lifetime
abstractions, `lamOf`), or a closure call. -/
def applyTo (fuel : Nat) (ctx : Ctx) (tF : TExpr) (a : Var) : CM Tm := do
  match lamOf 64 tF with
  | some (k, .lam _ _ _ _ body) => conv fuel (some a :: (List.replicate k none ++ ctx)) body
  | _ => do
    let f ← fresh (← repJ tF.jdg)
    return .letv f (← conv fuel ctx tF) (.app f a)

/-- **`handle_n e with (h_ret, hs)`, erased**  `[spec §47]`. Read from the node: its name `n`, its
operations `E`, its clauses' kinds `ks`, its outer row `Σ` and the masks. Every clause must be
`abortive`, or `tail` with its direct call licensed (`CState.direct`); any other kind is a
stored-continuation site, left to the state machines (N3). The handled computation runs in place;
its value goes to `h_ret`, an abort of one of `n`'s operations to that operation's clause (the
handler's join: `catch_abort`), an abort of `Σ`'s handed on (`fwd_abort`). A tail-resumptive
clause is called where it is performed (`effPerform`). -/
def convHandle (fuel : Nat) (ctx : Ctx) (S : Row) (E : List (Qual × VTy × VTy)) (fs : Nat → CTy)
    (n : UInt32) (A R : VTy) (u : Masks) (ks : List ClauseKinds.HKind) (site : Option HSite)
    (tc te : TExpr) (boxed : Bool := false) (rule : Bool := false) : CM Tm := do
  let direct := (← get).direct.getD n []
  readFact (if rule then "effHandleT:kinds" else "effHandleV:kinds")
  -- The handled computation's outcome: with a machine operation (one of the node's clauses that is
  -- not called where it is performed, or one of `Σ`'s), the node is a drive (SPEC §49).
  let teM ← outInfoJ te.jdg
  if teM.isNone then
    for (k, j) in ks.zipIdx do
      match k.kind with
      | .abortive => pure ()
      | .tail =>
        unless direct[j]? == some true do
          throw s!"LIR: `effHandleV`: the clause {n}.{j} is tail-resumptive, but its direct call is not licensed (condition 2, or one closed clause at its nodes): outside the pure fragment"
      | .resumeOnce _ | .stored =>
        throw s!"LIR: `effHandleV`: the clause {n}.{j} is `{k.kind.tag}`, a stored-continuation site (N3): outside the pure fragment"
      | kd => throw s!"LIR: `effHandleV`: the clause {n}.{j} is `{kd.tag}`, whose rule is not built: outside the pure fragment"
  let (pre, c₁, c₂) ← splitCtx ctx u "effHandleV"
  -- The handler's pair, written in place: `h_ret` and each clause with its part of the context.
  let .tensorI _ _ _ _ uH tR tCs := tc
    | throw "LIR: `effHandleV`: a handler pair not written in place is outside the pure fragment"
  let (preH, cR, cCs) ← splitCtx c₁ uH "effHandleV"
  let mut parts : Array (Ctx × TExpr) := #[]
  let mut cur := cCs
  let mut tcur := tCs
  let mut preCs : Array (Tm → Tm) := #[]
  -- The clauses not written in place, as one value: a drive takes them apart (SPEC §49).
  let mut tuple : Option TExpr := none
  for _ in E do
    if tuple.isSome then break
    match tcur with
    | .tensorI _ _ _ _ uc c rest => do
      let (pc, cc, cr) ← splitCtx cur uc "effHandleV"
      preCs := preCs.push pc
      parts := parts.push (cc, c)
      cur := cr; tcur := rest
    | t =>
      if teM.isNone then
        throw "LIR: `effHandleV`: a clause tuple not written in place is outside the pure fragment"
      tuple := some t
  let tailCtx := cur
  -- The direct calls' functions, made at the first node of the name.
  for (k, j) in ks.zipIdx do
    if k.kind == .tail && direct[j]? == some true then
      let some (cc, c) := parts[j]? | throw "LIR: a clause"
      let some o := E[j]? | throw "LIR: an operation"
      ensureWork fuel n j cc.length S o c
  let wrap (b : Tm) : Tm := pre (preH (preCs.foldr (fun f t => f t) b))
  if let some T := teM then
    match tuple with
    | none => return wrap (← convDrive fuel S E fs n R ks site c₂ te T cR tR parts tailCtx none boxed)
    | some tt =>
      readFact "effHandleV:clause tuple"
      let tv ← fresh (← repJ tt.jdg)
      return wrap (.letv tv (← conv fuel tailCtx tt)
        (← convDrive fuel S E fs n R ks site c₂ te T cR tR parts [some tv] (some parts.size) boxed))
  let ctxs : List Ctx := cR :: parts.toList.map (·.1) ++ [tailCtx]
  let dropAll (keep : Option Nat) (b : Tm) : Tm :=
    drops ((ctxs.zipIdx.filter fun (_, i) => some i != keep).flatMap fun (c, _) => live c) b
  let pt ← rowPay (Row.ofEff n E 0 fs ++ S)
  let ps ← rowPay S
  let aT ← vty A
  modify fun st => { st with erased := st.erased.insert "handle" (st.erased.getD "handle" 0 + 1) }
  let retArm (a : Var) : CM Tm := do return dropAll (some 0) (← applyTo fuel cR tR a)
  match payTy pt with
  | none => return wrap (← bindTm (← conv fuel c₂ te) aT retArm)
  | some ptT =>
    readFact "effHandleV:join"
    let b ← fresh (.sum aT ptT); let a ← fresh aT; let e ← fresh ptT
    let arms ← casePay pt e fun j v => do
      let some (key, _) := pt[j]? | throw "LIR: a payload's summand"
      if key.1 == n then
        let idx := key.2.toNat
        let some (cc, c) := parts[idx]? | throw "LIR: an abortive clause"
        return dropAll (some (idx + 1)) (← applyTo fuel cc c v)
      else
        let some j' := payIdx ps key | throw s!"LIR: an abort of {key} outside the handler's row"
        return dropAll none (← injectPay ps j' v fun w => pure (.inj true w))
    return wrap (.letv b (← conv fuel c₂ te) (.case b a (← retArm a) e arms))

/-- **A tail-resumptive clause's work**, the function a `perform` of its operation calls
(`[spec §47]`, `tail_resumes`): the clause `λp. let (x, κ) = p; M` with each resume of `κ`
replaced by its answer (`TailResumesAt 0 M M'`, which the clause's kind gives,
`classifyHandler_sound`). It takes the argument `x` and answers the operation's answer, at the
payload of the handler's outer row `Σ`. Made once per operation. -/
def ensureWork (fuel : Nat) (n : UInt32) (j : Nat) (depth : Nat) (S : Row)
    (o : Qual × VTy × VTy) (c : TExpr) : CM Unit := do
  if (← get).works.contains (n, j) then return
  match c.unUse with
  | .bangThunkV _ _ _ (.lam _ _ _ _ (.tensorE _ _ _ _ _ _ (.var _ _ 0 _) tM)) => do
    readFact "effHandleV:tail work"
    let x ← fresh (← vty o.2.1)
    let kv ← fresh .unit
    let ph ← rowPay S
    let bT ← vty o.2.2
    let fi ← reserveFn s!"clause {n}.{j}"
    -- At an outer row with machine operations the work is a machine (SPEC §49).
    let wm ← outInfo? bT S
    modify fun st => { st with works := st.works.insert (n, j) (fi, ph, wm) }
    let ctx₀ : Ctx := some kv :: some x :: none :: List.replicate depth none
    let (body, ret) ← match wm with
      | none => pure (← convWork fuel 0 ph ctx₀ tM, resTy bT ph)
      | some W => pure (← withMachineK W (convWorkK fuel 0 ctx₀ tM), W.ty)
    -- `κ`'s slot holds a unit: every resume of it is its answer, and it is dropped there.
    setFn fi { name := s!"clause {n}.{j}", params := [x], body := .letv kv .unit body, ret }
  | _ => throw s!"LIR: the clause {n}.{j} is not `λp. let (x, κ) = p; M`"

/-- **The context of a rule-written handler's code run where its operation is performed**
(`openOK`): at a node whose context has `depth` slots, each slot dead but `main`'s I/O externs the
code `body` reads (under its `k` binders), each made again here (`ioClos`, as `convMain` makes
it). The slots, and the bindings that make them.  `[spec §64]` -/
def ioCtx (depth k : Nat) (body : Expr) : CM (Ctx × (Tm → Tm)) := do
  let io := (← get).mainIO
  let n := io.size
  let mut ctx : Ctx := []
  let mut binds : Tm → Tm := id
  for p in List.range depth do
    let slot ← if depth ≥ n && p ≥ depth - n && ClauseKinds.mentions (p + k) body then
        match io[p - (depth - n)]? with
        | some (some (op, A)) => do
          let aT ← vty A
          let x ← fresh aT
          let c ← ioClos 8 op aT
          let b := binds
          binds := fun t => b (.letv x c t)
          pure (some x)
        | _ => pure none
      else pure none
    ctx := ctx ++ [slot]
  return (ctx, binds)

/-- **The tail-resuming rule's answering function**, the function a `perform` of its operation
calls (`effHandleT`, `tail_resume_direct`): the `j`-th answering function `g : !U(A ⊸ F_{Σ_N} B)`
of the node's tuple, its λ's body at the argument, at the payload of `Σ_N` (linear operations: none
but `Div`'s `tick`, answered where it is performed). Made once per operation.  `[spec §64]` -/
def ensureAns (fuel : Nat) (n : UInt32) (j : Nat) (depth : Nat) (SN : Row)
    (o : Qual × VTy × VTy) (g : TExpr) : CM Unit := do
  if (← get).works.contains (n, j) then return
  let some (k, .lam _ _ _ _ body) := lamOf 64 g
    | throw s!"LIR: the answering function {n}.{j} is not a λ"
  readFact "effHandleT:answering function"
  let x ← fresh (← vty o.2.1)
  let ph ← rowPay SN
  let bT ← vty o.2.2
  let fi ← reserveFn s!"clause {n}.{j}"
  modify fun st => { st with works := st.works.insert (n, j) (fi, ph, none) }
  let (cw, binds) ← ioCtx depth (k + 1) body.erase
  let b ← conv fuel (some x :: (List.replicate k none ++ cw)) body
  setFn fi { name := s!"clause {n}.{j}", params := [x], body := binds b, ret := resTy bT ph }

/-- **A `[handle-last]` operation's work**, the function a `perform` of its operation calls
(`effHandleL`, `last_resume_direct`, `last_cancel_direct`): the `j`-th work
`w : !U(A ⊸ F_{Σ_W}(B ⊕ X))` of the node's tuple, its λ's body at the argument, at the payload of
`Σ_W`. Made once per operation.  `[spec §64]` -/
def ensureLastWork (fuel : Nat) (n : UInt32) (j : Nat) (depth : Nat) (SW : Row)
    (o : Qual × VTy × VTy) (X : VTy) (w : TExpr) : CM Unit := do
  if (← get).lasts.contains (n, j) then return
  let some (k, .lam _ _ _ _ body) := lamOf 64 w
    | throw s!"LIR: the work {n}.{j} is not a λ"
  readFact "effHandleL:work"
  let x ← fresh (← vty o.2.1)
  let phW ← rowPay SW
  let bT ← vty o.2.2
  let xT ← vty X
  let fi ← reserveFn s!"work {n}.{j}"
  modify fun st => { st with lasts := st.lasts.insert (n, j) (fi, phW, xT) }
  let (cw, binds) ← ioCtx depth (k + 1) body.erase
  let b ← conv fuel (some x :: (List.replicate k none ++ cw)) body
  setFn fi { name := s!"work {n}.{j}", params := [x], body := binds b,
             ret := resTy (.sum bT xT) phW }

/-- **`perform` of a `[handle-last]` operation, erased** (SPEC §64): the work called on the
argument; `inl y` answers `y` where the operation is performed (`last_resume_direct`); `inr z`
leaves at the operation's cancel summand of the row's payload, as an abort, so every finaliser
between here and the node runs on the way (`last_cancel_direct`, `cancel_prefix`); a raise from
the work leaves at the same summand, beside `z`, and the node raises it on (the finaliser `κ.2 ()`
runs first, as `[finalise]` runs it). The summand is the node's own: no handler between here and
the node holds the operation's name, so nothing between catches it. -/
def lastPerform (fuel : Nat) (ctx : Ctx) (S : Row) (o : OpSig) (fi : Nat)
    (phW : List ((UInt32 × UInt32) × LTy)) (xT : LTy) (c : TExpr) : CM Tm := do
  readFact "effPerform:last direct call"
  modify fun st => { st with erased := st.erased.insert "perform" (st.erased.getD "perform" 0 + 1) }
  let p ← rowPay S
  let some jc := payIdx p (o.n, o.i)
    | throw s!"LIR: `effPerform` of ({o.n}, {o.i}) at a row without its cancel summand"
  let bT ← vty o.B
  let leaveWith (w : Var) : CM Tm := injectPay p jc w fun e => pure (.inj true e)
  let onBX (bx : Var) (inj : Var → CM Tm) : CM Tm := do
    let y ← fresh bT; let z ← fresh xT
    return .case bx y (.inj false y) z (← inj z)
  bindTm (← conv fuel ctx c) (← vty o.A) fun v => do
    match payTy phW with
    | none =>
      let r ← fresh (.sum bT xT)
      return .letv r (.call fi [v]) (← onBX r leaveWith)
    | some pwT =>
      let sT := LTy.sum xT pwT
      let r ← fresh (.sum (.sum bT xT) pwT)
      let bx ← fresh (.sum bT xT); let e ← fresh pwT
      let viaL (z : Var) : CM Tm := do
        let w ← fresh sT
        return .letv w (.inj false z) (← leaveWith w)
      let w ← fresh sT
      return .letv r (.call fi [v]) (.case r bx (← onBX bx viaL) e
        (.letv w (.inj true e) (← leaveWith w)))

/-- **`[handle-last]`, erased** (`effHandleL`, SPEC §64): read from the node, its name `n`, its
operations `E`, its outer row `Σ` and the masks. Each control operation's work is called where it
is performed (`lastFacts`, `lastPerform`, made first by `prepWorks`); the handled computation runs
in place; its value goes to `h_ret`, an abort of an abortive operation of `n` to its work, its
clause (`catch_abort`), an abort of `Σ`'s on outward (`fwd_abort`), and a control operation's
cancel summand to the node's join: `inl z` runs the exit at `z` (`last_cancel_exit`), `inr e`
raises the work's error on outward. -/
def convHandleL (fuel : Nat) (ctx : Ctx) (S : Row) (E : List (Qual × VTy × VTy))
    (fs : Nat → CTy) (n : UInt32) (A R : VTy) (u : Masks) (tc te : TExpr) : CM Tm := do
  readFact "effHandleL:kinds"
  let lasts := (← get).lasts
  for (o, j) in E.zipIdx do
    unless ClauseKinds.isAbortive o || lasts.contains (n, j) do
      throw s!"LIR: `effHandleL`: the work {n}.{j} is not licensed to be called where it is performed (a work that performs, or a node of its name that differs): outside the fragment"
  let teM ← outInfoJ te.jdg
  let (pre, c₁, c₂) ← splitCtx ctx u "effHandleL"
  let .tensorI _ _ _ _ uH tR tWN := tc
    | throw "LIR: `effHandleL`: a handler not written in place is outside the fragment"
  let (preH, cR, cWN) ← splitCtx c₁ uH "effHandleL"
  let .tensorI _ _ _ _ uWN tW tN := tWN
    | throw "LIR: `effHandleL`: works and exits not written in place are outside the fragment"
  let (preWN, cW, cN) ← splitCtx cWN uWN "effHandleL"
  let partsOf (c₀ : Ctx) (t₀ : TExpr) : CM (Array (Ctx × TExpr) × Array (Tm → Tm) × Ctx) := do
    let mut parts : Array (Ctx × TExpr) := #[]
    let mut pres : Array (Tm → Tm) := #[]
    let mut cur := c₀
    let mut tcur := t₀
    for _ in E do
      match tcur with
      | .tensorI _ _ _ _ uc c rest => do
        let (pc, cc, cr) ← splitCtx cur uc "effHandleL"
        pres := pres.push pc
        parts := parts.push (cc, c)
        cur := cr; tcur := rest
      | _ => throw "LIR: `effHandleL`: a tuple not written in place is outside the fragment"
    return (parts, pres, cur)
  let (works, preWs, wTail) ← partsOf cW tW
  let (exits, preNs, nTail) ← partsOf cN tN
  let wrapD (b : Tm) : Tm :=
    pre (preH (preWN (preWs.foldr (fun f t => f t) (preNs.foldr (fun f t => f t) b))))
  -- With a machine operation of `Σ` in the handled computation (a stored loop's `tick`, SPEC §64),
  -- the node is a drive (SPEC §49): an abortive operation's clause is its work, a control one's
  -- cancel goes to its exit, a suspension of `Σ`'s is forwarded.
  if let some T := teM then
    let union (a b : Ctx) : Ctx := a.zipWith (fun x y => x <|> y) b
    let mut parts : Array (Ctx × TExpr) := #[]
    let mut unused : Ctx := union wTail nTail
    for (o, j) in E.zipIdx do
      let some w := works[j]? | throw "LIR: a work"
      let some nf := exits[j]? | throw "LIR: an exit"
      if ClauseKinds.isAbortive o then
        parts := parts.push w; unused := union unused nf.1
      else
        let some (_, phW, _) := lasts[(n, j)]? | throw "LIR: a work"
        unless (payTy phW).isNone do
          throw "LIR: `effHandleL` whose work raises, around a computation with a machine operation, is outside the fragment"
        parts := parts.push nf; unused := union unused w.1
    return wrapD (← convDrive fuel S E fs n R (E.map ClauseKinds.lastKind) none c₂ te T cR tR parts
      unused none)
  let ctxs : List Ctx := cR :: works.toList.map (·.1) ++ [wTail] ++ exits.toList.map (·.1) ++ [nTail]
  let dropAll (keep : Option Nat) (b : Tm) : Tm :=
    drops ((ctxs.zipIdx.filter fun (_, i) => some i != keep).flatMap fun (c, _) => live c) b
  let wrap (b : Tm) : Tm :=
    pre (preH (preWN (preWs.foldr (fun f t => f t) (preNs.foldr (fun f t => f t) b))))
  let pt ← rowPay (Row.ofEff n E 0 fs ++ S)
  let ps ← rowPay S
  let aT ← vty A
  modify fun st => { st with erased := st.erased.insert "handle" (st.erased.getD "handle" 0 + 1) }
  let retArm (a : Var) : CM Tm := do return dropAll (some 0) (← applyTo fuel cR tR a)
  let exitIdx (j : Nat) : Nat := 1 + E.length + 1 + j
  let some ptT := payTy pt
    | return wrap (← bindTm (← conv fuel c₂ te) aT retArm)
  readFact "effHandleL:join"
  let b ← fresh (.sum aT ptT); let a ← fresh aT; let e ← fresh ptT
  let arms ← casePay pt e fun j v => do
    let some (key, _) := pt[j]? | throw "LIR: a payload's summand"
    if key.1 == n then
      let idx := key.2.toNat
      let some o := E[idx]? | throw "LIR: an operation"
      if ClauseKinds.isAbortive o then
        -- An abortive operation's clause is its work.
        let some (cc, w) := works[idx]? | throw "LIR: an abortive work"
        return dropAll (some (idx + 1)) (← applyTo fuel cc w v)
      let some (cc, nf) := exits[idx]? | throw "LIR: an exit"
      let some (_, phW, xT) := lasts[(n, idx)]? | throw "LIR: a work"
      match payTy phW with
      | none => return dropAll (some (exitIdx idx)) (← applyTo fuel cc nf v)
      | some pwT => do
        -- `inl z`: the exit at `z`; `inr e`: the work's raise, on outward.
        let z ← fresh xT; let ew ← fresh pwT
        let outE ← coercePay phW ps ew fun w => pure (.inj true w)
        return .case v z (dropAll (some (exitIdx idx)) (← applyTo fuel cc nf z)) ew (dropAll none outE)
    else
      let some j' := payIdx ps key | throw s!"LIR: an abort of {key} outside the handler's row"
      return dropAll none (← injectPay ps j' v fun w => pure (.inj true w))
  return wrap (.letv b (← conv fuel c₂ te) (.case b a (← retArm a) e arms))

/-- The variable a term answers through the nodes that keep their premise's value (`ret`,
`unbox`, `[sub]`, …): the alias `return κ`. -/
def aliasOf : Nat → TExpr → Option Nat
  | 0, _ => none
  | f + 1, t => match t with
    | .var _ _ i _ => some i
    | .effSub _ _ _ _ _ c => aliasOf f c
    | t => match transparent? t with
      | some c => aliasOf f c
      | none => none

/-- **The clause's body with its resumes removed** (`TailResumesAt`), `κ` in the slot `k`: on
each path, through `[⊕E]`, `[⊗E]`, `[1E]`, `[let]` and `[sub]`, to the resume `κ.1 y`
(`resumeB`), whose value is `y`; the right unit `x <- κ.1 y; return x` (`tailLeafB`,
`returns0B`) is the resume; an alias `κ' <- return κ` moves `κ` to its binder. An abort of the
path's `[let]`s is handed on at the handler's row's payload `ph`. -/
def convWork (fuel : Nat) (k : Nat) (ph : Pay) (ctx : Ctx) (t : TExpr) : CM Tm := do
  match fuel with
  | 0 => throw "LIR: the typed term is too deep"
  | fuel + 1 =>
  let answer (y : Var) : CM Tm := do
    match payTy ph with
    | none => return .var y
    | some _ => return .inj false y
  if resumeB k t then
    match t.unSub with
    | .app _ _ y _ _ u _ => do
      let (pre, c₁, c₂) ← splitCtx ctx u "app"
      let some (some yv) := c₂[y]? | throw "LIR: a resume's answer is not live"
      return pre (drops (live c₁) (leaf c₂ (some y) (← answer yv)))
    | _ => throw "LIR: a resume"
  match t with
  | .bind _ _ A _ u tM tN | .effLet _ _ A _ _ u tM tN =>
    let row := match t with | .effLet _ _ _ _ S .. => some S | _ => none
    if tailLeafB k tM && returns0B tN then
      -- The right unit: the resume's answer is the clause's.
      let (pre, c₁, c₂) ← splitCtx ctx u "bind"
      return pre (drops (live c₂) (← convWork fuel k ph c₁ tM))
    else if aliasOf 64 tM == some k then
      -- `κ' <- return κ`: the alias's slot holds `κ`.
      let (pre, c₁, c₂) ← splitCtx ctx u "bind"
      let some (some kv) := c₁[k]? | throw "LIR: an alias of a continuation that is not live"
      return pre (leaf c₁ (some k) (← convWork fuel 0 ph (some kv :: c₂) tN))
    else
      let (pre, c₁, c₂) ← splitCtx ctx u "bind"
      let aT ← vty A
      let p ← match row with | some S => rowPay S | none => pure []
      match payTy p with
      | none =>
        return pre (← bindTm (← conv fuel c₁ tM) aT fun x => convWork fuel (k + 1) ph (some x :: c₂) tN)
      | some pT =>
        let m ← fresh (.sum aT pT); let x ← fresh aT; let e ← fresh pT
        let pass ← coercePay p ph e fun e' => pure (.inj true e')
        return pre (.letv m (← conv fuel c₁ tM)
          (.case m x (← convWork fuel (k + 1) ph (some x :: c₂) tN) e (drops (live c₂) pass)))
  | .sumE _ _ A B _ u tV t₁ t₂ => do
    let (pre, c₁, c₂) ← splitCtx ctx u "sumE"
    let aT ← vty A; let bT ← vty B
    return pre (← bindTm (← conv fuel c₁ tV) (.sum aT bT) fun sv => do
      let x ← fresh aT; let y ← fresh bT
      return .case sv x (← convWork fuel (k + 1) ph (some x :: c₂) t₁)
        y (← convWork fuel (k + 1) ph (some y :: c₂) t₂))
  | .tensorE _ _ A B _ u tV tM => do
    let (pre, c₁, c₂) ← splitCtx ctx u "tensorE"
    let aT ← vty A; let bT ← vty B
    return pre (← bindTm (← conv fuel c₁ tV) (.pair aT bT) fun pv => do
      let x ← fresh aT; let y ← fresh bT
      return .letpair x y pv (← convWork fuel (k + 2) ph (some y :: some x :: c₂) tM))
  | .unitE _ _ _ u tV tM => do
    let (pre, c₁, c₂) ← splitCtx ctx u "unitE"
    return pre (← bindTm (← conv fuel c₁ tV) .unit fun v => return .drop v (← convWork fuel k ph c₂ tM))
  | .effSub _ _ _ _ _ c => convWork fuel k ph ctx c
  | .lendScope _ _ _ c | .litView _ _ c | .unfoldStep _ _ c => convWork fuel k ph ctx c
  | _ => throw s!"LIR: a tail-resumptive clause's path at `{ruleName t}` ends in no resume"

/-- A spine of `lolliE` nodes: its arguments evaluated outermost first, then its function: a
constant's operation (`expand`), a λ's body (β), or a closure call. -/
def convSpine (fuel : Nat) (ctx : Ctx) (t : TExpr) : CM Tm := do
  match fuel with
  | 0 => throw "LIR: the typed term is too deep"
  | fuel + 1 =>
  let (as, h) := spineOf 4096 t
  let resT ← repJ t.jdg
  -- A borrow whose callback is a λ written there: the callback's body at the borrow, with no
  -- closure made (the λ-value's construction does nothing).
  match as, cbConst (headOf 64 h) with
  | [(u₁, cb), (u₂, x)], true =>
    match lamOf 64 cb with
    | some (k, .lam _ _ _ _ body) => do
      readFact "lolliE:callback beta"
      let (pre₁, cA, cF) ← splitCtx ctx u₁ "lolliE"
      let (pre₂, cX, cH) ← splitCtx cF u₂ "lolliE"
      let xT ← repJ x.jdg
      let cbT ← repJ cb.jdg
      return pre₁ (pre₂ (← bindTm (← conv fuel cX x) xT fun xv => do
        let body ← expandCb fuel (headOf 64 h) xv cbT
          (fun b => conv fuel (some b :: (List.replicate k none ++ cA)) body) resT
        return leaf cH none body))
    | _ => go fuel ctx as [] h resT
  | _, _ => go fuel ctx as [] h resT
where
  cbConst : TExpr → Bool
    | .withbor1 .. | .withbor2 .. | .withbor3 .. | .withload .. | .withswap .. | .sliceBorrowM ..
    | .sliceBorrowI .. | .withborSM .. | .withborSI .. | .withborF2M .. | .withborF2I ..
    | .withbor1U .. | .withbor2U .. | .withbor3U .. | .withloadU .. | .sliceBorrowMU ..
    | .sliceBorrowIU .. => true
    | _ => false
  go (fuel : Nat) (ctx : Ctx) : List (Masks × TExpr) → List Var → TExpr → LTy → CM Tm
    | (u, ta) :: rest, vs, h, resT => do
      let (pre, cA, cF) ← splitCtx ctx u "lolliE"
      let aT ← repJ ta.jdg
      return pre (← bindTm (← conv fuel cA ta) aT fun a => go fuel cF rest (a :: vs) h resT)
    | [], vs, h, resT => do
      -- `vs` holds the arguments innermost first: the order they apply in.
      let hd := headOf 64 h
      match constArity hd with
      | some n =>
        if vs.length < n then
          let f ← fresh (← repJ h.jdg)
          return leaf ctx none (.letv f (← constClos fuel hd) (← applyAll f vs))
        let first := vs.take n
        let more := vs.drop n
        if more.isEmpty then return leaf ctx none (← expand fuel hd first resT)
        let r ← fresh (← satTy (← repJ hd.jdg) n)
        return leaf ctx none (.letv r (← expand fuel hd first (← tyOf r)) (← applyAll r more))
      | none =>
        match lamOf 64 h, vs with
        | some (k, .lam _ lj _ _ body), a :: more => do
          readFact "lolliE:beta"
          let (_, r) ← answerOf (← repJ lj)
          let ctx' := some a :: (List.replicate k none ++ ctx)
          if more.isEmpty then conv fuel ctx' body
          else bindTm (← conv fuel ctx' body) r fun g => applyAll g more
        | _, _ => do
          let f ← fresh (← repJ h.jdg)
          return .letv f (← conv fuel ctx h) (← applyAll f vs)

/-- The lend of a cell allocated for it (`TExpr.lendCell`, `withbor (alloc v) cb`, `lendCellB`):
as a spine, its cell's allocation `allocLent`, which the frame pass may place in the frame. -/
def convLendCell (fuel : Nat) (ctx : Ctx) (t inner : TExpr) : CM Tm := do
  let (as, h) := spineOf 8 inner
  match as with
  | [(u₁, cb), (u₂, aApp)] =>
    let (bs, ah) := spineOf 8 aApp
    match bs, headOf 64 ah with
    | [(u₃, v)], .alloc _ _ A => do
      readFact "lendCell:cell"
      -- The scope this cell is allocated for (`withScope`), taken before the callback is converted.
      let scope := (← get).scopeCell
      modify fun st => { st with scopeCell := none }
      let s ← match scope with
        | some s => pure s
        | none => newScope
      let cls ← classOf A
      let (pre₁, c₁, cF) ← splitCtx ctx u₁ "lolliE"
      let cbv ← fresh (← repJ cb.jdg)
      let cbTm ← conv fuel c₁ cb
      let (pre₂, c₂, cH) ← splitCtx cF u₂ "lolliE"
      let (pre₃, c₃, cA) ← splitCtx c₂ u₃ "lolliE"
      let vv ← fresh (← repJ v.jdg)
      let vTm ← conv fuel c₃ v
      let cell ← fresh (← repJ aApp.jdg)
      let body ← expand fuel (headOf 64 h) [cell, cbv] (← repJ t.jdg)
      if scope.isSome then modify fun st => { st with scopeOwner := some s }
      return pre₁ (.letv cbv cbTm (pre₂ (pre₃ (.letv vv vTm (leaf cA none
        (.letv cell (.prim (.allocLent s cls) [vv]) (leaf cH none body)))))))
    | _, _ => conv fuel ctx inner
  | _ => conv fuel ctx inner

/-- A `use` of a `def`: its body's term made once per key, instantiated at each later use. -/
def convUse (fuel : Nat) (ctx : Ctx) (info : TInfo) (j : Jdg) (decl : Nat) (targs : List VTy)
    (body : TExpr) : CM Tm := do
  let key := useKey decl targs info j (← get).mach
  let slots : List (Nat × Var) := ctx.zipIdx.filterMap fun (s, i) => s.map (i, ·)
  -- A body that takes a closure is specialised to each use, as it is to each set of argument codes
  -- (docs/compiler.md §3.1): its codes would join the closures of every use otherwise.
  if takesClos 64 (← repJ j) then
    readFact "use:per-use body"
    return ← conv fuel ctx body
  match (← get).uses[key]? with
  | some tp =>
    -- UNPROVED: that a `use` body converted at one context is, renamed, its conversion at
    -- another context with the same key, and that a slot live here and not in the template is
    -- one the body's derivation drops (`Ctx.DeadP`). It should hold because the key fixes the
    -- declaration, its type arguments and the judgment, and the body reads its slots by index:
    -- a slot it reads was live at the first use, or that conversion would have failed. It is
    -- not checked against this use's derivation. If it fails, a live owned value is dropped (a
    -- leak), or the template's copies and drops are those of another context.
    -- The slots the template reads must be live here; any other live slot is dropped.
    let mut m : Std.HashMap Var Var := {}
    let mut ok := true
    for (i, x) in tp.slots do
      match ctx[i]? with
      | some (some y) => m := m.insert x y
      | _ => ok := false
    if ok then
      readFact "use:key, shared"
      let kept := tp.slots.map (·.1)
      let extra := slots.filter fun (i, _) => !kept.contains i
      modify fun st => { st with scopeCopy := {} }
      return drops (extra.map (·.2)) (← renameTm m tp.tm)
    conv fuel ctx body
  | none =>
    let tm ← conv fuel ctx body
    modify fun s => { s with uses := s.uses.insert key ⟨slots, tm⟩ }
    readFact "use:key"
    return tm

/-- A division by a literal at which it cannot fail (`TExpr.divLit`): the dividend, then the
operation with no error arm. The node is over `(λa. B) e` (`divLitB`): `e` is the typed term's
bound computation. -/
def convDivLit (fuel : Nat) (ctx : Ctx) (j : Jdg) (op : HostOp) (c : IntLit) (inner : TExpr) :
    CM Tm := do
  let rT ← repJ j
  match peelRet inner with
  | .bind _ _ A _ u tM _ => do
    let (pre, c₁, c₂) ← splitCtx ctx u "bind"
    let aT ← vty A
    readFact "divLit:divisor"
    return pre (leaf c₂ none (← bindTm (← conv fuel c₁ tM) aT fun a => do
      let d ← fresh (match c with | .u8 _ => .int .w8 | .i64 _ => .int .w64 | _ => i32T)
      return .letv d (.lit c) (.prim (.divLit op) [a, d])))
  | _ => conv fuel ctx inner
where
  peelRet : TExpr → TExpr
    | .ofRet _ _ _ t | .ret _ _ _ t => peelRet t
    | t => t

/-- A constant as a value: a closure of a code that applies it, one argument at a time. -/
def constClos (fuel : Nat) (c : TExpr) : CM Tm := do
  let some n := constArity c | throw "LIR: not a constant"
  let cT ← repJ c.jdg
  if n == 0 then return ← expand fuel c [] cT
  curry fuel c cT [] n
where
  curry (fuel : Nat) (c : TExpr) (t : LTy) (got : List Var) : Nat → CM Tm
    | 0 => throw "LIR: a constant of no arguments"
    | k + 1 => do
      let .thunk ck := t.peel | throw s!"LIR: a constant at a non-function type {t}"
      let (some aT, rT) ← answerOf t | throw "LIR: a constant takes no argument"
      let ctx : Ctx := got.reverse.map some
      mkClos "const" ctx ck (some aT) rT fun ctx' => do
        let got' := (ctx'.filterMap id).reverse
        if k == 0 then expand fuel c got'.reverse.reverse rT
        else curry fuel c rT got' k

/-- **An unwinding borrow** (`withborUE d`, SPEC §19): `(f [] r) then b. (r, b) unwind d r`. The
owner lent as `genLend` does; the callback's value `b` gives `(r, b)`; its abort ends the lend, runs
the finaliser `d` on the owner, and is handed on (`then_fin`). Whether the callback may abort is
read from the node's row `S`: at a row with no abortive operation (a call-graded row, SPEC §63) it
is `genLend`'s, whatever the shape of its answer.  `[spec §47, §63]` -/
def genLendU (fuel : Nat) (op : Op) (src : Var) (cbT : LTy) (call : Var → CM Tm) (S : Row)
    (td : TExpr) : CM Tm := do
  match fuel with
  | 0 => throw "LIR: the typed term is too deep"
  | fuel + 1 =>
  let (some bT, rT) ← answerOf cbT | throw "LIR: a borrow's callback takes no borrow"
  let aborts := (payTy (← rowPay S)).isSome
  match rT.peel with
  | .sum vT eT => if !aborts then genLend op src cbT call else do
    readFact "withborU:finaliser"
    let pr ← fresh (.pair (← tyOf src) bT)
    let o ← freshLike src; let b ← fresh bT
    let r ← fresh rT
    let v ← fresh vT; let e ← fresh eT
    let q ← fresh (.pair (← tyOf src) vT)
    let u ← fresh .unit
    let fin ← match constArity (headOf 64 td) with
      | some 1 => expand fuel (headOf 64 td) [o] .unit
      | _ => throw "LIR: an unwinding borrow's finaliser that is not a constant is outside the pure fragment"
    return .letv pr (.prim op [src]) (.letpair o b pr (.letv r (← call b)
      (.case r v (.letv q (.pair o v) (.inj false q)) e (.letv u fin (.drop u (.inj true e))))))
  | _ => genLend op src cbT call

/-- A borrowing constant applied to its first argument `x`, its callback's call given by `call`. -/
def expandCb (_fuel : Nat) (c : TExpr) (x : Var) (cbT : LTy) (call : Var → CM Tm) (resT : LTy) :
    CM Tm := do
  readFact s!"{ruleName c}:expand"
  match c with
  | .withbor1 .. | .sliceBorrowI .. => genLend (.lend false) x cbT call
  | .withbor2 .. | .sliceBorrowM .. => genLend (.lend true) x cbT call
  | .withbor3 .. => genLend .relend x cbT call
  | .withload .. => genWithload x cbT call
  | .withswap .. => genWithswap x cbT call
  | .withborSM .. | .withborF2M .. => genLendTree true x cbT call
  | .withborSI .. | .withborF2I .. => genLendTree false x cbT call
  | .withbor1U _ _ _ _ S _ td | .sliceBorrowIU _ _ _ _ S _ td => genLendU _fuel (.lend false) x cbT call S td
  | .withbor2U _ _ _ _ S _ td | .sliceBorrowMU _ _ _ _ S _ td => genLendU _fuel (.lend true) x cbT call S td
  | .withbor3U _ _ _ _ _ S _ td => genLendU _fuel .relend x cbT call S td
  | .withloadU .. => genWithload x cbT call
  | c => throw s!"LIR: `{ruleName c}` is not a borrow (answer {resT})"

/-- **A constant applied to its arguments**, `args` in the order they apply, its answer of type
`resT`. -/
def expand (fuel : Nat) (c : TExpr) (args : List Var) (resT : LTy) : CM Tm := do
  readFact s!"{ruleName c}:expand"
  match c, args with
  | .alloc _ _ A, [v] => return .prim (.alloc (← classOf A)) [v]
  | .free .., [x] => return .prim .free [x]
  | .swap .., [x, v] => return .prim .swap [x, v]
  | .copy .., [x] | .arrCopy .., [x] => dup x fun x x' => pure (.pair x x')
  | .forgetImm .., [x] | .forgetMut .., [x] | .forgetUnk .., [x] | .arrForget .., [x] =>
    return .drop x .unit
  | .dtor _ _ A, [x] => do readFact "dtor:type"; genDtor 64 A x
  | .hostOp _ _ op, [x] => return .prim (.host op) [x]
  | .arrNew _ j _, [p] => do
    let (pT, aT) ← arrowOf (← repJ j)
    let .pair _ fT := pT.peel | throw "LIR: array_new's argument"
    genTab aT fT p
  | .arrFree _ j _, [p] => do
    let (pT, _) ← arrowOf (← repJ j)
    let .pair fT aT := pT.peel | throw "LIR: array_free's argument"
    genArrFree fT aT p
  | .arrSize .., [a] | .sliceLenM .., [a] => return .prim .size [a]
  | .arrLen .., [v] => return .prim .len [v]
  | .arrReplace .., [p] | .sliceReplaceM .., [p] =>
    letpairM p fun a r => letpairM r fun i x => do
      readFact s!"{ruleName c}:slot swap"
      return .prim .replace [a, i, x]
  | .arrGet .., [p] | .sliceGetM .., [p] => do
    let inRange := (← get).inRange
    if inRange then readFact s!"{ruleName c}:in range"
    letpairM p fun v i => pure (.prim (.idx (!inRange)) [v, i])
  | .sliceSplitI .., [p] | .sliceSplitM .., [p] =>
    letpairM p fun v i => pure (.prim (.split true) [v, i])
  | .sliceEmptyI .., [] | .sliceEmptyM .., [] | .arrEmpty .., [] => return .prim .emptyFam []
  | .sliceSwapM .., [p] =>
    letpairM p fun v r => letpairM r fun i k => pure (.prim .swapSlots [v, i, k])
  | .countFold _ j _, [p] => do
    let (pT, sT) ← arrowOf (← repJ j)
    let .pair fT _ := pT.peel | throw "LIR: count_fold's argument"
    genCount fT sT p
  | .countTry _ j _ _, [p] => do
    let (pT, rT) ← arrowOf (← repJ j)
    let .pair fT _ := pT.peel | throw "LIR: count_try's argument"
    let .sum sT eT := rT.peel | throw "LIR: count_try's answer"
    genCountTry fT sT eT p
  | .boundedFix _ j _ _, [p] => do
    let (some pT, _) ← answerOf (← repJ j) | throw "LIR: bounded_fix takes no argument"
    let .pair sT _ := pT.peel | throw "LIR: bounded_fix's argument"
    readFact "boundedFix:budget"
    genFix sT p
  | .iterate _ j S St B R, [p] => do
    let (pT, rT) ← arrowOf (← repJ j)
    let .pair fT _ := pT | throw "LIR: iterate's argument"
    -- At a stored loop's program, `tick` is a machine operation: a machine per node.  [spec §64]
    if (← get).mach.contains (divName, 0) then
      return ← genIterK fT S (← vty B) (← vty R) (← vty St) p
    -- `iterate` under the runtime: a function per node, its back edge a tail call.  [spec §62]
    unless (← get).divRt do
      throw "LIR: `iterate` whose ticks the runtime does not answer (a stored loop's `reify`) is outside the pure fragment"
    let (pT, rT) ← arrowOf (← repJ j)
    let .pair fT _ := pT | throw "LIR: iterate's argument"
    readFact "iterate:row"
    genIter fT rT (← rowPay S) p
  | .withbor1 .., [x, cb] | .sliceBorrowI .., [x, cb] => genLend (.lend false) x (← tyOf cb) (callCb cb)
  | .withbor2 .., [x, cb] | .sliceBorrowM .., [x, cb] => genLend (.lend true) x (← tyOf cb) (callCb cb)
  | .withbor3 .., [m, cb] => genLend .relend m (← tyOf cb) (callCb cb)
  | .withload .., [x, cb] => genWithload x (← tyOf cb) (callCb cb)
  | .withswap .., [m, f] => genWithswap m (← tyOf f) fun old => pure (.app f old)
  | .allocS _ _ σ, [v] => allocTree v resT σ
  | .freeS _ j _, [v] => do
    let (_, vT) ← arrowOf (← repJ j)
    freeTree v vT
  | .withborSM .., [x, cb] | .withborF2M .., [x, cb] => genLendTree true x (← tyOf cb) (callCb cb)
  | .withborSI .., [x, cb] | .withborF2I .., [x, cb] => genLendTree false x (← tyOf cb) (callCb cb)
  | .withbor1U _ _ _ _ S _ td, [x, cb] | .sliceBorrowIU _ _ _ _ S _ td, [x, cb] =>
    genLendU fuel (.lend false) x (← tyOf cb) (callCb cb) S td
  | .withbor2U _ _ _ _ S _ td, [x, cb] | .sliceBorrowMU _ _ _ _ S _ td, [x, cb] =>
    genLendU fuel (.lend true) x (← tyOf cb) (callCb cb) S td
  | .withbor3U _ _ _ _ _ S _ td, [m, cb] => genLendU fuel .relend m (← tyOf cb) (callCb cb) S td
  | .withloadU .., [x, cb] => genWithload x (← tyOf cb) (callCb cb)
  | .foldOwn _ _ F _, [g] | .foldReuse _ _ F _, [g] => do
    let k : FoldKind := match c with | .foldReuse .. => .reuse | _ => .own
    let .thunk fk := resT.peel | throw "LIR: a fold's answer is not a closure"
    let (some muT, R) ← answerOf resT | throw "LIR: a fold takes no structure"
    readFact s!"{ruleName c}:shape"
    let (recV, _) ← genFoldFns k F muT muT (← tyOf g)
    mkClos "fold" [some g] fk (some muT) R fun ctx' => do
      match ctx' with
      | some x :: some g' :: _ => return .call recV [g', x]
      | _ => throw "LIR: a fold's environment"
  | .foldImm _ _ F y _ _, [g] => do
    -- The answer's `∀'y` is erased (SPEC §44): a closure on the borrow.
    let .thunk fk := resT.peel | throw "LIR: a fold's answer is not a closure"
    let (some lT, R) ← answerOf resT | throw "LIR: fold_imm takes no borrow"
    let .imm cellT := lT.peel | throw "LIR: fold_imm's argument is not a borrow"
    let muT ← vty (VTy.immReborrow (.var y) (.mu F.ty))
    readFact s!"{ruleName c}:shape"
    let (_, recL) ← genFoldFns .imm F muT cellT (← tyOf g)
    mkClos "fold_imm" [some g] fk (some lT) R fun ctx' => do
      match ctx' with
      | some l :: some g' :: _ => return .call recL [g', l]
      | _ => throw "LIR: fold_imm's environment"
  | .unfoldN _ _ C _, [g] => do
    let .thunk uk := resT.peel | throw "LIR: unfold's answer is not a closure"
    let (some sT, _) ← answerOf resT | throw "LIR: unfold takes no state"
    let obs ← genUnfold (← cty C) C (← tyOf g) sT
    mkClos "unfold" [some g] uk (some sT) (.thunk (.nu (← cty C))) fun ctx' => do
      match ctx' with
      | some st :: some g' :: _ => return .clos obs [g', st]
      | _ => throw "LIR: unfold's environment"
  | c, _ => throw s!"LIR: `{ruleName c}` applied to {args.length} arguments"
end


/-- The clauses of a handler pair written in place, `(h_ret, (c₀, (c₁, … ())))`: `n` of them. -/
def clausesOf : Nat → TExpr → List TExpr
  | 0, _ => []
  | n + 1, .tensorI _ _ _ _ _ c rest => c :: clausesOf n rest
  | _, _ => []

/-- **The directly called clauses' functions, made first** (`ensureWork`): a `perform` may be
converted before its handler's node (a function made before the `handle` and called inside it).
Each tail-resumptive clause whose direct call is licensed, at the first `handle` node of its
name, with the depth of the node's context.  `[spec §47]` -/
def prepWorks (fuel : Nat) (depth : Nat) (t : TExpr) : CM Unit := do
  match fuel with
  | 0 => throw "LIR: the typed term is too deep"
  | fuel + 1 =>
  let here : Option (Row × List (Qual × VTy × VTy) × UInt32 × List ClauseKinds.HKind × TExpr) :=
    match t with
    | .effHandleV _ _ S E _ n _ _ _ ks _ _ tc _ => some (S, E, n, ks, tc)
    | .effHandleVB _ _ S E _ n _ _ _ _ ks _ _ tc _ => some (S, E, n, ks, tc)
    | _ => none
  if let some (S, E, n, ks, .tensorI _ _ _ _ _ _ tCs) := here then
    let direct := (← get).direct.getD n []
    let cs := clausesOf E.length tCs
    for (k, j) in ks.zipIdx do
      if k.kind == .tail && direct[j]? == some true then
        if let (some c, some o) := (cs[j]?, E[j]?) then
          ensureWork (1 <<< 22) n j depth S o c
  -- The tail-resuming rule's answering functions, and `[handle-last]`'s works.  [spec §64]
  match t with
  | .effHandleT _ _ _ SN E _ n _ _ _ _ _ _ (.tensorI _ _ _ _ _ _ tCs) _ =>
    let direct := (← get).direct.getD n []
    let cs := clausesOf E.length tCs
    for (o, j) in E.zipIdx do
      if !ClauseKinds.isAbortive o && direct[j]? == some true then
        if let some g := cs[j]? then ensureAns (1 <<< 22) n j depth SN o g
  | .effHandleL _ _ _ SW E _ Xs n _ _ _ _ _ (.tensorI _ _ _ _ _ _ (.tensorI _ _ _ _ _ tW _)) _ =>
    let ws := clausesOf E.length tW
    for (o, j) in E.zipIdx do
      if !ClauseKinds.isAbortive o && (← get).mach.last.contains (n, j.toUInt32) then
        if let some w := ws[j]? then ensureLastWork (1 <<< 22) n j depth SW o (Xs j) w
  | _ => pure ()
  for (sc, c) in t.children do
    let d := match sc with | .push k => depth + k | .fresh k => k
    prepWorks fuel d c

/-! ### `main` -/

/-- Take the capabilities back from `main`'s value `(caps, a)` (`ncaps` of them, right-nested):
each cell freed with its contents, and `a` the program's value. -/
def epilogue (r : Var) (ncaps : Nat) : CM Tm := do
  if ncaps == 0 then return .var r
  letpairM r fun caps a => do
    let rec split : Nat → Var → CM (List Var × (Tm → Tm))
      | 0, _ => pure ([], id)
      | 1, v => pure ([v], id)
      | k + 1, v => do
        let .pair xT rT := (← tyOf v).peel | throw "LIR: main's capabilities"
        let x ← fresh xT; let rest ← fresh rT
        let (xs, wrap) ← split k rest
        pure (x :: xs, fun t => .letpair x rest v (wrap t))
    let (xs, wrap) ← split ncaps caps
    let mut body : Tm := .var a
    for x in xs.reverse do
      let .ref cT := (← tyOf x).peel | throw "LIR: a capability that is not a cell"
      let c ← fresh cT
      body := .letv c (.prim .free [x]) (.drop c body)
    return wrap body

/-- Drive a loop (SPEC §11, §14): observe `next` until it finishes, its value the program's. -/
def genDrive (lT : LTy) : CM Nat := do
  let fi ← reserveFn "drive"
  let l ← fresh lT
  let rT ← selTy lT 0
  let .sum vT nT := rT.peel | throw "LIR: main's loop does not answer a sum"
  let r ← fresh rT
  let v ← fresh vT; let l' ← fresh nT
  setFn fi { name := "drive", params := [l], ret := vT,
             body := .letv r (.sel l 0) (.case r v (.var v) l' (.call fi [l'])) }
  return fi

/-- `main`'s value as `reify` of its body (SPEC §62: a `main` that loops is the loop value of its
body): through the nodes that keep their child's value, the `reify` constant applied to the
body's thunk. Its split's masks, the thunk, and the `reify` node's row `Σ`, result `B` and
residual `R`.  `[spec §62]` -/
def mainReify? (t : TExpr) : Option (Masks × TExpr × Row × VTy × VTy) :=
  match peel 64 t with
  | .lolliE _ _ _ _ u ta tf => match headOf 64 tf with
    | .reify _ _ S B R _ => some (u, ta, S, B, R)
    | _ => none
  | _ => none
where
  peel : Nat → TExpr → TExpr
    | 0, t => t
    | f + 1, t => match transparent? t with
      | some c => peel f c
      | none => t

/-- **The LIR of `main`**: its externs bound to their implementations (`exts`, in declaration
order; the context's slot `i` is extern `n − 1 − i`), its typed term converted, and its
capabilities taken back. With `loops`, `main`'s value is a loop, driven until it finishes. -/
def convMain (exts : List Ext) (ctx : List (VTy × Bool)) (t : TExpr) (C : CTy) (ncaps : Nat)
    (loops : Bool) (rt : Bool := false) : CM (Tm × LTy) := do
  let n := ctx.length
  let mut binds : List (Tm → Tm) := []
  let mut cx : Array (Option Var) := #[]
  for ((A, liveS), i) in ctx.zipIdx do
    if !liveS then cx := cx.push none; continue
    let aT ← vty A
    let x ← fresh aT
    let some e := exts[n - 1 - i]? | throw "LIR: main's context has a slot no extern gives"
    match e with
    | .cap fd => do
      let l ← fresh i32T
      let k := (← get).statics.size
      -- A capability's cell is as wide as its class (`Checked.classAt` of its contents, SPEC §57):
      -- a `swap` may put a wider value in it.
      let cls ← match A with
        | .ref B => classOf B
        | _ => pure []
      modify fun s => { s with statics := s.statics.push cls }
      binds := (fun b => .letv l (.lit (.i32 fd.toUInt32)) (.letv x (.prim (.staticCell k) [l]) b)) :: binds
    | .clock => do
      let l ← fresh (.int .w64)
      let k := (← get).statics.size
      let cls ← match A with
        | .ref B => classOf B
        | _ => pure []
      modify fun s => { s with statics := s.statics.push cls }
      binds := (fun b => .letv l (.lit (.i64 0)) (.letv x (.prim (.staticCell k) [l]) b)) :: binds
    | .io op => do
      let c ← ioClos 8 op aT
      binds := (fun b => .letv x c b) :: binds
    cx := cx.push (some x)
  modify fun st => { st with mainIO := (ctx.zipIdx.map fun ((A, _), i) => match exts[n - 1 - i]? with
    | some (.io op) => some (op, A)
    | _ => none).toArray }
  prepWorks (1 <<< 22) cx.size t
  if rt then
    unless (← get).divRt do
      throw "LIR: a `main` the runtime's clause drives, with a handler of `Div` of its own, is outside the pure fragment"
    let r ← graded cx.toList binds
    genMerges
    return r
  if loops && (← get).divRt then
    if let some (u, ta, S, B, R) := mainReify? t then
      let r ← runtimeMain cx.toList u ta S B R binds
      genMerges
      return r
  let body ← conv (1 <<< 22) cx.toList t
  genMerges
  let mT ← repJ (.comp C)
  let r ← fresh mT
  let (tm, resT) ← if loops then do
      let d ← genDrive mT
      let fT ← tyOf (← fresh (← selTy mT 0)) -- the loop's `next` answer
      let .sum vT _ := fT.peel | throw "LIR: main's loop"
      let v ← fresh vT
      let ep ← epilogue v ncaps
      pure (Tm.letv r body (.letv v (.call d [r]) ep), ← resultTy vT)
    else pure (Tm.letv r body (← epilogue r ncaps), ← resultTy mT)
  return (binds.foldl (fun t f => f t) tm, resT)
where
  resultTy (t : LTy) : CM LTy := do
    if ncaps == 0 then return t
    match t.peel with
    | .pair _ a => pure a
    | _ => throw s!"LIR: main's value with capabilities is not a pair: {t}"
  /-- **A `main` the runtime's clause drives**  `[spec §63]`: `main` is a computation at the graded
  row of `Div` alone, `F[div call] (B + R)` (`Frontend.Check.rtMainOf`), run under the runtime's
  clause (`rtMainE`, `DivRuntime.rtMain`), which answers every tick *next* where it is performed
  (`tickTm`). `inl b` finishes with `b`; `inr r` is not reached (the runtime never answers
  *close*), and its branch runs without end, as `rtMain`'s `Ω`. -/
  graded (cx : Ctx) (binds : List (Tm → Tm)) : CM (Tm × LTy) := do
    readFact "rtMain:main, at the runtime"
    modify fun st => { st with erased := st.erased.insert "handle" (st.erased.getD "handle" 0 + 1) }
    let some (S, _) := effParts C | throw "LIR: a graded `main`'s type"
    if (payTy (← rowPay S)).isSome then
      throw "LIR: a graded `main` at a row with aborts is outside the pure fragment"
    let body ← conv (1 <<< 22) cx t
    let .sum bT rT := (← repJ (.comp C)).peel | throw "LIR: a graded `main`'s answer is not `B + R`"
    let r ← fresh (.sum bT rT)
    let b ← fresh bT; let x ← fresh rT
    let resT ← resultTy bT
    let ep ← epilogue b ncaps
    let spin ← reserveFn "closed"
    let x₁ ← fresh rT
    setFn spin { name := "closed", params := [x₁], body := .call spin [x₁], ret := resT }
    let tm := .letv r body (.case r b ep x (.call spin [x]))
    return (binds.foldl (fun t f => f t) tm, resT)
  /-- **`main`'s loop under the runtime**  `[spec §62]`: `main`'s value is `reify` of its body
  `t ()`, which the runtime drives with *next* until it finishes (SPEC §11). The drive answers
  *next* to every tick of the body (`drive_reify_tick`, `Core/DivDrive.lean`), so the program is
  the body run with each tick answered *next* where it is performed (`tickTm`): `inl b` finishes
  with `b` (`drive_reify_done`); `inr r` is a loop closed with its residual, which the drive
  observes without end (`drive_reify_closed`), a run that does not finish. -/
  runtimeMain (cx : Ctx) (u : Masks) (ta : TExpr) (S : Row) (B R : VTy)
      (binds : List (Tm → Tm)) : CM (Tm × LTy) := do
    readFact "reify:main, at the runtime"
    modify fun st => { st with erased := st.erased.insert "handle" (st.erased.getD "handle" 0 + 1) }
    let p ← rowPay S
    if (payTy p).isSome then
      throw "LIR: `main`'s loop at a row with aborts (the platform's handler) is outside the pure fragment"
    let (pre, cA, cF) ← splitCtx cx u "lolliE"
    let unitV ← fresh .unit
    let body ← applyTo (1 <<< 22) cA ta unitV
    let bT ← vty B; let rT ← vty R
    let r ← fresh (.sum bT rT)
    let b ← fresh bT; let x ← fresh rT
    let resT ← resultTy bT
    let ep ← epilogue b ncaps
    -- The loop `closed r`, which every observation skips: it holds the residual, and does not
    -- finish.
    let spin ← reserveFn "closed"
    let x₁ ← fresh rT
    setFn spin { name := "closed", params := [x₁], body := .call spin [x₁], ret := resT }
    let tm := pre (leaf cF none (.letv unitV .unit (.letv r body
      (.case r b ep x (.call spin [x])))))
    return (binds.foldl (fun t f => f t) tm, resT)

/-- **Loops of tail calls** (SPEC §49): each call in tail position made a point whose callee's
outcome may hold the machine's own suspended computation (`loop`, read off the layouts'
classes) passes its callee's outcome on instead: the call closes a loop of tail calls through the
machine (a recursion's next turn, a drive's clause resuming `κ`), which stays a loop in constant
space. -/
def tailPass (s : CState) (loop : Nat × Var × OutInfo × Nat → Bool) : Except String (Prog × CState) := do
  let act : CM Unit := do
    for site in s.tailSites do
      if loop site then
        let (fn, _, M, _) := site
        let oP ← fresh M.ty
        readFact "machine:tail call"
        setFn fn { name := "tail", params := [oP], body := .var oP, ret := M.ty }
  let ((), s') ← act.run s
  return ({ fns := s'.fns, codes := s'.codes, main := default, mainTy := default, ty := s'.ty,
            data := s'.data, statics := s'.statics, lits := s'.lits, stackKs := s'.stackKs }, s')

/-- **State cells** (SPEC §49): each machine operation whose suspended computation's closure class
holds itself (`recursive`, the layouts' classes that keep their environment on the heap, §35)
has its codes made again with its state in a cell, written in place. -/
def cellPass (s : CState) (recursive : Nat → Bool) : Except String (Prog × CState) := do
  let act : CM Unit := do
    for (m, kcs) in s.done do
      let ops := kcs.filterMap fun (op, kc) => if recursive kc then some op else none
      unless ops.isEmpty || m.cell.isSome || m.stack.isSome do
        let _ ← genMach m ops
  let ((), s') ← act.run s
  return ({ fns := s'.fns, codes := s'.codes, main := default, mainTy := default, ty := s'.ty,
            data := s'.data, statics := s'.statics, lits := s'.lits, stackKs := s'.stackKs }, s')

/-- **The levels whose state cell is passed on** (SPEC §50), from a conversion's machines and the
layouts' recursive classes (`recursive`, as `cellPass` reads them): each machine whose body takes
its continuation (`withMachineK`), with no call in tail position, whose points are all at one
operation and whose state there is a cell (its suspended computation's class holds itself, not
at `unr`): its number and its state's type. -/
def threadedOf (s : CState) (recursive : Nat → Bool) : Std.HashMap Nat LTy := Id.run do
  let mut out : Std.HashMap Nat LTy := {}
  for (m, kcs) in s.done do
    unless m.threadable && m.tails.isEmpty do continue
    match kcs with
    | [(op, kc)] =>
      if recursive kc && !m.info.unrs.contains op && m.points.all (·.op == op) then
        out := out.insert m.start (machStateTy m op)
    | _ => pure ()
  return out

/-- **The stack machines** (SPEC §52), from a conversion's machines and the layouts: each machine
whose level's cell `threadedOf` passes on (its suspended computation's class holds itself, its
points at one operation, no call in tail position, not `unr`), whose every call point calls a
level of itself (`calleeCodes`, the layouts' classes of the callee's suspended computations, are
its own code), and whose operation is in `stackOps` (every `handle` node of it keeps `κ`: a stored
site, which gives the frames one owner): its number and its frame's state type, each call point's
state without the callee's `k`. -/
-- UNPROVED: that a stack machine's frames have one owner each, so that a level's frame may live
-- on the task stack and be popped by its answer, abort or cancel. It should hold because every
-- `handle` node of the operation stores `κ`, boxed, at no `unr` operation (`stackOps`, read off
-- the nodes' clause kinds and qualifiers), so one site's `κ` holds the stack, and because every
-- call point calls a level of the machine itself. That last fact is read off the layouts'
-- closure classes (`calleeCodes`), which is not a typing fact. If it fails, a frame is popped
-- while a level above it still runs, or a level resumes on another stack's frame.
def stackedOf (s : CState) (recursive : Nat → Bool) (stackOps : MachSet)
    (calleeCodes : Var → OutInfo → List Nat) : Std.HashMap Nat LTy := Id.run do
  let th := threadedOf s recursive
  let mut out : Std.HashMap Nat LTy := {}
  for (m, kcs) in s.done do
    unless th.contains m.start do continue
    let [(op, kc)] := kcs | continue
    unless stackOps.contains op do continue
    let self := m.points.all fun p => match p.kTy, p.outVar, p.callee with
      | none, _, _ => true
      | some _, some o, some M => M.ty.sameRep m.info.ty && !(calleeCodes o M).isEmpty &&
          (calleeCodes o M).all (· == kc) &&
          p.swapAt.isNone
      | _, _, _ => false
    unless self do continue
    let ps := m.points.toList
    out := out.insert m.start
      ((payTy (ps.zipIdx.map fun (p, i) => ((0, i.toUInt32), tupleTy p.argTys))).getD .unit)
  return out

/-- Convert a checked `main` to a program; `threaded` the machines whose level's cell is passed on
(`threadedOf` of a first conversion), `stacked` the stack machines (`stackedOf`). -/
def convertProg (exts : List Ext) (ctx : List (VTy × Bool)) (t : TExpr) (C : CTy) (ncaps : Nat)
    (loops : Bool) (census : Bool := false) (direct : Std.HashMap UInt32 (List Bool) := {})
    (mach : MachSet := {}) (divRt : Bool := false) (threaded : Std.HashMap Nat LTy := {})
    (stacked : Std.HashMap Nat LTy := {}) (classes : List (VTy × List LTy) := [])
    (rt : Bool := false) : Except String (Prog × CState) := do
  let ((m, mT), s) ← (convMain exts ctx t C ncaps loops rt).run
    { census, direct, mach, divRt, threaded, stacked, classes }
  return ({ fns := s.fns, codes := s.codes, main := m, mainTy := mT, ty := s.ty, data := s.data,
            statics := s.statics, lits := s.lits, stackKs := s.stackKs }, s)

end Backend2

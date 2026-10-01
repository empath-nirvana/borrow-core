import Std.Data.HashMap
import Std.Data.HashSet
import Backend.Clos.Unwind

/-!
# Backend — lowering handlers, control operations and cancels  `[spec §19]`

`hnd`, `ubind` and `perform` (from `Convert`) become closure IR that `Unwind` finishes: no handler
stack, no search, and a captured continuation is a value of statically known size.

**Handlers and finaliser frames.** A finaliser frame `ubind (N, D) M` is `let r = fin D M in N r`:
the frame `fin` runs `D` when `M` unwinds, and `N` is an ordinary call. A handler of a name whose
operations are all abortive (no `perform` of it in the program) is `catch n e`, then a `case` that
calls the answer clause on a value or the clause of the caught operation on its argument. A
handler of a name with control operations (a *control handler*) is
`let r = run (λ_. e) () in drive (hr, cls) r`:

- the body becomes a code of its own, `B`, so that its suspensions are its own;
- `drive` (`Drv`) takes the body's outcome: `inl v` goes to the answer clause; `inr (p, k)` of an
  operation of the name to that operation's clause on its argument and `κ`; any other `inr`
  passes outward (*forwarding*): `drive` suspends with `p`, and when it is resumed it resumes `k`
  and drives again, which reinstalls the handler as the deep handler does;
- `κ` (`Kap`) is a closure over the handler and `k`: its resume entry is the closure `Res`,
  `λy. drive (hr, cls) (run k (inl y))`, its cancel entry cancels `k` (below).

**Machines.** A code that may suspend answers its *outcome*: `inl v` when it returns `v`, or
`inr (p, k)` when it suspends with the payload `p`. The payload is a variant of an `n`-ary sum, one
variant per operation of the program (`con`), so operations of any argument types share it. `k`
is the suspended computation: a closure of the code's *resume code* `R` over its *state*, an
`n`-ary sum with one variant per **resumption point** of the body, holding the variables live
there. The resumption points are the `perform`s, the calls of codes that may suspend in non-tail
position, and `drive`'s forwarding. At a point the code builds its state and returns `inr`; each
frame it suspends through (`let`, `catch`, `fin`) passes the `inr` on. `R` takes `inl y` to resume
and `inr mask` to cancel, and switches on the state:

- **resume**: the point's continuation, its frames rebuilt around `y` (a call point first resumes
  its callee's `k`, and suspends again at the same point if the callee does);
- **cancel**: the callee's `k` cancelled first (innermost), then the finalisers of the point's
  `fin` frames, innermost first, and every other variable dropped. It answers `inl ()`, or
  `inr E`, the first error a finaliser raised whose name is not in `mask`: decision (C) of §19.

So a caller's state holds its callee's `k` at a call point: **suspension through calls nests**,
and `κ` is a value of statically known size. Which codes may suspend is the least solution of the
operations their bodies and callees may perform (the closure flow, `Backend/Clos/Flow.lean`), with
nothing written by the programmer. Codes called at one site share their convention, and so do a
code and a code it calls in tail position when the call closes a loop of tail calls, or when the
caller has no resumption point of its own: such a tail call passes its callee's outcome on, so a
loop of tail calls stays one, and a handler that resumes in tail position runs in constant stack.
Any other tail call is a resumption point. A call that may reach two codes that suspend
dispatches at its resume as it did at its call; a code that suspends through a call of itself has
a state that holds its own `k`, which the layout types make a recursive closure type, one heap
object per level (`Backend/README.md`).

**Tail-resumptive operations.** When every handler of a name has the same closed clause for an
operation, and the clause resumes `κ` once, in tail position, and neither suspends nor raises,
the operation is a direct call of the clause, its resume removed: the handler is the one known
statically, and nothing is suspended or resumed. So is a clause whose answer is computed by a
term that may raise, under a finaliser frame that resumes `κ` with the answer and cancels `κ` on
an unwind (`unwindClause?`): as a direct call, the unwind passes through the performing code's
own frames, which is what the cancel runs.

**Cancels.** `κ`'s cancel entry cancels `k` with the mask of the names of the handlers its region
may hold, then answers `()` or re-raises the kept error (`reraise`). The mask is the handler
sites reachable from the handler's body; it is the region's set exactly when no handler site is
reached again from its own body, which is checked when a finaliser may raise.
-/

namespace Backend.Clos

/-- A control handler: its name, and the codes `Capture` builds for it. -/
structure HInfo where
  n : UInt32
  body : Nat
  drv : Nat
  kap : Nat
  res : Nat
  /-- `drive`'s variables: the handler, the outcome, and the parts of its `case`. -/
  dVars : Array Var
  /-- `κ`'s variables. -/
  kVars : Array Var
  deriving Inhabited

structure KState where
  next : Var
  codes : Array Code
  hs : Array HInfo := #[]

abbrev KM := StateT KState (Except String)

def kfresh : KM Var := modifyGet fun s => (s.next, { s with next := s.next + 1 })

def kfreshN (k : Nat) : KM (Array Var) := do
  let mut a := #[]
  for _ in [0:k] do a := a.push (← kfresh)
  return a

def kregister (c : Code) : KM Nat :=
  modifyGet fun s => (s.codes.size, { s with codes := s.codes.push c })

def kset (k : Nat) (c : Code) : KM Unit :=
  modify fun s => { s with codes := s.codes.set! k c }

/-! ### The program's operations -/

/-- The payloads of a term's `perform`s and of its `raise`s. -/
def Tm.opPayloads : Tm → List Var × List Var
  | .perform p => ([p], [])
  | .raise p => ([], [p])
  | .letv _ e b =>
    let (a, c) := e.opPayloads
    let (a', c') := b.opPayloads
    (a ++ a', c ++ c')
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b | .hnd _ _ _ b | .ubind _ _ b => b.opPayloads
  | .case _ _ b₁ _ b₂ =>
    let (a, c) := b₁.opPayloads
    let (a', c') := b₂.opPayloads
    (a ++ a', c ++ c')
  | _ => ([], [])

/-- What the lowering knows of the program's operations. -/
structure Ops where
  defs : Std.HashMap Var Tm
  /-- The control operations, in order: the payload's variants. -/
  keys : Array OpKey
  /-- The names with a control operation. -/
  ctl : List UInt32
  /-- The abortive operations. -/
  aborts : List OpKey

def Ops.keyIdx (O : Ops) (k : OpKey) : Nat := (O.keys.toList.idxOf? k).getD 0

/-- The variants of the control operations of `n`, with their operation indices. -/
def Ops.keysOf (O : Ops) (n : UInt32) : List (Nat × Nat) :=
  O.keys.toList.zipIdx.filterMap fun ((m, i), j) => if m == n then some (j, i.toNat) else none

def Ops.of (p : Prog) : Except String Ops := do
  let terms := p.main :: p.codes.toList.map (·.body)
  let defs := terms.foldl defsOf {}
  let mut keys : Array OpKey := #[]
  let mut aborts : List OpKey := []
  for t in terms do
    let (ps, rs) := t.opPayloads
    for x in ps do
      let some k := payloadKey defs x | throw "capture: a control operation whose name is not a literal"
      if !keys.contains k then keys := keys.push k
    for x in rs do
      let some k := payloadKey defs x | throw "capture: a raise whose name is not a literal"
      if !aborts.contains k then aborts := aborts ++ [k]
  let ctl := (keys.toList.map (·.1)).eraseDups
  if let some (n, _) := aborts.find? (fun k => ctl.contains k.1) then
    throw s!"capture: the name {n} has both control and abortive operations, which is not lowered"
  return ⟨defs, keys, ctl, aborts⟩

/-! ### Handlers and finaliser frames -/

/-- Take the clause `j` out of the clause tuple `cls`, drop the others, and run `k c`. -/
def withClause (cls : Var) : Nat → (Var → KM Tm) → KM Tm
  | 0, k => do
    let c ← kfresh; let r ← kfresh
    return .letpair c r cls (.drop r (← k c))
  | j + 1, k => do
    let c ← kfresh; let r ← kfresh
    return .letpair c r cls (.drop c (← withClause r j k))

/-- `arm j` for the operation index `i` among `js`, by a compare per index; `i` is dropped. -/
def dispatchOp (i : Var) (arm : Nat → KM Tm) : List Nat → KM Tm
  | [] => throw "capture: a handler with no clause"
  | [j] => do return .drop i (← arm j)
  | j :: js => do
    let i' ← kfresh; let l ← kfresh; let pr ← kfresh; let bo ← kfresh; let u₁ ← kfresh
    let u₂ ← kfresh
    return .copy i i' (.letv l (.lit (.i32 j.toUInt32)) (.letv pr (.pair i' l)
      (.letv bo (.prim (.host (.rel .w32 .eq)) [pr])
        (.case bo u₁ (.drop u₁ (← dispatchOp i arm js)) u₂ (.drop u₂ (.drop i (← arm j)))))))

/-- A handler of abortive operations: `catch`, then the answer clause or the caught operation's
clause. -/
def abortiveSite (O : Ops) (n : UInt32) (hr cls : Var) (b : Tm) : KM Tm := do
  let ops := ((O.aborts.filter (·.1 == n)).map (·.2.toNat)).eraseDups
  let v ← kfresh
  if ops.isEmpty then return .letv v b (.drop cls (.app hr v))
  let r ← kfresh; let q ← kfresh; let m ← kfresh; let qi ← kfresh; let i ← kfresh; let w ← kfresh
  let onRaise ← dispatchOp i (fun j => withClause cls j fun c => pure (.app c w)) ops
  return .letv r (.catch n b) (.case r v (.drop cls (.app hr v)) q
    (.drop hr (.letpair m qi q (.drop m (.letpair i w qi onRaise)))))

/-- `drive`'s body: the answer clause, a clause of the name, or (`forward`) forwarding. -/
def drvBody (O : Ops) (h : HInfo) (forward : Bool) : KM Tm := do
  let #[hr, cls, r, v, q, pl, k] := h.dVars | throw "capture: drive's variables"
  let K := O.keys.size
  let mut chain : Tm := .absurd pl
  if forward then
    let y ← kfresh; let d ← kfresh
    chain := .letv y (.await pl k) (.letv d (.clos h.drv [hr, cls]) (.app d y))
  for (idx, j) in (O.keysOf h.n).reverse do
    let w ← kfresh; let cls₂ ← kfresh; let kap ← kfresh; let arg ← kfresh
    let call ← withClause cls₂ j fun c => pure (.app c arg)
    chain := .when pl idx K w (.copy cls cls₂ (.letv kap (.clos h.kap [hr, cls, k])
      (.letv arg (.pair w kap) call))) chain
  return .case r v (.drop cls (.app hr v)) q (.letpair pl k q chain)

/-- `drive`'s body without its forwarding, when its handler's body suspends with no other name's
operation: the forwarding arm is unreachable. -/
def noForward : Tm → Tm
  | .case r v a q (.letpair pl k q' chain) => .case r v a q (.letpair pl k q' (go pl chain))
  | t => t
where
  go (pl : Var) : Tm → Tm
    | .when s k n x b r => .when s k n x b (go pl r)
    | _ => .absurd pl

/-- `κ`'s body: `inl ()` gives the resume closure `Res`; `inr ()` cancels `k` with `mask` and
answers `()`, or re-raises the error the cancel kept (`reraise`). -/
def kapBody (h : HInfo) (mask : UInt64) (reraise : Bool) : Except String Tm := do
  let #[hr, cls, k, s, s', u₁, u₂, mk, mm, e, eu, eq] := h.kVars | throw "capture: κ's variables"
  let err : Tm := if reraise then .reraise eq mask else .drop eq .unit
  return .letv s' (.var s) (.case s' u₁ (.drop u₁ (.clos h.res [hr, cls, k])) u₂
    (.drop u₂ (.drop hr (.drop cls (.letv mk (.lit (.i64 mask)) (.letv mm (.inj true mk)
      (.letv e (.app k mm) (.case e eu (.var eu) eq err))))))))

/-- A control handler's site: its body becomes the code `B`, run and driven. -/
def controlSite (O : Ops) (n : UInt32) (hr cls : Var) (b : Tm) : KM Tm := do
  let fvb := b.fvs
  let u ← kfresh
  let cB ← kregister ⟨fvb, u, .drop u b⟩
  let cDrv ← kregister default
  let cKap ← kregister default
  let cRes ← kregister default
  let dVars ← kfreshN 7
  let kVars ← kfreshN 12
  let h : HInfo := { n, body := cB, drv := cDrv, kap := cKap, res := cRes, dVars, kVars }
  kset cDrv ⟨[dVars[0]!, dVars[1]!], dVars[2]!, ← drvBody O h true⟩
  kset cKap ⟨[kVars[0]!, kVars[1]!, kVars[2]!], kVars[3]!, ← liftM (kapBody h 0 false)⟩
  let rv ← kfreshN 7
  kset cRes ⟨[rv[0]!, rv[1]!, rv[2]!], rv[3]!, .letv rv[4]! (.inj false rv[3]!)
    (.letv rv[5]! (.run rv[2]! rv[4]!) (.letv rv[6]! (.clos cDrv [rv[0]!, rv[1]!])
      (.app rv[6]! rv[5]!)))⟩
  modify fun s => { s with hs := s.hs.push h }
  let t ← kfresh; let u₀ ← kfresh; let r ← kfresh; let d ← kfresh
  return .letv t (.clos cB fvb) (.letv u₀ .unit (.letv r (.run t u₀)
    (.letv d (.clos cDrv [hr, cls]) (.app d r))))
where
  liftM {α} (x : Except String α) : KM α := match x with
    | .ok a => pure a
    | .error e => throw e

/-- Lower the handlers and finaliser frames of a term. -/
def handlers (O : Ops) : Tm → KM Tm
  | .hnd n hr cls b => do
    let b ← handlers O b
    if O.ctl.contains n then controlSite O n hr cls b else abortiveSite O n hr cls b
  | .ubind nn dd b => do
    let b ← handlers O b
    let r ← kfresh
    if nn != dd then return .letv r (.fin false dd b) (.app nn r)
    -- The clauses as one code (`markUbinds`): `inj₁ r` continues, `inj₂ ()` finalises. The
    -- continuing call is through a variable of its own, so that its result type is its own.
    let i ← kfresh; let d' ← kfresh
    return .letv r (.fin false dd b) (.letv i (.inj false r) (.letv d' (.var dd) (.app d' i)))
  | .letv x e b => return .letv x (← handlers O e) (← handlers O b)
  | .letpair x y p b => return .letpair x y p (← handlers O b)
  | .case s x b₁ y b₂ => return .case s x (← handlers O b₁) y (← handlers O b₂)
  | .copy x x' b => return .copy x x' (← handlers O b)
  | .drop x b => return .drop x (← handlers O b)
  | t => pure t

/-! ### Which codes suspend -/

/-- The calls in tail position of a term, by their function variables. -/
def Tm.tailCalls : Tm → List Var
  | .app f _ => [f]
  | .letv _ _ b | .letpair _ _ _ b | .copy _ _ b | .drop _ b => b.tailCalls
  | .case _ _ b₁ _ b₂ | .when _ _ _ _ b₁ b₂ => b₁.tailCalls ++ b₂.tailCalls
  | _ => []

/-- The calls of a term, by their function variables (`run` aside). -/
def Tm.calls : Tm → List Var
  | .app f _ => [f]
  | .letv _ e b => e.calls ++ b.calls
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b | .catch _ b | .fin _ _ b | .catchAll b => b.calls
  | .case _ _ b₁ _ b₂ | .when _ _ _ _ b₁ b₂ => b₁.calls ++ b₂.calls
  | _ => []

/-- The functions a term calls or runs. -/
def Tm.callees : Tm → List Var
  | .app f _ | .run f _ => [f]
  | .letv _ e b => e.callees ++ b.callees
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b | .catch _ b | .fin _ _ b | .catchAll b => b.callees
  | .case _ _ b₁ _ b₂ | .when _ _ _ _ b₁ b₂ => b₁.callees ++ b₂.callees
  | _ => []

/-- The names of a term's `catch` frames. -/
def Tm.catches : Tm → List UInt32
  | .catch n b => n :: b.catches
  | .letv _ e b => e.catches ++ b.catches
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b | .fin _ _ b | .catchAll b => b.catches
  | .case _ _ b₁ _ b₂ | .when _ _ _ _ b₁ b₂ => b₁.catches ++ b₂.catches
  | _ => []

/-- The finalisers of a term's finaliser frames. -/
def Tm.finalisers : Tm → List Var
  | .fin _ dd b => dd :: b.finalisers
  | .letv _ e b => e.finalisers ++ b.finalisers
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b | .catch _ b | .catchAll b => b.finalisers
  | .case _ _ b₁ _ b₂ | .when _ _ _ _ b₁ b₂ => b₁.finalisers ++ b₂.finalisers
  | _ => []

/-- The analysis of the program after `handlers`. -/
structure SFacts where
  S : Solver
  /-- Every code's operations, as payload variants: those it may suspend with. -/
  skeys : Array (List Nat)
  /-- A `sel` code's operations per projection: a call whose argument is a known injection may
  suspend only with that projection's (a loop's `close` with none, say). -/
  skeysG : Array (Option (List Nat × List Nat)) := #[]
  /-- The codes that answer outcomes. -/
  poll : Array Bool
  /-- The codes that may raise. -/
  raises : Array Bool
  /-- `Unwind`'s facts: the keys each code and term may raise. -/
  U : UFacts
  /-- `drive`'s code's handler. -/
  drvOf : Std.HashMap Nat HInfo
  /-- Every code's convention class, by its representative: codes of one class answer the same
  outcome type. -/
  cls : Array Nat := #[]

/-- The codes of the closures `x` may hold; none for a variable the analysis has not seen. -/
def SFacts.codesOf (F : SFacts) (x : Var) : List Nat :=
  if x < F.S.num.vars then F.S.closuresAt (F.S.num.idx (.var x)) else []

def SFacts.pollAt (F : SFacts) (f : Var) : Bool := (F.codesOf f).any (F.poll[·]?.getD false)

def unionKeys (a b : List Nat) : List Nat := b.foldl (fun acc k => if acc.contains k then acc else acc ++ [k]) a

/-- The projection a call's argument selects, when it is a known injection. -/
def Ops.selArg (O : Ops) (a : Var) : Option Bool :=
  match O.defs[a]?.map Tm.tail with
  | some (.inj b _) => some b
  | _ => none

/-- The operations a call of the code `c` on an argument that selects `b` may suspend with. -/
def SFacts.keysAt (F : SFacts) (c : Nat) (b : Option Bool) : List Nat :=
  match b, F.skeysG[c]?.getD none with
  | some b, some (k₁, k₂) => if b then k₂ else k₁
  | _, _ => F.skeys[c]?.getD []

/-- The operations a term of the code `self` may suspend with. `sel` gives the injection some
variables are known to hold (the code's parameter, at a projection): a `case` on one runs one arm,
and a call on one runs that projection of its callee (a loop's `close`, say, which suspends with
none of its observations' operations). -/
def sKeysOf (O : Ops) (F : SFacts) (self : Nat) (sel : List (Var × Bool)) : Tm → List Nat
  | .perform p => match payloadKey O.defs p with
    | some k => [O.keyIdx k]
    | none => []
  | .await _ _ => match F.drvOf[self]? with
    | some h => (F.skeys[h.body]?.getD []).filter fun j => O.keys[j]!.1 != h.n
    | none => []
  | .app f a =>
    let b := (sel.lookup a).orElse fun _ => O.selArg a
    (F.codesOf f).foldl (fun acc c => unionKeys acc (F.keysAt c b)) []
  | .letv x e b =>
    let sel' := match e with
      | .var y => match sel.lookup y with | some v => (x, v) :: sel | none => sel
      | .inj v _ => (x, v) :: sel
      | _ => sel
    unionKeys (sKeysOf O F self sel e) (sKeysOf O F self sel' b)
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b | .catch _ b | .fin _ _ b | .catchAll b =>
    sKeysOf O F self sel b
  | .case s _ b₁ _ b₂ => match (sel.lookup s).orElse fun _ => O.selArg s with
    | some false => sKeysOf O F self sel b₁
    | some true => sKeysOf O F self sel b₂
    | none => unionKeys (sKeysOf O F self sel b₁) (sKeysOf O F self sel b₂)
  | .when _ _ _ _ b₁ b₂ => unionKeys (sKeysOf O F self sel b₁) (sKeysOf O F self sel b₂)
  | _ => []

/-- A term of the code `self`, in tail position when `tail`, has a resumption point that is not a
tail call: a `perform`, a live forwarding, or a call of a code that may suspend. -/
def ownPoints (O : Ops) (F : SFacts) (self : Nat) (tail : Bool) : Tm → Bool
  | .perform _ => true
  | .await _ _ => !(sKeysOf O F self [] (.await 0 0)).isEmpty
  | .app f a => !tail && (F.codesOf f).any fun c => !(F.keysAt c (O.selArg a)).isEmpty
  | .letv _ e b => ownPoints O F self false e || ownPoints O F self tail b
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b => ownPoints O F self tail b
  | .case _ _ b₁ _ b₂ | .when _ _ _ _ b₁ b₂ =>
    ownPoints O F self tail b₁ || ownPoints O F self tail b₂
  | .catch _ b | .fin _ _ b | .catchAll b => ownPoints O F self false b
  | _ => false

/-- `b` reaches `a` in the graph `succ`. -/
def reaches (succ : Array (List Nat)) (b a : Nat) : Bool := Id.run do
  let mut seen : Std.HashSet Nat := ({} : Std.HashSet Nat).insert b
  let mut work := [b]
  for _ in [0:succ.size + 1] do
    if work.contains a then return true
    let new := (work.flatMap fun c => succ[c]?.getD []).filter (!seen.contains ·) |>.eraseDups
    if new.isEmpty then return false
    seen := new.foldl (·.insert ·) seen
    work := new
  return false

/-- The analysis: the flow, the operations each code may suspend with (the least solution, by
iteration), and the convention: the classes of codes called at one site, joined with the codes a
code calls in tail position, answer outcomes when one of them suspends. -/
def SFacts.of (O : Ops) (p : Prog) (hs : Array HInfo) : Except String SFacts := do
  let cs := p.constraints
  let some S := solve p.codes cs (1 <<< 40) | throw "capture: the flow analysis did not finish"
  let drvOf : Std.HashMap Nat HInfo := hs.foldl (fun m h => m.insert h.drv h) {}
  let n := p.codes.size
  let mut F : SFacts :=
    { S := S, skeys := .replicate n [], skeysG := .replicate n none, poll := .replicate n false,
      raises := .replicate n false,
      U := ⟨O.defs, S, #[], some []⟩, drvOf := drvOf }
  for _ in [0:(p.codes.size + 1) * (O.keys.size + 1) + 1] do
    let sk := p.codes.toList.zipIdx.map fun (c, k) => sKeysOf O F k [] c.body
    let skG := p.codes.toList.zipIdx.map fun (c, k) =>
      some (sKeysOf O F k [(c.param, false)] c.body, sKeysOf O F k [(c.param, true)] c.body)
    let same := (sk.zip F.skeys.toList).all (fun (a, b) => a.length == b.length) &&
      (skG.zip F.skeysG.toList).all fun
        | (some (a, b), some (c, d)) => a.length == c.length && b.length == d.length
        | _ => true
    F := { F with skeys := sk.toArray, skeysG := skG.toArray }
    if same then break
  let tailSucc := p.codes.map fun c => (c.body.tailCalls.flatMap F.codesOf).eraseDups
  let mut parent : Array Nat := (List.range p.codes.size).toArray
  for (c, k) in p.codes.toList.zipIdx do
    for f in c.body.calls do
      if let c₀ :: rest := F.codesOf f then
        for c' in rest do parent := ufUnion parent c₀ c'
    -- A tail call shares the caller's convention when it closes a loop of tail calls, which then
    -- passes its outcome on and runs in constant stack, or when the caller has no resumption
    -- point of its own, so that it adds nothing to the outcome's continuation. Any other tail
    -- call is a resumption point.
    let own := ownPoints O F k true c.body
    -- A wrapper that may tail-call several codes that suspend keeps its own convention: its
    -- calls are resumption points, so a suspension's continuation is of one code, and resuming
    -- it does not dispatch.
    let susp := (c.body.tailCalls.flatMap F.codesOf).eraseDups.filter fun c' =>
      !(F.skeys[c']?.getD []).isEmpty
    let wrapper := !own && susp.length ≤ 1
    for f in c.body.tailCalls do
      for c' in F.codesOf f do
        if wrapper || reaches tailSucc c' k then parent := ufUnion parent k c'
  for f in p.main.calls do
    if let c₀ :: rest := F.codesOf f then
      for c' in rest do parent := ufUnion parent c₀ c'
  let susp := (List.range p.codes.size).filter fun c => !(F.skeys[c]!).isEmpty
  let bodies := hs.toList.map (·.body)
  let poll := (List.range p.codes.size).toArray.map fun c =>
    bodies.contains c || susp.any fun c' => ufFind parent c' == ufFind parent c
  -- Which codes may raise: `Unwind`'s analysis.
  let U := UFacts.solve O.defs S p
  let raises := U.rc.map (!Raises.isEmpty ·)
  let cls := (List.range p.codes.size).toArray.map (ufFind parent)
  return { F with poll, raises, U, cls }

/-! ### Tail-resumptive operations

A clause that resumes `κ` once, in tail position, with an answer it computes without `κ`
(`λ(w, k). …; k.resume y`) is *tail-resumptive*. When every handler of a name has one closed
tail-resumptive clause for an operation, and the clause neither suspends nor raises, a `perform`
of that operation is a direct call of the clause's code with its resume removed: the handler is
the one known statically, and no continuation is materialised. -/

/-- `x`, and the variables a `let y = z` of `t` binds to one of them, transitively. -/
def aliasesIn (t : Tm) (x : Var) : List Var := Id.run do
  let defs := (defsOf {} t).toList
  let mut out := [x]
  for _ in [0:defs.length + 1] do
    let new := defs.filterMap fun (y, e) => match e with
      | .var z => if out.contains z && !out.contains y then some y else none
      | _ => none
    if new.isEmpty then break
    out := out ++ new.eraseDups
  return out

/-- Every variable a term uses as an operand, bound in it or not, once per use. -/
def Tm.operands : Tm → List Var
  | .var x | .raise x | .reraise x _ | .perform x | .absurd x | .inj _ x | .con _ _ x => [x]
  | .unit | .lit _ => []
  | .pair a b | .app a b | .run a b | .await a b => [a, b]
  | .clos _ xs | .prim _ xs => xs
  | .letv _ e b => e.operands ++ b.operands
  | .letpair _ _ p b => p :: b.operands
  | .case s _ b₁ _ b₂ | .when s _ _ _ b₁ b₂ => s :: b₁.operands ++ b₂.operands
  | .copy x _ b | .drop x b | .fin _ x b => x :: b.operands
  | .hnd _ hr cls b | .ubind hr cls b => hr :: cls :: b.operands
  | .catch _ b | .catchAll b => b.operands

/-- The uses of the variables `xs` in `t`. -/
def occurrences (t : Tm) (xs : List Var) : Nat := (t.operands.filter xs.contains).length

/-- A `let f = E` of `t` whose value is the resume projection `kk s` of `κ` (`kk` among `ks`, `s`
an `inl`): `f`, `kk` and `s`. -/
def findResume (defs : Std.HashMap Var Tm) (ks : List Var) : Tm → Option (Var × Var × Var)
  | .letv f e b =>
    match e.tail with
    | .app kk s =>
      if ks.contains kk && (match defs[s]?.map Tm.tail with | some (.inj false _) => true | _ => false)
      then some (f, kk, s) else findResume defs ks e <|> findResume defs ks b
    | _ => findResume defs ks e <|> findResume defs ks b
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b => findResume defs ks b
  | .case _ _ b₁ _ b₂ => findResume defs ks b₁ <|> findResume defs ks b₂
  | _ => none

/-- `t` with the resume projection `kk s` replaced by `()` and the resume `ff y` by `y`, the
variables they consumed dropped. -/
def Tm.dropResume (kk s ff y : Var) : Tm → Tm
  | .app a b =>
    if a == kk && b == s then .drop kk (.drop s .unit)
    else if a == ff && b == y then .drop ff (.var y) else .app a b
  | .letv x e b => .letv x (e.dropResume kk s ff y) (b.dropResume kk s ff y)
  | .letpair x z p b => .letpair x z p (b.dropResume kk s ff y)
  | .case s' x b₁ z b₂ => .case s' x (b₁.dropResume kk s ff y) z (b₂.dropResume kk s ff y)
  | .copy x x' b => .copy x x' (b.dropResume kk s ff y)
  | .drop x b => .drop x (b.dropResume kk s ff y)
  | t => t

/-- The clause code `λp. let (w, k) = p; B` without its resume, when it is tail-resumptive: `B`
uses `κ` once, as `k.resume y` in tail position. Its argument is still the pair, with `()` for
`κ`. -/
def tailClause? (c : Code) : Option Code := do
  let .letv p' (.var p) (.letpair w k p'' B) := c.body | none
  guard (p == c.param && p' == p'' && c.env.isEmpty)
  let defs := defsOf {} B
  let ka := aliasesIn B k
  let (f, kk, s) ← findResume defs ka B
  let fa := aliasesIn B f
  let .app ff y := B.tail | none
  guard (fa.contains ff && occurrences B ka == ka.length && occurrences B fa == fa.length)
  return { c with body := .letv p' (.var p) (.letpair w k p' (B.dropResume kk s ff y)) }

/-- The code of a finaliser frame's clauses (`markUbinds`) that resumes `κ` with the answer and
cancels it on an unwind: `λs. case s {inl b. k.resume b | inr _. k.cancel}`, `k` its one captured
value. -/
def resumeOrCancel? (c : Code) : Bool := Id.run do
  let [ke] := c.env | return false
  let .letv s' (.var s) (.case s'' b r u x) := c.body | return false
  if !(s == c.param && s' == s'') then return false
  let ka := aliasesIn r ke ++ aliasesIn x ke
  -- The resume: `(k (inl ())) b`, `k` used once.
  let resOk := match r.tail with
    | .app t b' =>
      (aliasesIn r b).contains b' && occurrences r (aliasesIn r ke) == (aliasesIn r ke).length &&
        (match (defsOf {} r)[t]?.map Tm.tail with
          | some (.app kk sv) => ka.contains kk &&
              (match (defsOf {} r)[sv]?.map Tm.tail with | some (.inj false _) => true | _ => false)
          | _ => false)
    | _ => false
  -- The cancel: `k (inr ())`.
  let canOk := match x.tail with
    | .app kk sv => ka.contains kk && !(aliasesIn x u).contains kk &&
        (match (defsOf {} x)[sv]?.map Tm.tail with | some (.inj true _) => true | _ => false)
    | _ => false
  return resOk && canOk

/-- `t` with the binding `let cv = clos _ _` removed and the frame `ubind cv cv M` replaced by `M`. -/
def Tm.dropUbind (cv : Var) : Tm → Tm
  | .letv x e b =>
    if x == cv then b.dropUbind cv else .letv x (e.dropUbind cv) (b.dropUbind cv)
  | .ubind nn dd m => if nn == cv && dd == cv then m else .ubind nn dd m
  | .letpair x z p b => .letpair x z p (b.dropUbind cv)
  | .copy x x' b => .copy x x' (b.dropUbind cv)
  | .drop x b => .drop x (b.dropUbind cv)
  | t => t

/-- The clause code `λp. let (w, k) = p; B` without `κ`, when `B` ends in the frame
`M then b. k.resume b unwind k.cancel` and uses `κ` nowhere else: the answer is computed by `M`,
which may raise, and `κ` is resumed with it in tail position, or cancelled when `M` unwinds. As a
direct call the clause answers `M`'s answer, and an unwind of `M` unwinds the performing code's
own frames, which is what the cancel runs. Its argument is still the pair, with `()` for `κ`. -/
def unwindClause? (codes : Array Code) (c : Code) : Option Code := do
  let .letv p' (.var p) (.letpair w k p'' B) := c.body | none
  guard (p == c.param && p' == p'' && c.env.isEmpty)
  let .ubind nn dd _ := B.tail | none
  guard (nn == dd)
  let defs := defsOf {} B
  let some (.clos sc [k']) := defs[nn]?.map Tm.tail | none
  let ka := aliasesIn B k
  guard (ka.contains k' && occurrences B ka == ka.length)
  let some sel := codes[sc]? | none
  guard (resumeOrCancel? sel)
  return { c with body := .letv p' (.var p) (.letpair w k p'' (.drop k (B.dropUbind nn))) }

/-- The codes of the clauses at index `j` of the clause tuples a key holds. -/
def Solver.clausesAt (S : Solver) (k : Nat) : Nat → List Nat
  | 0 => ((S.set[k]?.getD #[]).toList.flatMap fun v => match S.vals[v]! with
    | .pair a _ => S.closuresAt a
    | _ => []).eraseDups
  | j + 1 => ((S.set[k]?.getD #[]).toList.flatMap fun v => match S.vals[v]! with
    | .pair _ b => S.clausesAt b j
    | _ => []).eraseDups

/-- Every variable of a term, bound in it or not. -/
def Tm.allVars : Tm → List Var
  | .letv x e b => x :: e.allVars ++ b.allVars
  | .letpair x y p b => x :: y :: p :: b.allVars
  | .case s x b₁ y b₂ => s :: x :: y :: b₁.allVars ++ b₂.allVars
  | .when s _ _ x b r => s :: x :: b.allVars ++ r.allVars
  | .copy x x' b => x :: x' :: b.allVars
  | .drop x b => x :: b.allVars
  | .fin _ dd b => dd :: b.allVars
  | .catch _ b | .catchAll b => b.allVars
  | t => t.operands

/-- `t` with each variable renamed by `σ`. -/
def Tm.rename (σ : Std.HashMap Var Var) : Tm → Tm
  | .var x => .var (σ.getD x x)
  | .pair a b => .pair (σ.getD a a) (σ.getD b b)
  | .inj r a => .inj r (σ.getD a a)
  | .con k n a => .con k n (σ.getD a a)
  | .clos c xs => .clos c (xs.map fun x => σ.getD x x)
  | .prim op xs => .prim op (xs.map fun x => σ.getD x x)
  | .app f a => .app (σ.getD f f) (σ.getD a a)
  | .letv x e b => .letv (σ.getD x x) (e.rename σ) (b.rename σ)
  | .letpair x y p b => .letpair (σ.getD x x) (σ.getD y y) (σ.getD p p) (b.rename σ)
  | .case s x b₁ y b₂ => .case (σ.getD s s) (σ.getD x x) (b₁.rename σ) (σ.getD y y) (b₂.rename σ)
  | .when s k n x b r => .when (σ.getD s s) k n (σ.getD x x) (b.rename σ) (r.rename σ)
  | .absurd s => .absurd (σ.getD s s)
  | .copy x x' b => .copy (σ.getD x x) (σ.getD x' x') (b.rename σ)
  | .drop x b => .drop (σ.getD x x) (b.rename σ)
  | .raise p => .raise (σ.getD p p)
  | .reraise p m => .reraise (σ.getD p p) m
  | .perform p => .perform (σ.getD p p)
  | .catch n b => .catch n (b.rename σ)
  | .fin q dd b => .fin q (σ.getD dd dd) (b.rename σ)
  | .catchAll b => .catchAll (b.rename σ)
  | .run f a => .run (σ.getD f f) (σ.getD a a)
  | .await p k => .await (σ.getD p p) (σ.getD k k)
  | .hnd n hr cls b => .hnd n (σ.getD hr hr) (σ.getD cls cls) (b.rename σ)
  | .ubind nn dd b => .ubind (σ.getD nn nn) (σ.getD dd dd) (b.rename σ)
  | t => t

/-- A closed code with its variables renamed afresh: a copy whose variables may take other
layout types than the original's. -/
def freshCopy (c : Code) : KM Code := do
  let xs := (c.param :: c.body.allVars).eraseDups
  let mut σ : Std.HashMap Var Var := {}
  for x in xs do σ := σ.insert x (← kfresh)
  return ⟨[], σ.getD c.param c.param, c.body.rename σ⟩

/-- `perform p` of a direct operation as a call of its clause's code. -/
def directCalls (O : Ops) (direct : Std.HashMap OpKey Nat) : Tm → KM Tm
  | .perform p => do
    let some key := payloadKey O.defs p | return .perform p
    let some tc := direct[key]? | return .perform p
    let a ← kfresh; let b ← kfresh; let i ← kfresh; let w ← kfresh; let u ← kfresh
    let arg ← kfresh; let f ← kfresh
    return .letpair a b p (.letpair i w b (.drop a (.drop i (.letv u .unit
      (.letv arg (.pair w u) (.letv f (.clos tc []) (.app f arg)))))))
  | .letv x e b => return .letv x (← directCalls O direct e) (← directCalls O direct b)
  | .letpair x y p b => return .letpair x y p (← directCalls O direct b)
  | .case s x b₁ y b₂ => return .case s x (← directCalls O direct b₁) y (← directCalls O direct b₂)
  | .when s k n x b r => return .when s k n x (← directCalls O direct b) (← directCalls O direct r)
  | .copy x x' b => return .copy x x' (← directCalls O direct b)
  | .drop x b => return .drop x (← directCalls O direct b)
  | .catch n b => return .catch n (← directCalls O direct b)
  | .fin p dd b => return .fin p dd (← directCalls O direct b)
  | t => pure t

/-- The operations whose clause, at every handler of their name, is one closed tail-resumptive
code that neither suspends nor raises: each with that code without its resume. -/
def tailResumptive (O : Ops) (F : SFacts) (codes : Array Code) (hs : Array HInfo) :
    List (OpKey × Code) := Id.run do
  let mut out := []
  for n in O.ctl do
    let sites := hs.toList.filter (·.n == n)
    for (idx, j) in O.keysOf n do
      -- The handlers whose body may perform the operation: another's clause never runs for it.
      let sites := sites.filter fun h => (F.skeys[h.body]?.getD []).contains idx
      let cs := (sites.flatMap fun h =>
        F.S.clausesAt (F.S.num.idx (.var h.dVars[1]!)) j).eraseDups
      let [c] := cs | continue
      if let some tc := codes[c]?.bind tailClause? then
        if !(sKeysOf O F c [] tc.body).isEmpty then continue
        if !Raises.isEmpty (F.U.raises tc.body) then continue
        out := out ++ [((n, j.toUInt32), tc)]
      else if let some tc := codes[c]?.bind (unwindClause? codes) then
        -- The answer's computation may raise: an unwind of the direct call unwinds the
        -- performing code's frames, as the cancel of `κ` does.
        if !(sKeysOf O F c [] tc.body).isEmpty then continue
        out := out ++ [((n, j.toUInt32), tc)]
  return out

/-! ### Machines -/

/-- A frame a resumption point stands in, inside its code. -/
inductive Frame where
  /-- `let x = [·] in b`. -/
  | let_ (x : Var) (b : Tm)
  /-- `catch n [·]`. -/
  | catch_ (n : UInt32)
  /-- `fin dd [·]`. -/
  | fin_ (dd : Var)
  deriving Inhabited

/-- The variables a stack of frames holds, innermost first: what each `let` uses after its
binder, and each finaliser. -/
def framesLive (fs : List Frame) : List Var :=
  (fs.flatMap fun
    | .let_ x b => b.fvs.filter (· != x)
    | .catch_ _ => []
    | .fin_ dd => [dd]).eraseDups

/-- A resumption point. -/
inductive PKind where
  /-- `perform p`. -/
  | perf (p : Var)
  /-- A call of a code that may suspend, `f a`, not in tail position. -/
  | call (f a : Var)
  /-- `drive`'s forwarding, `await p k`. -/
  | await (p k : Var)
  deriving Inhabited

def PKind.key : PKind → Var
  | .perf p | .call p _ | .await p _ => p

structure Point where
  kind : PKind
  frames : List Frame
  /-- The resume code it belongs to: a `sel` code has one per projection. -/
  group : Nat
  live : List Var
  deriving Inhabited

/-- What lowering one code needs. -/
structure MEnv where
  O : Ops
  F : SFacts
  /-- The code lowered. -/
  self : Nat
  /-- The live `await`s: those whose handler's body may suspend with another name's operation. -/
  liveAwait : Bool
  /-- Each point's group and position, by `PKind.key`. -/
  pointOf : Std.HashMap Var (Nat × Nat)
  points : Array Point
  /-- Each group's resume code, and its number of points. -/
  groups : Array (Nat × Nat)

/-- A tail call of `f` in the code `self` passes its outcome on: `f`'s codes share `self`'s
convention, as the codes of a loop of tail calls do. -/
def SFacts.passes (F : SFacts) (self : Nat) (f : Var) : Bool :=
  (F.codesOf f).all fun c => F.cls[c]? == F.cls[self]?

/-- The resumption points of a term of the code `self` at the frames `fs`, in group `g`. -/
def collectPoints (F : SFacts) (self : Nat) (liveAwait : Bool) (g : Nat) (fs : List Frame) :
    Tm → List Point
  | .letv x e b =>
    collectPoints F self liveAwait g (.let_ x b :: fs) e ++ collectPoints F self liveAwait g fs b
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b => collectPoints F self liveAwait g fs b
  | .case _ _ b₁ _ b₂ | .when _ _ _ _ b₁ b₂ =>
    collectPoints F self liveAwait g fs b₁ ++ collectPoints F self liveAwait g fs b₂
  | .catch n b => collectPoints F self liveAwait g (.catch_ n :: fs) b
  | .fin _ dd b => collectPoints F self liveAwait g (.fin_ dd :: fs) b
  | .perform p => [⟨.perf p, fs, g, framesLive fs⟩]
  | .await p k => if liveAwait then [⟨.await p k, fs, g, framesLive fs⟩] else []
  | .app f a =>
    if F.pollAt f && (!fs.isEmpty || !F.passes self f) then [⟨.call f a, fs, g, framesLive fs⟩]
    else []
  | _ => []

/-- The term may suspend: a `perform`, a live `await`, or a call of a code that may. -/
def MEnv.hasSusp (E : MEnv) : Tm → Bool
  | .perform _ => true
  | .await _ _ => E.liveAwait
  | .app f _ => E.F.pollAt f
  | .letv _ e b => E.hasSusp e || E.hasSusp b
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b | .catch _ b | .fin _ _ b | .catchAll b => E.hasSusp b
  | .case _ _ b₁ _ b₂ | .when _ _ _ _ b₁ b₂ => E.hasSusp b₁ || E.hasSusp b₂
  | _ => false

/-- A term with no suspension: each `run` a call. -/
def Tm.plain : Tm → Tm
  | .run f a => .app f a
  | .letv x e b => .letv x e.plain b.plain
  | .letpair x y p b => .letpair x y p b.plain
  | .case s x b₁ y b₂ => .case s x b₁.plain y b₂.plain
  | .when s k n x b r => .when s k n x b.plain r.plain
  | .copy x x' b => .copy x x' b.plain
  | .drop x b => .drop x b.plain
  | .catch n b => .catch n b.plain
  | .fin p dd b => .fin p dd b.plain
  | .catchAll b => .catchAll b.plain
  | t => t

def mkInl (t : Tm) : KM Tm := do
  let v ← kfresh
  return .letv v t (.inj false v)

/-- The right-nested tuple of `xs`, then `k` on it. -/
def mkTuple (xs : List Var) (k : Var → KM Tm) : KM Tm := do
  match xs with
  | [] => do let u ← kfresh; return .letv u .unit (← k u)
  | [x] => k x
  | x :: rest => do
    mkTuple rest fun r => do
      let t ← kfresh
      return .letv t (.pair x r) (← k t)

/-- Bind the variables `xs` from the right-nested tuple `t`, then `body`. -/
def unTuple (t : Var) (xs : List Var) (body : Tm) : KM Tm := do
  match xs with
  | [] => return .drop t body
  | [x] => return .letv x (.var t) body
  | x :: rest => do
    let r ← kfresh
    return .letpair x r t (← unTuple r rest body)

/-- Suspend at point `j` with the payload `pl` (and the callee's `k`): build the state, its
closure, and `inr (pl, k)`. -/
def MEnv.suspend (E : MEnv) (j : Nat) (pl : Var) (k : Option Var) : KM Tm := do
  let some pt := E.points[j]? | throw "capture: no point"
  let some (r, size) := E.groups[pt.group]? | throw "capture: no group"
  let pos := (E.pointOf[pt.kind.key]?.map (·.2)).getD 0
  mkTuple (pt.live ++ k.toList) fun t => do
    let st ← kfresh; let kk ← kfresh; let q ← kfresh
    return .letv st (.con pos size t) (.letv kk (.clos r [st]) (.letv q (.pair pl kk) (.inj true q)))

/-- The payload variant of `perform p`, then `k` on it. -/
def MEnv.payload (E : MEnv) (p : Var) (k : Var → KM Tm) : KM Tm := do
  let some key := payloadKey E.O.defs p | throw "capture: a control operation whose name is not a literal"
  let a ← kfresh; let b ← kfresh; let i ← kfresh; let w ← kfresh; let pl ← kfresh
  return .letpair a b p (.letpair i w b (.drop a (.drop i
    (.letv pl (.con (E.O.keyIdx key) E.O.keys.size w) (← k pl)))))

def MEnv.pointIdx (E : MEnv) (x : Var) : KM Nat := do
  match E.points.toList.zipIdx.find? (fun (pt, _) => pt.kind.key == x) with
  | some (_, j) => pure j
  | none => throw "capture: an unknown resumption point"

/-- A call of a code that may suspend at point `j`: its outcome, `inl` of its answer, or a
suspension at `j` holding its `k`. -/
def MEnv.callPoint (E : MEnv) (j : Nat) (call : Tm) : KM Tm := do
  let r ← kfresh; let v ← kfresh; let q ← kfresh; let pl ← kfresh; let k ← kfresh
  return .letv r call (.case r v (.inj false v) q (.letpair pl k q (← E.suspend j pl (some k))))

/-- The outcome of `catch n` over a body's outcome `t`: `inl (inl v)`, `inl (inr p)` for a caught
`p`, or the suspension. -/
def catchOutcome (n : UInt32) (t : Tm) : KM Tm := do
  let r ← kfresh; let o ← kfresh; let v ← kfresh; let q ← kfresh; let p ← kfresh
  let a₁ ← kfresh; let a₂ ← kfresh
  return .letv r (.catch n t) (.case r o
    (.case o v (.letv a₁ (.inj false v) (.inj false a₁)) q (.inj true q))
    p (.letv a₂ (.inj true p) (.inj false a₂)))

mutual
/-- The outcome of `t`, standing in the frames `fs`. -/
def MEnv.outcome (E : MEnv) (fs : List Frame) : Tm → KM Tm
  | .letv x e b => do
    if !E.hasSusp e then return .letv x e.plain (← E.outcome fs b)
    match e with
    | .perform _ | .await _ _ => E.outcome (.let_ x b :: fs) e
    | _ =>
      let r ← kfresh; let q ← kfresh
      return .letv r (← E.outcome (.let_ x b :: fs) e) (.case r x (← E.outcome fs b) q (.inj true q))
  | .letpair x y p b => return .letpair x y p (← E.outcome fs b)
  | .copy x x' b => return .copy x x' (← E.outcome fs b)
  | .drop x b => return .drop x (← E.outcome fs b)
  | .case s x b₁ y b₂ => return .case s x (← E.outcome fs b₁) y (← E.outcome fs b₂)
  | .when s k n x b r => return .when s k n x (← E.outcome fs b) (← E.outcome fs r)
  | .catch n b => do
    if !E.hasSusp b then return ← mkInl (.catch n b.plain)
    catchOutcome n (← E.outcome (.catch_ n :: fs) b)
  | .fin _ dd b => do
    if !E.hasSusp b then return ← mkInl (.fin false dd b.plain)
    return .fin true dd (← E.outcome (.fin_ dd :: fs) b)
  | .perform p => do
    let j ← E.pointIdx p
    E.payload p fun pl => E.suspend j pl none
  | .await p k => do
    if !E.liveAwait then return .absurd p
    let j ← E.pointIdx p
    E.suspend j p (some k)
  | .app f a => do
    if !E.F.pollAt f then return ← mkInl (.app f a)
    -- A tail call that closes a loop of tail calls passes the callee's outcome on.
    if fs.isEmpty && E.F.passes E.self f then return .app f a
    E.callPoint (← E.pointIdx f) (.app f a)
  | t => mkInl t.plain

/-- The outcome of the frames `fs` around a hole holding `h`: a value (`inl`) or an outcome
(`inr`). -/
def MEnv.plug (E : MEnv) : Tm ⊕ Tm → List Frame → KM Tm
  | .inl t, [] => mkInl t
  | .inr t, [] => pure t
  | .inl t, .let_ x b :: fs => do E.plug (.inr (.letv x t (← E.outcome fs b))) fs
  | .inr t, .let_ x b :: fs => do
    let r ← kfresh; let q ← kfresh
    E.plug (.inr (.letv r t (.case r x (← E.outcome fs b) q (.inj true q)))) fs
  | .inl t, .catch_ n :: fs => E.plug (.inl (.catch n t)) fs
  | .inr t, .catch_ n :: fs => do E.plug (.inr (← catchOutcome n t)) fs
  | .inl t, .fin_ dd :: fs => E.plug (.inl (.fin false dd t)) fs
  | .inr t, .fin_ dd :: fs => E.plug (.inr (.fin true dd t)) fs
end

/-- Resume point `j` at `y`: its continuation, its frames rebuilt around the answer. `k` is the
callee's suspended computation at a call point or a forwarding. -/
def MEnv.resumeArm (E : MEnv) (j : Nat) (y : Var) (k : Option Var) : KM Tm := do
  let some pt := E.points[j]? | throw "capture: no point"
  let hole : Tm ⊕ Tm ← match pt.kind, k with
    | .perf _, _ => pure (.inl (.var y))
    | .call .., some k => do
      let mm ← kfresh
      pure (.inr (.letv mm (.inj false y) (← E.callPoint j (.app k mm))))
    | .await .., some k => do
      let mm ← kfresh
      pure (.inl (.letv mm (.inj false y) (.app k mm)))
    | _, none => throw "capture: a call point with no callee"
  E.plug hole pt.frames

/-- The first error kept: `e` when it is one; else `r`'s error, unless its name is in `mask`. -/
def errNext (e r z : Var) : KM Tm := do
  let u ← kfresh; let v ← kfresh; let q ← kfresh; let ee ← kfresh; let u' ← kfresh
  let m ← kfresh; let rest ← kfresh; let m₂ ← kfresh; let m64 ← kfresh; let sh ← kfresh
  let sr ← kfresh; let one ← kfresh; let an ← kfresh; let bit ← kfresh; let t ← kfresh
  let u₁ ← kfresh; let u₂ ← kfresh; let u₃ ← kfresh; let q' ← kfresh
  let none' : Tm := .letv u' .unit (.inj false u')
  let test : Tm :=
    .letpair m rest q (.copy m m₂ (.letv m64 (.prim (.host .extend_u) [m₂])
      (.letv sh (.pair z m64) (.letv sr (.prim (.host (.bin .w64 .shr_u)) [sh])
        (.letv one (.lit (.i64 1)) (.letv an (.pair sr one)
          (.letv bit (.prim (.host (.bin .w64 .and)) [an]) (.letv t (.prim (.host (.eqz .w64)) [bit])
            (.case t u₁ (.drop u₁ (.drop m (.drop rest none')))
              u₂ (.drop u₂ (.letv q' (.pair m rest) (.inj true q'))))))))))))
  return .case e u (.drop u (.case r v (.drop v (.drop z none')) q test))
    ee (.drop r (.drop z (.letv u₃ (.var ee) (.inj true u₃))))

/-- Cancel point `j` with the mask `z`: the callee's `k` first, then the finalisers of its `fin`
frames, innermost first, every other variable dropped; the first error kept. -/
def MEnv.cancelArm (E : MEnv) (j : Nat) (z : Var) (k : Option Var) : KM Tm := do
  let some pt := E.points[j]? | throw "capture: no point"
  let dds := pt.frames.filterMap fun | .fin_ dd => some dd | _ => none
  let others := pt.live.filter (· ∉ dds)
  -- The finalisers in order, each with whether it may raise.
  let fins := dds.map fun dd => (dd, (E.F.codesOf dd).any (E.F.raises[·]?.getD false))
  let e₀ ← kfresh
  let rec go : List (Var × Bool) → Var → KM Tm
    | [], e => do return .drop z (.var e)
    | (dd, raising) :: rest, e => do
      let u ← kfresh; let rr ← kfresh
      if raising then
        let zc ← kfresh; let e' ← kfresh
        let u₀ ← kfresh
        return .copy z zc (.letv u₀ .unit (.letv u (.inj true u₀) (.letv rr (.catchAll (.app dd u))
          (.letv e' (← errNext e rr zc) (← go rest e')))))
      else
        let u₀ ← kfresh
        return .letv u₀ .unit (.letv u (.inj true u₀) (.letv rr (.app dd u) (.drop rr (← go rest e))))
  let tail ← go fins e₀
  let start ← match k with
    | some k => do
      let zc ← kfresh; let mz ← kfresh
      pure (.copy z zc (.letv mz (.inj true zc) (.letv e₀ (.app k mz) tail)))
    | none => do
      let u ← kfresh
      pure (.letv u .unit (.letv e₀ (.inj false u) tail))
  return Tm.drops others start

/-- Group `g`'s resume code: `inl y` resumes, `inr mask` cancels, by the state's variant. -/
def MEnv.resumeCode (E : MEnv) (g : Nat) : KM Code := do
  let s ← kfresh; let m ← kfresh; let m' ← kfresh; let y ← kfresh; let z ← kfresh
  let pts := E.points.toList.zipIdx.filter (·.1.group == g)
  let size := pts.length
  let mut res : Tm := .absurd s
  let mut can : Tm := .absurd s
  for (pt, j) in pts.reverse do
    let pos := (E.pointOf[pt.kind.key]?.map (·.2)).getD 0
    let hasK := match pt.kind with | .perf _ => false | _ => true
    let f₁ ← kfresh; let f₂ ← kfresh
    let k₁ ← if hasK then some <$> kfresh else pure none
    let k₂ ← if hasK then some <$> kfresh else pure none
    res := .when s pos size f₁ (← unTuple f₁ (pt.live ++ k₁.toList) (← E.resumeArm j y k₁)) res
    can := .when s pos size f₂ (← unTuple f₂ (pt.live ++ k₂.toList) (← E.cancelArm j z k₂)) can
  return ⟨[s], m, .letv m' (.var m) (.case m' y res z can)⟩

/-- Lower a code that answers outcomes: its points, its resume codes, its body. -/
def machine (O : Ops) (F : SFacts) (k : Nat) (c : Code) : KM Code := do
  let liveAwait := match F.drvOf[k]? with
    | some h => ((F.skeys[h.body]?.getD []).any fun j => O.keys[j]!.1 != h.n)
    | none => false
  let pts := match c.selShape? with
    | some (_, _, b₁, _, b₂) =>
      collectPoints F k liveAwait 0 [] b₁ ++ collectPoints F k liveAwait 1 [] b₂
    | none => collectPoints F k liveAwait 0 [] c.body
  let mut pointOf : Std.HashMap Var (Nat × Nat) := {}
  let mut counts : Array Nat := #[0, 0]
  for pt in pts do
    if pointOf.contains pt.kind.key then throw "capture: a resumption point twice"
    pointOf := pointOf.insert pt.kind.key (pt.group, counts[pt.group]!)
    counts := counts.modify pt.group (· + 1)
  let mut groups : Array (Nat × Nat) := #[]
  for g in [0:2] do
    let r ← if counts[g]! > 0 then kregister default else pure 0
    groups := groups.push (r, counts[g]!)
  let E : MEnv := { O, F, self := k, liveAwait, pointOf, points := pts.toArray, groups }
  let body ← E.outcome [] c.body
  for g in [0:2] do
    if counts[g]! > 0 then kset groups[g]!.1 (← E.resumeCode g)
  return { c with body }

/-- A code that answers plain values: no `perform`, and no call of a code that may suspend. -/
def plainCode (F : SFacts) (t : Tm) : Except String Tm := do
  if let some f := t.calls.find? F.pollAt then
    throw s!"capture: a call of a code that may suspend (code {F.codesOf f}), outside every handler of its operations"
  return t.plain

/-! ### Cancel masks -/

/-- The codes reachable from `c` by calls and runs. -/
def reachable (F : SFacts) (codes : Array Code) (c : Nat) : List Nat := Id.run do
  let mut seen : Std.HashSet Nat := ({} : Std.HashSet Nat).insert c
  let mut work := [c]
  for _ in [0:codes.size + 1] do
    let new := (work.flatMap fun c => ((codes[c]?.map (·.body.callees)).getD []).flatMap F.codesOf)
      |>.filter (!seen.contains ·) |>.eraseDups
    if new.isEmpty then break
    seen := new.foldl (·.insert ·) seen
    work := new
  return seen.toList

/-- Each control handler's cancel mask: the names of the handler sites reachable from its body,
its own included. -/
def masks (F : SFacts) (codes : Array Code) (hs : Array HInfo) : Except String (Array UInt64) := do
  let nameOfBody : Std.HashMap Nat UInt32 := hs.foldl (fun m h => m.insert h.body h.n) {}
  hs.mapM fun h => do
    let rs := reachable F codes h.body
    let names : List UInt32 := h.n :: rs.flatMap fun c =>
      ((codes[c]?.map (·.body.catches)).getD []) ++ (nameOfBody[c]?).toList
    names.foldlM (fun (m : UInt64) (n : UInt32) => do
      if n ≥ 64 then throw s!"capture: a cancel whose finalisers may raise, under a handler named {n} ≥ 64, is not lowered"
      pure (m ||| ((1 : UInt64) <<< n.toUInt64))) 0

/-! ### The pass -/

/-- The term has a construct of §19 that this pass lowers. -/
def Tm.hasCapture : Tm → Bool
  | .perform _ | .hnd .. | .ubind .. => true
  | .letv _ e b => e.hasCapture || b.hasCapture
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b => b.hasCapture
  | .case _ _ b₁ _ b₂ => b₁.hasCapture || b₂.hasCapture
  | _ => false

/-- **Lower the handlers, control operations and cancels.**  A program with none is returned as
it is. -/
def Prog.capture (p : Prog) : Except String Prog := do
  if !(p.main.hasCapture || p.codes.any (·.body.hasCapture)) then return p
  let O ← Ops.of p
  let terms := p.main :: p.codes.toList.map (·.body)
  let next := (terms.map Tm.maxVar).foldl max 0 + 1
  let act : KM Prog := do
    -- Handlers and finaliser frames.
    let main ← handlers O p.main
    let mut codes := #[]
    for c in p.codes do codes := codes.push { c with body := ← handlers O c.body }
    modify fun s => { s with codes := codes ++ s.codes.extract p.codes.size s.codes.size }
    let q₀ : Prog := { p with main, codes := (← get).codes }
    let hs := (← get).hs
    let F₀ ← liftE (SFacts.of O q₀ hs)
    -- Tail-resumptive operations become direct calls; then the analysis again.
    let direct := tailResumptive O F₀ q₀.codes hs
    let (main, q₀, F) ← if direct.isEmpty then pure (main, q₀, F₀) else do
      let mut tcs : Std.HashMap OpKey Nat := {}
      for (key, tc) in direct do tcs := tcs.insert key (← kregister (← freshCopy tc))
      let cs := (← get).codes
      for k in [0:cs.size] do
        kset k { cs[k]! with body := ← directCalls O tcs cs[k]!.body }
      let main ← directCalls O tcs main
      let q₁ : Prog := { p with main, codes := (← get).codes }
      pure (main, q₁, ← liftE (SFacts.of O q₁ hs))
    -- `drive`'s forwarding, where its body suspends with another name's operation; `κ`'s mask and
    -- re-raise, where a finaliser may raise.
    let anyRaise := q₀.codes.toList.any fun c => c.body.finalisers.any fun dd =>
      (F.codesOf dd).any (F.raises[·]?.getD false)
    let ms ← if anyRaise then liftE (masks F q₀.codes hs) else pure (hs.map fun _ => 0)
    if anyRaise then
      let succ := q₀.codes.map fun c => (c.body.callees.flatMap F.codesOf).eraseDups
      let cyc := onCycle succ
      if hs.toList.any (fun h => cyc[h.body]!) then
        throw "capture: a cancel whose finalisers may raise, under a handler reached from its own body, is not lowered"
    for (h, i) in hs.toList.zipIdx do
      let forward := (F.skeys[h.body]?.getD []).any fun j => O.keys[j]!.1 != h.n
      let d := q₀.codes[h.drv]!
      if !forward then kset h.drv { d with body := noForward d.body }
      let kc := q₀.codes[h.kap]!
      kset h.kap { kc with body := ← liftE (kapBody h ms[i]! anyRaise) }
    -- Each code that answers outcomes becomes a machine; the others are plain.
    let codes₁ := (← get).codes
    for k in [0:codes₁.size] do
      let c := codes₁[k]!
      if F.poll[k]?.getD false then kset k (← machine O F k c)
      else kset k { c with body := ← liftE ((plainCode F c.body).mapError (s!"in code {k}: " ++ ·)) }
    let main ← liftE ((plainCode F main).mapError ("in main: " ++ ·))
    pure { p with main, codes := (← get).codes }
  act.run' ⟨next, p.codes, #[]⟩
where
  liftE {α} (x : Except String α) : KM α := match x with
    | .ok a => pure a
    | .error e => throw e

end Backend.Clos

import Std.Data.HashMap
import Backend.Clos.Flow
import Backend.Clos.Convert

/-!
# Backend — lowering the abortive operations  `[spec §19]`

`raise`, the catching frames `catch` and `catchAll`, the finaliser frames `fin` and `reraise`
(`Tm.raise`, …; `Capture` turns handlers and `ubind` frames into them) become ordinary closure IR:
**branch-per-call propagation**, the representation of Rust's `Result` and `?`.

- **Which code raises.** A `raise` carries its name and operation as literals (§19: names are
  static), so its *key* `(n, i)` is known. A code raises the keys its body may raise and no
  frame of it catches: a `raise`'s key, the keys of the codes a call may call (the 0-CFA,
  `Backend/Clos/Flow.lean`), a `catch n`'s body less the keys of `n`, a finaliser frame's body and
  finaliser, and a `reraise`'s keys, those any `catchAll` catches whose names are not in its mask. The least solution is found by
  iteration.
- **The convention.** A code that may raise answers a sum: `inl v` when it returns `v`, `inr p`
  when it raises `p`. Codes that a call may call alike share one convention (a class of the
  codes called at one site): a class with a raising code answers sums throughout.
- **The rewrite.** A term that may raise is computed as such a sum. `let x = e in b`, with `e`
  raising, is `case e {inl x ⇒ b | inr p ⇒ drop (the rest's variables); inr p}`; a call of a
  non-raising code, or a term that cannot raise, is not touched, so a call pays a branch exactly
  when its callee may raise. A tail call passes the callee's sum on with no branch. A `catch n`
  cases on its body's sum and answers `inl` of a value or of a caught payload of the name `n` (a
  compare of the name when the body raises more than one), and passes any other name on. A
  finaliser frame runs its finaliser on `inr p` and raises `p` again (or the finaliser's own
  error, which supersedes it).

There is no handler stack and no search: the frame a `raise` reaches is the one whose `case` its
sum arrives at.
-/

namespace Backend.Clos

/-- A `raise`'s key: its name and operation. -/
abbrev OpKey := UInt32 × UInt32

/-- The keys a term may raise; `none` when a `raise`'s key is not a literal. -/
abbrev Raises := Option (List OpKey)

def Raises.union : Raises → Raises → Raises
  | some a, some b => some (b.foldl (fun acc k => if acc.contains k then acc else acc ++ [k]) a)
  | _, _ => none

def Raises.isEmpty : Raises → Bool
  | some [] => true
  | _ => false

/-- The free variables of a term, each once. -/
def Tm.fv : Tm → List Var
  | .var x => [x]
  | .unit | .lit _ => []
  | .pair a b => [a, b]
  | .inj _ a | .con _ _ a => [a]
  | .clos _ xs | .prim _ xs => xs
  | .app f a | .run f a => [f, a]
  | .letv x e b => e.fv ++ b.fv.filter (· != x)
  | .letpair x y p b => p :: b.fv.filter (fun z => z != x && z != y)
  | .case s x b₁ y b₂ => s :: b₁.fv.filter (· != x) ++ b₂.fv.filter (· != y)
  | .when s _ _ x b r => s :: b.fv.filter (· != x) ++ r.fv
  | .absurd s => [s]
  | .copy x x' b => x :: b.fv.filter (· != x')
  | .drop x b => x :: b.fv
  | .raise p | .reraise p _ | .perform p => [p]
  | .await p k => [p, k]
  | .hnd _ hr cls b => hr :: cls :: b.fv
  | .ubind nn dd b => nn :: dd :: b.fv
  | .catch _ b | .catchAll b => b.fv
  | .fin _ dd b => dd :: b.fv

/-- The free variables of a term that are variables, each once. -/
def Tm.fvs (t : Tm) : List Var := (t.fv.filter (fun x => !Var.isSelf x)).eraseDups

/-- Every `letv`'s definition, by its variable. -/
def defsOf (acc : Std.HashMap Var Tm) : Tm → Std.HashMap Var Tm
  | .letv x e b => defsOf (defsOf (acc.insert x e) e) b
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b | .hnd _ _ _ b | .ubind _ _ b | .catch _ b
  | .fin _ _ b | .catchAll b => defsOf acc b
  | .case _ _ b₁ _ b₂ | .when _ _ _ _ b₁ b₂ => defsOf (defsOf acc b₁) b₂
  | _ => acc

/-- The term a term's value is built by: its tail under bindings. -/
def Tm.tail : Tm → Tm
  | .letv _ _ b | .letpair _ _ _ b | .copy _ _ b | .drop _ b => b.tail
  | t => t

/-- The `i32` literal a variable is bound to. -/
def litOf (defs : Std.HashMap Var Tm) (x : Var) : Option UInt32 :=
  match defs[x]?.map Tm.tail with
  | some (.lit (.i32 n)) => some n
  | _ => none

/-- A payload's key: `(n, (i, v))` with `n` and `i` literals. -/
def payloadKey (defs : Std.HashMap Var Tm) (p : Var) : Option OpKey :=
  match defs[p]?.map Tm.tail with
  | some (.pair a b) =>
    match litOf defs a, defs[b]?.map Tm.tail with
    | some n, some (.pair i _) => (litOf defs i).map (n, ·)
    | _, _ => none
  | _ => none

/-- The analysis' facts: definitions, the flow solution, every code's raised keys, and the keys
a `reraise` may raise (those a `catchAll` catches). -/
structure UFacts where
  defs : Std.HashMap Var Tm
  S : Solver
  rc : Array Raises
  rr : Raises := some []

/-- The codes of the closures a key holds. -/
def Solver.closuresAt (S : Solver) (k : Nat) : List Nat :=
  ((S.set[k]?.getD #[]).toList.filterMap fun v => match S.vals[v]! with
    | .clos c => some c
    | _ => none).eraseDups

def UFacts.codesOf (F : UFacts) (x : Var) : List Nat := F.S.closuresAt (F.S.num.idx (.var x))

def UFacts.rcOf (F : UFacts) (cs : List Nat) : Raises :=
  cs.foldl (fun r c => Raises.union r (F.rc[c]?.getD (some []))) (some [])

/-- The keys a term may raise. -/
def UFacts.raises (F : UFacts) : Tm → Raises
  | .raise p => (payloadKey F.defs p).map ([·])
  | .reraise _ mask => F.rr.map (·.filter fun k => k.1 ≥ 64 || (mask >>> k.1.toUInt64) &&& 1 == 0)
  | .app f _ | .run f _ => F.rcOf (F.codesOf f)
  | .letv _ e b => Raises.union (F.raises e) (F.raises b)
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b => F.raises b
  | .case _ _ b₁ _ b₂ | .when _ _ _ _ b₁ b₂ => Raises.union (F.raises b₁) (F.raises b₂)
  | .catch n b => (F.raises b).map (·.filter (·.1 != n))
  | .fin _ dd b => Raises.union (F.raises b) (F.rcOf (F.codesOf dd))
  | _ => some []

/-- The keys the `catchAll`s of a term catch. -/
def UFacts.caughtAll (F : UFacts) : Tm → Raises
  | .catchAll b => Raises.union (F.raises b) (F.caughtAll b)
  | .letv _ e b => Raises.union (F.caughtAll e) (F.caughtAll b)
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b | .catch _ b | .fin _ _ b => F.caughtAll b
  | .case _ _ b₁ _ b₂ | .when _ _ _ _ b₁ b₂ => Raises.union (F.caughtAll b₁) (F.caughtAll b₂)
  | _ => some []

/-! ### The rewrite

Each lowering takes `outer`, the variables the enclosing levels own: a propagation drops what the
rest of its own level uses and leaves those to the level that owns them. In a converted term they
are never used inside, so this only matters where `Capture` has moved them into a suspension's
state from inside, and in a finaliser frame's body, whose frame owns `dd`. -/

structure UState where
  next : Var

abbrev UM := StateT UState (Except String)

def ufresh : UM Var := modifyGet fun s => (s.next, { s with next := s.next + 1 })

/-- The facts and the convention: which codes answer sums. -/
structure UEnv where
  F : UFacts
  sumConv : Array Bool

def UEnv.mayR (E : UEnv) (t : Tm) : Bool := !Raises.isEmpty (E.F.raises t)

/-- The callees of `f` answer sums. -/
def UEnv.sumAt (E : UEnv) (f : Var) : Bool := (E.F.codesOf f).any (E.sumConv[·]?.getD false)

def UEnv.sumOf (E : UEnv) (cs : List Nat) : Bool := cs.any (E.sumConv[·]?.getD false)

/-- `inl` of the value of `t`. -/
def wrapInl (t : Tm) : UM Tm := do
  let v ← ufresh
  return .letv v t (.inj false v)

/-- `inr` of the value of `t`. -/
def wrapInr (t : Tm) : UM Tm := do
  let v ← ufresh
  return .letv v t (.inj true v)

/-- A call answering a plain value, as a sum when `sumMode`. -/
def callAs (sumMode calleeSum : Bool) (f a : Var) : UM Tm := do
  if sumMode then
    if calleeSum then return .app f a else wrapInl (.app f a)
  else
    if calleeSum then throw "unwind: a call of a raising closure where no raise is handled"
    else return .app f a

/-- Drop each variable, then `t`. -/
def Tm.drops (xs : List Var) (t : Tm) : Tm := xs.foldr (fun x t => .drop x t) t

/-- `inr p`, the variables `xs` dropped first. -/
def propagateOn (xs : List Var) (p : Var) : Tm := Tm.drops xs (.inj true p)

/-- `onName q` when the payload `q = (m, …)` has the name `n`, `onOther q` otherwise: a compare
of `m`, unless every key `ks` the payload may have decides it. -/
def byName (n : UInt32) (ks : List OpKey) (q : Var) (onName onOther : Var → UM Tm) : UM Tm := do
  if ks.all (·.1 == n) then return ← onName q
  if ks.all (·.1 != n) then return ← onOther q
  let m ← ufresh; let rest ← ufresh; let m' ← ufresh; let l ← ufresh; let pr ← ufresh
  let bo ← ufresh; let u₁ ← ufresh; let u₂ ← ufresh; let q₁ ← ufresh; let q₂ ← ufresh
  return .letpair m rest q (.copy m m' (.letv l (.lit (.i32 n)) (.letv pr (.pair m' l)
    (.letv bo (.prim (.host (.rel .w32 .eq)) [pr])
      (.case bo u₁ (.drop u₁ (.letv q₁ (.pair m rest) (← onOther q₁)))
        u₂ (.drop u₂ (.letv q₂ (.pair m rest) (← onName q₂))))))))

/-- The finaliser `dd` on `()`, then the raise of `q` again, or the finaliser's own error. -/
def finalise (E : UEnv) (dd q : Var) : UM Tm := do
  let u ← ufresh; let dr ← ufresh
  let fin ← if E.sumOf (E.F.codesOf dd) then do
      let u₂ ← ufresh; let q₂ ← ufresh
      pure (.case dr u₂ (.drop u₂ (.inj true q)) q₂ (.drop q (.inj true q₂)))
    else pure (.drop dr (.inj true q))
  return .letv u .unit (.letv dr (.app dd u) fin)

/-- A finaliser frame's normal end on the body's value `v`: `dd` dropped; at `poll`, only at an
`inl` of the outcome, the other having moved `dd` into a suspension's state. As a sum when
`sumMode`. -/
def finNormal (sumMode poll : Bool) (dd v : Var) : UM Tm := do
  let wrap (t : Tm) : UM Tm := if sumMode then wrapInl t else pure t
  if !poll then return .drop dd (← wrap (.var v))
  let x ← ufresh; let s ← ufresh
  return .case v x (.drop dd (← wrap (.inj false x))) s (← wrap (.inj true s))

mutual
/-- `t` at a plain value: it cannot raise. -/
def lowerP (E : UEnv) (outer : List Var) : Tm → UM Tm
  | .letv x e b => do
    let outer' := outer ++ b.fvs.filter (· != x)
    return .letv x (← lowerP E outer' e) (← lowerP E outer b)
  | .letpair x y p b => return .letpair x y p (← lowerP E outer b)
  | .case s x b₁ y b₂ => return .case s x (← lowerP E outer b₁) y (← lowerP E outer b₂)
  | .when s k n x b r => return .when s k n x (← lowerP E outer b) (← lowerP E outer r)
  | .copy x x' b => return .copy x x' (← lowerP E outer b)
  | .drop x b => return .drop x (← lowerP E outer b)
  | .app f a => callAs false (E.sumAt f) f a
  | .reraise p mask => do
    -- An error the mask excludes entirely is never kept.
    if !E.mayR (.reraise p mask) then return .absurd p
    throw "unwind: a raise where none is handled"
  | .raise _ => throw "unwind: a raise where none is handled"
  | .catch n b => do
    if !E.mayR b then return ← wrapInl (← lowerP E outer b)
    let some ks := E.F.raises b | throw "unwind: a raise whose name is not a literal"
    if ks.any (·.1 != n) then throw "unwind: an operation no handler catches"
    let r ← ufresh; let v ← ufresh; let q ← ufresh
    return .letv r (← lowerS E outer b) (.case r v (.inj false v) q (.inj true q))
  | .catchAll b => lowerAtSum E outer b
  | .fin poll dd b => do
    if E.mayR b then throw "unwind: a finaliser frame whose body raises, where no raise is handled"
    let v ← ufresh
    return .letv v (← lowerP E (outer ++ [dd]) b) (← finNormal false poll dd v)
  | .hnd .. | .ubind .. | .perform _ | .run .. | .await .. =>
    throw "unwind: a handler or a control operation not lowered (`Capture`)"
  | t => return t

/-- `t` at a sum: `inl` of its value, or `inr` of what it raises. -/
def lowerS (E : UEnv) (outer : List Var) : Tm → UM Tm
  | .raise p | .reraise p _ => return .inj true p
  | .app f a => callAs true (E.sumAt f) f a
  | .letv x e b => do
    let own := b.fvs.filter (· != x)
    let outer' := outer ++ own
    if E.mayR e then
      let r ← ufresh; let q ← ufresh
      let rest := own.filter (· ∉ outer)
      return .letv r (← lowerS E outer' e) (.case r x (← lowerS E outer b) q (propagateOn rest q))
    else return .letv x (← lowerP E outer' e) (← lowerS E outer b)
  | .letpair x y p b => return .letpair x y p (← lowerS E outer b)
  | .case s x b₁ y b₂ => return .case s x (← lowerS E outer b₁) y (← lowerS E outer b₂)
  | .when s k n x b r => return .when s k n x (← lowerS E outer b) (← lowerS E outer r)
  | .copy x x' b => return .copy x x' (← lowerS E outer b)
  | .drop x b => return .drop x (← lowerS E outer b)
  | .catch n b => do
    -- `inl (inl v)`, `inl (inr q)` when `q` is of the name `n`, else `inr q`.
    if !E.mayR b then return ← wrapInl (← wrapInl (← lowerP E outer b))
    let some ks := E.F.raises b | throw "unwind: a raise whose name is not a literal"
    let r ← ufresh; let v ← ufresh; let q ← ufresh
    let caught ← byName n ks q (fun q => do wrapInl (.inj true q)) (fun q => pure (.inj true q))
    return .letv r (← lowerS E outer b) (.case r v (← wrapInl (.inj false v)) q caught)
  | .catchAll b => do wrapInl (← lowerAtSum E outer b)
  | .fin poll dd b => do
    let v ← ufresh
    if !E.mayR b then
      return .letv v (← lowerP E (outer ++ [dd]) b) (← finNormal true poll dd v)
    let r ← ufresh; let q ← ufresh
    return .letv r (← lowerS E (outer ++ [dd]) b)
      (.case r v (← finNormal true poll dd v) q (← finalise E dd q))
  | .absurd s => return .absurd s
  | .hnd .. | .ubind .. | .perform _ | .run .. | .await .. =>
    throw "unwind: a handler or a control operation not lowered (`Capture`)"
  | t => wrapInl t

/-- `t` at a sum, `inl` of its value when it cannot raise. -/
def lowerAtSum (E : UEnv) (outer : List Var) (t : Tm) : UM Tm := do
  if E.mayR t then lowerS E outer t else wrapInl (← lowerP E outer t)
end

/-! ### The pass -/

/-- The classes of codes called at one site: a union-find, its root found in at most `fuel`
steps. -/
def ufFindF (parent : Array Nat) : Nat → Nat → Nat
  | 0, c => c
  | fuel + 1, c =>
    let p := parent[c]!
    if p == c then c else ufFindF parent fuel p

def ufFind (parent : Array Nat) (c : Nat) : Nat := ufFindF parent parent.size c

def ufUnion (parent : Array Nat) (a b : Nat) : Array Nat :=
  let ra := ufFind parent a
  let rb := ufFind parent b
  if ra == rb then parent else parent.set! ra rb

/-- The call sites' code sets: every call's, and a finaliser frame's call of its finaliser. -/
def sitesOf (F : UFacts) : Tm → List (List Nat)
  | .app f _ | .run f _ => [F.codesOf f]
  | .letv _ e b => sitesOf F e ++ sitesOf F b
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b | .catch _ b | .catchAll b => sitesOf F b
  | .fin _ dd b => F.codesOf dd :: sitesOf F b
  | .case _ _ b₁ _ b₂ | .when _ _ _ _ b₁ b₂ => sitesOf F b₁ ++ sitesOf F b₂
  | _ => []

/-- The largest variable a term binds or uses, `self`s aside. -/
def Tm.maxVar : Tm → Var
  | .letv x e b => max x (max e.maxVar b.maxVar)
  | .letpair x y p b => max (max x y) (max p b.maxVar)
  | .case s x b₁ y b₂ => max s (max (max x y) (max b₁.maxVar b₂.maxVar))
  | .when s _ _ x b r => max (max s x) (max b.maxVar r.maxVar)
  | .copy x x' b => max (max x x') b.maxVar
  | .drop x b => max x b.maxVar
  | .hnd _ hr cls b => max (max hr cls) b.maxVar
  | .ubind nn dd b => max (max nn dd) b.maxVar
  | .fin _ dd b => max dd b.maxVar
  | .catch _ b | .catchAll b => b.maxVar
  | t => (t.fv.filter (fun x => !Var.isSelf x)).foldl max 0

/-- The term has an abortive construct of §19 that this pass lowers. -/
def Tm.hasRaise : Tm → Bool
  | .raise _ | .reraise .. | .catch .. | .fin .. | .catchAll _ => true
  | .letv _ e b => e.hasRaise || b.hasRaise
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b => b.hasRaise
  | .case _ _ b₁ _ b₂ | .when _ _ _ _ b₁ b₂ => b₁.hasRaise || b₂.hasRaise
  | _ => false

/-- The `raise`s of a term. -/
def Tm.raiseSites : Tm → Nat
  | .raise _ => 1
  | .letv _ e b => e.raiseSites + b.raiseSites
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b | .catch _ b | .fin _ _ b | .catchAll b =>
    b.raiseSites
  | .case _ _ b₁ _ b₂ | .when _ _ _ _ b₁ b₂ => b₁.raiseSites + b₂.raiseSites
  | _ => 0

/-- Every code's raised keys, the least solution by iteration, and the keys a `reraise` may
raise. -/
def UFacts.solve (defs : Std.HashMap Var Tm) (S : Solver) (p : Prog) : UFacts := Id.run do
  let mut F : UFacts := ⟨defs, S, .replicate p.codes.size (some []), some []⟩
  let terms := p.main :: p.codes.toList.map (·.body)
  -- Each round adds a key to a code or to the reraised keys, or makes one unknown; the keys are
  -- at most the `raise`s.
  let keys := terms.foldl (fun k t => k + t.raiseSites) 0 + 2
  for _ in [0:(p.codes.size + 1) * keys + 1] do
    let rc := p.codes.map fun c => F.raises c.body
    let rr := terms.foldl (fun r t => Raises.union r (F.caughtAll t)) (some [])
    let len (r : Raises) := r.map (·.length)
    let same := (rc.toList.zip F.rc.toList).all (fun (r, r') => len r == len r') && len rr == len F.rr
    F := { F with rc, rr }
    if same then break
  return F

/-- **Lower the abortive operations.**  A program with none is returned as it is. -/
def Prog.unwind (p : Prog) : Except String Prog := do
  if !(p.main.hasRaise || p.codes.any (·.body.hasRaise)) then return p
  let terms := p.main :: p.codes.toList.map (·.body)
  let defs := terms.foldl defsOf {}
  let cs := p.constraints
  let some S := solve p.codes cs (1 <<< 40) | throw "unwind: the flow analysis did not finish"
  let F := UFacts.solve defs S p
  -- The convention: the classes of codes called at one site.
  let mut parent : Array Nat := (List.range p.codes.size).toArray
  for t in terms do
    for site in sitesOf F t do
      if let c :: rest := site then
        for c' in rest do parent := ufUnion parent c c'
  let raising := (List.range p.codes.size).filter fun c => !Raises.isEmpty F.rc[c]!
  let sumConv := (List.range p.codes.size).toArray.map fun c =>
    raising.any fun c' => ufFind parent c' == ufFind parent c
  if let some fin := p.fin then
    if sumConv[fin]! then throw "unwind: a loop's code raises"
  let E : UEnv := ⟨F, sumConv⟩
  let next := (terms.map Tm.maxVar).foldl max 0 + 1
  -- `self`s are not variables: the fresh ones are below them.
  let act : UM Prog := do
    if E.mayR p.main then throw "unwind: an operation no handler catches"
    let main ← lowerP E [] p.main
    let codes ← p.codes.toList.zipIdx.mapM fun (c, k) => do
      let body ← if sumConv[k]! then lowerAtSum E [] c.body else lowerP E [] c.body
      pure { c with body }
    pure { p with main, codes := codes.toArray }
  act.run' ⟨next⟩

end Backend.Clos

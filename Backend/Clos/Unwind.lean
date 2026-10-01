import Std.Data.HashMap
import Backend.Clos.Flow
import Backend.Clos.Convert

/-!
# Backend — lowering the abortive operations  `[spec §19]`

`raise`, its handlers `hnd` and the finaliser frames `ubind` (`Tm.raise`, `Tm.hnd`, `Tm.ubind`,
from `Convert`) become ordinary closure IR: **branch-per-call propagation**, the representation
of Rust's `Result` and `?`.

- **Which code raises.** A `raise` carries its name and operation as literals (§19: names are
  static), so its *key* `(n, i)` is known. A code raises the keys its body may raise and no
  handler of it catches: a `raise`'s key, the keys of the codes a call may call (the 0-CFA,
  `Backend/Clos/Flow.lean`), a handler's body less its name's keys, and the clauses a handler or a
  finaliser frame calls. The least solution is found by iteration.
- **The convention.** A code that may raise answers a sum: `inl v` when it returns `v`, `inr p`
  when it raises `p`. Codes that a call may call alike share one convention (a class of the
  codes called at one site): a class with a raising code answers sums throughout.
- **The rewrite.** A term that may raise is computed as such a sum. `let x = e in b`, with `e`
  raising, is `case e {inl x ⇒ b | inr p ⇒ drop (the rest's variables); inr p}`; a call of a
  non-raising code, or a term that cannot raise, is not touched, so a call pays a branch exactly
  when its callee may raise. A tail call passes the callee's sum on with no branch. A handler
  cases on its body's sum: `inl v` goes to its answer clause, `inr (n, (i, w))` of its name to the
  clause `i` on `w`, any other name on outward. A finaliser frame runs its finaliser on `inr p`
  and raises `p` again (or the finaliser's own error, which supersedes it).

There is no handler stack and no search: the handler a `raise` reaches is the one whose `case`
its sum arrives at. Control operations (`perform`) and cancels (`ccatch`, `cfin`) are not
lowered (`Convert` rejects them).
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
  | .inj _ a => [a]
  | .clos _ xs | .prim _ xs => xs
  | .app f a => [f, a]
  | .letv x e b => e.fv ++ b.fv.filter (· != x)
  | .letpair x y p b => p :: b.fv.filter (fun z => z != x && z != y)
  | .case s x b₁ y b₂ => s :: b₁.fv.filter (· != x) ++ b₂.fv.filter (· != y)
  | .copy x x' b => x :: b.fv.filter (· != x')
  | .drop x b => x :: b.fv
  | .raise p => [p]
  | .hnd _ hr cls b => hr :: cls :: b.fv
  | .ubind nn dd b => nn :: dd :: b.fv

/-- The free variables of a term that are variables, each once. -/
def Tm.fvs (t : Tm) : List Var := (t.fv.filter (fun x => !Var.isSelf x)).eraseDups

/-- Every `letv`'s definition, by its variable. -/
def defsOf (acc : Std.HashMap Var Tm) : Tm → Std.HashMap Var Tm
  | .letv x e b => defsOf (defsOf (acc.insert x e) e) b
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b | .hnd _ _ _ b | .ubind _ _ b => defsOf acc b
  | .case _ _ b₁ _ b₂ => defsOf (defsOf acc b₁) b₂
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

/-- The `raise`s of a term. -/
def raisesIn : Tm → List Var
  | .raise p => [p]
  | .letv _ e b => raisesIn e ++ raisesIn b
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b | .hnd _ _ _ b | .ubind _ _ b => raisesIn b
  | .case _ _ b₁ _ b₂ => raisesIn b₁ ++ raisesIn b₂
  | _ => []

/-- The analysis' facts: definitions, the flow solution, every code's raised keys. -/
structure UFacts where
  defs : Std.HashMap Var Tm
  S : Solver
  rc : Array Raises

/-- The codes of the closures a key holds. -/
def Solver.closuresAt (S : Solver) (k : Nat) : List Nat :=
  ((S.set[k]?.getD #[]).toList.filterMap fun v => match S.vals[v]! with
    | .clos c => some c
    | _ => none).eraseDups

/-- The codes of the clauses at index `j` of the clause tuples a key holds. -/
def Solver.clausesAt (S : Solver) (k : Nat) : Nat → List Nat
  | 0 => ((S.set[k]?.getD #[]).toList.flatMap fun v => match S.vals[v]! with
    | .pair a _ => S.closuresAt a
    | _ => []).eraseDups
  | j + 1 => ((S.set[k]?.getD #[]).toList.flatMap fun v => match S.vals[v]! with
    | .pair _ b => S.clausesAt b j
    | _ => []).eraseDups

def UFacts.codesOf (F : UFacts) (x : Var) : List Nat := F.S.closuresAt (F.S.num.idx (.var x))

def UFacts.clauses (F : UFacts) (cls : Var) (j : Nat) : List Nat :=
  F.S.clausesAt (F.S.num.idx (.var cls)) j

def UFacts.rcOf (F : UFacts) (cs : List Nat) : Raises :=
  cs.foldl (fun r c => Raises.union r (F.rc[c]?.getD (some []))) (some [])

/-- The keys a term may raise. -/
def UFacts.raises (F : UFacts) : Tm → Raises
  | .raise p => (payloadKey F.defs p).map ([·])
  | .app f _ => F.rcOf (F.codesOf f)
  | .letv _ e b => Raises.union (F.raises e) (F.raises b)
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b => F.raises b
  | .case _ _ b₁ _ b₂ => Raises.union (F.raises b₁) (F.raises b₂)
  | .hnd n hr cls b =>
    match F.raises b with
    | none => none
    | some ks =>
      let caught := ks.filter (·.1 == n)
      let rest : Raises := some (ks.filter (·.1 != n))
      let cl := caught.foldl (fun r k => Raises.union r (F.rcOf (F.clauses cls k.2.toNat)))
        (some [])
      Raises.union (Raises.union rest (F.rcOf (F.codesOf hr))) cl
  | .ubind nn dd b =>
    Raises.union (Raises.union (F.raises b) (F.rcOf (F.codesOf nn))) (F.rcOf (F.codesOf dd))
  | _ => some []

/-! ### The rewrite -/

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

/-- Take the clause `j` out of the clause tuple `cls`, drop the others, and run `k c`. -/
def withClause (cls : Var) (j : Nat) (k : Var → UM Tm) : UM Tm := do
  match j with
  | 0 => do
    let c ← ufresh; let r ← ufresh
    return .letpair c r cls (.drop r (← k c))
  | j + 1 => do
    let c ← ufresh; let r ← ufresh
    return .letpair c r cls (.drop c (← withClause r j k))

/-- A handler, its body lowered at a sum (`bS`) and at a plain value (`bP`): its body's sum,
cased on. -/
def lowerHnd (E : UEnv) (sumMode : Bool) (n : UInt32) (hr cls : Var) (b : Tm) (bS bP : UM Tm) :
    UM Tm := do
  let some ks := E.F.raises b | throw "unwind: a raise whose name is not a literal"
  let caught := (ks.filter (·.1 == n)).map (·.2.toNat)
  let others := ks.any (·.1 != n)
  if others && !sumMode then throw "unwind: an operation no handler catches"
  let v ← ufresh
  let answer ← callAs sumMode (E.sumOf (E.F.codesOf hr)) hr v
  if caught.isEmpty && !others then
    -- The body raises nothing: its value goes to the answer clause.
    return .letv v (← bP) (.drop cls answer)
  let r ← ufresh; let q ← ufresh
  let m ← ufresh; let qi ← ufresh; let i ← ufresh; let w ← ufresh
  -- The clause of operation `j`, on `w`; `i` is dropped.
  let clauseCall (j : Nat) : UM Tm := withClause cls j fun c => do
    return .drop i (← callAs sumMode (E.sumOf (E.F.clauses cls j)) c w)
  -- Dispatch on the operation among the caught ones.
  let rec dispatch : List Nat → UM Tm
    | [] => throw "unwind: no clause"
    | [j] => clauseCall j
    | j :: js => do
      let i' ← ufresh; let l ← ufresh; let pr ← ufresh; let bo ← ufresh; let u₁ ← ufresh
      let u₂ ← ufresh
      return .copy i i' (.letv l (.lit (.i32 j.toUInt32)) (.letv pr (.pair i' l)
        (.letv bo (.prim (.host (.rel .w32 .eq)) [pr])
          (.case bo u₁ (.drop u₁ (← dispatch js)) u₂ (.drop u₂ (← clauseCall j))))))
  let propagateArm : UM Tm := do
    let qi' ← ufresh; let q' ← ufresh
    return .drop cls (.letv qi' (.pair i w) (.letv q' (.pair m qi') (.inj true q')))
  -- (`pure`, not `return`, in the arms: `return` would leave the whole function.)
  let onRaise ← match caught.isEmpty, others with
    | false, false => do
      let d ← dispatch caught
      pure (.drop m d)
    | true, true => propagateArm
    | false, true => do
      let arm : Tm := .drop m (← dispatch caught)
      let m' ← ufresh; let l ← ufresh; let pr ← ufresh; let bo ← ufresh; let u₁ ← ufresh
      let u₂ ← ufresh
      let pa ← propagateArm
      pure (.copy m m' (.letv l (.lit (.i32 n)) (.letv pr (.pair m' l)
        (.letv bo (.prim (.host (.rel .w32 .eq)) [pr])
          (.case bo u₁ (.drop u₁ pa) u₂ (.drop u₂ arm))))))
    | true, false => throw "unwind: unreachable"
  return .letv r (← bS) (.case r v (.drop cls answer) q
    (.drop hr (.letpair m qi q (.letpair i w qi onRaise))))

/-- A finaliser frame, its body lowered at a sum (`bS`) and at a plain value (`bP`): on `inr p`,
the finaliser, then `p` raised again (or the finaliser's own error). -/
def lowerUbind (E : UEnv) (sumMode : Bool) (nn dd : Var) (b : Tm) (bS bP : UM Tm) : UM Tm := do
  let v ← ufresh
  let normal ← callAs sumMode (E.sumOf (E.F.codesOf nn)) nn v
  if !E.mayR b then
    return .letv v (← bP) (.drop dd normal)
  if !sumMode then throw "unwind: a finaliser frame whose body raises, where no raise is handled"
  let r ← ufresh; let q ← ufresh; let u ← ufresh; let dr ← ufresh
  let fin ← if E.sumOf (E.F.codesOf dd) then do
      let u₂ ← ufresh; let q₂ ← ufresh
      pure (.case dr u₂ (.drop u₂ (.inj true q)) q₂ (.drop q (.inj true q₂)))
    else pure (.drop dr (.inj true q))
  return .letv r (← bS) (.case r v (.drop dd normal) q
    (.drop nn (.letv u .unit (.letv dr (.app dd u) fin))))

mutual
/-- `t` at a plain value: it cannot raise. -/
def lowerP (E : UEnv) : Tm → UM Tm
  | .letv x e b => return .letv x (← lowerP E e) (← lowerP E b)
  | .letpair x y p b => return .letpair x y p (← lowerP E b)
  | .case s x b₁ y b₂ => return .case s x (← lowerP E b₁) y (← lowerP E b₂)
  | .copy x x' b => return .copy x x' (← lowerP E b)
  | .drop x b => return .drop x (← lowerP E b)
  | .app f a => callAs false (E.sumAt f) f a
  | .raise _ => throw "unwind: a raise where none is handled"
  | .hnd n hr cls b => lowerHnd E false n hr cls b (lowerS E b) (lowerP E b)
  | .ubind nn dd b => lowerUbind E false nn dd b (lowerS E b) (lowerP E b)
  | t => return t

/-- `t` at a sum: `inl` of its value, or `inr` of what it raises. -/
def lowerS (E : UEnv) : Tm → UM Tm
  | .raise p => return .inj true p
  | .app f a => callAs true (E.sumAt f) f a
  | .letv x e b => do
    if E.mayR e then
      let r ← ufresh; let q ← ufresh
      let rest := b.fvs.filter (· != x)
      return .letv r (← lowerS E e) (.case r x (← lowerS E b) q (propagateOn rest q))
    else return .letv x (← lowerP E e) (← lowerS E b)
  | .letpair x y p b => return .letpair x y p (← lowerS E b)
  | .case s x b₁ y b₂ => return .case s x (← lowerS E b₁) y (← lowerS E b₂)
  | .copy x x' b => return .copy x x' (← lowerS E b)
  | .drop x b => return .drop x (← lowerS E b)
  | .hnd n hr cls b => lowerHnd E true n hr cls b (lowerS E b) (lowerP E b)
  | .ubind nn dd b => lowerUbind E true nn dd b (lowerS E b) (lowerP E b)
  | t => wrapInl t
end

/-- `t` at a sum, `inl` of its value when it cannot raise. -/
def lowerAtSum (E : UEnv) (t : Tm) : UM Tm := do
  if E.mayR t then lowerS E t else wrapInl (← lowerP E t)

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

/-- The call sites' code sets: every call's, and the closures a handler or a finaliser frame
calls. -/
def sitesOf (F : UFacts) (ops : Nat) : Tm → List (List Nat)
  | .app f _ => [F.codesOf f]
  | .letv _ e b => sitesOf F ops e ++ sitesOf F ops b
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b => sitesOf F ops b
  | .case _ _ b₁ _ b₂ => sitesOf F ops b₁ ++ sitesOf F ops b₂
  | .hnd _ hr cls b =>
    F.codesOf hr :: (List.range ops).map (F.clauses cls) ++ sitesOf F ops b
  | .ubind nn dd b => F.codesOf nn :: F.codesOf dd :: sitesOf F ops b
  | _ => []

/-- The largest variable a term binds or uses, `self`s aside. -/
def Tm.maxVar : Tm → Var
  | .letv x e b => max x (max e.maxVar b.maxVar)
  | .letpair x y p b => max (max x y) (max p b.maxVar)
  | .case s x b₁ y b₂ => max s (max (max x y) (max b₁.maxVar b₂.maxVar))
  | .copy x x' b => max (max x x') b.maxVar
  | .drop x b => max x b.maxVar
  | .hnd _ hr cls b => max (max hr cls) b.maxVar
  | .ubind nn dd b => max (max nn dd) b.maxVar
  | t => (t.fv.filter (fun x => !Var.isSelf x)).foldl max 0

/-- The program has a construct of §19. -/
def Tm.hasEffect : Tm → Bool
  | .raise _ | .hnd .. | .ubind .. => true
  | .letv _ e b => e.hasEffect || b.hasEffect
  | .letpair _ _ _ b | .copy _ _ b | .drop _ b => b.hasEffect
  | .case _ _ b₁ _ b₂ => b₁.hasEffect || b₂.hasEffect
  | _ => false

/-- **Lower the abortive operations.**  A program with none is returned as it is. -/
def Prog.unwind (p : Prog) : Except String Prog := do
  if !(p.main.hasEffect || p.codes.any (·.body.hasEffect)) then return p
  let terms := p.main :: p.codes.toList.map (·.body)
  let defs := terms.foldl defsOf {}
  -- The clauses a handler may call: one past the largest operation a `raise` carries.
  let mut ops := 0
  for t in terms do
    for x in raisesIn t do
      match payloadKey defs x with
      | some (_, i) => ops := max ops (i.toNat + 1)
      | none => throw "unwind: a raise whose name is not a literal"
  let cs := p.constraints ops
  let some S := solve p.codes cs (1 <<< 40) | throw "unwind: the flow analysis did not finish"
  -- Every code's raised keys: the least solution, by iteration.
  let mut F : UFacts := ⟨defs, S, .replicate p.codes.size (some [])⟩
  -- Each round adds a key to a code or makes it unknown, so the rounds are at most the codes
  -- times the keys and one.
  for _ in [0:p.codes.size * (ops * 64 + 2) + 1] do
    let rc := p.codes.map fun c => F.raises c.body
    let same := (rc.toList.zip F.rc.toList).all fun (r, r') => (r.map (·.length)) == (r'.map (·.length))
    F := { F with rc }
    if same then break
  -- The convention: the classes of codes called at one site.
  let mut parent : Array Nat := (List.range p.codes.size).toArray
  for t in terms do
    for site in sitesOf F ops t do
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
    let main ← lowerP E p.main
    let codes ← p.codes.toList.zipIdx.mapM fun (c, k) => do
      let body ← if sumConv[k]! then lowerAtSum E c.body else lowerP E c.body
      pure { c with body }
    pure { p with main, codes := codes.toArray }
  act.run' ⟨next⟩

end Backend.Clos

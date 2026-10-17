import Std.Data.HashSet
import Std.Data.TreeMap
import Paper.S1_Syntax.Definitions
import Backend.Clos.Syntax

/-!
# Backend — closure conversion

`convert` takes the erased `Expr` of `main` (`Frontend.Check.checkProgram_sound`) to the closure
IR. One pass does three things:

- **Naming and A-normal form.** De Bruijn indices become variables; each intermediate result is
  named by `letv`, in the machine's evaluation order (`Support/Dynamics/Interpreter.lean`:
  pairs left to right, the argument of an application before the function).
- **Ownership.** For sequential parts (the two sides of a pair, `seq`, `letpair`, the scrutinee
  and arms of a `case`, argument and function of an application), a variable free in a part
  and in a later part is `copy`-ed for the earlier one; the last user takes the original. The
  two arms of a `case` are one part, so a variable used by both arms is not copied: each path
  uses it once. An arm drops what only the other arm uses, and every binder is dropped where
  its scope does not use it. So each variable is consumed exactly once on every path, as
  substitution does in the source.
- **`let`.** A β-redex `(λx. b) a`, how the erasure spells `let`, is `letv x a b`: the
  argument is evaluated first, as the machine does, and no closure is made.
- **Closures.** `λ` captures its free variables, in index order, into an environment. A
  primitive in function position with its arguments present becomes `prim`; a primitive used
  as a value is η-expanded into closure code (`store` into two).
- **`swap`.** The axiom `swap ≜ λx.λy. let z = load x; store x y; (x, z)` becomes the closure
  IR's `swap`, which moves the old contents out instead of copying them and dropping the
  original. Its contents change type, which the layout types (`Backend/Clos/Types.lean`) follow.
- **Fixed points.** The Z combinator's fixed point `selfV B` (`Core/Fix.lean`) is one code
  `λx. B[self := clos c []]` that calls itself through a closure of its own code, which captures
  nothing; applied, `selfV B a` is a call of it. When `B` is the step of `fold_own` or
  `fold_reuse`, the step's code is recorded (`Prog.folds`) for the flat IR's pointer reversal.
- **η.** `λv. y v` of a variable `y` is `y`.
- **Operations** (spec §19). `raise p`, `perform p`, a handler `hnd (n, (qs, (hr, cls))) e` and a
  finaliser frame `ubind (N, D) M` are closure-IR nodes, which `Capture` and `Unwind` lower. The
  cancel frames `ccatch` and `cfin` occur only in the continuations the machine builds, and are
  rejected.
-/

namespace Backend.Clos
open BoCa

/-- The free de Bruijn indices of `e` under `d` binders, relative to the outside. -/
def fvsRaw : Expr → Nat → List Nat
  | .var i, d => if i < d then [] else [i - d]
  | .unit, _ => []
  | .loc _, _ => []
  | .prim _, _ => []
  | .pair a b, d => fvsRaw a d ++ fvsRaw b d
  | .seq a b, d => fvsRaw a d ++ fvsRaw b d
  | .app a b, d => fvsRaw a d ++ fvsRaw b d
  | .inj₁ a, d => fvsRaw a d
  | .inj₂ a, d => fvsRaw a d
  | .lam b, d => fvsRaw b (d + 1)
  | .letpair a b, d => fvsRaw a d ++ fvsRaw b (d + 2)
  | .case a b c, d => fvsRaw a d ++ fvsRaw b (d + 1) ++ fvsRaw c (d + 1)

/-- The free indices, each once, in order of first occurrence. -/
def fvs (e : Expr) (d : Nat) : List Nat := (fvsRaw e d).eraseDups

/-! ### Free indices of every subterm

`conv` asks for the free indices of the parts of each term it converts. Computed on demand, that
is a walk of each part at each node above it, quadratic in the depth of the term; instead they are
computed once, bottom-up, for every subterm, numbered in pre-order (a term, then its parts left
to right: `a` and `b` of `pair`, `seq`, `app` and `letpair`, the scrutinee and the two arms of
`case`). A part's number is its parent's plus one, plus the sizes of the parts before it. -/

/-- `a`, then the indices of `b` not in `a`: the free indices of two parts in order of first
occurrence. -/
def fvUnion (a b : Array Nat) : Array Nat :=
  if b.isEmpty then a else if a.isEmpty then b else
  let s : Std.HashSet Nat := a.foldl (·.insert ·) {}
  b.foldl (fun acc x => if s.contains x then acc else acc.push x) a

/-- The free indices under `k` binders, relative to the outside. -/
def fvUnder (k : Nat) (a : Array Nat) : Array Nat :=
  if k == 0 then a else a.filterMap fun x => if x < k then none else some (x - k)

/-- Every subterm's size and free indices (`fvs · 0`), by its pre-order number. -/
structure Pre where
  size : Array Nat := #[]
  fv : Array (Array Nat) := #[]

def Pre.enter : StateM Pre Nat :=
  modifyGet fun p => (p.size.size, { size := p.size.push 0, fv := p.fv.push #[] })

def Pre.leave (id : Nat) (fv : Array Nat) : StateM Pre (Array Nat) :=
  modifyGet fun p => (fv, { size := p.size.set! id (p.size.size - id), fv := p.fv.set! id fv })

/-- Number `e` and its subterms from `pre.size.size` on; `e`'s free indices. -/
def Pre.add : Expr → StateM Pre (Array Nat)
  | .var i => do leave (← enter) #[i]
  | .unit | .loc _ | .prim _ => do leave (← enter) #[]
  | .pair a b | .seq a b | .app a b => do
    let id ← enter
    let fa ← Pre.add a
    let fb ← Pre.add b
    leave id (fvUnion fa fb)
  | .inj₁ a | .inj₂ a => do
    let id ← enter
    leave id (← Pre.add a)
  | .lam b => do
    let id ← enter
    leave id (fvUnder 1 (← Pre.add b))
  | .letpair a b => do
    let id ← enter
    let fa ← Pre.add a
    let fb ← Pre.add b
    leave id (fvUnion fa (fvUnder 2 fb))
  | .case a b c => do
    let id ← enter
    let fa ← Pre.add a
    let fb ← Pre.add b
    let fc ← Pre.add c
    leave id (fvUnion (fvUnion fa (fvUnder 1 fb)) (fvUnder 1 fc))

def Pre.of (e : Expr) : Pre := (Pre.add e).run {} |>.2

/-- A context: the variable of each de Bruijn index, by its level (the index `i` of a context of
`depth` binders is level `depth - 1 - i`). A level with no variable is one a closure body cannot
refer to. -/
structure Ctx where
  depth : Nat := 0
  vars : Std.TreeMap Nat Var := {}

def Ctx.push (c : Ctx) (x : Var) : Ctx := { depth := c.depth + 1, vars := c.vars.insert c.depth x }

def Ctx.get? (c : Ctx) (i : Nat) : Option (Option Var) :=
  if i < c.depth then some c.vars[c.depth - 1 - i]? else none

def Ctx.set (c : Ctx) (i : Nat) (x : Var) : Ctx :=
  if i < c.depth then { c with vars := c.vars.insert (c.depth - 1 - i) x } else c

/-- The context of the variables `xs`, the first at index 0. -/
def Ctx.ofList (xs : List Var) : Ctx := xs.foldr (fun x c => c.push x) {}

/-- A marked use of a polymorphic let (`polyLets`): the let's number, the marked use it is
converted inside (its index among the uses), and the codes its conversion registers, in order,
the shared code of literals aside. -/
structure PolyUse where
  letId : Nat
  parent : Option Nat
  codes : Array Nat := #[]

structure CState where
  next : Nat
  codes : Array Code
  folds : List FoldCode := []
  pre : Pre := {}
  /-- The literals' bytes so far, each literal once. -/
  data : Array UInt8 := #[]
  /-- The address of each literal's bytes, by its bytes. -/
  lits : List (List UInt8 × Nat) := []
  litCode : Option Nat := none
  /-- The marked uses of polymorphic lets converted so far. -/
  uses : Array PolyUse := #[]
  /-- The marked uses being converted, innermost first. -/
  useStack : List Nat := []

abbrev CM := StateT CState (Except String)

/-- The variable standing for an index a closure body cannot refer to. -/
def dummy : Var := 0

/-- The variables from `selfBase` on are not variables: `selfBase + c` stands for `self` in the
native fixed point of code `c` (see `conv`), the closure `clos c []`, built where it is used. It
is never captured, copied or dropped. -/
def selfBase : Var := 1 <<< 62

def Var.isSelf (x : Var) : Bool := x ≥ selfBase

def fresh : CM Var := modifyGet fun s => (s.next, { s with next := s.next + 1 })

def register (c : Code) : CM Nat :=
  modifyGet fun s => (s.codes.size, { s with codes := s.codes.push c })

def lookup (ctx : Ctx) (i : Nat) : CM Var :=
  match ctx.get? i with
  | some (some x) => pure x
  | some none => throw s!"index {i} is not captured"
  | none => throw s!"unbound index {i}"

/-- The size of subterm `id`. -/
def sizeAt (id : Nat) : CM Nat := return (← get).pre.size[id]?.getD 0

/-- `fvs e d` of the subterm `e` numbered `id`. -/
def fvsAt (id : Nat) (d : Nat) : CM (List Nat) := return (fvUnder d (← get).pre.fv[id]!).toList

def wrapCopies (cs : List (Var × Var)) (t : Tm) : Tm :=
  cs.foldr (fun (x, x') t => .copy x x' t) t

def wrapDrops (xs : List Var) (t : Tm) : Tm :=
  xs.foldr (fun x t => .drop x t) t

/-- Copies for two sequential parts using the indices `f₁` and `f₂`: every index in both is
    copied for the first part. The contexts the two parts are converted in. -/
def plan2 (ctx : Ctx) (f₁ f₂ : List Nat) : CM (List (Var × Var) × Ctx × Ctx) := do
  let in₂ : Std.HashSet Nat := f₂.foldl (·.insert ·) {}
  let shared := f₁.filter in₂.contains
  let mut cs : Array (Var × Var) := #[]
  let mut ctx₁ := ctx
  for i in shared do
    let x ← lookup ctx i
    if x.isSelf then continue
    let x' ← fresh
    cs := cs.push (x, x')
    ctx₁ := ctx₁.set i x'
  return (cs.toList, ctx₁, ctx)

/-- The variables of the indices `is` in `ctx`, but for the fixed points' `self`s. -/
def vars (ctx : Ctx) (is : List Nat) : CM (List Var) :=
  return (← is.mapM (lookup ctx)).filter (!·.isSelf)

def Op.ofPrim? : Prim → Option Op
  | .alloc => some .alloc
  | .free => some .free
  | .load => some .load
  | .host op => some (.host op)
  | .tab => some .tab
  | .idx => some .idx
  | .split => some .split
  | .drop => some .drop
  | .count => some .count
  | .countTry => some .countTry
  -- `bounded_fix` is converted to codes of its own (`fixValue`).
  | .boundedFix => none
  | .store => none
  | .lit _ => none
  -- The primitives of spec §19 are converted by their shapes in `conv`; as values `primValue`
  -- rejects them.
  | .perform | .raise | .hnd | .ubind | .ccatch | .cfin => none

/-- `bounded_fix` (spec §20) as two codes: `fix (s, (k, a))` calls `s` on `(self, a)`, `self`
`inj₁ ()` at `k = 0` and otherwise `inj₂` of a closure of `self` over `s` and `k − 1`, whose call
`self x` calls `fix (s, (k − 1, x))`. The recursion is ordinary calls of known codes: the budget is
a word passed down, the self-reference a closure of `s`'s words and the budget, a stack value, and
nothing is allocated. Each occurrence has codes of its own, at its own types. -/
def fixValue : CM Tm := do
  let cF ← register ⟨[], dummy, .unit⟩
  -- `self x = fix (s, (j, x))`.
  let es ← fresh; let ej ← fresh; let x ← fresh
  let r₁ ← fresh; let r₂ ← fresh; let f ← fresh
  let cS ← register ⟨[es, ej], x,
    .letv r₁ (.pair ej x) (.letv r₂ (.pair es r₁) (.letv f (.clos cF []) (.app f r₂)))⟩
  -- `fix (s, (k, a)) = s (self, a)`.
  let p ← fresh; let sv ← fresh; let r ← fresh; let k ← fresh; let a ← fresh
  let k' ← fresh; let b ← fresh; let u₁ ← fresh; let u₂ ← fresh
  let s' ← fresh; let one ← fresh; let q ← fresh; let j ← fresh; let cl ← fresh
  let sf₁ ← fresh; let pr₁ ← fresh; let un ← fresh; let sf₂ ← fresh; let pr₂ ← fresh
  let more : Tm := .drop u₁ (.copy sv s' (.letv one (.lit (.i32 1)) (.letv q (.pair k one)
    (.letv j (.prim (.host (.bin .w32 .sub)) [q]) (.letv cl (.clos cS [s', j])
      (.letv sf₁ (.inj true cl) (.letv pr₁ (.pair sf₁ a) (.app sv pr₁))))))))
  let spent : Tm := .drop u₂ (.drop k (.letv un .unit (.letv sf₂ (.inj false un)
    (.letv pr₂ (.pair sf₂ a) (.app sv pr₂)))))
  let body : Tm := .letpair sv r p (.letpair k a r (.copy k k'
    (.letv b (.prim (.host (.eqz .w32)) [k']) (.case b u₁ more u₂ spent))))
  modify fun st => { st with codes := st.codes.set! cF ⟨[], p, body⟩ }
  return .clos cF []

/-- A primitive as a value: η-expanded closure code. -/
def primValue : Prim → CM Tm
  | .lit c => pure (.lit c)
  | .boundedFix => fixValue
  | .store => do
      let l ← fresh; let l' ← fresh; let v ← fresh
      let c₂ ← register ⟨[l'], v, .prim .store [l', v]⟩
      let c₁ ← register ⟨[], l, .clos c₂ [l]⟩
      pure (.clos c₁ [])
  | p => do
      match Op.ofPrim? p with
      | some op =>
        let x ← fresh
        let c ← register ⟨[], x, .prim op [x]⟩
        pure (.clos c [])
      | none => throw "unreachable primitive"

/-- The axiom `swap ≜ λx.λy. let z = load x; store x y; (x, z)` (`Paper.S2_Statics`, [TR] 3.24). -/
def isSwap : Expr → Bool
  | .lam (.lam (.app (.lam (.seq (.app (.app (.prim .store) (.var 2)) (.var 1))
      (.pair (.var 2) (.var 0)))) (.app (.prim .load) (.var 1)))) => true
  | _ => false

/-- The code of the axiom `swap`: `λx. λy. swap x y`. -/
def swapValue : CM Tm := do
  let l ← fresh; let l' ← fresh; let v ← fresh
  let c₂ ← register ⟨[l'], v, .prim .swap [l', v]⟩
  let c₁ ← register ⟨[], l, .clos c₂ [l]⟩
  pure (.clos c₁ [])

deriving instance BEq for BoCa.Expr

/-- `X = λx. F (λv. x x v)` for `F = λself. λx. B` (`Core/Fix.lean`, `zX`). -/
def zXE (B : Expr) : Expr :=
  .lam (.app (.lam (.lam B)) (.lam (.app (.app (.var 1) (.var 1)) (.var 0))))

/-- The Z combinator's fixed point `selfV B = λv. X X v` (`Core/Fix.lean`, `selfV`), with
`B` closed under its two binders (`self` = 1, `x` = 0): its body `B`. -/
def fixBody? : Expr → Option Expr
  | .lam (.app (.app (.lam (.app (.lam (.lam B)) (.lam (.app (.app (.var 1) (.var 1)) (.var 0)))))
      x₂) (.var 0)) =>
    if x₂ == zXE B && (fvs B 0).all (· < 2) then some B else none
  | _ => none

/-- The shape of an owned fold's traversal, `travO F` (`Core/FoldOwn.lean`) or, with `reuse`,
`travR F` (`Core/FoldReuse.lean`). -/
def travShape? (reuse : Bool) : Expr → Option FSh
  | .lam (.lam (.var 0)) => some .leaf
  | .lam (.lam (.app (.var 1) (.var 0))) => some .varX
  | .lam (.lam (.app (.var 1) (.app (.prim .free) (.var 0)))) => if reuse then none else some .refX
  | .lam (.lam (.app (.lam (.letpair (.var 0) (.app (.lam (.pair (.var 2) (.var 0)))
      (.app (.var 4) (.var 0))))) (.app (.app sw (.var 0)) .unit))) =>
    if reuse && isSwap sw then some .refX else none
  | .lam (.lam (.letpair (.var 0) (.app (.lam (.app (.lam (.pair (.var 1) (.var 0)))
      (.app (.app tG (.var 4)) (.var 1)))) (.app (.app tF (.var 3)) (.var 1))))) =>
    match travShape? reuse tF, travShape? reuse tG with
    | some F, some G => some (.tensor F G)
    | _, _ => none
  | .lam (.lam (.case (.var 0) (.app (.lam (.inj₁ (.var 0))) (.app (.app tF (.var 2)) (.var 0)))
      (.app (.lam (.inj₂ (.var 0))) (.app (.app tG (.var 2)) (.var 0))))) =>
    match travShape? reuse tF, travShape? reuse tG with
    | some F, some G => some (.sum F G)
    | _, _ => none
  | _ => none

/-- The body of an owned fold's fixed point, `λu. trav T (λw. self g w) u to r. g r`
(`fBO`, `fBR`): whether it is `fold_reuse`'s, and its shape. -/
def foldShape? : Expr → Option (Bool × FSh)
  | .lam (.app (.lam (.app (.var 2) (.var 0)))
      (.app (.app t (.lam (.app (.app (.var 3) (.var 2)) (.var 0)))) (.var 0))) =>
    match travShape? false t with
    | some F => some (false, F)
    | none => (travShape? true t).map (true, ·)
  | _ => none

/-- Reserve a code index, filled by `setCode`. -/
def reserve : CM Nat := register ⟨[], dummy, .unit⟩

/-! ### Literals

A string literal `"…"` is the value `(n, t)`, `t` the `!` function from an index to its byte
(`Frontend.Sugar.litValue`): a compare with the length, then a search on the index down to one
byte. A λ of that shape is converted to a closure of one shared code, `litCode`, capturing the
address of the literal's bytes in the read-only data and its length; its body is `litByte`, a
load. So every literal is the same code, a call of one is direct, and its bytes are emitted once.
The shape is semantic: a λ of it computes exactly its table, however it was written. -/

/-- The bytes a search over the index (the variable at depth `d`) answers on the indices
`[lo, hi)`: a `case` on `lt_u (i, mid)` whose `inl` arm is `[mid, hi)` and whose `inr` arm is
`[lo, mid)`, down to a byte literal. -/
def litTree : Nat → Nat → Nat → Nat → Expr → Option (List UInt8)
  | 0, _, _, _, _ => none
  | f + 1, d, lo, hi, e =>
    if hi ≤ lo + 1 then
      match e with
      | .prim (.lit (.u8 b)) => some [b]
      | _ => none
    else
      let mid := (lo + hi) / 2
      match e with
      | .case (.app (.prim (.host (.rel .w32 .lt_u))) (.pair (.var i) (.prim (.lit (.i32 m))))) a b =>
        if i == d && m.toNat == mid then do
          let up ← litTree f (d + 1) mid hi a
          let down ← litTree f (d + 1) lo mid b
          pure (down ++ up)
        else none
      | _ => none

/-- The bytes of a literal's tabulator `λi. body`, when `body` has the literal's shape. -/
def litTable? (body : Expr) : Option (List UInt8) :=
  match body with
  | .prim (.lit (.u8 0)) => some []
  | .case (.app (.prim (.host (.rel .w32 .lt_u))) (.pair (.var 0) (.prim (.lit (.i32 n)))))
      (.prim (.lit (.u8 0))) t =>
    if n.toNat == 0 then none else litTree (n.toNat + 1) 1 0 n.toNat t
  | _ => none

/-- A literal's closure: `litCode` over the address of its bytes and its length. -/
def litClosure (bs : List UInt8) : CM Tm := do
  let st ← get
  let addr ← match st.lits.lookup bs with
    | some a => pure a
    | none => do
      let a := dataBase + st.data.size
      modify fun s => { s with data := s.data ++ bs.toArray, lits := (bs, a) :: s.lits }
      pure a
  let c ← match (← get).litCode with
    | some c => pure c
    | none => do
      let ea ← fresh; let en ← fresh; let i ← fresh
      let c ← register ⟨[ea, en], i, .prim .litByte [ea, en, i]⟩
      modify fun s => { s with litCode := some c }
      pure c
  let a ← fresh; let n ← fresh
  return .letv a (.lit (.i32 addr.toUInt32)) (.letv n (.lit (.i32 bs.length.toUInt32))
    (.clos c [a, n]))

/-- `x` occurs free in `e`. -/
def occurs (x : Nat) (e : Expr) : Bool := (fvsRaw e 0).contains x

/-- The body `b` of `(λa. b) (tab (n, t))` is a literal view (`Frontend.Sugar`, the borrow block
on a literal): `a` is lent by `withbor`'s term to a callback that first copies the family (only
an `imm` family can be copied, so nothing writes the array), and the array handed back is
dropped next, with `a` used nowhere else. Then the array may be the literal's read-only bytes. -/
def litView? (b : Expr) : Bool :=
  match b with
  | .app (.lam b₂) (.app (.app wb (.var 0)) cb) =>
    let withborOk := wb == .lam (.lam (.pair (.var 1) (.app (.app (.var 0) .unit) (.var 1))))
    let cbOk := match cb with
      | .lam (.lam (.letpair (.app (.lam (.pair (.var 0) (.var 0))) (.var 0)) k)) => !occurs 4 k
      | _ => false
    let dropOk := match b₂ with
      | .letpair (.var 0) (.seq (.app (.lam (.app (.prim .drop) (.pair _ (.var 0)))) (.var 1)) rest) =>
        !occurs 1 rest && !occurs 3 rest
      | _ => false
    withborOk && cbOk && dropOk && !occurs 1 b₂
  | _ => false

/-- The mark of a literal view's `tab`: its argument paired with this `i64`, which no checked
term has there (`tab` takes an `i32` length). -/
def litViewMark : UInt64 := 0x4C49545649455753

/-- The term with each literal view's `tab` marked (`litView?`), before conversion. -/
def markLitViews : Expr → Expr
  | .app (.lam b) (.app (.prim .tab) arg) =>
    let b' := markLitViews b
    let arg' := markLitViews arg
    if litView? b then .app (.lam b') (.app (.prim .tab) (.pair (.prim (.lit (.i64 litViewMark))) arg'))
    else .app (.lam b') (.app (.prim .tab) arg')
  | .pair a b => .pair (markLitViews a) (markLitViews b)
  | .seq a b => .seq (markLitViews a) (markLitViews b)
  | .app a b => .app (markLitViews a) (markLitViews b)
  | .inj₁ a => .inj₁ (markLitViews a)
  | .inj₂ a => .inj₂ (markLitViews a)
  | .lam b => .lam (markLitViews b)
  | .letpair a b => .letpair (markLitViews a) (markLitViews b)
  | .case a b c => .case (markLitViews a) (markLitViews b) (markLitViews c)
  | e => e

/-- The mark of a finaliser frame whose two clauses are one code (`markUbinds`). -/
def ubindSelMark : UInt64 := 0x55424E44534C4354

/-- `e` with its free indices from `c` on raised by `d`. -/
def shiftE (d c : Nat) : Expr → Expr
  | .var i => if i < c then .var i else .var (i + d)
  | .pair a b => .pair (shiftE d c a) (shiftE d c b)
  | .inj₁ a => .inj₁ (shiftE d c a)
  | .inj₂ a => .inj₂ (shiftE d c a)
  | .lam b => .lam (shiftE d (c + 1) b)
  | .seq a b => .seq (shiftE d c a) (shiftE d c b)
  | .letpair a b => .letpair (shiftE d c a) (shiftE d (c + 2) b)
  | .case a b e => .case (shiftE d c a) (shiftE d (c + 1) b) (shiftE d (c + 1) e)
  | .app f a => .app (shiftE d c f) (shiftE d c a)
  | e => e

/-- Each finaliser frame `ubind (λx. N, λ_. D) M` with its two clauses made one,
`ubind (λs. case s {inj₁ x. N | inj₂ _. D}, mark) M`: exactly one of them runs, so the variables
they share are captured once, not copied (`conv`). -/
def markUbinds : Expr → Expr
  | .app (.app (.prim .ubind) (.pair (.lam N) (.lam D))) m =>
    let sel : Expr := .lam (.case (.var 0) (shiftE 1 1 (markUbinds N)) (shiftE 1 1 (markUbinds D)))
    .app (.app (.prim .ubind) (.pair sel (.prim (.lit (.i64 ubindSelMark))))) (markUbinds m)
  | .pair a b => .pair (markUbinds a) (markUbinds b)
  | .seq a b => .seq (markUbinds a) (markUbinds b)
  | .app a b => .app (markUbinds a) (markUbinds b)
  | .inj₁ a => .inj₁ (markUbinds a)
  | .inj₂ a => .inj₂ (markUbinds a)
  | .lam b => .lam (markUbinds b)
  | .letpair a b => .letpair (markUbinds a) (markUbinds b)
  | .case a b c => .case (markUbinds a) (markUbinds b) (markUbinds c)
  | e => e

/-! ### Scoped cells  `[spec §35]`

The elaborator scopes three cells to one borrow: the cell of a value lent to a call (`f(&x)`,
`f(&mut x)`), of a value `modify` changes, and of a handler's state given as a value
(`Frontend/Sugar.lean`, `lendBorrow`; `Frontend/Elab/Effects.lean`, `withBlk`). Each is
`let (c, r) = withbor (alloc v) cb; …` with the owner `c` used once afterwards, by its `free`:
the borrow's scope is the cell's life. `markScoped` marks such an `alloc` and its `free` with
the scope's number; the conversion makes them `scopedAlloc k` and `scopedFree k`, which are
`alloc` and `free` in every stage, and which the flat IR places in a frame slot of the code that
holds both (`Flat/Lower.lean`, `frameScopes`). The marks are literal pairs that no checked term
has as the operand of `alloc` or `free`. -/

/-- The mark of a scoped cell's `alloc` and `free`: `scopedMark ||| k` for the scope `k`. -/
def scopedMark : UInt64 := 0x53434F5045000000

/-- The mark carries a scope's number. -/
def scopedOf? (m : UInt64) : Option Nat :=
  if m &&& 0xFFFFFFFFFF000000 == scopedMark then some (m &&& 0xFFFFFF).toNat else none

/-- The erasure of `withbor1` and `withbor2`: `λℓ. λf. (ℓ, f () ℓ)`. -/
def withborE : Expr := .lam (.lam (.pair (.var 1) (.app (.app (.var 0) .unit) (.var 1))))

/-- The free occurrences of the index `j` in `e`. -/
def occursN (j : Nat) (e : Expr) : Nat := ((fvsRaw e 0).filter (· == j)).length

/-- `e` with the one occurrence of the index `j` marked as the `free` of the scope `k`, when
that occurrence is the operand of a `free` reached through `let`s (β-redexes, which the
conversion binds in the same code) and no other `λ`. -/
def markFreeOf (k : Nat) : Nat → Expr → Option Expr
  | j, .app (.prim .free) (.var i) =>
    if i == j then some (.app (.prim .free) (.pair (.prim (.lit (.i64 (scopedMark ||| k.toUInt64))))
      (.var i))) else none
  | j, .app (.lam b) a =>
    if isSwap (.lam b) || (fixBody? (.lam b)).isSome then none
    else if a == .var j then (markFreeOf k 0 b).map fun b' => .app (.lam b') a
    else if occurs j a then (markFreeOf k j a).map (.app (.lam b) ·)
    else (markFreeOf k (j + 1) b).map fun b' => .app (.lam b') a
  | j, .app f a =>
    if occurs j f then (markFreeOf k j f).map (.app · a) else (markFreeOf k j a).map (.app f ·)
  | j, .pair a b =>
    if occurs j a then (markFreeOf k j a).map (.pair · b) else (markFreeOf k j b).map (.pair a ·)
  | j, .seq a b =>
    if occurs j a then (markFreeOf k j a).map (.seq · b) else (markFreeOf k j b).map (.seq a ·)
  | j, .inj₁ a => (markFreeOf k j a).map .inj₁
  | j, .inj₂ a => (markFreeOf k j a).map .inj₂
  | j, .letpair a b =>
    if occurs j a then (markFreeOf k j a).map (.letpair · b)
    else (markFreeOf k (j + 2) b).map (.letpair a ·)
  | j, .case a b c =>
    if occurs j a then (markFreeOf k j a).map (.case · b c)
    else if occurs (j + 1) b then (markFreeOf k (j + 1) b).map (.case a · c)
    else (markFreeOf k (j + 1) c).map (.case a b ·)
  | _, _ => none

/-- The borrow `withbor (alloc v) cb` of a fresh cell, marked as the scope `k`'s, when `b` (the
body binding the owner at `1` and the result at `0`) frees the owner and uses it nowhere else. -/
def scopedAt? (k : Nat) (w b : Expr) : Option (Expr × Expr) :=
  match w with
  | .app (.app wb (.app (.prim .alloc) v)) cb =>
    if wb != withborE || occursN 1 b != 1 then none else
    (markFreeOf k 1 b).map fun b' =>
      let mk : Expr := .prim (.lit (.i64 (scopedMark ||| k.toUInt64)))
      (.app (.app wb (.app (.prim .alloc) (.pair mk v))) cb, b')
  | _ => none

/-- The term with each scoped cell's `alloc` and `free` marked: `let (c, r) = W; b` and
`(λp. let (c, r) = p; b) W` for `W = withbor (alloc v) cb`. -/
def markScoped : Expr → StateM Nat Expr
  | .letpair w b => do
    let w ← markScoped w
    let b ← markScoped b
    let k ← get
    match scopedAt? k w b with
    | some (w', b') => set (k + 1); pure (.letpair w' b')
    | none => pure (.letpair w b)
  | .app (.lam (.letpair (.var 0) b)) w => do
    let b ← markScoped b
    let w ← markScoped w
    let k ← get
    match (if occurs 2 b then none else scopedAt? k w b) with
    | some (w', b') => set (k + 1); pure (.app (.lam (.letpair (.var 0) b')) w')
    | none => pure (.app (.lam (.letpair (.var 0) b)) w)
  | .pair a b => return .pair (← markScoped a) (← markScoped b)
  | .seq a b => return .seq (← markScoped a) (← markScoped b)
  | .app a b => return .app (← markScoped a) (← markScoped b)
  | .inj₁ a => return .inj₁ (← markScoped a)
  | .inj₂ a => return .inj₂ (← markScoped a)
  | .lam b => return .lam (← markScoped b)
  | .case a b c => return .case (← markScoped a) (← markScoped b) (← markScoped c)
  | e => pure e

/-! ### Polymorphic lets

`let x = λy. b in N` with the λ closed is SPEC §24's `[let-poly]`: each occurrence of `x` in `N`
is typed on its own, at its own row, and the let reduces by one β-step, which allocates nothing,
to `N` with the λ at each occurrence (`letPoly_compatC`). Lowering is per code: a code raises,
suspends and is called by one convention, whatever row it is used at. A let whose uses are at
different rows is converted as that β-reduct, `N[λy. b / x]`, so that each use is lowered at its
own row, as a definition is substituted at each use (`Backend/README.md`); `Backend/Clos/Poly.lean`
finds those lets. A let is what `conv` converts as one, `(λx. N) V` whose function is neither the
axiom `swap` nor a fixed point; a self-application `(λx. N) (λx. N)`, the Z combinator's `X X`, is
not a let. -/

/-- The free occurrences of the index `j` in `e`. -/
def idxUses (j : Nat) : Expr → Nat
  | .var i => if i == j then 1 else 0
  | .pair a b | .seq a b | .app a b => idxUses j a + idxUses j b
  | .inj₁ a | .inj₂ a => idxUses j a
  | .lam b => idxUses (j + 1) b
  | .letpair a b => idxUses j a + idxUses (j + 2) b
  | .case a b c => idxUses j a + idxUses (j + 1) b + idxUses (j + 1) c
  | _ => 0

/-- `e` with the closed term `v` for the index `j`, its free indices above `j` lowered by one:
`Expr.subst j v` (`Support/Syntax/Terms.lean`) at a closed `v`, which no binder shifts. -/
def substClosed (j : Nat) (v : Expr) : Expr → Expr
  | .var i => if i == j then v else if i > j then .var (i - 1) else .var i
  | .pair a b => .pair (substClosed j v a) (substClosed j v b)
  | .seq a b => .seq (substClosed j v a) (substClosed j v b)
  | .app f a => .app (substClosed j v f) (substClosed j v a)
  | .inj₁ a => .inj₁ (substClosed j v a)
  | .inj₂ a => .inj₂ (substClosed j v a)
  | .lam b => .lam (substClosed (j + 1) v b)
  | .letpair a b => .letpair (substClosed j v a) (substClosed (j + 2) v b)
  | .case a b c => .case (substClosed j v a) (substClosed (j + 1) v b) (substClosed (j + 1) v c)
  | e => e

/-- `(λx. N) V` is a polymorphic let: a let, as `conv` converts one and not a self-application, of
a closed λ that `N` uses more than once. -/
def polyLet? (N V : Expr) : Bool :=
  (match V with | .lam _ => true | _ => false) && idxUses 0 N ≥ 2 && (fvsRaw V 0).isEmpty &&
    !isSwap (.lam N) && (fixBody? (.lam N)).isNone && V != .lam N

/-- The mark of a use of a polymorphic let converted as a code of its own (`polyLets`): the pair
of this `i64` and the let's number, applied to it, which no checked term has. -/
def polyUseMark : UInt64 := 0x504F4C5955534553

/-- The λ `v` at a use of the polymorphic let `i`, marked (`polyUseMark`). -/
def polyUseE (i : Nat) (v : Expr) : Expr :=
  .app (.prim (.lit (.i64 polyUseMark))) (.pair (.prim (.lit (.i32 i.toUInt32))) v)

/-- The term with the polymorphic lets `sel` holds of replaced by their β-reducts, inner lets
first; with `mark`, each use's λ is marked (`polyUseE`). The lets are numbered in pre-order from
the state, whether replaced or not. -/
def polyLets (sel : Nat → Bool) (mark : Bool) : Expr → StateM Nat Expr
  | .app (.lam N) V => do
    let i? ← if polyLet? N V then some <$> modifyGet (fun k => (k, k + 1)) else pure none
    let N' ← polyLets sel mark N
    let V' ← polyLets sel mark V
    match i? with
    | some i => if sel i then return substClosed 0 (if mark then polyUseE i V' else V') N'
                else return .app (.lam N') V'
    | none => return .app (.lam N') V'
  | .pair a b => return .pair (← polyLets sel mark a) (← polyLets sel mark b)
  | .seq a b => return .seq (← polyLets sel mark a) (← polyLets sel mark b)
  | .app a b => return .app (← polyLets sel mark a) (← polyLets sel mark b)
  | .inj₁ a => return .inj₁ (← polyLets sel mark a)
  | .inj₂ a => return .inj₂ (← polyLets sel mark a)
  | .lam b => return .lam (← polyLets sel mark b)
  | .letpair a b => return .letpair (← polyLets sel mark a) (← polyLets sel mark b)
  | .case a b c =>
    return .case (← polyLets sel mark a) (← polyLets sel mark b) (← polyLets sel mark c)
  | e => pure e

/-- The polymorphic lets of a term. -/
def polyLetCount (e : Expr) : Nat := ((polyLets (fun _ => false) false e).run 0).2

def setCode (c : Nat) (code : Code) : CM Unit :=
  modify fun s => { s with codes := s.codes.set! c code }

/-- Convert the subterm `e`, numbered `id` (`Pre`), in the context `ctx`. -/
def conv (ctx : Ctx) (e : Expr) (id : Nat) : CM Tm := do
  -- The numbers of `e`'s parts.
  let k₁ := id + 1
  let k₂ := k₁ + (← sizeAt k₁)
  match e with
  | .var i => do
      let x ← lookup ctx i
      return if x.isSelf then .clos (x - selfBase) [] else .var x
  | .unit => return .unit
  | .loc 0 => return .prim .nullLoc []
  | .loc _ => throw "a location in the source term"
  | .prim p => primValue p
  | .inj₁ e => do
      let a ← fresh
      return .letv a (← conv ctx e k₁) (.inj false a)
  | .inj₂ e => do
      let a ← fresh
      return .letv a (← conv ctx e k₁) (.inj true a)
  | .pair e₁ e₂ => do
      let (cs, c₁, c₂) ← plan2 ctx (← fvsAt k₁ 0) (← fvsAt k₂ 0)
      let a ← fresh; let b ← fresh
      let t₁ ← conv c₁ e₁ k₁
      let t₂ ← conv c₂ e₂ k₂
      return wrapCopies cs (.letv a t₁ (.letv b t₂ (.pair a b)))
  | .seq e₁ e₂ => do
      let (cs, c₁, c₂) ← plan2 ctx (← fvsAt k₁ 0) (← fvsAt k₂ 0)
      let u ← fresh
      let t₁ ← conv c₁ e₁ k₁
      let t₂ ← conv c₂ e₂ k₂
      return wrapCopies cs (.letv u t₁ (.drop u t₂))
  | .letpair e₁ e₂ => do
      let (cs, c₁, c₂) ← plan2 ctx (← fvsAt k₁ 0) (← fvsAt k₂ 2)
      let p ← fresh; let x ← fresh; let y ← fresh
      let t₁ ← conv c₁ e₁ k₁
      let t₂ ← conv ((c₂.push x).push y) e₂ k₂
      let used ← fvsAt k₂ 0
      let unused := (if 1 ∈ used then [] else [x]) ++ (if 0 ∈ used then [] else [y])
      return wrapCopies cs (.letv p t₁ (.letpair x y p (wrapDrops unused t₂)))
  | .case e e₁ e₂ => do
      let k₃ := k₂ + (← sizeAt k₂)
      let f₁ ← fvsAt k₂ 1; let f₂ ← fvsAt k₃ 1
      let (cs, c₀, c₁) ← plan2 ctx (← fvsAt k₁ 0) (f₁ ++ f₂)
      let s ← fresh; let x ← fresh; let y ← fresh
      let t₀ ← conv c₀ e k₁
      let t₁ ← conv (c₁.push x) e₁ k₂
      let t₂ ← conv (c₁.push y) e₂ k₃
      let in₁ : Std.HashSet Nat := f₁.foldl (·.insert ·) {}
      let in₂ : Std.HashSet Nat := f₂.foldl (·.insert ·) {}
      let only₁ ← vars c₁ (f₁.filter (!in₂.contains ·))
      let only₂ ← vars c₁ (f₂.filter (!in₁.contains ·))
      let d₁ := (if 0 ∈ (← fvsAt k₂ 0) then [] else [x]) ++ only₂
      let d₂ := (if 0 ∈ (← fvsAt k₃ 0) then [] else [y]) ++ only₁
      return wrapCopies cs (.letv s t₀ (.case s x (wrapDrops d₁ t₁) y (wrapDrops d₂ t₂)))
  | .app (.prim (.lit (.i64 m))) (.pair (.prim (.lit (.i32 i))) v) => do
      -- A marked use of a polymorphic let (`polyLets`): its λ, and the codes it registers.
      if m != polyUseMark then throw "a literal applied"
      let u := (← get).uses.size
      modify fun s => { s with uses := s.uses.push ⟨i.toNat, s.useStack.head?, #[]⟩,
                               useStack := u :: s.useStack }
      let start := (← get).codes.size
      let t ← conv ctx v (k₂ + 2)
      let s ← get
      let cs := ((List.range (s.codes.size - start)).map (· + start)).filter (some · != s.litCode)
      set { s with uses := s.uses.modify u ({ · with codes := cs.toArray }),
                   useStack := s.useStack.drop 1 }
      return t
  | .app (.prim .alloc) (.pair (.prim (.lit (.i64 m))) v) => do
      -- A scoped cell's `alloc`, marked by `markScoped`.
      let some k := scopedOf? m | throw "an `alloc` of a pair with a literal"
      let av ← fresh
      return .letv av (← conv ctx v (k₂ + 2)) (.prim (.scopedAlloc k) [av])
  | .app (.prim .free) (.pair (.prim (.lit (.i64 m))) l) => do
      -- A scoped cell's `free`, marked by `markScoped`.
      let some k := scopedOf? m | throw "a `free` of a pair with a literal"
      let av ← fresh
      return .letv av (← conv ctx l (k₂ + 2)) (.prim (.scopedFree k) [av])
  | .app (.prim .tab) (.pair (.prim (.lit (.i64 m))) arg) => do
      -- A literal view's `tab`, marked by `markLitViews`: `litTab`.
      if m != litViewMark then throw "a `tab` of a non-length"
      let kArg := (k₂ + 1) + (← sizeAt (k₂ + 1))
      let av ← fresh
      return .letv av (← conv ctx arg kArg) (.prim .litTab [av])
  | .app (.prim .raise) p => do
      -- `raise p` (§19): `p`, then the abortive stop.
      let pv ← fresh
      return .letv pv (← conv ctx p k₂) (.raise pv)
  | .app (.prim .perform) p => do
      -- `perform p` (§19): `p`, then the control operation, which `Capture` lowers.
      let pv ← fresh
      return .letv pv (← conv ctx p k₂) (.perform pv)
  | .app (.prim .ccatch) _ | .app (.app (.prim .cfin) _) _ =>
      throw "a cancel frame (`ccatch`, `cfin`) is a frame of the machine's continuations, not a term of a program"
  | .app (.app (.prim .hnd) (.pair (.prim (.lit (.i32 n))) (.pair _ (.pair hr cls)))) e => do
      -- `hnd (n, (qs, (hr, cls))) e` (§19): the clauses' parts, then the handled body. The parts
      -- are values, so the order is the machine's. The tags `qs` say which continuations own a
      -- cell (§25); the lowering builds `κ` itself (`Capture`), with no cell.
      let kH := k₁ + 2
      let kN := kH + 1
      let kQH := kN + (← sizeAt kN)
      let kQ := kQH + 1
      let kHC := kQ + (← sizeAt kQ)
      let kHr := kHC + 1
      let kCls := kHr + (← sizeAt kHr)
      let (cs, cH, cE) ← plan2 ctx (← fvsAt kHC 0) (← fvsAt k₂ 0)
      let (cs', cHr, cCls) ← plan2 cH (← fvsAt kHr 0) (← fvsAt kCls 0)
      let hv ← fresh; let cv ← fresh
      let tHr ← conv cHr hr kHr
      let tCls ← conv cCls cls kCls
      let tE ← conv cE e k₂
      return wrapCopies cs (wrapCopies cs' (.letv hv tHr (.letv cv tCls (.hnd n hv cv tE))))
  | .app (.app (.prim .hnd) _) _ => throw "a handler whose name is not a literal"
  | .app (.app (.prim .ubind) (.pair sel (.prim (.lit (.i64 mk))))) m => do
      -- `ubind (N, D) M` (§19) with its clauses one code (`markUbinds`): the code, then `M`; the
      -- frame calls it on `inj₁ x` to continue and on `inj₂ ()` to finalise.
      if mk != ubindSelMark then throw "a finaliser frame's clauses"
      let kND := k₁ + 2
      let kSel := kND + 1
      let (cs, cS, cM) ← plan2 ctx (← fvsAt kSel 0) (← fvsAt k₂ 0)
      let cv ← fresh
      let tS ← conv cS sel kSel
      let tM ← conv cM m k₂
      return wrapCopies cs (.letv cv tS (.ubind cv cv tM))
  | .app (.app (.prim .ubind) nd) m => do
      -- `ubind (N, D) M` (§19): the pair of clauses, then `M`.
      let kND := k₁ + 2
      let (cs, cND, cM) ← plan2 ctx (← fvsAt kND 0) (← fvsAt k₂ 0)
      let pv ← fresh; let nn ← fresh; let dd ← fresh
      let tND ← conv cND nd kND
      let tM ← conv cM m k₂
      return wrapCopies cs (.letv pv tND (.letpair nn dd pv (.ubind nn dd tM)))
  | .app (.app (.prim .store) l) v => do
      -- `l` is part 2 of `app (prim store) l`, `v` part 2 of the whole.
      let kl := k₁ + 2
      let (cs, cv, cl) ← plan2 ctx (← fvsAt k₂ 0) (← fvsAt kl 0)
      let vv ← fresh; let lv ← fresh
      let tv ← conv cv v k₂
      let tl ← conv cl l kl
      return wrapCopies cs (.letv vv tv (.letv lv tl (.prim .store [lv, vv])))
  | .app f a => do
      match f with
      | .app sw l =>
        if isSwap sw then
          -- `swap l a`, saturated: `a`, then `l`, as the machine evaluates them.
          let kl := k₁ + 1 + (← sizeAt (k₁ + 1))
          let (cs, cv, cl) ← plan2 ctx (← fvsAt k₂ 0) (← fvsAt kl 0)
          let vv ← fresh; let lv ← fresh
          let tv ← conv cv a k₂
          let tl ← conv cl l kl
          return wrapCopies cs (.letv vv tv (.letv lv tl (.prim .swap [lv, vv])))
      | .lam b =>
        if !isSwap f && (fixBody? f).isNone then
          -- `(λx. b) a`, the erasure's `let`: `a` is bound to `x` and no closure is made.
          let kb := k₁ + 1
          let (cs, ca, cb) ← plan2 ctx (← fvsAt k₂ 0) (← fvsAt kb 1)
          let x ← fresh
          let ta ← conv ca a k₂
          let tb ← conv (cb.push x) b kb
          let tb := if 0 ∈ (← fvsAt kb 0) then tb else .drop x tb
          return wrapCopies cs (.letv x ta tb)
      | _ => pure ()
      match f, Op.ofPrim? (match f with | .prim p => p | _ => .store) with
      | .prim _, some op =>
        let av ← fresh
        return .letv av (← conv ctx a k₂) (.prim op [av])
      | _, _ =>
        let (cs, ca, cf) ← plan2 ctx (← fvsAt k₂ 0) (← fvsAt k₁ 0)
        let av ← fresh; let fv ← fresh
        let ta ← conv ca a k₂
        let tf ← conv cf f k₁
        return wrapCopies cs (.letv av ta (.letv fv tf (.app fv av)))
  | .lam b => do
      if isSwap (.lam b) then return ← swapValue
      if let some bs := litTable? b then return ← litClosure bs
      match b with
      | .app (.var (k + 1)) (.var 0) =>
        -- `λv. y v` of a variable `y` is `y` (η): no closure wraps a closure of its own type.
        return .var (← lookup ctx k)
      | .app (.app (.lam (.app (.lam (.lam B)) (.lam (.app (.app (.var 1) (.var 1)) (.var 0)))))
          _) (.var 0) =>
        if (fixBody? (.lam b)).isSome then
          -- The native fixed point: code `c` is `λx. B[self := clos c []]`; it captures
          -- nothing and calls itself through a closure of its own code, built where `self`
          -- is used. `B` is six parts down from `b`, each the first.
          let kB := k₁ + 6
          let c ← reserve
          let x ← fresh
          let body ← conv (Ctx.ofList [x, selfBase + c]) B kB
          if let (some (reuse, shape), .clos cu xs) := (foldShape? B, body) then
            if let some i := xs.idxOf? x then
              modify fun st => { st with folds := ⟨cu, reuse, shape, i⟩ :: st.folds }
          let body := if 0 ∈ (← fvsAt kB 0) then body else .drop x body
          setCode c ⟨[], x, body⟩
          return .clos c []
      | _ => pure ()
      let fvAll ← fvsAt k₁ 1
      let selfs ← fvAll.filterM fun i => return (← lookup ctx i).isSelf
      let fv := fvAll.filter (· ∉ selfs)
      let xs ← vars ctx fv
      let es ← fv.mapM fun _ => fresh
      let p ← fresh
      -- The body sees the captured variables, and the `self`s, at their indices.
      let inner : Ctx := { depth := ctx.depth }
      let inner := (fv.zip es).foldl (fun c (i, x) => c.set i x) inner
      let inner ← selfs.foldlM (fun c i => return c.set i (← lookup ctx i)) inner
      let body ← conv (inner.push p) b k₁
      let body := if 0 ∈ (← fvsAt k₁ 0) then body else .drop p body
      let c ← register ⟨es, p, body⟩
      return .clos c xs

/-- The term the conversion converts: the polymorphic lets `sel` holds of replaced by their
β-reducts, each use marked when `mark` (`polyLets`), then the literal views and finaliser frames
marked. -/
def prepare (sel : Nat → Bool) (mark : Bool) (e : Expr) : Expr :=
  (markScoped (markUbinds (markLitViews ((polyLets sel mark e).run' 0)))).run' 0

/-- Closure-convert a closed term, the polymorphic lets `sel` holds of replaced by their β-reducts
and, with `mark`, their uses marked; and the marked uses. `convert` (`Backend/Clos/Poly.lean`)
replaces the lets whose uses are at different rows. -/
def convertWith (sel : Nat → Bool) (mark : Bool) (e : Expr) :
    Except String (Prog × Array PolyUse) := do
  let e := prepare sel mark e
  let (t, s) ← (conv {} e 0).run { next := dummy + 1, codes := #[], pre := .of e }
  pure ({ codes := s.codes, main := t, folds := s.folds, data := s.data, litCode := s.litCode },
    s.uses)

/-! ### Externs  `[spec §11]` -/

/-- The host implementation of an extern: a capability cell holding a stream's file
descriptor, or an I/O operation. -/
inductive ExtImpl where
  | cap (fd : Nat)
  /-- The clock's cell, holding the model's time `i64[0]` (SPEC §34). -/
  | clockCell
  | io (k : IOOp)

/-- An operation's closure, as the extern's value: `Λ. λm. op m`, with one `Λ` per lifetime
parameter (each argument is `()`, and is dropped). -/
def ioValue (k : IOOp) : CM Tm := do
  let m ← fresh
  let mut c ← register ⟨[], m, .prim (.io k) [m]⟩
  for _ in [0:k.lifes] do
    let u ← fresh
    c ← register ⟨[], u, .drop u (.clos c [])⟩
  pure (.clos c [])

/-- A word of the program's data for a capability's cell, after the literals' bytes: its
address.  `[spec §35]` -/
def staticWord : CM Nat := do
  let d := (← get).data
  let pad := (8 - d.size % 8) % 8
  modify fun s => { s with data := d ++ Array.replicate (pad + 8) 0 }
  return dataBase + d.size + pad

/-- Take the capabilities back from `main`'s result `(caps, a)`: each cell is freed with its
content, and the result is `a`. -/
def epilogue (r : Var) (n : Nat) : CM Tm := do
  if n == 0 then return .var r
  let caps ← fresh; let a ← fresh
  -- The capability variables, and the destructuring that binds them.
  let rec split : Nat → Var → CM (List Var × (Tm → Tm))
    | 0, _ => pure ([], id)
    | 1, v => pure ([v], id)
    | k + 1, v => do
      let x ← fresh; let rest ← fresh
      let (xs, wrap) ← split k rest
      pure (x :: xs, fun t => .letpair x rest v (wrap t))
  let (xs, wrap) ← split n caps
  let mut body : Tm := .var a
  for x in xs.reverse do
    let c ← fresh
    body := .letv c (.prim .free [x]) (.drop c body)
  return .letpair caps a r (wrap body)

/-- Closure-convert `main` over its externs, given in declaration order: the prologue binds each
extern to its host implementation (a cell holding a capability's file descriptor, a word of the
program's data (`staticWord`, `Op.staticCell`), or an operation's closure), an extern `main`
does not use is dropped, and when there are capabilities
`main`'s result `(caps, a)` gives them back and `a` is the program's value. When `main` returns a
loop (`loops`), its value is the loop, and the taking back is the code `fin`, run on the value
the loop finishes with. The polymorphic lets `sel` holds of are replaced by their β-reducts and,
with `mark`, their uses marked; the marked uses are returned too. `convertMain`
(`Backend/Clos/Poly.lean`) replaces the lets whose uses are at different rows.  `[spec §11]` -/
def convertMainWith (sel : Nat → Bool) (mark : Bool) (exts : List ExtImpl) (loops : Bool)
    (e : Expr) : Except String (Prog × Array PolyUse) := do
  let e := prepare sel mark e
  let ncaps := (exts.filter fun | .cap _ | .clockCell => true | _ => false).length
  let act : CM (Tm × Option Nat) := do
    let xs ← exts.mapM fun _ => fresh
    let ctx := xs.reverse
    let used ← fvsAt 0 0
    let r ← fresh
    let t ← conv (Ctx.ofList ctx) e 0
    let ep ← epilogue r ncaps
    let (main, fin) ← if loops then do
        let c ← register ⟨[], r, ep⟩
        pure (t, some c)
      else pure (.letv r t ep, none)
    let mut body : Tm := main
    for (x, i) in ctx.zipIdx do
      if i ∉ used then body := .drop x body
    for (x, ext) in (xs.zip exts).reverse do
      match ext with
      | .cap fd =>
        let l ← fresh
        let a ← staticWord
        body := .letv l (.lit (.i32 fd.toUInt32)) (.letv x (.prim (.staticCell a) [l]) body)
      | .clockCell =>
        let l ← fresh
        body := .letv l (.lit (.i64 0)) (.letv x (.prim (.staticCell (← staticWord)) [l]) body)
      | .io k => body := .letv x (← ioValue k) body
    return (body, fin)
  let ((t, fin), s) ← act.run { next := dummy + 1, codes := #[], pre := .of e }
  pure ({ codes := s.codes, main := t, fin, folds := s.folds, data := s.data,
          litCode := s.litCode }, s.uses)

end Backend.Clos

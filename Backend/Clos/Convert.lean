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

structure CState where
  next : Nat
  codes : Array Code
  folds : List FoldCode := []

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

def lookup (ctx : List Var) (i : Nat) : CM Var :=
  match ctx[i]? with
  | some x => if x == dummy then throw s!"index {i} is not captured" else pure x
  | none => throw s!"unbound index {i}"

def wrapCopies (cs : List (Var × Var)) (t : Tm) : Tm :=
  cs.foldr (fun (x, x') t => .copy x x' t) t

def wrapDrops (xs : List Var) (t : Tm) : Tm :=
  xs.foldr (fun x t => .drop x t) t

/-- Copies for two sequential parts using the indices `f₁` and `f₂`: every index in both is
    copied for the first part. The contexts the two parts are converted in. -/
def plan2 (ctx : List Var) (f₁ f₂ : List Nat) : CM (List (Var × Var) × List Var × List Var) := do
  let shared := f₁.filter (· ∈ f₂)
  let mut cs : List (Var × Var) := []
  let mut ctx₁ := ctx
  for i in shared do
    let x ← lookup ctx i
    if x.isSelf then continue
    let x' ← fresh
    cs := cs ++ [(x, x')]
    ctx₁ := ctx₁.set i x'
  return (cs, ctx₁, ctx)

/-- The variables of the indices `is` in `ctx`, but for the fixed points' `self`s. -/
def vars (ctx : List Var) (is : List Nat) : CM (List Var) :=
  return (← is.mapM (lookup ctx)).filter (!·.isSelf)

def Op.ofPrim? : Prim → Option Op
  | .alloc => some .alloc
  | .free => some .free
  | .load => some .load
  | .host op => some (.host op)
  | .tab => some .tab
  | .idx => some .idx
  | .drop => some .drop
  | .count => some .count
  | .store => none
  | .lit _ => none

/-- A primitive as a value: η-expanded closure code. -/
def primValue : Prim → CM Tm
  | .lit c => pure (.lit c)
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

def setCode (c : Nat) (code : Code) : CM Unit :=
  modify fun s => { s with codes := s.codes.set! c code }

def conv (ctx : List Var) : Expr → CM Tm
  | .var i => do
      let x ← lookup ctx i
      return if x.isSelf then .clos (x - selfBase) [] else .var x
  | .unit => return .unit
  | .loc _ => throw "a location in the source term"
  | .prim p => primValue p
  | .inj₁ e => do
      let a ← fresh
      return .letv a (← conv ctx e) (.inj false a)
  | .inj₂ e => do
      let a ← fresh
      return .letv a (← conv ctx e) (.inj true a)
  | .pair e₁ e₂ => do
      let (cs, c₁, c₂) ← plan2 ctx (fvs e₁ 0) (fvs e₂ 0)
      let a ← fresh; let b ← fresh
      let t₁ ← conv c₁ e₁
      let t₂ ← conv c₂ e₂
      return wrapCopies cs (.letv a t₁ (.letv b t₂ (.pair a b)))
  | .seq e₁ e₂ => do
      let (cs, c₁, c₂) ← plan2 ctx (fvs e₁ 0) (fvs e₂ 0)
      let u ← fresh
      let t₁ ← conv c₁ e₁
      let t₂ ← conv c₂ e₂
      return wrapCopies cs (.letv u t₁ (.drop u t₂))
  | .letpair e₁ e₂ => do
      let (cs, c₁, c₂) ← plan2 ctx (fvs e₁ 0) (fvs e₂ 2)
      let p ← fresh; let x ← fresh; let y ← fresh
      let t₁ ← conv c₁ e₁
      let t₂ ← conv (y :: x :: c₂) e₂
      let used := fvs e₂ 0
      let unused := (if 1 ∈ used then [] else [x]) ++ (if 0 ∈ used then [] else [y])
      return wrapCopies cs (.letv p t₁ (.letpair x y p (wrapDrops unused t₂)))
  | .case e e₁ e₂ => do
      let f₁ := fvs e₁ 1; let f₂ := fvs e₂ 1
      let (cs, c₀, c₁) ← plan2 ctx (fvs e 0) (f₁ ++ f₂)
      let s ← fresh; let x ← fresh; let y ← fresh
      let t₀ ← conv c₀ e
      let t₁ ← conv (x :: c₁) e₁
      let t₂ ← conv (y :: c₁) e₂
      let only₁ ← vars c₁ (f₁.filter (· ∉ f₂))
      let only₂ ← vars c₁ (f₂.filter (· ∉ f₁))
      let d₁ := (if 0 ∈ fvs e₁ 0 then [] else [x]) ++ only₂
      let d₂ := (if 0 ∈ fvs e₂ 0 then [] else [y]) ++ only₁
      return wrapCopies cs (.letv s t₀ (.case s x (wrapDrops d₁ t₁) y (wrapDrops d₂ t₂)))
  | .app (.app (.prim .store) l) v => do
      let (cs, cv, cl) ← plan2 ctx (fvs v 0) (fvs l 0)
      let vv ← fresh; let lv ← fresh
      let tv ← conv cv v
      let tl ← conv cl l
      return wrapCopies cs (.letv vv tv (.letv lv tl (.prim .store [lv, vv])))
  | .app f a => do
      match f with
      | .app sw l =>
        if isSwap sw then
          -- `swap l a`, saturated: `a`, then `l`, as the machine evaluates them.
          let (cs, cv, cl) ← plan2 ctx (fvs a 0) (fvs l 0)
          let vv ← fresh; let lv ← fresh
          let tv ← conv cv a
          let tl ← conv cl l
          return wrapCopies cs (.letv vv tv (.letv lv tl (.prim .swap [lv, vv])))
      | .lam b =>
        if !isSwap f && (fixBody? f).isNone then
          -- `(λx. b) a`, the erasure's `let`: `a` is bound to `x` and no closure is made.
          let (cs, ca, cb) ← plan2 ctx (fvs a 0) (fvs b 1)
          let x ← fresh
          let ta ← conv ca a
          let tb ← conv (x :: cb) b
          let tb := if 0 ∈ fvs b 0 then tb else .drop x tb
          return wrapCopies cs (.letv x ta tb)
      | _ => pure ()
      match f, Op.ofPrim? (match f with | .prim p => p | _ => .store) with
      | .prim _, some op =>
        let av ← fresh
        return .letv av (← conv ctx a) (.prim op [av])
      | _, _ =>
        let (cs, ca, cf) ← plan2 ctx (fvs a 0) (fvs f 0)
        let av ← fresh; let fv ← fresh
        let ta ← conv ca a
        let tf ← conv cf f
        return wrapCopies cs (.letv av ta (.letv fv tf (.app fv av)))
  | .lam b => do
      if isSwap (.lam b) then return ← swapValue
      match b with
      | .app (.var (k + 1)) (.var 0) =>
        -- `λv. y v` of a variable `y` is `y` (η): no closure wraps a closure of its own type.
        return .var (← lookup ctx k)
      | .app (.app (.lam (.app (.lam (.lam B)) (.lam (.app (.app (.var 1) (.var 1)) (.var 0)))))
          _) (.var 0) =>
        if (fixBody? (.lam b)).isSome then
          -- The native fixed point: code `c` is `λx. B[self := clos c []]`; it captures
          -- nothing and calls itself through a closure of its own code, built where `self`
          -- is used.
          let c ← reserve
          let x ← fresh
          let body ← conv [x, selfBase + c] B
          if let (some (reuse, shape), .clos cu xs) := (foldShape? B, body) then
            if let some i := xs.idxOf? x then
              modify fun st => { st with folds := ⟨cu, reuse, shape, i⟩ :: st.folds }
          let body := if 0 ∈ fvs B 0 then body else .drop x body
          setCode c ⟨[], x, body⟩
          return .clos c []
      | _ => pure ()
      let fvAll := fvs b 1
      let selfs ← fvAll.filterM fun i => return (← lookup ctx i).isSelf
      let fv := fvAll.filter (· ∉ selfs)
      let xs ← vars ctx fv
      let es ← fv.mapM fun _ => fresh
      let p ← fresh
      let inner := (List.range ctx.length).map fun i =>
        match fv.idxOf? i with
        | some k => es.getD k dummy
        | none => if i ∈ selfs then ctx.getD i dummy else dummy
      let body ← conv (p :: inner) b
      let body := if 0 ∈ fvs b 0 then body else .drop p body
      let c ← register ⟨es, p, body⟩
      return .clos c xs

/-- Closure-convert a closed term. -/
def convert (e : Expr) : Except String Prog := do
  let (t, s) ← (conv [] e).run ⟨dummy + 1, #[], []⟩
  pure { codes := s.codes, main := t, folds := s.folds }

/-! ### Externs  `[spec §11]` -/

/-- The host implementation of an extern: a capability cell holding a stream's file
descriptor, or an I/O operation. -/
inductive ExtImpl where
  | cap (fd : Nat)
  | io (k : IOOp)

/-- An operation's closure, as the extern's value: `Λ. λm. op m` (the lifetime argument is
`()`, and is dropped). -/
def ioValue (k : IOOp) : CM Tm := do
  let u ← fresh; let m ← fresh
  let c₂ ← register ⟨[], m, .prim (.io k) [m]⟩
  let c₁ ← register ⟨[], u, .drop u (.clos c₂ [])⟩
  pure (.clos c₁ [])

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
extern to its host implementation (a fresh cell holding a capability's file descriptor, or an
operation's closure), an extern `main` does not use is dropped, and when there are capabilities
`main`'s result `(caps, a)` gives them back and `a` is the program's value. When `main` returns a
loop (`loops`), its value is the loop, and the taking back is the code `fin`, run on the value
the loop finishes with.  `[spec §11]` -/
def convertMain (exts : List ExtImpl) (loops : Bool) (e : Expr) : Except String Prog := do
  let ncaps := (exts.filter fun | .cap _ => true | _ => false).length
  let act : CM (Tm × Option Nat) := do
    let xs ← exts.mapM fun _ => fresh
    let ctx := xs.reverse
    let used := fvs e 0
    let r ← fresh
    let t ← conv ctx e
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
        body := .letv l (.lit (.i32 fd.toUInt32)) (.letv x (.prim .alloc [l]) body)
      | .io k => body := .letv x (← ioValue k) body
    return (body, fin)
  let ((t, fin), s) ← act.run ⟨dummy + 1, #[], []⟩
  pure { codes := s.codes, main := t, fin, folds := s.folds }

end Backend.Clos

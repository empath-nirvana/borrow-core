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
- **Closures.** `λ` captures its free variables, in index order, into an environment. A
  primitive in function position with its arguments present becomes `prim`; a primitive used
  as a value is η-expanded into closure code (`store` into two).
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

abbrev CM := StateT CState (Except String)

/-- The variable standing for an index a closure body cannot refer to. -/
def dummy : Var := 0

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
    let x' ← fresh
    cs := cs ++ [(x, x')]
    ctx₁ := ctx₁.set i x'
  return (cs, ctx₁, ctx)

/-- The variables of the indices `is` in `ctx`. -/
def vars (ctx : List Var) (is : List Nat) : CM (List Var) := is.mapM (lookup ctx)

def Op.ofPrim? : Prim → Option Op
  | .alloc => some .alloc
  | .free => some .free
  | .load => some .load
  | .host op => some (.host op)
  | .tab => some .tab
  | .idx => some .idx
  | .drop => some .drop
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

def conv (ctx : List Var) : Expr → CM Tm
  | .var i => return .var (← lookup ctx i)
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
      let fv := fvs b 1
      let xs ← vars ctx fv
      let es ← fv.mapM fun _ => fresh
      let p ← fresh
      let inner := (List.range ctx.length).map fun i =>
        match fv.idxOf? i with
        | some k => es.getD k dummy
        | none => dummy
      let body ← conv (p :: inner) b
      let body := if 0 ∈ fvs b 0 then body else .drop p body
      let c ← register ⟨es, p, body⟩
      return .clos c xs

/-- Closure-convert a closed term. -/
def convert (e : Expr) : Except String Prog := do
  let (t, s) ← (conv [] e).run ⟨dummy + 1, #[]⟩
  pure { codes := s.codes, main := t }

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
  let ((t, fin), s) ← act.run ⟨dummy + 1, #[]⟩
  pure { codes := s.codes, main := t, fin }

end Backend.Clos

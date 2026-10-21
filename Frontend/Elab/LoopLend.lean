import Frontend.Elab.Meta
import Frontend.Check.Steps

/-!
# Frontend — Elab — borrow scopes and loops  `[spec §14]`

A borrow block's body is one computation: `withbor`'s callback returns before the block ends. A
loop is at the row `div` (SPEC §14): each of its back edges ticks, and `tick` is a control
operation that resumes, so a borrow block whose body loops holds its lend across a tick. That is
a lend held by a suspension whose continuation is resumed in its scope: the block is elaborated as
written, its borrow in the unwinding form at the graded row `div call` (`Frontend/Sugar.lean`,
`blockLoops`), which the kernel's rule for a lend at a row (`Row.Lend`, SPEC §48) checks. The
elaborator does not lend again per step.

This module recognises such a block, and holds two forms around borrow scopes:

* `let r = &x; S` (or `&mut x`) is the borrow block `borrow imm x { r -> S }` over the rest of
  the body (`lendLet`).
* The error for a block whose result has the block's lifetime (`escapeError`).
-/

namespace Frontend.Elab.LoopLend
open Frontend.Check (mentionsV mentionsC)

/-- A borrow block as the parser gives it: `borrow k P { 'x, b -> S }`. -/
structure Block where
  sp : Span
  ksp : Span
  k : BorrowKind
  x : String
  P : Val
  tsp : Span
  lsp : Span
  b : Ident
  S : Comp

/-- A borrow block (not `modify`). -/
def Block.of? : Val → Option Block
  | .app sp (.app _ (.sugar ksp (.borrow k x)) P) (.thunkv tsp (.lam lsp b _ S)) =>
    if k == .modify then none else some ⟨sp, ksp, k, x, P, tsp, lsp, b, S⟩
  | _ => none

def fuel : Nat := 1 <<< 16

/-- A head of a binding that makes the body loop: a call of a div function, or the step of a
counted loop at the row `div` (`VSugar.rowStep`). -/
def isLoopHead (divCall : Val → Bool) : Comp → Bool
  | .ret _ (.app _ (.sugar _ (.rowStep ..)) _) => true
  | .ret _ V => divCall V
  | _ => false

/-- A `for x in V { M }; N` over a bounded source, elaborated to a counted loop (SPEC §16, the
total `for`; `forData` in `Frontend/Sugar.lean`). Unless its body loops, it is one computation,
not a loop: a borrow block around it keeps its borrow open for the whole loop. -/
abbrev Finite := Val → Comp → Comp → Bool

/-- A loop is total by `fin`: only a `for` can be; a `while` or a `loop` never is. -/
def _root_.Frontend.LoopSrc.fin (src : LoopSrc) (fin : Finite) (V : Val) (M N : Comp) : Bool :=
  match src with
  | .each _ => fin V M N
  | _ => false

/-- A computation loops on its spine: a `for` that is not total, a counted `for` whose body
loops, or a call of a div function in the head of a binding or at a terminal. -/
def loopsOnSpine (divCall : Val → Bool) (fin : Finite) : Nat → Comp → Bool
  | 0, _ => false
  | n + 1, .bind _ _ _ M N _ => isLoopHead divCall M || loopsOnSpine divCall fin n N
  | n + 1, .letUnit _ _ M | n + 1, .letPair _ _ _ _ M => loopsOnSpine divCall fin n M
  | n + 1, .case _ _ _ M _ N => loopsOnSpine divCall fin n M || loopsOnSpine divCall fin n N
  | n + 1, .loop _ _ src V M N =>
    !src.fin fin V M N || loopsOnSpine divCall fin n M || loopsOnSpine divCall fin n N
  | _ + 1, T => isLoopHead divCall T

/-- The error for a borrow block whose result has the block's lifetime `'x` in its type `T`. -/
def escapeError (sp : Span) (x T : String) : Error :=
  ⟨sp, s!"this borrow block's result has type `{T}`, which has the block's lifetime `'{x}`: " ++
    s!"nothing borrowed at `'{x}` outlives the block (SPEC §14)"⟩

/-- `let r = &x; S` (or `&mut x`), with `x` a name: the borrow block `borrow imm x { r -> S }`
(`borrow mut`) over the rest of the body, after which `x` is rebound. The place may not be used
in `S`, where it is lent. `none` when the binding is not such a lend. -/
def lendLet (sp : Span) (r : Ident) (A : Option VTy) (M N : Comp) : Except Error (Option Comp) := do
  let .ret _ (.lend lsp x m) := M | return none
  -- A name the parser generated holds a lend it passes on (`f!(&mut c)`), not a `let r = &x`.
  if r.name.startsWith "io_" then return none
  if A.isSome then throw ⟨sp, s!"`let {r.name} = &{x.name}` takes its type from `{x.name}`: " ++
    "write it without an annotation"⟩
  if mentionsC x.name N then
    throw ⟨lsp, s!"`{x.name}` is lent to `{r.name}` for the rest of the block, so it cannot be " ++
      s!"used after `let {r.name} = {if m == .mut then "&mut " else "&"}{x.name}`"⟩
  let k : BorrowKind := if m == .mut then .mut else .imm
  let l := s!"io_ll{lsp.start.line}_{lsp.start.col}"
  let B := Val.app lsp (.app lsp (.sugar lsp (.borrow k l)) (.var x.span x.name))
    (.thunkv lsp (.lam lsp r (.name lsp "_") N))
  let v := s!"io_lv{lsp.start.line}_{lsp.start.col}"
  let res := s!"io_lr{lsp.start.line}_{lsp.start.col}"
  pure (some (.bind sp ⟨v, sp⟩ none (.ret sp B)
    (.letPair sp x ⟨res, sp⟩ (.var sp v) (.ret sp (.var sp res))) false))

/-- A call of a div function: its callee is at a row that holds `Div`, or its result is a loop,
with or without a lifetime binder. -/
def divCallIn (c : TCx) : Val → Bool
  | .app _ f _ => match c.tyV f with
    | some (.bang (.thunk (.all _ _ (.ret F)))) | some (.thunk (.all _ _ (.ret F))) =>
      (loopFnOf F).isSome || (divFnOf F).isSome
    | some F => (loopFnOf F).isSome || (divFnOf F).isSome
    | none => false
  | _ => false

/-- The context a block's body is read in, where the block's borrow is bound: on an owned array
it is a view, and a `for` over it a counted loop (SPEC §16). -/
def Block.cx (B : Block) (c : TCx) : TCx :=
  match c.tyV B.P, c.elabL (.dom B.lsp) with
  | some T, some dom =>
    let c₁ := c.pushLife B.x dom
    match c₁.E.lenv.lookup B.x with
    | some v =>
      let Tb : Option Frontend.Check.CVTy := match B.k, T with
        | .imm, .fam (.ref A) => some (.fam (.imm (.var v) A))
        | .mut, .fam (.ref A) => some (.fam (.mut (.var v) A))
        | .imm, .ref A => some (.imm (.var v) A)
        | .mut, .ref A => some (.mut (.var v) A)
        | _, _ => none
      c₁.push B.b.name Tb
    | none => c
  | _, _ => c

/-- A borrow block whose body loops on its spine: its lend is held across the loop's ticks. -/
def blockLoops (c : TCx) (fin' : TCx → Finite) (V : Val) : Bool :=
  match Block.of? V with
  | some B => loopsOnSpine (divCallIn c) (fin' (B.cx c)) fuel B.S
  | none => false

/-- The binding `x <- M; N` of a body, rewritten when `N` follows a `let r = &x`. -/
def hook (sp : Span) (x : Ident) (A : Option VTy) (M N : Comp) : Except Error (Option Comp) :=
  lendLet sp x A M N

end Frontend.Elab.LoopLend

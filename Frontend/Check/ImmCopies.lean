import Frontend.Check.Steps

/-!
# Frontend — Check — implicit copies of `imm` borrows  `[spec §66]`

An `imm` borrow is duplicable: the kernel's constant `copy[@a, A] : imm @a A ⊸ imm @a A ⊗ imm @a A`
makes two of one, at no run-time cost (a pointer). It is not persistent (SPEC §10), so a variable
of type `imm @a A` used by two parts of a node whose context the checker splits is refused unless
the program writes the copy. This module writes it, as SPEC §12 writes destructors: the program the
checker returns is an ordinary core term, the copy is a `copy` application, and the kernel checks
it like any other.

**The pieces of a node.** The checker splits a node's context among its *pieces* (`Fam.split`,
`overlapOK`): `x <- M; N`'s `M` and `N`; `M x`'s `M` and `x`; `let () = V; M`'s and
`let (x, y) = V; M`'s value and body; `case V {…}`'s scrutinee and its arms, which share one
context (`Fam.merge`) and so are one piece; `x <- M unwind (D); N`'s `M` and its continuation
with its finaliser (one piece). A value splits at `(V, W)` and `V W` and passes its context through
every other form with one operand, so the pieces of a node's value are the leaves of that tree
(`walkV`). A node of any other form has no pieces here: `<M, N>` shares its context, a binder's
body is checked at the binder's own node, and a handler or a relaxed lend is left as written.

**Where a copy goes.** At a computation node, for each variable `x` in scope whose slot has type
`imm @a A`, when two or more pieces mention `x` free, every piece but the last mentioning it gets
a copy of its own: `let (x₁, x) = copy[@a, A](x); …` before the node, with `x` renamed to `x₁`
in that piece (`insertCopies`). The node is then checked as written. Each new binder is owed to
its scope (SPEC §12): a copy a path does not use is dropped by `forget_imm`, at no run-time cost.

The names `x#d.i` the copies get carry `#`, which no identifier of the source has, so they capture
nothing; `d` is the depth of the context, so no two in scope at once coincide. A message names
the variable the copy is of (`Env.slotName`).

**What is not copied.** A view (`array_imm`, `view`) and a tuple holding a borrow are not `imm`
borrows; they are SPEC §66's *Open* (E2 of #58).
-/

namespace Frontend.Check
open BoCa.Fig16.LogRel.Core.Check

/-! ### Renaming a free variable -/

mutual
/-- `V` with the free occurrences of `x` named `y`, `y` fresh. -/
def renV (x y : String) : Val → Val
  | .var sp z => .var sp (if z == x then y else z)
  | .clone sp z => .clone sp (if z == x then y else z)
  | .copyImm sp z => .copyImm sp (if z == x then y else z)
  | .lend sp z m => .lend sp (if z.name == x then { z with name := y } else z) m
  | .pair sp V W => .pair sp (renV x y V) (renV x y W)
  | .app sp V W => .app sp (renV x y V) (renV x y W)
  | .inl sp V => .inl sp (renV x y V)
  | .inr sp V => .inr sp (renV x y V)
  | .thunk sp M => .thunk sp (renC x y M)
  | .thunkv sp M => .thunkv sp (renC x y M)
  | .bangThunk sp M => .bangThunk sp (renC x y M)
  | .bangThunkv sp M => .bangThunkv sp (renC x y M)
  | .unbang sp V => .unbang sp (renV x y V)
  | .boxed sp a V => .boxed sp a (renV x y V)
  | .unbox sp V => .unbox sp (renV x y V)
  | .sub sp V a => .sub sp (renV x y V) a
  | .roll sp V => .roll sp (renV x y V)
  | .unroll sp V => .unroll sp (renV x y V)
  | .run sp M => .run sp (renC x y M)
  | .inst sp V a => .inst sp (renV x y V) a
  | .ascribe sp V A => .ascribe sp (renV x y V) A
  | .shorten sp m σ a V => .shorten sp m σ a (renV x y V)
  | .mark sp k V => .mark sp k (renV x y V)
  | .reify sp B R r V => .reify sp B R r (renV x y V)
  | V@(.defApp ..) | V@(.unit _) | V@(.const ..) | V@(.sugar ..) => V

/-- `M` with the free occurrences of `x` named `y`, `y` fresh. -/
def renC (x y : String) : Comp → Comp
  | .ret sp V => .ret sp (renV x y V)
  | .bind sp z A M N l => .bind sp z A (renC x y M) (if z.name == x then N else renC x y N) l
  | .force sp z => .force sp (if z.name == x then { z with name := y } else z)
  | .lam sp z A M => .lam sp z A (if z.name == x then M else renC x y M)
  | .app sp M z => .app sp (renC x y M) (if z.name == x then { z with name := y } else z)
  | .with_ sp M N => .with_ sp (renC x y M) (renC x y N)
  | .proj sp i M => .proj sp i (renC x y M)
  | .top sp => .top sp
  | .letUnit sp V M => .letUnit sp (renV x y V) (renC x y M)
  | .letPair sp z w V M =>
    .letPair sp z w (renV x y V) (if z.name == x || w.name == x then M else renC x y M)
  | .case sp V z M w N =>
    .case sp (renV x y V) z (if z.name == x then M else renC x y M) w
      (if w.name == x then N else renC x y N)
  | .absurd sp V => .absurd sp (renV x y V)
  | .lamL sp z b M => .lamL sp z b (renC x y M)
  | .inst sp M a => .inst sp (renC x y M) a
  | .nuIn sp M => .nuIn sp (renC x y M)
  | .nuOut sp M => .nuOut sp (renC x y M)
  | .ascribe sp M C => .ascribe sp (renC x y M) C
  | .loop sp ℓ src V M N =>
    .loop sp ℓ src (renV x y V) (if src.bound.contains x then M else renC x y M) (renC x y N)
  | .perform sp k i V => .perform sp k i (renV x y V)
  | .abort sp k i V => .abort sp k i (renV x y V)
  | .handle sp k f st hr hc M => .handle sp k f st (renV x y hr) (renV x y hc) (renC x y M)
  | .unwind sp z A M D N =>
    .unwind sp z A (renC x y M) (renC x y D) (if z.name == x then N else renC x y N)
  | .withbor2r sp z b A B r p m M =>
    .withbor2r sp z b A B r (if p.name == x then { p with name := y } else p) m
      (if m.name == x then M else renC x y M)
end

/-! ### The pieces of a node -/

/-- A renaming plan: in piece `i`, each `(x, y)` names `x` `y`. -/
abbrev Plan := Nat → List (String × String)

/-- The walk over a node's pieces: each piece's mention test, in order. -/
abbrev PM := StateM (Array (String → Bool))

/-- A piece: its mention test recorded, and the plan's renaming applied to it. Its binders `bs`
are the node's, bound in it. -/
def pieceC (P : Plan) (bs : List String) (M : Comp) : PM Comp := do
  let i := (← get).size
  modify (·.push fun z => !bs.contains z && mentionsC z M)
  pure ((P i).foldl (fun M (x, y) => if bs.contains x then M else renC x y M) M)

def pieceV (P : Plan) (V : Val) : PM Val := do
  let i := (← get).size
  modify (·.push fun z => mentionsV z V)
  pure ((P i).foldl (fun V (x, y) => renV x y V) V)

def pieceId (P : Plan) (z : Ident) : PM Ident := do
  let i := (← get).size
  modify (·.push fun w => w == z.name)
  pure ((P i).foldl (fun z (x, y) => if z.name == x then { z with name := y } else z) z)

/-- The leaves of a value, each a piece: a value splits its context at `(V, W)` and `V W`. -/
def walkV (P : Plan) : Val → PM Val
  | .pair sp V W => do pure (.pair sp (← walkV P V) (← walkV P W))
  | .app sp V W => do pure (.app sp (← walkV P V) (← walkV P W))
  | .inl sp V => do pure (.inl sp (← walkV P V))
  | .inr sp V => do pure (.inr sp (← walkV P V))
  | .unbang sp V => do pure (.unbang sp (← walkV P V))
  | .boxed sp a V => do pure (.boxed sp a (← walkV P V))
  | .unbox sp V => do pure (.unbox sp (← walkV P V))
  | .sub sp V a => do pure (.sub sp (← walkV P V) a)
  | .roll sp V => do pure (.roll sp (← walkV P V))
  | .unroll sp V => do pure (.unroll sp (← walkV P V))
  | .inst sp V a => do pure (.inst sp (← walkV P V) a)
  | .ascribe sp V A => do pure (.ascribe sp (← walkV P V) A)
  | .shorten sp m σ a V => do pure (.shorten sp m σ a (← walkV P V))
  | .mark sp k V => do pure (.mark sp k (← walkV P V))
  | V => pieceV P V

/-- The pieces of a computation node, at its top. -/
def walkC (P : Plan) : Comp → PM Comp
  | .ret sp V => do pure (.ret sp (← walkV P V))
  | .bind sp z A M N l => do
    let M ← pieceC P [] M
    pure (.bind sp z A M (← pieceC P [z.name] N) l)
  | .app sp M z => do
    let M ← pieceC P [] M
    pure (.app sp M (← pieceId P z))
  | .letUnit sp V M => do
    let V ← walkV P V
    pure (.letUnit sp V (← pieceC P [] M))
  | .letPair sp z w V M => do
    let V ← walkV P V
    pure (.letPair sp z w V (← pieceC P [z.name, w.name] M))
  | .case sp V z M w N => do
    let V ← walkV P V
    -- The arms share one context: one piece.
    let i := (← get).size
    modify (·.push fun u => (u != z.name && mentionsC u M) || (u != w.name && mentionsC u N))
    let ren := fun (bs : String) (K : Comp) =>
      (P i).foldl (fun K (x, y) => if x == bs then K else renC x y K) K
    pure (.case sp V z (ren z.name M) w (ren w.name N))
  | .absurd sp V => do pure (.absurd sp (← walkV P V))
  | .perform sp k i V => do pure (.perform sp k i (← walkV P V))
  | .abort sp k i V => do pure (.abort sp k i (← walkV P V))
  | .unwind sp z A M D N => do
    let M ← pieceC P [] M
    -- The continuation and the finaliser: one piece.
    let i := (← get).size
    modify (·.push fun u => mentionsC u D || (u != z.name && mentionsC u N))
    let D := (P i).foldl (fun K (x, y) => renC x y K) D
    let N := (P i).foldl (fun K (x, y) => if x == z.name then K else renC x y K) N
    pure (.unwind sp z A M D N)
  | m => pure m

/-! ### Insertion -/

/-- The variables in scope whose slot has type `imm @a A`, each once, by name. -/
def immVars (E : Env) (T : List CVTy) : List String :=
  (List.range E.vars.length).filterMap fun i =>
    match E.vars[i]?, (T[i]? : Option CVTy) with
    | some (some x), some (.imm _ _) => if lookupVar x E.vars == some i then some x else none
    | _, _ => none

/-- The node `m` with the copies its pieces need written before it, or `none` when it needs none
(SPEC §66). -/
def insertCopies (E : Env) (T : List CVTy) (m : Comp) : Option Comp :=
  let xs := immVars E T
  if xs.isEmpty then none else
  let pieces := ((walkC (fun _ => []) m).run #[]).2
  let d := E.vars.length
  -- `(i, x, y)`: in piece `i`, `x` is named `y`.
  let plan : List (Nat × String × String) := xs.flatMap fun x =>
    let ms := (List.range pieces.size).filter fun i => (pieces[i]?.map (· x)).getD false
    (ms.dropLast).map fun i => (i, x, s!"{x}#{d}.{i}")
  if plan.isEmpty then none else
  let P : Plan := fun i => (plan.filter (·.1 == i)).map (·.2)
  let m' := ((walkC P m).run #[]).1
  let sp := m.span
  some (plan.foldr (fun (_, x, y) acc =>
    .letPair sp ⟨y, sp⟩ ⟨x, sp⟩ (.copyImm sp x) acc) m')

end Frontend.Check

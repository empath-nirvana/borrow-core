import Frontend.Syntax
/-!
# Frontend — what the respelling records during a parse

`bcc respell` (SPEC §82) rewrites a program written in today's spelling into the new one. It is
driven by the parser of today's spelling: while it reads a program the parser records, for each
construct whose spelling changes, the indices of the tokens the rewrite needs (`Ev`). The parse
itself never reads them, and nothing is recorded unless `St.on` is set, which only `bcc respell`
does (`Frontend/Respell.lean`). A token index is a position in the parser's token array. A range
`a b` is the tokens `a` up to, not including, `b`.  `[spec §82]`
-/

namespace Frontend.Respell

/-- One construct the respelling rewrites, as the parser read it.  `[spec §82]` -/
inductive Ev where
  /-- `include m` (D7). -/
  | include (i : Nat)
  /-- A `fn` header and body (D1–D3): its `->`, the `with` of a written row (and the row's end),
  its `=`, and the end of its body. -/
  | fnHead (arrow : Nat) (withTok : Option Nat) (rowEnd : Nat) (eq : Nat) (bodyEnd : Nat)
  /-- `main -> T = S` (D6). -/
  | mainHead (mainTok : Nat) (arrow : Nat) (eq : Nat) (bodyEnd : Nat)
  /-- `poly f[T](…) -> R` (D13): its `->`. -/
  | polyFam (arrow : Nat)
  /-- `poly f at T = S` (D13): its `=` and the end of its body. -/
  | polyAt (eq : Nat) (bodyEnd : Nat)
  /-- An operation of an `effect` (D14, D15, L9): its `fn`, its `->`, and its `)`. -/
  | opDecl (fnTok : Option Nat) (arrow : Option Nat) (rparen : Nat)
  /-- A `;` between the operations of an `effect` or the clauses of a handler. -/
  | declSep (i : Nat)
  /-- A handler's lent state `&mut s: S` (D18): the `&`. -/
  | hLent (amp : Nat)
  /-- A control handler's `, A -> R` (D16): the range of `A`. -/
  | hSig (a b : Nat)
  /-- A handler's written row `with E₂, …` (D16): the `with` and the row's end. -/
  | hRow (withTok : Nat) (rowEnd : Nat)
  /-- The `=` before a handler's clauses (D16). -/
  | hEq (eq : Nat)
  /-- A handler clause `op(x) = M` (D16): its `=`, and its body's range. -/
  | clause (eq : Nat) (a b : Nat)
  /-- A `fn`'s lifetime parameters `<…>` (P1–P3): their range, empty when it has none. -/
  | fnLives (a b : Nat)
  /-- A parameter of a `fn`, a `poly` family or an operation (P1–P5): the name's token, the end of
  its type, and the type. -/
  | param (name : Nat) (tyEnd : Nat) (ty : VTy)
  /-- A parameter of a handler (P4, P5): as `param`. -/
  | hParam (name : Nat) (tyEnd : Nat) (ty : VTy)
  /-- The parameters of the `fn` or `poly` family named `f`, by their types (P8: what a call lends
  to). -/
  | sig (f : String) (ps : List VTy)
  /-- An arrow type `A => B` (T1, T2): the start of `A` and the `=>`. -/
  | arrow (a : Nat) (i : Nat)
  /-- A function type with a row `(A => B with E, …)` (T1): the `with` and the closing `)`. -/
  | rowed (withTok : Nat) (close : Nat)
  /-- A `;` that sequences statements of a surface body. -/
  | seq (i : Nat)
  /-- A statement of a surface body: its range, `;` not included. -/
  | stmt (a b : Nat)
  /-- `x <- M` or `x : A <- M` in a surface body (E2): the name's token, the `<-`, and whether it
  assigns a `let mut` variable (R2) rather than binding a name. -/
  | bind (x : Nat) (arrow : Nat) (assigns : Bool)
  /-- A `return V` of a surface body that is a binding's head or the body's last statement
  (E2, E3): its `return`. -/
  | ret (i : Nat)
  /-- `let mut` (step 1's `var`): the `let`. -/
  | letMut (i : Nat)
  /-- A lend `&x` or `&mut x` in a surface body (P7, P8): its range and mode. -/
  | lend (a b : Nat) (isMut : Bool)
  /-- A call's or a handler's arguments: their range, and the callee when it is a declaration of
  the program or a library module, by name (P7, P8). -/
  | callArgs (a b : Nat) (callee : Option String)
  /-- A loop's source, or a fold's scrutinee: its range (§82 *Lends that are not P8*: kept as written). -/
  | loopSrc (a b : Nat)
  /-- `let r = &x; S` (P9): the `let`, the `;`, and the end of `S`. -/
  | letRef (letTok : Nat) (semi : Nat) (restEnd : Nat)
  /-- An arm of a `match`, `case` or `fold` in a surface body (E5, E7, E9): its body's range. -/
  | arm (a b : Nat)
  /-- `with h(e) { M }` in a surface body (H1–H4, H7): the `with`, the name of a named instance
  (`with n = h(e)`), the handler's range, and the body's `{` and `}`. -/
  | withBlk (w : Nat) (named : Option Nat) (h₀ h₁ : Nat) (lb rb : Nat)
  deriving Repr, Inhabited

/-- The respelling's record of a parse.  `[spec §82]` -/
structure St where
  /-- Whether events are recorded: only `bcc respell` sets it. -/
  on : Bool := false
  /-- Whether the types being read are in a declaration header whose arrows are respelled (T1):
  a `fn`, `poly`, `effect`, `handler` or `main ->` header. -/
  t1 : Bool := false
  evs : Array Ev := #[]
  /-- The first token of the binding whose head is being read (`x <- M`). -/
  stmt₀ : Nat := 0
  deriving Inhabited

end Frontend.Respell

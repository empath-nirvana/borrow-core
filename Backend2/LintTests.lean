import Backend2.Lint

/-!
# Backend2 — the lint's negative tests  `[docs/compiler.md §5.2]`

LIR programs no checked term converts to, each refused by `Lint.lint` for what the type of one
variable says, beside the program that differs only in that type and is accepted. A function
`f0` takes `x0` at the type under test and either copies it (`copy x0 -> x1`, answering the pair
of both) or drops it (`drop x0`, answering `()`). The `!` read here is the one `Types.ofV` keeps.
-/

namespace Backend2.LintTests
open Backend2

/-- `f0 (x0 : t) = copy x0 -> x1; (x0, x1)`. -/
def copyProg (t : LTy) : Prog where
  fns := #[{ name := "copies", params := [0], ret := .pair t t, body := .copy 0 1 (.pair 0 1) }]
  codes := #[]
  main := .unit
  mainTy := .unit
  ty := (({} : Std.HashMap Var LTy).insert 0 t).insert 1 t

/-- `f0 (x0 : t) = drop x0; ()`. -/
def dropProg (t : LTy) : Prog where
  fns := #[{ name := "drops", params := [0], ret := .unit, body := .drop 0 .unit }]
  codes := #[]
  main := .unit
  mainTy := .unit
  ty := ({} : Std.HashMap Var LTy).insert 0 t

/-- The lint refuses `p`, its message holding `word`. -/
def refuses (p : Prog) (word : String) : Bool :=
  match Lint.lint p with
  | .error e => (e.splitOn word).length > 1
  | .ok () => false

def accepts (p : Prog) : Bool := (Lint.lint p).isOk

def i32T : LTy := .int .w32
/-- A closure of `1 ⊸ F 1`, linear. -/
def closT : LTy := .thunk (.arr .unit (.ret .unit))

-- A copy of a variable that is not persistent: an owned cell, a linear closure, a `mut` borrow,
-- a family that owns its cells.
#guard refuses (copyProg (.ref i32T)) "copied at ref i32, which is not persistent"
#guard refuses (copyProg closT) "which is not persistent"
#guard refuses (copyProg (.mut i32T)) "which is not persistent"
#guard refuses (copyProg (.fam (.ref i32T))) "which is not persistent"
#guard refuses (copyProg (.pair i32T closT)) "which is not persistent"

-- The same copies at a persistent type, or of an `imm` borrow: accepted.
#guard accepts (copyProg (.bang closT))
#guard accepts (copyProg (.pair i32T (.bang closT)))
#guard accepts (copyProg i32T)
#guard accepts (copyProg (.imm i32T))
#guard accepts (copyProg (.fam (.imm i32T)))

-- A drop of a variable that may own a cell, or of a linear closure.
#guard refuses (dropProg (.ref i32T)) "dropped at ref i32, which may own a cell"
#guard refuses (dropProg closT) "which may own a cell"
#guard refuses (dropProg (.fam (.ref i32T))) "which may own a cell"

-- The same drops under `!`, and of borrows: accepted.
#guard accepts (dropProg (.bang closT))
#guard accepts (dropProg (.mut i32T))
#guard accepts (dropProg (.fam (.mut i32T)))

-- A drop of an opaque value, or of a pair holding one: refused. No constant forgets an opaque
-- value and it has no destructor, so only an `abandon` node discards one.
#guard refuses (dropProg (.opq .output)) "which may own a cell or an opq value"
#guard refuses (dropProg (.pair i32T (.opq .input))) "or an opq value"

/-- `f0 (x0 : t) = abandon x0 (a [let]'s abort); ()`. -/
def abandonProg (t : LTy) : Prog where
  fns := #[{ name := "abandons", params := [0], ret := .unit, body := .abandon .letAbort 0 .unit }]
  codes := #[]
  main := .unit
  mainTy := .unit
  ty := ({} : Std.HashMap Var LTy).insert 0 t
#guard accepts (abandonProg (.opq .output))
#guard accepts (abandonProg (.pair i32T (.opq .input)))
-- An abandonment admits no more than `LTy.drops`: an owned cell is refused there too.
#guard refuses (abandonProg (.ref i32T)) "abandoned at ref i32 (let abort), which may own a cell"

/-- A `[let]`'s branch on its premise's outcome `x0 : 1 + i32`, with `x1`, an output stream, in
`N`'s context: the abort arm abandons `x1` (`hW`) and answers the abort `inr e`; the value arm
`ok` gets `x1` with the value `u`. -/
def letArms (ok : Tm) : Prog where
  fns := #[{ name := "let arms", params := [0, 1], ret := .sum (.opq .output) i32T,
             body := .case 0 2 ok 3 (.abandon .letAbort 1 (.inj true 3)) }]
  codes := #[]
  main := .unit
  mainTy := .unit
  ty := (((((({} : Std.HashMap Var LTy).insert 0 (.sum .unit i32T)).insert 1 (.opq .output)).insert 2
    .unit).insert 3 i32T).insert 4 i32T)

-- The value arm hands the stream on: accepted.
#guard accepts (letArms (.drop 2 (.inj false 1)))
-- The value arm drops the stream, which the abort arm abandons: refused. The abort arm's
-- abandonment is a node at its own site and licenses nothing in the other arm, so the same
-- variable's drop there is checked by its type alone.
#guard refuses (letArms (.drop 2 (.drop 1 (.letv 4 (.lit (.i32 0)) (.inj true 4)))))
  "x1 dropped at Output, which may own a cell or an opq value"

-- A drop no type licenses, of a stack machine's level (`Prog.stackKs`): accepted.
#guard accepts { dropProg closT with stackKs := ({} : Std.HashSet Var).insert 0 }

end Backend2.LintTests

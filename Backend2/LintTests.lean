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

-- A drop no type licenses, of a stack machine's level (`Prog.stackKs`): accepted.
#guard accepts { dropProg closT with stackKs := ({} : Std.HashSet Var).insert 0 }

end Backend2.LintTests

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

/-- `f0 (x0 : t) = copy x0 -> x1 (at the rule r); (x0, x1)`. -/
def copyProg (t : LTy) (r : CopyRule := .dup) : Prog where
  fns := #[{ name := "copies", params := [0], ret := .pair t t, body := .copy r 0 1 (.pair 0 1) }]
  codes := #[]
  main := .unit
  mainTy := .unit
  ty := (({} : Std.HashMap Var LTy).insert 0 t).insert 1 t

/-- `f0 (x0 : t) = drop x0 (at the rule r); ()`. -/
def dropProg (t : LTy) (r : DropRule := .dead) : Prog where
  fns := #[{ name := "drops", params := [0], ret := .unit, body := .drop r 0 .unit }]
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

-- A split's copy (`Ctx.SplitP.dup`) of a variable that is not persistent: an owned cell, a linear
-- closure, a borrow, a family that owns its cells.
#guard refuses (copyProg (.ref i32T)) "copied at ref i32 (dup), where the rule's premise does not hold"
#guard refuses (copyProg closT) "where the rule's premise does not hold"
#guard refuses (copyProg (.mut i32T)) "where the rule's premise does not hold"
#guard refuses (copyProg (.fam (.ref i32T))) "where the rule's premise does not hold"
#guard refuses (copyProg (.pair i32T closT)) "where the rule's premise does not hold"
-- F4: an `imm` borrow is linear, so a split does not copy it; the derived copy does
-- (`copy_derives` at `DerivedCopy`), as does the constant.
#guard refuses (copyProg (.imm i32T)) "(dup), where the rule's premise does not hold"
#guard accepts (copyProg (.imm i32T) .derived)
#guard accepts (copyProg (.fam (.imm i32T)) .derived)
#guard accepts (copyProg (.imm i32T) .const)
-- The derived copy is at `DerivedCopy` only: not a `mut` borrow, an owned cell, or a persistent
-- value (which a split copies).
#guard refuses (copyProg (.mut i32T) .derived) "(derived), where the rule's premise does not hold"
#guard refuses (copyProg (.ref i32T) .derived) "(derived), where the rule's premise does not hold"
#guard refuses (copyProg i32T .derived) "(derived), where the rule's premise does not hold"

-- A split's copy at a persistent type: accepted.
#guard accepts (copyProg (.bang closT))
#guard accepts (copyProg (.pair i32T (.bang closT)))
#guard accepts (copyProg i32T)

-- A drop of a variable that may own a cell, or of a linear closure, at every rule.
#guard refuses (dropProg (.ref i32T)) "dropped at ref i32 (dead), where the rule's premise does not hold"
#guard refuses (dropProg closT .unused) "(unused), where the rule's premise does not hold"
#guard refuses ({ dropProg (.fam (.ref i32T)) .dtor with dtorFns := ({} : Std.HashSet Nat).insert 0 })
  "(dtor), where the rule's premise does not hold"

-- Weakening (`dead`) is at a persistent type only: a borrow is dropped by a `forget` constant or
-- a destructor's leaf.
#guard accepts (dropProg (.bang closT))
#guard refuses (dropProg (.mut i32T)) "(dead), where the rule's premise does not hold"
#guard accepts (dropProg (.mut i32T) .forget)
#guard accepts (dropProg (.imm i32T) .forget)
#guard accepts (dropProg (.fam (.imm i32T)) .forget)
-- F7: a family of `mut` borrows is dropped only by a destructor (`HasDtor.arrayMut`, at a `dtor`
-- node); no constant forgets it.
#guard accepts { dropProg (.fam (.mut i32T)) .dtor with dtorFns := ({} : Std.HashSet Nat).insert 0 }
-- …and only in a destructor function: the same drop in a function `Convert` did not register as
-- one is refused.
#guard refuses (dropProg (.fam (.mut i32T)) .dtor) "outside a destructor function"
#guard refuses (dropProg (.fam (.mut i32T)) .forget) "(forget), where the rule's premise does not hold"
#guard refuses (dropProg (.fam (.mut i32T)) .unused) "(unused), where the rule's premise does not hold"
-- A slot no mask holds is weakened, at a persistent type only: a borrow there is one the kernel
-- absorbs, which the conversion does not drop.
#guard accepts (dropProg i32T .unused)
#guard refuses (dropProg (.imm i32T) .unused) "(unused), where the rule's premise does not hold"

-- A drop of an opaque value, or of a pair holding one: refused at every rule. No constant forgets
-- an opaque value and it has no destructor, so only an `abandon` node discards one.
#guard refuses (dropProg (.opq .output)) "where the rule's premise does not hold"
#guard refuses (dropProg (.opq .output) .unused) "where the rule's premise does not hold"
#guard refuses ({ dropProg (.opq .output) .dtor with dtorFns := ({} : Std.HashSet Nat).insert 0 })
  "where the rule's premise does not hold"
#guard refuses (dropProg (.pair i32T (.opq .input)) .unused) "where the rule's premise does not hold"

/-- `f0 (x0 : t) = abandon x0 (at the rule r); ()`. -/
def abandonProg (t : LTy) (r : Abandon := .letAbort) : Prog where
  fns := #[{ name := "abandons", params := [0], ret := .unit, body := .abandon r 0 .unit }]
  codes := #[]
  main := .unit
  mainTy := .unit
  ty := ({} : Std.HashMap Var LTy).insert 0 t
#guard accepts (abandonProg (.opq .output))
#guard accepts (abandonProg (.pair i32T (.opq .input)))
-- A `[let]`'s abort admits `effLet`'s `hW` (`VTy.Drop`, `LTy.drops`) and no more: an owned cell
-- is refused.
#guard refuses (abandonProg (.ref i32T))
  "abandoned at ref i32 (let abort), where the rule's premise does not hold"
-- So is a persistent byte list, which `VTy.Drop` does not hold (`μ`): a type the program may drop,
-- but not one `hW` abandons.
#guard refuses (abandonProg (.mu (.sum .unit (.pair (.int .w8) (.tvar 0)))))
  "(let abort), where the rule's premise does not hold"
-- So is a closure, or a family of borrows.
#guard refuses (abandonProg closT) "(let abort), where the rule's premise does not hold"
#guard refuses (abandonProg (.fam (.imm i32T))) "(let abort), where the rule's premise does not hold"
-- `⊤` absorbs its whole context at every type: `topI` has no premise.
#guard accepts (abandonProg (.ref i32T) .top)
#guard accepts (abandonProg closT .top)
-- A superseded raise payload is abandoned at `effRaise`'s `hd` (`VTy.Drop`): an opaque value, and
-- a borrow, but not an owned cell or a family of borrows.
#guard accepts (abandonProg (.opq .input) .superseded)
#guard accepts (abandonProg (.imm i32T) .superseded)
#guard refuses (abandonProg (.ref i32T) .superseded) "(superseded), where the rule's premise does not hold"
#guard refuses (abandonProg (.fam (.imm i32T)) .superseded) "(superseded), where the rule's premise does not hold"

/-- `f0 (x0 : t) = x0.j`: an observation of a `&` closure. -/
def selProg (t : LTy) (j : Nat) (r : LTy) : Prog where
  fns := #[{ name := "sel", params := [0], ret := r, body := .sel 0 j }]
  codes := #[]
  main := .unit
  mainTy := .unit
  ty := ({} : Std.HashMap Var LTy).insert 0 t
-- A must-resume `κ`'s cancel component is `⊤`, which has no elimination: never observed.
#guard refuses (selProg (.thunk (.amp (.arr i32T (.ret .unit)) .top)) 1 .unit) "observed at `⊤`"
#guard accepts (selProg (.thunk (.amp (.arr i32T (.ret .unit)) (.ret .unit))) 1 .unit)

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
#guard accepts (letArms (.drop .dead 2 (.inj false 1)))
-- The value arm drops the stream, which the abort arm abandons: refused. The abort arm's
-- abandonment is a node at its own site and licenses nothing in the other arm, so the same
-- variable's drop there is checked by its type alone.
#guard refuses (letArms (.drop .dead 2 (.drop .unused 1 (.letv 4 (.lit (.i32 0)) (.inj true 4)))))
  "x1 dropped at Output (unused), where the rule's premise does not hold"

-- A drop no type licenses, of a stack machine's level (`Prog.stackKs`): accepted at the rule
-- `stackK` alone, and that rule admits no other variable.
#guard accepts { dropProg closT .stackK with stackKs := ({} : Std.HashSet Var).insert 0 }
#guard refuses { dropProg closT with stackKs := ({} : Std.HashSet Var).insert 0 } "(dead)"
#guard refuses (dropProg i32T .stackK) "(stack k), where the rule's premise does not hold"

end Backend2.LintTests

import Backend2.Lint
import Backend2.Interp
import Backend2.Lower
import Backend2.LayoutCheck
import Backend2.Flow

/-!
# Backend2 — the lint's negative tests  `[docs/compiler.md §5.2]`

LIR programs no checked term converts to, each refused by `Lint.lint` for what the type of one
variable says, beside the program that differs only in that type and is accepted. A function
`f0` takes `x0` at the type under test and either copies it (`copy x0 -> x1`, answering the pair
of both) or consumes it (`consume x0`, answering `()`). The `!` read here is the one `Types.ofV` keeps.
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

/-- `f0 (x0 : t) = consume x0 (at the rule r); ()`. -/
def consumeProg (t : LTy) (r : ConsumeRule := .dead) : Prog where
  fns := #[{ name := "consumes", params := [0], ret := .unit, body := .consume r 0 .unit }]
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

-- A consume of a variable that may own a cell, or of a linear closure, at every rule.
#guard refuses (consumeProg (.ref i32T)) "consumed at ref i32 (dead), where the rule's premise does not hold"
#guard refuses (consumeProg closT .unused) "(unused), where the rule's premise does not hold"
#guard refuses ({ consumeProg (.fam (.ref i32T)) .consume with consumeFns := ({} : Std.HashSet Nat).insert 0 })
  "(consume), where the rule's premise does not hold"

-- Weakening (`dead`) is at a persistent type only: a borrow is consumed by a `release` constant or
-- a consume's leaf.
#guard accepts (consumeProg (.bang closT))
#guard refuses (consumeProg (.mut i32T)) "(dead), where the rule's premise does not hold"
#guard accepts (consumeProg (.mut i32T) .release)
#guard accepts (consumeProg (.imm i32T) .release)
#guard accepts (consumeProg (.fam (.imm i32T)) .release)
-- F7: a family of `mut` borrows is consumed only by a consume (`Consumable.arrayMut`, at a `consume`
-- node); no constant discards it.
#guard accepts { consumeProg (.fam (.mut i32T)) .consume with consumeFns := ({} : Std.HashSet Nat).insert 0 }
-- …and only in a consume function: the same consume in a function `Convert` did not register as
-- one is refused.
#guard refuses (consumeProg (.fam (.mut i32T)) .consume) "outside a consume function"
#guard refuses (consumeProg (.fam (.mut i32T)) .release) "(release), where the rule's premise does not hold"
#guard refuses (consumeProg (.fam (.mut i32T)) .unused) "(unused), where the rule's premise does not hold"
-- A slot no mask holds is weakened, at a persistent type only: a borrow there is one the kernel
-- absorbs, which the conversion does not consume.
#guard accepts (consumeProg i32T .unused)
#guard refuses (consumeProg (.imm i32T) .unused) "(unused), where the rule's premise does not hold"

/-- `f0 (x0 : t, x1 : 0) = absurd x1`: `x0` left unconsumed on a path that ends at `absurd`, as
`zeroE` absorbs a slot its value does not read; and `f0 (x0 : t, x1 : 0) = ()`, the same slot
left on a path that returns.  [spec §66] -/
def absorbProg (t : LTy) (ends : Bool := true) : Prog where
  fns := #[{ name := "absorbs", params := [0, 1], ret := .unit,
             body := if ends then .absurd 1 else .consume .dead 1 .unit }]
  codes := #[]
  main := .unit
  mainTy := .unit
  ty := (({} : Std.HashMap Var LTy).insert 0 t).insert 1 .zero
-- At `absurd` the path never returns: an owned cell, a borrow or an opaque value is left there,
-- read from the node, whatever its type.
#guard accepts (absorbProg (.ref i32T))
#guard accepts (absorbProg (.imm i32T))
#guard accepts (absorbProg (.opq .output))
-- On a path that returns, the same slot is refused.
#guard refuses (absorbProg (.ref i32T) false) "ends with [x0] unconsumed"

-- A consume of an opaque value, or of a pair holding one: refused at every rule. No constant discards
-- an opaque value and it is not consumable, so only an `abandon` node discards one.
#guard refuses (consumeProg (.opq .output)) "where the rule's premise does not hold"
#guard refuses (consumeProg (.opq .output) .unused) "where the rule's premise does not hold"
#guard refuses ({ consumeProg (.opq .output) .consume with consumeFns := ({} : Std.HashSet Nat).insert 0 })
  "where the rule's premise does not hold"
#guard refuses (consumeProg (.pair i32T (.opq .input)) .unused) "where the rule's premise does not hold"

/-- `f0 (x0 : t) = abandon x0 (at the rule r); ()`. -/
def abandonProg (t : LTy) (r : Abandon := .letAbort) : Prog where
  fns := #[{ name := "abandons", params := [0], ret := .unit, body := .abandon r 0 .unit }]
  codes := #[]
  main := .unit
  mainTy := .unit
  ty := ({} : Std.HashMap Var LTy).insert 0 t
#guard accepts (abandonProg (.opq .output))
#guard accepts (abandonProg (.pair i32T (.opq .input)))
-- A `[let]`'s abort admits `effLet`'s `hW` (`VTy.Consume`, `LTy.consumes`) and no more: an owned cell
-- is refused.
#guard refuses (abandonProg (.ref i32T))
  "abandoned at ref i32 (let abort), where the rule's premise does not hold"
-- So is a persistent byte list, which `VTy.Consume` does not hold (`μ`): a type the program may consume,
-- but not one `hW` abandons.
#guard refuses (abandonProg (.mu (.sum .unit (.pair (.int .w8) (.tvar 0)))))
  "(let abort), where the rule's premise does not hold"
-- So is a closure, or a family of borrows.
#guard refuses (abandonProg closT) "(let abort), where the rule's premise does not hold"
#guard refuses (abandonProg (.fam (.imm i32T))) "(let abort), where the rule's premise does not hold"
-- `⊤` absorbs its whole context at every type: `topI` has no premise.
#guard accepts (abandonProg (.ref i32T) .top)
#guard accepts (abandonProg closT .top)
-- A superseded raise payload is abandoned at `effRaise`'s `hd` (`VTy.Consume`): an opaque value, and
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
#guard accepts (letArms (.consume .dead 2 (.inj false 1)))
-- The value arm consumes the stream, which the abort arm abandons: refused. The abort arm's
-- abandonment is a node at its own site and licenses nothing in the other arm, so the same
-- variable's consume there is checked by its type alone.
#guard refuses (letArms (.consume .dead 2 (.consume .unused 1 (.letv 4 (.lit (.i32 0)) (.inj true 4)))))
  "x1 consumed at Output (unused), where the rule's premise does not hold"

-- A consume no type licenses, of a stack machine's level: refused at every rule but `stackK`, which
-- admits only a hand-over (`handsOver`, below).
#guard refuses (consumeProg closT) "(dead)"
#guard refuses (consumeProg i32T .stackK) "(stack k), where the rule's premise does not hold"
#guard refuses (consumeProg closT .stackK) "(stack k), where the rule's premise does not hold"

def addrT : LTy := .addr
/-- A stack machine's `k`: a closure of a `&` code, resumed with `()` or cancelled. -/
def kT : LTy := .thunk (.amp (.arr .unit (.ret .unit)) (.ret .unit))

/-- **A hand-over's shape**: `c0`, a code of kind `kind` whose functions `f1`, `f2` take one
address each (`x10`, `x11` at `entryT`), at the closure type `kT` (`f1` answers a closure of `c1`,
`1 ⊸ F 1`); `f0 (x0 : t, x1 : baseT) =
body`, answering `kT`; `main` makes `x0 = clos c0 [5]` and calls `f0 x0 7`, no task stack. -/
def handProg (body : Tm) (t : LTy := kT) (baseT : LTy := addrT) (kind : CodeKind := .amp)
    (entryT : LTy := addrT) : Prog where
  fns := #[{ name := "hands over", params := [0, 1], ret := kT, body },
           { name := "resume entry", params := [10], ret := .thunk (.arr .unit (.ret .unit)),
             body := .consume .dead 10 (.clos 1 []) },
           { name := "cancel entry", params := [11], ret := .unit, body := .consume .dead 11 .unit },
           { name := "resumed", params := [13], ret := .unit, body := .var 13 }]
  codes := #[{ kind, fns := [1, 2], ty := .amp (.arr .unit (.ret .unit)) (.ret .unit) },
             { kind := .lam, fns := [3], ty := .arr .unit (.ret .unit) }]
  main := .letv 3 (.lit (.i64 5)) (.letv 4 (.clos 0 [3]) (.letv 5 (.lit (.i64 7))
    (.call 0 [4, 5])))
  mainTy := kT
  ty := [(0, t), (1, baseT), (2, kT), (3, addrT), (4, kT), (5, addrT), (10, entryT),
    (11, entryT), (12, .unit), (13, .unit)].foldl (fun m (x, t) => m.insert x t) {}

/-- `consume x0 (stack k); let x2 = clos c0 [x1]; x2`: `x0` handed over to `clos c0 [x1]`. -/
def handsOverTo : Tm := .consume .stackK 0 (.letv 2 (.clos 0 [1]) (.var 2))

#guard accepts (handProg handsOverTo)
-- The premise fails: the body does not first bind the `k` taking over; `x0` is not of the code's
-- closure type; the base is not an address; the code is not a `&`; its entries do not take an
-- address.
#guard refuses (handProg (.consume .stackK 0 (.letv 2 (.var 1) (.letv 12 (.consume .dead 2 .unit)
    (.consume .dead 12 (.clos 0 [1]))))))
  "does not first bind the k it hands over to"
#guard refuses (handProg handsOverTo (t := .thunk (.amp (.arr i32T (.ret .unit)) (.ret .unit))))
  "x0 is not of c0's closure type"
#guard refuses (handProg handsOverTo (baseT := i32T)) "x1, the base, is not an address"
#guard refuses (handProg handsOverTo (kind := .unit)) "is not a `&` code"
#guard refuses (handProg handsOverTo (entryT := i32T)) "does not take one address"

/-- The LIR interpreter's run of `p` fails, its message holding `word`. -/
def runFails (p : Prog) (word : String) : Bool :=
  match runLIR p 1000 [] with
  | .error e => (e.splitOn word).length > 1
  | .ok _ => false

-- `Lint` reads the hand-over's shape only. `handProg handsOverTo` passes it, but its `x0` is a
-- closure over no frame of a task stack: the interpreter refuses the run at the consume
-- (`handOverB`). So the hand-over is a fact about the code `Convert` generates
-- (`StackKHandOver`), not about every program `Lint` accepts.
#guard runFails (handProg handsOverTo) "at the rule stack k, where the hand-over does not hold"

/-- **A function whose lend bit is set, entered beside the owner** (SPEC §50, `LendEnclosesFn`):
`main` allocates a cell `x2`, lends it (`x3`, the owner `x4`, the borrow `x5`) and calls
`f0 (x4, x5)`, which ends the lend and frees the cell, as a machine's cancel step does. With `bits`,
`f0`'s parameter has its lend bit set. -/
def enclProg (bits : List Bool) : Prog where
  fns := #[{ name := "cancel", params := [0], ret := .unit, lendEncl := bits,
             body := .letpair 6 7 0 (.consume .release 6 (.letv 9 (.prim .free [7]) (.consume .dead 9 .unit))) }]
  codes := #[]
  main := .letv 1 (.lit (.i32 3)) (.letv 2 (.prim (.alloc [i32T]) [1]) (.letv 3 (.prim (.lend true) [2])
    (.letpair 4 5 3 (.letv 8 (.pair 5 4) (.call 0 [8])))))
  mainTy := .unit
  ty := [(0, .pair (.mut i32T) (.ref i32T)), (1, i32T), (2, .ref i32T), (3, .pair (.ref i32T) (.mut i32T)),
    (4, .ref i32T), (5, .mut i32T), (6, .mut i32T), (7, .ref i32T),
    (8, .pair (.mut i32T) (.ref i32T)), (9, i32T)].foldl (fun m (x, t) => m.insert x t) {}

-- `Lint` accepts the program at either bit; it reads no lifetimes. Its run is refused only where the
-- bit is set: the borrow is beside its owner (`enclosesB`). So the bit's setting is a fact about the
-- code `Convert` generates (`LendEnclosesFn`): set only at a source function.
#guard accepts (enclProg [])
#guard accepts (enclProg [true])
#guard refuses (enclProg [true, true]) "2 lend bits for 1 parameters"
#guard runFails (enclProg [true]) "beside its cell's owner or another borrow of it (LendEnclosesFn)"
#guard !runFails (enclProg []) "LendEnclosesFn"
#guard !runFails (enclProg [false]) "LendEnclosesFn"

/-- **A function whose lend bit is set, whose callee frees the cell through an owner it captured**:
`main` lends the cell `x4` (the owner `x6`, the borrow `x7`), closes `c0` over the owner, and calls
`f0 (x7, x8)`; `f0` releases the borrow and forces the closure, whose `f1` frees the cell. No
parameter of `f0` is the owner (`ownersIn` does not look into a closure's environment), so the
entry check passes; the cell is gone when `f0` returns. -/
def enclClosProg (bits : List Bool) : Prog where
  fns := #[{ name := "user", params := [0, 1], ret := .unit, lendEncl := bits,
             body := .consume .release 0 (.app0 1) },
           { name := "free", params := [2], ret := .unit,
             body := .letv 9 (.prim .free [2]) (.consume .dead 9 .unit) }]
  codes := #[{ kind := .unit, fns := [1], ty := .ret .unit }]
  main := .letv 3 (.lit (.i32 3)) (.letv 4 (.prim (.alloc [i32T]) [3]) (.letv 5 (.prim (.lend true) [4])
    (.letpair 6 7 5 (.letv 8 (.clos 0 [6]) (.call 0 [7, 8])))))
  mainTy := .unit
  ty := [(0, .mut i32T), (1, .thunk (.ret .unit)), (2, .ref i32T), (3, i32T), (4, .ref i32T),
    (5, .pair (.ref i32T) (.mut i32T)), (6, .ref i32T), (7, .mut i32T),
    (8, .thunk (.ret .unit)), (9, i32T)].foldl (fun m (x, t) => m.insert x t) {}

#guard accepts (enclClosProg [true, true])
#guard runFails (enclClosProg [true, true]) "returns with the cell of a parameter whose lend bit is set freed"
#guard !runFails (enclClosProg []) "LendEnclosesFn"

/-- `f0 (x0 : mut i32) = forget x0`, called on a borrow of a cell `main` lends and then frees;
`f0`'s lend bits are `bits`. -/
def borrowProg (bits : List Bool) : Prog where
  fns := #[{ name := "user", params := [0], ret := .unit, lendEncl := bits,
             body := .consume .release 0 .unit }]
  codes := #[]
  main := .letv 1 (.lit (.i32 3)) (.letv 2 (.prim (.alloc [i32T]) [1]) (.letv 3 (.prim (.lend true) [2])
    (.letpair 4 5 3 (.letv 6 (.call 0 [5]) (.consume .dead 6 (.letv 7 (.prim .free [4]) (.consume .dead 7 .unit)))))))
  mainTy := .unit
  ty := [(0, .mut i32T), (1, i32T), (2, .ref i32T), (3, .pair (.ref i32T) (.mut i32T)),
    (4, .ref i32T), (5, .mut i32T), (6, .unit), (7, i32T)].foldl (fun m (x, t) => m.insert x t) {}

/-- The number of `p`'s `f0`'s facts in the word IR (its `f1`), lowered as `Driver.flatOf` lowers:
the layouts, the closure flow, each checked, then the word IR. -/
def f0Facts (p : Prog) : Except String Nat := do
  let (g, m) ← Lay.places p
  let L := Lay.resolve p g m
  LayCheck.check p L
  let fs := Flow.solution p L
  let kn := Flow.known p L fs
  LayCheck.checkFlow p L fs.sets kn
  let fp ← Low.lowerProg p L kn fs.sets false
  pure (((fp.fns[1]?).map (·.facts.length)).getD 0)

-- `paramFacts` reads the bit: the `mut` borrow has its facts only where its bit is set.
#guard accepts (borrowProg [true])
#guard f0Facts (borrowProg [true]) == .ok 1
#guard f0Facts (borrowProg []) == .ok 0
#guard f0Facts (borrowProg [false]) == .ok 0

/-- `f0 (x0 : a) = let x1 : r = slotPop x0; letpair (x2, x3) = x1; (x2, x3)` (the result's
parts at `r`'s components, or `a` and `i32` when `r` is not a pair).  [spec §77] -/
def popProg (a r : LTy) : Prog where
  fns := #[{ name := "pops", params := [0], ret := r,
             body := .letv 1 (.prim .slotPop [0]) (.letpair 2 3 1 (.pair 2 3)) }]
  codes := #[]
  main := .unit
  mainTy := .unit
  ty := (((({} : Std.HashMap Var LTy).insert 0 a).insert 1 r).insert 2
      (match r with | .pair x _ => x | _ => a)).insert 3 (match r with | .pair _ y => y | _ => i32T)
-- A `slotPop` of an owned array, answering the family and its slot's contents: accepted.
#guard accepts (popProg (.fam (.ref i32T)) (.pair (.fam (.ref i32T)) i32T))
-- Of a family of borrows, whose slots are not the family's to move: refused.
#guard refuses (popProg (.fam (.imm i32T)) (.pair (.fam (.imm i32T)) (.imm i32T))) "not an owned array"
#guard refuses (popProg (.fam (.mut i32T)) (.pair (.fam (.mut i32T)) (.mut i32T))) "not an owned array"
-- Answering another family, or contents of another type: refused.
#guard refuses (popProg (.fam (.ref i32T)) (.pair (.fam (.ref (.int .w64))) i32T)) "not its operand's"
#guard refuses (popProg (.fam (.ref i32T)) (.pair (.fam (.ref i32T)) (.int .w64))) "answers contents"
-- Answering no pair: refused, as such.
#guard refuses (popProg (.fam (.ref i32T)) i32T) "not a pair of the family"

/-! ### The shapes of the values  (#1087)

A `letpair` takes apart a pair and a `case` a sum; a `pair` and an `inj` are built at the type
they are expected at (`Lint.elimBad`, `Lint.introBad`). -/

/-- `f0 (x0 : t) = letpair (x1, x2) = x0; (x1, x2)`, answering `r` (by default `t`), the parts at
`t`'s components (`i32` when `t` is not a pair). -/
def pairElim (t : LTy) (r : LTy := t) : Prog where
  fns := #[{ name := "unpairs", params := [0], ret := r, body := .letpair 1 2 0 (.pair 1 2) }]
  codes := #[]
  main := .unit
  mainTy := .unit
  ty := ((({} : Std.HashMap Var LTy).insert 0 t).insert 1
      (match t.peel with | .pair a _ => a | _ => i32T)).insert 2
      (match t.peel with | .pair _ b => b | _ => i32T)

/-- `f0 (x0 : t) = case x0 {inl x1. inr x1 | inr x2. inl x2}`, answering `r`, the arms' variables
at `t`'s summands (`i32` when `t` is not a sum). -/
def sumElim (t : LTy) (r : LTy) : Prog where
  fns := #[{ name := "swaps", params := [0], ret := r,
             body := .case 0 1 (.inj true 1) 2 (.inj false 2) }]
  codes := #[]
  main := .unit
  mainTy := .unit
  ty := ((({} : Std.HashMap Var LTy).insert 0 t).insert 1
      (match t.peel with | .sum a _ => a | _ => i32T)).insert 2
      (match t.peel with | .sum _ b => b | _ => i32T)

def i64T : LTy := .int .w64

-- A pair taken apart and rebuilt, a sum's arms swapped: accepted, also through a `!`.
#guard accepts (pairElim (.pair i32T i64T))
#guard accepts (pairElim (.bang (.pair i32T i64T)) (.pair i32T i64T))
#guard accepts (sumElim (.sum i32T i64T) (.sum i64T i32T))
-- A `letpair` of a sum injection (the #940 mis-lowering's shape), or of an integer: refused.
#guard refuses (pairElim (.sum i32T i64T) (.pair i32T i32T)) "a letpair takes apart x0 : (i32 + i64), which is not a pair"
#guard refuses (pairElim i32T (.pair i32T i32T)) "which is not a pair"
-- A `case` of a pair: refused.
#guard refuses (sumElim (.pair i32T i64T) (.sum i32T i32T)) "a case takes apart x0 : (i32 * i64), which is not a sum"
-- A pair built at a sum type, an injection at a pair type, or of the wrong summand: refused.
#guard refuses (pairElim (.pair i32T i64T) (.sum i32T i64T)) "which is not a pair type"
#guard refuses (sumElim (.sum i32T i64T) (.pair i64T i32T)) "which is not a sum type"
-- Each arm's injection is checked: the first arm's alone wrong, then the second's alone.
#guard refuses (sumElim (.sum i32T i64T) (.sum i64T i64T)) "an inr at (i64 + i64) of x1 : i32"
#guard refuses (sumElim (.sum i32T i64T) (.sum i32T i32T)) "an inl at (i32 + i32) of x2 : i64"
-- A letpair binding a component at another type: refused.
#guard refuses ({ pairElim (.pair i32T i64T) with
    ty := ((({} : Std.HashMap Var LTy).insert 0 (.pair i32T i64T)).insert 1 i64T).insert 2 i64T })
  "a letpair binds x1"

-- `sameTy`: a `ν` is its unrolling (no node rolls one); a `μ` is not (`Op.roll` does); `!` is
-- ignored at any depth; a cell is not a borrow of it.
/-- `C` of `νX. C`, `X` its variable `0`. -/
def nuC : LCTy := .amp (.ret (.sum i32T (.tvar 0))) (.ret .unit)
#guard nuC.unrollNu != nuC
#guard Lint.sameTy 64 (.thunk (.nu nuC)) (.thunk nuC.unrollNu)
#guard Lint.sameTy 64 (.sum i32T (.thunk nuC.unrollNu)) (.sum i32T (.thunk (.nu nuC)))
/-- `A` of `μX. A`. -/
def muA : LTy := .sum .unit (.pair i32T (.tvar 0))
#guard muA.unrollMu != muA
#guard !Lint.sameTy 64 (.mu muA) muA.unrollMu
#guard Lint.sameTy 64 (.pair i32T (.bang (.sum i32T (.bang i64T)))) (.pair i32T (.sum i32T i64T))
#guard !Lint.sameTy 64 (.ref i32T) (.imm i32T)

-- An `absurd` of a variable not of type `0`: refused.
#guard refuses ({ absorbProg (.ref i32T) with
    ty := (({} : Std.HashMap Var LTy).insert 0 (.ref i32T)).insert 1 i32T })
  "an absurd of x1 : i32, which is not 0"

/-- `f0 (ps) : r = body`, its variables' types `ty`. -/
def fnProg (ps : List Var) (r : LTy) (body : Tm) (ty : List (Var × LTy)) : Prog where
  fns := #[{ name := "f", params := ps, ret := r, body := body }]
  codes := #[]
  main := .unit
  mainTy := .unit
  ty := ty.foldl (fun m (x, t) => m.insert x t) {}

-- A `()` at a type not `1`: refused.
#guard refuses (fnProg [] i32T .unit []) "a () at i32"
-- A variable answered at a tail at another type than the function's `ret`, or `main`'s: refused.
#guard accepts (fnProg [0] i32T (.var 0) [(0, i32T)])
#guard refuses (fnProg [0] i64T (.var 0) [(0, i32T)]) "x0 : i32 answered at i64"
#guard refuses ({ fnProg [] .unit .unit [(0, i32T)] with
    main := .letv 0 (.lit (.i32 1)) (.var 0), mainTy := i64T }) "main: x0 : i32 answered at i64"
-- A direct call whose callee answers another type than the one expected: refused.
#guard refuses ({ fnProg [] i32T (.lit (.i32 0)) [] with
    fns := #[{ name := "g", params := [], ret := i32T, body := .lit (.i32 0) },
             { name := "f", params := [], ret := i64T, body := .call 0 [] }] })
  "f0 (g), answering i32, called at i64"
-- A `letv`'s value is checked at its variable's type, not at the function's `ret`: a pair bound
-- to a pair-typed variable in a function answering `i32`, accepted; the same at a sum-typed
-- variable, refused.
def letvProg (t : LTy) : Prog :=
  fnProg [1, 2] i32T (.letv 0 (.pair 1 2) (.letpair 3 4 0 (.consume .dead 3 (.var 4))))
    [(0, t), (1, i32T), (2, i32T), (3, i32T), (4, i32T)]
#guard accepts (letvProg (.pair i32T i32T))
#guard refuses (letvProg (.sum i32T i32T)) "a pair of x1 and x2 at (i32 + i32), which is not a pair type"
-- A variable with no type is refused where it is bound.
#guard refuses ({ letvProg (.pair i32T i32T) with
    ty := [(1, i32T), (2, i32T), (3, i32T), (4, i32T)].foldl (fun m (x, t) => m.insert x t) {} })
  "x0 has no type"
-- `copy`, `consume` and `abandon` pass the expected type on to their body.
#guard accepts (fnProg [0] i32T (.copy .dup 0 1 (.consume .dead 1 (.var 0))) [(0, i32T), (1, i32T)])
#guard refuses (fnProg [0] i64T (.copy .dup 0 1 (.consume .dead 1 (.var 0))) [(0, i32T), (1, i32T)])
  "x0 : i32 answered at i64"
#guard accepts (fnProg [0, 1] i32T (.abandon .letAbort 0 (.var 1)) [(0, .opq .output), (1, i32T)])
#guard refuses (fnProg [0, 1] i64T (.abandon .letAbort 0 (.var 1)) [(0, .opq .output), (1, i32T)])
  "x1 : i32 answered at i64"

/-! ### Calls, closures, literals, primitives and copies, on the LIR types  (#1094) -/

/-- `f0 (ps) : r = body` beside `f1 (x90 : i32) : i32 = x90`, its variables' types `ty`. -/
def twoFns (ps : List Var) (r : LTy) (body : Tm) (ty : List (Var × LTy)) : Prog :=
  { fnProg ps r body ((90, i32T) :: ty) with
    fns := #[{ name := "f", params := ps, ret := r, body := body },
             { name := "id", params := [90], ret := i32T, body := .var 90 }] }

-- A call's argument at its parameter's type.
#guard accepts (twoFns [0] i32T (.call 1 [0]) [(0, i32T)])
#guard refuses (twoFns [0] i32T (.call 1 [0]) [(0, i64T)]) "f1 (id) called: x0 : i64 for the parameter x90 : i32"

/-- A closure of `i32 ⊸ F i32`, of `F i32`, and of `F i32 & F 1`. -/
def arrT : LTy := .thunk (.arr i32T (.ret i32T))
def retT : LTy := .thunk (.ret i32T)
def ampT : LTy := .thunk (.amp (.ret i32T) (.ret .unit))
-- `app`: the argument at the closure's, the answer the closure's; not of a non-closure.
#guard accepts (fnProg [0, 1] i32T (.app 0 1) [(0, arrT), (1, i32T)])
#guard refuses (fnProg [0, 1] i32T (.app 0 1) [(0, arrT), (1, i64T)]) "x0 applied to x1 : i64, for an argument of i32"
#guard refuses (fnProg [0, 1] i64T (.app 0 1) [(0, arrT), (1, i32T)]) "x0 applied answers i32, at i64"
#guard refuses (fnProg [0, 1] i32T (.app 0 1) [(0, retT), (1, i32T)]) "not a closure of a function type"
-- `app0`: a closure of `F B`, answering `B`.
#guard accepts (fnProg [0] i32T (.app0 0) [(0, retT)])
#guard refuses (fnProg [0] i64T (.app0 0) [(0, retT)]) "x0 run answers i32, at i64"
#guard refuses (fnProg [0] i32T (.app0 0) [(0, arrT)]) "not a closure of a returner type"
-- `sel`: a closure of `C₀ & C₁`, answering the component's.
#guard accepts (fnProg [0] i32T (.sel 0 0) [(0, ampT)])
#guard accepts (fnProg [0] .unit (.sel 0 1) [(0, ampT)])
#guard refuses (fnProg [0] .unit (.sel 0 0) [(0, ampT)]) "x0 observed at 0 answers i32, at 1"
#guard refuses (fnProg [0] i32T (.sel 0 0) [(0, retT)]) "not a closure of a `&` type"

/-- `main = clos c0 [x0]` at `t`, where `x0 = 5 : e` and `c0`, a `unit` code of `F i32`, is `f0`,
whose environment parameter `x90` is an `i32`. -/
def closProg (t e : LTy) : Prog where
  fns := #[{ name := "thunk", params := [90], ret := i32T, body := .var 90 }]
  codes := #[{ kind := .unit, fns := [0], ty := .ret i32T }]
  main := .letv 0 (.lit (.i32 5)) (.clos 0 [0])
  mainTy := t
  ty := (({} : Std.HashMap Var LTy).insert 0 e).insert 90 i32T
#guard accepts (closProg retT i32T)
#guard refuses (closProg arrT i32T) "a closure of c0, of U F i32, at U (i32 -o F i32)"
-- (the literal `5 : i32` bound at `i64` is refused first, as a literal's width)
#guard refuses (closProg retT i64T) "a literal of i32 at i64"
#guard refuses ({ closProg retT i64T with main := .letv 0 (.lit (.i64 5)) (.clos 0 [0]) })
  "c0's closure captures: x0 : i64 for the parameter x90 : i32"
-- A code's functions at its closure type: a `unit` code of `F i64` whose function answers `i32`.
#guard refuses ({ closProg (.thunk (.ret i64T)) i32T with codes := #[{ kind := .unit, fns := [0], ty := .ret i64T }] })
  "c0: f0 (thunk) answers i32, for i64"

-- A literal at its own width.
#guard accepts (fnProg [] i64T (.lit (.i64 1)) [])
#guard refuses (fnProg [] i64T (.lit (.i32 1)) []) "a literal of i32 at i64"
#guard refuses (fnProg [] (.int .w8) (.lit (.i32 1)) []) "a literal of i32 at"

-- A copy's binder at its source's type.
#guard refuses ({ copyProg i32T with ty := (({} : Std.HashMap Var LTy).insert 0 i32T).insert 1 i64T })
  "x1 : i64 a copy of x0 : i32"

/-- `f0 (x0 : a, x1 : b) : r = op [args]`. -/
def primProg (op : Op) (args : List Var) (ts : List LTy) (r : LTy) : Prog :=
  fnProg (List.range ts.length) r (.prim op args) (ts.zipIdx.map fun (t, i) => (i, t))

/-- `p` with `f0` a harness extern's function. -/
def hostProg (p : Prog) : Prog := { p with hostFns := ({} : Std.HashSet Nat).insert 0 }

-- The primitives, each at its operands' and answer's types (`primBad`).
#guard accepts (primProg .free [0] [.ref i32T] i32T)
#guard refuses (primProg .free [0] [.ref i32T] i64T) "an owned cell's contents"
#guard refuses (primProg .free [0] [.imm i32T] i32T) "an owned cell's contents"
-- A stream's cell holds its descriptor, a clock's its time; not another word.
#guard accepts (hostProg (primProg .free [0] [.ref (.opq .output)] i32T))
#guard accepts (hostProg (primProg .free [0] [.ref (.opq .clock)] i64T))
#guard refuses (hostProg (primProg .free [0] [.ref (.opq .clock)] i32T)) "an owned cell's contents"
-- …only in a harness extern's function (`Prog.hostFns`): elsewhere a word is no capability.
#guard refuses (primProg .free [0] [.ref (.opq .output)] i32T) "an owned cell's contents"
#guard refuses (primProg (.alloc []) [0] [i32T] (.ref (.opq .output))) "a cell of the argument"
#guard accepts (hostProg (primProg (.alloc []) [0] [i32T] (.ref (.opq .input))))
#guard accepts (hostProg (primProg (.alloc []) [0] [i32T] (.ref (.opq .args))))
#guard refuses (hostProg (primProg (.alloc []) [0] [i64T] (.ref (.opq .args)))) "a cell of the argument"
#guard accepts (primProg (.alloc []) [0] [i32T] (.ref i32T))
#guard refuses (primProg (.alloc []) [0] [i32T] (.ref i64T)) "a cell of the argument"
-- `swap` answers the cell at its new contents' type and the old contents.
#guard accepts (primProg .swap [0, 1] [.ref i32T, .unit] (.pair (.ref .unit) i32T))
#guard refuses (primProg .swap [0, 1] [.ref i32T, .unit] (.pair (.ref i32T) i32T)) "the old contents"
-- `take` and `put` at a `mut` borrow or an owned cell, not a shared borrow.
#guard accepts (primProg .take [0] [.mut i32T] (.pair (.mut i32T) i32T))
#guard refuses (primProg .take [0] [.imm i32T] (.pair (.imm i32T) i32T)) "answering it and its contents"
#guard refuses (primProg .put [0, 1] [.mut i32T, i64T] (.mut i32T)) "and its contents, answering it"
-- `load` reads the contents through `Imm̲`: a pointer as a shared borrow, a closure as `Unk`.
#guard accepts (primProg .load [0] [.imm (.pair i32T (.ref i64T))] (.pair i32T (.imm i64T)))
#guard accepts (primProg .load [0] [.imm closT] .unk)
#guard refuses (primProg .load [0] [.imm (.pair i32T (.ref i64T))] (.pair i32T (.ref i64T))) "read through Imm"
-- …and a `μ`'s recursive pointers as shared borrows of the `μ` itself.
#guard accepts (primProg .load [0] [.imm (.mu (.sum .unit (.ref (.tvar 0))))]
  (.mu (.sum .unit (.imm (.mu (.sum .unit (.ref (.tvar 0))))))))
-- `lend` answers the owner and a borrow of its kind; `idx` a leaf or `()`.
#guard refuses (primProg (.lend true) [0] [.ref i32T] (.pair (.ref i32T) (.mut i64T))) "its borrow"
#guard accepts (primProg (.idx true) [0, 1] [.fam (.imm i32T), i32T] (.sum (.imm i32T) .unit))
#guard refuses (primProg (.idx true) [0, 1] [.fam (.imm i32T), i32T] (.sum (.imm i64T) .unit)) "a leaf or ()"
-- `roll` at the `μ` of its operand's unrolling.
#guard accepts (primProg .roll [0] [muA.unrollMu] (.mu muA))
#guard refuses (primProg .roll [0] [muA] (.mu muA)) "a value of the unrolling"
-- A host operation at its signature (`hostArg`, `hostRes`).
#guard accepts (primProg (.host (.bin .w32 .add)) [0] [.pair i32T i32T] i32T)
#guard refuses (primProg (.host (.bin .w32 .add)) [0] [.pair i32T i64T] i32T) "the host operation is"
-- An operand count no primitive takes.
#guard refuses (primProg .free [0, 1] [.ref i32T, i32T] i32T) "2 operands"

-- A machine's frames are of the type it declares (`Prog.frameTys`), as a site's `κ` region
-- (`Prog.regionTys`); one with no declaration is refused.
/-- A frame of machine 7, declared `d`, pushed at `c₁`, then its top read at `c₂`, each popped. -/
def framesProg (d : Option LTy) (c₁ c₂ : LTy) : Prog :=
  let pop (fa f a u : Var) (k : Tm) : Tm :=
    .letpair f a fa (.letv u (.prim (.framePop 0) [f]) (.consume .dead u (.consume .dead a k)))
  { fnProg [] .unit
      (.letv 0 (.prim (.framePush 7 0) []) (pop 0 2 3 4
        (.letv 1 (.prim (.frameTop 7 0) []) (pop 1 5 6 7 .unit))))
      [(0, .pair (.ref c₁) LTy.addr), (1, .pair (.ref c₂) LTy.addr), (2, .ref c₁), (3, LTy.addr),
       (4, .unit), (5, .ref c₂), (6, LTy.addr), (7, .unit)] with
    frameTys := match d with | some t => ({} : Std.HashMap Nat LTy).insert 7 t | none => {} }
#guard accepts (framesProg i32T i32T i32T)
#guard refuses (framesProg i32T i32T i64T) "a frame of machine 7 of i64, declared i32"
#guard refuses (framesProg i64T i32T i32T) "a frame of machine 7 of i32, declared i64"
#guard refuses (framesProg none i32T i32T) "a frame of machine 7 of i32, which has no declared type"
/-- `x1 : c₁` put in site 4's region (declared `d`) of the stack `x0`, then the region of `x2`
taken at `c₂`. -/
def regionProg (d : Option LTy) (c₁ c₂ : LTy) : Prog :=
  { fnProg [0, 1, 2] .unit (.letv 3 (.prim (.kappaPut 4) [0, 1]) (.consume .dead 3
        (.letv 5 (.prim (.kappaTake 4) [2]) (.letpair 6 7 5 (.consume .dead 6 (.consume .dead 7 .unit))))))
      [(0, LTy.addr), (1, c₁), (2, LTy.addr), (3, .unit), (5, .pair LTy.addr c₂), (6, LTy.addr), (7, c₂)] with
    regionTys := match d with | some t => ({} : Std.HashMap Nat LTy).insert 4 t | none => {} }
#guard accepts (regionProg i32T i32T i32T)
#guard refuses (regionProg i32T i32T i64T) "the κ region of site 4 of i64, declared i32"
#guard refuses (regionProg none i32T i32T) "the κ region of site 4 of i32, which has no declared type"

-- `load` is Core's `immG`: a persistent value (`!A`) is read as itself; a bare closure or an
-- opaque value only as `Unk`.
#guard accepts (primProg .load [0] [.imm (.bang closT)] (.bang closT))
#guard refuses (primProg .load [0] [.imm closT] closT) "read through Imm"
#guard accepts (primProg .load [0] [.imm (.opq .output)] .unk)
#guard refuses (primProg .load [0] [.imm (.opq .output)] (.opq .output)) "read through Imm"

-- The I/O operations at their externs' types (`lib/wasi.bc`).
def outM : LTy := .mut (.opq .output)
def inM : LTy := .mut (.opq .input)
def clkM : LTy := .mut (.opq .clock)
def u8T : LTy := .int .w8
#guard accepts (primProg (.io .readByte) [0] [inM] (.pair inM (.sum u8T .unit)))
#guard accepts (primProg (.io .readByte) [0] [.mut (.opq .args)] (.pair (.mut (.opq .args)) (.sum u8T .unit)))
#guard refuses (primProg (.io .readByte) [0] [.imm (.opq .input)] (.pair (.imm (.opq .input)) (.sum u8T .unit))) "not the extern's type"
#guard refuses (primProg (.io .readByte) [0] [outM] (.pair outM (.sum u8T .unit))) "not the extern's type"
#guard accepts (primProg (.io .writeByte) [0] [.pair outM u8T] outM)
#guard refuses (primProg (.io .writeByte) [0] [.pair inM u8T] inM) "not the extern's type"
#guard accepts (primProg (.io .writeAll) [0] [.pair outM (.fam (.imm u8T))] outM)
#guard refuses (primProg (.io .writeAll) [0] [.pair outM (.fam (.mut u8T))] outM) "not the extern's type"
#guard accepts (primProg (.io .readInto) [0] [.pair inM (.fam (.mut u8T))]
  (.pair inM (.pair (.fam (.mut u8T)) i32T)))
#guard refuses (primProg (.io .readInto) [0] [.pair inM (.fam (.imm u8T))]
  (.pair inM (.pair (.fam (.imm u8T)) i32T))) "not the extern's type"
#guard refuses (primProg (.io .readInto) [0] [.pair inM (.fam (.mut u8T))]
  (.pair inM (.pair (.fam (.mut u8T)) i64T))) "not the extern's type"
#guard accepts (primProg (.io .clockNow) [0] [clkM] (.pair clkM i64T))
#guard refuses (primProg (.io .clockNow) [0] [clkM] (.pair clkM i32T)) "not the extern's type"
#guard accepts (primProg (.io .clockSleep) [0] [.pair clkM i64T] clkM)
#guard refuses (primProg (.io .clockSleep) [0] [.pair clkM (.int .f64)] clkM) "not the extern's type"

-- A family's leaf at the modes its Core constants take.
#guard refuses (primProg (.idx true) [0, 1] [.fam (.ref i32T), i32T] (.sum (.ref i32T) .unit)) "an `imm` or `mut` family"
#guard accepts (primProg (.idx true) [0, 1] [.fam (.mut i32T), i32T] (.sum (.mut i32T) .unit))
#guard refuses (primProg (.split true) [0, 1] [.fam (.ref i32T), i32T]
  (.sum (.pair (.fam (.ref i32T)) (.fam (.ref i32T))) (.fam (.ref i32T)))) "an `imm` or `mut` family"
#guard accepts (primProg (.split true) [0, 1] [.fam (.imm i32T), i32T]
  (.sum (.pair (.fam (.imm i32T)) (.fam (.imm i32T))) (.fam (.imm i32T))))
#guard accepts (primProg .len [0] [.fam (.imm i32T)] i32T)
#guard refuses (primProg .len [0] [.fam (.ref i32T)] i32T) "an `imm` family"
#guard accepts (primProg .size [0] [.fam (.ref i32T)] (.pair (.fam (.ref i32T)) i32T))
#guard refuses (primProg .size [0] [.fam (.imm i32T)] (.pair (.fam (.imm i32T)) i32T)) "an owned or `mut` family"
#guard accepts (primProg .slotTake [0, 1] [.fam (.ref i32T), i32T] (.pair (.fam (.ref i32T)) i32T))
#guard refuses (primProg .slotTake [0, 1] [.fam (.imm i32T), i32T] (.pair (.fam (.imm i32T)) i32T)) "an owned or `mut` family"
#guard accepts (primProg .slotPut [0, 1, 2] [.fam (.ref i32T), i32T, i32T] (.fam (.ref i32T)))
#guard refuses (primProg .slotPut [0, 1, 2] [.fam (.imm i32T), i32T, i32T] (.fam (.imm i32T))) "an owned or `mut` family"
#guard accepts (primProg .replace [0, 1, 2] [.fam (.mut i32T), i32T, i32T] (.pair (.fam (.mut i32T)) (.sum i32T i32T)))
#guard refuses (primProg .replace [0, 1, 2] [.fam (.imm i32T), i32T, i32T] (.pair (.fam (.imm i32T)) (.sum i32T i32T))) "an owned or `mut` family"
#guard accepts (primProg .swapSlots [0, 1, 2] [.fam (.mut i32T), i32T, i32T] (.fam (.mut i32T)))
#guard refuses (primProg .swapSlots [0, 1, 2] [.fam (.ref i32T), i32T, i32T] (.fam (.ref i32T))) "a `mut` family"
#guard accepts (primProg .newArr [0] [i32T] (.fam (.ref i32T)))
#guard refuses (primProg .newArr [0] [i64T] (.fam (.ref i32T))) "an i32 length"
#guard accepts (primProg .freeArr [0] [.fam (.ref i32T)] .unit)
#guard refuses (primProg .freeArr [0] [.fam (.imm i32T)] .unit) "an owned array"
-- An index is an `i32`, not a float.
#guard refuses (primProg (.idx true) [0, 1] [.fam (.imm i32T), .int .f32] (.sum (.imm i32T) .unit)) "an i32 index"
#guard refuses (primProg (.divLit (.div .w32 .div_s)) [0, 1] [.int .f64, .int .f64] (.int .f64)) "two integers"
#guard refuses (primProg (.divLit (.div .w32 .div_s)) [0, 1] [i32T, i64T] i32T) "two integers"
-- A `slotPop` in a function's last position.
#guard refuses (primProg .slotPop [0] [.fam (.imm i32T)] (.pair (.fam (.imm i32T)) (.imm i32T))) "not an owned array"
-- The other rows.
#guard refuses (primProg .release [0] [.imm i32T] .unit) "an owned cell released"
#guard accepts (primProg .relend [0] [.mut i32T] (.pair (.mut i32T) (.imm i32T)))
#guard refuses (primProg .relend [0] [.ref i32T] (.pair (.ref i32T) (.imm i32T))) "a `mut` borrow"
#guard accepts (primProg .unroll [0] [.mu muA] muA.unrollMu)
#guard refuses (primProg .unroll [0] [.mu muA] muA) "its unrolling"
#guard accepts (primProg .litByte [0, 1, 2] [i32T, i32T, i32T] u8T)
#guard refuses (primProg .litByte [0, 1, 2] [i32T, i64T, i32T] u8T) "answering a byte"
#guard accepts (primProg .clampLen [0] [i32T] i32T)
#guard refuses (primProg .clampLen [0] [i32T] i64T) "an i32 length"
#guard accepts (primProg .cntLt [0, 1] [i32T, i32T] (.sum .unit .unit))
#guard refuses (primProg .cntLt [0, 1] [i64T, i64T] (.sum .unit .unit)) "an i32 index"
#guard refuses (primProg .cntSucc [0] [i64T] i64T) "an i32 count"
#guard refuses (primProg .cntPred [0] [i32T] i64T) "an i32 count"
#guard accepts (primProg (.stackSwap 0) [0] [LTy.addr] LTy.addr)
#guard refuses (primProg (.stackSwap 0) [0] [i32T] LTy.addr) "a stack"
#guard refuses (primProg .stackFree [0] [i32T] .unit) "a stack"
#guard refuses (primProg (.stackNew 3) [] [] i32T) "answering a stack"
#guard refuses (primProg (.kappaPut 4) [0, 1] [i32T, i32T] .unit) "a stack and a value"
#guard refuses (primProg .framePut [0, 1] [.ref i32T, i64T] .unit) "a frame's cell and its contents"
#guard refuses (primProg (.allocLent 0 []) [0] [i32T] (.ref i64T)) "a cell of the argument"

/-- `f0 (x0 x1 : i32) : r = tab f1 [x0, x1]`, where `f1 (x10 : i32, x11 : fill, x12 x13 : i32)`
is a tab loop answering `x11`. -/
def tabProg (fill r : LTy) : Prog :=
  { fnProg [0, 1] r (.prim (.tab 1) [0, 1]) [(0, i32T), (1, i32T), (10, i32T), (11, fill), (12, i32T), (13, i32T)] with
    fns := #[{ name := "f", params := [0, 1], ret := r, body := .prim (.tab 1) [0, 1] },
             { name := "tab", params := [10, 11, 12, 13], ret := fill,
               body := .consume .dead 10 (.consume .dead 12 (.consume .dead 13 (.var 11))) }] }
#guard accepts (tabProg (.fam (.ref i32T)) (.fam (.ref i32T)))
#guard refuses (tabProg (.fam (.imm i32T)) (.fam (.imm i32T))) "an owned array filled by its loop"

-- `sel` past a `&`'s two components; `⊤` seen through a `ν`.
#guard refuses (fnProg [0] .unit (.sel 0 2) [(0, ampT)]) "a `&` has two components"
#guard refuses (selProg (.thunk (.nu (.amp (.arr i32T (.ret .unit)) .top))) 1 .unit) "observed at `⊤`"

-- A code's functions at its closure type: a `lam` code's argument, a `&` code's second answer,
-- and a code of a kind its type is not.
def codeProg (kind : CodeKind) (ty : LCTy) (fns : List Nat) : Prog :=
  { fnProg [] .unit .unit [(20, i32T), (21, i32T)] with
    fns := #[{ name := "main fn", params := [], ret := .unit, body := .unit },
             { name := "a", params := [20], ret := i32T, body := .var 20 },
             { name := "b", params := [21], ret := i32T, body := .var 21 }]
    codes := #[{ kind, fns, ty }] }
#guard accepts (codeProg .lam (.arr i32T (.ret i32T)) [1])
#guard refuses (codeProg .lam (.arr i64T (.ret i32T)) [1]) "c0: f1 (a) takes i32, for i64"
#guard refuses (codeProg .amp (.amp (.ret i32T) (.ret i64T)) [1, 2]) "c0: f2 (b) answers i32, for i64"
#guard refuses (codeProg .unit (.ret i32T) [1, 2]) "code of 2 functions"

end Backend2.LintTests

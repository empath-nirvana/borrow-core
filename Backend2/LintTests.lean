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
address each (`x10`, `x11` at `entryT`), at the closure type `kT`; `f0 (x0 : t, x1 : baseT) =
body`, answering `kT`; `main` makes `x0 = clos c0 [5]` and calls `f0 x0 7`, no task stack. -/
def handProg (body : Tm) (t : LTy := kT) (baseT : LTy := addrT) (kind : CodeKind := .amp)
    (entryT : LTy := addrT) : Prog where
  fns := #[{ name := "hands over", params := [0, 1], ret := kT, body },
           { name := "resume entry", params := [10], ret := .unit, body := .consume .dead 10 .unit },
           { name := "cancel entry", params := [11], ret := .unit, body := .consume .dead 11 .unit }]
  codes := #[{ kind, fns := [1, 2], ty := .amp (.arr .unit (.ret .unit)) (.ret .unit) }]
  main := .letv 3 (.lit (.i64 5)) (.letv 4 (.clos 0 [3]) (.letv 5 (.lit (.i64 7))
    (.call 0 [4, 5])))
  mainTy := kT
  ty := [(0, t), (1, baseT), (2, kT), (3, addrT), (4, kT), (5, addrT), (10, entryT),
    (11, entryT), (12, .unit)].foldl (fun m (x, t) => m.insert x t) {}

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

/-! ### `evConfined` [spec §71]

`f0 (x0 : i32; ev x1 : !(1 ⊸ F 1))`: an evidence parameter is read by a copy, or passed on as
evidence, and stays the caller's; put anywhere else (a pair, a closure's environment, a consume,
the function's value) it is refused, as is a closure call that drops the evidence its type takes. -/

/-- The type of the evidence under test: a persistent closure. -/
def evT : LTy := .bang closT

/-- `f0 (x0 : i32; ev x1 : evT) = body`, answering `ret`; `f1 (y0 : i32; ev y1 : evT) = y0` for a
call that passes evidence, `c0` a closure of `F 1` taking evidence for a closure call. -/
def evProg (body : Tm) (ret : LTy) (more : List (Var × LTy) := []) : Prog where
  fns := #[{ name := "user", params := [0, 1], evs := 1, ret, body },
           { name := "callee", params := [10, 11], evs := 1, ret := i32T, body := .var 10 },
           { name := "thunk", params := [20], evs := 1, ret := .unit, body := .unit },
           { name := "env", params := [30], ret := .unit, body := .consume .dead 30 .unit }]
  codes := #[{ kind := .unit, fns := [2], ty := .ev 7 evT (.ret .unit) },
             { kind := .unit, fns := [3], ty := .ret .unit }]
  main := .unit
  mainTy := .unit
  ty := ([(0, i32T), (1, evT), (10, i32T), (11, evT), (20, evT), (30, evT)] ++ more).foldl
    (fun m (x, t) => m.insert x t) {}

-- Read by a copy, the copy consumed: accepted, the parameter left unconsumed.
#guard accepts (evProg (.copy .dup 1 2 (.consume .dead 2 (.var 0))) i32T [(2, evT)])
-- Passed on as evidence to a call's evidence parameter: accepted.
#guard accepts (evProg (.call 1 [0, 1]) i32T)
-- Passed as the evidence of a closure call whose type takes it: accepted.
#guard accepts (evProg (.consume .dead 0 (.letv 3 (.clos 0 []) (.appE 3 none 0 [1])))
  .unit [(3, .thunk (.ev 7 evT (.ret .unit)))])
-- In a pair: refused.
#guard refuses (evProg (.pair 0 1) (.pair i32T evT)) "evConfined: the evidence x1 used other than as evidence"
-- In a closure's environment: refused.
#guard refuses (evProg (.consume .dead 0 (.clos 1 [1])) (.thunk (.ret .unit)))
  "evConfined: the evidence x1 used other than as evidence"
-- Consumed: refused.
#guard refuses (evProg (.consume .dead 1 (.var 0)) i32T) "evConfined: the evidence x1 used other than as evidence"
-- As the function's value: refused.
#guard refuses (evProg (.consume .dead 0 (.var 1)) evT) "evConfined: the evidence x1 used other than as evidence"
-- Copied at a rule other than `dup`: refused.
#guard refuses (evProg (.copy .const 1 2 (.consume .dead 2 (.var 0))) i32T [(2, evT)])
  "evConfined: the evidence x1 copied at the rule const"
-- A closure whose type takes evidence, run without it: refused.
#guard refuses (evProg (.consume .dead 0 (.letv 3 (.clos 0 []) (.app0 3))) .unit
  [(3, .thunk (.ev 7 evT (.ret .unit)))]) "evConfined: x3 run with no evidence where its type takes some"
-- A value passed as evidence that is not persistent: refused.
#guard refuses (evProg (.letv 4 (.prim (.alloc [i32T]) [0])
    (.letv 5 (.call 1 [0, 4]) (.letv 6 (.prim .free [4]) (.consume .dead 6 (.var 5))))) i32T
  [(4, .ref i32T), (5, i32T), (6, i32T)]) "evConfined: x4 passed as evidence at ref i32, which is not persistent"

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

end Backend2.LintTests

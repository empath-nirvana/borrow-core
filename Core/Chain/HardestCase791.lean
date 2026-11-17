import Core.Chain.Const791
import Core.Chain.SchedProgs
import Core.StepsN

/-!
# The hardest case of #791 as a closed program  `[spec §62]`

A field reborrow held across a park, then resumed (`HardestCase791`) or cancelled
(`HardestCase791C`), written in the spawn scheduler's programs.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.Goal791
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.LogRel (substAll)
open BoCa.BoLo (hndE hndVal freeE Kont performE opPayload)

/-! ## §5. The hardest case -/

open BoCa.Fig16.Tree.Wp.SchedProgs.Park (nP)
open BoCa.Fig16.Tree.Wp.SchedProgs.SpawnProgs (parkE spawnE cancelE progOf)
open BoCa.Fig16.Tree.Wp.SchedProgs.Spawn (qsS hsS)
open BoCa.Fig16.Tree.Wp.SchedProgs.Stack (stackRet)

/-- `let x = M in N`. -/
def letE (M N : Expr) : Expr := .app (.lam N) M

/-- `alloc e`. -/
def allocE (e : Expr) : Expr := .app (.val (.prim .alloc)) e

/-- The record's finaliser: `λr. let k = load r in free r; free k`. -/
def dRec : Val := Val.lam (letE (.app (.val (.prim .load)) (.var 0)) (letE (freeE (.var 1))
  (freeE (.var 1))))

/-- The reborrow's finaliser: `forget`. -/
def dFwd : Val := Val.lam (.val .unit)

/-- `x := v`. -/
def storeE (x v : Expr) : Expr := .app (.app (.val (.prim .store)) x) v

/-- The value task A writes through the field's borrow. -/
def vField : Val := Val.i32 7

/-- **The field's borrow, held across `park`, then written**: `λ_. λu. park; u := 7; forget u`. -/
def cbField : Val := Val.lam (.val (Val.lam (letE parkE
  (letE (storeE (.var 1) (.val vField)) (.app forget (.var 2))))))

/-- **A write through the record's borrow**: a fresh box stored in the record, the old one freed:
`let o = !v in let b = alloc () in v := b; free o`. -/
def writeRecE : Expr :=
  letE (.app (.val (.prim .load)) (.var 0)) (letE (allocE (.val .unit))
    (letE (storeE (.var 2) (.var 0)) (freeE (.var 2))))

/-- **The record's borrow**: `λ_. λv. writeRec v; let (v′, _) = withborF dFwd v cbField in
forget v′`. The field reborrowed is the fresh box's. -/
def cbRec : Val := Val.lam (.val (Val.lam (letE writeRecE
  (letE (.app (.app (.val (withborFV (.val dFwd))) (.var 1)) (.val cbField))
    (.letpair (.var 0) (.app forget (.var 1)))))))

/-- **Task A**: `c ↦ own(loc k) ● k ↦ own(())`; a `mut` lend of `c` (`withbor (2)`, unwinding,
at `park`'s row); through it a fresh box `k′` stored in `c` and `k` freed; then the field reborrow
of `k′` (`withborF`), held across `park` and written through after it; both ended; `dRec` frees
`c` and `k′`. -/
def taskA : Expr :=
  letE (allocE (.val .unit)) (letE (allocE (.var 0))
    (letE (.app (.app (.val (withborUV (.val dRec))) (.var 0)) (.val cbRec))
      (.letpair (.var 0) (.app (.val dRec) (.var 1)))))

/-- The value the other task writes through its borrow. -/
def vB : Val := Val.i32 5

/-- The other task's borrow: `λ_. λu. u := 5; forget u`. -/
def cbB : Val := Val.lam (.val (Val.lam
  (letE (storeE (.var 0) (.val vB)) (.app forget (.var 1)))))

/-- The other task's finaliser: `λr. free r`. -/
def dB : Val := Val.lam (freeE (.var 0))

/-- **The other task's body**, then `tail`: `park (); let a = alloc () in let (a′, _) =
withborU dB a cbB in free a′; tail`. Its cell is allocated and lent `mut` after its `park`, so
under `HS` (a spawned child runs first; `park` swaps with the top ready task) the lend opens and
ends while task A is parked. -/
def bodyB (tail : Expr) : Expr :=
  letE parkE (letE (allocE (.val .unit))
    (letE (.app (.app (.val (withborUV (.val dB))) (.var 0)) (.val cbB))
      (.letpair (.var 0) (letE (freeE (.var 1)) tail))))

/-- **The other task**: `bodyB ()`. -/
def thB : Val := Val.lam (bodyB (.val .unit))

/-- **The other task, then the canceller**: `bodyB (cancel ())`. When it cancels, task A is the
top ready task. -/
def thBC : Val := Val.lam (bodyB cancelE)

/-- The root: spawn `B` (`thB`), then run `A`. `B` runs first and parks; `A` runs to the `park`
inside the field's borrow; `B` resumes, opens its lend, writes, ends it and frees its cell; then
`A` resumes and writes through the field's borrow. -/
def rootMut : Expr := letE (spawnE thB) taskA

/-- The cancel variant: spawn `B` (`thBC`), then run `A`. As in `rootMut`, `B`'s lend opens and
ends while `A` is parked; then `B` cancels `A` while `A` holds the field's borrow. -/
def rootMutC : Expr := letE (spawnE thBC) taskA

def progMut : Expr := progOf rootMut
def progMutC : Expr := progOf rootMutC

/-- **The hardest case, resumed**: closed, under the spawn scheduler `HS`. -/
def HardestCase791 : Prop := OrDiverges (ℍ := ℍ) progMut

/-- **The hardest case, cancelled.** -/
def HardestCase791C : Prop := OrDiverges (ℍ := ℍ) progMutC

end BoCa.Fig16.Tree.Wp.Goal791

end

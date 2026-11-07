import Core.Chain.Field791N

/-!
# #791: the terms that discharge the compatibility lemmas' hypotheses  `[spec §62]`

`withbor2S_compat`, `withbor3S_compat` and `withborFS_compat` take the finaliser's semantic
judgment `hd` beside `Const791.OK`'s clauses. `ConstKW835N` instantiates each with every
hypothesis discharged, so none of them is vacuous (`withbor2S_inst`, `withbor3S_inst`,
`withborFS_inst`, the finalisers at `SemJN` by `dRelease_sem` and `dFree_sem`, the performing
callback by `cbPerform_sem`). This file holds the terms and `Const791.OK`'s instances:

* **The finalisers.** `dRelease = λr. ()` at `Mut @a A ⊸ 1`, the borrow left as garbage (Core's
  `releaseMut`); `dFree = λr. free r` at `Ref 1 ⊸ 1`, the cell freed.
* **A callback that performs an operation while holding the borrow** (`cbPerform`):
  `λ_. λu. perform op ()` at a one-operation suspending row (`linSig`), the borrow live across the
  stop.
* **`Const791.OK` inhabited** (`w2_ok`, `w3_ok`, `wF_ok`) at the hardest case's row
  (`hardestRow`, `park` as `TJN` types it), the bound Core's rules fix at the empty context
  (`LifeCtx.empty.meetOfDom`).

The finalisers are read semantically; `λr. ()` is not a `CDerives` term at `Mut @a A ⊸ 1` (the
judgment consumes a live `Mut` only through `forget`), so these instances discharge the compat
lemmas' hypotheses, not `Const791.OK`'s `CDerives` clause.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 defines_meetOfDom_empty)
open BoCa.BoLo (Head Kont performE opPayload freeE)
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg (noOwn_single_mut)

/-! ### The finalisers -/

/-- `λr. ()`: the borrow left as garbage. -/
def dRelease : Expr := .val (Val.lam (.val .unit))

/-- `λr. free r`. -/
def dFree : Expr := .val (Val.lam (freeE (.var 0)))

theorem dRelease_closed : closedAt 0 dRelease = true := by decide

theorem dFree_closed : closedAt 0 dFree = true := by decide

/-! ### A callback that performs while holding the borrow -/

/-- A must-resume operation `1 ↠^lin 1`. -/
def linSig (n i : UInt32) : OpSig := ⟨n, i, .lin, .unit, .unit, .ret .unit, false⟩

theorem linSig_suspend {n i : UInt32} (hn : n ≠ 0) (x : LifeVar) (bnd : Lifetime.Life) :
    Row.Suspend [linSig n i] x bnd := by
  intro o ho
  simp only [List.mem_singleton] at ho
  subst ho
  exact ⟨by simp [linSig], hn, id, id, .unit, .unit, fun h => by simp [capB, linSig] at h⟩

/-- `λ_. λu. perform op ()`: the callback stops at `op` holding the borrow `u`, and answers with
the operation's answer, the borrow released (left as garbage) at the return. -/
def cbPerform (n i : UInt32) : Val :=
  Val.lam (.val (Val.lam (performE (.val (opPayload n i Val.unit)))))

/-! ### `Const791.OK` inhabited, finaliser judgment included -/

/-- **`w2`'s antecedent holds**, its finaliser `free : Ref 1 ⊸ 1` derived by `CDerives.free` at
the payload `1`. -/
theorem w2_ok (x : LifeVar) :
    (Const791.w2 x LifeCtx.empty.meetOfDom .unit .unit hardestRow (.val (.prim .free))).OK :=
  ⟨defines_meetOfDom_empty, ⟨.top, fun _ _ => ⟨_, rfl⟩, .unit⟩, id, id, hardestRow_suspend x _,
    rfl, .free .nil⟩

/-- `dRelease` is Core's `forget`. -/
theorem dRelease_eq_forget : dRelease = BoCa.forget := rfl

/-- **`w3`'s antecedent holds** at the instance's constant, its finaliser `dRelease`, Core's
`forget`, derived by `CDerives.releaseMut`. -/
theorem w3_ok (a : Lifetime.Life) (x : LifeVar) :
    (Const791.w3 a x LifeCtx.empty.meetOfDom .unit .unit hardestRow dRelease).OK :=
  ⟨defines_meetOfDom_empty, id, id, hardestRow_suspend x _, dRelease_closed, .releaseMut .nil⟩

/-- **`wF`'s antecedent holds** at the instance's constant, its finaliser `dRelease` at
`Mut @a (Ref 1) ⊸ 1` derived by `CDerives.releaseMut`. -/
theorem wF_ok (a : Lifetime.Life) (x : LifeVar) :
    (Const791.wF a x LifeCtx.empty.meetOfDom .unit .unit hardestRow dRelease).OK :=
  ⟨defines_meetOfDom_empty, id, id, hardestRow_suspend x _, dRelease_closed, .releaseMut .nil⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end

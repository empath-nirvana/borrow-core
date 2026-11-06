import Core.Chain.Lend791N
import Core.HandledNames

/-!
# Only the scheduler catches a resuming operation performed under a live lend  `[spec §19, §27]`

`docs/new-core/scope-835-restriction.md`. A Kripke stop under a live lend at `A` chooses the floor
`A`, below the lender's (`ErwpK.lean`), so a handler that receives its `κ` as a value would get it
at a floor it does not know. The restriction keeps such stops away from every handler but the
scheduler at the program's top, whose clauses meet `SchedOKN`, a contract, not a typing.

`Sched` is the set of the scheduler's operation names (at `Goal791SchedN`, the scheduler's one
name `n₀`). The restriction has two parts, both read on the program and its constants, neither on a
rule of `CDerives`:

* **the lends' rows** (`Row.SchedOnly`): every resuming operation a lend's callback may perform,
  and so stop at under the live lend, is the scheduler's. Abortive operations owe no continuation
  and are unrestricted. A cancel row is not read: a continuation captured under a live lend is held
  only by the scheduler, whose cancel runs are at a table inside its own (`SchedOKNLe.fin`);
* **the program's handlers** (`Expr.HndAvoids`): the program, and each constant's finaliser,
  holds no handler frame of a scheduler name (`Expr.hin`, the frames a term holds). A `handle` whose
  name is not a literal may be of any name, so it is refused.

The interpretation (a later unit) reads `Sched` in the row's table: an entry at a name outside
`Sched` owes its continuation along `KW.OwedR` (`LendExit835N.lean`), `ExtR` at the share with no
floor, which is the order `vN`'s `U` reads; so `[handle]` at such a name receives `κ` at `U`.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.Tree.Wp.Goal791 (Const791)
open BoCa.Fig16.LogRel.Core.ClauseKinds (HIn)

/-- **A row whose resuming operations are the scheduler's.** -/
def _root_.BoCa.Fig16.LogRel.Core.Row.SchedOnly (Sched : UInt32 → Prop) (S : Row) : Prop :=
  ∀ o ∈ S, o.abort = false → Sched o.n

/-- **No handler frame of a scheduler name**, read off the frames the term holds
(`Expr.hin`, `Core/HandledNames.lean`): no `handle` at a scheduler name anywhere in the term, and
no `handle` whose name is not a literal (which may be of any name). `steps_frame_of_node` carries
it to every handler frame a run of the term reaches. -/
def _root_.BoCa.Expr.HndAvoids (Sched : UInt32 → Prop) (e : Expr) : Prop :=
  ∀ n, Sched n → ¬ e.hin.HasHnd n

/-- A constant's callback row. -/
def _root_.BoCa.Fig16.Tree.Wp.Goal791.Const791.row : Const791 → Row
  | .w2 _ _ _ _ S _ | .w3 _ _ _ _ _ S _ | .wF _ _ _ _ _ S _ | .wl _ _ _ _ _ S
  | .sm _ _ _ _ S _ => S

/-- A constant's finaliser (`withload` has none). -/
def _root_.BoCa.Fig16.Tree.Wp.Goal791.Const791.fin : Const791 → Option Expr
  | .w2 _ _ _ _ _ d | .w3 _ _ _ _ _ _ d | .wF _ _ _ _ _ _ d | .sm _ _ _ _ _ d => some d
  | .wl .. => none

/-- **A constant under the restriction**: its callback's resuming operations are the scheduler's,
and its finaliser has no `handle` at a scheduler name. -/
def _root_.BoCa.Fig16.Tree.Wp.Goal791.Const791.SchedOK (Sched : UInt32 → Prop) (c : Const791) : Prop :=
  c.row.SchedOnly Sched ∧ ∀ d, c.fin = some d → d.HndAvoids Sched

/-- **The restriction on a program**: its constants, and the program. -/
def Restrict835 (Sched : UInt32 → Prop) (cs : List Const791) (e : Expr) : Prop :=
  (∀ c ∈ cs, c.SchedOK Sched) ∧ e.HndAvoids Sched

/-! ### Scope -/

/-- A row of abortive operations alone (`Row.Unwind`'s rows) is under the restriction at every
scheduler. -/
theorem _root_.BoCa.Fig16.LogRel.Core.Row.schedOnly_of_unwind {S : Row} {x : BoCa.Lifetime.LifeVar} (h : S.Unwind x)
    (Sched : UInt32 → Prop) : S.SchedOnly Sched :=
  fun o ho ha => by rw [(h o ho).1] at ha; exact absurd ha (by decide)

/-- **The hardest case's row is the scheduler's**: `park` is `HS`'s operation. -/
theorem hardestRow_schedOnly :
    Row.SchedOnly (· = BoCa.Fig16.Tree.Wp.SchedProgs.Park.nP) Goal791N.hardestRow := by
  intro o ho _
  simp only [Goal791N.hardestRow, List.mem_singleton] at ho
  subst ho
  rfl

/-- The frames of `handle_n e with H`: a handler of `n`, then `H`'s and `e`'s. -/
theorem hin_hndExpr (n : UInt32) (qs : List Qual) (H e : Expr) :
    (hndExpr n qs H e).hin = HIn.one n ++ ((qualsVal qs).1.hin ++ H.hin) ++ e.hin := rfl

theorem hin_qualsVal : ∀ qs : List Qual, (qualsVal qs).1.hin = {}
  | [] => rfl
  | _ :: qs => by
      show ({} : HIn) ++ (qualsVal qs).1.hin = {}
      rw [hin_qualsVal qs]; rfl

/-- **A `handle` at a name outside the scheduler's is allowed** when its handler and its
computation are. -/
theorem hndAvoids_hndExpr {Sched : UInt32 → Prop} {n : UInt32} (hn : ¬ Sched n)
    (qs : List Qual) {H e : Expr} (hH : H.HndAvoids Sched) (he : e.HndAvoids Sched) :
    (hndExpr n qs H e).HndAvoids Sched := by
  intro m hm hh
  have hmn : m ≠ n := fun h => hn (h ▸ hm)
  have h₁ := hH m hm
  have h₂ := he m hm
  rw [hin_hndExpr, hin_qualsVal] at hh
  simp only [HIn.HasHnd, HIn.names_append, HIn.any_append, List.mem_append, Bool.or_eq_true,
    HIn.one, List.mem_singleton, hmn] at hh h₁ h₂
  simp_all

/-- **A `handle` at a scheduler name is refused**, whatever its clauses: `[handle]`,
`[handle]` with tail clauses and `[handle-last]` alike, since the term does not say which rule
typed it. -/
theorem not_hndAvoids_hndExpr {Sched : UInt32 → Prop} {n : UInt32} (hn : Sched n)
    (qs : List Qual) (H e : Expr) : ¬ (hndExpr n qs H e).HndAvoids Sched := by
  intro h
  refine h n hn (.inl ?_)
  rw [hin_hndExpr]
  simp [HIn.one]

end BoCa.Fig16.LogRel.Core.Chain.SI

end

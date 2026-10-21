# SuspSpike: lends held across a suspension, for restricted classes (#645)

`lake build SuspSpike`. Imports `Core` only. No `sorry`, no `axiom`; every theorem below has
`#print axioms` within `[propext, Classical.choice, Quot.sound]`. Definitions and the proof plan
are in `DESIGN.md`, written before the proofs.

## The idea

`wpG` is a bracket: from a run's start to its end, at a value or at a stop, the world update is
`↭` and the records proper are unchanged. A lend cannot stay open at a stop. Every class ends the
lend at the stop (6.65's exit reads no term) and lends again at the resumption. GhostEnd lends
again at a **fresh** lifetime, so the frozen continuation must be re-derived from its typing at the
new lifetime (`RBodyOfTyped`, not derived). This spike lends again at **the same lifetime, with the
cell the stop held**: the continuation gets back exactly the resource it stopped with, so the
borrower side is Core's relation, unchanged. That works when the resumption happens at a list with
the stop's members, because the cell stores `𝒱⟦T⟧` read at the list. A call-like operation, whose
every handler resumes in tail position, is resumed there.

## Results

| file | result |
|---|---|
| `Defs.lean` | the grade (`Grade`, a property of operations); `contShareC`, `opTableC`: Core's `opTable` with call-like stops owed only at lists with the stop's members; `CallRow` (class 1) |
| `Conservative.lean` | **conservativity**: `opTableC_none` (`opTableC T Grade.none = opTable T`, by `rfl`), `ewpTS_none`; `opTableC_of_opTable`, `ewp_grade` (every computation in Core's relation is in the graded one, at every grade) |
| `Scope.lean` | `wpG_sameMem`, `ewp_sameMem`: at a scoped table every answer is at a list with the start's members |
| `FrameAt.lean` | `wpG_M_frameAt`: `[TR]` 6.65 at `wpG` with the lifetime given, the callback run from the cell the entry builds, the exit reporting the cell's content (the printed proof of `wpG_M_frameX`, H4 replaced by its conclusions) |
| `Frame.lean` | `six27S` (6.27's stratum with the cell set aside, from 6.50 at one location); `wpG_viewStrat`; `ownerFrame`; **`frameAt`**, **`ewpTS_M_frameC`**, **`frameC`**: 6.65 over `ewpTS` at a class-1 table, the lend spanning every stop |
| `Handler.lean` | **`ewp_handleC`**: `ewp_handle_or` at graded tables, the handler's name call-like; `ewp_frame_call`; **`tail_hop`**: a tail clause `λ(x, κ). (λw. κ.1 w) (g x)` with `g` at a class-1 row meets the clause obligation |
| `Lend.lean` | **`withborC`**: the kernel's `withbor ℓ f` at a class-1 row, answering `𝒱⟦Ref T ⊗ B⟧`; **`withborC_core`**: the same from a callback in Core's own relation (so any `CDerives` body, by `fundamentalC`) |
| `Depth.lean` | non-vacuity at depth 3, every hypothesis discharged: `callRow_tabOf`, `argIn_tabOf`; `prog3_lends` (three nested lends of three owned cells, open across a call-like `perform`); **`prog3_sem`** (that program under three nested tail handlers, each clause performing the next name's operation, is in `wpTS` from the three owners) |
| `Stored.lean` | classes 2 and 3: `openCellStop_false` (keeping the lend open at a stop needs an update `↭` does not allow); `ext_adds_record` (`Ext` admits a resumption list `SameMem` does not); `not_resumeO_tick` (R1's rows exclude `tick`) |

## Verdicts

- **Class 1, call-like operations: the two new semantic obligations are proved**, for the `mut`
  lend of an owned cell (`withbor`, 6.65): the lend across call-like stops (`withborC`, from Core's
  or the graded relation of the callback) and the tail handler at graded tables (`ewp_handleC`,
  `tail_hop`). Uniform in depth: one induction on `ewpTS` per lend, one per handler
  (`prog3_sem`). Not built: the grade in Core's types, and so the relation clause and the
  compatibility lemma of every other rule at a graded row (listed in the report).
- **Class 2, linear stored `κ`: unknown.** The same-lifetime route needs the resumption at the
  stop's members; a stored `κ` is owed at every `Ext`-extension (`ext_adds_record`). The
  fresh-lifetime route is GhostEnd's `RBodyOfTyped`. The open-cell route needs an invariant beyond
  `↭` (`openCellStop_false`): that kill criterion fires for the route, not the class.
- **Class 3, affine stored `κ`: unknown**, as class 2.

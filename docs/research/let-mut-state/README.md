# `let mut`: targets and evidence (#611, #613)

- `targets/<name>.bc` beside `targets/<name>.core.bc`: a `let mut` program and the core its
  elaboration should be, written by hand. `check-targets.sh` runs both and compares the
  elaboration's erasure with the target's. A pair whose erasure matches is moved to
  `corpus/sugar/`, where the gate checks it (`mut-heads`, `mut-modify`). `targets/state/` holds
  the State-handler forms that check.
- `corpus/reject/state-*.bc`: the State-handler forms the checker refuses, pinned with their
  messages. `experiments/LetMutState` states the borrow case in Lean.
- `scripts/mut-combos.py`: the combination check of SPEC §41, a gate step.

## The pairs not yet met

Every surface program here answers what its target answers. What separates each elaboration from
its target, by the part of the elaboration it is in:

| target | what differs | where |
|---|---|---|
| `mut-for-acc`, `mut-shadow` | `count_try` with the start in the state and an exit test after it, where the target has `count_fold` from the start; the loop is bound and its state rebound, where the target is the loop in tail position | the counted loop (§16, `forData`) |
| `mut-while-flag` | a step function, a close and a constructor of the loop (`io_run_0`, `io_step`, `io_mk`), where the target has one `turn` | the state machine of a div body (§14, `mAssemble`) |
| `mut-block` | the copy takes the block's variable first, `ap__…((x, f))`, as §32's capabilities are taken, where the target has `ap__x(f, x)`; the copy's call of the block is bound and its pair rebound, where the target calls it in tail position; the parameter is bound again (`f <- return io_p0`) | §32's calling convention (a rule: the target, or the rule, is the user's choice), and the copy's body (§30) |
| `mut-await` | the parameter bound again (`tag <- return io_p2`), an operation's answer bound twice, the clause's continuation call and `main`'s handler bound before they are returned | a function's parameters (the parser), and effects' elaboration of operations, clauses and handler sites (§18, §19) |
| `mut-yield`, `mut-service` | the generator's machine and the `for`'s handler of it; the handler's copies | §15's generator sites, §18's copies |

None of these is the threading of `let mut`'s variables: the parts of SPEC §41 (resolution, the
writes, the hand-on of a frame) elaborate them as the targets do.

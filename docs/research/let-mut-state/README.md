# `let mut`: targets and evidence (#611, #613)

- `targets/<name>.bc` beside `targets/<name>.core.bc`: a `let mut` program and the core its
  elaboration should be, written by hand. `check-targets.sh` runs both and compares the
  elaboration's erasure with the target's. A pair whose erasure matches is moved to
  `corpus/sugar/`, where the gate checks it (`mut-heads`, `mut-modify`). `targets/state/` holds
  the State-handler forms that check.
- `corpus/reject/state-*.bc`: the State-handler forms the checker refuses, pinned with their
  messages. `experiments/LetMutState` states the borrow case in Lean.
- `scripts/mut-combos.py`: the combination check of SPEC §41, a gate step.

## The pair not yet met

`mut-for-acc`, `mut-shadow`, `mut-while-flag`, `mut-block`, `mut-await` and `mut-service` are met
(#618) and are in `corpus/sugar/`. `mut-yield` answers what its target answers; what separates
its elaboration from the target, by the rule it is in:

| what differs | where |
|---|---|
| the target runs the generator's code up to its loop when it is called, and starts at the loop's state; the elaboration starts at a state holding the parameter and runs nothing when called. The target is wrong here: at a row a body runs nothing when called (SPEC §14, *Moves*), which is what makes a call of a generator perform none of its operations. | §14 at a row; the target, to be corrected |
| with that start state, the loop's head is called by a forward move and by its own arm, so it is a function (`io_run_1`) and the call is the core's `force` of a variable | §14 *Moves*: a point a move calls has a function |
| a state of one variable is bound from the step's argument again (`fx_pp1 <- return io_a`) | §14 `mAssemble`: each point binds its tuple from `io_a`, one variable included |
| `yield(i);` binds its value `()` (`io_s0 <- return ()`) | the statement's binding (parser); the target, to be corrected: the statement's own value is `()` beside the threaded `sum` |
| the target's `for` handles the generator in one loop whose return clause runs what follows the loop (`inl sum`); the elaboration's `for` site is a loop of its own, which `main`'s machine observes as a call of a div function, with the join of the loop's ending and its exits (`io_j`, `io_jj`) after it | §15's `for` site and §14's call point: the target merges the code after the loop into the site's return clause, which a rest with a point of its own cannot be; and a loop with no exit still has an exit summand in its answer, which §16's `count_fold` rule does not yet have a §15 counterpart for |
| the site's clause binds the frame's variable from the payload by name (`sum <- return io_hw`), and the resume's argument (`io_wv <- return sum`) | §15's `for` site: the payload's variables are not bound by their pattern; the resume's argument is bound by the core's syntax (`M x` takes a variable) |

None of these is the threading of `let mut`'s variables.

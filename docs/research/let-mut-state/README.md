# `let mut` as `State`: targets and evidence (#611)

- `targets/<name>.bc` beside `targets/<name>.core.bc`: a `let mut` program and the core its
  elaboration should be, written by hand. `check-targets.sh` runs both and compares today's
  elaboration's erasure with the target's. `targets/state/` holds the State-handler forms that
  check; `targets/reject/mut-shadow-assign.bc` is #504, which should be refused.
- `corpus/reject/state-*.bc`: the State-handler forms the checker refuses, pinned with their
  messages. `experiments/LetMutState` states the borrow case in Lean.
- `scripts/mut-combos.py`: random nestings of `if`, `match`, `for`, blocks, shadowing `let`s and
  a resuming control operation, each assigning two `let mut`s, run once as written and once with
  the variables as `State` instances; it prints every program whose two runs answer differently.

# Freeze as a binder

"Freeze is a binder over internal locations, lifetimes and instances; resume and placement instantiate it." (user, 2026-10-04)

A frozen computation abstracts the names its state uses internally. Resume instantiates the lifetimes and instances fresh, beneath the resumer's own. Placement, meaning storing or moving the frozen value, instantiates its locations.

**What it unifies (hypotheses to check):**
- **Ghost-ending:** ending a lend at the stop and re-lending it fresh at resume is instantiation of a bound lifetime.
- **Pin:** a frozen value has no addresses, so its self-references move consistently with it. Placement fixes the addresses once: on the stack for a second-class continuation, in a box for a first-class one.
- **Staton's ν instances:** fresh instances at resume are the instance half of the binder.
- **D-ORD:** bound lifetimes are instantiated beneath the resumer's, so resuming inside a younger lend is rejected.
- **TwoRun's determinism up to renaming:** this is the location half.

**What it needs.** The relation, and the invariant extended to W, are equivariant under:
- bijections of locations and of instances;
- order-respecting renamings of lifetimes.

**The known risk.** Restrat's `mut_not_natural` refutes naturality at a stored Mut invariant, and whether it arises has not been checked.

**In the targets.** The binder is a target beside done (`EndStateBinder`, DESIGN §5 I2.c), not a conjunct of it: its location half is stated as a symmetry, its lifetime half as forward instantiation, OPEN pending the arising check.

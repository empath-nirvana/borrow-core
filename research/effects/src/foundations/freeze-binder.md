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

**The known risk.** Restrat's `mut_not_natural` refutes naturality at a stored Mut invariant. Whether its witness arises is still undetermined (see below).

**In the targets.** The binder is a target beside done (`EndStateBinder`, DESIGN §5 I2.c), not a conjunct of it: its location half is stated as a symmetry, its lifetime half as forward instantiation, OPEN pending the arising check.

## The lifetime half: what is proved (ProbeD1, `BINDER.md` §11, `GAP.md` §8)

These results are at ProbeD1's draft W, at the `binder0` placement. Nothing in `Core/` and no printed definition changed. All verifiers passed.

- **Internal lifetimes.** A lifetime is internal when it lies strictly below the stack's cut, the point just above its outermost lend (`Internal`, `InternalVar`). Every `Δ` variable whose bound reaches below a stack variable is internal (`internalOfBound`), and every internal variable is a stack variable or was bound inside the outermost lend (`InternalBoundInside`). An instantiation moves them, fresh and beneath the resumer's lifetimes, preserving every `⊏` among them and to external lifetimes. It fixes every external reading (`SubOutsideInst`, `SharedReadFixed`). Fresh instantiations exist (`InstFreshExists`), and instantiations compose (`InstComp`).
- **Models.** An instantiation keeps `Δ`'s models with no condition on `Δ` (`instModels`, `reLendModelsI_of`). The configuration typing reaches, where `'1 ⊏ '0` sits under a lend of `'0` (`q2_reached`), is kept (`q2Inst`). This is D-ORD's half of the binder.
- **Ghost-ending as instantiation.** The re-lend at a resume is the instantiation. With `PlaceViews` in the guard, the four `U` introductions and the context's thaw are proved at `binder0` at the revised relation `vRLJ`, at every borrow payload type, for contexts whose only excluded slots are `μ` and `fam` slots outside a payload (`statement0UThawFreeKJ`, `GAP.md`).
- **Equivariance, in part.** The guard is kept by an instantiation (`GuardInst`). Coherence moves with its record when the outermost lend is below `⊤` (`cohE_inst`). Type equality is kept at every type (`tyEqInst`, `GAP.md` §2), and under every order embedding fixing `⊤` (`tyEqRoomBlind`): `TyEq` compares lifetimes only for equality, so a lifetime in the instantiation's gap behaves at each threshold like one that exists. The relation itself is not invariant under a gap-opening embedding: Core's printed ℕ-`∀` reads adjacency (`coreAllAdjacent`, `coreAllNotNatural`).
- **The position-`∀`.** Quantifying over the cuts below the stack's cut, each realised by an instantiation (`AllPosJ`), is transported along instantiations (`allPosJTransport`) and is Core's clause at `σ = []` both ways (`allPosJNil`). W's `U` clause implies it for the body at a `U (∀…)` type (`wU_allPosJ`, one way), so the thaw at a `U` slot never meets the adjacency effect. It is not adopted at `cRLJ`'s own `∀`; no statement needs it there yet.
- **Where naturality fails, as a fact about our statement.** At a retained `Mut` cell whose payload type reads an internal lifetime, the instantiation can break the stored predicate's support (`not_mutPayloadInst`). That is `mut_not_natural`'s mechanism. It is excluded by an added hypothesis (`RetainedPay`: a retained cell's payload reads only external lifetimes), which the rows that make `Mut` or `Imm` values still owe. Whether such a cell arises is undetermined. At a view slot the instantiation rebuilds the view and does not meet the witness (`mutWitnessThaws`).

## R1 and `binder0`'s monotonicity (ProbeD1, `R1MONO.md` §8)

The draft relation is now `vRLM`, which reads `μ`, `fam` and type variables itself. Nothing in `Core/` and no printed definition changed. The hygiene review passed; the content review raised two major findings (ProbeD1 `CHECKPOINT.md`, warning box), reflected here.

- **R1 is closed at `binder0`.** A thunk inside a `μ` value is now read by W's `U` clause, so the thaw never meets Core's ℕ-`∀` there. The thaw holds at every type by induction on the data (`relendMValueE`), and the four `U` introductions at every context (`statement0UFullM`). The cost: `vRLM` is strictly smaller than Core's relation at `μ` (`muAdjNotVRLM`), and the unroll row owes `vRLM`'s substitution lemma (`VRLMUnroll`), not attempted.
- **`OuterBelowTop`** holds at every lend and across the arising set (`outerBelowTopArises`), from [TR] 6.64/6.65 H4's consequence, now recorded in the draft `LendMutI`/`LendImmI`.
- **`RetainedPay`** is proved at the view, the transports and `∀E` at an instance with no join whose variable no stack entry names. At a bound `Mut` read-out it stops at `EntryPayLeaves`. The `mut_not_natural` risk is still where it was: whether a retained internal-payload cell arises is not checked.
- **`KeepsT`** at the share is proved from `LineageUnique`, which is not derived.
- **Monotonicity.** Unrestricted `MonoOwnG`, `MonoG`, `MonoV` at `vRLM .binder0` are refuted at `gd`, not shown to arise. The `∀I` row is proved at contexts reaching no `U` (`allIRowMNKUFree0`). The handler's `MonoHide` at `vRLM` is not stated.

**Still open for the lifetime half:** the `∀I` row at a `U` slot and at binder-named indices; `MonoHide` at `vRLM`; whether monotonicity has consumers beyond the `∀I` row and `MonoExtM` [unchecked]; `VRLMUnroll`; `EntryPayLeaves`; `LineageUnique`; whether `withload` at two side-by-side references meets `loadGuardFails2` [unchecked]; `ViewSlotInst` without `OuterBelowTop`; the arising check of a retained internal-payload cell (`InternalPayloadArises`); the instance and location halves, which no unit has touched.

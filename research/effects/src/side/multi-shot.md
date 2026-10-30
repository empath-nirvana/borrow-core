# Side question: multi-shot

> **Not a goal.** Multi-shot is ignored as a design goal (decision 63): "If it works it works, if it doesn't, it doesn't." This chapter exists only to record exactly whether multi-shot is hard or impossible here, and why. Nothing in it blocks, shapes or costs anything in the properties, the spec or the implementation. On friction, `unr` is restricted or removed.

## What multi-shot means here

A multi-shot continuation can be resumed more than once. In our kernel this is the `unr` qualifier, written `multi ctl` at the surface (SPEC §19).

## What we already know

- **The kernel already enforces the capturing condition.**
  - An `unr` continuation is typed `!U(…)`.
  - Its share in `contShare` must be the empty resource (`Core/EffDefs.lean:144–149`).
  - `[let]` requires `Ctx.Banged Γ₂` when the row has an `unr` operation (`Core/EffRules.lean:897`).

  So a multi-shot continuation can capture only persistent data, with no owned resources and no `Mut` lends. This is the survey's A3, the capturing condition of Affect and Tang et al., and it holds at Core σ=[] as built.
- **A law fails** (SIB). `nu_op_fails_multishot` (`experiments/EffModelRel/EffModelRel/Examples.lean:223`): Staton's ν/op law, which lets a fresh instance commute with an operation, fails for unrestricted operations, because one fresh instance is shared by both branches. The law holds for must-resume and cancellable operations.
- **The literature** (survey A3, P1):
  - resuming twice duplicates `&mut` and owned values;
  - regions are exited twice (Yarrow);
  - for borrow checking, the resume edge becomes a loop back-edge, which needs a fixed point.

## Why, in our terms (hypotheses to check)

- **Resources are linear.** Duplicating a continuation duplicates whatever resource it holds, so the only sound multi-shot continuation holds none. That is exactly the restriction the kernel already imposes. Within it, multi-shot over persistent data, such as backtracking `choose` over pure values, looks sound as built.
- **Under freeze-as-binder,** resuming twice instantiates the binder twice. Bound lifetimes and instances can be instantiated fresh each time. Bound locations would need their contents copied, which is a clone, so this works only for clonable contents. Borrows into outer locations duplicate as `Imm` but never as `Mut`.
- **Spanning lends (tier 2)** and multi-shot do not mix: a lend held across a stop is a resource, so an `unr` continuation cannot hold it.

## Open, as side questions only

- Does `nu_op_fails_multishot`'s counterexample arise in the kernel, or only in the sibling calculus?
- Does restricting multi-shot to persistent captures cost any law we want for must-resume and cancellable operations? The evidence so far says no.
- `corpus/pending/backtrack-multishot.bc` stays pending.

**The current answer:** multi-shot over persistent data is possible as built. Over resources it is impossible by linearity, and that is fine.

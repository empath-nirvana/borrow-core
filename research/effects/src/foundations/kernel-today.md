# What works today

borrow-core has a working, proved effect kernel at Core σ=[], meaning the kernel relation at the empty lend stack. The full inventory is [`docs/effects-state/01-kernel.md`](../../../../docs/effects-state/01-kernel.md).

**The kernel**
- **Machine:** six primitives (`perform`, `raise`, `hnd`, `ubind`, `ccatch`, `cfin`) plus `boundedFix`. Handlers are deep, and determinism holds with effects.
- **Types:** operation layers with qualifiers `lin`, `aff` and `unr`, and rows of them.
- **Typing:** `[sub]`, `[perform]`, `[raise]`, `[let]`, `[then]`, `[handle]`, `boundedFix`, and six unwinding borrow constants.
- **Semantics:** one generic `opTable`, and `ewpTS` as a least fixed point over `wpG`. Handler soundness is `ewp_handle`.

**The theorems:** `fundamentalC`, `adequacyD` and `adequacyD_obs`; leak freedom (`NoOwn` and `reclaim`); both cancel outcomes; ten acceptance programs.

**The toolchain:** surface stages 1–3 compile and run, and handling is erased (a call, a branch, or a state machine).

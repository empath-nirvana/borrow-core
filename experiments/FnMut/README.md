# FnMut — the affine closure as codata

**Question** (#236). Can a closure that owns or captures mutable or linear state be called many
times, each call borrowing that state, with its environment hidden by its type: Rust's `FnMut`?

**Answer.** Yes, as an abbreviation over `νX. C`, once `ν`'s positivity admits an observation
with an argument and a boxed rest:

    FnMut^c A B  ≜  νX. (A ⊸ F(B ⊗ [@c] U X)) & F 1

It needs no new former, no new rule and no new index. The design, the requirement-by-requirement
status and the kernel change are in [`docs/fnmut.md`](../../docs/fnmut.md).

Build: `lake build FnMut`. Non-default; nothing imports it. Every declaration's axioms are within
`[propext, Classical.choice, Quot.sound]`; there is no `sorry`, `axiom`, `native_decide`,
`implemented_by`, `opaque`, `partial` or `unsafe` outside comments.

## The fork

`FnMut/Core/` is `Core`'s import closure (the modules `Core.Fundamental`, `Core.Dtor` and
`Core.Steps` need, plus `Splits.lean` and `Weaken.lean`), copied at `620c82c` with `import Core.X`
renamed to `import FnMut.Core.X`. The namespace stays `BoCa.Fig16.LogRel.Core`, so nothing may
import both. The branch's first commit is the verbatim copy, and the relaxation is a later
commit. [`kernel.patch`](kernel.patch) is that diff against `Core/`, plus one proof arm in
`Frontend/Check/Decide.lean`; with it applied, `lake build Core Frontend Backend bcc` succeeds:

| file | change |
|---|---|
| `Types.lean` | `NuLeaf` admits `A ⊸ D` with `A` closed; `instT` passes through it; `VTy.Poly` admits `[@a] B` |
| `Relation.lean` | `cB`'s clause at `A ⊸ D`: `cC`'s `⊸` clause, the argument read without the environment |
| `RelationFacts.lean` | `cB_congr`, `cB_tyEq`, `CTyEq.nuLeaf_iff`, `TyEq.poly_iff` at the new shapes |
| `NuRel.lean` | `cB_mono`, `cB_unroll` at `A ⊸ D` |
| `Computation.lean` | `sSB`, `cB_iff_stacks`, `cB_step`, `cB_bind` at `A ⊸ D` |
| `Nu.lean` | coiteration: `nodeV`, `childA`, `node_ok` at `A ⊸ D`; `mapV`, `map_ok` at `[@a] B` |

## The experiment

| file | contents |
|---|---|
| `Types.lean` | `fnBody`, `fnMutT`, `fnBox`; `fnBody_nuOk`; the relation clause `cC_fnMut_iff`, `fnMut_coind`; the observable view and `Imm̲` (`vC_obs_fnMut`, `immReborrow_fnMut`, `obs_transfer_fnBox`); `hasDtor_fnMut`, `not_affine_fnMut`, `not_persistent_fnMut`, `not_hasDtor_lolli`; `fnBody_nuOk_higher`, `fnEffBody_nuOk` |
| `Kit.lean` | `partP` splits and their wrappers, copied from `Core/IntPrograms.lean` |
| `Rules.lean` | derived rules: `d_mk`, `d_mkBox`, `d_call`, `d_close`, `d_callMut`, `d_fromFn`, `d_once` |
| `Counter.lean` | `counterStep`; `counterProg`, a counter called twice through a `Mut` borrow (`4`); `scopeProg` |
| `Programs.lean` | `fromFnProg` (`23`), `onceProg` (`5`), `dropProg` (`0`), `nestProg` (`8`) |
| `Passing.lean` | `passF n` at every depth, with a reborrow (`d_passF`); `passProg 3` (`13`) |
| `Capture.lean` | `retProg` (`15`); `logProg`, a logger capturing `Mut 'x I32` (`12`); `logState_not_outlives`, `fnMut_not_outlives` |

Each program has `*_derives` (one closed `CDerives` derivation), `*_runs` (adequacy at every
host: a run from the empty memory to a 32-bit literal and the empty memory) and `*_eval` (the
interpreter at Wasm's host, by `decide`).

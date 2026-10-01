# SecondClass: second-class closures, System C, and capability-indexed prompts

Design note: `docs/second-class-and-system-c.md`. Issues #229, #216, #161.

**Build.** `lake build SecondClass`. The library is non-default, imports `Core` (and
`Core.EffPrograms`, `Core.Examples` for helpers), and nothing imports it. No `sorry`, `axiom` or
`native_decide`; every `#print axioms` is within `[propext, Classical.choice, Quot.sound]`.

| file | contents |
|---|---|
| `SecondClass/Restated.lean` | `bounded_fix` with a passed environment (`boundedFixEnv_compatX`) and at a record of functions (`boundedFixRec_compatX`, `boundedFixEnvRec_compatX`): instances of `boundedFix_compatX`; `envStepTy_persistent` |
| `SecondClass/RecLog.lean` | probe P1 at the judgment: a recursion that runs an answering operation on a capability passed through its argument, `c : Mut @a I32 ⊢ recLogE : F (Mut @a I32 ⊗ 1)` (`recLog_derives`), sound by `fundamentalC` (`recLog_sem`) |
| `SecondClass/AbortClause.lean` | #216 for abortive operations as a derived rule: the clauses capture any context and run after the handler (`d_handleAbortCapture`, `handleAbortCapture_sem`) |
| `SecondClass/Prompts.lean` | handling at a name chosen at run time is sound given freshness for the prompts in scope (`handleAt_compatC`); a fresh name exists (`fresh_exists`) |

**Probes** (`probes/*.bc`), hand-written core, each accepted by the certifying checker
(`bcc check`) and run to its answer with `live 0` at the source, `clos` and `flat` stages and
compiled (`bcc run`):

| probe | shows | answer | counts (alloc, indirect, copies) |
|---|---|---|---|
| `p1-rec-log.bc` | an answering capability through a recursion | 6 | 1, 0, 0 |
| `p2-rec-yield.bc` | `yield` before and after the call of itself, `exhausted` at a spent budget, no `rec` site | 165 | 6, 0, 0 |
| `p3-rec-loop.bc` | `bounded_fix` at a loop type: a loop in each level | 0 | 102, 35, 0 |
| `p4-clause-captures.bc` | a parameterized handler over an owned cell and a capability; an abortive clause run after the handler | 170 | 5, 3, 0 |
| `p5-two-blocks.bc` | System C's two blocks sharing one stateful handler, state behind control | 1 | 0, 3, 0 |
| `p6-rec-record.bc` | mutual recursion with different result types, at a record | 1 | 0, 0, 0 |
| `p7-shared-budget.bc` | one depth budget across nested recursions, carried as an argument | 10 | 0, 0, 0 |
| `p8-layer.bc` | a counting layer as a generator transformer | 1505 | 1, 0, 0 |

    for p in experiments/SecondClass/probes/*.bc; do .lake/build/bin/bcc check $p && .lake/build/bin/bcc run $p; done

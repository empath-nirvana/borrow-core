# The register

This is the global view, one row per property. **Status** uses the words defined in the [Introduction](intro.md). **Rests on** names the existing Lean a property builds on. **Depends on** names other properties.

| # | property | status | best evidence (world) | depends on | next step |
|---|---|---|---|---|---|
| P1 | [Soundness](properties/soundness.md): every run is safe, effect-safe and leak-free, with finalisation on cancel | proved at σ=[] for today's rules | `fundamentalC`, `adequacyD`, `adequacyD_obs` (Core σ=[]) | P2–P10 at W | state the target in Lean, over the platform |
| P2 | [Effect safety](properties/effect-safety.md) | evidence | `adequacyD` at `F_∅ 1` with `ewp_bot` (Core σ=[]); no named theorem | P1 | name it; check the row algebra against the Yoshioka conditions |
| P3 | [I1: a suspension is a value](properties/i1-suspension-value.md) | evidence | `ewp_gen` (lift-stage1, Core σ=[]); Aff as ν codata | P9 | state the semantic type of a suspension |
| P4 | [I2: capture and resume preserve the invariant](properties/i2-capture-resume.md) | evidence | GhostEnd spanning instances (Core σ=[]); WorldW resource-level hand-on (probe) | P9, P10 | state it as equivariance under freeze-as-binder; check whether Restrat's counterexample arises |
| P5 | [I3: drop finalises exactly once](properties/i3-drop.md) | evidence | `cancelTab`, `ewp_kappa_cancel`, `Core/EffCancel.lean` (Core σ=[]) | P8 | state finalisation exactly once as a theorem |
| P6 | [I4: answering effects are borrows](properties/i4-answering-borrows.md) | evidence | `translate_typed`, `handle_is_shift`, `effect_safety` (PAPER) | P2 | relate to `hnd` in Core (OQ-1) |
| P7 | [I5: the capture laws](properties/i5-capture-laws.md) | evidence | β, η and hiding in EffModelRel (SIB) | P11 | state them unarily over the kernel |
| P8 | [Continuation linearity](properties/continuation-linearity.md) | evidence | qualifiers `lin`/`aff`, `contShare`, `KapRel` (Core σ=[]) | — | state "used as typed" as a theorem |
| P9 | [Lifetime soundness](properties/lifetimes.md) | evidence | 6.60 `vC_outlives`, `Row.Unwind`, `ewp_box_end` (Core σ=[]) | — | outlives at `U C` (OQ-28) |
| P10 | [Exclusivity across the handler](properties/exclusivity.md) | evidence | TW/`TW.inv`; WorldW `entryRecorded_mut` (probe) | P4 | the invariant over 6.65 and 6.66 cells at a stop |
| P11 | [Handler correctness](properties/handler-correctness.md) | evidence | `ewp_handle` (Core σ=[]); laws in EffModelRel (SIB) | P1 | initiality and the unary laws over the kernel |
| P12 | [Abstraction safety](properties/abstraction.md) | open | none in Core | P11 | decide whether it is in scope (it is binary) |
| P13 | [Zero-cost lowering](properties/zero-cost.md) | evidence | the erased lowering, which compiles and runs; corpus counts | P11 | decide whether lowering correctness is a theorem (OQ-23) |
| P14 | [Well-bracketing conservativity](properties/conservativity.md) | proved for tier 1 by construction | T1, the lexical stop (`Core/EffDefs.lean:40`) | P4 | state what tier 2 gives up, and for which classes |

**Next by the rule.** P4, I2. P5, P10 and tier 2 depend on it, and it carries the largest unknown. Its first step is to state it in Lean as equivariance, then check whether Restrat's `mut_not_natural` arises.

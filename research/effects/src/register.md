# The register

This is the global view, one row per property. **Status** uses the words defined in the [Introduction](intro.md). **Lean target** names the property's statement in `experiments/Targets` and its status there (`Targets/Status.lean`). **Rests on** names the existing Lean a property builds on. **Depends on** names other properties.

| # | property | status | Lean target (`experiments/Targets`) | best evidence (world) | depends on | next step |
|---|---|---|---|---|---|---|
| P1 | [Soundness](properties/soundness.md): every run is safe, effect-safe and leak-free, with finalisation on cancel | proved at σ=[] for today's rules | `Soundness`, `SoundnessContracts`, `ReleasedOnceAll`: return conjunct proved at `Platform.none` (Core σ=[]); `ReleasedOnceAll` proved at every typing system; the rest open | `fundamentalC`, `adequacyD`, `adequacyD_obs` (Core σ=[]) | P2–P10 at W | adequacy across platform answers and for driven loops at σ=[] (`Soundness tier1`) |
| P2 | [Effect safety](properties/effect-safety.md) | evidence | `EffSafe`: proved at σ=[]; T0 `RowAlgSafe`, `RowLink`: proved at the minimal row form | `adequacyD` at `F_∅ 1` with `ewp_bot` (Core σ=[]); no named theorem | P1 | the row form the kernel adopts (OQ-13), and `EffSafe` at W |
| P3 | [I1: a suspension is a value](properties/i1-suspension-value.md) | evidence | `I1`: proved at σ=[] | `ewp_gen` (lift-stage1, Core σ=[]); Aff as ν codata | P9 | I1 at W |
| P4 | [I2: capture and resume preserve the invariant](properties/i2-capture-resume.md) | evidence | `I2`: proved at σ=[] at abortive rows; `FreezeBinder` (beside done) and `NotVDenNaturalArises`: open | GhostEnd spanning instances (Core σ=[]); WorldW resource-level hand-on and exit; Core embeds into the draft (probe) | P9, P10 | check whether Restrat's counterexample arises (`NotVDenNaturalArises`); I2 at resuming rows |
| P5 | [I3: drop finalises exactly once](properties/i3-drop.md) | evidence | `I3`: proved at σ=[] (nothing held); `NoInterception`: proved at σ=[]; `FinaliserOrder`: open | `cancelTab`, `ewp_kappa_cancel`, `Core/EffCancel.lean` (Core σ=[]) | P8 | `FinaliserOrder tier1` |
| P6 | [I4: answering effects are borrows](properties/i4-answering-borrows.md) | evidence | `I4a`: proved for tier 1 at abortive rows; `I4Typing`, `I4c`: open | `translate_typed`, `handle_is_shift`, `effect_safety` (PAPER) | P2 | relate to `hnd` in Core (OQ-1) |
| P7 | [I5: the capture laws](properties/i5-capture-laws.md) | evidence | `I5`: proved at σ=[] | β, η and hiding in EffModelRel (SIB) | P11 | I5 at W |
| P8 | [Continuation linearity](properties/continuation-linearity.md) | evidence | `P8a` (= `ReleasedOnceAll`): proved at every typing system; P8.b: named-only | qualifiers `lin`/`aff`, `contShare`, `KapRel` (Core σ=[]) | — | how a continuation's use is observed (OQ-50) |
| P9 | [Lifetime soundness](properties/lifetimes.md) | evidence | `LifetimeSound`: proved at σ=[] | 6.60 `vC_outlives`, `Row.Unwind`, `ewp_box_end` (Core σ=[]) | — | outlives at `U C` (OQ-28) |
| P10 | [Exclusivity across the handler](properties/exclusivity.md) | evidence | `Exclusive`: proved at σ=[] | TW/`TW.inv`; WorldW `entryRecorded_mut` (probe) | P4 | the invariant over 6.65 and 6.66 cells at a stop |
| P11 | [Handler correctness](properties/handler-correctness.md) | evidence | `P11`: proved at σ=[]; `Laws` (binary): open | `ewp_handle` (Core σ=[]); laws in EffModelRel (SIB) | P1 | initiality and the unary laws over the kernel |
| P12 | [Abstraction safety](properties/abstraction.md) | open | `Abstraction` (binary): stated, open | none in Core | P11 | decide whether it is in scope (it is binary) |
| P13 | [Zero-cost lowering](properties/zero-cost.md) | evidence | `LoweringCorrect`, `ZeroCost`: named-only | the erased lowering, which compiles and runs; corpus counts | P11 | decide whether lowering correctness is a theorem (OQ-23) |
| P14 | [Well-bracketing conservativity](properties/conservativity.md) | proved for tier 1 by construction | `WBCore`: proved; `ConservativeWB`, `Conservative`: proved at σ=[] | T1, the lexical stop (`Core/EffDefs.lean:40`) | P4 | state what tier 2 gives up, and for which classes |

**Not tracked:** multi-shot. It is ignored as a design goal. The side question of whether, and why, it is hard is recorded in [Multi-shot](side/multi-shot.md).

**Next by the rule.** P4, I2. P5, P10 and tier 2 depend on it, and it carries the largest unknown. It is stated in Lean (`Targets.I2`, with the lend frames at W and the spanning borrows as its own conjuncts, and the freeze binder as a target beside done) and proved at σ=[] at abortive rows. Its next step is to check whether Restrat's `mut_not_natural` arises (`Targets.NotVDenNaturalArises`).

# System B: the borrow calculus

System B is BoLo (Wagner et al., OOPSLA 2025), as transcribed in `Core/` and `Paper/`. Its guarantees are given, not researched here. [`experiments/Targets/RESTRUCTURE.md`](../../../experiments/Targets/RESTRUCTURE.md) §2 states each as a Prop over a typing system and a borrow world `BWorld`, which has borrow fields only (`Targets/B/*`). Each is proved at BoLo by citation:

| | guarantee | where it is proved |
|---|---|---|
| B0 | BoLo's programs stay typed | `CDerives`, one constant per borrow axiom |
| B1 | fundamental property ([TR] 6.151) | `fundamentalC` (`Core/Fundamental.lean`); `Paper/S6_8` |
| B2 | adequacy: every run safe, ending in empty memory ([CONF] 3.2, 3.3) | `adequacyC`, `adequacyD` (`Core/Demonic.lean`) |
| B3 | no use after free, no double free | `adequacyD_safe` |
| B4 | leak freedom | `NoOwn` and `reclaim` |
| B4′ | B3 and B4 with externs meeting their contracts | from B1 and B2 |
| B5 | release exactly once, location reuse included | from B4′, given the step-for-step simulation (OQ-43) |
| B6 | exclusive mutable borrows | the typed world `TW`, `TI`, `TW.inv` (`Core/Invariant.lean`); 6.65 and 6.66 |
| B7 | lifetimes respected | 6.60 (`vC_outlives`) |

The machinery behind them is described in [The BoLo machinery](foundations/bolo.md).

**The first rule** is that System B's guarantees still hold in the composite: "NOTHING CAN BREAK THE BORROW CALCULUS." In Lean that is `B.Guarantees`, a conjunct of the combined theorem. This is about the guarantees, not BoLo's text: "You can't add an effect system without changing it. They interact." Changes to B's definitions where it interacts with A, such as the stop condition and `↭`, belong to [the interaction](interaction.md). Each comes with the obligations that re-establish B's guarantees.

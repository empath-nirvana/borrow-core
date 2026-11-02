# #770: every condition and gap introduced so far (2026-11-01)

Classes: SEMANTIC (programs genuinely need it; justified) · PROOF (added to make a proof close; must be removed or justified) · GAP (unbuilt) · RISK (could break later).

| # | Item | Class | Status |
|---|---|---|---|
| 1 | No unrestricted (multi-shot-capable) ops under a live borrow/owned resource | SEMANTIC | Justified: κ owns the folded cell; copying lends twice, dropping leaks (`unr_share_no_own`). Restricted multi-shot over duplicable state is a separate opening. |
| 2 | `wc = sameW`: κ resumed at same frame records | PROOF | REMOVED (reb-canon 75b298b8): replaced by `extF` (records named by frozen locations kept) + global `LinDisj`; all frame rules, imm answer and handler-lends-and-resumes tests pass. `Ext → extF` at typed worlds PROVED (`ext_extF`, 5cc03032): no restriction relative to Core. |
| 3 | PA ∈ Res_A, PB ∈ Res_{↓A} (mut lend); PB ∈ Res_A (imm lend, 6.64 H11) | PROOF? | Expected from closed operation types; not derived. |
| 4 | PA/PB stable along Ext (imm lend) | PROOF? | Printed 6.64 asks the same of Q; not derived for ops. |
| 5 | Anti-Frame guard (CellFold): withswap with a callback that suspends | PROOF/GAP | Supplied for withbor3; withswap-with-stop not derived. |
| 6 | Finalisers that raise (cancel error only `none`; cferr/creraise) | GAP | Not covered since stage 1. |
| 7 | `[handle]` without hdv needs ops must-resume or cancellable (hE) | SEMANTIC? | Same reason as 1; check against unrestricted ops with nothing live. |
| 8 | Canonical images: TW → TWNC conservativity lost | RISK | All of Core must be re-proved at TWNC; 4 world-building sites without counterparts. |
| 9 | Div tick table (Px) mapping | GAP | Ticks are ordinary must-resume entries. |
| 10 | Termination: step-indexed relation proves safety only; totality results only for derivations not using the new [handle] | DESIGN | Matches target (progress-or-no-leaks); needs a stated story. |
| 11 | 𝒱/𝒞 for every type, fundamentalC, adequacy | GAP | Not started. The real test of 3, 4, 7, 8. |
| 12 | Core gaps found: inline-field projection rule; value-type polymorphism; arrays/foldImm across stops | GAP | Separate from #770 but needed for the field-borrow use case. |
| 13 | Recorded unreconciled point on 6.150 (`wp_reborrow_unreconciled_at_split_view`) | RISK | Untouched. |
| 14 | Lowering: self-referential state machines (Pin/movability), per-state drop glue | GAP | Scope doc not written. |

## Parked idea (not in any brief)
Lifetimes on continuation/task types (`Task@a`; stores of `@a` continuations must stay within `a`), as Rust's `Future + 'a` and Schuster et al.'s region-typed continuations. Hypothesis: may subsume `sameW`/`ExtK` and the PA/PB conditions as one typing rule, and give scoped spawn for cross-task. Kept out of the stops-redesign spike on purpose; revisit after it reports.

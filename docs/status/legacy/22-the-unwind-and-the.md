
The unwind and the cancel (§19 *Laws* items 5 and 6) are stated of Core's machine in
`Core/EffCancelRuns.lean`, with no change to `CDerives`, the machine or the relation. Read
prefix-closed over paths (`Path`): `unwind_prefix` (`UnwindTr`) and `cancel_prefix` (`CancelTr`),
at finalisers typed at rows of abortive operations (`FinRow`, `finAlone_of_finRow`,
`finOK_of_finRow`). On complete runs: `finaliserOrder_at` and `finaliserOrder_A` (`CancelRun`,
`UnwindRun`, `FinaliserOrder`), given `FinAloneAt`.

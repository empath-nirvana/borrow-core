
Frame deadness (*Cancels*, decision D1 of 2026-10-08) is implemented: the dead region `Kont.dead`,
`κ`'s cancel branch, the cancel state of the kept error alone and `[cfin-cancel]` in
`Paper/S3_Dynamics/Definitions.lean`; the interpreter; unique decomposition and determinism with
`[cfin-cancel]` in `Core/Steps.lean`; `cancelOwed` at the dead region and the empty error table in
`Core/EffDefs.lean`, and the cancel lemmas, `ewp_handle` and `then_compatC` in
`Core/EffRules.lean`; the runs and the refutation of the abortive-row `[then]` in
`Core/EffCancel.lean`; the lowering keeps the first error with no mask (`Backend/Clos/Capture.lean`,
`Backend/Clos/Unwind.lean`). The typing of finalisers with effects (decisions D2, D3) is §27.


Decision R (§19 *Typing*) is implemented, with no change to `CDerives`, the machine or the
relation: `EffCtx`, `RowAt`, `CDerivesAt`, `CDerivesAt.toCDerives`, `CDerivesAt.ofEffFree`,
`sig_prefix_of_rowAt`, `hndTags_of_rowAt` and `EffCtx.NoUnrExn` in `Core/Tied.lean`; the checker
builds every derivation tied (`Frontend/Check/Tied.lean`, `Frontend/Check/Rules.lean`), and
`checkProgram_tied` and `checkProgram_tiedAt` read it off (`Frontend/Check/Program.lean`). The
restriction to cancellable abortive operations (§18) is the checker's (`elabRow`,
`Frontend/Check/Elab.lean`; `sigsOkB`) and the elaborator's (`Frontend/Elab/Effects.lean`).

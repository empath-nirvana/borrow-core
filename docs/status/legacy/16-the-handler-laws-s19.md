
The handler laws (§19 *Laws*) are machine lemmas in `Core/EffMachine.lean`, with no change to
`CDerives`, the machine or the relation: H-ret, H-op at the capture cell (`catch_unr`,
`catch_cell`, `catchEv_cell`, `kappaC_resume`, `kappaC_cancel`, `kappaC_cancel_lin`,
`use_frees_cell`), H-fwd (`catch_fwd`, `fwd_resume`, `fwd_abort`), `[unwind]`, `[then]` and
`[finalise]`, and an abort's absorption of the frames it passes (`abort_absorbs`).

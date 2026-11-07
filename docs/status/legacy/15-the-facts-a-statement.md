
The facts a statement about every run of a program reads (§3, §13, §19), with no change to
`CDerives`, the machine or the relation: a run through an evaluation context splits where the
inner term stops stepping (`steps_plug_split`, `step1_plug_of_step`), and a context is determined
by the non-value it holds (`plug_inj_ctx`), in `Core/Steps.lean`; a typed term is closed at its
context (`closedAt_of_derives`), and a run from a closed term whose stored values are closed keeps
both closed (`closed_steps`), in `Core/Closed.lean`; `runM` computes a run at a finite memory,
deciding each step (`look`, `look_sound`), and every run it computes is a run of the machine
(`runM_sound`, `runM_val`), in `Core/Run.lean`.

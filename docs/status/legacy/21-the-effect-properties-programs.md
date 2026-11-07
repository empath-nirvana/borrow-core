
The effect properties' programs (§19 *Programs*, *Laws* item 3) are `Core/EffTier1Programs.lean`,
each with a derivation tied to its effect context and a run computed by `runM`, with no change to
`CDerives`, the machine or the relation; those the backend compiles are kernel programs
(`Backend/Kernel.lean`, their counts in `corpus/kernel-counts.expected`).

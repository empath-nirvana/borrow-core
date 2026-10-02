# FnMut — the affine closure as codata (promoted)

**Question** (#236). Can a closure that owns or captures mutable or linear state be called many
times, each call borrowing that state, with its environment hidden by its type (cf. Rust's
`FnMut`)?

**Answer.** Yes, as an abbreviation over `νX. C`, once `ν`'s positivity admits an observation with
a closed argument and a boxed rest:

    Aff^c A B  ≜  νX. (A ⊸ F(B ⊗ [@c] U X)) & F 1

**Promoted** (#239): SPEC §22. The positivity relaxation is in `Core/` (`Types`, `Relation`,
`RelationFacts`, `NuRel`, `Computation`, `Nu`); the closure's lemmas, derived rules and programs
are `Core/Aff.lean`, `Core/AffRules.lean` and `Core/AffPrograms.lean`; the library declaration is
`lib/aff.bc`; the corpus programs are `corpus/aff-*.bc`. The design and the requirement matrix are
in [`docs/fnmut.md`](../../docs/fnmut.md).

The experiment was a fork of `Core`'s import closure with the relaxation applied, plus the files
now in `Core/Aff*.lean`. Its code is at commit `60936af` (`experiments/FnMut/`).

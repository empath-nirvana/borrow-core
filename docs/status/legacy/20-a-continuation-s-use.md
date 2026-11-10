
A continuation's use (§19 *Laws* item 4) and the programs no derivation types (§19 *Programs*) are
stated by inversion of `CDerives`, with no change to `CDerives`, the machine or the relation: the
inversions (`fv_live`, `der_var`, `der_app`, `der_lam`, `der_swap`, …) and `refuses_R_clauses` in
`Core/Inversions.lean`, and `not_der_at05`, `not_der_at06`, `not_der_at08`, `not_der_at13` and the
typed control `at08Once` (the kernel program `at08-once`) in `Core/Rejections.lean`. Each inversion
is an induction on `CDerives`, so a rule added to `CDerives` adds a case to each
(`Core/Inversions.lean`, *Cost*).

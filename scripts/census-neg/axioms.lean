-- The negative test of scripts/check-hygiene.sh: `gate-census axioms+scripts/census-neg/axioms.lean`
-- must report each declaration that reaches an axiom outside the three.
axiom Core.negAxiom : False
theorem Core.negThm : 1 = 2 := Core.negAxiom.elim
def Core.negSorry : Nat := sorry

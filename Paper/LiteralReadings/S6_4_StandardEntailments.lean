import Paper.S5_Model.Definitions
import Support.Model.Notation
import Support.Model.Propositions

/-!
# Literal readings — [TR] §6.4

Measurements of §6.4's rules where the Lean adds a premise the printed statement
omits and the printed proof uses:

* 6.84 (`!l`): `bang_L_needs_premise`, the premise `P ⊨ Q` checked at the values
  where dropping it leaves `!P ⊨ Q` standing alone;
* 6.88 (`!∀`): `bang_all_needs_nonempty`, the index type the printed proof's
  *"Suppose `X ≠ ∅`"* excludes.

Nothing depends on this file.
-/

noncomputable section

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
### Lemma 6.84 (!l) — literal reading

The record is in `Paper/S6_4_StandardEntailments/Lemmas.lean`.
-/
/-- Without the premise `P ⊨ Q`, 6.84 would read `∀P Q. !P ⊨ Q`, which fails at
`P ≜ emp`, `Q ≜ ⊥`.
`[about ours: 6.84's added hypothesis, checked at the values where dropping it
would leave the entailment alone]` -/
theorem bang_L_needs_premise : ¬ ∀ (P Q : SPropU Loc Val), !ₛP ⊨ Q :=
  fun h => h emp bot PMap.empty ⟨emp_empty, emp_empty⟩

/-!
### Lemma 6.88 (!∀) — literal reading

The record is in `Paper/S6_4_StandardEntailments/Lemmas.lean`.
-/
/-- At an empty index type the premise is vacuous and the conclusion demands
`ρ = ∅`; the witness is a resource with a cell.
`[about ours: the printed 6.88 at an empty index type, which the printed proof's "Suppose X ≠ ∅" excludes]` -/
theorem bang_all_needs_nonempty (l : Loc) (v : Val) :
    ¬ (all (fun _ : Empty => !ₛ(top : SPropU Loc Val)) ⊨
        !ₛ(all (fun _ : Empty => (top : SPropU Loc Val)))) := by
  intro h
  have hb := h (ResU.single l (CellU.ownOf v)) (fun x => x.elim)
  have hnone : (ResU.single l (CellU.ownOf v)).get l = none := by
    rw [hb.1.1]; rfl
  rw [ResU.single_get_self] at hnone
  exact absurd hnone (by simp)

end BoCa.Fig16.BoLo

end

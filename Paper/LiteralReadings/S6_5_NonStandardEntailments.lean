import Paper.S5_Model.Definitions
import Paper.S6_2_NonStandardLemmas.Lemmas
import Support.Model.Entailments
import Support.Model.Propositions
import Support.Model.Singletons

/-!
# Literal readings — [TR] §6.5

* 6.102 (`[]∀`): `box_all_needs_nonempty`, the empty index type at a resource that
  holds a borrow, which the printed proof's *"Suppose `X ≠ ∅`"* excludes;
* 6.115 (`I-ag`): `not_iAgreeAtJoin`, the printed index `α ⊔ β` of the conclusion
  measured against the cells `{1}` and `{2}` under row 5.30's `α ⊑ ⊔β̄`.

Nothing depends on this file.
-/

noncomputable section

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
### Lemma 6.102 ([]∀) — literal reading

The record is in `Paper/S6_5_NonStandardEntailments/Lemmas.lean`.
-/
/-- At an empty index type the left side holds of every resource; the witness
is any `ρ` outside `Res_⊤`, which the right side's `[⊤]` refuses.
`[about ours: the printed 6.102 at an empty index type and `⊤`, which the printed
proof's "Suppose X ≠ ∅" excludes]` -/
theorem box_all_needs_nonempty {ρ : ResU Loc Val} (hρ : ¬ ρ.InStratum ⊤) :
    ¬ (all (fun _ : Empty => box ⊤ (top : SPropU Loc Val)) ⊨
        box ⊤ (all (fun _ : Empty => (top : SPropU Loc Val)))) :=
  fun h => hρ (h ρ (fun x => x.elim)).2

/-!
### Lemma 6.115 (I-ag) — literal reading

The record is in `Paper/S6_5_NonStandardEntailments/Lemmas.lean`.
-/
/-- Cells at `{1}` and at `{2}` compose to `{1, 2}`, whose meet `2` is not
`⊒ 1 ⊔ 2 = 1`.
`[about ours: `IAgreeAtJoin` at `ℓ ↦ imm({1},(),∅) ● ℓ ↦ imm({2},(),∅)`]` -/
theorem not_iAgreeAtJoin : ¬ IAgreeAtJoin := by
  intro H
  have h₁ := ResU.inStratum_empty (Loc := Nat) (Val := Nat) (LSet.singleton 1).join
  have h₂ := ResU.inStratum_empty (Loc := Nat) (Val := Nat) (LSet.singleton 2).join
  have h₃ := ResU.inStratum_empty (Loc := Nat) (Val := Nat)
    ((LSet.singleton 1) ∪ (LSet.singleton 2)).join
  have hc := ResU.compS_single_imm (0 : Nat) (LSet.singleton 1) (LSet.singleton 2)
    (0 : Nat) PMap.empty h₁ h₂ h₃
  obtain ⟨s, v, σ, hσ, e, -, hle⟩ := H 0 1 2 (fun _ _ => True) (fun _ _ => True) _
    ⟨_, _, hc, ⟨_, _, _, h₁, rfl, trivial, le_rfl⟩, ⟨_, _, _, h₂, rfl, trivial, le_rfl⟩⟩
  have hg := congrArg (fun r : ResU Nat Nat => r.get 0) e
  simp only [ResU.single_get_self] at hg
  obtain ⟨rfl, -, -⟩ := CellU.immOf_inj (Option.some.inj hg)
  exact absurd hle (by decide)

end BoCa.Fig16.BoLo

end

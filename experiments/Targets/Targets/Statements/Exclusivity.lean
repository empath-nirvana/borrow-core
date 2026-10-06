import Targets.Defs.World

/-!
# Targets — P10, exclusivity across the handler (DESIGN §6 P10)

**World:** [W].

Every configuration W reaches satisfies the aliasing invariant, counting the loans held by
suspended frames (`held`), by running clauses and by values in transit, all parts of the full
resource `fρ`.  It counts the same frames and records as `Arises` (I2), and `TI` is what `TW.inv`
gives of the `TW` world `Arises` names.  The program-level rules this invariant enforces are the
survey's A5 rules (a)–(c).

Literature: [CONF] 415:21 ("Conceptually, in a valid resource, every pair of aliases map to the
same object and each has an immutable ancestor"); the survey's T5 (i) ("exclusivity counting
suspended and in-transit loans").
-/

noncomputable section

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core

/-- **P10.** -/
def Exclusive (M : SemWorld) : Prop :=
  ∀ fρ ps i, M.Fam fρ ps i → ResU.Valid fρ ∧
    ∃ ps₀ ls₀, (∀ p, p ∈ ps₀ ↔ p ∈ ps ∨ p ∈ (M.held i).1) ∧
      (∀ x, x ∈ ls₀ ↔ x ∈ i.1 ∨ x ∈ (M.held i).2) ∧ TI fρ ps₀ (rsOf ls₀)

end Targets

end

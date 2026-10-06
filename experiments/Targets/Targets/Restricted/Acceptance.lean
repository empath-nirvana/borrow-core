import Targets.Defs.Programs

/-!
# Targets — the acceptance terms run (DESIGN §2 D14, §8)

`Support`'s executable interpreter (`eval`), with the capture steps of §19, on the four tier-2
acceptance terms: each program's observable answer and no leak, as DESIGN D14's table states.

| term | answer | observation |
|---|---|---|
| `at02` | `Flag` | `inj₁ ()`, memory empty |
| `at04` | `Flag ⊗ Flag` | `(inj₁ (), inj₂ ())`, memory empty |
| `at12` | `Flag` | `inj₂ ()`, memory empty (the cell freed by `dFlag` during the cancel) |
| `at17` | `Flag` | `inj₁ ()`, memory empty |

These are runs, not typings: tier 2's typing does not exist yet, and `AcceptsTier2` (the typing
conjunct) is OPEN.  `[prog]`
-/

noncomputable section

namespace Targets
open BoCa

/-- **AT02 runs**: the flag read through the lend after `Foo` resumes, and no cell left. -/
theorem at02_eval :
    (match eval at02 with
      | .value ⟨.inj₁ .unit, _⟩ false => true
      | _ => false) = true := by decide

/-- **AT04 runs**: the new content `inj₁ ()` (`Choose`'s answer, written through the lend) beside
the old `inj₂ ()`, and no cell left. -/
theorem at04_eval :
    (match eval at04 with
      | .value ⟨.pair (.inj₁ .unit) (.inj₂ .unit), _⟩ false => true
      | _ => false) = true := by decide

/-- **AT12 runs**: the handler cancels the continuation that holds the lend; the lend's finaliser
frees the cell during the cancel; the answer is `inj₂ ()`, and no cell left. -/
theorem at12_eval :
    (match eval at12 with
      | .value ⟨.inj₂ .unit, _⟩ false => true
      | _ => false) = true := by decide

/-- **AT17 runs**: the continuation holding the lend is moved into a cell and back, then resumed;
the answer is `inj₁ ()`, and no cell left. -/
theorem at17_eval :
    (match eval at17 with
      | .value ⟨.inj₁ .unit, _⟩ false => true
      | _ => false) = true := by decide

end Targets

end

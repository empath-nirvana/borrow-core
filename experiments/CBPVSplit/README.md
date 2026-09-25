# CBPVSplit — does the typed world factor through CBPV?

**Question.** BoLo's `T₁ ⊸ T₂` is CBPV's `U (T₁ → F T₂)`. The typed-world repairs put two
things in the `⊸` clause of `vX`: Kripke quantification over `Ext`, and the tagged `wpTS`.
If CBPV is the right home, the Kripke part should sit only at `U`, the `wp` only at `F`,
and `→` (and the lifetime `∀`) should need neither.

**Setup** (`Split.lean`). Mutual `VTy`/`CTy`; `cbv : Ty → VTy`, the CBV translation;
`vC`/`cC` over the existing typed world: `U` Kripke over `Ext`, `F` = `wpTS`, `→`/`∀`
plain. Computations are interpreted on BoLo expressions — no CBPV syntax or machine yet.

`Ty` has `!T` (`SPEC.md` §2), so `VTy` has `!A` with `vX`'s clause (resource `∅` and `A`'s
full relation, in both modes) and `cbv (!T) = !T⁺`. Build: `lake build Experiments`.

**Results** (all `[propext, Classical.choice, Quot.sound]`):

- `vX_eq_vC_fun`: `vX wpX b T = vC wpX b (cbv T)` for every BoLo type, both modes. The
  factoring holds clause for clause; the observable view's relaxation of `⊸`/`∀` is
  exactly relaxing `U`.
- `semX_iff_semC`, `fundamentalPropertyC`: `SemX Δ Γ e T ↔ SemC Δ Γ e (F T⁺)`, so the
  Fundamental Property holds of the CBV fragment of the CBPV relation.
- `vC_local`: `𝒱⟦A⟧` is stable along `Ext` at **every** CBPV value type, including ones
  that are no BoLo type's translation (e.g. `U (A → B → F C)`, arguments with no thunk
  between them). The proof is `vX_local` with the two Kripke clauses collapsed into `U`.

**Caveats.**

- The correspondence is by construction: `vC` was written from `vX`'s clauses. What the
  experiment shows is that the split is *consistent* (it type-checks and the equality is
  structural) and that the one property the split could have broken, `Ext`-stability,
  survives on native types. It does not show that the CBPV-native term formers are sound.
- The `Imm` clause's coherence conjunct is typed at BoLo's `Ty`: records store a `Ty`, so
  `vC`'s `Imm` clause reads `∃ T, cbv T = A ∧ CohE … T δ`. At a native payload type with
  no BoLo preimage the clause is empty. A CBPV core needs records typed at `VTy` (and
  `Coh`/`TyEq` over `VTy`) — the first thing the spec has to decide.

**Next probe.** CBPV term formers for the fragment (`thunk`, `force`, `return`, `bind`,
`λ`, application), interpreted on BoLo expressions, and their compatibility lemmas at
`cC`. The one most likely to need care is `bind` (`M to x. N`): the context's values were
accepted at the list before `M` ran and are used at the list after it, which is where
`vC_local` has to do its work.

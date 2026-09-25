> **Where the code is.** Archived, not copied: this experiment's library (`BangPaper`, roots
> `Paper` and `Support`) became this repository's library. `Paper/`, `Support/` here are its
> code with `[spec §2]` tags, and `Paper/Examples/BangExamples.lean` is `Examples/Closures.lean`
> (`flipCode` moved to `Examples/FnMut.lean`). The experiment itself lives in `borrow_lang`'s
> history at `Experiments/Bang/`, commit `c790ff9`; the last `borrow_lang` commit containing
> it is `a31b498`. `SPEC.md` §2 (version 0.2) is its spec entry.

# Bang — `!T` in place of closed code

The paper's own suggestion: *"Linear type systems are often presented with an exponential
modality, `!T` … Exponentials are therefore an orthogonal extension that we will not develop in
this paper, though they are completely compatible with our type system"* ([CONF] 415:4). BoLo
already has `!P ≜ emp ∧ P` (definition row 5.38).

Built on bolo-formalization `1658da9` (`Paper/`, `Support/` copied, library `BangPaper`).

**Added.**
- `Ty.bang T`. `𝒱⟦!T⟧δ(v) ≜ !𝒱⟦T⟧δ(v)`; at the typed world `ρ = ∅ ∧ vX true T`, in both modes;
  `vShape (!T) ≜ emp`; `Imm̲ 'b (!T) ≜ !T`; `Δ ⊢ !T ⊐ @a` for every `@a`; `tyLife (!T) = .free`.
- Typing: `bangLamI`, `bangAllI` (promotion of a `λ`/`Λ` over `!Γ`, `Ctx.Persistent`),
  `bangE` (dereliction), `copyBangAx`, `forgetBangAx`.
- `Support/Model/Unr.lean`; 6.131's `!` case by `reborrow_self_of_imm`; 6.60's by `ρ = ∅`.
- `gSepX_persistent`: `!Γ` holds `∅`.

**Results** (standard axioms): the Fundamental Property and adequacy over the extended
`DerivesWf`, and in `Paper/Examples/BangExamples.lean`:
- `ownedFn`: a closure owning its environment (`Ref 1`) with lifetime-polymorphic code
  `!(∀'c ⊏ ⊤. (Imm 'c 1 ⊗ 1) ⊸ 1)`, loaded through an `Imm` borrow and called twice.
- `mutClosure`: the whole closure `(env, !code)` in a cell, borrowed mutably (`withbor` form 2,
  using `Δ ⊢ !T ⊐ @a`), run twice through `withswap`.

Neither is typable with `fn T₁ T₂`. `fn T₁ T₂` is `!(T₁ ⊸ T₂)`.

**Removed** (they state facts about the judgment the extension changes): the literal-relation FP
at `Sem` and `ViewWitness.fundamentalProperty_refused`. `stripBox` also strips `!`, so `auxWf`
passes dereliction.

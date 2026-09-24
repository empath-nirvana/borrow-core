# Borrow core — specification

Version 0.1 · 2026-09-24

The library — `Paper/`, `Support/`, `Examples/` — implements this document and nothing else. A
change to the language is a new entry here, written before any code; the library then
implements it, and code an entry adds or changes is tagged `[spec §N]`. Experiments live
outside this repository and are never merged: what an experiment establishes reaches the
library only through an entry.

Notation follows Wagner, Gierczak, Marshall, Li and Ahmed, *From Linearity to Borrowing*
(PACMPL 9:OOPSLA2:415, 2025): `[CONF]` is the paper, `[TR]` its supplement.

---

## 1. Baseline

The calculus is BoCa with the logic BoLo, as mechanized in *bolo-formalization*
(github.com/empath-nirvana/bolo-formalization, commit `1658da9`). This repository starts from
that commit's `Paper/`, `Support/` and `docs/`: `Paper/INDEX.md` indexes the paper's results and
definitions, and `docs/adjudications.md` records every departure from the printed text. That
fixes:

- **Syntax** — `[TR]` §1: values, expressions, types `1`, `⊕`, `⊗`, `⊸`, `Ref`, `Imm @a`,
  `Mut @a`, `[@a]`, `∀'a ⊏ @b`, `Unk`.
- **Typing** — `[TR]` p. 2's rules and p. 3's axiom table, read under p. 2's presuppositions
  (`DerivesWf`).
- **Machine** — `[TR]` §3 with the frames `K; e` and `injᵢ K` (`BoLo.Steps`).
- **Semantics** — the typed world: `[TR]` §§4–6 with the definition changes recorded in
  bolo-formalization's `docs/adjudications.md` §12.66–§12.73 (`vX`, `wpTS`, `SemX`).

Baseline theorems, which every later entry must preserve:

- **Fundamental Property** — `DerivesWf Δ Γ e T → Δ.Ok → Ctx.ScopedB Δ Γ → SemX Δ Γ e T`.
- **Adequacy** — `DerivesWf ∅ [] e 1 → Steps ∅ e ∅ ()`: a closed program typed at `1` has a
  run to `()` that leaves memory empty.

---

## 2. Entry 1 — closed code, `fn T₁ T₂`

### Motivation

`Imm̲ 'b (T₁ ⊸ T₂) ≜ Unk` (`[CONF]` Fig. 8 clause (4)): an immutably borrowed function can only
be forgotten, because it may capture linear resources. With closure conversion a closure is a
pair of its environment and closed code. The environment is data, which `Imm̲` already views
correctly; what is missing is a type for the code. Closed code captures nothing, so it holds
no resource and can be kept whole through a borrow.

### Types

    T ::= … | fn T₁ T₂

Scoping, well-formedness, lifetime substitution and `TyEq` treat `fn T₁ T₂` exactly as
`T₁ ⊸ T₂`.

### Metafunction

    Imm̲ 'b (fn T₁ T₂) ≜ fn T₁ T₂

### Typing

    Γ dead    Δ ⊢ T₁    Δ; x : T₁, Γ ⊢ e : T₂
    ─────────────────────────────────────────  fnI
            Δ; Γ ⊢ λx.e : fn T₁ T₂

    Δ; Γ₁ ⊢ a : T₁    Δ; Γ₂ ⊢ f : fn T₁ T₂
    ──────────────────────────────────────  fnE
            Δ; Γ₁, Γ₂ ⊢ f a : T₂

Axioms, at a dead context:

    copy   : fn T₁ T₂ ⊸ fn T₁ T₂ ⊗ fn T₁ T₂
    forget : fn T₁ T₂ ⊸ 1

No new terms and no new machine rules: `fn` is inhabited by `λ` and eliminated by
application.

### Semantics

- Literal relation: `𝒱⟦fn T₁ T₂⟧δ(v) ≜ 𝒱⟦T₁ ⊸ T₂⟧δ(v) ∧ ρ = ∅`.
- Typed world: `vX b (fn T₁ T₂) ls δ v ρ ≜ ρ = ∅ ∧` the `⊸` clause at `ls`, in **both** modes.
  The observable view does not relax `fn` to `True` (it does for `⊸` and `∀`, §12.69).
- Shape: `vShape (fn T₁ T₂) ≜ emp`.

### Retired

The literal-relation Fundamental Property (`[TR]` 6.151 at `Sem` under `WithloadEscrow`, and
its refutation `ViewWitness.fundamentalProperty_refused`) is not carried: it quantifies over
`DerivesWf`, which now includes the `fn` rules. `Sem` at a `withload` node
(`ViewWitness.withloadSem_refused`) and the other literal readings in
`Paper/LiteralReadings/` are kept.

### Obligations

1. The Fundamental Property and adequacy of §1 hold over the extended judgment —
   `Fig16.LogRel.Typed.fundamentalProperty`, `adequacy`, with the cases `fnI_compatX`,
   `fnE_compatX`, `copyFn_compatX`, `forgetFn_compatX` (`Support/TypedWorld/Compatibility.lean`).
2. `[TR]` 6.131 at `fn`: `[α] 𝒱⟦fn T₁ T₂⟧ ⊨ ↺α 𝒱⟦fn T₁ T₂⟧` — `reborrow_vDen`'s `fn` case, by
   `reborrow_self_of_imm` (`Support/Model/Unr.lean`).
3. A closed program that loads a function through an immutable borrow and calls it —
   `Programs.callBorrowed` (`Examples/CallBorrowed.lean`), with `callBorrowed_runs` (adequacy)
   and `callBorrowed_eval` (the interpreter).  `Programs.captures` and `Programs.fnMut`
   (`Examples/Captures.lean`, `Examples/FnMut.lean`) exercise it with captured borrows and with
   `withswap`.

### Why closed code, and not a closure former

The typed world chooses each reborrow's image from types (§12.69, §12.71). A closure's image
must be its captured resource, and neither its type nor its value determines that: the
relation is not precise. Packing the environment existentially does not link the image to the
escrow, and neither does naming the environment's type while its value is free (both refuted
in the `borrow_lang` experiment `Experiments/BorrowedClosures/FnFork/EnvCheck.lean`). Closed
code has image `∅`, which is determined.

### Open

- **One arrow former.** `fn` is the empty-environment case of a single arrow indexed by the
  borrow that suffices to call it: `own` (`⊸`, Rust `FnOnce`), `mut` (`FnMut`), `imm` (`Fn`).
  The arms that differ between `fn` and `⊸` are the value clause, the shape, `Imm̲`, and the
  lemmas that read them; every structural arm is the `⊸` arm verbatim.
- **Captures of borrowed data** need nothing more. A closure is `(env, code)` with
  `code : fn (E ⊗ T₁) T₂`; when `E` is already a borrow, its view through a later borrow does
  not mention the new lifetime, so the stored code still applies
  (`Examples/Captures.lean`: `Imm 'a 1` captured, the closure loaded through an `Imm` borrow and
  called twice).
- **`FnMut`** needs nothing more when the code is held beside a `Mut` borrow of the
  environment: `code : fn (E ⊗ T₁) (E ⊗ T₂)` takes the environment by value and returns it, and
  `withswap` runs it in place (`Examples/FnMut.lean`: two calls, the environment updated by
  each).
- **Borrowing a closure mutably** — a `Mut` borrow of a cell holding `(env, code)` — needs
  `Δ ⊢ fn T₁ T₂ ⊐ @a`, which `OutlivesRules` lacks (it has no case for `⊸` either). Closed code
  holds `∅`, so the rule is expected to hold at every `@a`; it is not yet proved.
- **Captures of owned data** read through a borrow see `Imm̲ 'c E`, which mentions the lifetime
  `withload` picks. The code must be lifetime-polymorphic, `∀'c. fn (Imm̲ 'c E ⊗ T₁) T₂`, and
  `Imm̲ 'b (∀'a ⊏ @b. T) ≜ Unk`: this needs closed `∀` code, the `∀` counterpart of this entry.
- **Conservative extension.** Every baseline derivation is a derivation here and means the
  same thing. `DerivesWf` only gains constructors and `vX` is unchanged at `fn`-free types,
  but no theorem states it: stating it needs the baseline and the core in one environment.

---

## Changelog

- **0.1.1** (2026-09-24) — §2: capture and `FnMut` examples; the `Open` list records what
  mutable borrows of closures and owned captures still need.
- **0.1** (2026-09-24) — Baseline (§1). Entry 1, closed code (§2), from the `borrow_lang`
  experiments `CBPVSplit`, `ModesLabels`, `Shifts` and `BorrowedClosures`.

# Unsafe: asserted, not proved

Draft spec. Status words: EXISTS (in the code), DESIGNED (written down, not built), DECIDED
(a recorded user decision), OPEN (boxed question at the end).

## 0. Purpose

Sometimes a program or a language feature is believed sound but not proved. This spec gives one
mechanism for going ahead anyway. It must keep these properties:

- **Programs that assert nothing keep their guarantees unconditionally.** Their fundamental
  property, adequacy and borrow guarantees carry no hypothesis.
- **Every assertion is named and enumerable.** It is a hypothesis of the end-to-end theorem.
  The checker reports which assertions a program relies on, and the trusted base is generated,
  never declared by hand.
- **Every assertion is stated so that a run can falsify it,** and it has a falsifier.
- **Proving stays the default.** An assertion is an escape hatch for a gap that is proof-only:
  the program's physical behaviour is fine and the property is believed (DECIDED, 2026-10-14).

## 1. What exists

| piece | status |
|---|---|
| Externs: a named slot whose contract is its semantic type. The fundamental property quantifies over every closing substitution, so a checked `main` is safe under every implementation that meets the contracts (SPEC §11). | EXISTS |
| The assurance ladder: assumed, interpreter-checked, property-tested, typed low-level, boundary-checked, semi-automatically verified, proved. `bcc trusted` lists each extern with its level (SPEC §11 *Assurance*). | EXISTS |
| Decision 27: `unsafe` is an extern whose body we compile. Safe code meets unchecked code only at a boundary with a semantic-type contract; there are no unsafe blocks inside safe code. | DECIDED |
| #79: exceptions as typed constants (the axiom table extended), and a shape check for unsafe bodies, with raw memory only through a `RawMem` capability. | DESIGNED |
| `trust e`: the checker reports the smallest subterm it cannot type and why; the programmer marks it `trust e`; no assurance syntax or prover names in source (user preference, 2026-09-28). | DESIGNED |
| `PinLaw`: asserted compatibility lemmas of two typing rules, as a hypothesis of `fundamentalC_pin`/`adequacyD_pin` (`experiments/AsyncCap`, branch `async-capabilities`). | EXISTS (experiment) |

## 2. One principle, two kinds

**Every assertion is a hypothesis that something with a typing is in the logical relation at
that typing.** What the "something" is splits assertions into two kinds.

### 2.1 Kind T: a term at its judgment

**What is asserted.** `SemJ Δ Γ e j` for one term `e` that the program contains, at the judgment
`Δ; Γ ⊢ e : j` the checker expected there. This is the fundamental property's own conclusion at
that subterm, taken as given instead of derived.

**What it covers.**
- An extern: a closed `e`, with a host body.
- A compiled unsafe body (decision 27): the body is our code, shape-checked (§4).
- `trust e`: a subterm of a safe program. Its context `Γ` may hold borrows, and the contract is
  the relation under that context, which is exactly what a compatibility lemma states.

**The theorem.** The checker returns a derivation of an extended judgment `TDerives`. It is
`CDerives` plus one rule,

        (e, Δ, Γ, j) ∈ 𝒯
    ─────────────────────
      TDerives Δ Γ e j

where `𝒯` is the program's table of trusted sites. The theorems are:
- `fundamental_trusted (H : ∀ s ∈ 𝒯, SemJ s) : TDerives Δ Γ e j → SemJ Δ Γ e j`;
- `adequacy_trusted`, stated the same way;
- `TDerives.ofC`: every `CDerives` derivation is a `TDerives` one with `𝒯 = ∅`.

For externs nothing changes: they stay context slots, the special case where `e` is a variable.

**Where junk can still reach kind T.** The hypothesis is about one specific term, not about
every related term, so there is no quantifier over related code. But `SemJ Δ Γ e j` still
quantifies over every related substitution for `Γ` and every world, like an extern's contract.
A trusted `e` that is safe on every input a program can build, yet misbehaves on a related value
no program builds, makes the hypothesis false: earlier assertions were refuted this way
(`core_not_relend_kU`, `refoldKripke_false`). For a closed `e` (an extern, a closed unsafe body)
only worlds are quantified. For an open `trust` site this is OQ-8.

### 2.2 Kind R: a typing rule

**What is asserted.** A typing rule's compatibility lemma, at the rule's own premises, with
every premise about code taken as a derivation in the extended judgment, not as a semantic
fact.

**What it covers.** A rule whose premise is a derivation of code the program supplies, so that
no constant's type can state it without ranging over values no program builds. `PinLaw`'s R1
(a borrow held across a resuming operation) and R2 (a shared borrow over a loop whose state
holds it) are the first two.

**The theorem.** The kind-R rules are added to the extended judgment, giving
`TDerives` = `CDerives` + 𝒯 + the kind-R rules. The fundamental property and adequacy take one
hypothesis per kind-R rule, gathered into one structure (`PinLaw` is the shape). Their proof is
`fundamentalC`'s induction case for case, with each kind-R case closed by its hypothesis
(`fundamentalC_pin` is the shape).

**Who may add one.** Only the language, via a SPEC entry, never a program (OQ-2). A kind-R
rule widens what the checker accepts for every program, so it carries a spec entry and a user
decision, like any kernel rule.

## 3. Rules for an assertion's statement

These apply to both kinds. They are what went wrong or right with `PinLaw`.

1. **A hypothesis, never an axiom.** It is a `def … : Prop` or a `structure … : Prop` taken as
   an argument. `#print axioms` stays `[propext, Classical.choice, Quot.sound]`.
2. **Over typed things only.** Kind T is at one term's judgment; kind R is over derivations.
   Neither is a lemma pointwise over configurations or over related values.
3. **The claim itself, nothing smaller.** Assert the term's relation, or the rule's
   compatibility lemma. Do not assert an intermediate step of a proof route and then derive the
   claim. A route's step can be false where the claim is true: `PinStop` was first stated as the
   borrower's half of R1, and its cancel clause returned the owner before the borrower's
   finalisers ran. Shrinking an assertion is proof work, done separately.
4. **Non-vacuous.** At least one program that relies on it is checked and runs. For kind R, that
   program must be one `CDerives` refuses.
5. **Falsifiable by a run, with a falsifier.** A run of a program that relies on it gets stuck,
   leaks, answers outside its type, or trips the dynamic checks of §5. Any of these refutes the
   assertion. Each kind-R rule ships with an adversarial program list.
6. **Proof is the default.** Kind T is free for programmers to use; the trusted base records
   it. Kind R is raised with the user case by case.

## 4. Inside trusted code

From decision 27 and #79 §2, unchanged:

- **A trusted body is shape-checked, not borrow-checked.** Lifetimes, modes and linearity are
  erased; shapes are kept (`i32`, sums, products, arrays, pointer to a shape, closures). A
  shape-typed body never gets stuck at a non-memory operation.
- **Raw memory goes only through the `RawMem` capability.** Its operations are where a trusted
  body can fail, and the interpreter checks them dynamically (§5).
- **No raw pointer leaves a trusted body.** The boundary's type is a safe type `A`, and the
  contract is the relation at `A`. This keeps decision 27's reason for refusing unsafe blocks:
  provenance never reaches safe code. `trust e` is a boundary in exactly this sense (OQ-3).

## 5. Falsifiers

These are the U4 harness of `docs/async-capabilities.md` §6.1, applied to every assertion:

- **A never-reuse allocator,** so a use after free is a stuck run.
- **Tagged locations,** so an access through an ended borrow, an aliased write, or an owner
  access while a borrow is live is an error.
- **Differential runs:** the default allocator, the never-reuse allocator and the tagged
  interpreter must give the same output with `live 0`.
- **At a `RawMem` operation:** a bounds and liveness check.

A program that relies on an assertion is run under all of these in the gate. A failure
refutes the assertion, and the response is to restrict or remove it (OQ-7).

## 6. Reporting

- **`bcc check`** prints one line: either `assurance: unconditional`, or the list of
  assertions with their sites, e.g. `assurance: trust 12:5; PinLaw.R1 23:5`.
- **`bcc trusted`** generates the full trusted base: every extern, every `trust` site and every
  kind-R rule used, each with its assurance level. Evidence (tests, a Lean proof) is attached
  out of band and raises the level.
- **No ceremony in source.** There are no assurance clauses and no theorem names. Kind R needs
  no source marker at all, since its reliance is reported.
- **Migration.** When an assertion is proved it leaves the trusted base, and neither its type
  nor its callers change. Proving a kind-R rule moves it into `CDerives`; proving a kind-T site
  removes its `trust`.

## 7. Units

| unit | content |
|---|---|
| **V1** | `TDerives`: `CDerives` + 𝒯 + a slot for kind-R rules; `fundamental_trusted`, `adequacy_trusted`, `TDerives.ofC`. Built as `experiments/AsyncCap`'s `PDerives` was: generated from `CDerives`. Then move `PinLaw`'s R1 and R2 into it as the first kind-R rules. |
| **V2** | Checker: report the smallest subterm it cannot type, with the reason; `trust e` at the surface, elaborating to a 𝒯 entry; `bcc check`'s assurance line; `bcc trusted` covering `trust` sites and kind-R rules. |
| **V3** | Shape checker for trusted bodies, its soundness theorem, and `RawMem` (#79 §2). |
| **V4** | Falsifier at trusted boundaries: U4's harness plus the `RawMem` checks; the gate runs every relying program under it. |
| **V5** | Corpus: one `trust` site in safe code; one compiled unsafe body used from safe code; one shape-ill-typed body rejected; each kind-R rule's adversarial list. |

## 8. Open questions

> **OQ-1. `trust e` and its judgment.** The judgment of a `trust` site is the one the checker
> expected there. When the checker cannot infer it (the subterm is why inference failed), the
> programmer must ascribe it: `trust (e : A)`. Is the ascription required always, or only when
> inference fails?

> **OQ-2. User-level kind-R rules.** Can a library declare a typing rule it asserts, or only
> the language? Allowing it makes the trusted base include rules, which widen checking for
> every program that imports the library. Draft: language only.

> **OQ-3. Decision 27's wording.** "No unsafe blocks inside safe code" is incompatible with
> `trust e` as written, but its reason (provenance never reaches safe code) holds, because a
> `trust` site is a boundary at a safe type (§4). Amend decision 27 to say a boundary may sit at
> any subterm, provided its type is a safe type?

> **OQ-4. One ladder for both kinds?** The extern ladder has seven levels. A kind-R rule's
> evidence is of different sorts: the number of rules a partial proof covers, and the
> adversarial suite under the falsifier. Use the same ladder, or give kind R its own?

> **OQ-5. Trusted sites in generic code.** A `trust` inside a function the elaborator copies
> per row or type (§14 specialization) gives one 𝒯 entry per copy. Report each copy, or the
> source site once?

> **OQ-6. Effects across a boundary.** A trusted term's judgment includes its row, so its
> contract covers the operations it performs. A `trust` site inside a borrow block that is
> crossed by a resuming operation relies on both kinds at once. Nothing special is believed to
> be needed, but this has not been checked.

> **OQ-7. On falsification.** If a run falsifies an assertion: for kind R, restrict the rule
> (narrow its premises) or remove it; for kind T, the program is wrong and the `trust` site is
> the bug report. Should the gate block on falsification for kind T in the corpus, or only
> report it?

> **OQ-8. The context of an open `trust` site.** `SemJ Δ Γ e j` asks `e` to be safe on every
> related substitution for `Γ`, including values no program builds. Options: (a) accept it, as
> externs do: a trusted body must be safe at its whole semantic type, which is the usual meaning
> of a contract; (b) restrict the quantifier to substitutions that typed programs build, a
> derivation-indexed invariant that does not exist yet (tier-2 problem D); (c) allow `trust` only
> at closed terms or at contexts of first-order types, where junk is believed not to arise
> (`relend_fov`). (a) is simplest and matches externs; it risks vacuity only for code that
> depends on its context being reachable.

# Abstract types with a single provider (#778): scope

Kernel target: outside a type's provider, a well-typed program cannot eliminate a value of an
abstract linear type except through the provider's operations. For a linear handle whose provider
exposes only `close`, leak freedom then implies that `close` ran exactly once.

## The mechanism

**An abstract kind.** `Opaque.abs (n : Nat)` is the abstract type named `n`. Its relation is
`Tok`'s, an owned unit cell (`Opaque.rel (.abs n) := Opaque.rel .tok`). Like `Tok` it is not a host
type, not `OwnFree`, not persistent, has no derived drop, and its view is `Unk`. `Opaque.Host` is
redefined to exclude it. `File = .opq (.abs fileName)` (`Core/LetDtorFiles.lean`).

**The provider is an index of the judgment.** `CDerives` becomes `CDerivesIn (P : Nat → Prop)`, and
`CDerives := CDerivesIn (fun _ => True)` is an `abbrev`, so every existing statement is literally
unchanged. `P n` means "this derivation is inside `n`'s provider". Only two rules read `P`. They are
the iso between the name and its representation (the #141 reading: data inside the declaration,
abstract outside):

    absSeal   (hn : P n) : CDerivesIn P Δ Γ e (.val Tok)     → CDerivesIn P Δ Γ e (.val (abs n))
    absUnseal (hn : P n) : CDerivesIn P Δ Γ e (.val (abs n)) → CDerivesIn P Δ Γ e (.val Tok)

No other rule mentions `abs`. The compatibility lemma of each rule is the identity, because the two
relations are equal by definition. `mint` and `burn` stay `Tok`'s: a provider mints a `Tok` and seals
it, and unseals before it burns.

- **Provider of `n`:** a derivation at some `P` with `P n`. **Client:** a derivation at `P` with
  `¬ P n`.
- `CDerivesIn.mono : (∀ n, P n → Q n) → CDerivesIn P … → CDerivesIn Q …`. So `fundamentalC`,
  `adequacyC`, `adequacyD` and `resourceSafety` hold of every client derivation, and of every
  linked program, through `CDerives`.
- **`File`'s provider** is `with_fs`, Core code (the platform). It is typed at `⊤`, and its clauses
  unseal/burn and mint/seal. The program under it is typed at `P = ∅` and embedded by `mono`.
- **The program judgment.** `CDerivesAt Ξ` gets the same parameter, `CDerivesAtIn P Ξ` with
  `CDerivesAt Ξ := CDerivesAtIn ⊤ Ξ`, so that `ofEffFree` keeps its statement. The checker's
  translation `TDerivesAt → CDerivesAtIn P Ξ` is stated at every `P`, which holds because the
  frontend has no `abs` kind. So every checked program sits at `P = ∅`, outside every abstract
  type's provider (`checkProgram_outside`).

## `burn` and a written `match`

`burn : Tok ⊸ 1` is unchanged. A value of `abs n` becomes a `Tok` only through `absUnseal`, which
needs `P n`. So a destructor of `File` that burns, or any other route to `burn` from a `File`, does
not type outside `File`'s provider. That covers #775's skip-close.

A written `match` on a §42 declared type burns *that declared type's* token, `Tok`, whose provider is
the program (as today: "nothing ties a token to one consumer"). `File` is not a declared type, so no
`match` reaches its representation.

The parser-level exclusion of `tok_burn` becomes redundant as a guarantee for `File`. Keep it
anyway, as surface hygiene: `tok` is internal to the elaboration, and a written `tok_burn` on a
declared type adds nothing that a `match` cannot already do.

## What changes for existing code

- **Statements:** none. `CDerives`, `CDerivesAt` and every theorem about them read as before.
- **Proofs:** each induction over `CDerives`, `CDerivesAt` or `CDerivesP` gets the two new cases:
  `Fundamental`, `PinFundamental` (twice; `CDerivesP` gets both rules, ungated), `Weaken`,
  `InsertDead` (twice), `Inversions`, `EffTier1Programs` and `Tied` (`toCDerives`, `ofEffFree`).
  The `cases` on `Opaque` in `Opaque.lean`, `Invariant.lean`, `RelMu.lean` and `Backend2/Types.lean`
  get the new kind.
- **`LetDtorFiles`, `LetDtorCancel`, `LetDtorLoop`, `LetDtorSuspend`:** `File := abs fileName`, and
  `with_fs`'s clauses seal/unseal. The programs and theorem statements are unchanged.
- **§42 declared types and every corpus program:** unchanged.
- **`Core/Tree*`, `Support/Model/Tree/`:** untouched. #789 obligation: the embedding of total-mode
  derivations gets the two iso cases. They are trivial if #782's relation at `abs n` is `Tok`'s, and
  they are where #782's semantic abstraction attaches if it is not (see the decision below).
- **dtor-wire:** when `Fs` reaches the checker, `File` must map to `abs fileName`, not `tok`.

## Not-do

- No parser-only or elaborator-only restriction: the refusal is the absence of a rule at `¬ P n`.
- No convention ("nobody outside the library takes a `File` apart").
- No second provider by construction: authority over `n` is a judgment index that a program
  derivation (`P = ∅`) never has. One provider per type, not "correct by convention".
- No change to `burn`, `mint`, §42's rules, the machine, `Paper/`, `Support/`, or the new relation.
- No user-declared abstract types: who provides a user type (its declaration, an `impl`, a module)
  is the open methods/modules design. `P` is the hook for it.

## Theorem statements

- **T1, the kernel rule** (typing): `CDerivesIn.mono`; `CDerivesAtIn.toCDerivesIn`;
  `checkProgram_outside : … → CDerivesAtIn (fun _ => False) c.Ξ ∅ c.ctx c.t.erase (.comp c.C)`.
- **T2, the named wrong implementation refused:** for `¬ P fileName`,
  `¬ CDerivesIn P Δ Γ (.val (.lam (bindE (.app burnE (.var 0)) (.val .unit))))
     (.comp (.arr File (CTy.effOf S .unit)))`, and `¬ DropOk` at `File` with a burning
  destructor. The proof is an inversion over `CDerivesIn P`. `Core/Inversions.lean`'s machinery is
  at `CDerives` only, so it has to be restated at `P`, which is the bulk of the cost.
- **T3, #778's done-when:** for every client `M` at `¬ P fileName` under `with_fs`, every run that
  ends performed `close` once per `open`. **This one needs a decision; see below.**

## Decision needed (why work stopped after this document)

T3 cannot be a corollary of `fundamentalC` / `resourceSafety`. Every theorem about runs in the total
relation goes through `SemC`. `SemC` admits `burn` at `Tok ⊸ 1` (`tokBurn_compatX`), and with it at
`abs n ⊸ 1` (the relations are equal). So the skip-close program has a `SemC` denotation of the same
type as an honest client. #775's audit checks the consequence by machine: the skip-close program
satisfies `resourceSafety` and closes nothing (`scratch-archive/dtor/audit/SkipClose.lean`:
`fsSkipRaise_safe`, `fsSkip_closes_nothing`). A proof of T3 therefore has to use the client's
derivation at `¬ P n`, not its denotation. Two ways to do that:

- **(a) A parametric relation:** `abs n` is read at an invariant chosen by its provider, with a
  one-shot protocol (ghost token) between `open` and `close`. That is representation independence,
  which is #782's semantic types for opaque types, in the new relation. It would be a #789
  obligation.
- **(b) A syntactic metatheory in the total relation:** subject reduction plus an invariant that
  counts tokens over runs. Core has neither. This is large new mathematics in the relation that is
  being replaced, against "build only on what won't be rewritten".

**Recommendation:** close #778 with T1 and T2 at the total relation, and record T3 as a #789
obligation built by (a). This changes #778's done-when, so it is the user's call. Also open, but not
needed for `File`: the provider of a user-declared abstract type (methods/modules).

I have not derived T3 by any route. I have not verified that a syntactic proof is impossible. The
claim is only that T3 does not follow from any theorem that factors through `SemC`.

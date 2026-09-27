# Scope: recursion without step-indexing (`μ`, `ν`, the delay monad)

This is a scoping note. It changes no code, and nothing below is decided. It works out where
`μ`/`ν` and a delay monad would go, what each touches, and which parts are risky. Each claim
is marked in one of three ways:

- **[read]** — read off a definition, with file:line;
- **[expected]** — reasoned from the definitions but not built;
- **not derived, not verified** — an open question.

Nothing in this note is machine-checked.

Paper text: `[CONF]` 415:25 (the "Language Extensions" paragraph, lines 1496–1499 of the text
dump) says that pure constructs need no model change, and that non-terminating constructs
would need the model step-indexed in the standard way, which weakens leak freedom to
terminating executions. The design below takes a different route. Non-termination is kept
out of `F`-typed computations. It appears only as codata whose type says so (`ν`, `D`), and it
is observed a finite number of times. So the claim `F 1` programs terminate and leave memory
empty (`SPEC.md` §1, `docs/dream-properties.md` F2) is kept as it is, and the statement for
programs that may diverge is a new one (§4). This is a different extension from the one
415:25 describes. It does not dispute it.

## 0. The design being scoped

- **`μX. A`** — iso-recursive, finite data. `roll`/`unroll` and a fold (iteration).
- **`νX. B`** — codata, with coiteration and observations. For linear state it has a
  finalizing observation (`next & close`).
- **`D A ≜ νX. A ⊕ X`** — the delay monad, with divergence visible in the type.

The constraint is that infinity enters only as codata that is observed finitely. It never
becomes an element of a well-founded carrier that something inducts over. The carrier's
stratification is `WellFounded.fix` over `Life = ℕᵒᵈ` (`Paper/S5_Model/Definitions.lean:102`,
`:185`) **[read]**. Everything proposed below lives at the level of relations
(`WProp = WRes → Prop`), not in the carrier.

---

## 1. Where it goes

**Recommendation: a fork of `experiments/CBPVWorld` as the first experiment.** In that world,
`ν` is a computation type and `μ` is a value type.

The reasons:

1. **`close` needs `&`.** `next & close` has two observations with different result types.
   CBPV has `&`: `CTy.amp` (`experiments/CBPVWorld/CBPVWorld/Types.lean:57`), and `cC` at `&`
   is a conjunction at the same resource (`Relation.lean:94-95`). A stream's state is shared
   by the two branches, and one of them is taken. BoLo's `Ty` has no `&`
   (`Paper/S2_Statics/Definitions.lean:211-226` lists the formers). In the library, `close`
   would need a `&` spec entry first. **[read]**
2. **The records never look inside a computation type.** In CBPVWorld, `U C` is a leaf of
   `VTy.recV` (`Types.lean:64-90`) and has no `RefPos`/`Chain`/`MutPos`/`GPos` constructor
   (README:57-58). `vShape (U C) = True` (`World.lean:39`), and `Imm̲ 'b (U C) = Unk`
   (`Types.lean:134`). So a `ν` in `CTy` sits behind `U`, and it adds no case to the reborrow
   machinery (`Images`, `Invariant`, `Reborrow`, `ReborrowShapes`, `FrameRules`, about 6,000
   lines). It adds cases only to the `CTy` inductions. **[read; the "no case" part is expected]**
3. **Adding it to the library also touches the transcription layer.** The library's `Ty` is
   the paper's `Ty` (`Paper/S1_Syntax`). Adding `μ` there reaches the `Paper/` layer's
   inductions on types. A rough grep finds about 14 case sites in `Paper/` and about 48 in
   `Support/` that match on `⊸`. `SPEC.md` §2 already had to retire the literal-relation FP
   when it added `!` (`SPEC.md:99-104`). A fork of an experiment leaves the library alone.
   **[read; the counts are approximate]**
4. **BoLo programs still reach it.** `embed` (CBPVWorld README:173-188) sends every
   `DerivesWf` derivation into `CDerives`. So a BoLo-level `μ` can be added later as
   `cbv (μX.T) = μX. cbv T`. That is mechanical if `cbv` keeps positivity, which it does:
   `⊸`'s codomain goes to `F`'s argument under `U`, a positive position. **[expected]**

The "both via the embedding" option is not needed for the first experiment. `μ` costs the same
in either world, because it is a value type and touches the records in both (§2). `ν` is cheap
only in CBPVWorld.

---

## 2. `μX. A`

### 2.1 The value relation: not by structural recursion on the unfolding

The clause `vX (μX.T) v ≜ vX (T[μX.T/X]) v` is not structural, because `T[μX.T/X]` is not a
subterm. Three ways round that:

- **A measure on values fails at `Ref`.** The next value is read from the heap, not from `v`:
  `ptoOwn ℓ v' ⋆ vX b T ls δ v'` (`Support/TypedWorld/Relation.lean:80-81`;
  `CBPVWorld/Relation.lean:80-81`). A linked list's tail is not a sub-value of its head.
  **[read]**
- **A measure on the resource** (cells consumed by `⋆`, with nested witnesses counted) would
  work for data-only `μ`. It fails wherever `X` sits under `U` or `⊸`, where the resource is
  not bounded. It would also turn `vC` into well-founded recursion, and that changes the
  definitional unfolding that about 10,000 lines of relation lemmas rely on (`simp [vC]`,
  `rfl`). **[expected]**
- **Recommended: an impredicative least fixed point with an environment.** `vC` takes an
  environment `η` that maps each type variable to a predicate. The new clauses are these:

      vCE η b X        ≜ η X b
      vCE η b (μX. A)  ≜ fun ls v ρ => ∀ P, (∀ b' ls' v' ρ', vCE (η[X↦P]) b' A ls' δ v' ρ' → P b' ls' v' ρ')
                                         → P b ls v ρ

  This is Knaster–Tarski's `lfp = ⋂{P | Φ P ⊆ P}`, written in `Prop`. It needs no
  monotonicity proof to *define*, and `vCE` stays structurally recursive, because `A` is a
  subterm of `μX.A`. The top-level `vC := vCE ∅` gives `SemC`, `gDenC` and every existing
  compatibility statement their current signatures (`Relation.lean:115-119`).
  - `P` is indexed by the mode `b`, because mode `false` calls mode `true` at `!` and at `Mut`
    (`Relation.lean:78`, `:85-87`). So the fixed point is joint over `Bool`. **[read]**
  - **Monotonicity is needed only for `roll`/`unroll`.** `unroll` is
    `vC (μX.A) v ⟺ vC (A[μX.A/X]) v`. It needs a substitution lemma (`vCE η[X↦⟦μX.A⟧] A =
    vCE η (A[μX.A/X])`) and `Φ` monotone. **[expected]**

### 2.2 Positivity

For `Φ` to be monotone, `X` may occur only where the clause is monotone:

| position | clause | monotone? |
|---|---|---|
| `⊗`, `⊕`, `[@a]`, `!` | `Relation.lean:69-79` | yes **[read]** |
| `Ref` | `ptoOwn ℓ v' ⋆ vC A v'`, `:80-81` | yes **[read]** |
| `Imm @a` payload | `P ls₀ u σ` in `ptoImmS`, `:50`; the observable mode | yes, but `CohE` reads the *syntactic* type (`:83`), so `η` must carry the closed type `A[μX.A/X]` beside the predicate **[read / expected]** |
| `Mut @a` payload | `ofS Q = P ls₀` in `ptoMutS`, `:43` — an **equation** | **no**: invariant. Exclude `X` under `Mut` **[read]** |
| `U C`, `C`'s codomain / `F` / `&` / `∀` body | `:75-76`, `:91-98` | yes |
| `U C`, `⊸` domain | `vC A ─⋆ …`, `:93` | **no**: exclude (it would also give Curry-style self-application and break termination) **[expected]** |

So `μ` admits strictly positive occurrences, including under `U` in codomain position
(W-types, such as a free monad as data), but not under `Mut` or in a `⊸` domain.

**Fold has a narrower restriction than `unroll`.** The fold needs the functorial action of
`A` on `X`. Under `Ref` that action is `swap`-based, which is possible because BoCa's `swap` is
type-changing. Under `Imm` it is impossible, since a borrowed payload cannot be retyped.
Under `!` it is impossible for a linear result, and under `[@a]` it needs the result to
outlive `@a`. So fold needs `X` only under `⊗`, `⊕`, `Ref` and a `U`-codomain; `unroll` works
at every positive position. **[expected]**

### 2.3 `vShape`, `tyLife` and outlives at `μ`

- **`vShape (μX.A)`** is the same impredicative least fixed point. `vShape`'s `Mut` clause is
  `∃P, ptoMut ℓ α P ∧ ∀ u σ, P u σ → vShape T δ u σ` (`World.lean:45-46`), which is monotone.
  **[read]**
- **`tyLife`** exists only in the library, for the literal relation's `TyAt`
  (`Support/LogicalRelation/Compatibility.lean:462-480`); CBPVWorld has none. If `μ` goes to
  the library: `tyLife (μX.T) ≜ tyLife (T[X ↦ free])`. `free` is the unit of `combine`
  (`:449-455`), `tyLife` does not recurse under `Imm`/`Mut`/`[@a]`, and it passes through
  `Ref`. So the unrolling equation should hold. **[expected]**
- **Outlives**: `Δ ⊢ T[1/X] ⊐ @a ⟹ Δ ⊢ μX.T ⊐ @a`. `X` holds only what `T` holds, and
  `VOutlives` has `unit` (`Types.lean:310-319`). An inductive rule stated at the unrolling,
  `Δ ⊢ T[μX.T/X] ⊐ @a`, would need an infinite derivation. 6.60 at `μ` (`vC_outlives`,
  `RelationFacts.lean:611`) follows by induction on the least fixed point. **[expected]**

### 2.4 `Imm̲` at `μ`: the reborrow clause commutes only at head positions

`Imm̲ 'b` recurses through `⊗`, `⊕` and `[@a]`. At `Ref`, `Mut`, `Imm` and `!` it stops and
keeps the payload type unchanged:

- `Ref A ↦ Imm 'b A` (`Types.lean:135`; clause (5), `Paper/S2_Statics/Definitions.lean:216`);
- `Mut _ A ↦ Imm 'b A` (`:137`);
- `Imm @a A` kept (`:136`);
- `!A` kept (`:139`).

**[read]**

So the proposed `Imm̲ 'b (μX.T) = μX. Imm̲ 'b T` with `Imm̲ 'b X = X` is right only when `X`
never occurs under those four formers. The boxed list shows why:

    L = μX. 1 ⊕ (A ⊗ Ref X)
    Imm̲ 'b (T[L/X]) = 1 ⊕ (Imm̲ 'b A ⊗ Imm 'b L)            -- the payload of Imm 'b is L itself
    naive:            μX. 1 ⊕ (Imm̲ 'b A ⊗ Imm 'b X)          -- its unrolling has payload Imm̲-of-L

In the naive clause, the borrow of the tail claims a payload of the reborrowed type. The cell
holds an owned tail of type `L`: its own `Ref` cells are `own`, not views. `CohE` would also
compare against the record's `L`. The clause that clause (5) forces instead is this:

    Imm̲ 'b (μX.T) ≜ μY. Imm̲ᵡ 'b T
      where Imm̲ᵡ sends X at a head position (under ⊗, ⊕, [@a] only) to Y,
      and substitutes X ↦ μX.T inside the payloads kept by the Ref/Mut/Imm/! clauses.

The unrolling law to prove is `Imm̲ 'b (T[μX.T/X]) = (Imm̲ᵡ 'b T)[Imm̲ 'b (μX.T) / Y]`, a
syntactic induction on `T`. The two clauses agree on the examples below:

- the boxed list: `Imm̲ 'b L = 1 ⊕ (Imm̲ 'b A ⊗ Imm 'b L)`, with `Y` vacuous;
- an inline tree `μX. 1 ⊕ (X ⊗ X)`: `μY. 1 ⊕ (Y ⊗ Y)`.

**[expected]**

**6.131 at `μ`** (`reborrow_vShape`, `CBPVWorld/ReborrowShapes.lean:34`; `reborrow_vDen`,
`Paper/S6_6_ReborrowingEntailments/Lemmas.lean:479`). The proof would go by induction on the
least fixed point, not on `T`, with the `Ref` bullet unchanged. The `Ref` bullet gives a
borrow of the cell at the payload's own type, which is why the guarded clause above is the
one it matches. The typed-world half also needs `μ` constructors for `RefPos`, `Chain`,
`MutPos` and `GPos` (`CBPVWorld/Records.lean:44`, `:61`, `:73`, `:99`), which are one "unroll"
step each, and `TyEq`/`CTyEq` at `μ`/`ν` and at type variables (`:169`). The choosers
(`rebChooseTW_top`/`_deep`, `CBPVWorld/Reborrow.lean:132`, `:179`) build images along `Chain`.
For a list, the `k`-th tail is a chain of length `k`, and `Chain.step` already iterates
(`Records.lean:61-71`). **Not derived, not verified**: that the chooser and invariant proofs
(`Images.lean`, `Invariant.lean`, 4,800 lines) take the new `RefPos` case without more than
mechanical work. This is the main risk of `μ`.

### 2.5 `Ref` under `μ`

Linked lists (`μX. 1 ⊕ (A ⊗ Ref X)`) are positive (§2.2), and fold over them works by
`swap`. **[expected]** Traversing a *borrowed* list is a different question; see R4 in §6 and
the iterators in §7.

### 2.6 Terms

`roll`/`unroll` can be typing rules on the same term, as `!E` is (`SPEC.md:80-82`), so there
is no machine change. Fold needs recursion at runtime. BoCa's `Expr` is untyped CBV with `λ`,
so a Z-combinator term exists already (`Fundamental.lean:278-279` shows the term formers).
Fold can then be a closed constant with its own `CDerives` rule, as the borrow axioms are
(`Fundamental.lean:107-126`). Its compatibility lemma goes by induction on the least fixed
point, and the Z-combinator's unrolling is pure head steps (`cC_head`,
`Computation.lean:139`). So no new syntax and no new machine rule are needed. **[expected]**

---

## 3. `νX. B`

Implemented in SPEC 0.7 (§7, `Core/NuRel.lean`, `Core/Nu.lean`). `U X` is the value-type
variable `0` of the body's observations rather than a `CTy` variable, positivity is §3.1's with
`X` under `⊗`/`⊕` only, and coiteration is §3.3's map, over `⊗`/`⊕`.

### 3.1 Route: a direct greatest fixed point in `CTy`, not a packed `∃S`

- **`∃S. S ⊗ !U(S ⊸ B{S})` as a value type** runs into the obstruction already
  machine-checked in `experiments/BorrowedClosures/EnvCheck.lean`. `envShape_unlinked`
  (`:18`) and `envValue_unlinked` (`:34`) show that an existentially packed environment lets
  the image and the escrow choose `S` and `w` independently. That matters whenever `Imm̲`
  would look inside the package. It is the same reason `SPEC.md:132-138` gives for `!` over a
  closure former. It could be avoided only by setting `Imm̲ (∃S. …) = Unk`, and that is just
  `U` again. **[read]**
- **A syntactic `∃S` inside `vC`** is not structurally recursive, because `S` is quantified,
  not a subterm. **[expected]**
- **Recommended: `νX. B : CTy`, with the impredicative greatest fixed point**
  (`∃R. R ⊆ Φ R ∧ R e`, with `R : List SRec → Expr → WProp`), through the same environment as
  §2.1, where computation-type variables map to `cC`-shaped predicates. `∃R` over predicates
  is in `Prop` and raises no universe issue. The `∃S` form is how coiteration is *proved*:
  the witness `R` is the image of the state relation under the unfold. It is not how the type
  is defined.
  - **Positivity**: `X` only under `U`, only at positive positions (§2.2's table), and not at
    `B`'s head. That excludes `νX.X`.
  - **`roll`/`out`** (`e : B[νX.B/X] ⟺ e : νX.B`) needs only monotonicity.
- **The observation-depth alternative** is `⋂ₙ Bⁿ(⊤)`. `⊤` is `cC ⊤ = True`
  (`Relation.lean:96`). For this route, `out` needs `Φ` to commute with countable
  intersections, but `wpTS` has `∃` over post-states and over lifetimes (`ptoMutS`'s `∃ b`,
  `Relation.lean:41`). Whether `⋂ₙ` commutes with those is **not derived, not verified**.
  The greatest fixed point avoids the question.

### 3.2 Where `ν` meets the existing lemmas

- **`vC_local`** (`RelationFacts.lean:434`): `U` is already Kripke over `Ext`
  (`Relation.lean:75-76`), so `ν` under `U` inherits it. **[read]**
- **`cC_iff_stacks` / `sS`** (`Computation.lean:30-40`): a stack for `νX.B` is a stack for
  `B[νX.B/X]`. Because `B`'s head is a former, not `X`, `sS` at `ν` can recurse on
  (stack length, head size). **[expected]**
- **`cC_bind`/`cC_step`** (`:125`, `:146`) at `ν`: by coinduction, or from the stack form.
  **[expected]**
- **`forceE`** matches on the head constructor (`Relation.lean:60-62`). It must see through
  `ν` (`forceE (νX.B) = forceE B`). Otherwise `D A = νX. F(…)` would be forced as a λ-value,
  while its unrolling is forced by `()`. **[read / expected]**

### 3.3 Coiteration

    unfold : !U(S ⊸ B{S}) ⊸ S ⊸ U(νX.B)          (B{S}: U X replaced by S)

The runtime is `Z(λgen. λs. map_B gen (step s))`, with `map_B` the type-directed functorial
action. The soundness proof is coinduction with candidate
`R = {force (gen s) | vC S s}`, together with a map lemma that says `map_B` sends `cC B{S}`
to `cC_{X↦R} B`. The map lemma is the polytypic lemma that fold (§2.6) needs too.
**[expected]**

### 3.4 `close` and leak freedom

A `U C` cannot be dropped: `forget` exists at `!`, `Imm`, `Mut` and `Unk` only
(`Fundamental.lean:107-126`; `Affine`, `experiments/Records/Records/Encoding.lean:228`). A
stream observed only by `next : F(A ⊗ U X)` always hands back a new `U X`, so a closed `F 1`
program cannot end while holding one. So **`close` is necessary for linear codata in
terminating programs at all, not only for leak freedom**. **[read / expected]**

With `B = F(A ⊗ U X) & F 1`, the step's `close` branch consumes the state (for example,
`free`), and a program that runs `take n` and then `close` is an ordinary closed `F 1`
program. `adequacyC` (`Fundamental.lean:270`) then gives it an empty final memory, unchanged.
A stream whose state is `!` can be promoted over `!Γ` and forgotten.

### 3.5 Lifetime-indexed codata (`IterMut<'a>`)

No new former is needed: `[@d] U(νX.B)`. `VOutlives` has no rule at `U`
(`Types.lean:310-319`; README:202-204), which is the right default, because the state is
opaque. `[]I` boxes a context `Γ` that holds `Mut 'a` leaves at any `'d` with `'d ⊏ 'a`,
through `VOutlives.mut`. After that, the `[@d]`-boxed iterator crosses scopes as any
`[@d] T` does. In particular it cannot leave the callback that borrows at `'a` itself, since
`Mut 'a ⊐ 'a` is not derivable. That is Rust's behaviour. **[read / expected]**

**Result (SPEC §7, borrowed iteration).** For an iterator over *borrowed* data this route does
not help, and the missing outlives rule at `U` is not the obstacle. `[@d] U(νX.B)` is `[]I` at
`U C`, which needs only the captured context to outlive `'d`. The iterator of issue #57 needs
its state to hold element views at the list borrow's own lifetime. A list linked through cells
yields its tail only as a view through a pointer, inside a `withload` callback at a fresh
`'x`, and a rest capturing it cannot be boxed at `'x`; returning the tail view from a run is
excluded by `↭` (`experiments/FrameEnd`). What works is a sequence with a value spine, whose
`Imm̲` holds every element's view at one lifetime; `iterImm` (`Core/BorrowedIter.lean`) is
`unfold` over those views.

### 3.6 `Imm̲` at `ν`

- `Imm̲ 'b (U(νX.B)) = Unk` (`Types.lean:134`), as for any thunk.
- `!U(νX.B)` is kept whole (`:139`), but only a stream with `!` state can be promoted.
- A `!` step is not enough. The image of a stream is its captured state, which is exactly
  `SPEC.md:132-138`'s obstruction. Observing a stream consumes it anyway, so an `Imm` view of
  one has nothing to offer.
- `Mut 'a (U νX.B)` works as `&mut Iterator`: `withswap` it out, observe, and store the tail
  back. **[read / expected]**

---

## 4. The delay monad

- **`D A ≜ νX. F(A ⊕ U X)`**, preferably **`νX. F(A ⊕ U X) & F 1`** (cancellable). Either is
  a plain `ν` type. **[expected]**
- **`now`, `later` and `bind`.**
  - `now a = return (inj₁ a)` and `later t = return (inj₂ t)`, through `roll`.
  - `bind` is coiteration with state `(U(D A) ⊗ U(A ⊸ D B)) ⊕ U(D B)`. The continuation is
    carried in the state, so the step is `!`. **[expected]**
  - With the cancellable `D`, `close` of a `bind` must dispose of `k : U(A ⊸ D B)`, which is
    not affine. So continuations either are `!` or carry their own `& F 1`. This is a real
    design choice. It is not settled here.
- **Loops.** `iterD : !U(S ⊸ F(A ⊕ S)) ⊸ S ⊸ U(D A)` is coiteration directly. For the
  cancellable `D`, it also takes a finalizer `!U(S ⊸ F 1)`.
- **General recursion** can be derived without a `fix` rule. Take the resumption type
  `G B = νX. F(B ⊕ (A ⊗ U(B ⊸ X)))`, with `X` positive under `U`. A program is then
  `f : !U(A ⊸ G B)`, with no recursive handle. It is run into `D B` by coiteration with state
  "current resumption ⊗ stack of pending `U(B ⊸ G B)`". The stack is a `μ`-list, with `X` at
  data positions only. This is McBride's construction, and it needs `ν`, `μ` and `!`.
  **[expected]**
- **A direct `fix : !U(U(D A) ⊸ D A) ⊸ D A`** is **not derived, not verified**. The
  coinductive candidate would have to contain `fix f`, but `f`'s semantic type is stated at
  the greatest fixed point `⟦D A⟧`, not at the candidate. Closing that gap needs `f` to be
  parametric in `D`'s interpretation, or a later modality `▷`. `▷` is where step-indexing
  would come back in. I have not verified that any obstruction is real.
- **Adequacy, restated.**
  - *With `close`*: for every `n`, the driver "observe `n` times, then `close`" applied to a
    closed `e : D 1` is a closed `F 1` program, so `adequacyC` applies unchanged: it runs to
    `()` with empty memory. Separately, either some `n` reaches `now ()`, and that run ends
    with empty memory, or every `n` reaches `later`. That second case is the infinite chain
    of `later`s. **[expected]**
  - *Without `close`*: the driver ends at `inj₂ t` with `t`'s resources still in memory. That
    needs `theorem32` (`Fundamental.lean:238`) with a non-pure postcondition
    (`Steps ∅ e μ' v ∧ ∃ρ', μ' = ⟦ρ'⟧ ∧ vC A v ρ'`), which does not exist yet. It looks
    mechanical from the `wpTS` unfolding. **[expected]**

---

## 5. Blast radius (base: a fork of CBPVWorld)

Sizes are guesses, from line counts of the files touched (`CBPVWorld/*.lean`, 12,438 lines),
and none of them has been measured.

| Item | Where | Class | Guess |
|---|---|---|---|
| `VTy.mu`/`tvar`, `CTy.nu`/`cvar`; type substitution; `VFree`/`CFree`/`applyLSub`/`VScoped`; `recV` | `Types.lean` | mechanical, plus new substitution | 300–500 |
| `Imm̲` at `μ` with `Imm̲ᵡ`, and its unrolling law | `Types.lean` | real (small) | 100–200 |
| `VOutlives` at `μ` (`T[1/X]`) | `Types.lean:310` | mechanical | < 50 |
| `vCE`/`cCE` with an environment; top-level `vC := vCE ∅` | `Relation.lean` | real (signature) | 100 + threading |
| `unroll`/`out` (substitution + monotonicity under positivity) | new | real | 300–600 |
| `vC_local`, `vC_same`, `vC_tyEq`, `vC_congr`, `vO_obs`, `obs_transfer`, `image_vC_of_shape` at `μ`/`ν` | `RelationFacts.lean` (1,624) | real at the new cases, mechanical elsewhere | 400–800 |
| **6.60** (`vC_outlives`) at `μ` | `RelationFacts.lean:611` | real, small | 50–100 |
| **6.60** at `ν` | — | unchanged (no rule at `U`) | 0 |
| `vShape` at `μ` | `World.lean:31` | real, small | 50 |
| `RefPos`/`Chain`/`MutPos`/`GPos`/`TyEq` at `μ` | `Records.lean` | mechanical | 100 |
| **6.131** (`reborrow_vShape`) at `μ` | `ReborrowShapes.lean:34` | real | 150–300 |
| 6.131 at `ν` | — | unchanged (`Imm̲ (U C) = Unk`) | 0 |
| Chooser / invariant / images at `μ` (new `RefPos` case) | `Images`, `Invariant`, `Reborrow`, `FrameRules` (~5,900) | **unknown** | 200–1,500 |
| Chooser / records at `ν` | same | unchanged (`U` is a leaf) **[expected]** | ~0 |
| `sS`, `cC_iff_stacks`, `cC_step`, `cC_bind` at `ν`; `forceE` | `Computation.lean`, `Relation.lean:60` | real | 200–400 |
| Existing compatibility lemmas | `Compat.lean`, `Compatibility.lean` | unchanged if `vC := vCE ∅` | ~0 |
| New compatibility lemmas: `μI`, `μE`, fold (polytypic map), `νI`, `νE`, unfold | new | real | 600–1,200 |
| `CDerives` rules, `fundamentalC` cases | `Fundamental.lean` | mechanical | 100 |
| Adequacy at `F 1` | `Fundamental.lean:270` | unchanged | 0 |
| `D` adequacy with `close` | new | follows from `adequacyC` | 50 |
| `D` adequacy without `close` | new | `theorem32` generalized | 100–200 |
| `embed` (only if BoLo gets `μ`) | `Embedding.lean` | mechanical | 100 |

Taking `μ` and `ν` into the **library** additionally touches the `Paper/` layer's `Ty`
inductions and the literal relation (`vDen`, `tyLife`/`TyAt`), and it needs a `&` entry
before `close` can be typed.

---

## 6. First probe

Most of the risk can be tested **without forking** the typed world, by importing CBPVWorld
unchanged and fixing one recursive type at a time. The probe below does that, in three parts.
A fork is needed only for R4.

**Probe P-μ** (imports `CBPVWorld`). Let `L = μX. 1 ⊕ Ref X` be the boxed list of units,
written out by hand. `listRel` is Knaster–Tarski's least fixed point over `vC`'s clauses.

1. `listRel_unroll : listRel ls δ v ρ ↔ (⌜v = inj₁ ()⌝ ∨ ∃ℓ v', ⌜v = inj₂ ℓ⌝ ⋆ ptoOwn ℓ v' ⋆ listRel ls δ v') ρ`.
2. `listRel_outlives : listRel ls δ v ρ → BoLo.Outlives ρ α`, at every `α` (6.60's shape).
3. `listRel_local`: `Ext`-stability (`vC_local`'s shape).
4. `freeAll`: the Z-combinator term for "free every cell", with
   `SemV [] freeAll (U(L ⊸ F 1))`, by induction on the least fixed point.
5. `build3_free_runs`: `alloc` a 3-cell list, then `freeAll`. It runs from empty memory to `()`
   and empty memory (`corollary33`, `Fundamental.lean:257`).

**Probe P-ν** (imports `CBPVWorld`). Let `St = νX. F(1 ⊗ U X) & F 1`, with state `Ref 1`.
`stRel` is the greatest fixed point over `cC`.

1. `stRel_out`: `stRel ↔ cC(F(1 ⊗ U •) & F 1)` with `• ↦ stRel`.
2. `unfold_sem`: for a closed `step` with `SemV [] step (!U(Ref 1 ⊸ F(1 ⊗ Ref 1) & F 1))`,
   `SemV [x : Ref 1] (unfoldE step x) (U St)`.
3. `take2_close_runs`: `alloc`, `unfold`, `next`, `next`, `close`. It runs from empty memory
   to `()` with empty memory. This is the linear `close`.
4. **Negative check.** A version without `close` cannot be typed at `F 1`. The claim is only
   that no `CDerives` rule forgets a `U C` (`Fundamental.lean:107-126`), which can be checked
   by listing the rules.

**Probe P-Imm̲** (pure syntax, no model). Take a small `VTy` extension with `μ`/`tvar`.

1. `immReborrow_unroll`: `Imm̲ 'b (T[μX.T/X]) = (Imm̲ᵡ 'b T)[Imm̲ 'b (μX.T)/Y]`, for every `T`.
2. `naive_ne` (by `decide`/`rfl`): at `L = μX. 1 ⊕ (1 ⊗ Ref X)`, the naive clause's unrolling
   differs from `Imm̲ 'b (T[L/X])`.

**R4 (the fork; the real risk).** Add `μ` to CBPVWorld's `VTy`, with a `RefPos.mu` case.
Prove `reborrow_vShape` at `μ` and `withload_compatX` at `Imm 'a L`
(`Compatibility.lean:317`). Run `borrowHead`: `withbor` a list, then `withload` it, and read
`1 ⊕ (1 ⊗ Imm 'b L)`. A stretch goal is a total **borrowed fold** (recursion nested inside
successive `withload`s), `ifold : … ⊸ ∀'a. Imm 'a L ⊸ F R`. Its proof would be by induction
on the least-fixed-point derivation of the observable payload, and it is **not derived, not
verified**. The tail's derivation is a sub-derivation of the parent's payload. Whether that
rank survives the `withload` boundary, where the callback sees only `vC (Imm̲ 'b L)`, is the
question.

---

## 7. Downstream effects to watch

- **Iterators over a borrowed boxed structure.**
  - An *external* `Iter<'a>` over `Imm 'a L` would keep the current tail borrow as its state.
    That borrow lives at the `withload`'s `'b` and cannot leave the load
    (`experiments/Records/README.md:77-80`, `not_outlives_own_view`). Giving it `'a` is the
    same-lifetime projection P2, refuted in `Projection`/`Relaxed`/`FrameEnd`
    (`experiments/README.md:15-17`). So external iteration over a borrowed boxed list waits
    on P2.
  - *Internal* iteration (fold or visitor) needs R4's borrowed fold.
  - `IterMut` over `Mut 'a L` is the `Mut` projection (`mut_view_rejected`), and it is
    blocked the same way. **[read / expected]**
- **Iterators over a family** (`experiments/Places`). A list of leaf places,
  `μL. 1 ⊕ (Ref A ⊗ L)`, can be borrowed at one lifetime by a `withborN` defined by fold, with
  a higher-order result `(∀'c. List(Mut 'c A) ⊸ ['c]T) ⊸ …`. An `IterMut` whose state is
  `List(Mut 'c A)` is then a `ν` boxed at `'d ⊏ 'c`. That is the dynamic-length version of
  Places (e), and a good U4 test (`docs/dream-properties.md:17`). The Places side condition
  excludes `⊸`/`∀`/`Unk` in the result type outside `!` (`Places/README.md:58-61`), so a
  result holding a stream must be `[@d]`-boxed.
- **Iterator adapters** (U1). `map`/`zip`/`take` are productive coiterations. `filter`,
  `skip_while` and `find` are not productive on a possibly infinite stream, so their `next`
  lands in `D` (or the iterator is `νX. D(…)`). Rust leaves this implicit; here it is in the
  type.
- **Handlers and `yield`** (E1, `dream-properties.md:72`).
  - A generator is the resumption `νX. F(B ⊕ (Op ⊗ U(Res ⊸ X)))`, and a handler is a
    coiteration over it.
  - Deep handlers of possibly infinite computations land in `D`. Total deep handlers exist for
    the `μ` (W-type) free monad, which needs §2.2's admission of `X` under a `U`-codomain.
  - One-shot linear continuations are `U(Res ⊸ X)` used once (C6).
- **Deforestation (C1, `dream-properties.md:38`).**
  - `unfold` followed by `fold` is a hylomorphism. It terminates when the intermediate is `μ`,
    and lands in `D` when it is `ν`.
  - Fusion is an *equation*, and the model here is unary. Stating C1 needs a binary relation,
    which nothing here builds.
  - To keep fusion stateable, give fold and unfold as named constants with their own rules,
    not as ad hoc Z-terms.
- **The corpus (U1, `dream-properties.md:14`).**
  - Linked list: `μ` + `Ref` + fold.
  - Parser: fold over the input, or `D`.
  - Graph algorithms: `D` or fuel.
  - Growable vectors and hash maps need dynamic arrays, which this note does not address.
- **F4** (`dream-properties.md:29`). This design is an alternative to a second,
  step-indexed model. Divergence is a *type* (`D`), not a capability, and leak freedom at
  `D` holds on every finite prefix once there is a `close`. Whether F4 is still wanted once
  `D` exists is open.

## Summary of risks, in order

1. **R4.** The chooser/invariant proofs at the new `RefPos.mu` case, and a borrowed fold.
   Unknown.
2. **The environment in `vC`/`cC`** and the substitution lemma behind `unroll`/`out`. Real,
   bounded.
3. **`Imm̲` at `μ`.** The clause must substitute under `Ref`/`Mut`/`Imm`/`!`. Expected to be
   syntactic.
4. **`close` for `bind`.** Continuations must be `!` or finalizable. A design choice.
5. **A direct `fix` rule.** Not derived. General recursion goes through resumptions instead.

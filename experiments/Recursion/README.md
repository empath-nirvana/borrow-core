# Recursion: the first probe of `μ`, `ν` and `Imm̲` at `μ`

**Question.** `docs/scope-recursion.md` §6 proposes recursion without step-indexing: finite data
as an impredicative least fixed point (`μ`), codata as a greatest fixed point observed finitely
(`ν`), and a `Imm̲` clause at `μ` that substitutes inside the payloads it keeps. Before `μ` is
added to a type grammar (R4), does each piece hold for one fixed recursive type, over
`experiments/CBPVWorld` imported unchanged?

Build: `lake build Recursion`. Nothing in `Paper/`, `Support/`, `Examples/` or another experiment
is changed; `CBPVWorld` is imported as it is, with no fork. No recursive type is added to `VTy`
or `CTy`: each is written out by hand as a predicate over `vC`/`cC`'s clauses.

| File | Contents |
|---|---|
| `Recursion/Fix.lean` | the Z combinator over BoCa's untyped `λ`; `closedAt` and its substitution/shift lemmas |
| `Recursion/Mu.lean` | P-μ: the boxed list |
| `Recursion/Nu.lean` | P-ν: the stream with `close` |
| `Recursion/ImmMu.lean` | P-Imm̲: `Imm̲` at `μ`, pure syntax |

Every result's axioms are `[propext, Classical.choice, Quot.sound]` or a subset. There is no
`sorry`, `axiom`, `native_decide`, `implemented_by`, `opaque`, `partial` or `unsafe`.

## The Z combinator (`Fix.lean`)

For a functional `F = λself. λx. B`, `X = λx. F (λv. x x v)`, `selfV = λv. X X v` and
`fixV = λx. B[selfV/self]`. `wpTS_selfV_in`: in any evaluation context `K`, `K[selfV w]` reaches
`K[fixV w]` by three β-steps in front of a `wpTS`. No new syntax and no new machine rule. `B`
must be closed above its two binders (`closedAt 2 B`), which is decided by `rfl` for a concrete
term.

## P-μ: `L = μX. 1 ⊕ Ref X` (`Mu.lean`)

- `listF P` is `vC`'s `⊕`, `1` and `Ref` clauses with `P b` for `vC b X`. `listF_vC`: at
  `P = vC · A` it is `vC` at `1 ⊕ Ref A`, so the functor is a transcription of the relation's
  clauses and not a paraphrase.
- `listRel = ⋂{P | listF P ⊆ P}`, over predicates `Bool → List SRec → LSub → Val → WProp`
  (joint over the mode, as §2.1 says). Its definition needs no monotonicity.
- **`listRel_unroll`**: `listRel ↔ listF listRel`, from `listF_mono` (`listRel_roll`,
  `listRel_unfold`).
- **`listRel_outlives`**: `[TR]` 6.60's shape: a list outlives every `α`, by induction on the
  least fixed point.
- **`listRel_local`**: `Ext`-stability, `vC_local`'s shape, by induction on the least fixed point.
- `approx n` is the finite unrolling `1 ⊕ Ref (… (1 ⊕ Ref 0))`, a `VTy`; `listRel_of_approx`:
  each is contained in `L`.
- **`freeAll`** is `Z (λself. λl. case l {inj₁ u. u | inj₂ r. self (free r)})`.
  `freeAll_wp`: at a list `v`, `freeAll v` has a `wpTS` to `()` at every record list, by
  induction on the least fixed point (the `inj₂` case is `wp-free`, then the Z unrolling, then
  the induction hypothesis). **`freeAll_sem`** is its semantic type `U(L ⊸ F 1)` (`vLolliL`: `vC`'s
  `U`, `⊸` and `F` clauses with `listRel` at `L`); `freeAll_semV` the value judgment.
- **`build3Free_runs`**: `freeAll (inj₂ (alloc (inj₂ (alloc (inj₂ (alloc (inj₁ ())))))))`. The
  list is built by a `CDerives` derivation at `approx 3` (`build3_derives`), `fundamentalC` gives
  its `wpTS`, and `freeAll_wp` continues it. `theorem32` gives a run from the empty memory to `()`
  and the empty memory. `build3Free_eval`: the interpreter agrees (`unitNoLeak`, by `decide`).

Not done: `L` is not a `VTy`, so `freeAll_sem` is stated with the hand-written `vLolliL`, not as
`SemV [] freeAll (U(L ⊸ F 1))`, and `build3Free` is not a `CDerives` derivation. The list holds
`own` cells only, so `listRel_outlives` holds at every `α` and does not exercise the `μ` outlives
rule `Δ ⊢ T[1/X] ⊐ @a ⟹ Δ ⊢ μX.T ⊐ @a` at a payload with a bound. The mode index is carried but
never differs: `L` has no `U`, `Imm` or `Mut`.

## P-ν: `St A = νX. F(A ⊗ U X) & F 1` (`Nu.lean`)

- `stF A R` is `cC`'s `&`, `F`, `⊗` and `U` clauses with `R` for `cC X` (`next` is `π₁`, `close`
  is `π₂`). `stF_cC`: at `R = cC C`, for any `C` forced as it stands (`C.isRet = false`), it is
  `cC` at `F(A ⊗ U C) & F 1`. A thunk of `St` is forced by using it as it stands, which is §3.2's
  `forceE (νX.B) = forceE B`.
- `stRel A = ⋃{R | R ⊆ stF A R}`, a direct greatest fixed point `∃ R` over predicates
  `List SRec → LSub → Expr → WProp`. It is not a packed `∃S` value.
- **`stRel_iff`**: `out`/`roll`, from `stF_mono` (only `wpTS_mono`).
- **Coiteration.** `unfoldE st` is `λo. selfV x o` with `selfV = Z (λself. λs. λo. case o
  {inj₁ _. (st s π₁) to p. let (a, s′) = p in (a, λo′. self s′ o′) | inj₂ _. st s π₂})`.
  **`unfold_sem`**: for a closed step `st` with `SemC [] st (S ⊸ F(A ⊗ S) & F 1)` — the premise
  from which `bangThunkV` promotes it to `!U(…)` — a state `s : S` gives `unfold st s : U (St A)`.
  The proof is coinduction with the candidate `candR = {unfold st s | vC S s}`, the image of the
  state relation (`candR_post`): the `∃S` form as the proof, not the definition. `unfold_semV` is
  the same at the open term `unfoldE st` with the state substituted. `A` and `S` are arbitrary
  value types.
- **`take2Close_runs`**: `alloc () to r. unfold stepV r to t. π₁ t to p₁. let (a₁, t₁) = p₁ in
  a₁; π₁ t₁ to p₂. let (a₂, t₂) = p₂ in a₂; π₂ t₂`, with `stepV = λs. ⟨return ((), s), free s⟩ :
  Ref 1 ⊸ F(1 ⊗ Ref 1) & F 1` (`stepV_derives`, a `CDerives` derivation). It runs from the empty
  memory to `()` and the empty memory. The `close` observation frees the state.
  `take2Close_eval`: the interpreter agrees.
- **Negative check, by reading the rules (not machine-checked).** No `CDerives` rule
  (`CBPVWorld/Fundamental.lean`, `inductive CDerives`) forgets a `U C`: the `forget` constants
  are at `!A` (`forgetBang`), `Imm` (`forgetImm`), `Mut` (`forgetMut`) and `Unk` (`forgetUnk`);
  every other leaf rule asks `Ctx.Dead` of the rest of the context. `topI` and `zeroE` accept any
  context, but conclude at `⊤` or need a value of `0`. So a program that holds a stream can reach
  `F 1` only by `close`.

Not done: `St` is not a `CTy`, so the consumer is proved against `stRel` by hand (`consumer_wp`),
not derived. The step must be a closed value (`closedAt 0 st`), because it is written into the Z
term; `stepV_closed` is `rfl`. Passing the step as a runtime argument would remove the side
condition. The observation-depth alternative (`⋂ₙ Bⁿ ⊤`, §3.1) is not attempted.

## P-Imm̲: `Imm̲` at `μ` (`ImmMu.lean`)

`MTy` is `VTy` with de Bruijn type variables and `μ`; `rename`, `subst`, `Cl` (closedness) and
their composition lemmas are standard.

- `immG b pay` is `Imm̲ 'b` with a **payload substitution** `pay`. A variable at a head position
  (under `⊗`, `⊕`, `[@a]`) stays a variable. A payload kept by `Ref`, `Imm`, `Mut` or `!` has
  every variable replaced by the closed type it stands for. At `μX. A` the new variable stands for
  `μX. A` itself. `immReb b = immG b dflt` on closed types; `immX b T` is `Imm̲ᵡ 'b T`.
- **`immG_subst`**: `Imm̲` commutes with every substitution, for a closed `pay`, by induction on
  the type (`immG_rename` for the binder).
- **`immReborrow_unroll`**: `Imm̲ 'b (T[μX.T/X]) = (Imm̲ᵡ 'b T)[Imm̲ 'b (μX.T)/Y]` for every `T`
  with at most `X` free, an instance of `immG_subst`. `immReb_mu`: `Imm̲ 'b (μX.T) = μY. Imm̲ᵡ 'b T`.
- **`naive_ne`**: at `L = μX. 1 ⊕ (1 ⊗ Ref X)`, the clause `μX. Imm̲ 'b T` with `Imm̲ 'b X = X`
  unrolls to `1 ⊕ (1 ⊗ Imm 'b (μX. 1 ⊕ (1 ⊗ Imm 'b X)))`, while `Imm̲ 'b (T[L/X])` is
  `1 ⊕ (1 ⊗ Imm 'b L)` (`immReb_unroll_list`). `guarded_eq`: the guarded clause gives the latter.
  `tree_agree`: at the inline tree `μX. 1 ⊕ (X ⊗ X)` the two clauses agree.
- `toV_immReb`: on `μ`-free closed types, `immReb` is CBPVWorld's `VTy.immReborrow`.

## Against the scope note

- The note's `Imm̲ᵡ` substitutes `X ↦ μX.T` in the payloads. With nested `μ` the payloads also
  mention outer variables, so the clause needs an environment of payload types, one per bound
  variable (`pay`), not only `X`. With that environment the unrolling law holds for every `T`.
- The coinductive candidate is indexed by the lifetime substitution too:
  `List SRec → LSub → Expr → WProp`, `cC`'s signature (the note writes `List SRec → Expr → WProp`).
- A closed step or fold body written into a Z term carries a syntactic closedness side condition
  (`closedAt`). The note's suggestion to give fold and unfold as named constants with their own
  rules avoids it at the term level.
- Everything else in §6's P-μ and P-ν came out as the note says: the Z unrolling is pure head
  steps; the least fixed point needs monotonicity only for `unroll`; the greatest fixed point needs
  only `wpTS_mono`; `close` makes a terminating stream program a closed `F 1` program with an
  empty final memory.

## What R4 should expect

- The relation-level fixed points cost little once the functor is fixed: `listF_mono` and
  `stF_mono` are a few lines each. In R4 the functor is `vCE η` at an arbitrary `T`, so
  monotonicity becomes an induction on `T` under the positivity table of §2.2. This probe does not
  test the `Imm` clause under `μ`, where `CohE` reads the syntactic type, nor `Mut`.
- The syntactic side of `Imm̲` at `μ` is settled for every `T` (`immReborrow_unroll`). A `VTy.mu`
  needs de Bruijn type variables and the same `rename`/`subst` lemma set as `MTy`.
- The chooser and invariant proofs at a `RefPos.mu` case, 6.131 at `μ` and the borrowed fold are
  untouched here. I have not derived them and have not verified that any obstruction is real.
- The main friction in this probe was substitution bookkeeping on terms (shifts of a state value
  under the unfold's binders); the `closedAt` lemmas and `wpTS_selfV_in` are reusable.

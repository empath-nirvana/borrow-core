# CBPVWorld: the typed world re-typed at CBPV types

**Question.** `experiments/CBPVCore` put the borrow calculus into a CBPV core over the typed
world of `Support/TypedWorld`. That world's records and coherence are typed at BoLo's `Ty`, so
CBPVCore's `Imm` clause read `CohE` through a call-by-value preimage. As a result:

- `Imm @a A` is empty wherever `A` has no preimage;
- the borrow axioms exist only at `cbv T`;
- `[]I` needs translated types;
- `∀E` needs `F (cbv T)`.

Does the typed world, re-typed at CBPV types, remove all four restrictions while keeping the
Fundamental Property and adequacy?

Build: `lake build CBPVWorld`. The model below the typed world is imported unchanged from
this repository's `Paper`/`Support`: resources, the BoLo logic, `wp`, reborrowing, the machine, and `Support/Model`,
`Support/Dynamics`, `Support/Lifetimes`. The typed world (`Support/TypedWorld/*`) is forked.

## Design

- **Types** (`Types.lean`).
  - `VTy ::= 1 | A ⊗ B | 0 | A ⊕ B | U C | Ref A | Imm @a A | Mut @a A | [@a] A | !A | Unk` and
    `CTy ::= F A | A ⊸ C | C & D | ⊤ | ∀'x ⊏ @b. C`. These are CBPVCore's, redefined here.
  - `VTy.recV` is the value-type eliminator, with `U C` as a leaf.
  - `VFree`/`CFree` give the free lifetime variables.
  - `VTy.applyLSub`/`CTy.applyLSub` are capture-avoiding lifetime substitution. The `∀` binder
    is renamed as `Ty.applyLSub` renames it. `CTy.instLife x a C` is `C[@a/'x]`.
  - `VOutlives` is `OutlivesRules` on `VTy`, plus `0`. `CtxOutlives` is `Ctx.Outlives`.
    `VScoped` says the free variables are in `dom(Δ)`.
  - `VTy.lolli A B := U (A ⊸ F B)` and `VTy.all x b A := U (∀'x ⊏ @b. F A)`. These are
    abbreviations for BoLo's arrow and `∀`, read call-by-value. The axiom types `axSwapTy`, …,
    `axWithloadTy` are `[TR]` p. 3's table written with them, at arbitrary `VTy` payloads.

- **The `Imm̲` metafunction** (`VTy.immReborrow`):

  | `A`            | `Imm̲ 'b A`                |
  |----------------|---------------------------|
  | `1`            | `1`                       |
  | `A ⊗ B`        | `Imm̲ 'b A ⊗ Imm̲ 'b B`     |
  | `0`            | `0`                       |
  | `A ⊕ B`        | `Imm̲ 'b A ⊕ Imm̲ 'b B`     |
  | `U C`          | `Unk`                     |
  | `Ref A`        | `Imm 'b A`                |
  | `Imm @a A`     | `Imm @a A`                |
  | `Mut @a A`     | `Imm 'b A`                |
  | `[@a] A`       | `Imm̲ 'b A`                |
  | `!A`           | `!A`                      |
  | `Unk`          | `Unk`                     |

  `U C ↦ Unk` because codata has no safe view, as BoLo's `⊸`/`∀ ↦ Unk`. `!A` is kept whole
  because it holds no resource.

- **The forked typed world.** Every record and every transition is typed at `VTy`:
  - `FrameRec.T`, `RefPos`, `MutPos`, `Chain` and `GPos` (`Records.lean`). None of them has a
    constructor at `U` or `0`.
  - `Coh`, `AgreeOn` and `AdmWf` (`Records.lean`).
  - `TyEq` (`Records.lean`). It is mutual with `CTyEq`: `U C` against `U C′` is `CTyEq`, and
    `∀` compares the bodies at every `α`.
  - `vShape` (`World.lean`). It is `True` at `U C` and empty at `0`.
  - `TW` (`World.lean`), including `immFrame`'s type, `reb`/`rebDeep`'s `Imm̲` and
    `rebEndDeep`'s `S₀`.

  `Images`, `Invariant`, `Wp`, `ReborrowShapes`, `Reborrow`, `FrameRules` and `Compatibility`
  are the typed world's files, transported mechanically:
  - `Ty` becomes `VTy` and `LFree` becomes `VFree`;
  - each induction on a type becomes `induction … using VTy.recV`;
  - each `⊸`/`∀` case becomes the `U` case, and a `0` case is added. In a `0` case the relation
    or the shape is `False`.

  No proof was re-derived. `Reborrow`, `FrameRules` and the bulk of `Compatibility` built
  unchanged after the transport.

- **The relation** (`Relation.lean`). `vC b A` and `cC C` are CBPVCore's mode-indexed relation,
  except that the `Imm` clause reads coherence at the payload itself:

      vC b (Imm @a A) ls δ v = [@aδ = α] ∃ℓ. ⌜v = ℓ ∧ CohE (rsOf ls) ℓ A δ⌝ ⋆ ℓ ↦ I_α (vC false A)

  `SemC`/`SemV`, `gSepC`/`gDenC`, `forceE` and the term encodings are CBPVCore's.

## Results

Every result's axioms are `[propext, Classical.choice, Quot.sound]`, or a subset of them. There
is no `sorry`, `axiom`, `native_decide`, `implemented_by`, `opaque`, `partial` or `unsafe`.

**1. Types and substitution** (`Types.lean`, `RelationFacts.lean`)

- `TyEq`/`CTyEq`:
  - `.symm`, `.trans`, `.of_agree` and `.refl`;
  - `TyEq.extend_left` and `TyEq.immReborrow`;
  - `TyEq.applyLSub`/`CTyEq.applyLSub` (`Δ-subst`, with the capture-avoiding `∀` branch) and
    `TyEq.instLife`/`CTyEq.instLife`.
- `vShape_tyEq`.
- `vC_tyEq`/`cC_tyEq`: the relation reads a type only up to `TyEq`/`CTyEq`. These are the
  analogues of `vX_tyEq`.
- `vC_congr`/`cC_congr` and `vC_extend_of_not_free`.

**2. The relation at the re-typed world** (`RelationFacts.lean`, `Computation.lean`)

- `vC_local`, `vO_obs`, `vC_vShape`, `obs_transfer`, `relabel_obs` and `image_vC_of_shape`:
  the choosers' inputs at `vC`.
- **`vC_outlives`**: `[TR]` 6.60 at `vC`, both modes, for `VOutlives`.
- `cC_iff_stacks`, `cC_step`/`cC_head`, `cC_bind`, `semC_dead` and `semC_liveEq`: CBPVCore's
  lemmas, unchanged.

**3. Compatibility** (`Compatibility.lean`, `Compat.lean`)

- The borrow axioms, each at arbitrary value-type payloads, with the side conditions of the
  typed world's lemmas:
  - `alloc_compatX`, `free_compatX`, `swap_compatX` and `copy_compatX`;
  - `forgetImm_compatX`, `forgetMut_compatX` and `forgetUnk_compatX`;
  - `withbor1_compatX` (scoping as `VScoped`), `withbor2_compatX` (side condition as
    `VOutlives`) and `withbor3_compatX`;
  - `withload_compatX` (6.175) and `withswap_compatX`.
- **`boxI_compatC`** (`boxI_compatX`): `[]I` at every value type and every context, from
  `CtxOutlives`, via `gSepC_outlives` and `vC_outlives`.
- **`allE_compatC`**: `M [] : C[@a/'x]` at every computation type `C`, via `cC_tyEq` at
  `CTyEq.instLife`.
- Every CBPV former and `!` rule of CBPVCore: `var`, `unitI`, `tensorI`, `sumI₁/₂`,
  `thunkF`/`thunkV`, `ret`, `bind`, `force`, `lam`, `app`, `withI`, `proj₁/₂`, `topI`, `unitE`,
  `tensorE`, `sumE`, `zeroE`, `allI`, `bangThunkF`/`bangThunkV`, `bangE`, `copyBang`,
  `forgetBang`, `boxE`, `immSub` and `mutSub` (`_compatC`).

**4. Judgment, Fundamental Property, adequacy** (`Fundamental.lean`)

- `CDerives` is CBPVCore's judgment with no `cbv` in any rule:
  - `allE` is at any `C`;
  - `boxI` is at any `A`, with premise `CtxOutlives Δ Γ a`;
  - each borrow axiom is at any payload;
  - `allI`'s dead binder slot is at any type `S` (sound by `semC_liveEq`).
- Three call-by-value derived forms, used by the embedding (§6):
  - `lolliE`: `f a : B` for `f : A ⊸ B` (`VTy.lolli`) and `a : A`, both arbitrary expressions
    (`lolliE_compatX`);
  - `allEV`: `e [] : A[@a/'x]` for `e : ∀'x ⊏ @b. A` (`VTy.all`) (`allE_compatX`);
  - `ofRet`: a computation of `F A` is a value-judged expression at `A` (`SemV` is `SemC` at
    `F A`, so the rule is sound by the premise itself).
- **`fundamentalC : CDerives Δ Γ e j → SemJ Δ Γ e j`.**
- **`adequacyC`**: a closed `F 1` derivation runs from the empty memory to `()`.
  - `theorem32` and `corollary33` are `[CONF]` 3.2/3.3 at this world's `wpTS`.
  - `reclaim` is `Adequacy.reclaim`'s argument, copied, so that `Fundamental.lean` does not
    import `Paper.CONF.Results`, which imports the old typed world.
- `exProg_runs` is CBPVCore's `U`/`&`/`⊤` program.

**5. Programs** (`Examples.lean`)

- `cImmBorrow_derives`/`cImmBorrow_runs` and `cBang_derives`/`cBang_runs`: CBPVCore's two
  programs, re-derived in this judgment and run.
- **`cRecBorrow_derives`/`cRecBorrow_runs`** is the non-vacuity check. A cell holds a record of
  methods `M = U (F 1 & F 1)`.
  1. It is borrowed immutably with `withbor` at payload `M`. The borrower receives
     `Imm 'a M`.
  2. The borrower loads through the borrow with `withload`. The loader receives
     `Imm̲ 'b M = Unk` and `forget`s it.
  3. After the borrow ends, the cell is freed, the thunk is forced and `π₁` is called.

  The program derives at `F 1` and runs to `()` from the empty memory. CBPVCore cannot type it:
  `Imm @a M` has no `cbv` preimage, so its relation there is empty (`vC_imm_outside_image`),
  and its `withbor`/`withload` are not available at `M`.
- `cInst_derives`/`cInst_sem`: `∀E` at a computation type that is not an `F`, with a real
  substitution. `f : U (∀'b ⊏ ⊓∅. ['b]1 ⊸ F 1)` is instantiated at `'a` under
  `Δ₁ = 'a ⊏ ⊓∅` and applied to a `['a]1`. The program is open in `'a`, so its semantic judgment
  comes from `fundamentalC`; adequacy does not apply.

**6. The call-by-value embedding of BoLo** (`Embedding.lean`, `EmbeddingExamples.lean`)

- `cbv : Ty → VTy`: `T₁ ⊸ T₂ ↦ VTy.lolli T₁⁺ T₂⁺ = U (T₁⁺ ⊸ F T₂⁺)`,
  `∀'x ⊏ @b. T ↦ VTy.all x b T⁺ = U (∀'x ⊏ @b. F T⁺)`, every other former to its namesake.
  `cbvCtx` maps it over a context's slots.
- Facts along `cbv`: free variables (`lFree_iff_vFree`), `cbv_lifeBound`, substitution
  (`cbv_applyLSub`, `cbv_instLife`: both sides rename a `∀` binder under the same condition to
  the same variable), `cbv_immReborrow`, the ten axiom types (`cbv_axSwapTy`, …), outlives
  (`vOutlives_cbv`), scoping (`vScoped_cbv`), and `Ctx.Dead`/`Ctx.Solo`/`Ctx.Split`/`!Γ`/
  `Δ ⊨ Γ ⊐ @a` along `cbvCtx`.
- **`embed : DerivesWf Δ Γ e T → Δ.Ok → Ctx.ScopedB Δ Γ → CDerives Δ (cbvCtx Γ) e (.val (cbv T))`**,
  on the same term, by induction on `DerivesWf`; every rule embeds. The two hypotheses are those
  of the typed world's Fundamental Property (`Typed.fundamental`). Rule by rule:
  - `var`, `1I`, `⊗I`, `⊕I`, `[]I`, `[]E`, `⊑Imm`, `⊑Mut`, `!E` and every axiom map to their
    namesakes;
  - `1E`, `⊗E`, `⊕E` are CBPV's eliminators with the body at `F T⁺` (`ret`), read back with
    `ofRet`;
  - `⊸I` is `thunkV (lam (ret …))`, `∀I` is `thunkV (allI … (ret …))`, and `!I` at `λ`/`Λ` is
    `bangThunkV` over the same;
  - `⊸E` is `lolliE` and `∀E` is `allEV` (with `cbv_instLife`).
- **`adequacy_of_derivesWf : DerivesWf ∅ [] e 1 → BoLo.Steps ∅ e ∅ ()`**: `embed`, `ret`, then
  `adequacyC`.
- `EmbeddingExamples.lean` runs every closed program of `Paper/Examples/Programs.lean` and
  `Examples/Closures.lean` this way (`allocFree_runsC`, `fig2c_runsC`, `immBorrow_runsC`,
  `mutBorrow_runsC`, `loadClosure_runsC`, `aliasLoad_runsC`, `swapTwo_runsC`,
  `greetProg_runsC`, `ownedFn_runsC`, `mutClosure_runsC`).

## What remains restricted

No rule has a `cbv T` restriction. The remaining restrictions are these:

- **The borrow axioms have their printed side conditions:**
  - `¬ VFree x` on the payloads (6.132, p. 48);
  - `VScoped Δ A` for `withbor` (1);
  - `∃ b. Δ ⊨ b ∧ Δ ⊢ A ⊐ b` for `withbor` (2).
- **The axioms have their call-by-value types.** For example, `swap : U (Ref A ⊸ F (U (B ⊸ F
  (Ref B ⊗ A))))`. The terms are BoCa's curried λ-values, and this is the type their
  evaluation has. A natively curried CBPV type such as `U (Ref A ⊸ B ⊸ F (Ref B ⊗ A))` is a
  different computation and is not provided.
- **`VOutlives`** has `OutlivesRules`' formers, plus `0`. It has no rule at `U C` or `Unk`, as
  BoLo has none at `⊸`/`∀`/`Unk`. So `[]I` cannot box a context holding a thunk that is not
  under `!`.

## Open

- **Agreement with the old world on translated types** (a `vX_eq_…`-style check) is not
  attempted. The two worlds are different families: `TW` over `FrameRec` with a `Ty` field, and
  `TW` over `FrameRec` with a `VTy` field. Agreement would first need a translation of worlds
  and record lists along `cbv`, and it would carry `wpTS` across it.
- **The embedding is into the value judgment with three call-by-value derived forms**
  (`lolliE`, `allEV`, `ofRet`). CBPV's own `app` takes a variable argument and its `allE` a
  computation-judged term, so BoLo's `⊸E` and `∀E` on arbitrary subterms are not derived from
  them without a term translation; none is attempted.
- **A closed program that uses `∀E` at a non-`F` type and runs** is not given. `cInst` is open
  in `'a`. Closing it needs a `withbor` callback to bind `'a`.

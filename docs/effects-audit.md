# Effect system coherence audit (#288)

This audit asks whether the effect system works as **one proof algebra**, whether it uses BoLo's
machinery consistently, and whether it matches the established algebra of effects.

It was read only. Nothing was built and no gate was run.

| reference | state audited |
|---|---|
| `main` | 8a1c326 |
| PR #284 `gfp` | `Below.lean` |
| PR #285 `gfp-arising` | `Arising.lean` |
| PR #287 `borrow-callbacks` | `Extend.lean`, `docs/effects-tr/17-borrow-callbacks.md` |

**How the audit was run.**

1. Five inventories: kernel, surface, models, the ghost-end line, and a literature baseline.
2. Four lenses applied to them: algebra-of-effects conformance, proof-algebra coherence, ad hoc
   wiring, and global assumptions broken by local results.
3. An adversarial check of every finding. Skeptics refuted four findings (listed in §4.4), and
   corrected several of the survivors. The corrections are folded in below.

**Status marks.**

- **[Lean]**: the claim is about a declaration I located by name.
- **[read]**: a reading of code or documents.
- **[R]**: a literature claim from recall that has not been re-read (see the literature baseline in
  §5).

**Nothing in this document is a machine-checked obstruction.** Where a finding says something is
missing, it means "not built". It does not mean "cannot be built".

---

## 1. Executive summary

**Verdict: CONSOLIDATE.** Do not re-found, and do not settle for clean-up.

**The kernel's unary core is coherent, and it conforms to the literature.** It is the one place
the system really is a single proof algebra.

- One generic protocol, `opTable`, drives `ewpTS`, the least fixed point of `wpG`. `wpG` is
  [TR] p.6's `wp`, relativised to the typed world `TW` of resources that arise.
- All six §19 rules, cancel, the unwinding borrows, the ν observation leaves and `bounded_fix`
  go through that one relation, `vC`/`cC`. They are justified by BoLo's own frame rules,
  6.64–6.66 over `wpG`.
- Leak freedom (`wpTS` requires a `NoOwn` leftover), effect safety (`ewp_bot`) and adequacy are
  corollaries of one fundamental property: `fundamentalC`, `adequacyC` and `adequacyD`.

That is what a conforming system looks like, so re-founding is not warranted.

**Around that core, the effect system is not one algebra.** It is several mechanisms joined by
elaboration and by relations built beside the kernel. Five structural objects that the literature
puts at the spine are missing, and much of the observed wiring substitutes for them:

1. **No single signature object.**
   - The kernel `Row` is a first-match list of `(name, op)` keys.
   - The frontend `EffSig` is string-named and split into `fn` and `ctl` effects.
   - Answering (`fn`) effects never become a kernel row at all.
2. **Models and comodels are two unrelated mechanisms.**
   - Control effects are `hnd`/`perform` checked against `opTable`.
   - Answering effects are capability passing over `withswap`, and no table ever checks them.
   - TR D4.6 ("one protocol for model and comodel") is not a kernel fact.
3. **No law-bearing handler theory over the kernel.**
   - `hnd` has step rules but no stated H-ret, H-op or H-fwd lemma.
   - `handle_compatC` is a bespoke five-case induction, not "a model of Σ yields a homomorphism".
   - The kernel's law file (`Core/Handlers.lean`) describes the withdrawn decision-52 sum encoding.
   - Every algebraic law (algebraicity, H-laws, tensor, ν, η, no accidental handling) is proved
     only on standalone toy carriers in `experiments/EffModelRel`. Those carriers have no
     resources and no machine, and their contexts are unmoded.
4. **No world component for lends across a suspension.**
   - `wpG` requires every stop, including a stop at `perform`, to have closed every 6.64 frame
     and reborrow record it opened (`Core/EffDefs.lean:27–40`).
   - That one clause is where T1 comes from.
   - The whole ghost-end line (Restrat, GhostEnd steps 0–3l, PRs #284/#285/#287) works around
     it from outside. It built five relation families beside `vC`/`cC`, eight copies of one
     least-fixed-point piece, and about 45 predicates.
   - `TW`'s own index `ps` is already a stack of open frames.
5. **No row-generic borrow.**
   - There are 7 pure borrow constants and 6 `*U` twins, gated by `Row.Unwind` (abortive only).
   - There is no effectful `withswap`.
   - The callback row classes that the kernel (`Row.Unwind`), GhostEnd (`LinResume`) and the
     TR (`[lend]`, `req = lin`) admit are pairwise exclusive. A `Fail ⊕ Yield` callback fits
     none of them.

**Why CONSOLIDATE and not CLEAN UP.** Deleting dead code and correcting documents is necessary,
but it does not supply objects 1–5. **Why CONSOLIDATE and not RE-FOUND.** Each missing object
can be added on top of the existing `ewpTS`/`opTable`/`TW` core, and some can be added inside
it, without replacing it.

**The one technique that runs consistently through the whole line is worth keeping.** Take a
printed frame lemma over `wpG` (6.64/6.65/6.66, which never inspect the final term) and lift it
to the effect wp by induction on the least fixed point. This gives:

- `ewpTS_*_frameU` (in Core);
- `ewpTS_M_frameR`, `ewpTS_M_antiFrameR`, `ewpTS_I_frameR`;
- `OpenS` with `stack_step_*`.

**On tier 2.** #279 set a hard stop: "a new unknown, a reduction to a new lemma, a new construct
… tier 2 halts and the language ships at tier 1 (T1 kept)". By that rule tier 2 has already
halted. The record:

- #284 reported a reduction (the guard).
- #285 introduced a new construct (`vRLa`).
- #287 introduced another (`vRLk`) and a new open item (Kripke monotonicity over stack
  extension).

This audit therefore recommends **shipping at tier 1** and doing the consolidation that does not
depend on tier 2 (§6, steps 1–6). Any reopening of tier 2 (step 7) is the user's decision, and it
should be one bounded attempt at the single structural change the evidence points to.

---

## 2. Coherence map

### 2.1 Semantic settings in play

| # | setting | world | relation | Lean | relation to the kernel |
|---|---|---|---|---|---|
| K | **kernel** | `WRes` × `List SRec` (`Ext`); `TW` inside `wpG` | `vCE`/`vC`/`cC`/`cB`; `ewpTS` at `opTable` | Core, full FP | **the one relation of record** |
| S1 | phase A | CK machine with counters | finite context suite (`#guard`) | runs only | none |
| S2 | phase B binary | name bijections (`[Inj,Set]` + statuses), trees | `TreeRel`, `LR`, `CtxEq` (denotational, unmoded) | own FP + soundness | none; no resources, no machine (T6.6 paper) |
| S3 | phase B unary | trees + `Own` token multiset | `TS`/`VS`/`CS`, moded `VM`/`CM` | own FP + safety | none |
| S4 | cell model | Nat-levelled places | `TS (VSt L) L` | own adequacy | none; no typing maps into it |
| S5 | TR §§3–6 | TR's CK machine + BoLo `Res` at the own fragment | `wpG`/`ewp` + Π_E | paper | mirrors K by name, over a different machine |
| S6 | TR §§14–17, GhostEnd | K's world × lend stack σ (+ αs, `TabAtS`) | `vRL`, `vRLg`, `vRLs`, `vRLa`, `vRLk` | partial | wraps K's `vC`; equal at σ = [] only by `propext` (and not shown for `vRLk`) |
| R | Restrat | Paper/Support carrier | `vDen` naturality | partial | separate carrier |

Every algebraic law in the project is proved in S2. All of the GhostEnd and stacked Lean is in S6.
Only K carries a fundamental property over `CDerives`. [Lean]

### 2.2 Which pieces are the same structure under different names

| structure | its names | verdict |
|---|---|---|
| "`wpG` into value-in-Q or a table-allowed stop owing the continuation" (a least fixed point over `wpG`) | `ewpTS`; `Relend`, `Open`, `OpenD`, `RelendI`, `AntiRelend`, `NestRelend`, `NestRelend₂`, `OpenS`, `opTableO` | **one piece.** `OpenS` at depth \|σ\| subsumes the GhostEnd variants, and `ewpTS` is `OpenS` at σ = [] (`bodyS_nil_iff`). |
| a printed frame lemma lifted by lfp induction | `ewpTS_{I,M}_frameU`, `ewpTS_M_antiFrameU` (abortive, Core); `ewpTS_M_frameR`, `ewpTS_I_frameR`, `ewpTS_M_antiFrameR`; `stack_step_{other,reborrow,imm}`; `nested(₂)_relend` | **one technique.** Keep it. The 6.150 lift is missing. |
| a value relation | `vCE`; `vRL`, `vRLg`, `vRLs`, `vRLa`, `vRLk`; `vDen` (Restrat) | **one relation re-transcribed five more times.** Each copy handles ⊗/⊕/!/[@a]/Ref/U itself and sends Imm, Mut, μ, ν, [L] and type variables back to kernel `vC`. |
| the fundamental property | `fundamentalC`; `segment_fundamental`, `restrat_segment`, `gfpAt_nil`, `gfpAtA_nil` | **restatements of `fundamentalC`.** |
| a continuation obligation | `contShare` (stopped `K`), `KapRel` (reified κ), `cancelOwed` | **legitimately distinct.** One is about a stopped context and one about a reified value. A skeptic refuted the duplication claim (§4.4). |
| a handler | `hnd`/`[handle]`; answering handler (`withswap`); surface schemas (a) abort-after, (b) stateful, (c) plain; for-site; pull-site | **one construct in the literature** (a model, or a comodel for the answering case), **six code paths here** |
| an effect signature | kernel `OpSig`/`Row`; frontend `EffSig`/`OpSig`; TR D1.x; EffModelRel `Sig` | **no shared object.** The TR and S2 belong to a sibling calculus. The real gap is kernel vs frontend. |
| a row computation | E1 `rowV`/`rowC` (by name); E2 `opsC`/`opsV`/`fnRowOf` (by `(n,i)`) | **computed twice, with no lemma relating the two** |
| polymorphism over handlers | `copyFor`/`copyOf`, `groupCopy`, `layerCopy`, `deepCopy`, `Hof`, `makeInst` | **one monomorphisation.** Its justifying lemma (op-name renaming) is not built. |
| re-lendability | `FrameThaws(D)`, `StopSafe`, `URelend(RL)`, `KapRelR`, `CloL`, `Relendable`, `RelendableG/S/N`, `guardS` | `RelendableS/N` and `guardS` are live. **The rest is dead, superseded by `OpenS`.** |

### 2.3 What is glue

These items exist only to connect two mechanisms that the literature treats as one, or to stand in
for a missing structural object.

- **Kernel.** The `*U` borrow twins and `Row.Unwind` stand in for a row-generic borrow (object
  5). `Core/Handlers.lean`'s laws are the acceptance criterion of a withdrawn encoding.
- **Surface: elaboration paths.** The three `withCtl` schemas, `forSite`/`forYield` and
  `pullSite`/`pullView` stand in for "handler = model" (object 3).
- **Surface: shape recognisers.** `iterEff`, `exhEff?` (takes the *first declared* match),
  `driver?` and `isLayerTy` stand in for typed role declarations.
- **Surface: special names.** The magic binder `io_bt` and the name-based ambient
  `stdin`/`stdout`/`stderr`.
- **Surface: copies per assignment.** These stand in for the renaming lemma or ports.
- **Stacked line: indices.** The lend stack σ as a relation parameter, the lifetime vector αs
  with `ReLend`, and the guard `TabAtS` all stand in for a world component (object 4).
- **Stacked line: hypotheses.** `AllCross` (discharged only by constant `true`), `LinResume`,
  `Row.Resume`, `hTL`, `hβ`, `hσx`/`hσT`, `e.x ∉ σ`, `Tab.Local` and `hQa` each state one
  slice of a missing world preorder and its monotonicity lemma.

---

## 3. The unifying structure the evidence supports

The evidence supports a structure in four layers. Each layer is stated in terms of objects that
already exist in Core, wherever that is possible.

### 3.1 Layer 1: one signature, one protocol (algebra)

```
Sig      := finite set of ops  op : A ↠^q B   (param A, arity B, continuation qualifier q)
            (+ optional equations E; none today)
Row      := finite sum of Sigs, keys unique  (Row.Uniq everywhere, or quotient by it)
opTable  : Row → Table           -- exists; becomes the one interpretation of a Row
```

- **Handler.** A handler of `Σ` at carrier `C` is a **model**: clauses typed by `clausesTy`/`retTy`
  from `Σ`. Handling is the lfp, which is initial among models.
- **Capability.** A capability of `Σ` at state `S` is a **comodel**: a co-operation
  `Mut 'l S × A ⊸ F_{Σ'}(Mut 'l S × B)` per op, meeting the same `opTable Σ` protocol.
  `withswap` is its carrier.
- **Answering vs control** is then a choice of implementation for one signature, not a property
  of the declaration.
- **The PP08 restriction stays.** A theory with a constant (an abortive op) has only the empty
  comodel, which is why `Fail` cannot be answering.

### 3.2 Layer 2: one model lemma (CBPV)

```
IsModel Σ Φ  :=  Φ is closed under opTable Σ stops at every Ext-future world
```

- **Lemma M1.** `cC (Row.effOf Σ R)` and every `cC C` are Σ-models. This is the adjunction: every
  computation type is a model.
- **Lemma M2.** `ewp_handle` is "the lfp is initial among models". `ewp_let`/`ewp_then` are its
  free extension.
- **Lemma M3 (graded algebraicity, unary form).** An op stopped under `K` at grade `q` owes `K`'s
  share scaled by `q`, plus the destructor `D_K` when weakening applies. From M3:
  - `[let]`'s side conditions;
  - `[then]`/`ubind`;
  - κ's cancel entry in `kTy`;
  - `contShare`'s `unr ⇒ ∅` / `q ≠ lin ⇒ cancelOwed`.
- **Run lemmas H-ret, H-op (deep) and H-fwd** over `hndTerm`, stated next to `ewp_handle`.

### 3.3 Layer 3: one Kripke world with one preorder (BoLo)

```
W        := (ρ, ls, σ)    resource × frame records × open-lend stack
            where σ is TW's own ps/rs (open 6.64 frames and their lineages), not a new index
W ⊑ W'   := Ext ls ls' ρ  ∧  σ is a suffix of σ' (fresh entries above; ReLend on αs)
arising  := TW-reachable (ρ, ps, rs)      -- TW already is this inductive
```

- **The future-world quantifier stays at the kernel's existing Kripke points:**
  - `vCE`'s `U` clause;
  - `contShare`;
  - `KapRel`.

  It moves from `∀ ls' ⊒ ls` to `∀ W' ⊒ W`. The `⊸` and `∀` clauses get no quantifier and no
  guard. This is the CBPV placement. §17's "every clause that receives an outside value" is the
  CBV pattern, and it is the reason `vRLk` needed the quantifier at ∀ but not at `U` (proof-03).
- **One monotonicity lemma** for `gC` over `⊑`. `hTL`, `hβ` and the freshness side conditions
  become instances of it.
- **`TabAtS` becomes a `TW` invariant** (the generalisation of `wpG_tabAt`, from [TR] 6.50 by way
  of `wpG_tabAtS_one`). It is no longer a hypothesis inside the relation's clauses.
- **The stop condition.** This is the single change to the kernel's definitions. `wpG`'s
  post-condition at a *stop* is relativised to the table:

  ```
  value:  ps' = ps ∧ ls' = ls                  (unchanged: wpTS = wpG ∘ valPost is the printed wp)
  stop :  ps ⊆ ps' and the extra frames are handed to the table, which says what the continuation owes
  ```

  The printed value-time `wp` is untouched. The change is an added hypothesis on the table side,
  as CLAUDE.md §4 requires.
- **Core's `vC`/`cC` are the σ = [] instance by definition** (decision 20). They are not a
  sibling proved equal by `propext`.

### 3.4 Layer 4: one row-generic borrow

```
withborₖ  : one constant per printed borrow, indexed by row S, side condition  TableOK (opTable S)
TableOK T := T monotone ∧ its continuation obligation frames under 6.64/6.65/6.66 (+6.150)
```

- **Lift the frame lemmas once.** Lift 6.64, 6.65, 6.66 and 6.150 to `ewpTS` at any `TableOK`
  table, by the lfp-induction technique.
- **Instances.** `Table.Abortive` gives today's `*U` constants. The empty row gives the pure
  constants. A linear-resume table gives T1's case.
- **Prove `TableOK` closed under `OpTab.ext`, which is row sum.** Then rows are sums at a borrow
  too, and the effectful `withswap` falls out.

### 3.5 How each existing piece maps onto this structure

| piece | fate |
|---|---|
| `ewpTS`, `opTable`, `wpG`, `TW`, `Ext`, `vCE`/`cC`, `fundamentalC`, `adequacyC/D` | **keep.** `cC` is re-indexed by `W`, and `σ = []` is the base case. |
| `contShare`, `KapRel`, `cancelOwed` | **keep.** Their quantifier becomes `∀ W' ⊒ W`. |
| `ewpTS_*_frameU` | **keep** as the abortive instance of the general lift |
| `ewpTS_M_frameR`, `ewpTS_I_frameR`, `ewpTS_M_antiFrameR`, `OpenS`/`bodyS`/`stopS`/`ghostS`, `stack_step_*`, `RelendableS/N`, `wpG_tabAt`, `Payload.lean` facts (with `LOk`, which `Payload.lean` uses) | **promote** to Core under a spec entry. These are the reusable core. |
| `TabAtS`, `tabAtS_comp`, `wpG_tabAtS_one` | **promote** as the TW invariant |
| `vRL`, `vRLg`, `vRLs`, `vRLa` | **retire** once `cC` is re-indexed |
| `vRLk` | **retire.** Its content (future stacks) moves to the `U`/`contShare`/`KapRel` quantifier. It has no `vRLk_nil`, so it may be strictly stronger than the kernel at [] (proof-02). |
| GhostEnd steps 2–3f: `Open`, `RBody*`, `FrameThaws(D)`, `StopSafe`, `TV/TVG`, `fz*`, `KernelInvariant`, `O151AsStated`, `CloL`, `KapRelR`, `URelend`, `RelendableG` | **retire.** Pull out the helpers `Stacked.lean` reaches through its import chain first. |
| Restrat | **retire** everything except `Audit.lean` and the counterexample cell. Restate `not_vDenNatural` as "over all valid resources". |
| `not_gfp` (#284) | **do not merge under a `not_` name.** Its witness does not arise (#285). |
| the `*U` constants and their compat lemmas | **become abbreviations** of the row-generic borrow (decision 20) |
| `Core/Handlers.lean` abort laws | **relabel** as laws of a withdrawn encoding, or delete. Answering laws are restated as comodel facts. |
| EffModelRel S2–S4 | **keep as evidence**, marked "model of a sibling calculus". They have no standing as kernel results. |
| surface schemas (a)–(c), for-site, pull-site | **keep.** Each is proved to meet H-ret/H-op/H-fwd against `hnd`. Name the pull-site as the shallow handler. Move `d_handleAbortCapture` into Core. |
| shape recognisers, `io_bt` | replace with typed role declarations and a typed field on the desugared block |
| copies per assignment | justified by the op-name renaming lemma over `CDerives` |

---

## 4. Ranked incoherences

The severity marks are mine, reconciled with the skeptic notes. Each finding gives its root cause,
then its remedy.

### 4.1 Critical

**C1. `wpG`'s stop condition makes lend nesting lexical across suspension.** [read]
(`Core/EffDefs.lean:27–40`; `ewpStep = wpG (valPost Q ∨ Tb …)`)

- **What happens.** A stop at `perform` must satisfy `ps' ↔ ps ∧ ls' ↔ ls`. T1 and
  `Row.Unwind` are consequences of this one clause.
- **Root cause.** [TR]'s `wp` closes frames at the value because BoLo has no suspension. When
  `wpG` generalised the final term, it kept that value-time equality at stops. The effect layer
  then added "no new world component", so every attempt to span a stop built a second world
  beside `TW`.
- **Remedy.** §3.3: relativise the stop condition to the table, with `TW`'s `ps`/`rs` as the
  lend component. Leave `wpTS` unchanged.

**C2. Answering effects (comodels) and control effects (models) are unrelated mechanisms.**
[read]

- **What happens.**
  - The kind is fixed per effect, with no mixing of `fn` and `ctl`.
  - `withswap` calls are never checked against a `Table`.
  - The answering laws are run facts about elaborated terms.
  - Nothing relates `handle_fold` to `ewp_handle`.
- **Root cause.** S1a predates kernel rows (decisions 48/51). Decision 55 added control effects
  beside them without re-deriving S1a.
- **Remedy.** §3.1: a capability is a comodel of the same `Sig`, checked against `opTable`.
  Prove an answering handler equals `hnd` with a tail-resumptive state clause, or demote one
  path to an abbreviation.

**C3. Every algebraic law is proved only off the kernel.** [Lean]

- **What happens.**
  - `h_ret`, `h_op`, `h_fwd`, `tensor`, `idem_nu`, `nu_nu`, `new_nu`,
    `no_accidental_handling` and `soundness` are in S2.
  - S2 has no resources and no machine, and its `CtxEq` is unmoded. That is why ν/op is refuted
    even at linear ops, with O1 open.
  - No binary relation exists on Core (T16).
- **Root cause.** Phase B was built standalone for speed. Phase A's question 5 (the bridge) was
  never attempted.
- **Remedy.**
  - State the unary halves over `ewpTS`/`CDerives`: the step laws and graded algebraicity.
  - Record T16 as the single missing object for every binary law.
  - Mark S2–S4 as models of a sibling calculus.

**C4. The borrow callback row classes are pairwise exclusive, so rows are not sums at a borrow.**
[read]

- **What happens.**
  - `Row.Unwind` admits only abortive ops.
  - `LinResume` admits only linear resuming ops.
  - TR `[lend]` requires `req = lin`.
  - So a `Fail ⊕ Yield` callback fits none of them.
  - (Skeptic correction: `AllCross` is about stop depth, not linearity.)
- **Root cause.** Each line fixed the table class its frame lemma could carry, and nobody stated
  a table-level predicate that all three instantiate.
- **Remedy.** §3.4: `TableOK`, closed under row sum. Until then, record mixed rows at borrows as
  uncovered, and add no further row class.

### 4.2 Major

**M1. The stacked line has five relation families beside the kernel's, each wrapping `vC`.**
[Lean]

- **What happens.**
  - `vRL`, `vRLg`, `vRLs`, `vRLa` and `vRLk` re-transcribe ⊗/⊕/!/[@a]/Ref/U.
  - They fall back to kernel `vC` under Imm, Mut, μ, ν, [L] and type variables. So a `U` inside
    a `Mut` payload, a stored generator, `Aff` or a ν cell is read at the wrong relation. Those
    are exactly where lend-spanning callbacks get stored.
  - `vRLs_nil` and `vRLa_nil` are `propext` equalities, and no Core consumer was re-pointed.
  - (Skeptic correction: these *are* proved extensions at [], and experiments not being in Core
    is process, not a breach. Severity is major, not critical.)
- **Remedy.** Re-index `vCE`/`cC`/`cB` themselves (§3.3).

**M2. `vRLk` may be strictly stronger than the kernel at σ = [].** [Lean]

- **What happens.** It has no `vRLk_nil`/`cRLk_nil`, and its ∀ clause ranges over every future
  stack, so `cRLk [] ⊆ cC` and the converse is unproved. If the two differ, `fundamentalC` no
  longer gives FP at [], and adequacy would need a new FP.
- **Remedy.** Make `cRLk_nil` the first obligation, or adopt §3.3, which keeps ∀ unchanged.

**M3. The future-stack quantifier sits in the wrong place for CBPV.** [read]

- **What happens.** The kernel quantifies over the future only at `U`, `contShare` and `KapRel`.
  §17 puts it on `⊸`/∀, while `vRLk`'s `U` clause stays at the same σ. A thunk created at σ and
  forced at `τ ++ σ`, which is the callback case, is not covered.
- **Remedy.** §3.3. (Whether this removes every guard is a hypothesis to be tested with a Lean
  configuration, not prose.)

**M4. The world is split across four indices, with no monotonicity lemma.** [Lean]

- **What happens.**
  - The four indices are the resource, `Ext`, αs/`ReLend` and σ.
  - Core has only `Ext.refl`/`Ext.trans`; there is no `vC`-monotonicity lemma.
  - Extend.lean itself names the missing lemma (gRLk at σ ⇒ at τ ++ σ).
- **Remedy.** One preorder and one lemma (§3.3).

**M5. Arising for stacks is enforced by a guard in the relation, and proved at one entry only.**
[Lean]

- **What happens.** `guardS = TabAtS → P` sits at `U`, `⊸` and ∀. `wpG_below_not_arises` is
  stated only for `[e]`. The guard was asked for in 3f, dropped in 3h, refuted for its absence
  in 3j and re-added in 3k.
- **Skeptic correction.** This is **not** CoherentX. `TabAtS` is ⋆-compositional
  (`tabAtS_comp`) and run-invariant from [TR] 6.50. The defect is placement (a hypothesis inside
  the clauses) and coverage (one entry).
- **Remedy.** Make it a `TW` invariant at every stack (§3.3).

**M6. GFP at a non-empty stack has never been run against the rule set.** [Lean]

- **What happens.**
  - About 8–9 rows of ~60 are proved at a stacked relation (skeptic count): `force`, `thunkF`,
    `thunkE`, `app`, `allE`, `lam`, `allI`, and `withbor` at depth 1.
  - `bind`, `then`, `handle`, `unfold` and `boundedFix` are untested. GFP is not even stated at
    `vRLk`.
  - The relation was redesigned three times without a whole-rule-set check.
- **Root cause.** Agents were sent at the next refutation rather than at the full classification.
- **Remedy.** Before any relation change, write the GFP statement with the full row skeleton
  (rows as enumerated `sorry`s in an experiment).

**M7. Borrows are constants duplicated per row class.** [Lean]

- **What happens.**
  - There are 7 pure constants and 6 `*U` twins, each with an ~80-line compat lemma (`Core/EffBorrow.lean`
    :275, :356, :446, :548, :645, :726).
  - There is no effectful `withswap`.
  - T1 would need a third family.
- **Remedy.** §3.4.

**M8. `AllCross` and `LinResume` shrink the algebra so the stack step goes through.** [Lean]

- **What happens.** Instances discharge `AllCross` only by constant `true`. Its consequences:
  - a handler between two lenders (#278) is excluded;
  - affine and aborting ops at the lender are excluded, and with them cancel.
- **Mitigation.** Both are documented as added hypotheses.
- **Remedy.**
  - One induction on depth `k` with a split `σ = σ_in ++ σ_out` at the handler. A single n→n+1
    induction is allowed; per-depth instances like `stack2_*` and `stack3_*` are not.
  - The affine case through the existing `ResumeAff`/`opTableO`.

**M9. Handlers bind no extent.** [read]

- **What happens.** `effHandle` opens no lifetime, so a handler frame has no place in a
  lifetime-ordered σ. That is the #278 gap, and the same gap that makes generative labels need
  T2.
- **Remedy.** A kernel decision: either a handler site opens a stratum, or "handler between
  lenders" becomes a named restriction (§7, Q3).

**M10. `hnd` has no handler laws, and the kernel's law file is stale.** [Lean]

- **What happens.**
  - `abort_passes`, `return_resumes` and `loop_abort` are about decision 52's sum encoding.
  - Decisions 48 and 52 are not marked superseded. PR #234, which corrects 48, is still open.
  - Decision 53's acceptance laws cover none of the current control schemas.
- **Remedy.** Lemma M3 and the H-laws (§3.2). Mark 48 and 52 superseded.

**M11. `handle_compatC` is a case analysis, not a model lemma.** [Lean]

- **What happens.** It works through five hand cases, and a new row kind means a new case
  analysis.
- **Remedy.** M1/M2 (§3.2).

**M12. Linear algebraicity is spread over four encodings, and `cancel_compatC` does not exist.**
[Lean]

- **What happens.** The four encodings are `[let]`, `[then]`, `kTy` and `contShare`.
  `cancel_compatC` is named in SPEC.md:2764, but no declaration has that name.
- **Remedy.** Lemma M3. Correct the SPEC to name `ewp_ccatch`/`cancel_frame`.

**M13. Static names are justified, but their companion lemmas are missing.** [Lean]

- **What happens.**
  - There is no op-name renaming lemma, so copies per assignment are not shown to be typing
    artefacts.
  - There is no kernel no-accidental-handling theorem.
  - SPEC §19 justifies re-entry by "operation types are closed in lifetimes", which is not a
    premise of `effHandle` (only `Row.Unwind` enforces it).
- **Remedy.** Prove the renaming lemma. Then either add the closure premise to `effHandle` or
  delete the sentence.

**M14. The TR's rule fixes amend a calculus no code implements.** [read]

- **What happens.**
  - The §10 fixes (owning lend, `Res` as instance, scaled capture) and T5.1 are over the moded
    calculus.
  - `CDerives` has no modes, independence or instances.
  - The kernel avoids `retTwice` by making clauses `!`, and that choice forces schema (b) and the
    `io_bt` rejection.
- **Remedy.** Record in the TR which kernel rule replaces each fix, or lift the statics.

**M15. The surface has six handler schemas and no laws for five of them.** [read]

- **What happens.** `d_handleAbortCapture` lives only in `experiments/SecondClass`. (Skeptic
  note: it is built from kernel rules only, so its location is a placement issue, not a
  soundness gap.)
- **Remedy.** §3.5.

**M16. Copies per assignment are the polymorphism mechanism, without a justifying lemma.**
[read]

- **What happens.** PR #233 (R2a) was closed as first-order only, and #161 is blocked.
- **Remedy.** The renaming lemma (M13), before more schemas are built on copying.

**M17. The open-problem chain is one obligation renamed six times.** [read]

- **What happens.** The chain O3 → O5 → O14.1/O15.1 → GFP → `not_gfp` → guard → §17 is the
  obligation "an internal lend open at a suspension", which is C1. Meanwhile the working
  technique was never assembled into a closing proof.
- **Remedy.** Fix the world once (C1), then grind the rule table.

**M18. The finaliser discipline was sized to the abortive frame lemmas.** [read]

- **What happens.** Under decision C:
  - finalisers are abortive only;
  - region errors are suppressed;
  - `withswap` has no unwinding form;
  - the `close` residual is open;
  - the effectful `Aff` has positivity only.
- **Root cause.** These limits were not derived from the destructor law.
- **Mitigation.** They are stated openly in the SPEC.
- **Remedy.** Give one destructor law, coinciding with arity-0 algebraicity, and one open item:
  "finalisers at a non-abortive table".

### 4.3 Minor

| # | incoherence | remedy |
|---|---|---|
| m1 | Sum vs tensor is never declared. `Row.Uniq` is required only by `[then]`. Signals and capability tensor appear only as examples. | Declare rows as sums. Classify cancel as a signal. Give the unary disjoint-capability frame fact. |
| m2 | The interaction law is open. P13.14 (fails at affine ops) is by hand, which breaks the "negatives are machine-checked" rule (and even when checked it would be about S2). | Machine-check P13.14 or withdraw it. |
| m3 | Recursion, div, layers and `Aff` sit outside the effect algebra. They are recognised by shape, and `exhEff?` takes the first declared match. | Typed role declarations. Until then, reject ambiguity. State the ⊥ law (no `D_K`) for `Loop_Σ`. |
| m4 | Magic binder `io_bt` as a cross-pass protocol (`Parser.lean:1146`, `Effects.lean:1387,1404`) | A typed field, or reborrow outer places at the `with`. |
| m5 | Ad hoc per-lemma world hypotheses (`hTL`, `hβ`, `hσx`/`hσT`, `e.x ∉ σ`, `Tab.Local`, `hQa`) | Derive them from the preorder (§3.3). Until then, keep them named, as the README already partly does. |
| m6 | 6.150 is not lifted to resuming tables (`Frames.lean`'s section has only I-Dup), and freshness is handled by side conditions instead of И. | Transcribe 6.150 at `ewpTS` as printed, before `withloadU` is restated. |
| m7 | Two `not_` refutations over witnesses not checked to arise: `not_gfp` (#284) and Restrat's `not_vDenNatural` | Rename them, or state the arising hypothesis. |
| m8 | Dead GhostEnd/Restrat code. It is still transitively imported by `Stacked.lean`. | Prune it with the re-index (§3.5). |
| m9 | Document drift. The SPEC Status says §19 is "in progress". `15-mut-cell.md` reuses D14/L14/T14 labels. TR §11.6/§12 are stale against #249. effect-model §8.3 says "writers commute: open". `hnd_sim` is not reconciled with O7. The `Effects.lean` docstring uses the decision-51 spelling. | A doc pass (§6, step 1). |
| m10 | No exactly-once/LIFO finalisation theorem as a named corollary. No kernel abstraction safety. | A corollary of `adequacyC`. Abstraction safety goes with M13. |

### 4.4 Findings refuted by the skeptics

These are listed for transparency and are not relied on.

- **"The continuation obligation is written three times, and `cB` duplicates `cC`."** `contShare`
  (stopped `K`) and `KapRel` (reified κ) are about different objects. `cB` is deliberately trivial
  at ∀/⊤/ν. Neither collapse is possible.
- **"Dead code is kept against decision 20."** The 3f deletion list is conditional on the kernel
  re-index, which has not happened. The files are also transitively imported.
- **"`guardS` is CoherentX returning."** `TabAtS` is ⋆-closed and run-invariant (see M5).
- **"The only Lean unary FP is on a token multiset."** It is false: `fundamentalC` and
  `adequacyD` over `ewpTS` *are* "BoLo wp + protocols" in Core. What remains true is that the TR's
  L5.4/T5.2 are not restated as Core corollaries.

---

## 5. Conformance against the algebra-of-effects baseline

Items marked [R] in the literature baseline have not been re-read and should be verified before
anything cites them as laws.

| # | baseline item | literature | borrow-core | status |
|---|---|---|---|---|
| 1 | one signature object | Plotkin–Power; Plotkin–Pretnar | kernel `Row` and frontend `EffSig` are separate, and answering effects are never a row | **missing** |
| 2 | free model + uniqueness of handling | PP13 | the operational stand-in exists (stops `K[op v]`). Uniqueness (binary) exists only in S2 and `handle_fold`. | partial; binary missing (T16) |
| 3 | handlers are models; H-ret/H-op/H-fwd; H-unique; H-correct | PP13 | step rules exist, laws are not stated over `hnd`. Proved in S2. No equations, so H-correct is vacuous. | **missing in kernel** |
| 4 | one graded algebraicity law giving `[let]`, `[finalise]`, ⟨resume, cancel⟩ | Tang et al. POPL'24; CMD ESOP'26 | four encodings; destructor law unstated | **scattered** |
| 5 | rows are sums; tensor for independence; signals = tensor with 0-ary | HPP06; Ahman–Bauer | first-match lists; tensor only in S2 (`PureCo`); cancel is a machine rule | **undeclared** |
| 6 | capabilities are comodels of the same signature; running = model ⊗ comodel; constant-theory limit | Plotkin–Power 08; Møgelberg–Staton; Ahman–Bauer | capabilities are `withswap` passing outside rows. The limit is respected in effect (Fail is `ctl`). Interaction law open. | **missing** (C2) |
| 7 | instances + four ν laws, or a fixed-constant design; abstraction safety | Staton LICS'13/POPL'15; Zhang–Myers; Biernacki et al. [R] | static names, a recorded deviation (T2, #173). ν laws in S2, with ν/op open (O1). No renaming lemma, no kernel abstraction safety. | **justified deviation, companions missing** |
| 8 | qualifiers from the signature; persistence; LIFO destructors; exactly-once finalisation | Tang; Affect; Ahman–Bauer Thm 7; CMD26 | qualifiers on `OpSig` ✓; `[let]` persistence ✓; LIFO by machine ✓; leak freedom by `NoOwn` ✓; no named exactly-once theorem | **conforms; one corollary missing** |
| 9 | computation types are uniformly models (CBPV adjunction) | Levy; EEC [R] | `cC` at each former; no `IsModel` lemma; TR §13.6: "no §7 proof gets shorter" | **missing** |
| 10 | one Kripke world, one preorder, one monotonicity lemma, allocation only in compat lemmas, well-foundedness from strata | ADR'09; Pitts–Stark; Timany'18; λRust | the kernel has one world (`Ext`) with the quantifier at `U`/stops, and strata instead of steps ✓. The stacked line has four indices, no monotonicity lemma and a guard. | **kernel conforms; extension does not** |
| 11 | all unary safety theorems are corollaries of one FP | ADR; [TR] | kernel ✓ (`fundamentalC` → adequacy, leak freedom, effect safety). S2–S4, GhostEnd and Restrat each re-prove their own. | **kernel conforms** |
| 12 | a binary relation, or recorded as the single missing object | — | T16 not built and not recorded as such | **record it** |

**Justified deviations.**

- No runner for an abortive theory (PP08).
- Static names instead of ν.
- LIFO, stratified borrows.
- `NoOwn` totality.
- No step-indexing, because strata provide well-foundedness.

**Accidental deviations.**

- The `fn`/`ctl` split per effect.
- Constants per row class.
- Multiple carriers.
- The stale law file.
- The missing signature object.
- The lexical stop condition carried over from the value-time `wp`.

---

## 6. Recommended path

The general rule applies throughout: **a single n → n+1 induction is fine. A chain of per-depth
instances, or a new construct introduced to close a step, halts the step**, and it is reported as
a named `def … : Prop` or an arising Lean configuration, never as prose.

**The fallback for every step is tier 1, with T1 kept**: callbacks pure or abortive, as on `main`
today.

Steps 1–6 do not depend on tier 2 and should be done regardless.

1. **Correct the record (documents only).**
   - Mark decisions 48, 52 and 53 superseded by 55, which lands or replaces PR #234.
   - Fix the SPEC Status for §19 and the `cancel_compatC` reference.
   - Renumber `15-mut-cell.md`'s labels.
   - Update TR §11.6/§12 and effect-model §8.3.
   - Reconcile `hnd_sim` with O7.
   - Add a banner to `docs/effects-tr/README.md` and `effect-model.md`: "S2–S4 are models of a
     sibling calculus; no result transports to `CDerives`".
   - Record T16 as the one missing object for every binary law.
   - **Hard stop:** none. Documents only.
2. **Decide on the unmerged PRs.**
   - Do not merge #284 under a `not_` name.
   - Close #285 and #287 as experiments, with their findings recorded here and in §17. Their
     reusable facts (`tabAtS_comp`, `wpG_tabAtS_one`, `all_elimK`) are kept on their branches for
     step 7.
   - Freeze GhostEnd. Delete nothing until the re-index, per decision 20.
   - **Hard stop:** none.
3. **Handler laws over the kernel (unary).**
   - State H-ret, H-op (deep) and H-fwd as run/`ewpTS` lemmas over `hndTerm`, next to
     `ewp_handle`.
   - Restate or delete `Core/Handlers.lean`'s abort laws.
   - This needs a spec entry.
   - **Hard stop:** if any law needs a new relation or a new world component, stop. They are step
     facts and should not.
4. **One graded algebraicity lemma (M3)**, with `let_compatC`'s side conditions, `then_compatC`
   and κ's cancel entry re-derived from it.
   - **Hard stop:** if the re-derivation needs a side condition not already on the rules, report
     that condition and keep the current proofs.
5. **One signature object; capabilities as comodels.**
   - Add a Core `Sig`, with `Row` as a sum, and give E1 and E2 one shared row function.
   - State the comodel protocol over `opTable` and prove that a `withswap` clause meets it, which
     makes D4.6 a kernel lemma.
   - **Hard stop:** if the comodel protocol needs a table class beyond `opTable`, stop and report.
     That would make C2 a design question for the user (§7, Q1).
6. **Op-name renaming lemma over `CDerives`/`cC`.**
   - Corollaries: copies are meaning-preserving, and no accidental handling.
   - Resolve the SPEC's "closed in lifetimes" sentence.
   - **Hard stop:** this is one induction on the derivation. Any need for a second relation halts
     it.

Step 7 depends on tier 2 and needs the user's decision (§7, Q2). It is offered as **one bounded
attempt**.

7. **Re-index the kernel relation by the product world (§3.3–3.4).**
   1. **Spec entry first.** It states the stop-condition relativisation, `W` and `⊑`, the
      quantifier at `U`/`contShare`/`KapRel`, and `TabAtS` as a TW invariant.
   2. **Skeleton.** In an experiment, write the re-indexed `cC` and its GFP statement with **all
      ~60 rows** as enumerated `sorry`s, and the monotonicity lemma as one more.
   3. **Routine rows first**, then the non-routine ones: thunk, `⊸` application, bind, `[then]`,
      `[handle]`, `withbor*`, `unfoldN`, `boundedFix`.
   4. **Lift 6.64/6.65/6.66/6.150 once at `TableOK`**, by lfp induction, reusing
      `OpenS`/`stack_step_*` with depth `k` handled by **one** induction.
   5. **Hard stops:**
      - the relation needs a second redesign;
      - any row needs a new construct or a new predicate not in the spec entry;
      - depth needs per-depth lemmas;
      - `σ = []` fails to be `cC` by definition;
      - the monotonicity lemma does not close by one induction.

      On any of these: report it and ship tier 1.
   6. **On success:** delete per §3.5 in the same change (decision 20), and turn the `*U`
      constants into abbreviations.

---

## 7. Open questions requiring the user's decision

1. **Answering vs control.** Should answering (`fn`) effects become comodels of a kernel `Sig`
   checked against `opTable` (step 5)? Or should the two mechanisms stay separate, with the
   relationship recorded as a deliberate design choice? This decides whether D4.6 is a goal.
2. **Tier 2.** By #279's hard-stop rule, tier 2 has halted: #284, #285 and #287 each reported a
   new reduction or construct. Do you
   - (a) ship tier 1 and close the line, or
   - (b) authorise the single bounded attempt of step 7, which changes `wpG`'s stop condition in
     the kernel?
3. **Handler extent.** Should a handler site open a lifetime (a stratum in the world), so that
   "a handler between two lenders" (#278) has a place? Or should it be a named restriction of
   the relation? This also bears on generative labels (T2, #173).
4. **Binary relation.** Is T16 (a binary relation over Core's world) in scope? If not, every
   binary law (H-unique, tensor, ν, η, hiding) stays at "model of a sibling calculus" for good,
   and the docs should say so.
5. **EffModelRel's standing.** Keep S2–S4 as evidence with a banner, or archive them?
6. **Role declarations.** Should recursion, iteration, exhaustion and layers be identified by a
   typed role declaration in place of shape recognition (m3)? That is surface syntax, so it is a
   one-way door to weigh.
7. **Finalisers.** Is "finalisers at a non-abortive table" (the effectful `Aff`, the unwinding
   `withswap`, the `close` residual) wanted at tier 1, or deferred together with tier 2?

---

### Unspent and untranscribed items (CLAUDE.md §5)

**Printed lemmas in the run-up that are not transcribed at resuming tables:**

- 6.150 (with its И freshness);
- 6.64 at an `Imm` table beyond `ewpTS_I_frameR`;
- O2, 6.65's `↭` steps line by line.

**Open items stated but not derived:**

- O1 (a `def`, open);
- T6.6 (machine–tree agreement, paper only);
- `cRLk_nil`;
- Kripke monotonicity over stack extension;
- P13.14 (by hand).

I have not verified that any of these is an obstruction.

# 00 · The structure of the effect calculus

This file fixes the one structure every section of the specification uses. It names the
objects of the calculus and their notation, gives every kernel construct, law and metatheorem
a stable id with the section that owns it, indexes the open questions (whose register is
[99-open-questions.md](99-open-questions.md)), lists the named restrictions, and states what each
section must contain. A section adds an id or an object only by editing this file first.

The calculus specified here is **the** effect calculus of borrow-core's kernel: syntax,
statics, dynamics, semantic model, equational theory and metatheory, over BoLo's resource
world (Wagner et al., *From Linearity to Borrowing*, PACMPL 9 OOPSLA2, 2025; `[TR]` is its
supplement). It is not a fragment and not an encoding. Effectful closures, effectful
generators and recursions, stored continuations, and continuations that hold borrows are in
the calculus by design. Where something cannot be specified yet, it is a boxed open question
with a default, and every place it would narrow the calculus is a named restriction (§7.2).
Nothing is narrowed silently.

Tracking issue: #290. Input: `docs/effects-audit.md` (#288, PR #289), with the corrections
recorded in §0.3.

---

## 0. Conventions

### 0.1 Marks

- **[Lean]**: a claim about a declaration, cited `file:line`.
- **[read]**: a reading of code or documents, cited.
- **[via X]**: a literature claim taken from a report that read the passage (X is the report:
  the literature study on #235, `docs/effects-tr/12-sources.md`, or
  `docs/effects-tr/17-borrow-callbacks.md`), marked as that report marks it.
- **[I]**: an inference made in this specification from a cited source or definition, not a
  statement of that source. It may motivate and may appear in a proof sketch only as a step to be
  proved.
- **[user]**: a decision of the user, quoted with its source and strength (01 §4).
- **[R]**: recalled, not read. An [R] claim may motivate; it may not be cited as a law or used
  in a proof sketch. A section that needs it fetches the primary source and upgrades the mark.
- **as built / changed / new**: the status of a construct, definition or result against the
  kernel today (`Core/`, `Paper/`, `Support/`). **changed** and **new** at a kernel definition
  need a SPEC entry before any kernel work (CLAUDE.md §4 governs printed BoLo statements; a
  change to our own kernel definitions is a SPEC change, not an added hypothesis).

### 0.2 Standing rules for every section

1. **One world, one relation.** The only semantic objects are those of §1. A section that needs
   a new relation family, a twin constant or a side mechanism beside `W` reports it as a defect
   in an open question; it does not design one.
2. **BoLo's machinery, consistently.** Resource algebra, lifetime strata (`Life = ℕᵒᵈ`), the
   typed world of resources that arise (`TW`, `Core/World.lean:110`), the frame rules `[TR]`
   6.64 / 6.65 / 6.66, the reborrow `[TR]` 6.150, outlives (SPEC §23), the arising guard. No
   step-indexing.
3. **The paper is not wrong.** No printed BoLo lemma is called false, unsound or a gap. A step
   that will not follow is "cannot reconcile", with the step named, and the first question is
   which printed object we have not transcribed.
4. **Laws first.** A construct is specified together with the laws that define it (§4). A
   construct with no law entry is incomplete.
5. **Unknowns first.** Sections mark each obligation **unknown** or **mechanical**. For a
   mechanical one they name the single step most likely to be non-mechanical.
6. **A blocker is a claim.** An obstruction is reported only as a named `def … : Prop` that
   elaborates, or a configuration with every hypothesis discharged; otherwise "not derived, no
   obstruction verified".
7. **Mechanism before syntax.** The specification is of the kernel. Surface spellings appear
   only in 08, as the elaboration's source, and are provisional.
8. **Docs explain the thing.** No counts, no history, no puffery in the specification text.
9. **User positions keep their strength.** Multi-shot only if free; totality is not a goal and
   div is normal; effects are in the kernel; effect handling is erased at run time; no function
   colouring is the lead axis; threads are required eventually; externs and `unsafe` are
   outside the proofs; no Rust names for our constructs (Rust only as comparison); effects are
   one mechanism, with no fixed set of built-in control constructs; several effects at once
   (nested handlers, the reconciler chain) work, "full stop" (the handler that spans observations of
   the reconcile loop is K-HDIV, in the calculus; R-HDIV defers only its lift until OQ-67's proof,
   and is named as restricting U5 there, 01 §4); alloc is an effect (K-ALLOC, in the calculus;
   R-ALLOCORACLE defers its lift until OQ-68's proof); errors are a control-flow
   effect; cancellation is not interceptable; kernel-level equations (the binary halves of the
   laws) are optional unless needed for safety, while the unary halves over the kernel relation
   are required. 01 §4 records each with its source and strength.

### 0.3 Corrections to the audit carried into this specification

1. `experiments/HandlersAsBorrows` already unifies answering handlers with borrows: `handle`
   is `withbor` form (2), proved typed (`translate_typed`,
   `experiments/HandlersAsBorrows/HandlersAsBorrows/Translate.lean:190`) and safe
   (`effect_safety`, `…/Safety.lean:55`); an answering handler opens a fresh lifetime, and
   `handle_is_shift` (`…/Safety.lean:115`) places it in the shift schema of
   `experiments/Shifts` (`shiftTy`, `experiments/Shifts/Shifts.lean:17`).
   `experiments/HandlersControl` adds state behind control, re-entry and capture. Both are over
   `DerivesWf` and paper types, not `CDerives`; building on them is a rebuild through `embed`
   (`Core/Embedding.lean:235`), recorded as such in 08 §3.3. Whether a control handler is a
   borrow the same way is OQ-3.
2. Tier 2 did not halt by rule: #285 and #287 were continuations the user directed. Tier 1
   against tier 2 is OQ-2, open.
3. The placement of the future-world quantifier is OQ-8, to be settled by Lean, not prose.
4. The first unknown in relativising `wpG`'s stop is OQ-9: open **6.64** frames handed to a
   continuation that is cancelled, dropped or resumed between lenders. Its first probe is one Lean
   configuration at `[handle]` + cancel over a 6.64 lend (05 §12.1). Changing the stop is a kernel
   definition change and needs a SPEC entry.
5. Laws, graded algebraicity, `Sig` and renaming are stated over `W`, or shown to live at
   `σ = []` and survive the re-index (OQ-11). Nothing is stated over today's `cC` alone.

---

## 1. Objects and notation

Fixed once. Every section uses these names and symbols; none redefines them.

| id | object | notation | today | owner |
|---|---|---|---|---|
| O-LIFE | lifetimes, substitutions, contexts | `α, β : Life = ℕᵒᵈ`; `δ : LSub`; `Δ : LifeCtx`; `⊏`, `⊑` (a fresh lifetime is below every live one) | as built (`Paper/S5_Model`) | 05 |
| O-TY | value and computation types (CBPV) | `A, B ::= … \| U C \| !A \| [@a] A \| Ref A \| Imm a A \| Mut a A \| μ \| fam` (`fam L` is the array type, written `[L]`; `Imm̲` is a type metafunction, `VTy.immReborrow`, not a former); `C, D ::= F A \| F_Σ A \| A ⊸ C \| C & D \| ⊤ \| ∀'x ⊏ c. C \| νX. C` | as built (`Core/Types.lean`) | 03 |
| O-QUAL | continuation qualifier, read as a grade | `q ∈ {lin, aff, unr}` = `[1,1], [0,1], [0,∞]`; `rel = [1,∞]` is OQ-17; the grade of a row `g(Σ) = ⊔_{op ∈ Σ} q_op` (`g(∅) = [1,1]`); `Γ admits g` | `Qual`; grades in `experiments/Grades/Grades/Algebra.lean:58` | 02 |
| O-SIG | effect signature | `E = {op_i : A_i ↠^{q_i} B_i}_{i ∈ I}`, optional equations `Eq(E)`; `op_i` **abortive** iff `B_i = 0 ∧ q_i ≠ lin`; well-formedness `Δ ⊢ E sig`; `Closed E` (no free lifetime or type variable in an operation type; a premise only under OQ-35 (a)) | `OpSig` (`Core/Types.lean:147`), one operation per entry; no equations | 02 |
| O-NAME | names | `n, m ∈ Nm`; `⊥ = 0` reserved for cancel; a name is a handler site's static name (generative names: OQ-14) | `UInt32` names, `hn0 : n ≠ 0` | 02 |
| O-ROW | row | `Σ = n₁:E₁ ⊕ … ⊕ n_k:E_k`, a finite **sum** with distinct names; `Δ ⊢ Σ row`; `Σ₁ # Σ₂` disjoint names; `Σ ⊑ Σ'` inclusion; `Σ^abort` its abortive operations; `Σ^fin` the operations a finaliser may perform (`Σ^abort` under R-FINAB); `∅` the empty row; under OQ-3 (a) an entry carries its site's extent, `n:E @α_n`, and a row its lifetime `life(Σ)` | `Row = List OpSig`, first match (`Core/EffRules.lean:33-47`); `RowLe` (`:699`); `Row.Uniq` (`:746`) only at `[then]` | 02 |
| O-INT | interpretation of a row | `⟦Σ⟧δ : OpTab`, entries `⟨q, abort, P_A, P_B⟩` | `Row.tab` (`Core/EffRules.lean:47`), `OpEnt` (`Core/EffDefs.lean:104`) | 02 |
| O-TAB | protocol table | `Tb : Table`, read at the pre-stop world and the frames the stop added, `Tb (ls', σ) τ' t Φ`; `Tb.Mono`, `Tb.Abortive`; `opTable T`; `cancelTab T N`; `TableOK_x Tb` for a lend of variable `x`, and `TableOK Tb ≜ ∀ x. TableOK_x Tb` (new) | `Core/EffDefs.lean:50-65, 131, 157` | 05 |
| O-W | the Kripke world | `W = (ρ, ls, σ)`: `ρ : WRes`, `ls : List SRec`, `σ : List OEnt` the open-lend component, innermost first; its `imm` entries are a selection of `TW`'s own `ps`/`rs` (open 6.64 frames and their lineages), not a new index; what its `mut` entries record is OQ-44. The list `τ` of frames a resumed run must close is an index of `wpG_W`/`ewp_W` beside `W`, recorded as a defect in OQ-57 | `ρ`, `ls` as built; `σ` exists only inside `wpG`'s quantifier (`Core/EffDefs.lean:29`) | 05 |
| O-ORD | the world preorder | `W ⊑ W'` ≜ `Ext ls ls' ρ` ∧ `σ'` extends `σ` (fresh entries inside) — exact form in D-ORD, under OQ-8/OQ-9 | `Ext` (`Core/FrameRecords.lean:172`) only | 05 |
| O-ARISE | resources that arise | `TW ρ σ rs`, `Tagged`; the table guard `TabAtS σ αs ρ` as a `TW` invariant | `TW` (`Core/World.lean:110`); `TabAtS` (`experiments/GhostEnd/GhostEnd/Stacked.lean:290`) as a guard | 05 |
| O-WP | the generalised `wp` | `wpG_W(τ)(e){Q}`, `τ` the frames this run must close (OQ-57); `wpG_W(e) ≜ wpG_W([])(e)`; `wpTS = wpG ∘ valPost` the printed `[TR]` p.6 `wp` | `wpG` (`Core/EffDefs.lean:27-40`); `wpTS` (`Core/World.lean:186`) | 05 |
| O-EWP | the effectful `wp` | `ewp_W(τ)(e){Tb}{Q}`, one least fixed point indexed by `τ`, of `wpG_W(τ)` into "value in `Q`, or a stop `Tb` allows"; `ewp_W ≜ ewp_W([])` | `ewpTS` (`Core/EffDefs.lean:73-75`) | 05 |
| O-REL | the relation | `𝒱⟦A⟧_W δ`, `𝒞⟦C⟧_W δ`, `𝒢⟦Γ⟧_W δ`; `Δ; Γ ⊨ e : C`. `vC`/`cC` equal the `σ = []` instance by T-NIL: definitional at the **=** clauses, proved per introduction row at `U`, `share` and `KapRel`, where it is **unknown** (OQ-58) | `vCE`, `cC`, `cB` (`Core/Relation.lean:119, 154, 192`), `SemC` (`:228`) | 05 |
| O-KONT | continuations | `κ = ⟨resume, cancel⟩ : K_q(B, Σ, R)`; obligations `share` (stopped context), `KapRel` (reified `κ`), `owed` (cancel run) | `kTy` (`Core/EffRules.lean:976`), `contShare` (`Core/EffDefs.lean:144`), `KapRel` (`Core/EffRules.lean:569`), `cancelOwed` (`Core/EffDefs.lean:138`) | 03 (types), 05 (relations) |
| O-MODEL | a model of `Σ` (a handler) | `H = (h_ret, (h_op)_{op})` at carrier `C`; the derived judgement `Δ; Γ ⊢ H : Model(n:E ⇒ A; Σ; C)`; `IsModel_Σ Φ` | `retTy`, `clausesTy` (`Core/EffRules.lean:989, 994`); no `IsModel` | 02 (form), 05 (`IsModel`) |
| O-COMODEL | a comodel of `Σ` (a capability) | state `S` lent at `'l`; co-operations on the payload, `c_op : S ⊗ A_op ⊸ F_{Σ'}(S ⊗ B_op)`, run by `withswap` on the lent `Mut 'l S` (the `Mut` frame by 6.66 at the call), for non-abortive `op` (an abortive `op` has no co-operation at `Σ' = ∅`; a fallible co-operation's form is part of OQ-19 and OQ-20); the derived judgement `Δ; Γ ⊢ c : Comodel(n:E; S @ 'l; Σ')`; the capability type `Cap_l(E, S)`; carrier `withswap`; `IsComodel_Σ` | `withswap` (`Core/Types.lean:1906`); answering clauses elaborated per SPEC §18; no protocol check | 02 (form), 05 (`IsComodel`) |
| O-BOR | borrow constants | `bor_k[Σ]`, one per printed constant `k ∈ {withbor1, withbor2, withbor3, withload, sliceBorrowM, sliceBorrowI}`, at callback row `Σ` in the syntactic class `BorOK_x Σ` whose interpretation is `TableOK_x` (OQ-40), restricted by default by R-T1 and R-CLOSEDOP; `withswap` is not a shift | pure constants plus `*U` twins (`Core/Fundamental.lean:258-293`, `Core/EffBorrow.lean:181-209`) | 03 |
| O-FIN | finalisation | `M then x. N unwind D` (`ubind`); `D_K` the destructor of a context `K`: the nested stack `K°` of its finaliser frames, innermost first. Two forms: `D_K⟨e⟩ ≜ K°[e]`, **only for `e` a raise or a cancel**, which runs `D₁ (), …, D_k ()` LIFO because each frame's `[finalise]` fires (at a returning `e` the frames would run their continuations `N_j` instead, by `[then]`); and the sequential form `D_K ▷ e`, which runs `D₁ (), …, D_k ()` LIFO, each under the frames outside it, a finaliser's raise superseding and finalised outward, and then `e` outside all of them, for `e` that may return (04 K-CTX, 06 L-ALG0, L-HUNIQ); cancel state `(N, err)` | `ubind`, `ccatch`, `cfin` (`Paper/S3_Dynamics/Definitions.lean:513-545`) | 04 |
| O-JDG | typing judgement | `Δ; Γ ⊢ e : C` is `CDerives`; a row is a meta-index of the judgement, not a type variable (OQ-13) | `CDerives` (`Core/Fundamental.lean:60`) | 03 |
| O-EQ | equivalences | typed program contexts `𝒞 : (Δ; Γ ⊢ C) ⇒ (Δ'; Γ' ⊢ C')`; `≡` contextual equivalence and `≲` refinement, observed at `F_∅ G` under every allocator; `⇣_A^D` joinability up to `D`; `≅_W` unary interchangeability under every `TableOK`, `Irred` table; `≈` the binary relation over pairs of worlds (D-BIN, OQ-4) | none in Core | 06 |

**Reading of `W`.** `ρ` is BoLo's resource; `─⋆` and `wpG`'s frame are its future-world
quantifier, as in BoLo. `ls` is the record list ordered by `Ext`. `σ` is the stack of lends
open around the current term, which a stop hands to its continuation; its 6.64 frames are those
`TW` already carries as `ps`/`rs`, and the record of a 6.65 lend open across a stop is OQ-44.
Making `σ` a component of the world is the one structural change of the model (D-W, D-STOP). At `σ = []` the definitions
of 05 that read no extension of the world reduce to today's kernel by definition; those that
quantify over `W' ⊒ W` (`U`, `share`, `KapRel`) reduce to it only by T-NIL's per-row proof, which
is unknown at `U` (OQ-58).

---

## 2. Identifiers and the entry template

**Prefixes.** `O-` objects (§1) · `K-` kernel constructs (§3) · `D-` model definitions (§3.4)
· `E-` SPEC entries (§3.5) · `L-` laws (§4) · `T-` metatheorems (§5) · `C-` items of the "not an
approximation" checklist (01 §7) · `R-` named restrictions (§7.2) · `OQ-` open questions (§7.1,
99). Ids are stable: a withdrawn id is marked withdrawn, never reused.

**Every K, D, L and T entry in a section has this shape:**

```
### <id>: <name>
- Form:        the definition, rule, step, equation or statement, in §1's notation
- Uses:        O-/K-/D- ids
- Today:       file:line [Lean], or "not built"; status as built / changed / new
- Slices:      where its other facets live (e.g. typing 03, step 04, clause 05, law 06,
               compatibility 07, code and lowering 08)
- Depends on:  ids it needs first
- Open:        OQ ids; R ids that restrict it by default
- Obligation:  what must be proved, marked unknown or mechanical
```

---

## 3. Kernel constructs and model definitions

### 3.1 Signatures and rows (owner 02)

| id | construct | status |
|---|---|---|
| K-SIG | effect signature `E` (O-SIG): operations with parameter, arity, qualifier; abortive as the arity-0-with-weakening case; no operation type mentions its own row by default (R-NOSELFROW; K-SELFROW, OQ-61) | changed: grouped per effect, equations optional (OQ-22) |
| K-ROW | rows as sums (O-ROW), `[sub]` row weakening, `Σ^abort`, the empty row and `F A = F_∅ A` | changed: sum with distinct names, replacing first-match lists |
| K-NAME | names and instances: static site names, `⊥`, re-entry of a site, generative instances if adopted | as built static (OQ-14) |
| K-INT | interpretation `⟦Σ⟧δ`, and `opTable` as the one interpretation of a row | as built (`effTab_effOf`, `Core/EffRules.lean:49`) |
| K-THEORY | equations of a signature and handler correctness relative to them | new (OQ-22) |
| K-REN | renaming of names on terms, types and derivations | new |
| K-MODEL | the form of a model of `Σ` at a carrier `C` (clauses typed from `Σ`) | as built (`clausesTy`, `retTy`) |
| K-COMODEL | the form of a comodel of `Σ` at a state `S` (co-operations typed from `Σ`) | new as a kernel object (OQ-1, OQ-19) |

### 3.2 Terms and typing (owner 03)

| id | construct | status |
|---|---|---|
| K-FTY | `F_Σ A`, and every former at a row: `U(F_Σ A)`, `A ⊸ F_Σ B`, `&`, `∀`, `ν` with effectful leaves, `Aff` with an effectful body | changed: the former is as built (`CTy.eff`, `CTy.effOf` `Core/Types.lean:155`); `[thunkΣ]`, `[bangThunkΣ]` introduce `U(F_Σ A)` at a nonempty row |
| K-OP | `perform_{n,i} V`, a non-abortive operation | as built (`effPerform`, `Core/Fundamental.lean:343`) |
| K-RAISE | `raise_{n,i} V`, an abortive operation (errors are this, #168) | as built (`effRaise`, `:348`) |
| K-LET | `[let]` at a row, with the graded side condition on the abandoned or copied context | as built (`effLet`, `:353`) |
| K-THEN | `[then]`: `M then x. N unwind D`, the finaliser frame | as built (`effThen`, `:360`) |
| K-HND | `[handle]`: a deep handler of name `n` (a model), clauses `!` | as built (`effHandle`, `:367`); extent OQ-3 |
| K-KONT | the continuation `κ = ⟨resume, cancel⟩` and its types `K_q` | as built (`kTy`, `Core/EffRules.lean:976`; the value `kappa`, `Paper/S3_Dynamics/Definitions.lean:438`) |
| K-CAP | a capability: a comodel lent by a borrow, an operation a call on it | derived (`experiments/HandlersAsBorrows`); kernel status OQ-1 |
| K-SWAP | `withswap`, the comodel carrier; whether its callee may perform (OQ-20) | as built pure (`Core/Fundamental.lean:254`) |
| K-BOR | one borrow constant per printed constant, at any callback row `Σ` with `TableOK_x ⟦Σ⟧`; today's pure constants at `Σ = ∅`, `*U` twins at abortive rows, as abbreviations | changed (R-T1 and R-CLOSEDOP by default) |
| K-FIX | `bounded_fix[A, C]` at every computation type, rows included; recursive groups as fixed points of generators | as built (`Core/Fundamental.lean:196`, `Core/BoundedFix.lean:91`) |
| K-NU | `ν` codata with effectful observations (`Loop_Σ`), the effectful affine closure | as built (SPEC §19 *Divergence*, §22) |
| K-DIV | divergence: its kernel reading (OQ-15) | as built as codata (SPEC Entry 13, §14) |
| K-HOST | host-provided outermost handlers: I/O capabilities, allocation; externs outside the proofs | partly built (SPEC §11); OQ-30 |
| K-GRADE | the qualifier as a grade on the captured context (`[let]`'s side condition, `κ`'s copy and drop) | as built implicitly; explicit in `experiments/Grades` |
| K-GEN | a stored continuation: `[gen]` as a rule at `[@c] U(Aff^c_Σ A B)`, or an outlives rule at `U C` and `K_q` (03 §4, both options of OQ-28) | new (branch `lift-stage1`, option (a) at `Σ = ∅`); OQ-28 |
| K-SCOPE | a scoped operation: a computation argument delimited by the operation (03 §9.1) | new, not adopted (R-FO; OQ-12, OQ-59) |
| K-HDIV | a handler around a div computation, per observation and spanning observations, under both readings of OQ-15 (03 §9.2) | in the calculus (U5); lift deferred by R-HDIV until OQ-67 |
| K-CARRIER | `[handle]` at every computation type, with `K_q(B, C)` and `C_1` (03 §9.3) | new, not adopted (R-RETCARRIER; OQ-37) |
| K-BORANS | an operation answering a borrow of the handler's state at its extent (03 §9.4) | new, not adopted (R-NOBORANS; OQ-29) |
| K-ALLOC | allocation as the operations of `Alloc[T]` with a host outermost handler, or as a heap capability (03 §9.5) | in the calculus (U20); presentation OQ-30; lift deferred by R-ALLOCORACLE until OQ-68 |
| K-ROWABS | row abstraction `∀r # N. C` (03 §9.6) | new, not adopted (R-NOROWVAR; OQ-13) |
| K-SHALLOW | shallow handlers `hnd†` (03 §9.7) | new, not adopted (R-DEEP; OQ-26) |
| K-FINR | finalisers and unwinding forms at a resuming row (03 §9.8) | new, not adopted (R-FINAB; OQ-7) |
| K-OWNERR | an abortive payload that owns (03 §9.9) | new, not adopted (R-NOOWNERR; OQ-24) |
| K-RELQ | the relevant qualifier and `K_rel` (03 §9.10) | new, not adopted (R-NOREL; OQ-17) |
| K-SWAPΣ | a co-operation whose callee performs: `withswap[Σ]`, or the placeholder shape as a derived term (03 §9.11) | new, not adopted (R-PURESWAP; OQ-20) |
| K-SELFROW | operation types that perform their own effect, `μe. E` (03 §9.12) | new, not adopted (R-NOSELFROW; OQ-61) |
| K-FOLDΣ | folds and counted loops at a row (03 §9.13) | new, not adopted (R-PUREFOLD; OQ-62) |
| K-GENNAME | generative instances, K-NAME's `[new]` step collected (03 §9.14) | new, not adopted (R-STATIC; OQ-14) |
| K-NEGREC | the construct R-NONEGREC excludes, stated (03 §9.15) | not adopted (OQ-31) |

### 3.3 Machine (owner 04)

| id | construct | status |
|---|---|---|
| K-CTX | evaluation contexts; `K` free of `n` (`HasHnd`), catching nothing of `n` (`Catches`), unwind-clear, `hndNames`; `Kont.shift` | as built (`Paper/S3_Dynamics/Definitions.lean:386-420`; composition lemmas `Core/EffDefs.lean:77-98`) |
| K-STEP | the head steps `[ret]` `[op]` `[unwind]` `[then]` `[finalise]` `[finalise-cancel]` `[cfin-ret]` `[cfin-raise]` `[cancel]` `[cancel-raise]` `[boundedFix]` | as built (`Paper/S3_Dynamics/Definitions.lean:495-545`) |
| K-CANCEL | cancellation: `⊥`, `ccatch`, `cfin`, the cancel state, uninterceptable cancel | as built (SPEC §19 *Cancels*; `Core/EffCancel.lean`) |
| K-RUN | allocator runs (`ARun`, every allocator), unique decomposition, determinism | as built (`head_det_eff`, `Core/Steps.lean:596`) |

### 3.4 Model definitions (owner 05)

| id | definition | status |
|---|---|---|
| D-W | the world `W = (ρ, ls, σ)` | changed (`σ` made a component) |
| D-ORD | `W ⊑ W'` and its facts (reflexive, transitive) | changed (OQ-8, OQ-9) |
| D-ARISE | `TW` at `W`; `TabAtS` stated as a `TW` invariant at every stack, by the lemma T-ARISE.0 | intended change from a guard to an invariant, in force only once T-ARISE.0 is proved (OQ-45); until then a guard, as today |
| D-WPG | `wpG_W` | changed only at stops (D-STOP) |
| D-STOP | the stop condition relativised to the table: at a value, the run has closed every frame it held and opened; at a stop, the 6.64 frames still open are handed to the table as `τ'` | changed; **kernel definition change, SPEC entry required**; OQ-9, OQ-10, OQ-57 |
| D-TABLE | `Table`, `Mono`, `Abortive`, `bot`; a table receives the pre-stop world and `τ'` | changed (signature) |
| D-OPTAB | `opTable T` | as built; reads `W` |
| D-CANCELTAB | `cancelTab T N`, `errOk` | as built |
| D-TABLEOK | `TableOK_x Tb`: monotone, stable along `⊑`, stops irreducible (`Irred`), and its continuation obligation frames under 6.64/6.65/6.66/6.150; `TableOK ≜ ∀ x. TableOK_x` | new |
| D-EWP | `ewp_W(τ)` | changed: one least fixed point indexed by `τ`; `ewp_W([])` is today's `ewpTS` |
| D-EWPP | `wpGP_W`, `ewpP_W`: the partial-correctness relation at a row holding `div` | new, only under OQ-15 (b); a second wp family, recorded as a defect (OQ-63) |
| D-SHARE | `share` (today `contShare`): the stopped context's obligation | as built; quantifier OQ-8 |
| D-KAP | `KapRel`: a reified `κ`'s obligation | as built; quantifier OQ-8 |
| D-OWED | `owed` (today `cancelOwed`): the cancel run's obligation | as built; frames OQ-9 |
| D-REL | `𝒱⟦A⟧_W`, `𝒞⟦C⟧_W`, `𝒢⟦Γ⟧_W`: one clause per former, at `W`; equal to `vC`/`cC` at `σ = []` by T-NIL (OQ-58); three candidate clause sets, OQ-8 (a) and (b) and OQ-9 (b) | changed (re-indexed); OQ-8, OQ-9 |
| D-SEM | `Δ; Γ ⊨ e : C` at every `W` | changed |
| D-MODEL | `IsModel_Σ Φ`: `Φ` closed under `opTable ⟦Σ⟧` stops at every future world | new |
| D-COMODEL | `IsComodel_Σ c`: a capability's co-operations meet the `opTable ⟦Σ⟧` protocol over `𝒱⟦S⟧` | new (OQ-1, OQ-19) |
| D-DTOR | the destructor of a context and the `Cancel` predicate it discharges | changed (stated once, from SPEC §12 and `[then]`) |
| D-BIN | the binary relation `≈` over pairs of worlds | new, conditional on OQ-4 |

### 3.5 SPEC entries (owner 08)

Each changed or new kernel definition lands under one of these entries, written before the kernel
work it governs (§0.1). Every entry's text is drafted: D-STOP in 05 §4, the others in 08 §4.4, each
at its gating question's default with the delta per option. Numbers are assigned when an entry
lands.

| id | content | ids it governs |
|---|---|---|
| E-SIG | one signature object; rows as sums; `opTable ⟦Σ⟧` the one interpretation; optional equations | K-SIG, K-ROW, K-INT, K-THEORY |
| E-W | the world `W`, its order, `TabAt` as a `TW` invariant once T-ARISE.0 holds (OQ-45; a guard until then), the relativised stop (D-STOP's text, 05 §4), the re-indexed relation, with `vC`/`cC` equal to its `σ = []` instance by T-NIL, per introduction row (OQ-58); gated by OQ-8, OQ-9, OQ-10, OQ-44, OQ-45, OQ-57, OQ-58 | D-W, D-ORD, D-ARISE, D-STOP, D-WPG, D-REL, D-SEM, T-MONO, T-NIL, T-STOP, T-ARISE |
| E-BOR | one borrow constant per printed constant at every `TableOK` row; 6.64-6.66 and 6.150 lifted once | K-BOR, D-TABLEOK, T-FRAME, T-SUMOK, L-BOR |
| E-MODEL | `IsModel`; every computation type a model; `ewp_handle` as initiality; the handler laws' unary halves | D-MODEL, T-MODEL, L-ALG, L-ALG0, L-HRET, L-HOP, L-HFWD |
| E-COMODEL | capabilities as comodels of the same `Sig`; `IsComodel`; the capability rule | K-COMODEL, K-CAP, K-SWAP, D-COMODEL, T-COMODEL, L-STATE |
| E-REN | renaming of names; copies meaning-preserving; no accidental handling | K-REN, T-REN, L-REN, T-NAH |
| E-GEN | K-GEN: `[gen]`, a stored continuation at `[@c] U(Aff^c A B)`, or the outlives rule at `U C` (OQ-28) | K-GEN, K-HND, K-NU; OQ-28 |
| E-BIN | the binary relation | D-BIN, T-BINFP, T-SOUND, the binary halves of 06 |
| E-HOST | host carriers: I/O capabilities as comodels; allocation | K-HOST |
| E-LOWER | the lowering classes with their laws | T-LOWER, L-TAIL |

---

## 4. Laws (owner 06)

Each law is stated over `W` (or shown to live at `σ = []` and survive the re-index, OQ-11). Each
has a **unary half** (a `wp`/`ewp` or run fact over the kernel relation) and, where it is an
equation, a **binary half** (over `≈` or `≡`; OQ-4). A reduction-shaped law may be stated as
`↦*`-joinability. "Today" cites where any form of it exists.

| id | law | form | today |
|---|---|---|---|
| L-TO | the monad laws of `to` | left unit `return V to x. N ≡ N[V/x]`; right unit `M to x. return x ≡ M`; associativity `(M to x. N) to y. P ≡ M to x. (N to y. P)`, `x ∉ fv(P)` | `bind`'s `beta` step; not stated |
| L-UF | thunk and force | β `force (thunk M) ≡ M`; η `thunk (force V) ≡ V` at `U C` | `forceE`'s steps; not stated |
| L-LAM | functions | β `(λx. M) V ≡ M[V/x]`; η `λx. M x ≡ M` at `A ⊸ C`, `x ∉ fv(M)` | `beta` step |
| L-AMP | computation records | β `πᵢ ⟨M₁, M₂⟩ ≡ Mᵢ`; η `⟨π₁ M, π₂ M⟩ ≡ M` at `C & D` | `case` steps of the encoding |
| L-PAIR | tensors | β `let (x, y) = (V, W) in M ≡ M[V/x, W/y]`; η `let (x, y) = V in M[(x, y)/z] ≡ M[V/z]` | `letpair` step |
| L-CASE | sums | β `case inⱼ V {…} ≡ Mⱼ[V/x]`; η `case V {inⱼ x. M[inⱼ x/z]} ≡ M[V/z]` | `case` steps |
| L-BANG | `!` | β of `bangE` on a promoted value; η at `!A` | `bangE`'s rule |
| L-ALL | lifetime abstraction | β `(Λ'x. M) [] ≡ M` at an instance; η `Λ'x. M [] ≡ M` | `allE`'s reading |
| L-NUB | codata | β `out (in M) ≡ M`; η `in (out M) ≡ M` at `νX. C`; the coiteration laws are L-DIV's | `nuIn`/`nuOut`, the same term |
| L-CC | commuting conversions | `K[case V {inⱼ x. Mⱼ}] ≡ case V {inⱼ x. K[Mⱼ]}`, and the same for `let (x, y)`, for a plain `K` | not stated |
| L-ALG | graded algebraicity | `K[op(v; y.M)] ≡ op(v; y.K[M])`, with `Γ_K` scaled by `q` (additive at `aff`, contracted at `unr`); unary form: an op stopped under `K` at `q` owes `K`'s share scaled by `q`, plus `D_K` when weakening applies | `[op]` step; four encodings (`[let]`, `[then]`, `kTy`, `contShare`); EffModelRel `alg_*` |
| L-ALG0 | algebraicity at arity 0, destructor form | `K[raise e] ≡ D_K⟨raise e⟩` (O-FIN; `D_K⟨·⟩` at a raise only) | `[finalise]`, `then_compatC` (`Core/EffRules.lean:928`) |
| L-GEN | generic effect ↔ algebraic operation | `op(v; y.M) ≡ gen_op(v) to y. M` | a definition plus L-ALG at an empty frame; adds no obligation of its own |
| L-HRET | handler return | `hnd_n H (return v) ≡ h_ret v` | `[ret]` step; EffModelRel `h_ret` (`Laws.lean:148`) |
| L-HOP | handler operation, deep | `hnd_n H (op_n(v; y.M)) ≡ h_op(v, ⟨λy. hnd_n H M, cancel⟩)` | `[op]` step; EffModelRel `h_op` (`:164`) |
| L-HFWD | forwarding | `hnd_n H (op_m(v; y.M)) ≡ op_m(v; y. hnd_n H M)`, `m ≠ n`, at every arity | stop configurations in `handle_compatC` (`Core/EffRules.lean:1092`); EffModelRel `h_fwd` (`:202`) |
| L-HUNIQ | uniqueness / initiality of handling | a map satisfying L-HRET, L-HOP (resuming, and abortive with `D_K ▷`), L-HFWD (resuming and abortive), and transparent to the steps of the BoLo store (an added hypothesis) for `H` is `hnd_n H` | `handle_unique` (`experiments/CoeffectsStrict/CoeffectsStrict/Handler.lean:59`), one effect |
| L-HBIND | handling a sequence | `hnd_n H (M to x. N) ≡ hnd_n (λx. hnd_n H N, hs) M` | not stated; a corollary of L-HUNIQ |
| L-HFUSE | fusion | `hnd_{n₂} H₂ (hnd_{n₁} H₁ M) ≡ hnd_{n₁} (H₂ ∘ H₁) M` for `M` whose row excludes `n₂`, when `H₂ ∘ H₁` is a well-typed model (OQ-49) | not stated |
| L-HCORR | handler correctness | a handler of `E` is correct iff its clauses satisfy `Eq(E)` | vacuous (free theories) |
| L-EXC | exceptions | the theory of `raise` and its handlers (`to_result`, `default`, `map_err`) | `[unwind]`, `[finalise]` |
| L-STATE | state and linearly used state | get/put equations on a comodel; a capability's operations are state-access operations | `op_tail`, `op_answer`, `handle_fold` (`Core/Handlers.lean:76, 133, 211`): run facts only |
| L-YIELD | generators | `for` as a handler of `yield`: the H-laws instantiated; `take(n)` as cancel | not stated |
| L-ASYNC | asynchrony | `Async = μe. {suspend, spawn}` (`spawn`'s parameter names its own row: OQ-61, R-NOSELFROW by default); a scheduler over `Loop_Σ` codata (OQ-60); the H-laws, L-W and L-SIGNAL at it; finalising a parked queue needs R-FINAB lifted (OQ-7) | not stated |
| L-SCOPE | scoped operations, only under OQ-12 (b) | algebraic in the continuation, not in the scope | not stated |
| L-ND | nondeterminism, only if multi-shot is free (OQ-16) | choice laws at `unr` | not stated |
| L-DISCARD | discarding a computation | `M to _. N ≡ N` when `M`'s row has no `div` and no abortive operation, every operation of it is discardable, and its result drops (OQ-64) | not stated |
| L-COPY | duplicating a computation | `M to x. M to y. N ≡ M to x. N[x/y]` at an idempotent row and a persistent result (OQ-64) | not stated |
| L-COMMUTE | swapping computations | `M₁ to x. M₂ to y. N ≡ M₂ to y. M₁ to x. N` when the rows of `M₁`, `M₂` commute (tensor), `x ∉ fv(M₂)`, `y ∉ fv(M₁)` (OQ-64) | not stated |
| L-FOLD | folds and counted loops at a row | fold β, count β, fold uniqueness, at a row (under OQ-62 (b)) | `fold_beta`, `fold_unique` (`experiments/CoeffectsStrict/CoeffectsStrict/Fold.lean:76, 207`), pure |
| L-SUM | rows are sums | operations of distinct names interleave freely; forwarding preserves order; absorption (`log; raise ≡ raise`) holds exactly under the handlings that validate it | `logOutside`/`failOutside` (`Core/EffPrograms.lean`); EffModelRel `absorb_*` |
| L-TENSOR | disjoint capabilities commute | operations on capabilities from disjoint borrows commute; unary form: the disjoint-capability frame fact | EffModelRel `tensor` (`Tensor.lean:91`) |
| L-RUN | running a computation against a comodel | run-return, run-op, run-forward, run-bind (the unit and multiplication laws of a stateful runner, KRU §4), uniqueness of running (the free-model universal property, A-B §2.1-2.2, at `Σ' = ∅`) | `op_tail`, `handle_fold` as run facts |
| L-SIGNAL | cancel is uninterceptable and runs the destructor | no user handler intercepts a cancel; a clause that cancels discards what the body would still perform (L-HOP with L-W, a free-theory law). Whether this is Ahman-Bauer's signal is OQ-66 | `⊥` name, `cfin` (K-CANCEL) |
| L-W | weakening of a continuation is its destructor | `cancel κ ≡ ccatch (hnd_n H (K°[⊥_N]))`, which is `D_K ▷ return ()` when every finaliser answers `()` | `[cancel]` step; `ewp_ccatch`, `cancel_frame` (`Core/EffRules.lean:168`) |
| L-C | no duplication of a linear or affine `κ` | typing invariant: `κ` used by exactly one entry, at most once | `kTy`; `[let]` |
| L-P | multi-shot persistence | `κ` copied only if its captures are persistent | `lam_bang_persistent` (`experiments/HandlersControl/HandlersControl/Capture.lean:42`) |
| L-BETA | freeze then resume | resuming a captured `κ` is the identity up to fresh internal lifetimes | TR §13.2 (binary); kernel lift open (TR O5) |
| L-ETA | the forwarding handler, cancel included | a handler whose clauses forward (and forward cancel) is the identity | TR §13.3; OQ-27 |
| L-HIDE | hiding | the body's relation is parametric in the handler's or lender's witness (the anti-frame) | `wpTS_M_antiFrameX`, `ewpTS_M_antiFrameU` (`Core/EffWp.lean:854`) |
| L-INTER | answering/control commutation | an answering operation commutes with a control operation across a freeze (a tensor-style law, not Katsumata-Rivas-Uustalu's interaction law; L-RUN's run-return and run-bind are KRU's stateful-runner laws, §4, not the interaction-law axioms, which also constrain the comonad's counit and comultiplication) | TR §13.5: special case; open at affine (P13.14 by hand) |
| L-NAH | no accidental handling | a function parametric in a name it does not handle forwards that name's operations | EffModelRel (instances); kernel: none |
| L-REN | renaming | renaming names is meaning-preserving on derivations and relations | not built |
| L-NU | instance laws (idem-ν, ν/ν, new-ν, ν/op), only if generative instances are adopted (OQ-14) | Staton's laws at lin/aff | EffModelRel; ν/op refuted at `unr` (`nu_op_fails_multishot`, `Examples.lean:223`), open otherwise (`O1`, `Ownership.lean:93`) |
| L-BOR | a borrow across an effect | an abortive stop ends every lend it passes, LIFO, and the lender's finaliser runs; at a resuming stop, the open lend is handed on (under D-STOP) | `*U` frames (`ewpTS_*_frameU`, `Core/EffWp.lean:828, 842`) |
| L-FIX | the fixed point of a generator | `bounded_fix` unfolds one level; a layer composes before the fixed point | `[boundedFix]` step; SPEC §21 |
| L-DIV | divergence | the law of the chosen reading (OQ-15): codata coiteration laws, or `K[⊥] ≡ ⊥` without `D_K` | codata laws in `experiments/CoeffectsStrict` (`unfold_next`, `unfold_close`) |
| L-TAIL | a tail-resumptive clause is a direct call | the law that justifies the erased lowering of resume-once-in-tail-position | `op_tail` (run fact); SPEC §19 *Lowering* |

---

## 5. Metatheorems

### 5.1 Model lemmas (owner 05)

| id | statement | today |
|---|---|---|
| T-MONO | one monotonicity lemma: `𝒱`, `𝒞`, `𝒢` are monotone along `⊑`, by one induction on types | `Ext.refl`/`Ext.trans` only |
| T-NIL | at `σ = []` the relation equals `vC`/`cC`: by `rfl` at the **=** clauses, by a per-row proof at `U`, `share`, `KapRel` (unknown, OQ-58, `def NilAgreesU : Prop`); then every lemma of Core holds unchanged | the `*_nil` lemmas of GhostEnd are `propext` equalities; `vRLk` has none |
| T-STOP | conservativity of D-STOP: at a value `wpG_W ∘ valPost = wpTS`; at the empty table `ewp = wpTS` | `ewp_bot` (`Core/EffWp.lean:772`) for today's stop |
| T-ARISE | T-ARISE.0: every `TW` world, with `σ` consistent with its `ps`, has `TabAt_W` at every part a term holds (by induction on `TW`'s constructors, 6.50 at each); and `TabAt` preserved by every run, at returns and at stops | `wpG_tabAt` (`experiments/GhostEnd/GhostEnd/Table.lean:87`), `wpG_tabAtS_one` (branch `gfp-arising`, `Arising.lean:112`) at one entry |
| T-FRAME | `[TR]` 6.64, 6.65, 6.66 and 6.150 lifted once to `ewp_W` at every `TableOK_x` table, with the printed premises and boxed postconditions verbatim (05 T-FRAME), by induction on the least fixed point, depth handled by one induction | abortive half (`Core/EffWp.lean:828-854`); resuming halves in GhostEnd (`ewpTS_M_frameR` `Relend.lean:117`, `ewpTS_I_frameR` `ImmLend.lean:175`, `ewpTS_M_antiFrameR` `Frames.lean:89`, `stack_step_*` `StackStep.lean:392, 563, 1003`); 6.150 not lifted |
| T-SUMOK | `TableOK` is closed under row sum (`OpTab.ext`) | not built |
| T-MODEL | every computation type is a `Σ`-model (M1); `ewp_handle` is initiality of the least fixed point among models (M2); graded algebraicity (M3) from them | `ewp_handle` (`Core/EffRules.lean:615`), a case analysis |
| T-COMODEL | a capability meets the `opTable ⟦Σ⟧` protocol: one protocol for model and comodel (TR D4.6) as a kernel lemma; running a computation against a comodel is the tensor of a model and a comodel (Plotkin & Power, MFPS 2008 [via 12-sources]) | not built |
| T-DEF | the relation is defined by structural recursion on types and well-founded stratum and fixed-point recursion: no step index, no recursive domain, under the cut-offs of OQ-31 (R-NONEGREC) | `vRLs` structural (#279); TR §16.5 |

### 5.2 The metatheory (owner 07)

| id | statement | today |
|---|---|---|
| T-COMPAT | one compatibility lemma per typing rule, at `W` | per rule in Core at `σ = []` |
| T-FP | the fundamental property at `W`, by induction on the derivation; `fundamentalC` is its `σ = []` instance once T-NIL holds (OQ-58) | `fundamentalC` (`Core/Fundamental.lean:434`); GFP stated, not proved |
| T-ADEQ | adequacy, every run under every allocator: a closed `F 1` program is safe and reaches a value at empty memory | `adequacyC` (`:590`), `adequacyD` (`Core/Demonic.lean:312`) |
| T-SAFE | effect safety: no closed program at `F 1` stops at an unhandled operation | `ewp_bot` with T-ADEQ |
| T-LEAK | leak freedom: every run ends with no owned resource | `NoOwn` leftover in `wpTS` |
| T-FIN | finalisation exactly once, LIFO, on return, unwind and cancel | not a named corollary |
| T-LIN | a linear or affine `κ` is consumed exactly once | `kTy` with T-FP; no named corollary |
| T-DET | unique decomposition and determinism with capture | `head_det_eff` (`Core/Steps.lean:596`) |
| T-REN | the renaming lemma over `CDerives` and the relation at `W` | not built |
| T-NAH | no accidental handling over the kernel | not built |
| T-ABS | abstraction safety (parametricity in names) | not built; binary |
| T-TOTAL | a closed div-free program terminates (kept; not a goal) | `total_every_alloc` (`Core/Totality.lean:40`) |
| T-2RUN | binary facts from the unary relation and determinism up to renaming | `freshRun_det` (`experiments/TwoRun/TwoRun/Fresh.lean:255`), `run_sim` (`…/Sim.lean:253`) |
| T-BINFP | the binary fundamental property over `≈` (OQ-4) | not built on Core |
| T-SOUND | `≈` is sound for `≡` | not built on Core |
| T-T1 | at `σ = []` no internal lend spans a stop: a theorem from T-STOP once D-STOP is adopted | true by definition today (`Core/EffDefs.lean:40`) |
| T-T2 | at general `σ`, the lends a stop hands to its table close on every continuation path: resumed, cancelled, dropped at an abortive operation, resumed between lenders | GhostEnd's resuming halves at one stack shape each |
| T-PRES | every run preserves the typed world: `TW` and `Tagged` at the end of every run segment, `TI` from `TW`, and at a stop exactly the frames handed to the table | `TW.inv` (`Core/Invariant.lean:2702`); the world conjunct of `wpG` |

### 5.3 Correspondence results (owner 08)

| id | statement | today |
|---|---|---|
| T-CONS | conservativity: every derivation of today's `CDerives` is one of the extended judgement; the relation at `σ = []` is `cC`; every theorem of Core keeps its statement; BoLo's `DerivesWf` embeds with its adequacy (T-CONS.4) | the *Baseline* paragraphs of SPEC §§14, 18-23; `embed` (`Core/Embedding.lean:235`) |
| T-ELAB | each surface handler schema meets L-HRET / L-HOP / L-HFWD against `[handle]` or is a comodel meeting T-COMODEL | not built (audit M15) |
| T-LOWER | the lowering classes: resume once in tail position = a direct call (L-TAIL), never resume = a branch (L-ALG0), resume later = a state machine, multi-shot = copy; cost parity with the hand-written program; status OQ-23 | corpus counts (`corpus/kernel-counts.expected`), `Backend/Clos/Capture.lean`, `Backend/Clos/Unwind.lean` |

### 5.4 Equational metatheorems (owner 06)

| id | statement | today |
|---|---|---|
| T-SI1 | step interchange: an allocation-free head step `M ↦ N` gives `M ≅_W N` at every `W` | forward half: `ewp_step`, `wpG_head` (`Core/EffWp.lean:936, 973`); backward half not built |
| T-SI2 | reduction in context is equivalence: a reduction-shaped law (06 §1.3) holds as `≡`, by a stuttering simulation under a fixed allocator (OQ-47) | the technique of `run_sim` (`experiments/TwoRun/TwoRun/Sim.lean:253`) |

---

## 6. How the ids hang together

- **The spine.** K-SIG → K-ROW → K-INT → D-OPTAB → D-EWP → D-REL → T-FP → T-ADEQ / T-SAFE /
  T-LEAK / T-FIN / T-LIN. Every construct enters the relation only through `opTable ⟦Σ⟧` and
  `W`.
- **Models and comodels.** K-MODEL → D-MODEL → T-MODEL → (L-HRET, L-HOP, L-HFWD, L-ALG, L-ALG0,
  K-HND's compatibility). K-COMODEL → D-COMODEL → T-COMODEL → (K-CAP, K-SWAP, L-STATE,
  L-TENSOR, L-INTER). One `Sig`, two implementations.
- **Borrows.** O-BOR → D-TABLEOK → T-FRAME → T-SUMOK → K-BOR (one constant per printed
  constant at every `TableOK` row) → L-BOR.
- **The world.** D-W → D-ORD → T-MONO; D-ARISE → T-ARISE; D-STOP → T-STOP; all three under
  OQ-8, OQ-9, OQ-10, OQ-57. T-NIL makes Core the `σ = []` instance once OQ-58 is settled.
- **Laws over the kernel.** Every L id has its unary half proved over D-EWP at `W`; its
  binary half follows by T-SI2 when the law is reduction-shaped, and otherwise waits on OQ-4.
- **The register.** Every open question is in 99, with what it blocks; every default that
  narrows the calculus is an R id (§7.2).

---

## 7. Open questions and named restrictions

### 7.1 The register

The register is [99-open-questions.md](99-open-questions.md): every question boxed in the form

```
> [!IMPORTANT]
> **Open question OQ-<n>: <title>** (<cross-reference>) **[tag]** …
> *Why open:* … *Options:* (a) … (b) … *What settles it:* … *Blocks:* … *Default if unresolved:* …
```

with its tags (**[user decision]**, **[settle by proof]**, **[settle by literature]**), and a
table of every question against what it blocks, what settles it, and whether it needs the user.
Sections cite questions by id and never restate them; a new question is added to 99 first. The
audit's Q1-Q7 are OQ-1 to OQ-7. Of the critic's corrections, 1 asks OQ-3 (with OQ-1), 2 is OQ-2
and OQ-33, 3 is OQ-8, 4 is OQ-9 (with OQ-10), 5 is OQ-11, and 6 bears on OQ-18, OQ-43 and OQ-54.

| OQ | question |
|---|---|
| 1-7 | the audit's Q1-Q7: answering and control handlers; tier 1 or tier 2; handler extent; a binary relation; EffModelRel; role declarations; finalisers at a non-abortive table |
| 8-11 | the critic's: quantifier placement; open frames across a stop (the first unknown); the form of the stop; laws over `W` |
| 12-34 | scope and design: scoped operations, effect polymorphism, names, divergence, multi-shot, the relevant qualifier, sum and tensor, comodels, effectful co-operations, finaliser policy, equations, lowering correctness, owned payloads, handler state, shallow handlers, η with cancel, stored continuations, borrowed answers, allocation and I/O, the step-free cut-offs, the TR's moded calculus, the hard-stop rule, the BoLo world as a comodel |
| 35-40 | signatures and statics: closed operation types, row identity inside types, handler carriers, site freshness, qualifier subsumption, the borrow callback's row class |
| 41-43 | the machine: captures inside a cancel run, lowering gaps, determinism up to renaming |
| 44-46 | the model: the content of `σ`, the arising guard, the world of a stored payload |
| 47-49 | the laws: step inclusion, the interaction law at `aff`, the composite handler |
| 50-52 | the metatheory: linear use observed, adequacy at a row, subject reduction |
| 53-55 | correspondence: the elaborator, `σ` under a fork, the declaration kind |
| 56-60 | further findings: lifetime-open operation types at a borrow callback; `τ` beside `W`; Core as the `σ = []` instance at `U`; handling inside a scope; the async scheduler against the negative-recursion cut-off |
| 61-68 | further findings: operation types that perform their own effect; folds and counted loops at a row; a partial-correctness `wp` beside `ewp_W`; the effect-dependent laws; an operation form with a cancel continuation; cancel against Ahman-Bauer's signal; the proof obligations of K-HDIV and K-ALLOC |

### 7.2 Named restrictions

Each restriction is the default of an open question. A section states a construct in full and
marks where a restriction applies; it never writes the restricted form as the construct.

| id | restriction | default of | applies to |
|---|---|---|---|
| R-T1 | no internal lend spans a stop; only abortive operations cross a borrow's scope | OQ-2, OQ-9 | K-BOR, K-OP, D-STOP |
| R-MID | no handler between two lenders | OQ-3 | K-HND, T-FRAME |
| R-FINAB | finalisers and unwinding forms at abortive rows only | OQ-7 | K-THEN, K-FINR, K-BOR, K-SWAP, K-NU, L-ASYNC (a parked queue cannot be finalised by a finaliser that performs) |
| R-FO | no operation takes a computation | OQ-12 | K-SIG |
| R-NOROWVAR | rows are a meta-index: each copy at each row a separately checked derivation, related by no theorem except a renaming (T-REN); no first-class row-generic value; no polymorphic recursion across rows | OQ-13 | O-JDG, K-ROW, K-ROWABS, the reconciler chain's combinators (U5) |
| R-STATIC | static names; no recursion through a site | OQ-14 | K-NAME |
| R-HDIV | the kernel lift does not implement K-HDIV's spanning form until its obligation is proved; a restriction of the decided position U5 | OQ-67 | K-HDIV, K-DIV, K-NU, the reconciler chain (U5) |
| R-PURESWAP | a co-operation's callee is pure; with it, a capability cannot fail | OQ-20 | K-SWAP, K-SWAPΣ, K-CAP, the reconciler chain's `Kube` (U5) |
| R-NOOWNERR | an abortive payload owns nothing | OQ-24 | K-RAISE |
| R-NOBORANS | no operation answers a borrow into handler state | OQ-29 | K-SIG, K-CAP |
| R-RETCARRIER | a handler's carrier is `F_Σ R`; other carriers by encoding | OQ-37 | K-MODEL, K-HND, K-KONT |
| R-CLOSEDOP | operation types at a borrow callback are closed in lifetimes and free of the lend's variable | OQ-56 | K-BOR, D-TABLEOK (3)-(4), OQ-40 |
| R-ALLOCORACLE | the kernel lift keeps allocation as the machine's oracle until K-ALLOC's obligations are proved; a restriction of the decided position that alloc is an effect (U20) | OQ-68 | K-HOST, K-ALLOC |
| R-NONEGREC | no negative recursion through a stored continuation (no handler that stores or returns its own continuations); bounded recursion; positive `μ`/`ν` | OQ-31 | T-DEF, K-FIX, K-NU, K-HND, K-NEGREC, L-ASYNC |
| R-NOSELFROW | no operation type mentions its own signature's row | OQ-61 | K-SIG, K-SELFROW, L-ASYNC (`spawn`), threads |
| R-PUREFOLD | fold algebras and counted-loop steps are pure | OQ-62 | K-FOLDΣ, iteration over finite data with effects |
| R-DEEP | handlers are deep; step-wise handling only through `ν` codata | OQ-26 | K-HND, K-NU, L-YIELD |
| R-NOREL | no relevant continuation qualifier | OQ-17 | O-QUAL, K-KONT |
| R-EXACTQ | `[sub]` compares qualifiers exactly | OQ-39 | K-ROW, `[sub]` |

**Restrictions of the equational theory and the metatheory.** These narrow what is stated, not
which programs exist, and are named so that no narrowing is silent.

| id | restriction | default of | applies to |
|---|---|---|---|
| R-ETALIN | L-ETA is stated at linear operations only | OQ-27 | L-ETA |
| R-INTERLIN | L-INTER is stated at linear control operations only | OQ-48 | L-INTER |
| R-ALGPLAIN | L-ALG's binary form is stated at plain frames, handler frames of other names and borrow frames, not at finaliser frames | OQ-65 | L-ALG |
| R-FUSETAIL | L-HFUSE is stated at tail-resumptive clauses and `n₂`-free bodies only | OQ-49 | L-HFUSE |
| R-LINRES | T-LIN and T-FIN (1) are stated in their resource form | OQ-50 | T-LIN, T-FIN |
| R-ADEQF1 | adequacy is stated at `F 1` only | OQ-51 | T-ADEQ, T-LEAK |

Two questions have defaults that limit a route of proof, not the calculus or its statements, and
carry no R id: OQ-43 (two-run facts at runs with no array step) and OQ-47 (binary forms marked not
proved). OQ-42's default (three constructs not lowered) restricts the lowering, not the calculus,
and is recorded there as a restriction of the decided positions U6 and "compiler never stale".

---

## 8. The section contract

Every section: uses §1's objects verbatim; writes an entry (§2 template) for every id it owns;
cites `file:line` for every claim about code; cites open questions by id; marks each
obligation unknown or mechanical; lists at its end the printed lemmas in its run-up that are not
transcribed, the printed hypotheses it does not spend, and the uniqueness or functionality
results it does not use (CLAUDE.md §5).

### 01-scope.md: what the calculus is

- **Must contain.** The calculus in one page: BoLo's resource world plus effects as models and
  comodels of one signature, over one Kripke world. The standing requirements of §0.2 item 9,
  each with its strength. In scope by design: effectful closures, generators, recursions,
  stored continuations, continuations holding borrows, several effects at once (the reconciler
  chain `timeout |> retry |> log |> kube`, written as a program with K-HDIV and with R-HDIV, R-NOROWVAR
  and R-PURESWAP named where they restrict it), cancellation,
  asynchrony. Explicitly outside the proofs:
  externs, `unsafe`. The relation to SPEC entries 13 (§14), 17-22 (§18-§23): which the calculus
  replaces, extends or keeps. The tier question (OQ-2) and every named restriction (§7.2), each
  stated as a restriction of the full calculus. A checklist, "not an approximation", against
  which 08 validates: one signature object; one interpretation; models and comodels of it;
  laws over the kernel relation; one world; one borrow per printed constant; no construct
  recognised by name; and the further items 01 §7 lists.
- **Owns.** The checklist items C-1 to C-12. No K/D/L/T ids.
- **Carries.** OQ-2, OQ-12, OQ-15, OQ-16, OQ-18, OQ-30, OQ-31, OQ-33, OQ-34, OQ-56, OQ-58,
  OQ-60, OQ-61, OQ-62, OQ-67, OQ-68, and the R table.

### 02-signatures.md: signatures, rows, names, models and comodels as syntax

- **Must contain.** O-SIG, O-QUAL, O-NAME, O-ROW, O-INT in full; the quotient of today's
  first-match list by `Row.Uniq`; row sum and its algebra (associative, commutative, unit `∅`);
  `[sub]` as inclusion; the interpretation `⟦Σ⟧δ` and `opTable` as the one interpretation of a
  row (`effTab_effOf`); renaming of names as an operation on rows, terms and derivations; the
  syntactic form of a model (clauses typed from `Σ`: `retTy`, `clausesTy`, `kTy`) and of a
  comodel (co-operations typed from `Σ`); the PP08 constraint that a theory with an abortive
  operation has only the empty comodel [via 12-sources], hence which effects can be answering;
  one shared row function for the elaborator's two row computations (audit §2.2), as a
  requirement on 08.
- **Owns.** K-SIG, K-ROW, K-NAME, K-INT, K-THEORY, K-REN, K-MODEL, K-COMODEL.
- **Carries.** OQ-1, OQ-12, OQ-13, OQ-14, OQ-17, OQ-19, OQ-22, OQ-29, OQ-35, OQ-36, OQ-37,
  OQ-38, OQ-39, OQ-61, OQ-66.

### 03-statics.md: types and typing rules

- **Must contain.** Every typing rule of the effect calculus over `CDerives`, written once, with
  its premises: `[sub]`, `[perform]`, `[raise]`, `[let]` (with its graded side condition read
  from O-QUAL as a grade, after `experiments/Grades`), `[then]`, `[handle]`, `κ`'s types, the
  capability (K-CAP, building on `translate_typed`), `withswap`, the borrow constants as one
  constant per printed constant at any callback row with `TableOK ⟦Σ⟧` (from Shifts' `shiftTy`;
  today's pure constants and `*U` twins as abbreviations), `bounded_fix` at rows, `ν` with
  effectful leaves, the effectful affine closure; outlives at `U(F_Σ A)` and at boxed
  continuations; whether operation types are closed in lifetimes, where SPEC §19 relies on it
  (audit M13, OQ-35). For every former of the baseline (SPEC §§2-17, 22-23), the statement that it
  holds at `F_Σ` unchanged, or the change.
- **Owns.** K-FTY, K-OP, K-RAISE, K-LET, K-THEN, K-HND, K-KONT, K-GEN, K-CAP, K-SWAP, K-BOR,
  K-FIX, K-NU, K-DIV, K-HOST, K-GRADE; and, in its §9, K-SCOPE, K-HDIV, K-CARRIER, K-BORANS,
  K-ALLOC, K-ROWABS, K-SHALLOW, K-FINR, K-OWNERR, K-RELQ, K-SWAPΣ, K-SELFROW, K-FOLDΣ, K-GENNAME,
  K-NEGREC.
- **Must also contain** (§9 of 03) the full construct behind every restriction that narrows a
  construct of 03 or 02, with form, typing, step, model clause, laws and lowering class, marked
  "not adopted", or "in the calculus, lift deferred" for the constructs the user decided (K-HDIV,
  K-ALLOC).
- **Carries.** OQ-3, OQ-7, OQ-12, OQ-13, OQ-14, OQ-15, OQ-16, OQ-17, OQ-20, OQ-24, OQ-25, OQ-26,
  OQ-28, OQ-29, OQ-30, OQ-31, OQ-35, OQ-37, OQ-40, OQ-56, OQ-59, OQ-61, OQ-62, OQ-67, OQ-68.

### 04-dynamics.md: the machine

- **Must contain.** Evaluation contexts and their predicates; every head step of K-STEP with its
  side conditions; the static `κ` and its two entries; cancellation (`⊥`, `ccatch`, `cfin`, the
  cancel state, the error policy); allocator runs under every allocator; unique decomposition
  and determinism with capture; the run-level facts the laws need as `↦*` statements (the
  reduction halves of L-HRET, L-HOP, L-HFWD, L-ALG0, L-W, L-TAIL). Nothing about the relation.
- **Owns.** K-CTX, K-STEP, K-CANCEL, K-RUN.
- **Carries.** OQ-21, OQ-24, OQ-27, OQ-41, OQ-42, OQ-43.

### 05-model.md: the semantic model

- **Must contain.** D-W and D-ORD; D-ARISE with `TabAtS` as a `TW` invariant; D-WPG and D-STOP,
  with D-STOP written as the SPEC entry's text (a kernel definition change); D-TABLE, D-OPTAB,
  D-CANCELTAB, D-TABLEOK, D-EWP; D-SHARE, D-KAP, D-OWED; D-REL, one clause per former of O-TY
  at `W`, with the quantifier placement of OQ-8 shown as the two candidate clause sets until
  settled; D-SEM; D-MODEL, D-COMODEL, D-DTOR; D-BIN as conditional (OQ-4). Each definition's
  `σ = []` instance shown equal to the existing Core definition. The model lemmas of §5.1 with
  their proof routes, each step naming the printed lemma or the existing declaration it uses.
  The probe statements of OQ-9 (a 6.64 frame) and OQ-44 (a 6.65 frame), written out with every
  term and table bound; the probe statement of OQ-58.
- **Owns.** D-W, D-ORD, D-ARISE, D-WPG, D-STOP, D-TABLE, D-OPTAB, D-CANCELTAB, D-TABLEOK,
  D-EWP, D-EWPP, D-SHARE, D-KAP, D-OWED, D-REL, D-SEM, D-MODEL, D-COMODEL, D-DTOR, D-BIN; T-MONO, T-NIL,
  T-STOP, T-ARISE, T-FRAME, T-SUMOK, T-MODEL, T-COMODEL, T-DEF.
- **Carries.** OQ-8, OQ-9, OQ-10, OQ-11, OQ-19, OQ-31, OQ-44, OQ-45, OQ-46, OQ-56, OQ-57, OQ-58,
  OQ-61, OQ-63.

### 06-laws.md: the equational theory

- **Must contain.** Every L id: its statement over `W` (or at `σ = []` with its survival
  obligation, OQ-11); its unary half over D-EWP, with the construct it defines; its binary half
  over `≈` or `≡`, marked as waiting on OQ-4 where it does; whether it follows from TwoRun's
  route; its status today, citing kernel and experiment declarations; the theory-specific laws
  for exceptions, state and linearly used state, generators, and nondeterminism if multi-shot is
  free; sum and tensor, and which pairs of our effects combine which way; the linear laws
  (weakening of a continuation as its destructor, no duplication, the multi-shot condition).
  Every literature claim marked [via …] or upgraded from a primary source; an [R] mark only where
  the source could not be read and a [settle by literature] question boxes it (OQ-64).
- **Owns.** Every L id; O-EQ; T-SI1, T-SI2.
- **Carries.** OQ-4, OQ-5, OQ-11, OQ-15, OQ-16, OQ-18, OQ-21, OQ-22, OQ-27, OQ-43, OQ-47, OQ-48,
  OQ-49, OQ-59, OQ-60, OQ-61, OQ-62, OQ-64, OQ-65, OQ-66, OQ-67.

### 07-metatheory.md: what is proved

- **Must contain.** T-COMPAT as a table, one row per typing rule (03), each with its route and
  its unknown/mechanical mark; T-FP at `W` by induction on the derivation, with `fundamentalC`
  as its `σ = []` instance; the corollaries T-ADEQ, T-SAFE, T-LEAK, T-FIN, T-LIN; T-DET; T-REN
  and its corollaries T-NAH and the copies being meaning-preserving; T-ABS; T-TOTAL as kept;
  T-2RUN, T-BINFP, T-SOUND as conditional on OQ-4. For each, which model lemmas (§5.1) and which
  printed `[TR]` lemmas it rests on.
- **Owns.** T-COMPAT, T-FP, T-ADEQ, T-SAFE, T-LEAK, T-FIN, T-LIN, T-DET, T-REN, T-NAH, T-ABS,
  T-TOTAL, T-2RUN, T-BINFP, T-SOUND, T-T1, T-T2, T-PRES.
- **Carries.** OQ-4, OQ-11, OQ-13, OQ-14, OQ-43, OQ-50, OQ-51, OQ-52, OQ-58, OQ-66.

### 08-correspondence.md: the specification against the code

- **Must contain.** For every K, D, L and T id, the existing declarations that realise it (file:
  line) and their fate: keep, change (with the SPEC entry it needs), promote from an experiment
  (under a SPEC entry), become an abbreviation, retire. The retirement list includes `vRL`,
  `vRLg`, `vRLs`, `vRLa`, `vRLk`, and the GhostEnd and Restrat pieces the audit lists (§3.5),
  each conditional on the re-index. The surface: each handler schema (abort-after, stateful,
  plain, for-site, pull-site) mapped to K-HND or K-CAP with its T-ELAB obligation; shape
  recognisers and special names (`io_bt`) as glue to replace (OQ-6). The lowering: for each
  construct its class (direct call, branch, state machine, copy), the law that justifies it,
  and the backend file (`Backend/Clos/Capture.lean`, `Backend/Clos/Unwind.lean`); cost parity
  as the criterion. The SPEC entries this calculus requires, and the decisions it supersedes or
  revises (48, 52, 53; 57-59 where affected). The "not an approximation" checklist of 01,
  checked id by id: every construct has syntax, statics, dynamics, a model clause, laws and a
  compatibility obligation. The acceptance programs of SPEC §19 and the corpus programs that
  exercise each construct.
- **Owns.** T-CONS, T-ELAB, T-LOWER; the SPEC entries E-* (§3.5).
- **Carries.** OQ-5, OQ-6, OQ-13, OQ-20, OQ-23, OQ-32, OQ-42, OQ-53, OQ-54, OQ-55, OQ-58, OQ-60,
  OQ-61, OQ-67.

### 99-open-questions.md: the register

- **Must contain.** Every open question in the boxed form of §7.1, with its tags and its
  cross-references to the audit and the critic, and a table of every question against what it
  blocks, what settles it, whether it needs the user, and its default; and indexes by tag, by the
  absence of a default, and by the audit's and the critic's numbering.
- **Owns.** Every OQ id.

---

## 9. Sources the sections use

Read in the reports named, with the reports' own marks: the literature study on #235 ("linear
effect algebras"), `docs/effects-tr/12-sources.md`, `docs/effects-tr/17-borrow-callbacks.md`
(branch `borrow-callbacks`), the review inputs on #245, the capture-rebasing sketch on #251, and
the external input on #279. Primary sources named there include
Plotkin-Power (ACS 2003), Plotkin-Pretnar (LMCS 2013), Hyland-Plotkin-Power (TCS 2006),
Møgelberg-Staton (LMCS 2014), Staton (LICS 2013, POPL 2015), Tang-Hillerström-Lindley-Morris
(POPL 2024), van Rooij-Krebbers (POPL 2025), Congard-Munch-Maccagnoni-Douence (ESOP 2026),
Ahman-Bauer (ESOP 2020), Plotkin-Power (MFPS 2008), Brachthäuser et al. (OOPSLA 2020, 2022),
Zhang-Myers (POPL 2019), and for the Kripke structure Ahmed-Dreyer-Rossberg (POPL 2009),
Pitts-Stark (HOOTS 1998) and Timany et al. (POPL 2018) as verified in §17.2. A section that
relies on a passage fetches the primary source (generic user agent; no personal identifiers in
any request) and marks what it read. Fetched by the sections: Ahman-Bauer, *Runners in action*
(arXiv 1910.11629) and Katsumata-Rivas-Uustalu, *Interaction laws of monads and comonads*
(arXiv 1912.13477), in 05 §10 and, for §3 eq. (1), Thm 7 and the kernel theory's equations, in 06 L-SIGNAL; the abstract of Congard-Munch-Maccagnoni-Douence (arXiv
2510.23517), in 06; the abstract of Xie-Brachthäuser-Hillerström-Schuster-Leijen, *Effect
handlers, evidently* (ICFP 2020), in 04 §6.2 and 08 §6; the abstract of Sivaramakrishnan et al.,
*Retrofitting effect handlers onto OCaml* (PLDI 2021, arXiv 2104.00250), in 08 §7; Plotkin & Power,
*Notions of computation determine monads* (FoSSaCS 2002; the authors' copy), whose global-state
axioms 1-7 and semilattice example are cited in 06 L-STATE, L-TENSOR and L-ND; Hyland, Plotkin &
Power, *Combining effects: sum and tensor* (TCS 2006; the authors' copy), §1's definitions of sum
and tensor, in 02 §11 and 06. Kammar & Plotkin (POPL 2012) was not retrievable and is marked [R]
in 06 (OQ-64).

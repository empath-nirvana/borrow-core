# 07 · Metatheory

This section states what is proved of the effect calculus: one compatibility lemma per typing
rule, the fundamental property over the Kripke world `W = (ρ, ls, σ)`, and the theorems that
follow from it. These are adequacy under every allocator, effect safety, leak freedom, LIFO
finalisation and the linear use of continuations. It also covers determinism, renaming and its
two corollaries, totality, and the binary results that wait on OQ-4.

Every object used here is defined in 05 (`D-` ids) or 02–04 (`K-` ids) and is only cited. Notation
is §1 of [00-structure.md](00-structure.md). Marks follow 00 §0.1. Each obligation is marked
**unknown** or **mechanical**. For a mechanical one, the entry names the single step most likely
not to be mechanical.

---

## 0. Shape

The metatheory has the shape the audit found in Core and the literature's Kripke models share
(`docs/effects-audit.md` §5 rows 10–11; ADR'09 Lemma 4.1 and Pitts–Stark Lemma 4.3 as the
monotonicity lemma of a Kripke model [via 17-borrow-callbacks §17.2, verified there]):

```
 model lemmas (05)                       metatheory (07)
 T-DEF  T-NIL  T-MONO  T-STOP  T-ARISE
 T-FRAME  T-SUMOK  T-MODEL  T-COMODEL ──► T-COMPAT (one per rule) ──► T-FP at every W
                                                                        │
                       T-NIL (σ = [] equals cC; per row at U, OQ-58) ◄──┤
                                                                        ▼
                     T-ADEQ, T-SAFE, T-LEAK, T-TOTAL  (closed programs at W₀ = (∅, [], []))
                     T-FIN, T-LIN                     (runs; OQ-50)
                     T-T1 at σ = [];  T-T2 at general σ (OQ-2);  T-PRES
 machine (04) ──► T-DET ──► T-2RUN ;  K-REN ──► T-REN ──► T-NAH, copies ; T-ABS, T-BINFP, T-SOUND (OQ-4)
```

The fundamental property is proved once, at every `W`. Every closed-program corollary is a
statement at the initial world `W₀ = (∅, [], [])`, so it reads only the `σ = []` instance of T-FP.
That instance is today's `fundamentalC` statement (`Core/Fundamental.lean:434`) once T-NIL holds:
by definition at the clauses that read no extension of the world, and by a per-row proof at `U`,
`share` and `KapRel`, which is unknown (OQ-58). If OQ-58 is settled positively, the corollaries
keep their statements across the re-index; otherwise Core's `vCE` changes meaning and every
corollary is re-proved through T-FP at `W` (05 T-NIL). The general-`σ` T-FP is still
needed: the `σ = []` instance of a rule whose callback runs inside a lend (`K-BOR`, `K-HND` between
lenders) is proved through the callback's relation at `σ · new`. Today the kernel avoids that
step only by R-T1.

---

## 1. The judgements this section proves things about

These are cited, not redefined.

- `Δ; Γ ⊢ e : j` is `CDerives` (O-JDG; `Core/Fundamental.lean:60`), extended by 03's rules,
  where `j ::= val A | comp C`.
- `Δ; Γ ⊨ e : C` is D-SEM (05), quoted for reading the theorems below:

  ```
  Δ; Γ ⊨ e : C   ≜   ∀ δ γ W ρ.  Δ.Models δ  →  Wf W  →  σ.WF Δ  →  TabAt_W(ρ)  →
                       𝒢⟦Γ⟧_W δ γ ρ  →  𝒞⟦C⟧_W δ (γ e) ρ
  Δ; Γ ⊨ V : A   ≜   Δ; Γ ⊨ V : F A
  ```

  The open lends' lifetimes are bound in `δ` by the binders that opened them. `TabAt_W` is a `TW`
  invariant (D-ARISE, T-ARISE): every configuration at which D-SEM is used supplies it, so the
  premise is discharged at every use, not assumed of a resource that does not arise. Whether the
  clauses themselves keep the guard is OQ-45. At `σ = []`, `Wf`, `σ.WF Δ` and `TabAt` hold
  trivially and D-SEM is `SemC` (`Core/Relation.lean:228`), which quantifies over `δ γ ls ρ`
  (`Core/Relation.lean:229`).
- `ewp_W(e){Tb}{Q}` (D-EWP) and `wpG_W(e){Q}` (D-WPG). At a value, `wpG_W ∘ valPost` is
  `wpTS`, the printed `[TR]` p.6 `wp` (T-STOP; `Core/World.lean:186`, `Core/EffWp.lean:43`).
- Runs: `ARun A k μ e k' μ' e'`, an allocator run of the allocator `A` (K-RUN; SPEC §13,
  `SPEC.md:1119`). `Steps` is a run of the machine. `W₀ = (∅, [], [])` and `μ₀` is the empty
  memory (`Adequacy.emptyMem`).

---

## 2. Compatibility

### T-COMPAT: one compatibility lemma per typing rule, at `W`
- Form: for each rule `R` of 03 with premises `Δᵢ; Γᵢ ⊢ eᵢ : jᵢ` and conclusion `Δ; Γ ⊢ e : j`,
  ```
  (∀ i. Δᵢ; Γᵢ ⊨ eᵢ : jᵢ)  ⟹  Δ; Γ ⊨ e : j        (at every W, by D-SEM)
  ```
- Uses: D-SEM, D-REL, D-EWP, D-WPG, D-STOP, D-OPTAB, D-TABLEOK, D-SHARE, D-KAP, D-OWED, D-MODEL,
  D-COMODEL; every K id of 03.
- Today: one lemma per `CDerives` constructor, all at `σ = []`, dispatched by `fundamentalC`
  (`Core/Fundamental.lean:436-529`). Status **changed**: each lemma is re-stated at `W`, and its
  `σ = []` instance is the existing lemma by T-NIL.
- Slices: the rules are 03's; the steps they use are 04's; the clauses are 05's.
- Depends on: T-DEF, T-NIL, T-MONO, T-STOP, T-ARISE, T-FRAME, T-SUMOK, T-MODEL, T-COMODEL.
- Open: OQ-8 (rows B), OQ-9 and OQ-10 (rows F at a stop), OQ-3 (`[handle]` between lenders),
  OQ-7 (`[then]` and the unwinding forms), OQ-20 (effectful `withswap`), OQ-15 (div), OQ-30
  (host), OQ-1 (capabilities). R-T1, R-MID, R-FINAB, R-PURESWAP restrict rows by default; R-HDIV and R-ALLOCORACLE defer the lift of K-HDIV's spanning form and K-ALLOC until OQ-67 and OQ-68.
- Obligation: per row, in the table below.

**Order of work.** First write the statement of T-FP at `W` with every row of the table as an
enumerated `sorry` in an experiment, and T-MONO as one more: the whole-rule-set check
(`docs/effects-audit.md` M6). Do routine rows first, then the non-routine ones. The
audit's hard stops (§6 step 7.5) apply unchanged. If the relation needs a second redesign, if a
row needs a construct or predicate not in 05, if depth needs per-depth lemmas, if `σ = []` fails
to equal `cC` (OQ-58's `NilAgreesU` refuted at an introduction row), or if T-MONO does not close by
one induction on types: report, as a
named `def … : Prop` or a configuration with every hypothesis discharged.

**The table.** "Route at `W`" names the model lemma the row adds to today's proof. Today's proof
is the `σ = []` route. "[TR]" names the printed compatibility lemma the row transcribes, where
there is one (`Paper/INDEX.md:174-199`).

#### Rows A: formers whose clauses read no world quantifier

`⊗`, `⊕`, `0`, `1`, `!`, `[@a]`, `Ref`, `&`, `⊤`, `μ` and the `F A` clause carry no future-world
quantifier (`Core/Relation.lean:120-150, 155, 158-160`). At a value, D-STOP leaves `σ` unchanged
(T-STOP). So each lemma is today's proof with `ls` read as `W`. These rows are **mechanical**. The
single step that might not be is `bind`: `N`'s context `Γ₂` is framed across `M`'s run and read at
`M`'s post-world. At a value that world has the same `σ`, so this is today's `wpTS` bind, but it
must be checked against D-STOP's exact value clause.

| rule (03) | today | [TR] | mark |
|---|---|---|---|
| `var` | `var_compatC` `Core/Compat.lean:47` | 6.152 | mechanical |
| `unitI`, `unitE` | `Core/Compat.lean:56, 269` | 6.153, 6.154 | mechanical |
| `tensorI`, `tensorE` | `Core/Compat.lean:63, 282` | 6.155, 6.156 | mechanical |
| `sumI₁`, `sumI₂`, `sumE`, `zeroE` | `Core/Compat.lean:80, 87, 304, 330` | 6.157, 6.158 | mechanical |
| `ret`, `bind` | `Core/Compat.lean:130, 179` | — (CBPV) | mechanical; `bind` as above |
| `withI`, `proj₁`, `proj₂`, `topI` | `Core/Compat.lean:222, 249, 256, 263` | — | mechanical |
| `bangE`, `copyBang`, `forgetBang` | `Core/Compat.lean:406, 412, 431` | — (the `!` rules) | mechanical |
| `boxI`, `boxE` | `Core/Compat.lean:496, 450` | 6.163, 6.164 | mechanical; `boxI` reads `CtxOutlives` (`Core/Fundamental.lean:139`), and outlives at `U(F_Σ A)` is OQ-28 |
| `immSub`, `mutSub` | `Core/Compat.lean:456, 468` | 6.167, 6.168 | mechanical |
| `roll`, `unroll` | `Core/Fundamental.lean:44, 49` | — | mechanical |
| `lolliE`, `allEV`, `ofRet` | `Core/Compatibility.lean:512, 731`; `ofRet` is the identity (`Core/Fundamental.lean:515`) | 6.160 (CBV `⊸E`) | mechanical |

#### Rows B: the Kripke points (OQ-8)

These rows read a clause where a future-world quantifier sits under at least one candidate of
OQ-8. Today the quantifier is at `U` (`Core/Relation.lean:127-128`), and `⊸` and `∀` quantify only
over resource extensions through `─⋆` (`Core/Relation.lean:156-157, 161-162`). These rows are
**unknown** until OQ-8 is settled. Their proof shape is fixed under either candidate: a thunk
created at `W` and forced at `W' ⊒ W` needs its captured context `𝒢⟦Γ⟧_W δ γ` moved to `W'`, which
is T-MONO. This is the callback case the audit names (M3). Under candidate (b) the same step
recurs at `allI`, as in `cRLk` (branch `borrow-callbacks`,
`experiments/GhostEnd/GhostEnd/Extend.lean:92-96`, whose stack "grows at ∀ and nowhere else",
`:19-20`), and `allE` is the `τ = []` instance (`all_elimK`, `…/Extend.lean:110`). At `lam` the
candidate's clause is not yet built: `cRLk`'s `⊸` clause quantifies over resources only
(`:86-87`).

| rule | today | route at `W` | mark |
|---|---|---|---|
| `thunkF`, `thunkV` | `Core/Compat.lean:105, 118` | T-MONO on `Γ` to every `W' ⊒ W` | unknown (OQ-8) |
| `bangThunkF`, `bangThunkV` | `Core/Compat.lean:380, 394` | as `thunk`, at `ρ = ∅` | unknown (OQ-8) |
| `[thunkΣ]`, `[bangThunkΣ]` (K-FTY) | not built (changed rules, 03) | as `thunk`; the forced body is read by `ewp_W` through `cC_effOf` (`Core/EffRules.lean:73`) | unknown (OQ-8); mechanical at `σ = []` |
| `force` | `Core/Compat.lean:145` | instantiate `U`'s quantifier at `W' = W` (reflexivity of D-ORD) | mechanical once OQ-8 is fixed |
| `lam` (6.159), `app` | `Core/Compat.lean:154, 164` | (a): today's; (b): T-MONO at every extension | unknown (OQ-8) |
| `allI` (6.161), `allE` (6.162) | `Core/Compat.lean:345, 483` | (a): today's; (b): the extension `τ ++ σ` with `τ`'s variables fresh (`…/Extend.lean:81-95`) | unknown (OQ-8) |

#### Rows C: constants of the resource world

These are the BoLo axioms, integers, host operations, arrays and slices, counted loops and folds.
Each is a value at `Ctx.DeadP` whose type is `!` or `⊸`, and its proof runs through `wpTS` rules
built from `TW`'s constructors (`alloc`, `free`, `store`, the frames; `Core/World.lean:110-167`).
Those constructors are polymorphic in `ps` (`Core/World.lean:112-150`), so a run at a world whose
`σ` is non-empty preserves `TW` with `σ` untouched. These rows are **mechanical**. The step that
might not be is any lemma among these that takes `ps = []` or `Tagged` at the empty list as a
hypothesis rather than as an instance. Grep each proof for it before lifting.

| rule | today | [TR] |
|---|---|---|
| `alloc`, `free`, `swap`, `copy`, `forgetImm`, `forgetMut`, `forgetUnk` | `Core/Compatibility.lean:579, 539, 594, 653, 675, 694, 713` | 6.165, 6.166, 6.169, 6.170, 6.171 |
| `lit`, `hostOp` | `Core/Integers.lean:204, 213` | — |
| `arrNew`, `arrFree`, `arrSize`, `arrReplace`, `arrLen`, `arrGet`, `arrCopy`, `arrForget` | `Core/Arrays.lean:500, 560, 265, 369, 132, 171, 224, 253` | — |
| `sliceGetM`, `sliceLenM`, `sliceSplitI`, `sliceSplitM`, `sliceEmptyI`, `sliceEmptyM`, `sliceReplaceM`, `sliceSwapM` | `Core/Slices.lean:315, 319`; `Core/SliceOps.lean:83, 87, 99, 103, 131, 294` | — |
| `countFold`, `countTry` | `Core/CountFold.lean:94, 182` | — |
| `foldImm`, `foldOwn`, `foldReuse` | `Core/FoldImm.lean:625`, `Core/FoldOwn.lean:358`, `Core/FoldReuse.lean:426` | — |

#### Rows D: borrow constants (K-BOR, K-SWAP)

K-BOR has one constant per printed constant `k ∈ {withbor1, withbor2, withbor3, withload,
sliceBorrowM, sliceBorrowI}` at a callback row `Σ` with `TableOK ⟦Σ⟧δ` (D-TABLEOK). Its row is:

```
TableOK ⟦Σ⟧δ    k's side conditions (as today)
──────────────────────────────────────────────  T-COMPAT[bor_k]
Δ; Γ ⊨ bor_k[Σ] : τ_k[Σ]
```

*Route.* This is the printed lemma's proof (6.172–6.176). Its frame step is replaced by T-FRAME
at the table `opTable ⟦Σ⟧δ`, and its callback step instantiates the callback's `∀` and `⊸` clauses
at the extended world `W · new`. A fresh lend is created by the constant's own lemma, the world is
extended, and the callback's clauses are applied there. This is the pattern of every verified
Kripke model of a scoped allocation (Timany et al. POPL 2018, Lemma 3.2; λRust F-newlft;
Thamsborg–Birkedal Lemma 6.4 [via 17-borrow-callbacks §17.2, verified there]), and the shape of
`callback_ext` (`…/Extend.lean:131`) and `callback_ext_one` (`…/Extend.lean:167`). The row is then
closed under row sum by T-SUMOK. That makes the row generic in `Σ`, as Shifts' one schema
(`shiftTy`, `experiments/Shifts/Shifts.lean:17`) is generic in source and view.

*Instances.* `Σ = ∅`: today's pure constants (`Core/Compatibility.lean:937, 1028, 1109, 252`;
`Core/Slices.lean:60, 176`). `Σ` abortive: today's `*U` constants (`Core/EffBorrow.lean:275, 356,
446, 548, 645, 726`), through the abortive half of T-FRAME (`Core/EffWp.lean:828-854`); their
compatibility lemmas become instances. `Σ` resuming: new.

| constant | today | [TR] | mark |
|---|---|---|---|
| `bor_k[∅]` | the pure lemmas above | 6.172–6.175, `slice_borrow_*` | mechanical (instance) |
| `bor_k[Σ]`, `Σ` abortive | the `*U` lemmas above | same, unwinding forms SPEC §19 | mechanical (instance); the step: the unwinding finaliser `d` at R-FINAB (OQ-7) |
| `bor_k[Σ]`, `Σ` resuming, `k ≠ withload` | not built; `callback_ext` at one entry on a branch | 6.172–6.174 | **unknown**: T-FRAME's resuming halves (05) and OQ-9 |
| `bor_withload[Σ]`, `Σ` resuming | not built | 6.175 | **unknown**: 6.150 is not lifted to `ewp` (audit m6) |
| `withswap` | `Core/Compatibility.lean:1194` | 6.176 | mechanical at R-PURESWAP; effectful callee is OQ-20, unknown |

#### Rows E: codata and fixed points (K-NU, K-FIX, K-DIV)

| rule | today | route at `W` | mark |
|---|---|---|---|
| `nuIn`, `nuOut` | `Core/Nu.lean:517, 522` | the greatest fixed point clause (`Core/Relation.lean:163-164`) at `W`: the candidate `R` ranges over `W`-indexed predicates | mechanical |
| `unfoldN` | `Core/Nu.lean:492` | coinduction at `W`; an effectful observation leaf (`cB`'s `F_Σ` clause, `Core/Relation.lean:196-199`) is an `ewp_W` | mechanical at R-T1; **unknown** at general `σ` (a lend open across an observation that stops) |
| `boundedFix` | `Core/BoundedFix.lean:91` | induction on the budget at every computation type, rows included | mechanical; the step: a generator's layer composed before the fixed point (L-FIX) at a row |
| div (K-DIV) | codata (SPEC Entry 13, `SPEC.md:1190`) | per OQ-15 | per OQ-15 |
| a handler around a div computation (K-HDIV, 03 §9.2) | not built (SPEC §21 *Open*) | per observation: coinduction plus `ewp_handle`; spanning: `HndLoopSpanCompat` at a stored `κ` (OQ-28, OQ-46); under OQ-15 (b), `handle_compatC` at `ewpP_W` (D-EWPP) | per observation mechanical; spanning **unknown** (OQ-67; lift deferred by R-HDIV) |
| folds and counted loops at a row (K-FOLDΣ, 03 §9.13) | `Core/FoldImm.lean`, `Core/FoldOwn.lean`, `Core/CountFold.lean` at pure algebras | induction on the structure or the count, `ewp_bind` per level; `foldImm[Σ]` through T-FRAME's 6.64 half | not adopted (R-PUREFOLD, OQ-62); mechanical at abortive rows, **unknown** at resuming rows |

#### Rows F: the effect rules (K-OP, K-RAISE, K-LET, K-THEN, K-HND, K-KONT, K-CANCEL)

| rule | today | route at `W` | mark |
|---|---|---|---|
| `[sub]` | `sub_compatC` `Core/EffRules.lean:774`; `ewp_sub` `:159` | table inclusion is monotone (D-TABLE) | mechanical |
| `[perform]` | `perform_compatC` `Core/EffRules.lean:781`; `ewp_perform_here` `:100` | the stop hands the 6.64 frames it left open, `τ'`, to `opTable` (D-STOP, D-OPTAB) | **unknown** (OQ-9, OQ-10); at R-T1, mechanical |
| `[raise]` | `raise_compatC` `Core/EffRules.lean:797`; `ewp_raise_here` `:115` | abortive: owes nothing; argument `NoOwn` (R-NOOWNERR) | mechanical; OQ-24 changes the argument clause |
| `[let]` | `let_compatC` `Core/EffRules.lean:896`; `ewp_frame_plain` `:193` | L-ALG's unary form from T-MODEL (M3): the frame `K` stopped at grade `q` owes `Γ₂` scaled by `q` | mechanical at R-T1; **unknown** at general `σ`: `K` with open frames is captured into `κ` |
| `[then]` | `then_compatC` `Core/EffRules.lean:928`; `ewp_frame_then` `:369` | L-ALG0: `D` runs on `Γ₂` at an abortive stop and at a cancel | mechanical at R-FINAB; OQ-7 otherwise |
| `[handle]` | `handle_compatC` `Core/EffRules.lean:1092`; `ewp_handle` `:615` | T-MODEL (M2): `hnd_n H` is the initial map out of the least fixed point into the model `H`; `ewp_handle`'s five cases become one lemma | mechanical at R-MID; **unknown** between lenders (OQ-3) |
| `κ` (K-KONT) | `ewp_kappa_resume` `Core/EffRules.lean:493`, `ewp_kappa_cancel` `:529`, `vC_kTy_of_kapRel` `:1053` | D-KAP at `W` | as `[handle]`; quantifier OQ-8 |
| cancel (K-CANCEL) | `ewp_ccatch` `Core/EffRules.lean:580`, `ewp_cfin` `:284`, `cancel_frame` `:168` | `cancelTab` is abortive (`Core/EffWp.lean:1013`) | mechanical at R-T1; **unknown** at general `σ` (OQ-9's first probe) |
| the graded side conditions (K-GRADE) | `[let]`'s `hW`, `hU` (`Core/Fundamental.lean:354`); `fundamentalGraded` (`experiments/Grades/Grades/Soundness.lean:416`) | the qualifier as a grade on the captured context | mechanical |

#### Rows G: constructs new to the kernel

| rule | today | route at `W` | mark |
|---|---|---|---|
| a capability (K-CAP) | `translate_typed` `experiments/HandlersAsBorrows/HandlersAsBorrows/Translate.lean:190`, into `DerivesWf`, not `CDerives` | T-COMODEL; the borrow it rides on is `withbor` form (2) (`handle_is_shift`, `…/Safety.lean:115`), so Rows D | unknown (OQ-1, OQ-19) |
| host handlers (K-HOST) | `hostOp` (`Core/Integers.lean:213`) | per OQ-30 | per OQ-30 |
| effectful affine closure (K-NU, SPEC Entry 21) | SPEC `SPEC.md:3288` | as `unfoldN` | as `unfoldN` |
| a stored continuation (K-GEN, 03 §4) | `gen_compatC` (branch `lift-stage1`, `Core/Gen.lean`; T14.6 then T14.4), at `Σ = ∅`, `σ = []` | option (a): `[TR]` 6.62 puts the body's resource in `Res_{δ(c)}`, `wpTS_box` (6.147) keeps every suspension there, `affBox_of_kapRel` reads `κ` off by `aff_coind`; option (b): the outlives rule at `U C` checked against D-REL's `[@c]` clause | (a) as built on its branch at `Σ = ∅`; at a row and at `W` **unknown** (OQ-28, OQ-46) |
| allocation as an effect (K-ALLOC, 03 §9.5) | `alloc` compatibility `[TR]` 6.165 | the host handler `IsModel` from 6.165-6.166; arenas through T-FRAME at a resuming table | host handler mechanical; arenas **unknown** (OQ-68; lift deferred by R-ALLOCORACLE) |
| the not-adopted constructs of 03 §9 (K-SCOPE, K-CARRIER, K-BORANS, K-ROWABS, K-SHALLOW, K-FINR, K-OWNERR, K-RELQ, K-SWAPΣ, K-SELFROW, K-GENNAME) | not built | as each entry's *Obligation* states | **unknown**, each under its question |

---

## 3. The fundamental property

### T-FP: the fundamental property at every world
- Form:
  ```
  ∀ Δ Γ e j.   Δ; Γ ⊢ e : j   ⟹   Δ; Γ ⊨ e : j          (D-SEM, at every W)
  ```
  **Corollary (the `σ = []` instance).** `∀ Δ Γ e j. Δ; Γ ⊢ e : j ⟹ SemJ Δ Γ e j`, which is
  `fundamentalC`'s statement (`Core/Fundamental.lean:429-435`), by T-NIL.
- Uses: D-SEM, D-REL, every K id.
- Today: `fundamentalC` (`Core/Fundamental.lean:434`) at `σ = []`; `fundamentalD`
  (`Core/Demonic.lean:284`) at the demonic `wp`. At a stack, GFP is stated and not proved:
  `GFPAt σ` (`experiments/GhostEnd/GhostEnd/Stacked.lean:305`), with `gfpAt_nil`
  (`…/Stacked.lean:613`) being `fundamentalC`. Status **changed** (re-indexed).
- Slices: rules 03; clauses 05; corollaries §4.
- Depends on: T-COMPAT (every row), T-DEF.
- Open: OQ-8 (the relation's shape), OQ-9 and OQ-10 (the stop), OQ-3, OQ-11.
- Obligation: **mechanical given T-COMPAT.** Induction on the derivation. Each case is its row.
  This is `[TR]` 6.151's proof structure (`Paper/INDEX.md:174`; the induction is
  `Core/Fundamental.lean:436-529`). The step most likely not to be mechanical: the `allI` case
  applies `semC_liveEq` to the premise (`Core/Fundamental.lean:458`), a lemma at `σ = []` that must
  be restated at `W`.

**What it subsumes.** `fundamentalC` and `fundamentalD` become its `σ = []` instance and the
instance's demonic reading (`wpTS_demonic`, `Core/Demonic.lean:240`). The GhostEnd restatements
(`segment_fundamental`, `restrat_segment`, `gfpAt_nil`, `gfpAtA_nil`; audit §2.2) are retired.
`fundamentalGraded` (`experiments/Grades/Grades/Soundness.lean:416`) becomes the K-GRADE row.
HandlersAsBorrows' `effect_safety` (`…/Safety.lean:55`), proved through `DerivesWf` and
`Paper/CONF/Results.lean:349`, becomes a K-CAP instance once K-CAP is a `CDerives` rule.

**Why it is proved at every `W`, not only at `σ = []`.** The `σ = []` statement suffices for
every corollary (§4). It does not suffice as an induction hypothesis. A callback's derivation
is read at `σ · new` when the borrow's row resumes (Rows D), and a handler's body is read below an
open lend when the handler sits between lenders (OQ-3). With R-T1 and R-MID both imposed, the
induction closes at `σ = []` alone, which is today's kernel. T-FP at every `W` is what removing
either restriction costs.

---

## 4. Corollaries

Each corollary is stated at the initial world and reads only T-FP's `σ = []` instance. Its proof
is unchanged by the re-index, provided T-NIL holds.

### T-ADEQ: adequacy under every allocator
- Form:
  ```
  ⊢ e : F 1   (closed, Δ = ·, Γ = ·)   ⟹
    (i)   ∀ A k. ∃ k' μ'.  ARun A k μ₀ e k' μ' ()            (some run, under every allocator)
    (ii)  ∀ μ₁ e₁.  μ₀, e ↦* μ₁, e₁   ⟹   μ₁, e₁ ↦* μ₀, ()   (every run continues to () at μ₀)
    (iii) ∀ μ₁ e₁.  μ₀, e ↦* μ₁, e₁   ⟹   e₁ value  ∨  ∃ μ₂ e₂. μ₁, e₁ ↦ μ₂, e₂   (never stuck)
  ```
  At a value type `A` in place of `1`: the final memory holds exactly the value's resources
  (`wpTS`'s post-condition, `Core/World.lean:197-199`).
- Uses: D-SEM, D-WPG (value case).
- Today: `adequacyC` (`Core/Fundamental.lean:590`) via `theorem32` and `corollary33` (`:558, 577`),
  which are `[CONF]` Theorem 3.2 and Corollary 3.3 (`Paper/INDEX.md:201-202`). Also `adequacyD`,
  `adequacyD_safe`, `adequacyD_val` (`Core/Demonic.lean:312, 325, 334`) and `total_every_alloc`
  (`Core/Totality.lean:40`) for (i). Status **as built**.
- Slices: K-RUN (04).
- Depends on: T-FP's `σ = []` instance, T-NIL.
- Open: OQ-30 (a `main` program at the host's row: its statement is at the host's outermost
  handlers, not `F 1`).
- Obligation: **mechanical**. The step: `reclaim` (`Core/Fundamental.lean:534`) derives the empty
  leftover from `UpdV ∅ ρ ∧ NoOwn ρ`, and it must read D-WPG's post-configuration unchanged at
  `σ = []`.

### T-SAFE: effect safety
- Form. *Closed:* `⊢ e : F_∅ A ⟹` no run of `e` from `μ₀` reaches a term `K[perform_{n,i} v]` or
  `K[raise_{n,i} v]` with `K` free of `n`. *Open, at every `W`:*
  ```
  Δ; Γ ⊢ e : F_Σ A,   𝒢⟦Γ⟧_W δ γ   ⟹   every run of γ e from a configuration D-WPG quantifies over
     ends at a value in 𝒱⟦A⟧_W δ,  or stops at  K[perform_{n,i} v]  with (n,i) ∈ Σ, abort = false, K free of n,
                                   or stops at  K[raise_{n,i} v]    with (n,i) ∈ Σ, abort = true,  K catching nothing of n
  ```
  The arguments are in `⟦Σ⟧δ`'s parameter relation, and the continuation owes D-SHARE.
- Uses: D-OPTAB, D-EWP, K-ROW (`F A = F_∅ A`).
- Today: `ewp_bot` (`Core/EffWp.lean:772`) with `adequacyD`. The open form is the definition of
  `opTable` (`Core/EffDefs.lean:157-167`) read through `ewp_unfold` (`Core/EffWp.lean:765`); it is
  not a named theorem. SPEC §19 *Theorems* 4 states it in prose ("a closed program with an
  unhandled operation is not typed at `F 1`", `SPEC.md:2778`). Status **as built** (closed);
  **new** as a named open theorem.
- Slices: K-OP, K-RAISE (03); K-CTX `HasHnd`, `Catches` (04).
- Depends on: T-FP, T-ADEQ.
- Open: none.
- Obligation: **mechanical**. The step: a stuck `K[perform v]` with no handler is not a value
  and has no head step, which T-ADEQ (iii) excludes. This needs the machine fact that `perform`
  steps only under a handler of its name (K-STEP `[op]`).

### T-LEAK: leak freedom
- Form:
  ```
  (closed)   ⊢ e : F 1  ⟹  every complete run from μ₀ ends at μ₀
  (at W)     ewp_W(e){Tb}{Q}  ⟹  at every value end, the leftover ρ⁺ satisfies NoOwn ρ⁺, and
             at every stop the continuation's share, D-SHARE, holds every resource still owned
  ```
- Uses: D-WPG (the `NoOwn ρp` conjunct), D-SHARE, D-OWED.
- Today: the `NoOwn ρp` conjunct of `wpTS` and `wpG` (`Core/World.lean:197`,
  `Core/EffDefs.lean:38`). The closed form is part of `adequacyC` and `adequacyD` (the final memory
  is `Adequacy.emptyMem`: `Core/Fundamental.lean:571-574`, `Core/Demonic.lean:304-307`). An
  abortive stop drops a `NoOwn` continuation (`Core/EffDefs.lean:165-167`). Status **as built**
  at R-T1.
- Slices: L-W (06); K-CANCEL (04).
- Depends on: T-FP, T-ADEQ; at general `σ`, T-T2.
- Open: OQ-9. At general `σ` a stop hands open frames to the table. Leak freedom then requires
  every continuation path to close them, and OQ-9's first probe asks whether this holds.
- Obligation: **mechanical** at `σ = []`. **Unknown** at general `σ` (OQ-9).

### T-FIN: finalisation exactly once, LIFO
- Form. Let `⊢ e : F 1`, and fix a complete run `μ₀, e ↦* μ', ()` under any allocator. Call each
  evaluation of `M then x. N unwind D` (`ubind`) a frame instance. Then:
  1. *(once)* each frame instance is left exactly once: by `[then]` (`M` returned), or by
     `[finalise]` / `[finalise-cancel]` (`M` raised, or its continuation was cancelled), the
     latter running `D` exactly once. A frame instance inside a context captured into a `κ` is
     left once per use of that `κ`: at most once at `aff`, exactly once at `lin`, and once per copy
     at `unr`. Each `D` run at a cancel is on the context's own resources.
  2. *(LIFO)* frame instances are left in the reverse of the order they were entered, along each
     path of the run.
  3. *(resources)* every resource owned at a frame instance's entry and not passed to `N` is
     released by its `D` or returned by `N`. No location is released twice.
- Uses: O-FIN, D-DTOR, K-CTX, K-STEP.
- Today: not a named corollary (`docs/effects-audit.md` m10, §5 row 8). (2) is the machine:
  `Kont` is a stack and every head step acts at the innermost frame (`Paper/S3_Dynamics/Definitions.lean:495-545`;
  unique decomposition T-DET). (3)'s "no double release" is T-ADEQ (iii), since a released
  location's second release is stuck, and its "released" is T-LEAK. Status **new**.
- Slices: L-W, L-ALG0 (06); `[finalise]`, `[cancel]` (04).
- Depends on: T-ADEQ, T-LEAK, T-LIN, T-DET.
- Open: OQ-50 (how (1)'s "once per use of `κ`" is observed); OQ-7 (finalisers at a resuming
  table); OQ-21 (what `D` may perform and the error policy).
- Obligation: (2) and (3) **mechanical**. (1) is **unknown** in its `κ` clause (OQ-50). Without
  `κ` it is an induction on the run, which ends at a value with the empty context, so every frame
  entered was left. The literature's statement of this property is Ahman–Bauer ESOP 2020,
  Theorem 7 (finalisation "in the absence of external kill signals … is executed exactly once",
  arXiv 1910.11629, introduction, fetched in 05 §10). LIFO is Congard–Munch-Maccagnoni–Douence
  ESOP 2026, Prop. 2 (the release list `l′ = l`) [via #235, from the fetched summary]. Thm 7's
  finalisation map covers a run's own signals too: a co-operation's signal skips the rest of the
  user code and runs the clause `kill s ↦ N_s` (`φ_γ(ι₂ s) = ⟦N_s⟧`, arXiv 1910.11629 §3.2, §5.3);
  only an enveloping runner's signal bypasses the inner finalisation. Our cancel is uninterceptable
  (K-CANCEL) and runs the destructor `D_K`, LIFO, one finaliser per frame (06 L-SIGNAL); whether it
  is an instance of the signal is OQ-66. T-FIN holds with cancel included.

### T-LIN: linear and affine continuations are used as their qualifier says
- Form. Let `⊢ e : F 1` and fix a complete run. A `κ` value created by `[op]` at an operation of
  qualifier `q` is used, by `resume` or `cancel`, exactly once if `q = lin`, at most once if
  `q = aff`, and any number of times if `q = unr`, where each copy's captures are persistent
  (`ρ = ∅`, `Core/EffDefs.lean:146`; `Core/EffRules.lean:571`).
- Uses: K-KONT, O-QUAL, D-SHARE, D-KAP.
- Today: by typing only. `kTy` (`Core/EffRules.lean:976-980`) gives `κ` a `U` type, not `!`, at
  `lin` and `aff`, and `[let]`'s side conditions (`Core/Fundamental.lean:353-357`) bound the
  captured context. No run-level theorem exists. Status **new**.
- Slices: L-C, L-P (06).
- Depends on: T-FP; OQ-50's route.
- Open: OQ-50, OQ-16.
- Obligation: **unknown**. The unary relation sees resources. A `κ` that captures owned resources
  and is dropped breaks T-LEAK, and one resumed twice breaks T-ADEQ (iii), so the resource half
  follows. A `κ` that captures nothing owned can be dropped or duplicated without any
  resource-visible effect, so the unary relation alone does not state T-LIN (OQ-50).

---

## 5. T1 at `σ = []`, and the statement at general `σ`

### T-T1: no internal lend spans a stop, at `σ = []`
- Form:
  ```
  ∀ e Tb Q, W = (ρ, ls, []).   ewp_W(e){Tb}{Q} at ρ,  Tb receiving no frames   ⟹
     every stop t reached in the unfolding, from frames ps and list ls, has  ps' = ps ∧ ls' = ls
  ```
  Equivalently, every 6.64 frame and every reborrow record opened inside `e` is closed before `e`
  stops. **Syntactic half.** Under R-T1, every borrow's callback row is abortive (`Row.Unwind`,
  `Core/EffBorrow.lean:133`), so its table is `Abortive` (`Row.Unwind.abort`, `:143`;
  `opTable_abortive`, `Core/EffRules.lean:255`), and the abortive instance of T-FRAME suffices
  (`ewpTS_*_frameU`, `Core/EffWp.lean:828-854`).
- Uses: D-STOP, D-WPG, D-TABLEOK.
- Today: true **by definition**. `wpG`'s final conjuncts `(∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls)`
  hold at every final term, a stop included (`Core/EffDefs.lean:40`). The audit names this clause
  as the single source of T1 (C1). Status **changed**: under D-STOP it becomes a theorem, from
  T-STOP's `σ = []` clause.
- Slices: K-BOR's callback row (03); D-STOP (05).
- Depends on: T-STOP.
- Open: OQ-2, OQ-9, OQ-10.
- Obligation: **mechanical** given D-STOP's text. The step: at `σ = []` D-STOP's stop clause must
  reduce to `Core/EffDefs.lean:40` by definition, not by a proved equivalence (00 §1, *Reading of
  `W`*). Our own TR states the analogous condition, T1 needed only for a borrowed source whose
  callback's table is not in place or abortive (`docs/effects-tr/09-factoring.md` §9.3, T9.1, L9.2,
  T9.2).

### T-T2: lends that span a stop, at general `σ`
- Form. For a `TableOK` table `Tb` and `W = (ρ, ls, σ)`:
  ```
  ewp_W(τ)(e){Tb}{Q}  ⟹  at a stop with frames ps' ⊇ ps, the 6.64 frames τ' (ps' ↔ frames τ' ++ ps) are
    handed to Tb (and 6.65 lends as OQ-44 records them), and for each continuation path of the
    stopped context:
      resumed and run to a value           — the frames close at the value (D-STOP value clause);
      cancelled  (D-OWED, cancelTab)       — the frames close in the cancel run, LIFO, leftover NoOwn;
      dropped at an abortive operation     — the frames close before the drop, leftover NoOwn;
      resumed by a handler between lenders — the frames close in nesting order (with OQ-3)
  ```
  so that T-LEAK and T-FIN hold at every `W`.
- Uses: D-STOP, D-OWED, D-SHARE, D-KAP, D-CANCELTAB, D-TABLEOK, D-ORD.
- Today: not built. The resuming frame halves exist at one stack shape each in GhostEnd
  (`ewpTS_M_frameR` `experiments/GhostEnd/GhostEnd/Relend.lean:117`, `ewpTS_I_frameR`
  `…/ImmLend.lean:175`, `ewpTS_M_antiFrameR` `…/Frames.lean:89`, `stack_step_*`
  `…/StackStep.lean:392, 563, 1003`). They hold under `AllCross` (`…/StackStep.lean:182`),
  discharged only by constant `true` (audit M8), and under `LinResume` (`…/Body.lean:141`).
  Status **new**.
- Slices: 05 (D-STOP's text and SPEC entry).
- Depends on: T-FRAME at resuming tables, T-MONO, T-ARISE.
- Open: OQ-2 (whether the first lift implements it), OQ-9 (first probe), OQ-10, OQ-3, OQ-28.
- Obligation: **unknown**. This is the first unknown of the calculus. It is not attempted before
  OQ-9's `[handle]` + cancel configuration.

---

## 6. Preservation

### T-PRES: every run preserves the typed world
- Form:
  ```
  (world)      every run segment wpG_W covers, from a configuration with TW fρ ps (rsOf ls) and Tagged,
               ends at a configuration with TW fρ'p ps' (rsOf ls') and Tagged
  (invariant)  TW W ps rs  ⟹  TI W ps rs
  (stops)      under D-STOP, the stopped configuration is a TW configuration whose ps' records
               exactly the frames handed to the table
  ```
- Uses: O-ARISE, D-ARISE, D-WPG, D-STOP.
- Today: the world clause is a conjunct of `wpG` (`Core/EffDefs.lean:39`) and `wpTS`
  (`Core/World.lean:198`), so every proved `wp` fact carries it. `TW`'s constructors are the
  printed proofs' world operations (`Core/World.lean:97-109`: `alloc` 6.141, `free` 6.142, `store`
  6.145, `immFrame`/`immEnd` 6.64, `mutFold`/`mutUnfold` 6.65/6.66, `reb*` 6.150). The invariant
  clause is `TW.inv` (`Core/Invariant.lean:2702`); its file banner calls it "preservation of the
  invariant by every step" (`Core/Invariant.lean:38`). Status **as built** (world, invariant);
  **changed** (stops).
- Slices: T-ARISE (05) adds `TabAtS` to the invariant at every stack.
- Depends on: T-ARISE.
- Open: OQ-52 (syntactic subject reduction).
- Obligation: **mechanical** for the world and invariant clauses. The stop clause is **unknown**
  with D-STOP (OQ-10). Type soundness here is semantic (T-FP with T-ADEQ). No syntactic
  subject-reduction theorem over `CDerives` exists (no declaration in `Core/`, `Paper/` or
  `Support/` states one), and none is needed for any theorem in this section.

---

## 7. What this section takes from T-FRAME

T-FRAME belongs to 05. This section uses it in four places. Each place names the printed lemma
behind it, so the lift is built once and consumed as printed (CLAUDE.md §1).

| consumer | lifted lemma used | printed |
|---|---|---|
| Rows D, `bor_withbor1`, `bor_sliceBorrowI` | `ewp_W`-6.64 at `TableOK` | `[TR]` 6.64 (`Paper/INDEX.md:87`) |
| Rows D, `bor_withbor2`, `bor_sliceBorrowM` | `ewp_W`-6.65 | `[TR]` 6.65 (`Paper/INDEX.md:88`) |
| Rows D, `bor_withbor3` | `ewp_W`-6.66, then 6.60, then `ewp_W`-6.65, as 6.174's printed proof (`Paper/S6_8_FundamentalProperty/Lemmas.lean:1462-1466`) | `[TR]` 6.174 |
| Rows D (the lender's side), L-HIDE, K-CAP (the `withswap` call, D-COMODEL) | `ewp_W`-6.66 | `[TR]` 6.66 (`Paper/INDEX.md:89`) |
| Rows D, `bor_withload` | `ewp_W`-6.150 | `[TR]` 6.150 (`Paper/INDEX.md:173`) |

The technique is the one the audit keeps. A printed frame lemma over `wpG` that never inspects the
final term (`wpG_I_frameX`, `wpG_M_frameX`, `wpG_M_antiFrameX`; `Core/EffWp.lean:75, 363, 567`) is
lifted to the least fixed point by induction on it (`ewp_ind`, `Core/EffWp.lean:754`). Depth is
handled by one induction, never by per-depth lemmas. At an abortive table the lift is one
unfolding (`ewp_abortive`, `Core/EffWp.lean:811`), which is how the `*U` rows close today. T-T1
and T-T2 are the two ends of the same lift: `σ = []` with an abortive table, and general `σ` with
a `TableOK` table.

---

## 8. Determinism

### T-DET: unique decomposition and determinism, with capture
- Form:
  ```
  (decomposition)  every non-value term is K[a] for exactly one context K and redex a
  (head)           Head μ a μ₁ a₁ ∧ Head μ a μ₂ a₂ ∧ a not an allocation  ⟹  μ₁ = μ₂ ∧ a₁ = a₂
  (capture)        the same at the capture redexes: hnd, ubind, ccatch, cfin
  (allocator)      AStep1 under one allocator is deterministic
  ```
- Uses: K-CTX, K-STEP, K-RUN.
- Today: `head_det` (`Core/Demonic.lean:46`), `head_det_eff` (`Core/Steps.lean:596`, with
  `EffRedex` `:591`), `AHead.deterministic`, `AStep1.deterministic`
  (`Core/Demonic.lean:111, 117`). Status **as built**.
- Slices: 04 owns the machine; this entry only records the theorem.
- Depends on: none in the model.
- Open: none.
- Obligation: **mechanical**. It is a machine fact and reads no world, so the re-index leaves it
  unchanged. The step: any new head step of 04 (for instance a capability's call, OQ-1) must be
  added to `EffRedex` or shown not to overlap.

---

## 9. Renaming, no accidental handling, abstraction safety

### T-REN: renaming of handler names
- Form. For a permutation `π` of `Nm` with `π(⊥) = ⊥`, extended to rows, types, terms, contexts,
  tables and runs (K-REN):
  ```
  (statics)    Δ; Γ ⊢ e : j     ⟹   Δ; πΓ ⊢ πe : πj
  (machine)    Head μ a μ' a'   ⟹   Head μ (πa) μ' (πa')
  (relation)   𝒞⟦πC⟧_{π·W} δ (πe) ⟺ 𝒞⟦C⟧_W δ e,   𝒱⟦πA⟧_{π·W} δ (πv) ⟺ 𝒱⟦A⟧_W δ v,
               opTable (π·⟦Σ⟧δ) = π·opTable ⟦Σ⟧δ
  ```
  where `π·W = (ρ, ls, π·σ)` renames each entry's row `R : Nm → Bool` (D-W) to `R ∘ π⁻¹`, and with
  it every name `TabAt` and the tables read off the entries; `ρ` and `ls` hold no names. The world
  must be renamed with the term: the entries' rows are read by the tables, so the relation half
  does not hold at the same `W`. (K-REN lists `π·W` among the renamed objects.)
  **Corollary (copies).** Two copies of a function body that differ by a renaming of the names
  they tunnel have equal meaning at every `W` (with `W` renamed). This is decision 57's "copies are
  typing artefacts" (`docs/decisions.md:709`), now a theorem, for copies related by a renaming
  only. Copies at structurally different rows (`timeout_Σ` and `timeout_Σ'` for different
  signatures) are not related by T-REN or by any theorem here: under R-NOROWVAR each is a separately
  checked derivation (OQ-13; its option (a') adds a meta-level substitution lemma relating them).
- Uses: K-REN, K-NAME, D-OPTAB, D-REL.
- Today: not built (audit M13, M16). Location renaming exists for runs with no array step
  (`steps_rename`, `experiments/TwoRun/TwoRun/Rename.lean`; README "Step 1"); that is renaming of
  `Loc`, not of `Nm`. Status **new**.
- Slices: K-REN (02).
- Depends on: T-FP's statement (the relation half is by induction on types and on the least fixed
  point, not on derivations).
- Open: OQ-13 (with row variables in the kernel, T-REN becomes substitution), OQ-14 (generative
  instances replace renaming by `ν`), OQ-11.
- Obligation: **mechanical**. Statics: one induction on the derivation; the premise
  `hnS : ∀ o ∈ S, o.n ≠ n` of `[handle]` (`Core/Fundamental.lean:370`) is preserved because `π`
  is injective. Machine: `HasHnd`, `Catches`, `hndNames` commute with `π`
  (`Paper/S3_Dynamics/Definitions.lean:386-420` reads names only by equality). Relation: by
  induction on types, and on the least fixed point at `F_Σ`. The step: names are `UInt32`
  (O-NAME), and a host or allocation step that computes a name would break equivariance. One must
  check that no step does.

### T-NAH: no accidental handling over the kernel
- Form. Let `Δ; Γ ⊢ f : C` contain a handler site of name `n`. Let `g` be a value received by `f`
  through `⊸` or `U` at a computation type whose row is `Σ_g` with `n ∉ Σ_g`, which the
  `[handle]` premise `hnS` guarantees at every site in scope. Then:
  ```
  (unary)   no run of f g handles, at n, an operation g performs
  (via T-REN, T-DET)  for every injective π fixing names(Σ_g), the run of π f g equals the run of f g
            up to a renaming of names and locations
  ```
- Uses: K-HND, K-NAME, K-REN.
- Today: not built over the kernel. The sibling calculus proves `no_accidental_handling`
  (`experiments/EffModelRel/EffModelRel/Laws.lean:362`), and that result does not transport (OQ-5).
  Status **new**.
- Slices: L-NAH (06).
- Depends on: T-REN, T-DET, T-2RUN.
- Open: OQ-14 (re-entry of a site is resolved dynamically; under R-STATIC, recursion through a
  site is excluded), OQ-4 (the equation form).
- Obligation: **mechanical** at R-STATIC through T-REN, T-DET and T-2RUN. The step: the unary
  form is a property of which handler catches an operation, so it needs the provenance of an
  operation along a run. T-REN's route avoids stating provenance. The literature's statement is a
  parametricity theorem (Zhang–Myers POPL 2019 [via #235: venue read, content recalled there];
  Biernacki et al. POPL 2019 [12-sources: content recalled]). Both marks are recall, so they
  motivate this statement and are not cited as its proof.

### T-ABS: abstraction safety
- Form. Two implementations of a handler or capability that are related by a relation preserved
  by its operations are contextually equivalent to every client parametric in the handler's names:
  `≈`-related at every pair of worlds (D-BIN).
- Uses: D-BIN, K-NAME.
- Today: not built. Status **new**, conditional on OQ-4 (a).
- Depends on: T-BINFP, T-REN.
- Open: OQ-4, OQ-14.
- Obligation: **unknown**: binary.

---

## 10. Totality (kept, not a goal)

### T-TOTAL: a closed program with no div observation terminates
- Form:
  ```
  ⊢ e : F A  ⟹  ∀ A k. ∃ k' μ' v. ARun A k μ₀ e k' μ' v,    and    ¬ ∃ f. f 0 = (μ₀, e) ∧ ∀ n. f n ↦ f (n+1)
  ```
- Uses: D-WPG (its run conjunct `∃ k', ARun …` is total correctness, `Core/EffDefs.lean:36`).
- Today: `total_every_alloc`, `total_every_run`, `total_no_infinite_run`
  (`Core/Totality.lean:40, 64, 223`). Status **as built**.
- Slices: K-DIV, K-NU (03); SPEC Entries 13, 19, 20 (`SPEC.md:1190, 2985, 3134`).
- Depends on: T-FP, T-ADEQ.
- Open: OQ-15. Under (a), div is codata and a div computation's type is `U(Loop B R)`. T-TOTAL then
  holds at every `F A` as stated, since a div program is a value whose observations are run one at
  a time. Under (b), div is a row entry with a partial-correctness `ewp`, and T-TOTAL is restricted
  to rows without it.
- Obligation: **mechanical**. Totality is not a design goal (00 §0.2 item 9). The theorem is kept
  because it costs nothing: it is a corollary of the total-correctness `wp`.

---

## 11. Binary results (conditional on OQ-4)

### T-2RUN: binary facts from the unary relation and determinism up to renaming
- Form:
  ```
  (fresh determinism)  FreshRun μ e μ₁ v₁ ∧ FreshRun μ e μ₂ v₂  ⟹  ∃ π : Perm Loc. μ₂ = π·μ₁ ∧ v₂ = π·v₁
  (simulation)         FreshRun μ_B e_B μ_B' e_B' ∧ HeapRel g μ_B μ_A ∧ μ_A, g e_B ↦* μ_A', e_A' (value)
                         ⟹  ∃ g'. e_A' = g' e_B' ∧ HeapRel g' μ_B' μ_A'
  (laws)               a law whose two sides have, from T-FP, unary runs that reach related
                       configurations is a two-run equation, with no binary relation (T-SI2, 06 §1.5)
  ```
- Uses: K-RUN, T-DET.
- Today: `freshRun_det` (`experiments/TwoRun/TwoRun/Fresh.lean:255`), `run_sim`
  (`experiments/TwoRun/TwoRun/Sim.lean:253`), `fresh_run_image` (`…/Sim.lean:274`). They hold for
  runs with no array step (`experiments/TwoRun/README.md`, "Step 1"). `EveryRunFootprint` and
  `ReadFootprint` are refuted at named configurations (`…/Refute.lean`;
  `not_readFootprint`, `…/Read.lean:185`). Status: experiment; **promote** under OQ-4 (b).
- Slices: 06 (which laws follow by this route).
- Depends on: T-DET, T-FP.
- Open: OQ-4, OQ-43 (array steps).
- Obligation: **mechanical** for runs with no array step. **Unknown** with array steps (OQ-43).

### T-BINFP: the binary fundamental property over `≈`
- Form: `Δ; Γ ⊢ e : j ⟹ Δ; Γ ⊨ e ≈ e : j`, D-BIN at every pair of worlds `(W₁, W₂)`.
- Uses: D-BIN.
- Today: not built on Core. The sibling calculus has `fundamental : LR M M`
  (`experiments/EffModelRel/EffModelRel/Fundamental.lean:278`), and it does not transport (OQ-5).
  Status **new**, conditional on OQ-4 (a).
- Depends on: T-COMPAT's binary rows; T-MONO for pairs.
- Open: OQ-4, OQ-31 (no step-indexing: the binary relation, like the unary one, is defined by
  structural and stratum recursion).
- Obligation: **unknown**.

### T-SOUND: `≈` is sound for contextual equivalence
- Form: `Δ; Γ ⊨ e₁ ≈ e₂ : C ⟹ Δ; Γ ⊢ e₁ ≡ e₂ : C`, where `≡` (O-EQ, 06 §1.2) observes the final
  value at a ground type under every allocator. Under OQ-15 (a), the default, termination is not
  observed, since every closed computation at `F_∅ G` terminates (T-TOTAL); under OQ-15 (b)
  divergence is observed, and T-SOUND is restated at that observation.
- Uses: O-EQ, D-BIN.
- Today: not built on Core. The sibling calculus has `soundness`
  (`experiments/EffModelRel/EffModelRel/Adequacy.lean:258`). Status **new**, conditional on OQ-4 (a).
- Depends on: T-BINFP, T-ADEQ.
- Open: OQ-4.
- Obligation: **unknown**. The step: `≡` under every allocator relates runs whose locations
  differ, so soundness needs T-2RUN's renaming, and inherits OQ-43.

---

## 12. Open questions raised by this section

Boxed in [99](99-open-questions.md):

- **OQ-50**, how the linear use of a continuation is observed (T-LIN, T-FIN (1)); default: their
  resource form, marked.
- **OQ-43** (shared with 04 and 06), two-run facts with array steps (T-2RUN, T-SOUND).
- **OQ-51**, adequacy observed at a row (a closed program whose row is not empty).
- **OQ-52**, whether a syntactic subject-reduction theorem is part of the calculus.

Questions from the register this section depends on first: **OQ-58** (whether T-FP's `σ = []`
instance is `fundamentalC`'s statement, §0) and **OQ-15** (the observation T-SOUND is stated at).
Questions from the register this section carries: **OQ-4** (audit Q4) governs T-2RUN, T-BINFP,
T-SOUND, T-ABS, and T-NAH's equation form. **OQ-11** governs whether T-REN and T-NAH are stated at
`W` (here: at `W`, from T-REN's relation half). **OQ-13** decides whether T-REN is renaming or
substitution. **OQ-14** decides whether T-NAH and T-ABS are over static names or instances. **OQ-66** decides
whether T-FIN's cancel case is classified as Ahman & Bauer's signal; no statement here depends on
the answer.
Questions this section depends on and does not carry: OQ-2 (audit Q2), OQ-3 (audit Q3), OQ-7
(audit Q7), OQ-8, OQ-9, OQ-10, OQ-15, OQ-16, OQ-20, OQ-21, OQ-28, OQ-30, OQ-31. Audit Q1, Q5 and Q6
(OQ-1, OQ-5, OQ-6) reach this section only through K-CAP, the sibling-calculus citations, and
nothing, respectively.

---

## 13. Untranscribed, unspent, unused (CLAUDE.md §5)

**Printed lemmas in the run-up that are not transcribed at the tables this section needs:**

- `[TR]` 6.150 at `ewp`. It is proved at `wpTS` (`Paper/INDEX.md:173`, typed world
  `wpTS_reborrow`), and it is not lifted to any effect table (audit m6). Rows D `withload` needs
  it; `withbor3` does not (6.174 uses 6.66, 6.60 and 6.65).
- `[TR]` 6.64 at a resuming table beyond `ewpTS_I_frameR`'s stack shape
  (`experiments/GhostEnd/GhostEnd/ImmLend.lean:175`).
- 6.65's `↭` steps, line by line (audit "Unspent and untranscribed items", O2).
- `[TR]` 6.151 is scored `variant` (`Paper/INDEX.md:174`). T-FP follows its structure, induction on
  the derivation, one compatibility lemma per rule. Where 6.172–6.174 are themselves `variant`
  (`Paper/INDEX.md:195-197`), Rows D inherit the variant.

**Printed hypotheses this section does not spend:**

- 6.150's И freshness. Today's lifts use side conditions in its place (`hσx`, `hσT`, `e.x ∉ σ`;
  audit m5, m6). Under D-ORD those should become instances of T-MONO.
- 6.64's `hQ` (the post-condition stable along `Ext`, `Core/EffWp.lean:77`). At `W` it must be
  stability along `⊑`, which is T-MONO. It is an added hypothesis at today's `wpG_I_frameX`, not a
  printed one.

**Uniqueness and functionality results this section does not use:**

- `head_det` and `head_det_eff` (`Core/Demonic.lean:46`, `Core/Steps.lean:596`) are used by T-DET,
  T-2RUN and T-NAH, not by T-FP or its corollaries.
- `Row.find_of_mem` under `Row.Uniq` (`Core/EffRules.lean:748`) is used today only at `[then]`.
  Once rows are sums (K-ROW), uniqueness of keys holds at every row and the `hUq` premise
  (`Core/Fundamental.lean:361`) becomes vacuous.
- `ResU.Lower.functional` and `ResU.CompS.functional` are used only by T-ADEQ (`reclaim`,
  `Core/Fundamental.lean:568-573`).
- No functionality result for `TW` (two derivations of `TW W ps rs` agreeing) is stated or used.

---

## 14. Sources

Read for this section:

- Code and documents as cited `file:line` throughout. `docs/effects-audit.md`;
  [00-structure.md](00-structure.md); SPEC §13 (`SPEC.md:1119`), §19 *Theorems* (`SPEC.md:2726-2792`);
  `docs/effects-tr/09-factoring.md` §9.3; `docs/effects-tr/12-sources.md`;
  `docs/effects-tr/17-borrow-callbacks.md` §17.2 (branch `borrow-callbacks`);
  `experiments/TwoRun/README.md`; `Paper/INDEX.md`.
- The literature reports on #235, #245, #251 and #279 (`gh issue view N --comments`). From #235:
  Ahman–Bauer ESOP 2020 Thm 7 and Congard–Munch-Maccagnoni–Douence ESOP 2026 Prop. 2, with #235's
  marks; Zhang–Myers POPL 2019, content recalled there. From #251: the capture-rebasing sketch
  (L1–L6), which is OQ-9 option (b). From #245: the review inputs on capture rebasing and
  finalisers.
- Kripke-model literature (ADR'09 Lemma 4.1, Pitts–Stark HOOTS 1998 Lemma 4.3, Timany et al.
  POPL 2018 Lemma 3.2, λRust F-newlft, Thamsborg–Birkedal ICFP 2011 Lemma 6.4): taken from §17.2,
  which marks each as verified against the fetched primary text. Not re-fetched for this section.

No primary source was fetched for this section beyond the passage of Ahman & Bauer that 05 §10
fetched, cited at T-FIN. Every literature claim above is marked with the
report it comes from. Claims that report marks as recalled are used only as motivation.

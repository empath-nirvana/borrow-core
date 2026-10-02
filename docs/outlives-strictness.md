# Strict outlives: where `⊏` costs, and where `⊑` is admissible

Issue #241, a spike. Its recommendation landed as SPEC §23 (#243): K1, E1, B1 and K2 as §6
orders them, with K2 at every rule §2.6 lists. What follows describes the kernel before it. In the
spike the kernel is unchanged: `Core/`, `Paper/`, `Support/`, `Frontend/` and
`Backend/` are as on `main`. The probes are `experiments/Outlives` (`lake build Outlives`) and its
programs (`experiments/Outlives/run.sh`).

BoLo prints `⊏` in every outlives premise: the rules of `Δ ⊢ T ⊐ @a` ([TR] p. 2, rows 2.35–2.37),
the bound of `∀'a ⊏ @b`, the fresh lifetime of `withbor` and `withload`, and the strata of the
model. Where this document finds `⊑` admissible, the relaxation is an **extension** of the
calculus, read against the model the paper defines. It does not correct the paper. SPEC §4
(Entry 3, `experiments/Relaxed`) is the precedent, and its method is reused here: restate the
rule, rebuild the Fundamental Property over the restated rule, and change only the steps that
consumed the strict bound.

**How claims are marked.**

- **[Lean]**: a theorem in `experiments/Outlives`. Every result's axioms are within
  `[propext, Classical.choice, Quot.sound]`, with no `sorry`.
- **[scratch]**: a change to the library, applied in a scratch worktree and built there, not
  committed. The diff is `experiments/Outlives/k1.patch`.
- **[checked]**: a `.bc` program checked and run by the `bcc` of `main`.
- **[inspection]**: read off the rules or the code.
- **[unchecked]**: a sketch; nothing has checked it.

---

## 0. Answers

1. **Where strictness enters.** At eleven places (§1): the model's strata, the box modality,
   the three lifetime rules of the outlives judgment and its pointwise lift to contexts, the side
   condition of `withbor` (Ref → Mut), the fresh lifetime of `withbor` and `withload`, the bound
   of `∀`, the frontend's lifetime parameters, the boxed rest of §22, and the checker's decisions.
2. **Where `⊑` is admissible.**
   - **K1, the box rule of the outlives judgment**: `[@b] T ⊐ @a` from `@a ⊑ @b`. Admissible
     and proved: 6.60 holds (`vC_outlivesL`), `[]I` is sound (`boxIL_compatC`), and the FP and
     adequacy hold for `LDerives` (`fundamentalL`, `adequacyL`). As a library change it touches
     about ten lines, and the library and checker build with it [scratch].
   - **K2, the side condition of `withbor` (Ref → Mut)**, all three rules non-strict. Admissible
     and proved (`withbor2Le_compatX`, in `fundamentalL`).
   - **The lifetime rules for `Imm` and `Mut`, under `[]I`**: obstructed. 6.60 fails at the
     relaxed judgment (`not_vC_outlives_le`): the borrow's own cell is in the relation and not in
     `Res_α` (`borrow_cell`).
   - **The strata, and with them the box modality**: obstructed. A stratum whose `mut` cells may
     sit at its own lifetime contains its own predicates, which Cantor's theorem refuses
     (`no_nonstrict_stratum`). A non-strict reading of `[α]` exists only as a predicate on the
     union of the strata, and at `withbor`'s callback result it admits the borrow itself
     (`borrow_cell`).
   - **The fresh lifetime of `withbor`/`withload`**: not a cost. It sits in the callback's
     argument, so the strict bound is a hypothesis the callback receives.
   - **`∀'a ⊏ @b` as a binder**: open. A non-strict binder is a new binder kind in `LifeCtx`
     and `Models`. It was not probed, and no `aff-*` program needs it once E1 is in place.
   - **The frontend's lifetime parameters, strictly below `top`**: their cost is removed by
     elaboration (E1), with no kernel change.
3. **Lifetime bounds on generic parameters** (§4). Elaboration only. A bound `where S: 'c`
   becomes the bound `'c < ⊓q̄` on the template's own lifetime parameter in each instance, where
   `q̄` are the lifetimes of the type argument `S`. The kernel's `∀'c ⊏ @b` already takes any
   lifetime expression as its bound, and the unchanged checker accepts the elaborated instance
   [checked]. A bound that would let `'c` equal a lifetime of `S` (`'c ⊑ 'q`) needs a non-strict
   binder, which is open.
4. **Ergonomics** (§5). Across the six `aff-*` programs, the scaffolding comes to 10 scopes and
   6 cells, allocated only to name a lifetime, plus 18 `boxed[…]` annotations. With K1, E1 and
   B1, 1 scaffolding scope (`aff-capture`'s), 1 cell and 4 annotations remain. Four of the
   programs need K1 alone to lose a scope each, and they check and run with the corpus answers
   under the K1 patch [scratch].
5. **Recommendation** (§6), in order:
   1. K1 into the kernel.
   2. E1 in the elaborator.
   3. B1 in the elaborator.
   4. K2 into the kernel.

   Leave the strata, the box modality, the borrow rules under `[]I`, and the fresh lifetime as
   printed.

---

## 1. Inventory

Each row gives where strictness enters, what it protects, and the verdict.

| # | Place | File, definition | Strict premise | What it protects | Verdict |
|---|---|---|---|---|---|
| 1 | The model's strata | `Paper/S5_Model/Definitions.lean:154` `MutF.hβ`, `:140` `ImmF.hls`, `:186` `Cell` | a cell of `Cell_α` is at `β ⊐ α` | well-founded recursion: a `mut` cell's predicate ranges over `Res_β`, a stratum strictly above its own | **obstructed** (`no_nonstrict_stratum`) |
| 2 | The box modality `[α]P` | `Paper/S5_Model/Definitions.lean:666–671` (5.32: `Outlives`, `box`); `Core/Relation.lean:131` (`vCE` at `[@a] A`) | `@ρ ⊐ α`, membership in `Res_α` | the scope's end: `withbor`'s callback returns `['x] B`, and `Res_x` excludes the borrow's own cell | **obstructed** as a relaxation (row 1); the non-strict reading admits the borrow (`borrow_cell`) |
| 3 | The outlives judgment, box rule | `Core/Types.lean:1735` `VOutlives.box`; `Paper/S2_Statics/Definitions.lean:392` `OutlivesRules.box` (2.35) | `Δ ⊨ @a ⊏ @b` | nothing beyond `Res_b ⊆ Res_a` | **admissible, proved** (K1) |
| 4 | The outlives judgment, `Imm`/`Mut` rules | `Core/Types.lean:1736–1737`; 2.36–2.37 | `Δ ⊨ @a ⊏ @b` | a borrow at `β` is not in `Res_β` | **obstructed** under `[]I` (`not_vC_outlives_le`); admissible in the side condition (row 6) |
| 5 | Outlives of a context | `Core/Types.lean:1801` `CtxOutlives`; 2.58 `Ctx.Outlives` | rows 3–4, pointwise | `[]I` (`Core/Fundamental.lean:139`) | as rows 3–4: K1 admissible, the borrow rules obstructed |
| 6 | `withbor`'s side condition (Ref → Mut) | `Core/Fundamental.lean:240` `withbor2.hside`; likewise `withbor2U` (`:259`), `sliceBorrowM/I/MU/IU` (`:200`, `:206`, `:276`, `:283`), `Family.borrowsMut`, `BlockBorrow.formerMut` | `∃ @b. Δ ⊨ @b ∧ Δ ⊢ A ⊐ @b` | the payload lies in the stratum of the borrow's lifetime (`MutF`'s `ρ : Res_β`) | **admissible, proved for `withbor2`** (K2); the others take the same proof (not rebuilt) |
| 7 | The fresh lifetime of `withbor`/`withload` | `Core/Types.lean:1828–1846` (`∀'x ⊏ ⊓Δ` in `axWithbor*Ty`, `axWithloadTy`); `Core/FrameRules.lean:346` (`wpTS_M_frameX` picks `A ⊏ β`, below every tag) | `'x ⊏ ⊓Δ` | the borrow ends before every lifetime in scope | **not a cost**: a hypothesis the callback receives (§2.7) |
| 8 | The `∀` binder | `Paper/S2_Statics/Definitions.lean:290` `Models` (2.52); `Core/Fundamental.lean:122`, `:295` (`allE`, `allEV`: `Δ ⊨ @a ⊏ @b`); `Core/Relation.lean:161` (`cC` at `∀`, `LtLife`) | `δ('a) ⊏ δ(@b)` | the body may use `'a ⊏ @b`, e.g. to box an `Imm @b T` at `'a` | **open**: a non-strict binder is a new binder kind; not probed |
| 9 | The frontend's lifetime parameters | `Frontend/Parser.lean:2121` (`<'a>` is `<'a < top>`); `Frontend/Sugar.lean:4207` (an instance's lifetimes, `all 'io_qk < top`); SPEC §15 *Generic functions* | `'a ⊏ ⊤` | as row 8 | **elaboration** (E1, §2.9) |
| 10 | §22's boxed rest | `Core/Aff.lean:32` `affBody`: `νX. (A ⊸ F(B ⊗ [@c] U X)) & F 1` | a use of row 2 | each call's rest outlives `@c` | **no change of its own**; its cost is rows 3, 5 and 9 |
| 11 | The checker | `Frontend/Check/Decide.lean:438–495` (`ltB`, `leB`, `outlivesB` at box/imm/mut); `Frontend/Check/Consts.lean:80` (`outlivesWitness`, row 6's witness); `Frontend/Check/Rules.lean:103` (`rBoxI`), `:134`, `:216` (`rAllEV`, `rAllE`) | `ltB` | as rows 3–8 | **follows the kernel**: K1 is `outlivesB`'s box arm at `leB`; K2 is a non-strict `outlivesB` for `outlivesWitness` |

Two places were already non-strict before this issue. Both came from SPEC §4 (Entry 3):

- `FrameLife`'s view bound;
- the reborrow step's stratum, `StratumLe` (`Core/World.lean:92`).

---

## 2. Verdicts

### 2.1 The strata (row 1): obstructed

`Cell_α` is defined by well-founded recursion on the lifetime. A `mut` cell of `Cell_α` is
`mut(β, v, ρ, P̂)` with `β ⊐ α` and `P̂ : Val → SProp_β`, so its predicate ranges over a stratum
strictly above its own. Suppose `β = α` were allowed. Then `Cell_α` would contain, through `mut`,
every `(v, ρ, P̂)` with `P̂ : Val → Res_α → ℙ`.

**[Lean]** `no_nonstrict_stratum (C) (f : MutSelf C → C) : ¬ Function.Injective f`. No type
carries such a `mut` constructor. A set `S ⊆ C` is coded as the cell `mut((), ∅, P_S)`, where
`P_S w r ≜ w = () ∨ ∃ c. r(0) = c ∧ c ∈ S`. That code is injective, which contradicts Cantor's
theorem (`Function.cantor_injective`).

### 2.2 The box modality (row 2): obstructed as a relaxation

`[α]P` is `P ∧ ρ ∈ Res_α`: membership in a stratum. A non-strict `[α]` would be membership in a
non-strict stratum, which §2.1 refuses. What does exist is the predicate
`OutlivesLe ρ α ≜ ∀α′ ⊏ α. ρ ∈ Res_α′`, on the union of the strata. It is `Core.StratumLe`'s
shape at a resource.

It cannot replace `['x]` where the scope ends. **[Lean]** `borrow_cell ℓ` shows that the value of
`Mut 'x 1` at `δ('x) = α` is a single `mut` cell at `α`, and that this cell:

- is in the relation;
- satisfies `OutlivesLe _ α`;
- is not in `Res_α`.

So a callback whose result were only `OutlivesLe` could hand back the borrow its scope is about
to end. The strict `['x]` is exactly what excludes that cell.

### 2.3 The box rule of the outlives judgment (row 3): admissible (K1)

`[@b] T ⊐ @a` with `Δ ⊨ @a ⊑ @b`. A value of `[@b] T` has its resource in `Res_β`, and
`Res_β ⊆ Res_α` for `α ⊑ β`. The strict premise is not used.

**[Lean]**

- `VOutL` is the judgment with this rule non-strict (`VOutP` with `Rb = ⊑`, `Rr = ⊏`).
- `vC_outlivesL`: 6.60 at `VOutL`. It is `vC_outlives`'s induction; the box case uses
  `InStratum.mono` at `α ⊑ β` where `vC_outlives` uses it at `α ⊏ β`.
- `boxIL_compatC`: `[]I` at `CtxOutL`. It is `boxI_compatX`, with `gSepC_outlivesL` in place of
  `gSepC_outlives`.

K1 is sound only because the box's own meaning stays strict (§2.2). `[@x] T ⊐ 'x` holds because
a `[@x] T` value is already in `Res_x`. `Mut 'x T ⊐ 'x` stays refused (§2.4).

So a callback still cannot return the borrow. `m : Mut 'x A` can be boxed at `'x` neither
directly nor through a thunk capturing it: `[]I` reads the thunk's context, and `m` fails §2.4.
A `[@x] U C` already boxed holds nothing at `x` (§2.2).

### 2.4 The `Imm`/`Mut` rules under `[]I` (rows 4–5): obstructed

**[Lean]**

- `mut_outLe : VOutLe Δ₁ 'x (Mut 'x 1)`: the relaxed judgment holds.
- `not_vC_outlives_le`: 6.60 fails at `VOutLe`. The witness is `borrow_cell` (§2.2).

`boxI_compatX` reads `CtxOutlives` through 6.60 as `ρ ∈ Res_α` for the context's resource. At
`m : Mut 'x 1` boxed at `'x`, that membership is exactly what `borrow_cell` refutes. This is the
case `logState_not_outlives` (`Core/AffPrograms.lean`) refuses syntactically: a closure capturing
`Mut 'x T` is bounded strictly below `'x`.

The refutation is at 6.60, the step of `boxI_compatX` that consumes the premise. A refutation of
`SemV` for the relaxed `[]I` itself would need an inversion of `wpTS` at a value, which the
library does not have. That was not built.

### 2.5 Outlives of a context (row 5)

`CtxOutlives` is the pointwise lift of rows 3–4, and inherits their verdicts: K1 admissible, the
borrow rules obstructed. `CtxOutL` is the lift at K1.

### 2.6 `withbor`'s side condition (row 6): admissible (K2)

The side condition `∃ @b. Δ ⊨ @b ∧ Δ ⊢ A ⊐ @b` (§12.9) reaches the proof through 6.60, as
`𝒱⟦A⟧δ ⊧ [@bδ] 𝒱⟦A⟧δ` ([TR] 6.173). `MutFrame` (`wpTS_M_frameX`) uses that fact only to put the
payload in `Res_A`, where `A` is the borrow's lifetime. `A` is chosen inside the frame rule,
strictly below `@bδ` and below every tag. So the borrow is strictly below `@bδ` whatever the side
condition says. Under the relaxed condition, 6.60 gives every stratum strictly below `@bδ`
(`vC_outlivesLe`). `MutFrame` is then applied at `↓@bδ` and picks `A ⊏ ↓@bδ`.

**[Lean]** `withbor2Le_compatX` is `withbor2_compatX` with the side condition at `VOutLe` (all
three rules non-strict). One step changes: `hβ` is taken at `Life.down β`.

The other consumers of the condition consume it the same way, through `vC_outlives`:

- `withbor2U`;
- `sliceBorrowM`, `sliceBorrowI`, `sliceBorrowMU`, `sliceBorrowIU`;
- the family and block borrows, which build on `withbor2`.

Their relaxed versions were not rebuilt.

K1 already relaxes the side condition at a boxed payload, because the side condition is stated
with `VOutlives`. K2 adds `Imm`/`Mut` payloads. For example, a cell holding `Imm 'x T` can be lent
`mut` inside `'x`'s own scope; without K2 that needs a scope below `'x`.

### 2.7 The fresh lifetime of `withbor`/`withload` (row 7): not a cost

The callback's type is `∀'x ⊏ ⊓Δ. Mut 'x A ⊸ ['x] B`, so the `∀` is in argument position. Its
strict bound is information the callback receives: `'x` is strictly shorter than every lifetime
in scope, which is what lets the callback box an outer `Imm 'a` or `[@a] T` at `'x`. A
non-strict `∀'x ⊑ ⊓Δ` would ask more of every callback (it must also work at `'x = ⊓Δ`) and
would admit no program that is refused now [inspection]. The `['x] B` it returns is row 2.

### 2.8 The `∀` binder (row 8): open

`∀'a ⊏ @b` gives its body `'a ⊏ @b`, and `allE` asks the caller for it. A binder `∀'a ⊑ @b`
would be a second binder kind: `LifeCtx` entries and `Models` (2.52) would carry the kind, and
`EntailsLt`/`EntailsLe` would read it. That is a change to the Paper-level statics, and it was not
probed.

An `allE` at `⊑` for the existing binder is not proposed. A body may use the strict hypothesis,
for example to box an `Imm @b T` at `'a` through 6.60. I have not derived a refutation of such an
instance at `SemC` and have not verified that any obstruction is real. Row 9's cost does not need
the binder (§2.9).

### 2.9 The frontend's lifetime parameters (row 9): elaboration

Every `fn f<'a>` is `all 'a < top`, and so is every lifetime an instance takes from its type
arguments. No function can be called at `top`. Each program therefore opens a scope, borrowing a
cell `d` allocated for the purpose, only to have a lifetime to pass. The kernel itself has no such
need. Core's `retProg` boxes a closure at `⊤` under `Δ = ∅`. **[Lean]** `counterTop` and
`nestTop` run the counter and the nested closure with no scope.

Two elaborations remove the cost, with no kernel change:

- **E1, an implicit lifetime for `main`.** `main`'s body is elaborated inside a borrow of a unit
  cell, `'main`, as the corpus does by hand today. A lifetime argument the call does not
  determine is filled with `dom`, which is `'main` at `main`'s top level. With K1, a closure
  bounded by `dom` is lent `mut` in the same scope, since the side condition is
  `box dom … ⊐ dom /\ top`. The cost is one unit cell per program. A cell-free variant needs a
  rule that opens a lifetime without a borrow; it was not probed.
- **E1′, instances at `top`.** A call that passes `top` uses an instance of the function with the
  parameter substituted, as templates already are for types (SPEC §15). It needs no cell, but it
  instantiates every function the call reaches: `counter`, `twice`, `aff_call_mut`, …
  (`twice<'a, 'c>` at `'c = top` is refused today: "cannot show `top` ⊏ `top`").

The sketches use E1.

### 2.10 §22's boxed rest (row 10)

The rest `[@c] U X` is the box modality (row 2), and it stays. Its cost to programs came from two
places:

- the box rule (row 3): a closure over a closure bounded by `'c` could not itself be bounded by
  `'c`;
- the side condition (row 6): a closure bounded by `'x` could not be lent inside `'x`.

K1 removes both.

### 2.11 The checker (row 11)

The checker certifies a `CDerives` derivation, and its decisions mirror the rules:

- K1 changes `outlivesB`'s box arm from `ltB` to `leB`, and `outlivesB_sound`'s with it.
- K2 is a non-strict `outlivesB` (`leB` at all three arms) used by `outlivesWitness`.

`ltB`/`leB` (`ordB`, the structural rules) are unchanged.

---

## 3. The probe

`experiments/Outlives`, library `Outlives`, imports `Core` and changes nothing in it.

| file | content |
|---|---|
| `Judgment.lean` | `VOutP Rb Rr` (the judgment with the box premise `Rb` and the borrow premise `Rr`); `VOutL` (K1), `VOutLe` (all non-strict), `CtxOutL`; inclusions from `VOutlives`; `rename`/`subst`/`unroll`; 6.60 at each (`vC_outlivesL`, `vC_outlivesLe`) |
| `Compat.lean` | `boxIL_compatC`, `withbor2Le_compatX` |
| `Derives.lean` | `LDerives`, which is `CDerives` rule for rule (copied, renamed) with `boxI` at `CtxOutL` and `withbor2` at the `VOutLe` side condition, plus `core` embedding every `CDerives` derivation; `fundamentalL` (`fundamentalC`'s induction, with the two cases changed and `core` sent to `fundamentalC`); `adequacyL`; `runs_i32L` |
| `Programs.lean` | `counterTop` (Core's `counterProg` without its scope: the closure boxed at `⊤` is lent `mut` under `Δ = ∅` through K1/K2's side condition) and `nestTop` (Core's `nestProg` without its scope: the outer closure boxed at `⊤` over the inner one, by K1's `[]I`); each `_derives`, `_runs` (adequacy at every host) and `_eval` (the interpreter at Wasm's host by `decide`: `4` and `8`, no cell left) |
| `Obstructions.lean` | `borrow_cell`, `mut_outLe`, `not_vC_outlives_le`; `MutSelf`, `no_nonstrict_stratum` |
| `bc/` | the B1 instances, checked and run by `bcc` (§4) |
| `sketches/k1/` | four `aff-*` programs under K1 alone, checked under `k1.patch` [scratch] |
| `sketches/all/` | the six `aff-*` programs and `lib/aff.bc` under K1, E1 and B1 [unchecked] |
| `k1.patch` | K1 as a library diff [scratch] |

**K1 as a library change** [scratch]. `k1.patch` changes the following:

- `VOutlives.box`'s premise to `EntailsLe`;
- `vC_outlives`'s box case (one line);
- `Core/Embedding.lean`'s box case;
- three program sites that wrote `.box (entailsLt_top …)`;
- `Decide.lean`'s box arm and its soundness.

Every other consumer of `VOutlives` goes through `vC_outlives` (`Compatibility`, `EffBorrow`,
`Slices`, `Records`, `FoldImm`) or passes the judgment through unchanged (`rename`, `subst`,
`unroll`, the family and block borrows). Applied to a worktree of `main`, `lake build Core
Frontend bcc` succeeds. The four `sketches/k1/` programs check and run with their corpus answers,
and `bcc` of `main` refuses all four at the box rule. Under the patch the six corpus
`aff-*` programs still check, and `corpus/reject/aff-outlives.bc` (a closure capturing
`mut 'x i32` bounded by `'x`) is still refused, as §2.4 requires. Paper's `OutlivesRules` is untouched: the
embedding of `Derives` into `CDerives` maps its strict premise to the non-strict one.

---

## 4. Lifetime bounds on generic parameters

**The cost.** `fn aff_new[S, A, B]<'c>` cannot box its closure. At an instance with `S` mentioning
`'x`, SPEC §15 makes `'x` a parameter `all 'io_q0 < top.` of the instance, outside and unrelated to
the template's own `all 'c < top.`. So `S ⊐ 'c` cannot be shown, and every caller writes
`boxed['c] aff_new(…)`, with `boxed['c]` again on the state each call returns.

**The design (B1).** `fn f[S, …]<'c>(…) where S: 'c`. At an instance whose `S` has lifetimes
`q̄`, the template's `all 'c < top.` becomes `all 'c < 'q₁ /\ … /\ 'qₙ /\ top.` (`top` when `S` has
none). The kernel's `∀'c ⊏ @b` takes any lifetime expression as `@b`, so this is a different
bound at an existing binder. The instance is still checked by the unchanged checker, so `S ⊐ 'c`
is checked there, at the instance's types, as everything else in a template is. A caller
instantiates `'q̄` with its own lifetimes and `'c` with one below their meet, which `allE` asks
in the caller's `Δ`.

So B1 needs no judgment change and no new rule: elaboration only, in
`Frontend/Sugar.lean:4207`, where the instance's binders are made, plus the `where` syntax.

**Checked.** `experiments/Outlives/bc/capture-bounded.bc` writes out the instance B1 would make
of

    fn aff_new_boxed[S, A, B]<'c>(s: S, step: !U (S -o (A -o F (B * S)) & F 1)) -> box 'c Aff[A, B]<'c>
        where S: 'c

at `S = mut 'q i32`, as `fn aff_new_boxed__mut<'q, 'c < 'q>`. `logger` calls it with no
`boxed`. The program checks and runs to `aff-capture`'s answer (`i32[120512]`, `live 0`).
`bc/counter-bounded.bc` does the same at `S = ref i32` (`<'c>`: no lifetime in `S`, so the bound
is `top` and today's elaboration already is the bounded one), and runs to `aff-counter`'s answer.

**Where B1 stops.** B1's bound is strict: `'c < 'q`. A closure whose state is another closure
bounded by `'c` (`nest`, `doubler`) wants its own bound to be `'c` as well. K1 admits that when
the closure is made where `'c` is known (`sketches/k1/aff-drop.bc`, `aff-higher.bc`). Through the
generic `aff_new_boxed`, however, it would need the instance's bound to be `'c ⊑ 'q`, which is a
non-strict binder (§2.8, open). The alternative is an instance specialised at equal lifetimes, an
elaboration that was not designed further. The sketches keep `aff_new` and `boxed['c]` there.

---

## 5. Ergonomics

Scaffolding counts only the scopes a program opens to name a lifetime, and the cells it allocates
for them. It excludes the borrows a program is about (`aff-counter`'s `'w`, `aff-depth`'s `'w`
and `'v`, `aff-capture`'s `'x`). `boxed[…]` counts annotations in code, not comments.

| program | scaffolding scopes now | after K1 | after K1 + E1 | cells for scopes now → after | `boxed[…]` now | after B1 |
|---|---|---|---|---|---|---|
| `aff-counter` | 2 (`'x`, `'y`) | 1 | 0 | 1 → 0 | 2 | 0 |
| `aff-depth` | 2 (`'x`, `'y`) | 1 | 0 | 1 → 0 | 2 | 0 |
| `aff-capture` | 1 (`'w`) | 1 | 1 | 1 → 1 | 2 | 0 |
| `aff-coerce` | 1 (`'x`) | 1 | 0 | 1 → 0 | 2 | 0 |
| `aff-drop` | 2 (`'x`, `'y`) | 1 | 0 | 1 → 0 | 4 | 2 |
| `aff-higher` | 2 (`'x`, `'y`) | 1 | 0 | 1 → 0 | 6 | 2 |
| **total** | **10** | **6** | **1** | **6 → 1** | **18** | **4** |

Two more counts:

- The `'y` scopes K1 removes are reborrows of the scope cell's borrow, so they allocate nothing.
- In `lib/aff.bc`, `aff_of_fn`'s 2 `boxed[…]` go to 0 under B1, and `aff_new_boxed` holds the 2
  that every closure definition no longer writes.

Function signatures shrink as well:

- `nest<'c, 'd < 'c>` and `doubler<'c, 'd < 'c>` become `<'c>` (K1);
- `runner<'c, 'd>` becomes `<'c>`;
- `logger<'x, 'w < 'x>` is unchanged: its `'w < 'x` is row 4, which stays.

`aff-capture`'s remaining scope is a closure capturing `mut 'x i32`. It is bounded strictly below
`'x` (§2.4), so some lifetime below `'x` must be in scope. An elaboration could open it
implicitly when a lifetime argument must lie strictly below every lifetime available; that is not
designed here.

Sources:

- `sketches/k1/` holds the four K1-only rewrites [scratch: checked under `k1.patch`].
- `sketches/all/` holds all six under K1, E1 and B1 [unchecked].
- `bc/` holds B1's instances [checked].

---

## 6. Recommendation

In priority order:

1. **K1: the box rule of the outlives judgment non-strict.** `VOutlives.box` from
   `Δ ⊨ @a ⊑ @b`. This is a kernel change, and the smallest one considered. It is sound by
   `vC_outlivesL`, its FP and adequacy hold in the probe (`fundamentalL`, `adequacyL`), and the
   library builds with it [scratch]. It removes the four `'y` scopes, the second lifetime of
   `nest`/`doubler`, and §22's "a closure bounded by `'x` is lent inside a scope below `'x`". It
   needs a SPEC entry, which would rest on the following:
   - Baseline: `fundamentalC`, `adequacyC` and the totality theorems keep their statements.
   - Proof changes: `vC_outlives`'s box case changes, and `Core/Embedding.lean` maps 2.35's
     strict premise to the non-strict one.
   - Paper: `Paper/` is unchanged.
2. **E1: an implicit lifetime for `main`, and `dom` for an undetermined lifetime argument.**
   Elaboration only; checked by the unchanged checker. It removes the five `'x` scopes and their
   cells. Take E1′ (instances at `top`) instead if one cell per program matters more than one
   instance per function reached at `top`.
3. **B1: `where S: 'c` bounds on generic functions.** Elaboration only, at the point where an
   instance's lifetime binders are made; the elaborated instance checks today. It removes 14 of 18
   `boxed[…]` from the programs and both from `aff_of_fn`, and lets `aff_new` box its closure.
4. **K2: `withbor`'s side condition non-strict at all three rules.** This is a kernel change,
   proved for `withbor2` (`withbor2Le_compatX`). It is not needed by the `aff-*` programs: K1
   covers their boxed payloads. It removes a scope wherever a cell holding a borrow at `'x` is lent
   `mut` inside `'x`. `withbor2U`, the slice borrows and the family borrows should take it
   together, by the same one-step change.

**Do not relax:**

- the strata or the box modality (§2.1–2.2);
- the `Imm`/`Mut` rules of the outlives judgment where `[]I` reads them (§2.4);
- the fresh lifetime of `withbor`/`withload` (§2.7).

**Open:**

- a non-strict `∀` binder (§2.8, and B1's limit in §4);
- a rule that opens a lifetime without a borrow (the cell of E1, and `aff-capture`'s scope);
- the relaxed `withbor2U`/slice/family side conditions, not rebuilt (§2.6);
- a `SemV`-level refutation of `[]I` at the relaxed borrow rules, which needs a `wpTS` inversion
  at values (§2.4).

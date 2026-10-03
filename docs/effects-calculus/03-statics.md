# 03 · Kernel syntax and statics

This section gives every kernel construct of the effect calculus with its typing rule over
`CDerives` (O-JDG). It owns K-FTY, K-OP, K-RAISE, K-LET, K-THEN, K-HND, K-KONT, K-CAP, K-SWAP,
K-BOR, K-FIX, K-NU, K-DIV, K-HOST, K-GRADE and K-GEN (00 §8), and writes in §9 the
full constructs behind every restriction that narrows a construct of this section or of 02:
K-SCOPE, K-HDIV, K-CARRIER, K-BORANS, K-ALLOC, K-ROWABS, K-SHALLOW, K-FINR, K-OWNERR, K-RELQ,
K-SWAPΣ, K-SELFROW, K-FOLDΣ, K-GENNAME and K-NEGREC. It carries OQ-3, OQ-7, OQ-12, OQ-13, OQ-14,
OQ-15, OQ-16, OQ-17, OQ-20, OQ-24, OQ-25, OQ-26, OQ-28, OQ-29, OQ-30, OQ-31, OQ-35, OQ-37, OQ-61,
OQ-62, OQ-67 and OQ-68, and raises OQ-40, OQ-56 and OQ-59 (§10); every question is boxed in
[99](99-open-questions.md).

Each rule is written once, in full, as the construct of the calculus. Where a named restriction
(00 §7.2) applies by default, the rule is given without it and the restriction is
named beside it. Each rule is marked:

- **as built**: the rule exists in `Core/` with this content, cited `file:line`;
- **changed**: the rule exists, and this specification changes its premises or its form;
- **new**: the rule does not exist in `Core/`.

A **changed** or **new** rule is a change to `CDerives`, our kernel definition, and needs a SPEC
entry before kernel work (00 §0.1). No printed BoLo rule is edited: every printed rule
of `[TR]` p. 2 and every axiom of `[TR]` p. 3 keeps its statement.

---

## 1. Judgement forms and the syntax they range over

### 1.1 Judgements

```
Δ; Γ ⊢ V : A        value judgement        CDerives Δ Γ V (.val A)
Δ; Γ ⊢ M : C        computation judgement  CDerives Δ Γ M (.comp C)
```

`CDerives` is the inductive at `Core/Fundamental.lean:60`, its judgement forms `Jdg.val` and
`Jdg.comp` at `Core/Fundamental.lean:54-56` [Lean]. Terms are BoLo expressions in A-normal form;
the effect constructs are applications of primitives, and there is no new `Expr` constructor
(`Prim.perform`, `.raise`, `.hnd`, `.ubind`, `.ccatch`, `.cfin`, `Paper/S1_Syntax/Definitions.lean:72-86`
[Lean]).

- `Δ : LifeCtx` binds lifetime variables with their bounds (O-LIFE). `Δ.extend x b` adds
  `'x ⊏ @b`; `⊓Δ` (`Δ.meetOfDom`) is the meet of `Δ`'s domain, below which a fresh lifetime is
  placed.
- `Γ : Ctx VTy` is a list of slots `⟨A, live⟩`. Its premises are BoLo's linear ones with
  persistent slots free to duplicate and drop (SPEC §10):
  - `Γ = Γ₁ ∘ Γ₂` is `Ctx.SplitP Γ Γ₁ Γ₂` (`Core/Persistent.lean:112`);
  - `dead Γ` is `Ctx.DeadP Γ` (`Core/Persistent.lean:125`): no live slot but persistent ones;
  - `Γ ∋! i : A` is `Ctx.SoloP Γ i A` (`Core/Persistent.lean:132`): `i` is the one live
    non-persistent slot, at `A`.
- A row `Σ` is a meta-index of the judgement, never a type variable (O-JDG; OQ-13, R-NOROWVAR by
  default). Rows, their sum `⊕`, inclusion `⊑`, `Σ^abort` and the interpretation `⟦Σ⟧δ` are
  02's (K-ROW, K-INT). A signature `E = {op_i : A_i ↠^{q_i} B_i}` is 02's (K-SIG); `op_i` is
  **abortive** iff `B_i = 0 ∧ q_i ≠ lin` (O-SIG; `OpSig.abort`, `Core/EffRules.lean:40` [Lean]).

### 1.2 Types

O-TY fixes the formers. In the kernel today (`Core/Types.lean:45-93` [Lean]):

```
A, B ::= 1 | A ⊗ B | 0 | A ⊕ B | U C | Ref A | Imm @a A | Mut @a A | [@a] A | !A | Unk
       | X | μX. A | I32 | I64 | [L] | opq k
C, D ::= F A | A ⊸ C | C & D | ⊤ | ∀'x ⊏ @b. C | νX. C | F_Σ A
F_Σ A ≜ CTy.effOf Σ A        F_∅ A = F A
```

`F_Σ A` is a stack of `CTy.eff n i q A_i B_i` layers over `F A` (`CTy.effOf`,
`Core/Types.lean:155-157` [Lean]); it is the only effect-specific former. Every other effectful
type is an existing former applied at an `F_Σ` leaf: effectful functions `A ⊸ F_Σ B`, blocks
`!U(A ⊸ F_Σ B)`, effectful records `&ⱼ(Aⱼ ⊸ F_Σ Bⱼ)`, lifetime-polymorphic effectful code
`∀'x ⊏ @b. A ⊸ F_Σ B`, effectful codata `νX. … F_Σ … `.

### 1.3 Auxiliary predicates used in the rules

These are syntactic predicates over types, rows and contexts, local to the statics. None is a
semantic object; each is cited where it exists today.

| predicate | meaning | today |
|---|---|---|
| `Drop A` | `A`'s values hold no owned cell: `1, 0, I32, I64, Unk, opq, !A, Imm, Mut`, closed under `⊗`, `⊕` | `VTy.Drop`, `Core/EffRules.lean:815` |
| `Γ drops` | every live slot of `Γ` has a `Drop` type | `Ctx.Drops`, `Core/EffRules.lean:858` |
| `Pers Γ` | every live slot of `Γ` is at `!A` | `Persistent`, `Core/Relation.lean:235` |
| `Σ.NZ` | no name of `Σ` is the reserved `⊥ = 0` | `Row.NZ`, `Core/EffRules.lean:702` |
| `Σ.Weak` | some operation of `Σ` has weakening (`q ≠ lin`) | `Row.Weak`, `Core/EffRules.lean:705` |
| `Σ.Unr` | some operation of `Σ` is at `unr` | `Row.Unr`, `Core/EffRules.lean:708` |
| `g(Σ)` | the grade of a row (02 §3, O-QUAL): the join, in the containment order, of its operations' qualifiers (`lin ⊔ aff = aff`, `· ⊔ unr = unr`, `g(∅) = [1,1]`) | new (K-GRADE) |
| `Closed E` | every `A_i`, `B_i` of `E` has no free lifetime variable and no free type variable | not a predicate today; a premise only under OQ-35 (a) |
| `Data_x Σ` | every operation of `Σ` has a nonzero name and an argument type free of `'x` and outliving every lifetime | the non-abortive conjuncts of `Row.Unwind`, `Core/EffBorrow.lean:133`; the content of R-CLOSEDOP (OQ-56), not part of the full class |
| `BorOK_x Σ` | the row class a borrow callback may perform (K-BOR): `Σ.NZ` in full; `Closed ∧ Data_x` under R-CLOSEDOP; every operation abortive under R-T1 | `Row.Unwind x` today, which is the full class with both restrictions; OQ-40 |
| `Δ ⊢ A ⊐ @a`, `Δ ⊢ A ⊒ @a` | outlives, strict and non-strict at the leaf rules (SPEC §23) | `VOutlives`, `VOutlivesLe`, `Core/Types.lean:1755, 1761` |
| `Δ ⊨ Γ ⊐ @a` | `@a` defined under `Δ`, and every live slot of `Γ` outlives it | `CtxOutlives`, `Core/Types.lean:1858` |

The kernel's `[let]` reads `Σ.Weak` and `Σ.Unr` (`Core/Fundamental.lean:353-358`); K-GRADE
replaces both by the one grade `g(Σ)`.

### 1.4 Run-time forms have no typing rule

`κ`, `ccatch`, `cfin` and the cancel state `(N, err)` are built by the machine (`kappa`,
`Paper/S3_Dynamics/Definitions.lean:438` [Lean]) and never written by a program. They have no
`CDerives` rule. They are typed semantically: `κ` by `KapRel` (`Core/EffRules.lean:569`) and
`vC_kTy_of_kapRel` (`Core/EffRules.lean:1053`), the cancel run by `cancelOwed`
(`Core/EffDefs.lean:138`) [Lean]. Soundness is by the fundamental property over the relation
(T-FP), not by subject reduction, and this specification keeps that route. 05 owns their
relations (D-KAP, D-OWED).

---

## 2. The rules every former keeps at `F_Σ`

Every rule of the baseline that is stated at an arbitrary computation type `C` holds at
`C = F_Σ A` with no change, because `CDerives` quantifies over `C`. The table lists every former of
SPEC §§2-17 and 22-23 and its rules, and says which hold at `F_Σ` unchanged and which change.

| former (SPEC) | rules (`Core/Fundamental.lean`) | at `F_Σ` |
|---|---|---|
| `1`, `⊗`, `⊕`, `0` (§3) | `unitI` :62, `tensorI` :63, `sumI₁/₂` :66-69; `unitE` :100, `tensorE` :103, `sumE` :107, `zeroE` :113 at any `C` | unchanged: an eliminator's body may be at `F_Σ A` |
| `A ⊸ C` (§3) | `lam` :85, `app` :87 at any `C` | unchanged: `A ⊸ F_Σ B` is an effectful function |
| `C & D`, `⊤` (§3) | `withI` :91, `proj₁/₂` :94-97, `topI` :99 at any `C`, `D` | unchanged: `κ`'s type (K-KONT) and effectful records use them |
| `∀'x ⊏ @b. C` (§3) | `allI` :116, `allE` :122 at any `C` | unchanged: a borrow callback is `∀'x ⊏ ⊓Δ. L ⊸ F_Σ(['x] B)` |
| `U C`, force (§3) | `thunkV` :74 at `C` not `F`-headed; `force` :83 at any `C` (`forceE` applies to `()` at `F A` and `F_Σ A`, `Core/Relation.lean:64-67`) | unchanged for `U(A ⊸ F_Σ B)`, `U(C & D)`, `U(∀ …)` |
| `U (F A)` (§3) | `thunkF` :71, at `F A` only | **changed**: K-FTY adds `[thunkΣ]` (below) |
| `F A`, `to` (§3) | `ret` :77; `bind` :79 with `M : F A` | unchanged; the effectful sequencing is K-LET, of which `bind` is the `Σ = ∅` case |
| `!A` (§2) | `bangThunkF` :125 (at `F A`), `bangThunkV` :129, `bangE` :133, `copyBang` :134, `forgetBang` :136 | `bangThunkV` unchanged; `bangThunkF` **changed** with `[thunkΣ]` |
| `[@a] A` (§2, §23) | `boxI` :139, `boxE` :141 | unchanged; `[@c] U C` is the bound of a stored continuation (OQ-28) |
| `Ref`, `Imm`, `Mut`, `Unk`, the axioms (§3) | `immSub` :142, `mutSub` :144, `alloc` … `forgetUnk` :147-155 | unchanged |
| the borrows (§3, §9, §23) | `withbor1/2/3` :239-250, `withload` :251, `sliceBorrowM/I` :201-212 | unchanged as the `Σ = ∅` instance of K-BOR |
| `withswap` (§3) | `withswap` :254 | unchanged (K-SWAP; OQ-20) |
| `μX. A`, folds (§6) | `roll` :306, `unroll` :309, `foldImm` :316, `foldOwn` :322, `foldReuse` :327 | `roll`, `unroll` unchanged. The folds' algebras are typed at `F R` (`Core/Fundamental.lean:311-327`): an effectful algebra is a change to these rules, K-FOLDΣ (§9.13), not adopted; default R-PUREFOLD (OQ-62) |
| `νX. C` (§7, §22) | `nuIn` :331, `nuOut` :333, `unfoldN` :337, under `NuOk` | unchanged: `NuOk` admits `F_Σ` leaves (K-NU) |
| integers, host ops (§8) | `lit` :157, `hostOp` :160 | unchanged; host operations are pure constants today (K-HOST) |
| arrays, slices (§9) | `arrNew` … `sliceSwapM` :163-238 | unchanged |
| counted loops (§16) | `countFold` :187, `countTry` :191 | steps typed pure (`Core/Fundamental.lean:183-191`): an effectful step is K-FOLDΣ (§9.13), not adopted; default R-PUREFOLD (OQ-62) |
| `bounded_fix` (§20) | `boundedFix` :196 at every `C` | unchanged (K-FIX) |
| CBV forms (§3) | `lolliE` :296, `allEV` :300, `ofRet` :303 | unchanged at value types; `ofRet` reads `F A` only, and an effectful computation is never a value-judged expression |

Row weakening `[sub]` is K-ROW's (02). It is written here because every rule below uses it:

```
Δ; Γ ⊢ M : F_Σ A      Σ ⊑ Σ'
──────────────────────────────  [sub]
Δ; Γ ⊢ M : F_Σ' A
```

As built: `effSub`, `Core/Fundamental.lean:340`, with `⊑` read as `RowLe`
(`Core/EffRules.lean:699`) [Lean]. It is subsumption at an `F_Σ` judgement only. At `U(A ⊸ F_Σ B)`
and the other formers, row weakening is the η-expanded coercion `λx. [sub](f x)`, derived, not a
subtyping rule.

---

## 3. Operations

### K-FTY: the effectful returner and every former at a row

- **Form.**

  ```
  C ::= … | F_Σ A                 (Σ a row of K-ROW; F A = F_∅ A)

  Δ; ⟨1, dead⟩ :: Γ ⊢ M : F_Σ A
  ────────────────────────────────  [thunkΣ]
  Δ; Γ ⊢ thunk M : U(F_Σ A)

  Pers Γ      Δ; ⟨1, dead⟩ :: Γ ⊢ M : F_Σ A
  ──────────────────────────────────────────  [bangThunkΣ]
  Δ; Γ ⊢ thunk M : !U(F_Σ A)
  ```

  Every former of O-TY takes an `F_Σ` leaf: `U(F_Σ A)`, `A ⊸ F_Σ B`, `C & D` with effectful
  components, `∀'x ⊏ @b. C` with an effectful body, `νX. C` with effectful observations (K-NU),
  and the effectful affine closure (K-NU). `U(F_Σ A)` is a value type: it is stored in a `Ref`,
  passed, returned and put in data like any `U C`. It is not persistent, and it outlives no
  lifetime (below).
- **Outlives at `U(F_Σ A)`.** `VOutlivesR` has no rule at `U C` for any `C`
  (`Core/Types.lean:1730-1752` [Lean]), so `Δ ⊢ U(F_Σ A) ⊐ @a` never holds; a thunk outlives
  `@a` only through a box, `[@c] U(F_Σ A) ⊐ @a` from `Δ ⊨ @a ⊑ @c` (SPEC §23). This is the
  bound of every stored effectful computation and of every stored continuation (K-KONT; OQ-28).
- **Uses.** O-TY, O-ROW, O-JDG.
- **Today.** `CTy.eff` and `CTy.effOf`, `Core/Types.lean:92, 155` [Lean]; as built. `thunkF` is
  stated at `F A` only (`Core/Fundamental.lean:71`), and `thunkV` excludes every `F`-headed type
  (`hC : C.isRet = false`, `:74`), where `CTy.isRet` is true at `CTy.eff`
  (`Core/Compat.lean:95-97`) [Lean]. So `CDerives` has no introduction rule for `U(F_Σ A)` at a
  nonempty row; today a suspended effectful computation is written `U(1 ⊸ F_Σ A)`. `[thunkΣ]`
  and `[bangThunkΣ]` are **changed** (the existing `thunkF` and `bangThunkF` at every row).
- **Slices.** Step 04 (none: `thunk M` is a value); clause 05 (`𝒱⟦U C⟧` reads `forceE`, which
  already applies `()` at `F_Σ`, `Core/Relation.lean:66`); compatibility 07; lowering 08.
- **Depends on.** K-ROW, K-INT.
- **Open.** OQ-28 (the bound of a stored thunk); OQ-13 (rows as meta-index).
- **Obligation.** `thunkΣ_compatC`, `bangThunkΣ_compatC`: **mechanical**. The step most likely
  to be non-mechanical: `thunkF_compatC` (`Core/Compat.lean:105`) unfolds `wpTS` at the forced
  body; at a row the forced body is read by `ewpTS`, so the proof goes through `cC_effOf`
  (`Core/EffRules.lean:73`) instead of `wpTS` directly.

### K-OP: performing a non-abortive operation

- **Form.**

  ```
  n : E ∈ Σ      op_i : A_i ↠^q B_i ∈ E      op_i not abortive      Δ; Γ ⊢ V : A_i
  ────────────────────────────────────────────────────────────────────────────  [perform]
  Δ; Γ ⊢ perform_{n,i} V : F_Σ B_i
  ```

  `perform_{n,i} V ≜ perform (n, (i, V))` (`performE (opArgE n i V)`,
  `Core/EffRules.lean:696` [Lean]).

  The **generic effect** of `op_i` is derived, by `[perform]`, `lam`, `thunkV` and `bangThunkV`
  at a dead context:

  ```
  dead Γ
  ──────────────────────────────────────────  [genEff]  (derived)
  Δ; Γ ⊢ gen_{n,i} ≜ λx. perform_{n,i} x : !U(A_i ⊸ F_Σ B_i)
  ```

  So an operation is a first-class persistent effectful function, and L-GEN (06) relates
  `op(v; y.M)` and `gen_op(v) to y. M`. A **generator** is a computation at a row holding an
  iteration effect (`Yield[T] = {yield : T ↠^aff 1}`, SPEC §15); it needs no rule of its own:
  `yield` is `[perform]`, a `for` over it is a K-HND site, and a stored generator is a K-NU
  value.
- **Uses.** O-SIG, O-ROW, O-NAME, O-QUAL.
- **Today.** `effPerform`, `Core/Fundamental.lean:343-346` [Lean]; as built. Its premise is
  `Row.find S o.n o.i = some o`, first match (`Core/EffRules.lean:36`); with K-ROW's sum of
  distinct names it is membership. **changed** only through K-ROW.
- **Slices.** Step 04 (`[op]`, `[unwind]` never: a non-abortive operation is captured); clause
  05 (`opTable`'s first disjunct, `Core/EffDefs.lean:157`); laws 06 (L-ALG, L-HOP, L-HFWD,
  L-GEN); compatibility 07 (`perform_compatC`, `Core/EffRules.lean:781`); lowering 08.
- **Depends on.** K-SIG, K-ROW, K-INT.
- **Open.** OQ-12 (an operation whose parameter is a computation; R-FO); OQ-29 (an answer type
  that is a borrow into handler state; R-NOBORANS); OQ-35 (closed operation types); OQ-2 and
  R-T1 (a non-abortive operation inside a borrow callback, K-BOR).
- **Obligation.** Compatibility at `W`: **mechanical** from `ewp_perform_here`
  (`Core/EffRules.lean:100`) once D-EWP is re-indexed; the step most likely to be
  non-mechanical is the continuation's share at `W` when `σ ≠ []` (D-SHARE, OQ-8).
- **Remark.** The signature form admits `op : A ↠^lin 0`, which is not abortive. Its clause holds
  a linear `κ : U((0 ⊸ F_Σ R) & ⊤)` it can neither resume nor cancel, so a handler of it exists
  only if the clause's context holds a `0`. Whether K-SIG excludes the form is 02's.

### K-RAISE: raising an abortive operation (errors, #168)

- **Form.**

  ```
  n : E ∈ Σ      op_i : A_i ↠^q 0 ∈ E      q ∈ {aff, unr}      Drop A_i      Δ; Γ ⊢ V : A_i
  ──────────────────────────────────────────────────────────────────────────────────  [raise]
  Δ; Γ ⊢ raise_{n,i} V : F_Σ B            (any B)
  ```

  An error is an abortive operation of an ordinary effect, `Fail[E] = {raise : E ↠^aff 0}`,
  handled by ordinary handlers (SPEC §18 *Declarations*); there is no sum for failure and no
  special case. `Exhausted = {exhausted : 1 ↠^aff 0}` (SPEC §20) is another instance. The
  machine exercises weakening eagerly: `κ` is never reified, the finalisers between the raise and
  its handler run innermost first (K-THEN), and the clause receives only the argument (K-HND).
- **Uses.** O-SIG, O-ROW, O-QUAL.
- **Today.** `effRaise`, `Core/Fundamental.lean:348-351` [Lean]; as built. The premise `Drop A_i`
  is `hd : o.A.Drop`.
- **Slices.** Step 04 (`[unwind]`, `[finalise]`); clause 05 (`opTable`'s second disjunct, its
  argument `NoOwn`, `Core/EffDefs.lean:174-178`); laws 06 (L-ALG0, L-EXC); compatibility 07
  (`raise_compatC`, `Core/EffRules.lean:797`).
- **Depends on.** K-SIG, K-ROW.
- **Open.** OQ-24: `Drop A_i` is R-NOOWNERR, the default. Under OQ-24 (b) the premise is dropped
  and the payload is delivered to the handler after the unwound region's finalisers run (K-OWNERR,
  §9.9).
- **Obligation.** At `W`: **mechanical** from `ewp_raise_here` (`Core/EffRules.lean:115`). Under
  OQ-24 (b), **unknown**: the abandoned continuation and the delivered payload share no resource,
  which `[finalise]`'s frame must establish.

### K-GRADE: the qualifier as a grade on the captured context

- **Form.** The grade of a row is `g(Σ) = ⊔_{op ∈ Σ} q_op` in O-QUAL's containment order on
  intervals of use counts (`lin = [1,1]`, `aff = [0,1]`, `unr = [0,∞]`; `experiments/Grades/
  Grades/Algebra.lean:58` [Lean]). When `M : F_Σ A` stops at an operation, the context `Γ₂` of
  its continuation `x. N` is used by the continuation, and the continuation is used `q_op` times.
  The statics therefore asks `Γ₂` to admit the grade `g(Σ) · 1 = g(Σ)`:

  ```
  Γ₂ admits g   ≜   (lo g = 0 ⇒ Γ₂ drops)  ∧  (hi g = ∞ ⇒ Pers Γ₂)
  ```

  `lo g = 0` is weakening of the continuation (a cancel or an unwind abandons `Γ₂`); `hi g = ∞` is
  contraction (a multi-shot resume copies it). At `lo g = 0`, `Γ₂ drops` may be replaced by a
  destructor for `Γ₂`, which is K-THEN.
- **Uses.** O-QUAL, O-ROW.
- **Today.** Implicit: `[let]`'s premises `hW : S.Weak → Γ₂.Drops` and `hU : S.Unr → Persistent
  Γ₂` (`Core/Fundamental.lean:355`) are `lo g(Σ) = 0 ⇒ …` and `hi g(Σ) = ∞ ⇒ …`, since
  `Σ.Weak ⟺ lo g(Σ) = 0` and `Σ.Unr ⟺ hi g(Σ) = ∞`. `experiments/Grades` grades `CDerives`'s
  context premises (`GDerives`, `experiments/Grades/Grades/Judgment.lean:40`) and proves it
  equivalent to `CDerives` (`cderives_iff_graded`), but it has no rule of the effect layer: no
  grade on a row and no graded `[let]` (no `effLet` in `GDerives`). **changed** (presentation:
  one grade in place of two flags; the content is the as-built premises).
- **Slices.** K-LET (its side condition), K-KONT (the grade of `κ`), laws 06 (L-ALG's scaling of
  `Γ_K` by `q`, L-C, L-P).
- **Depends on.** K-SIG (qualifiers), K-ROW.
- **Open.** OQ-16 (whether `unr` stays: if dropped, `hi g(Σ) = ∞` never holds); OQ-17 (`rel =
  [1,∞]`, which would need contraction without weakening, unavailable from `!`); OQ-32 (the TR's
  scaled capture against this graded premise).
- **Obligation.** `effLet`'s premises are equivalent to `Γ₂ admits g(Σ)`: **mechanical**, by
  cases on the row. The step most likely to be non-mechanical: if a graded context
  (`GCtx`) replaces `Ctx` in the effect rules, `Grades`' `Profile.core` translation
  (`GDerives.toCore`, `CDerives.toGraded`) must be extended through `effLet`, `effThen` and
  `effHandle`, whose premises it does not cover today.

### K-LET: sequencing at a row

- **Form.**

  ```
  Γ = Γ₁ ∘ Γ₂      Δ; Γ₁ ⊢ M : F_Σ A      Δ; ⟨A, live⟩ :: Γ₂ ⊢ N : F_Σ B      Γ₂ admits g(Σ)
  ─────────────────────────────────────────────────────────────────────────────────  [let]
  Δ; Γ ⊢ M to x. N : F_Σ B                 (written (λx. N) M)
  ```

  At `Σ = ∅`, `g(∅) = [1,1]` and the side condition is vacuous: `[let]` is `bind`
  (`Core/Fundamental.lean:79`). The side condition is Tang, Hillerström, Lindley & Morris's
  `T-Seq` read at the row: a continuation used under a control-flow-unlimited row cannot capture
  linear resources (POPL 2024, §2.2, [via #235, report "linear effect algebras", L5-P]).
- **Uses.** O-ROW, O-QUAL, K-GRADE.
- **Today.** `effLet`, `Core/Fundamental.lean:353-358` [Lean]; as built, **changed** in
  presentation only (K-GRADE).
- **Slices.** Step 04 (none beyond `to`); clause 05; laws 06 (L-ALG, the graded form); compat 07
  (`let_compatC`, `Core/EffRules.lean:896`).
- **Depends on.** K-GRADE.
- **Open.** OQ-16.
- **Obligation.** At `W`: **mechanical** from `ewp_bind`; the step most likely to be
  non-mechanical is the `aff` case at `σ ≠ []`, where the abandoned `Γ₂` may hold the open frames
  OQ-9 asks about. `Γ₂ drops` gives `NoOwn` (`gDenC_noOwn`, `Core/EffRules.lean:873`), which says
  nothing about open lends.

### K-THEN: the finaliser frame

- **Form.**

  ```
  Γ = Γ₁ ∘ Γ₂      Σ.NZ      hi g(Σ) = ∞ ⇒ Pers Γ₂
  Δ; Γ₁ ⊢ M : F_Σ A      Δ; ⟨A, live⟩ :: Γ₂ ⊢ N : F_Σ B      Δ; ⟨1, dead⟩ :: Γ₂ ⊢ D : F_{Σ^fin} 1
  ──────────────────────────────────────────────────────────────────────────────────  [then]
  Δ; Γ ⊢ M then x. N unwind D : F_Σ B
  ```

  `M then x. N unwind D ≜ ubind (λx. N, λ_. D) M` (`thenE`, `Core/EffRules.lean:923` [Lean]).
  `D` runs instead of `N` when `M` unwinds or is cancelled, in the same `Γ₂`, additively: `N` and
  `D` share `Γ₂` and one of them consumes it. `D` is the destructor of the frame, and the
  destructor `D_K` of a context `K` (O-FIN, D-DTOR) is its `D`s, innermost first. This is the
  weakening-as-destructor reading of Congard, Munch-Maccagnoni & Douence (ESOP 2026; `K[raise e]
  ≡ D_K⟨raise e⟩`, [via 12-sources, CMD26]; `D_K⟨·⟩` and the sequential `D_K ▷ e` are O-FIN's).

  `Σ^fin` is the row a finaliser may perform. As built, `Σ^fin = Σ^abort` (and answering calls,
  which are not in rows).
- **Uses.** O-FIN, O-ROW, K-GRADE.
- **Today.** `effThen`, `Core/Fundamental.lean:360-365` [Lean]; as built, with one further
  premise `hUq : S.Uniq` (`Core/EffRules.lean:746`), which K-ROW's sum of distinct names makes
  true of every row: **changed** (the premise is deleted once K-ROW lands).
- **Slices.** Step 04 (`[then]`, `[finalise]`, `[finalise-cancel]`, `[cfin-ret]`, `[cfin-raise]`);
  clause 05 (D-DTOR); laws 06 (L-ALG0, L-W); compat 07 (`then_compatC`, `Core/EffRules.lean:928`);
  lowering 08 (`Backend/Clos/Unwind.lean`).
- **Depends on.** K-GRADE, K-ROW.
- **Open.** OQ-7: whether `Σ^fin` is `Σ^abort` (R-FINAB, the default) or any `TableOK` row's
  finalisable part (K-FINR, §9.8); OQ-21: what a finaliser may perform, and the cancel error policy. The
  elaborator's drop glue (a `[then]` for every owned local at a possible weakening point) is a
  surface obligation, 08's.
- **Obligation.** At `W`: **mechanical** at `Σ^fin = Σ^abort` from `ewp_frame_then`
  (`Core/EffRules.lean:369`); **unknown** under OQ-7 (a), where `D` may stop at a resuming
  operation during a cancel, reaching a dying handler of the region (SPEC §19 *Typing*, the
  finaliser paragraph).

---

## 4. Handlers and continuations

### K-KONT: the continuation and its types

- **Form.** The continuation of `op_i : A_i ↠^q B_i` under a handler answering `F_Σ R` is a value
  of type

  ```
  K_lin(B, Σ, R) ≜ U((B ⊸ F_Σ R) & ⊤)
  K_aff(B, Σ, R) ≜ U((B ⊸ F_Σ R) & F_Σ 1)
  K_unr(B, Σ, R) ≜ !U((B ⊸ F_Σ R) & F_Σ 1)
  ```

  Its two entries are `&` projections, by the baseline rules:

  ```
  Δ; Γ ∋! k : K_q(B, Σ, R)   Δ; Γ' ⊢ w : B
  ──────────────────────────────────────────  resume   (proj₁, then app)
  Δ; Γ ∘ Γ' ⊢ (force k).1 w : F_Σ R

  Δ; Γ ∋! k : K_q(B, Σ, R)      q ∈ {aff, unr}
  ──────────────────────────────────────────  cancel   (proj₂)
  Δ; Γ ⊢ (force k).2 : F_Σ 1
  ```

  The `&` makes the two entries share the one captured context: the textbook encoding of an
  affine type as `A & 1`, whose `1` branch is the destructor (Munch-Maccagnoni, *Resource
  polymorphism*, 2018, [via 12-sources, MM18]). At `lin` the cancel branch is `⊤`, which has no
  elimination to a computation, so `κ` must be resumed. At `unr`, `κ` is under `!`, so it is
  copied and dropped by `copyBang`/`forgetBang`; its captures are persistent, because promotion
  needs `Pers Γ` (`lam_bang_persistent`, `experiments/HandlersControl/HandlersControl/
  Capture.lean:42` [Lean]), which is the multi-shot persistence condition of Tang et al. (§2.2,
  [via #235, L5-P]). `κ` is a value: it may be stored in a `Ref`, put in data, passed to another
  handler, and resumed after its handler's clause has returned.

  No duplication of a linear or affine `κ` (L-C) is a consequence of BoLo's linear context
  premises: `K_lin` and `K_aff` are not `!` types, so `Ctx.SplitP` gives `k` to one side
  (`Core/Persistent.lean:112`).
- **Uses.** O-KONT, O-QUAL, K-FTY.
- **Today.** `kTy`, `Core/EffRules.lean:976-980` [Lean]; as built. The value `κ` the machine
  hands the clause is `kappa n H K` (`Paper/S3_Dynamics/Definitions.lean:438`), with resume
  `λy. hnd (n, H) K[y]` and cancel `ccatch (hnd (n, H) K[raise (⊥, (n :: names K, none))])`.
- **Slices.** Step 04 (`[op]` builds `κ`; `[cancel]`, `[cancel-raise]`); relation 05 (D-KAP,
  D-SHARE, D-OWED); laws 06 (L-W, L-C, L-P, L-BETA); compat 07 (through `handle_compatC`).
- **Depends on.** K-FTY, K-HND (which binds `κ`).
- **Open.** OQ-16 (`unr`); OQ-17 (`rel`; K-RELQ, §9.10); OQ-28 (the bound of a stored `κ`, whose two
  options are K-GEN below: as built, `κ` holds
  no lend, since under R-T1 no non-abortive operation crosses a borrow; once R-T1 is lifted, a
  `κ` capturing a lend at `'a` is stored at `[@c] K_q(…)` with `@c ⊐ @a`, as
  `box_lolli_outlives_iff`, `experiments/HandlersControl/HandlersControl/Outlives.lean:35`
  [Lean], gives for `[@c](T₁ ⊸ T₂)`); OQ-8 (where `κ`'s future-world quantifier sits).
- **Obligation.** `vC_kTy_of_kapRel` at `W`: **mechanical** at `σ = []`; **unknown** at `σ ≠ []`
  (OQ-8, OQ-9).

### K-GEN: a stored continuation (both options of OQ-28)

- **Why a rule is needed.** A `κ` is a run-time value with no `CDerives` rule (§1.4), and
  `VOutlivesR` has no rule at `U C` (K-FTY, *Outlives*), so `boxI` cannot put a `κ` under
  `[@c]`. A continuation that holds a borrow at `'a` and is stored must still be bounded by `'a`
  (OQ-28). The two options below are the two ways to give it a bound; each is written in full so
  that OQ-28's compatibility lemma has a fixed target. Neither is adopted until OQ-28 is settled.

- **Option (a): `[gen]` as a rule** (branch `lift-stage1`, `Core/Gen.lean`, transcribing
  `docs/effects-tr` §15, D14.3-D14.7). For one affine resuming operation
  `yield : B_y ↠^{aff} A` of name `n`:

  ```
  Δ ⊨ Γ ⊐ @c      Δ ⊢ A ⊒ @c      Δ; Γ ⊢ M : F_{n:{yield : B_y ↠^{aff} A} ⊕ Σ} 1      n ∉ names(Σ)
  ───────────────────────────────────────────────────────────────────────────────  [gen]
  Δ; Γ ⊢ gen_n M : F_Σ((B_y ⊕ 1) ⊗ [@c] U(Aff^c_Σ A (B_y ⊕ 1)))
  ```

  `gen_n M ≜ hnd_n (h_ret, [h_yield]) M` with `h_ret ≜ λ_. done to d. return (inj₂ (), d)` and
  `h_yield ≜ λ(b, κ). return (inj₁ b, κ)`: the clause returns `κ`, read as a bounded affine closure
  (K-NU's `Aff^c_Σ`, SPEC §22) whose `call` resumes it and whose `close` cancels it. As built the
  rule is at `Σ = ∅` (`Tout = ∅`, `ewp_gen` is one application of `ewp_handle` at `Tin = T_y`,
  `Tout = ∅`; `Core/Gen.lean` docstring); the form at a row `Σ` is this specification's
  generalisation. It is K-HND at a carrier whose answer stores `κ`, made a rule because the box
  cannot be introduced otherwise. Its relation to K-HND and K-NU: it is K-HND whose clause
  returns `κ`, with `κ`'s type read as K-NU's `Aff^c_Σ`.
- **Option (b): an outlives rule at `U C` and at `K_q`.**

  ```
  Δ ⊨ captures(C) ⊐ @c                                  Δ ⊨ Γ_κ ⊐ @c
  ───────────────────────  [U-outlives]               ─────────────────────  [K-outlives]
  Δ ⊢ U C ⊐ @c                                          Δ ⊢ K_q(B, Σ, R) ⊐ @c
  ```

  where `captures(C)` is the context the thunk was introduced at (a typing-time annotation: the
  rule is stated at `[thunkΣ]`'s conclusion, `Δ; Γ ⊢ thunk M : U C` with `Δ ⊨ Γ ⊐ @c` giving
  `Δ ⊢ thunk M : [@c] U C` directly), and `Γ_κ` the captured context of the stopped term. Then
  `boxI` boxes a thunk or a `κ`, and `[gen]` is derived: `gen_n M ≜ hnd_n … M` with the clause's
  `κ` boxed by `boxI`. Its cost: outlives becomes a judgement on terms at `U C`, not on types,
  which changes SPEC §23's outlives from a type judgement into one that reads a derivation.
- **Step (04).** Under both options, none new: `[op]` builds `κ`, `[ret]` the `done` answer;
  `call` on the stored `κ` is `resume`, `close` is `cancel` (K-KONT).
- **Model (05).** D-KAP at a boxed `κ`: `𝒱⟦[@c] U(Aff^c_Σ A B)⟧_W` holds of `κ` when `κ ∈ KapRel`
  at `W` and its resource lies in `Res_{δ(c)}` (`affBox_of_kapRel`, T14.4, `Core/Gen.lean`
  docstring), by coinduction at `Aff`'s `ν` (`aff_coind`). The world it is read at once stored is
  OQ-46's.
- **Laws (06).** L-BETA at a stored `κ`: `call (κ, w) ≡ resume κ w`; L-W at a stored `κ`:
  `close κ ≡ cancel κ`; L-HRET, L-HOP at `gen_n`'s handler.
- **Compatibility (07).** `gen_compatC` (T14.6 then T14.4: `[TR]` 6.62 puts the body's resource in
  `Res_{δ(c)}`, `wpTS_box` (`[TR]` 6.147) keeps every suspension there); a T-COMPAT row in 07,
  Rows G.
- **Lowering (08 §6).** A stored state machine value: the closure IR's `κ` (statically known size,
  SPEC §19 *Lowering*), `call` its resume arm, `close` its cancel arm; law L-BETA, L-W.
- **Uses.** K-KONT, K-HND, K-NU, K-FTY. **Today.** Option (a) on branch `lift-stage1`
  (`Core/Gen.lean`), citing `[spec §24]`, an unwritten section (08 §4.1); status **new**.
- **Depends on.** K-HND, K-NU. **Open.** OQ-28 (which option), OQ-46, OQ-8; R-T1 (as built,
  "no lend open at a suspension" is not needed because R-T1 holds, `Core/Gen.lean` docstring).
- **Obligation.** Option (a) at `Σ = ∅`, `σ = []`: **as built** on its branch. At a row and at
  `W`: **unknown**. Option (b): **unknown**, the outlives judgement on terms.

### K-HND: the deep handler (a model of `E`)

- **Form.**

  ```
  Γ = Γ₁ ∘ Γ₂      Γ₁ = Γr ∘ Γc      n ≠ ⊥      n ∉ names(Σ)
  Δ; Γr ∋! ir : !U(A ⊸ F_Σ R)                                         (h_ret)
  Δ; Γc ∋! ic : ⊗_{op_i ∈ E} H_i                                       (the clauses)
  Δ; Γ₂ ⊢ e : F_{n:E ⊕ Σ} A
  ──────────────────────────────────────────────────────────────────────  [handle]
  Δ; Γ ⊢ hnd_n (ir, ic) e : F_Σ R

  H_i ≜ !U(A_i ⊸ F_Σ R)                    op_i abortive (κ is not reified)
  H_i ≜ !U(A_i ⊗ K_{q_i}(B_i, Σ, R) ⊸ F_Σ R)  otherwise
  ```

  `hnd_n (ir, ic) e ≜ hnd (n, (h_ret, hs)) e` with `h_ret` and `hs` variables (A-normal form;
  `hndTerm`, `Core/EffRules.lean:997` [Lean]). The handler is **deep**: `κ` reinstalls
  `hnd_n` (K-KONT). It removes its own name and passes the rest of the row outward. Its clauses
  and its answer are at `Σ`, so a clause performs the outer handlers' operations, and an operation
  of another name inside `e` is forwarded (L-HFWD). The clauses are `!`: Tang et al.'s
  `T-Handler` asks this of a deep handler, since `hnd_n H` moves into an unrestricted
  continuation of another name ([via #235, H-fwd row]). The pair `(h_ret, (h_i)_i)` is a model of
  `E` at carrier `F_Σ R` (O-MODEL, K-MODEL); `[handle]` interprets `e` in it (D-MODEL, T-MODEL).

  A `for` over a generator is a `[handle]` of the iteration effect whose clause is the loop body
  (SPEC §15); `break`/`return` are `cancel` on `κ`. An abortive-only handler whose clauses run
  after it (`d_handleAbortCapture`, `experiments/SecondClass/SecondClass/AbortClause.lean:69`
  [Lean]) is a derived form of `[handle]`, and so are handlers with a state (SPEC §21, a
  state-passing answer type `F_Σ R = F_Σ(U(S ⊸ F_Σ(S' ⊗ R)))`).
- **Uses.** O-MODEL, O-NAME, O-ROW, O-SIG, K-KONT.
- **Today.** `effHandle`, `Core/Fundamental.lean:367-372` [Lean]; as built. Its
  body row is the list `Row.ofEff n E 0 ++ S` (`Core/EffRules.lean:969`), the `j`-th operation
  at index `j`; the clauses' type is `clausesTy` (`:989`) with `clauseTy` (`:984`); `h_ret`'s is
  `retTy` (`:994`); further premises `hn0 : n ≠ 0`, `hnS : ∀ o ∈ S, o.n ≠ n`, `hlen : E.length ≤
  2^32`. Under OQ-35 (a) the rule gains the premise `Closed E`; by default it has none.
- **Slices.** Step 04 (`[ret]`, `[op]`, `[unwind]`); relation 05 (D-MODEL, `ewp_handle`,
  `Core/EffRules.lean:615`); laws 06 (L-HRET, L-HOP, L-HFWD, L-HUNIQ, L-HFUSE, L-YIELD); compat 07
  (`handle_compatC`, `Core/EffRules.lean:1092`); lowering 08 (`Backend/Clos/Capture.lean`).
- **Depends on.** K-SIG, K-ROW, K-NAME, K-MODEL, K-KONT.
- **Open.**
  - OQ-3 (does a handler site open a lifetime?). Under OQ-3 (a) the rule's body premise becomes
    `Δ.extend x ⊓Δ; Γ₂ ⊢ e : F_{n:E ⊕ Σ}(['x] A)`, with `'x` free in neither `Γ₁`, `Σ`, `E` nor
    `R`, and `h_ret : !U(['x] A ⊸ F_Σ R)`, as `withbor`'s callback is `∀'x ⊏ ⊓Δ. L ⊸ ['x] B`. That
    places the handler in the lifetime order beside the borrows it sits between. The answering
    handler already has this form, since it is `withbor` form (2) (`handle_is_shift`,
    `experiments/HandlersAsBorrows/HandlersAsBorrows/Safety.lean:115` [Lean]). The candidate rule
    is written here only as OQ-3's option (a); it is not adopted. R-MID by default.
  - OQ-14 (static names or generative instances; R-STATIC); OQ-25 (handler state: a
    state-passing answer, or comodel state in a cell); OQ-26 (shallow handlers; `ν` only by
    default; K-SHALLOW, §9.7); OQ-15, OQ-67 and R-HDIV (a handler around a div computation, K-HDIV,
    §9.2); OQ-35 (closed operation types); OQ-37 (carriers other than `F_Σ R`; R-RETCARRIER;
    K-CARRIER, §9.3); OQ-61 (operation types that name their own row; R-NOSELFROW; K-SELFROW, §9.12).
- **Obligation.** `handle_compatC` at `W`: **unknown** at `σ ≠ []` (a stop of another name with
  lends open between the handler and the operation, OQ-3, OQ-9); **mechanical** at `σ = []`, the
  step most likely to be non-mechanical being T-MODEL's replacement of the four-case analysis of
  `handle_compatC` by initiality (audit M11).

---

## 5. Capabilities and co-operations

### K-SWAP: `withswap`, the comodel carrier

- **Form.** As printed (`[TR]` p. 3, read call-by-value):

  ```
  dead Γ
  ──────────────────────────────────────────────────────────  [withswap]
  Δ; Γ ⊢ withswap : Mut @a A ⊸ (A ⊸ A ⊗ B) ⊸ Mut @a A ⊗ B
  ```

  `withswap` takes the payload out of a `mut`-lent cell, runs the callee on it by value, and
  stores what the callee hands back. It is not a shift: its callee is a bare `⊸` with no
  lifetime label (`experiments/Shifts/Shifts.lean`, module docstring line 9 [read]). It is the
  carrier of every co-operation (K-CAP).

  The full calculus asks whether the callee may perform (OQ-20). The two shapes, each stated so
  the compatibility lemma of OQ-20's "what settles it" has a fixed target:

  ```
  (c)  withswap[Σ] : Mut @a A ⊸ U(A ⊸ F_Σ(A ⊗ B)) ⊸ F_Σ(Mut @a A ⊗ B)      BorOK-style premise on Σ
  (b)  a withtake shape : Mut @a (1 ⊕ A) ⊸ U(A ⊸ F_Σ(A ⊗ B)) ⊸ F_Σ(Mut @a (1 ⊕ A) ⊗ B)
       the cell holds inl () while the payload is out (#279, external input)
  ```

  (c) is the printed constant read at a row, as K-BOR reads the borrows; it adds no constant. Under
  (c) an abortive stop of the callee abandons the payload, leaving the cell with no value; the
  premise must exclude weakening on `Σ` or provide a value to put back. (b) is not an instance of
  any printed constant: adopting it would put a constant beside `withswap`, which one borrow per
  printed constant (C-6) and no new mechanism (C-9) exclude unless it is shown to be an instance
  of K-BOR's schema or a derived term over `load`/`store`. It is a candidate to justify, not a
  design; if no such justification is found it is reported as a defect under 00 §0.2 item 1. The
  placeholder would make the empty cell a value of the cell's type.
- **Uses.** O-COMODEL.
- **Today.** `withswap`, `Core/Fundamental.lean:254-255`; its type `axWithswapTy`,
  `Core/Types.lean:1906` [Lean]; as built, pure. No unwinding form: an unwind would abandon the
  payload (SPEC §19 *Typing*, the borrows paragraph). Called through `Mut` for affine closures
  (`d_callMut`, `Core/AffRules.lean:205` [Lean]) and for answering operations (`opCall`,
  `Core/Handlers.lean:55` [Lean]).
- **Slices.** Step 04 (the printed `withswap` steps); clause 05 (D-COMODEL); laws 06 (L-STATE,
  L-TENSOR, L-INTER, L-TAIL); compat 07 (`withswap_compatX`); lowering 08 (a direct call).
- **Depends on.** none beyond the baseline.
- **Open.** OQ-20 (R-PURESWAP by default; both shapes completed in K-SWAPΣ, §9.11, where (b) is
  shown a derived term over the printed `withswap`); OQ-7 (an unwinding form of `withswap` at a
  finalisable row).
- **Obligation.** None at (a). At (b) or (c): **unknown**, the frame of a `mut` cell whose payload
  is out across a stop of the callee.

### K-CAP: a capability (a comodel of `E`)

- **Form.** A capability for `E` at state `S` lent at `'l` is the state's `mut` view beside the
  co-operations as `!` code:

  ```
  Cap_l(E, S)  ≜  Mut 'l S ⊗ ⊗_{op_i ∈ E} !U(S ⊗ A_i ⊸ F(S ⊗ B_i))
  ```

  Its rules are derived from `withbor2`, `withswap` and the baseline:

  ```
  Δ; Γ₀ ⊢ s₀ : S     Δ; Γc ⊢ cl : ⊗_i !U(S ⊗ A_i ⊸ F(S ⊗ B_i))     ∃ @b. Δ ⊨ @b ∧ Δ ⊢ S ⊒ @b
  Δ.extend l ⊓Δ; ⟨Cap_l(E,S), live⟩ :: Γ ⊢ M : F_Σ(['l] B)       'l ∉ fv(Γ, Σ, B, S)      BorOK_l Σ
  ──────────────────────────────────────────────────────────────────────────  [cap-install] (derived)
  Δ; Γ₀ ∘ Γc ∘ Γ ⊢ with_E(s₀, cl) {c. M} : F_Σ (S ⊗ B)

  Δ; Γ ∋! c : Cap_l(E, S)      Δ; Γ' ⊢ v : A_i
  ──────────────────────────────────────────────────────────────  [cap-call] (derived)
  Δ; Γ ∘ Γ' ⊢ call_i(c, v) : F(Cap_l(E, S) ⊗ B_i)
  ```

  `with_E(s₀, cl) {c. M} ≜ bor_withbor2[Σ] (alloc s₀) (Λ'l. λm. M[(m, cl)/c])` followed by
  `free` on the returned cell, and `call_i(c, v) ≜ let (m, cl) = c; let (m', b) = withswap m
  (λs. force (π_i cl) (s, v)); ((m', cl), b)`. A capability's operations do not appear in any
  row: a computation that uses one holds it in `Γ`, and `Σ` lists only the effects served by a
  handler outside. A function over a capability is therefore not coloured by it; this is the
  statics of "no function colouring" for answering effects. The capability cannot escape its
  handler: `Mut 'l S ⊐ 'l` fails at every satisfiable `Δ`, so `[]I` refuses a result that holds it
  (`capability_not_outlives`, `escape_refused`,
  `experiments/HandlersAsBorrows/HandlersAsBorrows/Safety.lean:87, 108` [Lean]). It can be
  returned from a function and stored in a cell inside `'l` (`d_sepProg`, `…/Separating.lean`
  [read]), which separates it from Effekt's System Ξ (Brachthäuser, Schuster & Ostermann, OOPSLA
  2020, [via #235]). Two closures capturing one stateful capability at once are refused
  (`twoBlocks_refused`, `…/Sharing.lean:196` [Lean]); sharing a stateful effect among several
  closures is the control handler with the state in its frame (K-HND; the construction of
  `experiments/HandlersControl/HandlersControl/Behind.lean` [read], whose depth limit
  `no_uniform_comp` is what native capture removes).

  A state-access operation `B·S → A·S` on linearly used state is the same data as a generic
  effect and an algebraic operation (Møgelberg & Staton, LMCS 2014, Thm 8.1, §8.1.2, [via #235,
  item 3]); `Cap_l(E, S)` is that shape with `S` the lent cell, which is the sense in which a
  capability is a comodel of `E` (O-COMODEL, OQ-19).
- **Uses.** O-COMODEL, O-SIG, K-SWAP, K-BOR.
- **Today.** Derived, not a kernel construct. At the paper level `handle` is `withbor` form (2)
  and typing is preserved (`translate_typed`, `experiments/HandlersAsBorrows/HandlersAsBorrows/
  Translate.lean:190` [Lean]); effect safety is the FP on its image (`effect_safety`,
  `…/Safety.lean:55` [Lean]). Over `CDerives` the elaborator emits the same `withswap` call
  (`Core/Handlers.lean:51-60` [Lean]; SPEC §18 *Elaboration*). **new** as a kernel object only
  if OQ-1 chooses (b); under OQ-1 (a) it stays derived.
- **Slices.** 02 (K-COMODEL, the form); 05 (D-COMODEL, T-COMODEL); laws 06 (L-STATE, L-TENSOR,
  L-INTER, L-TAIL); elaboration 08 (T-ELAB for answering handlers).
- **Depends on.** K-SWAP, K-BOR, K-COMODEL.
- **Open.**
  - OQ-1. Under (a), an answering operation is a `[perform]` of `E` handled by a `[handle]` whose
    clause resumes once in tail position with the state, and `E` appears in `Σ` at the call;
    under (b) both stay, and the capability's protocol is checked against `opTable ⟦n:E⟧` by
    T-COMODEL. The two readings give different rows to the same program, so OQ-1 also decides
    which effects colour a function type.
  - OQ-19 (comodel = state access only, by default); OQ-20 (a co-operation that performs: `F` in
    `Cap_l` becomes `F_{Σ'}`); OQ-29 (an answer that borrows from `S`); OQ-25.
- **Obligation.** `[cap-install]` and `[cap-call]` as `CDerives` derivations: **mechanical** (the
  paper-level `translate_typed` restated over `CDerives` at a row). T-COMODEL: **unknown** (02,
  05).

---

## 6. Borrows at a row

### K-BOR: one borrow constant per printed constant, at any callback row

- **Form.** Every borrow constant is an instance of one schema, the labelled shift of
  `experiments/Shifts` (`shiftTy src view ret x bnd T₂ = src ⊸ (∀'x ⊏ bnd. view 'x ⊸ ['x] T₂) ⊸
  R`, `R = src ⊗ T₂` when `ret`, `T₂` otherwise; `experiments/Shifts/Shifts.lean:17` [Lean]),
  read at a callback row `Σ`:

  ```
  bor_k[Σ] : U( src_k ⊸ U(∀'x ⊏ ⊓Δ. view_k('x) ⊸ F_Σ(['x] B)) ⊸ F_Σ(res_k) )

  dead Γ      x ∉ dom Δ      x ∉ fv(A, B)      side_k(Δ, A, B)      BorOK_x Σ    (R-CLOSEDOP, R-T1)
  Σ.Weak ⇒ (d closed  ∧  Δ; Γ ⊢ d : src_k ⊸ F_{Σ^fin} 1)        (k ≠ withload)
  ─────────────────────────────────────────────────────────────────────  [bor_k]
  Δ; Γ ⊢ borE_k[Σ](d) : bor_k[Σ]
  ```

  | `k` | `src_k` | `view_k('x)` | `res_k` | `side_k` | finaliser `d` at `Σ.Weak` |
  |---|---|---|---|---|---|
  | `withbor1` | `Ref A` | `Imm 'x A` | `Ref A ⊗ B` | `A` scoped in `Δ` | the destructor of `Ref A` |
  | `withbor2` | `Ref A` | `Mut 'x A` | `Ref A ⊗ B` | `∃ @b. Δ ⊨ @b ∧ Δ ⊢ A ⊒ @b` | the destructor of `Ref A` |
  | `withbor3` | `Mut @a A` | `Mut 'x A` | `Mut @a A ⊗ B` | none | `forget` |
  | `withload` | `Imm @a A` | `Imm̲ 'x A` | `B` | none | none: the load consumed the source |
  | `sliceBorrowM` | `Array A` | `[Mut 'x A]` | `Array A ⊗ B` | `side_withbor2` at `A` and at `B` | the destructor of `Array A` |
  | `sliceBorrowI` | `Array A` | `[Imm 'x A]` | `Array A ⊗ B` | `A` scoped; `side_withbor2` at `A` and at `B` | the destructor of `Array A` |

  `borE_k[Σ](d)` is the printed constant's own term when `¬ Σ.Weak` (no stop can abandon the
  callback, so no finaliser is needed), and the unwinding term `withborU d = λr. λf. (f [] r)
  then b. (r, b) unwind d r` when `Σ.Weak` (`withborUE`, `Core/EffBorrow.lean:200` [Lean]);
  `withload` keeps its own term at every row (`Core/Fundamental.lean:276-279`). When the
  callback stops at an abortive operation, the lend ends, the source returns to the lender, `d`
  runs, and the unwind continues outward (L-BOR).

  **Instances.**
  - `Σ = ∅`: the pure constants `withbor1/2/3`, `withload`, `sliceBorrowM/I`
    (`Core/Fundamental.lean:201-253` [Lean]) are this instance up to the call-by-value reading:
    the pure constant's type is the value form `src ⊸ (∀'x ⊏ ⊓Δ. view 'x ⊸ ['x] B) ⊸ res`
    (`axWithbor1Ty`…, `Core/Types.lean:1886-1904`; `VTy.all x b A = U(∀'x ⊏ b. F A)`,
    `Core/Types.lean:163` [Lean]), and the generic one is the computation form above. Each is a
    closed `CDerives` coercion of the other (an η-expansion through `allEV` and `lolliE`), so the
    pure constants become abbreviations.
  - `BorOK_x Σ` with R-CLOSEDOP and R-T1, i.e. `Row.Unwind x`: the `*U` constants `withbor1U` … `sliceBorrowIU`
    (`Core/Fundamental.lean:258-294`; types `Core/EffBorrow.lean:177-196, 525, 625-631` [Lean]).
  - The answering handler is `bor_withbor2[Σ]` at `src = Ref S` (`handle_is_shift`; K-CAP).

  `withswap` is not an instance (K-SWAP). The one (source, view) pair of `Shifts`' mode analysis
  that no printed constant provides, `Mut` source with `Imm` view (`axWithborMITy`,
  `experiments/Shifts/Shifts.lean`), is not added: K-BOR has one constant per printed constant
  and per SPEC §9 slice constant, no more.
- **The full class.** The full calculus states `BorOK_x Σ` as the syntactic class whose
  interpretation is `TableOK_x` (D-TABLEOK):

  ```
  BorOK_x Σ  ≜  Σ.NZ                                                (the full class)
  ```

  Two named restrictions add conjuncts by default, and each is cited where it applies:

  ```
  R-CLOSEDOP (OQ-56):  Closed Σ ∧ Data_x Σ       operation types closed in lifetimes, free of 'x,
                                                  their arguments outliving every lifetime
  R-T1 (OQ-2, OQ-9):   every operation of Σ is abortive
  ```

  With both, the class is today's `Row.Unwind x` (`Core/EffBorrow.lean:133-134` [Lean]). Without
  R-T1 a callback may perform resuming operations, the lend is open across the stop, and `κ` holds
  it (OQ-9, OQ-10, D-STOP). Without R-CLOSEDOP an operation's type may mention lifetimes; it may
  not mention `'x` itself, because the callback's row is the borrow's result row and `'x` is not
  in scope there (premise `x ∉ fv(A, B)`). The precise class of operation types that may mention
  the lend is OQ-56; its candidate (b) is a lifetime-polymorphic operation, written here so that
  the question has a fixed target (not adopted):

  ```
  op_i : ∀'y ⊏ c. A_i['y] ↠^{q_i} B_i['y]                 (a lifetime-polymorphic operation)

  Δ ⊨ @b ⊏ c      Δ; Γ ⊢ V : A_i[@b/'y]
  ─────────────────────────────────────────────  [perform∀]
  Δ; Γ ⊢ perform_{n,i}[@b] V : F_Σ B_i[@b/'y]

  clause:  !U(∀'y ⊏ c. A_i['y] ⊗ K_{q_i}(B_i['y], Σ, R) ⊸ F_Σ R)      R, Σ free of 'y
  ```

  At the perform `@b` is the lend's `'x`, which is in scope there; the clause is parametric in
  `'y`, so the view it receives cannot reach `R` or the row. Its model entry is the `opTable`
  entry read at every instantiation below the lend, and its settling statement:

  ```lean
  /-- OQ-56 (b): a row with a lifetime-polymorphic entry is TableOK at every lend below c. -/
  def LifetimePolyOpTableOK : Prop :=
    ∀ (Σ : Row) (x : LifeVar) (δ : LSub) (c : Life), PolyEntriesBelow Σ c →
      ∀ α, LtLife δ c α → TableOK_x (opTable (⟦Σ⟧ (δ.extend x α)))
  ```

  (`PolyEntriesBelow`, `TableOK_x` and `⟦Σ⟧` at a polymorphic entry are names the settling experiment defines.)
  Checked against the tier-2 programs of 01 §5.3: the asynchronous read into a local buffer is
  typed at (b) with `read : ∀'y ⊏ c. Mut 'y Buf ↠^{aff} 1`; the generator yielding views is typed
  with `yield : ∀'y ⊏ c. Imm 'y T ↠^{aff} 1`; both are excluded by R-CLOSEDOP and by R-T1.
- **Uses.** O-BOR, O-ROW, D-TABLEOK, K-THEN.
- **Today.** A pure rule and an unwinding twin per constant, each with its own compatibility lemma
  (`Core/Compatibility.lean`, `Core/Slices.lean`, `Core/EffBorrow.lean:275, 356, 446, 548, 645,
  726` [Lean]). **changed**: one rule per printed constant, generic in `Σ`.
- **Slices.** Step 04 (the printed borrow steps; `[then]`/`[finalise]` for the unwinding term);
  relation 05 (T-FRAME at `TableOK` tables, T-SUMOK); laws 06 (L-BOR); compat 07 (one lemma per
  `k`, at every `BorOK_x Σ`); 08 (the `*U` twins and pure constants as abbreviations; the
  checker's constants).
- **Depends on.** D-TABLEOK, T-FRAME, T-SUMOK, K-THEN, K-ROW.
- **Open.** OQ-2, OQ-9, OQ-10 (R-T1); OQ-56 (R-CLOSEDOP); OQ-40 (the class); OQ-7 and OQ-21 (`d`'s row: pure today,
  `d : src ⊸ F 1` by the premise `hd`, `Core/Fundamental.lean:262`; the generic rule writes
  `F_{Σ^fin} 1`, equal to `F 1` until OQ-7/OQ-21 widen it); OQ-13 (`Σ` is a meta-index:
  `bor_k[Σ]` is a schema over rows, as `withbor1U` already is, and needs no row variable).
- **Obligation.**
  - The abbreviations: pure ⟷ `bor_k[∅]` and `*U` ⟷ `bor_k[Σ]` at `Row.Unwind x`:
    **mechanical** (closed derivations); the step most likely to be non-mechanical is `withload`,
    whose pure and unwinding terms coincide while their types differ in the callback's shape.
  - `bor_k_compat` at every `BorOK_x Σ`: under R-T1 **mechanical** from the existing `*U` lemmas;
    without R-T1 **unknown**, carried by T-FRAME at resuming tables and by OQ-9's probe. Each
    row follows its printed proof. `bor_withbor3[Σ]` follows `[TR]` 6.174 (withbor-compat3,
    `Paper/S6_8_FundamentalProperty/Lemmas.lean:1462-1466`): AntiFrame 6.66, then 6.60 for
    `𝒱⟦T₁⟧δ ⊨ [α]𝒱⟦T₁⟧δ`, then MutFrame 6.65, so its obligation at a resuming table is T-FRAME's
    6.66 and 6.65 halves plus 6.60; it does not use 6.150. `bor_withload[Σ]` follows 6.175 and
    needs `[TR]` 6.150 (the `↺` rule) lifted to `ewp`, which T-FRAME lists as not built.

---

## 7. Recursion, codata and divergence

### K-FIX: the bounded fixed point at every computation type

- **Form.**

  ```
  dead Γ
  ───────────────────────────────────────────────────────────────────  [boundedFix]
  Δ; Γ ⊢ bounded_fix[A, C] : !U(!U((1 ⊕ !U(A ⊸ C)) ⊗ A ⊸ C) ⊗ (I32 ⊗ A) ⊸ C)
  ```

  at every `C`, rows included (`C = F_Σ B`, or a record `&ⱼ(E ⊗ Pⱼ ⊸ F_Σ(E ⊗ Tⱼ))` of a
  recursive group's members, SPEC §21). A recursive group is the bounded fixed point of its
  generator, called directly; a layer is a transformer of the generator applied before the fixed
  point; the self-reference at a spent budget is `inj₁ ()`, on which the generator performs
  `Exhausted`, an abortive library effect (K-RAISE). No recursion construct is added: recursion
  is this constant plus K-RAISE.
- **Uses.** K-FTY, K-RAISE.
- **Today.** `boundedFix`, `Core/Fundamental.lean:196-198`; `boundedFixTy`,
  `Core/BoundedFix.lean:41`; `boundedFix_compatX`, `Core/BoundedFix.lean:91` [Lean]; as built.
- **Slices.** Step 04 (`[boundedFix]`); laws 06 (L-FIX); compat 07.
- **Depends on.** none beyond the baseline.
- **Open.** OQ-14 (recursion through a site needs generative instances; R-STATIC); OQ-15, OQ-67
  (a recursion whose body loops raises `Exhausted` inside a loop's observation, handled by K-HDIV,
  §9.2, whose lift is deferred by R-HDIV); OQ-31 (bounded recursion is one of the cut-offs keeping
  the relation step-free).
- **Obligation.** At `W`: **mechanical**, the induction on the budget at every `C`
  (`fixSelf_valid`); it reads `𝒞⟦C⟧` only through closure under a pure head step (`cC_head`),
  which D-REL must keep at `W`.

### K-NU: effectful codata and the effectful affine closure

- **Form.** `νX. C` with `C` positive (`NuOk`): a `&` of observation trees whose leaves may be
  effectful, `F_Σ A` with `A` polynomial in `X` and the operation types of `Σ` closed in type
  variables, and whose observations may take a closed argument `A ⊸ D`
  (`CTy.EffLeaf`, `NuLeaf`, `NuOk`, `Core/Types.lean:1141-1159` [Lean]).

  ```
  NuOk C    Δ; Γ ⊢ M : C[U(νX. C)/X]           NuOk C    Δ; Γ ⊢ M : νX. C
  ─────────────────────────────── [nuIn]       ─────────────────────────────── [nuOut]
  Δ; Γ ⊢ M : νX. C                             Δ; Γ ⊢ M : C[U(νX. C)/X]

  NuOk C      dead Γ
  ───────────────────────────────────────────────  [unfold]
  Δ; Γ ⊢ unfold_C : !U(S ⊸ C[S/X]) ⊸ !U(S ⊸ νX. C)
  ```

  Instances at a row:

  ```
  Loop_Σ A B  ≜  νX. F_Σ(A ⊕ U X) & F_Σ B                       (an effectful loop)
  Aff^c_Σ A B ≜  νX. (A ⊸ F_Σ(B ⊗ [@c] U X)) & F_Σ 1             (the effectful affine closure)
  ```

  `Aff^c_Σ A B`'s `close` observation is its destructor (SPEC §22): dropping the closure runs
  `close`, which may perform `Σ`. A stored generator is a `Loop_Σ`, observed step by step;
  shallow handling is observation (OQ-26).
- **Uses.** O-TY, K-FTY.
- **Today.** `nuIn`, `nuOut`, `unfoldN`, `Core/Fundamental.lean:331-339`; `CTy.loopEff`,
  `Core/Types.lean:1177`, positive by `loopEffBody_nuOk` (`:1272`); `affEffBody`, positive by
  `affEffBody_nuOk`, `Core/Aff.lean:155, 161` [Lean]; as built. The effectful affine closure's
  derived rules (`d_mk`, `d_callAff`, `d_close`, `d_callMut`, `Core/AffRules.lean:129-205`) are
  stated at the pure body `affBody` (`Core/Aff.lean:32`) only.
- **Slices.** Step 04 (none: in/out are typing rules on the same term); relation 05 (`cB` at an
  effectful leaf is `ewpTS`); laws 06 (L-DIV, L-YIELD); compat 07; lowering 08.
- **Depends on.** K-FTY.
- **Open.** OQ-7 (an effectful `close` is a finaliser at a row; under R-FINAB its row is
  `Σ^abort`); OQ-15; OQ-26; OQ-31 (positive `ν` is a cut-off). The `NuOk` leaf asks the operation
  types to be closed in type variables (`A.Cl 0 ∧ B.Cl 0`), not in lifetimes; whether every
  signature must be closed in lifetimes is OQ-35.
- **Obligation.** The derived rules of the affine closure at `Aff^c_Σ`: **mechanical** (the same
  derivations at `affEffBody`). The step most likely to be non-mechanical: `d_callMut` uses
  `withswap`, whose callee is pure (R-PURESWAP), so calling an effectful affine closure through
  `Mut` needs OQ-20 (b) or (c).

### K-DIV: divergence

- **Form.** Div is an effect, read as codata by default (OQ-15 (a)): a div function is

  ```
  A ⇒ div_Σ B   ≜   U(A ⊸ F_Σ(U(Loop_Σ B R)))          (R the residual, SPEC §14)
  ```

  and running a divergent computation is observing its loop. There is no divergence former,
  rule or relation clause: `div` is a reading of `Loop_Σ` (K-NU), and every run of a closed
  divergent program is safe, each observation terminating (SPEC §14 *The totality theorem*,
  §19 *Divergence*). `ewp` is total correctness (`∃ k', ARun …`, `Core/EffDefs.lean:36` [Lean]),
  read only at each observation.

  Under OQ-15 (b), div is a row entry `div ∈ Σ` read by the partial-correctness `ewpP_W`
  (05 D-EWPP, recorded as a defect in OQ-63); the statics then types a divergent computation at
  `F_{div ⊕ Σ} B` directly, and a handler around it by `[handle]`. The handler around a div
  computation, per observation and spanning observations, is K-HDIV (§9.2), written under both
  readings; it is in the calculus (U5), and its lift waits on OQ-67.
- **Uses.** K-NU, K-FTY.
- **Today.** SPEC Entry 13 (§14) and §19 *Divergence*; `CTy.loopEff`, `Core/Types.lean:1177`
  [Lean]; as built as codata.
- **Slices.** Laws 06 (L-DIV); 07 (T-TOTAL kept; adequacy for divergent programs); 08 (one state
  machine per body).
- **Depends on.** K-NU.
- **Open.** OQ-15 (the reading); OQ-67 (K-HDIV's obligation; R-HDIV defers the spanning form's
  lift: today a `with to_result { f(x) }` with `f` looping and raising is rejected for that reason,
  SPEC §21 *Open*); OQ-63 (under (b)).
- **Obligation.** Under (a), `HndLoopSpanCompat` (§9.2) at `W`: **unknown**. Under (b): **unknown**,
  `ewpP_W` (OQ-63) and `[handle]`'s compatibility at it.

---

## 8. The host

### K-HOST: host-provided outermost handlers and capabilities

- **Form.** A host operation is a pure persistent constant at its signature,
  `hostOp_o : !(A_o ⊸ F B_o)` (`Core/Fundamental.lean:160-161` [Lean]); opaque host types `opq k`
  are leaves with no rule (`Core/Types.lean:75`). I/O is a bundle of per-effect linear
  capabilities, ambient only in `main` (SPEC §11). In the effect calculus each host effect is a
  signature `E_host` whose implementation is a comodel with a host carrier: a K-CAP whose state is
  an `opq` value and whose co-operations are host operations. Allocation is an effect (U20): its
  construct is K-ALLOC (§9.5), in the calculus, presented as a capability by OQ-30's default (b');
  its kernel lift waits on OQ-68, and until then allocation stays the machine's oracle (SPEC §13),
  R-ALLOCORACLE, a restriction of the decided position. Externs and `unsafe` are outside the
  proofs.
- **Uses.** K-CAP, O-COMODEL.
- **Today.** Partly built: host operations and opaque types as above; the capability bundle in
  SPEC §11 *Capabilities*; no host effect is a `Sig` today.
- **Slices.** 05 (the host carrier's `Holds`, D-COMODEL); 07 (T-ADEQ for host programs); 08.
- **Depends on.** K-CAP.
- **Open.** OQ-30 (the presentation of allocation), OQ-68 (its obligations; R-ALLOCORACLE until
  then); OQ-19.
- **Obligation.** Restating host capabilities as K-CAP values over `opq`: **mechanical** for the
  typing; the step most likely to be non-mechanical is T-COMODEL at a host carrier, whose relation
  is the model `k.Holds` (SPEC §11 *The model*).

---

## 9. The full constructs behind named restrictions

00 §7.2 requires that a section state each construct in full and mark where a restriction
applies. The constructs below are the full forms behind every R id that narrows a construct of
this section or of 02: R-FO (§9.1), R-HDIV (§9.2), R-RETCARRIER (§9.3), R-NOBORANS (§9.4),
R-ALLOCORACLE (§9.5), R-NOROWVAR (§9.6), R-DEEP (§9.7), R-FINAB (§9.8), R-NOOWNERR (§9.9),
R-NOREL (§9.10), R-PURESWAP (§9.11), R-NOSELFROW (§9.12), R-PUREFOLD (§9.13), R-STATIC (§9.14)
and R-NONEGREC (§9.15). R-T1, R-MID, R-CLOSEDOP and R-EXACTQ restrict constructs written in full
in their own entries (K-BOR and D-STOP; K-HND, *Open*; K-BOR, *The full class*; 02 K-ROW).

Two of them, K-HDIV (§9.2) and K-ALLOC (§9.5), are constructs the user has decided (U5, U20):
they are **in the calculus**, and their restriction only defers their kernel lift until a proof
obligation is met (OQ-67, OQ-68, settled by proof). Every other construct below is **not
adopted**: its default restriction holds until its question is settled. Each is written with its
form, its typing, its step, its model clause, its law entries and its lowering class, so that
adopting it needs no further design; where a part cannot be written yet, the entry names the
boxed question that holds it.

### 9.1 K-SCOPE: scoped operations (not adopted; default R-FO; OQ-12, OQ-59)

- **Form.** A signature may carry scoped operations beside algebraic ones:

  ```
  sc_j : A_j ↠^{q_j} ⟨S_j⟩ B_j          parameter A_j, scope answer S_j, continuation arity B_j

  n:E ∈ Σ     sc_j : A_j ↠^{q_j} ⟨S_j⟩ B_j ∈ E     Δ; Γ₁ ⊢ V : A_j     Δ; Γ₂ ⊢ M : U(F_Σ S_j)
  ─────────────────────────────────────────────────────────────────────────────────────  [scope]
  Δ; Γ₁ ∘ Γ₂ ⊢ scope_{n,j}(V; M) : F_Σ B_j
  ```

  The scope `M` is delimited by the operation: its operations are not commuted out past
  `scope_{n,j}`, which is what separates `scope_{n,j}(V; M)` from `perform_{n,i}(V, M)` at a thunk
  parameter (02 K-SIG).
- **Step.** `scope_{n,j}(V; M) ≜ perform (n, (j, (V, M)))`: the machine is unchanged; `[op]` at the
  nearest `hnd_n` hands the clause the parameter, the scope thunk and `κ`.
- **Clause type.** At carrier `F_Σ R`: `!U(A_j ⊗ Scope_n(S_j) ⊗ K_{q_j}(B_j, Σ, R) ⊸ F_Σ R)`, where
  `Scope_n(S_j)` is the type at which the clause sees the scope. Whether `Scope_n(S_j)` is
  `U(F_{n:E ⊕ Σ} S_j)` (the scope unhandled, the clause handling it itself) or `U(F_Σ S'_j)` for a
  carrier-dependent `S'_j` (the scope already handled by `hnd_n`, with the handler's carrier
  threaded through its answer) is **OQ-59**; it cannot be specified yet.
- **Model clause.** The `opTable` entry of `sc_j` gains the scope's relation: the stop
  `K[perform (n, (j, (v, m)))]` is admitted when `v ∈ P_A`, `m ∈ 𝒱⟦U(F_Σ S_j)⟧_W` (the scope is in
  the relation at its own row), and the continuation owes `share` as at an algebraic operation.
- **Law (L-SCOPE, 06).** Write `sc_{n,j}(V; M; y. N) ≜ scope_{n,j}(V; M) to y. N`. It is algebraic
  in the continuation, not in the scope: for a plain `K` under L-ALG's graded side condition,
  `K[sc_{n,j}(V; M; y. N)] ≡ sc_{n,j}(V; M; y. K[N])`; and there is no law moving computation
  between the scope and the continuation: `scope_{n,j}(V; thunk(force M to z. P))` and
  `scope_{n,j}(V; M) to z. P` are different computations in general. The handler laws L-HRET,
  L-HFWD hold unchanged; L-HOP's form depends on OQ-59.
- **Lowering.** The operation lowers as K-OP: a resumption point of the state machine at the
  perform (L-HOP; L-SCOPE's algebraicity in the continuation is what lets the state hold `K`'s
  live variables), or a direct call when the clause resumes once in tail position (L-TAIL); the
  scope is a closure passed to the clause. How the clause runs the scope is OQ-59's.
- **Sources.** Lindley, Matache, Moss, Staton, Wu & Yang, ESOP 2024 [via #235, abstract]; the
  further sources are OQ-12's options, to be read.

### 9.2 K-HDIV: handling around a div computation (in the calculus, U5; reading OQ-15; lift OQ-67, default R-HDIV)

A handler around a div computation is in the calculus under both readings of OQ-15, per
observation and spanning observations. What is not yet proved is its compatibility (OQ-67).

**Under OQ-15 (a), div as codata.** A div computation is a value `l : U(Loop_Σ A B)`,
`Loop_Σ A B ≜ νX. F_Σ(A ⊕ U X) & F_Σ B` (K-NU).

*Per observation.* A handler handles every observation and re-wraps the rest:

```
hndLoop_n H : !U(U(Loop_{n:E ⊕ Σ} A B) ⊸ U(Loop_Σ A_H B_H))
hndLoop_n H ≜ unfold_{Loop_Σ A_H B_H} (λl. ⟨ hnd_n H_next (next l), hnd_n H_close (close l) ⟩)
```

where `H_next` is a model of `n:E` at carrier `F_Σ(A_H ⊕ U(Loop_{n:E⊕Σ} A B))` (its return clause
maps `inj₁ a` to the next output and `inj₂ l'` to the rest of the loop to be unfolded again) and
`H_close` a model at carrier `F_Σ B_H`.

*Spanning observations.* The handler's state, and any continuation captured in one observation and
resumed in the next, are carried in the unfold state:

```
hndLoopS_n H : !U(S ⊗ U(Loop_{n:E ⊕ Σ} A B) ⊸ U(Loop_Σ A_H B_H))
hndLoopS_n H ≜ unfold_{Loop_Σ A_H B_H} (λ(s, p). ⟨ step_H (s, p), stop_H (s, p) ⟩)

P ≜ μP. U(Loop_{n:E ⊕ Σ} A B) ⊕ K_q(B_op, Σ, A_H ⊕ (S ⊗ P))          the pending rest
```

`p : P` is either the rest of the loop or a continuation captured mid-observation; `step_H`
observes `l` under `hnd_n H_next`, or resumes the stored `κ`, and answers `inj₁ a_H` (an output,
`A_H = A ⊕ E_H` when a clause ends the whole loop with `E_H`) or `inj₂ (s', p')`. A deadline over
the whole loop is `S = I64` (read at each observation); a retry that restarts the loop keeps a
persistent generator `!U(S₀ ⊸ U(Loop_{n:E⊕Σ} A B))` and its seed in `S`. `P` is positive: `P`
occurs in the codomain of `κ`'s resume entry, not in a domain. Threading the state through a
state-passing carrier `S ⊸ F_Σ R` with `S` holding `κ` instead puts `S` in a domain inside `κ`'s
own type, the negative recursion of R-NONEGREC (§9.15, OQ-60); the form above avoids it by
threading the state through the observation's answer, the clauses reading `S` from their
parameter or from a lent cell (OQ-25 (b)).

- *Typing.* Derived from `[handle]`, `[unfold]`, `[nuIn]`, `roll` at `P`; no new rule.
- *Step.* None new.
- *Model clause.* The `ν` clause of D-REL at `W`, by coinduction, each observation an `ewp_W` at
  `opTable ⟦Σ⟧`; a stored `κ` in `S ⊗ P` is read at the world OQ-46 fixes and bounded as OQ-28
  bounds a stored continuation (K-GEN).
- *Law.* The coiteration law of L-DIV (a) with `hnd_n` inside each observation,
  `next (hndLoop_n H l) ≡ hnd_n H_next (next l) to x. map (hndLoop_n H) x`; at the spanning form,
  the same with `step_H`, and L-BETA/L-W at the stored `κ`.
- *Lowering.* One state machine per body (as K-NU), its state holding `S` and `P`; a stored `κ` is
  a state-machine value (L-BETA, L-W).

**Under OQ-15 (b), div as a row entry.** The signature `Div = {}` has no operations; its name
`div` in a row licenses unbounded recursion. One constant:

```
dead Γ
──────────────────────────────────────────────────────  [fix]
Δ; Γ ⊢ fix[C] : !U(!U(U C ⊸ C) ⊸ C)          C = F_{div ⊕ Σ} A  (or a record of such leaves)

⟨μ, fix (g)⟩ ↦ ⟨μ, g (thunk (fix g))⟩                                     [fix]
```

The relation at a row holding `div` is `ewpP_W` (05 D-EWPP): `wpTSD`'s every-run quantifier
(`Core/Demonic.lean:223`) with its conclusion ("every run continues to a value") replaced by
safety at every reachable configuration and, at every run that reaches a value or a stop, the post
in `Q` or in the table (partial correctness); a greatest fixed point over stops. It is a
second wp family beside `ewp_W`, recorded as a defect in OQ-63. A handler around a div computation,
spanning or not, is the ordinary `[handle]`, `div` passing outward (it has no operations to
forward), with `handle_compatC` re-proved at `ewpP_W`. Law: L-DIV (b), `K[⊥] ≡ ⊥` without `D_K`,
where `⊥` is a diverging computation (06 L-DIV). The observation of `≡` then observes divergence
(06 §1.2). Lowering: a loop; the handler is K-HND's `drive`.

- **Obligation.** Under (a): `def HndLoopSpanCompat : Prop` (OQ-67): `hndLoopS_n H` is in
  `𝒱⟦U(Loop_Σ A_H B_H)⟧_W` whenever `H_next`, `H_close` are `IsModel` at the observation carriers
  and `s` is in `𝒱⟦S⟧_W`; **unknown** at a stored `κ` (OQ-28, OQ-46), **mechanical** per
  observation (`hndLoop_n`, coinduction plus `ewp_handle`). Under (b): `handle_compatC` at
  `ewpP_W`, **unknown** (OQ-63).
- **Restriction.** R-HDIV: the kernel lift does not implement the spanning form until its
  obligation is proved (OQ-67's default). It restricts the decided position U5.

### 9.3 K-CARRIER: a handler into any computation type (not adopted; default R-RETCARRIER; OQ-37)

- **Form.** `[handle]` at a carrier `C`, any computation type:

  ```
  Δ; Γr ∋! ir : !U(A ⊸ C)      Δ; Γc ∋! ic : ⊗_{op_i ∈ E} H_i(C)      Δ; Γ₂ ⊢ e : F_{n:E ⊕ Σ} A
  ────────────────────────────────────────────────────────────────────  [handle_C]
  Δ; Γ ⊢ hnd_n (ir, ic) e : C

  H_i(C) ≜ !U(A_i ⊸ C)                              op_i abortive
  H_i(C) ≜ !U(A_i ⊗ K_{q_i}(B_i, C) ⊸ C)            otherwise
  K_lin(B, C) ≜ U((B ⊸ C) & ⊤)    K_aff(B, C) ≜ U((B ⊸ C) & C_1)    K_unr(B, C) ≜ !U((B ⊸ C) & C_1)
  ```

  `C_1`, the carrier's cancel answer, is defined by recursion on `C`:

  ```
  (F_Σ R)_1 = F_Σ 1      (A ⊸ C)_1 = A ⊸ C_1      (C & D)_1 = C_1 & D_1      ⊤_1 = ⊤
  (∀'x ⊏ c. C)_1 = ∀'x ⊏ c. C_1      (νX. C)_1 : not yet specified (OQ-37)
  ```

  At `C = S ⊸ F_Σ R`, the cancel entry consumes the state, so a cancelled state-passing handler's
  finalisers own the state's destruction.
- **Step.** As built: `[ret]`, `[op]`, `[unwind]` place no constraint on the carrier; `hnd_n H e`
  at `C = S ⊸ F_Σ R` runs under the frame `□ s` of its application, and `κ` captures up to `hnd_n`
  only (04 K-STEP).
- **Model clause.** D-MODEL with the target predicate `𝒞⟦C⟧_W` in place of
  `ewp_W(·)(opTable Tout) Qout`; T-MODEL's M1 (every computation type is a model) supplies it.
  `KapRel` at carrier `C` quantifies the resume entry into `𝒞⟦C⟧` and the cancel entry into
  `𝒞⟦C_1⟧`.
- **Law.** L-HRET, L-HOP, L-HFWD and L-HUNIQ unchanged in form at `C`.
- **Lowering.** At `C = S ⊸ F_Σ R`: a dispatched call per resume with the state passed as an
  argument, no closure allocated per operation (the encoding under R-RETCARRIER returns a closure
  per operation, the cost decision 56 records); at `C & D`, one code per component; law L-HOP at
  carrier `C`. The state-machine class is unchanged.
- **Obligation.** `ewp_handle` and `handle_compatC` at `C`: **unknown** (OQ-37).

### 9.4 K-BORANS: an answer that borrows the handler's state (not adopted; default R-NOBORANS; OQ-29)

- **Form.** Under OQ-3 (a), a handler site opens a lifetime `'h` (K-HND, *Open*), and its
  signature may answer a view at `'h`:

  ```
  op_i : A_i ↠^{q_i} Imm 'h T        'h the site's extent, bound by the site, free in no outer type
  ```

  The handler's state is a cell `s : Ref S` owned by the site for its extent; the clause of `op_i`
  answers `κ` with an immutable view of a part `T` of `S`, a `[TR]` 6.64 lend at `'h`. The answered
  part is frozen for the extent: the clause may not mutate it while any answer is live.
- **Typing.** `[handle]` at OQ-3 (a)'s body premise
  `Δ.extend h ⊓Δ; Γ₂ ⊢ e : F_{n:E['h] ⊕ Σ}(['h] A)`, with `'h` free in no outer row, `R` or `Γ₁`, so
  that no answer escapes the site.
- **Step.** None new: the view is a location; lends are ghost.
- **Model clause.** `P_B` at `Imm 'h T` is D-REL's `Imm` clause at the site's lifetime, read at
  `W`; the site's 6.64 frame is an `imm` entry of `σ` for the extent.
- **Law.** The H-laws unchanged; L-HIDE's unary half at the site.
- **Lowering.** As K-OP: the answer is a location, and the lend has no code (lends are ghost,
  04 §4); law L-HOP with L-HIDE's unary half.
- **What cannot be specified yet.** Whether the clause may mutate the answered part between
  answers, which needs `[TR]` 6.150 lifted to `ewp` at a resuming table (T-FRAME); this is part of
  OQ-29.

### 9.5 K-ALLOC: allocation as an effect (in the calculus, U20; presentation OQ-30; lift OQ-68, default R-ALLOCORACLE)

- **Form.** One signature per allocated type, instances per type under R-NOROWVAR:

  ```
  Alloc[T] = { new : T ↠^{lin} Ref T,   del : Ref T ↠^{lin} T }
  ```

  The host provides the outermost handler, whose clauses are the BoLo axioms `alloc` and `free`
  (`Core/Fundamental.lean:147-155`) resuming in tail position; an arena is a nested handler of
  `Alloc[T]` whose state is a lent block and whose `new` bumps an index in it.
- **Typing.** Under OQ-30 (b): `[perform]` at `Alloc[T]`; a function that allocates has
  `Alloc[T]` in its row, which colours it. Under OQ-30 (b'), the default: allocation is a
  capability over the heap (K-CAP with the host carrier), `Cap_h(Alloc[T], Heap)`, held in `Γ` and
  in no row, so it colours no function type; `new` and `del` are `[cap-call]`s.
- **Step.** None new: `perform` reaches the host handler (or the capability call reaches the host
  co-operation), whose clause takes the `alloc` or `free` step.
- **Model clause.** The entry `P_A = 𝒱⟦T⟧`, `P_B = 𝒱⟦Ref T⟧` (and the converse for `del`); the host
  handler meets it by the `alloc` compatibility (`[TR]` 6.165), and the host co-operation meets
  `IsComodel` by the same lemma.
- **Law.** L-TAIL at the host handler (its clauses are tail-resumptive), so the lowering is a
  direct call; an arena handler's laws are L-HRET/L-HOP at its clauses; under (b') L-RUN.
- **Lowering.** The allocator call (L-TAIL); an arena's `new` a bump (L-HOP at its clause).
- **Obligation.** The host handler as a model: **mechanical** from 6.165, 6.166. Arenas:
  **unknown**, the frame of a lent block across `new` (T-FRAME). Both are OQ-68.
- **Restriction.** R-ALLOCORACLE: the kernel lift keeps allocation as the machine's oracle until
  OQ-68's obligations are proved. It restricts the decided position U20.

### 9.6 K-ROWABS: row abstraction (not adopted; default R-NOROWVAR; OQ-13 (b))

- **Form.** Row variables `r` and rows with a variable tail; a computation type abstracting a row
  disjoint from a set of names `N`:

  ```
  Σ ::= … | r ⊕ Σ                 C ::= … | ∀r # N. C

  Δ; Ξ, r # N; Γ ⊢ M : C      r ∉ fv(Γ)                   Δ; Ξ; Γ ⊢ M : ∀r # N. C     Ξ ⊢ Σ' row     names(Σ') ∩ N = ∅
  ──────────────────────────────────  [rowI]          ──────────────────────────────────────────────────────────  [rowE]
  Δ; Ξ; Γ ⊢ Λr. M : ∀r # N. C                         Δ; Ξ; Γ ⊢ M [Σ'] : C[Σ'/r]
  ```

  `Ξ` is the row-variable context. `Λr. M ≜ λ_. M` and `M [Σ'] ≜ M ()`, as lifetime abstraction is
  (`allI`, `allE`, `Core/Fundamental.lean:116-122`): rows are erased from terms. A row-generic
  value `U(∀r # N. C)` may be stored, passed and instantiated later, and a recursion may
  instantiate its own type at another row (polymorphic recursion across rows), which a meta-index
  cannot express (R-NOROWVAR).
- **Step.** `beta` at `M ()`; nothing new.
- **Model clause.** The relation takes a row environment `θ : RowVar → OpTab` beside `δ`, with
  `⟦r ⊕ Σ⟧(δ, θ) = θ(r) ⊕ ⟦Σ⟧δ` (T-SUMOK's `⊕`):

  ```
  𝒞⟦∀r # N. C⟧_W (δ, θ) e  =  ∀ T : OpTab.  dom T ∩ N = ∅  →  Mono-able T  →  𝒞⟦C⟧_W (δ, θ[r ↦ T]) (e ())
  ```

  quantifying over semantic tables, not over syntactic rows, so that the clause stays structural
  on the type (T-DEF): a table is data quantified to the left, as `W'` is. `[rowE]` is sound
  because every syntactic row's `⟦Σ'⟧` is such a table. Which predicate the quantified tables must
  meet (`Mono-able`: monotone in `Φ`, and `TableOK` where the abstraction is a borrow callback's
  row) is part of OQ-13.
- **Laws.** β `(Λr. M) [Σ'] ≡ M[Σ'/r]`, η `Λr. M [r] ≡ M`; L-NAH's parametric form: a function at
  `∀r # N. C` forwards `r`'s operations, unary because its relation holds at every `T`. The
  binary form (parametricity in `r`, T-ABS) waits on OQ-4.
- **Lowering.** A row-generic body cannot be specialised by static masks (`masks`,
  `Backend/Clos/Capture.lean:984-996`): either one state machine per body, uniform in the row (any
  call may suspend), or one copy per instantiation (monomorphisation, as R-NOROWVAR's copies);
  which, under cost parity, is part of OQ-13.
- **What cannot be specified yet.** Instance abstraction (the TR's `Π`, abstracting names inside a
  row) and its interaction with static names (OQ-14); the predicate on quantified tables.
- **Obligation.** `rowI_compatC`, `rowE_compatC` at `W`: **unknown**.

### 9.7 K-SHALLOW: shallow handlers (not adopted; default R-DEEP; OQ-26 (b))

- **Form.**

  ```
  Γ = Γ₁ ∘ Γ₂      Γ₁ = Γr ∘ Γc      n ≠ ⊥      n ∉ names(Σ)
  Δ; Γr ∋! ir : !U(A ⊸ F_Σ R)      Δ; Γc ∋! ic : ⊗_{op_i ∈ E} H†_i      Δ; Γ₂ ⊢ e : F_{n:E ⊕ Σ} A
  ──────────────────────────────────────────────────────────────────────  [handle†]
  Δ; Γ ⊢ hnd†_n (ir, ic) e : F_Σ R

  H†_i ≜ !U(A_i ⊸ F_Σ R)                                   op_i abortive
  H†_i ≜ !U(A_i ⊗ K_{q_i}(B_i, n:E ⊕ Σ, A) ⊸ F_Σ R)         otherwise
  ```

  The continuation does not reinstall the handler: it answers the body's own type
  `F_{n:E ⊕ Σ} A`, and its further operations of `n` reach whatever handler of `n` the clause
  places around it.
- **Step.**

  ```
     clauseAt hs i = c      ¬HasHnd n K
  ──────────────────────────────────────────────────  [op†]
   ⟨μ, hnd†_n H K[perform_{n,i} v]⟩ ↦ ⟨μ, c (v, κ†(K))⟩

  κ†(K) ≜ ⟨ λy. K[y],  ccatch (K[raise (⊥, (hndNames K, none))]) ⟩
  ```

  `[ret]` and `[unwind]` as for `hnd`.
- **Model clause.** `IsModel†`: D-MODEL with `KapRel†` in place of `KapRel`, whose resume entry
  quantifies into `𝒞⟦F_{n:E ⊕ Σ} A⟧_W` (the body's relation at its own row) and whose cancel entry
  into `owed` at the body's row.
- **Laws.** L-HRET unchanged; L-HOP† `hnd†_n H (K[perform_{n,i} V]) ≡ c_i (V, κ†(K))` with
  `resume κ†(K) w ≡ K[w]`; L-HFWD unchanged. Deep from shallow:
  `hnd_n H M ≡ fix(λh. hnd†_n H[h]) M`, `H[h]` the clauses with `resume κ† w` replaced by
  `h (resume κ† w)`; the recursion is unbounded, so this law is stated under OQ-15 (b) or with a
  budget (K-FIX), part of OQ-26.
- **Lowering.** A state machine whose `κ†` holds the captured frames without the handler frame.
- **Obligation.** `handle†_compatC` at `W`: **unknown** (`KapRel†` at `W`).

### 9.8 K-FINR: finalisers and unwinding forms at a resuming row (not adopted; default R-FINAB; OQ-7 (a))

- **Form.** K-THEN with `Σ^fin = Σ`: the finaliser may perform every operation of the row,
  resuming ones included, handled outside the region:

  ```
  Δ; ⟨1, dead⟩ :: Γ₂ ⊢ D : F_Σ 1        (in place of F_{Σ^abort} 1)
  ```

  and, with it, K-BOR's unwinding form with `d : src_k ⊸ F_Σ 1`, K-SWAP's unwinding form, and the
  effectful `Aff`'s `close` at `F_Σ 1`.
- **Step.** Unchanged: `[finalise]`, `[finalise-cancel]` run `D` under `cfin` (04 K-STEP). A
  finaliser that stops at a resuming operation during a cancel is captured with the `ccatch` and
  `cfin` frames in its context; cancelling that capture is OQ-41.
- **Model clause.** D-DTOR at every `TableOK` table: the cancel run's table admits, besides the
  cancel, the stops of names outside the region at resuming entries,
  `cancelTab⁺ T N ≜ cancelTab T N ∨ opTable (T ∖ N)`, with the cancel run's rest as the continuation
  owed.
- **Laws.** L-W at every table, `cancel κ ≡ D_K ▷ return ()` (06 O-FIN's sequential form) with
  finalisers that perform; L-ALG0 unchanged; L-ALG at finaliser frames (OQ-65).
- **Lowering.** A finaliser that may suspend makes the state machine's cancel arm itself
  resumable: the cancel arm becomes a state machine (`MEnv.cancelArm`,
  `Backend/Clos/Capture.lean:893`, extended); **unknown** as a lowering obligation.
- **What cannot be specified yet.** The cancel error policy at a finaliser that suspends (OQ-21)
  and the delimiting of a cancel captured inside a cancel run (OQ-41).
- **Obligation.** `then_compatC` at a resuming `D`: **unknown** (T-FRAME at a resuming table).

### 9.9 K-OWNERR: an abortive payload that owns (not adopted; default R-NOOWNERR; OQ-24 (b))

- **Form.** `[raise]` without `Drop A_i`:

  ```
  n : E ∈ Σ      op_i : A_i ↠^q 0 ∈ E      q ∈ {aff, unr}      Δ; Γ ⊢ V : A_i
  ───────────────────────────────────────────────────────────────  [raise⁺]
  Δ; Γ ⊢ raise_{n,i} V : F_Σ B
  ```

  and K-SIG's `[sig]` without its premise `op_i abortive ⟹ Drop(A_i)`.
- **Step.** Unchanged: `[finalise]` runs each finaliser before the raise moves on; `[unwind]`
  delivers `v` to the clause. The payload's resources are disjoint from `K`'s by linearity, so the
  finalisers never free them.
- **Model clause.** D-OPTAB's abortive half with `en.P_A(ls, σ) v` owning, and `NoOwn` only of the
  abandoned rest: `⌜…⌝ ⋆ en.P_A(ls, σ) v ⋆ NoOwn`.
- **Laws.** L-EXC (E3) delivers the payload after the finalisers: `hnd_n H (K[raise_{n,i} V]) ≡
  D_K ▷ c_i V`; L-ALG0 unchanged.
- **Lowering.** The payload variant holds an owned value (`wrapRaise`,
  `Backend/Clos/Capture.lean:136`); branch class.
- **What cannot be specified yet.** The cancel error policy suppresses all but the first error
  outside the region (SPEC §19 *Cancels*); a suppressed error with an owned payload would leak.
  What the policy does with an owned payload is part of OQ-24 with OQ-21.
- **Obligation.** `raise_compatC` at an owned payload: **unknown**.

### 9.10 K-RELQ: the relevant qualifier (not adopted; default R-NOREL; OQ-17 (b))

- **Form.** A qualifier `rel = [1, ∞]` (O-QUAL) and its continuation type:

  ```
  K_rel(B, Σ, R) ≜ !_{[1,∞]} U((B ⊸ F_Σ R) & ⊤)
  ```

  with `!_{[1,∞]}` the graded `!` at grade `[1, ∞]` (`experiments/Grades`, `Grade`,
  `Algebra.lean:58`): copy (contraction) and no forget. The cancel entry is `⊤`, since a relevant
  `κ` may not be dropped. `[let]`'s side condition at `g ∋ rel`: `hi g = ∞ ⇒ Γ₂` contractible
  (persistent, or itself under `!_{[1,∞]}`), and no `Drops` premise since `lo g = 1`.
- **Step.** None new.
- **Model clause.** `KapRel` at `rel`: the resource empty (copies), resume entry as at `lin`.
- **Laws.** L-P at `rel`; L-C does not apply; a choice handler that takes both branches needs only
  `rel` (L-ND), one that may take neither needs `aff`/`unr`.
- **Lowering.** The copy class (T-LOWER).
- **What cannot be specified yet.** Whether `!_{[1,∞]}` is the kernel's `!` graded (one former) or a
  second modality, which C-9 would report as a defect; part of OQ-17.
- **Obligation.** **Unknown**.

### 9.11 K-SWAPΣ: a co-operation whose callee performs (not adopted; default R-PURESWAP; OQ-20 (b), (c))

- **Form (c), the printed constant at a row.**

  ```
  withswap[Σ] : Mut @a A ⊸ U(A ⊸ F_Σ(A ⊗ B)) ⊸ F_Σ(Mut @a A ⊗ B)
  premise:  ¬Σ.Weak,  or  Σ.Weak ⇒ a restore value  r : U(F_{Σ^fin} A)  put back on an abortive stop
  ```

- **Form (b), the placeholder shape, as a derived term.** The cell holds `1 ⊕ A`, and the payload
  is taken out and put back by two calls of the printed pure `withswap`:

  ```
  withtake m f ≜ withswap m (λx. (inj₁ (), x)) to (m, x).
                 case x { inj₁ () ↦ … ; inj₂ a ↦ force f a to (a', b). withswap m (λx'. (inj₂ a', x')) to (m, old). return (m, b) }
  ```

  The second call hands back the displaced content `old`, which is `inj₁ ()` by the protocol and
  is dropped by its case; the `inj₁ ()` branch of the first `case` is the cell found empty. So (b)
  adds no constant: it is a term over the printed `withswap` [I], and C-6 holds. Its cost is
  that the `Mut` view `m` is held across the callee's stops while the cell holds `inj₁ ()`.
- **Step.** Under (c), the printed `withswap` steps (load, call, store) with the callee's run in
  between; a stop in the callee is a stop with the payload out of the cell. Under (b), the steps of
  the derived term.
- **Model clause.** Under (c): `[TR]` 6.66 (AntiFrame) at the cell, lifted to `ewp_W` at
  `opTable ⟦Σ⟧` (T-FRAME's 6.66 half at a resuming table): the open anti-frame at a stop is handed
  on in `τ'` as a `mut` entry (OQ-44). `IsComodel` at `Σ' ≠ ∅` is D-COMODEL as written. Under (b):
  D-REL's `Mut` clause at payload predicate `𝒱⟦1 ⊕ A⟧`, with the view `m` across a stop a lend
  spanning a stop (R-T1, OQ-9, OQ-44).
- **Laws.** L-STATE (S1), (S2) with effectful `f`, `g` (sequencing, L-TO); L-RUN at `Σ' ≠ ∅`;
  L-TENSOR only for transformers whose rows commute (L-COMMUTE, OQ-64). Under (b), a read while
  the payload is out answers `inj₁ ()`.
- **Lowering.** A capability call that may suspend: a resumption point at the call site, the
  payload held in the state.
- **Obligation.** **Unknown** under both: the frame of a `mut` cell whose payload is out across a
  stop of the callee.

### 9.12 K-SELFROW: operation types that perform their own effect (not adopted; default R-NOSELFROW; OQ-61 (b))

- **Form.** A signature binder in parameters, occurring only positively:

  ```
  E = μe. { op_i : A_i[e] ↠^{q_i} B_i }        e only in parameters, only inside U(F_{n:e ⊕ Σ'} A')

  Δ; e sig ⊢ { op_i : A_i[e] ↠^{q_i} B_i } sig      Pos_e(A_i) for every i      e ∉ B_i
  ────────────────────────────────────────────────────────────────  [sig-μ]
  Δ ⊢ μe. { op_i : A_i[e] ↠^{q_i} B_i } sig
  ```

  `Async[Σ] = μe. { suspend : 1 ↠^{aff} 1, spawn : U(F_{n:e ⊕ Σ} 1) ↠^{lin} 1 }` is an instance.
  `[perform]` reads `A_i` with `e` unfolded to `μe. E`.
- **Step.** None new: the parameter is a thunk passed to the clause.
- **Interpretation and model clause.** `⟦n:μe.E ⊕ Σ⟧δ ≜ lfp (λT. ⟦n:E[T/e] ⊕ Σ⟧δ)`, the least
  fixed point of the table functional, tables ordered pointwise by `P_A` inclusion with `q`,
  `abort` and `P_B` fixed. The functional is monotone because `e` occurs only in `P_A`, which enters
  `opTable` positively, and inside `𝒱⟦U(F_{T ⊕ Σ'} A')⟧`, which reads `ewp` at `opTable T`
  positively (`ewp_mono` in the table, `Core/EffWp.lean:795`; `opTable_mono`, `:951`). The fixed
  point is taken over tables, outside the type recursion, so the relation stays structural on the
  type (T-DEF). The settling statement:

  ```lean
  /-- OQ-61 (b): a positively self-referential signature has a least table, which is TableOK. -/
  def SelfRowPositiveLFP : Prop :=
    ∀ (E : SigBody) (n : Nm) (Σ : Row) (δ : LSub), PositiveInParams E →
      Monotone (tabFun E n Σ δ) ∧ TableOK (opTable (lfpTab (tabFun E n Σ δ)))
  ```

  (`SigBody`, `PositiveInParams`, `tabFun`, `lfpTab` are names the settling experiment defines.)
- **Laws.** The H-laws unchanged; L-ASYNC (A3) at `spawn`.
- **Lowering.** None new: a thunk parameter is a closure.
- **What cannot be specified yet.** Occurrences in answers (negative, OQ-61 (c)); reference by name
  (OQ-61 (d)).
- **Obligation.** **Unknown** (`SelfRowPositiveLFP`).

### 9.13 K-FOLDΣ: folds and counted loops at a row (not adopted; default R-PUREFOLD; OQ-62 (b))

- **Form.** Each structural recursion constant at a callback row `Σ`:

  ```
  foldImm[Σ]   : !U(∀'y ⊏ ⊤. A_R ⊸ F_Σ R) ⊸ !U(∀'y ⊏ @c. Imm 'y (μX. T) ⊸ F_Σ R)     BorOK_y Σ  (R-CLOSEDOP, R-T1)
  foldOwn[Σ]   : !U(A′_R ⊸ F_Σ R) ⊸ !U(μX. T ⊸ F_Σ R)
  foldReuse[Σ] : !U(A″_R ⊸ F_Σ R) ⊸ !U(μX. T ⊸ F_Σ R)
  countFold[Σ] : !U(!U(I32 ⊗ S ⊸ F_Σ S) ⊗ (I32 ⊗ (I32 ⊗ S)) ⊸ F_Σ S)
  countTry[Σ]  : !U(!U(I32 ⊗ S ⊸ F_Σ(S ⊕ E)) ⊗ (I32 ⊗ (I32 ⊗ S)) ⊸ F_Σ(S ⊕ E))
  ```

  with the side conditions of today's rules (`Core/Fundamental.lean:183-191, 311-327`) unchanged.
  At `Σ = ∅` these are today's constants. Resuming operations inside the step are admitted (a
  `yield` from a traversal); `foldImm[Σ]`'s algebra runs under the `Imm 'y` lend, so it is a borrow
  callback that performs and its row is restricted as K-BOR's is.
- **Step.** The folds are λ-terms (`foldImmV`, `Core/FoldImm.lean:154`; `foldOwnV`,
  `Core/FoldOwn.lean:102`), so at a row they run as ordinary terms, each recursive level a `[let]`
  frame at `Σ`; `count` is the head step `Head.count` (`Core/CountFold.lean:10`), its next
  iteration under a plain frame. Stops propagate through these frames as through any plain frame.
- **Model clause.** Each level an `ewp_W` at `opTable ⟦Σ⟧`: compatibility by induction on the
  structure (folds) or on the count (loops), each level by `ewp_bind`. `foldImm[Σ]` additionally
  needs `TableOK_y ⟦Σ⟧` (D-TABLEOK) and T-FRAME's 6.64 half at a resuming row (the lend open across
  the algebra's stop, OQ-9).
- **Laws (L-FOLD).** Fold β at a row,
  `fold[Σ] alg (roll v) ≡ map_T (fold[Σ] alg) v to w. alg w` (the pattern of `fold_beta`,
  `experiments/CoeffectsStrict/CoeffectsStrict/Fold.lean:76`); count β,
  `countFold[Σ](f, (n, (i, s))) ≡ if i < n then f (i, s) to s'. countFold[Σ](f, (n, (i+1, s'))) else return s`;
  fold uniqueness at a row (the pattern of `fold_unique`, `Fold.lean:207`), binary (OQ-4); L-ALG
  through each level's frame.
- **Lowering.** When the step may suspend, the traversal's pending levels are held in the state
  machine (an explicit frame buffer, as the heap driver's `Loop`, 08 §5.1 schema D); otherwise the
  fold's ordinary code. Cost parity against a hand-written effectful traversal.
- **Obligation.** At abortive rows: **mechanical** (the `*U` frames). At resuming rows:
  **unknown** (`foldImm[Σ]` with OQ-9; the others by induction with `ewp_bind`, the step most likely
  non-mechanical being `count`'s head step under a captured context).

### 9.14 K-GENNAME: generative instances (not adopted; default R-STATIC; OQ-14 (b))

The full construct is K-NAME's (02 K-NAME, *Generative instances*): `hnd_ν (n, H) e` with the step
`(μ, hnd_ν (n, H) e) ↦ (μ, hnd (m, H) (m/n)·e)`, `m` fresh, typed as `[handle]`; its laws are L-NU
(06), at `lin` and `aff`. What cannot be specified yet: the model clause, since a fresh name is a
nominal resource that a continuation escaping its handler can meet reused (the stale-label
configuration OQ-14 asks for), and the lowering, since a fresh name per activation needs a
run-time mask (OQ-42 (a)). Recursion through a site needs it. Obligation: **unknown**.

### 9.15 K-NEGREC: the construct R-NONEGREC excludes (not adopted; OQ-31 (b))

Stated so that the exclusion is named, not silent. The excluded forms:

- a handler whose carrier stores or returns its own continuations in a negative position: carrier
  `C` with `K_q(B, C)` occurring in a domain of `C`, e.g. `C = S ⊸ F_Σ R` with `S` holding
  `K_q(B, C)` (the deep-handler scheduler of OQ-60 (a));
- `μ`/`ν` types with the bound variable in a domain;
- recursion with no budget at a row that is not `div`;
- operation types whose answers mention their own signature (OQ-61 (c)).

Typing: each is a well-formed type or term once the positivity premise is dropped. Step: none new.
Laws: the H-laws in form unchanged. Model clause: needs a recursive domain or step-indexing
(TR §16.5); without step-indexing (00 §0.2 item 2) it is not specified, which is why OQ-31's (b) is
listed only for the user to see. Lowering: a state machine whose state stores continuations, as
for any stored `κ`.

---

## 10. Open questions raised by this section

Boxed in [99](99-open-questions.md): OQ-40 (the syntactic row class `BorOK_x Σ` of a borrow
callback, whose interpretation is `TableOK_x`; default: the full class `Σ.NZ`, which with R-T1 and
R-CLOSEDOP imposed is today's `Row.Unwind x`); OQ-56 (operation types that mention the lend,
default R-CLOSEDOP); OQ-59 (how a handler reaches into a scope, §9.1); OQ-61 (operation types that
perform their own effect, §9.12); OQ-62 (folds and counted loops at a row, §9.13); OQ-67 and OQ-68
(the proof obligations of K-HDIV and K-ALLOC, §9.2, §9.5). OQ-35 (whether operation
types are closed in lifetimes) is shared with 02.

---

## 11. Run-up audit (CLAUDE.md §5)

- **Printed lemmas in the run-up not transcribed to the effect layer.** `[TR]` 6.150 (reborrow)
  is not lifted to `ewp` (T-FRAME), and `bor_withload[Σ]` at a resuming row needs it (6.175);
  `bor_withbor3[Σ]` follows 6.174 through 6.66, 6.60 and 6.65 and does not. `[TR]` 6.64,
  6.65, 6.66 are lifted at abortive tables only in Core (`Core/EffWp.lean:828-854`); the
  resuming halves are in `experiments/GhostEnd`. Every printed typing rule of `[TR]` p. 2 and
  every axiom of p. 3 is transcribed (`Core/Fundamental.lean:60-294`, `Core/Types.lean:1868-1907`).
- **Printed hypotheses not spent here.** `withbor1`'s `VScoped Δ A` (`hsc₁`) has no counterpart at
  `withbor2`/`withbor3`; K-BOR carries it in `side_k` unchanged. `effHandle`'s `hlen : E.length ≤
  2^32` is a representation bound (UInt32 operation indices), not a typing condition.
- **Uniqueness and functionality results not used.** `Row.find_of_mem`
  (`Core/EffRules.lean:748`, uniqueness of a row's keys) is used at `[then]` (through
  `Row.abortOnly_le`, `:760`) and not at `[handle]`; with K-ROW's sums it applies to every row. `head_det_eff` (`Core/Steps.lean:596`)
  is a dynamics fact the statics does not use.

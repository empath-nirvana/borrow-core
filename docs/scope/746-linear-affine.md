# #746 scope: unrestricted, affine and linear as Core predicates

Phase 1 of #746: the scope document the user reviews before any code changes. It covers items 2
(one vocabulary) and 3 (declared linear types) of the issue. Item 1 (removing binder `linear`) is
listed here because item 2 decides what replaces it. Items 4 (the gate step) and 5 (audit F3) are
out of scope apart from a pointer in section 8.

The rule this serves (user):

> "Affine and linear in the surface need to literally mean that they are affine or linear in the
> kernel, end of story." "Either it is a linear type or it is not and if it's not we need to call
> it something else."

Everything below was read at `origin/main` b566c459. The small facts marked *(probe)* were checked
in Lean against that build, in `~/repos/scratch-archive/linear-types/probes/Probe746.lean`
(`lake env lean` from this worktree, no errors).

---

## 0. Summary

- **The kernel's structural rules exist only at persistent types.** `CDerives` has contraction
  (`Ctx.SplitP.dup`) and weakening (`Ctx.DeadP.drop`, `Ctx.SoloP.skip`) at `VTy.Persistent` and
  nowhere else. Every other type is linear *as a rule of the judgment*. "Affine" can therefore
  only mean that weakening is **admissible**, a derived rule proved in Core. `drop_derives` is
  that derived rule today.
- **Proposal.** Each structural rule gets one Core predicate: `Weak A` (weakening admissible) and
  `Contr A` (contraction admissible). The three words are the quadrants, as in §19's own table:
  unrestricted = `Weak ∧ Contr`, affine = `Weak ∧ ¬Contr`, linear = `¬Weak ∧ ¬Contr`. Relevant
  (`Contr ∧ ¬Weak`) is empty, and that is a theorem.
- **Today Core has at least four notions with "affine" or "drop" in their meaning, and they do not
  agree.** `Records.Affine` (forget-only), `HasDtor` (a derived destructor), `VTy.Drop` (holds no
  `own` cell, so an abort may abandon it), and the `aff` qualifier of §19 (consumed by a cancel
  at a row). Section 2.3 maps each one onto the proposal or renames it.
- **Three design points cannot be settled from #746 or the rule** (section 7): whether weakening
  that has an effect counts (Q1), whether an abort's abandonment counts as weakening (Q2, which
  decides whether opaque host types are linear), and contraction at `Imm` (Q3). Declared linear
  types (Q4, Q5) need a decision on how strong the kernel's guarantee must be.
- **Checker:** `dtorB_sound` gets a converse, `dtorB_complete`, so `hasDtorB A = true ↔ HasDtor A`.
  `Class.of` (Tir) then provably computes the three predicates (section 3).

---

## 1. Inventory

Each row says what the word actually means there, as a Core predicate or as "surface-only". The
predicates named are today's: `P` = `VTy.Persistent`, `D` = `HasDtor`, `F` = `Records.Affine`
(renamed `Forgettable` below), `N` = `VTy.Drop` (holds no `own` cell).

### 1.1 Core

| site | name | meaning | as a predicate |
|---|---|---|---|
| `Core/Persistent.lean` `VTy.persistent`, `VTy.Persistent` | persistent | values hold only `∅` (`vP_empty_of_persistent`); contraction and weakening are rules (`SplitP.dup`, `DeadP.drop`, `SoloP.skip`) | `P` |
| `Core/Relation.lean:250` `Persistent (Γ : Ctx VTy)` | persistent (a context) | every live slot is at `!A`: the promotion premise of `bangThunkF/V`, and `[let]`'s `S.Unr → Persistent Γ₂` | **not** `∀ slot, P`. It is "all banged". SPEC §10 *Open* already says it is not widened. Same word, different predicate |
| `Core/Records.lean:288` `Affine`, `dropT` | affine | a closed **no-op** consumer exists (`forget`, componentwise): `1 0 ⊗ ⊕ Imm Mut Unk ! Int` | `F`; `F ⊆ D` (`hasDtor_of_affine`). Includes persistent types, so it is not "affine" in the quadrant sense. It is "forgettable" |
| `Core/Records.lean` `getAt_wf`, `loadField_wf`, `affine_immReborrow`, `affine_valTy`; `Core/RecordPrograms.lean` | affine | the fields a projection discards must be `F`, because `getAt` drops them with no action | `F` |
| `Core/Dtor.lean:402` `HasDtor`, `dtorE`, `dtor_wf`, `drop_derives` | destructor | a closed pure term `dtorE A : A ⊸ F 1` exists; it may free, fold or run `close` | `D` |
| `Core/Dtor.lean:448` `hasDtor_of_affine` | affine | `F → D` | |
| `Core/EffRules.lean:1041` `VTy.Drop`, `Ctx.Drops`, `vC_noOwn_of_drop` | drop | the value holds no `own` cell, so an abort may abandon it: `[let]` at a row with weakening needs `Γ₂.Drops`, `[raise]` needs its argument `Drop` | `N`. `N = F + opq`: same constructors as `F`, plus `.opq k`. **Not** a destructor notion |
| `Core/Types.lean:37` `Qual` (`lin`, `aff`, `unr`); `Core/EffRules.lean:1146` `kTy` | linear, affine, unrestricted | κ at `lin` is `U((B ⊸ F_Σ R) & ⊤)`, at `aff` `U((B ⊸ F_Σ R) & cancelTy Σ F)`, at `unr` the `!` of that | `lin`: `¬P ∧ ¬D` *(probe)*. `unr`: `P` *(probe)*. `aff`: **`D` exactly when `Σ = ∅` and the cancel row is empty** *(probe: `HasDtor (kTy [] R .aff B)` by `.close`)*; at a non-empty row, `¬P ∧ ¬D` *(probe, at a `Fail` row)*. Its cancel performs at the row |
| `Core/EffRules.lean:957` `Row.Weak`, `Row.Unr`, `Row.UnrD` | weak, unrestricted (a row) | the row has an operation whose κ may be dropped or copied | qualifier of the row's operations, not of a type |
| `Core/Types.lean:161` `capB` | capturable | `q ≠ lin ∧ B ≠ 0` | qualifier |
| `Core/Aff.lean` `affT`, `hasDtor_aff`, `not_affine_aff`, `not_persistent_aff`, `not_hasDtor_lolli`; `Core/AffRules.lean` "Affine ≤ linear" | affine closure, linear function | `Aff^c A B` is `D ∧ ¬P ∧ ¬F`; `U(A ⊸ F B)` is `¬D ∧ ¬P` | affine closure: `D`. Linear function: `¬D ∧ ¬P`. The effectful affine closure `νX. (A ⊸ F_Σ(…)) & F_Σ 1` is not `D` (`HasDtor.nu` asks for `ret R`) |
| `Core/Rejections.lean:98` `not_forget_kappa` | | `forget κ` has no derivation at `kTy lin/aff` | |
| `Core/Fundamental.lean` `copy`, `copyBang`, `forgetImm/Mut/Unk`, `forgetBang`, `arrCopy`, `arrForget` | (axioms) | contraction by a term at `Imm` (`copy`), `ArrayImm`, `!A`; weakening by a term at `Imm`, `Mut`, `Unk`, `!A`, `ArrayImm` | derived contraction at `Imm` is the Q3 question |
| SPEC §25 capture cell | linear, affine | a `lin`/`aff` κ owns a unit `own` cell, so leak freedom sees a dropped κ | semantic content of "used exactly once" for κ |

### 1.2 Checker and elaborator

| site | name | meaning | as a predicate |
|---|---|---|---|
| `Frontend/Check/Steps.lean:56` `dtorB`, `:139` `dtorB_sound`, `:300` `hasDtorB` | destructor | decides `D`, one direction proved | `D` (soundness only) |
| `Frontend/Check/Decide.lean:748` `dropB`, `dropB_sound` | drop | decides `N`, one direction proved | `N` (soundness only) |
| `Frontend/Check/Steps.lean:577` `Env.pushOwn`, `Env.own` | owed | `own := !lin && !A.persistent && hasDtorB A` | `¬P ∧ D ∧ ¬lin`. Without `lin`: `¬P ∧ D`, which is "affine" in the proposal |
| `Steps.lean:573` `Env.push` | not owed | dead binder, "or `linear`" | surface-only (the `lin` flag) |
| `Steps.lean:514` `unconsumed`, `:547` `popL` (`lin` param) | linear | error text for the `lin` flag | surface-only |
| `Steps.lean:864` `effBind` (`lin` param, `dropB A && (!Row.unrB S \|\| isBangB A)`) | | `[let]` vs `[then]` choice at a row | reads `N` and "banged", passes `lin` to `popL` |
| `Steps.lean:805` `finalOf` | no destructor | a non-persistent slot live across an abortive computation needs `D` | `D` |
| `Frontend/Elab/Tir.lean:33` `Class` (`persistent`, `dtor`, `linear`), `Class.of` | persistent, destructor, linear | `P` / `¬P ∧ D` / `¬P ∧ ¬D` | the three proposed classes under Q3 option U1 |
| `Frontend/Sugar.lean:539` `isLinear` | linear | `Class.of A == .linear` (residual of a div body) | `¬P ∧ ¬D` |
| `Frontend/Check/Kinds.lean:297` `qualWord`; `Elab/Effects.lean:3886` | linear, affine, unrestricted | `Qual` | qualifier |
| `Frontend/Check/Copies.lean` (§10) | persistent | implicit copy only at `P` | `P` |
| `Frontend/Check/Consts.lean:146` | destructor | finaliser source needs `D` and an effect-free `dtorE` | `D` |

### 1.3 Backend

| site | name | meaning |
|---|---|---|
| `Backend2/Lint.lean:61` `copyable` | copy | `persistent ∨ imm ∨ fam imm`, rebuilt on LIR types |
| `Backend2/Lint.lean:70` `droppable`, `Backend2/Types.lean:356` `LTy.drops` | drop | `persistent ∨ drops ∨ fam borrows`, rebuilt on LIR types: `N`-like plus family borrows |
| `Backend2/Lint.lean:149` `Prog.stackKs` | | an exemption list: a stack machine drops a linear closure (F3, #715) |

### 1.4 Surface syntax

| form | meaning today | as a predicate |
|---|---|---|
| `linear x <- M; N`, `linear x : A <- M; N` | binder flag `lin`: `x` not owed | surface-only. No effect at `P` (`corpus/forms.bc:43`, `linear d` at `1`), redundant at `¬D` |
| `linear ctl op` | `Qual.lin` | κ is `¬P ∧ ¬D`: linear, correctly |
| `ctl op` (default) | `Qual.aff` | κ is `D` only at the empty row; see Q1 |
| `multi ctl op` | `Qual.unr` | κ is `P`: unrestricted, correctly |
| `fn op` | answering | not a qualifier |
| `clone(x)` | written deep copy at `P` | `P` |

The lexer keyword `linear` (`Frontend/Lexer.lean:59`) stays: `linear ctl` uses it.

### 1.5 SPEC, decisions, docs, book

| place | what it says | conflict |
|---|---|---|
| SPEC §10 | persistent = holds no resource | consistent |
| SPEC §5 (line 333) | projection needs the other fields `Affine` | means `F` |
| SPEC §12 class 1 "forgettable … genuinely affine" | `F` and the borrows | includes persistent types, which are not affine in the quadrant sense |
| SPEC §12 class 2 "owned with a derived destructor … These are linear" | `D ∧ ¬F` | weakening is admissible (`drop_derives`), so these are not linear |
| SPEC §12 class 3 "strictly linear" | `¬D ∧ ¬P` | consistent with the proposal ("linear") |
| SPEC §12 *Insertion policy*, *Opt-out*, *Open* "`linear` on other binders" | owed; binder `linear` | removed by item 1 |
| SPEC §15 (line 1855) "an affine continuation has no destructor" | `aff` κ at a non-empty row | true only at a non-empty row (probe) |
| SPEC §19 qualifier table | weakening/contraction per qualifier | the definition this document adopts. Its `aff` row is weakening **at the row** |
| SPEC §22 "three kinds of function": linear / affine / persistent | `¬D` / `D` / `P` | consistent, with "persistent" for unrestricted |
| SPEC §22 effectful affine closure | `& F_Σ 1` | not `D`, so it is not affine in the pure reading (Q1) |
| SPEC §25 | `lin`/`aff` κ own a cell | consistent |
| SPEC §30 (line 5572), book `guide/async.md:89` "a task is a linear value: … run to the end or cancelled" | cancellable | a cancel is weakening at a row, so under Q1(a) this is neither "linear" nor "affine" |
| SPEC §52 (line 8925) "A dropped task leaks (affine, not cancelled)" | | contradicts the line above |
| SPEC §36 (line 6481) "a linear `K` or `V` makes the map linear: it has a destructor exactly when …" | `¬D` propagates | consistent |
| SPEC line 7347, line 10227 | list binder `linear` | removed by item 1 |
| `docs/decisions.md` 23 | "Only the forgettable types … are affine … the opt-out is a `linear` binder" | contradicts the proposal on both counts. Revising a decision needs the user (Q1) |
| `docs/glossary.md:45` | Persistent | consistent |
| `docs/syntax-core.md` 232, 350, 905; `docs/surface-cbpv.md` 330 (`linear let`), 945; `docs/internals/elaboration/implicit-destructors.md` 66–71; `docs/prior-art-rust-wishlists.md` 463 | binder `linear` | removed by item 1 |
| book `language-reference.md` 58, 135; `guide/effects.md` 84 | `linear ctl` | consistent |
| non-type uses: "linear recursion" (SPEC 3906, 8838, 9545), "linear probing" (6471), "linear state" | unrelated meanings | Q6 |

### 1.6 Error messages

| message | site | meaning |
|---|---|---|
| "`x` is declared `linear` and is not consumed in its scope" | `Steps.lean:515` | binder flag: removed |
| "… and its type `A` has no destructor" | `Steps.lean:500, 518` | `¬D`. Under the proposal: "its type is linear" or keep the reason |
| "… is live across a computation that may abort, and its type has no destructor" | `Steps.lean:815` | `¬D` at an abort |
| "`&c` cannot be used in an annotated or `linear` binding" | `Sugar.lean:136` | binder flag: the `linear` half goes |
| "… which is not persistent" (several) | `Checker.lean:530`, `Program.lean:177`, `Sugar.lean` 2454, 3554, 3705, 4682, 4975; `Lint.lean:143` | `P` |
| "an abortive operation is affine" | `Elab.lean:406`, `Program.lean:151`, `Effects.lean:3880` | qualifier |
| "a div function whose result holds `K`, which has no destructor" | `Sugar.lean:596, 5119` | `¬D` |

---

## 2. Definitions

### 2.1 The predicates

Proposed file `Core/Structural.lean`. It imports `Core.Dtor` and adds no rule, no index and no
semantic definition.

```lean
namespace BoCa.Fig16.LogRel.Core

/-- Weakening at `A` is admissible: a rule of `CDerives` at a persistent type
(`Ctx.DeadP.drop`, `Ctx.SoloP.skip`), the derived rule `drop` at a type with a
destructor (`drop_derives`).  [Q1 decides whether a weakening at a row counts.] -/
def Weak (A : VTy) : Prop := A.Persistent ∨ HasDtor A

/-- Contraction at `A` is admissible: a rule of `CDerives` at a persistent type
(`Ctx.SplitP.dup`).  [Q3, option U2, adds the derived rule `copy` at `Imm @a B` and
`ArrayImm @a B`.] -/
def Contr (A : VTy) : Prop := A.Persistent

/-- Both structural rules are admissible. -/
def Unrestricted (A : VTy) : Prop := Weak A ∧ Contr A

/-- Weakening is admissible, contraction is not. -/
def Affine (A : VTy) : Prop := Weak A ∧ ¬ Contr A

/-- Neither structural rule is admissible.  [Q2 option (b) adds `¬ A.Drop`.] -/
def Linear (A : VTy) : Prop := ¬ Weak A ∧ ¬ Contr A

/-- The designated weakening: `forget` at a persistent type, the destructor otherwise. -/
def wkE (A : VTy) : Expr := if A.persistent then forget else dtorE A

/-- `wkE A xᵢ; e`. -/
def weakenE (A : VTy) (i : Nat) (e : Expr) : Expr := .seq (.app (wkE A) (.var i)) e
```

The witness is fixed: `wkE`, not "some closed term". With an existential witness, `U(F 1)` would
be "affine", because forcing a thunk consumes it, and so would any declared linear type that has a
public consumer (`commit`). Weakening means the derived rule the kernel offers, as §19 says:
"weakening has computational content: the continuation's destructor".

### 2.2 The theorems (targets)

Each statement is meant to be proved without `sorry`. The column says where its proof comes from.

| # | statement | from | cost |
|---|---|---|---|
| T1 | `theorem contr_rule (hA : Contr A) (h : Ctx.SplitP Γ Γ₁ Γ₂) : Ctx.SplitP (⟨A, true⟩ :: Γ) (⟨A, true⟩ :: Γ₁) (⟨A, true⟩ :: Γ₂)` | `.dup hA`; soundness `gSepC_splitP` | exists |
| T2 | `theorem weak_rule (hA : A.Persistent) (h : Ctx.DeadP Γ) : Ctx.DeadP (⟨A, true⟩ :: Γ)` | `.drop hA`; soundness `gSepC_deadP` | exists |
| T3 | `theorem weaken_admissible (hA : Weak A) (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hx : Ctx.SoloP Γ₁ i A) (h : CDerives Δ Γ₂ e (.comp C)) : CDerives Δ Γ (weakenE A i e) (.comp C)` | `P`: `unitE` + `lolliE` + `forget_persistent`; `D`: `drop_derives` | small, new |
| T4 | `theorem no_relevant (h : Contr A) : Weak A` | `Or.inl` | trivial |
| T5 | `theorem classes_cover (A) : Unrestricted A ∨ Affine A ∨ Linear A` and pairwise disjointness | T4, excluded middle | trivial |
| T6 | `theorem Linear.not_hasDtor (h : Linear A) : ¬ HasDtor A`, `Linear.not_persistent` | definitional | trivial |
| T7 | `theorem TDerivesP.dtor_hasDtor : TDerivesP Δ Γ (.dtor i j A) j' → HasDtor A`: a drop node in a typed term is at a type with a destructor, so never at a linear type | cases on one constructor of `TDerivesP` (it carries `hA`) | small. It inverts `TDerivesP`, not `CDerives` |
| T8 | structural closure: `Linear A → ¬B.Persistent ∨ … → Linear (.tensor A B)`, and the same at `.tensor B A`, `.sum`, `.box`, `.ref`, `.fam (.ref _)`; `HasDtor.tensor_iff` and the like | cases on `HasDtor` (a type-indexed inductive, cheap) | small. `μ` needs `keysIn` (moderate). `!A` is persistent for every `A`, so `Linear A` does **not** give `Linear (!A)` (Q10) |
| T9 | qualifiers: `kTy_lin_linear : Linear (kTy S R .lin B F)`, `kTy_unr_unrestricted : Unrestricted (kTy S R .unr B F)`, `kTy_aff_empty : Affine (kTy [] R .aff B)` | cases; probes pass | small |
| T10 | `kTy_aff_row : S ≠ [] → ¬ Weak (kTy S R .aff B F)` under the pure definition | cases on `HasDtor`; probe at a `Fail` row | small. **This is Q1**: under the pure reading `ctl` gives a linear κ at every non-empty row |
| T11 | closures: `Affine (affT c A B)` (from `hasDtor_aff`, `not_persistent_aff`); `Linear (.lolli A B)` (from `not_hasDtor_lolli`) | exists | trivial |
| T12 | `Forgettable A → Weak A` (`hasDtor_of_affine`, renamed) | exists | trivial |
| T13 (U2 only) | `contract_admissible_imm : CDerives Δ (⟨.imm a B, true⟩ :: ⟨.imm a B, true⟩ :: Γ) e (.comp C) → CDerives Δ (⟨.imm a B, true⟩ :: Γ) (dupE e) (.comp C)`, with `dupE e` = `copy x` and `tensorE` | `CDerives.copy`, `tensorE`, `CDerives.insert_dead` for the shift | moderate |

None of these touches `fundamentalC` or `adequacyC`. The predicates classify. The rules they
summarise are already in `CDerives`, or are derived from it.

### 2.3 Each existing notion, mapped

| notion | becomes | action |
|---|---|---|
| `VTy.Persistent` | `Contr` and the `P` half of `Weak`; "unrestricted" | keep the name for the semantic fact (holds `∅`); "unrestricted" is the word for the class |
| `Persistent (Γ)` (all live slots `!`) | none of the three | rename (for example `Ctx.Banged`), or widen it to `∀ slot, P` (Q7) |
| `Records.Affine`, `dropT` | `Forgettable`, `forgetT`: weakening admissible **with no action**. A refinement of `Weak`, used where a drop may not be observable (projections). Not one of the three words | rename: `Affine → Forgettable`, `dropT → forgetT`, `affine_immReborrow → forgettable_immReborrow`, `affine_valTy`, `hasDtor_of_affine → hasDtor_of_forgettable`, `not_affine_aff → not_forgettable_aff`; four files (`Records.lean`, `RecordPrograms.lean`, `Dtor.lean`, `Aff.lean`) and SPEC §5, §12, §22 |
| `HasDtor` | the derived half of `Weak` | keep. "Has a destructor" is what it says |
| SPEC §12 class 1 | `Forgettable`; the persistent ones are unrestricted and the borrows affine | reword |
| SPEC §12 class 2 | **affine** | reword "These are linear" |
| SPEC §12 class 3 | **linear** | "strictly linear" becomes "linear" |
| `VTy.Drop`, `Ctx.Drops` | none of the three: "holds no `own` cell; an abort may abandon it" | rename away from "drop" (for example `VTy.OwnFree`), since "drop" also names `dropE`. Its relation to "linear" is Q2 |
| `Qual.lin` | linear κ | consistent |
| `Qual.unr` | unrestricted κ | consistent |
| `Qual.aff` | affine at the empty row (`HasDtor.close`); at a non-empty row it depends on Q1 | Q1 |
| §22 affine closure | affine | consistent |
| §22 effectful affine closure | linear under Q1(a); affine at `Σ` under Q1(b) | Q1 |
| `Aff ≤ linear` (`AffRules.lean`) | "affine ≤ linear" holds under the proposal: a linear use of an affine value | consistent |
| Tir `Class` | `Unrestricted` / `Affine` / `Linear` (U1) | rename the constructors to the words, prove `Class.of` (section 3) |
| `Env.own` "owed" | `Affine A`: a live slot of affine type is owed to its scope | keep the slot word "owed", defined from `Affine` |
| Backend2 `copyable`, `droppable` | read from Core: `Contr` (+ `copy` at `Imm`, U1/U2) and `Weak` / `OwnFree` | item 4/5 work, not now |
| task (§30, §52, book async) | a cancellable suspension | Q1 decides its word |

### 2.4 Weakening that needs an effect

Three weakenings in the kernel are not a pure destructor:

1. **A cancel at a row.** `κ` at `aff` at a non-empty `Σ` is consumed by `κ (inj₂ ())`, which
   runs at `cancelTy Σ F`: its finalisers may perform and raise there (§27). The effectful affine
   closure and a task are the same shape.
2. **Abandonment at an abort.** `[let]` at a row with an affine or abortive operation needs the
   rest's context to be `VTy.Drop`. Those values are abandoned when the operation aborts, with no
   term run. `[raise]`'s argument is the same.
3. **A finaliser.** `[then]`'s `D` runs the destructors (`finalOf`) of what the rest holds. That
   is ordinary `HasDtor` weakening, placed on the unwind path.

How the definition treats 1 and 2 is Q1 and Q2. Section 7 lays out the options. This document does
not pick between them.

---

## 3. The checker

`Class.of A = if A.persistent then .persistent else if hasDtorB A then .dtor else .linear` must be
the predicates themselves. `VTy.persistent` is already the Bool the predicate is defined by.
`hasDtorB` is proved sound only (`dtorB_sound`). The target theorems:

```lean
/-- `dtorB` is complete for `HasDtor`. -/
theorem dtorB_complete : ∀ A : CVTy, HasDtor A → dtorB false A = true
/-- …with its `alg` mode, by the same mutual induction as `dtorB_soundA`. -/
theorem dtorB_completeA : ∀ (A : CVTy) (Bs : Stack), AlgDtor Bs A → dtorB true A = true

theorem hasDtorB_iff (A : CVTy) : hasDtorB A = true ↔ HasDtor A
instance : DecidablePred HasDtor := fun A => decidable_of_iff _ (hasDtorB_iff A)

theorem Class.of_unrestricted (A : CVTy) : Class.of A = .persistent ↔ Unrestricted A
theorem Class.of_affine       (A : CVTy) : Class.of A = .dtor ↔ Affine A
theorem Class.of_linear       (A : CVTy) : Class.of A = .linear ↔ Linear A

/-- The owed slot is the affine one (after the `lin` flag is removed). -/
theorem pushOwn_own (E : Env) (x : String) (A : CVTy) :
    (E.pushOwn x A).own.head? = some (decide (Affine A))

/-- Under Q2(b), `dropB` is needed in both directions too. -/
theorem dropB_iff (A : VTy) : dropB A = true ↔ A.Drop
```

Options for getting there:

- **A. Prove `dtorB_complete`.** Every case but `μ` is immediate from the constructor. At `μ`,
  `HasDtor.mu` gives `PBody A` (decided by `pBodyB`, `pBodyB_iff` exists) and `AlgDtor [A] A`; the
  converse of `dtorB_soundA` is needed. I have not proved `dtorB_completeA`. The
  stack-independence of `dtorB true` against an `AlgDtor` that depends on `Bs` is the step to
  check first. I have not verified that any obstruction exists.
- **B. Define the predicate by the decider.** `HasDtor A := dtorB false A = true`, with today's
  constructors as lemmas. `dtor_wf` and every proof by induction on `HasDtor` have to be redone
  by recursion on `A`, which is a larger change for the same result.
- **C. Keep both, prove `iff`.** This is A, packaged as the `DecidablePred` instance.

A is the smallest change if `dtorB_completeA` holds. B is the fallback. Either way the stated
theorem is `hasDtorB_iff`. The checker never classifies by anything else: `Env.pushOwn`, `finalOf`,
`dropOne`, `notDropped`, `unconsumed` and `isLinear` all read `Class.of` or `hasDtorB`.

---

## 4. Declared linear types

A `data` declaration today is transparent: a name for a structural type of `⊗`, `⊕`, `μ` (SPEC §42,
"the kernel sees nothing new"). `HasDtor` is derived structurally, so `data Txn = { id: i32, log:
box Buf }` gets a destructor from its representation. A declared linear type needs a fact in the
type that the kernel sees, as opaque types (§11) have.

### 4.1 What "the kernel refuses any drop" can mean

This has to be settled first (Q4), because the options differ here.

- **(i) No derived weakening.** The type is `Linear`: no `HasDtor`, not persistent, not
  `OwnFree`. So the checker cannot insert a drop (T7), `[let]` cannot abandon it at an abort, and
  `[then]`'s finaliser has nothing to run. An explicit elimination (`match` on a constructor) is
  a use, allowed anywhere. The elaborator must then emit that elimination only where the program
  writes one. Nothing in the kernel stops an elaborator from writing `unseal x; dtorE A x`; the
  gate step (item 4) pins every such site.
- **(ii) No consumption outside the declaration.** Only the declaration's own definitions can
  eliminate the type, so code elsewhere has no derivation of any consumer except calling those
  definitions (`commit`, `abort`). This is abstraction (`docs/data-declarations.md` U3), and it is
  the only reading under which the kernel itself refuses an elaborator's drop.

Example of the difference. Under (i), E5 `txn.id` on an owned `txn` is `getAt` after an
elimination: it would consume `txn` and forget the other fields, which is a silent destruction
written by sugar. Under (i) the rule "E5 never eliminates a declared linear type" is the
elaborator's to keep. Under (ii) it has no derivation.

### 4.2 Mechanisms

| | mechanism | kernel-visible fact | guarantee | cost |
|---|---|---|---|---|
| **L-T** | a token field: `N ≜ A ⊗ Tok`, `Tok = VTy.opq .lin` a new opaque kind with constants `mint : 1 ⊸ Tok`, `burn : Tok ⊸ 1` | `Tok` has no `HasDtor` (as every `opq`) and is not persistent; `VTy.Drop`'s `opq` constructor is restricted to the host kinds | (i) | one `Opaque` kind and its model; two constants with compat lemmas (`Tok` holds `∅`, so they are the `I32`-leaf case); `Drop.opq` narrowed (no current program uses a non-host kind) |
| **L-A** | a new former `VTy.lin A` with `linI`/`linE` typing rules on the same term (the pattern of `boxI`/`boxE`, `roll`/`unroll`) | no `HasDtor`, `Drop` or `persistent` case | **weaker than (i).** `linE` applies to any value, so `dtorE A x` types for `x : lin A`, and the kernel derives the drop | about 100 match arms (CLAUDE.md growth) for no guarantee. Listed only to rule it out |
| **L-B** | `VTy.lin A` with a distinguished eliminator **term** `unseal` (identity step) | as L-A, and every consumption is an `unseal` node | (i), and auditable in the typed term | a former (~100 arms), a primitive with a machine step (`Paper/`/`Support/` machine, `make gate-full`) |
| **L-C** | keyed: `lin k A`, `unseal_k` needs a key value bound only in the declaration's definitions | no derivation of a consumer without the key | (ii) | an abstraction mechanism the kernel does not have; joins U3 |
| **L-D** | resourced (the §25 pattern): sealing allocates a unit `own` cell, eliminating frees it. Combines with L-T (`Tok` an owned unit cell with no destructor) or L-B | as the base option, plus semantics: a dropped value leaves its cell allocated, so `adequacyC` (memory empty at the end) sees every drop | (i) or (ii), **with semantic content**: no run ends with a sealed value unconsumed | `ewp_alloc`/`ewp_free` compat (6.141, 6.142, as §25); the cell lowers to no words (`zeroCell`, §23) |
| **L-E** | encode as `U(F A)` (seal = `thunk (return v)`, unseal = `force`) | a thunk of `F` has no destructor | (i) | no kernel change, but `Imm̲ 'b (U C) = Unk`: a borrow cannot read the fields, which #746 requires. It also allocates a closure per value. Fails the requirements |

Without L-D, the linearity of a declared type has no semantic content: a `Txn` whose
representation holds `∅` could be dropped and no theorem would notice. §19 makes the same point
about "relevant", and §25 answered it for κ with the capture cell.

### 4.3 The obligations, per item of #746

- **How the declaration elaborates.** Syntax is not fixed (`linear data N = …` is a placeholder).
  - L-T: constructor `C(e…)` ↦ `(payload, mint ())`; `match` ↦ `let (p, t) = v; burn t; …`.
  - L-B/L-C: constructor ↦ `seal(payload)`; `match` ↦ `unseal` then the decision tree.
  - In every option the declaration's type is the kernel type. No table in the elaborator holds
    linearity, so `Class.of` reads it from the type.
- **How `HasDtor` and `dtorB` refuse it.** L-T: `HasDtor` has no `opq` constructor and `dtorB _
  (.opq _) = false`, already. L-B: no constructor for the new former, `dtorB _ (.lin _) = false`,
  and `dtorAt` falls to its default `forget`, which `dtor_wf` never types because its premise
  fails. `Drop`/`dropB`: L-T needs `Drop.opq` restricted to host kinds; L-B gets no constructor.
  Theorem: `Linear N` for every declared linear `N` (T8 at the token or the former).
- **Borrows.** `Imm @a N` and `Mut @a N` are affine (`HasDtor.imm`/`mut`). Forgetting a loan
  does not consume the lent value, which returns to its lender at the lend's end (`withbor`'s
  `Ref A ⊗ B`).
  - L-T: `Imm̲ 'b (A ⊗ Tok) = Imm̲ 'b A ⊗ Unk`, so the fields can be read through a view
    (`loadField`) and the token's view is forgettable.
  - L-B: needs `Imm̲ 'b (lin A) ≜ Imm̲ 'b A`, plus 6.131 (`reborrow_vShape`) and 6.60
    (`vC_outlives`) at the former.
  - `Mut`: `withswap` hands the whole value to the callback, which must hand one back.
- **Containers and fields.** A linear field makes the container linear, by T8: `HasDtor.tensor`,
  `.sum`, `.box`, `.ref`, `.array` and `.mu` ask every leaf for a destructor, and `persistent`,
  `Drop` and `Forgettable` are conjunctive in the same way. `getAt` needs the discarded fields
  `Forgettable`, so a projection that would discard a linear field has no derivation. `!N` is the
  exception (Q10).
- **`fundamentalC`/`adequacyC`.**
  - L-T: two compat lemmas (`mint`, `burn`) and the `Opaque` model; nothing else.
  - L-B: a new `VTy` former, so a case in every lemma by induction on value types (relation
    clause = `A`'s, `Imm̲`, outlives, `NoMut`, `Cl`, `Poly`, `SpineMuFree`, `toFShape`, `dtorAt`,
    `algsIn`, Backend type maps), plus `unseal`'s machine step and compat lemma.
  - L-D: the alloc/free compat at the cell, as §25's `ewp_kappaCell`/`ewp_kappaC_*`; then the
    run-level statement "every sealed cell is freed", which is `adequacyC`'s empty final memory.
    The S6-style reduction from that to "every value consumed" is not a Core theorem today (§25
    *Open*).
  - Every option keeps `fundamentalC`'s and `adequacyC`'s statements.
- **Across an abort.** A linear value is not `Drop` and has no destructor, so it cannot be live
  in the rest of a computation that may abort: `[let]` needs `Drops`, `[then]`'s `finalOf`
  needs `HasDtor`. That rejects a `Txn` live across any call that may `raise` (Q5).

---

## 5. Removal (item 1)

Binder `linear` at b566c459. The brief's count of 6 uses in 4 files matches the corpus count with
`join-bind-head.bc`'s header comment included: 5 binder uses in 4 corpus files, plus 2 in a
Lean test string.

| site | use | replacement |
|---|---|---|
| `corpus/forms.bc:43`, `:44` | `linear d <- return ()`, `linear e : 1 <- return d` (at `1`, persistent: the flag does nothing) | plain `d <- …`, `e : 1 <- …`. Output unchanged (expected) |
| `corpus/join-bind-head.bc:17` and its header (lines 1, 6) | `linear a <- if …` at `i32` (persistent) | plain binder, header reworded. Output unchanged (expected) |
| `corpus/implicit-drops.bc:67` | `linear q <- alloc…`, consumed by `free` two lines on | plain binder: `q` is consumed, nothing is owed. Output unchanged (expected) |
| `corpus/reject/linear-unused.bc` | `linear r` unused at `Ref B` | delete it. Without the flag the program is accepted (`r` is dropped). Its replacement is a declared-linear-type reject program (item 4's `corpus/reject/linear-*`) |
| `Frontend/Tests.lean:89` `rt_linear` | parser round trip | delete it. A declaration round trip comes with item 3 |
| `Frontend/Syntax.lean:679` `Comp.bind … (lin : Bool)` | the field | remove it; doc at 677 |
| pattern sites carrying the field | `Print.lean` 191 (`linKw`), 290–292; `Syntax.lean` 1015; `Parser.lean` 1195, 1265–1272 (`bindForm`), 2005 (doc), 2061–2070 (the `linear x` branch: removed); `Elab/Divisions.lean` 70; `Elab/Hygiene.lean` 113–116; `Elab/RenameLife.lean` 178; `Elab/Respan.lean` 180; `Elab/Meta.lean` 377–379; `Elab/Subst.lean` 176; `Elab/LoopLend.lean` 91, 152–156, 324–330, 389, 432–433, 543–546; `Elab/Effects.lean` 896, 1727, 1737–1747, 1784, 1840–1867, 3625, 3729–3736; `Sugar.lean` 131–136, 206, 243, 772–790, 817, 857, 1187, 1249–1282, 1473, 2261, 3348–3382, 4270–4303, 5890–5892 | drop the field. Mechanical, except where `lin` changes behaviour (next rows) |
| `Elab/Effects.lean:1738` `bindValue` (`if !lin`) and `:1866–1867` (`if lin then … unpack … v`) | a `linear` binder kept its own binding instead of fusing with the call's | take the `!lin` path always |
| `Sugar.lean:135–136` | `&c` refused in an annotated or `linear` binding | keep the annotated half; the message loses "or `linear`" |
| `Check/Checker.lean` 414–429, 750–766 | pass `lin` to `pushOwn`, `popL`, `effBind` | drop the argument |
| `Check/Steps.lean` 514–515 (`unconsumed`'s `lin` branch), 546–550 (`popL`'s `lin`), 572 (`Env.push` doc "or `linear`"), 577–578 (`pushOwn`'s `lin`), 864–867 (`effBind`'s `lin`) | the flag | remove; `own := Affine` decided by `Class.of` (section 3) |
| SPEC §12 *Insertion policy* ("not declared `linear`"), *Opt-out*, *Open* ("`linear` on other binders"); line 7347; line 10227 | binder `linear` | remove; new entry text says what replaced it (a declared linear type) |
| `docs/syntax-core.md` 232, 350, 905; `docs/surface-cbpv.md` 330, 945; `docs/internals/elaboration/implicit-destructors.md` 66–71; `docs/prior-art-rust-wishlists.md` 463 | binder `linear` | remove or point at declared linear types |
| `docs/decisions.md` 23 | "the opt-out is a `linear` binder rather than a grade on types" | revised with the user (Q1) |
| SPEC changelog 0.6 (line 10962–10964) | history | unchanged: the changelog records versions |

Not removed: the keyword `linear` (for `linear ctl`), `Qual.lin`, and every `Class.linear` /
`isLinear` use, whose meaning (no destructor, not persistent) becomes the predicate `Linear`.

Every use of the flag is replaced by **nothing**. No program in the corpus relies on it for a
value whose silent destruction is a bug. The one that would (`reject/linear-unused.bc`) is a test
of the flag itself.

---

## 6. NOT-do list and tempting shortcuts

Each is a **STOP**: stop and report. Do not take it.

1. **Defining a word by an elaborator mechanism.** "Linear means not owed", "affine means the
   checker inserts a drop", or reading linearity from `Data.Table`. The words are the Core
   predicates of section 2; the checker decides them (section 3).
2. **Keeping a binder flag under a new name**, such as `must_use x <- M`, `#[linear]`, or `own:
   false` set by an annotation. Linearity is a property of the type.
3. **Checker-only obligations.** A check in `Frontend/` that refuses a drop or copy of a declared
   type with no kernel fact behind it. The checker's refusal must be "`HasDtor` fails" or "no rule
   applies", and nothing else.
4. **Enumerating cases per program.** Special-casing `Txn`, special-casing E5 for one record, or
   an exemption list (`Prog.stackKs` is the existing one, F3). Every refusal follows from T7/T8.
5. **An existential witness for weakening** ("some closed term consumes it"). It makes `U(F 1)`
   and every type with a public consumer affine (section 2.1).
6. **L-A** (`linI`/`linE` on the same term). It looks like `boxI`/`boxE`, but it derives the drop
   it is meant to refuse.
7. **Widening `Persistent Γ`, narrowing `VTy.Drop`, adding implicit `imm` copies, or inserting
   cancels as drops**, any of which changes which programs are accepted, without the user's
   decision on Q1–Q3 and Q7.
8. **Making the effectful affine κ "affine" by giving it a pure destructor**, such as dropping
   its cancel without running the finalisers. That weakens the borrow guarantee: the lends in κ
   must end by unwinding.
9. **Calling a type "linear" in prose, an error message or a name** when it is in `Weak`, or
   "affine" when it is not, while the definitions are pending. Say "has no destructor" or
   "persistent" until the words are settled.
10. **Proving `dtorB_complete` by changing `dtorB`** so that it accepts fewer or more types. A
    change to `dtorB` changes acceptance.
11. **Patching Backend2's `droppable`/`copyable` to match.** Those are item 5's: they will read
    the Core predicates, not grow cases.

---

## 7. Open questions for the user

**Q1. Does a weakening that needs an effect make a type affine?** It covers an affine κ at a
non-empty row, the effectful affine closure, and a task.

- **(a) Pure only.** `Weak` as in section 2.1. A `ctl` κ is affine at the empty row and *linear*
  at every non-empty row (T10). The word for "consumed by its cancel at `Σ`" must then be another
  word (for example "cancellable"), and §19's `aff` row, §22's effectful closure and the task text
  are renamed. Simple, decidable, and no effectful destructors. But the surface default `ctl`
  would no longer be "the affine qualifier" except at the empty row.
- **(b) Graded.** `WeakAt (S : Row) A`, with `HasDtorAt S` adding `cancel` at `U(C & F_{S'} 1)` for
  `S' ≤ S`, and `Weak = WeakAt []`. §19's table holds literally ("affine: weakening yes", at its
  row). The cost is that `dtor_wf` at a row needs effectful destructors: the componentwise case
  `dtorE A x₁; dtorE B x₂` at a row with an abortive operation leaves `x₂` live across a possible
  abort, so it needs `[then]`. That is SPEC §12's *Open* "destructors with effects that can fail".
  The checker's insertion policy can stay pure, so acceptance need not change. The definition is
  only harder.
- **(c) Pure, plus revise decision 23's other half.** Decision 23 says "only the forgettable types
  are affine", so class 2 (`Ref`, `μ`, `close`) would be "linear with a derived destructor". That
  contradicts admissibility, which the rule forbids. Either decision 23 is revised to "affine =
  has a destructor" (which (a) and (b) need), or class 2 needs its own word.

**Q2. Is abandonment at an abort a weakening?** It decides whether opaque host types are linear.
Today `opq` has no destructor and is not persistent, but it is `VTy.Drop`, so an abort may abandon
a live `Input`/`Output` *(probe)*.

- **(a) No.** `Linear := ¬Weak ∧ ¬Contr`. Opaque types are "linear", and an abort still abandons
  them. That reading is weaker than "literally linear".
- **(b) Yes.** `Linear := ¬Weak ∧ ¬Contr ∧ ¬Drop`. Opaque types are in none of the three and need
  a name (for example "abandonable"). Declared linear types get `¬Drop`.
- **(c) Yes, and remove `opq` from `Drop`.** Opaque types become linear. This **rejects programs**:
  any program with a capability live in the rest of a computation that may raise (most I/O
  programs with `Fail`). **STOP: this changes acceptance.** It is listed for completeness.

**Q3. Contraction at `Imm`.** `copy : Imm @a A ⊸ Imm @a A ⊗ Imm @a A` is a kernel axiom, so
contraction is admissible at `Imm` by a term.

- **U1.** `Contr := Persistent`. `Imm` is affine and has an explicit `copy`. Nothing changes,
  but "affine" then holds of a type whose contraction is derivable, which strains the literal
  reading.
- **U2.** `Contr := Persistent ∨ Imm/ArrayImm (derived)`. `Imm` is unrestricted, literally right.
  The checker need not insert copies there, so acceptance is unchanged unless it does: implicit
  `imm` copies were #58's E1, which stays rejected (`class1-revive`). `Class.of` needs a fourth
  outcome, or the `persistent` constructor is renamed `unrestricted` with `Imm` in it.

**Q4. How strong is a declared linear type's guarantee?** (i) no derived weakening, eliminations
anywhere, or (ii) eliminations only in the declaration's definitions (section 4.1). And which
mechanism: L-T (token, cheap, (i)), L-B (former and `unseal`, (i) auditable), L-C (keyed, (ii),
needs abstraction), each with or without L-D (resourced, semantic content). L-A and L-E fail
#746's requirements. **This is a design decision #746 does not settle.**

**Q5. A declared linear value across an abort.** Under every option it cannot be live across a
computation that may abort. That is Austral's position, but here `Fail` is everywhere.

- **(a) Accept it.** The program handles the error before the linear value is in scope, or
  converts it with `to_result`.
- **(b) The declaration names an unwind consumer** (`abort`), which `[then]`'s finaliser calls.
  The type then has a weakening on the unwind path, so by the rule it is not linear and needs
  another name.

**Q6. Other meanings of "linear".** "Linear recursion", "linear probing", "linear state", "linear
time". #746 says "use no other meaning anywhere". The saved precedent for order terms reserves
"linear" for types. Rename those too, or limit the sweep to classifications?

**Q7. `Persistent (Γ)`** means "every live slot is `!`". Rename it (for example `Ctx.Banged`), or
widen it to "every live slot persistent" (SPEC §10 *Open*; this changes acceptance, so STOP).

**Q8. `Forgettable` and `VTy.Drop`.** They have the same constructors except `opq`
(`Forgettable = Drop ∩ HasDtor`, to be proved). Keep two inductives, or define one from the
other?

**Q9. Checker strategy** (section 3): A (prove `dtorB_complete`), with B as the fallback if
`dtorB_completeA` does not go through.

**Q10. `!N` at a linear `N`.** `.bang A` is persistent for every `A`, so `!Txn` would be
unrestricted. If `!` is introduced only at `!U C` (promotion), `!Txn` is uninhabited and harmless.
That needs a lemma, which inverts `CDerives`, so its cost must be stated. The alternatives are to
forbid it in well-formedness, or to leave it.

---

## 8. After this document

The order of #746 stands: items 1 and 2 (removal and vocabulary), then 3 (declared linear types),
then 4 and 5. Item 4's gate step (`scratch-archive/kernel-boundary/gate-issue-draft.md`) pins
every site outside `Core/` that inserts a copy, forget, destructor or drop, and adds
`corpus/reject/linear-*`. Item 5 (F3) gives `Prog.stackKs` a kernel rule, a named assertion, or
removes the drop. Both read the predicates defined here. Nothing in this document changes code.

### What this document does not establish

- `dtorB_completeA` is unproved and unchecked (section 3).
- `Forgettable = Drop ∩ HasDtor` is read off the constructors, not proved.
- "Output unchanged" for the three corpus programs in section 5 is expected from reading them. No
  program was run.
- The probes check T9, T10 and Q2's facts at specific instances, not the general statements.
- Unread here: `experiments/` (the library never imports it) and `research/`.

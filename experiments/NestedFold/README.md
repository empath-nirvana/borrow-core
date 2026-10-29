# NestedFold: the owned fold by induction on the class `P` (#719, U0 of #595)

`lake build NestedFold`. Imports `Core`; nothing imports it.

## Question

Does the generic owned traversal spec close by induction on the class `P` (#595's design
§4.2, which replaces `FShape`), with the measure (cells, value size, binder rank) and an
environment of handles, one per binder? The test types are `μX. I32 ⊗ Array X` and
`μX. I32 ⊗ μY. 1 ⊕ (Ref X ⊗ Ref Y)`.

## Verdict: yes

`trav_spec` (`Spec.lean`) is one induction on the position `A ∈ P`, with one case per former
(variable, `⊗`, `⊕`, `Ref`, `[Ref S]`, `μ`, closed leaf). It follows `Core/FoldOwn.lean`'s
`travO_spec` case by case. `hs_all` is `hOSpec_all` with a third induction level. `fold_spec`
holds for every body in `P`. The two test types are instances of it (`roseA_fold`,
`nestA_fold`), and each is destroyed with concrete algebras, every hypothesis discharged
(`roseA_dtor`, `nestA_dtor`).

All the hypotheses come from `P` or are the algebras' own validity, as in `hOSpec_all`. There is
one more, a syntactic one: the algebras are closed values (see *Hypotheses*). No case tree over
combinations of formers was needed. Every theorem's `#print axioms` is within
`[propext, Classical.choice, Quot.sound]`. There is no `sorry`, `axiom`, `native_decide`,
`opaque`, `partial` or `unsafe`.

## What is proved

| File | Content |
|---|---|
| `Class.lean` | `P d A` and `PBody B` (`P 1 B ∧ Hd B`); decided by `PB_iff`, with `Decidable` instances; `P_of_closed`; **`P ⊇ FShape`** (`P_of_FShape`, `pBody_of_FShape`); binders as stacks of bodies, `env`, `closedOf`, `inst_closedOf` (the unrolling is the body under the extended environment); `rIn`/`aIn`/`reach`; `reach_ok`: the binders of a body in `P` are closed under the traversal's calls |
| `Term.lean` | the generated traversal `tE`/`trav`, one action per former; the result type `resO`; the dispatch `dsp`/`selfD` (one Z combinator over all binders: Bekič's simultaneous fixed point); handles `hdl b = λw. selfD (tag b w)`; closedness; reduction lemmas |
| `Loop.lean` | `countLoop_inv`: `countLoop_wp` with an invariant indexed by the counter |
| `Dispatch.lean` | `selfD_run`: at binder `b`'s tag the fixed point runs `b`'s traversal with itself as the handle, then `b`'s algebra |
| `Array.lean` | `step_spec`, `arr_spec`: the owned array action. A `count` loop with state `(acc, (w, s))`; each step does `idx`, `free` of the slot, the content's traversal at fewer cells (`dsize_tail_lt`), and `g_a (inj₂ (acc, r))`, seeded by `g_a (inj₁ ())`. The invariant holds the slots not yet visited |
| `Spec.lean` | **`trav_spec`**, **`hs_all`**, **`fold_spec`** |
| `Instances.lean` | `HasDtorMu` (`HasDtor.mu` restated at `P`) and `dtor_spec` (the fold at results `1` ends at `()` with the empty resource); the two test types: `PBody` by `decide`, outside `FShape`, their binders (`reach_roseB = [[roseB]]`, `reach_nestB = [[nestB], [nestInner, nestB]]`), `roseA_fold`/`nestA_fold`, `roseA_dtor`/`nestA_dtor`, `roseB_hasDtorMu`/`nestB_hasDtorMu` |
| `Probe.lean` | the design pass's probe: `μX. I32 ⊗ Array X` is outside `FShape`; the iso-recursive mismatch of a nested-`μ` mutual group (`tyBinA ≠ tyB`); the factorial size table (`#guard`) |

### The main statements

```lean
-- the generic traversal, by induction on A ∈ P
theorem trav_spec {s : Val} (hs : closedAt 0 s.1 = true) :
    ∀ (A : VTy) (Bs : Stack) (n K r : Nat), IHL ks G δ s n K r → P Bs.length A →
      sizeOf A ≤ r → Anc ks Bs → (∀ c ∈ rIn Bs A, c ∈ ks) → (∀ S ∈ aIn A, AlgAOK G δ Bs S) →
      ∀ w χ ls, sizeOf w.1 ≤ K → (Hd A ∨ sizeOf w.1 < K) →
        vP (A.subst (env Bs)) ls δ w χ → dsize χ ≤ n →
        wpTS ls (.app (.app (.val (trav ks G Bs A)) (.val s)) (.val w))
          (fun ls' => vP (resO G Bs A) ls' δ) χ

-- every binder's handle, by strong induction on (cells, size, rank)
theorem hs_all (hok : KeysOK ks) (halg : ∀ B Bs, (B :: Bs) ∈ ks → AlgOK G δ (B :: Bs) B)
    (harr : ∀ B Bs, (B :: Bs) ∈ ks → ∀ S ∈ aIn B, AlgAOK G δ (B :: Bs) S) :
    ∀ n K B Bs, (B :: Bs) ∈ ks → Anc ks (B :: Bs) → HS ks G δ (selfD ks G) B Bs n K

-- the fold of μB₀, for every body in P
theorem fold_spec {B₀ : VTy} (hB : PBody B₀) (G : Algs) (δ : LSub)
    (halg : ∀ B Bs, (B :: Bs) ∈ reach B₀ → AlgOK G δ (B :: Bs) B)
    (harr : ∀ B Bs, (B :: Bs) ∈ reach B₀ → ∀ S ∈ aIn B, AlgAOK G δ (B :: Bs) S)
    (w : Val) (χ : WRes) (ls : List SRec) (hv : vP (.mu B₀) ls δ w χ) :
    wpTS ls (.app (.val (hdl (reach B₀) G [B₀])) (.val w)) (fun ls' => vP (G.Res [B₀]) ls' δ) χ
```

### The measure

`IHL s n K r`: every listed binder's call meets its spec at every `(n', K', rank)` below
`(n, K, r)` lexicographically, where `n` bounds the value's cells, `K` its size and the rank
is the size of the binder's body. The measure drops at every call:

- **variable**: after `⊗`/`⊕`, the value is smaller. A body's head is never a variable (`Hd`),
  so the flag `Hd A ∨ sizeOf w < K` forces `<` at a variable;
- **`Ref`, array slot**: the content has fewer cells (`dsize_tail_lt`), and then any `K` will do
  (`IHL.down`);
- **inner `μ`**: same value, same cells; the inner body is a strict subterm, so the rank drops.

## Hypotheses

- **From `P`**: `PBody B₀` gives `KeysOK (reach B₀)` (`reach_ok`): each binder's body is in `P`,
  has `Hd`, and lists its inner binders.
- **Algebras** (as `hOSpec_all`'s `hg`): `AlgOK` per `μ` binder, `!U(T_b⟨R⟩ ⊸ F R_b)`, and
  `AlgAOK` per array binder, `!U(1 ⊕ (R_a ⊗ S⟨R⟩) ⊸ F R_a)`, each in the relation on every
  list.
- **Closed algebra values** (`Algs.alg_closed`, `algA_closed`). The traversal is generated with
  the algebra values written into it. `FoldOwn` passes its one algebra at run time instead
  (`λg. …`). This condition is on the algebra terms, not on the type, and it goes away once the
  constant abstracts the algebras (U1).

## Choices made here

- Algebras are keyed by the binder (a stack of bodies) and, at arrays, by the element type.
  Two identical positions under one binder share an algebra. The proof does not depend on the
  keying.
- The dispatch tags a binder by its index in `reach B₀`, as nested injections, so a call takes
  `index + 1` case steps. This matters only to the semantics; the backend would emit one
  function per binder.
- The array loop frees one slot per step (`free` of `ℓ + i`), as `drop` does in the model.

## Not done (U1)

- The kernel constant `foldOwnG` with the algebras as a run-time argument, its `SemV`
  compatibility lemma and its `CDerives` rule. That removes the closed-algebra condition.
- `HasDtor.mu` replaced in `Core/Dtor.lean` by `HasDtorMu`, with `dtorAt`/`dtor_wf` through
  `foldOwnG`. The step from `HasDtor (T_b⟨1⟩)` to an algebra in the relation, via `dtor_wf` and
  the fundamental property, is not built. `dtor_spec` takes the algebras as hypotheses, and the
  test types use hand-proved `g₀`, `g₁`.
- The borrowed and reuse folds, the frontend, Backend2 (out of scope for U0).

## Report items

- **Obstruction claims**: none.
- **Not derived**: the kernel constant and its rule (U1). I have not verified that any obstruction
  to them is real.
- **Unused hypotheses**: none. `P`'s `Hd` is used at the variable case. `KeysOK`'s parts are
  used at the unrolling, the inner `μ` and the variable cases.

# CBPVCore: do CBPV term formers, and the resource calculus, close over the typed world?

**Question.** `experiments/CBPVSplit` showed that the typed-world relation `vX` factors through
CBPV's `U`/`F` at the level of types: the Kripke quantifier over `Ext` sits only at `U`, and the
tagged `wpTS` only at `F`. This probe checks two further steps over the same model
(this repository's `Paper`/`Support`, imported unchanged; developed in `borrow_lang` against
the `Bang` experiment's library, which became them):

1. Are the CBPV term formers sound? The formers are `⊗ 1 ⊕ 0` on values and `& ⊤ ⊸` on
   computations, with the shifts `U`/`F`.
2. Does the full resource calculus live in the CBPV core? The resource value types are `Ref`,
   `Imm @a`, `Mut @a`, `[@a]`, `!` and `Unk`. The rules are the borrow axioms, the lifetime `∀`
   and the `!` rules. Does the extended judgment keep the Fundamental Property and adequacy?

Build: `lake build CBPVCore`.

## Design

- **Types** (`Relation.lean`).
  - `VTy ::= 1 | A ⊗ B | 0 | A ⊕ B | U C | Ref A | Imm @a A | Mut @a A | [@a] A | !A | Unk`.
  - `CTy ::= F A | A ⊸ C | C & D | ⊤ | ∀'x ⊏ @b. C` (`CTy.amp` is `&`).
  - There is no `⅋`/`⊥`.
- **The CBV translation** `cbv : Ty → VTy` sends `T₁ ⊸ T₂ ↦ U (T₁⁺ ⊸ F T₂⁺)` and
  `∀'x ⊏ @b. T ↦ U (∀'x ⊏ @b. F T⁺)`. Every other former goes to its namesake. `cbv_injective`
  proves it injective.
- **Terms.** There is no new syntax and no new machine. The judgment types BoLo `Expr`s in
  A-normal form:
  - `return V` is `V`, and `M to x. N` is `(λx. N) M`. BoLo evaluates the argument first, so `M` runs first.
  - `thunk` and `force` depend on the computation type (`forceE`):
    - A thunk of `F A` is `λ_. M`, with `M` under an extra dead binder. Forcing it is `x ()`.
    - A thunk of a λ-value `V : C`, for `C` of any other kind, is `V` itself, and forcing it is `x`.
      This is what makes `𝒱⟦U (A ⊸ F B)⟧(v)` apply `v` itself, as `vX`'s `⊸` clause does.
  - `λx. M` is `λx. M`, and `M x` is `M x` with `x` a variable.
  - `Λ. M` is `λ_. M`, with `M` under a dead binder, and `M []` is `M ()`.
  - `⟨M, N⟩` is `withPair M N = λs. case s {inj₁ u. u; M | inj₂ u. u; N}`. `M` and `N` are typed
    in the same context `withCtx Γ = u:1 (dead), s:1⊕1 (dead), Γ`. The projections are
    `M (inj₁ ())` and `M (inj₂ ())`.
  - `⟨⟩ : ⊤` is `()`, typed at any context.
  - `absurd V` is `absurdE V = case V {_. () | _. ()}`. It takes any rest of the context.
  - The borrow axioms are BoCa's terms (`alloc`, `free`, `swap`, `copy`, `forget`, `withbor`,
    `withload`, `withswap`), each a value of `U`-type `cbv T`.
- **Semantics.**
  - `vC b A` is mode-indexed like `vX b T`. `b = false` is the observable view that an `Imm`
    payload is held at, and `vC false (U C)` is `True`.
  - At `1`/`⊗`/`⊕` and at every resource type, `vC` has `vX`'s clause: `ptoOwn`, `ptoImmS`,
    `ptoMutS`, `atLife`/`box`, `ρ = ∅ ∧ 𝒱⟦A⟧` at `!`, and `emp` at `Unk`.
  - The `Imm` clause needs `CohE (rsOf ls) ℓ T δ` at a BoLo type. It reads it at a preimage:
    `∃ T, cbv T = A ∧ CohE (rsOf ls) ℓ T δ`.
  - `vC` is `False` at `0`. At `U C` it is `∀ ls', Ext ls ls' ρ → cC C ls' δ (forceE C v)`.
  - `cC` is written curried on the connective.
    - At `F` it is `wpTS`, and at `⊸` it is `∀ v, vC A v ─⋆ cC C (e v)`.
    - At `&` it is a conjunction of the two projections at the same resource, and at `⊤` it is `True`.
    - At `∀` it is `∀ α, ⌜α ⊏ @bδ⌝ ─⋆ cC C[δ['x ↦ α]] (e ())`.
  - `cC_iff_stacks` proves that this curried form is the stack semantics:
    `cC C ls δ e ρ ↔ ∀ S Q, (sS C ls δ S Q ─⋆ wpTS ls (plugS S e) Q) ρ`.
    Here `sS` (𝒮⟦C⟧) separates the stack's argument relations and fixes the final postcondition
    at the stack's `F A`. A `∀` frame is `()` together with the lifetime. `⊤` has no stacks.
  - `SemC Δ Γ e C` has `SemX`'s shape over `gDenC` (contexts of `VTy`). `SemV Δ Γ V A := SemC Δ Γ V (F A)`.

## Results

Every result's axioms are `[propext, Classical.choice, Quot.sound]`, or a subset of them. There
is no `sorry`, `axiom`, `native_decide`, `implemented_by`, `opaque`, `partial` or `unsafe`.

**1. Relation** (`Relation.lean`)

- `vC_local`: `𝒱⟦A⟧` is `Ext`-stable at every value type, in both modes.
- `vC_same`: the same-members form, which is what `vP_same` gives for `vX`.
- `cC_iff_stacks`: the curried `cC` is the stack semantics, `∀` included.
- `wpTS_step`: this is `wpTS_head` for a pure `Step1` in any evaluation context.
- `cC_step` and `cC_head`: `𝒞⟦C⟧` is closed under a pure step in front.
- `cC_bind`: `wpTS_bind_frame` at every computation type. The stack's arguments join the frame
  and are carried to the returned list by `vC_same`.
- Lifetimes:
  - `VFree`/`CFree` are the free lifetime variables.
  - `lFree_iff_vFree`: the translation keeps them.
  - `vC_congr`/`cC_congr`: `vX_congr` at `VTy`/`CTy`.
  - `vC_extend_of_not_free` and `gSepC_congr`.
- Contexts:
  - `gSepC_local`, `gDenC_same`, `gSepC_dead`, `gSepC_solo`, `gDenC_split` and `gDenC_dead_cons`.
  - `gSepC_persistent`: `!Γ` holds `∅`.
  - `gDenC_dead_eq`/`semC_dead`: a consumed context's slot types are not read.
  - `LiveEq`/`semC_liveEq`: a dead slot's type is not read.

**2. Agreement** (`Agreement.lean`)

- **`vX_eq_vC_fun : ∀ (b : Bool) (T : Ty), vX wpTS b T = vC b (cbv T)`**, by induction on `T`,
  in both modes. At `⊸`/`∀` the `U` clause, `cC`'s `⊸`/`∀` clause and `forceE` unfold to `vX`'s
  clause. At `Imm` the preimage is `T` itself, by `cbv_injective`.
- `vP_eq_vC`: the `b = true` instance.
- `cbvCtx` translates contexts slotwise. `gSepX_eq_gSepC`, `liveWithin_cbvCtx` and `gDenX_eq_gDenC`
  carry the context relation across.
- **`semX_iff_semV : SemX Δ Γ e T ↔ SemV Δ (cbvCtx Γ) e (cbv T)`.**
- `semV_of_semX_nil`: a closed typed-world fact holds at any consumed CBPV context.

**3. Compatibility** (`Compat.lean`, `Axioms.lean`). All of these close:

- Values: `var_compatC`, `unitI_compatC`, `tensorI_compatC`, `sumI₁_compatC`,
  `sumI₂_compatC`, `thunkF_compatC` and `thunkV_compatC`.
- Shifts: `ret_compatC`, `bind_compatC` and `force_compatC`.
- `⊸`: `lam_compatC` and `app_compatC`.
- `&`: `withI_compatC`, `proj₁_compatC` and `proj₂_compatC`.
- `⊤`: `topI_compatC`.
- Eliminations into any `C`: `unitE_compatC`, `tensorE_compatC`, `sumE_compatC` and `zeroE_compatC`.
- The lifetime `∀`:
  - `allI_compatC` is proved natively at every `C`. It uses `allI_compatX`'s freshness
    hypotheses, with `¬ VFree x` on the live slots of `Γ`.
  - `allE_compatC` is proved at `C = F (cbv T)`, with `vX_tyEq` at `TyEq.instLife` as the
    substitution lemma.
- `!`, all native at every `A`/`C`:
  - `bangThunkF_compatC` and `bangThunkV_compatC` promote over `!Γ`. At
    `C = A ⊸ F B` and `C = ∀. F B` they are `bangLamI`/`bangAllI`.
  - `bangE_compatC` is dereliction.
  - `copyBang_compatC` and `forgetBang_compatC` are `copy`/`forget` at `!`.
- `[@a]` and lifetime indices:
  - `boxE_compatC`, `immSub_compatC` and `mutSub_compatC` are native.
  - `boxI_compatC` is `boxI_compatX` carried by the agreement, at a context `LiveEq` to a
    translated one.
- Borrow axioms, each carried from its `_compatX` lemma by `semV_of_semX_nil`:
  - `alloc_compatC`, `free_compatC`, `swap_compatC` and `copy_compatC`.
  - `forgetImm_compatC`, `forgetMut_compatC` and `forgetUnk_compatC`.
  - `withbor1_compatC`, `withbor2_compatC` and `withbor3_compatC`.
  - `withload_compatC` and `withswap_compatC`.

  Each takes the side conditions of its `_compatX`.

**4. Judgment, Fundamental Property, adequacy** (`Fundamental.lean`)

- `CDerives Δ Γ e j` has `j = val A | comp C`. It has one rule per compatibility lemma.
- `fundamentalC : CDerives Δ Γ e j → SemJ Δ Γ e j`, proved by induction.
- `adequacyC`: a closed `F 1` computation runs from the empty memory to `()`. It is `fundamentalC`
  composed with `Typed.corollary33`, unchanged.
- `fundamentalCBV : DerivesWf Δ Γ e T → Δ.Ok → Ctx.ScopedB Δ Γ → SemV Δ (cbvCtx Γ) e (cbv T)`.
  This is the call-by-value embedding at the semantic level: 6.151 at `SemX`, carried by
  `semX_iff_semV`.
- `exProg_runs`: `thunk ⟨return (), ⟨⟩⟩ to t. π₁ (force t)` derives at `F 1` and runs to `()`.

**5. Resource programs** (`Examples.lean`)

- `cImmBorrow_derives` and `cImmBorrow_runs`: allocate, borrow immutably with `withbor` (1),
  load through the borrow with `withload`, and free. This is `immBorrow` without its
  `copy`/`forget` pair. It uses `∀I` twice, `[]I` twice, `⊗E` and `1E`. It derives at `F 1` in
  `CDerives`, and its `adequacyC` instance runs it to `()` from the empty memory.
- `cBang_derives` and `cBang_runs`: promote `thunk λx. return x` to `!U (1 ⊸ F 1)` over `[]`,
  `copy` it at `!`, `forget` one copy, then derelict the other and call it.

## How the connectives behave

- **`bind`.** It needs only same-members stability, not `Ext`. `M`'s run returns a list with the
  same members (`wpTS`), and at that list two things are carried by `gDenC_same`/`vC_same`: the
  context that `N` needs, and the stack that `C` is eliminated by. `cC_bind` is proved by
  induction on `C`, pushing each `⊸`/`&`/`∀` frame into the evaluation context and each `⊸`
  argument into the frame.
- **`Ext` is used once, at the thunks.** The environment moves by `gDenC_local`. `λ` and `Λ`
  need no Kripke quantifier: a computation runs at the list it is used at.
- **`&` with a shared context.** This is immediate. `cC (C & D)` is a conjunction at the same
  resource, and each projection hands the whole context resource to its branch. A projection is
  three head steps (β, `case`, `;`).
- **`⊤` absorbs the context.** `cC ⊤ = True`, because there are no stacks. `topI` needs no premise
  about `Γ`, and `zeroE` likewise takes any rest of the context. This also makes `vC (U ⊤)` hold at
  every resource, so a `U ⊤` value can hold any cells. Nothing eliminates `⊤`, and a linear value
  cannot be dropped, so this cannot leak out of a closed `F 1` program. No program here puts a
  cell under a `U ⊤`.

## Why the thunk encoding depends on the type

Under a uniform `λ_. M` encoding, forced by `x ()`, `𝒱⟦U (A ⊸ F B)⟧(v)` would run `v () v'`,
while `vX`'s `⊸` clause runs `v v'`. A closure can sit in the heap under `Ref`/`Imm`/`Mut`, so no
value-level coercion reconciles the two. So a thunk of `F A` is `λ_. M`, and a thunk of `⊸`, `&`,
`⊤` or `∀` is the λ-value itself (`thunkV`, `forceE`).

## Limitations

- **The preimage in `Imm`.** The typed world's records and coherence (`FrameRec.T`, `Coh`,
  `CohE`, `TyEq`, `vShape`, `Chain`, the `TW` transitions) are typed at BoLo's `Ty`. `vC`'s `Imm`
  clause therefore reads `CohE` at a `cbv`-preimage of the payload. Where the payload has no
  preimage, the clause holds at no resource, so that `Imm @a A` is empty (`vC_imm_outside_image`).
  The payloads outside the image are these, and every type that contains one:
  - `0` (`cbv_ne_zero`).
  - `U (F A)` (`cbv_ne_thunk_ret`), `U (C & D)` (`cbv_ne_thunk_amp`) and `U ⊤` (`cbv_ne_thunk_top`).
  - A curried computation arrow `U (A ⊸ B ⊸ C)` (`cbv_ne_thunk_arr_arr`). BoLo's curried `⊸` is
    `U (A ⊸ F (U (B ⊸ F C)))`.
  - `U (∀'x ⊏ @b. C)` with `C` not an `F`, and `U (A ⊸ C)` with `C` not an `F`.

  `Ref`, `Mut`, `[@a]`, `!` and `Unk` at those payloads have their full clauses. Only `Imm` loses
  meaning.
- **Rules available only at translated types.**
  - The borrow axioms are constants at `cbv T` only. The `_compatX` proofs go through the
    records, so, for example, `withbor` at `Ref (U (F 1))` is not available.
  - `[]I` is available only at `cbv T` and at a context `LiveEq` to a translated one. Its
    premise `Δ ⊨ Γ ⊐ @a` and its proof (`gSepX_outlives`, i.e. 6.60 at `vX`) are stated on `Ty`.
  - `∀E` is available only at `F (cbv T)`. There is no lifetime substitution on `CTy`, so no
    `vC` analogue of `vX_tyEq`.
- **What re-typing at `VTy` would take.** Every record would carry a `VTy`:
  - `FrameRec.T`, `Coh`/`CohE`, `TyEq` and `vShape` over `VTy`.
  - `Chain` and `RefPos` over `VTy`, with `U` as an opaque leaf like `⊸` is now.
  - `TW.rebEndDeep`'s `S₀`.
  - Then the reborrow machinery re-proved over `VTy` (`Invariant`, `Images`, `Reborrow`,
    `ReborrowShapes`, `FrameRules` and `withload_compatX`). The `Imm̲` metafunction
    and 6.60 (`vX_outlives`) would also need `VTy` forms.

  `vC` would then read `CohE` at the payload itself, and the image restriction would disappear.
  This step does not attempt it.

## Open items

- **The syntactic CBV embedding** `DerivesWf Δ Γ e T → CDerives … ⟦e⟧ (cbv T)` is not attempted.
  Only the semantic form, `fundamentalCBV`, is proved. The syntactic form needs an ANF term
  translation with de Bruijn shifting and a weakening lemma for `CDerives`.
- `∀E` at a general `C`, and `[]I` at native types, need `CTy` lifetime substitution and a `VTy`
  outlives judgment with its 6.60.
- **Encoding.** Values are typed at expressions, not only syntactic values: `SemV` is `F A`,
  so a value former's premises are run by `wpTS`. The ANF rules only ever give them value
  expressions after substitution.

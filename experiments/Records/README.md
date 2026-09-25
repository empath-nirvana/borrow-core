# Records: records and variants as derived forms

**Question.** `[CONF]` §5 (415:25): *"Pure constructs, like records or variants, would be
straightforward to add since they would not require changes to the model, though one would
likely wish to add corresponding reborrowing rules."*  Does that hold here, and what does field
access through a borrow give?

Build: `lake build Records`. Nothing in `Paper/`, `Support/` or `Examples/` is changed.

## Route: derived forms

Records and variants are encoded in BoCa's own formers:

    {l₁ : T₁, …, lₙ : Tₙ}    ≜  T₁ ⊗ (… ⊗ (Tₙ ⊗ 1))           recTy
    ⟨l₁ : T₁ | … | lₙ : Tₙ⟩  ≜  T₁ ⊕ (… ⊕ Tₙ),  n ≥ 1          varTy

Every rule is a derived rule of `DerivesWf`, with no constructor added. So the Fundamental
Property and adequacy apply as they are, and no model or proof is copied. I chose this over
new formers (route (b)) because the encoding turned out to give everything asked for. Each
reborrowing clause below is the binary one iterated, and no rule was needed that is not a
composite. New formers would add `Imm̲` clauses and re-prove the `⊗`/`⊕` cases of 6.131 and
the FP. Nothing here suggests that work would find anything the encoding misses.

The only thing the encoding costs is the shape of the terms. A variant needs at least one case,
because BoCa has no empty type. In `recLet`'s body, field `k` of `n` sits at de Bruijn index
`2(n−k)+1`, with the consumed tails in between (`recCtx`).

## What is derived

`Records/Encoding.lean`, `Records/Borrows.lean`:

| form | term | rule |
|---|---|---|
| `{lᵢ = eᵢ}` | `tuple` | `recI` |
| `let {lᵢ = xᵢ} = e in b` | `recLet` | `recE` |
| `e.lᵢ`, other fields affine | `getAt` | `getAt_wf` |
| `lᵢ e` | `injAt` | `injAt_wf` |
| `case e {lᵢ x ⇒ bᵢ}` | `vcase` | `vcase_wf` (premises `Branches`) |
| read `lᵢ` of `Imm @a {…}` | `loadField` = `withload` + `getAt` | `loadField_wf`, `loadField_sem` |
| match on `Imm @a ⟨…⟩` | `loadCase` = `withload` + `vcase` | `loadCase_wf` |
| run `g : Tᵢ ⊸ Tᵢ ⊗ T₂` on `lᵢ` of `Mut @a {…}` | `swapField` = `withswap` + `modAt` | `swapField_wf`, `swapField_sem` |

`Affine` is the set of types a closed term consumes (`dropT`): `1`, `⊗`, `⊕`, `Imm`, `Mut`, `Unk`,
`!T`. `affine_immReborrow` shows that **every `Imm̲ 'b T` is affine**. So a record read through an
immutable borrow can always be projected to one field, whatever the other fields are. An owned
record can be projected only when the other fields are affine. That is linearity, not
borrowing.

## Reborrowing clauses

| clause | Lean | status |
|---|---|---|
| `Imm̲ 'b {lᵢ : Tᵢ} = {lᵢ : Imm̲ 'b Tᵢ}` | `immReborrow_recTy` | definitional unfolding of row 2.49's `⊗`/`1` clauses |
| `Imm̲ 'b ⟨lᵢ : Tᵢ⟩ = ⟨lᵢ : Imm̲ 'b Tᵢ⟩` | `immReborrow_varTy` | same, `⊕` |
| `Δ ⊢ {lᵢ : Tᵢ} ⊐ @a ⟺ ∀i. Δ ⊢ Tᵢ ⊐ @a` | `outlives_recTy` | rows 2.31/2.32 iterated |
| `Δ ⊢ ⟨lᵢ : Tᵢ⟩ ⊐ @a ⟺ ∀i. Δ ⊢ Tᵢ ⊐ @a` | `outlives_varTy` | row 2.33 iterated |
| `[α] 𝒱⟦{lᵢ:Tᵢ}⟧ ⊨ ↺_α 𝒱⟦{lᵢ : Imm̲ 'x Tᵢ}⟧` (6.131) | `reborrow_vDen_recTy` | holds: `reborrow_vDen` at `recTy` |
| same at variants | `reborrow_vDen_varTy` | holds |
| typed-world 6.131 (`vShape`) at records / variants | `reborrow_vShape_recTy`, `_varTy` | holds: `Typed.reborrow_vShape` |
| 6.60 at records, typed world | `vX_outlives_recTy` | holds: `Typed.vX_outlives` |

Every semantic fact is the library's lemma applied at the encoded type and rewritten by the
fieldwise clause. `withbor`'s form (2) side condition `Δ ⊢ T₁ ⊐ @b` at a record is
`outlives_recTy` (used in `mutFields`).

## Programs

`Records/Programs.lean`. Each closed program has an adequacy instance (`…_runs`, from
`Fig16.LogRel.Typed.adequacy`) and an interpreter run (`…_eval`). Each `…Obs_eval` checks the
values read or written.

- **`readFields`**: `r : Ref {flag : 1 ⊕ 1, cell : Ref (1 ⊕ 1)}` is borrowed at `'a`, and each
  field is read with `loadField`. The load runs at a fresh `'b ⊏ 'a`, and its callback gets
  `{flag : 1 ⊕ 1, cell : Imm 'b (1 ⊕ 1)}`.
  - The unboxed `flag` arrives as a **copy** of its value. It has no lifetime, and it leaves
    both the load and the borrow.
  - The boxed `cell` arrives as a **view at `'b`**, not at `'a`. It cannot leave the load:
    `[]I` at `'b` would need `Δ ⊢ Imm 'b T ⊐ 'b`, and `not_outlives_own_view` shows that no
    satisfiable `Δ` entails it. Its contents are read by a second `withload` at `'c ⊏ 'b`.
    `readFieldsObs_eval` checks that the values read are `(inj₂ (), inj₁ ())`.
- **`getRefFn`** (an open derivation in `Δ = ['c ⊏ ⊤]`) has type
  `∀'a. Imm 'a {r : Imm 'c (1⊕1), n : 1⊕1} ⊸ Imm 'c (1⊕1)`. A borrow stored in a field keeps
  its own lifetime `'c` through the load, by clause (6) `Imm̲ 'b (Imm @c T) = Imm @c T`. This is
  Rust's `fn get<'a,'c>(s: &'a S<'c>) -> &'c T { s.r }`.
- **`mutFields`**: `Mut 'a {flag, cell}`. `flag` is flipped and `cell` is overwritten, each
  with `swapField`. There is no `Mut` to a field. `withswap` moves the **whole record** out of
  its cell, the callback rebuilds it with one field changed, and `withswap` stores the whole
  record back. The boxed `cell` is written through a `Mut 'c` of its own cell, which `pokeG`
  takes with `withbor` on the owned `Ref` inside the callback. That borrow ends inside the
  callback. `mutFieldsObs_eval` checks the final contents `(inj₁ (), inj₂ ())`.
- **`matchSome`**: `Imm 'a ⟨some : Ref (1⊕1) | none : 1⟩` is loaded at `'b` as
  `⟨some : Imm 'b (1⊕1) | none : 1⟩` and matched with `loadCase`. The `some` branch reads the
  payload's cell at `'c ⊏ 'b`. `matchSomeObs_eval` checks that the value read is `inj₁ ()`.

## Findings

1. **The claim holds here.** Records and variants need no model change. They need no new
   typing constructor either, and the reborrowing rules come with the encoding. `Imm̲`, outlives
   and 6.131 at records and variants are the binary `⊗`/`⊕`/`1` cases iterated. No rule was
   needed that is not a composite of the binary ones.

2. **What field access gives, compared with Rust:**

   | Rust | here |
   |---|---|
   | `&'a self.f`, `f: Box<T>` | `Imm 'b T` at the load's `'b ⊏ 'a`, scoped to the `withload` callback. At `'a` it is refuted by `experiments/Projection` and `Relaxed` (6.38) |
   | `&'a self.f`, `f: T` unboxed | no reference at all: the field's image `Imm̲ 'b T` is a copy of its value, with owned cells inside it turned into views at `'b` |
   | `self.f` where `f: &'c T` | `Imm 'c T`, at its own lifetime, which can leave the load (`getRefFn`) |
   | `self.f` where `f: Copy` data | a copy that can leave the load (`readFields`) |
   | `&mut self.f`, `f: T` unboxed | none. The update is `swapField`: the whole record is moved out, rebuilt and stored back |
   | `&mut self.f`, `f: Box<T>` | `Mut 'c T` of the field's cell, only inside a `withswap` callback on the record (`pokeG`) |

3. **Which gaps are about cells and which about the `imm` witness.**
   - *Cells: fields are not locations.* A borrow is a location (`Imm @a T` and `Mut @a T`
     denote `ℓ` with a cell at `ℓ`, `[TR]` p. 4), and a cell holds one whole value. An unboxed
     field has no location, so neither `Imm 'a T` nor `Mut 'a T` of it has anything to point
     to. This covers both unboxed rows above. Reading gives a copy through `Imm̲`. Writing goes
     through the enclosing record's cell (`swapField`). This is a gap in the *memory model*
     (no interior addresses), not in the borrow rules.
   - *The indivisible `imm` witness.* A boxed field does have a cell, and a view of it exists,
     but only at a fresh `'b` scoped to one `withload`. Giving it the borrow's own `'a` is the
     same-lifetime projection refuted in `experiments/Projection` and `Relaxed`. An `imm` cell
     carries one witness for the whole payload, and 6.38 lets the frame end against it. The
     record encoding changes nothing here: the boxed-field row is exactly the `Ref A ⊗ Ref B`
     configuration of those experiments.
   - The `Mut` analogue for a boxed field (splitting `Mut 'a {…}` into `Mut 'a` borrows of
     the fields' cells) is not attempted. I have not derived it, and I have not checked whether
     an obstruction to it is real.

## Axioms

Every result listed above has `#print axioms` ⊆ `[propext, Classical.choice, Quot.sound]`. I
checked this with a scratch file that imports `Records`. The directory has no `sorry`,
`axiom`, `native_decide`, `implemented_by`, `opaque`, `partial` or `unsafe`.

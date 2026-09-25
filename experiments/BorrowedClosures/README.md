> **Where the code is.** `Reborrow.lean` (stage 1) and `EnvCheck.lean` (the environment check)
> are here, in the `Experiments` library (`lake build Experiments`), built against this
> repository's `Paper`/`Support`. The library now carries stage 1 itself as
> `Support/Model/Unr.lean` (`SPEC.md` §2), so `Reborrow.lean` hides `BoLo.Free`.
>
> The `fn T₁ T₂` fork (`FnFork/`, stage 2) is archived, not copied: it lives in `borrow_lang`'s
> history at `Experiments/BorrowedClosures/FnFork/`, commits `d1f3929` (verbatim copy of the
> typed-world FP closure), `8d43821` (`fn` through the literal relation), `6b8a77e`
> (`EnvCheck`), `dfe907b` (a borrowed closure, called); stage 1 is `efa2084`. The last
> `borrow_lang` commit containing it is `a31b498`. It is superseded by the exponential `!T`
> (`SPEC.md` §2, `experiments/Bang/README.md`): `fn T₁ T₂` is `!(T₁ ⊸ T₂)`.

# BorrowedClosures — can a borrowed closure be called?

**Today.** `Imm̲ 'b (T₁ ⊸ T₂) ≜ Unk` ([CONF] Fig. 8 clause (4)): an immutably borrowed
closure can only be forgotten. [CONF] 415:9: a closure *"may hold linear references"*, so
*"there is no view at which it would be safe to access the payload"*. [TR] 6.131's `⊸`
bullet reborrows a closure to nothing: *"`[α] 𝒱⟦T₁ ⊸ T₂⟧δ(v) ⊧ ↺α emp`"*.

**Mode split** (ModesLabels). By what they capture, closures are `lin` (Rust `FnOnce`),
`aff` (`FnMut`) or `unr` (`Fn`: captured resource all-`imm`). The paper's `⊸` is the `lin`
one. An `unr` closure is duplicable by `dup_sound`'s argument.

**Stage 1 — the model-level licence** (`Reborrow.lean`; standard axioms):

- `reb_self_of_imm`: an all-`imm` resource in `Res_α` is its own reborrow,
  `ρ ∈ reb_α(ρ)`. By induction on the domain: `[TR]` 6.123's construction at each cell,
  glued with 6.61.
- `reborrow_self_of_imm`: `[α] P ⊨ ↺α P` for every `P` whose resources are all-`imm`.

So at an `unr` closure type, 6.131 holds with `Imm̲ 'b T ≜ T` instead of `Unk`: reborrowing
an `Fn` closure keeps it whole and callable. Nothing about the paper's `lin` closures
changes.

**Stage 2 — the typed world (not done).** The FP runs at `SemX`, where an `Imm` payload is
held at the observable view, `⊸` relaxed to `True` (§12.69). The relaxation is what
`obs_transfer` (TypedRel.lean:810) spends: moving a payload's view between two pieces of
one escrow, *"at a `⊸`/`∀` position both sides are `True`"*. Keeping `unr` closures
unrelaxed needs that transfer at an `unr` arrow: from the piece `A` the program holds to
the image piece `B`, both matching the escrow `R`.

Why it may go through: stage 1 says the identity is a valid reborrow of an all-`imm`
resource, and the typed world's chooser (`RebChooseTW`) picks the reborrow compatible with
the views already held. If it can pick the identity on the closure's cells, `B`'s cells at
the closure are `A`'s and the transfer is equality. Where it could fail: `CellMatch` lets an
`imm` cell carry fewer lifetimes in `B` than in `R`, so the transfer may need `𝒱⟦⊸⟧` at an
all-`imm` resource to be insensitive to shrinking `imm` lifetime sets.

Stage 2 needs a type former for `unr` arrows, so it forks `Ty` and the typed world rather
than extending them from here. The first lemma to state is `obs_transfer` at the new
arrow.

## Stage 2 — the fork (`FnFork/`, in progress)

`FnFork/` is the typed-world FP's import closure copied verbatim (27 modules; baseline commit
`d1f3929`), built as its own library `FnFork` so its names never meet `BoCa`'s. Added:

- `Ty.fn T₁ T₂`, the `⊸` codata former at mode `unr`. In a spec this is a mode index on the
  codata former, not a separate former: of the 47 `⊸` match arms, all but a handful are
  copied verbatim for `fn` (scoping, substitution, well-formedness, `TyEq`, …).
- `Imm̲ 'b (fn T₁ T₂) ≜ fn T₁ T₂`.
- `FnFork/Unr.lean`: `UnrRes` (only `imm` cells) and `reb_self_of_imm`.
- Literal relation: `𝒱⟦T₁ ⊸ω T₂⟧δ(v) ≜ 𝒱⟦T₁ ⊸ T₂⟧δ(v) ∧ UnrRes`; `[TR]` 6.131's `fn` case is
  `reborrow_self_of_imm` (`Fig16LogRel.lean`, `reborrow_vDen`). Builds.

**Where it stops: `TypedImage.image_dom`.** The typed world chooses each reborrow's image from
types (§12.69, §12.71): at `⊸` the image is `emp`; at `Ref`/`Imm`/`Mut` it is the one cell the
value's location names, read off the escrow. `image_dom` says every cell of an image sits over
a cell of the escrow, from the two shapes alone (`vShape (Imm̲ 'x T) δ' v c`,
`vShape T δ v R`). At `fn` the image must be the closure's captured resource, and neither the
type nor the value determines it: `𝒱⟦fn⟧` is not precise, since spare `imm` cells can be
dropped into `wp`'s `ρ⁺` (which forbids only `own` cells). So `vShape fn` cannot say which
escrow cells the image sits over.

I have not derived `image_dom` at `fn` and have not verified that any obstruction is real.
The ways on are design choices, not proof steps:

1. **Record the footprint in the world.** The typed world already records how a payload was
   made (the type at each borrow, §12.71); an `unr` closure's captured resource is the same
   kind of history. The chooser reads it from the record.
2. **Make `fn` precise.** The clause pins the resource to the closure's top-level locations.
   Captured `Unk` values break this (a value typed `Unk` can mention locations while its
   resource is `emp`), so it needs a footprint discipline on `Unk` too.
3. **Leave the image unchosen at `fn`.** Re-admits an escrow hypothesis at `withload` for
   closure payloads, which is what the typed world was built to remove (§12.68).

### The environment check (`EnvCheck.lean`, here; standard axioms)

Rust-style semantics for `Fn`: a closure whose body is valid with its environment viewed
through `Imm̲`, so it may own its captures and only read them. For the typed world to choose
a borrowed closure's image, the closure's shape must say which escrow cells its environment
occupies.

- `envShape_unlinked`: packing the environment existentially (`∃ E w, S E δ w ρ`) does not
  link image to escrow. For any shape family agreeing with `vShape` at `1` and `Ref`, an image
  and an escrow of that shape exist with an image cell over nothing in the escrow — the
  failure `image_dom`'s `fn` case would have to rule out.
- `envValue_unlinked`: fixing `E` in the arrow type does not help while the environment
  value is chosen independently (`Ref 1` at location 0 against location 1).

So the link needs both halves determined by the closure: the environment's **type** in the
arrow's type, and its **value** a component of the closure value — closure conversion in the
calculus, `(w, code)` with `code` closed. Then the arrow's shape is `vShape` of a pair
`E ⊗ (closed code)`, and `image_dom`'s arrow case is its `⊗` case. This is how Rust types
closures: each closure has its own type naming its captures, and `impl Fn` hides it only at
API boundaries.

## Stage 2 result — closed code through the typed world (`FnFork/`; builds, standard axioms)

With closure conversion a borrowed closure is a borrowed pair `(env, code)`: the environment is
data, which `Imm̲` already views correctly, and the code is **closed**. So the unit of work is a
type of closed code, `fn T₁ T₂` (Rust's `fn` pointer): the `⊸` clause at resource exactly `∅`.
Its reborrow image is `∅`, determined, which is what `image_dom` needed.

- **Relation.** `vX b (fn T₁ T₂)` = resource `∅` and the `⊸` clause, the same in both modes (kept
  whole in the observable view); `vShape (fn _ _) = emp`; `Imm̲ 'b (fn T₁ T₂) = fn T₁ T₂`.
  Literal side: `𝒱⟦fn⟧ = 𝒱⟦⊸⟧ ∧ ρ = ∅`, 6.131's case by `reborrow_self_of_imm`.
- **Typing** (`DerivesWf`): `fnI` (a `λ` over a dead context), `fnE` (application),
  `copyFnAx`, `forgetFnAx`.
- **FP.** `Fig16.LogRel.Typed.fundamentalProperty` and `adequacy` hold over the extended
  `DerivesWf`, with `fnI_compatX`, `fnE_compatX`, `copyFn_compatX`, `forgetFn_compatX`.
  `withload_compatX` is unchanged: its proof goes through `relabel_obs`, whose `fn` case is
  now the kept payload.
- **Program** (`Program.lean`): `callBorrowed` stores `λx.x : fn 1 1` in a cell, borrows it
  immutably, loads it (`Imm̲ 'b (fn 1 1) = fn 1 1`), copies it and calls it twice through the
  borrow, then frees the cell and calls it a third time. `callBorrowed_runs` is its adequacy
  instance: it runs from `∅` to `()` and `∅`. The paper's version of the same program
  (`loadClosure`) can only `forget` what it loads.

**Arms that read the difference.** `vX`'s clause, `vX_local`, `vO_obs`, `vX_vShape`,
`obs_transfer`, `relabel_obs`, `vShape`, `Imm̲`, `lfree_immReborrow`, and the literal clause and
6.131 case. Everything else is the `⊸` arm verbatim.

**Removed from the fork** (they state facts about the printed judgment that the extension
changes): `DerivesWf.toDerives`, and the literal-relation FP at `Sem`.

**Not done.** Environments: a closure capturing data is the pair `(env, code)` with
`code : fn (E ⊗ T₁) T₂`; the capture is the paper's own data borrowing and needs nothing new,
but no program here exercises it. `FnMut` (a `Mut` borrow suffices to call) is not attempted.

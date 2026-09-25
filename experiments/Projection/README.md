# Projection: an immutable borrow projected at the same lifetime

**Question.** From `v : Imm 'a (Ref A ⊗ Ref B)`, an immutable borrow of a cell holding a pair
of owned references, can we soundly get `Imm 'a A`? That is a view of the first component's
contents at the same lifetime `'a`. Rust does this with `&'a self.field`. Today the only route
is `withload`, and it gives views at a fresh `'b ⊏ 'a` that cannot leave its callback.

Build: `lake build Projection`. Code: `Projection/Obstruction.lean`. It builds against this
repository's `Paper`/`Support` without changing them.

## Result

**No, not at the typed world as it stands.** The refutation is machine-checked. Its axioms are
`propext`, `Classical.choice` and `Quot.sound`.

- `ProjSpec proj a A B` is the semantic statement of a projection `proj : Loc → Expr`. It takes
  any expression, including one that uses `withload` internally. From
  `vP (Imm a (Ref A ⊗ Ref B)) ls δ (loc ℓ) ρ` we get
  `wpTS ls (proj ℓ) (λ ls' w. vP (Imm a A) ls' δ w ∧ w = loc m with m the first component of
  the pair at ℓ)` at `ρ`.
- `no_projection proj x : ¬ ProjSpec proj (.var x) .unit .unit`.

The configuration is built by the library with every hypothesis discharged:

1. Three `wpTS_alloc` runs from the empty typed world (`TW.empty`) allocate `l₂`, `l₁` and
   `ℓ ↦ (l₁, l₂)`.
2. `[TR]` 6.64 (`wpTS_I_frameX`) borrows `ℓ` at `T = Ref 1 ⊗ Ref 1`.
3. In its callback, `proj` runs on the borrow it is handed, `ℓ ↦ imm({α}, (l₁,l₂), σ)`, read at
   `'x ↦ α`.

The whole `wpTS` is then refuted at the world reached after the allocations.

### Where it fails

`callback_blocked` gives the argument, and `no_view_at_tag` gives its last step.

- **Coherence (`CohE`) is not the obstruction.** The projected location `l₁` is a chain
  position of the frame record (`Chain.one (RefPos.tensorL (RefPos.ref …))`). `Coh`'s second
  disjunct accepts it.
- **The lifetime-set representation is not the obstruction.** The projected cell has the same
  shape as the one `TW.rebDeep` adds at a chain position, `imm(s′, (), ∅)` at `l₁`. Only its
  lifetime differs: `α ⊑ ⊓s′` instead of a fresh `β`.
- **The reborrow chooser (6.150 / `RebChooseTW`) is never reached.** The refutation does not
  touch it.
- **The obstruction is the typed world's tag discipline.** `wpTS` requires the post-world to be
  `Tagged`. `Tagged` gives every record `(r, t) ∈ ls` a root `q` with `FrameLife W q t`.
  `FrameLife`'s second conjunct requires every `imm` view in `ag(W)` at a lineage location of
  `q` to have all its lifetimes **strictly** below `t`. Here `r` is the frame record, and its
  tag is the frame lifetime `α`, because 6.64 hands over the borrow at exactly the tag it
  records. `l₁` is an `own` cell of `r.R`. A view `Imm 'a 1` at `δ('a) = α` needs a cell at
  `l₁` with `α ⊑ ⊓s′`, while `FrameLife` needs `⊓s′ ⊏ α`.

The goal that closes as `False` is exactly `no_view_at_tag`'s:

    Tagged W ps ls → (r, α) ∈ ls → r.R.get m = some (own u) → AgW W aW → ICpAt aW ρ m →
    ptoImmS m α ls₀ P ρ → False

The generating family `TW` has the same restriction at its source. `rebDeep`, the only
constructor that adds a view at a chain position, takes `β` with `W.InStratum β`, below every
lifetime of the world. No constructor adds one at the frame's lifetime.

### Pointers for a follow-up (not verified)

- `FrameLife.2`'s strictness is consumed in `not_rel_lineage` and `lifeBound_of_tagged`
  (`Support/TypedWorld/Wp.lean`). In both, the other inequality is already strict, so `⊑` would
  seem to do there. I have not checked the maintenance lemmas (`frameLife_frame`,
  `frameLife_reb_like`) or `NestLife` (`TI`). `NestLife` also asks deeper chain views to be
  strictly shorter than their parent chain view, so a two-level projection (`Ref (Ref A)`)
  would meet it too. I have not derived that a relaxed invariant is consistent and have not
  verified that any further obstruction is real.
- A projection whose result is not tied to the first component (no `FstLoc` conjunct) is not
  refuted here. Its output could be a view of another record's own cell at `α`. I have not
  derived either direction.
- `'a` strictly shorter than every lifetime of the world is the `rebDeep` regime. I have not
  derived a projection there.

## Properties of locations and places the proof relied on

- The witness of the borrowed cell owns the component cell. `𝒱X⟦Ref 1 ⊗ Ref 1⟧` at `(l₁, l₂)`
  puts `l₁ ↦ own(())` in the witness `σ` (`t0_payload`).
- A frame record's escrow is the witness of its cell. `LeInvW`, from `TW.inv`, gives
  `ψ.wit = r.R` at `r.le`. `ICp` transports the handed cell into `ag(W)`, so `r.R = σ`.
- Sub-resource cells appear in the flattened world. `ICpAt` runs along `●` and `AgW`
  (`icpAt_left`, `icpAt_right`, `icpAt_agW`) and keeps the lifetime sets.
- Records are tagged at the frame lifetime. `AddAt [] ls' α` makes every record of the
  callback's list tagged `α`.
- A place is a lineage location. `LinLoc q m` holds for an `own` cell of the escrow of any
  lineage member of `q`.
- The location returned is the first component (`FstLoc`), that is, `u = (loc m, _)` for the
  cell's value `u`.

The argument did not use disjointness of the two inner cells, the second component, or any
fact about `Steps`: only `wpTS`'s post-world clause (`TW`, `Tagged`, same list members). So it
applies to any new machine primitive given a `wpTS` specification of this shape.

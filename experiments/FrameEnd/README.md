# FrameEnd: a frame's end that subtracts the image at its own lifetime

**Question.** `experiments/Relaxed` refutes a same-lifetime `Imm` projection with
`frame_view_excluded`, which is `[TR]` 6.38 read at a frame's borrow. The survey's option 5.1(b)
(`docs/prior-art-borrow-splitting.md`) proposes that a 6.64 frame's end remove the cells at the
frame's lifetime `α` before it restores `ℓ ↦ own(v) ● ρv`, in the way 6.52 removes a reborrow's
image before 6.59's final `↭`. The views stay forgettable in `ρ⁺`, and the restore still comes
from the frame's own witness. This experiment asks:

1. With that change, do the Fundamental Property and adequacy still hold?
2. Does a same-lifetime `Imm` projection then go through?
3. Does a same-lifetime `Mut` view of one boxed field (L3) follow?
4. Does splitting `Mut_α` into two `Mut_α` views (L2) come with it?

Build: `lake build FrameEnd`. `FrameEnd/` is `experiments/Relaxed/Relaxed/` copied under the
namespace `BoCa.Fig16.LogRel.FrameEnd`, with the changes below. `Relaxed` and the library are
unchanged.

## The change

`TW.immEnd` (`World.lean`), the typed world's exit from a 6.64 frame for the record
`r = (ℓ, v, R, T, δ)` with the frame cell `ℓ ↦ imm(s, v, R)`, now works in two steps:

1. **Subtract** `c|dom(R|own,mut)` for some `c ∈ reb_{⊔s}(R)`. This is 6.52's `ρ_reb` at the
   frame's own lifetime. As in `TW.rebEnd`, it is `W = W₁ ● c.restrictDom R.exclPart`. A
   non-empty subtraction requires `StratumLe W₁ (⊔s)`, which is how 6.52's `@ρ_e ⊐ α` and
   `@ρ′ ⊐ α` read when the frame cell itself is at `α`. An empty subtraction requires nothing.
2. **Restore**: `W₁ = ℓ ↦ imm(s, v, R) ● Y` becomes `ℓ ↦ own(v) ● R ● Y`. This step is the old
   `immEnd` unchanged.

With `c = ∅` this is the old constructor. No predicate or invariant was added. The subtraction
uses `reb_α`, `restrictDom` and `exclPart`, which `rebEnd` already uses.

## 1. FP and adequacy: hold

`FrameEnd.fundamentalProperty`, `adequacy`, `theorem32` and `corollary33` depend on `propext`,
`Classical.choice` and `Quot.sound` only.

| Lemma | File | Change |
|---|---|---|
| `TW.immEnd` | `World.lean` | the subtraction step above |
| `ti_endReb` | `Invariant.lean` | premise `W'.InStratum β` weakened to `StratumLe W' β`. It is used only for `NestLife`'s `y = β` case, which now closes at `x ⊏ β` instead of `β ⊏ ⊓s′` |
| `ti_sub` (new) | `Invariant.lean` | the subtraction keeps `TI`: `W₁ = W` when nothing is subtracted, otherwise `ti_endReb` at `β = ⊔s` |
| `single_imm_get` (new) | `Invariant.lean` | `ℓ ↦ imm(s, v, R) ● Y` holds `imm(s′, v, R)` at `ℓ` |
| `TW.inv` (`immEnd`, `rebEnd`, `rebEndDeep` cases) | `Invariant.lean` | `immEnd` is `ti_sub` followed by `ti_end`. The `rebEnd`s pass `stratumLe_of_inStratum` |
| `TW.valid` (`immEnd` case) | `Invariant.lean` | pattern arity only |
| `linLife_sub` (new) | `Wp.lean` | removing a part keeps `LinLife`. This is the argument of the old `rebEnd` case, factored out |
| `TW.linLife` (`immEnd` case) | `Wp.lean` | `linLife_sub`, then the old argument at `W₁` |
| `wpTS_I_frameX` (6.64) | `FrameRules.lean` | the exit passes `c = ∅` (`reb_empty`, `restrictDom_empty`) |
| `frame_image_empty` (new) | `FrameRules.lean` | at 6.64's end, 6.52's `ρ_reb` is empty (below) |

No other lemma changed. Every lemma that establishes `TW` and does not end a frame is untouched.

**The subtraction removes nothing at 6.64's end.** `frame_image_empty` shows this under 6.38's
hypotheses, which are exactly what the inner run gives the frame rule (H21's
`ρ_b ● ρᵢ ↭ ρ′ ● ρ⁺`, with `ρ⁺` own-free). Under them, any part of `ρ⁺` of the form
`c|dom(ρv|own,mut)` is `∅`. The reason is 6.38's conclusion `ρ′ ● ρ⁺/ℓ # ρv ● ℓ ↦ own(v)`, so
`ρ⁺` holds no cell where `ρv` holds an `own` or `mut` cell. The frame rule therefore uses the new
exit with `c = ∅`. The non-empty branch belongs to the family `TW` that `wpTS`'s frame
quantifier ranges over, and FP holds with it there. No proof in the development takes that
branch. I did not build a `TW` world that reaches it. (`TW.reb` at `β = α` of a frame record,
which `Relaxed`'s `StratumLe` premise admits, would create such an image, but nothing in FP
calls it at that `β`.)

## 2. Same-lifetime `Imm` projection: still refuted, by `↭` at the projection's own run

`FrameEnd.Projection.ProjSpec` is `experiments/Projection`'s: from `vP (Imm a (Ref A ⊗ Ref B))`
at `ℓ`, `wpTS (proj ℓ)` returns `vP (Imm a A)` at the pair's first component (`FstLoc`).
`FrameEnd.Projection.no_projection proj x α : ¬ ProjSpec proj (.var x) .unit .unit`
elaborates at FrameEnd's world **with the proof text unchanged**, for every `proj : Loc → Expr`.

The frame-end change cannot reach this refutation. `no_projection` enters the frame with
`TW.immFrame` and refutes the `wpTS` of `proj ℓ` itself: that run's post-condition carries
`ρᵢ ↭ ρ′ ● ρ⁺` from `ρᵢ = ℓ ↦ imm({α}, v, ρv)`. The projection is a run that returns a view, and
the frame ends later. So the view is excluded before any frame ends.

**Key lemma: `FrameEnd.Views.imm_view_rejected`.** It states the obstruction directly as
`↭`'s `imm` clause, with no typed world, no `wp` and no 6.38:

    l ≠ m → ResU.UpdV (ℓ ↦ imm(s, v, m ↦ own(u))) π → π.get m = some ψ → ψ.kind = imm → False

`⦇ℓ ↦ imm(s, v, m ↦ own(u))⦈(m) = own(u)` (`flat_imm_single_own`). A top-level `imm` cell of `π`
at `m` puts an `imm` cell at `m` in `⦇π⦈` (`flat_imm_of_top`, via `○`'s clause (5):
`imm ○ own = imm`). `UpdImm` requires both flattenings to hold the same `imm` cells. The lemma is
stated for a one-cell witness. `frame_view_excluded` (6.38) covers any witness `ρv`, the pair
`l₂ ↦ () ● l₁ ↦ ()` included.

So the nearest precise semantic form of the projection is the update
`ℓ ↦ imm({α}, v, ρv) ↭ π` with a view at `m` in `π`, and `↭` refuses it. No resource entailment
can produce the view, because an entailment does not add cells. No term can produce it either,
because every `wpTS` run ends in a `↭`. The view's lifetime set is arbitrary in the lemma, so the
exclusion holds at `{α}` and at every other lifetime set.

**What would be needed, and why I stopped.** For the view to exist, the run that returns it has
to be allowed to end outside `↭` by exactly the image cells: something like
`ρ ↭ (ρ′ ● ρ⁺) ⊟ κ`, where `κ` is an `α`-image of a record's witness at the record's tag. That
changes `wpTS`'s `↭` conjunct at every run. It does not change the frame's end. It is a new
relation, and every consumer of the `↭` conjunct would have to be re-proved against it: bind
(6.49), 6.38 and 6.39 in the frame rules, and 6.59 in the reborrow rule. The task allowed only
the frame-end change and nothing beyond 6.52's vocabulary, so I did not build it. I have not
derived FP for such a `wpTS` and have not verified that any obstruction to it is real.

## 3. L3, a same-lifetime `Mut` view of one boxed field: excluded the same way

**`FrameEnd.Views.mut_view_rejected`**:

    ρw.get m = some (own u) → ResU.UpdV (ℓ ↦ mut(b, v, ρw, P̂)) π →
    π.get m = some (mut(b₁, u₁, χ₁, P̂₁)) → False

This holds at every `b₁` and `P̂₁`, `b₁ = b` included. `ex` walks the `mut` witness, so
`⦇ℓ ↦ mut(b, v, ρw, P̂)⦈(m) = own(u)` (`xpath_ex`). A top-level `mut` cell at `m` is exclusive,
so it is in `⦇π⦈`. `UpdMut` requires both flattenings to hold `mut` cells at the same locations
with the same lifetime and predicate. `↭` lets the parent's value and witness change, so a
nested lend in `ρw` is not excluded. What is excluded is a new `mut` cell at `m` in the
flattening. So a lens-style `Mut_α A` of the first component, returned from a run that starts at
the `Mut_α (Ref A ⊗ Ref B)` borrow, is excluded at that run's `↭`, just as in 2. The frame's end
is again not involved. I did not state a typed-world `MutProjSpec`. The lemma quantifies over
every `π` and does not construct a valid one.

## 4. L2 free rider: no

Both `Mut_α` views would be new `mut` cells in the flattening, and `mut_view_rejected` excludes
each of them.

## Axioms and hygiene

`#print axioms` was checked with a scratch file importing `FrameEnd`. The result is
`[propext, Classical.choice, Quot.sound]` for `fundamentalProperty`, `adequacy`, `theorem32`,
`corollary33`, `wpTS_I_frameX`, `frame_image_empty`, `ti_sub`, `ti_endReb`, `TW.inv`,
`TW.linLife`, `linLife_sub`, `Projection.no_projection`, `Projection.frame_view_excluded`,
`Views.imm_view_rejected` and `Views.mut_view_rejected`. The directory has no `sorry`, `axiom`,
`native_decide`, `implemented_by`, `opaque`, `partial` or `unsafe`. `lake build FrameEnd` gives
the same linter warnings as `lake build Relaxed`, and no others.

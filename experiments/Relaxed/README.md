# Relaxed: the typed world with non-strict lifetime bounds

**Question.** `experiments/Projection` refuted a same-lifetime `Imm` projection at the typed
world and traced its last step to `FrameLife`'s second conjunct, which asks every `imm` view at
a lineage location of a frame to be *strictly* shorter than the frame. Two questions follow.

1. Do the Fundamental Property and adequacy still hold if that bound is non-strict (`⊑`)?
2. If they do, does `Imm @a (Ref A ⊗ Ref B) ⊸ Imm @a A` at the same lifetime then go through?

Build: `lake build Relaxed`. The typed world (`Support/TypedWorld/*`) is copied into
`Relaxed/` under the namespace `BoCa.Fig16.LogRel.Relaxed`. Everything below it (`Paper`, and
`Support/Model`, `Dynamics`, `Lifetimes`, `LogicalRelation`) is imported from the library
unchanged. `Relaxed/Fundamental.lean` restates 6.151 at `SemX` and adequacy over the copy.
These are `Paper/S6_8`'s `fundamental` and `Paper/CONF/Results.lean`'s `theorem32`,
`corollary33` and `adequacy`, read at this directory's `wpTS`. `Adequacy.reclaim` is copied as
`reclaim` because it does not depend on the typed world.

## The changes

There are two relaxations. The first was built and checked on its own. The second is applied on
top of it, because its `frameLife_reb_like` step needs the first. FP and adequacy hold after
each one.

**1. `FrameLife.2`: `x ⊏ α` becomes `x ⊑ α`** (`Records.lean`). Four lemmas consumed the strict
bound. In each of them the other inequality in the chain was already strict, so the proof only
changes its combinator:

| Lemma | File | Change |
|---|---|---|
| `lifeBound_of_tagged` | `Wp.lean` | `lt_trans` becomes `lt_of_lt_of_le` |
| `not_rel_lineage` | `Wp.lean` | `lt_asymm` becomes `lt_irrefl _ (lt_of_lt_of_le …)` |
| `witLB_of` | `RelationFacts.lean` | `lt_trans` becomes `lt_of_lt_of_le` |
| `frameLife_reb_like` | `Wp.lean` | the new view's bound `β ⊏ α` is used as `β ⊑ α` (`.le`) |

No lemma that *establishes* `FrameLife` broke. Those lemmas either pass the conjunct through
or prove a strict bound, which implies the weaker one.

**2. `TW.reb`'s stratum premise: `W.InStratum β` becomes `StratumLe W β`** (`World.lean`). Here
`StratumLe W β := ∀ β′ ⊏ β, W.InStratum β′`, which says every lifetime of `W` is `⊒ β`. This
lets a reborrow at a record's cell take `β` equal to the shortest lifetime in the world. A
projection built on `TW.reb` would need that. `rebDeep`, `rebEnd`, `rebEndDeep` and `NestLife`
are unchanged.

| Lemma | File | Change |
|---|---|---|
| `frameLife_reb_like` | `Wp.lean` | takes `StratumLe W β`. It proves `β ⊑ α` by contradiction: at `α ⊏ β`, `StratumLe` gives `W ∈ Res_α`, and the frame's own cell, at `α`, is not in it |
| `TW.linLife` (`rebDeep` case) | `Wp.lean` | passes `stratumLe_of_inStratum hβ` |
| `tagged_reb` | `Reborrow.lean` | takes `StratumLe W β` |
| `tagged_rebDeep`, `rebChooseTW_top` | `Reborrow.lean` | pass `stratumLe_of_inStratum hβ` |

`ti_reb` (`Invariant.lean`) never used the premise. `Compatibility`, `FrameRules`, `Images`,
`Invariant`, `ReborrowShapes` and `Relation` are the library's files with only the namespace
changed.

## Result

**Relaxed FP and adequacy hold.** `Relaxed.fundamentalProperty` and `Relaxed.adequacy` depend on
`propext`, `Classical.choice` and `Quot.sound` only.

**The same-lifetime projection is still refuted, and the cause is not a strict inequality.**
`Relaxed.Projection.no_projection proj x α : ¬ ProjSpec proj (.var x) .unit .unit`
(`Relaxed/Projection.lean`, same axioms). `ProjSpec` is `experiments/Projection`'s.

With the relaxed `FrameLife`, `Projection.no_view_at_tag`'s last step (`s.meet ⊏ α` against
`α ⊑ s.meet`) no longer closes. The refutation here uses no typed-world invariant. Its key step
is `frame_view_excluded`, which is `[TR]` 6.38 (`ResU.six38`) applied with the frame's borrow as
the whole resource:

    ResU.CompS ρv (ℓ ↦ own(v)) W → ✓W →
    ℓ ↦ imm({α}, v, ρv) ↭ π → π|own = ∅ → ρv(m) = own(u) → π(m) = ψ → False

6.38 lets the frame end against `π`. The frame's end puts `own` cells back at `ρv`'s locations,
so no resource that the borrow updates to (`↭`) can hold a cell there. This holds at any
lifetime. The configuration is `experiments/Projection`'s, except that the frame is entered
directly with `TW.immFrame` (6.64's entry) and not through `wpTS_I_frameX`'s callback: three
allocations `l₂`, `l₁`, `ℓ ↦ (l₁, l₂)`, then the borrow `ℓ ↦ imm({α}, (l₁, l₂), l₂ ↦ () ● l₁ ↦ ())`
read at `'x ↦ α`. The `wpTS` that `ProjSpec` gives there returns a view at `l₁` inside
`π = ρ′ ● ρ⁺`, together with `ρ ↭ π` (`wpTS`'s own conjunct). `frame_view_excluded` refuses that.

The same file, with the namespace switched back, also elaborates against the library's unrelaxed
typed world (checked with a scratch file, not committed). So the `FrameLife` bound was not the
only thing refuting the projection. The model's `↭` from a frame's borrow, through 6.38,
refutes it independently of the typed world.

## Remaining obstruction

The `wpTS` post-condition requires `ρ ↭ ρ′ ● ρ⁺`. At a 6.64 frame's borrow `ρ = ℓ ↦ imm({α}, v, ρv)`,
6.38 excludes every cell of `ρ′ ● ρ⁺` at a location `ρv` owns. A projected view is such a
cell. Reborrows (6.150) avoid this: their views are never reached from `ρ` by `↭`. The inner
run starts at `ρ ● χ`, and 6.52 subtracts the image before the final `↭` (6.59). A projection
that returns its view has no such scope. I have not derived a projection spec in any weaker
form (for example one scoped like 6.150, or one not tied to the first component) and have not
verified that any further obstruction to one is real.

`NestLife`, `rebDeep`'s stratum and the reborrow chooser were not needed for this conclusion
and were not changed.

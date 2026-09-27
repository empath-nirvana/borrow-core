# TwoRun: two-run properties from the unary relation and the machine

**Question** (issue #39). Three results have needed a relation between two runs: the Optics
purity and effectful-fusion laws (#27), the frame theorem's transfer to runs that allocate (#37),
and guaranteed deforestation. The unary relation cannot state them. Can they be had
operationally, from the unary relation and the machine's determinism, or is a binary logical
relation needed?

Build: `lake build TwoRun`. The library imports `FrameTheorems` (and through it `Core` and
`Optics`), and nothing imports it. `Paper/`, `Support/`, `Core/` and `CDerives` are unchanged.
Every result's axioms are within `[propext, Classical.choice, Quot.sound]`.

| file | contents |
|---|---|
| `Rename.lean` | `Expr.rename`, `Heap.rename`; renaming commutes with shifting, substitution and plugging; the host step is location-free (`host_call_rename`); runs with no array step are invariant under permutations of `Loc` (`head_rename`, `step1_rename`, `steps_rename`) |
| `Fresh.lean` | `Named`, fresh steps and runs (`Step1F`, `FreshRun`); a run that does not allocate is fresh (`StepsNA.toFresh`); fresh runs are deterministic up to a permutation (`step1F_sim`, `freshRun_det`) |
| `Sim.lean` | every run follows every fresh run along a function (`HeapRel`, `head_sim`, `step_sim`, `run_sim`, `fresh_run_image`); the footprint of every fresh run (`wpTS_footprint_fresh`, `everyFreshRunFootprint`) |
| `Refute.lean` | `EveryRunFootprint` does not hold, at a fresh run of `alloc (free 0)` (`not_everyRunFootprint`); its renamed form does not hold, at a stale run of `staleE` (`not_everyRunFootprintRen`) |
| `Read.lean` | `Touch`, `RunIn`; the read footprint stated for every `wpTS` term (`ReadFootprint`) and for typed computations (`ReadFootprintTyped`); `ReadFootprint` does not hold, at `peekE k` (`not_readFootprint`) |

## Step 1: renaming, and the footprint on every run

**Renaming** (`steps_rename`). For a permutation `σ` of `Loc`, a run from `(μ, e)` to
`(μ′, e′)` that takes no array step renames to a run from `(σ μ, σ e)` to `(σ μ′, σ e′)`. Away
from the array steps the machine treats locations opaquely: no step compares two locations or
computes one. The host step's arguments and results are integer literals and booleans, which
renaming fixes. The array steps (SPEC §9) compute locations: `tab` places consecutive cells,
`idx` and `drop` add an index to a base, and a permutation does not preserve `ℓ + i`. Every
result in this library is therefore stated for runs with no array step (`StepsR`, and `Step1F`
requires it). Whether the results extend to runs with array steps, under a renaming of blocks
rather than of single locations, I have not derived and have not checked.

**Fresh runs.** A configuration *names* a location when the heap holds it, the term mentions
it, or a value in the heap mentions it. A *fresh* run takes no array step and allocates only
locations its configuration does not name. Every run that does not allocate is fresh (`StepsNA.toFresh`), and
so is every run of a bump allocator that starts above every location the initial configuration
names.

```
freshRun_det : FreshRun μ e μ₁ v₁ → FreshRun μ e μ₂ v₂ →
    ∃ σ : Equiv.Perm Loc, μ₂ = σ μ₁ ∧ v₂ = σ v₁
```

The proof is a lockstep simulation. A step that is not an allocation is the only step
(`step1_det`, #37), and renaming carries it. At an allocation the runs pick `ℓA` and `ℓB`, and
the permutation is extended by swapping `σ ℓA` with `ℓB`. The swap fixes everything the
configuration names because both picks are fresh.

**Every run follows every fresh run** (`fresh_run_image`). The exhibited run of `wpTS` need
not be fresh, so the result that closes the footprint question compares a fresh run `B` with an
arbitrary run `A`:

```
fresh_run_image : FreshRun μ e μB vB → Steps μ e μA vA →
    ∃ g : Loc → Loc, InjOn g (dom μB) ∧ μA = Heap.push g μB ∧ vA = vB.rename g
```

`Heap.push g μB` moves `μB`'s cell at `x` to `g x` and renames its value. At every step, `A`'s
term is `B`'s renamed by `g`, `g` maps `B`'s allocated locations injectively onto `A`'s, and the
cells agree along `g` (`HeapRel`). `g` need not be injective off `B`'s heap. `A` may reuse a
location it still names as a dangling pointer, and then `g` sends a name `B` holds only as a
dangling pointer to the reused location. `B` never reads through that name: `B` is fresh, so the
name stays unallocated in `B`, and a read would leave `B` stuck.

**The footprint of every fresh run** (`wpTS_footprint_fresh`, `everyFreshRunFootprint`).

```
wpTS ls e Q ρ → (ρf ● ρ a tagged typed world with heap μ) → FreshRun μ e μR w →
    ∃ g, InjOn g (dom μR) ∧ (∃ ls′ ρ′, Q ls′ (w.rename g) ρ′) ∧ Footprint ρf ρ μ (Heap.push g μR)
```

It holds for every `wpTS` term with no further hypothesis: a fresh run's final heap, renamed
injectively, is the exhibited run's final heap. It extends `wpTS_footprint_every` (#37), which
covered runs that do not allocate.

**The forms that do not hold.** Both witnesses mention a location literal and are not typed
by `CDerives`. They bound what follows from `wpTS` alone, not what holds of well-typed programs.

- **Without the renaming** (`not_everyRunFootprint`). `EveryRunFootprint`, the goal #37 stated,
  asks for `Footprint` on the final heap itself. `alloc (free 0)`, lent cell `0` as a `mut` cell,
  frees it and allocates a cell holding `()`. The exhibited run picks `0` again and ends where it
  started. A fresh run that picks `1` ends with `0` unallocated, and `Footprint`'s third clause
  fails. Renaming `1 ↦ 0` repairs it, which is the form `everyFreshRunFootprint` proves.
- **Without freshness** (`not_everyRunFootprintRen`). `staleE` allocates `x`, frees it, allocates
  `y` and `z`, and branches on `load x`. The run that reuses `x`'s location for `y` reads
  `inj₁ ()` and restores the heap, so `wpTS` holds from every world lending cell `0`
  (`staleE_wp`). The run that reuses it for `z` reads `inj₂ ()` and frees the lent cell
  (`staleE_frees`). Its final heap is empty, and no renaming of it keeps cell `0` allocated.

**Not derived.** The renamed footprint on every run of a *well-typed* program, stale runs
included. A typed program never reads through a dangling pointer, but `wpTS` exhibits one run
and says nothing about the states of other runs. I have not derived it and have not verified
that any obstruction to it is real.

## Step 2: the read footprint

A head step *touches* the location it loads, stores to or frees (`Touch`). `RunIn P` is a run
each of whose steps touches only locations in `P`. The goal:

```
ReadFootprint : wpTS ls e Q ρ → (ρf ● ρ a tagged typed world with heap μ) →
    ∃ μ′ v, RunIn (Own ρ μ) μ e μ′ v ∧ (∃ ls′ ρ′, Q ls′ v ρ′)
Own ρ μ ℓ := (∃ ψ, ⦇ρ⦈(ℓ) = ψ) ∨ μ ℓ = none
```

It asks only for *some* run satisfying the post-condition, the weakest form. **It does not
hold** (`not_readFootprint`). `peekE k = let x = alloc () in let _ = load k in x` satisfies
`wpTS` at `∅` (`peekE_wp`). In a world whose heap lacks `k`, the exhibited run allocates `k`
itself. In a world whose heap holds `k`, it allocates elsewhere and loads the frame's cell. From
the world whose frame owns `k`, every run to a value loads `k` (`runIn_head_inv`), and `⦇∅⦈` does
not hold `k`.

**What the model lacks.** Two features of `wpTS` meet here.
1. **A load leaves no trace in the post-world.** `wpTS` constrains a run only through its final
   world, and `↭` compares the resource before and after. That bounds what a run changes
   (`Footprint`). It does not bound what the run reads.
2. **Allocation is angelic.** `wpTS` exhibits one run per world, and that run's `alloc↦` may
   pick a location that depends on the frame. `peekE` uses the choice to make its load succeed in
   every world.

`peekE` is not typed by `CDerives`. The statement for typed programs is `ReadFootprintTyped`:
`ReadFootprint` at the instances `fundamentalC` gives, computations at `F A`. I have not derived
it and have not verified that any obstruction to it is real. By the stop rule, step 3 was not
attempted.

## Step 3: not attempted

Each law of step 3 needs the read footprint of a well-typed callback. Given step 1 and
determinism, two heaps that agree on what a run reads give runs that agree up to renaming. The
laws below are therefore not derived here.
- **`PureFn`'s value clause** for well-typed callbacks at plain-data payloads. The result
  depends only on the argument when the callback reads nothing but its argument and its own
  allocations.
- **Effectful fusion** (`over_fuse` without `PureFn`). It holds when `g` does not read the
  focus cell before writing it.
- **The Optics laws at every run.** They need the read footprint for the laws that compare
  heaps. The heap clauses (`ElemFrame`'s, `PureFn`'s) carry over to fresh runs through
  `wpTS_footprint_fresh`, in its renamed form; this was not restated per law.

## What would supply the read footprint

The missing fact is one statement, `ReadFootprintTyped`. Two routes are open, and neither is
built.

**(A) A unary strengthening (try first).** Add to `wpTS` the conjunct that the exhibited run
touches only `Own ρ μ` (a `RunIn` in place of `Steps`). This is a coordinate in the model, not
an index on `CDerives` (decision 19).
- The runs `wpTS` exhibits are built by about 16 witness constructions: `wpTS_val`,
  `wpTS_head`, `wpTS_alloc`, `wpTS_free`, `wpTS_load`, `wpTS_load_I` and `wpTS_store` in
  `Core/Wp.lean`, the frame rules in `Core/FrameRules.lean`, and `wpTS_reborrow`. `wpTS_bind` and
  the frame and ramification rules pass the run through.
- Each primitive touches a cell its own resource holds, so each construction is expected to
  extend directly. Not verified: that `↭` keeps the continuation's resource inside `⦇ρ⦈` plus
  fresh locations, which `wpTS_bind` needs.
- It rules out `peekE`: in the world whose frame owns `k`, no run of `peekE k` touches only
  `Own ∅ μ`.
- The two-run laws would then follow operationally. A run touching only `T` replays from any
  heap agreeing on `T` (the machine's locality, not built), and `fresh_run_image` covers the
  allocation choices.
- Cost: no new `VTy` or `CTy` former, no new `CDerives` rule, and no inversion. The
  Fundamental Property's compatibility lemmas that go through the `wpTS_*` rules would not
  change.

**(B) A binary logical relation, scoped.** It is needed only if (A) fails, or for properties
that are not locality: parametricity in lifetimes (decision 22) and representation
independence.
- **Fragment:** plain data (`1`, `⊗`, `⊕`, `I32`/`I64`), `Ref`, `Mut`, `withbor`, and the
  computation formers `F` and `⊸`.
- **Relation:** `𝒱²⟦A⟧` over pairs of values and pairs of worlds that agree on the borrowed
  cells' invariants. `wpTS²` runs two configurations whose frames are arbitrary and unrelated,
  and asks for related results and related final worlds.
- **What it would prove:** the read footprint as noninterference (related inputs, any two
  frames, related outputs). It would also give `PureFn`'s value clause at plain data, and fusion
  at effectful callbacks whose read footprint excludes the focus cell.
- **Cost, per the growth rules:**
  - no new former and no new `CDerives` index;
  - a second relation, with one binary compatibility lemma for each `CDerives` rule in the
    fragment (roughly 20 of the 59), and a Fundamental Property for it;
  - a paired `↭` for `Mut` cells, which is the largest part: it doubles the typed-world
    invariant at `Mut`;
  - no inversion of `CDerives`.
- **Estimate:** the fragment's share of `Core`'s unary development, in the thousands of lines.
  Not built.

## What this unlocks

**(U1) A new program expressible: no.** Nothing becomes typable.

**(U2) A proof obligation discharged once for a class: yes.**
- **Every `wpTS` term, so every well-typed program.** `wpTS_footprint_fresh` gives every fresh
  run the exhibited run's footprint, up to an injective renaming. #37 had this only for the
  exhibited run and for runs that do not allocate.
- **Every instance of the frame laws.** `call_frame`, `optic_frame`, `imm_call_keeps` and
  `mut_call_frame` are `wpTS_footprint` applied to a particular `wpTS`, and each extends to fresh
  runs the same way. They were not restated.
- **The machine:** `freshRun_det` and `fresh_run_image` hold for every term, typed or not.
  Allocation choice is the machine's only nondeterminism, and on fresh runs it is invisible up to
  renaming.

**(U3) Justified optimizations: partial.** A compiler whose allocator never reuses a location
the program still names (for example a bump allocator) gets the #37 table on its own runs, up to
renaming its allocations. Examples: values kept in registers
across calls, loads reused across `Imm` calls, reloads only of the lent cell. Allocators that
reuse freed memory are outside this for untyped terms (`not_everyRunFootprintRen`); for typed
terms it is not derived. Optimizations that rest on what a call *reads* are not justified: they
need `ReadFootprintTyped`.

**(U4) Fewer mechanisms: no.** Every Optics law keeps its hypotheses. The experiment answers
the issue's question as follows. The every-run half of #37 is operational: renaming plus
freshness, no new relation. The two-run laws all reduce to one missing fact, the read footprint
of typed computations. The unary `wpTS` cannot state that fact, because loads leave no trace and
allocation is angelic. A unary strengthening (A) is the cheaper candidate to supply it. A binary
relation (B) is needed only if (A) fails.

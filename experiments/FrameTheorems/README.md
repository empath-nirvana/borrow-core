# FrameTheorems: frame guarantees as theorems of the logical relation

**Question** (issue #37). The Optics laws (`experiments/Optics`) hold on every machine run, but
the ones that matter assume frame facts: the callback touches only what it was lent
(`ElemFrame`), pure callbacks (`PureFn`), distinct cells. Are these theorems of the logical
relation? Does a semantically typed callback `g : ∀'x ⊏ @b. Mut 'x A ⊸ ['x] T` provably leave
every location outside its lent resource and its own resource unchanged?

Build: `lake build FrameTheorems`. The library imports `Core` and `Optics`, and nothing imports
it. `Paper/`, `Support/`, `Core/` and `CDerives` are unchanged. Every result's axioms are within
`[propext, Classical.choice, Quot.sound]`.

| file | contents |
|---|---|
| `Footprint.lean` | the flattening of a factor (`flat_factor`); `Footprint`; the footprint of a `wpTS` run (`wpTS_footprint`) |
| `EveryRun.lean` | the machine is deterministic away from `alloc` (`head_det`, `step1_det`); a run with no `alloc↦` step is the only run to a value (`stepsNA_det`); the footprint on every such run (`wpTS_footprint_every`); `EveryRunFootprint`, stated; `not_runsAgreeOnDom` |
| `Callback.lean` | closed well-typed values are in the relation at `∅` (`closed_vP`); application in the relation (`app_wp`, `app2_wp`, `call_wp`); the frame of a callback (`call_frame`); `Imm` callbacks keep the lent cell (`imm_call_keeps`); `Mut` callbacks at a payload holding no resource change only the lent cell (`mut_call_frame`); a world that meets these hypotheses (`lent_unit_world`) |
| `Laws.lean` | the frame of every optic (`optic_frame`), of `over` and of IterMut; `ElemFrame`'s and `PureFn`'s heap clauses at typed worlds; distinct cells (`mut_ref_distinct`) and fusion with that hypothesis discharged (`over_fuse_typed`) |

## The frame theorem

`wpTS ls e Q ρ` quantifies over every frame `ρf` that completes `ρ` to a tagged typed world
`ρf ● ρ`. It exhibits one run from that world's heap `⟦ρf ● ρ⟧` to `⟦ρf ● ρ′ ● ρ⁺⟧`, with
`ρ ↭ ρ′ ● ρ⁺`. The frame is a factor of both worlds, and `↭` keeps `ρ`'s `imm` cells exactly
and its `mut` cells at the same invariant. The theorem reads this as a heap relation:

```
Footprint ρf ρ μ μ′ :=
    (∀ ℓ ψ, ⦇ρf⦈(ℓ) = ψ → μ′ ℓ = μ ℓ)                       -- the frame is untouched
  ∧ (∀ ℓ, ℓ ∈ dom μ → ImmOnly ρ ℓ → μ′ ℓ = μ ℓ)             -- so is what ρ holds only immutably
  ∧ (∀ ℓ ψ, ⦇ρ⦈(ℓ) = ψ → ψ.kind = mut → ℓ ∈ dom μ′)          -- lent cells stay allocated

wpTS_footprint : wpTS ls e Q ρ → (ρf ● ρ a tagged typed world with heap μ) →
    ∃ μ′ v, μ →* e ⇓ (μ′, v) ∧ Q v holds ∧ Footprint ρf ρ μ μ′
```

An existing location changes only where `⦇ρ⦈` holds it exclusively, as an `own` or a `mut`
cell. The proof needs no new model fact. `flat_factor` (the flattening of `X ● Y` contains
`⦇X⦈` and `⦇Y⦈` cell by cell, and every location of it is one of theirs) is
`ResU.Flat.split_factors` read through the erasure.

**Every run that does not allocate** (`wpTS_footprint_every`). The machine's only
nondeterministic step is `alloc↦`. `step1_det` shows that any other step is the only step
(unique decomposition, `Core/Steps.lean`, and `head_det`). So a run that takes no `alloc↦` step
is the only run to a value from its start (`stepsNA_det`), and it has the exhibited run's
footprint.

**Callbacks** (`call_frame`). For `g` at `∀'x ⊏ @b. F('x) ⊸ ['x] T` in the relation at `ρg` and
a borrow `v` at `F('x)` with `'x ↦ α ⊏ @b` at `ρv`, the relation's own clauses give
`wpTS (g () v)` at `ρg ● ρv` (`call_wp`). So `g () v` satisfies `Footprint ρf (ρg ● ρv)` from
every tagged typed world, on the exhibited run and on every run that does not allocate.
- **`Imm` callbacks** (`imm_call_keeps`): the lent cell holds what it held. The borrow's cell is
  `imm`, and so is the flattening's cell there (`immOnly_of_get`).
- **Closed `Mut` callbacks at a payload holding no resource** (`mut_call_frame`): take `g`
  closed and well typed (`CDerives Δ [] g …`, so `ρg = ∅` by `closed_vP`) and `A.Persistent`
  (`1`, `I32`, `N`, …, so the borrow's witness is empty and `⦇ρv⦈ = a ↦ mut`). Then every
  existing location other than `a` keeps its value, and `a` stays allocated.
- `lent_unit_world` builds a world, by `alloc` and `mutFold` from `∅`, that lends a cell at
  `Mut 'x 1`. So the hypotheses of `mut_call_frame` are met.

## The Optics laws

| law, hypothesis | what the relation gives | where |
|---|---|---|
| `iterMut_shape`, `ElemFrame g` | for closed well-typed `g` at a persistent `E`, `ElemFrame`'s heap clauses (lent cell allocated, every other existing location unchanged) at every heap of a typed world lending the cell, on every run that does not allocate | `elemFrameNA_of_typed` |
| `over_fuse`, `ℓ ≠ ℓ′` | at every typed world lending `ℓ` at `Mut @a (Ref V)`, `ℓ` holds `ℓ′ ≠ ℓ`, and `ℓ′` is allocated. `over_fuse_typed` is `over_fuse` at the identity lens with the hypothesis discharged | `mut_ref_distinct`, `over_fuse_typed` |
| `over_id`, `over_fuse`, `PureFn f` | for closed well-typed `f : V ⊸ V ⊗ T` at a persistent `V`, `PureFn`'s heap clause: every existing location keeps its value, on every run that does not allocate | `pure_heap_of_typed` |
| (new) every optic | one frame law for the interface: `L.run s g` changes an existing location only where the source's or the callback's resource holds it exclusively | `optic_frame` |
| (new) `over`, IterMut | the same at `over` (`d_over`) and at IterMut (`d_iterMut`); IterMut returns a list | `over_frame`, `iterMut_frame` |

**None of the Optics laws becomes unconditional in its own form.** Those laws are about every
run from every closed heap. The relation constrains runs only from the heaps of typed worlds,
and in this experiment only the exhibited run and the runs that do not allocate. What follows
is unconditional at typed worlds: `over_fuse_typed` no longer takes the distinct-cells
hypothesis, and `optic_frame`, `over_frame`, `iterMut_frame` and `imm_call_keeps` take no
frame hypothesis at all.

## What does not follow, and why

1. **Every run.** `wpTS` is a total-correctness predicate with one exhibited run (row 5.33),
   and `alloc↦` picks any fresh location. The transfer to every run is proved for runs that do
   not allocate. The general statement is `EveryRunFootprint` (`EveryRun.lean`). I have not
   derived it and have not verified that any obstruction to it is real.
   - A transfer must go through a renaming of the allocated locations: runs to values need not
     even agree on the initial heap (`not_runsAgreeOnDom`, `store 0 (alloc ())`).
   - Such a renaming holds only when `alloc` does not reuse a location that the heap or the term
     still names after a `free`. The model states no such invariant.
2. **Every closed heap.** `ElemFrame` and `PureFn` quantify over every closed heap, and the
   relation speaks only about heaps of typed worlds.
   - The shape law uses `ElemFrame` at the intermediate heaps of IterMut's own run.
     `fundamentalC` builds a typed world at each of them inside its proof, but its statement
     does not expose them.
   - So `iterMut_shape` still carries `ElemFrame`. Discharging it needs the typed worlds of a
     run's intermediate states, or IterMut's shape as a post-condition proved in the relation.
     Neither is built here.
   - `ElemFrame`'s `HeapClosed` clause is not derived either, and neither is its clause at
     locations the run allocates: no net allocation, `μ′ k = μ k` for fresh `k`.
3. **At a payload that owns cells, `ElemFrame` is stronger than the frame typing gives.** A
   borrow at `Mut 'x (Ref N)` lends the cell and the cell its content owns (`⦇ρv⦈` contains
   both). A well-typed callback may write the second, and `call_frame` allows that. The weaker
   form that does follow is "only the lent resource's exclusive cells change" (`call_frame`).
   `ElemFrame`'s "only the lent cell changes" follows at persistent payloads
   (`mut_call_frame`).
4. **`PureFn`.** A callback may change what its own resource and its argument hold
   exclusively, so `PureFn` does not follow in general. At a closed function and a persistent
   payload the heap clause follows (`pure_heap_of_typed`).
   - The value clause, that the result is a function of the argument alone, compares runs from
     different heaps.
   - The relation is unary: one run per world. Not derived.
5. **Fusion at effectful callbacks.** `over ℓ f; over ℓ g` stores `f`'s result in the focus
   cell before `g` runs; `over ℓ (f; g)` does not. The two agree when `g` does not read the
   focus cell. That is a non-interference property, again about two runs, and it is not derived.

## What this unlocks

**(U1) A new program expressible: no.** Nothing becomes typable. The theorems are about
programs that were already typable.

**(U2) A proof obligation discharged once for a class: yes.**
- **Every `wpTS`, hence every well-typed program.** `wpTS_footprint` is one lemma, and
  `fundamentalC` applies it to every derivation. It gives the exhibited run, and every run that
  does not allocate, a footprint read off the program's resource.
- **Every optic, once.** `optic_frame` holds for every instance of `Optics.Optic` (`idLens`,
  `reLens`, `fstLens`, `famLens`, prisms, `lift`, `comp`), from `Optic.sem`, with no
  per-instance proof.
- **Every closed well-typed callback at a persistent payload** satisfies `ElemFrame`'s heap
  clauses at typed worlds. Optics proved this by hand for one callback (`incCb_frame`), at every
  closed heap.

**(U3) Justified optimizations: partial.** Each item holds at heaps of typed worlds, on the run
the relation exhibits and on every run that does not allocate.

| fact | what a compiler may do |
|---|---|
| `wpTS_footprint` frame clause | keep the values of cells outside a call's arguments and resource in registers across the call |
| `imm_call_keeps` | reuse a load of a cell across a call that borrows it immutably |
| `mut_call_frame` | after a call lending one cell of plain data, reload only that cell |
| `over_fuse_typed` | fuse two accesses through the identity lens without checking that the source and focus cells differ (still for pure `f`, `g`) |

Runs that allocate are not covered: a compiler whose allocator makes a different choice from the
exhibited run is outside these statements (item 1 above).

**(U4) Fewer mechanisms: no.** The Optics laws keep their hypotheses, and no library mechanism
is replaced. The experiment shows where a frame fact comes from: a `Footprint` read off
`wpTS`. It also shows what is still missing for the machine-level laws: runs that allocate,
the typed worlds of intermediate states, and two-run properties.

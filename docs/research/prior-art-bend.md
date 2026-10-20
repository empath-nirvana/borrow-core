## Prior art: Bend/HVM, and automatic parallelism over the pure div-free fragment (#619)

This is a research note, not a decision. It records no new direction; it ends in a decision menu
(§8). Repo citations are to `main` at 9aa27c3. External sources are marked as read in full (FT),
read as an abstract or a documentation page (AB), or **unchecked**.

### 0. The question, and the short answer

**Question (#619).** Can our pure, div-free fragment be parallelised automatically, without
annotations and with a proof that every result is unchanged? If so, what does it need?

**Short answer.** *Permission* yes, *choice* no, *proof* not yet.

1. **Permission: yes, from facts the checker already proves.** Two subterms may run in parallel
   when the typed term shows that neither reads the other's result and that their contexts are
   split. Both facts are on the typed term the checker returns: the `Ctx.SplitP` masks at a
   `bind`/`tensorI`/`tensorE` node (SPEC §3 *What the checker returns*), and the empty row of
   `F A = F_∅ A` (SPEC §19 *Types*). No new analysis and no heuristic is involved. The kill
   criterion does not fire (§2).
2. **Choice: not without a heuristic.** *Which* independent pairs are worth forking is a cost
   question. A compiler that picks fork sites from a size estimate is a heuristic, which the
   standing rule "don't rely on LLVM; performance by construction, forcing annotations with a
   check" excludes. Two routes avoid that: a forcing annotation the checker verifies (`par`/`join`,
   #212), or a runtime mechanism with a proved overhead bound that needs no per-site decision
   (heartbeat scheduling, §5). Bend/HVM2 takes a third route, every redex is a task, and pays for it
   in single-thread speed (§4).
3. **Proof: the obligation is stated, not discharged.** "Parallel = sequential" does not reduce to
   `fundamentalC`/`adequacyD` as they stand, because `wpTS` is a start-to-end relation with a
   fixed frame and no per-step footprint. #212's scoping already names the routes (0, C, B); this
   note restates the obligation in the shape of our adequacy theorems (§3).

What Bend does not have and we do: two parallel branches may each mutate in place a disjoint
`mut` part of one array (`slice_split_mut`, SPEC §9). Bend's values are affine with no sharing
of mutable state, so its parallel branches build new data (§4).

---

### 1. What we already have

| fact | where | role |
|---|---|---|
| `F A = F_∅ A`, the pure returner: a computation that performs no control operation | SPEC §19 *Types*; `CTy.effOf [] A = .ret A` | a side of a fork has no outward operation, so no unwind, resume or handler ordering crosses the fork |
| A closed computation of `F A` terminates on every run | `total_every_alloc`, `total_every_run`, `total_no_infinite_run` (`Core/Totality.lean`); SPEC §14 *The totality theorem* | a side cannot diverge; well-foundedness for a reordering proof |
| Divergence is a type (`Loop`) or the `Div` row, never hidden in `F A` | SPEC §14 *Types*, *The effect `Div` in the kernel* | "div-free" is read off the type, not inferred |
| Every binary rule splits its context: `bind`, `tensorI`, `tensorE`, `unitE`, `sumE`, `app` take `Ctx.SplitP Γ Γ₁ Γ₂` | `Core/Fundamental.lean` (`CDerives`); `Core/Persistent.lean` (`Ctx.SplitP`) | the two parts of a split hold disjoint live slots |
| Only persistent slots go to both sides (`dup`), and a persistent value holds no resource | `Ctx.SplitP.dup`; `vP_empty_of_persistent` (`Core/Persistent.lean`) | `!` code (the algebra of a fold, a mapped function) is shared at no resource |
| The split's masks are recorded on the typed term and fixed by its derivation | SPEC §3 *What the checker returns* (`Masks`, `SplitMasks`, `TDerivesAt.split_masks`) | the independence fact is readable by the compiler, not recomputed |
| The split gives disjoint resources, `ρ = ρ₁ ● ρ₂`; strict `●` composes only agreeing `imm`/`imm` cells | `gDenC_split` (`Core/Compatibility.lean`); `ResU.Hash` (`Paper/S5_Model/Definitions.lean`) | `own`/`mut` cells are exclusive across the split |
| An `Imm` borrow is shared by an explicit `copy`, not by persistence | `copy` constant (`Core/Fundamental.lean`); #58 (implicit copies) | read sharing is two agreeing `imm` halves |
| A borrowed array family splits at a run-time index into two disjoint families at the same lifetime | `slice_split_imm`, `slice_split_mut`; `vP_fam_split` (SPEC §9 *Splits and writes on a borrowed family*) | in-place parallel writes on disjoint halves |
| Folds over `μ` with a `!` algebra at `F R`, total by the size of the witness | `foldImm`, `foldOwn`, `foldReuse` (SPEC §6; `Core/FoldImm.lean`) | the children of a node are folded independently; the fold node is a rule node of the typed term |
| A recursive group is `bounded_fix` with a depth budget; its row holds the abortive `Exhausted` | SPEC §20, §21; `corpus/rec-tree.bc` | a self-recursive function is **not** at `F_∅`; it is at a row with one abortive operation |
| The machine is deterministic apart from allocation | `AStep1.deterministic` (`Core/Demonic.lean`) | the sequential reference semantics |
| A start-to-end write footprint (cells held only immutably keep their value) | `wpTS_footprint`, `ImmOnly` (`experiments/FrameTheorems/FrameTheorems/Footprint.lean`) | half of a footprint fact; no read footprint and no per-step footprint (#212 scoping §2) |

Two facts from this table change how the question reads.

- **"Pure" is not "immutable".** `F_∅ A` means no control operation leaves the computation. The
  computation may still allocate, free, load and store, through what it owns and through `Mut`
  borrows it holds. That is why the fragment is Rayon's, not Haskell's `par`'s: sides may write.
- **The pure fragment's recursion is folds.** A function that calls itself is `bounded_fix`, and
  its row holds `Exhausted` (SPEC §20: "`Exhausted` stands in a recursion's row where `div` stands
  in a loop's"). `corpus/rec-tree.bc`'s `sum` runs under `with on_exhausted(…)`. So "pure,
  div-free" covers `foldImm`/`foldOwn`/`foldReuse`, counted loops and straight-line code, and a
  divide-and-conquer written as self-recursion is at the row `{Exhausted}`. Either the fork admits
  sides at an abortive row (#212's `Row.Unwind` option with law L5), or each side handles
  `Exhausted` inside itself. Section 2 states which programs this touches.
- **The kernel already has a total divide-and-conquer.** `bounded_fix[A, C]` is typed at every
  computation type `C`, `F B` among them, and "the step decides what a spent budget does: `self`
  is `inj₁ ()`" (SPEC §20 *The kernel*). The surface driver `bounded` performs `exhausted()` there;
  a step that instead runs a sequential base case (a counted loop) never performs anything, so the
  whole recursion is at `F_∅`. The budget is then the depth at which forking stops: a grain the
  program writes, checked, and no heuristic (§5). BELIEVED: that the surface accepts a
  `bounded_fix` written this way was not checked.

  **A raise changes what is observable.** Sequentially, a side that performs `exhausted()` stops
  its sibling from ever starting. In parallel the sibling has already written its `mut` half,
  and the handler, after the lend ends, sees those writes (#212 scoping §3(a), L5). So a fork at an
  abortive row is never result-preserving without choosing L5: automatic forking is confined to
  `F_∅`, and a fork at `{Exhausted}` is an explicit `join` with L5's semantics.

---

### 2. The target programs

The yes/no question per program: *can the split be made without an annotation, from a typed fact,
with a statable proof obligation?* The obligation for every row is §3's `adequacyPar`, at the
fragment named in the row.

| program | split point | fact that makes the split safe | row of each side | proof obligation | grain | answer |
|---|---|---|---|---|---|---|
| **Tree sum** (Bend's canonical `fold`) | the two recursive positions of a `node` in `foldImm`'s traversal: `travK (tensor F G)` is a `letpair` of the view, two `bind`s (one per component, the recursive call `h` shared) and a `pair` (`Core/FoldImm.lean`) | the `letpair` gives each bind one component of the view; each child is read through an `Imm` view (`withload` at `Ref X`), so reads are shared and nothing is written; the recursive call and the algebra are `!` and hold `∅` (`vP_empty_of_persistent`); each child's result is a fresh value | `F R` (`F_∅`) when written as a fold; `{Exhausted}` when written as self-recursion (`corpus/rec-tree.bc`) | `adequacyPar` at `F_∅`, with fork points only at fold nodes | the fold node knows the shape, not the size. Depth-based cut-offs are a heuristic; a forcing `par` at the fold, or heartbeat promotion, is not | **yes**, as a fold. As self-recursion, yes only with `Exhausted` handled inside each side or admitted by L5 |
| **Map over an array split in halves**, in place | the two halves from `slice_split_mut` | the two `ArrayMut 'x A` families are disjoint (`vP_fam_split`); the mapped function is `!`; the masks put each half in one side | the halving recursion is `bounded_fix` (`{Exhausted}`); the per-element step is `F_∅` | `adequacyPar` with `Mut` families split across the fork; this is where we exceed Bend (in-place writes) | the depth budget of a `bounded_fix` whose spent branch is the sequential loop (§1), or a cut-off the program writes (`if len < k`), or a forcing `par_for` | **yes** at `F_∅` with the split written by the program (a library `par_map_mut` over `slice_split_mut` and `bounded_fix`); the split itself is never inferred from a `for`. At `{Exhausted}`, only an explicit `join` with L5 |
| **Merge sort** | the two recursive sorts after `slice_split_mut` of data and scratch | as the map: disjoint `mut` halves of both buffers; the merge is sequential and depends on both results (the masks show it) | `{Exhausted}` as surface self-recursion (on slice length, not structural on a `μ`); `F_∅` over `bounded_fix` with a sequential base case | as the map; the merge is after the join | as the map | **yes** at `F_∅`, as the map; the merge is correctly not split |
| **Parallel fold of a k8s-style list** | none on a cons list: the fold's tail result is an argument of the head's algebra | for the **map** part (per-object computation) the masks give independence, as above; for the **reduce** part, splitting a list fold needs the combiner to be associative with a unit, which is a law about a user function, not a typed fact | `F_∅` if the per-object step is pure; any IO (API calls) makes the row non-empty and the program leaves the fragment | the map part: `adequacyPar`. The reduce part: `adequacyPar` **plus** a monoid law, `op (op a b) c = op a (op b c)`, stated and proved by the program (cf. Bend 2's laws, §6) or trusted | the list's spine is a chain: no split without converting to a tree or an array (NESL's flattening) | **map yes; reduce no** without a law. The kill criterion fires for the reduce only (§2.1) |
| **Negative: a loop with a carried dependency** (`acc = f(acc, a[i])`) | none | the elaborated loop threads `acc` through each turn: the next turn's first bind has `acc` live in its context (the masks), and a `Mut` accumulator is not persistent and cannot be in both parts | `F_∅` | none: there is no split to justify | n/a | **not split**, by the same fact; nothing is inferred to refuse it |

#### 2.1 The kill criterion

#619: "If independence of two subterms in the pure fragment cannot be stated as a typed fact the
checker already proves (rows plus lends), with no new analysis heuristic, say so."

**It does not fire for independence.** For two subterms `M₁`, `M₂` of a term the checker has
typed, the fact is: there is a node whose split gives `M₁` the context `Γ₁` and `M₂` a context in
which `M₁`'s result is dead, the two contexts share only persistent slots, and both are typed at
`F_∅`. Every part is a field of the typed term (masks, rows) or a lemma about it (`gDenC_split`,
`vP_empty_of_persistent`). Reading which nodes satisfy it is a pattern over the typed term, not an
analysis.

**It fires for one thing: reassociation.** Splitting a reduction over a sequence (the k8s list's
reduce, a sum over a list) changes the bracketing of the combiner. That is independence only if the
combiner is associative, which no row or lend states. It needs a law (Bend 2's `LAWS.bend` is the
closest prior art, §6) or an annotation. A reduction over an array or a balanced tree written as a
divide-and-conquer already has its bracketing fixed by the program, and does not need the law.

**It also does not decide grain.** The criterion asks about safety. Where the split pays is a
separate question (§5), and it is the one that forces an annotation or a runtime mechanism.

---

### 3. The proof obligation

Our theorems are stated about closed typed programs and the machine (`adequacyC`,
`Core/Fundamental.lean`; `adequacyD`, `Core/Demonic.lean`; `total_every_run`,
`Core/Totality.lean`):

    adequacyC : CDerives ∅ [] e (F 1) → Steps ∅ e ∅ (val ())
    total_every_run : CDerives ∅ [] e (F A) → every run from ∅ continues to a value

The parallel statement has the same shape, over a parallel machine and a set of fork points read
off the typed term.

**Forkable node.** For a typed term `t` (SPEC §3), a node `n` of `t` is *forkable* when it is
`M₁ to x. (M₂ to y. N)` (or `pair`/`tensorI` of two value judgments), and

1. `M₁` and `M₂` are typed at `F_∅` (the row is a field of the node);
2. the inner bind's masks give `x` to `N`'s part, not to `M₂`'s (`SplitMasks`);
3. the outer split gives `M₁` and the continuation disjoint live slots, shared only at persistent
   types (`Ctx.SplitP`, which the derivation fixes);
4. no node under `M₁` or `M₂` is a SemC-only site: an extern, a `trust` site, a `PinLaw` field.
   This is #212 scoping's B1: a term valid only through `SemC` may write through an `Imm` and
   undo the write, which a big-step relation cannot see. Every such site is a node kind, so the
   condition is a pattern too.

**Parallel machine.** `PStep_F`, for a set `F` of forkable nodes of `t`: `Step1`'s heads in a
`PKont` that, at a node of `F`, holds both sides and steps either (#212 scoping B5, O-Mach).
`Step1` is `PStep_∅`, so the sequential machine is a special case and the interpreter, the
corpus and the backends are unchanged.

**The statement.**

    adequacyPar :
      TDerivesAt Ξ ∅ [] t (F A) → (∀ n ∈ F, Forkable t n) →
      ∀ run of PStep_F from ∅ at t.erase,
        it continues to some (μ′, val v), and
        ∃ τ (a bijection of locations moving each allocated block whole),
          Steps ∅ t.erase (τ • μ′) (val (τ • v))

with the corollaries that every parallel run gives the sequential value up to `τ`, that two
parallel runs agree up to `τ`, and that output bytes, which go through one exclusive
`Mut Output`, are equal (#212 scoping B7). `F` ranges over *every* set of forkable nodes, so the
theorem licenses any scheduler, including one that forks at no node, at all nodes, or at the nodes
a heartbeat promotes (§5). That universality is what makes "automatic" a scheduling question
rather than a semantic one.

**What it needs** (#212 scoping §4, with its names):

| obligation | content | status there |
|---|---|---|
| U1, footprint component | the run `wpTS` exhibits is a permission run: loads in Rd ∪ O, stores and frees in O; permissions split at the fork as the context splits | UNKNOWN cost; BELIEVED mechanical at the witness constructions |
| B2, O-Fp | `Hash ρ₁ ρ₂ → Wr ρ₁ ∩ Rd ρ₂ = ∅ ∧ Wr ρ₂ ∩ Rd ρ₁ = ∅`, from `ResU.Flat.split` and `wpTS_footprint` | BELIEVED; "ex = writable" not checked |
| B3, O-Reorder | every interleaving equals, up to renaming, a sequential schedule consistent with the steps' dependency order; well-founded by `total_no_infinite_run` | BELIEVED, medium (Brookes/O'Hearn) |
| B4, O-Ren | `Step1` equivariant under block renamings, array steps included | BELIEVED, low to medium |
| B5, O-Mach | `PKont`, `PStep` | BELIEVED, low |

`adequacyPar` is #212's B6 at a typed term and a fork set instead of at an explicit `join`. Its
condition 4 is the only addition, and it is a node pattern. Nothing in this note makes U1 cheaper:
the automatic version and the annotated version need the same footprint fact.

**Why `fundamentalC` alone does not give it.** `wpTS` (`Core/World.lean`) says: for every frame
`ρf` and every allocator, the run from the lowered heap reaches a value and leaves the frame's
cells as they were. It says nothing about the states in between. A run may read a frame cell, or
write one and restore it, and still satisfy `wpTS` for every frame; run beside a sibling that
owns that cell, it races. The typed terms never do this, but `wpTS` cannot say so. That is the
whole content of U1.

**The div-free hypothesis is used twice.** Sides cannot diverge, so a fork always joins
(`total_every_run`), and the reordering induction is well-founded. A `Loop` side needs #212's U6,
a parallel `Loop` driver, and is outside this fragment.

---

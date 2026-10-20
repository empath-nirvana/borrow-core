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
   (heartbeat scheduling, §5). Bend 1/HVM2 took a third route, every redex is a task, and paid for
   it in single-thread speed; Bend 2 abandoned that route for explicit fork marks (§4).
3. **Proof: the obligation is stated, not discharged.** "Parallel = sequential" does not reduce to
   `fundamentalC`/`adequacyD` as they stand, because `wpTS` is a start-to-end relation with a
   fixed frame and no per-step footprint. #212's scoping already names the routes (0, C, B); this
   note restates the obligation in the shape of our adequacy theorems (§3).

What Bend does not have and we do: two parallel branches may each mutate in place a disjoint
`mut` part of *one* array, and the owner gets the whole array back at the join with no copy
(`slice_split_mut`, SPEC §9). Bend 1/HVM2 has no mutable arrays at all. Bend 2's arrays are
affine and updated in place by their one owner, but a value cannot be shared, borrows are
inferred and read-only, and "atomic arrays shared across threads are experimental and need
`@unsafe`" (Bend 2 README). A Bend 2 branch mutates an array it owns whole (§4).

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

### 4. How Bend answers the same question

There are two Bend lines, and they answer differently. Bend 1 (`HigherOrderCO/Bend1`) runs on
HVM2. Bend 2 (`bendlang/bend`; `HigherOrderCO/Bend2` is now a stub that points there) runs on
BendRT and checks against BendTT. Sources were shallow-cloned at `bendlang/bend` 642d8e1
(2026-10-20) and read as data. Both Bend 2 papers say they were written by an AI model from the
author's code. They are quoted here as the authors' published claims.

#### 4.1 Bend 1 on HVM2: automatic, every redex

- **Who decides.** Nobody: "just compute global redexes concurrently, until there is no more work
  to do" (HVM2 paper §8, FT). The guide: "Anything that _can_ be parallelized _will_ be
  parallelized" (FT).
- **Why the result is unchanged.** Strong confluence of interaction combinators (Lafont): "for
  each active pair exactly one rule applies, HVM2 retains the same strong confluence … the number
  of reductions is invariant to the order" (HVM2 §4.9). The argument is prose. The paper notes
  a defect in its own rule table ("CON-SWI being comm is problematic"), argues the atomic linker
  by three example orders, and none of the five HigherOrderCO/bendlang repositories holds a
  mechanised confluence proof for IC or HVM2.
- **Independence.** Structural: an interaction net has no shared mutable state. Sharing is by
  lazy DUP nodes, inserted automatically, and it is sound only on a restricted class. "A
  higher-order lambda that clones its variable can not be cloned" (HVM2 §13.1), and Bend 1's
  guide says the runtime catches the bad case "but at the moment that is not always the case"
  (`docs/dups-and-sups.md`).
- **Grain.** One interaction. CPU: a task-stealing bag where thieves take old redexes. GPU: block-
  local rounds of 2⁹–2¹³ interactions. One compiler-emitted mark, `!` on branching-recursive
  definitions, restricts which redexes the GPU shares; it took bitonic sort from 1,300 to 12,000
  MIPS (HVM2 §8).
- **Cost.** About 5× slower than GHC on one thread, "100x on programs that involve loops and
  mutable arrays, since HVM2 doesn't feature these yet" (HVM2 §13.3). 400 MIPS on one thread, 5,200
  on 16, 74,000 on an RTX 4090 on a tree map (abstract).

#### 4.2 Bend 2 on BendRT: explicit, balanced forks

- **Who decides.** The program. "The parallel let `l r = f(x) g(y)` … means: run these calls in
  parallel; they split the work into roughly equal parts. The mark `sum!(t)` means: run this call
  on the GPU. Nothing else creates parallelism" (BendRT, FT). Interaction nets are gone:
  "Readers of the author's earlier runtimes may expect interaction nets here; there are none."
- **Why the result is unchanged.** "Since Bend is pure and affine, the first point
  [independence] always holds. The second [balance] is yours to keep" (Bend 2 guide). Effects never
  reach parallel code: they run only in a single-threaded event loop ("Effects never run inside an
  evaluator, and the machine performs no IO"). The runtime is unverified: "the correctness argument
  is the checksum discipline plus the type system's guarantees, and the companion paper's theorems
  stop at the calculus" (BendRT §12).
- **Grain.** Bulk-synchronous: a 128×128 grid of rings forks along rows while the frontier is
  below 2¹⁴, then each lane drains its column sequentially, where "a fork met while draining runs
  as a plain call" (lazy task creation). No work stealing: "balance is the program's job", and
  "the equal-parts contract is unverified: a skewed program silently loses its parallelism"
  (BendRT, Limitations).
- **Cost.** Sequential 0.8–1.5× of a hand-written C twin; 8.8–12.1× on 16 threads; 52–67× on GPU
  for uniform work; divergent work (n-queens, symbolic regression) loses to 16 threads (BendRT
  Table 1, Apple M4 Max; only the Metal GPU lane is measured).

#### 4.3 What our borrows add, and what Bend has that we do not

| | Bend 1 / HVM2 | Bend 2 / BendRT | us |
|---|---|---|---|
| independence from | the net's structure (no shared state) | purity plus affinity | the context split plus `F_∅` (typed, on the term) |
| who forks | the runtime, at every redex | the program (`l r = f g`, `f!`) | §8's menu: annotation with a check, or a runtime with a proved bound |
| result-preservation proof | prose (strong confluence) | none for the runtime; BendTT confluence is of the calculus | stated (`adequacyPar`, §3), not built |
| in-place writes in parallel branches | none (no arrays) | an owned array, whole, per branch | disjoint `mut` halves of one array, handed back at the join |
| shared reads | lazy DUP, sound on a restricted class | copies of `Data` (kind of first-order values), reference counts placed by the compiler | `Imm` views copied for free; `!` values hold no resource |
| effects in parallel code | IO is a free-monad request (experimental) | never: one event loop | none at `F_∅`; abortive sides need L5 (§1) |
| sequential speed | 5–100× slower than GHC | close to C | the sequential lowering is the reference (#212 scoping §5) |

The difference that matters is the middle column of the in-place row. In Bend 2 a branch that
updates an array owns all of it. Dividing one array among branches means rebuilding it as a tree
of owned pieces (its source representation is a perfect binary tree walked by index bits) or using
`@unsafe` atomics. Ours lends both halves of one flat block at one lifetime and needs no
reassembly, because the lend's end hands the block back. Whether Bend 2 can split an owned array
into two owned halves without a copy was not found in the sources read (**unchecked**).

---

### 5. Grain and cost: who decides, without heuristics

The standing rule: performance by construction in our IR; LLVM only through forcing annotations
with a check, never heuristics or hints. Applied to forking, a heuristic is any compile-time guess
about size ("fork if the subtree is large"). The options that are not heuristics:

| mechanism | who decides | guarantee | prior art | fit |
|---|---|---|---|---|
| **forcing `join`/`par` with a check** | the program, at a site; the checker refuses a site that is not forkable (§3's four conditions) and says which condition failed | the site forks; the result is the sequential one under `adequacyPar` (or `ParLaw`, #212's Route 0) | Rayon `join` (a hint that the scheduler may ignore; docs.rs, AB), Cilk `spawn` (the serial elision is a correct implementation; Cilk-5 PLDI 1998, FT pp. 1–2), Bend 2's parallel let | matches the rule exactly. A site the checker cannot verify is an error, not a silent sequential fallback (#212's kill criterion for silent fallback) |
| **depth budget as grain** | the program, as a number: `bounded_fix`'s budget, whose spent branch is the sequential base case (§1) | at most 2^k tasks; no `Exhausted` in the row | Bend 2's "grow while the frontier is below 2¹⁴, then drain" is the same cut-off chosen by the runtime | uses an existing kernel constant; the budget is explicit and checked by typing |
| **heartbeat scheduling** | the runtime: every fork site is latent, and one is promoted to a real task once per heartbeat (every N μs of work) | "mechanized proofs that the scheduler guarantees low overheads for all nested parallel programs … without requiring manual tuning" (Acar, Charguéraud, Guatto, Rainey, Sieczkowski, PLDI 2018, AB) | the only prior art found that gives a proved overhead bound with neither per-site annotation nor a size guess | under `adequacyPar` with `F` ranging over every fork set, the schedule is invisible to the result; what is left is a runtime with a proved cost bound, in the spirit of "by construction". It needs a latent fork point in the compiled code at every forkable node: a cost in code size and a check per beat |
| **lazy task creation / work stealing** | the runtime: a fork pushes a cheap frame, a thief takes the oldest | work-first principle: overhead lands on the critical path, not on the work (Cilk-5) | Rayon, Cilk, HVM2's CPU bag | needs a fork frame at each site; with annotations it is Rayon; without them every forkable node pays a push, the "every redex" cost in a milder form |
| **work-depth cost model** | nobody at run time; the language gives a cost semantics | NESL: work and depth as a language-level model (Blelloch, CACM 1996, AB) | NESL, DPH's flattening of nested to flat parallelism (Peyton Jones et al., FSTTCS 2008, AB) | a specification of costs, not a scheduler; useful for the corpus count rule (#212's D6) |

Two observations.

- **Balance is not a typed fact in any system read.** Bend 2 trusts "the equal-parts promise
  absolutely" and states that a skewed program silently loses its parallelism. Work stealing and
  heartbeats repair imbalance at run time. A static split cannot.
- **The automatic route is a runtime route.** If forking is to need no annotation, then the
  decision must be made at run time by a mechanism whose cost is bounded by a theorem (heartbeat),
  and the compiler's only job is to keep every forkable node forkable. That is consistent with the
  standing rule only if the runtime mechanism counts as "by construction", which is the user's
  call (§8, item 2).

---

### 6. The rows on #619's list

Each row: what Bend does → whether it changes a decision we have made or one that is pending.

| item | what Bend does | for us |
|---|---|---|
| **Affine values; arrays without sharing** | Bend 1/HVM2: affine, with automatic lazy DUPs, sound only when no cloned lambda clones its variable (HVM2 §13.1). Bend 2: affine; only kind `Data` (no functions inside) may be used twice; `map` with a closure argument is refused; arrays are `Type`, one owner, updated in place; shared atomic arrays need `@unsafe`. | **No change.** Our linear/affine qualifiers, `!` for sharing code, and `Imm` views for sharing data already cover this, and add disjoint `mut` views. Bend 2's `Data` kind is the same cut as our `VTy.Persistent` (copyable because it holds no resource); a point of comparison for #489's derive work, not a change. |
| **`fold`/`bend` from `~` recursive fields** | Bend 1: `type Tree: Node { ~left, ~right } Leaf { value }`; `fold` calls itself on `~` fields implicitly; `bend` is the matching unfold with `fork`. The guide: "You do not need to use these constructs at all." Bend 2 dropped both keywords, and `~` now marks a template parameter. | **Input to #489/#593 (pending).** Our `foldImm`/`foldOwn`/`foldReuse` (SPEC §6) are the `fold` half, typed and total; a data declaration could generate them from the declaration, recursive positions read off the `μ`, with no marker needed. The `bend` half has no total counterpart for `μ` in our kernel: building a tree is self-recursion (`{Exhausted}`, `corpus/rec-tree.bc`'s `build`) unless written over `bounded_fix` with a total base case. A depth-counted `bend` is a library candidate, not a kernel change. That Bend 2 dropped `fold`/`bend` is weak evidence that the surface keywords matter less than the semantics. |
| **Termination by default, `f?` / `@unsafe`** | Bend 1: unrestricted recursion. Bend 2: termination is mandatory, checked by lexicographic descent on case-tree pieces (BendTT §5.2); `@unsafe def` or `def f?` skips it, and the proof gate then names every def that relies on it. Server loops count down a `Nat` fuel. | **No change; confirms decision 67 (div is a handled effect) by contrast.** Bend 2's default is ours: an unmarked function terminates. The difference is where the escape lives: Bend's is a marker that leaves the proof, ours is a type (`Loop`, the `Div` row) that stays inside it (`runtime_every_run`, `divFuel_every_run`). Bend's fuel-counting servers are our `div_fuel`. Our recursion's depth budget (`Exhausted`) has no Bend counterpart; Bend proves descent instead. |
| **The Lean kernel `bendtt.lean`, the unproven translation, `--verdict`** | One Lean 4 file: the kernel's evaluator, conversion and checker, with `Claim.*` props proved as theorems (consistency of `Book.check`, confluence of parallel reduction, subject reduction, progress, halting of live code); no `sorry`/`axiom` found. The translation from Bend (TypeScript) and the parser are unproved; `--verdict` re-checks the translated terms with the proved kernel. The runtime is unverified. | **No change; a contrast for decision 27 and the trusted-base work.** Our relation is about the machine, so `adequacyD`/`total_every_run` reach the runtime semantics, which BendTT's theorems stop short of. Our gap is in the same place as theirs, between the checker's front end and the kernel: SPEC §3's typed term (`TExpr.erase` is the checked term by definition) already closes the part `--verdict` leaves open. `--verdict`'s idea, a second, small, proved checker run on the elaborated term, is available to us cheaply if the checker ever grows past the kernel's rules. |
| **`LAWS.bend`: user laws re-proved on edit** | A convention plus a gate: `LAWS.bend` states laws as dependent types (human-written); `PROOF.bend` proves each by an ordinary def; `bend PROOF.bend` prints ALL PROOFS CHECK only when all hold. "Re-proved on edit" means re-running the gate; no incremental mechanism. Example: `Par.sum(d, i) == Par.seq(Par.pow2(d), i)`, a fork-join tree equals the sequential loop. | **Bears on a pending question.** This is exactly the missing fact of §2.1 (associativity, for reassociating a reduction). We have no user-level proof language; our laws are Lean theorems about library terms (SPEC §18 *Laws*). Options in §8, item 4. The decided "trust, not assurance ceremony" stance (`trust e`, generated trusted base) is the cheap form: a declared law is a trusted site. |
| **Interaction-net runtime without GC (lazy dup)** | HVM2: no GC pass, erasure by ERAS/VOID interactions; laziness from REF nodes. Bend 2 dropped nets: a match frees the node it consumed, compiler-inferred reference counts for shared `Data` (count in a separate word), inferred borrows; "Drop is the runtime's only collector". | **No change; confirms "no GC, no implicit RC".** Bend 2's move away from nets toward affine drops plus *inferred* RC is the direction our decisions reject (implicit RC). Our destructors (SPEC §12) are the drop half. |
| **Multi-target lowering (C/CUDA/Metal/JS)** | Bend 2: one C file is both CPU program and GPU kernel; Metal measured, CUDA in source; JS runs forks in sequence on one core; CPU and GPU never compute at once. HVM2: Rust, C, CUDA. | **No change; agrees with "portable lowerings" and "backends implement SPEC".** Bend's JS lane is our Wasm lane: forks sequential, same answers. The GPU lane needs uniform work and a different memory model; outside every target program here. |
| **IO monad vs our handlers** | Bend 1: `IO` as a free-monad request/continuation (experimental). Bend 2: `IO` as a CPS type with ops `Emit`/`Halt` (and `Exit` in `base.bend`; BendRT says two constructors), a generic `do` over any monad, effects as foreign host functions, one event loop with `IO.fork`/`join`/channels. | **No change; contrast for the effects decisions.** Bend confines all effects to one event loop so parallel code is pure by construction. Our `F_∅` gives the same separation per subterm, by type, and allows effects elsewhere in the same function. Bend's monadic surface is what "no surface monads" rejects. |

---

### 7. The strongest ideas from Bend for us

1. **Bend 2's retreat is evidence.** The line that bet hardest on automatic parallelism (every
   redex) now requires explicit, balanced fork marks, and reports a 5–100× sequential penalty for
   the automatic design. "Automatic" in the HVM2 sense cost more than it saved.
2. **A law that a fork tree equals the sequential loop** (`demos/pure_par_sum/LAWS.bend`) is the
   user-level form of `adequacyPar`. For divide-and-conquer whose bracketing differs from the
   sequential program's, this is the obligation the user owes, and Bend makes it a checked artefact.
3. **The grow-then-drain grain** ("a fork met while draining runs as a plain call") is the
   depth-budget idea: our `bounded_fix` with a sequential base case already expresses it as a typed
   number.
4. **Effects never in parallel code** is our `F_∅` restriction, which Bend arrived at by
   architecture (one event loop) and we have by type.
5. **A proved second checker on the elaborated term** (`--verdict`) is a cheap assurance pattern if
   our front end ever diverges from the kernel's rules.

---

### 8. Decision menu

None of these is recorded as a decision.

1. **Where the independence fact comes from.**
   - (a) The typed term's masks and rows at a node, plus "no SemC-only site underneath" (§3's
     four conditions). No new analysis. *Recommended.*
   - (b) A separate effect/region analysis in the style of DPJ (**unchecked**). Duplicates what the
     derivation already fixes.

2. **Who forks.**
   - (a) A forcing `join`/`par_for`, checked against the four conditions, refused with the failing
     condition named. Matches the standing rule as written; is #212's design. *Recommended first.*
   - (b) No annotation: every forkable node is a latent fork, and a heartbeat runtime promotes
     them. Needs a runtime with a proved overhead bound, a latent-fork lowering, and the user's
     ruling on whether that counts as "by construction". Only after (a) runs.
   - (c) A compiler size heuristic. Excluded by the standing rule.

3. **The proof.** As #212 scoping: Route 0 (`ParLaw`, a named assumption, as `PinLaw`), Route C
   (footprint component, reordering theorem), Route B (small-step). This note adds only that the
   automatic version needs nothing beyond the annotated one: `adequacyPar` over every fork set is
   the same footprint argument. *Recommendation unchanged from #212: Route 0 now, C later.*

4. **Reassociated reductions (the k8s list's reduce).**
   - (a) Not provided: a list reduce stays sequential; a program that wants it writes a tree or an
     array and forks the divide-and-conquer itself. *Recommended now.*
   - (b) A declared monoid law, trusted at the site (`trust`), so a library `par_reduce` may
     reassociate.
   - (c) A proved law, as Bend 2's `LAWS.bend`, which needs a user-level proof language: a large
     step, outside every target program.

5. **Recursion at `{Exhausted}` in a fork.**
   - (a) Forks only at `F_∅`; divide-and-conquer libraries use `bounded_fix` with a sequential base
     case, the budget doubling as grain. *Recommended*; needs the surface check in §1.
   - (b) Admit `Row.Unwind` sides with L5(i) ("both complete, re-raise the leftmost"), an explicit
     `join` only, since it is not the sequential result.

6. **A total `bend` for `μ`.** A depth-counted unfold in the library, for #593's data declarations
   to pair with the generated folds. A library question; no kernel change.

---

### Sources

**Bend / HVM (read from clones of the repositories, as data):**
- HVM2 paper, `paper/HVM2.pdf`, github.com/HigherOrderCO/HVM2 (FT; marked "work in progress", §11
  Benchmarks is "TODO").
- HVM2 README (FT); HVM3 and HVM4 READMEs (opening sections only).
- Bend 1: `GUIDE.md`, `docs/syntax.md`, `docs/dups-and-sups.md`, `src/fun/builtins.bend` (FT);
  `README.md`, `FEATURES.md` (searched), github.com/HigherOrderCO/Bend1.
- Bend 2, github.com/bendlang/bend at 642d8e1: `README.md` (FT), `guide/GUIDE.md`,
  `guide/EFFECTS.md`, `bend2/base.bend`, `WONTFIX.txt`, `demos/*/LAWS.bend` (relevant sections).
- *BendTT: An Affine Dependent Type Theory*, `paper/BendTT.pdf` (FT).
- *BendRT: A Parallel Runtime for CPUs and GPUs*, `paper/BendRT.pdf` (FT).
- `bend2/bendtt.lean`: header, `Claim.*` definitions and final theorems read; whole file searched.

**Literature:**
- Rayon `join`, docs.rs/rayon (AB, through a summariser). `par_iter` splitting and `split_at_mut`
  docs: **unchecked**.
- Frigo, Leiserson, Randall, *The Implementation of the Cilk-5 Multithreaded Language*, PLDI 1998
  (FT, pp. 1–2).
- Blelloch, *Programming Parallel Algorithms*, CACM 39(3), 1996 (introduction).
- Peyton Jones, Leshchinskiy, Keller, Chakravarty, *Harnessing the Multicores: Nested Data
  Parallelism in Haskell*, FSTTCS 2008 (AB). Chakravarty et al. 2007 DPH status report:
  **unchecked**.
- Westrick, Yadav, Fluet, Acar, *Disentanglement in Nested-Parallel Programs*, POPL 2020 (AB):
  destructive effects are allowed when concurrent threads do not learn of each other's
  allocations; determinacy-race freedom implies disentanglement. Our split is a static instance
  of that condition for the `F_∅` fragment (BELIEVED; the correspondence was not worked out).
- Arora, Westrick, Acar, *Provably Space-Efficient Parallel Functional Programming*, POPL 2021:
  **unchecked** (search summary only).
- Raghunathan, Muller, Acar, Blelloch, *Hierarchical Memory Management for Parallel Programs*,
  ICFP 2016: **unchecked** (search summary only).
- Guatto, Westrick, Raghunathan, Acar, Fluet, *Hierarchical Memory Management for Mutable State*,
  PPoPP 2018: **unchecked** (title and appendix fragment only).
- Acar, Charguéraud, Guatto, Rainey, Sieczkowski, *Heartbeat Scheduling: Provable Efficiency for
  Nested Parallelism*, PLDI 2018 (AB).
- Bocchino et al., *A Type and Effect System for Deterministic Parallel Java*, OOPSLA 2009:
  **unchecked**.
- Lafont, *Interaction Combinators* (1997): cited through HVM2 only, **unchecked**.
- #212's scoping comment (2026-10-16) for every route, obligation and law name used in §3.

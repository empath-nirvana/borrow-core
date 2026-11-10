# #835: E10 read through public and private world transitions

*History: a unit of #835, merged with #839. The code (`Core/Chain/`) is now its reference, `chain-interpretation.md` the design, and `assert-boundary.md` the analysis of the handler assumption. The text below is kept as the record.*

This is the mapping the brief asks for first. It covers E10 (a handler clause's `κ` read at `vN`),
`effHandleV`, `effHandleVB` and `reify`. The Lean results named here are in
`Core/Chain/Public835N.lean` and `Core/Chain/Kappa835N.lean`. §8 has the verdict.

## 1. Sources

The PDFs and their text extractions are in `scratch-archive/rule791/papers/`.

| Key | Paper | Used for |
|---|---|---|
| [DNB] | Dreyer, Neis & Birkedal, *The impact of higher-order state and control effects on local relational reasoning*, JFP 2012 (extended version of ICFP 2010). Cited by JFP numbering; ICFP numbers in brackets where they differ | the public/private structure and the effect of first-class control on it |
| [ADR] | Ahmed, Dreyer & Rossberg, *State-dependent representation independence*, POPL 2009 | the single-order ancestor: islands, laws, populations |
| [Yarrow] | Mathiasen, Timany & Birkedal, *Yarrow: Reconciling Effect Handlers and Region-Based Memory Management*, arXiv 2607.15876 | continuations captured inside a region |
| [Affect] | van Rooij & Krebbers, *Affect: An Affine Type and Effect System*, POPL 2025 | one-shot continuations in an Iris logical relation |
| [Hazel] | de Vilhena & Pottier, *A Separation Logic for Effect Handlers*, POPL 2021 | the bind rule's neutral contexts; the one-shot continuation as a wand |
| [Blaze] | de Vilhena, van Collem, Wright & Krebbers, *Blaze: A Relational Separation Logic for Effect Handlers*, POPL 2026 | the relational bind rule's restriction |

Timany & Birkedal (ICFP 2019) was not fetched.

## 2. What the papers' structure is

**Worlds.** [DNB] §7.1, Fig. 5 [ICFP Fig. 2]:
- A world is a list of islands. Each island is an STS `(s, δ, ϕ, I, H)`: a current state, the full
  transition relation `δ`, the public relation `ϕ ⊆ δ` (both reflexive and transitive), the
  inconsistent states, and a heap relation per state.
- Private transitions are `δ \ ϕ`.
- `W′ ⊒ W` moves each island along `δ`. `W′ ⊒pub W` moves each island along `ϕ`, and every new
  island must be safe.
- Islands are only added (`m′ ≥ m`); an island's transition system never changes.
- [ADR] Fig. 3 has a single order: populations and store typings grow, and laws are fixed.

**Which order each part reads** ([DNB] Fig. 6 [ICFP Fig. 3]):
- Values at `→` and `∀`, and heap relations, are monotone along the full order `⊒` (Lemma 1
  [Thm 1]).
- The continuation relation `K⟦τ⟧` reads only public futures:
  "`∀W′, v₁, v₂. W′ ⊒pub W ∧ (W′, v₁, v₂) ∈ V⟦τ⟧ ⇒ (W′, K₁[v₁], K₂[v₂]) ∈ O`".
- `E⟦τ⟧` takes continuations at the same `W` (biorthogonality).
- Monadic bind (Lemma 3) hands the rest of the computation "unknown related values in an unknown
  public future world".

**Private transitions need well-bracketed control.** [DNB] §5.1: "every time we pass control to the
context may be the last". Without control, a term may move privately inside a computation as long
as its extensional behaviour is a public move.

**First-class continuations collapse the two orders.** [DNB] §7.2, Lemma 10 (Cont) and Lemma 11
(Call/cc). `V⟦cont τ⟧` must be monotone along `⊒`, because every value is (Lemma 1). Continuations
are injected into values, so `K⟦τ⟧ ⊆ V⟦cont τ⟧` forces `K` to read `⊒` as well. In the paper's
words: "in the presence of call/cc, the private and public transition relations must be collapsed
into one" (`Island′`: `ϕ = δ`, `I = ∅`).

**One-shot continuations.** [DNB] does not say that one-shot continuations restore private
transitions. Its §9.3 (Friedman–Haynes) encodes full call/cc from one-shot continuations and a
local cell. Neither does it say anything about linear or affine continuations.

**Well-bracketed control other than call/cc.** [DNB] §8, exceptions: a raise passes control to
"the exception handler that was most recently pushed", so private transitions survive. The price is
a stronger `K` that also covers raised exceptions.

## 3. Our world changes, classified

| Change | Where | Class | Why |
|---|---|---|---|
| Allocation (`alloc`) | `rwp_alloc` | not a world change | The world `LocTy` records lends, not cells. A new `own` cell is a resource. ([ADR] §4.3 adds an island per `ref`; our `Ref` is ownership, which the resource carries.) |
| A new `mut` lend at a fresh `α` below the floor | `LocTy.add`, `extA_add` | **public** | `LocTy.extP_add`. [DNB]: "any extension of W with a new island is considered a public extension" (§9.5), and the new island is safe. |
| A new `imm` record at `α` below the floor | `LocTy.addImm`, `extR_addImm` | **public** | `LocTy.extP_addImm`. |
| A lend's fold at a stop (`mut(A, v, χ)` to `own(v) ● χ` in the lender's share) | `erwp_M_frameCR`, `erwp_M_frameCRG` | not a world change; a change of share | The world is `Θ` on both sides. What changes is which resource the obligation is read at. That is the step §5 checks. |
| A lend's unfold at resumption | the same frames | the same | — |
| A lend's exit (the key dropped, `vN_local`) | `extR_of_add` | **public at the lend's own floor `α`; private at the lender's floor** | `LocTy.extP_of_add` reads it at `α`. At a floor above `α` the dropped key is above the floor, and `ExtP` keeps such keys. This is [DNB]'s well-bracketed pattern: the lender moves privately inside, and the move is public extensionally. |
| An `imm` lend's exit (`extR_of_addImm`) | the Imm Frame | the same as a `mut` lend's exit | — |
| Other tasks' records (resumption along `extF`) | `entN`'s `wc` | public, on the record list | `extF` keeps every record a frozen location names (`SI/ExtF.lean`). Records are dropped only when no share names them. |
| A view change at a location outside the share | `U`'s and `⊸`'s `∀ c, ConsistentX c ρ` | **public** | The view at a location belongs to whoever holds that location's cell. A move by the context there is a move on another island. |
| A view change inside the share | none | — | `ConsistentX` fixes the view on the share's exclusive walk. |
| Lowering the floor | each lend | **public** | It narrows the futures (`LocTy.ExtP.mono` read backwards). |

## 4. The public order `ExtP`

`LocTy.ExtP lo Θ Θ′ ρ` (`Core/Chain/Public835N.lean`) is the conjunction of:

1. `Θ.ExtR Θ′ ρ`;
2. every key strictly longer-lived than the floor `lo` is the same in `Θ′`;
3. the `imm` records lent strictly above `lo` are the same list.

`lo` is the floor: the lifetime below which every lend from here on is taken. In [DNB] terms, the
lifetimes at and above the floor are the islands present, and clause 2 is "the islands present move
only publicly". A live lend's island has no public transition until its own exit. Below the floor
`ExtP` is `ExtR`.

Laws proved:
- `ExtP.extR`, `extP_refl`, `ExtP.trans`;
- `ExtP.mono`: a higher floor asks less;
- `ExtP.above_eq`: at and above the floor, `above` is unchanged;
- public moves: `extP_add`, `extP_addImm`, `extP_of_add`.

`ExtP` is a sub-order of `ExtR`. It is the collapsed order [DNB] §7.2 forces (§2): since `κ` is a
value, the obligation a stop owes and the order `U` reads must be the same order. So `ExtP` is
both. What is private is not a separate order. It is the moves above the floor, which only the
lender takes (its own exit), and only inside the code the captured continuation holds.

## 5. The three checks

### 5.1 `U` and the stop's obligation along `ExtP` give E10

Read `U`'s clause along `ExtP` at the value's world and floor. Let the stop owe its continuation
along the same order: at every `Θ′` with `Θ.ExtP lo Θ′ ρ`, every view consistent with the share,
and every list (`KapRelP`). E10 is then Core's `vC_kTy_of_kapRel` line for line. The two
quantifiers are the same quantifier, as Core's `ls` is (`hk ls′ he`).

**How the two `not_kapRelKTyN` configurations are excluded.** They are not refuted as rules. They
stop being instances, because the new obligation is no longer met by the stuck `κ = ()`:
- **The world.** `∅ + (ℓ′, α)` is a public extension of `∅` at every floor above `α`
  (`extP_world`). So `KapRelP` reaches the failing point, and `κ = ()` fails it
  (`not_kapRelP_world`). Above the key it is a private move (`not_extP_world`). That is the case
  where the stop's floor says the lifetime `α` is already taken.
- **The view.** `KapRelP` reads every view consistent with the share, the one that puts `ℓ′` at `α`
  included (`not_kapRelP_view`).
- **Both against `KapRelN`.** `kapRelN_not_kapRelP` shows that the obligation the chain's stop owes
  today (`KapRelN`, at one location typing) holds of `κ = ()` where `KapRelP` fails. So E10 needs
  the relation's stop to owe more than it does now (§7).

### 5.2 The lend's fold preserves `ExtP`

`LocTy.ExtP.fold`: read at the floor `A`, a public extension `Θ → Θ′` at the lender's share gives
`ExtR` at the borrowed share from `Θ + (ℓ, A)` to `Θ′ + (ℓ, A)`. It needs two things:
- the two shares agree on borrow cells shorter-lived than `A` (`hc`);
- no `imm` record of `Θ` was lent at exactly `A` (`hI`).

`extPFoldTransfer` is `not_extRFoldTransfer`'s statement with `ExtR` replaced by `ExtP` at the
floor `A`, and it is proved. The key that `not_extRFoldTransfer` adds above `A` is not a public move
at that floor (`not_extP_foldConfig`). That is the answer to the configuration.

The reading needs the floor at the lender's stop to be `A`, the lifetime of the live lend.
- [DNB]'s world still holds the lender's island, in its lent state, so its public futures exclude
  the move.
- Our lender's world `Θ` forgets the lend. The floor is the part of the island's state that `Θ` has
  to keep.

### 5.3 `vN_extR`'s users

| User | Move it takes | Under `ExtP` |
|---|---|---|
| `mut` lends (`w2`, `w3`, `wF`, `withbor2`/`2U`) | `Θ → Θ + (ℓ, α)`, `α` fresh | Public when `α` is below the floor. `LocTy.exists_fresh` already gives `α` below any bound, so the lend picks it below the floor. |
| `imm` lends (`withbor1`/`1U`) | `Θ → Θ.addImm (r, α)` | Public (`extP_addImm`). |
| Lend exits (`vN_local`, `extR_of_addImm`) | the key or record dropped | Public at the lend's floor (`extP_of_add`), and **only** there. The exit is the lender's own move, and it is inside the code the captured continuation holds. A `κ` whose share holds a cell at `α` is not in `Res_α`, so `vN_local` cannot carry it across the exit. |
| `withload` (`wl`) | the reborrow's `imm` record at a fresh `β` | Public (`extP_addImm`). |
| The constants (`constN_*`) | read `vN` at the world `Θ` they are given | Unchanged, except that the floor comes with the world. |
| The `⊸` argument | none: `⊸` is a wand at the function's own world (§8.1 of the interface) | Unchanged. |

**The one place this does not go through as is: the lender's post after an exit.**
- After `vN_local`, the result is read at `Θ` at the lend's floor `α`.
- `U` at a lower floor owes fewer futures (`ExtP.mono`). So `vN` at floor `α` does not give `vN`
  at the lender's floor `lo > α`.
- The lender's post must therefore be read at the floor the run has reached, which is lower than
  the one it started at. This is [DNB]'s Lemma 3 and [ADR]'s `E`: the post holds at an existential
  public future world.

## 6. Where our setting differs from the papers'

1. **The world is per run, not global.**
   - [DNB]'s world holds every island, and islands are only added.
   - Our run is `erwp` at one location typing `Θ.view c`, and its tables and post are read at `Θ`.
   - A lend's island lives only in the callback's run (`Θ + (ℓ, α)`). The lender's run never sees
     it. The fold hands the lender a share that no longer names the lend.
   - This is the difference behind `not_extRFoldTransfer`. The floor (§5.2) is the part of the
     lender's island state that has to survive into the lender's world.
2. **The world changes inside a run.** [DNB]'s `K` reads public futures of the world at the call,
   and the world advances through the run (Lemma 3's "unknown public future world"). Our `erwp`
   advances only the record list (`extF`). The location typing and the tables are fixed for the
   whole run.
3. **Lifetimes are stratified.**
   - A stored family reads the world above its key (`famL`), so a key added above a live lend
     changes the lend's typing (D4).
   - [DNB] islands are independent; [ADR] islands are separated by store typings.
   - The floor is how "above a live lend" becomes a public/private distinction at all. In [DNB] the
     distinction is a per-island transition relation instead.
4. **One-shot continuations are first-class here.**
   - `κ : U(…)` is a value, and it can be passed into a lend's callback and forced at
     `Θ + (ℓ, α)`.
   - That is [DNB]'s `cont τ` case (Lemma 10), so the collapse applies. One-shotness does not undo
     it ([DNB] §9.3).
   - What one-shotness buys is what [Hazel] §3.3 and [Affect] §5.3 say: the continuation may own
     non-duplicable resources (`KapRelN`'s share). It does not buy private transitions across the
     stop.
5. **The lender's private moves are bracketed inside the continuation.**
   - A stop under a live lend captures the lend's frame. The lend's exit, its only private move, is
     code inside `κ`.
   - So the private move never happens between the stop and the resumption. That is why reading the
     obligation at the lend's floor is enough, and why the fold transfer holds.
   - [DNB]'s call/cc can throw past a private move; our handler cannot run the lend's exit without
     resuming `κ`.

## 7. The more recent sources

**[Yarrow]**
- `Stack κ` is one exclusive resource (§4.1, Fig. 7). EWP-Do-Once surrenders the captured fibers'
  cells.
- The resume obligation is `Stack (κ₁′ ++ [(op, τ)] ++ κ₂) −∗ …` (§4, Fig. 9 `hdlGlb`): the
  captured suffix is restored verbatim and the handler's prefix `κ₁′` is arbitrary.
- In lifetime terms, the handler may open regions that end up *longer-lived* than the captured
  ones. That is the move `ExtR` at the borrowed share refuses, and `ExtP` forbids it at the floor.
- Yarrow allows it because its regions have no stratified meaning: nothing about a region is read
  "above" it. Ours do (`famL`, D4). Following Yarrow would mean the captured lend is re-based below
  the handler's new keys at resumption. That needs a lifetime-renaming invariance of `erwp` and of
  every stored family, which the development does not have.
- Yarrow is a unary program logic with no type interpretation (§8: semantic typing is future work),
  so it has no `U` clause to compare with E10.

**[Affect]** (Fig. 7)
- `τ −ρ⊸ κ := λv. ∀w. τ w −∗ ewp (v w) ρ {κ}` is a plain wand, not Kripke.
- EWP-Handle hands `k` the same plain wand. So E10 is immediate there: neither side quantifies
  future worlds.
- That works because the logic is Iris: every proposition is stable under the frame-preserving
  updates that play our lends' role. In [DNB]'s terms Iris is the collapsed model, with everything
  public.
- Our `erwp` at a fixed location typing is not stable under a lend. That is §6.1–6.2 again.

**[Hazel] / [Blaze]: neutral contexts**
- Hazel's Bind (Fig. 6) needs `N` to have no handler frame. Blaze's `unsound-bind` (§2.3) shows why
  the relational bind needs `traversable`/`neutral`: a context that handles the theory's effects
  changes what the effects mean.
- **This is not the analogue of the live-lend fold.**
  - A lend's frame is a neutral context: it handles no operation.
  - Hazel's Monotonicity and Frame rules put such a frame inside the continuation's wand, to be
    returned at resumption. That is what our Mut Frame already does (`erwp_M_frameCR` folds the
    borrow into the share).
  - The neutral restriction answers a different question: which handler a perform reaches.
- Our problem is not the frame's soundness. It is that the frame's world (the lend's key) is not in
  the world the handler's `κ` is read at. Neither paper has worlds to lose.

**Which source the design follows: [DNB].**
- It is the only source with a type interpretation whose values are Kripke along a world order, as
  `vN`'s `U` is.
- Its §7.2 collapse is the step that settles E10's shape: the stop and `U` must read one order.
- [Affect] and [Hazel] get E10 for free only because Iris makes every proposition world-stable.
  Taking that route means rebuilding `vN` in Iris (the `iris-lean` fallback), not changing an order.
- [Yarrow]'s verbatim restoration is the alternative to the floor, and it needs lifetime renaming
  (above).

## 8. Verdict

**The mapping holds for the order; the build does not reach E10.**

1. **The order.** `ExtP` at the floor is a sub-order of `ExtR`. It contains every move a lend, an
   `imm` record or a view change makes, and the lend's exit at its own floor. It is carried across
   the Mut Frame's fold (`extPFoldTransfer`), which answers `not_extRFoldTransfer`.
2. **E10.** With `U` and the stop's obligation both read along `ExtP`, E10 is Core's step (§5.1).
   Both `not_kapRelKTyN` configurations stop being instances (`not_kapRelP_world`,
   `not_kapRelP_view`).
3. **What the relation has to provide** (`kapRelN_not_kapRelP`). The stop must owe the handled
   continuation at other location typings `Θ′.view c′`, with tables and posts read at `Θ′`.
   `erwp`'s stop (`contShareN`) owes it only at the run's own `Θ.view c`. So the following step
   does not carry over: [DNB] Fig. 6's `K⟦τ⟧`, which reads public futures of a world that the run
   advances. It needs:
   - (a) `erwp` indexed by world-dependent tables and posts, with `contShareN` along `ExtP`;
   - (b) the floor carried by the run's world;
   - (c) posts at an existential later floor (§5.3's last paragraph).

   This is a change to the relation itself. 115 files use `erwp`. It was not built here.
4. **Not derived; obstruction not verified**, for (a)–(c) as a whole. No configuration shows that
   any of them fails. `kapRelN_not_kapRelP` shows only that the present stop does not give the
   reading.

**Fallback (#835, 2026-11-06).** Scope the feature so that only the scheduler catches operations
performed under a live lend.
- That removes the fold question (§5.2) from in-program handlers.
- It does not remove (a). Both `not_kapRelKTyN` configurations are stops with no live lend at all:
  the empty world and the one-key world, at the stop's own list. They still ask for the stop to be
  owed at other location typings.
- So the fallback does not by itself close E10 at in-program handlers. It was not examined further
  here.

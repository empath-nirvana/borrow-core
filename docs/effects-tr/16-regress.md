# §16 Does the effects-safety chain bottom out?

[← §15 The `Mut` cell with a rebased continuation](15-mut-cell.md) · [index](README.md)

Issue #269. This is a reading of the chain #249 → #268, not a new result. Nothing here is
mechanised. Each claim cites the Lean declaration it rests on, or is marked as a reading. A prior-art
survey of how other systems treat borrows across a suspension (#270) runs separately and is not
repeated here.

§15's labels are cited as renumbered on #251 (`T14.n` there is `T15.n` here). The chain, in
order: the cell lemma (§15, #249, #251), naturality (`experiments/Restrat`, #253), ghost-end and
its extensions (`experiments/GhostEnd`, #258, #260, #262, #264, #266), and the three unknowns of
#268. When this was written, #268's branch had no commits.

---

## 16.0 The answer in brief

1. **One thing fails at every level** (§16.2). A lifetime opened inside a suspended computation
   is still open at the suspension. Then the lender and the borrower of one lend are both inside
   the frozen state. That is the self-referential state machine. The hypothesis on #269 holds,
   with one refinement: what matters is where the **lend was opened** (the lender frame), not
   where the data is owned. A reborrow of an outside `Mut` view, made inside the suspended
   computation, is internal too. Lends opened outside the suspended computation never caused
   trouble: §14.2's case (E) and T15.6 need only existing lemmas.
2. **Why it regressed** (§16.3). BoLo's model assumes that lifetimes nest lexically: `Life = ℕᵒᵈ`,
   a fresh lifetime is below every live one, and `↭` brackets every borrow cell inside one run.
   An internal lend open at a stop breaks that nesting. Every fix restores it in the same way: end
   the lend at the stop and re-open it at a fresh, shorter lifetime when the computation resumes.
   That renaming is sound only for what is **parametric in the lend's lifetime**. So each fix
   pushed the obligation onto the next place the borrower's view can sit: the frame's code, a
   frame slot, data, closures the borrower builds, closures it calls, any `U` value, every type
   former, and the views of other internal lends. These places are finitely many kinds. Since
   #266 every type former is covered by one relation, route (b). One axis is left: the number of
   internal lends open at once.
3. **The measure** (§16.4). No single quantity bounds the levels, and none needs to. Each of the
   following is well founded:
   - the typing derivation, for the proof;
   - the type, for the relation's definition;
   - the lifetime strata, for the carrier and the predicates stored in cells;
   - least fixed points, for the stops;
   - the budget, for loops.

   The stack of open internal lends is not a measure. It is a parameter, universally quantified in
   the induction's motive. **One statement covers every level** (GFP, D16.2): the fundamental
   lemma at a relation indexed by the lend stack, by induction on the derivation alone. Every
   per-level object of the chain is a fragment of it.
4. **T15** (§16.5). No definition in the chain needs a recursive domain, and none of the
   generalisations it needs does either, provided five cut-offs hold. Four are already in the
   kernel:
   - bounded recursion;
   - positive `μ`/`ν`;
   - strict strata;
   - closed operation types.

   The fifth is a constraint on the lift: the relation is never stored in the typed world. With
   these five, full effects with borrows are feasible without step-indexing. Each cut-off is a
   language decision. Relaxing any one brings step-indexing back.
5. **The verdict** (§16.8) is **(a)**: there is a bottom, and its residue is finite and named. (c)
   is excluded for the kernel as specified. Two of #268's items are the only things that could
   turn a corner into (b). Separately, **(b) by restriction (i) is the kernel's present rule**
   (SPEC §19, T1). It is finite and nearly done on paper. What it costs is self-referential
   suspension (§16.6). Choosing between them is a language decision about which programs are
   wanted. It is not a proof question.

---

## 16.1 The chain, level by level

"Where the view sat" means the position, in the frozen state, of the borrower's access to the
internal lend: the position the level had to make valid at a fresh lifetime.

| level | issue | where the view sat | closed | left open | new construct, or the same problem moved |
|---|---|---|---|---|---|
| 0 | #249, #251 (§15) | the continuation stored in a `Mut` cell | the cell lemma for rebased continuations (T15.5); rebasing is 6.147 (`wpTS_box`) and 6.50 | O15.1, a lend spanning a stop; O15.2, relabelling at `U` | new: a stored continuation. The internal lend is excluded by T1 |
| 1 | #253 | the cell's stored invariant `P̂` | every definition natural under a re-stratification except `𝒱⟦Mut⟧` (`not_vDenNatural`) | `wp` naturality (`WpNatural`) | the same problem, at a stored predicate. It shows the renaming must re-create cells (re-lend), not move them |
| 2 | #258 | the frame's code and the root slot `m` | ghost-end (`freeze_at`), 6.65 at a resuming table (`ewpTS_M_frameR`), straight-line borrowers (`withbor_spans_yields_cC`) | general borrowers | new: freeze and re-lend |
| 3 | #260 | frame slots other than `m` (`StopSafe`) | typed borrowers (`withbor_of_rbody`), loops (`open_boundedFix`), affine drop | frames holding `'x` values; effectful premises | the same problem, one position over |
| 4 | #262 | data (`LOk`), closures the borrower builds (`TV`), closures it calls (`CloL`) | `withbor_of_rbodyT`, `withbor_of_rbodyC`, `callee_spans_yields` | a pure piece handed a `CloL` closure; `KernelInvariant` | the same problem, at data and then at closures |
| 5 | #264 | any `U` value of the ordinary relation | `URelend` named exactly (`frameThawsD_thunk_iff`); route (b) supplies it by construction | the fundamental lemma at route (b) | the same problem at every `U`. This is the last type position |
| 6 | #266 | every type former; the views of other internal lends | `uRelendRL`, the key steps of the non-routine compatibility lemmas, the guard `vRLg` | the stack of open lends | new axis: several internal lends. `thunkF_RL_fails_below_at` |
| 7 | #268 | a payload; an `Imm` lend; a nested lend | (running) | | cell kinds and nesting on the new axis |

Levels 1 and 3–5 move the same obligation to the next position. Levels 0, 2 and 6 introduce
something genuinely new: a stored continuation, the freeze, and a second internal lend.

## 16.2 The common failure

**One sentence.** At a suspension, some value in the frozen state may hold a borrow cell whose
lifetime was opened inside the suspended computation. At resume, that value must be valid at a
fresh, shorter lifetime, and the value's relation does not say that it is.

**The Lean shape.** It is `Relendable` (`RLCompat.lean`), and at the kernel's relation it is
`URelend` (`Bridge.lean`). Written for a predicate `P` indexed by the lend's lifetime:

    P α ls ρ  ⟹  ∃ d ρz ρn.  ρ = ρz ● ρn  ∧  dropC ℓ d ρn  ∧  ρz ∈ Res_α
                   ∧  ∀ ls' ⊒ ls.  ∀ α' ⊑ α.  (vwD ℓ T δ d α' ls' ─⋆ P α' ls') ρz

The value drops the cell, its remainder lies strictly above `α`, and the remainder, handed the
fresh view at any `α′ ⊑ α`, satisfies `P` at `α′`. This is the antitone closure of `P` in the
internal lifetime. It is a unary form of parametricity in `'x`, restricted to renamings that move
`'x` down.

**Testing the hypothesis.** Each level's hard case is a lend whose lender frame is inside the
suspended computation:

| level | what failed | internal lend? |
|---|---|---|
| cell lemma (§15) | O15.1: a body whose lend spans a `yield` | yes: D14.1's internal lifetime |
| naturality's `Mut` counterexample | moving a `mut` cell below the cut moves `P̂` into the gap | yes: only cells below the cut move, and the cells above it are fixed (`relRU_of_inStratum`) |
| ghost-end | the freeze and re-lend are needed only for a lend opened in the segment | yes, by construction |
| `FrameThaws` | a slot whose type mentions `'x` | yes: `'x` is the internal lend's variable |
| `CloL` | a callee stops with the internal lend's cell in its environment | yes |
| `URelend` | a `U` value holding the internal lend's cell (`capture_hides_lend`) | yes |
| `thunkF_RL_fails_below` | a view of a second lend, opened inside the first | yes: two internal lends |
| #268's three unknowns | a payload, `Imm` and a nested lend, each spanning a stop | yes |

**The refinement.** The hypothesis says "data owned inside". What is tested is where the lend
was opened.

- `withbor` (forms 1 and 2) moves its source's owner into its frame. A lend of a `Ref` opened
  inside therefore lends data the suspended state owns.
- `withbor` (3), `withload` and the slice borrows reborrow a view, which may be a view of an
  outside place. The inner lifetime is still internal: an outside `Mut` view reborrowed inside a
  generator, with the reborrow held across a `yield`, meets the same step.

The lender is then the outer view, held inside, so the frozen state still holds both ends of one
lend.

**Lends opened outside are finite.** In case (E) (§14.2) the handler is inside the borrow. It
needs one premise per capturer and `[]I` at the continuation, discharged by 6.60. T15.6 produces
rebased continuations from every body with no spanning lend, using 6.147 and 6.50 only. Neither
needed a new definition.

**Nothing else recurs.** O2 (in-place tables) and O8 (`withswap` across an abort or a
suspension) are open on separate grounds. O8's suspension case holds an anti frame across a
stop, which opens no lifetime, so O3's step does not arise there (§14.4).

The Restrat counterexample is the same root as the rest, met by a different mechanism. It says
that the renaming cannot be done by transporting a stored predicate, so it has to be done by
re-lending. Every later level re-lends.

## 16.3 Why it regressed

**The model assumes nesting.**

- A lend's lifetime is chosen below every lifetime of the resource it starts from (6.112, `fresh`).
- `↭` keeps every borrow cell of the flattening across a run. So a run can neither create nor end
  one (`upd_borrow_top`, `not_upd_of_new_mut`), and each borrow is bracketed inside one run.
- The typed world's Kripke order freezes the records that outlive a borrow cell's lifetime.

All three encode lexical nesting. A stop inside an internal lend breaks it. After the stop the
resumer may open its own lifetime `γ` with `α ⊏ γ`, and resume inside it.
`refold_fails_at_consumer_frame` builds exactly that list, and `refoldKripke_false` shows that the
old lifetime cannot be kept.

**Every fix renames.** Ghost-end ends `α` at the stop and re-lends at a fresh `α′` below
everything live at the resume. Nesting holds again. The cost is that everything in the frozen
state that mentions `α` must be read at `α′`.

**The renaming is parametricity, so it cannot be proved one syntactic class at a time.**

- Programs never see a lifetime. BoLo's terms carry none, since `Λ.` binds no variable, and the
  Restrat audit finds no definition that computes one. So the machine's run at `α` and at `α′` is
  the same run, and `Relendable` is a fact about the logic only. That is why it is true.
- It is also why it took an abstraction theorem. `𝒱⟦U C⟧` reads a closure only through its
  behaviour, so the part of its resource that is the internal cell cannot be found syntactically
  (`capture_hides_lend`). A property imposed from outside the relation holds only for the classes
  of value one can inspect: code by its typing, data by its type, closures by their derivation
  (`TV`). It fails at the first higher-order position whose contents are known only through the
  relation.

That is the sequence of levels 2 to 5. LoopBorrow had predicted the endpoint: refolding at a
fresh lifetime "would need the inner thunk's relation transported along a lifetime renaming. That
is a parametricity property of the relation." (`experiments/LoopBorrow/README.md`, *The dormant
lend*).

**Why it stopped.** Route (b) (`vRL`, `cRL`) puts the renaming into the relation's `U` clause,
read at a smaller type. A value of type `U C` is then re-lendable because its type is, and there is
no further position to reach. #266 classified every `CDerives` rule against it.

Two axes are not type positions, and both are finite in kind:

- **several internal lends open at once**: the stack. Its depth is unbounded, but it is one
  parameter (§16.4);
- **the cell kind** of each lend: `mut` or `imm`, the two borrow kinds of the carrier.

So "one order up" does not describe the chain. What it did was enumerate a finite list of
positions, which ended at the logical relation. The appearance of regress came from the method:
"unknowns first" proved a fragment closed under the rules considered, then looked for the next
rule whose premise leaves the fragment. That rule was always a higher-order one, because
first-order rules stay inside the fragment.

## 16.4 The measure and the single induction

**The measures each part uses.**

| object | well founded on | Lean precedent |
|---|---|---|
| the fundamental lemma | the `CDerives` derivation | `fundamentalC` |
| `vRL`/`cRL` (and the stacked form) | the type: the `U` clause reads `cRL C` at a smaller type | the `mutual` block in `Bridge.lean`, accepted by structural recursion |
| the carrier and stored predicates | the lifetime stratum: `Cell_α` stores `SProp_β` for `β ⊐ α` only | `Paper/S5_Model/Definitions.lean` (`Cell`, `ofDual` the measure) |
| the stops of a borrower piece | a least fixed point (Knaster–Tarski) | `OpenD`, `open_bind` |
| loops | the budget of `bounded_fix` | `open_boundedFix` |

**The stack is not a measure.** Each nested lend is at a strictly shorter lifetime, and
`Life = ℕᵒᵈ` is well founded only in the other direction, towards `⊤`. So the strata bound what a
cell can store, which is the T15 direction, and do not bound how deep lends nest. #249's levels
are the same measure: in `Cell.lean` a place at level `L + 1` holds trees at level `L`. They bound
content, not nesting. Nesting does not need a bound, because the induction never recurses on it.

**Definition D16.1 (the stacked relation).** This is a sketch. Its components are #266's four
changes, and the open parts are marked.

- A **lend stack** is `σ = [(ℓ₁, x₁, T₁, k₁), …, (ℓₙ, xₙ, Tₙ, kₙ)]`, with the `xᵢ` distinct
  lifetime variables of `Δ` and `kᵢ ∈ {mut, imm}`.
- A **lifetime vector** `α⃗` is in nesting order, `αₙ ⊏ … ⊏ α₁ ⊏ @bδ`, and
  `δ_σ(α⃗) = δ[x₁ ↦ α₁, …, xₙ ↦ αₙ]`.
- A **re-lend** `α⃗′` is a vector in nesting order, each entry chosen below the one just ended (as
  `OpenD`'s descending bound), and `α′ᵢ ⊑ αᵢ`.

The relation:

    vRL_σ (U C) α⃗ ls f   ≜ Relendable_σ (λ α⃗′ ls′. cRL_σ C α⃗′ ls′ (force f)) α⃗ ls
    vRL_σ (A ⊗ B)        ≜ componentwise
    vRL_σ A              ≜ a clause per former (⊕, !, [@a], μ, Ref, Mut, Imm), read at δ_σ(α⃗)
    cRL_σ (F_Σ B) α⃗ ls e ≜ OpenD_σ at Σ's own table:
                             answers in vRL_σ B;
                             a stop at the lenders' row ghost-ends every entry of σ and owes
                               OpenD_σ at every re-lend;
                             a stop at a row handled inside keeps σ open and owes a
                               Relendable_σ continuation;
                             a stop inside an inner lend is at an extension σ·τ
    cRL_σ (A → C)        ≜ ∀ v. vRL_σ A ─⋆ cRL_σ C (e v);  ∀, &, ⊤, ν as cC's
    vRL_[] = vC,  cRL_[] = cC

`Relendable_σ` drops one cell per entry, and its remainder lies strictly above the cut the
entries' table allows. `TabAt_σ` is `TabAt` for a stack. The exact form of both is #268's item 3,
and of their `imm` entries item 2. Neither is fixed here.

**Statement D16.2 (GFP, the generalised fundamental property).**

    ∀ 𝒟 : Δ; Γ ⊢ M : C.   ∀ σ well formed in Δ.   ∀ δ ∈ ⟦Δ⟧.   ∀ α⃗ in nesting order below @bδ.
    ∀ ls γ ρ.   TabAt_σ α⃗ ρ  →  𝒢RL_σ⟦Γ⟧ δ α⃗ ls γ ρ  →  cRL_σ C δ α⃗ ls (Mγ) ρ

*How the proof would go.* By induction on `𝒟` alone, with `σ`, `δ`, `α⃗` and `ls` in the motive.

- Each rule is one of #266's 85 rows.
- A rule that opens a lend applies the induction hypothesis to its callback's premise at
  `σ·(ℓ′, y, T′, k′)`. These rules are `withbor` (1–3), `withload`, the slice borrows, and
  O15.1's resuming `withbor`. The premise's derivation is smaller and the stack is longer, which
  is admissible because the stack is quantified.
- Stops are handled by `OpenD_σ`'s own induction, as in `open_bind`.
- `bounded_fix` is handled by its budget.
- There is no induction on `σ`, on `α⃗`, or on the length of a run.

*The conclusion at `σ = []`* is `fundamentalC`. At `σ = [x]` with a `withbor` around it, it is
O15.1's resume half (`withbor_of_relendOfTyped`, through `relend_of_openD`).

**Every earlier object is a fragment of GFP.**

| object | GFP at |
|---|---|
| `relend_chainΓ`, `RBody` (levels 2–3) | `σ = [x]`, the rules `ret`, `perform`, `let`, `1E`, `+E` |
| `RBodyT`, `LOk`, `lok_thaws` (level 4) | `σ = [x]`, `vRL` at `⊗`, `⊕`, `Mut`; `relendable_view`, `relendable_free`, `relendable_tensor` |
| `TV`, `RBodyC`, `tv_thaw` (level 4) | `σ = [x]`, the rules `thunk`, `lam` (`thunkF_RL`) |
| `CloL`, `cloL_call` (level 4) | `vRL`'s `U` clause at `U(1 → F_S B)` (`cloL_of_vRL`); `force_RL` |
| `URelend`, `KapRelR`, `KernelInvariant` (level 5) | `uRelendRL`; the inner-stop clause; GFP itself, which reads a pure piece's answer at `vRL` |
| `vRLg` (level 6) | `TabAt_σ` as a hypothesis |
| #268's items (level 7) | `σ` of length ≥ 2, `kᵢ = imm`, and `withbor`'s payload premise |

**The residue.** These are the rows of #266's table not yet derived, each named:

- `effThen` (a cancel of a frozen frame);
- `effHandle`'s inner-stop clause, and a handler frame passing the lenders' stops;
- `unfoldN`;
- the `*U` borrow constants;
- the resuming `withbor` inside a borrower (the nested spanning lend);
- an `Imm` lend spanning a stop;
- a payload mentioning `'x`.

Then the lifts of 6.64 and 6.150, whose added steps are proved (`opTable_extR`, `ptoImm_dup`).
The list is finite, and no item on it is a new level. Each is one compatibility lemma, or one
clause of D16.1.

## 16.5 T15: is a recursive domain needed?

**No, for the kernel as specified.** A definition needs a recursive domain when it refers to
itself at a position that is not smaller and is negative. The chain has five places where that
could happen, and each is cut:

| what would force it | the cut | Lean |
|---|---|---|
| unbounded recursion | `bounded_fix` (SPEC §20); divergence as `Loop` codata observed one step at a time (SPEC §14) | `open_boundedFix`; T9.4 item 1 |
| a recursive type with `X` negative under `U` | `μ`: `U C` is a leaf for type variables, so `X` never occurs under `U` (SPEC §6); `ν`: observations with closed arguments (`NuOk`, `A.Cl 0`; SPEC §7, §22) | `no_negative_domain` (`EffModelRel/Obstruction.lean`) |
| a store holding predicates over itself | the strict stratum of a borrow cell's predicate | `no_nonstrict_stratum` (`experiments/Outlives`); `no_place_store` (`EffModelRel/Cell.lean`); L15.9 |
| an operation type mentioning a computation of its own row | operation arguments and answers are closed data (SPEC §19: "operation types are closed data"; D1.2) | not stated separately. The shape: `cRL` at `F_Σ` would read the answer relation `PB` at `U(F_Σ …)`, under `─⋆`, at a type that is not smaller |
| the relation stored in the world | `TW`'s records are typed by `vShape`, `True` at `U` (`record_shape_thunk`); the stack is a parameter of the relation, not of `TW` | prose only (#264 item 1): `wpTS` takes `TW` as a hypothesis, so a record carrying the relation at `U` would occur negatively |

`vRL`/`cRL` pass Lean's structural recursion (the `mutual` block in `Bridge.lean`). D16.1 adds a
list parameter and one index to a least fixed point. Every reference it makes is at a smaller
type, a stored predicate (strata), or a positive fixed-point variable. That is a reading of a
definition not yet written; writing D16.1 in Lean would make it a fact.

**One thing to keep out.** LoopBorrow's register of open lends, a coordinate of `wpTS` and `TW`, is
the route that would put lend state into the world. If its entries carried predicates at `U`, the
fifth row would be crossed. Route (b) keeps the stack out of the world, and the lift should keep
it out.

**What would force step-indexing.** Relaxing any row:

- general recursion outside the delay codata;
- negative recursive types;
- unstratified higher-order store, or a non-strict stratum;
- higher-order operation signatures that mention their own row;
- relational worlds that store the relation.

RustBelt's lifetime logic stores arbitrary propositions in borrows and is built on Iris's
step-indexed model. That is the third row relaxed; see §16.6 (iii). Full effects with borrows are
therefore feasible without step-indexing, at these five decisions.

## 16.6 Making it evaporate

**(i) No internal lend may span a suspension. This is the kernel's present rule.** SPEC §19,
*Which operations cross a borrow's scope*: in a borrow's callback, answering operations cross
(they are calls) and abortive ones cross (unwinding ends each lend LIFO), but no other control
operation does (T1, #172). This is (i), stated on lifetimes. It makes the structure finite:

- **What remains to prove:** §15's T15.4–T15.6 and D15.7's `[gen]` rule (proved on paper, from
  existing lemmas); §14.2's case (E), an outlives premise per capturer and `[]I` at the
  continuation; O2, the in-place half of T9.2; O8, if `withswap` must survive an abort or a
  suspension.
- **What it deletes from the lift:** all of `experiments/GhostEnd`. That is the freeze and
  re-lend, `Relend`/`Open`/`OpenD`, `RBody*`, `TV`, `CloL`, `KapRelR`, `vRL`/`cRL`, and D16.1.
  The kernel's `vC`/`cC`/`KapRel` stay as they are.
- **What it recovers without proof:** the per-observation lend (LoopBorrow, landed:
  `lib/lend.bc`, `Frontend/Elab/LoopLend.lean`). The owner lives in the codata's state and each
  observation lends it. This covers a borrow taken again at each resume, generators holding a
  lender, async tasks in step form, and a div function with a borrow parameter whose body is
  visible.
- **What it costs, as program shapes.** Each is a lend opened inside a stored-continuation
  computation and open at its suspension:
  - **an opaque callee that suspends while holding a borrow of the caller's local**: a task
    allocates a buffer and calls a library function value that performs a resuming operation
    (an await) while the buffer is lent to it. LoopBorrow names this "a div callee with a borrow
    parameter" as the case that matters for no colouring. The elaboration covers it only when the
    callee's body is visible.
  - **a value derived from an internal borrow, live across a suspension**: an iterator or
    sub-slice over a task-local buffer, or a closure capturing the view, held across a `yield` or
    an await. Under the per-observation lend "a view is made inside a run and ends there"
    (`upd_borrow_top`), so these must be re-derived after the resume, for example by indexing.
  - **a reborrow of an outside `Mut` view held across a suspension** (`withbor` (3), slice
    borrows). The workaround is to re-slice after the resume.

  The workarounds that keep each program: hoist the owner outside the handler, which makes the
  lend external and bounds the continuation by `[@c]`; pass the buffer by ownership and get it
  back; re-borrow after each resume.
- **Not bought by any route:** a lending yield in pull form (`not_lendingYield_mut`,
  `not_lendingYield_imm`).

**(ii) Safety through compilation to state machines.** In plain BoLo, a struct that holds an owner
together with an open borrow of it has no type: `withbor`'s callback must return before the owner
is regained, and a frame is not a value. A typed translation of suspensions into state structs
therefore exists exactly for the programs whose internal lends end before each suspension and
are re-opened after it. Its image is (i)'s fragment together with the per-observation
elaboration. So (ii) is a second proof of (i), not a larger language. Its cost is a new theorem:
type preservation for a translation of captured continuations into structs. It is worth having
only if it doubles as compiler correctness for the backend's state-machine lowering. It does not
remove the residue of (a).

**(iii) Lifetimes as tokens.** This attacks the root, the lexical nesting, directly.

- #249's `Cell.lean` is a token model: a borrow is a `use r` token, a loan a `rsv r` token, there
  is no lifetime order, and a generator may hold a loan of its own resource across yields with
  nothing to rename. It needs no step index, but its borrowed resources carry no stored invariant.
- BoLo's borrows store a predicate `P̂`, and the strata are what make that impredicativity well
  founded. RustBelt keeps the invariants and drops the strata, and pays with Iris's step-indexing.
- The middle option keeps the strata over a well-founded partial order, with freshness relative
  to a lend's dependencies rather than to every live lifetime. It is a hypothesis, not checked.
  The carrier's algebra uses totality at `imm` cells' lifetime sets (`le_total` on joins and
  meets, `Paper/S5_Model/Definitions.lean`, `Support/Model/Algebra.lean`), and 6.112's fresh
  choice assumes a common lower bound. Either way it re-models [TR]'s carrier, the largest cost
  of any option here.

**(iv) Parametricity as the relation.** Stating the obligation as lifetime parametricity of the
relation, which is route (b) generalised, is the reformulation that removes the case-by-case
work. It is (a). Its cost is #266's list: every compatibility lemma restated, every consumer of
`vC`/`cC` re-pointed at the empty-stack instance, the stack table, the nested freeze, and the
6.64 and 6.150 lifts.

**(iv′) A first-order cut.** Allow an internal lend to span a suspension when, at every stop, it
is held only in the borrower's own frame slots, in `LOk` data, or in closures the borrower built.
Those borrowers are closed with every hypothesis discharged: `withbor_of_rbody`,
`withbor_of_rbodyT`, `withbor_of_rbodyC`. The fragment is semantic, however, and the syntactic rule
that would pick it out has no fundamental lemma. That lemma would be `RBodyTOfTyped` for the
rule's class, which is open. Its cost is that of (i) less the root-view and data cases, which
the per-observation lend already recovers. Its margin over (i) is small.

## 16.7 The toolbox

| tool | applies? | what it covers | why the chain did not use it |
|---|---|---|---|
| per-observation lend (LoopBorrow; SPEC §19, *Divergence*) | yes | the root-view case: ghost-end done in the program text. It is proved and landed | O15.1 asks about the kernel's captured continuation, whose observation re-enters a frozen stack with the lender's frame mid-callback. That continuation is `ν` codata (T15.4: an `Aff^c` object), but resuming it continues the lend; it does not open one. The per-observation form is a different program. Rewriting into it is ghost-end applied syntactically, and is possible only when the code is visible and nothing derived from the lend is live at the stop. So it gives (i), and avoids the residue rather than proving it |
| `ν`/`Aff` (SPEC §22) | yes, as the type of a stored continuation | T15.4, T15.5 | used, in §15 |
| #249's levels | to the heap axis | the T15 direction: what a stored generator can hold | they are the lifetime strata, and bound content, not nesting (§16.4) |
| second class = borrowed (#184); in-place tables (T9.2, L9.2) | yes, for second-class continuations | an internal lend across an answering operation: the stop is a call, and L9.2 ends every frame the clause opened before it resumes. This is O2 | the chain's target is the stored continuation (generators, tasks), which is first class by definition |
| independence and modes (ModesLabels, Shifts) | no | they classify structural rules, and read a label as a licence to break independence for a scope | the failure is the order of lifetimes, not which structural rules apply. Confinement of an internal-holding continuation (P14.3) is their reading, and it is (i) |
| the outlives box `[@c]` | yes, for external lends | case (E) in full | it cannot box a continuation holding an internal cell (P14.3 item 1) |
| non-strict frames (Relaxed; SPEC §4) | no | relaxes `FrameLife`'s bound on `imm` views | the refold fails at `Ext`'s freeze relative to a consumer frame, not at `FrameLife`. The stratum must stay strict (§16.5) |
| `bounded_fix` | yes | loops around stops (`open_boundedFix`) | used. Its budget is a run-time number and bounds no nesting, nor does it need to |
| determinism (`AStep1.deterministic`, `steps_replay`) | not needed | | the runs at `α` and at `α′` are the same run, since terms carry no lifetime, so there is nothing for determinism to add. Reusing the old run's induction hypothesis would need the re-lent state presented at the old lend, which is `RefoldKripke` (refuted). That last step is GhostEnd's reading, step 3a, and is not machine-checked |
| `relabel_reb`, `relabel_obs` | partly | the renaming at `imm` images, at data types | they stop at `U` (`vC_obs_aff`). This is O15.2, which route (b) answers by construction |
| TwoRun renaming (`steps_rename`) | no | permutations of locations | a lifetime renaming is a change of ghost state, not of the run |

## 16.8 Verdict

**(a), with a finite named residue. (c) is excluded for the kernel as specified.**

- **The bottom.** GFP (D16.2) at the stacked relation (D16.1), by induction on the derivation.
  Its definition is well founded by type, stratum and fixed point. No quantity bounds the levels,
  and none needs to: the stack is quantified, not recursed on. The induction terminates because
  derivations are finite trees, and every other recursion in it is one of §16.4's.
- **Why it is the bottom.** The obligation each level met is parametricity in an internal
  lifetime. Parametricity is a property of the relation at every type, and a relation defined by
  recursion on types has no further positions once its `U` clause carries it.
- **What could turn a corner into (b).** A Lean-stated obstruction at #268's item 3 (a nested
  lend spanning a stop, the 6.66 refold under the new witness) or item 2 (an `Imm` lend's set
  bookkeeping). The cut would then forbid that corner: an internal lend nested in another, or an
  `Imm` internal lend, spanning a suspension. That costs the corresponding shapes of §16.6 (i)
  for that corner only.
- **What would make it (c).** Relaxing one of §16.5's five cut-offs, or a resolution of #268
  that puts lend state carrying predicates at `U` into `TW`. Neither is on any current route.
- **What is not decided by proof.** (i) is a principled cut that is already the kernel's rule.
  It is finite, nearly done on paper (§15), and deletes `experiments/GhostEnd` from the lift. (a)
  costs #266's list. The choice is whether the language wants self-referential suspension: an
  opaque callee holding a task-local borrow across an await, or a value derived from such a borrow
  held across a suspension. For "no function colouring" that is the case LoopBorrow singled out.
  This is a language decision, not one the proofs make.

**What would settle the uncertainties.**

1. #268 item 3 decides between (a) and (b) for nesting.
2. Writing D16.1 in Lean, structurally recursive, makes §16.5's "no recursive domain" a fact
   rather than a reading.
3. Stating the operation-signature row of §16.5 in Lean (the shape of `no_negative_domain`) pins
   the fourth cut-off.

## 16.9 Report lists

- **Printed hypotheses not spent.** Not applicable. This section proves nothing, and its claims
  rest on the cited declarations.
- **Uniqueness and functionality results not used.** The machine's determinism (§16.7). Its use is
  not needed, by the reading given there.
- **Run-up lemmas untranscribed at resuming tables.** The lifts of 6.64 and 6.150 (their added
  steps are proved, `opTable_extR` and `ptoImm_dup`); the table of an `Imm` lend; D16.1 itself.

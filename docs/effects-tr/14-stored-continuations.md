# §14 Stored continuations, borrows, and proof cost

[← §13 The adjunction framing](13-adjunction.md) · [index](README.md)

**A candidate extension, not adopted** (#250). This section covers:

- the case the TR did not exercise: a continuation that holds a *borrow*, which uses BoLo's full
  model and not only its own-fragment (§9.1 item 4);
- capture rebasing and the re-stratification lemma it needs;
- the central lemma: a `Mut` cell holding a rebased continuation;
- T1 as a theorem;
- the verdict on proof cost (§14.5).

The setting is the kernel lift. The resource world is BoLo's full carrier (D4.1), with its
`imm` and `mut` cells, lifetimes, `[α]`, `↭` and the fresh-lifetime quantifier. Its `wp` is
borrow-core's `wpTS`/`ewpTS` (SPEC §19). Nothing here is mechanised. Each step names the
mechanised lemma it uses, or is marked open.

---

## 14.1 The borrow case, classified

**Definition D14.1 (internal and external).** Let a resuming operation stop with segment `S`,
up to its handler frame `f_H`, and resource `r_S`.

- A lifetime is **internal** to `S` when a frame of `S` opened it. Such frames are lends,
  [TR] 6.64's `withload`, 6.65's `withbor`, and 6.150's reborrow, together with the forms
  derived from them (slice, family and block borrows, which SPEC §23 derives from `withbor2`).
  `Int(S)` is the set of internal lifetimes.
- A cell of `r_S` is **external** when its lifetime is not in `Int(S)`. Such a cell is a borrow
  the segment holds from outside its handler.
- The **external footprint** `r_S|ext` is the composite of `S`'s external cells and of its
  `own` cells that are not the source of an internal lend.

The brief speaks of a handler extent `'h` with every internal lifetime below it. D14.1 does not
need such a lifetime to exist: a handler frame that opens a lifetime is one way to have one, and
the lift may or may not add it.

**Lemma L14.2 (stratification separates the footprints).** Every internal lifetime is `⊏` every
lifetime of an external cell of `r_S`. No external cell's stored predicate or witness contains an
internal cell.

*Proof (proved here, from [TR]'s definitions; not mechanised).*

- **Order.** An internal lifetime is opened by a frame of `S`. [TR] 6.112 (`Nf`) chooses it below
  every lifetime of the resource at that moment, and that resource includes every external cell
  `S` holds then. `S` acquires no external cell later: what enters a running segment from outside
  is an operation's answer or a resumption's argument, and both are ground (D1.2). At the lift
  they are closed data (SPEC §19: "operation types are closed data").
- **Containment.** A `mut` cell at `γ` carries its predicate and witness at a stratum `b`
  ([TR] §5 prints `Mut_α ≜ {(β ⊐ α, v, ρ, P̂ : Val → SProp_β)}`; borrow-core's `ptoMut`,
  `Paper/S5_Model/Definitions.lean`, takes `α ⊑ b` with the witness `InStratum b`). `InStratum b`
  admits only lifetimes `⊐ b`. An internal cell's lifetime is `⊏ γ ⊑ b`, so it is not in the
  witness.

The `imm` case is taken by analogy. I have read `Mut_α`'s stratum condition for this section; I
have not re-read `Imm_α`'s. ∎

Every borrow a continuation can hold falls into one of three cases:

| case | example | what a stored continuation needs |
|---|---|---|
| **(E) external** | `borrow mut buf { handle g { … yield … use buf … } }`: the handler is inside the borrow | an outlives bound: `κ : [@c] U K` with `c` the meet of its external lifetimes (§14.2) |
| **(I) internal** | `handle g { borrow mut buf { … yield … } }`: the yield is inside the borrow | either confinement (no rebasing) or rebasing (§14.3) |
| **(A) argument** | a borrow passed in at `resume` | none in this calculus: answers are ground. If §9.5's lifting is done, the argument joins the segment's external footprint, and the cell lemma asks it in the cell's stratum (L14.10) |

## 14.2 External borrows: an outlives bound

Case (E) needs no new idea.

- **Capture.** Every capturer of a continuation is listed in D2.6. Each gains a lifetime premise
  `Δ ⊢ Γ(x) ⊒ @c` for every captured `x`, beside its mode premise. Then `κ : [@c] U K`.
- **Compatibility.** The box is introduced by `[]I` at the continuation value. Its obligation,
  `r_S ∈ Res_c`, is 6.60 per captured value (`vC_outlivesLe`, SPEC §23), assembled as L5.4.2
  assembles modes.
- **Storing** beyond `c` is refused by outlives, as for a `Clo` closure (SPEC §22).
- **Resuming** within `c`: the external cells are live, and resume is L5.14's resume bullet at
  the full carrier.
- **Cancelling** a frozen continuation is "resuming it into `raise`" (SPEC §19,
  `cancel_compatC`). It ends the borrows inside it by the mechanised LIFO frame lemmas
  `ewpTS_I_frameU`, `ewpTS_M_frameU` and `ewpTS_M_antiFrameU`. Its external borrows are dropped
  by [TR] 6.148 and 6.149 (forget).

This is the route #249 tests: T1 by lifetime bounding. It needs a premise and its compatibility
lemma, and both are small. The structure under test does not change it.

**Property P14.3 (lifetime bounding alone, at an internal borrow).** *Argued here; not
machine-checked; not a claim about #249's results.* Without rebasing, a continuation whose
segment holds an internal borrow has cells at internal lifetimes in its resource. By L14.2 those
lifetimes are `⊏` every lifetime enclosing its handler. So:

1. **It cannot be boxed.** Its resource is in no `Res_c` for any lifetime `c` enclosing the
   handler.
2. **It cannot outlive any lifetime enclosing its handler.** Ending such a lifetime `ε` needs the
   remaining resource in `[ε]` ([TR] 6.65's end, 6.104), which internal cells are not. This is T1
   in its strong form: the continuation is confined to the scope its handler runs in.
3. **Local resumption still meets O3's step.** Suppose it is resumed where it was frozen. Between
   freeze and resume, the consumer may open lifetimes of its own, after the internal ones and
   below them. The resumed segment may then end an internal lifetime while a shorter one is open.
   That is exactly the step O3 names: [TR] 6.65's proof does not order the outside lifetimes
   relative to `α`.

So lifetime bounding gives case (E) in full. In case (I) it gives confinement, and O3 remains.

## 14.3 Internal borrows: capture rebasing

**The idea** (from the review input on #245, item 2). At a freeze, every internal lifetime is
ended *as ghost structure*. Each place an internal frame lent goes back into the frozen value as
an `own` cell. At a resume, the internal lifetimes are opened again **fresh**, below everything
live, and the places are lent again. The machine changes nothing:

- BoLo's terms carry no lifetime values (borrow-core's lifetime abstraction is `Λ.`, with no
  variable, e.g. `Core/CommonList.lean`);
- freeze and resume remain D3.6's capture and force.

**The shape of the frozen value.** The rebased relation of a frozen segment is the premise of
[TR] 6.65 (Mut Frame), stacked once per internal frame. Compare `ewpTS_M_frameU`'s premise,
`fresh (λα. ptoMutS ℓ α … ─⋆ wpG …)`, with BoLo's fresh-lifetime quantifier
`fresh P̂ ≜ ∃β. ∀α ⊏ β. [α] P̂(α)` ([TR] p. 6, row 18; `Paper/S5_Model/Definitions.lean`,
`fresh`). A frozen segment is a **suspended `withbor` callback**: it owns its source places, and
it is abstracted over the borrows a resume will create.

**Definition D14.4 (the rebased continuation relation).** For a segment `S` with internal frames
`f₁ … f_n` (outermost first), lending places `ℓ₁ … ℓ_n` at internal lifetime variables
`x₁ … x_n`:

    V°_c⟦K⟧(κ)(r)  ≜  ∃ r_e, r_o.  r = r_e ● r_o
                      ∧ r_e ∈ Res_c                               (the external footprint)
                      ∧ r_o = ●ᵢ (ℓᵢ ↦ own(vᵢ)) ● ρᵢ               (the places, owned, with their witnesses)
                      ∧ fresh(λα₁. … fresh(λα_n.
                            Relend_{α⃗}(r_o) ─⋆ V⟦K⟧_{δ[x⃗ ↦ α⃗]}(κ)(r_e ● Relend_{α⃗}(r_o))) …)

`Relend_{α⃗}` replaces each `ℓᵢ ↦ own(vᵢ) ● ρᵢ` by the cell that frame `fᵢ`'s start creates at
`αᵢ`: `mut` for 6.65, `imm` for 6.64, the reborrowed cell for 6.150. The resource `r` holds no
cell at an internal lifetime, so `κ`'s stratum is its external footprint.

**Lemma L14.4 (re-stratification of a stack segment). Open: O5.** Suppose the unary relation holds
of a segment `S` at its concrete internal lifetimes `α⃗`, with resource `r_S`, at a stop on its own
handler. Then `V°_c⟦K⟧(freeze S)(Freeze(r_S))`, where `c` is the meet of `S`'s external lifetimes
and `Freeze` ghost-ends the internal frames.

*What a proof needs.* Two ingredients, then the start steps of 6.64, 6.65 and 6.150 at the fresh
`α⃗'`:

1. **A transport lemma.** The relation is preserved when the internal lifetimes `α⃗` are moved to
   fresh `α⃗'`. The relation here means `𝒱`, `ewpTS`, `↭`, and the typed world `TW`/`Tagged` with
   its lifetime records. Three risks, none checked:
   - **No symmetry.** BoLo's lifetimes are `ℕᵒᵈ` (`Paper/S5_Model/Definitions.lean`, `Life`),
     which has no non-trivial order automorphism. So this cannot be a symmetry argument; it is an
     induction over every definition the relation reads.
   - **The successor.** [TR] p. 5 defines `↓α ≜ α + 1`. A uniform shift of the internal lifetimes
     commutes with `↓`, but it does not preserve an equation between an internal and an external
     lifetime such as `α_int = ↓α_ext`. I have not checked whether any definition the segment's
     relation reads relates two lifetimes that way.
   - **Precedent.** The nearest existing lemma is borrow-core's re-taking of [TR] 6.131's image
     at a new lifetime: `relRes`, `relabel_reb` (`Support/TypedWorld/Images.lean`), and
     `relabel_obs` (`Support/TypedWorld/RelationFacts.lean`). That is one cell's image at one
     lifetime. L14.4 needs every internal cell of a segment, at once.
2. **A ghost end of a suspended frame.** This is the step
   `mut(α, v, ρ, P) ↦ own(v) ● ρ` while the callback that holds `Mut α` is *suspended*. It is not
   6.65's end, which needs the callback finished and its leftover in `[α]`. Its justification is
   that no step reads `ℓ` while the segment is frozen, since the segment is a heap node (D3.2,
   L5.18). That justification is stated here, not derived.

I have not derived L14.4, and I have not verified that any obstruction to it is real.

**Lemma L14.5 (resume of a rebased continuation).** Given `V°_c⟦K⟧(κ)(r)`, `resume κ w` satisfies
`ewp` at the resumer's table, whenever its outer row is answering or abortive.

*Proof (proved here at the level of its steps; depends on L14.4 at the next freeze).*

1. [TR] 6.112 gives a `β` below every live lifetime. Instantiate each `fresh` of D14.4 at some
   `α'ᵢ ⊏ β`. Then `Relend_{α⃗'}` is the start of each frame `fᵢ`, at a lifetime below
   everything live.
2. Run the segment. Its frames are open only for a stretch with no suspension. At a return, end
   them by 6.65's (6.64's, 6.150's) end. At an abortive stop, use the LIFO frame lemmas
   (`ewpTS_*_frameU`, mechanised). At an in-place stop, use T9.2 (O2).
3. At a stop on its own handler, the segment is frozen again by L14.4. ∎

**Theorem T14.6 (O3 reduces to O5).** [TR] 6.65 lifted to `ewp` at a table with a suspending
instance (O3) holds if L14.4 holds and O2 holds.

*Proof (proved here at the level of the argument).*

- **At every stop on a suspending instance**, the frame's `α` is internal to the captured
  segment. L14.4 ghost-ends it, and L14.5 re-opens it fresh at the resume, below every lifetime
  opened in between.
- **So the frame is open only across stretches without a suspension.** On those, 6.65's proof
  applies as printed: at abortive stops via `ewpTS_M_frameU`, and at in-place stops via T9.2
  (O2). The step O3 names, outside lifetimes unordered relative to `α`, does not arise: no
  outside code runs while `α` is open.
- 6.64 and 6.66 alike. ∎

**Rebasing composes.** A frozen value holds no cell at an internal lifetime. So when it is itself
captured, for instance by the forwarding clause of T13.8 holding `k` across an outer suspension,
it is an owned value together with its external footprint. Some of that footprint may be at
lifetimes internal to the *outer* segment, and the outer freeze rebases those. η's typing at the
lift therefore needs nothing beyond L14.4.

## 14.4 The central lemma: a `Mut` cell holding a rebased continuation

**Definition D14.7 (continuation cell).** For a lifetime `γ` and a stratum `c ⊒ γ` (`ptoMut`'s
`α ⊑ b`),

    I_c(v)(r)    ≜  (v = inl () ∧ r = ∅)  ∨  (∃ κ. v = inr κ ∧ V°_c⟦K⟧(κ)(r))
    Cell(ℓ, γ, c) ≜  ℓ ↦ Mut γ I_c,       with Supported c I_c

`Supported c I_c` holds because `V°_c` puts the external footprint in `Res_c` and the places in
`own` cells. `c ⊒ γ` is the outlives check: the continuation's external borrows outlive the cell.

**Lemma L14.8 (closed under resume).** Let

    step(w) ≜ withswap ℓ (λv. case v of
                 inl _ ⇒ ret (inl (), done)
               | inr κ ⇒ resume κ w to r. case r of
                           done a         ⇒ ret (inl (), a)
                         | yielded (a, κ') ⇒ ret (inr κ', a))

Assume:

- `w`'s resource is in `Res_c` (here `w` is ground, so it is `∅`);
- every operation the resumed segment performs outside itself is answering (in place);
- the yield's handler is inside `κ` (a generator's handler is, being installed with its body).

Then `step(w)` is sound, and it leaves `Cell(ℓ, γ, c)` in place.

*Proof (proved here at the level of its steps; conditional on L14.4).*

1. **`withswap`'s compatibility** ([TR] 6.176, `withswap_compatX`, `Core/Compatibility.lean`).
   It opens the cell by Anti Frame (`wpTS_M_antiFrameX`). The callback owns the content `v`, with
   `I_c(v)`, and must hand back `v'` with `I_c(v')`.
2. **`inr κ`.** By L14.5, `resume κ w` runs with fresh internal lifetimes. It ends either
   - at `done a`: put back `inl ()`; or
   - at a stop on the generator's own handler, whose clause answers `yielded (a, κ')` with `κ'`
     the new freeze. By L14.4, `V°_{c'}(κ')`, where `c'` is the meet of `κ'`'s external lifetimes.
     These are `κ`'s and `w`'s, since nothing else enters a running segment (L14.2), so `c' ⊒ c`
     and `I_c(inr κ')`.
3. **The outer row.** At an answering operation the callback continues in place, inside the
   anti frame. ∎

*Why not abortive outer operations.* SPEC §19 gives `withswap` no unwinding form: "its callback
takes the payload by value, and an unwind would abandon it". An abort inside the resumed segment
would unwind the segment, running its destructors and consuming `κ`, and leave the cell with no
content satisfying `I_c`. The step that is missing is an unwinding form of `withswap` that writes
back `inl ()` once the payload's own destructors have run. It is not defined here. It is part of
O8.

**Lemma L14.9 (closed under drop).** Dropping the cell's owner runs
`case v of inl _ ⇒ () | inr κ ⇒ cancel κ`, and that finalises everything `κ` holds, exactly once.

*Proof (proved here at the level of its steps; conditional on L14.4).* `cancel κ` is a resume into
`raise` (SPEC §19, `cancel_compatC`). By L14.5's first step the internal frames restart fresh.
The LIFO frame lemmas (`ewpTS_I_frameU`, `ewpTS_M_frameU`, `ewpTS_M_antiFrameU`, mechanised) then
end them innermost first. The places return to their owners inside the segment, and those
owners' drop glue frees them (SPEC §12). The segment's `fin` frames free their resources (D4.5).
External borrows are forgotten (6.148, 6.149). ∎

**What the lemma yields.** Each item is conditional on L14.4 (O5) and on L14.8's hypothesis that
the resumed segment's outside operations are answering. A generator that may raise or await
across `next` needs O8.

| target | how | further condition |
|---|---|---|
| **generator objects** | `Gen ≜ Ref(1 ⊕ κ°)`, with `next ≜ step` an answering operation. The recursion moves into the heap, and the type is inductive: no `μ` under `U`, unlike `strm` (D1.6), and no positivity premise. | none beyond the two above |
| **capabilities held across `yield`** | an owned capability inside the segment is an `own` cell of `r_o` or `r_e` | across a **linear** yield, none. Across a **cancellable** yield (a generator that may be dropped), the capability needs a destructor, and §2's `cap` has none (D2.4, T5.2.2). A lend frame inside the segment needs one too, which [lend]'s `bound(ρ).req = lin` refuses today. This is #245's fourth seam (which effects destructors may perform), and it is a decision, not a lemma. |
| **task queues** | `Ref(List κ°)`, with `I_c` lifted pointwise by a separating list. `step` pops, resumes and pushes. | every task's external footprint in `Res_c` |
| **handler state** | the handler's state in a cell. The clause owns it while the body is suspended (`withswap`); the body has it lent while it runs. This is linear state in Møgelberg & Staton's sense, with the continuation as its user (*Linear usage of state*, LMCS 10(1:17), 2014 [via phase A]). | as for generators |
| **T1** | T14.10 | as above |

**Theorem T14.10 (T1 as the `withswap` discipline).** In a program built from L14.8 and L14.9, no
continuation is resumed while a lend it holds is out, and no borrow it holds is used after its
lifetime. No premise forbids this; it follows from three facts:

1. **Linearity.** A stored continuation is resumed only by a callback that owns it (`withswap`).
   While it runs, its cell's `Mut γ` borrow is held by `withswap`, so it cannot be resumed again
   from inside itself.
2. **Stratification.** It holds no borrow of its own cell: `I_c` is at stratum `c ⊒ γ`, and
   a cell at `γ` is not in `Res_c`, which admits only lifetimes `⊐ c`. So no Landin knot can be
   tied, as in TR §9.4 item 3.
3. **Rebasing.** Its internal borrows are re-created fresh at every resume (L14.5) and ended or
   ghost-ended before control leaves (L14.4). Its external borrows outlive `c ⊒ γ`, and the cell
   is reachable only within `γ`.

*Status.* Proved here at the level of this argument, conditional on L14.4 (O5) and on L14.8's
hypothesis (answering outside operations). Beyond that hypothesis is O8:

- **an abort** inside a resume needs an unwinding form of `withswap`;
- **a suspension** inside a resume holds the anti frame open across it. Anti Frame introduces no
  lifetime of its own, so O3's step does not arise, but I have not derived
  `ewpTS_M_antiFrameU` at a suspending table.

**#245's decisive test.** The test: "a continuation captures a borrow, escapes its handler, is
stored, and is later resumed or cancelled", by the three interfaces alone.

- **Case (E):** passes with an outlives premise (§14.2).
- **Case (I):** passes with L14.4. L14.4 is interface 2 ("continuations are values in the
  resource world") made precise for borrows. It speaks of frames, lifetimes and freezing together,
  so in the test's sense it *is* borrow/handler glue: one lemma's worth, against T1's typing rule.

## 14.5 Verdict: does the structure reduce the proof obligations of the lift?

Sizes are rough: **S** is about one compatibility lemma; **M** composes mechanised lemmas with
a few new steps; **L** touches every definition of the relation.

**The kernel lift, to pass #245's decisive test.**

| obligation | TR as it stands | with §§13–14 | size |
|---|---|---|---|
| redo every step that uses L4.1 (own fragment) at the full carrier | needed | needed, unchanged | reuse of borrow-core's `wpTS` lemmas |
| O2: the in-place half of T9.2, written out | needed | needed, unchanged (in-place tables do not suspend) | S |
| case (E): capture-outlives premise and `[]I` at a continuation | needed (§9.3 points at T2, #173) | needed, unchanged | 2 S |
| case (I): O3 | **open, no route** | **replaced** by L14.4 (O5), with a route: transport and ghost end (T14.6) | 1 L |
| ghost end and restart per lifetime-introducing frame (6.64, 6.65, 6.150; the rest derive from `withbor2`) | — | new | 3 S |
| T1 | a typing rule, or a theorem only at in-place and abortive tables (T9.2) | a theorem (T14.10), via the cell lemma, conditional on O5 | — |
| the cell lemma, L14.8 and L14.9 | — | new | 1 M |
| `withswap` across an abort or a suspension | — | new, open (O8); needed only when a resumed segment raises or suspends outside itself | ? |

**The laws.**

| item | TR as it stands | with §13 | size |
|---|---|---|---|
| β | T7.1 and T7.5 (mechanised) | T13.2: no new obligation | 0 |
| η | absent | T13.8(a), (c): one tree induction | 1 S |
| η at cancellable operations (forwarding a cancel) | absent | D13.7's frame: machine row, typing rule, L13.9, `Dtor.run` and `DR` flattening, cases of L6.2, L6.3, L6.5 | about 5 S |
| η at linear operations in general | — | open (O6) | — |
| interaction law | absent | T13.13 (special case); P13.14 (fails at cancellable); general open (O6) | 1 S |
| hiding, binary | absent | open (O7); no law needs it | — |
| tensor, instance parametricity, destructor form, contraction | proved (§7) | unchanged; no proof shortened (§13.6) | 0 |

**The verdict.**

1. **The `F ⊣ U` framing itself removes no obligation.** In the TR's tree semantics `F A` is
   already the free model, so the binary β is the existing H-op with `U`-β (T13.2, nothing new),
   and η is the uniqueness half of the same universal property. Instance parametricity and
   contraction come from generativity and independence, not from the three facts (§13.6). Read as
   a structure for the TR, the framing **adds a layer of vocabulary without removing work**.
2. **The framing yields two new laws, each with a sharp limit.**
   - η holds at linear and abortive operations, and at cancellable ones only with a frame that holds
     a continuation (D13.7). That frame is a new former, and it bears on #245's fourth seam.
   - The interaction law holds only at operations resumed exactly once (P13.14).

   These are useful findings, but they are additions, not reductions.
3. **Capture rebasing does reduce open work, independently of the framing.** It turns O3, which
   has no route, into one stated lemma (L14.4) with a route and an identified precedent
   (`relabel_reb`). It also makes T1 a theorem (T14.10). The cost is one large lemma, three small
   ones and one medium one, against one open problem and a typing rule. Counted as lemmas, the
   number goes up; counted as open problems with no route, it goes from one to none. The new
   opens O5 and O8 have stated steps.
4. **One missing construct recurs in three places.** O1 (ν/op), O6 (η at linear operations with
   `using` frames; the interaction law in general) and P13.9 all wait on a **binary relation that
   reads qualifiers**:
   - D6.2 relates destructor lists at every operation, but a moded program runs only those of
     weakenable ones;
   - D6.2 does not know a continuation is forced at most once.

   If that relation is built, it should be built once, for all three.

**Recommendation.**

- Do not restructure the TR around `F ⊣ U`.
- Keep capture rebasing, L14.4 and the cell lemma as the reserve route that #249 already names
  for case (I). §14.2 argues that lifetime bounding settles case (E) and leaves case (I) at O3.
- Add η and the interaction law to the TR's laws, with the limits proved here, if they are
  wanted.
- Take D13.7 up with the fourth-seam decision: which effects a destructor may perform, and
  whether a frame may own a continuation.

## 14.6 Open problems added

| | statement | where | the step that does not go through |
|---|---|---|---|
| O5 | L14.4, re-stratification of a stack segment | §14.3 | a transport of the relation along fresh internal lifetimes on `ℕᵒᵈ`, which has no automorphism (risk: `↓α = α + 1`), and the ghost end of a suspended frame |
| O6 | η at linear operations whose segment crosses a `using` frame; the interaction law at linear operations in general; both as `CtxEq_op` | P13.9, §13.5 | D6.2 relates destructor lists of operations that a moded program never cancels; `LR` fails, and `CtxEq_den` fails at unhandled operations (P13.9) |
| O7 | binary hiding (D13.11) | §13.4 | `VR` has no relational parameter for a state type, and worlds match cells by equal contents |
| O8 | the continuation cell when the resumed segment raises or suspends outside itself | L14.8, T14.10 | an abort: `withswap` has no unwinding form (SPEC §19), and one that writes back `inl ()` is not defined. A suspension: Anti Frame (`ewpTS_M_antiFrameU`) at a suspending table, not derived (6.66 opens no lifetime, so O3's step does not arise) |

O3 is not withdrawn: it stands, reduced to O5 and O2 by T14.6.

## 14.7 Sources and novelty

| key | reference | mark | used for |
|---|---|---|---|
| CFMM16 | Curien, Fiore & Munch-Maccagnoni, *A theory of effects and resources: adjunction models and polarised calculi*, POPL 2016, pp. 44–56, DOI 10.1145/2837614.2837652 | [verified via Crossref]; content recalled, general reading only | the framing (§13.1) |
| Lev05 | Levy, *Adjunction models for call-by-push-value with stacks*, Theory and Applications of Categories, DOI 10.70930/tac/e17sf9pc (earlier ENTCS 69, 2003, DOI 10.1016/s1571-0661(04)80568-1) | [verified via Crossref]; content recalled | stacks and thunks as the transposes (D13.1) |
| Lev99 | Levy, *Call-by-push-value: a subsuming paradigm*, TLCA 1999, LNCS 1581, DOI 10.1007/3-540-48959-2_17 | [verified via Crossref] | CBPV |
| KRU20 | Katsumata, Rivas & Uustalu, *Interaction laws of monads and comonads*, LICS 2020, DOI 10.1145/3373718.3394808 | [verified via Crossref]; content recalled | the interaction law (§13.5) |
| FKLP17 | Forster, Kammar, Lindley & Pretnar, *On the expressive power of user-defined effects: effect handlers, monadic reflection, delimited control*, PACMPL 1 (ICFP 2017), DOI 10.1145/3110257 | [verified via Crossref]; content recalled | the brief's vocabulary: reify and reflect (monadic reflection) beside handlers and delimited control |
| ADR09 | Ahmed, Dreyer & Rossberg, *State-dependent representation independence*, POPL 2009, DOI 10.1145/1480881.1480925 | [verified via Crossref]; content recalled | worlds with per-cell relations (O7) |
| HLPP07 | Hyland, Levy, Plotkin & Power, *Combining algebraic effects with continuations*, TCS, 2007, DOI 10.1016/j.tcs.2006.12.026 | [verified via Crossref]; content via #245 | the one-shot/multi-shot dichotomy (contraction, §13.6) |
| Has02 | Hasegawa, *Linearly used effects: monadic and CPS transformations into the linear lambda calculus*, LNCS, 2002, DOI 10.1007/3-540-45788-7_10 | [verified via Crossref]; content via #245 | the same |
| PP08, PP13, MS14, Sta13, CMD26 | as §12 | as §12 | tensor; handlers as folds; linear state; ν/op; destructors |
| [TR] | as §12 | 6.64–6.66, 6.104, 6.112, 6.131, 6.148, 6.149, 6.176, p. 5 (`Mut_α`, `↓α`), p. 6 (`fresh`) | §14 |

**New to us** (in the sense of §12.3: not found in the sources above and the #235 and #245
reports; not a claim of priority):

1. η at cancellable operations is not a term of §2, because forwarding a cancel needs a frame that
   owns a continuation (L13.5, P13.6, D13.7).
2. η at a fresh instance with renaming fails through `ieq` (P13.10). So generativity forces η to
   be stated at the same instance.
3. The interaction law needs exactly-once resumption, where ν/op needs at most once (P13.14).
4. O1, O6 and P13.9 share one missing construct: a binary relation that reads qualifiers.
5. A rebased continuation's relation is a stack of [TR] 6.65 premises under BoLo's
   fresh-lifetime quantifier (D14.4). With it, O3 reduces to O5 (T14.6).
6. T1 as three facts: `withswap`'s linearity, stratification, and rebasing (T14.10).

Capture rebasing and the continuation cell are the #245 review's. What is written here is their
statement against the TR's definitions, and the reduction of O3.

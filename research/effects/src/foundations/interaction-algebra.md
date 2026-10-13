# The interaction algebra (part 2 of 2): borrows and suspension

> **Status: draft for review. Not decided.** Nothing here holds until the tests in §6 pass.
> It builds on [part 1, the effects algebra](effects-algebra.md): §2 below cites part 1's laws
> instead of restating them.

This page states the borrow × effect interaction as **equations of the calculus**, and derives
what any semantics of those equations must be. The interface properties I1–I5 state what a
*given* relation must preserve; this page asks which equations the language owes, and lets the
relation follow.

## 1. Signature

Everything except one law below is already in the kernel.

- **Lends** are constants with a lifetime-polymorphic callback (SPEC §1, §9; `[TR]` 6.172, 6.175):

      withbor  : Ref A ⊸ (∀'c. Mut 'c A ⊸ C['c]) ⊸ … (Ref A ⊗ T)
      withload : Imm @a A ⊸ (∀'x. Imm 'x A' ⊸ C['x]) ⊸ …

  The place comes back in the result type (`Ref A ⊗ T`). **The return is already part of the
  lend's type.** Reborrow is `[TR]` 6.150. The callback's row is restricted to unwinding rows
  (`Row.Unwind`). That restriction is T1 at the constants.
- **Effects** (SPEC §19): `perform`, `raise`, `handle`, `M then x. N unwind D`, `κ = ⟨resume, cancel⟩`
  (linear or affine), frame deadness.

## 2. Equations already decided

- **BoLo's lend equations.** `withbor`/`withload` β (the callback runs and the place returns),
  framing, nesting, reborrow under its parent. ☐ *To be transcribed from `[TR]` as equations, not
  re-invented (OC5).*
- **Handler laws, algebraicity, abort:** `raise e to x. P = raise e`.
- **Finally:** `(raise e) then x. N unwind D = D (); raise e`. With frame deadness, a cancel
  unwinds the region innermost first.
- **An abort inside a lend already unwinds the lend.** SPEC §19 makes the borrow block an
  unwinding form, so the abortive case of the interaction is already decided.

## 3. The new content: two statements

**(C) A lend's callback frame is an evaluation frame that operations pass through.** For a
non-abortive `op` whose handler lies outside the lend:

    withbor p (Λ'c. λr. E[perform op v])  =  perform op v (y. withbor p (Λ'c. λr. E[y]))

Algebraicity extends through the lend: the operation commutes past the open lend, and the lend
together with the instantiated `'c` moves into the continuation. This *is* "a suspension holding
a lend". It amounts to lifting `Row.Unwind` from the constants.

**(R) The end of a lend is its finaliser.** The lend's frame is a `then … unwind` frame whose
finaliser hands the place back:

    cancel (λy. withbor p (Λ'c. λr. E[y]))  =  (finalise E;  end 'c;  ())

The "calculus of returns" is then the finally law applied to lends, with no new mechanism:
- **resume:** the callback runs on, and the return happens when it ends (lend β);
- **cancel:** the return happens during unwinding (finally plus frame deadness);
- **never:** impossible. `κ` is linear or affine, there is no `forget`, and dropping an affine
  `κ` is its cancel.

## 4. What follows (derived, not chosen)

1. **Exclusivity during suspension.** While `κ` holds the lend, `p` is unusable outside it. At
   Core level, linearity has already moved `p` into the region (an outside-owned place lent inside
   does not occur: BRIDGE.md, *Segment-shift check*, check 2). So (C) needs no side condition for
   this. ☐ *Verify against the reader object (OC2).*
2. **Parametricity in the lend's lifetime, under stated premises.** "No term observes where a
   lifetime sits" is **contingent**. Lifetimes are positions in the *dynamic nesting order*, and
   (C) changes a suspended region's lifetimes' position relative to the resumer's.
   - **Why it changes.** The region's lend `'c` was created *before* any lend `'d` the handler
     clause opens. If the clause resumes `κ` inside `'d`, `'c` must end before `'d`, so in the
     nesting order it now sits *above* `'d`. The move is order-preserving inside the segment, but
     it reorders the segment relative to the clause's lifetimes.
   - **What keeps that reordering unobservable.** It is unobservable only if no value relates the
     two groups of lifetimes. That rests on these premises, each a design fact that could be
     changed:
     - ☐ **PL1, operation types mention only lifetimes below the handler's cut** (SPEC §19:
       "operation types are closed in lifetimes"). Then no resume argument or operation payload
       carries a clause lifetime in, or a region lifetime out.
       - **Where this premise bites: lending iterators.** A generator that yields a borrow *of its
         own state* puts an internal lifetime in the `yield` payload, so the consumer holds a
         value at `'c` while the region is suspended. The order between `'c` and the consumer's
         lifetimes is then observable. This is Rust's `LendingIterator` problem, and it is a real
         program class: it must be either an explicit exclusion or a case the theory covers.
     - ☐ **PL2, lifetimes are erased.** No term compares lifetimes at run time; order is used only
       by typing (outlives, `⊑`).
     - ☐ **PL3, embeddings fix everything at or below the cut**, including `⊤`/static.
     - ☐ **PL4, freshness is relative only to lifetimes the code can name.** "Fresh = newest"
       (`[TR]` 6.108–6.112) must not be relied on against the resumer's unnamed lends.
   - **Under PL1–PL4, the equations of §2–§3 are invariant under the moves (C) makes.**
     Consequently:
   - **Any model of the theory is natural in the lifetime order.** It is a functor over finite
     orders and the morphisms (C) induces: order-preserving inside a segment, and free relative to
     lifetimes the segment cannot name. This is weaker than "all order-embeddings", and which of
     the two is right is OC3.
   - **Resume and placement are instantiations.** This is I2's binder reading, here a consequence
     of the theory.
3. **Why the relation we have cannot be the model of (C).** Core's relation interprets `∀'c`
   over positions in `ℕᵒᵈ` and observes adjacency (`coreAllAdjacent`, `coreAllNotNatural`). (C)
   moves an instantiated `'c` past a handler whose clause may open lends, which opens a gap. That
   is the machine-checked segment-shift failure. Core's relation validates BoLo's theory, where
   `'c` never leaves its callback while lends are opened around it. It cannot validate the theory
   extended by (C). The required change is derived: **`∀'c` must be interpreted parametrically**,
   as relations invariant under order-embeddings, à la Reynolds.
4. **Conservativity.** For programs in which no lend spans a stop (every program today, by
   `Row.Unwind`), the parametric interpretation and today's interpretation must make the same
   observations (adequacy). The borrow calculus's guarantees then carry over unchanged.

## 5. Open choices

- ☐ **OC1, which operations (C) covers.** All non-abortive operations, or a declared class?
  Answering operations already return in place.
- ☐ **OC2, `mut` against `imm`.** Is (C) at a `mut` lend different? While suspended, the place is
  frozen in `κ`.
- ☐ **OC3, the morphisms.** All order-embeddings, or only those fixing the handler's cut?
- ☐ **OC4, construction.** Either replace the `∀` clause by a parametric one, or build the
  parametric relation as a layer and prove the observational equivalence of §4.4.
- ☐ **OC5.** Transcribe BoLo's lend equations from `[TR]`.

## 6. What would make it hold (tests, in order)

1. **The equations in Lean:** (C), (R) and the BoLo lend equations, stated as contextual
   equivalences or as the laws the relation must validate.
2. **The parametric interpretation** of `∀'c`, and a proof that it validates (C) and (R), at every
   type and so at every nesting depth.
3. **Conservativity** (§4.4): same observations as Core on `Row.Unwind` programs; `fundamentalC`
   and adequacy unchanged.
4. **Programs, typed and run:**
   - the reader object with `Log` handled outside the counter's lend;
   - `gen-self-borrow`, `for-lend-resumes`;
   - `async-borrow`;
   - a callback that suspends inside a callback inside a lend (nesting).

**Kill criterion:** if a program needs a term former or an equation outside §1–§3, the theory is
incomplete, and that program shows what is missing.

## Literature

- Oles; Reynolds, functor categories for Algol's local variables.
- O'Hearn and Tennent, *Parametricity and Local Variables* (1995).
- Reynolds, relational parametricity.
- Pitts and Stark, the ν-calculus.
- Ahmed, Dreyer and Rossberg, Kripke logical relations with world morphisms.
- Plotkin and Pretnar, handler laws.
- Leijen, finalisation in effect handlers.

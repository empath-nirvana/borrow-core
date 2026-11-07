# Roadmap

Where the work goes next, coarsely. Each item points at the issue that holds its plan; the issue is
the source of truth.

## Where the kernel is

Borrows can be held across a suspension. The kernel proves it at the rule level over the chain
relation with Kripke stops (#839): `imm` and `mut` lends, reborrows, field and slice borrows held
across a suspending operation and then resumed or cancelled, with cleanup that may perform effects
(the suspending lends at `Row.Suspend`). The headline is plain adequacy,
`goal791N : HandlerLawN → Goal791N`, for closed programs whose handlers are inside the program
(SPEC §62, `docs/new-core/chain-interpretation.md`).

`HandlerLawN` is a named assertion, trusted on the same footing as `PinLaw`: the compatibility of
`effHandleV`, `effHandleVB` and `reify`, the three rules with no compatibility lemma yet. It is a
hypothesis of the theorem, never an axiom (decision 75).

The checker and the compilers have not caught up yet. Until they do, the checker enforces T1
(SPEC §19): no borrow is held across a suspension handled outside it, R1 aside.

## Next

1. **Catch-up to the new kernel (#843).** In order:
   - the surface: the checker and elaborator emit the suspending lends, effectful cleanup on
     cancel, and handlers inside the program;
   - Backend2 becomes the default compiler, then the old backend is retired;
   - the corpus: programs that exercise the new rules.
2. **Borrowed payloads to handlers (#844).** A borrow passed in an operation's payload, lent to the
   handler for the duration of the stop. Tier 1, outer borrows, comes first; Tier 2, a callback's
   own borrow such as `read(sock, &mut buf)` across `await`, goes together with cross-task lends
   (#821).
3. **The trusted base (#838, #840).** Shrink or discharge `HandlerLawN` (#838), and the follow-ups
   from #839's review (#840).

## North star

A Kubernetes operator written in the language (#67). Before the operator, a JSON parser runs as a
corpus program (#65, #783). Then files (#769), networking (#597), and HTTP with the operator end
to end (#600).

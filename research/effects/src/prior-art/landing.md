# How other languages landed effects × ownership: synthesis

**Sources.** Three surveys, written 2026-10-12, each with every claim tagged
[read]/[repo]/[unverified]:
- [landing-systems.md](landing-systems.md): Rust, Swift, Hylo, Mojo, Vale/Valen, Austral, Pony,
  Verona, Cyclone;
- [landing-effects.md](landing-effects.md): OCaml 5/OxCaml, Koka, Effekt, Scala, Flix,
  Unison/Frank/Links, Lexa, WasmFX, Roc, the theory papers;
- [landing-formal.md](landing-formal.md): Hazel, RustBelt and its family, Kripke and nominal
  models, regions, loan-set models, Granule.

This page draws conclusions for us; the three pages carry the detail and citations.

## 1. Where we stand against the field

No surveyed system has any of these:
- a statically **linear (no-drop) continuation together with a cancel**;
- a cancel that **hands back an owned value** (our K3);
- a **lifetime bound on a stored continuation**;
- **static checking of a suspension that holds a borrow** (tier 2);
- a mechanised model of lifetime-indexed borrows live across a resumable suspension. This is a
  search result, not a theorem.

Lending across a suspension shipped only where the resumer holds the suspension exclusively for
the lend's duration:
- Swift's `_read`/`_modify` accessors (SE-0474);
- Rust's async closures (`AsyncFnMut`);
- Hylo's projections.

**So tier 1 is already at or past the frontier on several axes, and tier 2 is beyond it.** The
literature will not settle our remaining questions; our proofs have to.

## 2. Negative results that constrain decisions we have made or will make

| # | result | source | bears on |
|---|---|---|---|
| N1 | Shared ownership with cycles makes leaking safe; any guarantee relying on a destructor running is then unsound | RFC 1066, Leakpocalypse | **explicit `Rc`/`Arc` (deferred).** Adding cyclic `Rc` would break the guarantees linearity gives us (forced return, scoped tasks). Decide `Rc`'s rules with this in hand. |
| N2 | Scoped borrowing children need an un-leakable scope; otherwise at most two of concurrency, parallelism and borrowing | boats, *Scoped Task Trilemma* | `async-borrow`, threads. Swift escapes it: async frames are not droppable, cancellation is cooperative, and scope exit awaits children. **Our linear continuations are the same ingredient.** |
| N3 | Linear types conflict with unwinding: an exception either leaks or needs per-frame obligations | Gankra 2017; Austral aborts instead | our answer is in place: values without a destructor may not cross an abort (`effect-abort-live`), and finalisers run. Keep it. |
| N4 | Must-use types infect generic code: every generic drop needs a bound | Gankra 2017 | generics: drop glue needs a destructor bound on `T`. Check our generic story states this. |
| N5 | Async destructors cannot be guaranteed by a drop hook | boats 2024 | our finalisers may perform operations, so they are "async drop", and linearity guarantees they run. **But a finaliser that suspends is not lowered yet** (§27, M2c fallback). |
| N6 | Cancel-as-drop at every suspension makes many operations cancellation-unsafe | Tokio `select!` | applies to us too. Our cancel happens only at stops, with finalisers, but partial-effect safety is a library concern to document. |
| N7 | A suspended accessor should **resume, not unwind**, when the caller throws; only the caller can restore the lent value's invariants | Swift SE-0474 (earlier design reversed) | tier 2 lending: our "cancel unwinds the region" may be the wrong default when a consumer aborts while holding a lent value. |
| N8 | Multi-shot breaks linearity, and one-shot is not enough without a condition on what a continuation captures | Tang et al. POPL 2024; Affect POPL 2025 | covered by our capture cell and independence rule. Affect leaves linear + `discontinue` as future work; that is our design. |
| N9 | Rows make linearity tracking coarse | Tang et al. | visible already: E5 and E2d need "no `unr` operation" side conditions. |
| N10 | Dynamic handler lookup gives accidental handling | Zhang–Myers; Biernacki et al. | solved by our static per-site names (E6). |
| N11 | Finalisation must be deep; a finaliser must not run under its own handler | Leijen 2018 | matches our frame deadness and finaliser-error decisions, reached independently. |
| N12 | One-shot continuations plus higher-order state encode `call/cc`, so stack-discipline reasoning fails | Dreyer–Neis–Birkedal ICFP'10/JFP'12 | **tier 1:** our soundness is machine-checked, so not at risk. But any *law* or reasoning principle that assumes well-bracketing (P14 conservativity) must be checked against stored affine continuations. |
| N13 | Well-bracketing for handlers is an open conjecture | Timany–Guéneau–Birkedal POPL 2024 | the same point as N12. |
| N14 | Higher-rank effect polymorphism inference is research; Koka is rank-1 | Balik et al. 2025; Koka | OA4: rank-1 rows are the standard. Go beyond only if a program demands it. |
| N15 | `(ℕ,<)` has only the identity automorphism, so equivariance over it is vacuous; well-behaved ordered names use `(ℚ,<)` | Bojańczyk–Klin–Lasota LMCS 2014 | tier 2: our `coreAllAdjacent` is this phenomenon. The carrier is not settled; see §4. |
| N16 | Effect-generic over a fixed keyword set multiplies variants (96 for five effects) | Rust effects initiative | confirms user-defined effects with rows over keyword generics. |
| N17 | Static exclusivity does not reach escaping closures, globals or class references; Swift checks those dynamically | SE-0176 | stored callbacks (item 2): R6 forbids stored callbacks capturing borrows, which is why we need no dynamic check. Keep it. |

## 3. What this changes for landing tier 1

- **Add before the Core landing inventory:** state which tier-1 laws, if any, rely on
  well-bracketing, and check each against a stored affine continuation (N12, N13).
- **Record as design facts in SPEC:** N3 (no destructorless value across an abort), N5 (finalisers
  run, guaranteed by linearity), N10 (static names), N11 (deep finalisation). Each is a place we
  are deliberately different from Rust or Koka.
- **Flag for future decisions:** N1 before any `Rc`; N4 in generics; N6 as library guidance.
- **Items 1–2:** rank-1 rows are the field's norm (N14). R6's ban on borrow-capturing stored
  callbacks matches the static half of Swift's split (N17).

## 4. Leads for a tier-2 restart (not proposals)

- **Position-free borrows.** Every model that allows resumption gives up lifetime positions:
  tokens, prophecies, ownership, named regions, or loan sets. Our lifetime carrier is **not
  settled** (only the guarantees are).
  - A dense carrier (N15) would make adjacency undefinable, but our construction recurses down
    `⊏`, which is well-founded only on ℕ-like carriers.
  - Loan sets / invalidation (Oxide, Polonius, LLBC) are position-free without step-indexing, but
    their proofs are on paper only, with no closures or async.
- **Invalidation at the cut.** Borrows internal to a suspended region cannot be touched
  (linearity moved the place in), so the check is about the model, not the program. Borrows that
  cross in payloads (lending iterators) get a real rule: resuming invalidates outstanding views.
  This matches the shipped "resumer holds it exclusively" pattern.
- **Scoped tasks.** Swift's escape from the trilemma (N2) uses exactly the property our linear
  continuations have.
- **Cancel or resume when a consumer aborts (N7).** This must be decided for lending.

See [tier2-status.md](../tier2-status.md).

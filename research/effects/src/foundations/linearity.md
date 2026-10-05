# Linearity, not affinity

The literature mostly assumes affine values with silent weakening, as in Rust's `mem::forget`. Many of its hardest problems come from that:
- leaking a continuation breaks scoped threads and `Pin`;
- the interception policy for a drop has to be chosen;
- exactly-once finalisation is conjectured, not proved (Koka), or left as future work (Affect).

BoLo is linear: adequacy ends with empty memory. In our kernel, discarding a continuation is an explicit cancel, because an affine continuation owes `cancelOwed`. So:
- there is no `forget`;
- a drop is a cancel, with the semantics SPEC §19 defines;
- exactly-once finalisation is a theorem shape (P5).

**What linearity does not fix:** lifetimes (P9), exclusivity (P10), and lends spanning a suspension (P4). Multi-shot is ignored.

**The cost:** every continuation must be consumed. The elaborator inserts cancels, the way drop glue is inserted.

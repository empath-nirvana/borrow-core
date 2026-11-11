# Pipes on nested wires: the design and its bridge to the kernel's handler laws (#1103)

Theory-foreman, 2026-11-11. On paper. The kernel facts are cited by the Lean names kernel-foreman gave (H1–H14 in its answers). User decisions:
- "I don't actually care about the order." Pipes take the kernel's natural behaviour under nesting: ownership order and the kernel's error rules.
- "We should not be redoing stuff in the elaborator that the kernel already does."
- "I approve the pipe plan."

This document supersedes `assembly-n.md` for pipes.

## 5. The design: a chain is nested binary wires, built from one library function

**N2 or N4?** kernel-foreman checked three ways for a wire to hold its upstream (H12):
- **(a), a parameterised deep handler**, types only with `unwind close up` at the handle and at every resume, and cannot take a `Div` stage.
- **(b), the upstream in a cell**, does not type: it is a lend across the stage's suspensions (T1).
- **(c), per-observation stepping in an `unfold` loop**, is kernel-natural and types today. It is exactly L1's own two-stage `conn_step` (core-pipe-connector.bc ~226–269, "unconditional", goldens at live 0).

So the wire is **(c), written once as a row-generic library function**, and a chain is **nested applications of it**. N4 (stages holding their upstream as a value) would need the upstream threaded through the stage body: a linear rebinding at every `next`, which is the elaborator threading we are avoiding. Or it would need it lent, which is (b) and T1. So N4 is not taken. `stop()` stays an operation, handled by the wire.

**The wire, schematically.** Kernel-foreman to co-sign. The full types are L1's, with one stage in place of `n`.
```
-- Up    = U (pull_Σ A K R)   : the stored upstream; .1 observes (item, end or skip), .2 closes
-- St    = Ready(Loop_s) | AtNext(κ) | AtYield(κ) | Ended    : the stage, stored per observation (Part A)
-- Out   = U (pull_Σ B K' 1)  : the wire is itself a stored generator, so it can be the next wire's Up
pull_into : Up ⊸ Loop_s ⊸ F Out
pull_into(up, s) = return (unfold wire_step (up, Ready s, none))

wire_step (up, st, inp) = <
  OBS:                                          -- one observation of the composite
    e <- step(st, inp) unwind close(up);        -- the stage's turn; a raise or cancel in it closes the upstream
    case e of
      Next κ      -> o <- observe(up) unwind cancel(κ);       -- the upstream's turn; a raise or cancel closes the stage
                     case o of item(a, up') -> again (up', AtNext κ, inl a)
                             | end(k)       -> again (up_ended, AtNext κ, inr k)
                             | skip(up')    -> skip (up', AtNext κ, none)
      Yield(b, κ) -> return item(b, (up, AtYield κ, ()))     -- the stage's yield is this generator's item
      Return r    -> close(up); return end(r)
      Stop κ      -> close(up) then _. again (up_ended, AtYield κ, inr ())   unwind κ.2 ()   -- H13's shape
  ,
  CLOSE:                                        -- the composite closed from downstream
    x <- cancel(st) unwind close(up); close(up)  -- the stage first, then its upstream
>
```
- **A chain** `s₀ >| s₁ >| … >| s_{n−1}` elaborates to `pull_into(… pull_into(pull_into(gen s₀, s₁), s₂) …, s_{n−1})`. When the last stage is a sink, the result is run to its end.
- **`|>`** elaborates to the same term. P1 Lemma M, which says the two operators give one trace (§75 "Demand and the operators"), then holds by construction. The *push* fast path for a stateless, tail-resumptive stage is §15's existing `for`-as-clause form, related by `last_resume_direct`/`last_cancel_direct`/`last_perform_direct` (T-B1/T-B1′/T-B2, H2).
- **`connect`** is the outermost wire returning `(r, up)` instead of `close(up); end(r)`. **`rest`** *is* `up`.
- **Outer operations pass straight through.** There is no forwarding, renaming or `close_all`, *if* H14 below holds.

**What the elaborator emits:** the nesting above plus sugar. Every one of L1's generated pieces is gone: the state tuple, the frame lists, the shared frames, forwarding renames, `stop()` reify and re-raise, and the per-chain glue. What remains:
- Part A's storing of a stage per observation, which is general and not pipe-specific;
- §15's push/pull test.

**User-visible changes against §75 as drafted.** These are stated so the user and docs can see them; per the coordinator, none needs a decision.
1. **Order:** ownership order (§1 table).
2. **Errors.** On a raise path and on an early stop (`run`'s close is code), the latest escaping cleanup error wins (H6: a finaliser can't see the pending error). Only when an outside cancel triggers the cleanup does the first error within that one cancel win (H5).
3. **`stop()`.** If the upstream's cleanup raises during `stop()`, the stage is *cancelled*, not unwound, so a handler the stage writes around `stop()` does **not** catch that error. It propagates past the stage, and the stage's own cleanup error, if any, supersedes it (H13). The order is still upstream, stage, downstream (`123`).

## 6. The bridge: each pipe law from kernel handler facts

Every law below is a **single-run** statement: the order in which cleanups fire, and which error emerges, in one run of the nested term. None compares two programs, except where marked.

**The per-wire lemma (W).** It comes from H1, H5, H4 and H13 typing. For one wire with a stored upstream `up` and a stage `s`, from any configuration:
- **(W-raise)** a raise escaping `s`'s turn runs `s`'s frames innermost-first, then `close(up)`, then escapes the wire. The source of each fact:
  - `step(st) unwind close(up)`;
  - `unwind_prefix`, EffCancelRuns:1777;
  - supersede, `supersede_prefix`.
- **(W-raise-up)** a raise escaping `up`'s observation runs `up`'s own (by induction), then `cancel(κ_s)`, then escapes. This uses `cancel_prefix` (:1798) for the cancel of κ_s.
- **(W-close)** CLOSE runs `cancel(st)`, then `close(up)` even if the former raises. This uses `cancel_prefix` and `unwind_prefix`.
- **(W-stop)** a `Stop` runs `close(up)`. If that raises, it then runs `cancel(κ_s)` and escapes (H13). Otherwise it resumes κ_s with `inr ()` (`catch_step`, `kappaC_resume`, H1).

**Laws by induction over the nesting depth, from W:**

| Law (ownership order, kernel errors) | Statement | Derivation |
|---|---|---|
| **S: the last stage returns early** | stages n−2, …, 0 close downstream-first. If two cleanups raise, the latest wins: CLOSE is code, not a machine cancel (kernel-foreman, batch 3) | The outer wire's `Return` gives `close(up)`, which is CLOSE of the next wire inward (W-close), and so on. Downstream-first holds because CLOSE cancels the stage before its upstream. |
| **R: a raise at stage i** | i's frames; then i−1, …, 0; then i+1, …, n−1. The error is the latest escaping one | W-raise at wire i (i, then CLOSE inward, giving i−1…0 by S). Then at each enclosing wire j > i, W-raise-up runs `cancel(κ_j)` and escapes, giving i+1, …, n−1. Supersede at each frame gives "latest". |
| **X: an outside cancel at an operation of stage i** | the same order. The error is the first within the cancel | One cancel through the same frames: `cancel_prefix` (fire, pend by `[cfin-cancel]`, keep the first, re-raise at the canceller). H7 covers a cancel arriving inside a running cleanup (absorbed). |
| **`stop()` by stage i** | i−1, …, 0 close downstream-first, then i resumes with `K = 1`. If a cleanup raised: i is cancelled, then i+1, …, n−1 | W-stop, then S inward, then R's outward part |
| **`rest`** | `close(rest)` closes the remaining stages downstream-first | It is S applied to `up` |
| **Early stop with effectful cleanup** | the same orders, with a cleanup's operations reaching outer handlers | **Gap G1.** H4 and H5 assume abortive-only finaliser rows (`FinRow`/`FinAloneAt`), and K-b's effectful `d` is outside them too (H11) |
| **A: associativity** | one nesting per chain | **No proof obligation:** §70's normal form emits one term per chain, so no second bracketing exists to compare. (Under ownership the bracketing is plausibly irrelevant anyway, §1, but the normal form makes the question moot.) |
| **Lemma M: `\|>` and `>|`** | one trace | **By construction**, since both emit `pull_into`. The push fast path is related by T-B1/T-B1′/T-B2, which exist (H2) |
| **Identity laws** (`s >| id ≈ s`) | equal traces for two programs | **Gap G3 (two-run).** No program's behaviour depends on these. |

**The gaps (candidate kernel lemmas):**

| Gap | What is missing | Needs a two-run relation? | Estimate |
|---|---|---|---|
| **G1: order with effectful finalisers** (kernel-foreman: ~0.6–1.2k) | `unwind_prefix`/`cancel_prefix` and their complete-run forms stated for finalisers that perform operations answered outside (`Trace`, `Log`, I/O), as K-b's `d` does. kernel-foreman calls this "a small kernel lemma unit" (H11) | no | ~0.5–1.5k Lean [kernel-foreman to size] |
| **G2: unwinding through handler frames** (kernel-foreman: ~0.4–0.9k) | H4's complete-run form assumes no handler frames. The wire's raise passes through Part A's storing handler, so the order lemma is needed across `catch_fwd` | no | ~0.3–1k [kernel-foreman to size] |
| **G3: identity laws, and any trace equality between two programs** | there is no outcome or trace notion and no allocation agreement (H10, A2): "a new kernel unit" | **yes** | the 2026-10 N2 figure was ~1.5–3k. **Not needed** for the order and error laws |
| **H14 (open question): cancel-row precision** | see below | no | depends on the answer |

**H14, which decides forwarding. kernel-foreman confirmed it is real, in both directions:** a stage that shares a capturable operation with its downstream (`kappaFinSelf`, SPEC ≈5758) or with its upstream (via `step(st) unwind close(up)`) is refused. kernel-foreman's order of routes:
1. type the wire's per-observation handler as `[handle-last]`, where κ's cancel row is already precise (being checked; it may need a storing variant);
2. the restriction "no two adjacent stages share a capturable operation";
3. per-wire forwarding.

A precise `cancelTy` in general would be a rule change: about 1–2.5k lines over ~50 use sites, not spiked.

The original analysis follows. `cancelTy` types a stored stage's cancel as performing its whole row (rev 2.4). In the nesting, stage i's operations run under the enclosing wire's `observe(up) unwind cancel(κ_{i+1})`. So if stage i+1 (downstream) performs the same capturable operation `o`, then `o`'s cancel row must contain `cancel(κ_{i+1})`'s row, which contains `o`, and only `⊤` satisfies that. Today this would refuse, for example, two stages that both perform the same network operation.
- **Either** `cancelTy` can be made precise (a κ's cancel performs only its finalisers' rows), which would be a kernel lemma;
- **or** the restriction stands ("no two stages perform the same capturable operation") until it can;
- **or** forwarding comes back in a small, per-wire form.

[Question to kernel-foreman.]

**Unused kernel facts:** H3 (handling as a fold) is not needed, because the laws are stated over configurations ("when stage i raises, the frames fire in this order"), not as trace equality against a tree model.

## 9. Final (2026-11-11): H14 settled, the term for checking, and the hand-offs

**H14b (kernel-foreman).** The `[handle-last]` route is closed. `effHandleL` types only clauses it writes itself, where κ never becomes a value. The wire's storing clauses are outside it, so Part A's observation is `effHandleV`, with κ's cancel at `cancelTy Σ F = F ⊕ Σ`.
- **The default now: the restriction.** "No two adjacent stages share a capturable operation." It is refused by the existing message (`corpus/reject/fin-cancel-capturing.bc`, SPEC ≈5758).
- **The kernel unit that would lift it (needs a go from the coordinator and the user):** an n-free refinement of `cancelTy`. When the finalisers in κ perform no operation of the handler's own name, κ's cancel performs only their rows.
  - Then only a stage whose *finalisers* perform `o` would conflict.
  - It is a definition change: `cancelTy` gains `n`, and `kTy`/`clausesTy` restate.
  - It needs one new lemma: an n-free cancel never enters `hnd n`'s clauses.
  - Estimate: 1–2.5k lines, unspiked (a day's spike would firm it up).
- **Forwarding does not come back.**

**The goldens, re-derived** for three stages (cleanups: source 1, middle 2, sink 3), from §6:

| # | Case | Order | Reported error |
|---|---|---|---|
| 1 | `run`: the sink returns early | `21` (the sink has returned; CLOSE cancels the middle, then the source). With the sink's own cleanup, `321` | — |
| 2 | the middle calls `stop()` | `123` | — |
| 3 | raise at the source | `123` | the latest escaping |
| 4 | raise at the middle | `213` | the latest escaping |
| 5 | raise at the sink | `321` | the latest escaping |
| 6 | outside cancel at an operation of the middle | `213` | the first within the cancel |
| 7 | the sink raises; the middle's and the source's cleanups raise | `321` | **the source's error**: CLOSE's `close(src)` supersedes `cancel(mid)`'s error, and supersedes the sink's own |

**The term for kernel-foreman's `bcc check`** is §5's wire, with H13's Stop arm and CLOSE as `cancel(st) then x. close(up) unwind close(up)`. Its full types are L1's two-stage `conn_step` types with `Up` in place of stage 0's state. Kernel-foreman checks the core-text version against `effHandleV` with storing clauses.

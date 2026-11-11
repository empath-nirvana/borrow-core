# Pipes on nested wires: the design and its bridge to the kernel's handler laws (#1103)

Theory, 2026-11-11. This is a paper argument. It supersedes `assembly-n.md` for pipes. SPEC §75 Part B is the normative text; this document explains why that text holds.

**Decisions** (user, 2026-11-11):
- "I don't actually care about the order." Pipes take the kernel's natural behaviour under nesting.
- "We should not be redoing stuff in the elaborator that the kernel already does."
- "I approve the pipe plan."

## 1. The wire

A **wire** is one library function, `pull_into(up, s)`. It is row- and site-generic (§76).
- `up : U (pull_Σ A K R)` is the stored upstream: observation `.1` gives an item, the end, or a skip, and `.2` closes it.
- `s` is a stage, stepped one observation at a time by §75 Part A's per-observation handling. The wire's clauses for `Stream.next`, `Stream.stop` and the stage's `Yield` are *storing* clauses: each answers with the stage's continuation κ (the rest of one turn) held in a value.
- The wire is itself a stored generator, `U (pull_Σ B K' 1)`, so it is the upstream of the next wire.

```
pull_into(up, s) = return (unfold wire_step (up, Ready s, none))

wire_step (up, st, inp) = <
  OBS:
    e <- step(st, inp) unwind close(up);
    case e of
      Next κ      -> o <- observe(up) unwind cancel(κ);
                     case o of item(a, up') -> again (up', AtNext κ, inl a)
                             | end(k)       -> again (up_ended, AtNext κ, inr k)
                             | skip(up')    -> skip (up', AtNext κ, none)
      Yield(b, κ) -> return item(b, (up, AtYield κ, ()))
      Return r    -> close(up); return end(r)
      Stop κ      -> close(up) then _. again (up_ended, AtYield κ, inr ())   unwind κ.2 ()
  ,
  CLOSE:
    cancel(st) then _. close(up) unwind close(up)
>
```

- **A chain** `s₀ ∘ s₁ ∘ … ∘ s_{n−1}` (with `∘` either `|>` or `>|`) elaborates to `pull_into(… pull_into(gen s₀, s₁) …, s_{n−1})`.
- **`connect`** is the outermost wire answering `(r, up)` instead of closing `up`. `rest` is that `up`.
- **Outer operations** pass straight through, with no forwarding.
- **This is the two-stage instance of L1's connector**, `conn_step` in `corpus/core-pipe-connector.bc`, made generic. It is the kernel-natural way to hold a linear upstream across a stage's run. The alternatives do not type with the upstream consumed on every exit:
  - a parameterised deep handler cannot take a `Div` stage;
  - a cell lent to the clauses is a lend held across the stage's suspensions (§19's T1).

## 2. Order and errors

A stage owns its upstream. For three stages (cleanups: source 1, middle 2, sink 3):

| # | Case | Order | Reported error |
|---|---|---|---|
| 1 | the sink returns early (its own cleanup, then `run` closes the rest) | `321` | the latest |
| 2 | the middle calls `stop()` | `123` | — |
| 3 | raise at the source | `123` | the latest |
| 4 | raise at the middle | `213` | the latest |
| 5 | raise at the sink | `321` | the latest |
| 6 | outside cancel at an operation of the middle | `213` | the first within the cancel |
| 7 | the sink raises, and the middle's and the source's cleanups raise | `321` | the source's |

**In general:**
- A raise or an outside cancel at stage i runs i's own unwinding, then i−1, …, 0 (its upstream, downstream-first), then i+1, …, n−1.
- On a raise, and whenever a chain is closed by code (`run`, `close`, CLOSE), each frame's escaping cleanup error supersedes the pending one, so the latest is reported. A finaliser cannot see the pending error (§27).
- Only when an outside cancel triggers the cleanup is the first error within that cancel kept, and re-raised at the canceller (§19 *Cancels*, `[cfin-raise]`, `[cancel-raise]`).
- A cancel arriving while a cleanup runs is absorbed (`[cfin-cancel]`).

**`stop()`:** if the upstream's cleanup raises, the stage is cancelled, not unwound. A handler the stage writes around `stop()` does not catch the error. If the stage's own cleanup raises, that error supersedes.

## 3. The bridge

**The kernel facts used** (Lean names in Core):
- **One handler step:** `Head.hop`, `catch_step`, `kappaC_resume`, `kappa_resume_steps`.
- **The unwind order:** `unwind_prefix`, with complete-run form `UnwindRun`/`unwindOrder_at`. Finalisers fire innermost first, and an escaping raise supersedes (`supersede_prefix`).
- **The cancel trace:** `cancel_prefix`, with complete-run form `CancelRun`/`cancelOrder_at`. Finalisers fire, a cancel arriving in one is pended (`Head.cfcancel`), the first error is kept, and the canceller gets `()` or a re-raise.
- **Linearity of a stored κ:** `kTy_cancel_consumable_iff`. The clause must cancel κ itself; nothing cancels it implicitly.
- **The push fast path:** `last_resume_direct`, `last_cancel_direct`, `last_perform_direct` (§51's erasure laws).

**The per-wire lemma (W).** For one wire with upstream `up` and stage `s`:
- **(W-raise)** A raise escaping `s`'s turn runs `s`'s frames innermost-first, then `close(up)`, then escapes the wire. Uses `unwind_prefix` and `supersede_prefix`.
- **(W-raise-up)** A raise escaping `up`'s observation runs `up`'s own cleanup, then `cancel(κ_s)`, then escapes. Uses `cancel_prefix` for κ_s.
- **(W-close)** CLOSE runs `cancel(st)`, then `close(up)` even if the former raised. If both raise, `close(up)`'s error is reported.
- **(W-stop)** `Stop` runs `close(up)`. If that raises, it runs `cancel(κ_s)` and escapes; otherwise it resumes κ_s with `inr ()`.

**The laws, by induction over the nesting depth:**

| Law | Derivation |
|---|---|
| Early return (row 1) | The outer `Return` gives `close(up)`, which is the next wire's CLOSE (W-close), and so on inward. CLOSE cancels a stage before its upstream, so the order is downstream-first |
| Raise at stage i (rows 3–5, 7) | W-raise at wire i gives i, then i−1, …, 0 by the early-return case. W-raise-up at each enclosing wire gives i+1, …, n−1. The latest error is reported, by supersede |
| Outside cancel (row 6) | One cancel through the same frames (`cancel_prefix`). The first error is kept |
| `stop()` (row 2) | W-stop, then the early-return case inward, then the raise case outward |
| `rest` | `close(rest)` is the early-return case applied to `up` |
| One normal form (P1 Thm A) | By §70's normal form: one term per chain |
| `\|>` and `>|` agree (P1 Lemma M) | Both emit `pull_into`. The push fast path is related by §51's erasure laws |

Every law is a **single-run** statement: the order of cleanups and the error in one run. No law compares two programs. Identity laws such as `s >| id ≈ s` would, and they are not claimed.

## 4. The cancel-row condition (the adjacent-stage restriction)

- A stored stage's cancel is typed as performing the stage's whole row (`cancelTy Σ F = F ⊕ Σ`).
- In the nesting, a stage's operations run under `observe(up) unwind cancel(κ_{i+1})`, and under its own `step(st) unwind close(up)`. So if two adjacent stages share a capturable operation `o`, then `o`'s cancel row must contain itself, which only `⊤` allows (`kappaFinSelf`; §27 *Open*).
- §51's `[handle-last]` already has a precise cancel row. But it types only clauses it writes itself, where κ never becomes a value, and the wire's clauses store κ.
- **So the rule is:** no two adjacent stages share a capturable operation.
- **What would lift it:** an n-free refinement of `cancelTy`. When the finalisers in κ perform no operation of the handler's own name, κ's cancel performs only their rows.

## 5. Mechanising the bridge

Most of the facts above are already Lean theorems. Two kernel lemma units would close the remaining gaps.
- **G1, order lemmas with effectful finalisers.** `unwind_prefix` and `cancel_prefix` assume finalisers whose operations are all abortive. Pipe cleanups perform operations answered outside (logging, I/O).
- **G2, order through handler frames.** The complete-run forms assume no handler frames, but a raise in a wire passes through Part A's per-observation handler.

| Part | Estimate (Lean lines) |
|---|---|
| G1 | 0.6–1.2k |
| G2 | 0.4–0.9k |
| The wire as a core term, the W lemmas, and the laws by induction | 1.5–2.9k |

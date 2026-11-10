# Assembly(n): the generated connector is the paper model's flat n-chain (L1, #920)

Issue: borrow-core #920 (pipes unit L1). Track: theory-foreman. Date: 2026-11-10, rev 2.2 (after one independent review, §7). **Kernel target: none.** Paper proof; mechanisation is out of scope. Cited by SPEC §75.

Claims about the paper model cite P1 or P1b, theory's notes on the paper model, which are not in this repository (as in `scope-pipes.md`). The one P1b definition this proof changed, `sel_ii`, is restated in §2.

**Sources:**
- SPEC §75 (the L1 entry: the connector, forwarding, errors, restrictions) and surface's decisions D1–D8 recorded there;
- P1: the connection operator, Thm A/I/S, Lemma M, the configurations S1–S3;
- P1b: Thm R, Thm X, `Abort E u d p`, (a′)(ii), **with §3's `sel_ii` amendment (review E3)**;
- SPEC §29a (cancellable waits, `[await-c]`), §27 (cancel rows);
- the user's (a′): "ONE n-ary connector per chain, as library code".

**Stop rule:** stop if a piece needs a property its signature can't carry, or if the proof needs a chain-wide invariant beyond P1's.

---

## 0. Result at a glance

- **Assembly(n) holds for every n**, by **one direct simulation for arbitrary n** (rev 2; the rev-1 induction on n misapplied its hypothesis, E1). Each case of the simulation uses one piece's lemma and touches the running stage and at most its two wires. S, R, X and (ii) transfer to every n.
- **Signatures:** §1 proposes them, each over one stage's or one wire's types; surface has adopted rev 1's and rev 2 adds what the review found missing (`Stop`, `Ended(k)`, `forwardWait_i`, and the three generated frame lists).
- **Chain-wide invariants used:** (I2) at most one stage runs, and (I5) the **demand-stack shape** (every stage downstream of the running one is `AtNext`). Both are P1's own (one active side of the operator; P1's S1–S3 configurations). So the stop rule is not triggered. The rev-1 claim that (I2) was the only one was wrong (review G1).
- **The model was amended, not the connector:** P1b's `catch` reported the latest error over all cleanups; the decided connector reports (ii). P1b §3 now has `sel_ii` (review E3), re-checked there.
- **One open decision, for kernel-foreman and surface (E4):** a §29a **cancellable wait** forwarded from a non-last stage. §3's L-forward-wait states the case D6/D7 already chose (Thm X's order: the connector is the waiter). Its consequence, that the stage cannot catch `cancelled` at that wait, is proposed as an **L1 restriction**. This needs kernel-foreman's confirmation that the forwarding clause types (§3).

---

## 1. The pieces and their proposed signatures (surface owns the final ones; the lemmas follow what surface adopts)

Stage `i` (0 ≤ i < n) reads wire `i` (type `A_i`, end `K_i`) and writes wire `i+1`. Rows are elided (`Σ` is the chain's outer row). `Event_i` is what one run of stage `i` can stop at.

    type State_i  = Ready(Loop_i) | AtNext(Kn_i) | AtYield(Ky_i) | AtFwd(Kf_i, Op_i) | AtStop(Ks_i) | Ended(K_{i+1}?)
    type Event_i  = Next(Kn_i) | Yield(A_{i+1}, Ky_i) | Return(K_{i+1}) | Skip(Loop_i)
                  | Fwd(Op_i, Kf_i) | FwdWait(WaitOp_i, Kf_i) | Stop(Ks_i)

    step_i         : State_i ⊸ Input_i ⊸ F_Σ Event_i
                     -- one observation of Loop_i, or one resume of the stored κ with its input
                     -- (Input_i = A_i + K_i at AtNext, 1 at AtYield, Ans at AtFwd, K_i at AtStop),
                     -- under the stage's wire sites and fresh sites (storing clauses: Part A)
    stop_i         : State_i ⊸ F_Σ 1          -- cancel the κ; close a not-started loop; Ended ↦ ()
    withStop_i     : State_i ⊸ U(1 ⊸ F_Σ R) ⊸ F_Σ R      -- rev 2.1: a thunked λ (U(F_Σ R) is unbuildable at non-empty Σ)
                     -- run the inner computation inside one unwind frame whose finaliser is stop_i
    handoff_i      : (Yield | Return)_{i−1} ⊸ State_i ⊸ (State_{i−1} ⊗ Input_i ⊗ State_i)   -- rev 2.1: Yield/Return only
                     -- wire i, defined at State_i = AtNext (I5):
                     --   Yield(b,κ) ↦ (AtYield κ, inl b, ·);  Return(k) ↦ (Ended(k), inr k, ·)
    forward_i      : Op_i ⊸ F_Σ Ans_i          -- performs the real resumable outer op (not a §29a wait)
    forwardWait_i  : WaitOp_i ⊸ F_Σ Ans_i      -- performs a §29a wait with [await-c]'s shape (§3, E4)
    finish         : R ⊸ (others' states) ⊸ F_Σ R   -- run's end: close the others, then answer r

`Ended(k)` keeps `k` when `K_{i+1}` is unrestricted, and is `Ended(·)` otherwise (review G3). The last stage has no `Ended`: `finish` consumes its `R`.

**Rev 2.2 (surface's forwarding check, the core text now `corpus/core-pipe-connector.bc`: it gives `(i32[55], (i32[10], inr i32[3]))`, `live 0`, interp and Backend2; `core-pipe-cancel-order` traces `21`):** L1 forwards cancellable ops only, with no `FwdWait`/`forwardWait_i` (§3); N stores `AtFwd` and the stage resumes on the next turn; stage rows exclude the forwarded op ((Row)); the forward site's handler is outside the yield site's ((One-frame)); a source's `Ended` keeps `()` at `K = 1`; at n = 2, `close_up_1 = close_others_1` (stage 1 is last, so nothing is downstream of it).

**Rev 2.1 (surface's first check, two-stage core text, all three programs check, `live 0`):**
- the glue's state also carries the **running stage** and the **pending input** `1 + Input_i`, since a hand-off's input reaches the stage at the next turn;
- `Input_i` is passed every turn and ignored at `Ready`;
- `Skip` is dispatched before `handoff`, which sees only `Yield`/`Return`;
- `stop()`'s κ is stored at the `next` κ's type (`AtStop`), and after `close_up_i` the stage is resumed with `inr ()` (the residual `K_i = 1` on the `A_i + K_i` answer; L1 provides `stop()` only at `K = 1`).

**The three generated frame lists** (each is nested `withStop`s, **most downstream innermost**, so the stops run downstream-first; each is one cancel region):
- `close_others_i` over every `j ≠ i`: the **per-step finaliser** around `step_i`;
- `close_all` over all n stages, with `i` at its own rank (between `i+1` and `i−1`): around `forward_i` / `forwardWait_i` (review E2);
- `close_up_i` over `i−1, …, 0`: the region of `stop()` by `i` (review G2).

**The glue (generated per chain):** the tuple `State_0 ⊗ … ⊗ State_{n−1}`, and a loop (one `unfold`) that at each turn calls the running stage's `step_i` under `close_others_i`, then dispatches on the event:
- `Next(κ)`: store `AtNext κ`. If `State_{i−1} = Ended(k)`, resume `κ` with `inr k` (stage `i` stays running; G3). Otherwise make `i−1` running.
- `Yield`/`Return` from `i < n−1`: pass through `handoff_{i+1}`; make `i+1` running.
- `Return(r)` from `n−1`: `finish r`.
- `Fwd(op, κ)` (only for `i < n−1`): store `AtFwd(κ, op)`; run `forward_i op` under `close_all`; resume `κ` with the answer.
- `FwdWait(w, κ)` (only for `i < n−1`): as `Fwd`, with `forwardWait_i`.
- `Stop(κ)`: store `AtStop κ`; run `close_up_i` (one region); resume `κ` with `K_i`, or, if the region kept an error, raise it at `κ` (§75's "raised at the call of `stop()`").
- `Skip`: loop.

The glue makes no other decisions. The last stage's ops, abortive ops and `must_resume` ops are not events: they pass through (§75, *Forwarding*).

---

## 2. The model and the relation

**The model** (P1 §2 and §4, P1b §3, under (a′)):
- a flat chain `s_0 ⊙ … ⊙ s_{n−1}`, one connection operator per wire;
- a configuration is **at most one running stage `i`** and every other stage at rest: a rest at a yield (`more & stop`), an awaiting continuation at an await, not yet started, or ended; or **no running stage, at an external point** (an `Eff` node of the whole chain, P1b (c3′)/(c8′));
- P1's step relation: the running stage steps, or hands over across a wire atomically (P1b row 2);
- P1b's abort `Abort E u d p` and `catch`/`seal` **with `sel_ii`** (P1b §3, amended by this proof's review, E3):
  `sel_ii(E, O_u, O_dp) = head O_dp` if the stops raised (`O_dp ≠ []`), else `last(E · O_u)`;
  `catch(Abort E u d p, H) = graft! u [O_u ↦ graft! (d ;; p) [O_dp ↦ H (sel_ii(E, O_u, O_dp))]]`;
  `seal` collapses an inner chain to its `sel_ii` choice, raised last on the enclosing stage's unwinding.
  Bracketing independence survives: `d ;; p` is one Lemma G′ composite, `head` commutes with reassociating `++`, and `u` is fixed at the raiser;
- an external point's stop branch is `…;; Ke.stop ;; …`, every stage downstream-first (c3′)/(c8′): where Thm X's cancel lands.

**Hypotheses** (P1b's premises, now listed; review G6): NP-cooperative, NP-masked-cleanup (a stage's unwinding and every stop run masked, so an op a cleanup performs is not a cancel point, and no `Fwd` is dispatched while a frame list is unwinding), NP-no-wire-cleanup, A0; and L1's restrictions (D1–D9, closed chains, an unrestricted `K` on every wire, `stop()` at `K = 1`, no marked wait forwarded (§75 *Restrictions in L1*)).

**R_n** relates Cₙ's tuple, the running stage (or "at `AtFwd`"), and the active frame list to a model configuration:
- **(I1)** componentwise: `Ready(l)` ~ not started; `AtNext(κ)` ~ awaiting; `AtYield(κ)` ~ a rest at a yield; `Ended(k)` ~ ended (with `k` delivered again on a later `next` when unrestricted); `AtFwd(κ, op)` ~ suspended at the chain's external point; `AtStop(κ)` ~ the model's `stop()` in progress.
- **(I2)** at most one stage runs in Cₙ, and it is the model's active stage; at `AtFwd` none runs and the model is at the external point (G1).
- **(I3)** the active frame list is read off the states: `close_others_i` while `i` runs, `close_all` at `AtFwd`, `close_up_i` at `AtStop`. Each is downstream-first.
- **(I4)** at `AtFwd`, the outer op is performed from the connector's frame, with every stage stored, under `close_all`.
- **(I6)** (rev 2.1) the glue's carried running stage is (I2)'s; a pending input `inr v` occurs only right after a hand-off or `Next` answer, and is the model's value in flight.
- **(I5)** the demand-stack shape: if `i` runs, every `j > i` is `AtNext`, and every `j < i` is `Ready`, `AtYield` or `Ended`. This is P1's S1–S3 (the downstream waits, the upstream rests). It is what makes `handoff_{i+1}` and `Next`'s dispatch total.

(I2) and (I5) are the chain-wide conditions; both are P1's. (I1), (I3), (I4) are per-stage, or a list read off per-stage states.

**≈** is P1's weak bisimilarity on observable effects, stage cleanup events (model stops / Cₙ's `stop_i` runs), **and the reported error** (review E3, N3).

---

## 3. One lemma per piece

- **L-step (`step_i`).** If `i` runs and `State_i ~ σ_i`, then `step_i`'s run is the model's run of `s_i` up to its next interaction point, ≈. The event is the model's next interaction: await → `Next`; yield → `Yield`; return → `Return`; turn end → `Skip` (stutter); a resumable outer op of a non-last stage → `Fwd` or `FwdWait`; `stop()` → `Stop`. *Proof:* `step_i` is one observation/resume of the stage under its storing clauses (Part A); the stage's code runs unchanged. That is P1 §2's operational reading, restricted to one segment.
- **L-handoff (`handoff_i`).** (Rev 2.1: the model's atomic handoff is split across two Cₙ turns, `handoff_{i+1}` then the next turn's `step_{i+1}` with the pending input. Between them the glue performs no op, so no cancel or effect can land there; the split is one model step plus a stutter, and R_n relates the pending input to the value in flight.) At `State_i = AtNext(κ')` (I5): `Yield(b, κ)` gives `AtYield(κ)` at `i−1` and `κ'` resumed with `inl b`, the model's atomic handoff (P1 (c4′)/(c10)); `Return(k)` gives `Ended(k)` plus `inr k`, the end delivery. A later `Next` at `Ended(k)` answers `inr k` again (G3).
- **L-stop (`stop_i`).** Runs exactly σ_i's current model stop, once: a κ cancel for a suspended stage (its finalisers, cancel mode); for a not-started stage, its loop's close, the model's stop of a `Ready` stream (P1 §2's `stop` on an unstarted producer; N2); `()` at `Ended`.
- **L-region (`withStop_i`).** A nest `withStop_{j₁}(… withStop_{j_m}(M))` runs M, then on unwind or cancel runs `stop_{j_m}, …, stop_{j₁}` (innermost first) in **one cancel region**, keeping the first error (`[cfin-raise]`; K2's `core-pipe-close`). The region's kept error is re-raised when it ends and, on an ordinary unwind, supersedes the pending one (§27). So each generated list gives its stages downstream-first with `head` of their errors: exactly `d ;; p` with `sel_ii`'s `head O_dp` for `close_others_i`, Thm X's list with `sel_cancel` for `close_all`, and P2's `stop()` region for `close_up_i`.
- **L-forward (`forward_i`, a non-§29a resumable op, `i < n−1`).** Premises:
  - **(Fresh-site)** "the site is fresh per copy": no handler sits between the stage's fresh site and the connector's clause (site discipline, §18), with D7's conditions (the name is connector-local, absent from the outer row; the op is not `unr`).
  - **(Same-sig)** the fresh name's signature equals the outer op's (A, B, q, marker), so `Input_i` at `AtFwd` is the outer answer (G5a).
  - **(One-frame)** the storing clauses for stage `i`'s wire and fresh sites capture `κ_i` up to the same connector frame (G5c). Rev 2.2, as built: the forward site's handler sits **outside** the wire (yield) site's, two nested handlers per turn, and the rest stored at either site has **one type**, so `AtYield` and `AtFwd` hold interchangeable rests that `step_i` resumes the same way.
  - **(Row)** the outer op's cancel row covers `close_all`'s row, `⋃_j row(stop_j)` (§27 `hfin`); inferred by #868 when the op's row is open, refused when it is fixed and too small (G4). Rev 2.2: **the stages' rows, hence their cleanup rows, exclude the forwarded op**; only the glue's row adds it. Otherwise `close_all`'s row contains the op and (Row) would need the op's cancel row to contain itself, which only ⊤ satisfies. So a stage's cleanup cannot perform **the same cancellable op the chain forwards** (§27's ⊤ cancel-row limit, listed in §27 Open; the checker already refuses it outside pipes: #868 phase 1's `[then]` refusal and `corpus/reject/fin-cancel-capturing.bc`; confirmed by surface). Answering (`fn`, e.g. `Log.note`), `must_resume` and abortive ops are never forwarded: in cleanup they only widen the forwarded op's cancel row, which is allowed (effectful cleanup).

  *Then* (rev 2.2, as built: N does not resume `κ_i` itself; it stores `AtFwd κ` and sets the pending input to the answer, and the next turn runs `step_i` under `close_others_i`. Between the answer and that turn the glue performs no op, so the split is one model step plus a stutter, as in I6): the answer resumes `κ_i` (Thm S's normal path, unchanged); a κ.2 cancel at the op runs `close_all`, every stage downstream-first with `i` at its rank, and returns the first error to the canceller: Thm X, matching (c3′)/(c8′). If the outer handler cancels and then raises, that is Thm X followed by an ordinary raise at the handler (G5b).
- **L-forward-wait (`forwardWait_i`, a §29a cancellable wait, `i < n−1`; E4). Not in L1 (rev 2.2):** the checker does not yet emit `effAwait` (§29a lists it as not built), so no stage can perform a marked wait, and L1 forwards only **cancellable** resumable ops (`cancel[CR]`, L-forward). This lemma, (R-wait) and its conditions move with `forwardWait_i` to the surface unit that makes the checker emit `effAwait`; nothing in it changes. A §29a cancel is a resume with `inr ()` at `[await-c]`, which then raises `cancelled` at the wait site (SPEC §29a; only `[await-c]` may perform a marked op, `[perform]`'s `hac`). So:
  - `forwardWait_i` is the connector's own `[await-c]` on the real wait, under `close_all`. On `inl a` it resumes `κ_i` with `inl a` (normal path). On `inr ()` it raises `cancelled` **at the connector**, which unwinds `close_all`: every stage's stop downstream-first (`κ_i` cancelled in cancel mode), then `cancelled` propagates out of the chain. That is Thm X's order, and it is what D7 and D6's `pipe-cancel-order` ("`321`", not "`132`") already require.
  - **Consequence:** stage `i` does not observe `cancelled` at that wait; its frames run as a cancelled κ (finalisers in cancel mode, the task's region still live, since the connector is inside it).
  - **(R-wait), the restriction that comes with marked-wait forwarding** (accepted by the coordinator for that unit): a non-last stage may not catch `cancelled` around a forwarded wait (refused, with the reason "a forwarded wait's cancel stops the whole chain, downstream-first"). Under it, L-step's "the stage's code runs unchanged" holds, since no stage code could tell the difference. The alternative, resuming `κ_i` with `inr ()`, keeps the stage's `catch` but gives Thm R's order with `i` first, i.e. `132`, and also needs the connector to pass a marked answer through, which `hac` forbids.
  - **Kernel-foreman's answer (2026-11-10, read against `effThen` Fundamental.lean:581 and §29a; nothing built): it types.** The clause is a `[then]`: M = the connector's `[await-c]` on the outer wait at Γ₁; N = resume `κ_i` with `inl a`; D = `close_all`, with the stored κ's in Γ₂ (N and D share Γ₂ as alternatives). The stage's `[await-c]` at the fresh marked name is handled by the connector (`effHandleCs` takes markers); resuming with a `1 ⊕ 1` value is not a `[perform]`, so `hac` doesn't apply. Conditions, all now premises of L-forward-wait:
    - **(hU)** the connector's row is `¬UnrD` (κ's are not banged);
    - **(hfin)** the outer wait's cancel row is above D's row, which is (Row); the elaborator gives the wait that row (§29a allows any);
    - **(Clause)** the connector also types a clause for the fresh name's op 1 (the abortive cancel target), though it is never reached;
    - **(Shield)** after the wait answers `inr ()`, law 5c keeps the task cancelled, so a stage finaliser that waits on a marked wait raises `cancelled` at once (kept by `cfin`). Stage finalisers that must wait use §29a's shielded, unmarked `complete`, its existing rule, now listed as a hypothesis.
  - **D is `close_all` in K2's one-region form** (`core-pipe-close`, #918/#959): a perform at a connector-local site under the nested `withStop` frames, whose clause cancels that one continuation, so every frame's stop runs inside **one** `ccatch` and `[cfin-raise]` keeps the first error. A *sequence* of separate `κ_j.2()` calls would not do: a raising one would skip the rest, or (as nested `[then]`s) keep the latest. Kernel-foreman flagged that sequence form; K2's form is the one every frame list in §1 uses.
- **L-finish (`finish`).** Stage `n−1`'s `Return(r)` runs `close_others_{n−1}` (downstream-first, one region) and answers `r`, or raises the kept first error. That is the model's `run` composed with `run_or_raise` (P1b `run` returns `(r, O)`; §75 chose the raise, with A0 on `r`; G7).

---

## 4. The simulation (rev 2: direct, for arbitrary n; E1)

**Assembly(n).** For every n ≥ 1, every well-typed closed chain `s_0, …, s_{n−1}` under the hypotheses of §2, and the initial states (all `Ready`, stage `n−1` running, the model's initial configuration): **Cₙ ≈ the model chain**, and every Cₙ turn preserves R_n and matches zero or one model step.

*Proof,* by cases on one turn of Cₙ: the running stage's **position** (first `i = 0`, middle, last `i = n−1`; for n = 1 the first is the last) and the **event**. Each case reads at most `State_{i−1}`, `State_i`, `State_{i+1}` and one frame list, so it is the same for every n.

| Event at running `i` | Lemma | Model step | R_n afterwards |
|---|---|---|---|
| `Skip` | L-step | none (stutter) | unchanged |
| `Next`, `i > 0`, upstream not `Ended` | L-step | `i` awaits; active side moves to `i−1` (P1 (c9′)) | (I5): `i` joins the `AtNext` suffix |
| `Next`, upstream `Ended(k)` | L-handoff | `inr k` delivered again | unchanged |
| `Next` at `i = 0` | — | impossible: the head is a source (D1), which never awaits | — |
| `Yield`/`Return(k)`, `i < n−1` | L-handoff | atomic handoff on wire `i+1` | (I5): `i+1` leaves the suffix and runs |
| `Return(r)`, `i = n−1` | L-finish | `run`'s end, Thm S's order | final |
| `Fwd`, `i < n−1` | L-forward | the chain's external point (c3′)/(c8′) | (I2)/(I4): `AtFwd`, `close_all` |
| `FwdWait`, `i < n−1` (not in L1) | L-forward-wait | as above; on cancel Thm X then `cancelled` | as above |
| an outer op of `i = n−1` | — (passes through) | the last stage's own `Eff`; its stop branch is (c3′) with `i` most downstream, i.e. `close_others_{n−1}` around it, every stage downstream-first | unchanged |
| `Stop`, any `i > 0` | L-region on `close_up_i` | P2's `stop()`: the upstream downstream-first, then resume with `K_i`; a kept error is a raise at `i` (next row) | `j < i` all `Ended` |
| a raise from `i` | L-region on `close_others_i` | Thm R: `u_i` (`i`'s own frames, masked), then `d` = `n−1 … i+1`, then `p` = `i−1 … 0`, reported by `sel_ii` | final (propagates) |

The order in the raise row: `close_others_i` nests the most downstream innermost, so its stops run `n−1, …, i+1, i−1, …, 0`; `i`'s own frames are inside `step_i`, so they unwind first. That is `u ;; d ;; p` exactly, and L-region's `head` is `sel_ii`'s `head O_dp`, with the raiser's latest error kept when no stop raises. In the `AtFwd` rows the list is `close_all`: `n−1, …, 0` with `i` at its rank, Thm X's.

**Stutter is finite:** `Skip`, the dispatch and the storing of κ are bounded per turn; one turn is one model step or zero. (A non-productive stage that only `Skip`s is a divergence in the model too, by L-step.)

**Locality.** No case reads a stage other than `i−1`, `i`, `i+1` except through a frame list, and the frame lists are generated from per-stage `stop_j`. Adding a stage changes only the lists' length and the positions that count as "last". No induction on n is needed, and the rev-1 attempt was unsound (the prefix of C_{n+1} is an open chain whose last stage changes role; E1).

**Transfer.** S, R, X and (ii) are statements about the model's traces: stage cleanup order and the reported error, both among ≈'s observables. With P1b's model amended to `sel_ii` (P1b §3, re-checked there), **each holds of Cₙ for every n**. The seven L1 traces (D6) are instances at n ≤ 3 and test the generator, not the laws.

---

## 5. What this does not cover

- **Fusion (F):** a separate equivalence, Cₙ against the fused form. That is P3's relation R, not Assembly.
- **Open chains / chain-as-stage** (D8, L2), linear `K` (D4), and `stop()` at a residual other than `1`: excluded by L1's restrictions, so by the hypothesis.
- **Forwarding §29a marked waits:** not in L1 (no stage can perform one); L-forward-wait, (R-wait) and kernel-foreman's four conditions wait for the unit that makes the checker emit `effAwait` (§3).
- **Mechanisation:** out of scope. A Lean proof would be a machine-level simulation of the generated core term against the model, with P3-style location bijections for κ cells.

---

## 6. Interface with SPEC §75

- **Signature changes from rev 1:** `AtStop` and `Ended(k)` in `State_i`; `FwdWait` and `Stop` in `Event_i`; `forwardWait_i`; and three generated frame lists (`close_others_i`, `close_all`, `close_up_i`) where rev 1 had one. **`forward_i` now runs under `close_all`, not the per-step finaliser** (E2): under `close_others_i` a cancel at the forwarded op would never stop `κ_i`.
- **Restrictions in §75:** (Row), the forwarded op's cancel row covers every stage's cleanup row, and the ⊤ limit on a cleanup performing the forwarded op. (R-wait) is in §75 *Open*, with marked waits.
- The proof uses only: each piece's one-stage or one-wire type; the glue being a tuple plus dispatch; the three lists nested most-downstream-innermost; site discipline for the fresh sites.
- **Suggested SPEC sentence:** "The connector is generated per chain from `lib/pipe.bc`'s pieces (`step_i`, `stop_i`, `withStop_i`, `handoff_i`, `forward_i`, `forwardWait_i`, `finish`). By Assembly(n) (theory, `docs/new-core/assembly-n.md`), for every n it is weakly bisimilar to P1's flat chain, observing effects, cleanup order and the reported error, so P1 Thm S, P1b Thm R and Thm X, and (ii) hold for every chain."

---

## 7. Review findings and resolutions

The review (theory's notes, not in this repository) was by one independent agent, given the document and P1/P1b, not the author's conclusions). E3 and E4 were checked against the sources before fixing: P1b §3's `catch` does use `sel_raise` over all cleanups (before the amendment), and SPEC §29a's cancel is a resume with `inr ()` with `hac` restricting marked ops to `[await-c]`.

| id | verdict | resolution | re-check |
|---|---|---|---|
| E1 induction misapplied | holds | §4 is now a direct simulation for arbitrary n, by position × event | every row reads ≤ 3 states plus one generated list; n = 1 is the row set with first = last |
| E2 `forward_i` under the wrong frame | holds | `close_all` generated; (I3)/(I4) and the glue say so | `close_all`'s order `n−1…0` with `i` at its rank = (c3′)/(c8′)'s `…;; Ke.stop ;; …` |
| E3 model reports latest, connector first | holds | **model amended**: P1b §3 `sel_ii`, `catch` and `seal` redefined; Thm R row restated; ≈ observes the error | P1b §10 amendment: bracketing independence (head commutes with reassociating `++`; `u` fixed at the raiser); seal collapses an inner chain to its choice; Thm X unchanged |
| E4 §29a waits | holds | L-forward-wait states D7/D6's existing choice (connector is the waiter, Thm X's order); (R-wait) proposed; the alternative and its cost stated | kernel-foreman: the clause types (on paper, against `effThen`); moved out of L1 with marked waits (rev 2.2) |
| G1 hidden shape invariant | holds | (I5) added, cited to P1 S1–S3; (I2) amended for `AtFwd`; §0 reworded | `handoff` and `Next`'s dispatch are total under (I5); each §4 row preserves it |
| G2 `stop()` missing | holds | `Stop` event, `AtStop`, `close_up_i` | the row's order is §75's: upstream, then `i`'s unwinding (if a kept error raises), then downstream |
| G3 `Next` at `Ended` | holds | `Ended(k)` and a dispatch case | — |
| G4 cancel rows | holds | (Row) premise; a §75 restriction | — |
| G5 a–c | holds | (Same-sig), (One-frame), the cancel-then-raise case | — |
| G6 P1b's premises | holds | listed as hypotheses in §2; NP-masked-cleanup rules out a `Fwd` during unwinding | — |
| G7 `run` vs raise | holds | L-finish cites `run_or_raise` | — |
| N1–N3 | hold | fixed (N1 is moot: no induction; N2 in L-stop; N3 in ≈) | — |

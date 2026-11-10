# P2: scope for building pipes (`|>` push, `>|` pull)

Issue: borrow-core #907. Track: theory-foreman. Date: 2026-11-09. For kernel-foreman and surface-foreman; with notes for backend-foreman and docs-foreman.
Kernel target: none for this document. Each proposed unit in §9 carries its own line.
Repo state read: **origin/main df4f135f** (kernel-foreman's E1 verdict is at 4a1d42af), read-only, through `git show`. The kernel-foreman answers of P1b §11 cite 5e574363; that commit is not on this fetch's origin/main.

**Markers.** Every claim about the code carries one of two markers:
- **[checked: path:line]** — I read those lines at df4f135f;
- **[assumed]** — not verified.

Claims about the paper model cite P1 or P1b, theory's notes on the paper model, which are not in this repository.

**Decided inputs:**
- user, earlier surface work: "|> and >| as being push/pull";
- P1 choices: return-the-rest, tree-bisimulation laws, `|>` = stateful push with `//>` as its stateless case;
- P1b: errors are a control-flow effect;
- P1b §11 (a′)+(ii): one n-ary connector per chain, as library code; downstream-first cancels, each in its own nested finaliser; the first error across stages wins;
- FFI is out of scope.

**User decisions, 2026-11-09 (via the coordinator):** "I agree with r and fusion later", then clarified: "I mean ideally we land fusion at the same time or immediately after."
- **Q1 = (B′):** `|>` is push and keeps §33's cases. A stage whose first parameter is `pull` is refused at `|>`, with a message pointing to `>|`. `>|` is new. Existing stream pipes migrate.
- **Q2 = (R):** the adapters are rewritten as stages, using an item effect (named `Stream` after review, to avoid lib/async.bc's `await`) plus `Yield`, and the connector is a handler holding the stages' κs. Ports are dropped. K3′, typing the connector around looping stages (review E1), was later dropped: per-observation handling already types it. zip keeps its partner as a stored pull source.
- **Fusion (unit F) is in the main sequence** (the user's clarification: "ideally we land fusion at the same time or immediately after"). It lands with, or immediately after, L2, the unit that migrates the existing pipes, so the window in which counts are raised is **one merge at most**. Count changes in units before F are recorded as intended, "removed by F" (§8).

---

## 0. Summary

1. **`|>` exists already and is decided.** It is decision 50, a one-way door, with three elaboration cases chosen by the right-hand stage. Today's stream pipelines are pull, through `|>`'s plain-application case, into adapters that own their source. `>|` does not exist (§1).
2. **The paper model maps onto existing pieces almost one for one** (§2):
   - P1's *rest* is SPEC §15's stored generator `pull A B R`;
   - P1's stop branch is `unwind (D)`;
   - P1b's cancel is §19's cancel with `[cfin-raise]`, where the first error wins;
   - the n-ary connector is the `lib/async.bc` scheduler pattern.
3. **What is new to build:**
   - the `>|` operator, and stream edges recognised by their effects;
   - the n-ary connector (library), with stages as `Stream`/`Yield` computations, and the adapters rewritten (R);
   - the amber checks;
   - fusion via §51 `[handle-last]`;
   - #910 (raising stored generators) is no longer on this path under (R), but stays scheduled by surface.

   The design aims at **no kernel change**. kernel-foreman confirmed that the bracketing dependence comes from the nested encoding, and suggested a library connector (P1b §11). Open items remain (§6):
   - K1: the step finaliser's cancel rows;
   - K2: one cancel region for (ii);
   - ~~K3′~~ **dropped**: per-observation handling already types the pattern (kernel-foreman, main 4a1d42af; see §4);
   - **K4: §51 `[handle-last]`'s frontend and erasure laws**, which is fusion's real prerequisite (review E2);
   - B1 and B2 in the backend.
4. **The user's example** `watch(kube) |> filter(..) |> each(e -> reconcile(e) |> retry(3) |> timeout(30s))`.
   - The outer `|>`s are a stream chain: their stages perform `Stream`, so they get one connector.
   - The inner `|>`s are §33's existing effect layers.
   - Both follow §33 case (ii)'s pattern, in my words, not a quotation.
   - In that order, a timeout that escapes `each` closes the whole `watch` pipeline (§3).

---

## 1. What exists today

| Fact | Where |
|---|---|
| The token `\|>`, at the lowest precedence, associating left | [checked: Frontend/Lexer.lean:116, via the locator; Parser.lean:1171–1177, 1343–1350 via the locator] |
| `pipeStage`'s three cases: (i) a handler gives `with h { e }`; (ii) a function whose first parameter is a computation parameter gives `f(!{()->e}, …)`; (iii) any other function gives `f(e, …)` | [checked: Frontend/Elab/Effects.lean:3616–3640] [checked: SPEC.md:6373–6392] |
| Decision 50 (N6): "`\|>` pipes first and suspends its left side at a computation parameter", a one-way door. The user's words are the example in §3. "Applies the handler on the right" is marked as the assistant's provisional reading. | [checked: docs/effects-state/04-decisions.md:831–837] |
| §33 law 1 `m \|> h ≡ with h { m }`; law 2: chains of handler stages are associative, but associativity across *function* stages is open (port relabelling) | [checked: SPEC.md:6274–6292, 6474] |
| `>|` exists nowhere | [checked via the locator: Frontend, SPEC, book, lib; the `git grep` I ran returned no hits] |
| `Yield[T]` is a library effect, `ctl yield(x: T)` (cancellable) | [checked: lib/yield.bc:13] |
| A `for` over a generator is a handler site (push). The body is the clause. `break`/`return` cancel the generator, running its finalisers. | [checked: SPEC.md:2169–2191] |
| A body that performs a control operation, or loops, is not a clause, so the `for` **stores** the generator instead (pull). That is P1 §9's tail-resumptive criterion, already implemented. | [checked: SPEC.md:2193–2198] |
| A stored generator is `pull A B R ≜ νX. F((A ⊗ U X) ⊕ (B ⊕ U X)) & F R`: `next` returns an item plus the rest, or `B`, or a skip; `close` cancels, handing back `R` | [checked: SPEC.md:2226–2250] |
| The adapters are generic generators over stored generators, and **own** their source: map, filter, take, skip, enumerate, chain, flat_map, take_until, scan, zip, chunks, lines, batch | [checked: lib/adapters.bc:1–100] [checked via the locator: line numbers 20–147] |
| `\|>` into an adapter stores the left side: today's stream pipes are **pull**, through case (iii) | [checked: SPEC.md:6383–6385] (`corpus/gen-pipeline-pipe.bc` [assumed: not read]) |
| A stored generator's observations are pure: a generator with another effect (such as `Fail`) is not stored | [checked: SPEC.md:2372–2373; Frontend/Sugar.lean:5445–5447]. SPEC 1.58 (#913) states it as a limit of the surface, which the kernel admits (SPEC.md:2407–2411 at b16f8c73). #910: the kernel already admits raising stored generators, and surface builds that after J1 (coordinator). [assumed: #910 not read] |
| Stateful push stages ("adapters written as handlers over a computation") are not provided | [checked: SPEC.md:2366–2369] |
| Finalisers: `x <- M unwind (D); N` runs D on raise or cancel only (P1b's stop branch). `with h { M } finally { D }` runs D on every exit, elaborating to `x <- with h { M } unwind (D); D; x`. | [checked: Frontend/Elab/Effects.lean:1972–1976; Parser.lean:1840–1846] (`unwind` parsing at Parser.lean:2456–2465 [assumed: via the locator]) |
| Cancel semantics: `[finalise-cancel]`, `[cfin-raise]` (first error kept, `err ∨ e`), `[cfin-cancel]`, `[cancel-raise]` | [checked: SPEC.md:3262–3270] |
| `[then]` with an effectful finaliser: `Σ_D ≤ Σ`, cancel rows `F ⋈ Σ_D ≤ T` | [checked: SPEC.md:5177–5250] |
| Cancellable waits: a cancel resumes the `await` with `inr ()`, which re-raises `cancelled`; level-triggered | [checked: SPEC.md:5706–5730] |
| `lib/async.bc`: `Task[A] = box top U (νX. F (A + box top U X) & F 1)` (a boxed κ, BOXED-κ §28); `resume`, `cancel` ("its continuation's finalisers run, innermost first"); a queue of tasks run round-robin | [checked: lib/async.bc:31, 42–54, 60–110] |
| Backend2: `cancelK` keeps the first error (`[cfin-raise]`) | [checked: Backend2/Convert.lean:915–925] |
| Backend2 refuses only a finaliser that may *suspend* | [checked: Backend2/Convert.lean:2994–2995] |
| Backend2 cancels a stored κ | [assumed: Convert.lean:2484–2565, via the locator] |
| Backend2 builds state machines at stored-continuation sites (SPEC §49) | [assumed: via the locator, Convert.lean:35–36, 2569, 3374; SPEC.md:9162 heading checked] |
| There is no `each` or `fold` over generators in lib | [assumed: via the locator] |

---

## 2. The paper model on the real pieces

| P1/P1b notion | Real counterpart | Status |
|---|---|---|
| A *rest* `(B′ → T) & CT` (P1 §2): a stage suspended at a yield; `.more` continues it, `.stop` closes it | A stored generator `pull A K R` (one-way, B′ = 1): observation `.1` is `next`, `.2` is `close` | [checked: SPEC.md:2226–2250]. Exact for the one-way case. Two-way (B′ ≠ 1, a request sent upstream) has no counterpart in `pull`. A two-way stored stage would be `νX. B′ ⊸ F(…)` (a §22 `Clo`-style observation with an argument [assumed]). Out of scope for the first build (§9 unit L1 is one-way). |
| A stop branch at every suspension point (P1b §1) | A cancellable `ctl` operation's κ has a cancel branch (§27 `cancelTy`). The stage's `unwind (D)` frames run under the cancel. | [checked: SPEC.md:5235–5241, 3262–3270] |
| `on_close { C }` (P1b's close-only cleanup) | `x <- M unwind (C); N` | [checked: Effects.lean:1972–1976] |
| `finally` | `with h { M } finally { D }` | [checked: ibid.] |
| Cancel = take `.stop` (P1b Thm X) | `cancel` on a stored κ (`(nu_out (force g)).2`); a cancellable wait is resumed with `inr ()` (§29a) | [checked: lib/async.bc:54; SPEC.md:5706–5730] |
| Within one cancel, the first error wins | `[cfin-raise]` | [checked: SPEC.md:3267] |
| On an ordinary unwind, the latest error wins | A finaliser's escaping raise supersedes the pending one | [assumed: kernel-foreman's answer, SPEC ≈3295 / 3718–3722; not read by me] |
| Errors own nothing (NoOwn) | `[then]`'s pending-error persistence, `Row.PendPers` | [checked: SPEC.md:5232 for `PendPers`] (NoOwn as named by the coordinator [assumed]) |
| The n-ary connector (P1b §11 a′) | The `lib/async.bc` scheduler pattern: a handler that boxes each stage's κ (BOXED-κ), plus a loop that resumes and cancels them | Pattern [checked: lib/async.bc]. The connector itself is new (§4). |
| Push, deep fold (`//>`, P1 Thm L) | `for x in g(…) { body }` with a tail-resumptive body: a direct call, no allocation | [checked: SPEC.md:2193–2203] |
| Reify at a push→pull switch (P1 §9) | `for` with a body that performs a control operation **stores** the generator | [checked: SPEC.md:2193–2198] |

---

## 3. Surface: `|>` and `>|` (decided: B′)

**Decided (B′).** It keeps decision 50 intact. (Revised after review E3: under (R), stream stages are recognised by their **effects**, not by a first parameter, because an (R) stage has no source parameter.)

1. **A stream edge.** `e |> s` or `e >| s` is a **stream edge** when e performs `Yield[A]` (it is a source, or the end of a chain so far) and the call `s` performs the item effect `Stream[A]` (an (R) stage). A maximal run of stream edges is a **stream chain**, and elaborates to one n-ary connector (§4) in normal form; the user never sees a bracketing. The operator at each edge names that wire's mode: `|>` push, `>|` pull.
2. **Everything else under `|>` is §33, unchanged.**
   - (i) A handler: `with h { e }`.
   - (ii) A function whose first parameter is a computation parameter: `f(!{()->e}, …)`.
   - (iii) Any other function: `f(e, …)` (`x |> print`).
   - These are exactly today's cases [checked: Effects.lean:3624–3640, SPEC.md:6373–6392].
3. **The new refusal.** A function whose *first* parameter is `U (pull A K R)` and which performs no `Stream` is an old-style, source-owning adapter. It is refused at `|>`. *Message:* `` `old_map` takes its source as a stored generator; adapters are stages now: write `gen |> map(f)` (push) or `gen >| map(f)` (pull) ``. Under (R), lib's adapters are stages, so this refusal only fires on user-written source-owning functions.
   - A stage whose *other* parameter is a stored pull source, such as `zip(b)` or `chain(b)`, is unaffected, because its first parameter is not the piped source.
4. **`>|` is new.** It has the same precedence as `|>`, associates left, and is accepted **only on a stream edge**. *Message otherwise:* `` `>|` connects stream stages; `s` performs no `Stream[A]` ``.
5. **Mixing.** `src >| take(3) |> each(f)` is one chain of three stages, with one pull wire and one push wire, in one connector.
   - **Where a mode switch costs something** is an *operational* claim (P1 §9's tail-resumptive criterion, stated there and not proved; review: faithfulness). The connector boxes a stage's κ when that stage is suspended across another stage's work.
   - **Visibility.** The operator names the mode at each wire (P0 §4's option (i), done with operators).
6. **Migration** (the full list is in §8): `|>` pipes into adapters stay `|>` (push) or become `>|`, as the author chooses; both are valid under (R). The refusal fires only on old-style functions. Direct calls of adapters over stored generators (`map(gen, f)`, `for x in map(g, f)`) need the stage form or a wrapper.

**The user's example:**

```
watch(kube) |> filter(p) |> each(e -> reconcile(e) |> retry(3) |> timeout(30s))
```

- **The outer chain** `watch(kube) |> filter(p) |> each(…)` is a stream chain: `watch` performs `Yield[Event]`, and `filter` and `each` perform `Stream[Event]`. So it is one connector with push wires.
- **`each`'s per-item body** `reconcile(e) |> retry(3) |> timeout(30s)` contains no stream edge: neither `retry` nor `timeout` performs `Stream`. So it is §33's ordinary case (ii), effect layers, run per item inside `each`.
- **My summary, not a quotation** (review E6): both readings follow the pattern of §33's case (ii), where the stage receives the left computation and handles some of its effects. A stream stage is distinguished by `Stream`, which makes it a stream edge.
- **`each`'s body performs control operations** (`retry` performs `Clock.sleep`; `timeout` raises `Fail`) [checked by the reviewer: lib]. So it is not a tail-resumptive clause under SPEC §15 as written [checked: SPEC.md:2193–2198], and the connector keeps `each`'s upstream suspended as a boxed κ. Once §51's `[handle-last]` frontend lands, this clause class is covered without storing (§6, item K4).
- **A semantic note for the user:** in this order, a timeout that `retry` does not catch escapes `each`'s body, so `each` raises. By Thm R, that **closes the whole `watch` pipeline**. If per-item failures should not stop the watch, catch inside `each`'s body, e.g. `… |> timeout(30s) |> log_and_skip`.
- **What the example needs that does not exist:**
  - the stages `each` and the (R) `filter`;
  - a `watch` source that performs I/O. Stored generators cannot hold a capability today (SPEC §15 *Open*, :2358–2363 [checked]). Under (R), `watch` is a stage held by the connector, not a stored generator, and its I/O row is typed by the same per-observation pattern; only §15's capability item remains for a source that holds a capability.

Alternatives (A) and (C), not chosen: (A) leaves `|>` able to mean pull; (C) drops `>|`.

---

## 4. The connector as library code (decided: R)

**The stage form.**
- **The item effect** is new in lib, next to `Yield`: `Stream[A, K] { ctl next() -> A + K;  ctl stop() -> K }`.
  - It is **renamed** from the draft's `Await`, to avoid lib/async.bc's scheduling `await` [checked: lib/async.bc:27].
  - `next()` answers an item, or `inr k`: the upstream has ended with its final value k (P1 DP-1, end of stream carried as `A + U`).
  - **`stop()`** closes this stage's whole upstream (its stages' stops, downstream-first) and answers the upstream's residual `K`. That is today's `take` contract, which needs a source "that returns what it hands back when closed", `pull A K K` [checked: lib/adapters.bc:9–13]. A `next()` after `stop()` raises a protocol error. This is a runtime check, not typestate.
  - (Fix-check: this answers both "End has no payload for a mid-chain `take`" and the fused/unfused `take` mismatch. See §4, early stop, and §12.)
- **A stage**, for example:

  `fn map[A, B, K](f: !(A => B)) -> K with Stream[A, K], Yield[B] = loop { match next() { inl x -> yield(f(x)) | inr k -> return k } }`

  - A middle stage **returns** K at end of stream. The connector delivers that return to the downstream stage's pending `next()` as `inr k`. This is P1's DP-1 option, where the upstream's result flows downstream. It needs no NP-server here, because the connector, not the downstream stage, holds the downstream continuation. So nothing is stranded.
  - A second `next()` after `inr k` is answered `inr k` again only when K is unr. With a lin K it raises a protocol error (P1 NP-server's documented excluded case).
  - `Yield[B]` takes one type argument, as in lib [checked: lib/yield.bc:13].
- **`take(n)`** is `… after n items: let k = stop(); return k`. It closes its upstream **promptly**, as lib's `take` does today. `take_until` is the same.
- **Sinks** return. For example, `fold(z, f) -> S with Stream[A, K]`.
- **Names that clash with lib**, needing a qualified module or a rename at L2 [checked by the reviewer: lib/list.bc's `fold`]: `fold` and `find`.
- **A stage that begins with `next` works under both operators** (P1 Lemma M), so one adapter set serves `|>` and `>|`.

**The connector** is a library handler of `Stream` and `Yield` for every stage of a chain, on the lib/async.bc pattern (a handler that boxes a κ, plus a loop that resumes and cancels) [checked: lib/async.bc:31, 42–54]:
- **State:** one slot per stage, holding its boxed κ and the wire it waits on.
- **Driving:** the last stage drives. When a stage performs `next` on a pull wire, or `yield`s into a push wire, the connector resumes the stage on the other side, until it yields (pull) or performs `next` (push). This is P1's ⟨_|_⟩, generalised to n stages.

**Typing the connector around stages that loop** (review **E1**; this item is open, not "already typed"). Stages loop, so their rows hold `Div`, and `effHandleV`/`effHandleVB` require that the handled row hold no `Div` [checked: SPEC.md:2084–2089]. "A handler around a div computation is not provided" [checked: SPEC.md:7828]. So **a κ-boxing handler around a whole looping stage is not typeable today**, and `corpus/pending/async-stream.bc` waits on exactly this [the reviewer's finding; file not read by me].

The likely route, the one today's `for` already takes, is per-observation handling. A generator whose body loops is elaborated as a `Loop_Σ` state machine, and each of its observations is total [checked: SPEC.md:2210–2220, the "A loop" item]. A `for` handles one observation at a time (`handle_with[n](…) ((nu_out l).1)`) [checked: SPEC.md:2188–2192]. So the connector would hold each stage as its `Loop` state machine and handle `Stream`/`Yield` *within one total observation*, boxing that observation's κ. That never puts a handler around a `Div` computation.
- **Verdict (kernel-foreman, main 4a1d42af, 2026-11-09): the premise is true, the conclusion false, and K3′ is dropped.**
  - No rule stores κ around a computation whose handled row holds `Div`. V/VB carry `hdv`; `effHandleT`/`effHandleL` don't store; reify and `div_fuel` handle `Div` only.
  - **Per-observation handling already does it:** handle *one* observation `(nu_out l).1`, whose row is `Div`-free, with `effHandleV` inside `unfold`. The clause stores κ as the ν-rest, and the next observation resumes it.
  - [checked by kernel-foreman: `corpus/core-yield-pull.bc`, assurance unconditional, `i32[88]`, live 0; the surface already elaborates the pattern in `corpus/gen-div.bc`.]
- **The connector is that pattern's mirror, written for n stages.** It is plausible but not yet written:
  - the handled computation is one observation of the downstream stage's loop;
  - the `next` clause stores that stage's κ as the rest;
  - the `unfold` state is the tuple of the stage states.

  **Writing that instance is L1's first check**, with a stage that *has* a cleanup (SPEC.md:2194–2197's consumability point). Static site names are an elaborator concern.

**Its finaliser** (decided (a′)+(ii)):
- **Placement** (review gap: `[then]` splits the context, so a finaliser cannot reach κs that the running body owns). `D_close` is therefore installed **per step**, around each resume of a stage:

  `x <- resume(κ_i) unwind (cancel_downstream_first(others)); N(x, others)`

  `[then]` gives M the resumed stage's κ (Γ₁), and gives D and N the other stages' κs (Γ₂) [checked: the rule's context split, SPEC.md:5219–5222]. D consumes them on a raise; N gets them back on a normal step.
- **Order:** D cancels the other stages downstream-first, each cancel in its own nested `unwind` frame, so a raising cleanup cannot skip the rest. The raiser's own frames unwind first, because they are inside the resumed stage. This is P1b Thm R's order (u, then d, then p).
- **(ii) first error across stages:** the cancel sequence runs inside one cancel region, so `[cfin-raise]` keeps the first error [checked: SPEC.md:3267]. Whether that is expressible as library code is open item **K2**.
  - **If K2 is "no": stop and report to the user.** Do **not** fall back silently to (i): (ii) is the user's decision (review gap).
  - (ii) is a **decision** (P1b §11), not a consequence of Thm R. Thm R itself is stated for the model's latest-wins unwind (review: faithfulness).

**Return-the-rest and `run`** (P1 §8; P1b §3):
- When the last stage returns r, the connector returns `(r, rest)`, where `rest.stop` cancels the remaining stages downstream-first.
- `run` returns `(r, close outcome)`. `run_or_raise` is offered for unr R. The default for a chain used as an expression is a surface choice.

**A chain under `for`** (review gap): `for x in src >| map(f) { body }` makes `for` the chain's last stage. Its body is the sink, and `break`/`return` are the last stage returning (return-the-rest, then `run` closes). **The mode of the edge into `for`** follows today's §15 rule [checked: SPEC.md:2193–2198]: push (a deep fold) when the body is a tail-resumptive clause, otherwise pull (the connector keeps the upstream boxed).

**Early stop in the middle of a chain** (review E7, revised after the fix-check).
- **With `stop()`,** a mid-chain `take`, `take_until` or any stage that stops pulling closes its upstream **at once**, which is today's behaviour [checked: lib/adapters.bc:30]. Only the last stage returning goes through return-the-rest (P1 Thm S).
- **Without `stop()`,** P1's NP-close-at-rest would apply: the upstream stays open until the chain's rest is closed. The coordinator had accepted that as a documented restriction. The fix-check then showed it **contradicts fusion**: a fused `take` exits through `[handle-last]`'s cancel branch, which closes the upstream at once, while an unfused one waits. So fused and unfused traces would differ.
- **DECIDED (coordinator, 2026-11-09):** adopt `ctl stop() -> K`. The E7 acceptance of NP-close-at-rest for `take` is withdrawn. The alternative would make fusion change behaviour, so it was not a real option. It restores today's prompt `take`, makes fused and unfused traces equal, and gives End its payload. NP-close-at-rest then remains only for a stage that stops pulling *without* calling `stop()` (a lint, §7).

**Two-way stages** are deferred: `pull` is one-way, and a two-way wire needs an observation with an argument (SPEC §22's `Clo` [checked by the reviewer]). The laws are already two-way.

**The size of the rewrite** (R):
- The 13 generators of lib/adapters.bc [checked]. map, filter, skip, enumerate, scan, take, take_until, chunks, lines and batch become `loop { next; … yield }`.
- chain and flat_map run their inner source as a nested chain (sealed, P1b §5).
- zip keeps its partner as a stored `pull` source (P1 §12 form 2), because a second wire would be fan-in.
- lib/iters.bc (sized iterators over data) is untouched [checked by the reviewer].
- Direct calls over stored generators need the stage form or a `stored_to_stage` wrapper. The call sites are counted in §8.
- The missing Rust-parity adapters and sinks are written in the stage form.

---

## 5. The laws each piece must satisfy

Cite these in each unit's done-when. Each must be shown of the elaborated term, or as a corpus property in the §33 style ("holds by definition" or "holds by law X"). The wording was tightened after review to match what P1/P1b prove.

| Piece | Law | Source |
|---|---|---|
| The connector, normal operation | Items move in the same order, on the same wire, whatever the bracketing. With one normal form this is trivial for user programs, and it is what licenses the compiler's rewrites (F). | P1 Thm A, Cor A1–A3 |
| The identity stages | Identity up to weak bisimulation | P1 Thm I |
| The **last** stage returning early (`take_collect(n)`, `find`, `any`, a `for` with `break`) | Return-the-rest; `run` closes downstream-first, each stage once | P1 Thm S, §8 |
| `take(n)` / `take_until` in the **middle** of a chain | Calls `stop()` at the n-th item: its whole upstream is closed **at once** (downstream-first), and the upstream's residual K becomes the End it returns downstream. This is today's prompt behaviour (§4, decided). P1 NP-close-at-rest applies only to a stage that stops pulling **without** calling `stop()` (a lint, §7). | §4 `stop()`; P1 Thm S, applied to the upstream part; P1 NP-close-at-rest (lint case only) |
| A raise in any stage | The raiser's unwinding, then the stops downstream of it (downstream-first), then the stops upstream of it (downstream-first), then propagation. **Order:** Thm R. **Which error is reported:** by the decided rule (ii), the first among the closed stages' cleanup errors if any; otherwise the raiser's. (ii) is a decision, not part of Thm R, which is stated for the latest-wins unwind. | P1b Thm R; P1b §11 decision (a′)(ii) |
| An outside cancel (timeout) | Every stage's current stop, downstream-first; the first error wins; returned to the canceller | P1b Thm X; SPEC §29a |
| Cleanup that raises | Every remaining cleanup still runs once | P1b Lemma G′ |
| A handler around the chain vs around the last stage | Same cleanups, same order; only the handler's own effects move relative to cleanup (with the exact difference when a cleanup raises) | P1b Lemma T |
| A stateless stage | `p \|> loop(f) ~ p //> f`: the stage *is* a deep fold, in the tree model. That it compiles without capture is the operational tail-resumptive criterion (P1 §9, stated, not proved). | P1 Thm L; SPEC §15 [checked: SPEC.md:2199–2203] |
| Where the connector boxes a κ | **Not a law.** An operational expectation: at mode switches and at stages that are not tail-resumptive. Measured by counts, not proved. | P1 §9 (not proved) |
| try_fold | `fold` plus a handler (three placements) | P1b §7½ |

---

## 6. Open kernel and backend items

| # | Item | Owner | What is known |
|---|---|---|---|
| K1 | The connector's per-step finaliser (§4) cancels the other stages' κs, so its row Σ_D must include their cancel rows. `[then]` asks `Σ_D ≤ Σ` and `Σ_M(o).fin ⋈ Σ_D ≤ Σ(o).fin`. | kernel-foreman | The rule [checked: SPEC.md:5219–5228]; the context split that puts the other κs in Γ₂ [checked: ibid.]. That a library connector types at a row the user's program supplies is [assumed]. **`[then]`'s `!Γ₂` premise** [checked: SPEC.md:5219–5222]: if the chain's row holds an unrestricted operation at some depth, the other stages' κs in Γ₂ must be persistent. So the connector requires that **a stream chain's row has no unrestricted operation**, or K1 must show otherwise. **Check:** a derivation for a 2-stage connector step. |
| K2 | (ii): the downstream-first cancel sequence inside one cancel region, so `[cfin-raise]` keeps the first error | kernel-foreman | `[cfin-raise]` [checked: SPEC.md:3267]. Expressibility as library code is [assumed]. **If no: stop and report to the user.** No silent fallback to (i). |
| K3′ | **DROPPED** (kernel-foreman, main 4a1d42af). Per-observation handling (`effHandleV` around one observation inside `unfold`, κ stored as the ν-rest) already types the pattern [checked by kernel-foreman: corpus/core-yield-pull.bc; corpus/gen-div.bc]. What remains is L1's first check (§4, §9). | — | — |
| K4 | **Added after review E2.** F's prerequisite is §51 `[handle-last]`. A clause that works (here, yields downstream) then resumes κ last is the rule for "adapters over a source computation". Its **frontend** (R-1's: a checker producer for the node; the elaborator writing the works' and exits' tuples) and its **erasure laws** (T-B1/T-B1′/T-B2: the backend's licence to call a work where it is performed) are *Open*. **So is handler state (R-2, `effHandleLS`)** [checked: SPEC.md:9651], which the *stateful* adapters need: take, skip, enumerate, scan, chunks and batch, used by all four §8 programs (fix-check). | surface-foreman (frontend), kernel-foreman (erasure laws) | [checked: SPEC.md:9545–9562 (the rule), 9640–9653 (*Open*)]. |
| SPEC-fix | **If kernel-foreman finds a cited SPEC sentence stale** (**found:** §21 *Open*'s "a handler around a div computation is not provided", SPEC.md:4472–4474, ≈5836 at 4a1d42af: accurate literally but misleading, since per-observation handling is provided. Corrected by SPEC 1.58 (#913), SPEC.md:4513–4519 at b16f8c73. **Also:** §15's :2372–2373, which #910 overtook), the outcome is a **SPEC correction by docs-foreman** (user practice, 2026-11-09: "force the theory agent to go through the spec because it forces us to update it"). This document is then revised to cite the corrected lines. | kernel-foreman finds, docs-foreman corrects | Each claim here cites exact lines, so each stale sentence can be found. |
| B1 | Backend2 lowering of a finaliser that cancels a stored κ | backend-foreman | Backend2 refuses only *suspending* finalisers [checked: Convert.lean:2994–2995]. Stored-κ cancel exists [checked by the reviewer: Convert.lean:2484–2565]; `cancelK` [checked: :915–925]. That a cancel inside the finaliser is not "may suspend" is [assumed]. **Check:** one compiled 2-stage connector. |
| B2 | A wire's κ boxed at a bound (`spawn_in`) when a stage holds a borrow across a yield | backend-foreman, kernel-foreman | lib/async.bc has `spawn_in` [checked: its header]. Borrowed items across wires wait for the loans line (NP-owned). |

---

## 7. Amber restrictions: checks and messages (from P1b §6)

Owner: surface-foreman (unit C). Each must cite its P1b row.

| Row | Restriction | Check | Message |
|---|---|---|---|
| 3 | Cancel only lands at suspension points (NP-cooperative) | Lint: a loop in a stage body with no suspension point on some path | `warning: this loop in stage \`scan_all\` never suspends; a cancel or timeout cannot reach the pipeline until it finishes. Consider an explicit \`check_cancel()\` point.` |
| 4 | Cleanup cannot be cancelled from outside (masked) | Lint: a potentially blocking effect in `unwind (D)` or `finally` not under a local `timeout` | `warning: cleanup of \`sock_reader\` calls \`net.flush\`, which may block, and cleanup cannot be cancelled from outside; wrap it in its own timeout` |
| 7 | No `yield`/`next` (wire operations) in cleanup | Typing: D's row excludes `Yield` and `Stream`. Backend2 already refuses suspending finalisers [checked: Convert.lean:2995]. | `error: cleanup of stage \`gzip\` yields an item, but cleanup runs after downstream is closed. Emit trailing items when upstream sends End, not in cleanup.` |
| 8, 13 | A `catch` or `timeout` inside a later stage does not see upstream errors or bound upstream work (lexical) | Lint: a handler around a `next()` whose handled effects only upstream stages perform | `warning: this catch in \`each\` will not catch errors raised by upstream stages; catch around the upstream sub-chain: (src >\| parse).catch(...) >\| each(...)` |
| 11 (A0) | Every lin value live at a raise or close point is consumed on that path (released, or handed to an owner; NoOwn forbids moving it into the error) | Typing: extends `[let]`'s refusal of a non-consumable value held across a wait [checked: SPEC.md:5756] to every may-raise call | `error: \`buf\` (owned) is live where \`parse\` may raise, and no cleanup releases it on that path; add \`unwind (release(buf))\`` |
| P1 NP-close-at-rest (P1 §1; not a P1b row) | A stage that stops pulling **without** calling `stop()` leaves its upstream open until the chain's rest closes. (Rust's `Take` behaves the same.) lib's `take`/`take_until` call `stop()` and close at once. | Lint: a stage that returns without `stop()` while its upstream has a cleanup | `note: \`first_n\` stops pulling without \`stop()\`, so \`read_chunks\` stays open until the whole pipeline finishes; call \`stop()\` before returning to close it now` |
| P2-validate | Per-item recovery must not pass lin state the handler needs into a raising call | Typing: an instance of A0 together with NoOwn | `error: \`acc\` (owned) is passed to \`check\`, which may raise; errors cannot carry owned values. Validate first, then update.` |

---

## 8. Fusion, counts, migration and grounding

**Fusion (unit F).** In the elaborator, adjacent stages whose per-item work ends by resuming κ last compile as **one `[handle-last]` clause** (SPEC §51), with no κ boxed.
- **Review E2 corrected the draft's premise.** The draft said "tail-resumptive, as today's `for`". But a body that *yields* is not a clause under §15 [checked: SPEC.md:2193–2198], and stateful push adapters are "not provided" [checked: SPEC.md:2366–2369]. The rule that does cover map, filter, take, … is §51 `[handle-last]`, whose frontend and erasure laws are *Open* (K4).
- So **F = K4's frontend for stage chains + K4's erasure laws + R-2 handler state for stateful stages + the count restoration.**

**Fusion keeps the cleanup order and the reported error.** The connector's normal form has no bracketing. Merging adjacent stages turns two cancels into one, and under (ii) the first error across stages equals the first error within the merged stage. So adjacent fusion keeps both the cleanup order and the reported error. This is why (ii) matters.

**The count window: decided** (coordinator, 2026-11-09, on the user's "ideally we land fusion at the same time"). **L2's merge is gated on F's merge** (not on every count being restored), so L2 and F land together. If F cannot restore a program's count (a stage that cannot be fused), that program's rise is reported to the coordinator and the user with the stage named, and they decide. One unfusable stage then cannot block L2 indefinitely (fix-check: E9 by a new route). L2's intermediate counts on its branch are recorded in its PR as *"connector boxes stage κs; removed by F, #<F issue>"*, and are not committed to `counts.expected`.

**The programs whose counts move** [checked: `git grep -l "include adapters" origin/main -- corpus`, `corpus/counts.expected`]:
- `gen-adapters` `8 0 0 33 33 0`
- `gen-adapters-fail` `11 0 0 51 51 0`
- `gen-pipeline-adapters` `3 0 0 3 3 0`
- `gen-pipeline-pipe` `3 0 0 3 3 0`
- also `bench/chain-gen/main.bc:22`, the C/Rust comparison benchmark [found by the reviewer], whose timing (R) slows until F lands.

These baselines are **not** "zero allocations": `gen-pipeline-adapters` is `3 0 0 3 3 0` (review E8). F restores each to its pre-L2 line. Counts are measured on the backend that produces `counts.expected` [assumed: the closure backend; SPEC §15's lowering is `Backend/Clos/Capture.lean`, checked at SPEC.md:2340ff]. Backend2 is unit B. Not affected: `for-adapters` (sized iterators) and `gen-pipeline` (no adapters) [checked].

**Migration sites** (unit S edits the syntax, unit L2 the call shapes) [checked: `git grep` at origin/main, plus the reviewer's additions]:
- `|>` into adapters, which stays valid under (R), as push:
  - `corpus/gen-pipeline-pipe.bc:26,28`
  - `bench/chain-gen/main.bc:22` (a `|>` site; the fix-check corrected the draft's classification)
  - `docs/ergonomics.md:647–655`
  - `book/src/stdlib.md:552`, and the adapter signature table at `:513–535`
  - `docs/rec-effect/25-for-stdin.bc:22`
  - prose at `book/src/guide/iteration.md:250` and `bench/README.md:94`
  - `book/src/guide/iteration.md:291`
  - `book/src/recipes.md:443`
  - `book/src/stdlib.md:548`
  - `docs/ergonomics.md:684–1162`
  - `docs/effect-lowering.md:237` (prose)
- **Direct calls** over stored generators (`map(gen, f)`), which need the stage form:
  - `book/src/guide/iteration.md:268`
  - `corpus/gen-adapters*.bc` and `gen-pipeline-adapters.bc`
  - `scripts/compile-scaling.sh`
  - `corpus/reject/for-free-bound.bc` (its rejection reason must survive the change)
- `corpus/reject/take-failing.bc`: its reason (a failing source "stopped early has no error to report") changes meaning under (R). Mid-chain `take` no longer closes its source early (NP-close-at-rest), and no raise is involved (review E7: the draft wrongly cited Thm R). **L2 re-examines it, and any change of rule goes to the user.**
- `corpus/pending/async-stream.bc` waited on the same `Div` obstacle (E1); re-examine it against the per-observation pattern in L1; `div-in-adapter.bc` and `gen-adapters-io.bc` are re-examined in L2 [assumed: not read].

**Grounding.**
- **J2** (#783): `runChain(read_chunks(sock) >| tokens >| events >| fold(z, step))`. `read_chunks` performs I/O, so its typing under the connector is the per-observation pattern plus SPEC §15's capability *Open* item [checked: SPEC.md:2358–2363].
- **Hand checks:**
  - the *last-stage* early stop `… >| take_collect(3)` gives `read · release(buf) · close(sock)` (P1 §13);
  - a raise in `fold` gives the raiser's unwinding, then events' frames, then buf, then sock (P1b §8);
  - a timeout gives the stops downstream-first.
- **The user's example, its intended reading** (coordinator, 2026-11-09). In `watch(kube) |> filter(p) |> each(e -> reconcile(e) |> retry(3) |> timeout(30s))`, a timeout that `retry` does not catch escapes `each`'s body, so `each` raises, and by Thm R **the whole `watch` pipeline is closed**, every stage's cleanup running downstream-first. That is the intended reading of this order. To keep watching after a per-item failure, handle it inside `each`'s body (for example `… |> timeout(30s) |> log_and_skip`). The reading follows P1b §5's lexical rule: a stage's handlers see only its own effects.
- **Rust parity (P1 §11):**
  - map, filter, take, skip, enumerate, chain, flat_map, take_until, scan, zip, chunks, lines and batch exist (to be rewritten as stages);
  - **missing:** skip_while, step_by, dedup, inspect, and the sinks (fold, sum, count, collect, each/for_each, any, all, find, position, last, min, max);
  - try_* = fold plus a handler (P1b §7½);
  - zip in three forms (P1 §12).

---

## 9. Proposed unit split

Each unit names its Kernel target line, a done-when that is not shaped like the corpus, a stop rule, and the **SPEC entry content for docs-foreman** (code PRs do not edit SPEC).

| Unit | Owner | Kernel target | Done-when | Stop rule | SPEC entry content (for docs-foreman) |
|---|---|---|---|---|---|
| **K** — confirm K1, K2 and K4's erasure laws | kernel-foreman | none (derivations in existing rules); K4's erasure laws are theorems about `effHandleL` | (1) A `[then]` derivation for a 2-stage connector step (K1). (2) Yes or no on K2, with the derivation or the obstruction. (3) T-B1/T-B1′/T-B2 (§51 *Open*) proved, for F. (K3′ dropped.) | If K1 needs a new kernel rule: stop and report. A kernel change contradicts (a′). If K2 is no: stop and report to the user. | §27 *Programs*: the connector's step finaliser as `[then]`. §51: its erasure laws, moved from *Open*. (The §21 *Open* correction goes separately: kernel-foreman to docs-foreman.) |
| **S** — surface: `>|`, stream edges, the refusal | surface-foreman | none (elaboration into existing core) | (1) `>|` parsed. (2) A stream edge recognised by effects (left side `Yield[A]`, stage `Stream[A]`, §3), and a maximal chain normalised, left-nested with the edges marked. **Theorem shape:** two bracketings of one chain normalise to the same term. (3) **Transitional `>|`:** until L2, `e >| f(…)` with f's first parameter `pull` elaborates as today's case (iii) (store and apply), so `>|` is usable at once and outputs and counts are unchanged. **The refusal of source-owning functions at `|>` moves to L2**, where lib's adapters stop being source-owning (fix-check new error 1). In S it would break gen-pipeline-pipe, the bench and the book sites. (4) **The left side's row:** the stream-edge test needs the row of `e`. When `e` is not a call (a block, an `if`), its row is inferred where available. Otherwise the edge is treated as §33's case (iii), with a note `cannot tell whether this is a stream: annotate the block's row`. | If decision 50's cases (i)–(iii) would change for non-stream functions: stop and report. | A new entry "`>|` and stream chains": the stream-edge rule by effects, the normal form, the mixing rule, the refusals, the user's example (§3, including the note that a timeout escaping `each` closes the pipeline). |
| **L1** — the connector, one-way | surface-foreman (lib) | none | (0) **First check:** write the connector as the mirror of `core-yield-pull.bc`'s per-observation pattern for 2 stages, one of which has a cleanup, and run it (assurance unconditional, live 0). (0′) A normalised chain elaborates to one connector call. (1) `lib/pipe.bc`: the item effect `Stream[A, K] { ctl next() -> A + K }`; the connector as a handler of Stream/Yield, holding each stage per observation (the verified pattern), with the per-step finaliser (§4), return-the-rest, and `run`/`run_or_raise`. (2) **The check:** on a 3-stage chain, the cleanup traces under last-stage early stop, a raise in each position and an outside cancel equal P1 Thm S / P1b Thm R / Thm X: **7 traces, compared against the laws**. (3) The first error across stages (K2 must be yes; if it is no, the work stops and goes back to the user, §6). (4) A `for` over a chain (`for` as the last stage). (5) **Fixes the connector's shape**, for F. | If the 2-stage instance in (0) does not type with existing rules: stop and report. A kernel change contradicts (a′). | A new entry "The pipe connector": the stage form, the per-step finaliser and its order, the error rule (ii), return-the-rest, `run`, `for` over a chain. `stop()` and prompt mid-chain close. *Open:* NP-close-at-rest for stages that stop pulling without `stop()` (Rust's `Take` behaves the same); `next()` after `stop()` is a runtime protocol error, not typestate. |
| **L2** — rewrite the adapters, add the missing ones, zip | surface-foreman (lib) | none | (1) The 13 adapters as Stream/Yield stages, one set for both operators (P1 Lemma M). (2) The missing Rust-parity adapters and sinks, resolving the `fold`/`find` name clashes. (3) zip's three forms. (4) The direct-call sites of §8 migrated, and the `|>` refusal of source-owning functions enabled (moved from S). **Count:** every adapter in P1 §11's table exists or has a recorded reason. **Merge gated on F** (§8): L2 and F land together, so `counts.expected` never records a rise. L2's branch counts are recorded in its PR as *"connector boxes stage κs; removed by F, #<F issue>"*. | If an adapter needs a primitive beyond `next`, `yield` and release: stop and report. | Replace §15's adapter paragraph with the stage form; note take-failing's and for-free-bound's outcomes. |
| **C** — amber checks and lints | surface-foreman | none | Each §7 row implemented, and one program per row triggers it with the stated message. **Count: 7 of 7.** | If A0 needs a kernel premise beyond `[let]`'s: stop and report. | A short entry "Pipes: restrictions and their messages", citing P1b §6. |
| **F** — fusion via `[handle-last]` | surface-foreman (elaborator, K4's frontend); kernel-foreman (K4's erasure laws, in K) | none for the frontend; K carries the theorems | (1) Adjacent stages whose work ends by resuming κ last elaborate to one `effHandleL` node (§51), with no κ boxed. (2) **Counts:** the §8 programs return to their pre-L2 lines; any program that cannot is reported, with the unfusable stage named (§8). (3) **The check:** a fused and an unfused 3-stage chain, including a mid-chain `take` that calls `stop()`, have equal cleanup traces under early stop, raise and cancel (by (ii) and `stop()`). (4) R-2 handler state for the stateful stages (K4). Starts once L1 fixes the connector's shape. **Merges together with L2**, since L2's merge is gated on F (§8). | If a stage's work cannot be put in `[handle-last]`'s shape: it keeps its κ, and is **recorded by name** (not a stop). If the frontend needs a kernel change beyond §51: stop and report. If the erasure laws fail: stop and report. | §51: its frontend for stage chains, moved from *Open*. A connector-entry paragraph on fusion and why it preserves the order and the reported error. |
| **B** — Backend2 lowering | backend-foreman | none | One compiled 2-stage connector with a raising stage and a timeout, run on Backend2, produces Thm R's and Thm X's cleanup orders. **Counts:** the §8 programs at their pre-L2 lines on Backend2 too, after F. | If the step finaliser's cancel is classed "may suspend" (Convert.lean:2995): stop and report. | §49/§27 Lowering paragraphs: the connector's step finaliser and its boxed κs. |
| **J** — grounding | surface-foreman | none | J2 `runChain(read_chunks >\| tokens >\| events >\| fold(...))` runs; a last-stage early stop, a raise and a timeout give the P1/P1b traces. | If `read_chunks`'s I/O needs §15's capability *Open* item: report. | None (corpus). |

**Order:**
- K ∥ S;
- then L1 (its first check is the per-observation instance);
- then L2 ∥ C ∥ F. F starts once L1 lands, and needs K4. **L2's merge is gated on F** (decided), so the counts never rise on main;
- then B;
- then J.

---

## 10. Not covered

FFI callbacks (deferred by the user), two-way wires in the build (laws already two-way), fan-in and fan-out, `race`, other effects as the "track", borrowed items across wires (the loans line), concurrent cancel (P1b row 12, red), and dynamic handler scope across wires (P1b row 13, red).

---

## 11. Review findings and their resolution

The review was independent: one agent, read-only. It checked about 30 citations and spot-checked 10 `[assumed]` claims, all of which proved true.

| Finding | Severity | Resolution |
|---|---|---|
| E1: the (R) connector, a κ-boxing handler around looping stages, is not typeable today (`effHandleV`/`VB` refuse `Div`; "a handler around a div computation is not provided") | error | The premise was verified in SPEC. The route proposed was per-observation handling (§4). **kernel-foreman (4a1d42af): that route already works**, so K3′ is dropped, and §21's sentence is corrected (SPEC 1.58, #913). |
| E2: F's premise ("tail-resumptive, as today's `for`") is false for stages that yield | error | Verified [SPEC.md:2193–2198, 2366–2369]. F is rebuilt on §51 `[handle-last]`, whose frontend and erasure laws are *Open*: **K4**. **Decided:** L2's merge is gated on F (§8). |
| E3: (B′) classified stages by first parameter, which (R) stages lack | error | Fixed: stream edges are recognised by effects (§3). |
| E4: missing site `bench/chain-gen/main.bc:22` | error | Added (§8). |
| E5: leftovers from (P) and the pre-decision draft | error | Removed (K3, ports, `map_push`, "push versions", "case (ii)'s Yield instance"). |
| E6: an invented quotation | error | Marked as my summary (§0, §3). |
| E7: mid-chain `take` is not prompt under NP-server, and that changes today's behaviour; take-failing wrongly cited Thm R | error | **Resolved by `stop()`** (§4, decided after the fix-check; the earlier acceptance of NP-close-at-rest is withdrawn). Mid-chain `take` closes promptly, as today. NP-close-at-rest remains only as C's lint (§7). take-failing is to be re-examined (§8). |
| E8: wrong count baseline ("allocations at 0") | error | Fixed (§8, unit B). |
| E9: F's stop rule made its done-when unreachable | error | Fixed: a stage that can't be fused is recorded by name, not stopped on (§9). |
| Faithfulness: the push→pull switch stated as a law; (ii) cited to Thm R; "no capture"; "confirmed by kernel-foreman" | — | All restated (§0, §5). |
| Gaps: `D_close` can't see the running body's κs; which backend produces the counts; `for` over a chain; End payload; name clashes; missing §8 sites; K2's silent fallback | gap | The per-step finaliser (§4); the counts backend (§8); `for` as the last stage (§4); `Stream[A, K]` with `K` in-band (§4); `Stream`/`next` renamed and the `fold`/`find` clash noted (§4); the sites added (§8); K2 = no now means stop and report (§4, §6). |
| Nits: citation ranges | nit | Fixed where cited (ergonomics 684–1162, the SPEC ranges). |


**Fix-check** (one agent, the fixes only; the review ends here):

| Item | Verdict | Resolution |
|---|---|---|
| E5, E6, E8, §5 faithfulness, C's count | fixed | — |
| E1/K3′ | fixed with nits | Fixed. Then **resolved by kernel-foreman** (4a1d42af): premise true, conclusion false, K3′ dropped, and SPEC §21 *Open* is corrected (SPEC 1.58, #913). |
| E7 | nits | Superseded by `stop()` (§4): **decided**. |
| The gaps (per-step finaliser; `!Γ₂`; K2 wording; the `for` wire mode) | nits | Fixed (§4, §6, §9). |
| K4 omits R-2 handler state | still wrong | Fixed (§6, §8, F). |
| E9 by a new route (F's full restoration gating L2) | still wrong | Fixed: the gate is on F's merge, and an unfusable stage is reported, not blocking (§8). |
| E4 sites | still wrong | Sites added and reclassified (§8). |
| New: S's refusal would break pipes before L2 | new error | The refusal moved to L2; `>|` is transitional in S (§9). |
| New: fused vs unfused `take` traces differ under NP-close-at-rest | new error | `stop()` (§4): decided. |
| New: End has no payload for mid-chain `take` | new error | `stop()` returns the upstream's residual K (§4). |
| New: the stage example's `Yield[B, K]` and `end(k)` | new error | Fixed: `Yield[B]`, and a middle stage returns K (§4). |
| New: the stream-edge test cannot see a non-call left side's row | note | Inferred where available; otherwise §33 case (iii), with a note (§9 S). |

The fixes made after the fix-check have not had an independent pass. Under the standing rule the review ends here.

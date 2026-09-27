# Salvage from l_lang

A skeptical read of the previous language (`~/repos/l_lang`) for ideas worth keeping. Six readers covered theory, compiler theory, proposals and literature, spec, surface and corpus, and the archive. A synthesis pass deduplicated and ranked their candidates, and an adversarial reviewer tried to reject each one against borrow-core. **Verdicts** is the section to act on; **Ranked candidates** is the evidence.

Not covered: the proof techniques of the l_lang kernel (`LambdaLC/`) for μ, ν and coinduction, and where its proof burden grew. That needs a separate read of the Lean sources.

---

# Verdicts

Sources I checked: `borrow-core/SPEC.md` §§6–11, `docs/decisions.md`, `docs/overview.md`, `docs/scope-recursion.md` §§4 and 7, `docs/dream-properties.md`, `docs/prior-art-*.md`, `Backend/README.md`, `scripts/compile-corpus.sh`, and issues #1–#27. On the l_lang side I opened the files each idea cites.

## 1. A suspended computation needs a cancel path, and cancelling must unwind it — **KEEP**

- **Supported in l_lang.** `l_lang/docs/theory/one-rule-mobility.md` §6 ("What is missing is not lifetime safety but a destructor") grades its evidence READ/RAN, and §12 corrects three premises of that document, none of them in §6. `corpus/abort_discards_runner_finalizer.l` exists and says outright: "the exit clause is a NORMAL-EXIT hook, not an unwind hook."
- **One correction.** "None of the runtimes disposes of a dropped continuation" is too strong. §6 names Rust `async` as the case that works, because a boxed future has drop glue that runs when it is dropped. That strengthens the idea: a `close` observation on the resumption is borrow-core's drop glue.
- **Not already done in borrow-core.** `docs/scope-recursion.md:303-308` and item 4 at :470 leave "continuations are `!` or carry their own `& F 1`" undecided. The resumption type `G B` at :310 has no close.
- **What is new.** Outside evidence that picks the finalizable option; the lowering of `close` as re-entry with an unwind (Wasm `resume_throw`), rather than as freeing; and the abort-across-borrow corpus program.

## 2. Name the exit mode where give-back does not run — **REJECT**

- The KRU theorem is cited faithfully (`2026-08-16-borrow-handler-hard-reason.md` §5, marked verified verbatim), but borrow-core has already answered the question it raises.
  - `SPEC.md` §8: "Partial operations return a sum where Wasm traps, because a trap would abandon linear resources." Trapping exits are designed out.
  - Out-of-memory is already planned as an escape in the compiler refinement, not the source theorem (`prior-art-memory-model.md:169`, Beck et al.).
  - An abort effect under #18 has to dispose of a resumption that cannot be dropped, so it reduces to idea 1.
- Keep KRU and Ahman–Bauer only as citations under idea 1.

## 3. Finite streams: end-of-stream in the observation, and close returns a residual — **KEEP-AS-REQUIREMENT (narrowed)**

- **Evidence to discard.** "Eight of ten measured wrong machines disappear" (`surface-design/10-synthesis.md:139`) measures l_lang's push/handler protocol with a `Done` tag. The document calls itself "Unverified", and its own §"one conclusion" says the agreement across designs "is an artifact of the `Done` tag". Do not cite it.
- **What survives.**
  - `Stream A` (SPEC §7) is infinite by construction, so §9 Open ("iteration over a borrowed buffer as a lifetime-indexed `Stream`") cannot express the end of a finite buffer except by encoding it inside `A`.
  - l_lang's file sources did return state from `finally` (`corpus/zoo_source_finally.l:14`).
  - That is a requirement: `νX. F(R ⊕ (A ⊗ U X)) & F R'`. It adds weight to the pending decision between a general `ν` and more fixed formers (`consolidation-audit.md:220`, item 8).

## 4. No extern may yield a host resource as a persistent integer — **KEEP**

- **Supported in l_lang.** `22-unsound.md` §22.1 (D-2) was read off the rules. The l_lang README (:344-350) records L-199, a use-after-free that exits 0.
  - Caveat: the README also says the fixtures that would reproduce L-199 are "not in `corpus/`". Treat L-199 as reported, not reproduced.
- **Why the gap is real in borrow-core.**
  - §11 allows `extern name : A` for any `A`, and §10 makes `I32` persistent.
  - The value relation at `I32` holds only at the empty resource. An extern typed `… ⊸ F I32` that returns a file descriptor meets its semantic type, and adequacy ("memory left empty") says nothing about the descriptor.
- **Action.** Add a §11 rule: an extern that yields a world resource yields a non-persistent opaque type. Optionally, add a ledger of world handles to the end-to-end theorem.

## 5. Buffer vocabulary against SPEC §9 — **KEEP-AS-REQUIREMENT (narrowed)**

- **Weak l_lang support.** `corpus/ARRAY-VOCAB.md` is a wish list: l_lang never built a runtime-sized carrier. Its "teeth" (for example C4, "borrow a linear-element array" → REJECT "until [FB]") are l_lang limitations, not soundness boundaries, so drop them.
- **Gaps found in borrow-core's own §9 table.**
  - (a) `buf_free` requires `A` persistent, so a `Buf (Ref X)` can be drained with `pop` but never freed.
  - (b) `Buf` has no sub-range view, while `Str` has `slice`.
  - (c) There is no `swap`, `tabulate` or `replicate`.
- **One flag.** `get` returns a same-lifetime `Imm 'a A` through the buffer. Decision 5 says the model excludes same-lifetime views through a pointer. #8 says such views are "justified by the extern", but if no implementation can meet that semantic type, the extern hypothesis is unsatisfiable and the end-to-end theorem is vacuous for any program using `get`. That needs a satisfiability check.
- **Drop:** the Vec length-in-header measurement (`bench/README.md:79-82`). It is an LLVM loop-invariant-hoisting result and does not transfer to Wasm.

## 6. Stream, iterator and I/O corpus programs — **KEEP-AS-REQUIREMENT**

- borrow-core's `corpus/` has no stream or I/O program. U1 (`dream-properties.md:14`) asks for iterator adapters and file I/O.
- **Programs to carry over:**
  - a file source that owns an fd and a buffer and is closed on early stop;
  - `repeat |> take 3 |> sum = 30` over an infinite source;
  - AoC 2015 day 1, reading one borrowed buffer twice;
  - `any`, `find` and `position`, each short-circuiting;
  - tee over a linear pull stream;
  - a guessing game driven by a scripted `Ref Input`.
- **Caveats.**
  - l_lang's `zoo_any*.l` does not short-circuit (`zoo_any_none.l:21`).
  - The take/drop answers depend on l_lang internals and were "NATIVE-ONLY; the interpreter declines" (`file_source_take_drop.l:54`), so they are unchecked.
  - The ratios are from a retired emitter.
- Take the program shapes only. Most wait on #7, #8 and a decision on finite streams.

## 7. Capability ops compile to direct calls on borrowed state — **REJECT**

- In borrow-core's #18 design the capability is a borrowed value, so an op call already is a direct call that writes the lent `Mut` state in place. No handler elimination is needed.
- #18 already says "test … the compiled cost (handlers as direct calls)", and C5 covers the equivalence.
- The benchmark ratios are ML and LLVM figures and do not transfer. Nothing is left that #18 and C5 do not already hold.

## 8. Handlers lend an ordinary borrow: acceptance tests — **KEEP-AS-REQUIREMENT (two tests only)**

- The direction duplicates #18.
- **Artifacts of l_lang:**
  - The label-search miscompile came from dispatching by type. borrow-core capabilities are lexical variables, so the ambiguity cannot arise in the source.
  - get/put over one state is trivial in borrow-core.
  - The Effekt/MLton point (`compiler-theory/02-…:37`) is about effect-polymorphic recursion, which borrow-core does not have (decision 8, and lifetimes are not monomorphised).
- **What survives.**
  - `handleFailList`, the program Effekt rejects (Schuster et al. 2020 §4.3, relayed as `[SAYS]` in `archive/2026-07/2026-08-01-multiop-lit-dispatch.md:338`), as an expressiveness test for `∀'h`.
  - Two same-typed capabilities in nested scopes, as a test for the #18 lowering.

## 9. Resumption obligations (Mut-lent needs at most one shot, lost updates) — **REJECT**

- One-shot continuations are already C6 (`dream-properties.md:43`), and `prior-art-memory-model.md` §"Multi-shot continuations" records the same hazard.
- A clause running over a stale snapshot of outer state is impossible when the state is a lent `Mut` cell updated in place.
- The finer content matters only if multi-shot is added, and that is not planned.

## 10. Corpus discipline — **KEEP (only machine-checked answers)**

- **The real gap.** `-- Answer:` lines (for example `corpus/sum-i32.bc:5`, `map-reuse.bc:6`) are prose that no script checks. `compile-corpus.sh` compares only `bcc run` against `bcc interp`.
  - The interpreter is the proved semantics, but that proof does not show the program computes what its author meant. #1's falsifier observables are only worth something if the stated answer is checked.
  - The `-- expect:` mechanism in `check-corpus.sh` already shows how to do it.
- **Reject the rest:**
  - the "pending" class: the l_lang corpus rotted with it, and decision 17 defines "done" differently;
  - the borrow→let criterion: it came from l_lang, where `borrow` admitted no program;
  - twin fixtures: already practised, for example the controls in #1.

## 11. One run sees one path: branch-dependent leaks — **KEEP**

- **Stronger than the list says, because the same shape exists in borrow-core.** `Backend/README.md:77-78`: "in a `case` arm, what only the other arm uses" is deep-freed. That is compiler-inserted drop code that differs by branch, the same shape as l_lang's 16-byte leak (`archive/2026-07/SPEC.md:1489`, found by reasoning after the empirical checks passed).
- The closure-IR interpreter "checks this as it runs", so it checks only the arm that ran, and `live 0` is per-run.
- **Action.** Before #15 lands, add a static check on the closure or flat IR that every variable is consumed exactly once on every path, or make the corpus exercise both arms of each discarding `case`. It matters most once #14's optimisations start moving drops.

## 12. Reject-set coverage — **REJECT**

- #6 already lists "escaping borrows through data". `corpus/reject/borrow-escapes.bc` already covers a thunk that captures a borrow.
- The effect and abort routes wait on #18 and would be written against its design, not l_lang's.
- Rust fixtures c04/c07 need dynamic indexing into places, which borrow-core does not have outside the §9 externs.

## 13. Mutually recursive data (Tm/Val/Env) — **KEEP-AS-REQUIREMENT**

- The source (`archive/2026-07/THEORY-mutual-recursion.md`) is low-trust, and l_lang's obstacle was its own grade machinery. The requirement stands on borrow-core's side.
- SPEC §6 restricts folds to `FShape` with a "closed leaf". A nested `μ` whose inner leaf mentions an outer variable (a mutual family, a rose tree, an evaluator over Tm/Val/Env) has no fold. No borrow-core doc or issue mentions this (grep for "mutual" in `docs/` finds nothing about data types).
- Bekić's theorem (simultaneous fixpoints become nested ones) is standard. How nested `μ` interacts with the fold rules and with `Imm̲` at `μ` has not been derived.

## 14. Handler-compilation rules and reading list — **REJECT**

- The raw reports are unaudited and flag their own inferences.
- A-normalisation is largely given by CBPV, where sequencing is explicit.
- "Resume or close is a run-time choice" is already true of borrow-core's linear resumptions.
- The Karachalias rules are for deep handlers in ML, and decision 15 makes deep handlers derived.
- At most, the Karachalias et al. citation can go in #18 when handler compilation starts. It is not a salvage item.

## 15. Stream sugar drops a second `emit` — **REJECT**

- No program exhibits it; it was read off equations (§22.3).
- In borrow-core, sugar desugars before checking, so a desugaring that drops a linear element is rejected by the checker.
- At persistent `A` it is an ordinary sugar bug that #17's desugaring tests would catch. There is no specific insight.

## 16. Checklist for graded modalities — **REJECT**

- Grade-0 erasure is standard QTT/Atkey material.
- The rest documents failures of l_lang's κ grades. #23 is future work and will start from the literature, not from this checklist.

## 17. Forcing programs P10, P11, P15, P27 — **REJECT**

- **P11** (writing a variant's tag invalidates borrows of the old payload) follows from `Mut` exclusivity and is #19's stated question.
- **P10** (`get_disjoint_mut`) duplicates §9 Open `split_at_mut`.
- **P15** (early exit leaving a vacant place) and **P27** (partial move, then reassembly) are covered by #5 (RFC 2094 cases) and by blocks.
- The places programme's own documents call themselves "a list rather than a theory".

## 18. Falsifiers for #27 (borrows as optics) — **REJECT**

- Refusing a thunk that captures the borrow is `borrow-escapes.bc`.
- Admitting `withbor(l, length)` is trivial with `foldImm`.
- Excluding runST, letregion and handler `finally` comes from l_lang's definition, which was rejected at review.
- `prior-art-optics.md` §§6–9 already sets #27's tests.

## 19. Sugar method and surface priors — **REJECT**

- "Write the program as it should read, then price the elaboration" is #17 plus decision 13 as already written.
- Guessing integer widths before typing is a standard front-end mistake.
- The Scala 51.7% figure is relayed, and elision-by-default is Rust's settled practice anyway.

## 20. SAX/SNAX layout prior art — **KEEP (as a reading pointer only)**

- DeYoung–Pfenning, where shift placement decides indirection, is a layout account in a polarised setting close to CBPV's `U`/`F`, and it is directly relevant to #13 (type-directed layout).
- borrow-core already cites Jang–Pientka (`prior-art-borrow-splitting.md:313`), but not SAX.
- Low trust: it is relayed through `archive/2026-07/2026-07-22-snax-comparison.md` and must be read from the paper itself. It says nothing about borrowing a variant payload.

## Salvage list

1. **Cancel path for suspended computations** → **#12 and #18**. Decide item 4 of `scope-recursion.md` for the finalizable option, citing one-rule-mobility §6 plus KRU and Ahman–Bauer. Specify `close` on the resumption as re-entry with an unwind (Wasm `resume_throw`), and add an abort-across-`withbor`/owned-cell program that must end with `live 0`.
2. **Extern handle rule** → **#7**. Add to §11: an extern that yields a world resource must yield a non-persistent opaque type, never `I32`/`I64`, and note that adequacy does not cover world handles.
3. **Branch-agreement check in the backend** → **#14 and #15**. Before any optimisation moves drops, add a static check on the closure or flat IR that every variable is consumed exactly once on every path, or corpus inputs that drive both arms of every discarding `case`.
4. **Machine-checked answers** → **new issue**. Give `-- Answer:` lines a parseable value and have `compile-corpus.sh` compare the interpreter's output against it, as `check-corpus.sh` does for `-- expect:`.
5. **Finite streams with a residual close** → **#8 and new issue**. (Resolved in SPEC 0.7, §7: general `ν` with `Iter A R R'`.) Before implementing §9 iteration, decide `νX. F(R ⊕ (A ⊗ U X)) & F R'` (general `ν` or a new fixed former, consolidation-audit item 8), so buffer iteration does not encode end-of-stream inside `A`.
6. **Buffer vocabulary gaps** → **#8**. Add a free for an emptied `Buf A` at linear `A`, a sub-range view on `Buf`, and `swap`/`tabulate`/`replicate`, and check that `get`'s same-lifetime view can be met at all under decision 5.
7. **Mutually recursive data** → **new issue** (link #3). Add a Tm/Val/Env evaluator or rose tree as a required program, and determine whether folds extend past `FShape`'s closed-leaf restriction to nested `μ` via Bekić.
8. **Stream and I/O corpus programs** → **#7, #8 and a new corpus issue**. Rewrite the file source with early close, `repeat|>take|>sum`, AoC day 1 over one borrowed buffer, short-circuiting `any`/`find`, tee over a pull stream, and the scripted guessing game, once #7 and #8 land.
9. **Handler acceptance tests** → **#18**. Add `handleFailList` (Schuster et al. §4.3) and two nested same-typed capabilities as #18 corpus tests.
10. **SAX layout reading** → **#13**. Read DeYoung–Pfenning (MFPS 2022) first-hand and cite it in the type-directed layout design if it applies to CBPV shifts.

---

# Ranked candidates

I checked each idea against borrow-core's `docs/overview.md`, `docs/decisions.md`, the headings of `SPEC.md` and §§7, 9 and 11 in full, `docs/scope-recursion.md`, `docs/dream-properties.md`, `docs/prior-art-memory-model.md`, `scripts/compile-corpus.sh`, `scripts/check-corpus.sh`, and issues #1–#27. I did not re-open or re-check any l_lang file or any literature citation. The skepticism notes come from the six readers, plus what I checked in borrow-core.

## Ranked list

### 1. A suspended computation needs a cancel path, and cancelling must unwind it, not free it
- **Kind:** requirement and pitfall (merges four candidates)
- **Sources:**
  - `l_lang/docs/theory/one-rule-mobility.md` §6
  - `l_lang/docs/compiler-theory/12-abandoned-list-applied-to-us.md` §2 (Koka #360), `00-LEDGER.md` K3/D-2
  - `l_lang/docs/spec/03-resource-algebras.md` §3.6.3, `22-unsound.md` §22.2 (D-3)
  - `l_lang/corpus/abort_discards_runner_finalizer.l`, `abort_across_borrow.l`, `abort_discards_nested_finalizers.l`, `kont_stored_abandoned.l`, `examples/salvage.l`
- **What it is:**
  - None of the runtimes the survey cites (OCaml 5, Chez, libmprompt, Koka) disposes of a dropped continuation. Where cleanup does run, it runs by re-entering the frames with an unwind (`discontinue`, Wasm `resume_throw`). l_lang had the same bug: its exit clause was a normal-exit hook only, so an abort skipped it.
  - The shape that did work: a linear resource on the failure path goes to the handler through the operation's payload.
- **Why it matters:** #18, #12, and the handler-compilation direction.
  - `D` and `Stream` carry `& F 1`. The resumption type in `scope-recursion.md:440`, `νX. F(B ⊕ (Op ⊗ U(Res ⊸ X)))`, has no close. Item 4 there ("continuations must be `!` or finalizable") is still undecided.
  - This is outside evidence for the finalizable option.
  - It also gives the lowering: close means re-entering with an unwind, and Wasm needs a separate abort/unwind instruction path.
  - Required corpus program: abort across a live owned cell and an open `withbor`. The lender gets its value back, and the run ends with `live 0`.
- **Skepticism:**
  - In borrow-core a `U C` cannot be forgotten, so l_lang's leak shows up as a type error, not a leak.
  - What is new is the design choice (a cancel observation on the resumption), the lowering, and the test programs. Safety is not new.
  - The one-rule-mobility survey is graded READ/RAN but not mechanised, and it corrects three of its own premises in §12.

### 2. State the exit mode where give-back does not run, before abort or trap exists
- **Kind:** theory
- **Sources:** `l_lang/docs/proposals/2026-08-16-borrow-handler-hard-reason.md` §5, §7.2 C5; `borrow-handler/effect-coeffect.md` §5, §8.1; `borrow-handler/control.md` §4
- **What it is:**
  - Katsumata–Rivas–Uustalu (LICS 2020), Thms 1–2: if the effect has a nullary operation (abort, raise), the only comonad that interacts with it exactly is the constant one. So a lender cannot promise an exact, total give-back.
  - Their repair is a residual interaction law with R = Maybe. Ahman–Bauer Thm 7 realises it: finalisation is guaranteed on every exit except one named "signal" mode.
  - Design rule: attach exit actions to the scope, not to the resumption.
- **Why it matters:**
  - `adequacyC` says memory is left empty.
  - Adding abort, exceptions or a Wasm trap forces a decision on how the theorem treats that exit: either a whole-program trap outside the theorem, or a named mode. It is better to decide this than to discover it.
  - Nothing in borrow-core mentions KRU, abort or panic (grep found none).
- **Skepticism:**
  - The adjudicator marks the theorem as checked against the PDF. I did not re-check it.
  - Reading the effect functor as the body's demand and the comonad as the lender's supply is informal.
  - Treating a trap as outside the theorem is a legitimate answer, but it still has to be written down.

### 3. Finite iterators: end-of-stream belongs in the observation, and close hands back a residual
- **Kind:** design
- **Sources:** `l_lang/docs/surface-design/10-synthesis.md`; `v2/00-best-features.md`; `corpus/zoo_source_finally.l`, `file_source_take_drop.l`; `surface/zoo.sfcp`
- **What it is:**
  - l_lang put a `Done` tag inside the element type. The synthesis measured ten wrong bytes→lines machines under that encoding, including a "biased length" bug (lengths stored as n+1, then corrected). Eight disappear once end-of-stream becomes an outcome of the pull.
  - Every l_lang file source returned its state from close.
  - Translated: `νX. F((A ⊗ U X) ⊕ R) & F R'`. The producer ends with R, and early close returns R' (for example the fd or the buffer) instead of `F 1`.
- **Why it matters:**
  - `Stream A ≜ νX. F(A ⊗ U X) & F 1` is infinite by construction.
  - §9 Open ("iteration over a borrowed buffer as a lifetime-indexed Stream") would have to encode end inside A, which is l_lang's mistake.
  - Close cannot return an owned resource.
  - This is evidence for the deferred general `νX. C` (§7 Open, scope-recursion §3) over fixed formers. It also bears on #27, where the residual is held until close.
- **Skepticism:**
  - The synthesis is self-described as "unverified", with lowerings compared by hand.
  - `scope-recursion.md` already sketches `G B` with a result B. What is new is the residual on close and the evidence against a Done tag.

### 4. Linear handles from the host world: no extern may carry one as an integer
- **Kind:** pitfall (merges two candidates)
- **Sources:** `l_lang/docs/spec/22-unsound.md` §22.1 (D-2), `08-effects-scopes.md` §8.7, `09-properties.md` §9.4.6–9.4.7; `l_lang/README.md` (L-199); `docs/archive/2026-07/THEORY-DROP.md` §3.2
- **What it is:**
  - In l_lang a host handle was an atom, and atoms were copyable and droppable.
  - L-199 was the result: a use-after-free that exited 0 and printed another object's byte, with different output at -O0 and -O2.
  - No proved property related program values to world resources.
- **Why it matters:** #7 and #8.
  - §11 allows `extern name : A` for any A, and §10 makes `I32`/`I64` persistent.
  - Spec rule: any extern that yields a host resource (a WASI fd, a host-table index) yields a non-persistent opaque type, never an integer.
  - Optionally, extend adequacy with a world ledger: every acquired handle is released exactly once. This is the one place heap-empty says nothing.
- **Skepticism:**
  - D-2 was read off the rules and no program exhibits it; L-199 did execute.
  - borrow-core already has linear `Ref Input`/`Ref Output` and opaque linear `Buf`/`Str`. The gap is only the rule for extern signatures.

### 5. Buffer vocabulary checked against SPEC §9, with two specific gaps
- **Kind:** requirement
- **Sources:** `l_lang/corpus/ARRAY-VOCAB.md`, `array_into_iter.l`, `array_source_multishot.l`; `examples/inc_all.l`, `vec_sum.l`; `bench/README.md` (Vec len)
- **What it is:** Seven operation groups, plus "teeth" that must fail closed:
  - silently dropping a linear occupant on update;
  - borrowing an array of linear elements unsafely;
  - multishot resumption over a consuming source.
- **Why it matters:** #8. Compared with §9 as written:
  - (a) `buf_free` exists only when A is persistent, and nothing frees an emptied `Buf` of linear A. A `Buf (Ref X)` can be drained with `pop` but never freed. I confirmed this from the §9 table.
  - (b) `Buf` has no sub-range view, while `Str` has `slice`.
  - (c) There is no `swap(i,j)`, `tabulate` or `replicate`.
  - Unverified, and needs a check: `get` returns a same-lifetime `Imm 'a A` through the buffer, and decision 5 says the model excludes same-lifetime views through a pointer. The extern's semantic type may then be impossible to meet.
  - The dated LLVM measurement (len in the heap header, 11.7× slower) suggests passing `{data, len}` by value in the #13 Buf lowering. Treat it as a hypothesis for Wasm.
- **Skepticism:**
  - l_lang never built a runtime-sized array, so the list is a wish list.
  - The buf_free and `get` points are readings of borrow-core's spec, not l_lang findings.

### 6. Iterator zoo and resource-owning stream pipelines as corpus requirements
- **Kind:** corpus (merges four candidates)
- **Sources:**
  - `l_lang/surface/zoo.sfcp`, `pipe_filter_count.sfc`, `take_sum.sfc`
  - `prelude.l`, `prelude_handlers.l`
  - `corpus/zoo_take_count.l`, `file_source_lines.l`, `file_source_drop_take.l`, `aoc2015_day01_real_iter.l`
  - `examples/zip.l`, `counter.l`, `guessing_game.l`, `expr_eval.l`, `salvage.l`
  - `docs/compiler-theory/raw/wc0isfyj5--measure.md`, `docs/spec/22-unsound.md` §22.3, `aoc/README.md`
- **What it is:**
  - Adapters: map, filter, fold, split_on and take, derived to count, sum, last, lines, words, head, any, all and map_maybe; also scan, position and concat.
  - Fan-in and fan-out. With push, tee is natural and zip is not; with pull, the reverse.
  - A file source that owns an fd and a buffer, with partial reads and refills, and is closed on early stop.
  - AoC 2015 day 1: one borrowed buffer read twice.
  - take/drop order changes the answer: `{count=2,pos=9}` vs `{1,5}`.
  - `repeat(10) |> take 3 |> sum = 30`, over an infinite source.
  - A FnMut counter, and a guessing game whose I/O is swapped for a scripted `Ref Input`.
  - expr_eval: a fold over a μ ADT.
- **Why it matters:**
  - Issues #2–#5, #7 and #8, U1/C1, and §7 streams. The borrow-core corpus has no stream or I/O program yet (confirmed by listing `corpus/`).
  - tee over a linear pull stream is the costly adapter to exhibit.
  - any, position and find are where early exit meets `close`.
  - Target: composition within single-digit percent of hand fusion. Measure instructions retired, not wall-clock time.
- **Skepticism:**
  - Everything has to be rewritten.
  - All of l_lang's versions iterate words, never borrowed elements, which is borrow-core's hard case (P2).
  - l_lang's `any` did not short-circuit.
  - The measured numbers are from a retired emitter. Take the programs, their answers and the measurement method.

### 7. Capability ops compile to direct calls on borrowed state; suspension only for ops that really suspend
- **Kind:** compiler and design (merges five candidates)
- **Sources:**
  - `l_lang/docs/compiler-theory/10-what-nobody-has-solved.md` §1, `11-where-we-sit…` §3 (unaudited), `08-theorem-handler-elimination.md` (audit)
  - `l_lang/docs/paper/grounding/relationships.md` §4.5 (Cor 4.6/4.7), `REFEREE.md` A.4
  - `l_lang/docs/spec/18-scopes-blocks.md` §18.0.4, `08-effects-scopes.md` §8.3.4
  - `l_lang/bench/README.md`
- **What it is:**
  - A clause that is uniform in the answer type, with target monad Id, is forced to be `k ↦ k(z)`: linear and tail-resumptive (standard Plotkin–Power).
  - Koka's `fun` and `linear effect` declare "no resume" on the signature.
  - Every real l_lang program lowered to one-shot state-carrying runners. None needed a reified continuation.
  - Measurements:
    - a tail-resumptive state handler ran at 1.00× rustc, while a non-tail generator took the fiber path at 23×;
    - state in globals cost 5 memory ops per byte against 1 in locals;
    - capability passing without it (Schuster et al.) was 5.56× on a stateful counter.
- **Why it matters:**
  - #18 ("test … the compiled cost (handlers as direct calls)") and dream-property C5.
  - Criterion: a handler that lends a `Mut` borrow of its state is a runner. Its ops are direct calls that write in place, with no write-back.
  - Benchmark stateful effects early.
  - Supports decision 15: pull codata avoids the non-tail push shape.
- **Skepticism:**
  - The mathematics is standard. The benchmarks are ML/LLVM, and the specific ratios do not transfer to Wasm and Cranelift.
  - Decision 8 (no ∀ in the core) means answer-uniformity can only be checked per instance.

### 8. Handlers lend an ordinary BoLo borrow, dispatched by value, with the tests that pin it
- **Kind:** design (merges five candidates)
- **Sources:**
  - `l_lang/docs/proposals/2026-08-16-borrow-handler-hard-reason.md` §3.3, §4, §6(c), §8; `borrow-handler/representation.md`
  - `l_lang/docs/compiler-theory/02-impossibility-static-handler-environment.md` §5
  - `l_lang/docs/archive/2026-07/2026-08-01-multiop-lit-dispatch.md`
  - `l_lang/docs/theory/new-language-plan.md` §4.6
- **What it is:**
  - Construction B, the tracked binder (System C's [Region] is [TryEff] minus the clause premise), rather than construction A, co-operations only. A hits a sub-capability wall on nested data.
  - Generative, lexical delivery (Tang & Lindley POPL'26). Label search let the innermost of two same-typed borrows win, and it caused an l_lang miscompile.
  - The capability should be one record of operations over one state. Two nested single-op handlers cannot share a state.
- **Why it matters:**
  - #18 already takes this direction (`withbor h …`). What this entry adds is acceptance tests:
    - an ambiguous-answerer program (two same-typed borrows);
    - get/put over one state;
    - `handleFailList` (Effekt's named rejected program, ICFP 2020 §4.3), to test whether `∀'h` recovers it;
    - two nested handlers of the same effect.
  - A freeze-gate note for decision 8: effect- or capability-polymorphic recursion under monomorphisation is what killed Effekt's MLton backend.
- **Skepticism:**
  - This corroborates a direction, it is not new.
  - Several citations are relayed "via ANGLE" and were not re-checked.
  - Whether borrowed capabilities stay second-class through blocks and codata has not been derived.

### 9. Resumption obligations: Mut-lent needs at most one shot; clause state must be threaded; lost-update test
- **Kind:** theory and pitfall (merges four candidates)
- **Sources:**
  - `l_lang/docs/proposals/borrow-handler/control.md` §3; `hard-reason.md` §2, §3.2
  - `l_lang/docs/compiler-theory/07-open-self-performing-handlers-as-recursion.md`, `02-…` §2 (Xie–Leijen TR §2.9.2)
  - `l_lang/corpus/runner_multishot_double_free.l`
- **What it is:**
  - Imm-lent resources survive multi-shot; Mut-lent ones need κ ≤ 1.
  - The check belongs on the operation signature, because the resources a continuation captures are at the perform site (Tang et al. POPL'24 Thm 3.4).
  - Deep-handler clauses may not capture linear state; it must be threaded.
  - Running a clause over a snapshot of outer handler state loses updates.
  - Falsifier: multishot re-runs an inner finaliser. l_lang printed 400 for a correct answer of 200.
- **Why it matters:**
  - #18, #23 and C6.
  - Corpus pair: nested handlers where the inner clause updates the outer state, plus a rejected self-reentry. Exclusivity should give λcoop's stratification.
- **Skepticism:**
  - Mostly covered already (C6; `prior-art-memory-model.md:142`).
  - The finer content matters only if multi-shot is ever added.
  - The semiring form of the rule is the authors' own design, not a cited result.
  - "Borrowing gives the stratification" is a reviewer's inference.

### 10. Corpus discipline: machine-checked answers, pending class, accepting twins, borrow→let test
- **Kind:** requirement (merges four candidates)
- **Sources:**
  - `l_lang/docs/theory/new-language-plan.md` §3, §4.6
  - `l_lang/corpus/ARRAY-VOCAB.md`, `zoo_take_count.l`
  - `l_lang/docs/analysis/2026-08-17-does-l-need-borrow.md` §4–§8
- **What it is:**
  - Compare each result against a pinned value, never only engine against engine.
  - A "pending" class: a program at its target shape with its current failure pinned, kept apart from soundness rejects.
  - Minimal-pair twins for every negative result.
  - Reordered-twin fixtures for layout.
  - A borrow program counts only if its answer depends on the borrowed contents: rewriting `withbor` to an owned `let` must change acceptance or the result.
- **Why it matters:**
  - Decision 17 and #6.
  - `compile-corpus.sh` compares `bcc run` only against `bcc interp`. The `-- Answer:` lines in corpus files are prose that no script checks. Rejects are machine-checked through `-- expect:`, so the same mechanism would work for answers.
  - Falsifier observables are already done (#1, closed).
- **Skepticism:**
  - borrow-core's interpreter is the proved semantics, so two equally wrong engines are unlikely.
  - l_lang's corpus still rotted. Keep headers short, and never pin known-wrong answers as passing rows.

### 11. One run sees one path: `live 0` missed a branch-dependent leak
- **Kind:** pitfall
- **Sources:** `l_lang/docs/archive/2026-07/SPEC.md` §7.8.25, §7.9; `RULINGS.md` R-07-12-A/B
- **What it is:**
  - Six passing runs hid a 16-byte leak that happened only on the untaken branch. It was found by reasoning.
  - The fix was a Lean checker requiring both arms of a branch to leave the same objects live, with a sorry-free soundness proof.
- **Why it matters:**
  - #14 and #15. The backend is tested, not proved.
  - Until #15 lands, a cheap intermediate: a branch-agreement check over the flat IR, or corpus inputs that drive both arms of every case that frees.
  - This matters most for the first optimisations and for aborting handlers.
- **Skepticism:** The bug was in l_lang's hand-written freeing code. Only the lesson transfers.

### 12. Reject-set coverage: escape routes and Rust soundness-hole fixtures
- **Kind:** corpus (merges two candidates)
- **Sources:**
  - `l_lang/corpus/borrow_escape*.l`, `abort_across_borrow.l`
  - `l_lang/docs/theory/borrowck-probe.md` (c04/c07), `rust-soundness-check.md`
- **What it is:**
  - Ways a borrow escapes: through a record field, a variant payload, a returned closure, a let-alias, an effect payload across suspension, an abort out of a borrow scope, or out of a finaliser.
  - Rust programs that rustc accepts and Miri flags as UB: c04/c07, a move inside an index operand; rust-lang/rust#153140.
- **Why it matters:**
  - #6. `corpus/reject/` has one escape test, `borrow-escapes.bc`.
  - Each route is a cheap reject with an accepting twin. They also give evidence for U3.
- **Skepticism:**
  - borrow-core rejects escape semantically, so the alias hole is probably absent there. The value is coverage.
  - The effect cases wait on #18.
  - Only c04/c07 have their sources reproduced.
  - Dynamic indexing into places may be impossible to express, in which case those fixtures test nothing.

### 13. Mutually recursive data (Tm/Val/Env) as a requirement
- **Kind:** requirement
- **Sources:** `l_lang/docs/archive/2026-07/THEORY-mutual-recursion.md` §1–§3, §7; `RULINGS.md` R-07-21-R
- **What it is:**
  - A metacircular interpreter or generic `clone` over `Tm ↔ Val ↔ Env`.
  - Encoding the family as one sum works but forgets the sort in the fold's result, which forces defensive re-projection.
  - Bekić's theorem desugars simultaneous fixpoints to nested ones, so no kernel former is needed. MultiRec gives index-preserving folds.
- **Why it matters:**
  - This is a gap in "programs we must be able to write": borrow-core's docs do not mention mutually recursive data (grep).
  - Folds exist only for `FShape`, whose leaves are closed. Nested μ with an inner leaf that mentions an outer variable gets no fold.
  - Relevant to #3 and §6.
- **Skepticism:**
  - l_lang's actual obstacle was its own grade machinery.
  - How nested μ interacts with the fold rules and `Imm̲` at μ has not been derived.

### 14. Handler-compilation rules and reading list
- **Kind:** compiler (merges four candidates)
- **Sources:**
  - `l_lang/docs/archive/2026-07/compiler-constraints.md` §13.4, §14; `RULINGS.md` R-08-03-B, R-08-04-A
  - `l_lang/docs/compiler-theory/08-…` (Karachalias et al. OOPSLA 2021)
  - `raw/wy90v40zm--synthesis.md`, `raw/woiqf6ien--ruling.md`
  - l_lang shadowing corpus: `deep_reinstall_shadows_outer.l`, `runner_shadow_across_handle.l`, `iter_shadow_across_case_arm.l`
- **What it is:**
  - Whether a clause resumes can be decided at run time (one object file printed 7 or 200 depending on argc). So:
    - build one general lowering first;
    - make each fast path a transformation that proves its own eligibility;
    - never classify clauses by whether they resume.
  - Karachalias et al.: handler reduction rules plus function specialisation for a handler around a recursive function (7564× slowdown without it).
  - Production state-machine transforms:
    - A-normalize first, so every value crossing a suspension is a named binder;
    - use one liveness analysis for both frame layout and drop insertion;
    - over-approximating the captured set can double-drop in a linear language;
    - Kotlin/Wasm skips its transform when the target has stack switching.
  - Return-tag protocol (Koka's `yld`) as a third lowering beside state machines and stack switching.
  - Same-effect shadowing across a function, handler or case-arm boundary. These miscompiled identically at -O0 and -O2, so differential testing between optimisation levels could not see them.
- **Why it matters:**
  - The "shallow handlers as state machines / stack switching" direction, and decision 15.
  - borrow-core's typed linear continuations still leave "resume or close" as a run-time choice.
- **Skepticism:**
  - The raw reports are unaudited and flag their own inferences.
  - The Karachalias rules are for deep handlers in ML and need re-deriving for CBPV with linear continuations.
  - Use this as a reading list with rules of thumb, not as findings.

### 15. Stream sugar pitfall: a one-seat step silently drops a second `emit`
- **Kind:** pitfall
- **Sources:** `l_lang/docs/spec/22-unsound.md` §22.3 (D-4), `18-scopes-blocks.md` §18.2.4
- **What it is:**
  - `emit A; emit B` delivered only B.
  - `emit A; break` delivered nothing, after A's side effects had already run.
  - The core program was well typed; the bug was in desugaring.
- **Why it matters:**
  - `unfoldS`'s step `S ⊸ F(A ⊗ S) & F 1` has the same one-seat shape.
  - Under decision 13 sugar is outside the trusted base. Generator sugar must refuse a second emit or lower to a real generator, backed by a desugaring test (#17).
- **Skepticism:** Read off the equations; no program exhibits it.

### 16. Checklist for graded modalities (#23)
- **Kind:** pitfall (merges three candidates)
- **Sources:**
  - `l_lang/docs/analysis/2026-08-17-does-l-need-borrow.md` §2, §7(b)
  - `l_lang/docs/spec/03-resource-algebras.md` §3.1, `25-open-questions.md` §25.1
  - `l_lang/docs/compiler-theory/12-…` Tier 3, `04-…`
- **What it is:**
  - Grade 0 must mean "erased at run time". l_lang evaluated grade-0 fields anyway, and a "borrowed" connection escaped into the program's answer.
  - "Never built" and "built, then unused" are different zeros.
  - Interval grades need lo ≤ hi, and every premise must be declared as either a membership test or an order comparison.
  - Survey: six systems typed grades and never lowered them; l_lang's κ became a seventh.
- **Why it matters:**
  - #23. Prove erasure in the model.
  - A grade should arrive with the instruction it selects, which is decision 17 applied to grades.
- **Skepticism:** Known from QTT and Atkey; recorded failures, not new theory.

### 17. Forcing programs still open for borrow-core
- **Kind:** corpus
- **Sources:** `l_lang/docs/theory/places-forcing-programs.md` Part 1, Part 4
- **What it is:**
  - P10 `get_disjoint_mut`: runtime indices, returning ⊕ an error.
  - P11: writing a variant's tag invalidates borrows of the old payload.
  - P15: early exit leaving a vacant place.
  - P27: partial move out of an aggregate, then reassembly.
  - P13 (arena cells outliving one iteration) and P21 (two-phase borrows) are already noted in `ideas-pointers-and-lifetimes.md`.
- **Why it matters:** #19 (P11), #8 (P10 as an extern), #5.
- **Skepticism:** A catalogue of citations. Ignore the numbering and everything from P29 on.

### 18. Falsifiers for #27 (borrows as optics)
- **Kind:** requirement
- **Sources:** `l_lang/docs/paper/defining-the-borrow.md` §2, §4.3; `REFEREE.md` A.2, A.3
- **What it is:**
  - Admit `withbor(l, λx. length x)`.
  - Refuse a thunk that captures the borrow and is invoked after the scope.
  - Exclude runST, letregion and handler `finally`.
  - The referee confirmed that non-escape is not parametricity, and that strict non-escape conflicts with nesting in that algebraic setting.
- **Why it matters:** #27 step 2: a falsifier list to run before building in Lean.
- **Skepticism:**
  - The paper's actual contribution was rejected at review.
  - Overlaps heavily with `prior-art-optics.md` §6.

### 19. Sugar method and surface priors (#17)
- **Kind:** design (merges three candidates)
- **Sources:**
  - `l_lang/docs/archive/2026-07/2026-07-22-surface-dream-draft.md`; `RULINGS.md` R-07-22-W/V
  - `l_lang/docs/spec/23-underspecified.md` §23.2 (D-7)
  - `l_lang/docs/lit/05-refusing-escape.md`, `06-permitting-escape.md`
- **What it is:**
  - Method: write each corpus program as it should read, then price the elaboration back to the core.
  - Don't let sugar pick integer widths before typing: l_lang's surface guessed operand widths before any types were known, producing spurious refusals and errors that named generated operations instead of the user's `+`.
  - Scala capture checking: 51.7% of changed signatures only mark a parameter as "uses but does not retain". That argues for non-retaining (elided) as the default.
- **Why it matters:** #17 and decision 13.
- **Skepticism:**
  - l_lang never built the surface.
  - The figures are relayed and the width problem is a standard front-end issue.

### 20. SAX/SNAX layout prior art
- **Kind:** theory
- **Sources:** `l_lang/docs/archive/2026-07/2026-07-22-snax-comparison.md` §1, §4
- **What it is:**
  - DeYoung–Pfenning (MFPS 2022): contiguous layout of sums and products, with `|⊕| = 1 + max`, and indirection chosen by where ↓ shifts are placed.
  - "Snip": a non-allocating cut that reuses part of an existing block.
  - Jang–Roshal–Pfenning–Pientka (FSCD 2024): freedom from garbage via adjoint modes.
- **Why it matters:** #13, #19 and #23. borrow-core's docs do not cite any of these (grep).
- **Skepticism:**
  - Not substructural and has no borrows.
  - Says nothing about borrowing a variant's payload in place, which is #19's actual problem.

## Area quality

- **docs/theory/:** Low. It is a closed loop of "places" documents, each auditing the last, and it ends by calling itself "a list rather than a theory". The two questions it circles are already settled in borrow-core (decision 5, `experiments/ModesLabels`). Worth keeping: the continuation survey graded READ/RAN, the pinned handler falsifiers, and the Rust probe programs.
- **docs/compiler-theory/:** Low to transfer, moderate as literature.
  - About 80% audits l_lang's own emitter.
  - The ledger retires 34 of its own beliefs, several of them the folder's own headlines, and counts disagree between audits.
  - Keep the page-cited literature (Karachalias et al., Schuster et al., Xie–Leijen, Muhcu et al., Koka #360).
  - The raw reports are unaudited leads.
- **docs/proposals, lit, paper, analysis, reviews:** Mixed.
  - The L-specific claims were overturned inside the repo: unifying-scopes was retracted, the scoped-access paper was rejected at review, and `borrow` "admits no program".
  - The adjudicated borrow-handler literature layer (KRU, Tang et al., System C, Ahman–Bauer) marks each citation as checked against the PDF or relayed, and it is the most reliable theory in the repo.
  - reviews/ has nothing to salvage.
- **docs/spec/:** Low as theory, since it describes what the implementation did after the fact and its only proved properties are syntactic. Useful as a register of defects: D-2, D-3, D-4 and D-7 are real pitfalls for areas borrow-core has not reached yet (externs, stream sugar, handlers).
- **surface-design, book, examples, corpus, preludes:**
  - The book is nearly all stubs and argues the failed thesis.
  - The synthesis is self-described as unverified.
  - The corpus is messy, with long dated headers and known-wrong answers pinned as passing rows, but it is the best record of which programs the user kept wanting to write and which pitfalls were measured.
  - The bench harness is self-declared unrunnable.
- **docs/archive/2026-07:** Low trust. It labels itself "never citable as fact" and its own index lists 14 contradictions. Keep only the survey files that grade their own evidence and the rulings measured against named fixtures.

## Dropped

- **Places accounting, stratification, reduction, root-decomposition, authority-sigma, adjoint-separation, nine-facts:** borrow-core already settled places by disjointness (decision 5) and lifetimes as labels (ModesLabels), and l_lang's own documents found this material self-refuting.
- **The runner as a construct, handler vs runner as two formers, l_lang's "custody coordinate":** l_lang machinery. The plan itself marks the runner "Not salvaged".
- **κ grades, interval grades, demand and delay axes, confinement modes, rows:** l_lang machinery, and the known cause of its failure.
- **One escape rule for closures:** already decision 3.
- **The -O2 malloc-elision finding:** applies only to the LLVM path, deferred by decision 18.
- **Reordered-twin layout bug as a design driver:** it was in l_lang's row layout, which borrow-core does not have. The twin-fixture practice survives in #10.
- **Wall-clock pipeline ratios and the rustc parity table:** from a retired emitter; only the method survives, in #6.
- **The "one rule, three enforcements" framing from one-rule-mobility:** not needed; its premises were corrected in the same document.
- **P29 onward from the forcing programs:** GC, C effective types, concurrency, CHERI and device memory are out of scope.
- **The Rust soundness check's seven "properties" as criteria:** they come from the places programme.
- **Q1/Q2/Q3 dispatch as a framework:** the author's own [INFER] framing. The test programs are kept in #8.
- **"Borrow cannot be a scope that answers operations" (unifying-scopes):** retracted within l_lang.
- **The scoped-access / defining-the-borrow definitions:** rejected at review. Only the falsifier probes are kept, in #18.
- **The zoo_source_escape.l reject:** in a linear language, returning a raw fd that the caller then closes is not an error.
- **Measured annotation-burden numbers as requirements:** kept only as a prior for surface defaults in #19.
- **Handler identity via tombstoned frames and co-operations:** l_lang's repair machinery. It is unnecessary if capabilities are values.
- **Pinning known-wrong answers as passing rows:** inappropriate for a verified project. Such programs belong in reject or pending.

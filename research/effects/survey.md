# Effects meets Borrows: a literature survey

**Scope.** The survey covers three questions:
- **Q1.** Which effect systems have formal proofs?
- **Q2.** What must an algebraic effect system satisfy when it extends a proven borrow calculus? This is the centerpiece.
- **Q3.** How do effects and borrows or ownership interact, both in papers and in working languages?

It also covers the stretch topics: linear, adjoint, graded and modal frameworks, and CBPV.

**Conventions.**
- **Mechanized (tool):** a proof-assistant development whose existence was confirmed from a primary source (paper text, README or source file).
- **Paper:** pen-and-paper proofs only.
- **(synthesis):** my own construction from the cited pieces. It is not a published result.
- **(unverified):** a claim I could not confirm from a primary source.

Your project directory (`/Users/johnthompson/repos/personal/borrow-land`) was empty when I surveyed it, so I could not tell how your borrow calculus is proved. Where the right choice depends on that, the survey gives both routes:
- **Semantic:** an Iris logical relation in the style of RustBelt.
- **Syntactic:** progress and preservation in the style of Oxide.

---

## TL;DR

- **The model.** A handler adds one runtime object to your calculus: the captured continuation `k`, which holds suspended frames together with their live loans and owned values. It also removes one assumption your borrow proofs almost certainly rely on, which is well-bracketed control. Each new proof obligation re-establishes a borrow invariant for one thing a handler can do with `k`: resume it once later, never resume it, resume it many times, resume it somewhere else, forget it, or re-enter the suspended code before resuming (§1.1).
- **What you must prove (Tier A).**
  - **A1:** type soundness for configurations that contain suspended frames.
  - **A2:** effect safety.
  - **A3:** multiplicity soundness, also called the capturing condition: a continuation may be used no more freely than the values it captures.
  - **A4:** lifetime soundness for continuations and handler capabilities.
  - **A5:** exclusivity across the handler boundary.
  - **A6:** defined discard semantics.
  - **A7:** semantic conservativity, meaning library proofs that assume well-bracketed control still hold.

  A1 and A2 are standard. A3 to A7 are where borrows cause trouble.
- **A widespread assumption that is false.** "Leaking `k` is as safe as `mem::forget`" does not hold in a Rust-like ecosystem. `mem::forget` cannot make a callee stop returning while its caller keeps running. Dropping or forgetting `k` can. Three libraries break this way:
  - `std::thread::scope`, which runs its body under `catch_unwind` and joins the threads afterwards (verified in the std source).
  - `replace_with` and `take_mut`.
  - `Pin`'s drop guarantee.
- **Decision 1: make effects lexically scoped capabilities typed with your existing lifetime sort.** `handle` lends `cap: &'h (mut) H`. Effect safety then becomes an outlives check, and abstraction safety holds by construction. This does not lock you out of rows: Tang & Lindley (POPL 2026) show that both rows and capabilities encode into modal effects.
- **Decision 2: every operation declares a control class.** The four classes are:
  - **tail-resumptive:** about the same as a method call.
  - **abortive:** about the same as unwinding.
  - **one-shot:** the core of the new work.
  - **multi-shot:** opt-in, and only allowed when the capturing condition holds.

  Tail-resumptive and abortive operations reuse your proofs almost unchanged. §1.7 lists which of your lemmas survive under each class.
- **Decision 3: discarding a continuation means observable unwinding.**
  - Dropping `k` unwinds its frames. Destructors run, and `catch_unwind`-style cleanup code sees the unwind and must re-raise it.
  - `forget(k)` is allowed only when `k: 'static`. The alternative is to make continuations linear.
  - You must specify whether code inside `k` may intercept the unwind. OCaml's `discontinue` can be caught.
- **Decision 4: `resume` is second-class by default.** Storing a continuation requires boxing it into `Cont<'k, A, R>`. Its lifetime bound, multiplicity and `Send` are derived from the **witness**, the set of locals live across the `perform`, which is how rustc already treats coroutines.
- **Decision 5: the borrow checker treats `perform` as a terminator with three edges:** out to the handler, resume, and drop. This matches MIR's `Yield`.
  - One-shot handlers can be macro-expressed by asymmetric coroutines (Kobayashi & Kameyama 2025), so rustc's coroutine borrow checking (including error E0626) is a sufficient template for them.
  - Multi-shot resumption turns the resume edge into a loop back-edge, which requires the borrow state at the resume point to be a loop invariant.
- **Decision 6: in v1, use deep handlers, algebraic operations only, and stackful fibers that never move** (so no `Pin` judgment is needed). Keep regions, borrow scopes and RAII in the core, because scoped operations are not algebraic.
- **Choose the proof route that matches your borrow proof.**
  - **Semantic:** start from Hazel, then Affect (affine continuations plus `Cell`-style references, Coq/Iris, no admits), then Yarrow (regions with temporary versus permanent revocation, Rocq/Iris).
  - **Syntactic:** start from System C (Coq, progress and preservation, no admits) and add Tang et al.'s linearity-aware semantics.
  - No published work combines RustBelt's lifetime logic with handler protocols.
- **Staging.** Each stage is a conservative extension of the previous one (§1.10):
  1. Tail-resumptive and abortive operations with lexical capabilities.
  2. One-shot operations with second-class `resume` and deep handlers.
  3. Boxed, first-class continuations.
  4. Multi-shot as an opt-in.
  5. Multiplicity polymorphism.
  6. A relational model.
  7. Inference.
- **Your project would be novel.** No published mechanized calculus combines lifetime-indexed `&`/`&mut` (with reborrowing, NLL and two-phase borrows) with effect handlers. Several related problems are also open (§6):
  - a conservativity theorem for library proofs that assume well-bracketed control;
  - lifetime-polymorphic operations under multi-shot resumption;
  - a sound join of borrow states at resume points.

---

## 1. What your effect system must satisfy (Q2)

### 1.1 The model

Your borrow theorems were proved under well-bracketed control. Timany, Guéneau & Birkedal (2024) define it as follows: "A program is said to be well-bracketed if every called function must return before its caller can resume execution."

It helps to read `op(v)` the way capability-passing semantics does (Brachthäuser, Schuster & Ostermann 2020). `op(v)` is a method call on a handler capability, the handler clause is the method body, and `resume(x)` is the return. The difference from a normal call is that the clause decides whether the return happens, when it happens, how many times, and from where. Each new obligation re-establishes one borrow invariant under one of those choices:

| What the handler does with `k` | What happens to the captured frames | Invariant at risk | Property |
|---|---|---|---|
| Resumes it once, later | They stay suspended, with live loans, while handler code runs | Exclusivity between handler and suspended frames; the lender must stay alive | A4, A5 |
| Never resumes it (abort, or drops `k`) | They are abandoned | Drop discipline; loans must end; cleanup that libraries run "after the body returns or unwinds" | A6, A7 |
| Forgets it (leak) | They never run and never unwind, and their loans end statically | Leak-sensitive APIs (scoped threads, `Pin`) | A6, A7 |
| Resumes it two or more times | They are duplicated, and regions are exited twice | Uniqueness of `&mut` and owned values; no double drop | A3 |
| Stores it and resumes it elsewhere | They outlive the code that lent to them | No dangling references | A4 |
| Re-enters the suspended code's API before resuming | Private invariants are observed partway through a transition | Library reasoning that assumes well-bracketed control | A7 |
| (Any case: which handler receives `op`?) | n/a | Who may capture your private frames | A2, B1 |

### 1.2 Terminology

Papers use these terms inconsistently. This survey uses them as follows.
- **one-shot:** resumed at most once (affine).
- **linear:** resumed exactly once.
- **multi-shot:** resumed any number of times.
- **abortive:** never resumed. Koka writes this `final ctl`.
- **tail-resumptive:** resumes exactly once, as the clause's final action. Koka writes this `fun`. The Koka book says "almost all operations in practice turn out to be tail-resumptive."
- **Koka's `linear effect`:** "effects whose operations are always tail-resumptive and use only linear effects themselves (and thus resume exactly once)". This is not about linear types.
- **Control-flow linearity** (Tang et al. 2024) and the **capturing condition** (Affect) are the same law, stated in different papers.
- **Witness:** rustc's term for the locals that are live across a suspension point. It is the natural definition of what `k` captures.

### 1.3 Tier A: metatheorems you cannot skip

#### A1. Type soundness for configurations that contain suspended frames

- **Statement.**
  - **Preservation:** if `Σ ⊢ ⟨σ; e⟩ : τ ! ε` and `⟨σ; e⟩ → ⟨σ'; e'⟩`, then `Σ' ⊢ ⟨σ'; e'⟩ : τ ! ε` for some `Σ' ⊒ Σ`. `Σ` must now also type continuation values and the loans they hold.
  - **Progress:** `e` is a value, or it steps, or it is `E[op v]` where `op ∈ ε` and no handler for `op` sits in `E`. This is the shape of Pretnar 2015 (Thm 4.2), Tang et al. 2024 (Thms 3.2–3.3) and Met (Thms 4.3–4.4).
  - **Double resume:** make "resume a continuation that was already resumed" a stuck state, so that soundness rules it out. Affect keeps a one-shot flag per continuation in the heap, a technique it takes from de Vilhena & Pottier.
- **Why it matters.** Configurations now contain things your borrow proof never saw: frames suspended inside handler frames, and frames stored in the heap.
- **Who has it.**
  - Bauer & Pretnar 2014 (Twelf).
  - System C (Coq).
  - Affect (Coq/Iris, semantic).
  - Tang et al. and Met (paper).
  - WasmFXCert (Rocq).
- **Proof cost.** Medium. The genuinely new lemma is that capturing an evaluation context preserves typing. System C's Lemma 4.6 derives the typing of `H[return y]` (with `y : τ0` free) from the typing of `H[cap_l(v)]`. Tang et al.'s Thm 3.4(2) is the linearity-aware version.
- **Borrow interaction.** That lemma must also split the loan environment, because the loans live in `E` move into the continuation.
  - In Oxide terms, the continuation value carries a loan set, just as Oxide's closures carry a captured frame.
  - In RustBelt terms, the continuation owns the lifetime tokens of its frames.

#### A2. Effect safety, and conditions on how effects are represented

- **Statement.**
  - If `⊢ e : τ ! ∅` and `e →* e' ↛`, then `e'` is a value (Yoshioka, Sekiyama & Igarashi 2024, Thm 5.8).
  - In capability form: a program never reaches `H[cap_l(v)]` without a delimiter for `l`. System C states this as Cor. 4.8: a well-typed program "never results in an undelimited label".
- **Conditions on the representation** (Yoshioka et al. Def. 5.1). The notation `(L)↑ < ε` means "label `L` may occur in `ε`".
  1. `(L)↑ < 0` never holds. Subeffecting cannot hide a performed label.
  2. If `(L)↑ < ε`, `(L')↑ ⊙ ε' ∼ ε` and `L ≠ L'`, then `(L)↑ < ε'`. Handling `L'` never erases `L`.
  3. *Only if you have `lift` or masking* (Def. 7.1): sets and simple rows fail this condition (Thm 7.2); scoped rows and multisets pass (Thm 7.4).
  4. *Only if handler dispatch ignores effect type arguments* (Def. 7.6): sets, multisets, simple rows and scoped rows all fail as they stand (Thm 7.7). They become safe if same-name labels may not be swapped.
- **Why it matters.** An unhandled operation is a failure mode separate from ordinary type errors. Subeffecting or masking can reintroduce it even when the rest of the soundness proof goes through.
- **Who has it.** Bauer & Pretnar (Twelf), System C (Coq), Met (paper), and Yoshioka et al. (generic, paper).
- **Proof cost.** Low. It is a corollary of A1 once progress mentions `ε`. Prove the algebra lemmas first.
- **Borrow interaction.** With capability effects, effect safety *is* a lifetime theorem: no capability is used after its handler frame has been popped. That is your outlives check. Conditions 1 and 2 then become facts about your lifetime or capture-set algebra: nothing can be subsumed into the empty set, and ending one handler's lifetime cannot discharge another's.

#### A3. Multiplicity soundness (control-flow linearity, the capturing condition)

- **Statement, typing side.** Affect §2.4: "when performing an effect do op e1; e2, either the effect op is one-shot, or the effect op is multi-shot and the remainder of the computation e2 is unrestricted (i.e., e2 does not capture any affine variables)". Tang et al. Thm 3.4(2) states it as "Unlimited continuations are unlimited". In your language, "affine" covers:
  - owned values that are not `Copy`;
  - `&mut` loans;
  - borrows of stack-local or region-local data;
  - one-shot continuations;
  - linear resources.
- **Statement, semantic side.** Use a tagged semantics in which every step conserves tags, `ℒ(M) ∪ S = ℒ(N) ∪ T`. This is Tang et al. Thm 3.6, which shows that tagged linear values "are not duplicated or discarded during evaluation". In addition, no step may resume a continuation whose one-shot flag is set (Affect).
- **Why it matters.**
  - Resuming twice a frame that holds `&mut x` creates two live `&mut x`. Resuming twice a frame that owns a `Box` frees it twice.
  - Links shipped exactly this bug for session-typed channels (Tang et al.).
  - Yarrow's example `region (let r = ref local 0 in do Foo r; !r)` is safe when `Foo` is one-shot and unsafe when it is multi-shot, because "multi-shot effect handlers break the invariant that regions can be exited at most once".
- **Where the condition hides.**
  1. *Implicit sequencing.* Affect: "constructs such as application and binary arithmetic operators implicitly perform sequencing". Check the condition in an ANF- or MIR-like core, not only at `let`.
  2. *Effect-polymorphic code.* Affect §2.5 shows that the naive type `∀θ.∀α.(1 ⊸θ 1) → α ⊸θ α` for `g := λf x. f(); x` is unsound. The fix is either use types `!` and flip-bang `¡` (Affect), or inferred qualified types (Tang et al.'s Q°eff).
  3. *Deep handler clauses* run once per operation, so they cannot move out of their environment. Tang et al. Thm 3.4(3) states "Deep handlers are unlimited". The Ante post's error message for the same mistake: "Handler body moves `value` which will still be needed if the handler is called again".
- **Who has it.**
  - Tang et al. 2024 (paper; implemented in Links).
  - Affect (Coq/Iris).
  - Tov & Pucella 2011 (paper).
  - Hazel and Iris-WasmFX, which model one-shot as a ghost token.
  - The closure analogue in Lorenzen et al. 2024: "Only affine closures may close over unique values".
- **Proof cost.** High. This is the largest new proof.
  - Syntactic route: Tang et al.'s tagged semantics.
  - Semantic route: model one-shot as an exclusive ghost token (Hazel, Affect).
- **Borrow interaction.** Treat multiplicities as a lattice of intervals, `{0}`, `{1}`, `[0,1]` and `[0,ω]`, not as a chain. `{0}` is harmless for affine values but breaks must-use values and destructors that must run, so 0-shot and 1-shot are incomparable once linear values exist. Affect notes its own gap here: "it might be useful to equip Affect with join ⊔ and meet ⊓ operations on modes".

#### A4. Lifetime (escape) soundness for continuations and capabilities

- **Statement.** In every reachable configuration:
  - (a) no handler capability is invoked outside its handler's extent;
  - (b) no continuation is resumed after a lifetime it holds a loan from has ended, or outside the extent of an enclosing handler whose capability it uses.
- **Typing proposal (synthesis).** A stored continuation has type `Cont<'k, A, R>`, where `'k` is outlived by every loan live at the capture point and by every enclosing handler it uses. Storing it at lifetime `'r` requires `'k: 'r`.
- **Why it matters.** A continuation is a closure over stack frames. Schedulers, generators and async code store continuations, and that is how a suspended frame's borrow comes to outlive its lender.
- **Who has it.**
  - System C (Coq): `resume` is second-class, and storing it requires `box`, which records the captured capabilities in the type.
  - Osvald et al. 2016 (Coq): second-class values with stack-bounded lifetimes.
  - Biernacki et al. 2020 (Coq): effect instances as type binders.
  - Xie et al. 2020: scoped resumptions, where "a resumption can only be applied under the same handler context as it was captured". In that paper this is a dynamic runtime check.
  - Xie et al. 2022: named handlers with rank-2 scoping.
  - Capture sets: Boruch-Gruszecki et al. 2023 (paper proofs), whose box calculus was later mechanized in Coq by Fourment & Xu 2023. System Capless (Lean 4) proves type soundness and scope safety.
  - Yarrow is a program logic, not a type system.
- **Proof cost.** Low if `resume` is second-class, because the property reduces to your existing escape analysis. Medium to high for first-class continuations.
- **Borrow interaction.** This is your no-dangling theorem applied to one more kind of value, with capture sets playing the role of loan sets. Müller et al. 2023 prove on paper that a typed translation from second-class capabilities into regions with explicit subregion evidence is "typability- and semantics-preserving". That is formal evidence that a handler's scope is a region, or lifetime.

#### A5. Exclusivity across the handler boundary

- **Statement.** Every reachable configuration satisfies your aliasing invariant when you count the loans held by:
  - (i) suspended frames;
  - (ii) handler clauses that are currently running;
  - (iii) values in transit, meaning operation arguments and resume values.
- **Rules that follow.**
  - **(a) Borrows passed up to the handler** must end by the matching `resume`, or when `k` is discarded. Ante ties such a borrow to `resume`, so that "we cannot call `resume` until they are dropped". Hylo has the same discipline for subscripts: "A subscript must have exactly one `yield` statement on every possible execution path."
  - **(b) Borrows passed down through `resume`** must end before the computation performs another operation that needs the same handler state. Ante: "each function using the same `Read (&own mut Box String)` effect is considered to borrow from the same effect handler". Two `&mut` obtained from one handler is then a lifetime error.
  - **(c) Handler code during suspension** runs in a loan environment that still contains the suspended frames' loans, so it cannot write places those frames have borrowed. Yarrow makes it undefined behavior "to use local references that are not part of the current stack", meaning references into a captured fiber's regions.
- **Why it matters.** This is iterator invalidation across a `perform`, and it is the biggest difference from garbage-collected effect languages. No mechanized type system covers it for lifetime-indexed `&`/`&mut`. Hazel's protocols cover the ownership-transfer part as a program logic.
- **Who has it.**
  - Ante (design only, no proofs).
  - Hylo subscripts and Swift yielding accessors (implementations; Swift's SE-0474 is accepted).
  - Hazel and TES (Coq/Iris).
  - Yarrow (logic level).
- **Proof cost.** Medium if encoded as reborrowing (next point); high otherwise.
- **Borrow interaction (synthesis): let your existing checker do the work.**
  1. `handle` lends `cap: &'h mut H` to the body, or `&'h H` when every operation takes `&self`.
  2. `cap.op(args)` reborrows `cap` for the call. The clause is a method that receives that reborrow as `self`, and `resume(x)` is its return.
  3. Rules (a) and (b) are then the ordinary reborrow rules for a call whose return happens to be delayed.
  4. Rule (c) holds conservatively if clauses are typed as closures that stay alive for the whole `handle` expression, because such closures cannot capture by `&mut` anything the body borrows.
  5. One piece is non-standard. Inside a clause, calling `resume` hands `self` back to the continuation for the duration of the call, so anything passed through `x` is a reborrow of `self` that ends when `resume` returns.

  Precedents are Effekt's capability passing and Jane Street's `handled_effect`. In `handled_effect`, handlers are passed as `local` capability arguments, and continuations are moded so that a double resume is "Only achievable with [Obj.magic_unique] or similar escape hatches". It is an implementation only, with no proofs.

#### A6. Discard (drop) semantics and resource safety

- **Statement for an affine core.** Every owned value is dropped at most once on every execution, including through continuations that are discarded or resumed more than once. Dropping a continuation **unwinds** its frames: destructors run in LIFO order and their loans end. Leaking a continuation is allowed only under A7's conditions, because forgetting `k` is not like forgetting a struct (§2, P2).
- **Statement for a linear core.** Every continuation that captures a must-use value is resumed or explicitly discontinued exactly once, and every owned value is dropped exactly once.
- **Interception policy, which you must specify.**
  - OCaml's `discontinue k e` "resumes the continuation k by raising the exception e in k" (OCaml manual). A handler *inside* `k` can catch the exception, keep running, and even perform again.
  - Rust's `catch_unwind` catches panics, and `std::thread::scope` relies on it to join its threads.

  The options are:
  - **(i) Catchable but must re-raise.** Cleanup code runs, and swallowing the unwind is an error. This is the C++ thread-cancellation convention: the libstdc++ manual's pattern catches `__cxxabiv1::__forced_unwind` and rethrows it.
  - **(ii) An uncatchable forced unwind that runs only destructors.** Cleanup based on `catch_unwind`, such as `std::thread::scope`'s join, then silently does not run, so libraries like it would have to be rewritten with drop guards.
  - **(iii) Interceptable,** but the continuation that intercepted it becomes linear again, so the obligation to resume or discard comes back.
- **Invariant shape.** Voigt et al. 2025, Thm 3.6: "If ActiveOpen(M) and InactiveClosed(M) and M → M′, then ActiveOpen(M′) and InactiveClosed(M′)". Your analogue: a value is dropped only when its owning frame is popped or unwound, and it is unreachable afterwards.
- **Why it matters.** RAII guards, scoped threads and every "the borrow ends when the guard drops" API assume a drop discipline. Existing languages do not enforce one:
  - OCaml 5 requires each continuation to be continued or discontinued, but does not check this statically.
  - WasmFX relies on the programmer calling `resume_throw`.
  - For Koka's deep finalization, Voigt et al. report that the authors "conjecture but do not prove that all finalizers are executed".
  - The Koka book makes it the programmer's responsibility to resume or finalize first-class resumptions.
- **Who has it.**
  - Voigt et al. 2025 give paper proofs for System Ξ↬. Note their own caveat: "These invariants are not statically checked, but rather represent a set of best practices."
  - Ahman & Bauer 2020 (runners): a denotational guarantee of linear resource use and that finalization runs.
  - Congard, Munch-Maccagnoni & Douence 2026: a resource CBPV with exceptions and destructors (paper).
  - Fowler et al. 2019 (EGV): session endpoints held by a discarded continuation are cancelled.
- **Proof cost.**
  - Low for at-most-once plus unwinding. It follows from A3 once "discard" is defined as "drop of the continuation value".
  - High for exactly-once. Affect lists "a linear (instead of affine) version of Affect with a 'discontinue' operation for unused continuations" as future work.
- **Borrow interaction.**
  - The loans held by `k`'s frames stay live until `k` is resumed and finishes, or is dropped. Dropping must end them, by unwinding.
  - If your core aborts on panic instead of unwinding, then abortive operations and discards introduce unwinding, and your proof needs drop-on-unwind.
  - If your `&mut` reasoning uses prophecies (RustHornBelt), a dropped continuation must still resolve its prophecies. That interaction has not been studied (conjecture).

#### A7. Semantic conservativity: proofs that assume well-bracketed control still hold

- **Statement (target).** It has three parts:
  - A library or `unsafe` abstraction that was proved sound against well-bracketed contexts stays sound when its callbacks are restricted to operation classes that preserve well-bracketing.
  - A library that relies on well-bracketing can state this in its type, for example with an effect bound that excludes the capturing classes.
  - A continuation that captures such a library's frames is never dropped without unwinding and never forgotten.
- **Why it matters.** The leak safety of your core calculus does not imply that libraries proved RustBelt-style remain sound. The breakages are detailed in §2 P2. In summary:
  - `std::thread::scope` runs its body under `catch_unwind` and joins the threads afterwards.
  - `replace_with` and `take_mut`.
  - `Pin`'s drop guarantee.
  - `GhostCell` under multi-shot resumption.
  - VAE-style private transitions under one-shot re-entry. The "very awkward example" (VAE) is a closure that temporarily resets private state around callbacks.
- **Who has it.** Nobody proves it. The relevant tools are:
  - **Dreyer, Neis & Birkedal 2010** catalogue exactly which reasoning principles control effects break. With call/cc, "the private and public transition relations must be collapsed into one, and consequently we must disallow inconsistent states", because "every time we pass control to the context may be the last!". Exceptions, by contrast, cause a "well-bracketed" kind of control effect and do not restrict their model.
  - **Timany & Birkedal 2019** (Coq/Iris): context-local weakest preconditions recover the bind rule for the fragment of the program that has no non-local control.
  - **Timany, Guéneau & Birkedal 2024** (Coq/Iris): a well-bracketed program logic that satisfies every Iris HeapLang rule "except the fork rule". The authors *conjecture* that it extends to innocuous uses of call/cc and of handlers, using protocol-style markers.
  - **Stepanenko et al. 2025** (Rocq): context-dependent effects added as a conservative extension at the level of the program logic.
  - **Blaze** (Rocq/Iris): relational proofs that a handler-based implementation refines a well-bracketed one, one library at a time.
- **Proof cost.** High, and an open problem. A realistic first theorem: libraries whose callbacks perform only tail-resumptive or abortive-unwinding operations keep their proofs. A plausible route is to simulate such handlers by calls plus exceptions (synthesis).
- **Borrow interaction** (synthesis, following the research pass).
  - In RustBelt, a call borrows a fraction `[κ]_q` of a lifetime token and returns it when it returns.
  - If a `perform` suspends while holding `[κ]_q`, and the handler sits inside `κ`'s scope, then discarding or leaking `k` loses that fraction. The caller can never end `κ`, so the typing rule for calls becomes unprovable.
  - Consequences: protocols must transfer lifetime tokens explicitly, and a handler may discard `k` only if the handler is installed outside every lifetime `k` borrows from, or if discarding unwinds.
  - Yarrow's "temporary revocation for one-shot effects and permanent revocation for multi-shot effects" is the published analogue for regions.

### 1.4 Tier B: strongly desirable

**B1. Abstraction safety (no accidental handling) and effect encapsulation.**
- **Statement.** Zhang & Myers 2019: it should be "impossible for higher-order, effect-polymorphic code to accidentally handle effects raised by functions passed in". Formally, you want a logical relation that is sound for contextual refinement and satisfies the fundamental property. A corollary: two implementations that differ only in encapsulated internal effects are contextually equivalent.
- **Why it matters.** Borrow checking reasons about one function at a time. With dynamically scoped handlers, an intermediate handler you cannot see can capture a continuation that contains a callee's private `&mut` loans. Xie et al.'s `opevil` example shows such a handler changing the result of `op1`.
- **Who has it.**
  - Zhang & Myers: about 4,000 lines of Coq 8.7 for the language plus about 4,200 lines for the logical relations, built on IxFree. In their Coq version, the types and effects attached to a label must be closed.
  - Zhang, Salvaneschi & Myers 2020 (Coq).
  - Biernacki et al. 2018 (Coq), 2019 (paper only; no Coq development is linked from the author page) and 2020 (Coq).
  - Effekt and System C have it by construction, but System C's Coq development proves soundness, not parametricity.
- **Proof cost.** High. Build the logical relation once and reuse it for B3.
- **Borrow interaction.** This is the analogue of ownership encapsulation. A fresh handler instance behaves like a fresh lifetime, and masking an effect behaves like a lifetime ending. Compare Lucassen & Gifford's effect masking (1988) and the mechanized `runST` encapsulation of Timany et al. 2018 (Coq/Iris).

**B2. Polymorphism that stays sound with state, multiplicities and lifetimes.** There are three separate issues here.
1. **References and let-polymorphism.** This is the classic value restriction, and it is independent of handlers. Rust-style generics, which appear only on items and never let-generalize effectful expressions, already avoid it. Affect likewise restricts polymorphism to values, "akin to the value restriction". Keep that.
2. **Polymorphic operations and polymorphic type assignment.**
   - Sekiyama, Tsukada & Igarashi 2020: "The naive combination of polymorphic effects and polymorphic type assignment has been well known to break type safety."
   - The fixes are the value restriction, or their **signature restriction**: `∀α. A ↪ B` is safe if `α` occurs only negatively or strictly positively in `A`, and only positively in `B`.
   - Kammar & Pretnar 2017 (Twelf) show that with monomorphic operation signatures, no value restriction is needed.
   - The canonical counterexample resumes the continuation twice, at different instantiations (per the research pass's reading of the paper body). So one-shot-only polymorphic operations plausibly avoid the problem, but this has not been stated as a theorem (unverified).
3. **The borrow analogue (open problem).** Take an operation signature that is lifetime-polymorphic, such as `op<'a>(…) -> &'a U`, or whose result has a higher-ranked type such as `for<'b> Fn(&'b T) -> &'b T`.
   - A multi-shot handler can resume such an operation at different lifetime instantiations.
   - Because lifetimes are erased at runtime, the failure is a dangling reference rather than a stuck term.
   - A conjectured sufficient condition is the same polarity restriction applied to lifetime binders.
   - A safe default is to make lifetime-polymorphic operations one-shot (synthesis; I found no paper on this).

**Multiplicity polymorphism.** Three existing systems handle it:
- Affect's mode polymorphism, using `!` and `¡`.
- Tang et al.'s Q°eff: qualified types with complete inference.
- Brachthäuser & Leijen, MSR-TR-2023-42, "Qualified Effect Types — Taming Control-Flow through Linear Effect Handlers".

Without multiplicity polymorphism, `map` and iterators need one copy per multiplicity or must assume the worst case. Fecher calls the propagation of such constraints "a big hit to the usability of effects in this scheme since these constraints would have to be manually specified".

**B3. Relational reasoning and optimization soundness.**
- **Statement.** A logical relation or bisimulation that is sound for contextual equivalence, plus an explicit list of the program transformations that remain valid across a `perform` in each control class.
- **Why it matters.**
  - Affect: "The key rule that is broken is that every code block entered is exited at most once". The paper gives a constant-propagation example around `do choose () && !r` whose result changes under multi-shot resumption.
  - Hazel: "if a continuation can be called twice, then a code block can be entered once and exited twice".
  - Optimizations that exploit `&mut` non-aliasing need the same at-most-once guarantee across a suspension.
- **Who has it.**
  - Biernacki et al. 2018 and 2020 (Coq).
  - Blaze (Rocq/Iris), whose related programs need not have corresponding handlers.
  - Sieczkowski, Pyzik & Biernacki 2023: a reduction theory.
  - Kammar & Plotkin 2012: soundness of effect-dependent optimizations.
  - Plotkin & Pretnar 2013: handlers as models of equational theories. Practical languages drop the equations.
- **Proof cost.** High. For v1, prove only the one-shot "exited at most once" property, which falls out of A3.

**B4. Ownership specifications for operations (protocols).**
- **Statement.** Each operation's specification says which ownership and loans flow to the handler and what flows back at `resume`, and a frame rule holds across `perform`.
- **Who has it.**
  - Hazel: for one-shot continuations, the bind and frame rules stay essentially unchanged.
  - TES: effect rows act as permissions, with dynamically allocated labels.
  - Maze (de Vilhena's thesis): with multi-shot continuations the frame rule is unsound, and only a restricted frame rule survives.
  - Iris-WasmFX.
- **When you need it.** To verify handler libraries such as schedulers and generators. A5's operation signatures are the type-level shadow of these specifications.

**B5. Conservative extension and coherent subsumption.**
- **Statement.** Effect-free programs typecheck unchanged with the empty effect and behave the same. Effect subsumption is coherent: a program's meaning does not depend on which derivation was used. Elaborating to explicit coercions is the preferred way to get this.
- **Who has it.** ExEff (Abella), and Biernacki & Polesiuk 2018 (coherence via logical relations, Coq).
- **Borrow interaction.** If effects are capture sets of lifetimes, effect subsumption is the lifetime subtyping you already have. Reuse it. A second subtyping relation would complicate the inversion lemmas in your mechanization.

### 1.5 Tier C: operational properties

**C1. Every operation declares a control class: `fn`, `abort`, `once` or `many`.**
- **Who has it.** Koka (`fun`, `ctl`, `final ctl`), Affect, Tang et al., and Brachthäuser & Leijen's tech report.
- **Role.** It is not a theorem in itself; it parameterizes A3 to A7.
- **Tail-resumptive operations are calls.** Xie et al. 2020 run them in place "at a cost similar to a virtual method call". The clause runs in the **handler's** context, not the perform site's: Koka "calls it directly as a regular function (except with an adjusted evidence vector for its context)". Two consequences follow:
  - The clause's own effects go to handlers outside its handler.
  - The clause's footprint, which is the handler's state, must not conflict with loans live at the perform site (A5).

  These are the ordinary rules for calling a closure that owns `&mut` state.
- **Abortive operations** need only the unwinding rules that panics already need.
- **Only the capturing classes** (`once` and `many`) need the new machinery of A3 to A7, and the checker can pick the rule at each call site.

**C2. Suspended frames keep stable addresses.**
- **Who has it.**
  - libmprompt keeps stacks that are never moved.
  - libseff rejects stack copying because C has pointers into the stack.
  - Rust has `Pin`.
- **Why OCaml 5 is not a precedent.** OCaml 5 grows fiber stacks on demand and moves them, which works because "OCaml does not generate pointers into the stack" (Sivaramakrishnan et al. 2021).
- **Borrow interaction.** This choice decides which borrows of locals may stay live across a `perform`.
  - rustc forbids borrows of a coroutine's own locals across `yield` in movable coroutines (error E0626) and allows them in pinned, static ones.
  - Multi-shot resumption copies frames, and copying breaks pointers into those frames. Muhcu et al. 2025 add an indirection layer, but per Yarrow it works only "as long as two continuations never capture the same stack segment".

**C3. Unwinding is fully specified.**
- **What to specify.**
  - destructor order through captured frames;
  - what happens when a destructor performs an effect or panics during a discard;
  - whether dropping `k` can itself suspend;
  - the interception policy from A6.
- **Who has it.** Voigt et al. (control effects inside pre- and postludes are well-defined), OCaml's `discontinue`, WasmFX's `resume_throw`, and Leijen 2018.
- **Production data point: Kotlin.**
  - Cancellation is delivered as a `CancellationException` at suspension points.
  - Suspending inside `finally` after cancellation requires `withContext(NonCancellable)`.
  - The lesson: cleanup code that itself needs effects must run with cancellation masked.

**C4. You pay only for what you use.**
- **Statement.**
  - Code that performs nothing pays nothing.
  - Tail-resumptive operations cost about a call.
  - Aborts get zero-overhead unwinding.
  - Statically known handlers are inlined.
- **Who has it.**
  - Ma et al. 2025: zero-overhead lexical handlers for exceptional (non-resuming) effects, with a paper proof that compilation preserves semantics.
  - Lexa (Ma et al. 2024): lexical handlers compiled to stack switching, with a simulation proof and a Racket implementation of the formalism.
  - Schuster et al. 2020: capability-passing compilation.
  - Xie et al. 2020: handler lookup at a constant offset in the evidence vector.
  - Xie & Leijen 2021.
- **Borrow interaction.** Lexical handlers give each operation a statically known handler, and monomorphizing per capability fits a Rust-like compiler.

**C5. Continuations cross threads only when safe.**
- **Rule.** Derive `Send` for `k` from its witness. For rustc futures, the witness "simply contains all locals live across suspend points".
- **Precedents.**
  - Ante: "In order to spawn a new thread to call `resume` we'd need to require a reference to the closure environment is `Send`".
  - OxCaml's portability and contention modes (Georges et al. 2025, Iris/Rocq).
- **Status.** A formal treatment for handler calculi is open.

**C6. Some frames and values can never be captured.**
- **What to forbid.** Suspension inside:
  - FFI frames;
  - destructors;
  - regions where a lock is held;
  - `unsafe` blocks that rely on invariants;
  - closures passed to APIs that need well-bracketed control (A7).
- **Precedents.**
  - Effect exclusion (Lutze et al. 2023).
  - Capability classifiers (Pham et al. 2026, Lean 4).
  - GHC's delimited-continuation primops proposal, which restricts capture through certain frames (the exact rules are unverified).
  - The async analogue in Rust is clippy's `await_holding_lock`, `await_holding_refcell_ref` and the configurable `await_holding_invalid_type` lints.
- **Example.** "No suspension while a `MutexGuard` or `RefMut` is live" is exactly an effect-exclusion constraint.

**C7. The borrow checker treats `perform` as a terminator with three edges.** The edges go out (to the handler), resume (which writes the resume argument) and drop (cleanup). This is rustc's MIR `Yield { value, resume, resume_arg, drop }`. The liveness conditions are in §2 P4.

### 1.6 Tier D: ergonomics (trade these off openly)

- **D1. Effect polymorphism without annotating every arrow.**
  - Rows need an effect variable on every higher-order arrow. Effekt (second-class blocks), Met (modalities) and Frank/Unison (ambient abilities) avoid this.
  - With capability effects, a closure's effects are the capabilities it captures. So `fn map<F: FnMut(A) -> B>` is already effect-polymorphic through ordinary generics and lifetimes. What remains is multiplicity (B2) and `Send`.
  - For ambient effects such as logging, prefer operations that take `&self`, with interior mutability inside the handler, so that several closures can hold the capability at once.
- **D2. Inference.** Options:
  - principal inference over scoped rows (Leijen 2017);
  - closed rows (Ikemori et al. 2022);
  - inferred control-flow linearity (Q°eff);
  - sound and complete effect inference with higher-rank polymorphism (Balik, Jędras & Polesiuk 2025, mechanized in Rocq);
  - associated effects for traits (Lutze & Madsen 2024).

  Keep effect indices first-order (capabilities, lifetimes, labels) so that effect inference can run inside lifetime inference.
- **D3. Subsume existing control features.** Async/await, generators, iterators, `?` and panics should all become library effects (Johnston 2024). Two cautionary tales:
  - OCaml shipped untyped effects and still has no typed effects (Scherer, OCaml Discuss 2026).
  - Rust's effect generics are a retrofit with combinatorial cost (Wuyts 2023, and the keyword-generics initiative).
- **D4. Errors phrased as borrow errors.** For example: "cannot resume `k` twice: it captures `&mut v` (borrowed at line 12)".

### 1.7 Which of your existing borrow lemmas survive (synthesis)

This checklist maps each lemma your borrow proof already has to what each control class does to it.

| Existing lemma | `fn` (tail-resumptive) | `abort` (unwinds) | `once` | `many` |
|---|---|---|---|---|
| Value substitution | Reuse | Reuse | Reuse; add substituting the resume value into a captured context (T1) | As `once`, plus contraction: the captured context must be duplicable |
| Weakening / frame | Reuse | Reuse | Reuse (Hazel keeps frame and bind for one-shot) | Breaks in general; Maze keeps only a restricted frame rule |
| Store typing is monotone (`Σ ⊑ Σ'`) | Reuse; add capability values | Reuse | Generalize: `Σ` types continuations with their loan set, one-shot flag and lifetime bound | As `once`, without the flag |
| Context decomposition | Reuse | Reuse; unwinding pops `E` frame by frame | Generalize to the capture lemma: `Λ = Λ_E ⊎ Λ_rest`, and `Λ_E` moves into `k` | Capture lemma at ω: `Λ_E` must be duplicable |
| Loan splitting for sequencing | Reuse | Reuse | Generalize to a three-way split: `k`, handler, values in transit | As `once`; `Λ_E` holds no `&mut` and no owned non-`Copy` values |
| Outlives transitivity / region subtyping | Reuse; `&'h H` is an ordinary reference | Reuse | Reuse for `Cont<'k>` bounds | Reuse; captured regions must strictly outlive the handler (Yarrow) |
| Stack discipline ("a lifetime ends when its frame pops") | Reuse | Reuse (unwinding is LIFO) | **Breaks**: a frame can be suspended (alive but not running) while outer code runs. Restate as "ends when its frame is popped, unwound or revoked" | **Breaks further**: a frame can be exited more than once |
| Each owned value dropped once | Reuse | Reuse if your core already unwinds on panic; otherwise add drop-on-unwind | Generalize: `drop(k)` means unwind; `forget(k)` only if `k: 'static` | Captured owned values must be `Clone` (and copied), or are forbidden |
| NLL liveness | Reuse (`perform` is a call edge) | Reuse (as for panics) | Generalize: three edges; loans in the witness stay live across the suspension | **Breaks** single-pass checking: the resume edge is a back-edge, so you need a fixed point (Oxide's T-While) or a join (Aeneas) |
| Exclusivity | Reuse via the reborrow encoding (A5) | Reuse | Generalize: count suspended and in-transit loans (T5) | **Breaks** for any `&mut` in the witness; only shared loans are allowed |
| Semantic call rule (lifetime-token fraction returned on return) | Reuse | Reuse, with unwinding | Generalize: tokens move through protocols and are owned by `k` | Tokens cannot be duplicated, so only persistent facts may flow into `k` |
| Library proofs that assume well-bracketed contexts | Reuse | Reuse if the library is unwind-safe (exceptions are well-bracketed; Rust libraries already are, because panics unwind) | **At risk**: private transitions under re-entry, and APIs sensitive to leaks or aborts (A7) | **Breaks further**: APIs that rely on uniqueness (`GhostCell` tokens, `replace_with`) |

### 1.8 Design axes and recommendations

| Axis | Options | Recommendation | Why |
|---|---|---|---|
| Effect representation | Rows (Koka, Links); sets (Eff, Flix); capabilities with capture sets (Effekt, Scala); modal (Met) | Capabilities typed with your lifetime sort. Modal if your core is already mode-based | Effect safety becomes an outlives check (A2, A4); capture sets play the role of loan sets; no second sort of variable. Tang & Lindley 2026 show that rows and capabilities both encode into modal effects |
| Handler binding | Dynamic; lexical | Lexical | Abstraction safety by construction (B1); each operation's handler is known statically (C4); a handler's extent is a lifetime |
| Continuation multiplicity | One-shot only; declared per operation; multi-shot everywhere | One-shot by default; multi-shot opt-in per operation when the witness is duplicable; abortive as its own class | Rust's `Drop` is affine; Affect mechanizes this design; multi-shot over `&mut` is unsound (A3) |
| Discard | Leak; affine with unwinding; linear | Affine, and dropping means observable unwinding with a specified interception policy; `forget` only for `k: 'static`. Use linear continuations if your core has must-use types | A6, A7 |
| Regions where suspension is forbidden | None; effect-exclusion bounds | Provide bounds that exclude the capturing classes, so that APIs which need well-bracketed control can demand them | A7, C6 |
| `resume` | Second-class; first-class | Second-class by default; explicit boxing into `Cont<'k, …>` | A4 reduces to your existing escape analysis (System C; Osvald et al.) |
| Deep or shallow | Deep; shallow; parameterized | Deep, with parameterized handlers for state | Shallow handlers "do not resume under their own handler" (Xie et al. 2020); the three kinds are interdefinable (Hillerström 2021) |
| Named handlers or instances | Anonymous; named | Implicitly named: each `handle` introduces a fresh instance that behaves like a lifetime | Biernacki et al. 2020; Xie et al. 2022 |
| Algebraic vs scoped operations | Algebraic only; scoped or higher-order | Algebraic only in v1; keep borrow scopes, regions and RAII in the core | Scoped operations are not algebraic (Piróg et al. 2018); add λsc or hefty algebras later if needed |
| Effect subsumption | Row unification; subeffecting; capture-set subsumption | Reuse lifetime subtyping; elaborate anything else to explicit coercions | B5 |
| Borrow checking across `perform` | Treat as a call; three-edge terminator | Three edges. One-shot reuses coroutine borrow checking; multi-shot needs a fixed point at resume points | C7, §2 P4 |
| Runtime representation | Stackful and non-moving; stackless and pinned; CPS or evidence passing | Stackful and non-moving, with one-shot resumed in place; or stackless with a pinning typestate | C2 |
| Proof architecture | Semantic (Iris); syntactic | Match your borrow proof | Semantic: Hazel protocols plus one-shot ghost tokens (Affect, TES, Yarrow, Iris-WasmFX). Syntactic: System C's Coq development plus Tang et al.'s tagged semantics. RustBelt's lifetime logic combined with handler protocols is unpublished |

If you prefer rows because of their inference, use scoped rows (Koka-style, where duplicate labels are allowed) so that masking is sound (Yoshioka et al.'s condition 3). Then add named handlers, instance handlers or `mask` to recover abstraction safety.

### 1.9 The baseline design these choices add up to (synthesis)

1. `handle h { |cap| body }` lends `cap: &'h mut H` (or `&'h H`), where `'h` is fresh. A computation's effects are the capabilities it captures.
2. Operations are methods on the capability, with ordinary borrow-checked signatures. Clauses run once per operation, so they are typed like `FnMut` closures.
3. Each operation declares one of four classes: `fn` (the default), `abort`, `once` or `many`.
4. For `once` operations, `resume` is second-class and `FnOnce`. This matches Ante: "`resume` is by default a `FnOnce` unless otherwise specified". Calling `resume` hands `self` back to the continuation for the duration of the call.
5. Storing a continuation requires boxing it into `Cont<'k, A, R>`. Its auto-properties, such as `Send` and duplicability, are computed from the witness.
6. Dropping a continuation unwinds it, as `drop(future)` does in Rust. The unwind is visible to `catch_unwind`-style cleanup, which must re-raise it. `forget(k)` requires `k: 'static`.
7. APIs that rely on well-bracketed control take closures whose effect bound excludes `once` and `many`. The alternative is to make any continuation that captures their frames linear.
8. Handlers are deep. There are no scoped operations in v1.
9. One-shot continuations resume in place. A multi-shot resumption copies only frames that are duplicable, contain no borrows into themselves, and whose captured regions all outlive the handler.
10. Under polymorphism, two properties are tracked the way `Send` is:
    - "may perform a `many` operation", as an auto-trait-like property of closures and capabilities;
    - "this frame is duplicable", as a property of its witness.

    Violating them breaks memory safety, so they must be `unsafe` auto traits like `Send` and `Sync`, not advisory traits like `UnwindSafe`. The std docs describe `UnwindSafe` as "more of a 'speed bump'" that is "mostly an advisory", and say that "in the absence of `unsafe` code, a panic cannot lead to memory unsafety". Item 10 is the Rust-shaped version of Affect's two signatures for `g`.

### 1.10 Core theorem package and staging

```
T0 Effect algebra (Yoshioka et al. 2024, Def 5.1; + Def 7.1 if lift/mask; + Def 7.6 if dispatch erases effect type args)
   (1) ∀L. ¬((L)↑ < 0)      (2) (L)↑ < ε ∧ (L')↑ ⊙ ε' ∼ ε ∧ L ≠ L'  ⇒  (L)↑ < ε'

T1 Capture lemma (generalizes System C Lemma 4.6 and Tang et al. Thm 3.4(2))
   Σ;Λ ⊢ E[op v] : τ ! C,  op ∈ C,  op unhandled in E   ⇒
   ∃ Λ = Λ_E ⊎ Λ_rest with loans(E) ⊆ Λ_E such that Σ;Λ_E, y:B ⊢ E[y] : τ ! C,
   and mult(op) = ω ⇒ every value/loan in Λ_E is duplicable and no loan in Λ_E points into E

T2 Preservation
   Σ ⊢ ⟨σ;e⟩ : τ ! C ∧ ⟨σ;e⟩ → ⟨σ';e'⟩  ⇒  ∃Σ' ⊒ Σ. Σ' ⊢ ⟨σ';e'⟩ : τ ! C
   (Σ types each continuation with multiplicity, loan set, lifetime bound 'k)

T3 Progress + effect safety
   Σ ⊢ ⟨σ;e⟩ : τ ! C  ⇒  e ∈ Val ∨ ⟨σ;e⟩ → _ ∨ e = E[op v], op ∈ C, op ∉ handled(E)
   (resuming a flagged continuation is a stuck state)
   Corollary: C = ∅ ⇒ no unhandled operation / undelimited capability is reached

T4 Multiplicity / resource conservation (shape of Tang et al. Thm 3.6)
   tagged semantics: M →(S introduced, T eliminated) N ⇒ tags(M) ∪ S = tags(N) ∪ T;
   no step resumes a flagged continuation

T5 Borrow invariants with suspended frames: every reachable configuration satisfies
   Inv_borrow over (stack ∪ all reachable continuations):
   (i) exclusivity counting suspended and in-transit loans;
   (ii) every loan held by a live continuation has a live lender;
   (iii) no capability is invoked outside its handler's extent

T6 Discard
   (i) every owned value is dropped at most once   [linear core: exactly once]
   (ii) drop(cont_ι(E)) = unwind E: LIFO drops, loans end, cleanup frames observe it and must re-raise
   (iii) forget(k) is well-typed only if k : 'static
   (iv) a value is dropped only when its owning frame is popped or unwound (shape of Voigt et al. Thm 3.6)

T7 Conservativity (A7; target, open)
   for every library L proved sound against well-bracketed contexts:
   L remains sound in every context whose operations, as observable from L's callbacks, are in {fn, abort}

T8 (later) Abstraction safety: logical relation sound for contextual refinement + fundamental property
T9 (later) Elaboration: surface inference elaborates to the explicit core, preserving typing (ExEff shape)
```

**Order of work.** Each stage is a conservative extension of the one before.
1. **T0, then `fn` and `abort` only, with lexical capabilities.**
   - Prove T2, T3, T5(iii) and T6 for unwinding.
   - Attempt T7 for `{fn, abort}`. This is the stage where simulating handlers by calls plus exceptions is plausible.
   - Most of this reuses your borrow proof, because a capability is just a borrowed reference to a handler frame.
2. **`once` with second-class `resume` and deep handlers.** Prove T1, the one-shot half of T4, T5(i)–(ii) and T6. This is the core new work, and most bugs surface here (A5's rules a to c).
3. **Boxed, first-class continuations with lifetime bounds.** Extend T5(ii) and T6(iii).
4. **`many` as an opt-in.** Extend T1 and T4 to ω, with witness duplicability, no self-loans, and captured regions that outlive the handler.
5. **Effect and multiplicity polymorphism** (B2), including lifetime-polymorphic operations. Re-prove T1 under instantiation.
6. **A relational model** (B1, B3). On the Iris route, reuse the same model that gives adequacy: Affect's adequacy theorem yields both "called at most once" and "no unhandled effects".
7. **Surface inference** (T9).

**Test programs each stage must accept or reject correctly**

| # | Program | Expected | Source |
|---|---|---|---|
| 1 | A linear or owned value captured by a multi-shot continuation | Reject | Links bug (Tang et al.) |
| 2 | `region (let r = ref local 0 in do Foo r; !r)` | Accept if `Foo` is one-shot, reject if multi-shot | Yarrow |
| 3 | `g := λf x. f(); x` with a multi-shot `f` and an affine `x` | Reject | Affect §2.5 |
| 4 | `v.push(do choose())` with a multi-shot `choose` | Reject: the auto-ref `&mut v` (a two-phase borrow) is live across the `perform` | Illustration (synthesis) |
| 5 | Two `&mut` into handler state from the same handler | Reject | Ante |
| 6 | A handler clause writes a place that the suspended body has borrowed | Reject | A5(c) |
| 7 | A boxed continuation that captures `&x` is stored past the end of `x`'s frame | Reject | A4 |
| 8 | A continuation stored in a shared cell and read twice | Reject; moving it out with `replace` is allowed | Affect |
| 9 | An abort while guards are live | Each destructor runs exactly once, via unwinding | A6 |
| 10 | A higher-order function would accidentally handle its argument's effect | The effect tunnels through | Zhang & Myers |
| 11 | A resumption applied under a different handler | Reject, or impossible by construction | Xie et al. `opevil` |
| 12 | `thread::scope(\|s\| { s.spawn(\|\| read(&data)); perform Abort() })`, with the handler inside `data`'s owner dropping `k` | Accept only if dropping unwinds through `scope` (so the join runs), or reject through `scope`'s effect bound. Never "accept and free" | A7, §2 P2 |
| 13 | `forget(k)` where `k` holds a loan from a frame outside `k` | Reject (`k: 'static` required) | A7 |
| 14 | A frame inside `k` swallows the discard-unwind with `catch_unwind` | Defined by the interception policy: an error, or `k` becomes linear again | A6 |
| 15 | `op<'a>() -> fn(&'a T) -> &'a T` resumed twice by a multi-shot handler | Reject (polarity), or force one-shot | B2(3) |
| 16 | `RefCell::borrow_mut` held across a `perform` whose handler borrows the same cell again | A runtime panic, not undefined behavior. Lint it, as clippy's `await_holding_refcell_ref` does for async | §2.2 |
| 17 | A borrow of a local held across a `perform` in a movable, first-class continuation | Reject unless the continuation is pinned or non-moving | E0626 analogue |

### 1.11 Pitfalls

1. **Marking operations one-shot or multi-shot without enforcing the capturing condition.** The marking alone is not enough; this is the Links bug.
2. **Checking the condition only at `let`.** Application and binary operators sequence implicitly (Affect).
3. **Naive types for effect-polymorphic code.** Higher-order functions hide `perform` sites (Affect §2.5).
4. **Deep handler clauses that move out of their environment.** A deep clause runs once per operation.
5. **Continuations stored in ordinary mutable references.** Loading one twice duplicates it; use `Cell`-style move-out.
6. **"Leaking `k` is like `mem::forget`."** It is not (A7, §2 P2).
7. **Freeing a dropped continuation's stack without unwinding it.** This violates `Pin` and breaks scoped threads.
8. **Leaving interception of discard unspecified.** OCaml's `discontinue` can be caught, and `std::thread::scope` needs `catch_unwind` to see the unwind.
9. **Treating "never resumes" as a weaker form of "resumes once".** They are incomparable for must-use values.
10. **Unsound effect algebras.** Yoshioka et al.'s Thms 7.2 and 7.7, and their condition 1.
11. **Dynamic handlers combined with per-function borrow reasoning.** This allows accidental handling, as in `opevil`.
12. **Shallow handlers as the default.** Their resumptions leave the handler's context.
13. **Modeling borrow scopes or regions as effect operations.** They are scoped operations, not algebraic ones.
14. **Implementing multi-shot by copying stacks that contain pointers into themselves.** This is the libseff problem and the Yarrow problem. The indirection of Muhcu et al. fails when two continuations capture the same stack segment.
15. **Forgetting that a handler's own state can be aliased across operations.** Two `&mut` from one handler.
16. **Letting handler code touch the suspended computation's locals.** Yarrow treats this as undefined behavior.
17. **Polymorphic operations plus generalization, without a value or signature restriction.** The same applies to its lifetime analogue.
18. **Treating `perform` as a plain call in NLL when operations can be multi-shot.** The resume edge is a back-edge.
19. **Shipping the runtime first and the types later.** See the OCaml and Rust experience in D3.
20. **Assuming the Iris route composes with RustBelt for free.** No published development combines them.
21. **Conflating uniqueness with linearity.** Capturing a unique value makes a closure `once`; it does not make the closure unique.

---

## 2. Effects × borrows: problems and solutions (Q3)

**The law.** Several lines of work arrived at the same law independently: Tov & Pucella 2011, Tang et al. 2024, and the Hazel, Maze, Affect and Yarrow line in Iris. **The number of times a continuation may be used must be compatible with the substructural qualifiers of everything live across the `perform`.**
- A continuation that may run many times (ω) needs every captured value to be duplicable.
- A continuation that may be dropped (0) needs every captured value to be droppable. In an affine, Rust-like core it also needs a decision about whether destructors and borrow-end events run.
- A one-shot continuation may capture `&mut` and owned values.

**Caveats.**
- Koka (via Perceus reference counting, which drops the in-place reuse optimization once a value is shared) and Effekt (which backtracks local state) enforce the law dynamically, not statically.
- Maze keeps multi-shot reasoning sound by restricting the frame rule instead.
- In a Rust-like ecosystem the law is necessary but not sufficient, because aborting or leaking `k` also breaks well-bracketed control (P2).

### 2.1 The interaction problems and how each has been addressed

#### P1. Multi-shot resumption duplicates unique ownership (A3)

**Failure.** `let r = &mut v; perform Choose(); r.push(x)` is resumed twice.

**Strategies.**
- **Forbid multi-shot.**
  - OCaml 5 checks one-shot use at runtime.
  - WasmFX.
  - OxCaml: Yarrow reports that it does "not support multi-shot effect handlers".
  - Rust's compiler-generated coroutines.
  - Ante (`FnOnce` `resume` by default).
  - Kotlin.
  - Swift's yielding accessors.
- **Grade multiplicity and check a capture condition at each `perform`.** Tang et al. 2024 (paper; in Links); Affect (Coq/Iris); Tov & Pucella 2011 (paper).
- **Make duplication explicit.**
  - Ante lets an effect declare `resume` as `Fn` or `FnMut`, which then propagates `Clone`/`Copy` constraints.
  - rustc's unstable `coroutine_clone` lets non-static coroutines be cloned when every saved local is `Clone`. The MIR docs warn that `Yield` then "can return multiple times" (tracking issue #95360).
- **Dynamic uniqueness.** Koka with Perceus reuses memory in place only when a reference count shows the value is unshared, so resuming twice just bumps counts. Lean 4 works similarly (Ullrich & de Moura 2019). A static borrow calculus cannot use this escape hatch.
- **Backtrack handler-local state.** Effekt (Muhcu et al. 2025). This is an implementation only, with no type system or logic.

#### P2. Dropping or leaking a continuation: destructors, borrow ends, and libraries that assume well-bracketed control (A6, A7)

**Failure.** The handler never calls `k` (an abort, a timeout, a failed search branch) or stores it forever. Owned values in the suspended frames are never dropped, guards never run, and "borrow ends here" events never happen. Zero-shot is incomparable with one-shot.

**Concrete library breakages.** S1 is verified against the std source. S2 to S5 follow the research pass's analysis.

| # | Library | What breaks | Restoring condition |
|---|---|---|---|
| S1 | `std::thread::scope`: runs `catch_unwind(AssertUnwindSafe(\|\| f(&scope)))`, then parks until no threads are running | An abort that drops `k` without unwinding, or `forget(k)`, skips the join while spawned threads still borrow `'env` data, giving use-after-free or a data race. This is the 2015 `JoinGuard` leak with `k` playing the guard. If the lender is inside `k` and `k`'s fiber memory leaks forever, memory stays valid | Discarding unwinds, visibly to `catch_unwind`; `forget(k)` only for `k: 'static`; or `scope`'s closure bound excludes capturing classes; or `k` is linear |
| S2 | `replace_with` / `take_mut` | Soundness rests on "the closure returns, or unwinds through our guard". A non-panic abort without unwinding leaves `*dest` moved out (double drop). `forget(k)` ends `&'a mut` statically. Multi-shot writes back twice | Abort means unwinding (the guard runs and takes its abort or default path); `forget` only for `'static`; no multi-shot (the witness holds a `&mut`) |
| S3 | `Pin` (drop guarantee: pinned memory may not be invalidated or reused before its destructor runs, though leaking it forever is allowed) | Freeing a dropped `k`'s fiber without running destructors; multi-shot copying relocates `!Unpin` values; growing stacks by copying moves pinned data | Dropping unwinds; forgetting leaks the storage; stacks never move; multi-shot only for `Unpin` witnesses |
| S4 | `GhostCell` (Yanovski et al. 2021; mechanized in Coq on RustBelt) | One-shot is fine: the token moves with `k`. Multi-shot duplicates `GhostToken<'brand>`, giving two live `&mut T` | The capturing condition (the token is affine). The paper itself does not discuss handlers |
| S5 | VAE-style private transitions (temporarily reset state, call `f`, restore) | A first-class one-shot `k`: the handler re-enters the closure, which resets the state, then resumes the old `k` partway through the transition. This is the same interleaving as Timany et al.'s concurrency counterexample and Dreyer et al.'s call/cc example | Restrict callbacks to `fn`/`abort`; context-local reasoning (Timany & Birkedal 2019); make non-reentrancy expressible (an `FnMut` receiver captured in `k` already makes the borrow checker reject re-entry) |

**Strategies in the literature.**
- **Affine continuations, with leaking allowed.** Affect's one-shot continuations are affine and need no `discontinue`. This is memory-safe for the core calculus but not for libraries that depend on well-bracketed control (S1–S3). Rust has already run this experiment:
  - RFC 1066: "It has never been a guarantee of Rust that destructors for a type will run, and this aspect was overlooked with the thread::scoped API" (see also Desires 2015).
  - without.boats' "scoped task trilemma": because futures (one-shot continuations) can be forgotten, a sound API can have at most two of concurrency, parallelism and borrowing.
  - The `async-scoped` crate calls its non-blocking scoped API "inherently unsafe".
- **Dropping means unwinding.**
  - OCaml's `discontinue` (catchable).
  - Rust's "drop the future = cancel", which runs the future's drop glue.
  - EGV, which cancels the session endpoints in a discarded continuation (Fowler et al. 2019).
- **Dynamic wind** (Voigt et al. 2025).
  - Suspend clauses run during capture, "since we cannot be sure whether the continuation will be discarded or resumed".
  - Acquiring and releasing resources stays well-bracketed even with unrestricted continuations (paper proofs).
  - Finalizing eagerly at suspension sidesteps interception, but for obligations that cannot be re-acquired (such as running threads) it degenerates to blocking.
- **Linear, must-resume continuations.**
  - Future work for both Affect and Voigt et al.
  - Idris 2's `App1`: "linear programs can never throw".
  - Swift's yielding accessors are always resumed, even when the caller throws.
- **Prophecy-based verification (conjecture).** In RustHornBelt each `&mut` resolves its prophecy exactly once, so dropped or duplicated continuations plausibly break prophecy completeness.

#### P3. Can code inside `k` intercept the discard? (A6)

- OCaml: `discontinue k e` behaves as `k (λx. raise e)`, so a `try`/`with` inside `k` can catch it and continue (Sivaramakrishnan et al. 2021). The paper's suggested leak cleanup is `Gc.finalise (fun k -> try ignore (discontinue k Unwind) with _ -> ())`.
- Rust: `catch_unwind` catches panics, and `std::thread::scope` *needs* it to catch the discard so that the join runs. So making the discard uncatchable conflicts with an existing std implementation.
- The options are (i) catchable but must re-raise, (ii) a forced unwind that runs only destructors, plus rewriting such libraries with drop guards, or (iii) interceptable, with the continuation becoming linear again (A6).
- Whether Koka's finalization exception can be caught by user code is unverified.

#### P4. Flow-sensitive borrow checking across `perform` (C7)

**Production precedent: rustc coroutines.**
- MIR has a `Yield { value, resume, resume_arg, drop }` terminator.
- E0626 ("borrow may still be in use when coroutine yields") fires only in movable coroutines, and only for borrows of the coroutine's own locals. Borrows of upvars or external data may cross a yield.
- The coroutine transform saves the locals that are live across suspension points. The saved set is computed from storage-liveness, borrowed-locals and liveness analyses, and the same witness determines auto traits such as `Send`.
- The drop shim drops the values in scope at the last suspension point.

**Theory.**
- NLL (RFC 2094): a lifetime contains every point at which a value whose type mentions it may later be used.
- Polonius: origins are sets of loans. I found no published soundness proof.
- Aeneas/LLBC (Ho, Fromherz & Protzenko, ICFP 2024; paper proof): sound borrow checking via a symbolic semantics, with a join of borrow states at control-flow merges (for loops) and region abstractions for calls.
- Oxide: `T-While` requires the loop body to map the typing context Γ2 back to Γ2, a fixed point.
- Kobayashi & Kameyama 2025: one-shot handlers and one-shot delimited control "can be macro-expressed by asymmetric coroutines, but not vice versa". Rust's coroutine borrow checking is therefore a sufficient template for one-shot handlers. Only multi-shot needs new theory.

**Liveness conditions** (synthesis, following the research pass). Write `p` for the `perform` point, `p'` for the resume point, and `W(p)` for the witness.
- **L1 (capture).** `k`'s type mentions every origin in `W(p)`, and `'k ⊆ ⋂ origins(W(p))`.
- **L2 (self-loans).** A loan into a frame captured by `k` requires that frame to be immovable. This is the E0626 rule.
- **L3 (handler interference).** `perform` is a call whose footprint is the handler's environment plus the operation's arguments. Conflicting loans must be dead at `p` (A5).
- **L4 (drop edge).** The context at `p` must be well-typed along the drop path. A linear continuation has no drop edge.
- **M1 (multi-shot fixed point).** The borrow and initialization state at `p'` is a loop invariant: the continuation never moves out of a place in `W(p)`.
- **M2 (duplication).** `W(p)` contains no `&mut` and no affine owned value. Shared loans are allowed, but their origins span every resumption.
- **M3 (no self-loans at all).** A copied frame with internal pointers would alias the original.
- **M4 (regions).** Captured regions must strictly outlive the handler (Yarrow).

**Status.** There is no formalization of NLL or Polonius with suspension, and no proven join for multi-shot resume points. Effect polymorphism that hides multiplicity and footprint also defeats flow-sensitive checking at call sites unless rows carry that information (P12).

#### P5. A continuation outlives the borrows it captured (A4)

- **Second-class continuations and capabilities.** Effekt (System Ξ); Osvald et al. 2016 (Coq).
- **Boxes with capture sets.**
  - System C (Coq).
  - CC<:□ (Capturing Types, paper proofs), mechanized in Coq by Fourment & Xu 2023.
  - Capless (Lean 4).
- **Reachability types.** Wei et al. 2024 (Coq).
- **Loan sets on the continuation type.** This is the natural extension point for Oxide's provenances. Ante ties the borrows passed as arguments to `resume`.
- **Gap.** No published calculus does this with flow-sensitive loans in the style of NLL or Polonius.

#### P6. A capability outlives its handler (effect safety meets lifetimes) (A2, A4)

- **Rows** (Koka, Links, Flix): principal inference, but rows say nothing about lifetimes.
- **Scoped, second-class capabilities** (Effekt; Scala capture checking), with Müller et al.'s 2023 translation into regions as formal evidence that a handler's scope is a region.
- **Named handlers with rank-2 scoping** (Xie et al. 2022).
- **Effects as modalities** (Met, OOPSLA 2025); Tang & Lindley 2026 encode both rows and capabilities this way.

#### P7. The handler interferes with what the suspended computation has borrowed (A5)

**Failure.**
- The body holds `&mut self.buf` across `perform Log()`, and the handler mutates `self.buf`.
- Or two operations each return a `&mut` into the handler's state.

**Strategies.**
- Treat the handler capability as a borrow of the handler frame (Ante).
- Require disjoint footprints through separation-logic protocols (Hazel).
- Give state only `Cell`-like access: Affect models `Ref τ` as Rust's `&Cell<τ>`, and affine contents are moved out by replacing them.

`RefCell` borrows held across a `perform`, combined with a re-entrant handler, turn a static error into a runtime panic. Make that a deliberate design point (§2.2).

#### P8. Borrows passed through operations (A5 a/b)

- Tie argument borrows to `resume` (Ante).
- Scoped lending across exactly one yield:
  - Hylo subscripts.
  - Swift SE-0474 yielding accessors (yield exactly once; the code after the yield always runs, even if the caller throws).

  Neither language has user-defined handlers or a mechanized soundness proof.
- Protocol pre- and postconditions (Hazel, TES).

#### P9. Non-local control vs. the stack discipline that regions and lexical lifetimes rely on

- **Yarrow** (Rocq/Iris program logic):
  - temporary revocation for one-shot, permanent revocation for multi-shot;
  - using references into a captured fiber is undefined behavior;
  - a type system "using semantic typing" is future work.
- **Timany, Guéneau & Birkedal 2024**, which isolates what well-bracketed control buys.
- **Fluet, Morrisett & Ahmed 2006**: a region monad translated into linear region capabilities (λrgnUL), with safety mechanized in Twelf.
- **A cautionary data point.** Yarrow: in Flix, "The combination of regions and effect handlers is undefined behavior", citing personal communication with Magnus Madsen.

#### P10. Borrows into a captured frame, and whether frames can move (C2)

- **Stackless with pinning.** Rust's `Pin`. Jung 2018 gives a semi-formal pinned typestate. I found no mechanized semantics of `Pin` together with coroutines.
- **Stackful.**
  - OCaml 5 moves its fibers, which is safe only because it creates no pointers into the stack.
  - WasmFX, Lexa and libmprompt resume in place.
- **Copying plus an indirection layer** (Muhcu et al.). This is restricted to continuations that are not re-entrant.
- **OxCaml's `yielding` mode axis**, which "tracks whether a function is permitted to perform effects that will be handled in its parent stack". Local values default to yielding. It is documented, but has no published semantics.

#### P11. Sending continuations that capture borrows to another thread (C5)

- **Rust:** `Send` is computed from the witness.
- **Ante:** the closure environment must be `Send`.
- **OxCaml:** portability and contention modes (Georges et al. 2025, Iris/Rocq).
- **Swift:** region-based isolation and `sending` (SE-0414 and SE-0430, based on Milano, Turcotti & Myers, PLDI 2022).
- **Pony, Verona and Inko:** only isolated, immutable or unique values cross between actors.
- **Gap:** a formal treatment of `Send` together with lifetime-bounded captures.

#### P12. Effect polymorphism hides ownership constraints (B2)

- **Qualified types:** Q°eff.
- **Mode polymorphism:** Affect, and OxCaml's inferable modes.
- **Multiplicity polymorphism:** Linear Haskell; Linearly Qualified Types.
- **Contextual effect polymorphism:** Effekt.
- **Qualifier polymorphism:** Lee et al. 2024 (mechanization status uncertain).
- **Lifetime-polymorphic operation signatures under multi-shot:** see B2(3).
- **Rows must carry multiplicity and footprint** for P4's checks to work at call sites of effect-polymorphic functions. Otherwise callers must assume the worst case.

#### P13. Continuations stored in mutable state

- Read-by-replace (Affect).
- Use/kill effects that disable every alias, including aliases captured in closures (Capture Now, Consume Later; mechanized in Rocq; includes a use-once-continuations case study).

#### P14. Dynamic handler resolution breaks local borrow reasoning (B1)

- Tunneling: Zhang & Myers 2019, and Zhang, Salvaneschi & Myers 2020 (both Coq).
- Lexical or capability-passing handlers: Effekt, Lexa, Helium.

#### P15. Optimizations and aliasing models across suspension points

- Retags and protectors in Stacked Borrows and Tree Borrows assume that a function frame is active. What they mean for a suspended fiber is open.
- Tools that apply: Blaze (relational reasoning about handlers) and Simuliris (which mechanizes Stacked and Tree Borrows).

### 2.2 Design-detail checklist

The six items below are smaller design questions, raised in review (synthesis unless cited).
- **Drop check (`#[may_dangle]`).** Destructors in captured frames run when `k` is later dropped. Treat `Cont<'k, …>` as having a `Drop` impl that uses every captured lifetime (no `may_dangle`), so that drop check requires those lifetimes to be live at the drop point.
- **`RefCell`/`Cell` flags across `perform`.** Under re-entrant handlers they turn a static error into a runtime panic, which is safe but surprising. Either lint it (clippy's `await_holding_refcell_ref` is the async analogue) or allow an effect-exclusion bound on `RefMut`.
- **Variance.**
  - `Cont<'k, A, R>` should be covariant in `'k` and `R` and contravariant in `A`.
  - `&'h mut H` is invariant in `H`, so effect subsumption cannot change handler types. This is another reason to keep effect subtyping inside lifetime subtyping.
- **Trait objects and `dyn Fn`.**
  - The dynamic type must carry the capability set, the multiplicity class and `Send`, just as `dyn Fn() + Send + 'a` carries `Send` and a lifetime today. Otherwise every call through `dyn` must assume the worst case.
  - Monomorphizing capability-generic code per handler type risks code-size blowup. Capability-passing compilation (Schuster et al. 2020) is the dictionary-passing alternative.
- **Handler-owned state.** With deep or parameterized handlers, the handler's state is part of what a multi-shot resumption duplicates. Require the state to be `Clone`, or forbid `many` operations on such handlers. Muhcu et al. backtrack this state dynamically.
- **Specified evaluation order.** Two-phase borrows and capture sets both depend on it, as does Affect's implicit-sequencing lesson. An ANF- or MIR-like core makes it explicit.

### 2.3 Languages: how they combine ownership with effects or suspension

| Language | Ownership mechanism | Effects / suspension | Rule at the interface | Formal backing |
|---|---|---|---|---|
| **Rust** | Affine ownership, lifetimes, `&`/`&mut` | No user handlers. Compiler-generated, stackless, one-shot coroutines (async, `gen`). Keyword-generics initiative | Self-borrows across `yield` only in pinned coroutines (E0626); `gen` blocks forbid them (RFC 3513); dropping cancels; `Send` from the witness; `forget` is safe (RFC 1066), so borrowing scoped async tasks cannot be sound | RustBelt (Coq/Iris) and Oxide (paper) cover the core, not coroutines or `Pin` |
| **Ante** (prototype) | Rust-like ownership and borrows | Algebraic effects and handlers | `resume` is `FnOnce` by default, and `Fn`/`FnMut` can be declared; deep clauses may not move captured values; argument borrows tied to `resume`; functions using the same effect borrow from one handler; threads need a `Send` environment | None (design blog) |
| **Koka** | Perceus reference counting with in-place reuse; FP² fully-in-place fragment | Row-typed handlers: `fun`/`val` (tail-resumptive), `ctl` (multi-shot), `final ctl` | Multi-shot coexists with in-place update through the reuse check; `finally`/`initially` for resources | Perceus and FP² (paper) |
| **Effekt** | Second-class capabilities, boxes with capture sets, regions | Lexical capability-passing handlers, one-shot and multi-shot | Capabilities cannot escape; local state backtracked under multi-shot; dynamic wind | System C (Coq); Capabilities to Regions (paper); Dynamic Wind (paper); Muhcu et al. (implementation) |
| **OCaml 5** | GC, no ownership | Untyped handlers on stackful fibers | One-shot checked at runtime; `discontinue` (catchable); a dropped continuation leaks | Paper semantics; Osiris (Rocq/Iris) for a fragment with handlers |
| **OxCaml** + `handled_effect` | Modes: locality, uniqueness, affinity, contention, portability; `yielding` axis | Typed handlers passed as `local` capability arguments over OCaml 5 effects | Continuations are unique (a double resume needs `Obj.magic_unique`); multi-shot unsupported; local values default to yielding | Modes: ICFP 2024 (paper) and POPL 2025 (Iris/Rocq). No formalization of handlers with modes (per Yarrow) |
| **Flix** | Lexical regions with effect masking | Effects, effect exclusion, handlers | Regions combined with handlers is undefined behavior (Yarrow, citing Madsen) | Paper proofs for parts |
| **Links** | Linear session-typed channels | Row-typed handlers, multi-shot | Control-flow linearity retrofitted after a soundness bug | F°eff/Q°eff (paper) |
| **Scala 3** (capture checking, Gears) | Capture sets; separation checking | Effects as scoped capabilities; Gears' `Async` capability | Capabilities bounded by capture sets | CC<:□ (paper) and its Coq mechanization; Capless (Lean 4); Capybara (Lean 4, preprint); Classifying Capabilities (Lean 4) |
| **Swift** | Noncopyable types; `~Escapable` (SE-0446); `Span`; region isolation | async/await, actors, yielding accessors (SE-0474) | Escaping `Task` closures cannot capture `~Escapable` values; accessors yield exactly once and always resume, even on throw; `sending` gates crossing isolation | SE-0414 is based on Milano et al. (PLDI 2022); the rest is implementation |
| **Hylo** | Mutable value semantics; second-class references | Yield-once subscripts | References cannot be stored, so they cannot be captured | Paper formal core (Racordon et al., JOT 2022; IWACO 2023 borrow checking) |
| **Kotlin** | GC | `suspend` via CPS; structured concurrency | One-shot; cancellation is an exception at suspension points; cleanup that suspends needs `NonCancellable` | None |
| **Idris 2** | Quantitative types (0/1/ω) | `Control.App` | `App1`: "linear programs can never throw" | Paper metatheory for QTT |
| **Granule** | Linear base; graded modalities; fractional uniqueness | Graded monads; no user handlers found (unverified) | Effect and coeffect grading kept separate | Paper |
| **Pony / Verona** | Reference capabilities; regions and cowns | Run-to-completion behaviours / `when` | No suspension partway through a behaviour | Paper formal models |
| **Inko** | Single ownership with runtime borrow counts | Processes | Only `uni` and value types are sendable; dropping a value with live borrows panics | None |
| **Cyclone** | Lexical and dynamic regions, unique pointers | Exceptions; regions as effects | A region effect is the set of live regions | Paper |
| **ATS** | Linear viewtypes | Effect annotations on arrows (syntax unverified) | Linear values must be consumed; exceptions can leak them (unverified) | Paper (Chen & Xi 2005) |
| **Mojo** | Origins on references | `raises` (typed, value-based) and async | Errors are returns, so destructors run; how origins interact with suspension is undocumented | None |
| **Vale** | Generational references; planned regions | (Planned "pure" blocks act like effect masking) | n/a | None |
| **Unison** | None | Abilities, multi-shot | A handler may resume 0 to n times | None |
| **Helium** | None | Lexically scoped handlers, instances, abstract effects | A handler's extent is lexical | Paper; Coq for the logical relations (Biernacki et al. 2018, 2020) |
| **WasmFX** | None (low-level) | Typed, one-shot, stackful continuations | One-shot only; `resume_throw` | Spec plus reference interpreter (OOPSLA 2023); WasmFXCert type soundness in Rocq (PLDI 2026) |
| **Lexa** | None | Lexical handlers compiled to stack switching | Stack-disciplined handler frames | Paper simulation proofs; Racket implementation of the formalism |
| **Lean 4 / Roc** | Reference counting with inferred borrowed parameters | Monads | Destructive update only on unshared values | Paper (Ullrich & de Moura) |

### 2.4 Research calculi that sit directly on the interface

| Calculus | Ownership side | Effect side | Key rule | Proof |
|---|---|---|---|---|
| Affect (POPL 2025) | Affine types; `Ref τ` ≈ `&Cell<τ>` | One-shot and multi-shot effects in rows | Capturing condition; `!` and `¡` | Coq/Iris semantic typing, no admits |
| F°eff / Q°eff (POPL 2024) | Linear values | Row-typed handlers | Control-flow linearity | Paper |
| Tov & Pucella (OOPSLA 2011) | Generic substructural qualifiers | Generic control effects | Continuation qualifier bounded by the captured qualifiers (meet/join) | Paper |
| Yarrow (2026 preprint) | Lexical regions, stack references | One-shot and multi-shot handlers on fibers | Regions in protocols; temporary vs. permanent revocation | Rocq/Iris program logic; no type system |
| Hazel / TES / Maze | Separation-logic ownership | One-shot (Maze: multi-shot) | Protocols; Maze's restricted frame rule | Coq/Iris |
| System C (OOPSLA 2022) | Second-class capabilities, boxes with capture sets | Lexical handlers | Capability non-escape | Coq |
| Capless / Classifying Capabilities / Capybara | Capture sets; separation, consumption, freshness | Scoped capabilities; exception interception | Scope safety; handler coverage; data-race freedom | Lean 4 |
| Capture Now, Consume Later (preprint) | Reachability types with use/kill | Flow-sensitive effects | Moves as kill effects; use-once continuations | Rocq |
| λrgnUL (ESOP 2006) | Linear region capabilities | Region monad | Regions as linear capabilities | Twelf |
| Effects and Coeffects in CBPV (OOPSLA 2024) | Usage (coeffect) grades | Effect grades | Both in one judgment; no handlers | Coq |
| Mezzo (TOPLAS 2016) | Permissions, adoption/abandon | None | Closures that capture exclusive permissions are affine | Coq (core) |

### 2.5 The classic lineage: type-and-effect systems with regions and ownership

| Work | Contribution | What it gives your design |
|---|---|---|
| Lucassen & Gifford 1988 | Effect polymorphism, effect masking, effects used to justify parallelism | Mask effects on lifetimes that have ended |
| Talpin & Jouvelot 1994 | Principal inference of types, regions and effects; static effects over-approximate dynamic ones | The statement of effect soundness |
| Tofte & Talpin 1997 (syntactic proofs: Calcagno, Helsen & Thiemann 2002) | Dangling pointers are fine if no latent effect mentions a dead region | When `k` resumes, its latent effect must not mention an ended lifetime |
| Crary, Walker & Morrisett 1999 | Effects as capability sets; unique capabilities allow non-LIFO deallocation | Read effect rows as required loans |
| Cyclone (PLDI 2002) | Outlives constraints; `regions_of(α)` for abstract types | Operations polymorphic in a type that may hide borrows must account for them |
| Vault (2001); Adoption and Focus (2002) | Transformers from a pre-state key set to a post-state key set; "focus" is a scoped mutable borrow | Each clause must restore or transform the held capabilities on every path, including not resuming |
| Clarke & Drossopoulou 2002; Greenhouse & Boyland 1999 | Effect disjointness from an ownership hierarchy; abstract regions that stay stable under overriding | Trait effect signatures must not leak private places |
| Boyland 2003 | Fractional permissions | State effect footprints in the same permission algebra as loans |
| DPJ (OOPSLA 2009) | Region path lists; disjoint effects imply determinism; commutativity annotations | Aim for a theorem that disjoint effects commute |
| L3 (2005); Linear Regions (2006, Twelf) | Separating a pointer from its capability; a region monad compiles into linear capabilities | Effects over lifetimes can compile to capability passing in your core |
| Mezzo (Coq) | Closures that capture exclusive permissions are affine | The same rule applies to continuations |
| runST (Timany et al. 2018, Coq/Iris) | Masking local state proved as contextual equivalence | The right statement for encapsulation (B1) |
| Superficially Substructural Types (2012); Recovering Purity (2020) | Linear protocols at library level via semantic models; a comonad for "captures no capabilities" | Handlers definable as libraries over a semantic core; a "pure/shareable" mode |
| Coeffects for Sharing and Mutation (2022) | Aliasing is a *non-structural* coeffect | Do not re-encode your borrow calculus as per-variable grades |
| Reachability types (2021–2025; Coq/Rocq) | Separation for higher-order code; use/kill effects | The closest precedent for continuations that capture ownership |
| Degrees of Separation (2024); Capybara (2026, Lean 4) | Separation checking layered over capture checking | Opt-in separation on top of capability effects |

---

## 3. Formally proven effect systems (Q1)

**Main findings.**
- **No mechanized calculus combines Rust-style borrows (lifetime-indexed shared and mutable references) with effect handlers.** The closest pieces are:
  - Affect (Coq/Iris): affine continuations plus `Cell`-style references.
  - Yarrow (Rocq/Iris; preprint): regions with one-shot and multi-shot handlers.
  - Capture Now, Consume Later (Rocq; preprint): ownership transfer expressed as effects.
  - Capybara (Lean 4; preprint): separation and consumption over capabilities.
  - Classifying Capabilities (Lean 4): handles exceptions only.
- **Lean 4.** I found no general handler calculus with resumptions. Lean 4 does host:
  - capability calculi: Capless (scope safety), Classifying Capabilities (effect safety and handler coverage for exception interception) and Capybara;
  - Iris-Lean (HeapLang and MoSeL, but no Hazel-style handler logic);
  - ITree libraries.
- **Isabelle.** I found no mechanization of typed handlers in Isabelle or the AFP.
- **Scoped and higher-order operations.** Hefty Algebras (Agda) is the only mechanization I found. λsc and Structured Handling of Scoped Effects have paper proofs only.

### 3.1 Coq/Rocq with Iris (semantic typing, separation logic, logical relations)

| System | What is proven | Artifact | Year / venue | Link |
|---|---|---|---|---|
| **Hazel** (de Vilhena & Pottier) | Iris separation logic for an untyped calculus with deep and shallow handlers and state; protocols; one-shot continuations keep the bind and frame rules | gitlab.inria.fr/cambium/hazel; Zenodo snapshot 10.5281/zenodo.7371093 | POPL 2021 | https://doi.org/10.1145/3434314 |
| **Maze** (de Vilhena, PhD thesis, ch. 6) | Multi-shot continuations: the frame rule is unsound, a restricted frame rule survives; SAT solver and callcc case studies | Same repo | 2022 | https://devilhena-paulo.github.io/thesis/de-vilhena-thesis.pdf |
| **TES** (de Vilhena & Pottier) | Semantic type soundness for references, handlers and dynamic labels; rows act as permissions and disjointness | gitlab.inria.fr/cambium/tes | ESOP 2023 | https://link.springer.com/chapter/10.1007/978-3-031-30044-8_9 |
| **Affect** (van Rooij & Krebbers) | Semantic type safety for an OCaml-5-like language; one-shot vs. multi-shot; `Cell`-style references; every typing rule is an Iris lemma; no syntactic type datatype | github.com/ovanr/affect; Zenodo 10.5281/zenodo.14198790 | POPL 2025 | https://doi.org/10.1145/3704841 |
| **Blaze** (de Vilhena, van Collem, Wright, Krebbers) | Relational separation logic for handlers with state and concurrency; the related programs' handlers need not correspond | github.com/DeVilhena-Paulo/blaze | POPL 2026 | https://doi.org/10.1145/3776676 |
| **Yarrow** (Mathiasen, Timany, Birkedal) | Semantics, Yarrow Logic and case studies (checkpointing, async, LIFO structures) for handlers combined with lexical regions; "The Rocq mechanization accompanies the paper" | No public repo found | arXiv 2026 (preprint) | https://arxiv.org/abs/2607.15876 |
| **Iris-WasmFX / WasmFXCert** (Legoupil et al.) | Type soundness of WasmFX in Rocq (built on WasmCert), plus an Iris program logic; coroutine and generator case studies | Not located | PLDI 2026 | https://doi.org/10.1145/3808271 |
| **Osiris** (Seassau, Yoon, Madiot, Pottier) | Semantics of OLang (exceptions and handlers); Horus and Osiris program logics | gitlab.inria.fr/fpottier/osiris | ICFP 2025 | https://doi.org/10.1145/3747509 |
| **Guarded Interaction Trees** (Frumin, Timany, Birkedal) | Modular denotational semantics of higher-order effects; separation logic; adequacy | Coq/Iris | POPL 2024 | https://arxiv.org/abs/2307.08514 |
| Context-dependent effects in GITrees (Stepanenko et al.) | call/cc and shift/reset added conservatively: the reasoning rules for context-independent effects are unchanged | Rocq (per the research pass) | arXiv 2025 | https://arxiv.org/abs/2512.11577 |
| Program Logics à la Carte (Vistrup, Sammler, Jung) | Iris logics for ITrees, built from "logical effect handlers" | Coq; three axioms (K, functional choice, bisimulation-is-equality) | POPL 2025 | https://research.ralfj.de/papers/2025-popl-itree-program-logic.pdf |
| Well-bracketed control (Timany, Guéneau, Birkedal) | Ghost-stack logic for well-bracketed control; all HeapLang rules except fork | github.com/logsem/well-bracketed-logic | POPL 2024 | https://doi.org/10.1145/3632862 |
| Timany & Birkedal | Logical relations for a concurrent language with call/cc; context-local weakest preconditions | Coq/Iris | ICFP 2019 | https://doi.org/10.1145/3341709 |
| runST encapsulation (Timany et al.) | `runST` encapsulates state, proved as contextual equivalence | Coq/Iris | POPL 2018 | https://doi.org/10.1145/3158152 |
| Data Race Freedom à la Mode (Georges et al.) | OxCaml modes, contention and portability, with a semantic model; no handlers | Iris/Rocq | POPL 2025 | https://doi.org/10.1145/3704859 |
| GhostCell (Yanovski, Dang, Jung, Dreyer) | Branded permissions, as an extension of RustBelt (relevant to A7) | gitlab.mpi-sws.org/FP/ghostcell | ICFP 2021 | https://plv.mpi-sws.org/rustbelt/ghostcell/ |

### 3.2 Coq/Rocq without Iris

| System | What is proven | Artifact | Year / venue | Link |
|---|---|---|---|---|
| **System C** (Brachthäuser, Schuster, Lee, Boruch-Gruszecki) | Progress and preservation (`preservation_step`, `progress_step` in `Soundness.v`; the research pass found no admits); effect safety as Cor. 4.8 | github.com/se-tuebingen/oopsla-2022-artifact; Zenodo 10.5281/zenodo.5833713 | OOPSLA 2022 | https://doi.org/10.1145/3527320 |
| Second-class values (Osvald et al.) | Type soundness and lifetime properties | github.com/TiarkRompf/scala-escape (`coq/`) | OOPSLA 2016 | https://doi.org/10.1145/3022671.2984009 |
| Box calculus CC<:□ (Fourment & Xu) | Coq mechanization of the capture calculus (the TOPLAS 2023 paper had paper proofs) | On GitHub, per the paper | IWACO 2023 | https://arxiv.org/abs/2309.05362 |
| Handle with Care (Biernacki et al.) | Step-indexed biorthogonal logical relation for row-typed handlers with `lift` | bitbucket.org/pl-uwr/aleff-logrel | POPL 2018 | https://doi.org/10.1145/3158096 |
| Binders by Day, Labels by Night (Biernacki et al.) | Kripke logical relations for lexically scoped effect instances | bitbucket.org/pl-uwr/aleff-lex | POPL 2020 | https://doi.org/10.1145/3371116 |
| Typed equivalence of handlers and delimited control (Piróg et al.) | Type-preserving macro translations | pl-uwr.bitbucket.io/efftrans.zip | FSCD 2019 | https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2019.30 |
| Coherence of effect subtyping (Biernacki & Polesiuk) | Meaning is independent of the subtyping derivation | bitbucket.org/pl-uwr/coherence-logrel | LMCS 2018 | https://lmcs.episciences.org/4180 |
| **Tunneling** (Zhang & Myers) | Parametricity, contextual-refinement soundness, type safety | github.com/yizhouzhang/abseff-coq (Coq 8.7, IxFree) | POPL 2019 | https://doi.org/10.1145/3290318 |
| Handling bidirectional control flow (Zhang, Salvaneschi, Myers) | Parametricity and soundness, "fully mechanized in Coq" | github.com/yizhouzhang/olaf-coq | OOPSLA 2020 | https://doi.org/10.1145/3428207 |
| **Effects and Coeffects in CBPV** (Torczon et al.) | Graded effects plus coeffects; CBV and CBN translations; logical relations; no handlers | github.com/plclub/cbpv-effects-coeffects (Coq 8.19.2, Autosubst 2) | OOPSLA 2024 | https://doi.org/10.1145/3689750 |
| Capture Now, Consume Later (Deng et al.) | Effect soundness and preservation for use/kill effects | Rocq; no repo found | arXiv 2025 (preprint) | https://arxiv.org/abs/2510.08939 |
| Polymorphic Reachability Types (Wei et al.) | Soundness and preservation of separation | github.com/TiarkRompf/reachability | POPL 2024 | https://doi.org/10.1145/3632856 |
| Mezzo (Balabonski, Pottier, Protzenko) | Soundness and data-race freedom for Simple Mezzo | Coq | TOPLAS 2016 | https://doi.org/10.1145/2837022 |
| Interaction Trees (Xia et al.); Choice Trees (Chappe et al.) | Semantic frameworks; no typed effect-safety theorem | github.com/DeepSpec/InteractionTrees | POPL 2020; POPL 2023 | https://arxiv.org/abs/2211.06863 |
| Deciding not to Decide (Balik, Jędras, Polesiuk) | Sound and complete effect inference with higher-rank polymorphism | Rocq | arXiv 2025 (preprint) | https://arxiv.org/abs/2510.20532 |

### 3.3 Twelf

| System | What is proven | Artifact | Link |
|---|---|---|---|
| Bauer & Pretnar, An Effect System for Algebraic Effects and Handlers (LMCS 2014) | Effect safety (no unhandled operations) | github.com/matijapretnar/proofs | https://lmcs.episciences.org/1153 |
| Kammar & Pretnar, No Value Restriction Is Needed (JFP 2017) | Soundness of generalization when operation types are monomorphic | Same repo | https://arxiv.org/abs/1605.06938 |
| Fluet, Morrisett & Ahmed, Linear Regions Are All You Need (ESOP 2006) | Type safety of the substructural target calculus | Project page | https://www.cs.rit.edu/~mtf/research/substruct-regions/ |

### 3.4 Abella

| System | What is proven | Link |
|---|---|---|
| ExEff (Saleh et al., ESOP 2018) | Type safety of the explicit core with coercions; elaboration. The JFP 2020 extensions may be paper-only (unverified) | https://doi.org/10.1007/978-3-319-89884-1_12 |
| Forster, Kammar, Lindley & Pretnar (ICFP 2017; JFP 2019) | Macro-expressiveness among handlers, monadic reflection and delimited control, in CBPV calculi | https://doi.org/10.1145/3110257 |
| Polymorphic fine-grain CBV (unpublished) | Type safety | https://github.com/matijapretnar/proofs |

### 3.5 Agda

| System | What is proven | Link |
|---|---|---|
| AEff, asynchronous effects (Ahman & Pretnar, POPL 2021) | Preservation and progress | https://github.com/danelahman/aeff-agda |
| Higher-Order Asynchronous Effects (Ahman & Pretnar, LMCS; year unverified) | The same metatheory, extended | https://github.com/danelahman/higher-order-aeff-agda |
| Hefty Algebras (Bach Poulsen & van der Rest, POPL 2023) | Modular elaboration of higher-order (scoped) operations | https://doi.org/10.1145/3571255 |
| Algebraic Effects Meet Hoare Logic in Cubical Agda (Kidney, Yang, Wu, POPL 2024) | Free monads quotiented by equations; a Hoare logic generic in the effect | https://doi.org/10.1145/3632898 |
| When Programs Have to Watch Paint Dry (Ahman, FoSSaCS 2023) | Main results formalized, with stated gaps (some auxiliary lemmas, two presheaf laws) | https://github.com/danelahman/temporal-resources |
| Graded type theory (Abel, Danielsson, Eriksson, ICFP 2023) | Graded dependent types, generic in the modality structure | https://doi.org/10.1145/3607862 |

### 3.6 Idris

| System | What is proven | Link |
|---|---|---|
| System Ξ, Effects as Capabilities (Brachthäuser, Schuster, Ostermann, OOPSLA 2020) | Type system and semantics are intrinsically typed: preservation holds by indexing, and progress by a total step function. The translation proofs appear on paper (whether they are also mechanized is unresolved) | https://doi.org/10.1145/3428194 |

### 3.7 Lean 4

| System | What is proven | Link |
|---|---|---|
| System Capless (Xu, Bračevac, Pham, Odersky, OOPSLA 2025) | Type soundness and scope safety for capture tracking | https://doi.org/10.1145/3763112 (repo github.com/Linyxus/capless-lean) |
| Classifying Capabilities (Pham et al., OOPSLA 2026) | Type safety, effect safety and handler coverage for exception interception (big-step proof) | https://doi.org/10.1145/3839474 |
| System Capybara (Xu et al., arXiv 2026) | Semantic soundness; memory safety, immutability, data-race freedom | https://arxiv.org/abs/2607.09383 |
| Iris-Lean | Partial port of Iris (MoSeL, HeapLang); no handler logic | https://github.com/leanprover-community/iris-lean |
| Lean ITrees | Coinductive ITree libraries; no paper | https://github.com/mit-plv/lean4-itree |

### 3.8 Paper-only results that matter for the desiderata

| Result | Year | Link |
|---|---|---|
| Plotkin & Power: algebraic operations and generic effects | 2003 | https://doi.org/10.1023/A:1023064908962 |
| Plotkin & Pretnar: a logic for algebraic effects; handling algebraic effects | 2008; 2013 | https://doi.org/10.1109/LICS.2008.45 ; https://doi.org/10.2168/LMCS-9(4:23)2013 |
| Kammar & Plotkin: effect-dependent optimisations | 2012 | https://doi.org/10.1145/2103656.2103698 |
| Katsumata: parametric effect monads | 2014 | https://doi.org/10.1145/2535838.2535846 |
| Kammar, Lindley & Oury: Handlers in Action | 2013 | https://doi.org/10.1145/2500365.2500590 |
| Hillerström, Lindley & Atkey: generalised continuations | 2020 | https://doi.org/10.1017/S0956796820000040 |
| Leijen: row-typed effects in Koka | 2017 | https://doi.org/10.1145/3009837.3009872 |
| Xie et al.: Effect Handlers, Evidently; Xie & Leijen: generalized evidence passing | 2020; 2021 | https://doi.org/10.1145/3408981 ; https://doi.org/10.1145/3473576 |
| Biernacki et al.: Abstracting Algebraic Effects (no Coq development linked) | 2019 | https://doi.org/10.1145/3290319 |
| Tang, Hillerström, Lindley & Morris: Soundly Handling Linearity | 2024 | https://doi.org/10.1145/3632896 |
| Met (Tang et al.); Rows and Capabilities as Modal Effects (Tang & Lindley) | 2025; 2026 | https://doi.org/10.1145/3720476 ; https://doi.org/10.1145/3776674 |
| Lorenzen et al.: Oxidizing OCaml (no mechanization mentioned) | 2024 | https://doi.org/10.1145/3674642 |
| Yoshioka, Sekiyama & Igarashi: Abstracting Effect Systems | 2024 | https://doi.org/10.1145/3674641 |
| Scoped effects: Wu, Schrijvers & Hinze; Piróg et al.; λsc (Haskell implementation); Yang et al. | 2014–2024 | https://doi.org/10.1145/2633357.2633358 ; https://doi.org/10.1145/3209108.3209166 ; https://arxiv.org/abs/2304.09697 ; https://arxiv.org/abs/2201.10287 |
| Ahman & Bauer: Runners in Action | 2020 | https://doi.org/10.1007/978-3-030-44914-8_2 |
| Lexa; Zero-Overhead Lexical Handlers (simulation proofs on paper) | 2024; 2025 | https://doi.org/10.1145/3689770 ; https://doi.org/10.1145/3763177 |
| Retrofitting effect handlers onto OCaml; Perceus | 2021 | https://doi.org/10.1145/3453483.3454039 ; https://doi.org/10.1145/3453483.3454032 |
| Frank | 2017–2020 | https://doi.org/10.1017/S0956796820000039 |
| Dynamic Wind (Voigt et al.) | 2025 | https://doi.org/10.1145/3763155 |
| Tov & Pucella; Dreyer, Neis & Birkedal | 2011; 2010 | https://doi.org/10.1145/2048066.2048115 ; https://doi.org/10.1145/1863543.1863566 |
| Congard et al.: resource safety with linear effects and exceptions | 2026 | https://doi.org/10.1007/978-3-032-22720-1_8 |
| Sekiyama, Tsukada & Igarashi: signature restriction | 2020 / 2024 | https://doi.org/10.1145/3408999 |
| Müller et al.: From Capabilities to Regions | 2023 | https://doi.org/10.1145/3622831 |
| Ho, Fromherz & Protzenko: Aeneas/LLBC soundness | 2024 | https://doi.org/10.1145/3674640 |
| Oxide; Featherweight Rust | 2019–21; 2021 | https://arxiv.org/abs/1903.00982 ; https://doi.org/10.1145/3443420 |

One more item is not confirmed as mechanized. *Building Extensible Program Logics through Effect Handlers* (Zhang, Gregersen & Tassarotti, arXiv:2607.12642) exists, but its abstract names no proof assistant: https://arxiv.org/abs/2607.12642.

### 3.9 Which mechanizations to build on

The deciding question is **how your borrow calculus is proved**. Effect metatheory has split into two proof cultures, and crossing between them is expensive.

| Your borrow core | Start from | Add | Why |
|---|---|---|---|
| Rocq/Iris, semantic (RustBelt-style) | Hazel, then Affect | Yarrow for regions; TES for labels as permissions; Blaze for relational proofs; Iris-WasmFX if compiling to stack switching | Same foundation as RustBelt: semantic typing, typing rules as lemmas, ghost tokens for one-shot. Combining with the lifetime logic is unpublished |
| Coq/Rocq, syntactic (Oxide-style) | System C (locally nameless, progress and preservation; its capability escape argument resembles borrow-checker escape) | Tang et al.'s tagged semantics for A3; a Biernacki- or Zhang–Myers-style logical relation for B1 | Abstraction safety needs a logical relation either way |
| Agda | AEff, Hefty Algebras, Kidney–Yang–Wu | — | Hefty Algebras is the only mechanized treatment of scoped operations found, but it has no account of state or ownership |
| Lean 4 | Capless, Capybara, Classifying Capabilities (capabilities, scope safety, exceptions, separation) | Port System C's or Bauer–Pretnar's proofs for resumptions; Iris-Lean lacks a Hazel analogue | No general handler calculus with resumptions exists in Lean yet |

**Stretch goals (grades and CBPV).** Torczon et al. is the only mechanized CBPV I found that combines a graded effect monoid with a usage coeffect semiring. Forster et al. (Abella) is the mechanized CBPV reference for comparing handlers, delimited control and monadic reflection.

**Results that exist only on paper, so mechanizing them would be new work:**
- control-flow linearity;
- scoped resumptions;
- Met together with OxCaml modes;
- the semantics of dropping a continuation;
- the effect algebra conditions;
- dynamic wind.

---

## 4. Organizing frameworks: linear, adjoint, graded, modal, CBPV (stretch)

### 4.0 What each framework answers for you

| Framework | Question it answers | Where it goes in your language |
|---|---|---|
| CBPV | Where do effects live, and where do borrows live? | Borrows and ownership go on value types and contexts; effects go on computation types. They meet only at thunks `U B` and at captured continuations (stacks) |
| LNL / adjoint logic | How do several structural disciplines coexist? | A preorder of modes with per-mode weakening and contraction, connected by shifts |
| Modes | How do you add independent axes without rewriting the core? | A product of small mode lattices, with effects as one more modality |
| Grades | How do you count uses, in particular resumptions? | A grade on the operation and on `k`, from a small ordered structure |
| Linear types | Must a captured resource be consumed? | A choice between affine and linear `k`, kept separate from uniqueness |

### 4.1 Call-by-push-value

**Key papers.**
- **Forster et al. 2017/2019:** CBPV with handlers, plus a partial Abella mechanization. This is the template for handlers in CBPV.
- **Torczon et al. 2024 (Coq):** graded effects on computation types and coeffects on contexts. It has no handlers and no captured continuations.
- **Levy 2003/2005:** CBPV with an explicit stack judgement. In CBPV, an operation's captured continuation is a **stack**, and stacks are used linearly by construction. That is a natural place to attach a resumption multiplicity, separate from the `U` modality that carries closure multiplicity.
- **Congard, Munch-Maccagnoni & Douence 2026:** a linear, optionally ordered CBPV with `new` and `delete`, and a "resource CBPV" with exceptions and destructors. Weakening and exchange have side effects there, so types are affine but derivations are ordered, and an explicit `move` is needed to release a resource out of LIFO order (paper proofs). It is the closest proven account of what happens when an exception discards owned resources. It does not cover multi-shot resumption.
- **Curien, Fiore & Munch-Maccagnoni 2016:** adjunction models for mixing resources with effects. Use them to decide which η-laws and commuting conversions survive.
- **McDermott & Mycroft 2019:** extended CBPV for reasoning about evaluation order.
- **Graded presentations:** Kammar & McDermott 2018; McDermott & Uustalu 2022; Katsumata, McDermott, Uustalu & Wu 2022.
- **Not found:** any graded CBPV with effect handlers.

**How it helps (synthesis).** Your borrow metatheory stays almost entirely inside the value fragment. New interaction rules are needed in exactly two places, `U B` and captured stacks.

### 4.2 LNL and adjoint logic

**Key papers.**
- **Benton 1994:** LNL splits linear logic's `!` into an adjunction between a linear world and a cartesian world. Reed's unpublished 2009 manuscript generalizes this to a preorder of modes.
- **Jang, Roshal, Pfenning & Pientka (FSCD 2024):** adjoint natural deduction. Its *independence* principle says that a term of mode k depends only on hypotheses of mode ≥ k. Garbage freedom follows from the modes.
- **Roshal & Pfenning (IJCAR 2026):** ordered adjoint logic, which mixes weakening, contraction and left/right mobility per mode, with cut elimination.
- **Pruiksma & Pfenning (2019–2022):** a message-passing reading in which weakening means cancellation.
- **Licata, Shulman & Riley (FSCD 2017):** cut admissibility proved once for every mode theory.

**How it helps (synthesis).**
- Model `copy`, `owned` (affine, so `Drop`), `linear` and possibly `ordered` (stack-scoped regions and handler frames) as modes.
- The capturing condition becomes an adjoint shift: a multi-shot `k` lives in a mode with contraction, and you may enter that mode only when every captured hypothesis allows contraction.
- Reading weakening as cancellation gives "drop `k`" a principled meaning: cancel and unwind.
- No published adjoint CBPV with handlers exists.

### 4.3 Modes (OxCaml, MTT, modal effects)

**Key papers.**
- **Lorenzen et al. (ICFP 2024):** locality, uniqueness and affinity axes, with "Only affine closures may close over unique values". The soundness proof is syntactic and on paper. The calculus has no handlers.
- **Georges et al. (POPL 2025):** contention and portability axes, with a semantic model in Iris/Rocq. This is the proof architecture to reuse.
- **Met (OOPSLA 2025):** effects as modalities on the ambient effect context, with paper proofs; the artifact is Haskell only.
- **Tang & Lindley (POPL 2026):** rows and capabilities both encode into Met.
- **Gratzer (LMCS 2026):** normalization for multimodal type theory, which reduces type checking to deciding equality of modalities. This is for dependent MTT; Met has its own simpler proofs.
- **Zyuzin & Nanevski (ICFP 2021):** contextual modal types for handlers.
- **The OxCaml docs** add a `yielding` axis, with local values defaulting to yielding. It has no published semantics.

**How it helps (synthesis).**
- Keep the axes separate:
  - **locality/lifetime:** whether something may escape a scope;
  - **uniqueness:** past aliasing, which is your `&mut` and ownership axis;
  - **affinity/multiplicity:** future use count, which is where continuation multiplicity goes;
  - **effect modality:** which operations a computation may perform;
  - **portability:** whether something may move to another thread.
- Locality restricts *escape*, not how many times something is invoked. A `many` continuation may capture local data as long as it does not escape.
- The capture law per axis: `mode(k) ≤ meet` of the captured values' modes. This is OxCaml's closure rule applied to continuations. Tang et al. and Affect prove only its affinity component.
- No soundness proof has been published for a single mode theory combining Met-style effects with OxCaml-style ownership.

### 4.4 Grades (coeffects, QTT, graded monads, graded handlers)

**Key papers.**
- **Granule** (Orchard, Liepelt & Eades 2019).
- **Gaboardi et al. 2016:** graded distributive laws between effects and coeffects.
- **Katsumata 2014:** the baseline laws for an effect algebra.
- **QTT** (Atkey 2018; Brady 2021): grade 0 means erasure, which suits lifetimes and ghost capabilities.
- **Abel & Bernardy 2020:** which laws each metatheorem needs.
- **GraD** (Choudhury et al. 2021, Coq): a heap semantics that tracks usage.
- **Abel, Danielsson & Eriksson 2023 (Agda).**
- **Bianchini et al. 2022:** aliasing is a *non-structural* coeffect.
- **Marshall & Orchard 2024:** Rust-style ownership as fractional uniqueness, in Granule.
- **Graded handlers:**
  - Kura 2020: graded algebraic theories.
  - Sanada 2023: handlers graded by morphisms of a category, which are typestate-like; sound and adequate.
  - Ahman 2023: a time grade forces linear resumption, since "k must be executed exactly once for Mop's execution time to match".
- **Liepelt, Marshall & Orchard (ICFP 2026):** grades on arrows and a graded modality over a linear base are inter-translatable for coeffect systems.

**How it helps (synthesis).**
- Write `op : A ⇒[r] B` with `r` from the interval lattice, and bind `k` at grade `r`. Ordinary coeffect accounting then charges the captured context `r·Γ`.
- Soundness needs three laws:
  - `1·u = u`;
  - `0·u` is defined only when `u` is droppable;
  - `ω·u` is defined only when `u` is duplicable.
- This scaling rule is **unpublished** beyond the two-point cases that Tang et al. and Affect prove.
- How a usage grade acts on an ownership grade is open. State it as an axiom of your design.
- Do not re-express your borrow calculus as grades, because aliasing is non-structural.

### 4.5 Linear vs. unique

**Key papers.**
- **Marshall, Vollmer & Orchard 2022:** "linearity restricts the future; uniqueness guarantees the past".
- **Linear Haskell; Linearly Qualified Types:** multiplicity polymorphism and inference.

**What follows.**
- Owned values and `&mut` live on the uniqueness axis, and `k`'s multiplicity lives on the affinity axis.
- If `k` captures something unique, `k` is at most once. It does **not** follow that `k` is unique.
- **The decision to make first** is between affine `k` (droppable, with unwinding) and linear `k` (must resume or discontinue). §1 recommends affine plus unwinding, plus A7's restrictions.

### 4.6 Foundations for linear continuations and well-bracketing

- **Filinski 1992:** linear continuations. Copying and discarding a continuation are explicit structural acts.
- **Berdine, O'Hearn, Reddy & Thielecke 2002:** linear continuation-passing. It links linear use of continuations to stack discipline (abstract not retrieved, so this characterization is unverified).
- **Bruggeman, Waddell & Dybvig 1996:** one-shot continuations avoid stack copying, so pointers into the stack stay valid.
- **Egger, Møgelberg & Simpson 2012:** the enriched effect calculus. CPS translations that use continuations linearly are fully complete.
- **Munch-Maccagnoni 2018:** resource polymorphism (destructors and moves in OCaml), the design ancestor of Congard et al.
- **Kawahara & Kameyama 2020; Kobayashi & Kameyama 2025:** one-shot handlers compared with coroutines.

### 4.7 A concrete skeleton (synthesis; not a published system)

1. **CBPV core.** Value types carry your borrow structure unchanged, and computation types carry effects. `U B` and handler-bound `k` are the only points where the two interact.
2. **A product of mode axes:**
   - uniqueness (from your borrow core);
   - locality/lifetime (from your borrow core);
   - multiplicity (new);
   - effect modality or capabilities (new).
3. **One capture rule for closures and continuations alike.** Multiplicity is bounded by the meet of what is captured, and lifetime by the intersection of the captured lifetimes.
4. **Operation resumption classes** from the interval lattice `{0}`, `{1}`, `[0,1]`, `[0,ω]`.
5. **Capabilities as borrows scoped to a handler,** with capture sets for anything first-class.
6. **Multiplicity and mode polymorphism from day one, with inference.**
7. **Theorems:** the T-package from §1.10, plus erasure of grade-0 and mode annotations.

### 4.8 Recommendation

- **Use a mode theory as the organizing principle, presented over a CBPV skeleton.** OxCaml shows that independent, inferable mode axes can be added to an existing language (paper). DRF à la Mode shows the same architecture mechanized in Iris/Rocq, and Met shows that effects can be one more modality.
- **Use adjoint logic as the semantic justification, not as the surface system.**
- **Use grades narrowly,** only for continuation multiplicity, starting from the interval lattice. Upgrade to a semiring only if a real effect needs exact counts, as in Ahman's time grades.
- **Let your proof style pick the route,** as in §3.9.

---

## 5. Suggested reading order

1. **Tang, Hillerström, Lindley & Morris, *Soundly Handling Linearity* (POPL 2024).** The law, the Links bug, and a linearity-aware semantics you can copy for T4.
2. **van Rooij & Krebbers, *Affect* (POPL 2025).** The mechanized affine version: `Cell`-style references, the polymorphism pitfalls, and a semantic proof architecture.
3. **Dreyer, Neis & Birkedal (ICFP 2010), then Timany, Guéneau & Birkedal (POPL 2024).** Exactly what well-bracketed control buys and what control effects take away. These are the foundation for A7.
4. **Brachthäuser et al., *System C* (OOPSLA 2022).** Capabilities as scoped values, boxes as capture sets, with a Coq proof.
5. **Yoshioka, Sekiyama & Igarashi (ICFP 2024).** The minimal conditions your effect representation must satisfy (T0).
6. **Mathiasen, Timany & Birkedal, *Yarrow* (2026 preprint).** Regions under one-shot and multi-shot handlers: revocation, and undefined behavior for references into captured fibers.
7. **de Vilhena & Pottier, *Hazel* (POPL 2021), plus de Vilhena's thesis chapter on Maze.** Protocols; one-shot keeps the frame rule, multi-shot breaks it.
8. **Voigt, Schuster & Brachthäuser, *Dynamic Wind* (OOPSLA 2025).** Finalization under suspend and resume, and the shape of a resource-safety invariant.
9. **without.boats, *The Scoped Task Trilemma*, with RFC 1066.** What "leaks are safe" costs once continuations exist.
10. **Zhang & Myers, *Tunneling* (POPL 2019).** Abstraction safety, stated and mechanized.
11. **Xie et al., *Effect Handlers, Evidently* (ICFP 2020).** Scoped resumptions; tail-resumptive operations as calls that run in the handler's context.
12. **Ho, Fromherz & Protzenko (ICFP 2024), with rustc's E0626, MIR `Yield` and the coroutine-witness documentation.** Borrow-state joins, and how production borrow checking handles suspension.
13. **Fecher, the Ante post.** The only design write-up aimed squarely at Rust-style borrows plus handlers.
14. **Lorenzen et al. (ICFP 2024), then Tang et al., *Modal Effect Types* (OOPSLA 2025).** Modes and effects as modalities (stretch).
15. **Torczon et al., *Effects and Coeffects in CBPV* (OOPSLA 2024).** A mechanized graded CBPV template (stretch).

---

## 6. Open problems, and where your project could contribute

**Gaps in the literature.**
1. **A mechanized borrow calculus with handlers.** No calculus combines lifetime-indexed `&`/`&mut` (reborrowing, NLL, two-phase borrows) with handlers. Even stages 1–2 of §1.10 would be a first.
2. **RustBelt's lifetime logic combined with handler protocols.** Something like "Yarrow for lifetimes" is unpublished.
3. **Conservativity (T7).** No theorem shows that library proofs assuming well-bracketed control survive under `{fn, abort}`. Timany et al. 2024 only conjecture it for innocuous control. A crisp result tying this to Rust libraries (`thread::scope`, `replace_with`) would be new.
4. **Discard semantics.** Whether discard-unwinding should be catchable, and which choice keeps scope-like and guard-like libraries sound, has not been studied formally.
5. **Leaking vs. linear continuations.** A `!Leak` kind, linear continuations, or "`forget` requires `'static`" has never been formalized together with handlers.
6. **Flow-sensitive borrow checking with suspension.** No formalization of NLL or Polonius with resume or drop edges exists. A sound borrow-state join at multi-shot resume points is unproven (Aeneas's join covers loops only).
7. **Lifetime-polymorphic operations under multi-shot.** An analogue of Sekiyama et al.'s signature restriction for lifetime binders is unexplored.
8. **First-class continuations that hold `&mut` under flow-sensitive lifetimes,** including a pinned-continuation typestate. There is no mechanized semantics of `Pin` together with coroutines.
9. **Multi-shot over shared borrows.** It is plausibly sound if every lifetime covers all resumptions, but there is no formal treatment.
10. **Prophecy-based verification** (RustHornBelt, Aeneas) with dropped or duplicated continuations.
11. **A formal treatment of `Send` for continuations** with lifetime-bounded captures.
12. **Graded resumption beyond two points.** The scaling rule `r·Γ`, the law relating usage grades to ownership grades, and a graded CBPV with handlers are all open.
13. **A single mode theory unifying Met and OxCaml modes,** with a soundness proof. OxCaml's `yielding` axis has no formal semantics.
14. **Lean 4.** There is no general handler calculus with resumptions, and Iris-Lean lacks a Hazel analogue.
15. **Adjoint or ordered mode theories with algebraic handlers.**
16. **Destructor order and drop check** for dropped continuations that span several frames.

**Highest-leverage contributions for your project:** 1, 3, 6 and 7. Each one builds directly on a proven borrow core, and each yields a theorem you can state precisely.

---

## Appendix A: Bibliography with links

### Effect handler foundations and type systems
- Plotkin, Power (2003). Algebraic Operations and Generic Effects. *ACS*. https://doi.org/10.1023/A:1023064908962
- Plotkin, Pretnar (2008). A Logic for Algebraic Effects. *LICS*. https://doi.org/10.1109/LICS.2008.45
- Plotkin, Pretnar (2013). Handling Algebraic Effects. *LMCS* 9(4). https://doi.org/10.2168/LMCS-9(4:23)2013
- Kammar, Plotkin (2012). Algebraic Foundations for Effect-Dependent Optimisations. *POPL*. https://doi.org/10.1145/2103656.2103698
- Katsumata (2014). Parametric Effect Monads and Semantics of Effect Systems. *POPL*. https://doi.org/10.1145/2535838.2535846
- Kammar, Lindley, Oury (2013). Handlers in Action. *ICFP*. https://doi.org/10.1145/2500365.2500590
- Bauer, Pretnar (2014). An Effect System for Algebraic Effects and Handlers. *LMCS* 10(4:9). https://lmcs.episciences.org/1153
- Pretnar (2015). An Introduction to Algebraic Effects and Handlers. *MFPS*. https://www.eff-lang.org/handlers-tutorial.pdf
- Kammar, Pretnar (2017). No Value Restriction Is Needed for Algebraic Effects and Handlers. *JFP*. https://arxiv.org/abs/1605.06938
- Pretnar et al. Proof repository (Twelf, Abella). https://github.com/matijapretnar/proofs
- Saleh, Karachalias, Pretnar, Schrijvers (2018). Explicit Effect Subtyping. *ESOP*. https://doi.org/10.1007/978-3-319-89884-1_12
- Biernacki, Polesiuk (2018). Logical Relations for Coherence of Effect Subtyping. *LMCS*. https://lmcs.episciences.org/4180 ; https://bitbucket.org/pl-uwr/coherence-logrel
- Forster, Kammar, Lindley, Pretnar (2017/2019). On the Expressive Power of User-Defined Effects. *ICFP / JFP*. https://doi.org/10.1145/3110257 ; https://arxiv.org/abs/1610.09161
- Hillerström, Lindley, Atkey (2020). Effect Handlers via Generalised Continuations. *JFP*. https://doi.org/10.1017/S0956796820000040
- Hillerström (2021). Foundations for Programming and Implementing Effect Handlers (PhD thesis). https://www.dhil.net/research/papers/thesis.pdf
- Leijen (2017). Type Directed Compilation of Row-Typed Algebraic Effects. *POPL*. https://doi.org/10.1145/3009837.3009872
- Leijen (2018). Algebraic Effect Handlers with Resources and Deep Finalization. MSR-TR-2018-10. https://www.microsoft.com/en-us/research/publication/algebraic-effect-handlers-resources-deep-finalization/
- Koka language book. https://koka-lang.github.io/koka/doc/book.html
- Xie, Brachthäuser, Hillerström, Schuster, Leijen (2020). Effect Handlers, Evidently. *ICFP*. https://doi.org/10.1145/3408981
- Xie, Leijen (2021). Generalized Evidence Passing for Effect Handlers. *ICFP*. https://doi.org/10.1145/3473576
- Xie, Cong, Ikemori, Leijen (2022). First-Class Names for Effect Handlers. *OOPSLA*. https://doi.org/10.1145/3563289
- Ikemori, Cong, Masuhara, Leijen (2022). Sound and Complete Type Inference for Closed Effect Rows. *TFP*. https://doi.org/10.1007/978-3-031-21314-4_8
- Brachthäuser, Leijen (2023). Qualified Effect Types — Taming Control-Flow through Linear Effect Handlers. MSR-TR-2023-42. https://www.microsoft.com/en-us/research/publication/qualified-effect-types/
- Yoshioka, Sekiyama, Igarashi (2024). Abstracting Effect Systems for Algebraic Effect Handlers. *ICFP*. https://doi.org/10.1145/3674641 ; https://arxiv.org/abs/2404.16381
- Sekiyama, Tsukada, Igarashi (2020; JFP 2024). Signature Restriction for Polymorphic Algebraic Effects. *ICFP*. https://doi.org/10.1145/3408999 ; https://doi.org/10.1017/S0956796824000054 ; https://arxiv.org/abs/2003.08138
- Balik, Jędras, Polesiuk (2025). Deciding not to Decide: Sound and Complete Effect Inference in the Presence of Higher-Rank Polymorphism. arXiv. https://arxiv.org/abs/2510.20532
- Lutze, Madsen, Schuster, Brachthäuser (2023). With or Without You: Programming with Effect Exclusion. *ICFP*. https://doi.org/10.1145/3607846
- Lutze, Madsen (2024). Associated Effects: Flexible Abstractions for Effectful Programming. *PLDI*. https://doi.org/10.1145/3656393
- Biernacki, Piróg, Polesiuk, Sieczkowski (2018). Handle with Care. *POPL*. https://doi.org/10.1145/3158096 ; https://bitbucket.org/pl-uwr/aleff-logrel
- Biernacki et al. (2019). Abstracting Algebraic Effects. *POPL*. https://doi.org/10.1145/3290319
- Biernacki et al. (2020). Binders by Day, Labels by Night. *POPL*. https://doi.org/10.1145/3371116 ; https://bitbucket.org/pl-uwr/aleff-lex
- Piróg, Polesiuk, Sieczkowski (2019). Typed Equivalence of Effect Handlers and Delimited Control. *FSCD*. https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2019.30
- Sieczkowski, Pyzik, Biernacki (2023). A General Fine-Grained Reduction Theory for Effect Handlers. *ICFP*. https://doi.org/10.1145/3607848
- Zhang, Myers (2019). Abstraction-Safe Effect Handlers via Tunneling. *POPL*. https://doi.org/10.1145/3290318 ; https://github.com/yizhouzhang/abseff-coq
- Zhang, Salvaneschi, Myers (2020). Handling Bidirectional Control Flow. *OOPSLA*. https://doi.org/10.1145/3428207 ; https://github.com/yizhouzhang/olaf-coq
- Lindley, McBride, McLaughlin (2017); Convent et al. (2020). Frank: Do Be Do Be Do. *POPL / JFP*. https://doi.org/10.1017/S0956796820000039
- Wu, Schrijvers, Hinze (2014). Effect Handlers in Scope. *Haskell Symposium*. https://doi.org/10.1145/2633357.2633358
- Piróg, Schrijvers, Wu, Jaskelioff (2018). Syntax and Semantics for Operations with Scopes. *LICS*. https://doi.org/10.1145/3209108.3209166
- Bosman, van den Berg, Tang, Schrijvers (2024). A Calculus for Scoped Effects & Handlers. *LMCS* 20(4). https://arxiv.org/abs/2304.09697
- Yang, Paviotti, Wu, van den Berg, Schrijvers (2022). Structured Handling of Scoped Effects. *ESOP*. https://arxiv.org/abs/2201.10287
- Bach Poulsen, van der Rest (2023). Hefty Algebras. *POPL*. https://doi.org/10.1145/3571255 ; https://github.com/heft-lang/POPL2023
- Ahman, Bauer (2020). Runners in Action. *ESOP*. https://doi.org/10.1007/978-3-030-44914-8_2
- Ahman, Pretnar (2021). Asynchronous Effects. *POPL*. https://github.com/danelahman/aeff-agda
- Ahman, Pretnar. Higher-Order Asynchronous Effects. *LMCS*. https://github.com/danelahman/higher-order-aeff-agda
- Kidney, Yang, Wu (2024). Algebraic Effects Meet Hoare Logic in Cubical Agda. *POPL*. https://doi.org/10.1145/3632898
- Ahman (2023). When Programs Have to Watch Paint Dry. *FoSSaCS*. https://doi.org/10.1007/978-3-031-30829-1_1 ; https://github.com/danelahman/temporal-resources

### Capabilities, capture sets, lexical handlers, compilation
- Brachthäuser, Schuster, Ostermann (2020). Effects as Capabilities. *OOPSLA*. https://doi.org/10.1145/3428194
- Brachthäuser, Schuster, Lee, Boruch-Gruszecki (2022). Effects, Capabilities, and Boxes. *OOPSLA*. https://doi.org/10.1145/3527320 ; https://github.com/se-tuebingen/oopsla-2022-artifact
- Schuster, Brachthäuser, Ostermann (2020). Compiling Effect Handlers in Capability-Passing Style. *ICFP*. https://doi.org/10.1145/3408975
- Müller, Schuster, Starup, Ostermann, Brachthäuser (2023). From Capabilities to Regions. *OOPSLA*. https://doi.org/10.1145/3622831
- Voigt, Schuster, Brachthäuser (2025). Dynamic Wind for Effect Handlers. *OOPSLA*. https://doi.org/10.1145/3763155
- Muhcu, Schuster, Steuwer, Brachthäuser (2025). Multiple Resumptions and Local Mutable State, Directly. *ICFP*. https://doi.org/10.1145/3747529
- Osvald, Essertel, Wu, González-Alayón, Rompf (2016). Gentrification Gone too Far? *OOPSLA*. https://doi.org/10.1145/3022671.2984009 ; https://github.com/TiarkRompf/scala-escape
- Boruch-Gruszecki et al. (2023). Capturing Types. *TOPLAS*. https://doi.org/10.1145/3618003
- Fourment, Xu (2023). A Mechanized Theory of the Box Calculus. *IWACO*. https://arxiv.org/abs/2309.05362
- Xu, Bračevac, Pham, Odersky (2025). What's in the Box (System Capless). *OOPSLA*. https://doi.org/10.1145/3763112 ; https://github.com/Linyxus/capless-lean
- Pham, Bračevac, Xu, Zhao, Odersky (2026). Classifying Capabilities. *OOPSLA*. https://doi.org/10.1145/3839474
- Xu, Bračevac, Pham, Zhao, Odersky (2026). System Capybara. arXiv. https://arxiv.org/abs/2607.09383
- Xu, Boruch-Gruszecki, Odersky (2024). Degrees of Separation. *OOPSLA*. https://doi.org/10.1145/3649853
- Lee et al. (2024). Qualifying System F<:. *OOPSLA*. https://arxiv.org/abs/2311.07480
- Ma, Ge, Lee, Zhang (2024). Lexical Effect Handlers, Directly. *OOPSLA*. https://doi.org/10.1145/3689770
- Ma, Ge, Jung, Zhang (2025). Zero-Overhead Lexical Effect Handlers. *OOPSLA*. https://doi.org/10.1145/3763177
- Sivaramakrishnan et al. (2021). Retrofitting Effect Handlers onto OCaml. *PLDI*. https://doi.org/10.1145/3453483.3454039
- OCaml manual, Effect handlers. https://ocaml.org/manual/5.2/effects.html
- Phipps-Costin et al. (2023). Continuing WebAssembly with Effect Handlers. *OOPSLA*. https://doi.org/10.1145/3622814
- Legoupil, Pedersen, Birkedal, Lindley, Pichon-Pharabod (2026). Iris-WasmFX. *PLDI*. https://doi.org/10.1145/3808271
- Alvarez-Picallo et al. (2024). libseff: effect handlers for C via coroutines. *OOPSLA*. https://doi.org/10.1145/3689798
- libmprompt. https://github.com/koka-lang/libmprompt
- Reinking, Xie, de Moura, Leijen (2021). Perceus. *PLDI*. https://doi.org/10.1145/3453483.3454032
- Lorenzen, Leijen, Swierstra (2023). FP²: Fully in-Place Functional Programming. *ICFP*. https://doi.org/10.1145/3607840
- Ullrich, de Moura (2019). Counting Immutable Beans. *IFL*. https://arxiv.org/abs/1908.05647
- GHC proposal 0313, Delimited continuation primops. https://ghc-proposals.readthedocs.io/en/latest/proposals/0313-delimited-continuation-primops.html

### Linearity, modes, separation logic for handlers
- Tang, Hillerström, Lindley, Morris (2024). Soundly Handling Linearity. *POPL*. https://doi.org/10.1145/3632896 ; https://arxiv.org/abs/2307.09383
- Tang, White, Dolan, Hillerström, Lindley, Lorenzen (2025). Modal Effect Types. *OOPSLA*. https://doi.org/10.1145/3720476 ; https://arxiv.org/abs/2407.11816
- Tang, Lindley (2026). Rows and Capabilities as Modal Effects. *POPL*. https://doi.org/10.1145/3776674 ; https://arxiv.org/abs/2507.10301
- Tov, Pucella (2011). A Theory of Substructural Types and Control. *OOPSLA*. https://doi.org/10.1145/2048066.2048115
- van Rooij, Krebbers (2025). Affect. *POPL*. https://doi.org/10.1145/3704841 ; https://github.com/ovanr/affect ; https://doi.org/10.5281/zenodo.14198790
- de Vilhena, Pottier (2021). A Separation Logic for Effect Handlers. *POPL*. https://doi.org/10.1145/3434314 ; https://gitlab.inria.fr/cambium/hazel
- de Vilhena, Pottier (2023). A Type System for Effect Handlers and Dynamic Labels. *ESOP*. https://link.springer.com/chapter/10.1007/978-3-031-30044-8_9 ; https://gitlab.inria.fr/cambium/tes
- de Vilhena (2022). Proof of Programs with Effect Handlers (PhD thesis). https://devilhena-paulo.github.io/thesis/de-vilhena-thesis.pdf ; https://doi.org/10.5281/zenodo.7371093
- de Vilhena, van Collem, Wright, Krebbers (2026). A Relational Separation Logic for Effect Handlers. *POPL*. https://doi.org/10.1145/3776676 ; https://github.com/DeVilhena-Paulo/blaze ; https://iris-project.org/pdfs/2026-popl-blaze.pdf
- Mathiasen, Timany, Birkedal (2026). Yarrow. arXiv. https://arxiv.org/abs/2607.15876
- Zhang, Gregersen, Tassarotti (2026). Building Extensible Program Logics through Effect Handlers. arXiv. https://arxiv.org/abs/2607.12642
- Seassau, Yoon, Madiot, Pottier (2025). Osiris. *ICFP*. https://doi.org/10.1145/3747509 ; http://cambium.inria.fr/~fpottier/publis/seassau-yoon-madiot-pottier-osiris-2025.pdf
- Frumin, Timany, Birkedal (2024). Guarded Interaction Trees. *POPL*. https://arxiv.org/abs/2307.08514
- Stepanenko et al. (2025). Context-Dependent Effects and Concurrency in Guarded Interaction Trees. arXiv. https://arxiv.org/abs/2512.11577
- Vistrup, Sammler, Jung (2025). Program Logics à la Carte. *POPL*. https://research.ralfj.de/papers/2025-popl-itree-program-logic.pdf
- Xia et al. (2020). Interaction Trees. *POPL*. https://github.com/DeepSpec/InteractionTrees
- Chappe et al. (2023). Choice Trees. *POPL*. https://arxiv.org/abs/2211.06863
- Lorenzen, White, Dolan, Eisenberg, Lindley (2024). Oxidizing OCaml with Modal Memory Management. *ICFP*. https://doi.org/10.1145/3674642
- Georges et al. (2025). Data Race Freedom à la Mode. *POPL*. https://doi.org/10.1145/3704859
- OxCaml modes documentation. https://oxcaml.org/documentation/modes/intro/
- Jane Street, handled_effect. https://github.com/janestreet/handled_effect
- Fowler, Lindley, Morris, Decova (2019). Exceptional Asynchronous Session Types: Session Types without Tiers. *POPL*. https://doi.org/10.1145/3290341
- Iris-Lean. https://github.com/leanprover-community/iris-lean ; Lean ITrees. https://github.com/mit-plv/lean4-itree

### Well-bracketing and conservativity
- Dreyer, Neis, Birkedal (2010; JFP 2012). The Impact of Higher-Order State and Control Effects on Local Relational Reasoning. *ICFP*. https://doi.org/10.1145/1863543.1863566 ; https://people.mpi-sws.org/~dreyer/papers/stslr/icfp.pdf
- Timany, Guéneau, Birkedal (2024). The Logical Essence of Well-Bracketed Control Flow. *POPL*. https://doi.org/10.1145/3632862 ; https://github.com/logsem/well-bracketed-logic
- Timany, Birkedal (2019). Mechanized Relational Verification of Concurrent Programs with Continuations. *ICFP*. https://doi.org/10.1145/3341709
- Yanovski, Dang, Jung, Dreyer (2021). GhostCell. *ICFP*. https://plv.mpi-sws.org/rustbelt/ghostcell/

### Rust, borrow checking, and suspension
- RFC 1066, Safe mem::forget. https://rust-lang.github.io/rfcs/1066-safe-mem-forget.html
- RFC 1236, Stabilize catch_panic. https://rust-lang.github.io/rfcs/1236-stabilize-catch-panic.html ; UnwindSafe docs. https://doc.rust-lang.org/std/panic/trait.UnwindSafe.html
- std::thread::scope docs and source. https://doc.rust-lang.org/std/thread/fn.scope.html ; https://github.com/rust-lang/rust/blob/master/library/std/src/thread/scoped.rs
- std::pin docs. https://doc.rust-lang.org/std/pin/index.html
- E0626. https://doc.rust-lang.org/error_codes/E0626.html
- MIR TerminatorKind (Yield). https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/enum.TerminatorKind.html
- rustc coroutine transform. https://doc.rust-lang.org/nightly/nightly-rustc/rustc_mir_transform/coroutine/index.html
- coroutine_clone tracking issue #95360. https://github.com/rust-lang/rust/issues/95360
- RFC 2033, Experimental coroutines. https://rust-lang.github.io/rfcs/2033-experimental-coroutines.html
- RFC 3513, gen blocks. https://rust-lang.github.io/rfcs/3513-gen-blocks.html
- RFC 2094, NLL. https://rust-lang.github.io/rfcs/2094-nll.html
- Matsakis (2018). An alias-based formulation of the borrow checker (Polonius). https://smallcultfollowing.com/babysteps/blog/2018/04/27/an-alias-based-formulation-of-the-borrow-checker/
- Ho, Fromherz, Protzenko (2024). Sound Borrow-Checking for Rust via Symbolic Semantics. *ICFP*. https://doi.org/10.1145/3674640 ; https://arxiv.org/abs/2404.02680
- Weiss, Gierczak, Patterson, Ahmed. Oxide: The Essence of Rust. https://arxiv.org/abs/1903.00982
- Pearce (2021). A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust. *TOPLAS*. https://doi.org/10.1145/3443420
- Matsushita et al. (2022). RustHornBelt. *PLDI*. https://doi.org/10.1145/3519939.3523704
- Jung (2018). A formal look at pinning. https://ralfj.de/blog/2018/04/05/a-formal-look-at-pinning.html
- a-mir-formality. https://github.com/rust-lang/a-mir-formality
- Simuliris. https://gitlab.mpi-sws.org/iris/simuliris
- Keyword generics initiative. https://blog.rust-lang.org/inside-rust/2022/07/27/keyword-generics/
- Wuyts (2023). Extending Rust's Effect System. https://blog.yoshuawuyts.com/extending-rusts-effect-system/
- Johnston (2024). Rust effect lowering. https://www.abubalay.com/blog/2024/01/14/rust-effect-lowering
- without.boats (2023). The Scoped Task Trilemma. https://without.boats/blog/the-scoped-task-trilemma/
- Desires (2015). Pre-Pooping Your Pants With Rust. https://faultlore.com/blah/everyone-poops/
- async-scoped. https://docs.rs/async-scoped/latest/async_scoped/
- replace_with; take_mut. https://docs.rs/replace_with/latest/replace_with/ ; https://docs.rs/take_mut/latest/take_mut/
- tokio::select! cancellation safety. https://docs.rs/tokio/latest/tokio/macro.select.html
- Oxide Computer RFD 609 (Futurelock). https://rfd.shared.oxide.computer/rfd/0609
- clippy await_holding lints. https://github.com/rust-lang/rust-clippy/blob/master/clippy_lints/src/await_holding_invalid.rs
- libstdc++ manual, exceptions and forced unwinding. https://gcc.gnu.org/onlinedocs/libstdc++/manual/using_exceptions.html

### Languages
- Fecher (2024). Effects, Ownership, and Borrowing (Ante). https://antelang.org/blog/effects_ownership_and_borrowing/
- Hylo subscripts. https://docs.hylo-lang.org/language-tour/subscripts
- Racordon et al. (2022). Implementation Strategies for Mutable Value Semantics. *JOT*. https://doi.org/10.5381/jot.2022.21.2.a2
- Racordon, Abrahams (2023). Borrow checking Hylo. *IWACO*. https://2023.splashcon.org/details/iwaco-2023-papers/5/Borrow-checking-Hylo
- Swift SE-0446, SE-0474, SE-0414, SE-0430. https://github.com/swiftlang/swift-evolution/blob/main/proposals/0446-non-escapable.md ; https://github.com/swiftlang/swift-evolution/blob/main/proposals/0474-yielding-accessors.md ; https://github.com/swiftlang/swift-evolution/blob/main/proposals/0414-region-based-isolation.md ; https://github.com/swiftlang/swift-evolution/blob/main/proposals/0430-transferring-parameters-and-results.md
- Milano, Turcotti, Myers (2022). A Flexible Type System for Fearless Concurrency. *PLDI*. https://www.cs.cornell.edu/andru/papers/gallifrey-types/
- Kotlin coroutines; cancellation. https://kotlinlang.org/docs/coroutines-basics.html ; https://kotlinlang.org/docs/cancellation-and-timeouts.html
- Unison abilities. https://www.unison-lang.org/docs/language-reference/abilities-and-ability-handlers/
- Brady (2021). Idris 2: Quantitative Type Theory in Practice. *ECOOP*. https://arxiv.org/abs/2104.00480 ; Control.App. https://idris2.readthedocs.io/en/latest/app/linear.html
- Pony reference capabilities; Clebsch et al. (2015). https://tutorial.ponylang.io/reference-capabilities/reference-capabilities.html ; https://doi.org/10.1145/2824815.2824816
- Project Verona publications; Behaviour-Oriented Concurrency (2023). https://microsoft.github.io/verona/publications.html ; https://doi.org/10.1145/3622852
- Inko memory management. https://docs.inko-lang.org/manual/latest/getting-started/memory-management/
- Vale regions. https://vale.dev/guide/regions
- Mojo lifetimes; errors. https://mojolang.org/docs/manual/values/lifetimes ; https://mojolang.org/docs/manual/errors
- Chen, Xi (2005). Combining Programming with Theorem Proving (ATS). *ICFP*. https://doi.org/10.1145/1086365.1086375
- Scala Gears. https://github.com/lampepfl/gears
- Scherer (2026). What's the status of typed effects? (OCaml Discuss). https://discuss.ocaml.org/t/whats-the-status-of-typed-effects/18439

### Classic type-and-effect, regions, ownership
- Lucassen, Gifford (1988). Polymorphic Effect Systems. *POPL*. https://doi.org/10.1145/73560.73564
- Talpin, Jouvelot (1994). The Type and Effect Discipline. *I&C*. https://doi.org/10.1006/inco.1994.1046
- Tofte, Talpin (1997). Region-Based Memory Management. *I&C*. https://doi.org/10.1006/inco.1996.2613
- Calcagno, Helsen, Thiemann (2002). Syntactic Type Soundness Results for the Region Calculus. *I&C*. https://doi.org/10.1006/inco.2001.3112
- Crary, Walker, Morrisett (1999). Typed Memory Management in a Calculus of Capabilities. *POPL*. https://doi.org/10.1145/292540.292564
- Grossman et al. (2002). Region-Based Memory Management in Cyclone. *PLDI*. https://doi.org/10.1145/512529.512563 ; https://cyclone.thelanguage.org/wiki/Papers/
- DeLine, Fähndrich (2001). Enforcing High-Level Protocols in Low-Level Software. *PLDI*. https://doi.org/10.1145/378795.378811
- Fähndrich, DeLine (2002). Adoption and Focus. *PLDI*. https://doi.org/10.1145/512529.512532
- Clarke, Drossopoulou (2002). Ownership, Encapsulation and the Disjointness of Type and Effect. *OOPSLA*. https://doi.org/10.1145/582419.582447
- Greenhouse, Boyland (1999). An Object-Oriented Effects System. *ECOOP*. https://doi.org/10.1007/3-540-48743-3_10
- Boyland (2003). Checking Interference with Fractional Permissions. *SAS*. https://doi.org/10.1007/3-540-44898-5_4
- Bocchino et al. (2009). A Type and Effect System for Deterministic Parallel Java. *OOPSLA*. https://doi.org/10.1145/1640089.1640097
- Morrisett, Ahmed, Fluet (2005). L3: A Linear Language with Locations. *TLCA*. https://doi.org/10.1007/11417170_22
- Fluet, Morrisett, Ahmed (2006). Linear Regions Are All You Need. *ESOP*. https://link.springer.com/chapter/10.1007/11693024_2 ; https://www.cs.rit.edu/~mtf/research/substruct-regions/
- Balabonski, Pottier, Protzenko (2016). The Design and Formalization of Mezzo. *TOPLAS*. https://doi.org/10.1145/2837022
- Timany, Stefanesco, Krogh-Jespersen, Birkedal (2018). A Logical Relation for Monadic Encapsulation of State. *POPL*. https://doi.org/10.1145/3158152
- Krishnaswami, Turon, Dreyer, Garg (2012). Superficially Substructural Types. *ICFP*. https://doi.org/10.1145/2364527.2364536
- Choudhury, Krishnaswami (2020). Recovering Purity with Comonads and Capabilities. *ICFP*. https://doi.org/10.1145/3408993
- Bianchini, Dagnino, Giannini, Zucca, Servetto (2022). Coeffects for Sharing and Mutation. *OOPSLA*. https://doi.org/10.1145/3563319
- Bao et al. (2021). Reachability Types. *OOPSLA*. https://doi.org/10.1145/3485516
- Wei et al. (2024). Polymorphic Reachability Types. *POPL*. https://doi.org/10.1145/3632856 ; https://github.com/TiarkRompf/reachability
- Bao et al. (2023). Modeling Reachability Types with Logical Relations. arXiv. https://arxiv.org/abs/2309.05885
- Deng, He, Jia, Bao, Rompf (2025). Capture Now, Consume Later. arXiv. https://arxiv.org/abs/2510.08939

### CBPV, adjoint, graded, foundations of continuation linearity
- Torczon, Suárez Acevedo, Agrawal, Velez-Ginorio, Weirich (2024). Effects and Coeffects in Call-By-Push-Value. *OOPSLA*. https://doi.org/10.1145/3689750 ; https://arxiv.org/abs/2311.11795 ; https://github.com/plclub/cbpv-effects-coeffects
- Levy (2003). Adjunction Models for Call-By-Push-Value with Stacks. *ENTCS*. https://doi.org/10.1016/S1571-0661(04)80568-1 ; Levy (2003). Call-By-Push-Value (book). https://doi.org/10.1007/978-94-007-0954-6
- Congard, Munch-Maccagnoni, Douence (2026). Linear Effects, Exceptions, and Resource Safety. *ESOP*. https://doi.org/10.1007/978-3-032-22720-1_8 ; https://arxiv.org/abs/2510.23517
- Munch-Maccagnoni (2018). Resource Polymorphism. arXiv. https://arxiv.org/abs/1803.02796
- Curien, Fiore, Munch-Maccagnoni (2016). A Theory of Effects and Resources. *POPL*. https://doi.org/10.1145/2837614.2837652
- McDermott, Mycroft (2019). Extended Call-by-Push-Value. *ESOP*. https://doi.org/10.1007/978-3-030-17184-1_9
- Kammar, McDermott (2018). Factorisation Systems for Logical Relations and Monadic Lifting. *MFPS*. https://doi.org/10.1016/j.entcs.2018.11.012
- McDermott, Uustalu (2022). Flexibly Graded Monads and Graded Algebras. *MPC*. https://doi.org/10.1007/978-3-031-16912-0_4
- Katsumata, McDermott, Uustalu, Wu (2022). Flexible Presentations of Graded Monads. *ICFP*. https://doi.org/10.1145/3547654
- Filinski (1992). Linear Continuations. *POPL*. https://doi.org/10.1145/143165.143174
- Berdine, O'Hearn, Reddy, Thielecke (2002). Linear Continuation-Passing. *HOSC*. https://doi.org/10.1023/A:1020891112409
- Bruggeman, Waddell, Dybvig (1996). Representing Control in the Presence of One-Shot Continuations. *PLDI*. https://doi.org/10.1145/231379.231395
- Egger, Møgelberg, Simpson (2012). Linear-Use CPS Translations in the Enriched Effect Calculus. *LMCS* 8(4:2). https://doi.org/10.2168/LMCS-8(4:2)2012
- Kawahara, Kameyama (2020). One-Shot Algebraic Effects as Coroutines. *TFP*. https://doi.org/10.1007/978-3-030-57761-2_8
- Kobayashi, Kameyama (2025). Expressive Power of One-Shot Control Operators and Coroutines. *APLAS*. https://arxiv.org/abs/2509.11901 ; https://doi.org/10.1007/978-981-95-3585-9_5
- Benton (1994). A Mixed Linear and Non-Linear Logic. *CSL*. https://doi.org/10.1007/BFb0022251
- Jang, Roshal, Pfenning, Pientka (2024). Adjoint Natural Deduction. *FSCD*. https://doi.org/10.4230/LIPIcs.FSCD.2024.15
- Roshal, Pfenning (2026). Ordered Adjoint Logic. *IJCAR*. https://doi.org/10.1007/978-3-032-32592-1_6 ; https://arxiv.org/abs/2605.19112
- Pruiksma, Pfenning (2019; 2021). A Message-Passing Interpretation of Adjoint Logic. *PLACES*; *JLAMP*. https://doi.org/10.4204/EPTCS.291.6 ; https://doi.org/10.1016/j.jlamp.2020.100637
- Pruiksma, Pfenning (2022). Back to Futures. *JFP*. https://doi.org/10.1017/S0956796822000016
- Licata, Shulman, Riley (2017). A Fibrational Framework for Substructural and Modal Logics. *FSCD*. https://doi.org/10.4230/LIPIcs.FSCD.2017.25
- Gratzer (2022; 2026). Normalization for Multimodal Type Theory. *LICS*; *LMCS* 22(1:27). https://doi.org/10.1145/3531130.3532398 ; https://doi.org/10.46298/lmcs-22(1:27)2026
- Zyuzin, Nanevski (2021). Contextual Modal Types for Algebraic Effects and Handlers. *ICFP*. https://doi.org/10.1145/3473580
- Orchard, Liepelt, Eades (2019). Quantitative Program Reasoning with Graded Modal Types. *ICFP*. https://doi.org/10.1145/3341714
- Gaboardi, Katsumata, Orchard, Breuvart, Uustalu (2016). Combining Effects and Coeffects via Grading. *ICFP*. https://doi.org/10.1145/2951913.2951939
- Atkey (2018). Syntax and Semantics of Quantitative Type Theory. *LICS*. https://doi.org/10.1145/3209108.3209189
- Abel, Bernardy (2020). A Unified View of Modalities in Type Systems. *ICFP*. https://doi.org/10.1145/3408972
- Choudhury, Eades, Eisenberg, Weirich (2021). A Graded Dependent Type System with a Usage-Aware Semantics. *POPL*. https://doi.org/10.1145/3434331 ; https://github.com/sweirich/graded-haskell
- Abel, Danielsson, Eriksson (2023). A Graded Modal Dependent Type Theory with a Universe and Erasure, Formalized. *ICFP*. https://doi.org/10.1145/3607862
- Marshall, Vollmer, Orchard (2022). Linearity and Uniqueness: An Entente Cordiale. *ESOP*. https://doi.org/10.1007/978-3-030-99336-8_13
- Marshall, Orchard (2024). Functional Ownership through Fractional Uniqueness. *OOPSLA*. https://doi.org/10.1145/3649848 ; https://arxiv.org/abs/2310.18166
- Kura (2020). Graded Algebraic Theories. *FoSSaCS*. https://doi.org/10.1007/978-3-030-45231-5_21
- Sanada (2023). Category-Graded Algebraic Theories and Effect Handlers. *ENTICS*. https://doi.org/10.46298/entics.10491
- Liepelt, Marshall, Orchard (2026). Same Coeffect, Different Base. *ICFP*. https://doi.org/10.1145/3828697
- Bernardy et al. (2018). Linear Haskell. *POPL*. https://arxiv.org/abs/1710.09756
- Spiwack et al. (2022). Linearly Qualified Types. *ICFP*. https://doi.org/10.1145/3547626

---

## Appendix B: Verification status

**What I re-checked while writing this report.** I checked against the extracted paper texts in `/private/tmp/claude-501/-Users-johnthompson-repos-personal-borrow-land/6e8dad4c-cb6f-4cf2-8ba6-0f11c7843dc2/scratchpad/txt/` and `/private/tmp/claude-501/-Users-johnthompson-repos-personal-borrow-land/6e8dad4c-cb6f-4cf2-8ba6-0f11c7843dc2/scratchpad/`:
- **Affect:** capturing condition, "exited at most once", affine one-shot continuations with no `discontinue`, the linear version as future work, Zenodo DOI, the meet/join remark, value-restricted polymorphism, implicit sequencing.
- **Tang et al.:** Thms 3.2–3.6.
- **System C:** Coq mechanization (§4.5.4), Cor. 4.8.
- **Dynamic Wind:** Thm 3.6, the "best practices" caveat, the summaries of Leijen and OCaml.
- **Effect Handlers, Evidently:** scoped resumptions, the dynamic guard, constant offsets, `opevil`, shallow handlers.
- **Yoshioka et al.:** Def. 5.1, Thms 5.8, 7.2, 7.4, 7.7.
- **Yarrow:** the abstract claim, revocation, undefined behavior for references into captured fibers, Flix undefined behavior via personal communication, OxCaml statements, the Muhcu limitation, the type system as future work.
- **Zhang & Myers:** Coq line counts, IxFree, the closed-label limitation.
- **Oxidizing OCaml:** the affine-closures quote; no mechanization mentioned.
- **Met:** Thms 4.3–4.4.
- **Ahman 2023:** partial Agda formalization.
- **Timany et al. 2024:** definition of well-bracketing, the fork rule, the conjecture about handlers.
- **Dreyer et al. 2010:** the quotes used.
- **Hazel:** the "entered once and exited twice" quote.
- **Retrofitting OCaml:** fibers moved, no pointers into the stack, `discontinue`, `Gc.finalise`.
- **Oxide:** `T-While`, `abort!`.
- **Lexa and Zero-Overhead:** simulation proofs.
- **Capabilities to Regions:** abstract.
- **Iris-WasmFX:** WasmFXCert in Rocq.
- **Program Logics à la Carte:** its three axioms.
- **Box calculus:** the Fourment & Xu Coq mechanization.
- **Koka book:** the passages quoted.

I also re-checked by web fetch:
- The `std::thread::scope` source (`catch_unwind`, then join).
- The Sekiyama et al. abstract.
- Crossref metadata for Capless, FP², Ho et al., Leijen 2017, Blaze, Ikemori et al., Lutze et al. 2023 and 2024, Wu et al. 2014, Sieczkowski et al. and Fowler et al.
- The arXiv abstracts of Kobayashi & Kameyama and Balik et al.
- The MSR page for Brachthäuser & Leijen.
- The Ante post (the quotes used; it contains no `Mutate` effect and no rule forbidding a handler from mutating borrowed places).
- The Hylo documentation.
- The `UnwindSafe` documentation.
- The libstdc++ forced-unwind rethrow pattern.
- Clippy's `await_holding_*` lints.

**Relayed from the research passes,** which fetched primary sources. Their uncertainty markers are kept above. This covers:
- the mechanization verdicts for Capless, Classifying Capabilities, Capybara, Iris-Lean, olaf-coq, abseff-coq, scala-escape, the Hazel/TES thesis repositories, Blaze, and λrgnUL (Twelf);
- the Swift, Kotlin, OxCaml and rustc documentation items;
- the classic-lineage DOIs.

**Still uncertain.**
- Whether the translation and soundness proofs of System Ξ are mechanized.
- The repositories for Yarrow and Iris-WasmFX.
- The JFP extension of ExEff.
- The year of Higher-Order AEff.
- ATS effect syntax and its leak-on-exception behavior.
- Whether Granule has user-defined handlers.
- Whether Koka's finalization exception can be caught.
- The GHC primops capture restrictions.
- The details of Berdine et al. 2002.
- Whether one-shot-only polymorphic operations avoid the signature-restriction problem in general.

**Not verified.** No award claims were checked.


# What is proved

The language's safety guarantees are proved in Lean, not just tested. For you as a programmer,
that means a program `bcc check` accepts:

- never uses memory after freeing it, and never frees it twice;
- never leaks: when it finishes, everything it allocated has been freed;
- terminates, unless its type says it may loop (a `while`, a `loop`, or a call of a function
  that has one);
- does only the I/O its signature allows: a function with no I/O effect can't touch a stream.

This holds however the program uses effects: errors that unwind through borrows, handlers,
generators and cancelled tasks are all covered. Better still, it isn't just a claim about the
checker: every time `bcc check` accepts a program, it builds a proof for that particular program.

The rest of this page is for readers who want the details: the theorems, where they live in the
Lean sources, what is trusted, and what is not claimed. Every result below is checked before each
merge. None depends on an axiom beyond Lean's standard three (`propext`, `Classical.choice`,
`Quot.sound`), and the library contains no `sorry`, `native_decide` or `partial`
(`scripts/check-hygiene.sh`).

## The theorems, in plain language

**Every typing rule is sound.** The typing judgment of the core is `CDerives`. Its meaning is a
logical relation over a model of memory: a well-typed term, run in any memory that its inputs'
types describe, finishes with a result of its type and leaves memory described by the result's
type. The Fundamental Property says that every derivable judgment holds in this model.
`fundamentalC` in [`Core/Fundamental.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/Fundamental.lean).

**Closed programs run safely and leave memory empty, on every run.** Take a closed program of
type `F 1` and any allocator that returns free locations. No run of it from empty memory gets
stuck, and every run continues to `()` at empty memory (`adequacyD`, `adequacyD_safe` in
[`Core/Demonic.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/Demonic.lean)). Because no run gets stuck, there is no use after
free or double free; because memory ends empty, there is no leak. `adequacyC` and `theorem32`
are the paper's form, that some run succeeds; `adequacyD_obs` gives every run at any answer type
that holds no resource.

**Loops are covered one observation at a time.** A `delay` loop observed any number of times and
then closed runs to a value and leaves memory empty (`drive_runs_unit`, `drive_runs_nat` in
[`Core/DelayPrograms.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/DelayPrograms.lean); `take_runs` for streams in
[`Core/StreamPrograms.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/StreamPrograms.lean)).

**The checker produces proofs.** When `bcc check` accepts a program, the checker has built a
`CDerives` derivation for `main`'s erasure: every step of the checker applies one typing rule
to the proofs of its premises. `checkProgram_sound` in
[`Frontend/Check/Program.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Frontend/Check/Program.lean) states it, and `checked_sem` and
`checked_runs` apply the two theorems above to the checked program. The drops that the checker
inserts ([Implicit destructors](elaboration/implicit-destructors.md)) are part of the derivation.

**Elaborated handlers mean what their clauses say.** A surface handler (SPEC §18) is defined by
its elaboration into core terms ([Effects and handlers](guide/effects.md)), so a handled program is safe by the theorems
above with no new case. What could still be wrong is what a handler *means*, and each class of
clause has its law, about the machine's runs of the terms the elaboration emits
([`Core/Handlers.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/Handlers.lean)).
An answering operation is its clause run on the handler's state in place, the rest of the body
resumed once with the answer (`op_tail`, `op_answer`), and a handled body that performs
operations runs the clauses one after the other on the threaded state (`handle_fold`). Control
operations, errors among them, are the kernel's handlers below, and their laws (a value reaches
the return clause, an operation its clause with the continuation, an operation of another name
passes the handler) are machine lemmas in
[`Core/EffMachine.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/EffMachine.lean)
(`catch_unr`, `catch_cell`, `catch_fwd`, `fwd_resume`, `fwd_abort`).

**Handlers in the kernel.** SPEC §19 adds to the kernel the primitives `perform`, `raise`, `hnd`,
`ubind` (a finaliser frame), `ccatch` and `cfin` (a cancel's catchers), and the effectful returner
`F_Σ A`, a computation of `A` that may perform the operations of the row `Σ`. Its relation is
`ewpTS`, a least fixed point: the computation performs finitely many operations, each at its
protocol, and then answers. So the relation gives total correctness and safety at `F A`,
finitely many operations at `F_Σ A`, and termination of each observation at `ν` types, including
a loop whose observations perform operations.

Each of the six rules has its compatibility lemma
(`sub_compatC`, `perform_compatC`, `raise_compatC`, `let_compatC`, `then_compatC`,
`handle_compatC` in [`Core/EffRules.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/EffRules.lean)), and
`fundamentalC`, `fundamentalD` and `adequacyD` cover the extended judgment.

An operation that raises crosses a borrow: each borrow has an unwinding form, which ends the lend and runs the
source's finaliser before the unwind continues outward. Its obligations are the frame lemmas
`ewpTS_I_frameU`, `ewpTS_M_frameU` and `ewpTS_M_antiFrameU` in
[`Core/EffWp.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/EffWp.lean), used by
[`Core/EffBorrow.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/EffBorrow.lean).

Cancelling a stored continuation runs
its finalisers innermost first, with the handlers of the cancelled region dead, and answers `()`,
or re-raises at the canceller the first error a finaliser raised, to the nearest live handler of
its name; the outcomes are run in
[`Core/EffCancel.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/EffCancel.lean) (`prog₃_run`, `progRe_run`, `progFinOp_run`, …).

The six acceptance programs of §19 (two effects in both nesting orders, logging and raising inside a
borrow, an infinite loop that logs, early exit from a producer that holds a cell, and
cancelling a stored continuation) are closed derivations in
[`Core/EffPrograms.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/EffPrograms.lean), each with its every-run theorem
(`logOutside_answers`, `reborrowRaise_answers`, `tickProg_runs`, `takeProg_runs`,
`storeCancel_runs`, …). The surface's control handlers, `raise` and `await` elaborate to these
primitives (SPEC §18), so the theorems cover them with no case of their own.

**Arithmetic is a parameter.** The machine performs integer operations through a *host*, and
every theorem above holds for every host. Nothing about arithmetic is assumed.

**Arrays are covered by the same two theorems.** Each array constant is a typing rule with its
compatibility lemma in
[`Core/Arrays.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/Arrays.lean):
`array_new` places the cells at fresh consecutive locations and fills them, `array_free` frees
them one by one, and `array_get` hands out one element's view. The family of an array's element
views comes from `withload`, whose rule was already sound; what it needs of the new type is that
every lemma about the model proved by induction on types has its array case, and each has.

**Programs with standard I/O are safe for every implementation of their externs.** The
capabilities and their operations are externs, hypotheses rather than rules. The model of each
operation, ordinary core terms over a byte list in a cell, meets its extern's type
(`readByte_meets`, `writeByte_meets`, … in
[`Core/Stdio.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/Stdio.lean)).
For every implementation that meets the types, every run of the program's `run_io` wrapper from
empty memory continues to its outputs at empty memory, under every allocator
(`externs_every_run`); `bcc interp` runs the model, and `IORun.every_run` is the theorem at the
very term it runs. A cell owned outside a computation keeps its value through every run of it
(`wpTSD_frame_own`): a function given no capability does not touch the stream in it. A program
that runs until its input ends returns a loop, which the runtime drives; it is covered one
prefix at a time, observed at most `n` times for every `n` (`externs_loop_every_run`,
`IORun.loop_every_run`). The I/O sugar is elaborated before checking, so these theorems are
about the elaborated program, with no case of their own.

**Code without divergence terminates.** A closed program of type `F A`, including one that
performs operations and handles them, terminates on every run: there is no infinite run of it (`total_no_infinite_run` in
[`Core/Totality.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/Totality.lean)),
and under every allocator its run reaches a value (`total_every_alloc`). Divergence shows in the
type, as a loop the program returns ([Divergence](elaboration/divergence.md)); a total function that
runs a loop under a fuel bound is still of type `F A`, and covered.

**The baseline is preserved.** The paper's calculus (BoCa) and its logic (BoLo) embed into the
core, and the paper's Fundamental Property and adequacy hold as before.
[`Paper/INDEX.md`](https://github.com/empath-nirvana/borrow-core/blob/main/Paper/INDEX.md) indexes each result of the paper to its Lean declaration,
and [`docs/adjudications.md`](https://github.com/empath-nirvana/borrow-core/blob/main/docs/adjudications.md) records each departure from the printed
text.

## What is trusted

- **The compiler is tested, not yet proved.** Each stage has an interpreter. Every corpus program
  and every runnable example in this book gives the same answer compiled as under the Lean
  interpreter, and ends with `live 0`. Proving the compiler correct is planned.
- **The handler lowering is tested, not verified.** There is no runtime handler stack and no
  handler search: an abortive operation is a branch after each call that may raise
  (`Backend/Clos/Unwind.lean`), a tail-resumptive operation whose handler is known is a direct
  call of its clause, and other control operations and stored continuations are state machines
  with one flat tagged state, nested through calls (`Backend/Clos/Capture.lean`). Every kernel
  program gives the same answer at every stage and in WebAssembly, with `live 0`
  (`scripts/compile-kernel.sh`).
- **The allocator** is WebAssembly text, trusted against its written specification
  ([`Backend/README.md`](https://github.com/empath-nirvana/borrow-core/blob/main/Backend/README.md)).
- **The WAT printer and wasmtime** are trusted.
- **Integer operations**: that WebAssembly's instructions agree with the interpreter's host is
  tested (`corpus/int-ops.bc`).
- **The host implementations of the externs**: that WASI `fd_read`/`fd_write` behave as the
  model is tested on the corpus, not proved. `bcc trusted` lists each boundary with its level.

## What is not claimed

- A program that holds a borrow across a suspension (a task that lends its own cell across
  `await`, the relaxed lend of SPEC §29) is covered under `PinLaw`, a hypothesis stated in Lean
  ([`Core/PinLaw.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/PinLaw.lean))
  and not yet proved: `fundamentalC_pin` and `adequacyD_pin` assume it.
  [`docs/async-capabilities.md`](https://github.com/empath-nirvana/borrow-core/blob/main/docs/async-capabilities.md)
  §4 gives the evidence for it, and the corpus has programs that try to break it. `bcc check`
  prints `assurance: PinLaw (R1 at L:C)` for such a program and `assurance: unconditional`
  otherwise, so you can always see which programs rely on it.

- A loop (`delay`, `loop`, a div function) is not claimed to terminate; its type says it may not.
  The same holds for a computation that performs operations forever: it is typed as a loop whose
  observations are effectful, not at `F_Σ A`.
- That the elaborator emits exactly the schemas the handler laws are about is by construction of
  `Frontend/Elab/Effects.lean`, checked on the sugar pairs, not proved.
- The checker is not complete: a well-typed program may be rejected (`Frontend/README.md`,
  *Incompleteness*).
- Nothing is claimed about host handles: adequacy's empty memory is the model's cells, not file
  descriptors (whether a stream was flushed or closed). I/O errors are not modeled.

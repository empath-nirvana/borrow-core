# What is proved

Everything below is a Lean theorem, checked by CI on every change. No result depends on an axiom
beyond Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`), and the library
contains no `sorry`, `native_decide` or `partial` (`scripts/check-hygiene.sh`).

## The theorems, in plain language

**Every typing rule is sound.** The typing judgment of the core is `CDerives`. Its meaning is a
logical relation over a model of memory: a well-typed term, run in any memory that its inputs'
types describe, finishes with a result of its type and leaves memory described by the result's
type. The Fundamental Property says that every derivable judgment holds in this model.
`fundamentalC` in [`Core/Fundamental.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/Fundamental.lean).

**Closed programs run safely and leave memory empty.** A closed program of type `F 1` runs from
empty memory to `()` and empty memory (`adequacyC`, same file). Because the run never gets
stuck, there is no use after free or double free; because memory ends empty, there is no leak.
`theorem32` gives the same for a program that returns a value, given that the value holds no resource.

**Loops are covered one observation at a time.** A `delay` loop observed any number of times and
then closed runs to a value and leaves memory empty (`drive_runs_unit`, `drive_runs_nat` in
[`Core/DelayPrograms.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/DelayPrograms.lean); `take_runs` for streams in
[`Core/StreamPrograms.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/StreamPrograms.lean)).

**The checker produces proofs.** When `bcc check` accepts a program, the checker has built a
`CDerives` derivation for `main`'s erasure: every step of the checker applies one typing rule
to the proofs of its premises. `checkProgram_sound` in
[`Frontend/Check/Program.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Frontend/Check/Program.lean) states it, and `checked_sem` and
`checked_runs` apply the two theorems above to the checked program. The drops that the checker
inserts ([Implicit destructors](guide/implicit-destructors.md)) are part of the derivation.

**Handlers mean what their clauses say.** A handler is defined by its elaboration into core
terms ([Effects and handlers](guide/effects.md)), so a handled program is safe by the theorems
above with no new case. What could still be wrong is what a handler *means*, and each class of
clause has its law, about the machine's runs of the terms the elaboration emits
([`Core/Handlers.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/Handlers.lean)).
An answering operation is its clause run on the handler's state in place, the rest of the body
resumed once with the answer (`op_tail`, `op_answer`), and a handled body that performs
operations runs the clauses one after the other on the threaded state (`handle_fold`). An abort
passes every branch around it, running none of the rest, and reaches the handler as `inr e`
(`abort_passes`), also from inside a loop, whose exit it takes (`loop_abort`); a value runs the
rest (`return_resumes`).

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

**Code without divergence terminates.** A closed program of type `F A` terminates on every run:
there is no infinite run of it (`total_no_infinite_run` in
[`Core/Totality.lean`](https://github.com/empath-nirvana/borrow-core/blob/main/Core/Totality.lean)),
and under every allocator its run reaches a value (`total_every_alloc`). Divergence shows in the
type, as a loop the program returns ([Divergence](guide/divergence.md)); a total function that
runs a loop under a fuel bound is still of type `F A`, and covered.

**The baseline is preserved.** The paper's calculus (BoCa) and its logic (BoLo) embed into the
core, and the paper's Fundamental Property and adequacy hold as before.
[`Paper/INDEX.md`](https://github.com/empath-nirvana/borrow-core/blob/main/Paper/INDEX.md) indexes each result of the paper to its Lean declaration,
and [`docs/adjudications.md`](https://github.com/empath-nirvana/borrow-core/blob/main/docs/adjudications.md) records each departure from the printed
text.

## What is trusted

- **The compiler is tested, not yet proved.** Each stage has an interpreter. Every corpus program
  and every runnable example in this book gives the same answer compiled as under the Lean
  interpreter, and ends with `live 0`. The plan for proving it is #15.
- **The allocator** is WebAssembly text, trusted against its written specification
  ([`Backend/README.md`](https://github.com/empath-nirvana/borrow-core/blob/main/Backend/README.md)).
- **The WAT printer and wasmtime** are trusted.
- **Integer operations**: that WebAssembly's instructions agree with the interpreter's host is
  tested (`corpus/int-ops.bc`).
- **The host implementations of the externs**: that WASI `fd_read`/`fd_write` behave as the
  model is tested on the corpus, not proved. `bcc trusted` lists each boundary with its level.

## What is not claimed

- A loop (`delay`, `loop`, a div function) is not claimed to terminate; its type says it may not.
- The checker is not complete: a well-typed program may be rejected (`Frontend/README.md`,
  *Incompleteness*).
- Nothing is claimed about host handles: adequacy's empty memory is the model's cells, not file
  descriptors (whether a stream was flushed or closed). I/O errors are not modeled.

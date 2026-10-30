# Overview

borrow-core is the core of a systems language: linear ownership with Rust-style borrowing, in a
call-by-push-value calculus, with a compiler to WebAssembly. It starts from the Lean
mechanization of Wagner, Gierczak, Marshall, Li and Ahmed, *From Linearity to Borrowing*
(OOPSLA 2025), whose calculus (BoCa) and logic (BoLo) are the baseline (`SPEC.md` §1).

## What the language has

- **Ownership and borrowing:** owned references, immutable and mutable borrows with lexical
  lifetimes, reborrowing, and the paper's borrow constructs (`SPEC.md` §1).
- **An exponential `!T`** for values holding no resource, so code can be borrowed and closures
  shaped like Rust's `Fn`/`FnMut` are expressible (§2).
- **Call-by-push-value:** value types and computation types kept apart, so thunks, codata and
  the cost of reification are explicit (§3).
- **Blocks and family borrows:** unboxed structs whose fields are separate places, borrowed
  together at one lifetime (§5).
- **Recursive types and folds:** `μ` with borrowed, owned and in-place folds as typing rules (§6).
- **Codata:** one former `νX. C` with coiteration; the delay type for loops that may not
  terminate, streams and finite iterators are abbreviations over it, each with a mandatory
  `close` (§7).
- **The closure `Clo`:** `Clo[A, B]<'c>` (`lib/clo.bc`), codata whose `call` takes an argument
  and hands back the rest: called any number of times, through a `mut` borrow, then closed; its
  captured state is hidden by its type (§22).
- **Integers and bytes:** `i32`/`i64` with Wasm's operations, and the byte `u8` (§8).
- **Arrays and slices:** `array A` owns `n` cells, read through the family of leaf views; slice
  borrows lend a run of an array, which can be split, and its elements replaced or swapped (§9).
- **Persistent variables:** values holding no resource are copied and dropped freely (§10).
- **Externs and standard I/O:** `stdin`, `stdout`, `stderr` as capabilities with opaque
  content, `read_byte`/`write_byte` on `mut` borrows of them, proved against their model and
  compiled to WASI `fd_read`/`fd_write` (§11).
- **Implicit destructors:** an owned value a path leaves unused is freed or closed by a
  destructor the checker inserts (§12).
- **Divergence as an effect:** a function whose body may loop without bound has a loop in its
  type; this is inferred, and `total def` asserts its absence (§14).
- **Generators:** `gen fn` with `yield`; each generator body is one state machine, and generic
  adapters over them are in `lib/adapters.bc` (§15).
- **Counted loops and `for`:** a loop over a count, with an early exit, and `for` over counts,
  arrays, views and iterators (§16).
- **Buffers, text and literals:** a growable `buf A`, UTF-8 `string` and text views, and string
  literals (§17).
- **Effects and handlers, by elaboration:** `effect`, `handler` and `with` declare and run
  answering operations, and `Fail` raises errors; both elaborate into capability passing and
  sums, with no change to the kernel (§18). Spellings are provisional.
- **Effects and handlers, in the kernel:** `perform`, `raise`, `hnd`, the finaliser frame `ubind`,
  and `ccatch`/`cfin` for cancels; the effectful returner `F_Σ A`; answering and control
  operations, a control operation's continuation must-resume, cancellable or unrestricted; unwinding, which
  ends each lend it passes; and cancelling a stored continuation (decision C of SPEC §19's
  *Cancels*: the canceller re-raises the first finaliser error that names a handler outside the
  cancelled region) (§19).

Recursion is the fixed point of a generator (decision 24, SPEC §20, §21): a function calls itself,
and functions call one another, as written; the group is the bounded fixed point of its generator,
each call a direct call of the self-reference, run by a driver chosen at the call site. Its
environment (the capabilities it uses) is passed with each call, and layers (`with L { … }`) are
transformers of the generator. The default, `bounded`, is the kernel's `bounded_fix`: a native recursion with a budget of
depth whose end performs `Exhausted` (`lib/rec.bc`), an abortive effect a handler catches. The
heap driver `deep` keeps the pending calls as first-order frames in one growable buffer and is
div. Pending: the layer `memo`, which needs a map (#211).

The kernel's effects are written as Lean terms (`Core/EffPrograms.lean`) and compiled with
`bcc kernel`; the surface does not reach them yet. Work in progress: the surface onto kernel
effects (#188), and `Yield` inside generators (#159).

## What is proved

All in Lean, with no axioms beyond `propext`, `Classical.choice` and `Quot.sound`:

- **Fundamental Property:** every typing rule is sound in the logical relation (`fundamentalC`;
  `fundamentalD` at the demonic `wp`). This includes §19's six rules (`Core/EffRules.lean`) and
  the unwinding forms of the borrows (`Core/EffBorrow.lean`). What the relation gives at each
  type:
  - at `F A`, total correctness: the computation terminates with a value of `A`, and the
    memory it leaves is described by the type (`wpTS`);
  - at `F_Σ A`, the computation performs finitely many operations of `Σ`, each at its protocol,
    and then answers a value of `A` (`ewpTS`, a least fixed point);
  - at `νX. C`, each observation terminates; the whole may be observed without end.
- **Adequacy, every run:** take a closed program of type `F 1` and every allocator that returns
  free locations; no run gets stuck, and every run continues to `()` at the empty memory: no
  use-after-free, no double free, no leak (`adequacyD`, `adequacyD_safe`). `adequacyC` is the
  paper's form, that some run succeeds; `adequacyD_obs` is the same at any persistent answer
  type. This covers handled programs; a closed program with an unhandled operation is not typed
  at `F 1`. Loops that may not terminate are covered observation by observation: observed any
  number of times and then closed, they leave memory empty.
- **Totality:** a closed program of type `F A`, handled effects included, has no infinite run
  (`total_no_infinite_run`), and every run of it continues to a value (`total_every_run`).
- **Checker soundness:** when `bcc check` accepts a program, it returns a proof of the typing
  judgment for it (`checkProgram_sound`), so the theorems above apply to it.
- **Elaborated handlers:** §18's handlers are core terms, safe by the theorems above; each class
  of clause has a law about the runs of the terms emitted (`op_tail`, `handle_fold`,
  `abort_passes`, `loop_abort` in `Core/Handlers.lean`).
- **Kernel handlers:** §19's acceptance programs (two effects in both nesting orders, logging and
  raising inside a borrow, an infinite loop that logs, early exit from a producer, cancelling a
  stored continuation) are closed derivations whose every run is safe and ends at the empty
  memory (`Core/EffPrograms.lean`).
- **Parametric arithmetic:** every theorem holds for every implementation of the integer
  operations, so nothing about arithmetic is assumed.
- **Externs:** a program with standard I/O is safe and leak-free on every run for every
  implementation of its externs that meets their types (`externs_every_run`,
  `io_loop_every_run`); the model of each operation meets its type (`readByte_meets`, …), and a
  function given no capability does not change the stream in it (`wpTSD_frame_own`).

## What is trusted, and what is tested

- **The compiler is tested, not yet proved.** Every corpus program gives the same answer compiled
  as in the Lean interpreter (its golden `.out`, re-verified against the interpreter by
  `make gate-full`), and ends with no live objects (`scripts/compile-corpus.sh`). Every
  kernel program gives the same answer at every stage (`scripts/compile-kernel.sh`).
- **The handler lowering is tested, not verified.** There is no runtime handler stack and no
  handler search. An abortive operation is a branch after each call that may raise
  (`Backend/Clos/Unwind.lean`); a tail-resumptive operation whose handler is known is a direct
  call of its clause (#207); other control operations and stored continuations are state
  machines with one flat tagged state, nested through calls (`Backend/Clos/Capture.lean`).
- **The allocator** is trusted against its written spec (`Backend/README.md`).
- **The WAT printer and wasmtime** are trusted.
- **The host implementations of the externs** (WASI `fd_read`/`fd_write`) are assumed to behave
  as their model; `bcc trusted` lists them with their assurance levels.

The plan for proving the compiler is #15.

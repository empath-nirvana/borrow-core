# Addendum: `bounded` and `deep`

Status: the design as built for #188 stage 3 (#158), SPEC §20, decision 58. It supersedes the
README's drivers (`fix` on the host stack, `fuel`, tabulation) where they differ; the README's
corpus and requirements stand as the record of what was explored.

## 1. The two drivers

A recursive group (a function that calls itself, or functions that call one another) is run by
a driver chosen at the call site.

- **`bounded`**, the default, needs nothing written. It is the kernel's `bounded_fix`: a native
  recursion that carries a **budget of depth**, each call with one less. A recursion whose depth
  is bounded, and each of whose levels makes finitely many calls, terminates: so it is total, and
  it runs inside one computation as an ordinary native recursion (direct calls of known code,
  nothing allocated). When the budget is spent, the recursion performs `exhausted()`.
- **`deep`**, written `with deep { … }`, keeps the pending calls as **first-order frames** in one
  growable buffer, `buf (1 + K)`: a call that is not in tail position pushes the variables the
  rest of its body uses, an answer pops them. It is limited only by memory, and it is div.

## 2. `Exhausted`

`effect Exhausted { ctl exhausted() -> never }` (`lib/rec.bc`) is an ordinary abortive effect,
like `Fail`. It sits in the row of recursive code where `div` sits in the row of a loop. An
`exhausted()` unwinds: the finalisers of every level run, innermost first (each level's drop glue
around its call, SPEC §19), and a handler receives it: `on_exhausted(d)` answers `d(())`,
`exhausted_to_option` answers `inr ()`. `corpus/rec-overflow.bc` is the test: a recursion a
hundred times past the budget, a cell held at every level, `live 0` at the end.

**Embedded platforms.** A platform that provides no handler of `Exhausted` around `main`
rejects a recursion it does not handle, statically, as it rejects any unhandled operation
(`corpus/reject/rec-unhandled.bc`). The WebAssembly platform provides none today, so a program
handles it. Not built: a platform handler that reports exhaustion and exits.

## 3. The fuel is a stack check

The budget is a conservative abstraction of a stack check in each recursive function's entry
code.

- **WebAssembly** cannot inspect its stack, so the check is an explicit depth counter: the budget
  itself, a word passed down with each call (`bounded_fix`'s `k`). It is calibrated against the
  stack `wasmtime` runs with, which `bcc` sets to 64 MiB (`Backend.wasmStackBytes`,
  `-W max-wasm-stack`). Measured: a linear recursion uses about 120 bytes of native stack per
  level (it overflows `wasmtime`'s default 512 KiB between 4 000 and 4 500 levels). The budget is
  10 000 levels (`Frontend.Elab.Effects.recBudget`), about 1.2 MiB at that rate: room for bodies
  fifty times larger, and for what an unwind runs.
- **LLVM**, later: a Go-style comparison of the stack pointer against a limit in each recursive
  function's prologue, the limit the stack's end less the headroom. The budget then becomes
  global (one stack for every recursion) instead of per driver.

**Headroom.** The check must leave enough stack for unwinding: the worst-case stack use of the
finalisers an unwind runs. Decision C (SPEC §19) limits a finaliser to abortive and answering
operations; a finaliser that is recursion-free has a bound computed from the call graph with
`rec` removed, which is a DAG. Frame sizes are not computed yet, so the headroom is the margin
of the measured constant above (provisional).

**Not exact.** The budget is per driver: a recursion running inside another's body has a budget of
its own, so their native depths add. A recursion nested ten deep, each at its budget, would need
ten times the stack. The LLVM check makes it one.

## 4. Why neither (a) nor (b)

The first report (§3.2 of the README, and this stage's report) found that a `fix` whose `rec` is a
native call cannot be typed: a closed computation of `F A` terminates (`Core/Totality.lean`), so
one observation of a loop cannot hold a whole recursion, and pending frames of an unbounded
recursion must live in a loop's state between observations.

- **(a) Partial correctness** in the kernel (a relation in which an observation may diverge) was
  ruled out: it changes the relation, and every theorem with it.
- **(b) Refunctionalising** the heap machine in the backend (fusing a loop's observations into
  native recursion when nothing counts them) was dropped: a whole-program analysis that `div_fuel`
  defeats.
- **(c), taken:** bound the depth. A recursion with a budget is total, so the native recursion is
  typed by one new constant whose soundness is an induction on the budget, and the unbounded
  case is the heap driver.

## 5. The frames of `deep`

The frames are the elaborator's, first order: a variant of `K` per call site that is not in tail
position, holding the variables live there with their types (`Frontend/Sugar.lean`,
`recMachine`). They are not kernel continuations stored as closures, which the first prototype
did (a continuation turned into `ν` codata answering through an outer operation, 2 allocations
and 4 dispatched calls per call): a thunk has no filler, so it cannot be a buffer's element
(SPEC §17).

The buffer's element is `1 + K`, its empty slots `inl ()`: `1 + K` has a filler whatever `K`
holds, so a frame may hold an owned `μ` value (a tree's right subtree, `corpus/rec-deep.bc`) or a
cell. The buffer doubles when it is full: a few allocations per run (a dozen to reach 30 000 frames),
none per call. Measured: `fib` under `deep` makes 3 allocations, and no dispatched call.

**A frame that holds a borrow.** A frame is pushed into a buffer that outlives the step, so a
borrow it holds would cross observations; a recursion under `deep` that holds a borrow across a
call is not exercised (a recursion that performs an effect is not provided under `deep`, and a
borrow passed to a recursive function is a lifetime parameter, which a recursive function does
not take yet).

**Follow-ups.**
- Tail recursion modulo context (Leijen and Lorenzen, POPL '23): some frames could be made
  smaller, or vanish, before they reach the buffer.
- `fold_imm`, which keeps a native frame per level of the structure, could use the same buffer
  and lose its depth limit.
- If a frame type had no filler even as `1 + K` (it always has one), the fallback was a LIFO free
  list of linked frames (AxCut, Schuster et al., OOPSLA 2025).

## 6. What is not provided

- `memo`: it needs a map (#211).
- A recursion whose body has a `while` or a `loop`; one that performs an operation that resumes;
  one that uses an answering effect's capability; a recursion under `deep` that performs any
  effect; a generic recursive function; members of one group answering different types.
- Recursion through a site (decision 57): a call of itself inside a handler of an effect its
  recursion performs needs a site per level (`corpus/reject/rec-through-site.bc`). Decision 57's
  exact pattern, a callback that raises passed down the recursion, is rejected earlier: a
  function with a row passed as a value is #161.

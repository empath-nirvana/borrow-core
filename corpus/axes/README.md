# The three axes, and the programs we can't write yet

The strict account of data/codata and effects/coeffects (branch `coeffects-strict`, PR #101,
`experiments/CoeffectsStrict/README.md`) classifies the language along three independent axes:

- **polarity**: data (`mu` on value types) or codata (`nu` on computation types);
- **direction**: effects, the output side (`F`; `mut` capabilities and I/O are linear state,
  `alloc` is an operation of the ambient monad), or coeffects, the input side (an `imm` demand is
  the reader comonad; `!` and `[@a]` are context modalities);
- **scope**: owned, or borrowed at `'a` (`withbor` is a scoped operation, sound by a global
  store invariant).

This directory holds small programs for each axis and each combination, in the surface where it
suffices and in core where it does not. `corpus/pending/` holds the programs a user would
naturally write that the language cannot express yet, one per current limit.

**How they are checked.** Every `corpus/axes/*.bc` is part of the corpus: it parses, checks,
and runs at every stage (`bcc interp`, the closure and flat IRs, and wasm under wasmtime) with
the same answer and `live 0`, against its golden `<name>.out` where it has one, and within its
line in `corpus/counts.expected` (`scripts/parse-corpus.sh`, `check-corpus.sh`,
`compile-corpus.sh`). Every `corpus/pending/*.bc` names its blocker on a
`-- pending:` line and records today's error on its `-- now:` line; `scripts/check-corpus.sh`
checks that it still fails with exactly that error. When a feature lands and a pending program
checks, the gate fails with "checks now: move it into the corpus with its golden output". The
expected golden is in the program's header.

Each header names the axes, says what the program does, and states the answer and what the
plausible bugs would print (or, for a pending program: what blocks it, what the checker does
today, and the golden once it lands).

## Programs that run

| program | axes | combination | status |
|---|---|---|---|
| `data-effects.bc` | data × effects, owned | a list built while the input is echoed; then a `fold_own` into an effectful function writes it reversed | runs |
| `data-coeffects.bc` | data × coeffects, borrowed | two `fold_imm`s through one `imm` borrow, `copy`'d (the reader comonad) | runs |
| `codata-effects.bc` | codata × effects, owned | an iterator whose state owns `stdout`; each `next` writes; consumed by `for` | runs |
| `codata-coeffects.bc` | codata × coeffects, borrowed | two cursors over one borrowed array family (`array_copy`), counting increases | runs |
| `scope-data-effects.bc` | data × effects × scope | an in-place `fold_reuse` under a `mut` borrow; a `fold_imm` with output inside an `imm` borrow block | runs |
| `scope-codata-effects.bc` | codata × effects × scope | an iterator holding `mut 'x output` inside `borrow mut stdout` | runs |
| `scope-loop-lend.bc` | codata × effects × coeffects × scope | a `for` over the input that lends a table `imm` on every step | runs |
| `borrow-across-loop.bc` | codata × effects × coeffects × scope | a `for` over the input inside a borrow block of a table, lent per observation (SPEC §14) | runs |
| `scope-boxed-iter.bc` | codata × coeffects × scope | an iterator holding a borrow leaves an inner borrow block as `[@w] U(iter …)` (the account's §6, test case 2) | runs |
| `free-monad.bc` | effects × data | a program of `write` operations as data, handled by two folds (the account's §3: handlers are folds) | runs |
| `codata-generic.bc` | codata × effects, independence | one consumer written once, run on a pure iterator and an I/O iterator (the account's §6, test case 1) | runs |
| `effects-coeffects.bc` | effects × coeffects | a `!` function with an `imm` demand and a capability, called three times; no distributive law is needed | runs |
| `result-fold-own.bc` | data × effects (failure), owned | baseline: a hand-threaded `Result` in a `fold_own` (Rust's `try_fold`); every node freed on the error path | runs |
| `result-fold-imm.bc` | data × effects (failure) × scope | baseline: the same in a `fold_imm`; the borrow is handed back on the error path | runs |

The two `result-fold-*` programs are baselines, for comparison with the error effect
(`pending/raise-in-fold.bc`) and to test the error path's cleanup; they are not the intended
style.

## Programs we can't write yet

"Pending" means inexpressible today, whatever the reason: a surface form not built, a kernel
rule not stated, or a design question not settled. For the design questions, the header lists
the options and their trade-offs and settles none of them.

| program | axes | blocked by | where | status |
|---|---|---|---|---|
| `map-div-fold.bc` | data × effects (div) | a div callback called inside a fold's algebra is not specialized, even in the whole program; separately compiled, it needs effect polymorphism (no variable over computation types) | surface; kernel for separate compilation | pending (SPEC §14, #63) |
| `callbacks-in-data.bc` | data × effects (div) × coeffects | a callback stored in data keeps its written effect, so a list cannot hold a total and a div callback | surface, then kernel; open design question | pending (SPEC §14 Open) |
| `async-borrow.bc` | codata × effects × scope | `async fn`, `spawn`, `.await`, a scheduler; a scheduler over tasks at different lifetimes | surface, runtime; open design question | pending (#52) |
| `iter-mut.bc` | codata × effects × scope | no family of leaf `mut` borrows `[Mut 'c A]`, no `iter_mut` | kernel | pending (#57, SPEC §9 Open) |
| `noalloc.bc` | effects | `F` is not graded and `alloc` is untracked, so no type says "does not allocate" | kernel; open design question | pending (the account's §8 item 5) |
| `dig-bang.bc` | coeffects | digging `!A ⊸ !!A`, valid in the model, is not a rule; promotion is at `fun`/`Fun` only | kernel | pending (SPEC §2 Open) |
| `box-dup.bc` | coeffects × scope | same-lifetime `[@a]A ⊸ [@a][@a]A`, valid in the model, is not a rule (`VOutlives.box` is strict) | kernel | pending (the account's §8 item 6) |
| `two-writers.bc` | effects × scope | two live `mut` borrows of one capability in one call: `Mut ⊸ Mut ⊗ Mut` is not a rule | open design question | pending |
| `data-box-tree.bc` | data × coeffects × scope | `data`, `box`, constructor patterns, fold blocks | surface | pending (#54, stage 8) |
| `needs-stdout.bc` | effects × scope | `needs`/`provide` (PR #100's `KDem`), elaboration only | surface | pending (PR #100) |
| `backtrack-multishot.bc` | effects × codata × scope | handlers; a continuation `U C` is linear, so one-shot | surface; open design question | pending (#18) |
| `fold-under-u.bc` | effects × data | an operation with an input (`read`) puts `X` under `U`, outside `FShape` and outside `mu` | kernel | pending (SPEC §6) |
| `raise-in-fold.bc` | data × effects (failure) × scope | `raise`/`try`; the folds are not polymorphic in their algebra's effect; unwinding of the abandoned rest | surface, kernel; open design questions | pending (#18) |
| `print-borrowed-list.bc` | data × effects × coeffects × scope | `fold_imm`'s result must outlive every lifetime, so it cannot be a writer; no borrowed list iterator | kernel | pending (#57) |
| `closure-captures-int.bc` | coeffects × data | a `!` closure may capture only `!` values, not an `i32` | kernel | pending (#9, SPEC §10 Open) |
| `for-finite.bc` | codata × effects (div) | `for` over a count, total | surface | pending (#54, stage 9) |
| `lend-nested.bc` | coeffects × scope | a lend inside an operator's operand | surface | pending (#54, decision 38) |
| `lend-two.bc` | effects × coeffects × scope | two lends in one call | surface | pending (#54, SPEC §14 Open) |
| `closure-lend.bc` | data × effects | a lend to the call of a local closure, `w!(&mut stdout)` | surface | pending (#54) |

Where a pending program meets a recorded decision, its header cites it, and the decision is
revisitable like any other: `needs-stdout.bc` keeps decision 30 (no ambient authority: only
`main` holds a capability, and a need is in the function's type); `map-div-fold.bc` and
`callbacks-in-data.bc` meet decision 8 (monomorphization, no type `∀` in the core) through
SPEC §14's specialization; `generator-handler.bc` and `async-borrow.bc` follow decision 25
(control effects lower to state machines) and decision 15 (a suspended computation is codata);
`noalloc.bc`'s grade would go in the type former, not on `CDerives` (decision 19).

## Which pending items look most valuable

Judged by how natural the program is, and how often a user would write it:

1. **`data-box-tree.bc`** (stage 8): `data` and `box` replace hand-written `mu`, `shape` and
   `roll` in every program with a list or a tree.
2. **`print-borrowed-list.bc` and `iter-mut.bc`** (#57): iterating a borrowed collection, reading
   or updating each element, is the most common loop in systems code. Arrays can be read today
   (`codata-coeffects.bc`); lists and `mut` elements cannot.
3. **`for-finite.bc`** (stage 9): a `for` over a count in a total function.
4. **`closure-captures-int.bc`** (#9): a fold or callback that uses a parameter, as
   `map(|x| x + n)` does. The model already validates it (`vCE_empty_of_persistent`).
5. **`lend-nested.bc`, `lend-two.bc`, `closure-lend.bc`**: small surface gaps, each met in the
   first programs written here, and each reported with a message that does not mention the lend.
6. **`raise-in-fold.bc`, `generator-handler.bc`** (#18): errors and generators are the first
   control effects users will reach for.
7. **`map-div-fold.bc`, `callbacks-in-data.bc`**: div callbacks in folds and in data.

Less natural, each needed mostly through generic code or in niche programs: `dig-bang.bc`,
`box-dup.bc` (the model validates both; each is one lemma), `noalloc.bc`, `two-writers.bc`
(Rust rejects it too), `backtrack-multishot.bc`, `fold-under-u.bc`, `async-borrow.bc` (until
there is a runtime), `needs-stdout.bc` (ambient `main` and `&mut` cover the common case).

## What writing them found

**Expressible after all.**

- **Codata capturing a borrow across a scope** (`scope-boxed-iter.bc`). SPEC §7 Open says an
  iterator over a borrowed buffer "is not yet written as a program", and the account's §6
  (test case 2) predicts `[]I` at `U(nu X. C)` covers it. It does, today, in core: a cursor over
  an array's leaf views is boxed at an inner lifetime, leaves the inner borrow block, and is
  consumed in the outer one. The `mut` version (`iter-mut.bc`) still waits for leaf `mut`
  families.
- **`for` over any iterator a function returns** (`codata-effects.bc`: `for x in ticks(&mut
  stdout, 5)`), with a capability lent to it and handed back when it finishes. SPEC §14 Open
  still says "`for` iterates only over `bytes c`"; the restriction that remains is that `for`
  always makes its function div.
- **I/O inside a borrow block** (`scope-data-effects.bc`): the capability is passed into the
  block and handed back out with its result. There is no sugar for it, but no limit either.

**Blocked for a reason not in the list of current limits.**

- **A loop inside a borrow scope** (`borrow-across-loop.bc`, now running). A borrow block's body
  is one computation of `F`, and a div body returns a loop, which cannot leave the scope that
  holds its borrow. This is the account's "`withbor` is a scoped, non-algebraic operation" met by
  the div effect. It is met by lending again at each observation (SPEC §14, borrow scopes over
  loops): the elaborated program is `scope-loop-lend.bc`'s. What remains is a loop whose codata
  holds the borrow itself (a pipeline over a borrowed source); it also bounds scoped spawning for
  async (#52).
- **A div callback inside a fold's algebra is not specialized** (`map-div-fold.bc`), even in the
  whole program: SPEC §14's specialization reaches callbacks called on a function's spine, not
  inside the `!` closure a fold takes. This is the case of `map` over a list, before separate
  compilation enters.
- **A `!` closure cannot capture an `i32`** (`closure-captures-int.bc`, #9), so a fold or callback
  cannot use a function's integer parameter. It shaped two of the programs here.
- **`fold_imm` cannot compute a writer** (`print-borrowed-list.bc`): its result must outlive
  every lifetime and a thunk outlives none, so printing a borrowed list element by element needs
  #57, while an owned list can be printed by `fold_own` (`data-effects.bc`).
- **The order of errors differs between the effect and the baseline** (`raise-in-fold.bc`): a
  fold's algebra runs on the way back up, so a `raise` reports the last bad element in list
  order, where the hand-threaded `Result` chooses the first.
- **Lends**: a lend in an operand (`lend-nested.bc`), two lends in one call (`lend-two.bc`; the
  message depends on their order), a lend to a local closure's call (`closure-lend.bc`), and a
  lend in tail position (`sum(&t)` as a body's last expression: "it may appear only in the head
  `M` of `y <- M; N`").

**Smaller things met on the way** (none changed here):

- Reserved words that collide with names a user or library would choose: `iter`, `node`, `leaf`,
  `fam`, `total`, `run`.
- `>` inside `< … , … >` closes the pair, so `if i > n` in a step's observation is a parse error;
  written `n < i`.
- Messages that name the elaborator's variables (`io_lm42_3` in `two-writers.bc`), and a
  declaration error that lists `type`, `shape`, `def`, `extern` or `main` but not `fn`, `total`
  or `include`.
- An ill-formed type abbreviation is reported after the closures that use it
  (`fold-under-u.bc`), and an unknown function in a `for` after a later error in the loop's body
  (`iter-mut.bc`).

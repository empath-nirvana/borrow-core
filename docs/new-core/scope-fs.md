# Scope — `Fs`: files as the platform's effect, on #804's guarantee

Plan for #769. Status: for review. No `Fs` code is written. This revision replaces the plan on
branch `fs-plan` (f3de34cb). That plan represented `File` as a two-way thunk
`U(F (ref input) & F 1)` for one reason: a `ν` observation could not take `&mut buf`, because
`CTy.NuLeaf` had no lifetime-polymorphic argument. #808 (on main) adds the `∀` case to `NuLeaf`,
so that reason is gone. Here `File` is a real `ν` object whose observations take borrowed
buffers.

**Kernel target: no kernel change.** No `CDerives` rule, judgment, type former or relation clause
is added. What is added sits at §11's extension point, "a new host resource is a new `k` with its
model, not a new former", which is how `clock` and `args` were added (§34): one opaque kind `fs`,
its model, and the externs over it. Decision 1 asks whether that counts as "no kernel change".

---

## 1. The target

**The guarantee.** It is exactly what main and #804 already give, with no new theorem about
files:

- **Every checked program.** Every program the checker accepts, `Fs` programs included, has a
  `CDerives` derivation of its `run_io` (`checkProgram_sound`, §11). So `externs_every_run`
  applies: under the one named hypothesis `ExternsMeet` (the host externs meet their contracts),
  every run from the empty memory, under every allocator, continues to a value at the empty
  memory. That covers runs that end with a handled raise. This is `resourceSafety`'s statement at
  `run_io`, and it is on main today.
- **What #804 adds.** For the source fragment of `experiments/ExnGlue`, the consume glue always
  exists: no program of the fragment is refused for lack of a finaliser (`tr_derives`), and every
  one is resource safe (`sourceResourceSafety`).

**"Every opened file is closed, except by deliberate leak" is prose, not a theorem.** A Lean
corollary would need a model that counts opens and closes, which is more than a few lines, so the
bar is stated in prose:

- a file (§2) holds a stream cell, and the cell is freed only by the file's `close` observation,
  whose extern closes the descriptor (its host contract);
- the final memory is empty, so every file cell was freed, so every file was closed, except
  through the deliberate leaks listed in §2.

**Which programs it covers.** Every program the checker accepts that uses `Fs` through
`lib/fs.bc`, including programs that raise `Fail[FsError]` with files open, inside and outside
borrow blocks and borrowing calls.

**The known limit: the checker is not `tr`.** #804's `tr` is a model translation; the checker's
glue (`finalOf`, `thenIt` in `Frontend/Check/Steps.lean`) is a separate implementation.
- **Soundness does not depend on the gap.** Whatever the checker accepts, the kernel has checked
  (`checkProgram_sound`), so every accepted `Fs` program has the guarantee above, with no
  reference to `ExnGlue`.
- **The gap is completeness only.** #804 does not prove that the checker finds the glue `tr`
  finds, so a program `tr` would translate may still be refused.
- **One difference matters for files.** The checker emits `[let]` instead of `[then]` when the
  rest is own-free. A host opaque value is own-free, so a bare host handle would be abandoned at
  an abort without a close. §2's representation never puts a bare handle in user scope.

This is a stated limit, not a work item.

## 2. `File`: a `ν` object

**One type per mode, each a `ν` object over its stream cell.**

    ReadFile  ≜ box top U(νX. (∀'x ⊏ top. Mut 'x string ⊸ F((i32 ⊕ FsError) ⊗ box top U X)) & F 1)
    WriteFile ≜ box top U(νX. (∀'x ⊏ top. Imm 'x string ⊸ F((1 ⊕ FsError) ⊗ box top U X)) & F 1)

- **The state** is the stream's cell, `ref input` for a read file and `ref output` for a write
  file: §11's kinds. In the host the cell holds the descriptor; in `bcc interp` the model's
  content. The object is built by `unfold` over that state, as `corpus/nu-file-read.bc` builds its
  `File<'c>` over a content cell.
- **The observations.**
  - `read` (`π₁`) is lent the buffer `mut` for the one call (`∀'x`, #808). Its body takes the
    buffer's spare capacity, calls `file_read` on the cell and that room, and answers the count
    or the error as a sum, with the rest of the object.
  - `write` (`π₁` of a write file) is lent the buffer `imm` for the call, calls `file_write`
    with the buffer's initialised prefix, and answers `()` or the error, with the rest.
  - `close` (`π₂`) calls the close extern on the cell and answers `()`.
- **The rest is boxed at `top`.** The rest of the object is `box top U X`, as `nu-file-read`'s is
  `box 'c U X`: the object outlives the lend it is observed under, so `read(f, &mut buf)` hands
  back a file that is not tied to `buf`'s lend. The state is an owned cell, which outlives `top`.
  Decision 3 asks whether `File` should instead take a lifetime parameter `'c`.
- **The observations answer, they do not raise.** An observation is `F A`, not `F_Σ A` (an
  `EffLeaf` would be allowed by `NuLeaf`, but a raise inside the observation would abandon the
  object's rest). The library functions of §3 raise after the observation has handed the rest
  back. So no lend inside the library is held across a raise, and the only lends a raise crosses
  are the caller's.

**How it behaves.**
- **An unused file is closed.** `box top U(νX. C & F 1)` is consumable (`Consumable.nu`,
  `consumableAtB`'s `ν` case, §12 group 2): its consume is "unbox, force, `nuOut`, `close`". The
  checker's end-of-path consumes close it on the normal exit (`corpus/nu-file-consumed.bc` is the
  same shape).
- **A raise closes it.** A file is not own-free, so a `let` whose head may raise is `[then]`, and
  `finalOf` consumes the file by its `close`. Several files are closed most recently bound first,
  §12's order (#811 made the abort path agree with the normal path).
- **No double close, no use after close.** The object is linear and `close` ends it.
- **Typestate.** The two modes are two types. More states can be more types later.
- **Any object of the type is a file to the library.** A fake built by `unfold` over a model state
  serves `read` and `write` as well as `open` (the source stage's `fs-fake`, §6).

**What a user would have to write to leak a file.** These are named and not designed out:
1. **Build an object whose `close` frees the cell without closing the descriptor**, or take the
   state out through a fake `unfold`. The bare `input` handle is own-free, so `[let]` abandons it
   at an abort.
2. **Call the raw externs directly.** They are visible to code that includes `lib/fs.bc`, as §11's
   operations are today.
3. **Never finish.** A run that diverges, or code that is never reached (`⊤`, `absurd`).

**The alternatives considered:**

| representation | leak by accident? | raise with the file open | why not |
|---|---|---|---|
| **`ν` object over a cell, observations lent the buffer** (recommended) | no: unused means closed | closed by the glue | — |
| two-way thunk `U(F (ref input) & F 1)` (the previous plan) | no | closed by the glue | chosen only because `NuLeaf` had no `∀`; #808 removed that. The I/O sits outside the object, so a fake replaces `open` but not the reads |
| `ref input` cell, not consumable, explicit `close` | no | **refused** (`finalOf`: linear and not consumable) | every program that raises with a file open is rejected |
| bare host opaque handle | **yes**: own-free, abandoned at aborts by `[let]` | abandoned, descriptor leaked | leaks in ordinary code |
| handler-owned table (files closed when the handler exits) | descriptors held until the program ends | closed at exit | not prompt: a long-running operator holds descriptors until it exits |

## 3. The operations

**The effect** (`lib/fs.bc`), answering as §34's effects are. Only `open` needs authority; a file
is its own capability.

    effect Fs {
      fn open_status<'b>(path: array_imm 'b u8) -> ReadFile + FsError;
      fn create_status<'b>(path: array_imm 'b u8) -> WriteFile + FsError
    }
    data FsError = NotFound | Denied | IsDir | BadFile | TooBig | Other(i32)

The platform handler is `wasi_fs(&mut c: fs)`, on the capability `fs : ref fs` (a new opaque kind,
made and taken by harness externs as `clock` is). `main` is the only place `Fs` is ambient (§34).

**The library.** Errors are raised with `Fail[FsError]`. The status functions answer the status
as an ordinary sum, for programs that want it as a value; the sum is a return value, not the
error mechanism.

| function | type | raises |
|---|---|---|
| `open(path)` | `array_imm 'b u8 -> ReadFile` with `Fs, Fail[FsError]` | the open's error |
| `create(path)` | `array_imm 'b u8 -> WriteFile` with `Fs, Fail[FsError]` | the open's error |
| `read(f, &mut buf)` | `<'a> ReadFile * mut 'a string -> ReadFile * i32` with `Fail[FsError]` | a read error. Appends into `buf`'s spare capacity; `0` at end of file |
| `write(f, &buf)` | `<'a> WriteFile * imm 'a string -> WriteFile` with `Fail[FsError]` | a write error. Writes every byte |
| `read_all(f, &mut buf)` | `<'a> ReadFile * mut 'a string -> 1` with `Fail[FsError]` | a read error. Grows `buf` to the file and closes the file |
| `close(f)` | `ReadFile -> 1` | none |
| `finish(f)` | `WriteFile -> 1` with `Fail[FsError]` | the close's error (decision 4) |
| `read_status(f, &mut buf)` | `<'a> ReadFile * mut 'a string -> ReadFile * (i32 + FsError)` | none: the status is the answer |
| `write_status(f, &buf)` | `<'a> WriteFile * imm 'a string -> WriteFile * (1 + FsError)` | none |

- **`read` is the observation, then the raise.** `read(f, m) = let (r, f) = observe(f).read(m);
  match r { inl k -> (f, k) | inr e -> raise(e) }`, the file in scope at the raise and closed by the
  glue. `read_status` is the observation alone.
- **`read(f, &mut buf)` is callable as written.** A `&mut buf` in the arguments of a call that may
  raise is lent by the unwinding form of its borrow (#812): `withbor2U` when `buf` is a cell, and a
  cell scoped to the call when `buf` is a `let mut` value. Before #812 it was refused, and programs
  wrote `borrow mut buf { m -> read(f, m) }`.
- **`read` and `write` need no `Fs`.** A function given a file can read it without file-system
  authority.
- **One system call per observation.** `read_all` grows one buffer.
- **A path from a literal.** `borrow imm "in.txt" { p -> open(p) }` works with the raise of `open`
  crossing the literal's lend (#813). The literal's view across an abort tabulates the path into a
  heap array rather than pointing at the read-only bytes (§7, R6).
- **Suspension.** Blocking `Fs` holds no borrow across a suspension. A suspending `Fs` (#750 unit
  B) belongs to the stretch track, where a lend of `buf` across a pending operation is the question
  to answer.

**The externs**, each with its contract in `ExternsMeet`, listed in `bcc trusted`:

| extern | type | model | host |
|---|---|---|---|
| `fs_open_read` | `!(all 'a 'b. mut 'a fs * array_imm 'b u8 => mut 'a fs * (ref input + i32))` | look the path up in the model file system, `alloc` an `Input` cell of its bytes, or an error code | libc `open(O_RDONLY\|O_CLOEXEC)`, a heap cell holding the descriptor; WASI `path_open` under a preopened directory |
| `fs_open_write` | the same, at `ref output` | `alloc (fd, nil)`, the descriptor from the model's counter | `open(O_WRONLY\|O_CREAT\|O_TRUNC, 0644)`; WASI `path_open` with create and truncate |
| `file_read` | `!(all 'a 'b. mut 'a input * array_mut 'b u8 => mut 'a input * (array_mut 'b u8 * i32))` | `read_into`'s model (never an error) | `read(2)` / `fd_read` once; a negative count is an error code |
| `file_write` | `!(all 'a 'b. mut 'a output * array_imm 'b u8 => mut 'a output * i32)` | `write_all`'s model | `write(2)` / `fd_write` until every byte is written, or an error code |
| `close_input` | `!(ref input => 1)` | `free` | `close(fd)`, then free the cell |
| `close_output` | `!(ref output => i32)` | `free` | `close(fd)`, then free the cell; the code is the close's result |
| `mk_fs`, `take_fs` | harness | `alloc` / `free` of the model file system | a cell with no content (WASI: the preopens) |

The error codes and the host code for open, read, write and the WASI preopen walk are taken from
branch `fs-769`, adapted from a descriptor passed as `i32` to a descriptor held in the cell, as the
spike (`fs-spike`) did. The models live in `Core/Files.lean`, each meeting its contract by the
Fundamental Property at the transparent type, as `readInto_meets` does. Writes stay in the cell's
model content and are not stored back into the model file system (R4).

## 4. Raises with a file open

**How the glue consumes a file.** At a raise, every file in the abandoned context is closed by its
`close` observation, most recently bound first (§12's order, on the abort path since #811). The
buffer never enters the payload, which is the `FsError` alone: data, as `effRaise.hd` asks.

**What happens to the buffer**, by where the handler is relative to the lend:
- **The handler is inside the lend**, for example
  `borrow mut buf { m -> with to_result { read(f, m) } }`. The lend ends normally after the
  handler, and the owner has `buf` back, contents included.
- **The raise leaves the lend.** The lend is the unwinding form: `withbor2U` for a cell,
  `sliceBorrowMU`/`IU` for a buffer's array (#814), and the call-scoped cell for a `let mut`
  value lent in a call (#812). Its finaliser consumes the source, so `buf` is freed with the rest
  of the abandoned scope. Nothing leaks, and the owner does not get it back, because the owner's
  continuation was abandoned too.

**The gaps the previous plan named, now closed on main's elaborator** (this branch, #810–#814):
"a borrow of a buffer or a literal crossed by an abort" (SPEC §18 *Not provided*, #813, #814),
`&mut x` in a call that may raise (#812), a raise as a branch's value in a borrow block (#810),
and the consume order at an abort (#811). Each is an elaboration into existing kernel forms.

**One gap stays** (SPEC §18 *Not provided*): a place declared outside a control `with` and lent
inside it, so `let mut buf = …; with to_result { read(f, &mut buf) }` is refused. Decision 8.

## 5. The hardest case, kept in

**The case:** a raise inside a borrow while two files are open, one bound outside the lend and one
inside it.

    main -> i32 + FsError = with to_result {
      let out = create("out.txt");                   // outside the lend
      let mut buf = alloc(string_new(64));
      let n = borrow mut buf { 'x, m ->              // a raise leaves this lend
        let inp = open("in.txt");                    // inside; may raise NotFound
        let (inp, n) = read(inp, m);                 // may raise
        n                                            // inp closed at the scope's end
      };
      let out = write(out, &buf);                    // a borrowing call that may raise (#812)
      let s = free(buf); n
    }

What runs, in order, when `read` raises:
1. **Inside `read`.** The observation has handed the rest of `inp` back before the raise, so the
   consumes before the raise close `inp` (`close_input`). No lend inside the library crosses the
   raise.
2. **The lend of `buf`.** The raise leaves the callback, so the lend is `withbor2U` at the row
   `Fail[FsError]`. Its finaliser `d = consumeE (ref string)` frees `buf`.
3. **The `Fs` capability.** The control `with` lent it to its body (`withbor3`), and the callback
   captured that borrow. The borrow is released.
4. **Outside the callback.** The call site's `[then]` consumes the rest of its context: `out`,
   closed by its `close` (`close_output`).
5. **The handler.** `to_result` answers `inr e`. The memory is empty, and both descriptors were
   closed.

When `open` raises instead, step 1 has no inner file yet, and steps 2–5 are the same. When `write`
raises, its own lend of `buf` (`withbor1U`) ends, `buf` is freed by that lend's finaliser, and
`out` is closed inside `write` before the raise.

**The kernel rules' premises.**
- **`withbor2U`'s `S.Unwind 'x`.** The callback's row holds only `Fail[FsError]`'s `raise`:
  abortive, a nonzero name, and a payload of data, which does not mention `'x`. `Fs` contributes no
  row operation: §18 elaborates an answering operation to a call on the capability.
- **`withbor2U`'s `hd`.** `consumeE (ref string)` is closed and typed.
- **`allI`'s `hΓx`.** The callback captures the borrow `Mut 'l fs`, whose type does not mention
  `'x`.
- **The observation's `∀'x ⊏ top`** is `NuLeaf`'s `∀` case (#808), and `NuOk`'s side condition
  holds: `'x` is not free in the body.

**The handled variant**, `borrow mut buf { m -> with to_result { … read(inp, m) … } }`, gives
`buf` back to its owner with its contents. It is the second corpus case.

**Corpus programs.** `fs-hard` (both variants, all three raise points) and `fs-raise-two` (two
files open when a third open raises; the closes' order is pinned by a native trace). Both run
natively and on Wasm at a golden, with `live 0` at the source stage.

## 6. The PR sequence to main

Every PR is merge-intended and lands with its lowering (native and WASI) and running corpus
programs.

| PR | content | corpus | depends on |
|---|---|---|---|
| **0** | `spike-804`: `experiments/ExnGlue`, `scope-804.md` | — (Lean) | — |
| **1** | surface fixes #810–#814 (this branch) | `raise-in-borrow-branch`, `buf-lend-raise`, `lit-lend-raise`, `lend-call-raise`, `lend-call-record`, `sugar/finaliser-order`; `aoc/2022-12`, `2023-03`, `2022-21` on `/` and `%` | — |
| **2** | `fs` opaque kind and model (`Core/Opaque.lean`, `Core/Files.lean`); `fs_open_read`, `file_read`, `close_input`, `mk_fs`/`take_fs` with models and `_meets`; `ExternsMeet` and `bcc trusted` entries; host code native and WASI (from fs-769); `lib/fs.bc` with `ReadFile` as the `ν` object, `open`, `read`, `read_status`, `read_all`, `close`; the `Fs` effect and `wasi_fs`; `bcc run --dir` | `fs-cat`, `fs-missing` | 1 |
| **3** | `WriteFile`: `fs_open_write`, `file_write`, `close_output`; `create`, `write`, `write_status`, `finish` | `fs-copy` (two files open at once) | 2 |
| **4** | raises with files open: the hard case | `fs-hard`, `fs-raise-two`, `fs-fake` (a fake `Fs` handler and fake file objects, at the source stage) | 3 |
| **5** | `json-field` (operator milestone 1, #67); fs-769's `scripts/check-fs.sh` (real-file runs) in the gate | `json-field` | 4 |

- **PR 0 is independent.** `Fs` does not use `ExnGlue`, because the guarantee of accepted programs
  comes from `checkProgram_sound`. Order is decision 7.
- **No widening of `ExnGlue` is needed.** Widening would only extend #804's completeness result to
  `Fs` programs (decision 7).

**#769's done-when:**
- `Fs` is a platform effect, ambient only in `main`. Its externs meet their contracts, and
  `bcc trusted` names them.
- A file is a `ν` object whose `read` and `write` observations are lent the buffer for the call,
  and whose `close` the checker runs when the file goes unused, raises included. No program in the
  corpus closes a file the glue would not have closed.
- Natively and on Wasm (WASI): `fs-cat` prints a file named on the command line; `fs-copy` copies
  one file to another; `json-field` reads a field from a JSON file; `fs-hard` and `fs-raise-two`
  end at `inr …` with every descriptor closed.
- `fs-fake` runs at the source stage with fake `open` and fake file objects.

## 7. Risks, NOT-do list, tempting shortcuts

**Risks, ranked** (each checked by its PR's corpus program):

| # | risk | check in |
|---|---|---|
| R1 | The `read` observation splits the spare capacity of a `string` reached through `Mut 'x string` (a record behind a `Mut`, §5 *Family borrows*) inside an `unfold` step, and calls an extern there. `nu-file-read` lends an `i32`, not a buffer | PR 2, `fs-cat` |
| R2 | **The hard case:** the borrow callback captures the control `with`'s borrow of the `Fs` capability, and the unwinding lend releases it; T1's refusal must not fire, since `Fs` is answering. Precedents: `corpus/effects-borrow-raise.bc`, `effects-map-fail.bc`; neither combines the two | PR 4 |
| R3 | The implicit `close` at a `WriteFile` ignores `close(2)`'s error, a possible silent data loss on a write (decision 4) | PR 3 |
| R4 | The model does not store writes back, so `bcc interp` and native differ for a program that writes and then reads back. Such programs run natively only (`check-fs.sh`) | PR 3 |
| R5 | WASI opens only under preopens. fs-769's walk and `bcc run --dir` are reused | PR 2 |
| R6 | A literal path lent across a raise is tabulated into a heap array (the unwinding form of a literal's view is not a `litView` node, §57). Correct, and one allocation per such `open` | PR 2 counts |

**NOT-do, and the shortcuts that mean STOP:**
- **Closing files outside the term.** No backend or runtime code closes a file, no "close
  descriptors at exit" in `run_io`'s host, and no table of open files in the backend. Every close
  is a consume in the checked term.
- **Special cases in the elaborator or checker:** no rule that recognises `File`, `close` or `Fs`,
  and no checker heuristic about where files are live. Everything goes through `Consumable.nu` and
  the existing glue.
- **Revived dtor-wire machinery:** no `must_close`, `Tok` or `[let-dtor]`.
- **Work on deliberate leaks** (§2's list): no abstract types and no hiding of the raw externs.
- **No special error construct**: no `Result` mechanism and no `?`. The status functions' sums are
  ordinary return values.
- **No new kernel rule or judgment**, and no change to `CDerives`. If an observation needs a shape
  `NuLeaf` does not admit, that is kernel work and stops the PR.
- **A persistent descriptor** (`i32`) in any user-visible type.
- **A raise inside an observation**, or a lend inside the library held across a raise.

## 8. Decisions for the user

1. **The `fs` opaque kind.** Add one opaque kind with its model, as `clock` and `args` were.
   Recommended: yes. It is §11's extension point, with no rule; there is no other carrier for the
   file-system capability.
2. **Files' kinds.** Reuse `input`/`output` for open files, two types `ReadFile` and `WriteFile`.
   Recommended: yes; their models and the stream externs exist, and the typestate falls out.
3. **The object's bound.** The rest boxed at `top` (one type per mode, no lifetime parameter), or
   `File<'c>` with the bound a parameter, as `nu-file-read` has it. Recommended: `top`. The state
   is an owned cell, so nothing is gained by a parameter, and every signature stays shorter.
4. **Close errors.** The implicit `close` ignores them (pure `F 1`, as consumability requires);
   `finish(f)` raises `Fail[FsError]` on a failed close of a write file. Recommended: yes.
5. **Read and write errors.** `read`/`write` raise after the observation hands the file back; the
   file is then closed by the unwind. Programs that keep the file after an error use
   `read_status`/`write_status`. Recommended: yes, from the standing decision that errors are
   `raise` and handlers, with sums as ordinary values.
6. **A `Fail[FsError]` unhandled at `main`.** Served by a platform handler `main_fs_error`, which
   writes the error on standard error and exits with status 1. Recommended: yes, as `main_div_error`
   serves `DivError` (SPEC §39).
7. **`ExnGlue` (PR 0).** Land it independently, and do not widen it to codata and externs now.
   Recommended: as stated; `Fs`'s guarantee does not use it.
8. **A place lent inside a control `with`** (§4's remaining gap). Programs write the lend around
   the handler, `borrow mut buf { m -> with to_result { … } }`, or declare the buffer inside the
   `with`. Recommended for this plan: yes. Building the elaboration that lends an outer `let mut`
   across a control `with` is separate work after PR 5.
9. **The interpreter's file system.** `bcc interp` reads the files a run names from the host into
   the model's `fs` at the start (the spike did this). Recommended: yes; the alternative, an empty
   model file system, leaves the source stage with fakes only.

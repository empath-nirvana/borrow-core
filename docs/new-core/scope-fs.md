# Scope — `Fs`: files as the platform's effect, on #804's guarantee

Plan for #769, rewritten after the 2026-11-01 reset. #797 stays paused, and nothing here depends
on it. Status: for review. No code is written.

**Kernel target: no kernel change.** No `CDerives` rule, judgment, type former or relation clause
is added. What is added sits at §11's extension point, "a new host resource is a new `k` with its
model, not a new former", which is how `clock` and `args` were added (§34): one opaque kind `fs`,
its model, and the externs over it. D1 asks whether that counts as "no kernel change".

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
- **What #804 adds.** For the source fragment of `experiments/ExnGlue`, the consume glue *always
  exists*: no program of the fragment is refused for lack of a finaliser (`tr_derives`), and every
  one is resource safe (`sourceResourceSafety`).

**"Every opened file is closed" is prose, not a theorem.** A Lean corollary would need a model
that counts opens and closes, which is more than a few lines, so the bar is stated in prose:

- a file (§2) holds a cell, and the cell is freed only by the file's `close`, whose extern closes
  the descriptor (its host contract);
- the final memory is empty, so every file cell was freed, so every file was closed, except
  through the deliberate leaks listed in §2.

**Which programs it covers.** Every program the checker accepts that uses `Fs` through
`lib/fs.bc`. That includes programs that raise `Fail[FsError]` with files open, inside and outside
borrow blocks. A raise that reaches `main` unhandled is decision D5.

**The known limit: the checker is not `tr`.** #804's `tr` is a model translation. The checker's
glue (`finalOf`, `thenIt` in `Frontend/Check/Steps.lean`) is a separate implementation.
- **Soundness does not depend on the gap.** Whatever the checker accepts, the kernel has checked
  (`checkProgram_sound`), so every accepted `Fs` program has the guarantee by the argument above,
  with no reference to `ExnGlue`.
- **The gap is completeness only.** #804 does not prove that the checker finds the glue `tr`
  finds, so a program `tr` would translate may still be refused.
- **One difference matters for files.** The checker emits `[let]` instead of `[then]` when the
  rest is own-free (`Steps.lean:1124`). A host opaque value is own-free, so a bare host handle
  would be abandoned at an abort without a close. §2's representation never puts a bare handle in
  user scope, so `Fs` does not need this changed.

This is a stated limit, not a work item.

## 2. `File`'s representation

**Recommended: a stream cell behind a two-way thunk, one type per mode.**

    ReadFile  ≜ U(F (ref input)  & F 1)        -- take the cell, or close
    WriteFile ≜ U(F (ref output) & F 1)

- **The state.** The object holds the stream's cell, `ref input` for a read file and
  `ref output` for a write file. These are §11's kinds: in the host the cell holds the descriptor,
  and in `bcc interp` the model's content.
- **The two components.**
  - `take` (`π₁`) ends the object and answers its cell. The library calls the extern on the cell
    and rebuilds the object (`mk_read c = thunk ⟨return c, close_input c⟩`; both components use
    `c`, additively).
  - `close` (`π₂`) calls the close extern.
- **Why not a codata object whose observations do the I/O** (the earlier draft): an observation
  cannot take a lifetime-polymorphic argument. `CTy.NuLeaf` admits `A ⊸ D` with `A` closed, and no
  `∀`. So a `ν` file could take only an owned buffer, never `&mut buf`. The two-way thunk keeps the
  I/O in the library function, which has the lifetime parameters.
- **Typestate.** The two modes are two types, as the #769 design note proposes. More states can
  be more types later.
- **The checker already supports this shape.** `U(C & F 1)` is `Consumable.close`
  (`consumableAtB`, `Steps.lean:64`): its consume is "force, then the second projection".

How it behaves:

- **An unused file is closed.** Its consume is `close` (§12 group 2), so the checker's
  end-of-path consumes close it on the normal exit. This is the decided implicit `close`.
- **A raise closes it.** A file is a thunk, not `OwnFree`, so a `let` whose head may raise is
  `[then]`, and `finalOf` consumes the file by its `close`. A raise with the file in the abandoned
  context runs the consumes before the raise. A borrow callback that raises does the same in its
  own context (§5).
- **No double close.** The thunk is linear, and both components end it.
- **No use after close.** After `close` there is no object left.

**What a user would have to write to leak a file.** These are named and not designed out:
1. **Take the cell and drop the descriptor.** `take` it, then `free` the cell, or build a forged
   object whose `close` frees the cell without closing. The bare `input` is own-free, so `[let]`
   abandons it at an abort.
2. **Call the raw externs directly.** They are visible to code that includes `lib/fs.bc`, as §11's
   operations are today.
3. **Never finish.** A run that diverges, or code that is never reached (`⊤`, `absurd`).

**The alternatives considered:**

| representation | leak by accident? | raise with the file open | why not |
|---|---|---|---|
| **two-way thunk over a cell** (recommended) | no: unused means closed | closed by the glue | — |
| codata object whose observations do the I/O | no | closed by the glue | an observation cannot take `&mut buf`: no `∀` in `NuLeaf` |
| `ref input` cell, not consumable, explicit `close` | no | **refused** by the checker (`finalOf`: linear and not consumable). A borrow's finaliser `d` must be a closed pure term, so it cannot call an extern | every program that raises with a file open is rejected |
| bare host opaque handle | **yes**: own-free, abandoned at aborts by `[let]` | abandoned, descriptor leaked | leaks in ordinary code |
| declared type with `Tok` and a destructor (`[let-dtor]`, PR #799) | no | closed | void since the 2026-11-01 reset; needed a control `Fs`, finaliser machines and the `directFacts` fix |
| handler-owned table (files closed when the handler exits) | descriptors are held until the program ends | closed at exit | not prompt: a long-running operator holds descriptors until it exits |

## 3. The operations

**The effect** (`lib/sys.bc`), answering as §34's effects are. Only `open` needs authority; a
file is its own capability.

    effect Fs {
      fn open_read<'b>(path: array_imm 'b u8) -> ReadFile + FsError;
      fn open_write<'b>(path: array_imm 'b u8) -> WriteFile + FsError
    }
    data FsError = NotFound | Denied | IsDir | BadFile | TooBig | Other(i32)

The platform handler is `wasi_fs(&mut c: fs)` (`lib/wasi.bc`), on the capability `fs : ref fs`
(a new opaque kind, made and taken by harness externs as `clock` is). `main` is the only place
`Fs` is ambient (§34).

**The library** (`lib/fs.bc`). Errors are raised with `Fail[FsError]`. The status operations
underneath return the status as an ordinary sum, for programs that want it as a value. Ordinary
sums from ordinary functions are fine (user, 2026-11-04): what the language does not have is a
special error construct.

| function | type | raises |
|---|---|---|
| `open(path)` | `array_imm 'b u8 -> ReadFile` with `Fs, Fail[FsError]` | the open's error |
| `create(path)` | `array_imm 'b u8 -> WriteFile` with `Fs, Fail[FsError]` | the open's error |
| `read(f, &mut buf)` | `<'a> ReadFile * mut 'a string -> ReadFile * i32` with `Fail[FsError]` | a read error. Appends into `buf`'s spare capacity; `0` at end of file |
| `write(f, &buf)` | `<'a> WriteFile * imm 'a string -> WriteFile` with `Fail[FsError]` | a write error. Writes every byte |
| `read_all(f, &mut buf)` | `<'a> ReadFile * mut 'a string -> 1` with `Fail[FsError]` | a read error. Grows `buf` to the file and closes the file |
| `close(f)` | `ReadFile -> 1` (and the same at `WriteFile`) | none (D3) |
| `read_status(f, &mut buf)` | `<'a> ReadFile * mut 'a string -> ReadFile * (i32 + FsError)` | none: the status is the answer |
| `write_status(f, &buf)` | `<'a> WriteFile * imm 'a string -> WriteFile * (1 + FsError)` | none |
| `open_status`, `create_status` | the `Fs` operations themselves | none |

- **The buffer is borrowed, and the file is passed and handed back.** `read` takes the cell
  (`take`), lends it and the buffer's spare capacity to the extern for one call, rebuilds the file,
  and only then raises on an error code. So inside the library no lend is held across a raise, and
  no `withborU` is needed there.
- **`read` and `write` need no `Fs`.** A function given a file can read it without file-system
  authority.
- **One system call per operation.** `read_all` grows one buffer.
- **The async-era question.** Owned-buffer hand-back (decision 71, voided by the 2026-11-01
  reset) existed so that no borrow would be held across an async suspension. Blocking `Fs` holds
  none. A suspending `Fs` (#750 unit B) belongs to the stretch track, where this API's borrow of
  `buf` across a pending operation is the question to answer.

**The externs** (`lib/wasi.bc`). Their contracts are extended into `ExternsMeet`, they are listed
in `bcc trusted`, and they are assumed (1) at the host:

| extern | type | model | host |
|---|---|---|---|
| `fs_open_read` | `!(all 'a 'b. mut 'a fs * array_imm 'b u8 => mut 'a fs * (ref input + i32))` | look the path up in the model file system, `alloc` an `Input` cell of its bytes, or an error code | libc `open(O_RDONLY\|O_CLOEXEC)`, a heap cell holding the descriptor; WASI `path_open` under a preopened directory (fs-769's walk) |
| `fs_open_write` | the same, at `ref output` | `alloc (fd, nil)`, the descriptor from the model's counter | `open(O_WRONLY\|O_CREAT\|O_TRUNC, 0644)`; WASI `path_open` with create and truncate |
| `file_read` | `!(all 'a 'b. mut 'a input * array_mut 'b u8 => mut 'a input * (array_mut 'b u8 * i32))` | `read_into`'s model (never an error) | `read(2)` / `fd_read` once; a negative count is an error code |
| `file_write` | `!(all 'a 'b. mut 'a output * array_imm 'b u8 => mut 'a output * i32)` | `write_all`'s model | `write(2)` / `fd_write` until every byte is written, or an error code |
| `close_input` | `!(ref input => 1)` | `free` | `close(fd)`, then free the cell |
| `close_output` | `!(ref output => i32)` | `free` | `close(fd)`, then free the cell; the code is the close's result |
| `mk_fs`, `take_fs` | harness | `alloc` / `free` of the model file system | a cell with no content (WASI: the preopens) |

The error codes are fs-769's (`-1` not found … `-(16 + c)`). The host code for open, read,
write and the WASI preopen walk is taken from branch `fs-769` (`Backend/Native/Runtime.lean`,
`Backend/Wasm/Runtime.lean`, Backend2's `Ext` plumbing in `44d1ecb3`), adapted from a descriptor
passed as `i32` to a descriptor held in the cell.

**The model** (`Core/Files.lean`, as `Core/Stdio.lean`). `fs.Holds v`: `v` is a list of
(path, bytes) pairs and a descriptor counter. Each model meets its contract
(`fsOpenRead_meets`, …), by the Fundamental Property at the transparent type, as `readInto_meets`
is. Writes stay in the cell's model content and are not stored back into the model file system
when the file is closed (risk R5).

## 4. Raises with a file open

**How the glue consumes the file.** The library raises after the file is rebuilt:

    read(f, b) = let c = f.take;
                 let (c, (b, n)) = file_read_on(c, b);  // pure lends of c and of b's spare room
                 let f = mk_read(c);
                 if n < 0 { raise(err(n)) } else (f, n)

At the `raise`, `f` is live, so the checker consumes it by its `close`. The borrow `b` is own-free,
and is released or abandoned. The error then propagates.
- **The rule is the same for every file in scope:** a file in the context of an abort is closed
  there, most recently bound first (§12's order).
- **Keeping the file after an error.** `read_status` answers the status as a sum and hands the file
  back. A program that wants to retry, or to report and go on, uses it.

**What happens to the buffer.** The buffer never enters the payload, which is the `FsError`
alone: data, as `effRaise.hd` asks. `buf` stays with its owner, and what happens to it depends on
where the error is handled relative to the lend:
- **The handler is inside the owner's lend**, for example
  `borrow mut buf { m -> with to_result { read(f, m) } }`. The lend ends normally after the
  handler, and the owner has `buf` back, contents included.
- **The raise leaves the lend** (the handler is outside it). The lend is the unwinding form
  (`withbor2U`; `sliceBorrowMU` for a view). Its finaliser consumes the source, so `buf` is freed
  with the rest of the abandoned scope. Nothing leaks, but the owner does not get it back, because
  the owner's own continuation was abandoned too.

**Two gaps in today's elaborator** (§18 *Not provided*, SPEC:2745). Both are elaboration over the
existing unwinding forms, with no kernel change:
- **"a borrow of a buffer … crossed by an abort"** is not provided. The `string` lend in
  `read(f, &mut buf)` under a raise that leaves it is exactly that. The same refusal keeps
  `aoc/2022-12` and three other corpus programs in their forms (SPEC:7496).
- **"a place lent in [a control `with`]"** is not provided either. So
  `let mut buf; with to_result { read(f, &mut buf) }` is refused, and the explicit
  `borrow mut buf { m -> with … }` above is the form that works.

The cause of the first gap was not investigated. PR 3 builds it. The second is D9.

## 5. The hardest case, kept in

**The case:** a raise inside a borrow callback while two files are open, one bound outside the
callback and one inside it. The callback's lend is the buffer's.

    main -> i32 + FsError = with to_result {
      let out = create("out.txt");                   // outside the callback
      let mut buf = string_new(64);
      let n = borrow mut buf { 'x, m ->              // the callback: a raise leaves it
        let inp = open("in.txt");                    // inside; may raise NotFound
        let (inp, n) = read(inp, m);                 // may raise
        n                                            // inp closed at the scope's end
      };
      let out = write(out, &buf); n
    }

What runs, in order, when `read` raises:
1. **Inside `read`.** The file is rebuilt before the raise, so the consumes before the raise close
   `inp` (`close_input`), and `m` is released. No lend inside the library crosses the raise.
2. **The callback's lend of `buf`.** The raise leaves the callback, so the lend is the unwinding
   form `withbor2U`, at the row `Fail[FsError]`. Its finaliser `d = consumeE (ref string)` frees
   `buf`.
3. **The `Fs` capability.** The control `with` lent it to its body (§18, `withbor3`), and the
   callback captured that borrow. The borrow is released.
4. **Outside the callback.** The call site's `[then]` consumes the rest of its context. That is
   `out`, closed by its `close` (`close_output`).
5. **The handler.** `to_result` answers `inr e`. The memory is empty, and both descriptors were
   closed.

When `open` raises instead, step 1 has no inner file yet, and steps 2–5 are the same.

**The kernel rules' premises at the callback.**
- **`withbor2U`'s `S.Unwind 'x`.** The callback's row holds only `Fail[FsError]`'s `raise`:
  abortive, a nonzero name, and a payload of data, which does not mention `'x` and outlives every
  lifetime. `Fs` contributes no row operation, because §18 elaborates an answering operation to a
  call on the capability.
- **`withbor2U`'s `hd`.** `consumeE (ref string)` is closed and typed (`string = buf u8`, an owned
  array and an `i32`, so `Consumable`).
- **`allI`'s `hΓx`.** The callback captures the borrow `Mut 'l fs`, whose type does not mention
  `'x`.
- **No `withborU` inside the library.** `read`'s own lends of `c` and of `b`'s spare room end
  before it raises, so they are the pure forms.

**The handled variant**, `borrow mut buf { m -> with to_result { … read(inp, m) … } }`, gives
`buf` back to its owner with its contents. It is the second corpus case.

**Corpus programs.**
- `fs-hard`: both variants, and both raise points.
- `fs-raise-two`: two files open when a third open raises.

Both pin the case natively and on Wasm, each at a golden and checked with `live 0` at the source
stage.

## 6. The PR sequence to main

Every PR is merge-intended and lands with its lowering (native and WASI) and running corpus
programs.

| PR | content | corpus | depends on |
|---|---|---|---|
| **0** | `spike-804`: `experiments/ExnGlue`, `scope-804.md`, one `judgments.allow` line | — (Lean) | — |
| **1** | `fs` opaque kind and model (`Core/Opaque.lean`, `Core/Files.lean`); `fs_open_read`, `file_read`, `close_input`, `mk_fs`/`take_fs` with models and `_meets`; `ExternsMeet` and `bcc trusted` entries; `IORun` models; host code native and WASI (from fs-769); `lib/fs.bc` with `ReadFile`, `open`, `read`, `read_all`; the `Fs` effect and `wasi_fs`; `bcc run --dir` | `fs-cat` (a file named in `Args`, printed); `fs-missing` (prints `not found` via `to_result`) | — |
| **2** | `WriteFile`: `fs_open_write`, `file_write`, `close_output`; `create`, `write` | `fs-copy` (two files open at once) | 1 |
| **3** | the elaborator's unwinding lends of buffers crossed by an abort (§4's first gap; `withbor2U` / `sliceBorrowMU`/`IU` at `buf T` places and views); `aoc/2022-12` and the three others in SPEC:7496 move to their direct forms | those four programs, plus `fs-buf-raise` | — |
| **4** | raises with files open: the hard case | `fs-hard`, `fs-raise-two`, `fs-fake` (a fake `Fs` handler whose `open` answers chosen errors, at the source stage; reads there go through the model file system, D8) | 2, 3 |
| **5** | `json-field` (operator milestone 1, #67); fs-769's `scripts/check-fs.sh` (real-file runs) in the gate | `json-field` | 4 |

- **PR 0 is independent.** `Fs` does not use `ExnGlue`, because the guarantee of accepted
  programs comes from `checkProgram_sound`. Landing it first records the argument of §1 on main.
  Order is decision D6.
- **No widening of `ExnGlue` is needed** (`case`, `Mut` lends, codata, externs). Widening would
  only extend #804's completeness result to `Fs` programs, which D7 asks about. If chosen, it is a
  PR after 5.
- **The closed `dtor-wire` branch (PR #799).** Its `directFacts` fix (`82fc9576`,
  `Backend2/Driver.lean`) was needed because `Fs` was a control effect there: `files`' clauses
  performed `FsHost`, a machine operation, inside clause work. Here `Fs` is answering, and the
  file functions call externs, so no clause work performs a machine operation. **It is not
  needed.** It stays available on the branch if a control-effect fake `Fs` appears. That
  branch's extern plumbing (`44d1ecb3`) is reused in PR 1, without its `Tok`-owning `file` kind.

**#769's done-when, rewritten:**
- `Fs` is a platform effect, ambient only in `main`. Its externs meet their contracts, and
  `bcc trusted` names them.
- A file is a codata object whose `close` the checker runs when the file goes unused, raises
  included. No program in the corpus closes a file the glue would not have closed.
- Natively and on Wasm (WASI):
  - `fs-cat` prints a file named on the command line;
  - `fs-copy` copies one file to another;
  - `json-field` reads a field from a JSON file;
  - `fs-hard` and `fs-raise-two` end at `inr …` with every descriptor closed.
- `fs-fake` runs at the source stage with a fake `Fs` handler of `open`.

## 7. Risks, NOT-do list, tempting shortcuts

**Risks, ranked** (none checked in Lean yet; each is checked by its PR's corpus program):

| # | risk | check in |
|---|---|---|
| R1 | §4's first gap: an unwinding lend of a `buf T` crossed by an abort is not provided today (SPEC:2745). The kernel forms exist; the elaborator does not pick them for buffers. Cause not investigated | PR 3 |
| R2 | `read` lends the spare capacity of a `string` reached through `mut 'a string`, a field of a record behind a `Mut` (§5 *Family borrows*). Not yet exercised with an extern | PR 1, `fs-cat` |
| R3 | **The hard case:** the borrow callback captures the control `with`'s borrow of the `Fs` capability (§18 `withbor3`), and the unwinding lend releases it; T1's refusal must not fire, since `Fs` is answering. Precedent: `corpus/effects-borrow-raise.bc` (a raise inside `borrow mut c { … }`, handler outside) and `effects-map-fail.bc` (a capability reborrowed for `to_result`'s body). Neither combines the two | PR 4 |
| R4 | The implicit `close` at a `WriteFile` ignores `close(2)`'s error, a possible silent data loss on a write (D3) | PR 2 |
| R5 | The model does not store writes back, so `bcc interp` and native differ for a program that writes and then reads back. Such programs are run natively only (`check-fs.sh`) | PR 2 |
| R6 | WASI opens only under preopens. fs-769's walk and `bcc run --dir` are reused | PR 1 |
| R7 | The order of consumes at an abort (most recent first) is observable through descriptors, not memory, and is tested, not proved | PR 4 |

**NOT-do, and the shortcuts that mean STOP:**
- **Closing files outside the term.** No backend or runtime code closes a file, no "close
  descriptors at exit" in `run_io`'s host, and no destructor table in the backend. Every close is
  a consume in the checked term.
- **Special cases in the elaborator or checker:** no rule that recognises `File`, `close` or
  `Fs`, and no checker heuristic about where files are live. Everything goes through
  `Consumable.close` and the existing glue.
- **Revived dtor-wire machinery:** no `must_close`, `Tok`, `[let-dtor]` or destructor syntax.
- **Work on deliberate leaks** (§2's list): no abstract types and no hiding of the raw externs.
- **No special error construct**: no `Result` mechanism and no `?`. Ordinary sums (the status
  operations) are not policed.
- **No new kernel rule or judgment**, and no change to `CDerives`.
- **A persistent descriptor** (`i32`) in any user-visible type.
- **A lend inside the library held across a raise.** `read`/`write` end their own lends before
  raising; only the caller's lends meet the unwinding forms.

## 8. Decisions for the user

- **D1. The `fs` opaque kind.**
  - (a) Add one opaque kind with its model, as `clock` and `args` were (recommended). This is
    §11's extension point, with no rule.
  - (b) Treat that as a kernel change and find another carrier. There is none for the
    file-system capability: `input` and `output` model streams.
- **D2. Files' kinds.**
  - (a) Reuse `input`/`output` for open files (recommended): their models and the stream
    externs' structure already exist, and the two-type typestate falls out.
  - (b) A new `file` kind with one read-write type: one more kind and model, and a single `File`
    type.
- **D3. Close errors.**
  - (a) The implicit `close` ignores them (pure `F 1`, as `Consumable.close` requires), and an
    explicit `finish(f)` (`take`, then `close_output`'s code) raises `Fail[FsError]` on a failed
    close (recommended).
  - (b) Ignore close errors everywhere.
- **D4. A read or write error.**
  - (a) `read`/`write` raise, and the file, rebuilt before the raise, is closed by the unwind. A
    program that wants to keep the file uses `read_status`/`write_status` (recommended).
  - (b) Only the status operations, and programs raise themselves.
- **D5. A `Fail[FsError]` unhandled at `main`.**
  - (a) A platform handler, `main_fs_error`, prints the error and exits nonzero, as
    `main_div_error` does for `DivError` (recommended).
  - (b) §18's error: `main` must handle it.
- **D6. The order of PR 0.** Before PR 1 (records §1's argument on main), or independently.
- **D7. Widen `ExnGlue`** to codata and externs, so that #804's completeness ("the glue always
  exists") covers `Fs` programs. It is not needed for `Fs` to work or for its guarantee.
  Recommended: not now.
- **D8. The interpreter's file system.**
  - (a) `bcc interp` reads the files a run names from the host into the model's `fs` at the start
    (recommended).
  - (b) An empty model file system; source-stage runs use `fs-fake`.
- **D9. A place lent inside a control `with`** (§4's second gap). Either:
  - (a) Programs write the owner's lend around the handler,
    `borrow mut buf { m -> with to_result { … } }`, as today (recommended for the first slice).
  - (b) Build the elaboration that lends a `let mut` place across a control `with`, a separate PR
    after 5.
- **D10. Which representation.**
  - (a) The two-way thunk (recommended). It takes `&mut buf` and `&buf`. Reads always reach the
    extern, so a fake can replace `open` but not the reads (the source stage uses the model file
    system).
  - (b) A `ν` object whose observations do the I/O. Any object of the type is a file, so reads are
    fakeable too. But it takes owned buffers only, the earlier draft's hand-back.

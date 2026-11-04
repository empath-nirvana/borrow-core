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

- a file is a codata object (§2) whose state is a cell, and the cell is freed only by the file's
  `close` observation, whose extern closes the descriptor (its host contract);
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

**Recommended: a codata object over a stream cell, one type per mode.**

    ReadFile  ≜ U(νX. (read  : Buf ⊸ F((Buf ⊗ (I32 ⊕ FsError)) ⊗ U X)) & F 1)
    WriteFile ≜ U(νX. (write : Buf ⊸ F((Buf ⊗ (1 ⊕ FsError)) ⊗ U X)) & F 1)

- **The state.** The object's hidden state is the stream's cell: `ref input` for a read file and
  `ref output` for a write file. These are §11's kinds, so the cell holds the descriptor in the
  host and the model's content in `bcc interp`.
- **The observations.** `read` and `write` hand back the buffer, the answer and the rest of the
  object. `close` (`F 1`) calls the close extern on the cell.
- **Typestate.** The two modes are two types, as the #769 design note proposes. Types for more
  states (for example a seekable file) can be added later.
- **Construction.** Each object is `unfold` of a library step over the cell (the pattern of
  `corpus/axes/codata-effects.bc`). The step is a `!` thunk over the persistent externs.
- **The checker already supports this shape.** `U(νX. C & F R)` with `C` an observation tree is
  `Consumable.nu` (decided by `consumableAtB`, `Steps.lean:65`). Observations that take an argument
  are §22's.

How it behaves:

- **An unused file is closed.** Its consume is `close` (§12 group 2), so the checker's
  end-of-path consumes close it on the normal exit. This is the decided implicit codata `close`.
- **A raise closes it.** A `ReadFile` is a thunk, not `OwnFree`, so a `let` whose head may raise
  is `[then]`, and `finalOf` consumes the file by its `close`. A raise with the file in the
  abandoned context runs the consumes before the raise. A borrow callback that raises does the
  same in its own context (§5).
- **No double close.** The object is linear, and `close` ends it, because the observation returns
  no rest.
- **No use after close.** After `close` there is no object left to observe.
- **The handle is hidden.** The cell is the object's state and is reachable only through the
  observations. That is `ν`'s own encapsulation, with no abstract type (#797 not needed).

**What a user would have to write to leak a file.** These are named and not designed out:
1. **Write a forged object.** Build a `ReadFile` by `unfold` over a cell obtained from the raw
   open extern, with a `close` that frees the cell without closing the descriptor.
2. **Abandon a bare handle.** Call the raw extern, `free` its `ref input` cell, and let the bare
   `input` value (own-free) be abandoned by `[let]` at an abort.
3. **Never finish.** A run that diverges, or code that is never reached (`⊤`, `absurd`).

The raw externs are visible to code that includes `lib/fs.bc`, as §11's operations are visible
today.

**The alternatives considered:**

| representation | leak by accident? | raise with the file open | why not |
|---|---|---|---|
| **codata over a cell** (recommended) | no: unused means closed | closed by the glue | — |
| `ref file` cell, not consumable, explicit `close` | no | **refused** by the checker (`finalOf`: linear and not consumable). A borrow's finaliser `d` must be a closed pure term, so it cannot call an extern | every program that raises with a file open is rejected |
| bare host opaque `file` | **yes**: own-free, abandoned at aborts by `[let]` | abandoned, descriptor leaked | leaks in ordinary code |
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

**The raising library** (`lib/fs.bc`). Errors are raises; no `Result` type appears at the
surface:

| function | type | raises |
|---|---|---|
| `open(path)` | `array_imm 'b u8 -> ReadFile` with `Fs, Fail[FsError]` | the open's error |
| `create(path)` | `array_imm 'b u8 -> WriteFile` with `Fs, Fail[FsError]` | the open's error |
| `read(f, buf)` | `ReadFile * Buf -> ReadFile * (Buf * i32)` with `Fail[FsError]` | a read error; `0` at end of file |
| `write(f, buf)` | `WriteFile * Buf -> WriteFile * Buf` with `Fail[FsError]` | a write error |
| `read_all(f)` | `ReadFile -> Buf` with `Fail[FsError]` | a read error; closes the file at the end |
| `close(f)` | `ReadFile -> 1` (and the same at `WriteFile`) | none (D3) |

- **Buffers are owned and handed back** (decision 71's hand-back shape). `Buf` is `string`, that is
  `buf u8` (`lib/text.bc`), an owned array and its length. The observation lends the buffer's spare capacity to the extern inside
  itself and gets it back before it returns. So no borrow is held while an operation is pending,
  and none crosses a raise.
- **`read` and `write` need no `Fs`.** A function given a file can read it without
  file-system authority.
- **One system call per operation**, and `read_all` grows one buffer.

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

**How the glue consumes the file.** A wrapper raises after the observation hands back the object:

    read(f, b) = let (r, f) = f.read(b); let (b, res) = r;
                 case res { inl n -> (f, (b, n)) | inr e -> raise(e) }

At the `raise`, `f` and `b` are live, so the checker consumes them by their consumes: `close` for
`f`, a free for the buffer. The error then propagates.
- **The rule is the same for every file in scope:** a file in the context of an abort is closed
  there, most recently bound first (§12's order).
- **Getting the file back after an error.** A program that wants the file and buffer back calls
  the observation `f.read(b)` itself and cases on the answer. That is a sum the library answers,
  not a `Result` the surface promotes.

**The `OwnFree` payload restriction.** A raise's payload holds no owned cell (`effRaise.hd`), so a
failed write cannot hand its buffer back in the payload. The API deals with that in two ways:
- the raising wrapper consumes the buffer at the raise, and the payload is the `FsError` alone,
  which is data;
- the observation always hands the buffer back with the answer, so a caller that wants the buffer
  after an error uses the observation, or handles the error inside the scope that owns the buffer
  (a `with to_result` around the call).

## 5. The hardest case, kept in

**The case:** a raise inside a borrow callback while two files are open, one bound outside the
callback and one inside it.

    main -> i32 + FsError = with to_result {
      let out = create("out.txt");                 // outside the callback
      let mut acc = 0;
      borrow mut acc { 'x, m ->                    // the callback: a raise unwinds it
        let inp = open("missing.txt");             // inside; raises NotFound here
        let (inp, (b, n)) = read(inp, buf(64));
        *m = n; ...
      };
      let out = write(out, ...); acc
    }

What runs, in order, when `open` raises:
1. **Inside the callback.** The raise is in the callback's own context. Every file the callback
   has opened by then is closed by `finalOf`'s consumes. In the variant that raises at `read`,
   that is `inp` (`close_input`) and `b` (freed).
2. **The callback's lend.** The unwinding form `withbor2U` ends the lend of `acc`. Its source is
   consumed by `d = consumeE (Ref i32)`, which frees the cell.
3. **The `Fs` capability.** It was reborrowed into the callback (§18), and that reborrow ends.
4. **Outside the callback.** The call site's `[then]` consumes the rest of its context. That is
   `out`, closed by its `close` (`close_output`).
5. **The handler.** `to_result` answers `inr NotFound`. The memory is empty, and both descriptors
   were closed.

**Kernel rule premises met.** `Row.Unwind`: `Fail[FsError]`'s payload is data, closed and
outliving every lifetime. The callback's row holds no answering operation, because §18 elaborates
`Fs` calls to calls on the capability, not to row operations, so §19's unwind-only rule holds.

The corpus programs `fs-hard` (this case, both variants) and `fs-raise-two` (two files open when a
third open raises) pin it, natively and on Wasm. Each has a golden and is checked with `live 0`
at the source stage.

## 6. The PR sequence to main

Every PR is merge-intended and lands with its lowering (native and WASI) and running corpus
programs.

| PR | content | corpus | depends on |
|---|---|---|---|
| **0** | `spike-804`: `experiments/ExnGlue`, `scope-804.md`, one `judgments.allow` line | — (Lean) | — |
| **1** | `fs` opaque kind and model (`Core/Opaque.lean`, `Core/Files.lean`); `fs_open_read`, `file_read`, `close_input`, `mk_fs`/`take_fs` with models and `_meets`; `ExternsMeet` and `bcc trusted` entries; `IORun` models; host code native and WASI (from fs-769); `lib/fs.bc` with `ReadFile`, `open`, `read`, `read_all`; the `Fs` effect and `wasi_fs`; `bcc run --dir` | `fs-cat` (a file named in `Args`, printed); `fs-missing` (prints `not found` via `to_result`) | — |
| **2** | `WriteFile`: `fs_open_write`, `file_write`, `close_output`; `create`, `write` | `fs-copy` (two files open at once) | 1 |
| **3** | raises with files open: the hard case | `fs-hard`, `fs-raise-two`, `fs-fake` (a fake `Fs` handler whose `open` builds a `ReadFile` over in-memory bytes, at the source stage) | 2 |
| **4** | `json-field` (operator milestone 1, #67); fs-769's `scripts/check-fs.sh` (real-file runs) in the gate | `json-field` | 3 |

- **PR 0 is independent.** `Fs` does not use `ExnGlue`, because the guarantee of accepted
  programs comes from `checkProgram_sound`. Landing it first records the argument of §1 on main.
  Order is decision D6.
- **No widening of `ExnGlue` is needed** (`case`, `Mut` lends, codata, externs). Widening would
  only extend #804's completeness result to `Fs` programs, which D7 asks about. If chosen, it is a
  PR after 4.
- **The closed `dtor-wire` branch (PR #799).** Its `directFacts` fix (`82fc9576`,
  `Backend2/Driver.lean`) was needed because `Fs` was a control effect there: `files`' clauses
  performed `FsHost`, a machine operation, inside clause work. Here `Fs` is answering, and the
  file observations call externs, so no clause work performs a machine operation. **It is not
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
- `fs-fake` runs at the source stage with a fake `Fs` handler.

## 7. Risks, NOT-do list, tempting shortcuts

**Risks, ranked** (none checked in Lean yet; each is checked by its PR's corpus program):

| # | risk | check in |
|---|---|---|
| R1 | Codata observations that take an owned `Buf` and hand back `U X` inside a sum: the checker, Backend2 and the old backend all have `Clo` (§22), but an owned array argument has not been exercised | PR 1, `fs-cat` |
| R2 | The step thunk captures the persistent externs, and the clause of `wasi_fs.open_read` builds the object: a `def` using `lib/fs.bc`'s externs at each use (§11) | PR 1 |
| R3 | **The hard case:** the `Fs` reborrow into a borrow callback that raises (§18 control-`with` reborrow, §19 unwinding forms); and T1's refusal must not fire, since `Fs` is answering | PR 3 |
| R4 | The implicit `close` at a `WriteFile` ignores `close(2)`'s error, a possible silent data loss on a write (D3) | PR 2 |
| R5 | The model does not store writes back, so `bcc interp` and native differ for a program that writes and then reads back. Such programs are run natively only (`check-fs.sh`) | PR 2 |
| R6 | WASI opens only under preopens. fs-769's walk and `bcc run --dir` are reused | PR 1 |
| R7 | The order of consumes at an abort (most recent first) is observable through descriptors, not memory, and is tested, not proved | PR 3 |

**NOT-do, and the shortcuts that mean STOP:**
- **Closing files outside the term.** No backend or runtime code closes a file, no "close
  descriptors at exit" in `run_io`'s host, and no destructor table in the backend. Every close is
  a consume in the checked term.
- **Special cases in the elaborator or checker:** no rule that recognises `File`, `close` or
  `Fs`, and no checker heuristic about where files are live. Everything goes through
  `Consumable.nu` and the existing glue.
- **Revived dtor-wire machinery:** no `must_close`, `Tok`, `[let-dtor]` or destructor syntax.
- **Work on deliberate leaks** (§2's list): no abstract types and no hiding of the raw externs.
- **No `Result` type at the surface**, and no `?`.
- **No new kernel rule or judgment**, and no change to `CDerives`.
- **A persistent descriptor** (`i32`) in any user-visible type.
- **A lend held across a pending operation**, or a buffer lent across a raise from the library.

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
  - (a) The implicit `close` ignores them (pure `F 1`, as the codata `close` must be), and an
    explicit `finish(f)` raises `Fail[FsError]` on a failed close (recommended). This adds a
    third observation, `finish : F(1 ⊕ FsError)`.
  - (b) Ignore close errors everywhere.
- **D4. A read or write error.**
  - (a) The raising wrapper closes the file (recommended). The observation answers the sum for a
    program that wants to keep it.
  - (b) Expose only the observation, and leave raising to the program.
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

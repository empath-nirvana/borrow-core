# Spike for #769 — never merged; File is a workaround pending #808

This branch checks that the Fs plan (`docs/new-core/scope-fs.md`, f3de34cb) works apart from
`File`'s representation. `File` here is scope-fs D10's two-branch thunk, boxed at `top`:
`box top U(F (ref input) & F 1)` and `box top U(F (ref output) & F 1)`. The user rejected that
representation for merging. The real `File` waits on #808 (codata observations that take
borrowed arguments).

What is here:

- `Core/Opaque.lean`: the `fs` opaque kind (D1), whose model is a byte list.
- `Core/Stdio.lean`, *Files*: the models of `fs_open_read`, `fs_open_write`, `file_write`,
  `close_input`, `close_output`, `mk_fs` and `take_fs`, each with its `_meets`. `file_read` has
  `read_into`'s type and model.
- `Frontend/Main.lean`, `modelFiles`: `bcc interp` reads the host files its arguments name into
  the model file system (D8).
- `Frontend/Sugar.lean`: the unwinding lend of a buffer crossed by an abort (scope-fs §4's first
  gap). It is an elaboration into the existing `slice_borrow_*_u`, and the kernel checks it.
- `lib/fs.bc`: the `Fs` effect, `wasi_fs`, and `open`, `create`, `read`, `read_status`,
  `read_all`, `write`, `close`, `finish` and `main_fs_error`.
- The host code is fs-769's `bc_file` / `$file`. The flat IR allocates the descriptor's cell.
  `BC_FS_TRACE=1` makes the native runtime write each open and close on standard error. It
  closes nothing.
- `Frontend/Check/Program.lean`: a `main` served by `main_fs_error` answers an exit status. The
  program installs that handler itself; it is not installed automatically.
- Corpus programs: `fs-cat`, `fs-missing`, `fs-copy`, `fs-hard`, `fs-raise-two`, `json-field`
  and `fs-buf-raise`. Their data is in `corpus/fs-data/`. Each golden comes from `bcc interp`.

Not done: the new backend (Backend2) refuses the file externs, and the closure and flat
interpreters do not run them.

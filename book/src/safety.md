# Safety guarantees

borrow-core's ownership and borrowing rules are proved sound in Lean, a proof assistant, not just
tested. For you as a programmer, that means a program `bcc` accepts:

- never uses memory after freeing it, and never frees it twice;
- never leaks: when it finishes, everything it allocated has been freed (the `live 0` at the end
  of every run);
- finishes, unless its type says it may loop: it has a `while` or a `loop`, or calls a function
  that does. Mark a function `total` and the compiler checks that it finishes;
- does only the I/O its signature allows: a function given no I/O effect can't touch a stream.

This holds however the program uses effects: errors that unwind through borrows, handlers,
generators and cancelled tasks are all covered. And it isn't only a claim about the checker in
general: each time `bcc` accepts a program, it builds a proof for that particular program, made
of the proved rules.

Two things sit outside the proof. The compiler, from the checked program to WebAssembly or
native code, is tested rather than proved: every example in this book and every program in the
test suite gives the same output compiled as in the reference interpreter, and ends with
`live 0`. And a task that holds a borrow of its own data across `await`
([Async tasks](guide/async.md#borrows-across-await)) relies on one stated assumption, which is not
proved; `bcc check` names the programs that rely on it.

[`SPEC.md`](https://github.com/empath-nirvana/borrow-core/blob/main/SPEC.md) is the precise
definition of the language, and
[`docs/internals/proved.md`](https://github.com/empath-nirvana/borrow-core/blob/main/docs/internals/proved.md)
lists the theorems and where they live in the Lean sources.

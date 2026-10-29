# Declarations and programs

See [`docs/syntax-core.md`](../../syntax-core.md) (the part marked `declarations`).

The standard externs (the streams, the clock and the arguments, and their operations) are
compiled and run ([Standard I/O as capabilities](../elaboration/standard-io.md), [Input and
output](../../../book/src/guide/io.md), SPEC §11, §34); any other extern is checked but not compiled. `bcc trusted <file>` lists a program's externs with their contracts,
host implementations and assurance levels.

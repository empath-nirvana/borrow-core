# Declarations and programs

{{#include ../../../docs/syntax-core.md:declarations}}

The standard I/O externs (`stdin`, `stdout`, `stderr`, `read_byte`, `write_byte`) are compiled
and run ([Command-line tools](../guide/command-line-tools.md), SPEC §11); any other extern is
checked but not compiled. `bcc trusted <file>` lists a program's externs with their contracts,
host implementations and assurance levels.

# Unsafe code

**Planned** (#7 for externs, now built; #18 for handlers); the design is decision 27 in
[Design decisions](../../decisions.md).

Externs are built: a program declares them, each becomes a variable in `main`'s initial context,
and the theorems hold for every implementation that meets the externs' types. Standard I/O is the
first set of them ([Command-line tools](../command-line-tools.md)).

There are no unsafe blocks inside safe code. `unsafe` is to be an extern whose body the compiler
compiles: safe code meets unchecked code only at a boundary with a semantic-type contract. The
contract is either assumed, and then it is a hypothesis of the end-to-end theorem, or proved in
Lean. The set of unproved boundaries is the program's trusted base, which `bcc trusted` lists
with each boundary's assurance level, and a boundary can move from host code to a compiled body
to a proved body without its type or its callers changing.

An extern the compiler has no implementation for is checked but not compiled:

```bc,check
extern c : ref i32

main : F i32 = return (free[i32] c)
```

# Unsafe code and externs

**Planned: #7** (externs and standard I/O); the design is decision 27 in
[Design decisions](../../decisions.md).

## Externs

`extern name : A` declares a value that the program receives from outside. The parser and checker
already accept it: each extern becomes a variable in `main`'s initial context, the Fundamental
Property holds for every implementation of the externs that meets their types, and `main` must
consume every non-persistent extern. The compiler does not support externs yet, so `bcc run` and
`bcc interp` need a closed `main`. This program checks, but does not run:

```bc,check
extern c : ref i32

main : F i32 = return (free[i32] c)
```

Standard input and output are planned as linear capabilities, run by the interpreter as cells and
compiled to WASI `fd_read`/`fd_write`:

```text
main : ref Input -o ref Output -o F (ref Input * ref Output)
```

## Unsafe code

There are no unsafe blocks inside safe code. `unsafe` is to be an extern whose body the compiler
compiles: safe code meets unchecked code only at a boundary with a semantic-type contract. The
contract is either assumed, and then it is a hypothesis of the end-to-end theorem, or proved in
Lean. The set of unproved boundaries is the program's trusted base, and a boundary can move from
host code to a compiled body to a proved body without its type or its callers changing.

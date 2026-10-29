# Structs as blocks, family borrows

## Blocks

A struct is a **block**: several cells allocated together, one per field. Its layout is a
**shape**, a binary tree whose leaves are the field types:

```text
shape Pair = node (leaf B) (leaf B)
```

Two types are computed from a shape `σ`:

- `val σ` is the struct's contents: the leaf types, paired as in the tree. For `Pair` it is
  `B * B`.
- `block σ` is the struct's handle: a cell per leaf, paired the same way. For `Pair` it is
  `ref B * ref B`.

So a block's handle is exactly the family of its field cells, and each field is a separate
place. `alloc_s[σ] : val σ => block σ` allocates a block, and `free_s[σ] : block σ => val σ`
frees it.

## Borrowing a whole block

`withbor_s_mut[σ, 'c, T]` borrows every field of a block mutably at one lifetime `'c`:

```text
block σ => (all 'c < dom. fam mut 'c σ => box 'c T) => block σ * T
```

`fam mut 'c σ` is a `mut 'c` borrow of each leaf, paired as in the shape. The callback can take
it apart and work on the fields independently. `withbor_s_imm` is the same with `imm` borrows.

This program allocates a block `{inl (), inr ()}`, borrows both fields, swaps their contents with
two nested `withswap`s, and frees the block:

```bc
type B = 1 + 1
shape Pair = node (leaf B) (leaf B)

main : F (B * B) =
  s0 <- return (alloc_s[Pair] (inl (), inr ()));
  r <- return (withbor_s_mut[Pair, 'c, 1] s0
         (thunkv Fun 'c < top. return (thunkv fun (m : fam mut 'c Pair) ->
            let (ma, mb) = m;
            q1 <- return (withswap['c, B, 1] ma (thunkv fun (x : B) ->
                    q2 <- return (withswap['c, B, B] mb (thunkv fun (y : B) -> return (x, y)));
                    let (mb2, y2) = q2;
                    return (y2, ())));
            let (ma2, u1) = q1;
            let () = u1;
            return (boxed['c] ()))));
  let (s, u) = r;
  let () = u;
  ab <- return (free_s[Pair] s);
  return ab
-- answer: (inr (), inl ())
```

A block borrow needs **plain** leaves and a plain result: no lifetimes and no thunks. At present
`i32` and `i64` are not plain, so a block of integers cannot be borrowed this way (planned: #11).

## Family borrows of separate cells

`withbor_f2_mut` borrows two separate cells mutably at one lifetime. It is derived from two nested
`withbor`s and a lifetime shortening, so it adds no new typing rule:

```text
withbor_f2_mut['c, 'a, 'b, @w, A, B, T] :
  ref A * ref B => (all 'c < dom. mut 'c A * mut 'c B => box 'c T) => (ref A * ref B) * T
```

`'c` is the callback's lifetime. `'a` and `'b` name the two internal borrows and appear nowhere
else in the program. `@w` is a lifetime that `A` outlives, as in `withbor2`.

```bc
main : F (i32 * i32) =
  ra <- return (alloc[i32] i32[9]);
  rb <- return (alloc[i32] i32[500]);
  r <- return (withbor_f2_mut['c, 'a, 'b, top, i32, i32, 1] (ra, rb)
         (thunkv Fun 'c < top. return (thunkv fun (m : mut 'c i32 * mut 'c i32) ->
            let (ma, mb) = m;
            q1 <- return (withswap['c, i32, 1] ma (thunkv fun (x : i32) ->
                    q2 <- return (withswap['c, i32, i32] mb (thunkv fun (y : i32) -> return (x, y)));
                    let (mb2, y2) = q2;
                    return (y2, ())));
            let (ma2, u1) = q1;
            let () = u1;
            return (boxed['c] ()))));
  let (s, u) = r;
  let () = u;
  let (ra2, rb2) = s;
  a <- return (free[i32] ra2);
  b <- return (free[i32] rb2);
  return (a, b)
-- answer: (i32[500], i32[9])
```

`withbor_f2_imm` is the immutable version.

## Shortening a family

`shorten_mut[σ, @a] V` turns `V : fam mut @b σ` into `fam mut @a σ` for a shorter `@a`, leaf by
leaf; `shorten_imm` does the same for `fam imm`. For a single borrow, use `(V :> @a)`.

## Not yet in the syntax

Records and variants with named fields are derived rules in `Core/Records.lean` but have no
syntax yet: write them with pairs and sums. Block provenance is not enforced: a block's handle
may be taken apart and its leaves re-paired with other cells (`SPEC.md` §5, Open; #20).

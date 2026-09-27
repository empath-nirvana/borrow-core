# Arrays

An array is a run of places whose number is known only when the program runs. `array A` owns
`n` cells, each holding an `A`; its value is the pair of a base location and the length `n`, and
element `i` is the cell at base + `i`. It is the run-time counterpart of a struct's block
([Structs as blocks](blocks-and-families.md)): a block has a fixed shape, an array has a length.

`array A` is linear, like `ref A`: it owns memory, so it is used once and freed once.

## Making and freeing

`array_new[A]` takes a length and a *tabulator*, a `!`-function from the index to the element,
and calls it once per index, in order. A negative length makes the empty array.

`array_size[A]` returns the array with its length, and `array_replace[A]` puts a new element at
an index and returns the old one. An index out of range is not an error that stops the program:
the result is `inr`, carrying the new element back.

```bc
type A = array i32

def tab : !(i32 => i32) = !thunkv fun (i : i32) -> return ((unbang host[mul32]) (i, i32[10]))

def replace : A * (i32 * i32) => A * (i32 + i32) = unbang array_replace[i32]

main : F (i32 * ((i32 + i32) * (i32 + i32))) =
  a <- return ((unbang array_new[i32]) (i32[4], tab));
  q <- return ((unbang array_size[i32]) a);
  let (a1, n) = q;
  q1 <- return (replace (a1, (i32[2], i32[42])));
  let (a2, old) = q1;
  q2 <- return (replace (a2, (i32[9], i32[5])));
  let (a3, oob) = q2;
  return (n, (old, oob))
-- answer: (i32[4], (inl i32[20], inr i32[5]))
```

The array `a3` is not used again, so the checker frees it at the end of `main`
([Implicit destructors](implicit-destructors.md)). `array A` has a destructor whenever `A` has
one: every element goes to `A`'s destructor, and then the cells are freed. The explicit form is
`array_free[A]`, which takes the consumer to call on each element:

```bc
type R = ref i32

def mk : !(i32 => R) = !thunkv fun (i : i32) -> return (alloc[i32] i)

def consume : !(R => 1) = !thunkv fun (c : R) -> x <- return (free[i32] c); return ()

main : F i32 =
  a <- return ((unbang array_new[R]) (i32[3], mk));
  u <- return ((unbang array_free[R]) (consume, a));
  let () = u;
  return i32[3]
-- answer: i32[3]
```

`live 0` after the value is the check that all three cells and the array itself were freed.

## Borrowing

An array is a value, so it is borrowed the way any value is: in a cell. `withbor1` on a
`ref (array A)` lends `imm 'x (array A)`, a borrow of the cell that holds the array.

To reach the elements, `withload` reads through that borrow. Its callback receives
`view 'y (array A)`, which is `array_imm 'y A`: the *family* of views of the array's elements,
at a lifetime `'y` inside `'x`. On a family:

| constant | type |
|---|---|
| `array_len['y, A]` | `!(array_imm 'y A => i32)` |
| `array_get['y, A]` | `!(array_imm 'y A * i32 => imm 'y A + 1)` |
| `array_copy['y, A]` | `!(array_imm 'y A => array_imm 'y A * array_imm 'y A)` |
| `array_forget['y, A]` | `!(array_imm 'y A => 1)` |

`array_get` gives the view of one element at the family's own lifetime, or `inr ()` past the
end. The view is read with `withload` like any `imm` borrow.

```bc
type A = array i32
type T = i32 * (i32 + 1)

def tab : !(i32 => i32) = !thunkv fun (i : i32) -> return ((unbang host[add32]) (i, i32[100]))

def read : all 'z < top. imm 'z i32 => i32 =
  thunkv Fun 'z < top. return (thunkv fun (v : imm 'z i32) ->
    return (withload['z, 'w, i32, i32] v
      (thunkv Fun 'w < dom. return (thunkv fun (x : i32) -> return (boxed['w] x)))))

main : F T =
  a <- return ((unbang array_new[i32]) (i32[3], tab));
  r <- return (alloc[A] a);
  q <- return (withbor1['x, A, T] r
         (thunkv Fun 'x < top. return (thunkv fun (b : imm 'x A) ->
            t <- return (withload['x, 'y, A, T] b
                   (thunkv Fun 'y < dom. return (thunkv fun (f : array_imm 'y i32) ->
                      c <- return ((unbang array_copy['y, i32]) f);
                      let (f1, f2) = c;
                      n <- return ((unbang array_len['y, i32]) f1);
                      g <- return ((unbang array_get['y, i32]) (f2, i32[1]));
                      x : i32 + 1 <- case g {
                        inl v -> return (inl (read ['y] v))
                      | inr u -> return (inr u)
                      };
                      return (boxed['y] (n, x)))));
            return (boxed['x] t))));
  let (r2, t) = q;
  return t
-- answer: (i32[3], inl i32[101])
```

The cell `r2` and the array in it are dropped implicitly when `main` ends.

To change an array through a borrow, borrow the cell `mut` with `withbor2`, and let `withswap`
lend the array itself to a function that returns it:

```bc
type A = array i32

def tab : !(i32 => i32) = !thunkv fun (i : i32) -> return i

def replace : A * (i32 * i32) => A * (i32 + i32) = unbang array_replace[i32]

main : F ((i32 + i32) * (i32 + i32)) =
  r <- return (alloc[A] ((unbang array_new[i32]) (i32[2], tab)));
  q <- return (withbor2['x, top, A, i32 + i32] r
         (thunkv Fun 'x < top. return (thunkv fun (m : mut 'x A) ->
            s <- return (withswap['x, A, i32 + i32] m
                   (thunkv fun (a : A) -> return (replace (a, (i32[1], i32[7])))));
            let (m2, o) = s;
            return (boxed['x] o))));
  let (r2, first) = q;
  q2 <- return (replace (free[A] r2, (i32[1], i32[0])));
  let (a, now) = q2;
  return (first, now)
-- answer: (inl i32[1], inl i32[7])
```

## What the checker rejects

A view of an element lives no longer than its family. Here the callback of `withload` tries to
return the view of element 0 at the outer lifetime `'x`:

```bc,reject
type A = array i32

def tab : !(i32 => i32) = !thunkv fun (i : i32) -> return i

main : F 1 =
  a <- return ((unbang array_new[i32]) (i32[2], tab));
  r <- return (alloc[A] a);
  q <- return (withbor1['x, A, 1] r
         (thunkv Fun 'x < top. return (thunkv fun (b : imm 'x A) ->
            v <- return (withload['x, 'y, A, imm 'x i32] b
                   (thunkv Fun 'y < dom. return (thunkv fun (f : array_imm 'y i32) ->
                      g <- return ((unbang array_get['y, i32]) (f, i32[0]));
                      case g {
                        inl e -> return (boxed['y] e)
                      | inr u -> absurd u
                      })));
            return (boxed['x] ()))));
  let (r2, u) = q;
  return u
-- expect: 14:52: type mismatch: expected `imm 'x i32`, but this has type `imm 'y i32`
```

And an array cannot be changed while it is borrowed: the cell is lent to the first borrow, so a
second borrow of it, `mut`, uses it twice.

```bc,reject
type A = array i32

def tab : !(i32 => i32) = !thunkv fun (i : i32) -> return i

main : F 1 =
  r <- return (alloc[A] ((unbang array_new[i32]) (i32[2], tab)));
  q <- return (withbor1['x, A, 1] r
         (thunkv Fun 'x < top. return (thunkv fun (b : imm 'x A) ->
            q2 <- return (withbor2['z, top, A, 1] r
                    (thunkv Fun 'z < dom. return (thunkv fun (m : mut 'z A) ->
                       return (boxed['z] ()))));
            return (boxed['x] ()))));
  let (r2, u) = q;
  return u
-- expect: 7:16: `r` is used twice here, and its type `ref array i32` is not persistent
```

## Why an element's view can live as long as the family

A borrow of a cell cannot hand out a view of something the cell *owns* at the borrow's own
lifetime: that is a view through a pointer, and the model excludes it
([decision 5](../decisions.md)). That is why `withload` gives the family at a shorter lifetime
`'y`. The family itself is not a pointer: it is the views of the elements, side by side, and
nothing in it owns anything. `array_get` takes one of those views out and forgets the rest, so a
view of an element at `'y` is sound (`SPEC.md` §9, `Core/Arrays.lean`).

## Not yet

Splitting an array at a run-time index, iterating over one, a growable `Vec`, and strings are
planned. An array cannot yet be borrowed without a cell, and there is no `mut` view of a single
element.

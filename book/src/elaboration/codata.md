# Codata: iterators, streams, delay

Data is built and then taken apart. **Codata** is defined by what can be asked of it: a stream
is something you can ask for its next element, or close. borrow-core has one codata former,
`nu X. C`, a computation type. `C` is a lazy pair of **observations**, each returning a value in
which `U X`, "the rest", may appear.

Three abbreviations cover the common cases:

| written | expands to | what it is |
|---|---|---|
| `stream A` | `nu X. F (A * U X) & F 1` | always yields an `A` and the rest |
| `iter A R R'` | `nu X. F (A * U X + R) & F R'` | yields an `A` and the rest, or finishes with `R`; closing early returns `R'` |
| `delay A` | `nu X. F (A + U X) & F 1` | a loop: either done with an `A`, or asks to be run again |

The second observation (`.2`) is always `close`. No rule discards a thunk, so codata that is
not run to its end must be closed, and closing is where it frees what it holds.

## Building codata: coiteration

Codata is built from a **state** `S` and a **step** that says what each observation does at a
state:

| constant | type |
|---|---|
| `unfold[C, S]` | `!U (S -o C′[S/X]) => !U (S -o C)`, for `C = nu X. C′` |
| `unfold_s[A, S]` | `unfold[stream A, S]` |
| `fixd[A, S]` | `unfold[delay A, S]` |

The step is `C′` with the state in place of the rest. For a stream it is
`!U (S -o F (A * S) & F 1)`: given a state, either yield an element and the next state, or close.

`nu_out M` unrolls a codata computation to its observations, and `nu_in M` rolls them back.
`stream_out`/`stream_in` and `delay_out`/`delay_in` are other spellings of the same two forms.
Creating the codata value for a given initial state `z` goes through the observations once,
because `thunkv` needs a literal lazy pair:

```text
thunkv stream_in < (stream_out (force f z)).1, (stream_out (force f z)).2 >
```

## Streams

The stream 7, 17, 27, …, with two elements taken:

```bc
def nats_step : !U (i32 -o F (i32 * i32) & F 1) =
  !thunkv fun (s : i32) ->
    < return (s, (unbang host[add32]) (s, i32[10])),
      return () >

main : F (i32 * i32) =
  f <- return (unbang (unfold_s[i32, i32] nats_step));
  z : i32 <- return i32[7];
  t0 <- return (thunkv stream_in < (stream_out (force f z)).1, (stream_out (force f z)).2 >);
  p1 <- (stream_out (force t0)).1;
  let (x1, t1) = p1;
  p2 <- (stream_out (force t1)).1;
  let (x2, t2) = p2;
  return (x1, x2)
-- answer: (i32[7], i32[17])
```

The rest of the stream, `t2`, is never used, so the checker closes it (see
[Implicit destructors](implicit-destructors.md)).

## Finite iterators

`range (1, 5)` as an `iter i32 i32 1`: `next` yields `i` while `i <= n`, and then finishes with
`i`. `pull` is one step of a sum. Six pulls are five elements and the finish.

```bc
type It = U (iter i32 i32 1)
type Pull = i32 * It + i32 * i32

def plus : i32 * i32 => i32 = unbang host[add32]

def range_step : !U (i32 * i32 -o F (i32 * (i32 * i32) + i32) & F 1) =
  !thunkv fun (s : i32 * i32) ->
    < let (i, n) = s;
      case (unbang host[gt_s32]) (i, n) {
        inl u -> return (inl (i, (plus (i, i32[1]), n)))
      | inr u -> return (inr i)
      },
      let (i, n) = s;
      return () >

def range : i32 * i32 => It =
  thunkv fun (s : i32 * i32) ->
    f <- return (unbang (unfold[iter i32 i32 1, i32 * i32] range_step));
    return (thunkv nu_in < (nu_out (force f s)).1, (nu_out (force f s)).2 >)

def pull : Pull => Pull =
  thunkv fun (st : Pull) ->
    case st {
      inl a ->
        let (acc, it) = a;
        o <- (nu_out (force it)).1;
        case o {
          inl p -> let (x, rest) = p; return (inl (plus (acc, x), rest))
        | inr r -> return (inr (acc, r))
        }
    | inr d -> return (inr d)
    }

main : F (i32 * i32) =
  it <- return (range (i32[1], i32[5]));
  st <- return (pull (pull (pull (pull (pull (pull (inl (i32[0], it) : Pull)))))));
  case st {
    inl a -> let (acc, rest) = a; return (acc, i32[4294967295])
  | inr d -> return d
  }
-- answer: (i32[15], i32[6])
```

The close observation's result `R'` is the **residual**: what the iterator hands back when it
is closed early. An iterator over a cell can return the cell (`iter A R (ref A)`); see
`corpus/iter-close.bc`.

## Loops: `delay`

A loop that may not terminate has type `delay A`. Each run of `.1` performs one step and returns
`inl a` when done or `inr d`, the rest of the loop, otherwise. The program decides how many
steps to run, and closes the loop if it stops early. Nothing is claimed about termination: the
type says the loop may not end.

```bc
def step : !U (i32 -o F (i32 + i32) & F 1) =
  !thunkv fun (n : i32) ->
    < case (unbang host[eqz32]) n {
        inl u -> return (inr ((unbang host[sub32]) (n, i32[1])))
      | inr u -> return (inl i32[99])
      },
      return () >

main : F (i32 + 1) =
  f <- return (unbang (fixd[i32, i32] step));
  s <- return i32[1];
  d0 <- return (thunkv delay_in < (delay_out (force f s)).1, (delay_out (force f s)).2 >);
  o1 <- (delay_out (force d0)).1;
  case o1 {
    inl a -> return (inl a)
  | inr d1 ->
      o2 <- (delay_out (force d1)).1;
      case o2 {
        inl a -> return (inl a)
      | inr d2 -> u <- (delay_out (force d2)).2; return (inr u)
      }
  }
-- answer: inl i32[99]
```

From the state `1` the loop takes one step to `0` and then finishes. There is no syntax for
running a loop to completion yet: a driver is written out to the depth wanted, as here.

## Beyond this chapter

The surface's generators and stored generators are codata of this former, `pull A B R`, and the
adapters (`map`, `filter`, `take`, …) are library code over them, not new formers
([Iteration](../guide/iteration.md)). External iteration over borrowed linked structures is still
open (#57).

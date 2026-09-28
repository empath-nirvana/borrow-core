# Divergence

A function may loop without bound: read until its input ends, serve until it is stopped, or run a
loop nobody knows to finish. Divergence is an effect, and like any effect it shows in the type.
You do not write it: **div is inferred. Mark a function `total` to guarantee that it terminates.**
Code that is not div terminates, and that is a theorem.

## A loop in a helper

A `for` over the input may never end, so a function with one is div. Here `count_lines` loops to
the end of its input and hands the count back; `main` calls it and then writes the count:

```bc
def count_lines : In => In * i32 =
  thunkv fun (c : In) ->
    n : i32 <- return i32[0];
    for b in bytes c {
      n : i32 <- case (unbang host[eq32]) (b, i32[10]) {
        inl other -> return n
      | inr newline -> return ((unbang host[add32]) (n, i32[1]))
      };
      return ()
    };
    return (c, n)

main : F i32 =
  n <- return (count_lines (&stdin));
  _ <- return (put_dec (&stdout, n));
  _ <- return (putb (&stdout, i32[10]));
  return n
-- stdin: one
-- stdin: two
-- output: 2
-- answer: i32[2]
```

Nothing is marked. `count_lines` has a `for`, so it is div; `main` calls it, so `main` is div
too. The call is direct style: `main` goes on when the loop finishes. A function is div when its
body has a `for`, or calls a div function in direct style (`x <- return (f V); …`). Definitions
come before their uses, so one pass in order finds every div function.

## `total`: a promise the compiler checks

`total def` says a function terminates. It is the annotation a library writes, and the compiler
holds it to it:

```bc,reject
total def count : In => In * i32 =
  thunkv fun (c : In) ->
    n : i32 <- return i32[0];
    for b in bytes c {
      n : i32 <- return ((unbang host[add32]) (n, i32[1]));
      return ()
    };
    return (c, n)

main : F i32 =
  r <- return (count (&stdin));
  let (stdin, n) = r;
  return n
-- expect: 4:5: `count` is declared `total`, but it has a `for` (SPEC §14)
```

`div def` is allowed too, for documentation, but inference never needs it.

## Running a loop is handling it

A div computation is a loop that something has to run. The runtime runs `main`'s until it
finishes, however long that takes. `div_fuel` runs one for at most `n` steps, and closes it if it
has not finished; code that uses it is total. Whether the Collatz loop always reaches 1 is an open
problem, so `collatz` is div, but a bounded run of it is `total`:

```bc
def collatz_step : !U (i32 * i32 -o F (i32 + (i32 * i32)) & F 1) =
  !thunkv fun (s : i32 * i32) ->
    < let (n, k) = s;
      case (unbang host[eq32]) (n, i32[1]) {
        inl other ->
          k2 <- return ((unbang host[add32]) (k, i32[1]));
          case (unbang host[eqz32]) ((unbang host[and32]) (n, i32[1])) {
            inl odd ->
              return (inr ((unbang host[add32]) ((unbang host[mul32]) (n, i32[3]), i32[1]), k2))
          | inr even -> return (inr ((unbang host[shr_u32]) (n, i32[1]), k2))
          }
      | inr one -> return (inl k)
      },
      let (n, k) = s;
      return () >

-- The steps from `n` to 1: a loop, written in core. Its type says it is div.
def collatz : i32 => U (loop i32 1) =
  thunkv fun (n : i32) ->
    f <- return (unbang (unfold[loop i32 1, i32 * i32] collatz_step));
    s0 : i32 * i32 <- return (n, i32[0]);
    return (thunkv nu_in < (nu_out (force f s0)).1, (nu_out (force f s0)).2 >)

total def collatz_within : i32 * i32 => i32 + 1 =
  thunkv fun (p : i32 * i32) ->
    let (n, fuel) = p;
    return (div_fuel[i32, 1] (collatz n, fuel))

main : F ((i32 + 1) * (i32 + 1)) =
  a <- return (collatz_within (i32[27], i32[200]));
  b <- return (collatz_within (i32[27], i32[50]));
  return (a, b)
-- answer: (inl i32[111], inr ())
```

A loop cut off this way hands back what it holds: a loop over the input hands the capability
back, and the program reads on (`corpus/io-fuel.bc`). Timeouts and yielding to a scheduler are
further handlers of the same kind.

## Higher-order functions

A callback's type says whether it may loop. A higher-order function is written once, for a
total callback, and serves both kinds: given a div function, the compiler makes a copy of it at
the callback's type, and the copy is div. Given a total one, it uses the function as written,
which stays total. So functions do not come in two colors (`corpus/div-hof.bc`).

## What it means in core

A div function returning `B` has the core type `A => U (loop B R)`: a call runs the function up
to its first loop and returns the rest as a loop, which finishes with `B`, or, closed early,
hands back the residual `R`, the capabilities the function holds (or `()`). A call of a div
function in direct style is `div_bind`, the delay bind, which runs one loop and then the rest of
the function; it is ordinary library code over `unfold` (`lib/div.bc`). `bcc desugar` shows
all of it; the checker sees only core, and nothing in the kernel knows about `div`.

## What is proved

A closed program of type `F A`, one that does not return a loop, has no infinite run
(`total_no_infinite_run`, [What is proved](../proved.md)). A program whose `main` loops is safe
one prefix at a time: every finite part of its run is safe.

## Not yet

- `for` runs over the input, which may not end; a `for` over a finite source, allowed in total
  code, is not provided.
- A `for` body is one step of its loop and must be total: no `for` or div call inside it.
- Specialization covers a named function given a named callback; a callback held in a closure or
  a variable of the caller is not specialized.

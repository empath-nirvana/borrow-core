# Standard library

The library is ordinary borrow-core code in `lib/`, checked with your program. `include name`
brings one module into scope, together with the modules it includes itself; only what a program
calls is compiled. This page lists each module's user-facing names, and the guide chapter linked
from each section teaches them.

| include | for | brings in |
|---|---|---|
| (none) | [the prelude](#the-prelude) | |
| [`fail`](#fail) | errors | |
| [`arith`](#arith) | Euclidean division | `fail` |
| [`rec`](#rec) | recursion handlers | `buf` |
| [`io`](#io) | the I/O effects, decimal output | |
| [`textio`](#textio) | text I/O | `text`, `io` |
| [`text`](#text) | strings and text views | `buf`, `slice`, `fail` |
| [`buf`](#buf) | growable buffers, a priority queue | |
| [`slice`](#slice) | array views | |
| [`key`](#key) | equality, hashing, order | `slice` |
| [`map`](#map) | hash map and set | `key`, `buf` |
| [`list`](#list) | a generic list | `rec` |
| [`yield`](#yield) | generators | |
| [`adapters`](#adapters) | generator adapters | `yield` |
| [`iters`](#iters) | adapters over data | |
| [`async`](#async) | tasks and a scheduler | `list` |
| [`float`](#float) | float operations, printing, parsing | `textio` |

## Reading the signatures

Signatures are written as they are declared. Two conventions recur.

**Hand-back functions.** A function that changes or reads a value without consuming it takes the
value first and returns it first: `push(b: buf A, x: A) -> buf A * 1`. You call it with a lend,
`push(&mut b, x)`, which moves `b` in, rebinds it to what comes back, and answers the rest, here
`()`. `len_of(&b)` reads one the same way and answers the `i32`. A lend must be the whole of a
`let` or a statement: `let n = len_of(&b);`.

A function that returns the value alone, with nothing after it (`truncate`, `clear`, `reserve`,
`grow`, `heap_push`, `clear_str`, and the view functions that hand back an `array_mut`), is
rebound with `let`: `let b = truncate(b, 1);`, `let v = set(v, 0, x);`.

**Sums.** `T + 1` is an optional `T`: `inl x` when there is one, `inr ()` when not. `bool` is
`1 + 1`. An `Option[T]` matches as `Some(x)` or `None`.

## The prelude

In scope in every program, with no `include`.

| name | signature | |
|---|---|---|
| `true`, `false` | `bool` | |
| `not` | `!(bool => bool)` | negation |
| `to_i32` | `!(u8 => i32)` | a byte as `0`…`255` |
| `to_u8` | `!(i32 => u8)` | the low byte of an `i32` |
| `Option[T]` | `data Option[T] = Some(T) \| None` | an optional value |
| `Vec[T]` | `data Vec[T] = Vec(buf T)` | a growable vector; every [`buf`](#buf) function works on it |

The built-in forms (`alloc`, `free`, `array_new`, `checked_div`, `div_fuel`, …) are in the
[Language reference](language-reference.md).

## fail

The `Fail` effect and its handlers. [Errors](guide/errors.md) teaches them.

| name | signature | |
|---|---|---|
| `Fail[E]` | `effect Fail[E] { ctl raise(e: E) -> never }` | an error of type `E` |
| `raise(e)` | `e: E`, answers `never` | `e` to the nearest handler of `Fail[E]` |
| `to_result` | `handler to_result[E, A]: Fail[E], A -> A + E` | `inl` the value, or `inr` the error |
| `default(d)` | `handler default[E, A](d: A): Fail[E], A -> A` | the value, or `d` |
| `map_err(f)` | `handler map_err[E, E2, A](f: !(E => E2)): Fail[E], A -> A with Fail[E2]` | an error `e` raised again as `f(e)` |

## arith

Euclidean division, and the names of division's error. `/` and `%` raise `Fail[DivError]` with no
`include`; `include arith` adds the rest. [Division](guide/errors.md#division) teaches them.

| name | signature | |
|---|---|---|
| `DivError` | `type DivError = 1 + 1` | division's error |
| `div_by_zero`, `div_overflow` | `DivError` | `inl ()` and `inr ()`: a zero divisor, and `MIN / -1` |
| `div_euclid` | `div_euclid[T](a: T, b: T) -> T` | the `q` of `a = b * q + r` with `0 <= r < \|b\|`; raises as `/` does |
| `rem_euclid` | `rem_euclid[T](a: T, b: T) -> T` | that `r`, never negative |

```bc
include textio
include arith

-- The minute within its hour of `m` minutes after midnight, which may be negative.
fn minute(m: i32) -> i32 = rem_euclid(m, 60)

main -> 1 =
  print_dec(minute(0 - 75));
  print_byte(b' ');
  print_dec((0 - 75) % 60);
  print_byte(b' ');
  match checked_div(minute(0), 0) {
    inl q -> print_dec(q)
  | inr e -> match e { inl u -> print_lit("division by zero") | inr u -> print_lit("overflow") }
  };
  print_byte(b'\n')
-- output: 45 -15 division by zero
```

## rec

The handlers a recursive function needs. A function that calls itself has a budget of 10000
levels and performs `Exhausted` when it runs out. [Recursion](guide/data.md#recursion) teaches
them.

| name | signature | |
|---|---|---|
| `Exhausted` | `effect Exhausted { ctl exhausted() -> never }` | the budget ran out |
| `on_exhausted(d)` | `handler on_exhausted[A](d: !(1 => A)): Exhausted, A -> A` | the value, or `d(())` |
| `exhausted_to_option` | `handler exhausted_to_option[A]: Exhausted, A -> A + 1` | `inl` the value, or `inr ()` |
| `deep` | `with deep { e }` | the recursions in `e` keep their pending calls on the heap: no depth limit |

```bc
include textio
include rec

fn depth(n: i32) -> i32 = if n == 0 { 0 } else { 1 + depth(n - 1) }

main -> 1 =
  match with exhausted_to_option { depth(100) } {
    inl d -> print_dec(d)
  | inr u -> print_lit("too deep")
  };
  print_byte(b' ');
  print_dec(with deep { depth(100) });
  print_byte(b'\n')
-- output: 100 100
```

## io

The system's effects, and decimal output. `main` is given each effect by the platform; any other
function performs them and its caller serves them. [Input and output](guide/io.md) teaches them.

| effect | operations |
|---|---|
| `Stdout` | `print_byte(b: u8)`, `print_bytes(v: array_imm 'b u8)` |
| `Stderr` | `eprint_byte(b: u8)`, `eprint_bytes(v: array_imm 'b u8)` |
| `Stdin` | `input_byte() -> u8 + 1`, `input_into(v: array_mut 'b u8) -> array_mut 'b u8 * i32` |
| `Clock` | `now() -> i64` (nanoseconds, monotonic), `sleep(ns: i64)` |
| `Args` | `arg_byte() -> u8 + 1`: the arguments' bytes, each argument followed by `0` |

| name | signature | |
|---|---|---|
| `print_dec` | `print_dec(x: i32) -> 1` | `x` in decimal to standard output |
| `print_dec64` | `print_dec64(x: i64) -> 1` | the same at `i64` |
| `eprint_dec` | `eprint_dec(x: i32) -> 1` | `x` in decimal to standard error |
| `ns_of_ms` | `ns_of_ms(ms: i32) -> i64` | milliseconds as nanoseconds, for `sleep` |

## textio

Text over the standard streams. [Input and output](guide/io.md) teaches them.

| name | signature | |
|---|---|---|
| `print_lit` | `print_lit(l: lit) -> 1` | a literal `"…"` to standard output, in one write |
| `print_str` | `print_str<'a>(t: text 'a) -> 1` | a text view to standard output |
| `print_string` | `print_string(s: string) -> string` | a string to standard output, and the string back |
| `eprint_lit`, `eprint_str` | as `print_lit`, `print_str` | to standard error |
| `read_input` | `read_input() -> string` | the whole of standard input |
| `next_arg` | `next_arg(s: string) -> string * bool` | the next argument appended to `s`, and whether there was one |

```bc
include textio

main -> 1 =
  let s = read_input();
  let n = borrow imm s { t -> fold_lines(t, !{ (l, k) -> k + 1 }, 0) };
  let s = print_string(s);
  print_dec(n);
  print_lit(" lines\n")
-- stdin: alpha
-- stdin: beta
-- output: alpha
-- output: beta
-- output: 2 lines
```

## text

`string`, a growable buffer of UTF-8 bytes, and `text 'a`, a view of some (`text_mut 'a` when it
is exclusive). A view is lent from a string with `borrow imm s { t -> … }`, or from a literal with
`borrow imm "…" { t -> … }`, and the functions that cut it answer sub-views without copying. A
string is a [`buf`](#buf) of `u8`, so `len_of`, `pop` and the rest work on it.
[Buffers and strings](guide/data.md#buffers-and-strings) teaches them.

**Building a string.** The `push_` functions are called with `&mut s`.

| name | signature | |
|---|---|---|
| `box string(cap)` | `string` | an empty string with room for `cap` bytes (`string_new(cap)`) |
| `push_lit` | `push_lit(s: string, l: lit) -> string * 1` | a literal appended |
| `push_str` | `push_str<'a>(s: string, t: text 'a) -> string * 1` | a view's bytes appended |
| `push_byte` | `push_byte(s: string, x: u8) -> string * 1` | a byte appended |
| `push_char` | `push_char(s: string, c: i32) -> string * 1` | a character (a scalar value) appended as UTF-8 |
| `push_dec` | `push_dec(s: string, x: i32) -> string * 1` | `x` in decimal appended |
| `clear_str` | `clear_str(s: string) -> string` | emptied, the capacity kept |
| `to_string` | `to_string<'a>(t: text 'a) -> string` | a copy of a view |
| `string_of_lit` | `string_of_lit(l: lit) -> string` | a copy of a literal |

**Reading text.**

| name | signature | |
|---|---|---|
| `eq_lit` | `eq_lit<'a>(t: text 'a, l: lit) -> bool` | whether `t` has the literal's bytes |
| `lit_len` | `lit_len(l: lit) -> i32` | a literal's length in bytes |
| `count_chars` | `count_chars<'a>(t: text 'a) -> i32` | the number of characters |
| `char_at` | `char_at<'a>(t: text 'a, i: i32) -> i32 * i32` | the character at byte `i`, and its length in bytes |
| `split_char` | `split_char<'a>(t: text 'a) -> i32 * text 'a + 1` | the first character and the rest |
| `split_once` | `split_once<'a>(t: text 'a, sep: u8) -> text 'a * text 'a + text 'a` | the views before and after the first `sep`, or `inr t` |
| `next_line` | `next_line<'a>(t: text 'a) -> text 'a * text 'a + 1` | the first line and the rest |
| `fold_lines` | `fold_lines[S]<'a>(t: text 'a, f: !(text 'a * S => S), s: S) -> S` | each line folded into `s`, in order |
| `trim` | `trim<'a>(t: text 'a) -> text 'a` | without leading and trailing white space |
| `skip_while`, `rskip_while` | `skip_while<'a>(t: text 'a, p: !(u8 => bool)) -> text 'a` | without the leading (trailing) bytes `p` holds of |
| `prefix_len`, `suffix_len` | `prefix_len<'a>(t: text 'a, p: !(u8 => bool)) -> i32` | how many leading (trailing) bytes `p` holds of |
| `is_space` | `is_space(b: u8) -> bool` | space, tab, carriage return or newline |
| `find_str` | `find_str<'a, 'b>(t: text 'a, p: text 'b) -> i32 + 1` | the index of the first occurrence of `p` |

**UTF-8 and parsing.**

| name | signature | |
|---|---|---|
| `str_from_utf8` | `str_from_utf8<'a>(v: array_imm 'a u8) -> text 'a with Fail[i32]` | the bytes as text; raises the index of the first bad byte |
| `from_utf8` | `from_utf8(b: buf u8) -> string with Fail[i32]` | a byte buffer as a string, in place; raises as above |
| `utf8_error` | `utf8_error<'a>(t: text 'a) -> i32 + 1` | the index of the first bad byte, or `inr ()` |
| `ParseError` | `type ParseError = 1 + (u8 + 1)` | no digits, a byte that isn't a digit, or too large |
| `parse_i32` | `parse_i32<'a>(t: text 'a) -> i32 with Fail[ParseError]` | a decimal integer, with an optional `-` |
| `fold_i32s` | `fold_i32s[S]<'a>(t: text 'a, f: !(i32 * S => S), s: S) -> S` | every integer written in `t`, folded into `s` |
| `fold_i64s` | as `fold_i32s`, at `i64` | |
| `add_checked`, `mul_checked` | `add_checked(a: i32, b: i32) -> i32 with Fail[1]` | `a + b` (`a * b`); raises `()` on overflow |

**In place, and buffers of views.**

| name | signature | |
|---|---|---|
| `make_ascii_uppercase` | `make_ascii_uppercase<'a>(v: text_mut 'a) -> text_mut 'a` | `a`–`z` to `A`–`Z` |
| `make_ascii_lowercase` | `make_ascii_lowercase<'a>(v: text_mut 'a) -> text_mut 'a` | `A`–`Z` to `a`–`z` |
| `sort_views` | `sort_views<'a>(b: buf (text 'a)) -> buf (text 'a)` | a buffer of views sorted by their bytes, stably |
| `view_at` | `view_at<'a>(b: buf (text 'a), i: i32) -> buf (text 'a) * text 'a` | a copy of the view at `i` |
| `swap_views` | `swap_views<'a>(b: buf (text 'a), i: i32, j: i32) -> buf (text 'a)` | the views at `i` and `j` exchanged |

```bc
include textio

-- The number after the `=` of `key = value`, or 0 when there is no `=`.
fn value<'t>(line: text 't) -> i32 with Fail[ParseError] =
  match split_once(line, b'=') {
    inl (k, v) -> parse_i32(trim(v))
  | inr l -> 0
  }

main -> 1 =
  let mut s = box string(16);
  push_lit(&mut s, "caf");
  push_char(&mut s, 0xe9);
  push_lit(&mut s, " = ");
  push_dec(&mut s, 42);
  let bytes = len_of(&s);
  let chars = borrow imm s { t -> count_chars(t) };
  let v = borrow imm s { t -> with default(0 - 1) { value(t) } };
  let s = print_string(s);
  print_lit(": ");
  print_dec(bytes);
  print_lit(" bytes, ");
  print_dec(chars);
  print_lit(" characters, value ");
  print_dec(v);
  print_byte(b'\n')
-- output: café = 42: 10 bytes, 9 characters, value 42
```

## buf

`buf A`, a growable array, and a priority queue on one. `Vec[T]` wraps a `buf T`, and every
function here works on both. `borrow imm b { v -> … }` and `borrow mut b { v -> … }` lend the
elements as a view for [`slice`](#slice). [Buffers and strings](guide/data.md#buffers-and-strings)
teaches them.

| name | signature | |
|---|---|---|
| `box buf[A](cap)` | `buf A` | an empty buffer with room for `cap` elements (`buf_new[A](cap)`) |
| `buf_of_array` | `buf_of_array[A](a: array A) -> buf A` | an array as a full buffer |
| `array_tab` | `array_tab[A](n: i32, f: !(i32 => A)) -> array A` | an array of `f(0)`, …, `f(n - 1)` |
| `array_set` | `array_set[A](a: array A, i: i32, x: A) -> array A` | `x` in slot `i` of an array |
| `len_of` | `len_of[A](b: buf A) -> buf A * i32` | the length |
| `cap_of` | `cap_of[A](b: buf A) -> buf A * i32` | the capacity |
| `push` | `push[A](b: buf A, x: A) -> buf A * 1` | `x` at the end, growing when full |
| `pop` | `pop[A](b: buf A) -> buf A * (A + 1)` | the last element taken out |
| `take` | `take[A](b: buf A, i: i32) -> buf A * (A + 1)` | element `i` moved out, an empty element left in its place |
| `truncate` | `truncate[A](b: buf A, k: i32) -> buf A` | the first `k` kept, the rest dropped |
| `clear` | `clear[A](b: buf A) -> buf A` | every element dropped, the capacity kept |
| `reserve` | `reserve[A](b: buf A, extra: i32) -> buf A` | room for `extra` more |
| `grow` | `grow[A](b: buf A, cap: i32) -> buf A` | moved to capacity `cap` |
| `heap_push` | `heap_push[A](h: buf (i32 * A), k: i32, x: A) -> buf (i32 * A)` | `x` added with priority `k` to a min-heap |
| `heap_pop` | `heap_pop[A](h: buf (i32 * A)) -> buf (i32 * A) * ((i32 * A) + 1)` | the smallest priority and its element, taken out |
| `heap_peek` | `heap_peek[A](h: buf (i32 * A)) -> buf (i32 * A) * ((i32 * A) + 1)` | the same, left in place |

An element type needs a placeholder for the spare capacity: numbers, views, arrays, buffers and
data built from them have one; a heap cell `ref A` doesn't. A heap's elements are copied where
they lie, so its `A` is copyable (`i32`, `bool`, tuples of them).

```bc
include textio

main -> 1 =
  let h = box buf[i32 * i32](4);
  let h = heap_push(h, 5, 50);
  let h = heap_push(h, 2, 20);
  let mut h = heap_push(h, 9, 90);
  for i in 0..3 {
    let r = heap_pop(&mut h);
    match r { inl (k, x) -> print_dec(x); print_byte(b' ') | inr u -> () }
  };
  let mut b = box buf[i32](2);
  push(&mut b, 1); push(&mut b, 2); push(&mut b, 3);
  let mut b = truncate(b, 1);
  let c = cap_of(&b);
  let n = len_of(&b);
  print_dec(n); print_byte(b' '); print_dec(c);
  print_byte(b'\n')
-- output: 20 50 90 1 8
```

## slice

Functions on views: `array_imm 'a A` (shared) and `array_mut 'a A` (exclusive), lent from an
array or a buffer by a `borrow` block. A function that changes a view hands it back, and
`discard_mut` ends it. An index out of range reads the default and writes nothing. Searches and
sorts take the element comparison as an argument, and functions that copy an element need a
copyable `A`. [Arrays](guide/data.md#arrays) teaches them.

| name | signature | |
|---|---|---|
| `eq_u8`, `eq_i32` | `eq_i32(x: i32, y: i32) -> bool` | element equality, to pass to a search |
| `cmp_u8`, `cmp_i32` | `cmp_i32(x: i32, y: i32) -> i32` | element order, `-1`, `0` or `1` (`u8` unsigned) |
| `len` | `len[A]<'a>(v: array_imm 'a A) -> i32` | the length |
| `len_mut` | `len_mut[A]<'a>(v: array_mut 'a A) -> array_mut 'a A * i32` | the length of an exclusive view |
| `at` | `at[A]<'a>(v: array_imm 'a A, i: i32, d: A) -> A` | a copy of element `i`, or `d` |
| `get` | `get[A]<'a>(v: array_imm 'a A, i: i32) -> imm 'a A + 1` | element `i`, lent |
| `get_mut` | `get_mut[A]<'a>(v: array_mut 'a A, i: i32) -> mut 'a A + 1` | element `i`, lent `mut`; the rest of the view is given up |
| `read` | `read[A]<'a>(g: imm 'a A) -> A` | a copy of what a borrow points at, as `*g` |
| `peek` | `peek[A]<'a>(v: array_mut 'a A, i: i32, d: A) -> array_mut 'a A * A` | a copy of element `i` through an exclusive view |
| `set` | `set[A]<'a>(v: array_mut 'a A, i: i32, x: A) -> array_mut 'a A` | `x` in slot `i` |
| `replace` | `replace[A]<'a>(v: array_mut 'a A, i: i32, x: A) -> array_mut 'a A * (A + A)` | `x` in slot `i`; `inl` the old element, or `inr x` |
| `swap_at` | `swap_at[A]<'a>(v: array_mut 'a A, i: i32, j: i32) -> array_mut 'a A` | slots `i` and `j` exchanged |
| `discard_mut` | `discard_mut[A]<'a>(v: array_mut 'a A) -> 1` | the view given up |
| `empty`, `empty_mut` | `empty[A]<'a>() -> array_imm 'a A` | an empty view |
| `split_at` | `split_at[A]<'a>(v: array_imm 'a A, i: i32) -> array_imm 'a A * array_imm 'a A + array_imm 'a A` | the first `i` and the rest, or `inr v` past the end |
| `split_at_mut` | the same over `array_mut` | |
| `split_first`, `split_last` | `split_first[A]<'a>(v: array_imm 'a A) -> imm 'a A * array_imm 'a A + 1` | the first (last) element and the rest |
| `split_first_mut`, `split_last_mut` | the same over `array_mut` | |
| `reverse` | `reverse[A]<'a>(v: array_mut 'a A) -> array_mut 'a A` | reversed in place |
| `fill` | `fill[A]<'a>(v: array_mut 'a A, x: A) -> array_mut 'a A` | `x` in every slot |
| `copy_from` | `copy_from[A]<'a, 'b>(dst: array_mut 'a A, src: array_imm 'b A) -> array_mut 'a A` | `src` copied in, as far as the shorter |
| `sort` | `sort[A]<'a>(v: array_mut 'a A, c: !(A * A => i32), d: A) -> array_mut 'a A` | sorted by `c`, stably; `d` is any element |
| `find` | `find[A]<'a>(v: array_imm 'a A, x: A, eq: !(A * A => bool)) -> i32 + 1` | the index of the first element equal to `x` |
| `contains` | `contains[A]<'a>(v: array_imm 'a A, x: A, eq: !(A * A => bool)) -> bool` | whether an element equals `x` |
| `binary_search` | `binary_search[A]<'a>(v: array_imm 'a A, x: A, c: !(A * A => i32)) -> i32 + i32` | in a sorted view, `inl` an index of `x`, or `inr` where it would go |
| `cmp` | `cmp[A]<'a, 'b>(v: array_imm 'a A, w: array_imm 'b A, c: !(A * A => i32)) -> i32` | lexicographic order |
| `eq` | `eq[A]<'a, 'b>(v: array_imm 'a A, w: array_imm 'b A, e: !(A * A => bool)) -> bool` | the same elements |
| `starts_with`, `ends_with` | `starts_with[A]<'a, 'b>(v: array_imm 'a A, p: array_imm 'b A, e: !(A * A => bool)) -> bool` | |

```bc
include textio
include slice

fn scramble(i: i32) -> i32 = (i * 7) % 10

main -> 1 =
  let mut a = array_new[i32](6, scramble);
  borrow mut a { v -> let v = sort(v, cmp_i32, 0); let v = reverse(v); discard_mut(v) };
  let at5 = borrow imm a { v -> find(v, 5, eq_i32) };
  let has3 = borrow imm a { v -> contains(v, 3, eq_i32) };
  for x in &a { print_dec(*x); print_byte(b' ') };
  match at5 { inl i -> print_lit("5 at "); print_dec(i) | inr u -> print_lit("no 5") };
  if has3 { print_lit(", has 3") } else { print_lit(", no 3") };
  print_byte(b'\n')
-- output: 8 7 5 4 1 0 5 at 2, no 3
```

## key

The families a map uses: one equality, hash and order per type. They have cases at the integers,
`1`, tuples, sums (so `bool`), arrays, views and buffers (so `string` and `text`), compared
structurally, and a program adds cases at its own types with `poly`. A float has none.
[Equality, hashing and order](guide/data.md#equality-hashing-and-order) teaches them.

| name | signature | |
|---|---|---|
| `equal` | `poly equal[T]<'a, 'b>(x: view 'a T, y: view 'b T) -> bool` | equality |
| `hash` | `poly hash[T]<'a>(x: view 'a T) -> i64` | a deterministic hash, the same on every run |
| `order` | `poly order[T]<'a, 'b>(x: view 'a T, y: view 'b T) -> i32` | `-1`, `0` or `1` |

A `view 'a T` of an integer, a tuple of them or a view is the value itself, so `equal(x, y)`
takes the values.

```bc
include textio
include key

main -> 1 =
  if equal((1, true), (1, true)) { print_lit("equal ") } else { print_lit("different ") };
  print_dec(order((1, 5), (2, 0)));
  print_byte(b' ');
  if hash(7) == hash(7) { print_lit("same hash") } else { print_lit("?") };
  print_byte(b'\n')
-- output: equal -1 same hash
```

## map

A hash map and a set, keyed by [`key`](#key)'s families. A map is a value: an operation takes it
with `&m` or `&mut m`. `borrow imm m { 'x, r -> … }` lends it as `r : MapRef[K, V]<'k, 'x>`, to
read values in place. [Maps and sets](guide/data.md#maps-and-sets) teaches them.

| name | signature | |
|---|---|---|
| `Map[K, V]`, `Set[K]` | types | a set is a map to `1` |
| `map_new` | `map_new[K, V](cap: i32) -> Map[K, V]` | an empty map with room for `cap` entries |
| `map_insert` | `map_insert[K, V](m: Map[K, V], k: K, v: V) -> Map[K, V] * (V + 1)` | `v` at `k`; the value displaced |
| `map_lookup` | `map_lookup[K, V](m: Map[K, V], k: K) -> Map[K, V] * (V + 1)` | a copy of the value at `k` (`V` copyable) |
| `map_contains` | `map_contains[K, V](m: Map[K, V], k: K) -> Map[K, V] * bool` | whether `k` has a value |
| `map_remove` | `map_remove[K, V](m: Map[K, V], k: K) -> Map[K, V] * (V + 1)` | the entry at `k` taken out |
| `map_len` | `map_len[K, V](m: Map[K, V]) -> Map[K, V] * i32` | the number of entries |
| `map_get` | `map_get[K, V]<'k, 'x>(r: MapRef[K, V]<'k, 'x>, k: K) -> imm 'x V + 1` | the value at `k`, lent |
| `map_size` | `map_size[K, V]<'k, 'x>(r: MapRef[K, V]<'k, 'x>) -> i32` | the number of entries of a lent map |
| `map_iter` | `map_iter(r)` | a `for` source: each key with a view of its value, `K * imm 'x V` |
| `set_new` | `set_new[K](cap: i32) -> Set[K]` | an empty set |
| `set_insert` | `set_insert[K](s: Set[K], k: K) -> Set[K] * bool` | `k` added; whether it was new |
| `set_contains` | `set_contains[K](s: Set[K], k: K) -> Set[K] * bool` | |
| `set_remove` | `set_remove[K](s: Set[K], k: K) -> Set[K] * bool` | `k` taken out; whether it was there |
| `set_len` | `set_len[K](s: Set[K]) -> Set[K] * i32` | |

The values need a placeholder, as a buffer's elements do.

```bc
include textio
include map

main -> 1 =
  let mut seen = set_new[i32](8);
  let mut dups = 0;
  for x in 0..20 {
    let fresh = set_insert(&mut seen, (x * x) % 7);
    if not(fresh) { dups = dups + 1 }
  };
  let mut m = map_new[i32, i32](8);
  let old = map_insert(&mut m, 1, 10);
  let old = map_insert(&mut m, 1, 11);
  let gone = map_remove(&mut m, 2);
  let n = set_len(&seen);
  print_dec(n);
  print_byte(b' ');
  print_dec(dups);
  print_byte(b' ');
  match old { Some(v) -> print_dec(v) | None -> print_lit("none") };
  print_byte(b' ');
  match gone { Some(v) -> print_dec(v) | None -> print_lit("none") };
  print_byte(b'\n')
-- output: 4 16 10 none
```

## list

A generic owned list. Its functions are recursive, so a call needs a [`rec`](#rec) handler around
it. [Recursion](guide/data.md#recursion) introduces it.

| name | signature | |
|---|---|---|
| `List[A]` | type | a list of `A`s |
| `nil` | `nil[A]() -> List[A]` | the empty list |
| `cons` | `cons[A](x: A, xs: List[A]) -> List[A]` | `x` in front of `xs` |
| `map` | `map[A, B](xs: List[A], f: !(A => B)) -> List[B]` | each `x` as `f(x)` |
| `filter` | `filter[A](xs: List[A], p: !(A => bool)) -> List[A]` | the elements `p` holds of (`A` copyable) |
| `fold` | `fold[A, B](xs: List[A], z: B, f: !(B * A => B)) -> B` | combined from the left, from `z` |

```bc
include textio
include list

main -> 1 =
  let xs = cons(1, cons(2, cons(3, cons(4, nil()))));
  let sum = with on_exhausted(!{ u -> 0 - 1 }) {
    fold(filter(map(xs, !{ x -> x * x }), !{ x -> x % 2 == 0 }), 0, !{ (a, x) -> a + x })
  };
  print_dec(sum);
  print_byte(b'\n')
-- output: 20
```

`list`'s `map` and `filter` share their names with those of [`adapters`](#adapters) and
[`iters`](#iters), so a program that calls them includes only one of these modules.

## yield

The effect a generator performs. [Generators](guide/iteration.md#generators) teaches it.

| name | signature | |
|---|---|---|
| `Yield[T]` | `effect Yield[T] { ctl yield(x: T) }` | |
| `yield(x)` | `x: T`, answers `()` | `x` to the `for` running the generator |

## adapters

Generic generators over a source computation. A source `(1 => K with Yield[A])` is a
computation parameter that yields `A`s and returns `K`; a call of a generator, or of an adapter, at
a source is that source, so a pipeline runs as nested direct calls. `take` and `take_until` stop
their source early, which hands nothing back: their source returns `1`. `zip` steps two sources by
hand, so it takes stored generators `U (pull A K R)`
([Stored generators](guide/iteration.md#stored-generators)). Chain them with `|>`
([Pipelines](guide/iteration.md#pipelines)).

| name | signature | yields |
|---|---|---|
| `map` | `map[A, B, K](it: (1 => K with Yield[A]), f: !(A => B)) -> K with Yield[B]` | `f(x)` for each `x` |
| `filter` | `filter[A, K](it: (1 => K with Yield[A]), p: !(A => bool)) -> K with Yield[A]` | the elements `p` holds of (`A` copyable) |
| `take` | `take[A](it: (1 => 1 with Yield[A]), n: i32) -> 1 with Yield[A]` | the first `n` |
| `skip` | `skip[A, K](it: (1 => K with Yield[A]), n: i32) -> K with Yield[A]` | all after the first `n` |
| `take_until` | `take_until[A](it: (1 => 1 with Yield[A]), p: !(A => bool)) -> 1 with Yield[A]` | the elements before the first `p` holds of |
| `enumerate` | `enumerate[A, K](it: (1 => K with Yield[A])) -> K with Yield[i32 * A]` | each element with its position |
| `chain` | `chain[A, K](a: (1 => K with Yield[A]), b: (1 => 1 with Yield[A])) -> K with Yield[A]` | `a`'s elements, then `b`'s |
| `flat_map` | `flat_map[A, B, K](it: (1 => K with Yield[A]), f: !(A => U (pull B 1 1))) -> K with Yield[B]` | the elements of each `f(x)` |
| `scan` | `scan[A, S, K](it: (1 => K with Yield[A]), s: S, f: !(S * A => S)) -> K with Yield[S]` | the running states `f(s, x)` |
| `zip` | `zip[A, K, B](a: U (pull A K K), b: U (pull B 1 1)) -> K with Yield[A * B]` | pairs, until either ends |
| `chunks` | `chunks[A, K](it: (1 => K with Yield[A]), n: i32) -> K with Yield[List[A]]` | lists of `n`, each last first |
| `batch` | `batch[A, S, K](it: (1 => K with Yield[A]), s0: S, add: !(S * A => S * bool)) -> K with Yield[S]` | states filled by `add` until it says full |
| `lines` | `lines[K](it: (1 => K with Yield[u8])) -> K with Yield[List[u8]]` | a byte source's lines, each last first |

```bc
include textio
include adapters

fn range(lo: i32, hi: i32) -> 1 with Yield[i32] =
  let mut i = lo;
  while i < hi { yield(i); i = i + 1 };
  ()

main -> 1 =
  let mut last = 0;
  for s in range(1, 100) |> skip(2) |> scan(0, !{ (acc, x) -> acc + x }) |> take_until(!{ s -> s > 40 }) {
    last = s
  };
  let mut pairs = 0;
  for p in zip(range(0, 10), range(100, 103)) { let (a, b) = p; pairs = pairs + a * b };
  print_dec(last);
  print_byte(b' ');
  print_dec(pairs);
  print_byte(b'\n')
-- output: 33 305
```

## iters

Adapters over data, a view or a count `a..b`. A `for` over a chain of them runs at most once per
element, so it stays total. [`for` over data](guide/iteration.md#for-over-data) covers the loop
they feed.

| name | takes | yields |
|---|---|---|
| `elems(v)` | `v: array_imm 'a A` | each element, lent: `imm 'a A` |
| `elems_mut(v)` | `v: array_mut 'a A` | each element, lent `mut`: `mut 'a A` |
| `copied(it)` | an iterator of `imm 'a A` | each element copied: `A` |
| `map(it, f)` | `f: !(A => B)` | `f(x)` |
| `filter(it, p)` | `p: !(A => bool)` | the elements `p` holds of |
| `take(it, k)` | `k: i32` | the first `k` |
| `enumerate(it)` | | `i32 * A`: each with its position |
| `zip(a, b)` | two iterators | pairs, until either ends |

```bc
include textio
include iters

fn big(x: i32) -> bool = x > 2

total fn weighted<'a>(v: array_imm 'a i32) -> i32 =
  let mut s = 0;
  for p in zip(filter(copied(elems(v)), big), 100..200) { let (x, y) = p; s = s + x * y };
  s

main -> 1 =
  let a = array_new[i32](5, !{ i -> i });
  let w = borrow imm a { v -> weighted(v) };
  print_dec(w);
  print_byte(b'\n')
-- output: 704
```

## async

Tasks and a round-robin scheduler, written in the language. [Async tasks](guide/async.md) teaches
them.

| name | signature | |
|---|---|---|
| `Async` | `effect Async { ctl await(); ctl log(x: i32) }` | let other tasks run; record an entry |
| `spawn` | `with spawn { e }`, a `Task[A]` | `e` run to its first `await` |
| `resume` | `resume[A](t: Task[A]) -> A + Task[A]` | run to the next `await`: `inl` the value, or `inr` the rest |
| `cancel` | `cancel[A](t: Task[A]) -> 1` | a task abandoned, what it owns freed |
| `queue` | `queue[A]() -> Queue[A]` | an empty queue |
| `push` | `push[A](q: Queue[A], t: Task[A]) -> Queue[A]` | a task queued |
| `run_until_empty` | `run_until_empty[A](q: Queue[A]) -> List[A]` | the tasks' values, in the order queued |
| `spawn_logged` | `with spawn_logged { e }`, a `Stopped[A]` | a task whose `log` entries are kept |
| `lresume`, `lcancel` | `lresume[A](t: LTask[A]) -> Stopped[A]` | `resume` and `cancel` for a logged task |
| `lqueue` | `lqueue[A]() -> LQueue[A] * List[i32]` | an empty logged queue |
| `lpush` | `lpush[A](q: LQueue[A] * List[i32], s: Stopped[A]) -> LQueue[A] * List[i32]` | a logged task queued |
| `run_logged` | `run_logged[A](q: LQueue[A] * List[i32]) -> List[A] * List[i32]` | the values, and every entry logged, in order |
| `spawn_in` | `with spawn_in { e }`, a `TaskIn[A]<'d>` | a task that may hold a borrow from the scope it was spawned in |
| `resume_in`, `cancel_in` | `resume_in[A]<'d>(t: TaskIn[A]<'d>) -> A + TaskIn[A]<'d>` | |
| `queue_in`, `push_in` | `push_in[A]<'d>(q: QueueIn[A]<'d>, t: TaskIn[A]<'d>) -> QueueIn[A]<'d>` | |
| `run_in` | `run_in[A]<'d>(q: QueueIn[A]<'d>, rounds: i32) -> List[A] with Exhausted` | at most `rounds` rounds; a task still pending makes it perform `exhausted()` |

`async`'s `push` shares its name with [`buf`](#buf)'s, so a program that queues tasks doesn't
push to a buffer by that name.

## float

The float operations by name, conversions, IEEE 754's total order, and printing and parsing in
the shortest decimal that reads back as the same float. Each name below exists at `f64` and, with
`f32` in place of `f64`, at `f32`. [Floats](guide/basics.md#floats) introduces them.

| name | signature | |
|---|---|---|
| `sqrt_f64`, `abs_f64`, `neg_f64`, `floor_f64`, `ceil_f64`, `trunc_f64` | `(x: f64) -> f64` | |
| `round_f64` | `(x: f64) -> f64` | to the nearest integer, ties to even |
| `min_f64`, `max_f64`, `copysign_f64` | `(x: f64, y: f64) -> f64` | |
| `is_nan_f64` | `(x: f64) -> bool` | |
| `f64_of_i32`, `f64_of_i64` | `(n: i32) -> f64` | correctly rounded |
| `i32_of_f64`, `i64_of_f64` | `(x: f64) -> i32 + 1` | truncated; `inr ()` for a NaN or out of range |
| `i32_of_f64_sat`, `i64_of_f64_sat` | `(x: f64) -> i32` | truncated; a NaN is `0`, out of range the nearest end |
| `f64_of_f32`, `f32_of_f64` | `(x: f32) -> f64` | |
| `bits_f64`, `of_bits_f64` | `(x: f64) -> i64` | the bit pattern, and back |
| `total_cmp_f64` | `(x: f64, y: f64) -> i32` | IEEE 754's `totalOrder`: `-1`, `0` or `1` |
| `ord_f64`, `of_ord_f64` | `(x: f64) -> i64` | an integer key in `totalOrder`, usable in a map, and back |
| `push_f64` | `push_f64(s: string, x: f64) -> string * 1` | `x` appended, called with `&mut s` |
| `print_f64` | `print_f64(x: f64) -> 1` | `x` to standard output |
| `parse_f64` | `parse_f64<'a>(t: text 'a) -> f64 with Fail[FloatParseError]` | the float nearest the decimal `t` |
| `FloatParseError` | `type FloatParseError = 1 + u8` | the text ended early, or the byte that can't stand there |

```bc
include float

main -> 1 =
  let x = borrow imm "2.5e-3" { t -> with default(0.0) { parse_f64(t) } };
  let mut s = box string(32);
  push_f64(&mut s, x * 4.0);
  push_lit(&mut s, " ");
  push_f32(&mut s, f32_of_f64(0.1));
  let s = print_string(s);
  print_byte(b' ');
  print_dec(total_cmp_f64(neg_f64(0.0), 0.0));
  print_byte(b' ');
  match i32_of_f64(1.0e12) { inl n -> print_dec(n) | inr u -> print_lit("out of range") };
  print_byte(b'\n')
-- output: 0.01 0.1 -1 out of range
```

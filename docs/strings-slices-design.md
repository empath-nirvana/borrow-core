# Strings and slices, end to end — design

Status: a design. Stages S1 to S4 are built (below, *Stage status*); the rest is proposed. It
proposes spec entries, and names the theorems each needs.

**Stage status.**

| stage | status | where |
|---|---|---|
| §9 length bound | built: `⌜c < 2³¹⌝` in the `[L]` clause; `FamLenBound` derived | SPEC §9, `Core/Relation.lean`, `arrLen_of_bound` |
| S1 K0 | built, **as a machine step** `count`, not a Z-combinator loop: a loop that counts with the host's `add`/`lt_u` is total only at hosts whose operations count, and every theorem holds at every host (SPEC §16, *Why a step*). The constant takes a start index: `count_fold (f, (n, (i, s)))` | SPEC §16, `Core/CountFold.lean` (`countFold_compatX`), `corpus/count-fold.bc` |
| S1 K1 | built: `u8`, `b'c'`, `wrap8`/`extend8_u`, surface operators at `u8` through `i32`, `to_i32`/`to_u8` | SPEC §8, `corpus/bytes-upper.bc` |
| S1 backend | built: byte slots for `u8`, `tab 0` allocates nothing | `Backend/README.md`, Representation |
| S1 `read_byte`/`write_byte` at `u8` | not done: it changes every I/O program's types; left to S5 | SPEC §8 Open |
| S1 total `for` | built with S4: `for i in range(n)` is `count_fold` | SPEC §16, `corpus/for-finite.bc` |
| S2 K2 | built at `Mut` and `Imm`, with the side conditions of `experiments/PositiveArrays`; `borrow mut a { 'x, v -> … }` on an array | SPEC §9, `Core/Slices.lean`, `corpus/slice-mut.bc`, `corpus/slice-imm.bc` |
| S2 K4 | built with S2: `slice_get_mut`, `slice_len_mut` (a `mut` family is unusable without them) | `Core/Slices.lean` |
| S3 K3 | built, **as a machine step** `split`, not a term over the host's `le_u`/`sub` (as K0); `slice_split_imm`/`_mut`, and `slice_empty_imm`/`_mut` typed `[L]` (not `![L]`) | SPEC §9, `Core/SliceOps.lean` (`famSplit_compatX`, `famEmpty_compatX`), `corpus/slice-split.bc` |
| S3 K5 | built: `slice_replace_mut` (Mut Anti-Frame on the leaf), `slice_swap_mut` (two nested Anti-Frames, `sepRange_pick2N`; one leaf at `i = j`) | `Core/SliceOps.lean` (`sliceReplaceM_compatX`, `sliceSwapM_compatX`) |
| S3 destructor | built: `array_mut @a A` has one, derived from `slice_get_mut` and `forget` (no kernel change) | SPEC §9, §12, `Core/Dtor.lean` |
| S3 backend | built: `split` is a compare and pointer and length arithmetic, no allocation; the empty family's base is `0` | `Backend/Flat/Lower.lean`, `Backend/Clos/` |
| S3 library | built: `lib/slice.bc`, generic in the element type, comparisons as arguments; `sort` is an insertion sort | SPEC §9, `docs/decisions.md` 44 |
| S4 total `for` | built: a `for` over a bounded source (`range`, `iter_imm`/`iter_mut`, the adapters that observe their source once per observation over one, `take` over a bounded or never-skipping source) is `count_fold` with the source's bound, and its function stays total; bounded by the library's names, not by type | SPEC §16 *The total `for`*, `docs/decisions.md` 46, `corpus/slice-total.bc`, `corpus/take-bytes.bc` |
| S4 lend row | built: `&mut a`/`&a` of an owned array at a view parameter is `slice_borrow_*` around the call (a view handed back is dropped); in a total `for`'s source, a borrow block around the loop | SPEC §9, `corpus/sugar/lend-array.bc`, `corpus/iter-mut.bc` |
| S4 iterators | built: `iter_imm`/`iter_mut` are generators over the rest of the view, `len + 1` observations; they compose with the adapters (an instance takes the element's lifetime as a parameter) | SPEC §9, §15, `corpus/slice-pipeline.bc` (1 allocation, the array; 0 dispatched calls) |
| P10 | in direct style but for `read_all` (a 64-byte buffer filled from the input): `upper` is a `total fn` over `for c in iter_mut(v)` | `corpus/split-at-mut.bc` |
| P7 (numbers) | an `array i32` sorted in place and binary-searched | `corpus/sort-numbers.bc` |
| search, reverse | `find`/`contains`/`starts_with`/`ends_with`/`eq`/`cmp` over bytes; `rev` in place | `corpus/find-bytes.bc`, `corpus/reverse-bytes.bc` |
| P12 | as written: `for x in iter_mut(&mut a) { modify x { … } }` | `corpus/iter-mut.bc`, `corpus/iter-mut-slice.bc` (a borrow block), `corpus/iter-mut-count.bc` (indices) |
| array analogue of `print-borrowed-list` | built: a `total fn` printing each element of `&a` through `iter_imm` | `corpus/print-borrowed-array.bc` |
| S4 left | `bytes`, `chars`, `lines` over views (S5, with text); a total `for` whose body breaks; a bound read off a type; a lend of an array at a function with two lifetime parameters | SPEC §16 Open, §9 Open |
| S3 left | an `imm` reborrow of a `mut` family (K2′: `peek` and `sort` take a filler meanwhile); lifetime inference for two lifetimes (`copy_from`, `eq`, `cmp` take them written); static bounds-check elimination | SPEC §9 Open |
| `div_fuel` over K0 | built: `io-fuel` from 3746 allocations and 174 dispatched calls to 1 and 0 | `lib/div.bc` |

The method follows the user's direction. The programs come first (§1), then the types they need
(§2, §3), then the API (§4), and then the memory model that API forces (§5). Arrays and buffers
are not designed in the abstract. Each piece is there because a program in §1 needs it.

## 0. Summary

**Types.** Five concepts, each on its own axis. None is a special case of another.

| concept | core | axis |
|---|---|---|
| `u8` | `VTy.int .w8` (a new width) | element width: a byte is one byte of memory |
| `array A`, `slice 'a A`, `slice mut 'a A` | `[Ref A]`, `[Imm 'a A]`, `[Mut 'a A]`: the existing family former `[L]` | a range of places, at a permission (owned, shared, exclusive) |
| `buf A` | stage A: `array A ⊗ I32`, library; stage F: a former | growth: capacity beyond the length |
| `string`, `str 'a`, `str mut 'a` | `buf u8`, `slice 'a u8`, `slice mut 'a u8`, with the UTF-8 invariant | encoding: a refinement of byte storage, kept by the text library |
| `lit` | a persistent value (`I32 ⊗ !(I32 ⇒ U8)`) | static: program data that no one owns |

Rust's `Box<str>`, `Cow<str>`, `Rc<str>`, `OsString`/`OsStr` and `CString`/`CStr` get no type of
their own. Each is covered by a combination, a plain sum, or a conversion at the FFI boundary
(§2.3). The one real exception is the NUL-terminated representation C needs. It exists, but it
lives only at extern boundaries.

**Kernel.** Six additions. Each is a constant with an ordinary term and one compatibility
lemma. Only K1 also adds a case to `Width`. None adds a `VTy` former or a machine step.

| | constant | proof reuses | risk |
|---|---|---|---|
| K0 | `count_fold`: a counted loop over `I32`, total | the Z-combinator lemmas of the folds; induction on the count | low |
| K1 | `u8`: literal, `wrap8`, `extend8_u` | every width-generic lemma; one new `Width` case | low |
| K2 | `slice_borrow` at `Mut` and at `Imm`: an owned array lent as a family of leaf borrows, **with no cell** | `wpTS_M_frameX`/`wpTS_I_frameX` applied `n` times; 6.60 to rebox | **medium** (Imm: medium-plus) |
| K3 | `slice_split` at a run-time index, and `slice_empty` | `sepRange_split` (**spiked**: `vP_fam_split`) | low |
| K4 | `slice_get`, `slice_len` at `Mut` | `arrGet_compatX` with `mut` leaves | low |
| K5 | `slice_replace`, `slice_swap` at `Mut` | `sepRange_pick`/`sepRange_pick2`, and the `withswap` lemma (6.66) | low-medium |

Everything else is library code: iterators, UTF-8, parsing, formatting, `buf`, and literals.

**The questions this design had to answer:**

- **Run-time `split_at` works.** A borrowed family `[M 'c A]` is `⊛_{i<n} leaf(ℓ+i)`. Splitting
  it at a run-time `i` is splitting a separating conjunction (`sepRange_split`). It needs no
  frame, no lifetime and no model change, and the spike proves it at the relation. The hard part
  is not the split. It is *creating* a `mut` family at one lifetime (K2), which is `n` nested
  Mut Frames. That is a semantic induction on `n`, with each step the existing single-leaf lemma.
- **Growth needs no new kernel for text.** A byte buffer is an array plus a length, with the
  unused slots holding `0` (stage A). Reallocation is `tab`, element moves and `drop`, each
  already sound under every allocator (§13). No borrow can span a growth. That follows from
  linearity: a buffer's views exist only inside a lend of it, where the buffer itself is not in
  scope (§5.4). The cost is a zero-fill on each growth.
- **Owned families are not split.** Splitting an *owned* family is sound in the model, but it would
  break the lowering: a block is freed once, and byte ranges are not word-aligned.
  Uninitialised capacity for element types with no cheap filler waits
  for a `buf` former (stage F).
- **Contiguity is already solved for arrays.** `tab` places `n` cells at the allocator's block
  (`Alloc.fresh`, `wpTS_tab`) on every run. #77 is about records (`allocS`), not arrays.

**Staging** (§8): K0/K1 → K2 → K3–K5 → iterators and total `for` → the text library → nominal
text types → a zero-cost growth former. Every stage lands with running programs from §1.

## 1. Target programs

The spellings are hypotheses. They follow draft 0's surface and typed elaboration's
conventions, and every new name is listed in §4. Each program states the features it
*forces*: the ones it cannot be written without, or cannot be written at zero cost without.
Error results are sums, `A + E`. `-- #18` marks where an error effect would replace the
threading.

Several spellings recur:

- `box array(n, f)`, `box buf(cap)` and `box string(cap)` allocate. `box` appears exactly where
  heap memory is taken.
- `&x` lends `x` to one call and gets it back afterwards. This is typed elaboration §5.1
  unchanged, plus one row (§4.3): a `string`, `buf` or `array` value lent at a `str`/`slice`
  parameter lends its initialised range, with no cell.
- `borrow x { v -> … }` holds such a lend across a block.
- `&mut x` at a parameter of `x`'s own type is move-and-rebind (§5.1's last owned row). A
  function that may grow a buffer takes it by value and hands it back first, so
  `push_str(&mut s, t)` reads like Rust and costs no cell.

### P1 `fields` — read lines, split fields, no copies

Print the second comma-separated field of every input line.

```
fn nth_field<'a>(line: slice 'a u8, sep: u8, k: i32) -> slice 'a u8 + 1 =
  let mut rest = line;
  let mut found = inr ();
  for i in range(k + 1) {
    match split_once(rest, sep) {
      inl (f, r) -> if i == k { found = inl f }; rest = r
    | inr r      -> if i == k { found = inl r }; rest = empty()
    }
  };
  found

main -> i32 =
  let mut line = box buf[u8](64);
  let mut n = 0;
  for b in bytes(&mut stdin) {
    if b == b'\n' {
      borrow line { v ->
        match nth_field(v, b',', 1) { inl f -> write_all(&mut stdout, f); putb(&mut stdout, b'\n')
                                    | inr _ -> () } };
      line = clear(line);
      n = n + 1
    } else { push(&mut line, b) }
  };
  n
```

Forces:

- a growable byte buffer, reused across lines (`clear` keeps the capacity);
- `u8`;
- a borrowed view of the initialised prefix, lent per step inside the input loop;
- a split at a run-time index, yielding sub-views at the *same* lifetime (`split_once` is
  `find_byte` then `split_at`);
- a bulk write of a view (`write_all`);
- a total counted loop (`range`, K0);
- a borrow block that threads the capabilities it uses, as `for` threads variables (§4.3).

The line is bytes here, because a comma split is byte-level. P5 does the text version.

### P2 `parse-int` — integers from text, checked

```
data ParseErr = Empty | BadDigit(i32) | Overflow

fn digit(n: i32, d: u8) -> i32 + ParseErr =              -- #18: `raise` instead of the sum
  if d < b'0' || b'9' < d { inr BadDigit(i32(d)) }
  else { match mul_checked(n, 10) {
           inl m -> match add_checked(m, i32(d) - 48) { inl r -> inl r | inr _ -> inr Overflow }
         | inr _ -> inr Overflow } }

fn parse_i32<'a>(t: str 'a) -> i32 + ParseErr =
  let (neg, digits) = match split_first(as_bytes(&t)) {     -- `&t`: a copy; `t` is used below
      inl (c, r) -> if *c == b'-' { (true, r) } else { (false, as_bytes(t)) }
    | inr _ -> (false, empty()) };
  if len(&digits) == 0 { inr Empty } else {
    let mut acc = inl 0;
    for d in bytes(digits) { acc = match acc { inl n -> digit(n, d) | inr e -> inr e } };
    match acc { inl n -> inl (if neg { 0 - n } else { n }) | inr e -> inr e }
  }
```

Forces:

- byte iteration over a text view (`bytes`) that is total, because it is bounded by the view's
  length;
- `u8` compared and widened (`i32(d)`);
- checked arithmetic, as library code over the host operations (§8 Open);
- an error sum, and the place where the error effect goes;
- `data` with a payload and without `box`: a non-recursive variant is a value, not a heap block.

### P3 `trim-find-replace` — sub-views and building

```
fn trim<'a>(t: str 'a) -> str 'a =
  let s = skip_while(t, is_space);           -- a sub-view: pointer + length, no copy
  rskip_while(s, is_space)

fn replace_all<'a, 'b>(t: str 'a, from: str 'b, to: str 'b) -> string =
  let mut out = box string(len(&t));
  let n = len(&from);
  let mut rest = t;
  for _ in range(len(&rest) + 1) {           -- total: each step ends or consumes a match
    match find(&rest, &from) {
      inl i -> match split_at_str(rest, i) {                  -- `find` returns a boundary
                 inl (pre, post) -> push_str(&mut out, pre); push_str(&mut out, &to);
                                    rest = skip_str(post, n)
               | inr r -> rest = r }                           -- not reached after `find`
    | inr _ -> push_str(&mut out, &rest); rest = empty_str() } };
  out
```

Forces:

- sub-views at run-time indices (`split_at`) that stay at the input's lifetime;
- comparison of sub-views (`find` compares windows);
- appending views to an owned buffer (`push_str`, which may grow);
- a total loop whose bound is a length;
- `&v` on a view is a copy of two words, and says that the caller keeps it.

`split_at_str` checks that the index is a character boundary and returns a sum. Since `find`
returns boundaries, the error branch is unreachable here, but it is typed. `skip_str(t, k)`
drops the first `k` bytes when that is a boundary. If `from` is empty, the bound ends the loop.

### P4 `format` — build a string from literals and numbers

```
fn point(x: i32, y: i32) -> string =
  let mut s = box string(16);
  push_lit(&mut s, "x="); push_dec(&mut s, x);
  push_lit(&mut s, ", y="); push_dec(&mut s, y);
  push_char(&mut s, '\n');
  s

main -> i32 = let s = point(12, -7); write_str(&mut stdout, &s); len(&s)
```

Forces:

- literals as data that no one owns (`"x="`);
- formatting an integer *into* a buffer (`push_dec`; today `put_dec` writes to an output);
- encoding a character as UTF-8 (`push_char`);
- `&s` lending a string to a text parameter;
- the implicit destructor freeing `s` at the end.

### P5 `utf8-count` — chars vs bytes, with validation

For each input line, print its byte count and its character count. Reject invalid UTF-8 with
the line number.

```
main -> i32 =
  let mut line = box buf[u8](64);
  let mut no = 1;
  for b in bytes(&mut stdin) {
    if b == b'\n' {
      borrow line { v ->
        match str_from_utf8(v) {                         -- checked, O(n), no copy
          inl t -> put_dec(&mut stdout, len(&t)); putb(&mut stdout, b' ');
                   put_dec(&mut stdout, count(chars(t))); putb(&mut stdout, b'\n')
        | inr e -> write_lit(&mut stderr, "invalid UTF-8 on line "); put_dec(&mut stderr, no);
                   putb(&mut stderr, b'\n') } };
      line = clear(line); no = no + 1
    } else { push(&mut line, b) }
  };
  no
```

Forces:

- validated construction of a text view from a byte view;
- a character iterator (`chars`, decoding UTF-8) beside the byte iterator, both total;
- text and bytes as distinct types, so that `chars` of unvalidated bytes cannot be written.

### P6 `key-value` — views stored in a buffer, one borrow of the whole input

Read `key=value` lines. Print the value of every key named `name`.

```
main -> i32 =
  let input = read_all(&mut stdin);                           -- div: runs until EOF
  match from_utf8(input) {                                    -- checked, in place: buf u8 -> string
    inl text ->
      borrow text { t ->                                      -- one borrow, after the loop (total)
        let mut pairs = box buf[str 't * str 't](8);          -- a buffer of views
        for l in lines(t) {
          match split_once_str(l, '=') { inl (k, v) -> push(&mut pairs, (trim(k), trim(v))) | inr _ -> () } };
        borrow pairs { ps ->
          for p in iter(ps) { let (k, v) = *p;
                              if eq_lit(&k, "name") { write_str(&mut stdout, v); putb(&mut stdout, b'\n') } } };
        len_of(&pairs) }
  | inr (bytes, e) -> free(bytes); 0 }
```

Forces:

- a buffer whose elements are views, `buf (str 't * str 't)`. Its element type holds a lifetime,
  so the buffer lives inside the borrow of `text`;
- a filler for unused slots of a non-integer element type (the empty view, `slice_empty`);
- the input read whole *before* the borrow, because a borrow block's body cannot loop
  (`pending/borrow-across-loop.bc`). This is the idiom that design question forces;
- `lines(t)` over a view, which is total. It is not a `lines()` over the input stream: an
  observation that reads an unbounded line would loop (SPEC §7 Open, "Other positions of `X`");
- reading a copyable element through an `imm` view (`*p`).

### P7 `sort-lines` — compare and sort views in place

```
fn sort<'a, 'b>(v: slice mut 'b (str 'a)) -> () =          -- insertion sort, total
  let n = len_mut(&mut v);                                  -- a `mut` view is handed back
  for i in range(n) { for j in range_down(i) {
    let a = peek(&mut v, j); let b = peek(&mut v, j + 1);
    if cmp(a, b) == Greater { swap(&mut v, j, j + 1) } } }

main -> i32 =
  let input = read_all(&mut stdin);
  match from_utf8(input) {
    inl text -> borrow text { t ->
      let mut ls = box buf[str 't](16);
      for l in lines(t) { push(&mut ls, l) };
      borrow mut ls { v -> sort(v) };
      borrow ls { v -> for l in iter(v) { write_str(&mut stdout, *l); putb(&mut stdout, b'\n') } };
      len_of(&ls) }
  | inr (b, _) -> free(b); 0 }
```

Forces:

- lexicographic comparison of views (`cmp`);
- in-place swap through a `mut` view at run-time indices (`swap`, K5);
- reading an element through a `mut` view without consuming the view (`peek`);
- `&mut v` handing a `mut` view to a call that hands it back (move-and-rebind: a `mut` view
  is not copied);
- nested total loops.

`peek` is library code today, a replace-and-restore over K5. The zero-cost route is an `imm`
reborrow of a `mut` family, an open extension of K2 (§5.2).

### P8 `json-tokens` — a tokenizer with views into the input

```
data Tok<'a> = Punct(u8) | Str(slice 'a u8) | Num(i32) | Word(slice 'a u8) | End | Bad(i32)

-- The token at byte `i` of `t`, and the index after it. JSON is scanned as bytes: every
-- structural character is ASCII, so the text is validated once, where a string token is used.
fn token<'a>(t: slice 'a u8, i: i32) -> Tok<'a> * i32 =
  let i = skip_ws(&t, i);
  match get_byte(&t, i) {
    inr _ -> (End, i)
  | inl c ->
      if c == b'{' || c == b'}' || c == b'[' || c == b']' || c == b':' || c == b',' { (Punct(c), i + 1) }
      else if c == b'"' {
        match scan_string(&t, i + 1) {                  -- honours \" and \\; returns the closing quote
          inl j -> (Str(sub(t, i + 1, j)), j + 1)       -- a view into the input, no copy
        | inr j -> (Bad(j), j) } }
      else if is_digit(c) || c == b'-' { let (n, j) = scan_int(&t, i); (Num(n), j) }
      else if is_alpha(c) { let j = scan_word(&t, i); (Word(sub(t, i, j)), j) }
      else { (Bad(i), i + 1) } }
```

Forces:

- random access by index with bounds as a sum (`get_byte`);
- sub-views by `[i, j)` (`sub`, clamped to the view, so total), and views stored in a variant;
- `data` with a lifetime parameter;
- escape scanning by byte;
- no allocation: a string token without escapes is a view of the input. P13 shows the case
  with escapes, where a sum replaces `Cow`.

### P9 `http-request` — build a request line and headers into a buffer

```
fn request<'a, 'b>(host: str 'a, path: str 'a, headers: slice 'b (lit * lit), limit: i32) -> string =
  let mut r = box string(256);
  push_lit(&mut r, "GET "); push_str(&mut r, path);
  push_lit(&mut r, "?limit="); push_dec(&mut r, limit);
  push_lit(&mut r, " HTTP/1.1\r\nHost: "); push_str(&mut r, host); push_lit(&mut r, "\r\n");
  for h in iter(headers) {
    let (k, v) = *h;                                -- literals are persistent: `*` copies them
    push_lit(&mut r, k); push_lit(&mut r, ": "); push_lit(&mut r, v); push_lit(&mut r, "\r\n") };
  push_lit(&mut r, "\r\n");
  r

-- The fixed headers, by index: ("Accept", "application/json"), ("User-Agent", "op/0.1").
fn header_at(i: i32) -> lit * lit =
  if i == 0 { ("Accept", "application/json") } else { ("User-Agent", "op/0.1") }

main -> i32 =
  let hs = box array(2, header_at);
  let req = borrow hs { v ->
    request(&"api.cluster.local", &"/api/v1/namespaces/default/pods", v, 10) };
  write_str(&mut stdout, &req);                     -- later: `Net`'s `send(&mut conn, &req)`
  len(&req)
```

Forces:

- many appends of views and literals into one buffer, with the capacity given up front;
- an array of literal pairs, iterated. Literals are persistent values, so an array can hold
  them with no lifetime;
- literal views lent to a call (`&"…"`), two in one call (`pending/lend-two.bc`);
- a single bulk write. Per-byte writes would be one system call per byte.

This is the operator's shape: a request built once into one buffer and sent.

### P10 `split-at-mut` — two exclusive views at a run-time index

Reverse the first half of the input and upper-case the second half, in one borrow.

```
fn reverse<'a>(v: slice mut 'a u8) -> () =
  let n = len_mut(&mut v);
  for i in range(n >> 1) { swap(&mut v, i, n - 1 - i) }

fn upper<'a>(v: slice mut 'a u8) -> () =
  for x in iter_mut(v) { modify x { c -> if b'a' <= c && c <= b'z' { c - 32 } else { c } } }

main -> i32 =
  let mut b = read_all(&mut stdin);
  let n = len_of(&b);
  borrow mut b { v ->
    match split_at(v, n >> 1) { inl (l, r) -> reverse(l); upper(r) | inr _ -> () } };
  write_all(&mut stdout, &b);
  n
```

Forces:

- **dynamic disjoint `mut` families.** `split_at` of a `mut` view at a run-time index gives two
  exclusive views at one lifetime, used in the same scope;
- `mut` leaf borrows handed out one at a time (`iter_mut`), updated in place (`modify`);
- a cell-free `mut` borrow of an owned buffer (`borrow mut b`, K2).

### P11 `ascii-upper` — an in-place text transform that keeps the invariant

```
main -> i32 =
  let input = read_all(&mut stdin);
  match from_utf8(input) {
    inl s -> make_ascii_uppercase(&mut s); write_str(&mut stdout, &s); len(&s)
  | inr (b, _) -> free(b); 0 }
```

`make_ascii_uppercase : str mut 'a -> ()` changes only bytes below `0x80` and leaves every
multi-byte sequence as it was, so the result is valid UTF-8.

Forces:

- an exclusive text view (`str mut`) whose API is only the operations that keep UTF-8;
- `&mut s` at a `str mut` parameter lending the initialised range with no cell (§4.3).

### P12 `iter-mut` — the pending program, as written in `corpus/pending/iter-mut.bc`

```
main -> i32 =
  let mut a = box array(4, tab);
  for x in iter_mut(&mut a) { modify x { v -> v * 10 } };
  sum(&a)
```

Forces:

- `[Mut 'c A]` families (K2);
- `iter_mut` as codata whose state is the remaining `mut` view (library over K3/K4);
- a total `for` over a finite iterator inside the lend.

### P13 `labels-json` — escaping with a borrowed-or-owned result (no `Cow`)

```
-- The text itself when it needs no escaping; otherwise a new, escaped string.
fn escape<'a>(t: str 'a) -> str 'a + string =
  if not(any_byte(&t, needs_escape)) { inl t } else {
    let mut s = box string(len(&t) + 8);
    for c in chars(t) {
      if c == '"' || c == '\\' { push_char(&mut s, '\\') };
      push_char(&mut s, c) };
    inr s }

fn push_json_str<'a>(out: string, t: str 'a) -> string =
  push_char(&mut out, '"');
  match escape(t) { inl v -> push_str(&mut out, v) | inr s -> push_str(&mut out, &s) };  -- s freed here
  push_char(&mut out, '"');
  out
```

Forces:

- a sum of a view and an owned string as the return type, which is Rust's `Cow<'a, str>` with
  no type of its own. Its destructor is componentwise (§12): the view side forgets, the owned
  side frees;
- `chars` and `push_char`.

### P14 `args` — OS strings are bytes

```
main -> i32 =                                       -- `Args` is designed in SPEC §11, not built
  let n = arg_count(&mut args);
  let mut arg = box buf[u8](64);
  for i in range(n) {
    arg = clear(arg);
    read_arg(&mut args, i, &mut arg);               -- argument `i`'s bytes, appended to `arg`
    borrow arg { v ->
      match str_from_utf8(&v) {
        inl t -> write_str(&mut stdout, t)
      | inr _ -> write_lossy(&mut stdout, v) } };   -- invalid sequences as U+FFFD
    putb(&mut stdout, b'\n') };
  n
```

Forces:

- OS-provided text is bytes. On WASI and POSIX, arguments, environment and paths are byte
  strings, so `OsStr` is `slice 'a u8`;
- checked conversion to text when the program needs text;
- a lossy display for bytes that are not UTF-8.

### P15 `c-string` — the NUL-terminated boundary

```
extern c_open : !(all 'a < top. cstr 'a * i32 => i32 + i32)   -- LLVM target, C ABI; design only

fn open_path<'a>(p: slice 'a u8) -> i32 + i32 =
  with_cstr(p, { c -> c_open(c, 0) })     -- copies into a NUL-terminated scratch array; or
                                          -- `Nul` if `p` has an interior NUL
```

Forces:

- a NUL-terminated representation at, and only at, an extern whose contract is C's;
- one copy per call. `with_cstr` allocates, writes the bytes and a NUL, and frees after the
  call. A `buf u8` with spare capacity can instead write the NUL in place: `terminate(&mut b)`
  checks for interior NULs and costs no allocation.

### What the programs force, collected

| feature | programs | where |
|---|---|---|
| `u8` with byte layout | all | K1, backend |
| a view of an owned array or buffer with no cell (`imm` and `mut`) | P1, P5–P7, P9–P12 | K2 |
| a split at a run-time index, and sub-ranges | P1, P3, P8, P10 | K3 |
| writes through a `mut` view: `modify` a leaf, `swap`, `replace` | P7, P10–P12 | K4, K5 |
| total loops over a count or a view | all | K0, library |
| `iter`, `iter_mut`, `bytes`, `chars`, `lines` over views | P1, P2, P5–P7, P9–P13 | library (codata, §7) |
| a growable buffer, `clear`, `push`, `reserve` | P1, P3–P7, P9, P13, P14 | library (stage A), a former later |
| a buffer of views, or of other non-integer elements (a filler) | P6, P7 | library, `slice_empty` |
| UTF-8 validated construction, in place and of views | P5–P7, P11, P14 | library |
| formatting into a buffer | P4, P9 | library |
| literals as unowned data, and their views | P4, P6, P9, P13 | library, backend |
| bulk read and write of a view | P1, P9, P10 | externs (not kernel) |
| `data` values without `box`, and with a lifetime parameter | P2, P8 | surface (stage 8) |
| `fn f<'a>` | nearly all | surface: done (`corpus/fn-lifetime.bc`, SPEC §15 *Generic functions*) |
| a borrow block that threads capabilities | P1, P5, P6 | surface |
| a sum in place of `Cow` | P13 | nothing new |
| the NUL-terminated C boundary | P15 | extern marshalling |

## 2. Types: the axes, and Rust's zoo

### 2.1 The principle used

Several string types are fine when each follows from an independent axis. What the design
avoids is types that exist as accidents or workarounds. Each type below names its axes, and
says why a combination of the others does not express it. Each conversion's cost follows
from the axes it crosses (§2.4).

**Ownership and permission.** A range of places can be owned (`array A = [Ref A]`), shared at
a lifetime (`slice 'a A = [Imm 'a A]`) or exclusive at a lifetime (`slice mut 'a A =
[Mut 'a A]`). These are one former, `[L]` (SPEC §9), at three leaf permissions. So the range
concept is orthogonal to permission: a view is a family of leaf borrows, not "a borrow of an
unsized thing". This is what the §9 former already is. `[Mut 'a A]` is the one permission it
does not yet provide (K2).

**Growth.** A growable buffer has a capacity beyond its length, whose slots are not part of its
value. Neither an array (its length is its capacity) nor a view (it owns nothing) can grow, so
`buf A` is its own concept. It is owned only: a shared or exclusive view of a buffer is a view
of its initialised range, and growth needs the owner.

**Encoding.** UTF-8 validity is a refinement of byte storage, orthogonal to permission and to
growth. `string`, `str 'a` and `str mut 'a` are `buf u8`, `slice 'a u8` and `slice mut 'a u8`
with the invariant. Is bytes versus text one type with an encoding parameter, or two? Only two
encodings matter: UTF-8, and none. "None" is plain bytes. The APIs differ: text has `chars`
and character boundaries, bytes have neither. A parameter with two values, one of which is
"no refinement", is a wrapper, and the design says so: text is `utf8(·)` over byte storage.

**Why the invariant needs no kernel support.** Every operation is safe on any bytes. Indexing is
bounds-checked, and decoding is total: an invalid sequence decodes to U+FFFD. So memory safety
never depends on UTF-8 validity. Validity is a correctness property of the text library. It can
be stated in Lean, if wanted, as "each library function maps `Utf8Valid` bytes to `Utf8Valid`
bytes", and it needs no rule.

Enforcing it needs an abstraction boundary: only the text library may build a `str` from
bytes. The core is structural (decision 9), so that boundary is an opaque type at the module
level (#63). Until #63 lands, `string` and `str 'a` are abbreviations, and the invariant is kept
by construction and by convention. Stage T2 (§8) is the enforcement.

**Static data.** A literal is part of the program, owned by no one. It is persistent data
(`!`-like: it holds no resource), not a borrow. Viewing it as a `str` is a scoped lend, like
viewing any value (§5.7).

**Element width.** `u8` exists because of layout: an array of `u8` must be one byte per
element, or text costs 8× its size. That is the only reason it is a type and not `i32` (§5.6).

### 2.2 The proposed set

| type | core | axes | why not a combination |
|---|---|---|---|
| `u8` | `int w8` | width | `i32` in a slot is 4 or 8 bytes |
| `array A` | `[Ref A]` | range, owned | exists (§9) |
| `slice 'a A` | `[Imm 'a A]` | range, shared | exists (`array_imm`) |
| `slice mut 'a A` | `[Mut 'a A]` | range, exclusive | new leaf permission of `[L]` (K2) |
| `buf A` | `array A ⊗ I32`, with a filler (stage A); a former (stage F) | growth, owned | capacity is not in any range |
| `string` | `buf u8` + UTF-8 | growth, owned, encoding | invariant |
| `str 'a` | `slice 'a u8` + UTF-8 | range, shared, encoding | invariant |
| `str mut 'a` | `slice mut 'a u8` + UTF-8 | range, exclusive, encoding | invariant; only UTF-8-preserving writes |
| `lit` | `I32 ⊗ !(I32 ⇒ U8)` + UTF-8 | static | owned by no one, persistent |

Not provided, each for a reason:

- **Owned fixed text** (`Box<str>`). It saves the capacity word of `string`. Growth's fixed
  point for text is not worth a type, so `string` with `cap = len` serves. If an interning
  table ever needs the word, `utf8(array u8)` is the combination, and nothing new is needed.
- **Fixed-size stack arrays** (`[u8; N]`). They are a layout question (placement, #15), not a
  type question. `box array(n, f)` is the only array.

### 2.3 Rust's string zoo, case by case

| Rust | its job | here | notes |
|---|---|---|---|
| `String` | owned, growable UTF-8 | `string` | |
| `str` | the unsized UTF-8 range | (none) | there are no unsized types: a range is a sized value `(ptr, len)` at a permission |
| `&str` | a shared UTF-8 view | `str 'a` | a family of leaf `imm` borrows, not a borrow of a `str` |
| `&mut str` | exclusive UTF-8 view | `str mut 'a` | only UTF-8-preserving operations (ASCII case), as in Rust |
| `&'static str` | literal | `lit`, viewed by `&"…"` | persistent data, not a borrow (§5.7) |
| `Box<str>` | owned, fixed, one word smaller | `string` | not worth a type (§2.2) |
| `Rc<str>`, `Arc<str>` | shared ownership | none; indices into an arena of strings (#94) | no RC (standing constraint) |
| `Cow<'a, str>` | borrowed or owned | `str 'a + string` | a plain sum; its destructor is componentwise; P13 |
| `Vec<u8>` | growable bytes | `buf u8` | |
| `Box<[u8]>` | owned fixed bytes | `array u8` | |
| `&[u8]`, `&mut [u8]` | byte views | `slice 'a u8`, `slice mut 'a u8` | |
| `[u8; N]` | inline fixed bytes | not provided | layout, not type (§2.2) |
| `OsString`, `OsStr` | platform strings | `buf u8`, `slice 'a u8` | on WASI and POSIX they are bytes; P14 |
| `CString`, `CStr` | NUL-terminated, no interior NUL | at extern boundaries only: `with_cstr`, `terminate` | a real representation axis; P15 |
| `char` | a Unicode scalar value | `i32` from `chars` (a nominal `char` with #63) | |
| `from_utf8_unchecked` | skip validation | not in safe code; an extern (decision 27) if ever needed | |

**Where the zoo is right, and where the complexity moves.**

- **`CStr` is a real axis.** A NUL-terminated string has no length word and forbids interior
  NULs. C requires it, and no view can be one without a copy or spare capacity. The design
  confines it to extern contracts. That moves the cost to each C call (a copy, or a scan plus a
  write into spare capacity), where Rust can cache a `CString`. If FFI-heavy code appears, a
  library `cstring` (a `buf u8` with "ends in NUL, no interior NUL") is the combination, still
  with no kernel type.
- **`OsStr` exists in Rust for Windows** (WTF-8 over UTF-16). Windows is not a target. If it
  becomes one, the conversion belongs in the `Args`/`Env`/`Fs` externs, which hand out bytes.
  The honest cost is that Windows paths could not round-trip without that extern-level
  encoding.
- **`Cow` disappears only because sums and destructors do its job.** What moves is the `match`
  at each use (P13's `push_json_str`). Rust's `Deref` hides that `match`. Here it is written,
  about one line per use.
- **Losing `Box<str>` costs a word per owned string.**
- **Losing `Rc<str>`** moves shared strings to arena indices, an API change for programs that
  share many strings. This is decision-level (no RC), not a string question.

### 2.4 Conversions, costed by the axes they cross

| conversion | axis crossed | cost |
|---|---|---|
| `&s : str 'a` from `string`; `&b : slice 'a u8` from `buf u8`/`array u8` | permission (owned → view) | free: `(ptr, len)`, no cell |
| `&v` of a view | none (a copy of an `imm` view) | free: two words |
| `split_at`, `sub`, `trim`, `split_first` | range (narrowing) | one compare; free otherwise |
| `as_bytes(t)`, `into_bytes(s)`, `as_bytes_mut` | encoding (forget the refinement) | free |
| `str_from_utf8(v)`, `from_utf8(b)` (in place) | encoding (establish the refinement) | checked: O(n), no allocation |
| `split_at_str`, `sub_str` | range, on text | one compare and a boundary check |
| `to_string(t)`, `to_buf(v)` | ownership (view → owned) | allocating: O(n) copy |
| `&"lit" : str 'c` | static → view | free in the lowering: a pointer into read-only data (§5.7) |
| `string_of_lit` | static → owned | allocating |
| `array_of_buf` | growth → fixed | free when `len = cap`; otherwise a reallocation |
| `buf_of_array` | fixed → growth | free (`cap = len`) |
| `with_cstr(v, f)` | representation (C) | allocating: O(n) copy and scan, per call |
| `terminate(&mut b)` | representation (C) | O(n) scan, plus a write into spare capacity or one growth |

There are no implicit conversions. Every row is a named function, or `&` at a call, whose
mechanism the parameter type selects (§3).

## 3. Rust's overloaded `&` and `Box`, weighed

The user's view is that Rust overloads `&` and `Box`. That view is weighed here as design input,
not as a settled principle. Where the design splits a Rust overload into separate concepts, a
target program justifies it. Where one construct is simpler, it keeps one.

### 3.1 `&`

| Rust's job for `&` | here | justified by |
|---|---|---|
| a permission at a lifetime | `imm 'a A`, `mut 'a A`: only that | BoLo |
| the only way to hold unsized data (`&str`, `&[T]`) | split out: ranges are the sized family `[L]` at a permission, so owned, shared and exclusive ranges are one concept | P6, P7 store views in buffers; P10 needs `mut` ranges; P9 an owned `array` of pairs |
| sub-views (`&s[1..3]`) | split out: `sub`, `split_at` and `trim` are functions on a view that return a view at the same lifetime. No new borrow is made | P3, P8, P10: a sub-view at a *run-time* index must stay at the parent's lifetime, which a fresh borrow would shorten |
| deref coercion (`&String → &str`), auto-borrow in method calls | not provided: `&s` is written at each call. There are no methods | readability checked below |
| static data (`&'static str`) | split out: `lit` is persistent data, viewed by a scoped `&"…"` | P4, P9, P13 |

**Kept as one construct.** `&x` remains the one lend marker. The parameter's type selects the
mechanism: a borrow of a cell, a family view of a range, a copy of an `imm` view, or
move-and-rebind. This is typed elaboration §5.1's decision, and to the reader every row means
"lent here, back afterwards". Splitting `&` into several spellings would add syntax with no
program that needs it. It is a deliberate overload, and a type-directed one.

**Readability without coercions.** Across P1–P15:

- `&` appears at every call that lends, which is about one per line in the formatting programs
  (P4, P9);
- there are no `.as_str()`, `.as_bytes()` or `&*` chains;
- conversions that change a type are named (`as_bytes`, `str_from_utf8`);
- the heaviest cost is P9's `push_*(&mut r, …)` on each line. That is Rust's `r.push_str(…)`
  with the receiver written as an argument.

Two conveniences would pay for themselves, each elaboration only:

- A **borrow block that threads capabilities** (P1, P5, P6). Today a block must return the
  capabilities it used. It should hand them back as `for` hands back its variables.
- **A `format` form** (`push_fmt(&mut r, "GET {path}?limit={limit}")`), elaborated to the
  `push_*` calls. It is an optional later stage (§8), not needed for any program.

Indexing sugar `v[i]` is not proposed. It would have to return a sum (`u8 + 1`), because
out-of-range is an error value, not a trap. `get_byte(&v, i)` says that.

### 3.2 `Box`

`box` means heap allocation only. Rust's other uses of `Box`:

| Rust's use of `Box` | here |
|---|---|
| heap allocation | `box e`, `box array(n, f)`, `box buf(cap)`, `box string(cap)`: `box` marks every allocation site |
| unsized ownership (`Box<str>`, `Box<[T]>`) | not needed. `array A`, `buf A` and `string` are sized handles. `box` appears at their construction because they allocate, not because they are unsized |
| indirection for recursive types | the same meaning: a recursive `data` field is a heap cell, `box Cons(x, t)` (typed elaboration §5.3). No separate concept |
| type erasure (`Box<dyn Trait>`, `Box<dyn Fn>`) | unnecessary: closures are defunctionalized, generics are monomorphized (decision 8), and there are no traits |
| stable addresses, pinning | unnecessary now: a cell never moves while owned, and a borrow cannot make a value self-referential (lends are scoped). Async state machines (#52) may revisit this |
| cheap moves of large values | handles are 2–3 words. A large record is a block only if the program writes `box`; placement is the backend's (#15) |
| FFI ownership transfer (`into_raw`) | no raw pointers in safe code (decision 27). Ownership crosses only extern contracts. Our allocator is not C's, so buffers handed to C are copied. This is a real reason Rust has `into_raw`, deferred to the LLVM FFI |
| leaking to `'static` | excluded: adequacy says memory is empty at the end. Static data is `lit` |

**One place allocation is not at a `box`: growth.** `push` on a full `buf` reallocates, as Rust's
`Vec::push` does. The allocation site `box buf(cap)` is visible, and the type `buf` says "may
reallocate". Allocation *inside* `push` is not marked, though. Options (Q2, §10):

- accept it;
- make growth explicit: `push` returns `buf ⊕ (buf ⊗ A)` when full, and `grow(box, b, n)` is
  the only reallocation;
- mark it with the `noalloc` design (`pending/noalloc.bc`).

## 4. The API: kernel and library

### 4.1 Kernel, with the justification for each

Every kernel item is a constant typed at a dead context, with a closed term and a compatibility
lemma, as the §9 constants are (`Core/Arrays.lean`). K1 also adds a `Width` case. None adds a
`CDerives` rule that inverts, an index, or a `VTy` former.

- **K0 `count_fold[S] : !(!(I32 ⊗ S ⇒ S) ⊗ (I32 ⊗ S) ⇒ S)`.** It runs the step at
  `i = 0, …, n−1`. The term is a Z-combinator loop on an `i32` counter, like the folds'
  terms, and the proof is induction on `n − i`.

  Why a primitive: every total loop over a view or a count needs one. Today's total iteration
  folds over the unary count `μX. 1 ⊕ X` (`div_nat`), and in the backend each `inr` is a boxed
  object. So a counted loop of `n` allocates `n` objects, which is not zero-cost. Stage 9 of
  typed elaboration planned exactly that fold. K0 replaces it.

- **K1 `u8`.** `Width.w8`, `IntLit.u8`, and two host operations: `wrap8 : I32 ⇒ U8` (the low
  8 bits) and `extend8_u : U8 ⇒ I32`. There is no arithmetic at `w8`: it is done in `i32`, as
  in Wasm.

  Why a primitive: layout. An array of `u8` is one byte per slot only if the type says so (§5.6).
  `read_byte`/`write_byte` move to `u8`, which withdraws decision 32's "bytes as `I32`".

- **K2 `slice_borrow[M] : !(array A ⊗ U(∀'c ⊏ ⊓Δ. [M 'c A] ⊸ F(['c] T)) ⇒ array A ⊗ T)`**, for
  `M ∈ {Imm, Mut}`, with `T` outliving the context's lifetimes (as `withborF2`) and, at `Mut`,
  `A` outliving (as `withbor` form 2). The term is `withbor`'s own term, `λa. λg. (a, g () a)`:
  the handle is passed to the callback and returned.

  Why a primitive: `[Mut 'c A]` exists nowhere else. §9 Open lists it, and `pending/iter-mut.bc`
  waits for it. At `Imm`, the existing route is `withload` of a cell holding the array, and
  every lend of a `string` value would pay a scoped cell: an `alloc` and a `free` per call in
  the model, and a heap cell in today's backend. Proof: §5.2.

- **K3 `slice_split[L] : !([L] ⊗ I32 ⇒ ([L] ⊗ [L]) ⊕ [L])`**, at `L = Imm 'c A` and at
  `L = Mut 'c A`, and **`slice_empty[L] : ![L]`**, the value `(0, 0)`.

  The term: `λ((ℓ, n), i). if i ≤ₓ n then` `case idx((ℓ, n), i) { inl c → inl ((ℓ, i), (c, n − i)) | inr _ → inl ((ℓ, n), (ℓ, 0)) }` `else inr (ℓ, n)`. When `i = n`, `idx` is out of range and the right part is the empty family. It uses the existing `idx` and host steps, so there is no new machine step.

  Why a primitive: a family value cannot be built from a location and a length by typing, so no
  library code can split one. Owned families are excluded by typing (§5.4). Proof: §5.1.

- **K4 `slice_get` and `slice_len` at `Mut`:**
  - `[Mut 'c A] ⊗ I32 ⇒ Mut 'c A ⊕ 1` consumes the family and hands out one leaf (the rest is
    forgotten, since `mut` leaves hold no `own` cell);
  - `[Mut 'c A] ⇒ [Mut 'c A] ⊗ I32`.

  Why a primitive: the `imm` forms exist (`array_get`, `array_len`). The `mut` forms need their
  own lemma, because a `mut` family is not duplicable.

- **K5 `slice_replace : !([Mut 'c A] ⊗ (I32 ⊗ A) ⇒ [Mut 'c A] ⊗ (A ⊕ A))` and
  `slice_swap : !([Mut 'c A] ⊗ (I32 ⊗ I32) ⇒ [Mut 'c A])`.**

  Why a primitive: a write at an index must keep the rest of the family. With only K3 and K4, a
  write splits the family into pieces that cannot be rejoined. A borrowed-family join would
  need a location comparison, a new machine step. Two constants are cheaper than a step, and
  `sepRange_pick`/`sepRange_pick2` already exist for exactly these.

### 4.2 Library (`lib/slice.bc`, `lib/buf.bc`, `lib/text.bc`, `lib/io.bc`)

- **Views.**
  - Access: `len`, `get`, `get_byte`, `split_first`, `split_last`, `split_at`, `split_once`,
    and `sub(v, i, j)`, which clamps `[i, j)` to the view and so is total.
  - Search and compare: `find_byte`, `find`, `starts_with`, `eq`, `cmp`, `skip_while`,
    `rskip_while`, `any_byte`.
  - Writes: `fill`, `copy_from`, `reverse`, `peek` (replace-and-restore).
  - Iteration: `iter`, `iter_mut`, `bytes`, `range`, `range_down`, `count`.
  - All of it is written over K0 and K2–K5 and §9's constants.
- **`buf A`, stage A** (`array A ⊗ I32`, with the unused slots holding a filler):
  - construction and lending: `box buf[A](cap)` (the filler by type: `0` for integers, `empty`
    for views, `string` of capacity 0 for strings), and `borrow b { v -> … }` (K2, then
    `split_at` at the length);
  - edits: `push` (may grow), `pop`, `clear`, `truncate`, `reserve`;
  - queries and disposal: `len_of`, `free`.

  Growth is `box array(cap′, filler)`, a move of each element by `array_replace`, then
  `array_free` of the old block.
- **Text.**
  - Types: `string`, `str 'a`, `str mut 'a`.
  - Construction: `box string(cap)`, `from_utf8`, `str_from_utf8`, `to_string`,
    `string_of_lit`.
  - Byte views: `as_bytes`, `into_bytes`.
  - Appending: `push_str`, `push_lit`, `push_char`, `push_dec`, `push_hex`.
  - Iteration and search: `chars`, `char_indices`, `lines`, `split_once_str`, `trim`,
    `split_at_str`, `sub_str`, `find`, `replace_all`, `eq_lit`, `cmp`.
  - Parsing and in-place case: `parse_i32`, `parse_i64`, `make_ascii_uppercase`,
    `make_ascii_lowercase`.
- **Literals.** `"…" : lit`; `&"…"` lends a `str 'c` view to one call; `lit_len`.
- **I/O.**
  - Externs, not kernel: `write_all : !(all 'a 'b < top. mut 'a output * slice 'b u8 => mut 'a output)`, and `read_into` (fill a `mut` view and return a count).
  - Library over them: `write_str`, `write_lit`, `write_lossy`, `read_all`, `put_dec`.

  Each extern's model is a loop over `write_byte`/`read_byte`, so its contract is the
  Fundamental Property of the model term (SPEC §11's pattern). The host implementation is one
  `fd_write`/`fd_read`. They exist for cost (one system call per view instead of per byte), and
  that is the SPEC §11 rule for adding a primitive: when "a loop over these two cannot express
  it" at acceptable cost.
- **FFI** (LLVM stage, design only): `with_cstr`, `terminate`.

### 4.3 Surface additions (elaboration only)

- **One new row of typed elaboration §5.1's lend table.** For `x : array A`, `buf A` or
  `string`, at a parameter `slice 'a A`/`str 'a` (`&x`) or `slice mut 'a A`/`str mut 'a`
  (`&mut x`), the lend is `slice_borrow` around the call, with `split_at` at the length for
  `buf`/`string`, and `x` is rebound from the pair. There is no cell.
- **`borrow x { v -> S }`** on the same types, and threading of the capabilities and `let mut`
  variables the block uses.
- **`box array(n, f)`, `box buf(cap)`, `box string(cap)`.**
- **Literals:** `b'x' : u8`, `'x' : i32` (a scalar value), `"…" : lit`.
- **Total `for`:** `for x in e` over a *bounded* source is a K0 loop, which is total. A bounded
  source is a view's `iter`/`iter_mut`/`bytes`/`chars`/`lines`, or `range(n)`. A source that
  may not end (`bytes(&mut stdin)`) stays div. This is typed elaboration's stage 9, with K0 in
  place of the unary fold.
- **`*e` of a copyable payload.** Today `*e` reads only a persistent payload. It extends to a
  payload `A` with `Imm̲ 'b A = A`, such as an `imm` view, which `withload` copies out at its own
  lifetime (P6, P7).
- **`data T<'a>`** (stage 8); `fn f<'a>(…)` is done (`corpus/fn-lifetime.bc`).

## 5. The memory model this forces

This is the core of the document. For each requirement it says what the model and the proofs
need, and whether §9's array, a family of leaf places, already suffices.

### 5.1 Borrowed sub-ranges at a lifetime, split at a run-time index

**What §9 gives.** `𝒱⟦[L]⟧δ(v) ≜ ∃ℓ c. ⌜v = (ℓ, c)⌝ ⋆ ⊛_{i<c} 𝒱⟦L⟧δ(ℓ + i)` (`vP_fam_iff`).
At `L = Imm 'c A` each leaf is an `imm` cell at the family's lifetime, at the top level of the
resource, and no cell owns another (`Core/Arrays.lean`'s header). At `L = Mut 'c A` it is the
same with `mut` cells.

**The split.** Splitting `(ℓ, n)` at `i ≤ n` gives `(ℓ, i)` and `(ℓ + i, n − i)`. Semantically
it is `⊛_{j<n} P(ℓ+j) = ⊛_{j<i} P(ℓ+j) ⋆ ⊛_{j<n−i} P(ℓ+i+j)`, which is `sepRange_split`. The
leaf predicate is unchanged, so both halves are at the same lifetime. The resources are
disjoint (`ResU.CompS ρ₁ ρ₂ ρ`), so two `mut` halves never alias.

This was checked as a spike, against `main` at `998214d` (not committed):

```lean
theorem vP_fam_split {L : VTy} {ls : List SRec} {δ : LSub} {ℓ : Loc} {n i : UInt32}
    {ρ : WRes} (hv : vP (.fam L) ls δ (Val.arr ℓ n) ρ) (hi : i ≤ n) :
    ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ vP (.fam L) ls δ (Val.arr ℓ i) ρ₁ ∧
      vP (.fam L) ls δ (Val.arr (ℓ + i.toNat) (n - i)) ρ₂
```

It is proved in six lines from `vP_fam_iff`, `sepRange_split` and `vP_fam_mk`. `#print axioms`
is `[propext, Classical.choice, Quot.sound]`.

The constant K3 around it is `wpTS_head` for `idx` and the host comparison, then `wpTS_val`
at the two families. That is the shape of `arrGet_compatX`, with `vP_fam_split` in place of
`sepRange_pick`.

**Assessment of the old suspicion.** The suspicion was that `split_at_mut` at a run-time index
might not work. Its source was the parent-cell shape of `experiments/Projection`, `Relaxed` and
`FrameEnd`: a view below a cell that owns it, which `↭` rejects (`imm_view_rejected`,
`mut_view_rejected`). A family has no parent cell: its leaves are at the top level. That is why
`experiments/Places` got static `split_at_mut` "for free". The run-time version is the same
argument with `sepRange_split` in place of `⊗E`. Nothing in it depends on `n` being static.

So the split is not the risk. The risk is getting a `mut` family in the first place (§5.2).
`experiments/Optics` records the all-at-once `mut` borrow of a *list* at one lifetime as not
derived (`AllAtOnceGoal`, L2). §5.2 is the array case of that goal, and it is easier: the
places are consecutive, and none is behind another's cell.

**Owned families are not split**, although the model would allow it. See §5.4.

### 5.2 The cell-free borrow: a family of `mut` leaves at one lifetime

**The requirement.** A family of `mut` leaf borrows `[Mut 'c A]` at one lifetime, taken from an
owned array with no cell around it. The `imm` form is also wanted, to avoid a cell per lend.

**Why §9 does not give it.** `withload` produces `[Imm 'x A]` from `Imm @a (Array A)`, because
`Imm̲` exists for `imm` borrows. There is no `mut` counterpart: `Mut @a (Array A)` is mutated
through `withswap`, which owns the whole array for one callback. No typing rule yields
`[Mut 'c A]`. At `imm`, `withload` needs the array in a cell, and a cell is an allocation.

**The argument.** It is the one sketched in §9 Open ("each leaf framed by its own 6.64/6.65
frame, nested"), now concrete. Take `e = g () (ℓ, n)`, the body of K2's term. Apply Mut Frame
at the typed world (`wpTS_M_frameX`, `Core/FrameRules.lean`) to leaf `ℓ` around `e`. Inside its
premise, apply it again to leaf `ℓ+1` around the same `e`, and so on `n` times. This is an
induction on `n`, generalized over the postcondition and over the leaves already framed.

- Each application gives its own fresh lifetime `α_j`, below the context's lifetimes.
- At the bottom the callback is instantiated at a lifetime `γ` below every `α_j` and below
  `⊓Δ`. Every leaf `ptoMutS (ℓ+j) α_j` is a leaf of `𝒱⟦Mut 'c A⟧δ['c ↦ γ]`, because `ptoMutS`
  accepts any `α ⊒ δ('c)`. That is the fact that makes `⊑Mut` sound, so the `n` leaves form
  `sepRange` at `'c = γ`.
- The callback returns `[γ] 𝒱⟦T⟧`. Frame `j` wants its postcondition under `box α_j`.
  Because `T` does not mention `'c` and outlives the context's lifetimes, 6.60
  (`vC_outlives`) reboxes it at every `α_j`. That is the side condition `withborF2` and
  `withborS` carry, and K2 carries it too.
- Each frame's exit hands back `∀w. ℓ+j ↦ w −⋆ 𝒱⟦A⟧(w) −⋆ …`. Together they rebuild
  `sepRange (vP (Ref A)) ℓ n`, the owned array, with whatever values the callback left.

This is `withbor2_compatX`'s proof (`Core/Compatibility.lean`) iterated. The iteration is on
`n` inside the semantics, not on a derivation. `experiments/Places` is the evidence for any
fixed `n`: nested `withbor2` and `⊑Mut` derive the static-`n` family, and FP covers it. The run-time version replaces the syntactic nesting with a semantic induction. It needs no
new rule and no model change.

**At `Imm`.** The same argument uses `wpTS_I_frameX`. Each frame adds a record
(`AddAt ls ls′ α`), and its premise needs the record to exist
(`∃ r ∈ rsOf ls′, r.le = ℓ ∧ …`). The induction then carries a list of `n` records, and `Ext`
stability of the postcondition (`hQ`) through `n` extensions. It is the same proof with more
bookkeeping, so it is rated one notch riskier.

**Operationally** the primitive is the identity: the callback receives the handle it would have
received anyway. The `n` frames are proof-only. That is the "cell-free element borrow" of §9
Open.

**Named obstacle, and what to check first.** I have not derived K2 and have not verified that
any obstruction is real. The first thing to check is `wpTS_M_frameFam`, the `n`-fold lemma
stated at `wpTS`, *at `n = 2`*, by two direct applications of `wpTS_M_frameX` around one `e`.
It shows whether the inner `fresh` quantifier can be discharged with the outer frame's `mut`
cell in the resource, whether a `γ` below both frames' lifetimes is available where the
callback is instantiated, and whether reboxing at `α₁` goes through `vC_outlives` as stated.
`experiments/Places` makes the `n = 2` case expected to hold. After that, the induction is
routine.

**Deliberately left out.**

- An `imm` reborrow of a `mut` family (`[Mut 'c A] ⊸ (∀'d. [Imm 'd A] ⊸ ['d] T) ⊸ …`), which
  `peek` in P7 would use. It is `n` applications of `withbor3`'s anti-frame and frame, and a
  natural K2′ once K2 exists.
- A `mut` reborrow at a shorter lifetime, which is `⊑Mut` (already free for families, since
  `ptoMutS` is monotone).

### 5.3 Iteration at the borrow's lifetime

- **`iter` over `[Imm 'c A]`** already runs: `corpus/axes/codata-coeffects.bc` is a cursor
  whose state is the family and an index. With K3 it is cleaner: the state is the remaining
  view, and `next` is `split_first`.
- **`iter_mut` over `[Mut 'c A]`** is `unfold` at `Iter (Mut 'c A) 1 1` (§7) with state
  `[Mut 'c A]`:
  - `next` splits off the first leaf and yields it with the rest (K3, K4);
  - `close` forgets the rest (a `mut` family has no `own` cell, so its destructor is `forget`).

  The element type `Mut 'c A` does not mention `X`, so the body is in `NuOk`. It is library
  code with no rule.
- **The lifetime.** The iterator's type mentions `'c`, so it lives inside K2's callback, where
  `'c` is bound. It can cross an *inner* scope boxed at that scope's lifetime.
  `corpus/axes/scope-boxed-iter.bc` does this for the `imm` cursor today. The `mut` version
  needs `[Mut 'z A] ⊐ 'w`, which `VOutlives` at `[L]` gives from `L ⊐ 'w`.
- **The loop.** A `for` over the iterator must stay inside the lend, so it must not be div
  (`pending/borrow-across-loop.bc`: a borrow block's body cannot return a loop). It is total:
  a view's iterator finishes within `len + 1` observations. The `for` elaborates to K0 with
  that bound, observing once per step. After the iterator finishes, the remaining steps do
  nothing, and the bound's exhaustion branch closes it. That branch is unreachable, but it is
  typed.

  This is what `pending/for-finite.bc` and stage 9 need. The difference from stage 9's plan is
  that the bound is counted by K0, not by a unary list.
- **Lists** (the other half of #57) are not addressed. A borrowed list's nodes are behind
  cells, so a list iterator still needs `withload` per node (§7 Open, `[@d] U(νX. C)`).

### 5.4 Growth

**Requirements:**

- capacity versus length;
- slots that are not initialised;
- reallocation as a move that is sound under every allocator;
- no borrow held across growth.

**Stage A: no kernel change.** `buf A ≜ array A ⊗ I32`. The array's length is the capacity,
the `I32` is the length, and slots at or beyond the length hold a filler. For text the filler
is `0`. For views it is the empty view (`slice_empty`). For owned strings it is a string of
capacity 0, which allocates nothing (see §7).

- `push` is `array_replace` at the length (the filler comes back, and is persistent or dropped
  by its destructor).
- `pop` is `array_replace` with the filler.
- Growth is `box array(cap′, filler)`, then `len` element moves by `array_replace` on both
  arrays (the old slots get fillers back), then `array_free` of the old array. The filler
  destructor runs on the old slots.

**Sound under every allocator, with nothing new.** `tab` places its block at the allocator's
pick on every run (§13: `alloc_block`, `wpTS_tab` for every `A` and `k`). `array_replace` and
`drop` allocate nothing. `adequacyD` and `total_every_run` cover every program over them. A
buffer is therefore one block on every run, and its reallocation is a new block on every run.

**No borrow across growth, from linearity.** A view of a buffer exists only inside a lend:
K2's callback, or `withload`'s. The owner is not in the callback's context
(`experiments/Affine`'s `owner_not_shared`, and K2's typing, which takes `array A` linearly).
So no code can call `push` on a buffer while a view of it is live. The view's type
`[Imm 'c A]` cannot leave the callback, because `['c] T` requires `T` not to mention `'c`.
The typing rules alone rule out Rust's "iterator invalidation", with no borrow checker pass.

A function that may grow a buffer takes it by value and hands it back first. `&mut s` at such a
parameter is move-and-rebind (typed elaboration §5.1), with no cell. That is the `&mut Vec`
of Rust, without the reference.

**Cost of stage A.** Each growth writes `cap′` fillers (a memset for bytes). Amortized, that is
O(1) per push, as the copy already is, but it is not zero. The element moves are a loop of
`array_replace`, not a `memcpy`. The lowering may recognize the loop, but that is not proved.
Element types without a filler cannot be buffered: an owned cell `box T`, a capability.
`1 ⊕ A` would do, at a tag word per slot.

**Why not owned split** (the uninitialised tail as a separate owned family `[Ref 1]`)? It would
be the natural zero-cost design: a `Ref 1` slot is uninitialised memory, since the lowering
stores nothing for `()`, and `swap` changes a cell's type. The model accepts it:
`sepRange_split` holds at `Ref`, and the machine frees cells one by one. The lowering does not:

1. **A block is freed once.** `array_free` lowers to one `free` of the block. An owned family
   split into two and freed separately would free `base + i·s`, which is not a block the
   allocator returned. A runtime adjacency check cannot tell "adjacent" from "same block": two
   separate allocations may be adjacent. Soundness would rest on a provenance discipline that
   typing does not enforce. That is §5 Open's "Block provenance" problem, and `LeafPlaces`'
   `crossPack` shows it.
2. **Allocating at sub-range granularity does not rescue it.** A range allocator that accepts
   sized frees of any live sub-range would make the model true of the runtime. But byte
   buffers split at odd indices would need byte-granular liveness, and the allocator works in
   8-byte granules.

So owned families stay whole, and uninitialised capacity waits for stage F.

**Stage F: zero-cost growth, when a program needs it.** Two independent pieces:

- **`array_realloc`** (for filler types): one allocating head step. It frees the old block and
  takes `cap′` cells at `A.pick k μ′ cap′` *after* the free, so an allocator may extend in
  place (C's `realloc`). It copies the values and fills the rest.
  - Cost: `Expr.allocs`, `AHead`, `Alloc.ofRun`'s replay and determinism each gain a case.
  - Proof: `alloc_block` plus a `free_block` counterpart, `n` of `TW.free`. The values keep
    their relation when moved, because `𝒱⟦A⟧(v)` does not mention the location.
  - Risk: low to medium. It is bookkeeping in the shape of `wpTS_tab`.
- **A `buf A` former**, value `(ℓ, len, cap)`, relation
  `sepRange (vP (Ref A)) ℓ len ⋆ sepRange (ptoOwn · ()) (ℓ+len) (cap−len)`. The tail is
  structurally the same block's, so provenance holds by construction.
  - Cost: a `VTy` former, about 100 arms.
  - `Imm̲ 'x (buf A)` would be `[Imm̲ 'x (Ref A)]` of the prefix. 6.131 at `buf` must show that
    the reborrowed tail (`imm` cells of `()`) can be forgotten. It has no `own` cell, as
    `noOwn_fam` argues for families, but the lemma is new.
  - Risk: medium.
  - Growth rule 20 asks whether `array` then becomes `buf` with `len = cap`. It does not
    delete anything: views still need `[L]`. So this is a second former, paid only if a program
    needs a buffer of non-filler elements, or the counts show the fill.

### 5.5 Contiguity

A buffer must be one block under every allocator. For arrays this already holds. `tab` is a
single step that places `n` cells at `A.pick k μ n`, and `Alloc.fresh` makes the whole block
free at every finite memory (`Core/Alloc.lean`, `Core/ArrayWp.lean`). So `array`, and stage A's
`buf` built from it, are contiguous on every run.

#77 is a different problem. Records built by `allocS` are several `alloc`s, contiguous only on
some runs. Strings do not depend on #77. Its fix (a block primitive for records, as `tab` is
for arrays) and stage F's `array_realloc` share the same kind of step: an allocating head step
over a block.

### 5.6 Bytes

**The type.** `u8` is `VTy.int .w8`. It is persistent, holds no resource, `Imm̲ 'b U8 = U8`, and
it outlives every lifetime, exactly as `I32` does (§8). Its relation holds at a `u8` literal and
the empty resource.

**Relation to `Prim.host`.** Values are `lit (.u8 c)`. The host gains two typed functions,
`wrap8` and `extend8_u`, grouped like the §8 conversions. The machine's host step
`(μ, host op v) ↦ (μ, r)` is unchanged. Every theorem stays parametric in the host.
`wasmHost` implements them by `i32.and 0xff` and the identity. Comparisons and arithmetic go
through `extend8_u`: the surface's `b'a' <= c` elaborates to `le_u32 (extend8_u …)`, and the
lowering folds the extension away.

**Layout is the reason, and it is a backend change.** Today every layout word is an `i64`, and an
array slot is `max 1 (class width)` words, 8 bytes each (Backend README, Representation). So
`array i32` is 8 bytes per element, and an `array u8` would be too. K1 alone does not make text
compact. The backend must give a slot the byte size of its class:

- `u8` 1 byte, `i32` 4 bytes, a location 4 bytes on wasm32 or 8 on LLVM, as it chooses;
- element `i` at `base + s·i`;
- `load8_u`/`store8` for `u8`.

Words stay the unit of locals and of non-array cells. This is the one lowering change strings
cannot do without.

**The byte list.** SPEC §11's `Input` model `Bytes = μX. 1 ⊕ (I32 ⊗ X)` becomes
`μX. 1 ⊕ (U8 ⊗ X)`. `read_byte`/`write_byte` take and return `u8`. `Core/Stdio.lean`'s model
proofs change at one type, and `lib/io.bc` follows.

### 5.7 Static text

**The requirement.** Literals that no one owns and that cost nothing to view.

**The design.**

- A literal is the persistent value `(n, t)` of `lit ≜ I32 ⊗ !(I32 ⇒ U8)`. `t` is a `!` closure
  with no captures that maps `i` to the `i`-th byte. It is persistent (`!`, and `I32`), so it
  is copied and dropped freely, and it holds no resource. That is the user's "persistent data,
  not a borrow". It needs nothing in the kernel.
- `&"…"` at a `str 'c` parameter is `lit_view`, library code: `box array(n, t)`, then K2 at
  `Imm`, then `array_free`. That is an allocation, `n` fills, a borrow and a free.

**The lowering** emits each literal's bytes once into read-only data. It lowers `t` to a load
from that data, and a `lit_view` whose array is never written (an `imm` lend) and freed at the
end to a pointer into the data. The claim that this is observationally the same run up to
locations (runs are invariant under renaming: `experiments/TwoRun`'s `steps_rename`) is a
lowering claim. It is tested on the corpus, not proved, like the rest of the lowering (§11
Assurance).

**Limit.** A literal's view is scoped to one lend, so it cannot be stored at a longer lifetime
beside views of the input. For P6-style tables mixing literals with input views, the
alternative is a real static region: literals as `[Imm ⊤ U8]` families in an initial memory.
Every view of them then outlives everything. That changes adequacy's statement from "empty
memory" to "the static memory" (Q4, §10).

### 5.8 Counted loops

K0 is in §4.1. It is here because the memory model is at stake. A total loop that allocates
one object per iteration is not a zero-cost loop over a slice, and the unary count does that.
K0's term is a Z-combinator loop, which the backend's native fixed points (#50) compile to a
loop. Its proof is an induction on `n − i` that applies the step's `!` function (`bang_app`)
at each `i`.

## 6. Proof obligations and risks

| entry | new lemma | reuses | new work | difficulty | risk |
|---|---|---|---|---|---|
| K0 `count_fold` | `countFold_compatX` | `bang_app`; the Z-combinator run lemmas of `Core/Fix.lean`/`FoldOwn.lean`; `wpTS_bind`, host steps | induction on `n − i` over `UInt32` | small | low |
| K1 `u8` | the `w8` cases | every width-generic lemma (`vP_i32` pattern, persistence, outlives, `Imm̲`); `Stdio` at `U8` | host functions `wrap8`, `extend8_u`; backend byte slots | small (Lean), medium (backend) | low |
| K2 `slice_borrow` (Mut) | `wpTS_M_frameFam`; `sliceBorrowM_compatX` | `wpTS_M_frameX`, `vC_outlives` (6.60), `withbor2_compatX`'s structure, `sepRange_*` | the `n`-fold frame induction, generalized over the frame and the postcondition | medium | medium |
| K2 `slice_borrow` (Imm) | `wpTS_I_frameFam`; `sliceBorrowI_compatX` | `wpTS_I_frameX`, `withbor1_compatX`, `Ext` stability | `n` records in `ls`; the record-existence premise at each level | medium | medium-plus |
| K3 `slice_split`, `slice_empty` | `sliceSplit_compatX` | `vP_fam_split` (spiked), `wpTS_head` (`idx`), host steps | the term's `case`s | small | low |
| K4 `slice_get`/`slice_len` at Mut | `sliceGetM_compatX` | `arrGet_compatX`, `sepRange_pick`, `noOwn_fam` | `noOwn` at a `mut` leaf | small | low |
| K5 `slice_replace`, `slice_swap` | `sliceReplace_compatX`, `sliceSwap_compatX` | `sepRange_pick`, `sepRange_pick2`, `withswap`'s compat (6.66 at `wpTS`) | opening one or two `mut` cells inside a family; `i = j` as a no-op | small-medium | low-medium |
| F `array_realloc` | `wpTS_realloc`, `free_block` | `alloc_block`, `wpTS_tab`, `TW.free`; §13's run machinery | a new allocating head step in `Paper/`/`Support/`, with its `AHead`, `Expr.allocs` and `Alloc.ofRun` cases | medium | low-medium |
| F `buf` former | `vP_buf_iff`, 6.131 and 6.60 at `buf` | `sepRange_*`, `noOwn_fam` | a `VTy` former, about 100 arms | large | medium |

**Obligations that do not change.**

- `fundamentalC`/`fundamentalD` cover each constant by its compat lemma.
- `adequacyC`/`adequacyD`, totality and `externs_every_run` keep their statements. K0–K5 add
  no machine step, and F's `array_realloc` is the only one that would.
- Decision 21 (inverting `CDerives`) is not touched: the checker gains constants, not
  inversions.
- `write_all`/`read_into` are externs with model terms. Their contracts are FP at the model
  (`*_meets`), as SPEC §11's are.

**What might not be provable, named.** Only K2, as `wpTS_M_frameFam`/`wpTS_I_frameFam` at a
run-time `n`. I have not derived it and have not verified that any obstruction is real. The
check is the `n = 2` instance (§5.2). If it fails, the failure is at a specific premise:
`fresh`'s threshold at the inner frame, the choice of `γ`, or the rebox at the outer. The fallback is a
restricted K2 whose result `T` is persistent. The rebox is then trivial, and it still covers
P10–P12.

**What is not claimed.**

- The lowering of any of this is not proved. Lowering correctness is tested (Backend README,
  Verification).
- The UTF-8 invariant is not a theorem unless stage T2 states it.
- `write_all`'s host implementation agrees with its model on the corpus (assurance level 2).

## 7. Lowering

| construct | Wasm | LLVM |
|---|---|---|
| `slice 'a A`, `slice mut 'a A`, `array A` | `(ptr: i32, len: i32)`, two locals | `{ ptr, i64 }` (or `i32` length) |
| `buf A`, `string` (stage A) | `(ptr, cap, len)`: the array's two words and the length | `{ ptr, i64, i64 }` |
| `u8` in a slot | 1 byte: `i32.load8_u`, `i32.store8` | `i8`, `load i8`/`store i8`, `zext` |
| `slice_borrow` (K2) | nothing: the handle is passed | nothing |
| `slice_split` (K3) | `i32.le_u`, then `(p, i)`, `(p + i·s, n − i)` | `icmp ule`, `getelementptr` |
| `slice_get` | `i32.lt_u i n`, `p + i·s` | `icmp ult`, `getelementptr` |
| `iter`, `iter_mut`, `bytes` | a loop over `(p, n)`: `n` decrements, `p` advances; the length test is the loop test, with no separate bounds check | the same; LLVM keeps it as a counted loop |
| `count_fold` (K0) | a native loop (#50's fixed points) | a loop; `musttail` if expressed as calls |
| `chars` | a UTF-8 decode step: classify the lead byte by `i32.clz` of its complement, then 0–3 continuation loads | the same, or a table |
| `str_from_utf8` | a validation loop (the standard state machine); SIMD later as an optimization with a scalar fallback | the same |
| literal `"…"` | a data segment; `(addr, len)` constants | `private unnamed_addr constant [N x i8]` |
| `&"…"` | `(addr, len)`, no allocation | the same |
| `write_all` | WASI `fd_write` with one iovec `(p, n)` | `write(2)` |
| growth (stage A) | `$alloc` of the new block, a copy loop, `$free` of the old | `malloc`/`free` or our allocator, copy loop (`memcpy` after stage F) |
| `array_realloc` (F) | `$realloc`, which may extend in place | `realloc` |

**Bounds checks and their elimination.**

- Index access (`get`, `split_at`, `sub`) has one unsigned compare, and its failure is the
  sum's error branch. Nothing traps.
- Iterators have no per-element bounds check: the remaining length is the loop's state.
- The library therefore prefers iterators, and the programs in §1 use indices only where the
  algorithm is index-based (P7's sort, P8's scanner). LLVM removes some of those checks by
  range analysis. Wasm engines do not, and the compare costs about a cycle.

**`tab 0`.** Today an array of 0 elements allocates one word (`max 1 (n·s)`). Stage A buffers
use empty arrays as fillers for strings, so `n = 0` must allocate nothing: a null base, whose
`drop` frees nothing. That is a small backend change. The allocator's specification already
covers it, since nothing is allocated.

**Byte slots.** §5.6: the backend's array slot becomes the byte size of its class. That also
halves `array i32`.

## 8. Staging

Each stage lands with its SPEC entry, its proofs, its lowering, and running corpus programs from
§1, and passes `scripts/ci-local.sh`. Each stage's programs move out of `corpus/pending/` or are
added with goldens.

| # | stage | spec | kernel | programs |
|---|---|---|---|---|
| S1 | **Counted loops and bytes**: K0, K1; backend byte slots and `tab 0`; `read_byte`/`write_byte` at `u8` | §8 (a width), a new entry for K0 | K0, K1 | `pending/for-finite.bc` (total `range`), P2's digit loop over an `array u8`; `io-upper` at `u8` |
| S2 | **Cell-free borrows**: K2 at `Mut`, then at `Imm`; the §5.1 lend row for arrays | §9 (the Open item) | K2 | P12 (`pending/iter-mut.bc`, with a core iterator until S4) |
| S3 | **Split and writes**: K3, K4, K5; `lib/slice.bc` | §9 | K3–K5 | P10 (with `iter_mut` in core), a sort of `array i32` (P7's shape) |
| S4 | **Iterators and total `for`** over views: `iter`, `iter_mut`, `bytes`, `range`; `for` over a bounded source is K0 (typed elaboration stage 9, revised) | §7 (instances), §14 (bounded `for` is total) | none | P12 as written, P10 as written, `pending/print-borrowed-list.bc`'s array analogue |
| S5 | **Buffers and text**: `lib/buf.bc` (stage A), `lib/text.bc`, literals (`lit`, `lit_view`, backend read-only data), `write_all`/`read_into` externs; `box buf/string/array`; capability-threading borrow blocks | a new entry: text library, and the literal lowering; §11 (two externs) | none | P1–P9, P11, P13 |
| S6 | **Surface prerequisites** used throughout, from typed elaboration: `fn f<'a>`, `data` values without `box` and with lifetime parameters | typed elaboration §5.3 | none | P2, P8 with `data` |
| T2 | **Enforced text**: `string`, `str`, `str mut`, `char` as opaque types (#63); optionally a Lean statement that the text library preserves `Utf8Valid` | module entry (#63) | none | a reject: bytes passed as `str` |
| F | **Zero-cost growth**, when a program or the counts need it: `array_realloc`, then a `buf` former with an uninitialised tail | §9 | step, former | a `buf (box T)` program; allocation and fill counts |
| C | **C boundary** with the LLVM backend: `with_cstr`, `terminate`, `cstr 'a` in extern contracts | §11 | none | P15 |

P14 (`args`) waits for the `Args` capability (SPEC §11, designed), and runs at S5 once `Args`
exists.

**Issue mapping.**

- **#8** (closed; its text still describes `Buf`/`Str` as externs with same-lifetime views
  justified by the extern) is superseded. §9 withdrew the extern design, and this note replaces
  it with library code over §9 and K0–K5. Nothing of #8's design survives. Its "unblocks sieve,
  queens, … strings/IO corpus" is S3–S5. Suggest a closing comment pointing here.
- **#57** is split.
  - The array half is S2–S4: `iter`/`iter_mut` over views, and the `mut` family it needs.
  - The list half, a borrowed list iterator through `withload` per node or `[@d] U(νX. C)`,
    remains open and is unchanged by this design.
  - #57's `iter_mut` "if the same route works" is answered: for arrays it is a different route
    (K2), and for lists it stays open.
- **#77** is independent. Strings use `tab`, which is contiguous on every run. #77's block
  primitive for records and F's `array_realloc` are the same kind of step and could share a
  change.
- **#94** changes scope. Its "array helpers (get/set/fill/iterate)" become `lib/slice.bc` at
  S3–S4, over views rather than owned arrays. `Arena`/`Id` is unaffected, and #94 becomes where
  S3's library lands.
- **Stage 8 (`data`/`box`)** gains:
  - `box` spellings for `array`/`buf`/`string` allocation (or S5 adds them);
  - `data` values without `box` for non-recursive variants (P2, P8), which today's stage 8
    text makes an error ("`Cons(x, t)` without `box` is an error");
  - `data` with lifetime parameters (P8).

  Q5 asks which.
- **Stage 9 (finite `for`)** is revised by S4: the bound is K0, not a unary fold. Built.
- **#9** (a `!` closure capturing an `i32`) is not needed. K0's step and every `for` thread their
  state instead of capturing it.
- **#63** (modules and opaque types) is where the UTF-8 invariant becomes enforced (T2).
- **#18** (error effect) is where every `A + E` result marked `-- #18` changes.
  `raise-in-fold.bc` is the same question.

## 9. Coherence

| choice | follows from | notes |
|---|---|---|
| no RC, no `Rc<str>`; strings freed by destructors | no GC or RC; decision 23 | shared strings are arena indices (#94) |
| `box` at every allocation site | heap allocation is explicit | growth inside `push` is the exception (Q2) |
| `str mut` allows only UTF-8-preserving writes; no shared mutable text | no interior mutability | |
| `&`, `borrow`, `for`, literals, capability threading are elaboration | sugar is elaboration only; decisions 26, 33, 37, 38 | the §5.1 table gains one row |
| K0–K5 each have a SPEC entry and a compat lemma; no `CDerives` index; no new `VTy` former until F | kernel changes need a spec entry and a proof; decisions 19–21 | F's former is the one place the growth rule's cost is paid, and only on demand |
| views are `(ptr, len)`, `buf` is `(ptr, cap, len)`, byte slots, no headers or per-element cells; iterators without bounds checks | zero-cost | stage A's zero-fill on growth, and the element-move loop, are the known deviations until F |
| every lowering has a Wasm and an LLVM counterpart; no WASI-only semantics | portable lowerings; decision 25 | `write_all` is `fd_write` or `write(2)` |
| I/O through capabilities; `write_all`/`read_into` take `mut` borrows of them | capabilities for I/O; decision 30 | |
| `A + E` results, marked `-- #18` | errors are an effect, not yet built | |
| arrays remain the one run-time family former; slices are its borrowed leaves | decision 29 | K2 fills the `mut` leaf that decision 29 left open |
| literals as persistent data, viewed by a scoped lend | the user's input on `&'static` | its scope limit is Q4 |

**Outside the standing commitments, stated.**

- **The literal lowering** (§5.7) relies on an observational claim, "a never-written, promptly
  freed copy is the same as a pointer into read-only data". It is tested, not proved.
- **Stage A's `buf` is not strictly zero-cost** (the fill), and it cannot hold element types
  without a filler.
- **Owned text costs a capacity word** where Rust's `Box<str>` would not.
- **C strings cost a copy per call** where Rust can cache a `CString`.

## 10. Open questions for the user

1. **Spellings.**
   - `slice 'a A`/`slice mut 'a A` for views, or `view`?
   - `str mut 'a`?
   - `box buf(cap)` and `box string(cap)` for allocation?
   - `b'x'` for a `u8` literal and `'x'` for a scalar value?
2. **Growth and visibility.** Should `push` reallocate implicitly, as Rust does? Or should
   growth be explicit (`push` returns the element back when full, and `grow` allocates)? Or
   should it wait for `noalloc`?
3. **Stage A before F.** Is the zero-fill of stage A acceptable until a program needs
   uninitialised capacity? The alternative is to build F's `buf` former first, at about
   100 arms.
4. **Literal views.** Scoped lends (no kernel change, §5.7), or a static region of
   `[Imm ⊤ U8]` families, which gives unscoped literal views and changes adequacy's statement
   to start and end at the static memory?
5. **`data` values.** Should stage 8 allow `data` constructors without `box` for non-recursive
   types (P2's `ParseErr`, P8's `Tok`), and `data` with lifetime parameters?
6. **`char`.** An `i32` scalar value from `chars` until #63, or a nominal `char` sooner?
7. **The error effect.** Every text function returning `A + E` would change when #18 lands. Should
   S5 wait for #18, or land with sums and change later?

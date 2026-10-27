# `let mut` as a place in the borrow calculus (#626)

The question (#626, the user's direction of 2026-10-20): `let mut` goes through the borrow
calculus. This unit designs how, builds it behind a flag (`BCC_MUT=place`), and measures it
against the threading elaboration of SPEC §41. Nothing is switched over.

The prototype is on branch `mut-place` (PR #631, closed unmerged). Its SPEC entry and the
flagged code are there, not on main; `scripts/mut-place-measure.sh` runs on that branch. The
follow-up is #632 (frames with typed exits).

Claims are marked **measured** (a run, with the command in §9), **by inspection** (read off the
code or SPEC, cited), or **hypothesis**.

## 0. Summary

- **The model.** `let mut x = e; N` is a cell lent `mut` over its scope:
  `borrow mut alloc(e) { x -> N }`, the cell freed after. `x` names the borrow (the place's
  *token*, `mut 'x A`). A read of `x` is a load (`withswap` with a copy), `x = e` is a store
  (`withswap` whose callback is `e`), `let (x, q) = f(…, x, …)` is one swap, and every lend of `x`
  is a reborrow (`withbor3`) or a lend of its content through its swap. The kernel decides every
  aliasing, mutation, extent and escape question: no rule of the place elaboration refuses
  anything (§2).
- **What the kernel cannot do without a join.** A `mut` borrow is linear (`two-mut.bc`): every
  operation on it hands it back. So in the kernel as it is, a place's token is still handed on
  through arms, heads and loop turns. What changes is *what* is joined: one linear token whose
  value is always the same place, checked by the kernel's linearity, instead of a set of values
  computed by R2. A join the elaboration gets wrong is now a refusal ("used twice", "consumed in
  one arm"), never a stale value: **0 wrong answers** in 374 corpus programs and 2,400 generated
  ones (measured, §5). "No join" literally needs a kernel former (§6, K1).
- **Measured** (`BCC_MUT=place`, the library threaded, §5):
  - corpus: 237 of 374 programs run with their goldens, **0 differ**, 137 are refused. Of the 209
    programs that write `let mut`, 74 run and 135 are refused.
  - `scripts/mut-combos.py --gate`: **0 differences** in 600 programs (and in 1,800 more on
    seeds 1–3); 396 refused: A1 201, A2 102, B2 49, A4 43, B1 1 (§5.3, §7).
  - the #504/#586/#590 programs: every accepted one gives the threaded answer;
    `reject/mut-stored-thunk.bc`, which R3 refuses, **runs and answers `i32[52]`, the right
    answer** (§5.4).
  - the target pairs: 6 of 9 answer as their targets (the other three are refused by kernel
    rules, §5.1).
  - renaming check: 1 difference in 629, between two refusals of one program (§5.5).
  - counts: 73 of the accepted programs count more than `counts.expected` (41 allocate more, all
    load and store more); 1 of the 74 accepted `let mut` programs counts as expected. The place
    is a frame slot only when its scope is one lend; promotion to a native local is not built
    (§4).
- **Refusals** (§7): the borrow rules refuse four classes, each with a fix inside the calculus:
  A1 a resuming operation inside a place's scope (T1, 21 programs); A2 a `!` closure capturing a
  place (2 corpus, most of combos' refusals); A3 a read that moves a linear content out of a
  place (56); A4 a `let mut` that holds a cell (2). The other 56 are gaps of the prototype's
  plumbing (type synthesis through the place's block, loop stretches), not borrow refusals.
- **Kernel needs** (§6): none for the prototype. K1 (a derived "frame" computation type, so the
  elaborator performs no join) costs derived rules and their compatibility lemmas, no FP or
  adequacy re-proof. K2 (holes: a place moved out of and filled again) is a value-type former
  with a relation clause. K3 (`!` closures over `imm` borrows) is #58. K4 (a place across a
  resumption) is T1/#172's question.
- **STOP: KERNEL WORK findings** (§8). Under the standing rule merged in #627, the current R3 has
  two parts that are kernel work: the callee copy that passes a block's writes in and out
  (`Effects.mutCap`, so a `!` closure "writes"), and the escape refusal (`Effects.escapingWriter`,
  a refusal on borrow grounds). The place model needs neither, and the prototype bypasses both.
  The prototype extends LoopLend (§14's per-observation lend) for nested places and loop exits;
  LoopLend itself decides lend extents so that a loop the kernel cannot hold a borrow across gets
  through, which the rule names. Both are flagged for the user's decision (§8).
- **Deletable on a switch-over** (§10): R3's In (`mutCap`, `blockKeys`, the `ap__x` copies),
  `escapingWriter`, the `writes` marks, the in-place `modify` of a `let mut` value, and the
  value branch of `lendBorrow` for `let mut`s. R2's write sets stay, as the set of places a
  construct touches, until K1.

## 1. The model

A `let mut x = e` of a surface body introduces a place whose storage is a cell and whose name is
the borrow of that cell for the place's scope:

    let mut x = e; N      ⟶      let (c, q) = borrow mut alloc(e) { x -> N }; free(c); …

The borrow is `withbor2` of a fresh cell, `x : mut 'x A`. That is §35's scoped cell exactly: the
lend of a fresh cell whose owner is freed after it, which the backend places in a frame slot
(`Backend/Clos/Convert.lean`, `markScoped`). No allocation is written and none is made when the
scope is one lend.

Inside `N`, `x` is used only through the kernel's constants:

| use | kernel term | note |
|---|---|---|
| a read `x` (persistent `A`) | `withswap x (v -> (v, v))`, a load | for a linear `A` the copy is refused by the kernel: "`v` is used twice" |
| a read `clone(x)` | `withswap x (v -> (v, clone(v)))` | |
| `x = e` | `withswap x (o -> e[o/x])`, a store; `e` reads `x` as the old content `o` | `x = push(x, 1)` of a linear content is one swap |
| `x <- M` | `t <- M; x = t` | |
| `let (x, q) = f(…, x, …)` | `q <- withswap x (o -> f(…, o, …))` | the threading API's rebinding call is one swap |
| `f(&mut x)` at a `mut 'a A` parameter | `withbor3 x (m -> f(m))`, a reborrow | |
| `f(&x)`, `f(&mut x)` at any other parameter | `withswap x (v -> f(&v), handing v back)` | the content swapped out, lent as a value by the existing rules (a scoped cell, a slice borrow, an owned parameter), swapped back |
| `borrow mut x { m -> S }` of a cell-like content | `withbor3` | |
| `borrow k x { v -> S }` of an array, a buffer, or `imm` | `withswap x (a -> borrow k a { v -> S })` | the value's borrow rules (§9, §36) |
| `modify x { v -> S }`, `modify &mut x { … }` | `withswap x (v -> S)` | §41's "a `let mut` value is no place" is gone |
| the scope's last value `V` | evaluated after the lend: `V[free(c)/x]` | a linear content is moved out at the end by the `free` (`let mut acc = nil(); …; acc`) |

The kernel then decides, with its proved rules:

- **aliasing and mutation**: the token is linear, so two live uses of a place are "used twice";
  a callback that holds the token while another use needs it is refused the same way;
- **escape**: a closure or result that keeps the token past the place's scope mentions `'x`,
  which `withbor2`'s `'x ∉ FV(B)` refuses ("has the block's lifetime");
- **extent**: the lend is the scope of the `let mut` (lexical, as SPEC §14's decision 40 makes
  `let r = &mut x`); a call's lend is the call.

## 2. Joins: what the kernel can and cannot express

`mut 'x A` is linear in the kernel (`corpus/reject/two-mut.bc`): `withswap` takes the borrow and
hands it back (`mut @a A => (A => A * B) => mut @a A * B`, syntax-core §8). A case's arms share
their linear context, but what follows the case needs the borrow back, so an arm that uses the
place returns it. A loop turn returns it in the loop's state. A callback (a borrow block's,
`modify`'s, `with`'s) returns it beside its result.

So in the kernel as it is, **a place in a construct that runs code in another frame is handed on
by that construct**. The prototype does this with R2 and R3's hand-on machinery (`handOn`,
`joinBind`), with the place's token as the variable handed on. Two differences from §41's
threading of values make this a different thing, not a renaming:

1. **What is handed on is a token, not a value.** A token is the same place wherever it goes; it
   has no stale copy. If the elaboration fails to hand it on, the next use is "used twice" or
   the arms disagree ("consumed in the `inl` arm but not in the `inr` arm"): the kernel refuses.
   Under value threading a lost hand-on reads the old value silently (#504, #586, #590, §41).
2. **Nothing is decided by the hand-on.** R3's In (a block's writes as parameters of the callee's
   copy) and the escape refusal are not used for places: a closure that uses a place captures
   its token, and the kernel types the closure (§8).

The hand-on is the insertion of the token's return, the same kind of insertion as `f(&mut x)`'s
`let (x, r) = io_lend` (SPEC §11, `Comp.elab`), which the standing rule lists as in scope. A
literal "the elaborator performs no join" needs the join in the kernel: K1 (§6) makes it a
derived computation type, so that `case`, `bind` and the loops of the frame compose without a
hand-on in the elaboration.

## 3. The rule table

One rule per construct, the place `x` declared outside it. "touches" is R2's write set read as
the set of places the construct uses (a read is a use of the token).

| construct | the place elaboration |
|---|---|
| `let mut x = e; N` | `borrow mut alloc(e) { x -> N' }`, `N'` = `N` without its last value; the cell freed; the last value read after (§1) |
| a read `x` in a value | a load, bound before the construct whose value reads it, in evaluation order (`placeLoads`); a call whose argument is a closure over `x` is bound at its place among the loads |
| a read in a `run` of an expression (`a && b`) that only reads `x` | the load before the expression (a load has no effect) |
| a read in a `run` that writes `x` | a load where the `run` reads it; the `run` hands `x` back (R3) |
| a read in a `while`'s condition | the loop is `loop { if c { body } else { break } }`, so the condition loads at each turn |
| a binding's head that begins with loads | the loads before the binding (`peelLoads`), so the token they rebind reaches what follows |
| `x = e`, `x <- M`, `let (x, q) = f(…, x, …)` | a store or a swap (§1) |
| `&mut x`, `&x`, `borrow k x`, `modify x` | a reborrow or the content lent through the swap (§1) |
| `if`, `match` (statement and head), a loop turn, a borrow block, `with`, `modify`, `run` | R2 and R3's hand-on of each place it touches (§2) |
| a closure that uses `x` | captures the token; no `writes` mark, no copy of the callee |
| a `for`, `while`, `loop` that is div, inside the place's scope | §14's per-observation lend (LoopLend): the cell moves into the loop's state and each turn lends it; nested places are split innermost first; a turn that exits (`break`, `continue`, `return`) is split at the exit (§8) |
| a capability (`stdin`, …), a handler's `mut` parameter, core text | unchanged: not places |

## 4. Lowering

**What exists.** A place whose scope is one lend is §35's scoped cell, a frame slot (measured:
`allocs 0` for `mut-for-acc`, `mut-heads`, `mut-shadow`, …). The slot's `load` and `store` are
counted (`corpus/counts.expected` counts frame-slot traffic), so every accepted place program
loads and stores more than its threaded build: 210,704 loads against 199,665 and 193,063
stores against 182,024 over the 73 programs whose counts differ (measured).

**What allocates.** 41 programs allocate more (measured). A place whose scope holds a div loop
is lent per observation (LoopLend): the cell is lent at each turn, so it is not one lend, and
`markScoped` leaves it a heap cell. A place across a suspension would be one too (§35, *A
suspension inside a scope*), but those are refused (A1).

**Native.** LLVM at `-O2` does not remove them. The optimised IR's loads, stores and allocation
calls (static counts, measured, §9):

| program | threaded | place |
|---|---|---|
| `0070-climbing-stairs` | 10 / 18 / 4 | 18 / 25 / 7 |
| `0198-house-robber` | 10 / 36 / 5 | 18 / 46 / 8 |
| `0371-sum-of-two-integers` | 8 / 12 / 3 | 19 / 23 / 8 |
| `io-break` | 4 / 1 / 0 | 9 / 7 / 4 |
| `mut-while-flag` | 1 / 0 / 0 | 4 / 4 / 3 |
| `mut-for-acc` | 1 / 0 / 0 | 1 / 0 / 0 |

Where the place is one lend in straight-line code and a counted loop (`mut-for-acc`), LLVM
promotes the slot and the IR is the threaded one. Where the place's cell is lent per observation
of a div loop, it is a heap cell passed through the loop's state, which LLVM cannot promote.

**What is needed** (not built; a backend unit):

- **L1, a frame slot that no other code addresses becomes a local.** At the flat IR (and LIR's
  storage rule, `docs/compiler.md` §3.3: "a local variable when the handler's scope is one
  code, or a frame slot whose address is passed"), a slot whose address is only the operand of
  `load`/`store` in its own code is a variable: a Wasm `local`, a C local, an SSA value. The fact
  is read off the checked term: the slot is a scoped cell (`markScoped`), and the borrow's
  lifetime is the token's; nothing else holds `'x`.
- **L2, a cell lent per observation lives in the loop's state by value.** LoopLend's owner is in
  the loop's state and lent inside each turn only; the state holds the content, and each turn's
  lend is a slot of the turn's code (then L1). The fact is in the term: the owner is used only by
  `withbor` per turn and the final `free`.
- **The check** (a gate step, `scripts/check-promotion.sh`, proposed): every corpus program
  counts under `BCC_MUT=place` exactly what its threaded build counts (allocations, loads,
  stores). A place left in memory is then a count above the threaded one, by program. A second
  check on the native target: the optimised IR of each program has no `alloca` of a place
  (`bcc compile --target native`, `-O2`).

L1 and L2 are where the user's "a reliable pass is fine" applies. They are not recovery passes in
the sense of the standing rule ("no hand-rolled passes that recover what an earlier stage
lost"): the term says the cell is the place, and the lowering decides where a place lives, as
§35 already does for scoped cells.

## 5. Measurements

### 5.1 The target pairs

`BCC_MUT=place BCC_MUT_LIB=thread bcc interp` (measured):

| pair | threaded | place |
|---|---|---|
| `mut-for-acc` | `i32[10]` | `i32[10]` |
| `mut-heads` | `i32[5120]` | `i32[5120]` |
| `mut-modify` | `(i32[6], i32[7])` | `(i32[6], i32[7])` |
| `mut-shadow` | `i32[3]` | `i32[3]` |
| `mut-while-flag` | `(i32[5], inr ())` | `(i32[5], inr ())` |
| `mut-block` | `i32[52]` | refused, A2: the block given to `ap(f: !(i32 => i32))` captures `x`'s token; `!thunk` promotes only over `!` types |
| `mut-await` | `i32[111]` | refused, A1: `await` resumes inside `acc`'s scope |
| `mut-yield` | `i32[12]` | refused, A1: `yield` resumes inside `sum`'s scope |
| `mut-service` | `(i32[10], i32[6])` | refused, A4: `let mut c = alloc(0)` is a place holding a cell; `with summing(&mut c)` wants the cell's borrow |

The pairs' cores are the threaded elaboration; the place elaboration's core differs by design,
so their erasures are not compared.

### 5.2 The corpus

`scripts/mut-place-measure.sh` (measured): every program `compile-corpus.sh` runs, elaborated
with `BCC_MUT=place`, run in WebAssembly and compared with its goldens; then `bcc-counts`.

| library | same as golden | wrong answer | refused | counts as expected |
|---|---|---|---|---|
| threaded (`BCC_MUT_LIB=thread`) | 237 | **0** | 137 | 164 |
| places too | 191 | **0** | 183 | — |

With the library as places, 46 more programs are refused, every one at a library function that
threads a linear value by moving it out of a `let mut` and assigning it again: `textio`'s
`read_all` (`let (c2, (s2, more)) = read_chunk(c, s); c = c2; s = s2`, 34 programs), `async`'s
`rev`/`rev_in` (`match unroll cur { … cur = r }`), and three others (A3a).

Of the 374 programs, 209 write `let mut` themselves. Of those, 74 run under the place model and
135 are refused (§7); 1 of the 74 counts as expected (§4).

### 5.3 `scripts/mut-combos.py --gate`

| row | agree | differ | refused | the refusals, by class (§7) |
|---|---|---|---|---|
| `joins` | 84 | **0** | 116 | A1 116: the program's `pause` resumes inside the places' scope |
| `frames` | 50 | **0** | 150 | A1 59, B2 49 (the control `with`), A2 26 (blocks at `ap`'s `!` parameter), A4 16 (`let mut cell = alloc(…)`) |
| `loops` | 70 | **0** | 130 | A2 76, A4 27, A1 26 (a `for` over a generator), B1 1 |

Seeds 1, 2 and 3 (1,800 programs): **0 differences** (measured). The gate's requirement (no
refusal) does not hold under the place model: the refusals are the classes of §7. The check found
one real fault of the prototype on the way (a `run` that writes a place had its reads hoisted out
of it; fixed, `c85`/`c159`).

### 5.4 The bug programs of #504, #586, #590

| program | threaded | place |
|---|---|---|
| `mut-shadow-arms` | `(2, (3, (4, 6)))` | same |
| `fail/mut-shadow-assign`, `-loop` | refused (R1) | same refusal |
| `loop-shadow-persistent` | `(1, 3)` | same |
| `mut-bind-arm` | `(5, 3)` | same |
| `loop-shadow-linear` | `6` | refused, A3b (an `imm` view read twice) |
| `lend-shadow`, `name-clash`, `mut-run`, `mut-lend-arm`, `for-in-if-lend`, `generated-names` | as golden | same |
| `mut-block`, `mut-block-nested` | as golden | refused, A2 |
| `fail/mut-run-nested` | refused (R3) | same refusal |
| `reject/mut-stored-thunk` | refused (`escapingWriter`) | **`i32[52]`**: the stored block captures the token, is forced while the scope is open, and the write lands in the place |
| `mut-modify` | `((6, 7), 120)` | refused, A4 |
| `reject/mut-control-with` | refused | same refusal (B2) |
| `loop-shadow-owner`, `mut-name-capture` | as golden | refused only with the library as places (`read_all`) |

No accepted program gives a different answer.

### 5.5 The renaming check

`BCC_MUT=place BCC_MUT_LIB=thread scripts/alpha-check.py` (measured): 629 programs, 1 difference:
`aoc/2024-11.bc`, refused in both forms with different messages (a gap of B1). The first run found
7 more, all one fault of the prototype (a place's rebinding call did not record what its binder
resolves to); fixed.

## 6. Kernel needs

None for the prototype: every term it writes is a kernel term the checker derives.

**K1. The frame as a derived computation type (for "no join").** Proposed entry:
`St Π C ≜ Π ⊸ C ⊗ Π`-shaped derived forms over the tuple `Π` of the frame's tokens, with derived
rules `stRet`, `stBind`, `stCase`, `stLoad`, `stStore`, `stLend` (a reborrow of one component)
and `stIterate`. The elaborator writes `stCase` where it writes a case, and the derived rule
threads `Π`: no hand-on in the elaboration, and R2's write sets go. Cost: derived rules, each
proved from existing rules (as `Core/AffRules.lean` derives `Aff`'s), so `fundamentalC` and
`adequacyC` cover them unchanged; no index on `CDerives` (growth rule 19 is kept by making `Π` a
type, not a context). Estimate (hypothesis): seven derived rules, a few hundred lines in `Core/`.

**K2. Holes.** A linear content moved out of a place and filled again (A3a) needs the place to
be empty in between. Two forms:
- a value-type former `out @a A`, a `mut` borrow of an uninitialised cell, with
  `take : mut @a A ⊸ A ⊗ out @a A` and `put : out @a A ⊸ A ⊸ mut @a A`. Cost: a `VTy` former
  (about 100 match arms by `CLAUDE.md`'s count), a relation clause (an owned location holding
  nothing, as `Unk`'s), and `fundamentalC`'s new cases; adequacy unchanged.
- no kernel change: a place of a linear type is `A + 1` (Rust's drop flag, but always on), a
  tag word and a check at each use.
The cheaper path for the corpus is the lend form the language already has: `push(&mut stack, b)`
for `let (s, _) = push(stack, b); stack = s` (§7).

**K3. `!` closures over `imm` borrows** (#58, E1). A closure that reads a place takes `&x` for
its extent; a `!` closure cannot capture an `imm` borrow today ("`!thunk` promotes only over `!`
types"). One rule (`!` promotion over `imm 'a A` at a lifetime bound) and its compatibility
lemma. The alternative with no kernel change is a decision, not a need: a reading closure
captures a copy of a persistent content (Rust's `move` of a `Copy` value).

**K4. A place across a resumption** (T1, #172). A borrow is not held across a resuming
operation, so a place's scope may not contain one. The kernel's existing answer is R1 under
`PinLaw` (SPEC §29), which admits only operations answering `1` and a body that sees only the
borrow. For a place, what crosses the resumption need not be the borrow: the cell can (§35's
heap cell, or the state machine's state). The form that needs no new kernel rule is the
per-segment lend: the place's lend ends before each resuming operation and begins again after,
the cell crossing, as LoopLend does at a loop turn. That is an extent the elaboration chooses,
which §8 puts to the user.

## 7. Refusals and their fixes

The full list is the appendix. Classes, with the library threaded (measured):

| class | programs | why | the fix inside the calculus |
|---|---|---|---|
| **A1** a resuming operation inside a place's scope | 21 (`async-*`, `gen-*`, `for-yield-*`, `block-yield-inner`, …) | T1: a borrow held across a resumption (#172) | the per-segment lend (K4), or keep the place's cell in the suspended state (pinned, §35 *Open*) |
| **A2** a `!` closure that uses a place | 2 (`mut-block`, `mut-block-nested`); most of combos' `block` refusals | the closure captures the linear token | a closure that writes is `Aff` (SPEC §22, exists): callees that call a block repeatedly take `Aff[A, B]<'c>`; one that only reads takes K3 or a copy |
| **A3a** a read that moves a linear content out | 40 | no hole in a `mut` borrow | the lend form (`f(&mut x)`), `replace`; or K2 |
| **A3b** an `imm` view read twice | 16 | views are copied only by `copy`/`array_copy` | #58's implicit copy of `imm` borrows; or the load copies a view by `copy` (a decision) |
| **A4** `let mut c = alloc(…)` | 2 (`mut-modify`, `effects-log-fail`; the pair `mut-service` too); 43 in combos | the place holds a cell, the program wants the cell | write `let c = alloc(…)` (a cell is a place already) or `let mut c = 0` (the place) |
| **B1** the type of the place's block | 26 | the block's body does not synthesise its type and the scope's expected type is not passed in every case | prototype plumbing: pass the expected type through the scope's bindings |
| **B2** a control handler's body that uses a place | 7 | the existing R3 refusal (`Effects.withCtl`) | lend the places to the body as §34 lends capabilities ("reborrowed for it … so that they come back when the body is abandoned") |
| **B3**, **B4**, **B6** stretches of a lent loop | 13 | a capability or a token not handed on by a stretch of LoopLend's split | prototype plumbing in `Env.exitBody` |
| **B5** other | 10 | inference gaps through the place's block; an internal error at two sites | prototype plumbing |

The A classes are the borrow rules refusing; each fix is a library signature, a kernel rule or
the lend form. The B classes are this prototype's elaboration not yet doing what it should; none
is a reason the model fails.

## 8. Standing-rule audit (`STOP: KERNEL WORK`, #627)

Reported, not acted on:

- **R3's In is kernel work.** A block that writes a `let mut` is given at a `!` parameter by
  copying the callee (`ap__x`) with the writes as parameters (`Effects.mutCap`): it threads state
  so that a `!` closure that writes, which the kernel cannot express, gets through. The place
  model does not use it: the closure captures the token and the kernel refuses (A2).
- **`Effects.escapingWriter` is a refusal on borrow grounds.** The place model leaves escape to
  `withbor2`'s side condition; `reject/mut-stored-thunk.bc` then runs, correctly (§5.4).
- **LoopLend decides extents.** §14's per-observation lend (`Frontend/Elab/LoopLend.lean`,
  decision 40) rewrites a borrow block over a div loop into one lend per turn, so that a loop the
  kernel cannot hold one borrow across gets through. Each lend it writes is checked, and its
  soundness argument is the per-observation lend of `lib/lend.bc` and `experiments/LoopBorrow`,
  but the extent is the elaborator's. The prototype extends it, behind the flag: nested blocks
  over one loop are split innermost first (`lendBind`'s `preSplit`), and a turn that exits is
  split at the exit (`Env.exitBody`). Whether LoopLend stays, or becomes a kernel derived rule
  (an `iterate` that lends a cell at each observation, proved once), is the user's call.
- **The prototype's own rules** decide nothing the kernel decides: they insert loads, stores,
  swaps and the token's hand-on, and choose the place's lend as the scope of its `let mut`
  (lexical, the construct's meaning). Swapping a place's content out to lend it as a value
  (`f(&x)` at an `imm` parameter) is an insertion the kernel checks: the token is held by the
  swap, so nothing else can use the place during the call.

## 9. Reproduction

- the flag: `BCC_MUT=place` (all `let mut`s, the library's included); `BCC_MUT_LIB=thread` keeps
  the library's threaded.
- corpus: `BCC_MUT_LIB=thread scripts/mut-place-measure.sh` and `scripts/mut-place-measure.sh`.
- combos: `BCC_MUT=place BCC_MUT_LIB=thread scripts/mut-combos.py --gate [--seed N]`.
- renaming: `BCC_MUT=place BCC_MUT_LIB=thread scripts/alpha-check.py`.
- native: `bcc compile --target native f.bc -o f.ll` with and without the flag, then
  `clang -O2 -S -emit-llvm`, counting `load`, `store`, `alloca` and allocation calls.

## 10. What a switch-over deletes

On switching (the user's call; nothing is deleted in this unit):

| code | why it goes |
|---|---|
| `Effects.mutCap`, `blockKeys`, the `m0`/`m1` keys, the callee copies for writes (SPEC §41 R3 *In*) | a closure captures the token; the kernel types it |
| `Effects.escapingWriter` and its two call sites | escape is `withbor2`'s side condition |
| `VSugar.writes`, `writesOf`, the `writes(…)` printed form and its parser case | no closure is marked |
| `Sugar`'s in-place `modify` of a `let mut` value (`io_mu`, SPEC §41 *A `let mut` value is no place*) | a place is a place |
| `lendBorrow`'s value branch for `let mut`s, and ergonomics N1 (borrowing a `let mut` value outside a call) | `&x` of a place is its reborrow or swap |
| `checkRun`'s refusal of a writing `run` in an expression | stays until the expression's calls are lifted in order (SPEC §41 *Open*) |
| R2's write sets (`frame`, `assigned`) | stay, as the places a construct touches, until K1 |
| R1 | stays |

## 11. Decision menu

1. **Adopt the place model as the meaning of `let mut`** (switch the default to it), with the
   A-class refusals as language changes:
   a. A2: callees that call a writing block take `Aff`; or keep R3's copy (kernel work).
   b. A3: the lend form in the corpus and the library (`push(&mut s, b)`), plus K2 (holes) or the
      `A + 1` form for what remains.
   c. A1: the per-segment lend at a resuming operation (an elaborator extent, like LoopLend), or
      places in the suspended state (`PinLaw`-style assurance, or #172's answer).
2. **K1, the frame type**, so that the elaborator performs no join and R2 goes. Derived rules
   only.
3. **Reading closures**: `&x` with K3 (Rust's `Fn`), or a copy of a persistent content (Rust's
   `move`).
4. **Lowering**: L1 and L2 with the promotion check (§4) before the switch, so that the counts
   stay where they are.
5. **LoopLend**: keep it as the elaborator's per-observation lend, or make it a kernel derived
   rule.
6. **Keep threading** (the current §41) and close #626 with this record. The user's direction
   rules this out as the end state; it stays the default until 1–5 are decided.

## Appendix: every refused corpus program (`BCC_MUT=place`, the library threaded)

#### A1 resuming operation inside a place scope (T1) (21)

| program | the refusal |
|---|---|
| `async-bank-inbox.bc` | 47:5: this borrow block's body performs the operation 2.0, which resumes: only an abortive operation crosses a borrow's scope (a continuation held across a lend is T1,… |
| `async-lend-slots.bc` | 22:3: this borrow block's body performs the operation 1.0, which resumes: only an abortive operation crosses a borrow's scope (a continuation held across a lend is T1,… |
| `async-scheduler.bc` | 20:3: this borrow block's body performs the operation 1.0, which resumes: only an abortive operation crosses a borrow's scope (a continuation held across a lend is T1,… |
| `async-timers.bc` | 42:3: this borrow block's body performs the operation 3.0, which resumes: only an abortive operation crosses a borrow's scope (a continuation held across a lend is T1,… |
| `async-workers-scoped.bc` | 19:3: this borrow block's body performs the operation 3.0, which resumes: only an abortive operation crosses a borrow's scope (a continuation held across a lend is T1,… |
| `block-yield-inner.bc` | 12:3: this borrow block's body uses `fx_w1`, which is outside it, and performs the operation 1.0, which resumes: a borrow held across a resumption sees only its view (… |
| `for-never.bc` | 11:3: this borrow block's body uses `fx_w1`, which is outside it, and performs the operation 1.0, which resumes: a borrow held across a resumption sees only its view (… |
| `for-yield-branch.bc` | 15:3: this borrow block's body uses `fx_w1`, which is outside it, and performs the operation 1.0, which resumes: a borrow held across a resumption sees only its view (… |
| `gen-borrowed.bc` | 20:3: this borrow block's body uses `e`, which is outside it, and performs the operation 2.0, which resumes: a borrow held across a resumption sees only its view (R1, … |
| `gen-cell.bc` | 14:3: this borrow block's body uses `c`, which is outside it, and performs the operation 1.0, which resumes: a borrow held across a resumption sees only its view (R1, … |
| `gen-close.bc` | 19:3: this borrow block's body uses `io_m4`, which is outside it, and performs the operation 2.0, which resumes: a borrow held across a resumption sees only its view (… |
| `gen-fib.bc` | 17:3: this borrow block's body uses `a`, which is outside it, and performs the operation 2.0, which resumes: a borrow held across a resumption sees only its view (R1, … |
| `gen-from.bc` | 17:3: this borrow block's body uses `fx_w1`, which is outside it, and performs the operation 1.0, which resumes: a borrow held across a resumption sees only its view (… |
| `gen-nested.bc` | 12:3: this borrow block's body uses `fx_w2`, which is outside it, and performs the operation 2.0, which resumes: a borrow held across a resumption sees only its view (… |
| `gen-return.bc` | 22:5: this borrow block's body uses `fx_w1`, which is outside it, and performs the operation 1.0, which resumes: a borrow held across a resumption sees only its view (… |
| `gen-tokenize-parse.bc` | 31:3: this borrow block's body performs the operation 3.0, which resumes: only an abortive operation crosses a borrow's scope (a continuation held across a lend is T1,… |
| `gen-value.bc` | 17:3: this borrow block's body uses `fx_w1`, which is outside it, and performs the operation 1.0, which resumes: a borrow held across a resumption sees only its view (… |
| `lend-div.bc` | 27:3: this borrow block's body uses `fx_w1`, which is outside it, and performs the operation 1.0, which resumes: a borrow held across a resumption sees only its view (… |
| `loop-row-answer.bc` | 17:3: this borrow block's body performs the operation 1.0, which resumes: only an abortive operation crosses a borrow's scope (a continuation held across a lend is T1,… |
| `reconcile-chain.bc` | 75:3: this borrow block's body performs the operation 3.0, which resumes: only an abortive operation crosses a borrow's scope (a continuation held across a lend is T1,… |
| `reconcile-clock.bc` | 63:3: this borrow block's body performs the operation 1.0, which resumes: only an abortive operation crosses a borrow's scope (a continuation held across a lend is T1,… |

#### A2 a ! closure capturing a place (2)

| program | the refusal |
|---|---|
| `mut-block-nested.bc` | 9:33: `!thunk` promotes only over `!` types, but `x`, of type `mut 'io_l8 i32`, is used inside |
| `mut-block.bc` | 13:14: `!thunk` promotes only over `!` types, but `x`, of type `mut 'io_l44 i32`, is used inside |

#### A3a linear content read (a move out of a place) (40)

| program | the refusal |
|---|---|
| `aoc/2021-10.bc` | 47:27: `io_lv18c` is used twice here, and its type `array u8 * i32` is not persistent |
| `aoc/2023-07.bc` | 75:16: `io_lv75c` is used twice here, and its type `array (i64 * i32) * i32` is not persistent |
| `iter-mut-slice.bc` | 39:60: `io_lv9c` is used twice here, and its type `array i32` is not persistent |
| `leetcode/arrays/0015-3sum.bc` | 59:27: `io_lv80c` is used twice here, and its type `array (i32 * i32 * i32) * i32` is not persistent |
| `leetcode/dp/0039-combination-sum.bc` | 32:46: `io_lv5c` is used twice here, and its type `array i32 * i32` is not persistent |
| `leetcode/dp/0300-longest-increasing-subsequence.bc` | 24:25: `io_lv10c` is used twice here, and its type `array i32 * i32` is not persistent |
| `leetcode/graphs/0128-longest-consecutive-sequence.bc` | 53:42: `io_lv43c` is used twice here, and its type `array (array i32 * i32)` is not persistent |
| `leetcode/graphs/0261-graph-valid-tree.bc` | 72:31: `io_lv48c` is used twice here, and its type `array i32 * array i32` is not persistent |
| `leetcode/graphs/0323-number-of-connected-components.bc` | 71:29: `io_lv48c` is used twice here, and its type `array i32 * array i32` is not persistent |
| `leetcode/heaps/0347-top-k-frequent-elements.bc` | 52:30: `io_lv41c` is used twice here, and its type `array (i32 * i32) * i32` is not persistent |
| `leetcode/intervals/0056-merge-intervals.bc` | 50:16: `io_lv81c` is used twice here, and its type `array (i32 * i32) * i32` is not persistent |
| `leetcode/intervals/0057-insert-interval.bc` | 54:44: `io_lv63c` is used twice here, and its type `array (i32 * i32) * i32` is not persistent |
| `leetcode/intervals/0252-meeting-rooms.bc` | 37:16: `io_lv29c` is used twice here, and its type `array (i32 * i32) * i32` is not persistent |
| `leetcode/intervals/0253-meeting-rooms-ii.bc` | 40:16: `io_lv55c` is used twice here, and its type `array (i32 * i32) * i32` is not persistent |
| `leetcode/intervals/0435-non-overlapping-intervals.bc` | 36:16: `io_lv39c` is used twice here, and its type `array (i32 * i32) * i32` is not persistent |
| `leetcode/lists/0019-remove-nth-node-from-end-of-list.bc` | 90:42: `io_lv52c` is used twice here, and its type `array (array i32 * i32)` is not persistent |
| `leetcode/lists/0021-merge-two-sorted-lists.bc` | 94:42: `io_lv52c` is used twice here, and its type `array (array i32 * i32)` is not persistent |
| `leetcode/lists/0141-linked-list-cycle.bc` | 46:25: `io_lv35c` is used twice here, and its type `array i32` is not persistent |
| `leetcode/lists/0143-reorder-list.bc` | 104:31: `io_lv51c` is used twice here, and its type `mu X. 1 + i32 * ref X` is not persistent |
| `leetcode/lists/0206-reverse-linked-list.bc` | 78:42: `io_lv51c` is used twice here, and its type `array (array i32 * i32)` is not persistent |
| `leetcode/matrix/0048-rotate-image.bc` | 27:18: `io_lv20c` is used twice here, and its type `array_mut 'a i32` is not persistent |
| `leetcode/matrix/0054-spiral-matrix.bc` | 38:73: `io_lv87c` is used twice here, and its type `array i32 * i32` is not persistent |
| `leetcode/strings/0020-valid-parentheses.bc` | 29:27: `io_lv20c` is used twice here, and its type `array u8 * i32` is not persistent |
| `leetcode/strings/0076-minimum-window-substring.bc` | 51:28: `io_lv119c` is used twice here, and its type `array i32` is not persistent |
| `leetcode/trees/0098-validate-binary-search-tree.bc` | 37:27: `io_lv65c` is used twice here, and its type `array (i32 + 1) * i32` is not persistent |
| `leetcode/trees/0100-same-tree.bc` | 39:27: `io_lv65c` is used twice here, and its type `array (i32 + 1) * i32` is not persistent |
| `leetcode/trees/0102-binary-tree-level-order-traversal.bc` | 42:27: `io_lv65c` is used twice here, and its type `array (i32 + 1) * i32` is not persistent |
| `leetcode/trees/0104-maximum-depth-of-binary-tree.bc` | 39:27: `io_lv65c` is used twice here, and its type `array (i32 + 1) * i32` is not persistent |
| `leetcode/trees/0105-construct-binary-tree-from-preorder-and-inorder-traversal.bc` | 40:27: `io_lv65c` is used twice here, and its type `array (i32 + 1) * i32` is not persistent |
| `leetcode/trees/0124-binary-tree-maximum-path-sum.bc` | 38:27: `io_lv65c` is used twice here, and its type `array (i32 + 1) * i32` is not persistent |
| `leetcode/trees/0226-invert-binary-tree.bc` | 33:27: `io_lv65c` is used twice here, and its type `array (i32 + 1) * i32` is not persistent |
| `leetcode/trees/0230-kth-smallest-element-in-a-bst.bc` | 45:27: `io_lv65c` is used twice here, and its type `array (i32 + 1) * i32` is not persistent |
| `leetcode/trees/0235-lowest-common-ancestor-of-a-binary-search-tree.bc` | 39:27: `io_lv65c` is used twice here, and its type `array (i32 + 1) * i32` is not persistent |
| `leetcode/trees/0297-serialize-and-deserialize-binary-tree.bc` | 41:27: `io_lv65c` is used twice here, and its type `array (i32 + 1) * i32` is not persistent |
| `leetcode/trees/0572-subtree-of-another-tree.bc` | 40:27: `io_lv65c` is used twice here, and its type `array (i32 + 1) * i32` is not persistent |
| `mut-name-capture.bc` | 15:27: `io_lv15c` is used twice here, and its type `array u8` is not persistent |
| `reverse-bytes.bc` | 28:37: `io_lv30c` is used twice here, and its type `array u8` is not persistent |
| `sort-numbers.bc` | 37:71: `io_lv15c` is used twice here, and its type `array i32` is not persistent |
| `split-at-mut.bc` | 30:37: `io_lv29c` is used twice here, and its type `array u8` is not persistent |
| `text-wordfreq.bc` | 94:43: `io_lv82c` is used twice here, and its type `ref output` is not persistent |

#### A3b view/imm content read twice (#58 copy) (16)

| program | the refusal |
|---|---|
| `aoc/2022-21.bc` | 63:40: `io_lv23c` is used twice here, and its type `(array (1 + i32 * array_imm 't u8) * array i32) * i32` is not persistent |
| `aoc/2023-01.bc` | 39:40: `io_lv9c` is used twice here, and its type `array_imm 'a u8` is not persistent |
| `io-laws.bc` | 79:54: `io_lv11c` is used twice here, and its type `array_imm 'a u8` is not persistent |
| `leetcode/dp/1143-longest-common-subsequence.bc` | 33:40: `io_lv39c` is used twice here, and its type `array_imm 'b u8` is not persistent |
| `leetcode/heaps/0295-find-median-from-data-stream-f64.bc` | 61:43: `io_lv58c` is used twice here, and its type `array_imm 't u8` is not persistent |
| `leetcode/heaps/0295-find-median-from-data-stream.bc` | 75:43: `io_lv60c` is used twice here, and its type `array_imm 't u8` is not persistent |
| `leetcode/strings/0003-longest-substring-without-repeating-characters.bc` | 46:23: `io_lv83c` is used twice here, and its type `array_imm 't u8` is not persistent |
| `leetcode/strings/0005-longest-palindromic-substring.bc` | 32:27: `io_lv19c` is used twice here, and its type `array_imm 't u8` is not persistent |
| `leetcode/strings/0125-valid-palindrome.bc` | 33:36: `io_lv52c` is used twice here, and its type `array_imm 't u8` is not persistent |
| `leetcode/strings/0242-valid-anagram.bc` | 45:23: `io_lv60c` is used twice here, and its type `array_imm 't u8` is not persistent |
| `leetcode/strings/0271-encode-and-decode-strings.bc` | 30:24: `io_lv19c` is used twice here, and its type `array_imm 't u8` is not persistent |
| `leetcode/strings/0424-longest-repeating-character-replacement.bc` | 36:36: `io_lv46c` is used twice here, and its type `array_imm 't u8` is not persistent |
| `leetcode/strings/0647-palindromic-substrings.bc` | 31:27: `io_lv19c` is used twice here, and its type `array_imm 't u8` is not persistent |
| `leetcode/trees/0208-implement-trie.bc` | 53:25: `io_lv54c` is used twice here, and its type `array_imm 'a u8` is not persistent |
| `loop-handler-binder.bc` | 19:37: `io_lv16c` is used twice here, and its type `array_imm 'a u8` is not persistent |
| `loop-shadow-linear.bc` | 12:36: `io_lv19c` is used twice here, and its type `array_imm 'a i32` is not persistent |

#### A4 a let mut holding a cell (2)

| program | the refusal |
|---|---|
| `effects-log-fail.bc` | 24:49: type mismatch: expected `mut ('fx_rl5 /\ 'fx_l2 /\ 'io_l8 /\ top) i32 * i32`, but this has type `mut 'fx_rl5 ref i32 * i32` |
| `mut-modify.bc` | 15:56: type mismatch: expected `mut ('l /\ 'io_l17 /\ 'io_l27 /\ 'io_l34 /\ 'main /\ top) i32`, but this has type `mut 'l ref i32` |

#### B1 type inference through the place block (26)

| program | the refusal |
|---|---|
| `aoc/2020-08.bc` | 37:3: the type of the block's result is not determined here: ascribe it |
| `aoc/2021-15.bc` | 60:3: the type of the block's result is not determined here: ascribe it |
| `aoc/2022-12.bc` | 53:3: the type of the block's result is not determined here: ascribe it |
| `aoc/2023-03.bc` | 75:3: the type of the block's result is not determined here: ascribe it |
| `aoc/2024-01.bc` | 41:3: the type of the block's result is not determined here: ascribe it |
| `effects-fold-sum.bc` | 30:22: the type of `inl V` cannot be synthesized: ascribe it, `(inl V : A + B)` |
| `effects-map-hand.bc` | 17:30: the type of `inl V` cannot be synthesized: ascribe it, `(inl V : A + B)` |
| `effects-map.bc` | 33:30: the type of `inl V` cannot be synthesized: ascribe it, `(inl V : A + B)` |
| `effects-named.bc` | 120:3: the type of the block's result is not determined here: ascribe it |
| `float-arith.bc` | 40:3: the type of the block's result is not determined here: ascribe it |
| `float-ordered.bc` | 49:3: the type of the block's result is not determined here: ascribe it |
| `float-roundtrip.bc` | 44:3: the type of the block's result is not determined here: ascribe it |
| `for-return.bc` | 23:3: the type of the function's result, which a `return` in this loop returns, is not determined here |
| `leetcode/arrays/0011-container-with-most-water.bc` | 56:22: `let (x, y) = V` needs a `*` type, but `V : U (delay (array i32 * i32))` |
| `leetcode/arrays/0153-find-minimum-in-rotated-sorted-array.bc` | 56:22: `let (x, y) = V` needs a `*` type, but `V : U (delay (array i32 * i32))` |
| `leetcode/dp/0139-word-break.bc` | 45:3: the type of the block's result is not determined here: ascribe it |
| `leetcode/graphs/0133-clone-graph.bc` | 42:3: the type of the block's result is not determined here: ascribe it |
| `leetcode/graphs/0200-number-of-islands.bc` | 41:3: the type of the block's result is not determined here: ascribe it |
| `leetcode/graphs/0207-course-schedule.bc` | 45:3: the type of the block's result is not determined here: ascribe it |
| `leetcode/graphs/0269-alien-dictionary.bc` | 37:3: the type of the block's result is not determined here: ascribe it |
| `leetcode/graphs/0417-pacific-atlantic-water-flow.bc` | 51:3: the type of the block's result is not determined here: ascribe it |
| `leetcode/matrix/0073-set-matrix-zeroes.bc` | 23:3: the type of the block's result is not determined here: ascribe it |
| `leetcode/strings/0049-group-anagrams.bc` | 81:3: the type of the block's result is not determined here: ascribe it |
| `leetcode/trees/0211-design-add-and-search-words-data-structure.bc` | 77:3: the type of the block's result is not determined here: ascribe it |
| `leetcode/trees/0212-word-search-ii.bc` | 134:3: the type of the block's result is not determined here: ascribe it |
| `loop-labels.bc` | 5:3: the type of the block's result is not determined here: ascribe it |

#### B2 control handler body (existing elaborator refusal) (7)

| program | the refusal |
|---|---|
| `effects-fold.bc` | 33:9: the body of `with map_err` assigns a `let mut` variable declared outside it, or lends a place declared outside it: a control handler's body may be abandoned, and… |
| `leetcode/lists/0023-merge-k-sorted-lists.bc` | 118:11: the body of `with exhausted_to_option` assigns a `let mut` variable declared outside it, or lends a place declared outside it: a control handler's body may be … |
| `leetcode/matrix/0079-word-search.bc` | 59:11: the body of `with exhausted_to_option` assigns a `let mut` variable declared outside it, or lends a place declared outside it: a control handler's body may be a… |
| `parse-int.bc` | 30:15: the body of `with map_err` assigns a `let mut` variable declared outside it, or lends a place declared outside it: a control handler's body may be abandoned, an… |
| `parse-recover.bc` | 126:15: the body of `with to_result` assigns a `let mut` variable declared outside it, or lends a place declared outside it: a control handler's body may be abandoned,… |
| `state-machine.bc` | 65:13: the body of `with to_result` assigns a `let mut` variable declared outside it, or lends a place declared outside it: a control handler's body may be abandoned, … |
| `tree-map.bc` | 84:19: the body of `with to_result` assigns a `let mut` variable declared outside it, or lends a place declared outside it: a control handler's body may be abandoned, … |

#### B3 a capability not handed on by a lent loop stretch (7)

| program | the refusal |
|---|---|
| `axes/data-effects.bc` | 36:36: `stdout` is not consumed in its scope, and its type `ref output` has no destructor |
| `div-residual-copy.bc` | 9:3: `i` is not consumed in its scope, and its type `ref input` has no destructor |
| `fields.bc` | 35:7: `stdout` is not consumed in its scope, and its type `ref output` has no destructor |
| `io-for-after.bc` | 15:17: `stdout` is not consumed in its scope, and its type `ref output` has no destructor |
| `io-upper-effects.bc` | 17:16: `stdout` is not consumed in its scope, and its type `ref output` has no destructor |
| `lend-config.bc` | 39:3: `stdin` is not consumed in its scope, and its type `ref input` has no destructor |
| `utf8-count.bc` | 20:7: `stderr` is not consumed in its scope, and its type `ref output` has no destructor |

#### B4 an arm of a lent loop body does not hand the token on (3)

| program | the refusal |
|---|---|
| `io-args.bc` | 18:5: in this `case`, `n` is consumed in the `inr` arm but not in the `inl` arm |
| `leetcode/arrays/0033-search-in-rotated-sorted-array.bc` | 31:7: in this `case`, `hi` is consumed in the `inl` arm but not in the `inr` arm |
| `surface/io-wc.bc` | 21:5: in this `case`, `words` is consumed in the `inl` arm but not in the `inr` arm |

#### B5 other (10)

| program | the refusal |
|---|---|
| `aoc/2024-02.bc` | 48:39: internal error: a surface form was not elaborated before checking |
| `aoc/2024-11.bc` | 101:25: `*` reads an `imm` borrow or a cell, but this has type `i32` |
| `div-infer.bc` | 32:27: the operation 3.0 is not in the row `[]` |
| `effects-instances.bc` | 39:17: this computation performs the operations `[6.0 aff 1 + u8 + 1 ~> 0]`, which are not within the row `[]` here |
| `effects-map-fail.bc` | 28:30: type mismatch: expected `mut ('fx_rl19 /\ 'fx_l6 /\ 'io_l5 /\ 'main /\ top) array i32 * array_imm 'io_l5 i32`, but this has type `array_mut 'fx_rl19 i32 * array… |
| `gen-adapters-fail.bc` | 56:3: internal error: a surface form was not elaborated before checking |
| `iter-mut.bc` | 22:12: the iterator of this `for` holds the borrow of `a`: a borrow block over a loop lends its place again at each step, so what the loop holds between steps must not… |
| `lend-copy.bc` | 37:3: this borrow block's result has type `ref array_mut 'io_l16 i32`, which has the block's lifetime `'io_l16`: nothing borrowed at `'io_l16` outlives the block. When… |
| `operator-rounds.bc` | 79:11: this borrow block's place has type `(mu X. 1 + (i32 * i32) * X) * (1 + 1)`: `borrow imm`/`borrow mut` take a cell `ref A` or an array (a pair of cells for a fam… |
| `retry-block.bc` | 45:35: type mismatch: expected `mut 'fx_l_clock i32 * i32 * mut 'io_l17 i32`, but this has type `0` |

#### B6 a lent value handed back twice (3)

| program | the refusal |
|---|---|
| `axes/scope-loop-lend.bc` | 27:3: `t` is used twice here, and its type `ref array i32` is not persistent |
| `leetcode/dp/0322-coin-change.bc` | 20:3: `coins` is used twice here, and its type `array i32` is not persistent |
| `lend-server.bc` | 32:5: `cfg` is used twice here, and its type `imm 'a (i32 * i32)` is not persistent |


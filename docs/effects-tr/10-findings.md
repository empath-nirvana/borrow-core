# §10 Findings about phases A and B

[← §9 The factoring, T1, step-indexing](09-factoring.md) · [index](README.md) · next: [§11 Transcription guide](11-transcription.md)

Writing the proofs surfaced three programs that phase A's checker accepts and whose runs go
wrong, and one law phase A recorded as holding that phase B refutes. Each is machine-checked: the
three phase A probes below were run against phase A's model at `origin/main` (`8cbc973`) with
`lake env lean`, and the outputs are copied verbatim. They are not committed: this change adds no
Lean. To reproduce, save the block as a file and run `lake env lean <file>` in a checkout after
`lake build EffModel`.

Each finding changed a rule of §2, and each change is the smallest one the proofs need.

---

## 10.1 A lent place that was moved before the lend

Phase A's `lend c as x in M` leaves `c` with its owner and checks only that `c` is not free in
`M`. It does not check that `c` still holds the capability. A thunk captured before the lend can
consume it.

```lean
import EffModel.Refusals
open EffModel
-- A place consumed through a thunk captured before the lend, then lent.
def movedLend : Tm :=
  newCtr "c" (.bind (.ret (.thunk Mode.lin (.getcap (v "c")))) "t"
    (.lend "c" "x" (.bind (.force (v "t")) "s" (inc "x" (.ret (v "s"))))))
#eval (typecheck sigs movedLend |>.toBool, rejection sigs movedLend)
#eval run sigs movedLend
```

Output:

```
(true, "")
{ out := EffModel.Outcome.stuck "a lent capability used after its owner consumed it", trace := [], leaks := [] }
```

**Why.** Grades count `c` once (inside the thunk); the lend is not a use. The lend's scope check
looks for `c` syntactically in `M`, and `M` mentions only `t`.

**Change.** The lend consumes its capability and answers it back (BoLo's `withbor` shape, D1.9,
[lend]). Phase A's form is the derived form that rebinds `c`. In `movedLend` the lend is then a
second use of `c`, refused by grades. With this change T1 is not needed (T9.1).

## 10.2 A frame-owned resource carried past its frame by a continuation

Phase A forbids a thunk from capturing a `resD` handle, but a continuation is a thunk the machine
builds, and nothing checks what it captures. A handler inside the `using` frame can return the
continuation, in a stream, past the frame.

```lean
import EffModel.Refusals
open EffModel
def resEscape : Tm :=
  .bind (.using "r" 1 (.handle "y" "Yield" hStream [] streamC
      (yld "y" (n 1) (seq (.use (v "r")) (.ret (n 0))))))
    "s0" (.case (v "s0") "a" (.ret (v "a")) "q"
      (.split (v "q") "p" "rest" (.bind (.force (v "rest")) "o" (firstOf (v "o")))))
#eval (typecheck sigs resEscape |>.toBool, rejection sigs resEscape)
#eval run sigs resEscape
```

Output:

```
(true, "")
{ out := EffModel.Outcome.ret "0",
  trace := [EffModel.Event.acq 1, EffModel.Event.free 1, EffModel.Event.use 1],
  leaks := [] }
```

The trace shows `use 1` after `free 1`: a use after free. (Phase A's machine does not check
liveness at `use`, so the run does not get stuck; it reports the wrong order.)

**Why.** The `using` frame frees `r` when the handler returns the stream. The continuation in the
stream holds `r` (a `to` frame captured it), and the stream's type `stream [] int` says nothing of
it.

**Change.** The handle is an instance of a built-in effect `Res` (D1.3, [using]); `use` is an
operation on it. The continuation's resume row then mentions `r`, the stream's type must mention
it, and `x ∉ atoms(A)` at the `using` binder refuses the escape. The frame's ownership of the
resource is unchanged (L5.16). This is phase A's thunk scope rule ("thunks may not capture a
frame-owned resource") extended to continuations, by moving the handle where rows confine it.

## 10.3 A handler's return clause run twice

A deep handler's frame is part of every continuation of its own operations. Phase A checks the
clauses' captures at the row the handler *forwards*, and for its own operations only the case
where a continuation may be dropped (the return clause may not run). It does not check the case
where a continuation may be resumed twice, which reinstalls the frame twice and runs the return
clause twice.

```lean
import EffModel.Refusals
open EffModel
def hAgainOwn : Hnd :=
  .cl "again" "p" "k" (seq (call (v "k") .unit) (call (v "k") .unit))
    (.ret "a" (.getcap (v "c")))
def retTwice : Tm :=
  newCtr "c" (.handle "g" "Again" hAgainOwn [] (.F .int)
    (.op "g" "again" .unit "_" (.ret (n 0))))
#eval (typecheck sigs retTwice |>.toBool, rejection sigs retTwice)
#eval run sigs retTwice
```

Output:

```
(true, "")
{ out := EffModel.Outcome.stuck "a capability consumed twice", trace := [], leaks := [] }
```

**Why.** `Again` is relevant (`rel`: resumed at least once, possibly twice). The return clause
owns `c`. Grades count it once.

**Change.** [handle]'s capture premise also checks the clauses' captures at the join of the
handler's own resuming qualifiers, and the return and abortive clauses' usage is scaled by `ω` when
one of them admits contraction (§2, [handle] and *Clauses*). In the proof this is exactly the
`mode` bullet of L5.14 case 2: the reinstalled frame's resource must be `Pers` when the
continuation may be copied.

## 10.4 ν/op does not hold at a multi-shot operation

Phase A recorded Staton's four instance laws as holding in every context of its suite
(`docs/effect-model.md` §0, §3.1). Its suite checked ν/op at a `Log` operation, which is linear.
Phase B refutes ν/op at a multi-shot operation in Lean (`nu_op_fails_multishot`, by `decide`,
`Examples.lean`). This document states the law with that restriction (T7.15) and leaves the
non-contractible case open (O1). This is a difference in setting from Staton's, not a defect of
it (T7.15, *On Staton's law*).

## 10.5 What did not change

- The 21 law rows of phase A's matrix hold here as stated, with T7.15's restriction; the ones phase
  B proved, in Lean; T7.3 and T7.11 on paper.
- Phase A's 11 refusals: each is still refused, by the same rule, except T1's two
  (`t1Lend`, `t1Callback`), which are refused by independence at the `run` frame (`Yield` is
  affine, so `bound(ρ).req ≠ lin` in [lend]) rather than by T1; and `t1Harm`, refused by grades
  (T9.1).
- Phase A's 10 programs: each types under §2 after mechanical rewrites: the lend's rebinding
  (10.1); an explicit `cancel k` where a clause drops an affine continuation, and `hStream`'s
  stream built as `fold (thunk_lin ⟨resume k (), cancel k⟩)` (§8.1); and each `fix` (`retry`,
  `retryPolN`, `countdown`, `pullAll`) as `bfix_n` under a handler of an exhaustion effect (§9.4,
  SPEC §20). Every lend in them has a body whose row, after erasing the lent instance, holds only
  `lin` instances (`Log` under `hPrint`) or nothing, so [lend] accepts it. This is checked by
  reading the programs (`Programs.lean`), not by running a checker for §2, which does not exist.
- Phase B: nothing it has proved is contradicted (§6.4).

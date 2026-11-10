# K1: adequacy with host externs (the chain's plain adequacy, for programs that do I/O)

Kernel target: a design scope for extending `goal791N : HandlerLawN → Goal791N` from closed,
extern-free programs to programs that call host externs (standard streams, files, sockets, the
clock, the arguments), so that I/O programs are covered by the kernel's guarantee. This is
kernel-foreman's charter item K1, not #855's K1. It is a design only, with no Lean and no
library change.

Read at `main` 3309a41e (worktree `borrow-core-scope-externs`, branch `scope-externs`). The
unmerged Fs branch `fs-769` (2b322a61) was read for the owned-buffer shape. Counts are in
`scratch-archive/kernel/scope-externs/measure.txt`.

## 0. Summary

- **What excludes externs is the statement, not the relation or the machine.**
  - `Goal791N` (`Core/Chain/Adequacy791N.lean:80–83`) types the program at the context
    `ctx791 cs`, which holds only the #791 constants, and at `F 1`.
  - `SemJN`, `gN` and `fundamentalN_all` are already stated at every context
    (`Goal791N.lean:1073–1086`, `FundamentalKW835N.lean:94`).
  - The machine has no I/O step, and none is needed: an extern is a slot of `main`'s context
    closed by a value (SPEC §11, `SPEC.md:1103`).
  - `erwpK`'s tables have no entry for a host call, and none is needed either: a call into an
    extern is ordinary steps of the value that closes the slot.
- **Core already covers externs, and it is the template.** Core states the host contract as the
  named hypothesis `ExternsMeet` (`Core/Stdio.lean:769`): every extern value is in the relation at
  its type at `∅`. `externs_every_run` concludes from it, the models discharge it
  (`stdModel_meets`), and `IORun.every_run` applies it to every checked `run_io` with no pins.
  Every corpus I/O program is covered today, at Core's relation.
- **What K1 adds.** I/O programs that hold a borrow across a suspension leave Core's coverage
  once the surface emits the suspending constants (surface A1). Today no frontend file names
  `Const791`, `withbor2S` or `ctx791` (measured: 0). K1 puts those programs under `goal791N`.
- **Recommended contract: `ExternN`, the form of `ConstN`.** An extern value is in `𝒱⟦!T⟧` at
  `∅` at every `δ`, world and index (`Core/Chain/ConstKW835N.lean:37–39`). It is a named
  hypothesis, like `ExternsMeet`, for host code. For the models it is a theorem, from
  `fundamentalN_all` at the model's derivation and the opaque type read as its representation.
  One contract serves every class: pure reads, writes, owned handles and blocking calls.
- **Recommended reading: a call, neither a step nor a stop.** A host call is a call of the value
  in the closing substitution. Owned buffers move through `⊸`'s resource split. `KW.Owed` is not
  read, because no continuation is captured. `HandlerLawN` is unchanged, since its three fields
  quantify over every context (`FundamentalKW835N.lean:57–84`).
- **The hardest case is a suspending lend of a capability cell, at its cancel.**
  - `Const791.OKAt` asks for the lend's finaliser at the empty context, closed, at
    `Ref A ⊸ F 1` (`Core/TreeGoal791.lean:184`, and `:188`, `:192`, `:199` for the other forms).
  - At `A = Output` or a socket, the finaliser must give the cell back to the host, which only
    an extern can do (`Consumable` has no `opq` case, `Core/Consume.lean:406–431`). The extern
    is a slot of the program's context, out of the finaliser's reach.
  - So A1 cannot emit `withbor2S` over `stdout` at all. The fix is additive: the finaliser is
    typed at the externs' context and closed by their values (unit K1.3).
- **Units:** K1.0 to K1.5, about 5 proof units after the entry. The last concludes
  `corpus/io-effects.bc`, the running example (§1), at the extended `goal791N`. Suspending I/O
  answered by the platform itself (the "stop" reading, §4.3) is a later, separate design.

## 1. The running example

**The operator's watch loop:** read from a socket into an owned buffer, parse or print, loop.
No socket program exists (`Net`, #597, is "designed, not built", `SPEC.md:1425–1429`). The
candidates:

| Program | Shape | On main |
|---|---|---|
| `corpus/fs-cat.bc` on `fs-769` | `let (f2, (b2, n)) = read(f, b)` in a counted loop over a not-consumable `File`, then `print_string(b2)`: exactly #597's owned shape | no: the branch is unmerged, and its later form rested on `[let-dtor]`, removed by #771 |
| **`corpus/io-effects.bc`** | `read_input()` (`lib/textio.bc:78–85`) loops `input_chunk(s) -> (s, more)`: an owned string in, the string and a flag out, each chunk read by `input_into` on a view lent for one call to the `read_into` extern (`lib/wasi.bc:20`); then counts and prints through `Stdout`, notes through `Stderr` | **yes** |
| `corpus/ascii-upper.bc` | `read_all`/`read_chunk(c, s) -> (c, (s, more))` (`lib/textio.bc:24–46`), the same loop over the input cell instead of the effect | yes |
| `corpus/io-task.bc` | a task given `Stdout` holds the borrow of `stdout` across its `await`s (`spawn_in`, BOXED-κ) | yes; covered by Core today |

**Chosen: `corpus/io-effects.bc`.** It is on main and is the owned-buffer read loop, a print and
a platform handler in one program. A socket read under `Net` is the same program with
`Stdin.input_into` replaced by `Net.recv` and the extern by `recv`: a new opaque kind with its
model, and no kernel change beyond the kind (§2.4). `fs-cat` is the same shape once #769 lands.

What the kernel sees in it:
- the checked wrapper `run_io : Bytes ⊸ F R` at the context of the operation and harness externs
  (`wrapperSrc`, `Frontend/Check/Externs.lean:260`);
- the extern calls in the clauses of `wasi_stdin`, `wasi_stdout` and `wasi_stderr`, each a call
  of the extern on the lent cell (`lib/wasi.bc:18–31`);
- the loop's buffer, a `string` owned by the loop's state and passed into and out of
  `input_chunk` by value.

It holds no borrow across a suspension, so it needs no constant. It is the test that the
extended statement covers I/O at all. The instance program of unit K1.4 is the test that I/O and
a suspending lend meet in one run.

## 2. What excludes externs today (question 1)

### 2.1 The statement

```
def Goal791N : Prop :=
  ∀ (cs : List Const791), (∀ c ∈ cs, c.OK) → ∀ e₀ : Expr,
    CDerives LifeCtx.empty (ctx791 cs) e₀ (.comp (.ret .unit)) →
      OrDiverges (ℍ := ℍ) (substAll (vals791 cs) e₀)
```
(`Core/Chain/Adequacy791N.lean:80–83`.)

The premise that makes it "closed, extern-free" is the context `ctx791 cs`
(`Core/TreeGoal791.lean:238`): one slot `!c.ty` per constant, and nothing else. A program that
names an extern is typed at a context with a slot the constants do not supply. The type
`.comp (.ret .unit)` is the second narrowness: `run_io` answers `F R` for a persistent `R`.

The proof (`:89–101`) uses nothing specific to that context:
- `fundamentalN_all hm hder` at the empty world;
- `gN_ctx791`, the context met by the constants' values (`:70–77`);
- `cN_ret_iff` and `erwp_adequacy`, whose only demand on the post is that it holds at `∅`
  (`Core/Chain/SI/LoopN.lean:175–176`).

At a persistent `R` that demand is `vN_empty_of_persistent` (`Goal791N.lean:2450`).

### 2.2 The machine

- `Head.host` (`Paper/S3_Dynamics/Definitions.lean:530–532`) applies `ℍ.call op v`.
- `Host` (`Support/Dynamics/Host.lean:34–58`) is §8's and §37's arithmetic, one function per
  operation, and nothing else.
- `HostIs ℍ` (`:62`) carries no data. It threads the host through every theorem, so each holds
  at every host.

There is no I/O step. SPEC §11 makes that the design: "no `CDerives` constructor and no machine
step is added for them" (`SPEC.md:1103`). In compiled code, the backends bind each extern to its
host function (`Backend2/Convert.lean`, `mkClosOf`). The program the backend compiles is
`IORun.expr r []` with those bindings (SPEC §11 *Lowering*).

### 2.3 The relation

`erwpK`'s tables (`OpTabK`, `opTableK`, `Core/Chain/SI/ErwpK.lean:64`, `:101`) are indexed by
operation names. An extern is not an operation and has no entry. At `F A` the table is empty
(`cN_ret_iff`), and an extern call is read as the steps of the value that closes its slot.

The opaque types are already in the chain's relation: `vNE … (.opq k) … = k.rel v ρ`
(`Goal791N.lean:99`, and `vOE` at `:135`), Core's clause.

### 2.4 How Core does it, the template

| Piece | Core (`Core/Stdio.lean`) | What it is |
|---|---|---|
| the contract | `ExternsMeet Γ γ` (`:769–773`) | each slot live, at a persistent type, its value in `vC true T ls δ` at `∅`, at every `ls`, `δ` |
| the context | `gDenC_of_meets` (`:776`) | the contracts meet the context relation at `∅` |
| the theorem | `externs_every_run` (`:794`) | `run_io[γ] inp` runs to a value of `R` at the empty memory, from `fundamentalC` and `theorem32D` |
| the models | 15 entries of `stdModel` (`:828`), 15 `cC_*` congruences, `vC_bytes`, `vC_outRep`, `vC_clockRep`, `vC_argsRep` | each model is a `CDerives` derivation at the representation (`d_readByte`, …); the relation at the opaque type is the relation at the representation |
| the loop | `externs_loop_every_run` (`:956`) | `run_io` driven `n` times |
| the frontend | `IORun.every_run` (`Frontend/Check/Externs.lean:526`) | at the checked wrapper, `pins = []` |

A new host kind costs one `Opaque` constructor with its `Holds` and `rel` arms. Measured on
`args`: 18 arm lines in 10 files across `Core/`, `Frontend/`, `Backend/` and `Backend2/`. It
also costs its representation lemma and its models' `*_meets`. No `VTy` former is added.

**Conclusion.** Core's answer transfers to the chain unchanged in shape. The chain's novelties
are the constants, the typed world and the Kripke stops, and none of them is read at an extern
call (§4).

## 3. The extern contract (question 2)

### 3.1 One contract, the form of `ConstN`

```
ExternN (T : VTy) (v : Val) : Prop :=
  closedAt 0 v.1 = true ∧ T.Persistent ∧
  ∀ (δ : LSub) (Θ : LocTy) (n : Nat), Θ.OK → vN (ℍ := ℍ) T δ Θ n v PMap.empty
```

- It is `ConstN`'s conclusion (`ConstKW835N.lean:37–39`) for a value that is not a #791 constant.
  The two kinds of slot are then read alike by `gN`.
- `closedAt` is new beside Core's. It is needed only by K1.3, where a finaliser closed by the
  extern values must be closed.
- `ExternsMeetN Γ γ` lists it slot by slot, as `ExternsMeet` does.

It is a named hypothesis, a `Prop` and not an axiom. It is stated once for every extern, as
`ExternsMeet` is, so that `bcc trusted` keeps one line per extern.

**Proved for the models, assumed for the hosts.**
- **Models.** `ExternN T v` is a theorem: `fundamentalN_all` at the model's derivation
  (`d_readByte`, …), with the opaque type read as its representation in `vN`, as Core's `cC_*`
  read it in `vC`. It needs `MissingN`, since `fundamentalN_all` takes it. The models use no
  handler rule, but there is no handler-free fundamental that would remove the hypothesis (§8, C4).
- **Hosts.** It is assumed, with the same assurance levels as today.

**Why a host can meet it: an argument, not verified.**
- `OrDiverges` is a property of every finite prefix of a run.
- A finite prefix of a real run observes finitely many host answers: bytes read, times, results.
- A model whose capability cell holds the position in that trace answers exactly those, at the
  representation's type. The content is opaque, so the program cannot tell a position from a
  stream.
- Such a model is a typed closed term, and `fundamentalN_all` puts it in `ExternN`.
- So each prefix of the real run is a prefix of a run that `Goal791N` covers.

This is the prophecy reading SPEC §34's laws already take for `Stdin` ("a byte list fixed
before the run"), extended to the clock and sockets. Not checked in Lean: the host is not a
Lean term.

### 3.2 Per class

| Class | Externs | Type shape | Model | Contract |
|---|---|---|---|---|
| pure reads | `read_arg`, `clock_now` | `!(∀'a ⊏ ⊤. Mut 'a k ⊸ F (Mut 'a k ⊗ R))`, `R` persistent | `withswap` on the cell: pop the argument stream, or answer the time | `ExternN`; models proved by K1.2 |
| writes | `write_byte`, `write_all`, `clock_sleep` | `!(∀'a. Mut 'a k ⊗ X ⊸ F (Mut 'a k))` | `withswap` consing onto the output list (`write_all` a counted loop) | `ExternN`; models proved |
| owned handles | today `mk_*`/`take_*`; under `Net` `connect`, `accept`, `close` | a make answers `Ref k`, a take consumes it; `Ref k` is not consumable (`Core/Consume.lean:406`) | `alloc` and `free` of the cell | `ExternN`; plus a host claim outside the relation: freeing the cell closes the descriptor |
| owned-buffer I/O (#597) | `read_into` today; `recv`, `send` under `Net` | `!(∀'a. Mut 'a k ⊗ Buf ⊸ F (Mut 'a k ⊗ (Buf ⊗ I32)))`, the buffer owned in and out | a counted loop writing the trace's bytes into the buffer's cells | `ExternN`; the buffer's cells move through `⊸`'s split (§4.2) |
| blocking I/O | any of the above whose host blocks | unchanged | unchanged | `ExternN` unchanged: `cN` at `F A` is `erwp`, a safety property, so a call that never returns meets it. A blocked run is a diverging run, which `OrDiverges` allows |
| suspending I/O, answered by the platform | none today | an operation in `main`'s outer row | none | **not covered by `ExternN`**: needs the stop reading and a world contract (§4.3) |

With owned handles, the empty final memory of `OrDiverges` says every capability and
connection cell was freed: every handle was given back. It says nothing about descriptors, as
SPEC §11 *Adequacy's scope* states for Core. Closing the descriptor when the cell is freed is the
host's claim, at `bcc trusted`'s "assumed (1)".

### 3.3 Two claims per host, or one

Core's contract is at `vC`, the chain's at `vN`. A host is then claimed to meet both. There is
no lemma from `vC` membership to `vN` membership; not derived. For the models both are theorems,
from the two fundamental properties at one derivation. That is the argument for stating the
host's claim as "behaves as a typed term at the representation" (§3.1), from which both follow
(§8, C1).

## 4. How `erwpK` and `KW` read a host call (question 3)

### 4.1 The reading: a call

The extern is a slot of `Γ`. `SemJN` closes it by `γ` (`Goal791N.lean:1083–1086`), and `gN`
asks of it what it asks of a constant's slot (`:1073–1078`). A call `force x` at the slot's
`U C` is `force_compatN`'s case, unchanged. Its run is `cN C` at the value's thunk, given by
`ExternN` through `vN`'s `U` clause (`Goal791N.lean:71`). That clause is read at every
`Θ' ⊒_ExtR Θ`, every consistent view and every record list, so the call is valid wherever the
program makes it:
- inside a lend's callback, at a world with the lend's key;
- under a handler, at a nonempty table: `cN` at `F A` reads no table, and `bind_compatN` and
  `effLet` lift it;
- in a cancel run, at the canceller's table (§6).

Neither alternative in the brief is needed for the classes of §3.2 but the last:
- **A step** (host calls as machine steps under a host-transition relation) would change the
  machine (`Paper/`, which is a transcription) or add a run relation beside `Step1`. That is
  needed only where the host acts outside any call the program makes.
- **A stop** (a host call as an operation answered by the world) is §4.3.

### 4.2 Owned buffers across the call (#597's shape)

`recv : !(∀'a ⊏ ⊤. Mut 'a Conn ⊗ Buf ⊸ F (Mut 'a Conn ⊗ (Buf ⊗ I32)))`, or `io-effects`'s
`read_into`, whose buffer is a view lent for the one call.
- **In.** `⊸`'s clause splits the caller's resource. The buffer's cells (`Buf`, an owned array) go to the call with the argument.
- **Out.** The answer's resource holds them again, with the bytes written. `cN` at `F (… ⊗ (Buf
  ⊗ I32))` posts `vN` at the answer, so the cells come back owned.
- **The view form.** `read_into`'s `array_mut 'b u8` is a borrow lent by the caller for one
  non-suspending call. The `Mut` clause holds over the call's segment, and the lend ends before
  any stop. Nothing new.
- **`KW.Owed`** (`ErwpK.lean:758`) is read only at a stop, by `contShareK`'s owed continuation.
  A call captures no continuation. **`KW.Owed` needs nothing.**

Under a suspending lend the call happens inside the callback's segment, between stops. A
buffer held across an `await` is owned by the continuation, which decision 71's "owned across
suspensions" already admits. A buffer *borrowed* across an `await` (`read(sock, &mut buf).await`)
is #844 Tier 2, not K1.

### 4.3 The stop reading, for later: the platform as an outer handler that suspends

**Needed when.** The host itself suspends the program and resumes it later: an event loop in
the runtime, not `lib/async.bc`'s scheduler inside the program. The program's outer row is
then nonempty, and a run ends at `K[op p]` with `op` an I/O operation. Today `OrDiverges` calls
that configuration final and not a value (`final_opPlug`, `Core/StepsN.lean:84`), so it is
refused.

**What it would take** (a design sketch; none of it is derived):
1. **A run relation with world steps**, in `Core/`, beside `Step1` and not in `Paper/`. From
   `K[op p]` at `μ`, the world answers `r` at `μ'`. A named contract `WorldOK` asks that the
   world changes only the payload's cells and answers in the entry's `PB`.
2. **`erwp_adequacyW`**: `erwp_adequacy` (`LoopN.lean:175`) at the I/O row's table instead of
   the empty table. At a world step, the stop's obligation (`contShareK`) gives the continuation
   at every answer in `PB`.
3. **The world resumes in place.** `KW.owed_self` (`ErwpK.lean:764`) is the floor it needs. The
   world is a tail-resumptive handler, and `HandlerLawN` is about a clause that stores `κ`
   (`assert-boundary.md` §0.2). So `HandlerLawN` should not grow. Not derived; obstruction not
   verified.
4. **Payloads and answers obey `Row.Suspend`'s closed bounds.** Owned buffers pass
   (`VOutlives ∅ ⊤` excludes only borrows, thunks, `Unk` and boxes at variable lifetimes,
   `TreeGoal791.lean:70–76`). That is the #597 shape, and decision 71's rule.

Recommended out of the first cut (§8, C2): blocking calls and `lib/async`'s in-program scheduler
cover the watch loop without it.

## 5. What `HandlerLawN` needs (question 4)

**Unchanged.**
- `HandleVN`, `HandleVBN` and `ReifyN` quantify over every `Γ`, `Γ₁` and `Γ₂`, with `SemJN`
  premises (`FundamentalKW835N.lean:57–84`). A context with extern slots is one of them.
- `MissingN ↔ HandlerLawN` (`HandlerLawN.lean`, `handlerLawN_iff`) is untouched, and
  `fundamentalN_all` is used as it is.
- No new named law sits beside it under the call reading. `ExternN` is the boundary of the host,
  not of the handler rules. It is a hypothesis of the goal on the program's context, not a law
  about a typing rule.

**With A1.** A1 emits `withbor2S`/`sliceBorrowMS` for a `borrow mut` held across a suspending
row, and puts the constants in `main`'s context (`scratch-archive/foremen/surface.md`, item 3).
An I/O program under A1 has both kinds of slot in one context. So the extended statement must
take a context of constants and externs together (unit K1.1), not two goals. A1 over a
capability cell also meets the finaliser obstruction of §6, so K1.3 lands before A1 can emit a
lend of `stdout`.

## 6. The hardest case (question 5)

### 6.1 A cancel of a task holding a lent capability

The program:
1. A task is lent `stdout`'s cell by `withbor2S`.
2. It writes through the borrow, `await`s, and writes again.
3. It is cancelled by its scheduler while parked. This is `io-task.bc` with the borrow made a
   suspending lend, the form A1 emits.

The cancel goes as follows:
- `cancel(t)` forces the task's `close` observation (`lib/async.bc`, `cancel`), which takes `κ`'s
  cancel branch.
- `erwp_kappaC_cancel` (`Core/Chain/SI/HandleN.lean:284–298`) frees `κ`'s cell and runs
  `ccatch (K†[raise cancel])` at the canceller's table: the canceller drives the cleanup.
- The cleanup reaches the lend's frame `then b. (r, b) unwind d r` (`withborUE`,
  `Core/EffBorrow.lean:206–208`) and runs `d r` on the source cell `r : Ref Output`.

**The obstruction.** `d` is fixed by `Const791.OKAt`:
`closedAt 0 d = true ∧ CDerives Δ [] d (.val (.lolli (.ref A) .unit))`
(`Core/TreeGoal791.lean:184`; `:188`, `:192`, `:199` for `w3`, `wF`, `sm`).
- `.lolli (.ref A) .unit` is `U (Ref A ⊸ F 1)` (`Core/Types.lean:213`).
- At `A = Output`, `d` must end the cell's content, an opaque value. `Consumable` has no `opq`
  case (`Core/Consume.lean:406–431`), so `consumeE` is not available.
- The only way to give a capability back is a harness extern (`take_output`), or `close` under
  `Net`. `d` is typed at the empty context and closed, so it cannot name one.

**Status.**
- "`d` cannot name an extern" is the premise's form: verified by reading.
- "No closed `d` of that type exists at an opaque `A`": not derived; obstruction not verified.
  No inhabitant is known. One would have to consume an opaque value with no elimination rule,
  at `F 1`, with no row in which to diverge.

**Consequence.** No `Const791` lends a capability cell today, resumed or cancelled. So A1 cannot
emit a suspending lend of `stdout`, a file or a socket, and the cancel case is the resumed case
too: the premise is asked of every constant whether or not it is cancelled.

**The fix (K1.3): the finaliser at the externs' context.**
- `Const791.OKAt` takes the finaliser at a context `Γx` of persistent extern slots:
  `CDerives Δ Γx d …`.
- The constant's value is closed by the extern values, `c.val[γx]`.
- A bridge `semJN_close` turns `SemJN Δ Γx d j` and `ExternsMeetN Γx γx` into
  `SemJN Δ [] (d.psub γx) j`. The five `*S_compat` lemmas take the finaliser's `SemJN` at `[]`
  (`CancelKW835N.lean:124–130` for `withbor2S_compat`), so **they are unchanged**.
- Only `Const791.OKAt`, `Const791.val_closed` (`ConstKW835N.lean:65`) and `constNAt_all`
  change. Measured: 6 references outside `TreeGoal791.lean`.
- `Γx = []` is today's premise, so every existing instance holds unchanged.

The finaliser stays at `F 1`, effect-free. It runs in the canceller's context and performs
nothing, so the canceller's table is not read.
- The `close` call is steps of the extern's value, inside the frame that holds the source's
  resource (`erwp_kappaC_cancel`'s `ptoOwn` frame and the lend frame's source).
- An *effectful* finaliser, one that performs `Stdout` on cancel (surface A4), is the different
  change named in #769's comments, option (a). It is not K1.

### 6.2 A blocking read under the built-in scheduler

A task under `lib/async.bc` calls a blocking `recv`. Under the call reading the call returns or
runs forever, and every other task waits. That is a liveness fact, and `OrDiverges` is a safety
property, so the kernel has nothing to prove. Not interleaving needs, at the surface and in the
runtime:
- a non-blocking extern that answers "would block";
- a task loop that `await`s between polls.

Both are ordinary calls and an ordinary in-program handler, covered by the call reading. A
cancel cannot land inside a host call, because a call is not a stop. So "cancel while the read
is in flight" exists only under the stop reading (§4.3), where the world would have to drive
`κ`'s cancel branch.

## 7. Units (question 6)

Kernel units only. Each preserves the baseline theorems:
- `goal791N` (restated in place, the old statement an instance);
- `fundamentalN_all`, `handlerLawN_iff`;
- Core's `externs_every_run`, `externs_loop_every_run`, `io_every_run`, `fundamentalC`,
  `adequacyC`, untouched;
- `prog791_orDiverges`, `progRes_orDiverges`, `progCan_orDiverges`.

No `VTy` or `CTy` former, no `CDerives` rule or index, and no typing rule gains a side condition.

| Unit | Content | Done-when |
|---|---|---|
| K1.0 | SPEC entry: `ExternN` and `ExternsMeetN`; the restated `Goal791N`; the finaliser at the externs' context; the trust wording of §3.1; the baseline above; open: the stop reading (§4.3), effectful finalisers (A4), #844 Tier 2 | entry merged |
| K1.1 | `ExternN`, `ExternsMeetN`, `gN_of_meetsN` over a context of constants and externs. `Goal791N` restated in place: `∀ cs Γx γx, (∀ c ∈ cs, c.OK) → ExternsMeetN Γx γx → CDerives ∅ (ctx791 cs ++ Γx) e (.comp (.ret R)) → R.Persistent → OrDiverges (substAll (vals791 cs ++ γx) e)`. `goal791N` re-proved, the post discharged by `vN_empty_of_persistent` | `goal791N : HandlerLawN → Goal791N` at the new statement; the 3 callers (`Adequacy791N.lean:218`, `Nest844N.lean:464`, `:470`) re-proved at `Γx = []`, `R = 1` with their statements unchanged; axioms ⊆ `[propext, Classical.choice, Quot.sound]`; judgment freeze passes |
| K1.2 | The models at `vN`: `vN_bytesRep`, `vN_outRep`, `vN_clockRep`, `vN_argsRep` (the opaque type as its representation, `funext` form); `meets_of_derivesN`; the 15 `*_meetsN`; `stdModel_meetsN`; `externsMeetN_of_model`. In `Core/`: `externs_every_runN`, `io_every_runN`, `externs_loop_every_runN`, `io_loop_every_runN`, each concluding `OrDiverges` of `run_io[γ] inp` (resp. driven `n` times) from `HandlerLawN` | `stdModel_meetsN : ∀ p ∈ stdModel, ExternN p.1 p.2` from `HandlerLawN` with no other hypothesis; 15 of 15 entries; the first congruence (`read_byte`) measured before the rest (§9) |
| K1.3 | The finaliser at the externs' context (§6.1): `Const791.OKAt` with `Γx`; `semJN_close`; `val_closed` above `Γx`; `constNAt_all` re-proved; `Goal791N` substitutes `c.val[γx]` | every existing `Const791.OK` instance holds at `Γx = []` unchanged; the five `*S_compat` statements unchanged; a `w2` constant over `Ref Output` whose finaliser is `λr. take_output r` has `OKAt` inhabited |
| K1.4 | Kernel instance `progIO`: `prog791` with the lent cell `stdout`'s, made by `mk_output`; the callback writes a byte by `write_byte` on its borrow, `wait`s, and writes again; then `take_output`. Resumed (the handler resumes `κ` in tail position) and cancelled (the handler cancels `κ`, the finaliser takes the cell back) | `progIO_res_orDiverges` and `progIO_can_orDiverges` proved from `HandlerLawN` alone, the externs given their models; axioms ⊆ the three |
| K1.5 | Grounding. The chain's end-to-end at the checked wrapper: `IORun.every_runN` and `IORun.loop_every_runN` (`Frontend/Check/Externs.lean`, statements reading K1.2's theorems; no elaboration change). `bcc trusted`'s typing line names the chain theorem | `IORun.every_runN` proved for every `IORun` with `pins = []`; `corpus/io-effects.bc` concluded by it at the extended `goal791N` (its `IORun` exists: the checked wrapper and `modelsOf`), at its golden (`scripts/compile-corpus.sh corpus/io-effects.bc`); `bcc trusted corpus/io-effects.bc` names it |

**Costs, as measured or estimated.**
- **K1.1.** `Adequacy791N.lean` is 221 lines. The goal and its 3 callers change, and `gN` gains
  one lemma.
- **K1.2.** Core's counterpart is `Core/Stdio.lean` lines 60–118 (the representations), 221–300
  and 578–760 (the congruences and meets). The chain twin should be shorter, since the
  derivations `d_*` are reused. Estimate about 250 lines; not measured.
- **K1.3.** 6 references to `OKAt`/`val_closed` outside their definitions, and one bridging
  lemma.
- **K1.4.** `prog791`'s instance is 117 lines (`Adequacy791N.lean:103–219`). The I/O instance is
  about twice that, with a cancel run. Estimate.
- **K1.5.** Two theorems, each a few lines over K1.2.
- **In all.** About 5 proof units. No unit touches `erwpK`, `KW`, the tables or `HandlerLawN`.

**After K1, not kernel units.**
- `Net` (#597) and `Fs` (#769): each kind is one `Opaque` constructor (18 arm lines in 10 files,
  measured on `args`), its representation lemma at both relations, and its models in
  `stdModel`. The kernel theorem covers them with no change.
- A1 may emit lends of capability cells once K1.3 lands.

## 8. Choices for the user (question 7)

- **C1. What the host is claimed to meet.**
  - (a) `ExternN` at `vN` beside `ExternsMeet` at `vC`: two claims per host, each a membership
    in a logical relation.
  - (b) **Recommended.** The theorems take `ExternsMeetN` as their hypothesis, the most general
    form. The trusted claim printed by `bcc trusted` is "behaves, on each run, as a typed closed
    term at the representation" (§3.1). That claim is about behaviour rather than a relation,
    and both memberships follow from it by the two fundamental properties.
  - (c) Keep only Core's claim, and prove `vC` membership implies `vN` membership. Not derived,
    and the relations differ by design (`chain-interpretation.md` §5, D4, D5).
- **C2. Blocking I/O in the first cut.** **In** (recommended): it costs nothing under the call
  reading (§3.2). Suspending I/O answered by the platform (§4.3) **out**: it needs a run relation
  with world steps and a new adequacy theorem, and the watch loop does not need it while the
  scheduler is in the program.
- **C3. The finaliser at the externs' context (K1.3) in K1, or with A1.** **In K1**
  (recommended). Without it no suspending lend of a capability can be written (§6.1), K1.4's
  instance cannot be stated, and A1 is blocked on it. The alternative is to let A1 land K1.3,
  which splits one kernel change across two owners.
- **C4. `HandlerLawN` on the models.** The models use no handler rule. Making
  `stdModel_meetsN` unconditional needs a handler-free fundamental property (`fundamentalN_all`
  minus three cases, by a fragment predicate). **Not in K1** (recommended): the goal carries
  `HandlerLawN` anyway, and the fragment machinery is #840's.
- **C5. Restate `Goal791N` in place, or add a second goal.** In place (recommended, and the
  kernel rule "no parallel copies"). The old statement is the instance `Γx = []`, `R = 1`.

## 9. Risks and what is not verified

- **The representation congruences at `vN`** may not be one-line `simp` rewrites as Core's
  `cC_*` are. `vN`'s `Mut` clause stores the payload family in the world (`mutL`, `famL`), so
  the rewrite has to hold under `famL`. It should, as a `funext` equation of predicates
  (`vC_argsRep`'s form). Not derived. Measure on `read_byte` first.
- **The prophecy argument of §3.1** is not checked in Lean and cannot be, since the host is not a
  Lean term. It is the same kind of claim as SPEC §11's hosts, and it is no stronger.
- **`OrDiverges` and descriptors.** The empty final memory covers capability cells, not
  descriptors (SPEC §11). That a freed cell's descriptor is closed is the host's claim.
- **Pins.** `IORun.every_run` and K1.5 ask for `pins = []`. A program relying on `PinLaw` stays
  outside both. Not in K1's scope.
- **The stop reading's `HandlerLawN` claim** (§4.3 point 3) is argued from the world resuming in
  place. Not derived; obstruction not verified.
- **#844 Tier 2.** A buffer *borrowed* across an `await` is not covered by K1, and neither is
  `read(sock, &mut buf).await`. That is the loans line.
- **A4.** An effectful finaliser (I/O performed on cancel through an effect) is not K1. K1.3's
  finaliser calls an extern directly, at `F 1`.

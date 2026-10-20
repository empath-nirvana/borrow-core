# Compiler: compile from what the checker establishes (#555)

A design for the compiler as a whole: what the checker proves, how it reaches the backend as
data, and the pipeline built on it. It changes no code. Each claim is marked:

- **measured**: a run of `bcc` or `bcc-counts` from `~/repos/borrow-core-l2b-base/.lake/build/bin/`.
  The brief places those binaries at `7a6d275`. That tree is checked out at `3b67803`, the binary
  was built after that commit (11:55 against 11:07), and `bcc-counts --sites
  bench/chain-yield/main.bc` prints `tail-resumptive [(1, 0)] machines 2`, the `3b67803` row of
  `docs/pipeline-architecture.md` §1.3. So the binaries include #544. `main` at `45608db`
  differs from `3b67803` by documents only. Timings were taken on a loaded machine (load average
  25–33), so only their proportions are used;
- **by inspection**: read off the code at `45608db`, with the line cited;
- **hypothesis**: argued here, not checked.

The hard requirements are #555's: every decided law holds and the algebra hard stop applies
(`research/effects/src/decisions.md`, *The decided algebra*); nothing breaks the borrow calculus;
no run-time dispatch to handlers; performance by construction in our IR, LLVM only through
forcing annotations with a check; no hand-rolled pass that recovers what an earlier stage knew;
code size is not a goal outside degenerate blowups; real choices as options with a
recommendation; no syntax decisions.

**Relation to #553.** `docs/pipeline-architecture.md` keeps compiling the erased term and carries
the rest in a site table (route M) and by recognisers (route R). It lists "types to the backend"
as G, later (§2.2, last row). This design makes that row the base. Once the checker returns a
typed term, the table has nothing left to carry, and the recognisers of user code have nothing
left to recognise. `Div` as a handled effect (decision 67, S0 #554), the effect-erasure pass
agreed on #552, and loops U1–U4 are taken as decided and placed in the new pipeline.

## 0. Summary

- **The defect** (§1). The checker computes a type at every node and discards it. `synV`
  returns `Σ A, Res` (`Frontend/Check/Checker.lean:29–30`), and the result `Res` keeps only the
  erasure, the rows and the pins (`Frontend/Check/Rules.lean:28–32`). The backend receives one
  untyped `BoCa.Expr` (`Backend/Driver.lean:107`) and recomputes everything else from it:
  - layouts, by unification, with a retry;
  - rows, by two least fixed points over a 0-CFA;
  - clause kinds, by syntactic recognisers;
  - copies and drops, from free variables;
  - stack slots, from a syntactic pattern and an interval walk.

  Nothing in `Backend/` reads a type, a mode, a lifetime or a qualifier. §1.2 lists 24 facts
  and where each is lost.
- **Making the derivation data** (§2). Three options, judged against the existing proofs. The
  recommendation is **(b), a typed term with an indexed derivation**:
  - The checker returns `t : TExpr`, the derivation's skeleton as data: one node per rule, with
    the rule's types, rows, lifetimes, qualifiers and use masks. The derivation stays a `Prop`,
    `TDerives Δ Γ t j`, generated from `CDerives` the way `CDerivesP` already is
    (`scripts/gen-pin.py`).
  - One projection, `TDerives Δ Γ t j → CDerives Δ Γ t.erase j`, carries FP, adequacy, PinLaw
    and `TiedDer` over unchanged. `Checked.e` is defined as `t.erase`, so the compiled term is the
    checked one by definition.
  - Cost: a generated mirror (as `CDerivesP` is), one more field in each rule builder, and
    `Program.lean`'s theorems restated at `t.erase`. No proof of FP or adequacy changes. Check
    time grows by about one allocation per node (hypothesis).
- **The pipeline** (§3):

      parse → effects → typed elaboration (one, typed schemes) → check → typed term
        → specialise → effect erasure (handler laws at static sites) → state machines
        → typed low IR (modes, lifetimes, ownership) → Wasm, LLVM

  Every stage reads its facts off the typed term or an IR that carries them. One whole-program
  analysis stays, the 0-CFA. It answers a question no stage knew: which closure code reaches a
  `U C` value.
- **Rewrite or staged** (§4). The recommendation is **a new backend beside the old one, with
  the old one kept as a differential oracle until the new one passes the corpus. The frontend
  changes are staged, and both backends consume them.** Every backend IR changes from untyped to
  typed, the effect lowering moves ahead of closure conversion, and the open backend plans
  (B3, effect-lowering 3–9, #531, #509) are parts of the new backend. Staging would carry types
  into IRs and passes that are then deleted.
- **Deleted** (§3.6): `Clos/Types.lean`, `Clos/Poly.lean`, `Clos/Collapse.lean`'s recognisers,
  `Capture`'s and `Unwind`'s analyses (`SFacts`, `UFacts`, `Ops.of`, `tailClause?`,
  `clausesAt`), `Convert`'s ownership inference and pattern marks (`plan2`, `markScoped`,
  `markLitViews`, `polyLets`), the `lowerEffects` retry, the second elaboration, the TIR on core
  (`Frontend/Elab/Infer.lean`), and `drive` outside `reify`. The flow analysis and the target
  emitters are kept and rewritten at typed input.
- **Hard stops** (§7.1). None in the recommended path. One is conditional: the kernel programs
  `Backend/Kernel.lean:35` calls untyped. A compiler of typed terms cannot compile an untypable
  one, and dropping it is hard-stop item 2. One tension needs the user: #555 asks that
  `kernel-counts.expected` be unchanged, and the new lowering lowers some of those counts.
- **Defects** (§7.2). Eight, each with its root fix. The largest:
  - the checker discards the types it computes;
  - the checker re-checks a `def`'s body at every use and never emits `[let-poly]`. That is the
    root of #509 and of most of the check time of `corpus/float-arith.bc` (measured in C2: the
    `check` stage 898 ms of 1217 ms, and 325 ms of 634 ms once each `def` is checked once per
    key; the 44.6 s of 65.8 s first given here did not reproduce);
  - every copy and drop is inferred from free variables;
  - the stack-slot decision re-derives T1.

## 1. What the checker establishes, and where it is lost

### 1.1 The hand-off

- **What crosses.** `Checked` holds `ctx`, `e`, `C`, `sigs`, `ok`, `pins` and `tied`
  (`Frontend/Check/Program.lean:36–43`). From it the backend reads:
  - `k.main.e` (`Driver.lean:107`, `:108`, `:255`, `:256`, `:301`, `:335`, `:408`);
  - `c.pins`, for the report text only (`:380`);
  - the whole `Checked`, passed to `ioMainOf` (`:68`, `:250`). This is the one place a checked
    type is read: `ioMainOf` matches `c.C` (`Frontend/Check/Externs.lean:330–344`), and the
    backend gets the Boolean `m.loopB.isSome` from it.

  A grep of `Backend/` for `sigs`, `CVTy`, `CCTy`, `EffCtx` and `.Ξ` finds nothing. By
  inspection.
- **The erasure.** `BoCa.Expr` has twelve constructors (`Paper/S1_Syntax/Definitions.lean:120–133`)
  and nineteen primitives (`:47–77`). Handlers, finalisers, borrows and folds are encodings over
  them:
  - `hndExpr` (`Core/EffRules.lean:1179`), `thenE` (`:1018`);
  - `withborE = λℓ.λf.(ℓ, f () ℓ)` (`Backend/Clos/Convert.lean:493–494`);
  - the copy and forget axioms, `λx.(x, x)` and `λx.()` (`Paper/S3_Dynamics/Definitions.lean:624`,
    `:629`).

  The erasure drops binder types, ascriptions, every lifetime (`rImmSub` and the others erase to
  `r.e`, `Rules.lean:109–123`), constants' type arguments, `def` references (inlined), names and
  spans. What survives is the name `n` and the tags `qs` of a handler (`hndTerm`,
  `Core/EffRules.lean:1069`), the key `(n, i)` of an operation (`opArgE`, `:848`), and drops
  inserted as `dtorE A` code (`Core/Dtor.lean:326`). By inspection.
- **The program is typed four times and elaborated twice.**
  - Sugar's own inference (`TCx`, `Frontend/Elab/Meta.lean:33`, `:69–75`;
    `Frontend/Elab/Instances.lean:401`).
  - The TIR, inferred on core after the sugar. It calls the checker's `synV`/`synC` per node and
    discards the derivation (`Frontend/Elab/Infer.lean:10–14`, `:54–64`). Its lowering is the
    identity (`Frontend/Elab/Pipeline.lean:25–33`).
  - The checker.
  - The backend's unification (`Backend/Clos/Types.lean:26–39`).

  `checkedOf` runs `checkProgram`, which elaborates (`Program.lean:183`), and then
  `Sugar.elaborateO` again for `ioMainOf` (`Driver.lean:63`). C0 removed the second elaboration.
  Measured in C2 (`bcc compile --timings`, median of 5 interleaved runs, load average 1.7) on
  `bench/sieve`: `check` 43 ms of 78 ms before C2, 39 ms of 74 ms after. The 2590 ms and
  1907 ms of 6753 ms first given here were taken at a load average of 25–33 and did not
  reproduce.
- **Defs at each use.** The checker resolved a `def` to its body and re-checked it at the use
  (`Checker.lean:46–51`, `:53–62`), so `main`'s erasure holds a copy per use. It never emits
  `[let-poly]`. `checkProgram_letPoly` recovers that rule from the copies (`Program.lean:240–246`;
  `Frontend/README.md:199`). C2 checks each `def` once per key and places the body at each use
  (a `use` node, SPEC §3); the erasure still holds a copy per use. Measured in C2 on
  `corpus/float-arith.bc` (`bcc compile --timings`, median of 5 interleaved runs, load average
  1.7): `check` 898 ms of 1217 ms before C2, 325 ms of 634 ms after, 2080 codes and 142937
  nodes after conversion either way. The 44596 ms of 65848 ms first given here did not reproduce
  (C0 measured 783 ms).
- **Kernel programs carry no `Checked`.** `bcc kernel` converts a bare `Expr`
  (`Driver.lean:351–352`, `Backend/Kernel.lean:171–212`), and "the cancels and the shapes are not
  typed" (`Kernel.lean:35`).

### 1.2 Fact by fact

"Proved at" is the checker step. "Lost at" is where it is dropped. "Rebuilt by" is the backend's
substitute. "From the typed term" is what compiling from it gives. All by inspection.

**Types and layouts**

| # | fact | proved at | lost at | rebuilt by | from the typed term |
|---|---|---|---|---|---|
| T1 | each subterm's value or computation type | `synV`/`synC`/`bindHead`/`abortIt`/`synConst` return `Σ A, Res` (`Checker.lean:29–30`, `:246–247`, `:518–519`, `:542–543`; `Consts.lean:222–223`); callers discard it (`⟨_, r₁⟩`, `Checker.lean:66–67`, `:368`, `:376–377`) | `Res` (`Rules.lean:28–32`) | union-find unification without occurs check (`Types.lean:209–236`, `infer` `:359–426`), with `primTy` per primitive (`:257–356`) | layouts from `VTy`; no unifier |
| T2 | the `&` projections of a thunk | `withI`, `proj₁`, `proj₂` | erasure: a `&` is a `case` on a literal injection | `selShape?`/`fwdShape?` (`Types.lean:429–446`); the literal-injection argument as a projection (`:383–393`); the same shapes in `Flow.lean:302–306` | the rule node |
| T3 | operations' answer types | the row at `[perform]` (`OpSig.B`) | erasure | `lowerEffects`' retry with answers as variants when unification fails (`Driver.lean:93–101`; `Ops.wrapsAnswers`, `Capture.lean:162–168`); `freshCopy` so a clause may take other layouts (`:685–689`) | the answer type at each `perform`; no retry |
| T4 | recursive types and which fields close a cycle | `roll`/`unroll` at `μ` | erasure ("regular trees, as the erasure leaves them", `Types.lean:30`) | `sccs`, `backEdges`, `sumBoxes` (`Types.lean:563–693`) | the `μ` in the type; the boxing choice stays a layout decision |
| T5 | a value's width, and whether copying or dropping it does anything | `VTy`; `persistent`, `hasDtorB` | erasure | `width`, `trivial` (`Types.lean:756–771`), read by `copyVals`/`dropVals` (`Flat/Lower.lean:357–365`) | from the type: `i32` slots of 4 bytes (#537 fix 8) |
| T6 | `seq`'s first part is `1` | `[unit-E]` | erasure | not used: `drop u` always (`Convert.lean:669–674`) | no drop of `()` |

**Rows, operations and handlers**

| # | fact | proved at | lost at | rebuilt by | from the typed term |
|---|---|---|---|---|---|
| E1 | the operations a computation may perform or raise | `F_Σ` at every computation; `effLet`, `effSub`, `effThen` | erasure | `SFacts.of`, a least fixed point over the flow, solved twice per capture (`Capture.lean:469–519`, `:1100`, `:1111`); `UFacts.solve` (`Unwind.lean:386–404`); "the rows' information, recovered after erasure" (SPEC.md:3204) | the row at each node |
| E2 | each operation's signature and qualifier: the effect context | `Checked.sigs`, `Checked.Ξ` (`Program.lean:49`); `sigsOkB` | not read by `Backend/` | `Ops.of` collects keys from every `perform`/`raise` and throws when a name has both kinds (`Capture.lean:178–194`) | the signature at each `perform` and `handle` |
| E3 | abortive or control, per operation | `OpSig.abort`; `effPerform`'s `hna`, `effRaise`'s `ha` | erasure | a handler is a control site when some `perform` of its name exists anywhere (`Capture.lean:315`) | the signature |
| E4 | the continuation's qualifier `lin`/`aff`/`unr` | `kRead` reads it off `κ`'s type (`Steps.lean:236`); `[handle]`'s tags | discarded at conversion (`Convert.lean:737–740`) | not rebuilt: a cancel arm for every `κ` (`kapBody`, `Capture.lean:261–266`) | no cancel arm for a linear `κ` (`kappaC_cancel_lin`) |
| E5 | the site an operation reaches | static names (SPEC §19 *Names*); the literal `n` | kept | `Convert` throws if `n` is not a literal (`Convert.lean:755`) | the node's `n` |
| E6 | the clause code at a site | the handler value `H` is a value form of the `[handle]` node (`effHandleV`'s `hH : H.ValFormIn Γ₁`; `ValFormIn` admits values, `Core/EffRules.lean:1201–1204`) | the checker's erasure binds the clauses to variables (`hndTerm … ir ic`, `Core/EffRules.lean:1069`) | `Solver.clausesAt` over the 0-CFA (`Capture.lean:635–641`), and "every relevant site has the same single clause code" (`:712–727`) | the clause is a subterm of the node, or a variable's binding |
| E7 | the clause's kind: tail-resumptive on every path, resume or cancel, keeps `κ` | not a typing fact today. The effects pass knows it for `for` bodies (`forSite`, `Effects.lean:2679–2718`; `pullSite`, `:2720–2754`) and reports it as text (`:2708`, `:2745`) | the report is text | `tailClause?`, `TPath.resume?`, `Tm.paths` (`Capture.lean:573–632`) | classified by the checker on the typed clause (§2.4), a field of the `handle` node |
| E8 | whether the handled body forwards another name's operations | the row `Row.ofEff n E 0 fs ++ S` | erasure | `forward` from `skeys[h.body]`; `noForward` (`Capture.lean:251–257`, `:1133–1135`) | `S` at the node |
| E9 | what a finaliser may raise or perform | `effThen`'s `SD` and the cancel rows `fs` | erasure | `finRaises`, `finSuspends`, `cancelArm` over a syntactic recognition of the `sel` code (`Capture.lean:1116–1131`, `:970–998`) | `SD` and `fs` at the node |
| E10 | that every raise is handled and no suspension escapes | safety (`effPerform`/`effRaise` only at the row; `main` at its row) | — | compile-time errors on the erasure: "a raise where none is handled", "an operation no handler catches" (`Unwind.lean:209`, `:266–276`, `:424`, `:429`); "a suspending call outside every handler" (`Capture.lean:1064–1067`) | unreachable by construction: internal errors |
| E11 | the handler's state (§21) | the clause types, the `mut` parameters (`HInfo.params`, `Frontend/Syntax.lean:338–353`) | elaborated to a state-passing closure | lost: a dispatched call at each resume (`docs/effect-lowering.md` §1.4, 7 programs) | the state's type, for a local variable (§3.3) |

**Modes, lifetimes, ownership**

| # | fact | proved at | lost at | rebuilt by | from the typed term |
|---|---|---|---|---|---|
| B1 | a value is an `imm` or `mut` borrow, at a lifetime | `withbor1`/`2`/`3`, `withload`, `withswap`, slices (`Consts.lean:253–282`, `:146–203`, `:332–430`); `immSub`/`mutSub` | erasure: a borrow is a location word | never consulted. The falsifier cannot tell `withbor1` from `withbor2` (`Backend/Falsify.lean:36–38`). LLVM gets `inttoptr` at every access and no attribute (`Native/Lower.lean:98–101`; no `noalias`, `readonly`, `nonnull`, `dereferenceable` anywhere) | `noalias`/`readonly`/`dereferenceable`/`nonnull` (#531); typed pointers with `getelementptr` (#537 fix 5); lend kinds in the falsifier |
| B2 | an array is only read | the `imm` family's type | erasure | `litView?` guesses `imm` from the callback's `λx.(x, x)` shape (`Convert.lean:401–417`), then a run-time test on tag and length (`Flat/Lower.lean:574–595`) | the type |
| B3 | a lend's lifetime ends inside its block, and no resumption point crosses it | `withbor*U`: a fresh `x` (`hx : Δ.find? x = none`) and the callback at an unwind-only row (`Row.Unwind`, T1) | erasure | `markScoped`, a syntactic match of `let (c, r) = withbor (alloc v) cb; b` with one `free` (`Convert.lean:528–563`); `crossedScopes`, an interval walk over `pollAt` (`Capture.lean:1042–1061`); `frameScopes` (`Flat/Lower.lean:1577–1580`). SPEC §35 says of the crossing case: "No program has one: the typing refuses a resuming operation across a borrow block's body" | a frame slot by the rule. The exception is R1 (`lendR`, a pin), which keeps the cell in the state (SPEC §29) |
| B4 | which slots each subterm consumes | the masks `u`, `w` of `Fam` (`Fam.lean:49–54`); `Ctx.SplitP` | erasure | `plan2` copies every index free in both parts (`Convert.lean:199–210`); drops at unused binders (`:680–682`, `:695–697`, `:802`, `:835`, `:850`); more copies and drops in `Capture` and `Unwind` (`Capture.lean:199–214`, `:998`; `Unwind.lean:217`, `:226`, `:244–249`, `:294`) | a move where the slot is linear, a copy only of a persistent slot used on both sides, and its cost from its type |
| B5 | a copy is of an `imm` borrow, a `!` value or `clone` | `copy`, `copyBang` (`Consts.lean:234`, `:238`); `clone` by elaboration (`Sugar.lean:3298–3304`) | erasure; `clone` lives in the origins (`cloneOrigin`, `Sugar.lean:563–564`) | not recognised: the axiom's `copy` comes from `plan2` because index 0 is free in both halves (by inspection of `plan2` against `Paper/S3_Dynamics/Definitions.lean:624`) | the rule node: a word copy for `imm`, a deep copy only where the type has one |
| B6 | the owned structure a fold walks has no other pointer into it | `foldOwn`, `foldReuse` | erasure | `travShape?`/`foldShape?` (`Convert.lean:308–335`); pointer reversal "safe because the fold owns the structure" (`Flat/Lower.lean:853–855`), an assumption, not a check | the rule node, whose premise is the ownership |
| B7 | a cell is moved by `swap` | the `swap` axiom | erasure | `isSwap` (`Convert.lean:280–290`) | the rule node |
| B8 | a `def`'s identity at each use | `findDef` (`Checker.lean:46–62`) | inlined into the erasure | `polyLet?` recognises a closed λ used twice (`Convert.lean:603–605`); `polySelect` converts the whole program, runs the effect analysis and compares rows, returning `[]` on any error (`Poly.lean:96–105`) | a `use d τ` node: one body per key (#509) |

**Loops, codata, fixed schemes**

| # | fact | proved at | lost at | rebuilt by | from the typed term |
|---|---|---|---|---|---|
| L1 | a fixed point, a counted loop, a bounded recursion | `countFold`, `countTry`, `boundedFix` (`Core/Fundamental.lean:216–228`); the Z combinator (`Core/Fix.lean`), typed as a composite | the primitives survive; the Z combinator is a λ-term | `fixBody?` (`Convert.lean:295–304`), `fixValue` (`:240–260`) | the rule node, or a derived node (§2.4) |
| L2 | a codata value built by a fixed scheme | `unfoldN`, `nuIn`, `nuOut` | erasure | `collapse?` (`Collapse.lean:74–103`) with `armHead?`, `callOfVars?`, `findCall`, and `pureValue`, a syntactic purity guess (`:33–64`); `mergeCodesT`, which reruns `p.types` per round (`:205–225`) | a derived node; after B1, `iterate` and `reify` |
| L3 | a div body's loops, and who consumes them | the frontend's machine (`mAssemble`, `Sugar.lean:1463–1527`); decision 67 makes `Div` a row | the machine is an `unfold` | `drive` around `main` (`Flat/Lower.lean:1125–1154`, `:1465–1480`) | after B1, `iterate` at a row with `Div` (§3.1) |
| L4 | literal tables and views | `lit`, the constants | erasure | `litTable?`, `litTree`, `litClosure` (`Convert.lean:352–397`) | a derived node |
| L5 | `main` returns a loop; `main` is served `Fail[DivError]` | `c.C` (read by `ioMainOf`, `Externs.lean:330–344`); the handler `main_div_error` in the term | `exits` comes from an origin string tag (`Driver.lean:67`) | — | both from the typed term |

### 1.3 What the inventory says about the passes

- **Passes that exist only because of the loss**: `Clos/Types.lean` (T1–T5), `Clos/Poly.lean`
  (B8), `Capture`'s `SFacts`, `Ops.of`, `tailResumptive` and `crossedScopes` (E1–E8, B3),
  `Unwind`'s `UFacts` (E1, E10), `Collapse`'s recognisers (L2), `Convert`'s `plan2`,
  `markScoped`, `markLitViews` and `polyLets` (B2–B5, B8), and the `lowerEffects` retry (T3).
- **Passes that do real compilation work** and stay, at typed input: closure conversion and ANF
  (`Convert`), the construction of state machines (`Capture.machine`), the lowering of abortive
  operations to branches (`Unwind.lowerP`), defunctionalisation (`Flat/Lower.lean:305–336`,
  `:1487–1503`), pointer reversal (`:841–1045`), and the target emitters.
- **The analyses**: the 0-CFA is solved at least six times per compile (`Unwind.lean:412`,
  `Capture.lean:471` twice, `:1176`/`:1182` from `Poly`, `Collapse.lean:232`,
  `Flat/Lower.lean:1598`), and `lowerEffects`' retry doubles three of them. The layout types are
  inferred at least three times (`Collapse.lean:210` per round, `Flat/Lower.lean:1594–1596`,
  `Backend/Counts.lean:61`, `:73`). By inspection. On `bench/sieve` the `effects` and `collapse`
  stages are 1660 ms of 6753 ms (measured).

## 2. Making the derivation data

### 2.1 What constrains the choice

- **The judgments.** `CDerives : LifeCtx → Ctx VTy → Expr → Jdg → Prop`
  (`Core/Fundamental.lean:85`), 92 rules, indexed by the untyped `Expr`. `CDerivesAt Ξ` copies it
  with `RowAt Ξ` premises (`Core/Tied.lean:53`). `CDerivesP` copies it with R1, R2 and `nilDead`
  added, and is generated from `CDerives` by `scripts/gen-pin.py`, which the gate checks for
  staleness (`gen-pin.py:11–12`, `:128`). `TiedDer` is the pair the checker returns
  (`Frontend/Check/Tied.lean:317–318`). FP (`fundamentalC`), adequacy (`adequacyC`),
  `fundamentalC_pin` and `stop_lemma` take these `Prop`s.
- **The checker builds a family, not a derivation.** `Fam T P` holds the masks `u`, `w` (data) and
  `d : ∀ L, Btw u w L → P L` (`Fam.lean:49–54`). The enclosing rule chooses the liveness `L`.
  The builders destructure existentials inside `d` (`rPair`: `fun _ ⟨_, _, hs, h₁, h₂⟩ =>
  .tensorI hs h₁ h₂`, `Rules.lean:47–50`). That is allowed only because `P` is a `Prop`, and
  `Btw` has two constructors, so it cannot be eliminated into `Type`.
- **The checker runs in the kernel.** `Frontend/Check/CrossCheck.lean` evaluates it with
  `decide +kernel`. Proofs cost nothing there, and data costs its size.
- **Growth discipline** (CLAUDE.md, decisions 19–21): no new index on `CDerives`; do not invert
  `CDerives` casually.

### 2.2 The options

**(a) A `Type`-valued derivation.** `CDer : LifeCtx → Ctx VTy → Expr → Jdg → Type`, constructor
for constructor, with side conditions as `Prop` fields, and `CDer.toProp : CDer Δ Γ e j →
CDerives Δ Γ e j`.

- *The erasure lemma*: none is needed. The index is `e`.
- *Checker*: `Fam` must produce `Type`. Every operation that now destructures an `∃` must
  produce a `Σ`, and the liveness of each premise must be computed as data. That is `Fam.lean`
  (370 lines) and every builder: `Rules.lean` (326), `Consts.lean` (509), `Steps.lean` (746),
  `Frontend/Check/Tied.lean` (746), `Pin.lean` (100). A rewrite of the checker's bookkeeping.
- *Theorems*: unchanged through `toProp`. A second mirror is needed for `CDerivesP`, and
  `CDerivesAt` follows from the ties.
- *Compile time*: the derivation is built. Each node stores `Δ` and its context, and every split
  makes two new contexts, so memory is O(nodes × context length). Today it is zero, because
  proofs are erased. The kernel evaluation in `CrossCheck` carries the whole tree.
- *Backend*: it reads an indexed family. Every pass is dependent matching over contexts.

**(b) A typed term with an indexed derivation.** `TExpr`, one node per rule, holding the rule's
non-context arguments (types, rows, lifetimes, qualifiers, names, use masks) and its subterms.
`TExpr.erase : TExpr → Expr` gives the term each rule concludes with. A `Prop` judgment
`TDerives Δ Γ t j` copies `CDerives` with `t` for `e`, and is proved to project:
`TDerives.erase : TDerives Δ Γ t j → CDerives Δ Γ t.erase j`.

- *The erasure lemma*: `Checked.e := c.t.erase`, by definition. `checkProgram_sound` reads
  `CDerives LifeCtx.empty c.ctx c.t.erase (.comp c.C)`.
- *Checker*: `Res` holds `t` where it holds `e`, and `F : Fam T (fun L => TTied pins sigs Δ
  (mkCtx T L) t j)`. `Fam` is unchanged, since the family is still of `Prop`s. Each builder
  makes the node beside the proof: one field per builder, with the types it already has in hand.
- *Theorems*: FP, adequacy, PinLaw, `stop_lemma` and the borrow theorems are untouched. `TTied`
  projects to `TiedDer` at `t.erase`. `Program.lean`'s eight theorems are restated at
  `c.t.erase`, which is definitionally `c.e`.
- *What is generated*: `TDerivesAt` and `TDerivesP`, and their projections, from
  `CDerivesAt`/`CDerivesP`. This is the mechanism `gen-pin.py` already runs. A rule added to
  `CDerives` is picked up by rerunning it.
- *Compile time*: one node per rule application, its fields pointers to types the checker has
  already built. About twice the erasure's allocation (hypothesis). Proofs stay erased.
- *Backend*: it matches plain data. No `CDerives` inversion anywhere.

*Rejected variant (b′)*: the checker returns an annotated term, and a second checker over it
validates the annotations, with a soundness proof. That is two checkers, and the second's
soundness is a second proof of the first's.

**(c) An intrinsically typed elaboration.** The elaborator produces `Tm : LifeCtx → Ctx VTy → Jdg
→ Type` with proofs of side conditions, and "checking" is the projection to `CDerives`.

- *The erasure lemma*: `Tm.erase`, as in (b).
- *Checker and elaborator merge.* The elaborator decides liveness up front, with no `Fam`
  slack, and discharges every side condition as it builds. That rewrites
  `Frontend/Sugar.lean` (5729), `Frontend/Elab/Effects.lean` (3860), the inference modules and
  the checker into one program. It ends the split between an untrusted elaborator and a checker
  (`docs/typed-elaboration.md` §1.4). It loses no soundness: Lean checks the elaborator's code.
- *For it*: one pass over the program, no core syntax in between, errors from one place.
- *Against*: the largest change; every backend pass on an indexed family, as in (a); the core
  syntax that `bcc desugar` prints and the sugar pairs compare (`scripts/check-sugar.sh`) stops
  being the interface.

| | (a) `Type` derivation | **(b) typed term + `Prop` derivation** | (c) intrinsic elaboration |
|---|---|---|---|
| data | the whole derivation | the derivation's skeleton (`t`) | the whole derivation |
| stays `Prop` | side conditions | side conditions, contexts, derivations | side conditions |
| erasure lemma | none (index) | `Checked.e := t.erase` | `Tm.erase` |
| checker change | `Fam` and every builder rewritten | one field per builder | checker merged into the elaborator |
| theorems | through `toProp` | through `TDerives.erase`; statements at `t.erase` | through the projection |
| new code | a mirror, `Fam` at `Type` | `TExpr`, `erase`, generated mirrors | the frontend |
| compile time | O(nodes × context) | O(nodes) | O(nodes × context) |
| backend reads | an indexed family | plain data | an indexed family |

### 2.3 Recommendation: (b)

(b) gives every fact of §1.2 as data, keeps every proof as it is, and costs a generated mirror
the project already maintains for `CDerivesP`. (a) buys nothing over (b): the contexts it would
store are the masks (b) already keeps, and it rewrites the checker's bookkeeping. (c) is the
end state of a different project, the merge of elaboration and checking, and nothing in #555
needs it.

### 2.4 What the typed term carries

| node | carries | fact (§1.2) |
|---|---|---|
| every node | its judgment `j` (a `VTy` or `CTy`), its span | T1, #532's debug info |
| `lam`, `bind`, `effLet`, `tensorE`, `sumE` | binder types; the use mask of the first premise at a split | T1, B4 |
| coercions `immSub`, `mutSub`, `effSub`, `bangE`, `boxI`, `roll`, `nuIn`, … | explicit, with their parameters | T2, T4, B1 |
| `effPerform`, `effRaise` | the row `S` and the signature `o` (`q`, `A`, `B`, `abort`, `fin`) | E1–E3, E5 |
| `effHandleV`, `effHandleVB` | `n`, `E` (qualifiers and types), `fs`, `S`, `A`, `R`, `d`, and each clause's kind | E2, E4, E6–E9 |
| `effThen` | `SM`, `SD`, `S` | E9 |
| borrow constants (`withbor1`…, `withload`, `withswap`, slices) | the lifetime variable, payload types, and the callback row | B1, B3 |
| `copy`, `copyBang`, `forget*`, `swap`, `free`, `alloc` | their types | B5, B7 |
| `foldOwn`, `foldReuse`, `foldImm`, `countFold`, `countTry`, `boundedFix`, `unfoldN` | `F`, `R`, `S`, `C` | B6, L1, L2 |
| `lendR`, `lendLoopR` | the pin | B3's exception |
| **`use d τ t`** (derived) | the `def`, its type arguments, and its checked body `t`; `erase` is `t.erase` | B8 |
| **derived nodes** for fixed schemes | the Z combinator, the scoped lend, literal tables, `io_mk`'s codata | L1, L2, L4 |

- **Derived nodes.** A fixed scheme the backend recognises today (C1–C7, A8 of
  `docs/pipeline-architecture.md` §1.2) becomes a node whose erasure is the scheme and whose
  `TDerives` case is the lemma that types it. These are written by hand, as `CDerivesP`'s extra
  rules are written in `scripts/pin/CDerivesP.tmpl.lean`. The elaborator emits the scheme once,
  and the checker builds the node. Where Core has no single typing lemma for a scheme (the Z
  combinator is typed as a composite, `Core/Fix.lean`), the unit writes it. The scheme's
  recogniser is deleted when its node lands.
- **Clause kinds.** At `[handle]` the checker classifies each clause by a Bool function on its
  typed term, with a lemma that the kind gives the premise of the law the effect-erasure pass
  applies (`tail_resumes`'s shape, #552). This is `docs/pipeline-architecture.md` §8 choice 6,
  "the checker", made concrete. The clause must be in reach: `effHandleV` admits value forms
  (`ValFormIn`, `Core/EffRules.lean:1201–1204`), so the elaborator can emit the clauses in the
  node. Otherwise the classifier follows the variable to its binding. Which of the two is used is
  decided in unit C3 (§6): C3 follows the variable to its binding (the checker keeps the typed
  term of each `x <- return V`), since emitting the clauses in the node changes the erasure. C3b
  keeps that: the premises gain the right unit and the alias of `κ` (SPEC §18, §19), and each
  `handle` node carries the elaboration's record of its site (`HSite`: effect, type arguments,
  handler, slot, site kind, handler state), checked against the node. C3c (#574) emits the
  clauses in the node: each handler's erasure loses its two clause `β`-redexes, the classifier
  reads the node's own pair, and the site record travels with the site to its node, where the
  checker elaborates it to core types and checks its operations against the node's `E`.
- **`use` and sharing.** Two uses of `d` at the same `τ` and the same site assignment have bodies
  whose erasures differ only if they use externs at different indices. A `def` sees only
  persistent externs (`Env.forDef`, `Steps.lean:452–456`). One code per key is sound when the
  body is closed, which is `[let-poly]`'s premise (`closedAt`, `CDerives.letPoly`'s `hcl`). That
  is a check on data, not a reconstruction.
- **Weakening at a use** (C2). Weakening by dead slots (`CDerives.append_dead`,
  `CDerives.insert_dead`) is not enough to place a body checked once at its uses: the checker
  lets a body absorb an unused live slot of the use's context wherever its rules can (a
  persistent slot at a leaf, any slot at `⟨⟩`), and a program can need it to (`x <- return 5;
  return k` with `def k : 1 = ()` is accepted, `x` absorbed by `k`'s body). C2 proves weakening by
  inserted slots whose live ones satisfy the body's absorption (`TDerivesAt.weaken`,
  `TDerivesP.weaken`), read off the typed term's rules (`TExpr.absF`) and recorded on the `use`
  node. The key includes the lifetime context: the checker numbers lifetime binders from it
  (`Δ.freshVar`), so a body's typed term and type differ by it. A use under a lifetime binder or
  a borrow is a key of its own.
- **Spans.** Every node of the core syntax has a span (`Frontend/Syntax.lean:442–536`). Keeping
  them costs one field and gives #532 its source locations.

### 2.5 Against the growth discipline

- No index is added to `CDerives`. `TDerives` is a generated sibling, as `CDerivesP` is.
- No inversion: the backend matches on `TExpr`.
- What grows is the generator's template, by one case per derived node.

## 3. The target pipeline

### 3.1 The stages

| stage | input | output | checked facts it reads |
|---|---|---|---|
| parse | text | surface AST | — |
| effects (`Elab/Effects.lean`) | surface AST | surface with sites, instances, copies; rows with `Div` inferred like any effect (decision 67) | — (it decides; the checker checks) |
| typed elaboration | surface with sites | the core AST, built by typed scheme functions (no `template`, `mTemplate`, `parseComp`; `Sugar.lean:253`, `:570`, `:1057`, 18 call sites). Loops are `iterate`/`count_try`/`bounded_fix` after B2. One run (§1.1). | — |
| check | core AST | `Checked` with `t : TExpr`, `TTied`, `sigs`, `pins`; `e := t.erase` | — (it proves) |
| specialise | `t` | `t` with one body per (definition, type arguments, site assignment, closure codes of its function-typed arguments) (#541 decision) | `use` nodes (B8); closure codes lexically, and from the 0-CFA where an argument's code is not lexical |
| effect erasure (#552) | specialised `t` | a typed middle IR (MIR): no `handle`/`perform` except at named stored-continuation sites; join points; local cells for handler state; `iterate`, `count_try` and `bounded_fix` as loops | sites `n`, signatures, clause kinds, rows, qualifiers (E1–E9) |
| state machines | MIR | MIR with each stored-continuation site's machine | qualifiers (E4: no cancel arm for a linear `κ`), the live variables' types |
| closure conversion | MIR | typed low IR (LIR): ANF with codes and environments, explicit moves, copies and drops, typed pointers, frame slots | use masks (B4), copy rules (B5), modes and lend scopes (B1, B3), folds (B6) |
| layout and defunctionalisation | LIR | LIR with layouts and each closure type's union of codes | types (T1–T5); the 0-CFA for unions |
| targets | LIR | Wasm; LLVM IR | modes (B1) for attributes; tail calls; frame slots |

**Where the effect-erasure pass runs.** On the typed term, before closure conversion. Each rule
is a handler law over Core terms (`tail_resumes`, `handle_fold`, `catch_abort`,
`kappa_cancel_steps`), and the typed term's erasure is a Core term. So each rewrite's
statement is about the terms the semantics is about: `erase (rule t)` is the law's right side at
`erase t`, under the kind's premise. On the closure IR, as `Capture` does today, the law would
have to be restated over a second language. The output is MIR, not `TExpr`: join points and
local cells are not kernel terms. The output is checked by a lint (§5.2), not by a derivation.

**Fit with decision 67 and `docs/loops.md`.**
- U1 (#548) lands first and changes the frontend only.
- Until B1 and B2, a div body is the frontend's machine, an `unfold`. The new backend compiles it
  as stored codata, with a `drive` at `main` (`Flat/Lower.lean:1465–1480`'s behaviour). After B2
  every loop is `iterate` at a row with `Div`, and the effect-erasure rules for `tick` apply:
  - under the runtime, a back edge;
  - under `div_fuel`, a counter test;
  - under `reify`, a state machine.
- Loops U2's class pass is the `Div` inference (`docs/pipeline-architecture.md` §3.7). U3 and U4
  change elaboration only, and the backend sees their join points as `iterate`'s and
  `count_try`'s exits.

### 3.2 Effect erasure, as agreed on #552

Each rule is a handler law applied at a known site. The pass reads only the node's fields.

| clause kind (on the `handle` node) | rewrite | law |
|---|---|---|
| tail-resumptive on every path, its own names unhandled inside (`handlerNames`, `cond2B` at `Checked.flows`) | a direct call of the clause at the `perform` | `op_tail`, `tail_resumes`, `tail_clause_names`, `Checked.unhandledNames` |
| tail-resumptive, with handler state | the state in a local cell of the handler's scope | `handle_fold` (equation stated and proved in its unit) |
| abortive (`raise`, a loop exit) | a jump to the handler's join point | `catch_abort`, `abort_absorbs`, `unwind_prefix` |
| `tick` under the runtime / `div_fuel` | the back edge / a counter test | S0's laws (`docs/pipeline-architecture.md` §4.2) |
| resume or cancel in place | the deciding part at the `perform`; the cancel unwinds in place with `⊥`'s semantics | `kappa_cancel_steps`, `cancel_prefix` |
| resumes once, not in tail, `κ` not stored | frames run at the handler's exit, or a local machine | its own law and unit |
| `κ` stored (generator, task, `reify`) | left for the state-machine stage | — |

**Postcondition**, checked in the gate: no `handle` or `perform` remains except at the named
stored-continuation sites. Any other is a compile error, and the count per program is pinned.

### 3.3 The typed low IR

LIR replaces the closure IR and the flat IR. It is target-neutral, as the flat IR is.

- **Types.** Every variable has its `VTy`, and its layout is computed from it. A borrow is a typed
  pointer that records its mode (`imm`, `mut`), the lend it came from, and the cell's
  allocation class (frame slot, heap, static).
- **Ownership.** Each variable is consumed once, as in the closure IR today (`Clos/Syntax.lean`,
  header). Moves, copies and drops are placed by closure conversion from the masks and the copy
  rules, not from free variables:
  - a linear slot is moved;
  - a persistent slot used on both sides of a split is copied, a word copy at a borrow;
  - a `clone` is a deep copy;
  - a drop is the checker's `dtorE`, or a persistent slot's end.
- **Storage.** A cell lent by `withbor*U` is a frame slot of the code that opens the lend, by
  the rule (B3). A pinned lend (R1) keeps its cell in the suspended state (SPEC §29 *Lowering*).
  The interval walk goes.
- **State machines.** The state at a resumption point is its live variables, typed, so no answer
  wrapping is needed (T3). Narrowing comes by construction: a state holds the variables live at
  its point, not the union of every loop code's environment (#537's 71 words).
- **Handler state** from §3.2 is a local variable when the handler's scope is one code, or a frame
  slot whose address is passed. This is the scalar replacement #537 fix 9 asks for, done in our
  IR, not by LLVM.
- **Loops.** `iterate`, `count_try` and `bounded_fix` are structured loops with loop-carried
  variables (MLIR's `scf` and `iter_args`), lowered to the target's loop or a `musttail`
  self-call.

### 3.4 The targets

- **Wasm.** As `Wasm/Lower.lean` today, from LIR. Frame slots on the shadow stack (SPEC §35).
  Locals are reused across disjoint live ranges, which removes #509's local-count failure
  together with the per-use copies.
- **LLVM.**
  - Typed `ptr` values and `getelementptr` from a base, not `inttoptr` of integer arithmetic
    (#537 fix 5).
  - `alloca` for frame slots.
  - **Forcing annotations, with a check.**
    - `musttail` on every LIR tail call. LLVM's verifier rejects a `musttail` it cannot honour,
      and the build fails then. `classArity`'s prototype classes stay (`Native/Lower.lean:557–572`).
    - `alwaysinline` only where LIR asks for it, with a check that no call to the function
      remains in the optimised IR.
  - **Facts.** `noalias` and `readonly` from `mut` and `imm`, `dereferenceable` and `nonnull`
    from "a live borrow points at a live cell" (#531). Each cites its borrow guarantee. These are
    facts, not forcing annotations. Under "performance by construction" they may be emitted for
    correctness and for LLVM's benefit, but no performance target may depend on LLVM using them.
    The work they would buy (handler state in a register, #537 fix 9) is done in LIR (§3.3).
    This is a reading of the user's rule, and it changes #531's goal. §8 choice 6 asks the user.

### 3.5 Kernel programs and hand-written core

Every input is a typed term. A kernel program enters as a core-syntax program that `bcc` checks,
or as a `TExpr` with a `TDerives` proof written in `Backend/Kernel.lean`. There is no untyped
generic path, so no recogniser survives for "table-less input"
(`docs/pipeline-architecture.md` §3.4). The untyped kernel programs are §7.1's conditional hard
stop.

### 3.6 Every existing pass

| pass | verdict | why |
|---|---|---|
| `Frontend/Sugar.lean` templates | **rewritten** (B2 and C0): typed scheme functions | strings carry no law (`docs/pipeline-architecture.md` §9.2 defect 2) |
| second `elaborateO` (`Driver.lean:63`) | **deleted** (C0) | `Report` carries the elaboration |
| TIR on core (`Elab/Infer.lean`, `Tir.lean`, `Pipeline.lean`'s lowering) | **deleted** (C1) | the typed term is the checker's; `implicitCopy` (`Elab/Copies.lean:140`) runs on `t` |
| `Clos/Convert.lean` | **rewritten**: closure conversion and ANF into LIR, from MIR | the conversion is real work; `plan2`, `markScoped`, `markLitViews`, `markUbinds`, `polyLets`, `isSwap`, `fixBody?`, `travShape?`, `litTable?` go (B2–B8, L1, L4) |
| `Clos/Poly.lean` | **deleted** | `use` nodes and specialisation (B8) |
| `Clos/Capture.lean` | **split**: the state-machine construction is **rewritten** on MIR; `Ops.of`, `SFacts`, `tailClause?`, `tailResumptive`, `clausesAt`, `noForward`, `finRaises`, `finSuspends`, `crossedScopes` are **deleted** | §3.2 does their work from the node's fields |
| `Clos/Unwind.lean` | **rewritten** as §3.2's abortive rule; `UFacts` and the compile-time "no handler" errors **deleted** | E1, E10 |
| `Clos/Collapse.lean` | **deleted**: the codata recogniser (L2) by derived nodes, `mergeCodesT` by specialisation keys | — |
| `Clos/Types.lean` | **deleted** | T1–T5 |
| `Clos/Flow.lean` | **kept**, run once on LIR (and on MIR for specialisation) | which closure code reaches a `U C` value is not a typing fact |
| `Clos/Interp.lean` | **replaced** by an LIR interpreter | the stage check against the goldens stays |
| `Flat/Lower.lean` | **rewritten** as LIR's layout and lowering; defunctionalisation, pointer reversal (now from `foldOwn`/`foldReuse` nodes), count loops kept; `drive` only for unfold-based codata until B2, then only inside `reify` | — |
| `Flat/Interp.lean` | **replaced** by the LIR interpreter, keeping its checks (unwritten reads, live frames) | — |
| `Wasm/*` | **kept**, from LIR; local reuse added | — |
| `Native/*` | **rewritten** at typed pointers, attributes, `alloca` slots | §3.4 |
| `Backend/Falsify.lean` | **kept**, with lend kinds from the typed term (B1) | — |
| `Backend/Counts.lean` | **kept**; `--sites` reads LIR and adds the postcondition count | — |

## 4. Rewrite or replace in stages

### 4.1 The options

**R: a new backend, the old one as oracle.** `Backend2/` (name provisional) consumes `c.t`. The
old backend consumes `c.t.erase`, which is today's `c.e`. Both start from one `Checked`, so the
oracle compares two compilations of one checked program. The new backend runs the stage
interpreters against the goldens, and its output is compared with the old one's. It replaces
`bcc` once it passes the whole corpus, the kernel programs, `book/` and `bench/`. Then the old
backend is deleted.

**S: replace stage by stage.** Each new stage feeds the old next stage, through an adapter that
erases what the old stage cannot hold. The order runs front to back: types into `Clos.Tm`, then
`Types.lean` replaced, then `Poly`, then the effect passes, then the flat IR.

| | R | S |
|---|---|---|
| one compiler at all times | no: two until the switch | yes |
| adapters | none | one per stage boundary, each deleted later |
| reconstruction passes alive in the middle | in the old backend only, which is the oracle | in the shipping compiler: until its stage is replaced, `Types.lean` re-unifies what the adapter erased |
| the IR changes | made once: MIR and LIR, typed from the start | the closure IR and flat IR gain types in steps, then are replaced anyway (§3.6) |
| the order change (effect erasure before closure conversion) | built in that order | `Capture` and `Unwind` run on the closure IR after `Convert` today. Moving them is a replacement, not a step |
| the open backend plans (B3, effect-lowering 3–9, #531, #509) | built once, in the new backend | built in the old IRs, or deferred until each stage is replaced |
| risk | the new backend lags the language while it is built | each step is small; the end state is the same |

### 4.2 Recommendation: R for the backend, S for the frontend

- **The backend changes at every level at once.** Its input type changes (`Expr` → `TExpr`).
  Every IR becomes typed. The effect lowering moves ahead of closure conversion. Almost every
  pass is deleted or rewritten (§3.6). Under S, each intermediate state runs a typed stage
  feeding an untyped one, and the untyped one reconstructs what the adapter dropped. That is
  #555's defect, kept alive on purpose for the length of the migration.
- **The planned backend work is the new backend.** B3, effect-lowering units 3–8, #531's
  attributes, #509's sharing and #540's narrowing are §3.2–§3.4. Building any of them in the old
  IRs first is building a recovery to be deleted.
- **The frontend changes are prerequisites of both, and small steps.** One elaboration (C0), the
  typed term (C1), derived and `use` nodes (C2), clause kinds (C3), typed schemes (B2). Each
  keeps the old backend running unchanged, since `t.erase` is today's `e`. So they are staged.

### 4.3 "Compiler never stale" during the change

- The old backend stays `bcc` until the switch. Every frontend feature lands as today, with its
  lowering through the old backend and a running corpus program.
- New backend features are not built in the old backend. Effect-lowering units 3–9 and B3 are
  absorbed (§6.2). Bug fixes in the old backend continue.
- The new backend has a pass list in the gate: the corpus programs it compiles to the golden.
  The list may only grow, and every frontend change must keep it. A feature that lands in the
  frontend while the new backend is in progress either passes there, or is added to the new
  backend's list of known failures with its unit named. The list must be empty at the switch.
- `bcc compile --backend old|new` (spelling provisional) selects the backend. The gate runs both
  until the switch.

## 5. The test before building

### 5.1 What must hold

- Every corpus program's output, every golden, every exit status and `live 0` are unchanged, on
  both backends.
- `counts.expected`: `allocs`, `indirect` and `copies` only drop.
- `kernel-counts.expected`: #555 says unchanged. CLAUDE.md's *Changing Core* allows "a changed
  count is explained". The new lowering lowers some kernel counts, for example `nested-log-outside
  0 2 0`, where `withLog`'s answer is a state-passing closure, and `take 2 2 0`. This is §8
  choice 5.
- The falsifier's four modes (`scripts/falsify.sh`) pass, with lend kinds from the typed term.

### 5.2 Reconstruction is gone, and the gate keeps it gone

1. **Each pass of §1.3 is deleted**, and its row in §1.2 names the field that replaced it.
2. **An import fence.** The new backend's modules import only the typed term
   (`Frontend/Check/Typed.lean`, name provisional) and their own modules. Not `Frontend.Elab`,
   `Frontend.Sugar`, `Backend.Clos.*` or `BoCa.Expr`'s constructors. A script in the gate checks
   the import graph.
3. **A ban list.** No unifier, no fixed-point solver over rows, no recogniser of user code in the
   new backend: no function that takes an untyped `Expr`, and none of the names deleted in §3.6.
   The script fails on a match.
4. **Lints verify, never derive.** After each stage the gate runs a lint of its output (GHC's Core
   Lint): every variable has its type, every node's annotation agrees with its children's, every
   variable is consumed once, every pointer has a mode and an allocation class. A lint may reject.
   It may not fill in an annotation. A missing annotation is the producing stage's bug.
5. **The effect-erasure postcondition** (§3.2), pinned per program in `counts.expected`.
6. **`bcc-counts --sites`** reports a "recognised" column, the sites lowered by a recogniser rather
   than a node's field. It is pinned at 0.

### 5.3 Predicted #537 rows

Ratios are ours over Rust, from `bench/README.md`. All predictions are hypotheses. Each names the
unit of §6.1 it rests on.

| row | now | predicted | units | why |
|---|---|---|---|---|
| sieve | 5.63× | ≤ 1.4× (sieve-for 1.30×) | B2, N4 | `while` is `iterate`; the runtime's `tick` is a back edge |
| chain-yield | 2.10× | ≤ 1.2× (chain-for 0.99×) | B2, N2, N4 | `yield` a direct call; `range`'s `while` native |
| chain-gen | 21.5× | ≤ 1.3× | N2, N4, push stages (effect-lowering 7) | as `docs/pipeline-architecture.md` §6.2 |
| gen-tree | 1.72× | ≤ 1.4× | N2 | the re-injection after the right call is the abortive rule's identity, so the call is a tail call (#537 fix 3) |
| gen-tree-cb | 1.96× | ≤ 1.4× | N2 | the same cause (`bench/README.md`, *gen-tree*) |
| raise-small | 1.30× | ≤ 1.1× | N2 | an error is a jump out of `count_try`'s loop, not a loop-carried word (#537 fix 6) |
| handlers-di | 0.98× | ≤ 0.9× | N2 | the clock's state a local variable in our IR (#537 fix 9), not a load and store per step |
| async-tree | 0.84×, indirect 201 | ≤ 0.84×, indirect 0 | N3, N1 | one code per task body; copies keyed by `use` |
| sum | 1.88× | not predicted | N5 | typed pointers and aligned arrays enable vectorisation; #537 did not measure the gain |
| n-body | 1.78× | unchanged | — | records and fixed-size arrays (#489, #72) |
| others | — | unchanged ± noise | — | — |

**Compile time.**
- The second elaboration goes (C0): `elaborate`'s 28% of `bench/sieve`'s total in the run of
  §1.1 (measured proportion).
- Checking each `def` once per key, not once per use (C2, choice 7), removes most of
  `float-arith`'s 44.6 s `check` (hypothesis; the measured share is check time, and the def
  re-checks are the dominant cause by inspection, not measured).
- #509's reproduction (`print_f64` called twice) compiles one copy of the printer (N1).

**Counts.** The (b) and (c) programs of `docs/effect-lowering.md` §5.1 reach `indirect 0` after
N2 and N3. (a) and (d) are unchanged.

### 5.4 Kill criteria

1. **The typed term** (C1): some rule's `TDerives` case does not project to `CDerives` without
   changing a `CDerives` rule or a theorem's statement beyond `e := t.erase`. Stop and report: the
   recommendation of §2.3 is wrong there.
2. **Check time** (C1): the corpus check time rises by more than 25%. Re-examine the node
   representation before going on. Measured in C2 (`bcc check` on every program, median of 5
   interleaved runs, load average 1.4–3.5): the corpus (579 programs) 41.8 s before C2 and
   38.1 s after; `bench/` (24 programs) 4.8 s and 3.2 s.
3. **The inventory is incomplete**: a new-backend stage needs a fact that is neither on the typed
   term nor the 0-CFA's. The fact is added to the typed term (§2.4) and a row to §1.2. It is not
   recovered in the backend. Three such additions after N2 mean the inventory method was wrong.
4. **Meaning**: any unit changes an output, a golden, an exit status, `live 0` or a falsifier mode.
   That is the hard stop.
5. **The rewrite stalls**: the new backend's pass list does not grow across two consecutive units
   after N1. Re-examine R against S at that point.
6. **Performance**: at the switch, a #537 row is slower than the old backend's by more than 10%,
   or a count of `counts.expected` rises.

## 6. Build plan

### 6.1 Units, in dependency order

Frontend units keep the old backend running. Each lands with its spec text, its acceptance
programs, `counts.expected` and the desugar diff. A unit that touches `Core/`, `Frontend/` or
`Backend/` runs `make gate-full`.

| # | unit | needs | acceptance |
|---|---|---|---|
| C0 | **One elaboration.** `Report` carries `Elaborated`; `checkedOf` and `ioMainOf` use it; `exits` from the term, not an origin tag | — | every output unchanged; `--timings` has no second `elaborate` |
| C1 | **The typed term.** `TExpr`, `erase`, `TDerivesAt`/`TDerivesP` and projections generated (`gen-pin.py` extended, `--check` in the gate); `Res.t`; `Checked.e := t.erase`; `Program.lean`'s theorems at `t.erase`; the TIR on core deleted, `implicitCopy` on `t` | C0 | `bcc erase` byte-identical on the corpus; `CrossCheck` unchanged; axioms within the three; kill criteria 1, 2 |
| C2 | **`use` and derived nodes.** `use d τ`; the derived nodes for fixed schemes, each with its typing lemma; optionally (choice 7) one check per key with `CDerives.append_dead` for the context | C1 | `erase` unchanged; one derived node per recogniser of §1.2 (L1, L2, L4, B3, B7) |
| C3 | **Clause kinds**, classified by the checker at `[handle]`, each with the lemma that gives its law's premise | C1, B2 if `tick` | every handler of the corpus classified; the report rendered from the field (`docs/pipeline-architecture.md` §9.2 defect 3) |
| C3b (#571) | **Kinds complete, sites on the node**: right-unit and alias steps in the premises and laws; site names, site kind and handler state on the `handle` node, cross-checked; `exits` from the platform handler's site; condition 2 stated over the rows | C3 | `kinds.expected` changes only by the new laws; every other output unchanged |
| C3c (#574) | **Self-contained handler sites**: the clauses inline in `hnd`, read by the classifier from the node (no chase through `Env.vals`); the site record at core types in the frame of its node, its operations checked equal to the node's `E` | C3b | `erase` changes only by removing the clause `β`-redexes; every run output, golden and count unchanged |
| C4 (#575), C4b (#610) | **Condition 2 as a checked fact**: the frames inside each handled computation (`inside`) and the program's flow record (`Checked.flows`), with the run invariant; condition 2 over the names each clause's own code performs or raises (`handlerNames`), which bound its work's runs (`tail_clause_names`); a bound per node stated (`Checked.FramesPerNode`) | C3c | `handled.expected`: every direct call of the old backend agrees; every other output unchanged |
| S0 (#554) | **running** | — | its own |
| B1 | `Div` in the kernel, as `docs/pipeline-architecture.md` §3.7 | S0 | as there |
| B2 | the `Div` elaboration as typed schemes; the remaining templates converted (no `parseComp` on the elaboration path) | B1, U1, C1 | as there; `template`/`mTemplate` deleted |
| N1 | **New backend, pure fragment.** Specialisation; closure conversion into LIR; layouts from types; flow once; Wasm and LLVM from LIR; LIR interpreter; the gate's fence, ban list and lints | C2 | every effect-free corpus program at its golden on both targets; #509's reproduction compiles one printer copy; `aff-higher` indirect 0 |
| N2 | **Effect erasure** (§3.2), each rule with its proof over Core; the postcondition | N1, C3 | the (b) and (c) programs of `docs/effect-lowering.md` §5.1 at their predicted `indirect`; gen-tree ≤ 1.4×, raise-small ≤ 1.1×, handlers-di ≤ 0.9× |
| N3 | **State machines** at stored-continuation sites, on MIR, typed; one code per task body | N2 | async programs at `indirect 0` except class (a); async-tree ≤ 0.84×; falsifier modes |
| N4 | **Codata and loops**: `unfold` and `drive` until B2; `iterate`, `count_try`, `bounded_fix` as LIR loops; `tick`'s rules | N2; B2 for `iterate` | sieve ≤ 1.4×, chain-yield ≤ 1.2×; no `drive` outside `reify` |
| N5 | **Target facts**: frame slots by rule; typed pointers and `getelementptr`; `musttail` and `alwaysinline` with their checks; `noalias`/`readonly`/`dereferenceable`/`nonnull` per choice 6, differential at `-O2` | N1 | `scopeSites` framed counts no lower; corpus at goldens with attributes on |
| N6 | **Switch.** The new backend is `bcc`; the old backend and its interpreters deleted | N1–N5, pass list complete | §5.1 on the whole corpus, `book/`, kernel programs and `bench/`; kill criterion 6 |

**Order.** C0 → C1 → C2 → C3 alongside S0 (running) and U1 (running). Then B1 → B2 and N1 → N2 →
N3, N4 (after B2), N5 → N6. Frontend loop units U2–U4 and #58 go as their own plans say.

### 6.2 Every open plan, mapped

| plan | verdict | where |
|---|---|---|
| `docs/pipeline-architecture.md` S0 (#554) | **kept**, unchanged | first, running |
| B1 | **kept** | after S0 |
| B2 | **kept**, merged with "no string templates" | after B1, U1, C1 |
| B3 | **merged** into N2 and N4 | the new backend |
| N3 site table (effect-lowering unit 9) | **dropped** | its entries are fields of the typed term: clause kinds (C3), copy groups (`use`), handler state (E11) |
| effect-lowering 3 (classify; native handler state) | **merged** into N2 | — |
| 4 (resume or cancel in place) | **merged** into N2 | — |
| 5 (one code per codata value; copies merged) | **merged** into N3 and N1 | copies merged by `use` keys, not by comparing code |
| 6 (specialisation S1) | **merged** into N1 | — |
| 7 (push stages, at elaboration) | **kept**, frontend | after B2 |
| 8 (abortive pass-through, loop exit) | **merged** into N2 | #537 fixes 3 and 6 |
| #540 (`loops-as-loops`) | **interim**, in the old backend, on its own acceptance | its narrowing is by construction in LIR (§3.3); its loop recovery is not ported |
| loops U2 (#549) | **kept** as `docs/pipeline-architecture.md` §3.7 says: class pass as `Div` inference in B2, counted machine half held for S0 | frontend |
| U3 (#550), U4 (#551) | **kept**, frontend | after U2 |
| L3 #531 | **merged** into N5, with its performance goal moved into LIR (§3.4, choice 6) | — |
| L4 #532 | **kept**, after N6: debug info from the typed term's spans; stack-depth guard and C linking unchanged | — |
| #216 (clause multiplicity) | **kept**, kernel unit, independent; its grade is a field of the `handle` node, read by N2 (an affine capture moved into a branch) | after C3 |
| #58 (implicit copies of `imm`, E1) | **kept**, frontend, independent; the inserted copy is a `copy` node, a word copy by type | any time |
| #509 | **fixed** by C2 (`use`) and N1 (one body per key); choice 7 for check time | — |

## 7. Hard stops and defects

### 7.1 The algebra hard stop

No step of the recommended path changes a decided equation:
- The effect-erasure rules are the handler laws, applied under their premises (§3.2).
- No runtime rule is added. The compile-time errors of E10 become internal errors on input that
  typing excludes.
- No program the algebra gives a meaning to is rejected.

**Conditional, hard-stop item 2.** A compiler of typed terms cannot compile an untypable term.
`Backend/Kernel.lean:35` says "the cancels and the shapes are not typed". The programs:
- the cancels: `cancel-reraised`, `cancel-reentered`, `cancel-propagated`;
- the shapes: `loop-tail`, `loop-captured`, `recursive-yield`, `two-callees`,
  `two-callees-tail`, `forward`, `forward-cancel`, `multi-shot`, `poly-id`.

I have not checked which of these have a typing. Each one that has a typing is given its typed
term in N1–N3. One that has none would leave the compiled set, which is item 2. It is reported to
the user, not dropped, and the old backend stays its oracle until the user decides (§8 choice 3).

**Not a stop, a tension.** #555 requires `kernel-counts.expected` unchanged, and the new lowering
lowers some counts (§5.1). §8 choice 5.

### 7.2 Defects

1. **The checker discards the types it computes** (`Checker.lean:29–30`, `:66–67`;
   `Rules.lean:28–32`). The backend then infers them again by unification (`Types.lean:26–39`):
   "the source's typing derivation guarantees that the erasure has these types". Root fix: C1.
2. **The checker re-checks each `def` at every use and never emits `[let-poly]`**
   (`Checker.lean:46–62`; `Frontend/README.md:199`). Every use is a copy in the erasure. That is
   the root of #509 (the backend README's "a definition is substituted at each use") and the
   likely cause of most of `float-arith`'s check time. Root fix: C2's `use` node and choice 7
   (landed: each `def` checked once per key; the erasure keeps a copy per use until N1).
3. **Every copy and drop is inferred from free variables** (`plan2`, `Convert.lean:199–210`), not
   read from the derivation's splits. Whether a copy does anything is decided by layout
   triviality (`Types.lean:757–769`), and `imm` against `mut` is never consulted. Correct for a
   well-typed term, by the derivation's splits, but nothing ties the two. Root fix: N1 from the
   masks.
4. **The stack-slot decision re-derives T1** (`markScoped`, `Convert.lean:528–563`;
   `crossedScopes`, `Capture.lean:1042–1061`). SPEC §35 says no program has the crossing case,
   because typing refuses it. Root fix: frame slots by the `withbor*U` rule (§3.3).
5. **A swallowed error in a correctness-relevant analysis.** `polySelect` returns `[]` when its
   conversion or its effect analysis fails (`Poly.lean:102`, `:104`), and the let is then
   converted once. I have not checked what the backend does when such a let's uses need
   different lowerings. Root fix: N1's `use` keys; `Poly` deleted.
6. **Pointer reversal assumes exclusive ownership** (`Flat/Lower.lean:853–855`), a fact the
   `foldOwn`/`foldReuse` rule proves and the backend never receives. Root fix: the rule node
   (B6).
7. **Trusted string channels beside the checked term**: `exits` from an origin tag
   (`Driver.lean:67`); `clone` known only in the origins (`Sugar.lean:563–564`, `Driver.lean:58–59`);
   the lowering report as text (`docs/pipeline-architecture.md` §9.2 defect 3); `ioWrapper` builds
   source text and parses it (`Externs.lean:347–361`). Root fix: C0, C1, C3. `ioWrapper` serves
   the model run only and can stay until a unit owes it a law.
8. **The qualifier discarded at conversion** (`Convert.lean:737–740`), already
   `docs/pipeline-architecture.md` §9.2 defect 1. Here it is the `handle` node's `E`.

**Unverified.** Every row of §5.3, the compile-time effect of C1, the typability of the kernel
programs of §7.1, and the cost estimates of §2.2. #540, U1 and S0 were not read for this design
beyond their branches' heads.

## 8. Open choices for the user

1. **Making the derivation data**: **(b) a typed term with a generated `Prop` derivation
   (recommended)**, (a) a `Type`-valued derivation, or (c) an intrinsically typed elaboration
   (§2.2).
2. **Rewrite or staged**: **a new backend with the old one as oracle, the frontend staged
   (recommended)**, or stage-by-stage replacement of the backend (§4).
3. **Untyped kernel programs**: **give each a typed term, and report any that has none
   (recommended)**; keep an untyped path for them (recognisers survive for that input); or retire
   them (hard-stop item 2, needs a decision).
4. **Where effect erasure runs**: **on the typed term, before closure conversion
   (recommended)**, so each law is stated over Core terms; or on LIR, where `Capture` runs today.
5. **`kernel-counts.expected`**: **drops allowed, each explained, as `counts.expected` and
   CLAUDE.md's *Changing Core* allow (recommended)**, or held unchanged as #555 states. Holding them
   would keep those programs on today's lowering.
6. **`noalias` and its kin**: **emitted as cited facts, with no performance target resting on
   LLVM's use of them, and the optimisation they stand for done in LIR (recommended)**; or #531 as
   filed, with performance expected from LLVM.
7. **Checking a `def`**: **once per key (definition, type arguments, site assignment), reused at
   each use by weakening (`CDerives.append_dead`) (recommended)**; or at each use, as today, with
   only the `use` node added. The first changes the checker's cost, not its rules.
8. **Fixed schemes**: **derived nodes with their typing lemmas (recommended)**, or the
   recognisers kept as exact tests (route R of #553).

## 9. Reproduction

All runs use `~/repos/borrow-core-l2b-base/.lake/build/bin/` (§0's note on the version), from that
directory, writing to a scratch directory.

- `bcc compile --timings bench/sieve/main.bc -o x.wat`, and the same for
  `bench/chain-gen/main.bc` and `corpus/float-arith.bc`: §1.1's and §1.3's timings.
- `bcc-counts --sites bench/chain-yield/main.bc`: the version check of the header.
- The greps of §1.1: `grep -rn 'sigs\|CVTy\|CCTy\|EffCtx' Backend/`, and `grep -n 'noalias\|readonly\|dereferenceable\|nonnull' Backend/Native/`.

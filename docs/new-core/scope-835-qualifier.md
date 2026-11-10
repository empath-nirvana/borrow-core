# #835: an operation qualifier for suspending under a borrow, and the handler contract (superseded)

Superseded: its §4 claim that `HandlerLawN` can go is superseded by the decision to keep
`HandlerLawN` as the named assertion for `effHandleV`, `effHandleVB` and `reify`, tracked in #838;
`Goal791SchedN` and `CNW835N.lean` are gone. The current design is `chain-interpretation.md` (the
interpretation at the typed world `KW`, the departures from Core, what is proved and what is open),
`scope-835-tables.md` §10 and SPEC §62; the configurations are indexed in `configurations.md`. The
body below is the record of the qualifier design.

Kernel target: none. This note is a design scope; it changes no Lean.

It replaces two things on `rule-791-kstop`:
- the scheduler names `Sched` of `Restrict835` (`Core/Chain/Restrict835N.lean`) and the parameter
  `Sch` of the relation at the typed world (`Core/Chain/CNW835N.lean`);
- the single top-level scheduler `n₀` of `Goal791SchedN` (`Core/Chain/Goal791N.lean`).

In their place it puts:
- a qualifier on each operation, read off the row type at the perform site;
- a contract every handler of a qualified operation meets, at any depth;
- a top-level theorem over the program and an optional stack of handlers.

No definition or theorem below names `await`, `spawn` or a scheduler. The scheduler is one
handler that meets the contract.

It builds on `scope-835-restriction.md` (the restriction it replaces), `scope-835-lendexit.md`
(the two orders `KW.Owed`/`KW.OwedR`), `scope-835-tables.md` §1, §9 and §10 (the tables at `KW`,
the modes, the relation at `KW`), `../archive/new-core/scope-835-handlers.md` §1–§2 (our conditions against the
paper), and the independent review `scratch-archive/rule791/review-cnw.md` (F1, F2).

The paper is Tang, Hillerström, Lindley & Morris, *Soundly Handling Linearity*, PACMPL 8 (POPL
2024), article 54, cited as [SHL] with its section, figure and rule names.

## 1. The qualifier

### 1.1 What it is

Each operation carries one more Boolean beside its qualifier `q`. This note calls it `ub` ("may be
performed under a borrow"). The spelling is provisional.

- `OpSig` gains `ub : Bool := false`.
- `CTy.eff` gains the same field, next to `q`. A row's table is built from the `.eff` layers
  (`tabN`, `tabF`), so the type has to carry the field. Otherwise the table built at the perform
  site cannot read it.
- `Row.ofEff` gains markers `us : Nat → Bool := fun _ => false`, beside the existing `cs` (`rc`).
- `OpSig.Sig` (`Core/EffFin.lean`) compares `ub` as it compares `rc`, so `[sub]` neither adds nor
  removes it.

The precedent is `rc`: a per-operation Boolean on `OpSig` and `CTy.eff`, carried by `Sig`, with
`Row.ofEff` markers that the handler rules pass (`effHandleV`'s `cs`).

### 1.2 What it means

An operation marked `ub` may be performed while a borrow is open in its continuation. "Open in
its continuation" means one of two things lies between the `perform` and the handler that
catches it:
- a lend frame (a `Const791` callback); or
- a tail or last clause holding a continuation captured at a `ub` operation (§2.4).

**In the relation.** At the typed world the qualifier fixes an entry's order:
- An entry marked `ub` owes its continuation along `KW.Owed x f y`: `ExtP` at the floor `f` the
  stop chose, with `FoldInv` kept at every floor at or above `f`.
- An unmarked resuming entry owes along `KW.OwedR x y`: `ExtR` at the share, with no floor. That
  is the order `vN`'s `U` reads (`vN_thunk_iff_kapRelR`).
- An abortive entry owes nothing, so the mark is not read there.

This is `KW.OwedS S m` (`TabK835N.lean`) with the test `S m` replaced by the layer's own `ub`.

**The cancel row of a `ub` entry.** Every entry of that cancel row owes along `KW.Owed`, whatever
its own mark. The mode becomes a Boolean `μ`:
- an entry's order is read at `μ || ub`;
- its cancel row is read under `μ || ub`;
- the top mode is `false`.

This is `finSched S m n = S m ∨ S n` (tables §1) with names replaced by marks. The reason is
unchanged: such a cancel run runs inside the continuation, under the lends live there.

**The typing condition that makes the order sound.** Every resuming operation a lend's callback
may perform is marked `ub`:

```lean
def Row.UBOnly (S : Row) : Prop := ∀ o ∈ S, o.abort = false → o.ub = true
```

This replaces `Row.SchedOnly Sched` (S1) on each constant's callback row. It reads the type,
where (S1) read a name set.

### 1.3 How it maps to [SHL]

[SHL] classifies each operation by the control-flow linearity of its continuation:
- **The annotation.** `A ↠^Y B` (§2.2; Fig. 1). "Control-flow-linear operations can be used in
  contexts which may contain linear resources, whereas control-flow-unlimited operations cannot"
  (§2.2).
- **Lifted to rows.** `K-Present`, `K-ExtendRow` (Fig. 2).
- **Read by sequencing.** `T-Seq` at `Y = ◦` asks `Δ ⊢ R : ◦` when the rest of the computation
  holds linear values (Fig. 4, §3.2).
- **Read by the handler.** `T-Handler` gives `rᵢ` the value linearity `Yᵢ` (Fig. 4). It reads
  the operation's signature, not the row's kind, so `Row◦ ≤ Row•` never lets a `◦` operation be
  handled as `•` (§2.2, last paragraph; §3.2).

`ub` is a second annotation of the same kind. It says *where* the continuation may be resumed,
not *how many times*.

| [SHL] | `ub` | Verdict |
|---|---|---|
| `A ↠^◦ B`: the continuation may hold a linear value (§2.2) | `ub`: the continuation may hold an open borrow (a live lend frame, or a `ub` continuation in a clause) | **same kind**: a classification of what the continuation holds, on the operation |
| `T-Seq`, `Y = ◦`: the context of `N` holds linear values, so `Δ ⊢ R : ◦` (Fig. 4) | a lend's callback holds the borrow, so its row is `Row.UBOnly` | **matches**: the condition sits where the context is captured, here the callback row |
| `K-Present`, `K-ExtendRow`: a row's kind from each label (Fig. 2) | `CTy.UBOnly` lifted through the layers (`CTy.SchedOnly`'s recursion, marks for names) | **matches** |
| `T-Handler` reads the signature's annotation (§2.2, §3.2) | each handler rule reads the handled operations' marks (`Row.ofEff`'s `us`) | **matches** |
| Fig. 5, trivial subtyping: the same signature | `OpSig.Sig` keeps `ub` | **matches** (§8, R10 has the semantic latitude) |
| `T-ShallowHandler` (§6): a handler holding linear variables needs `Δ ⊢ R : Y` for the operations it does not handle, "because the shallow handler may be captured as part of the continuations of these unhandled operations in outer handlers" | a tail or last clause holding a `ub` continuation needs its own row's resuming operations marked `ub` (§2.4) | **matches**: the same reason, at a clause instead of a shallow handler |
| `Y ∈ {◦, •}` counts resumptions | `ub` bounds the worlds of resumption (`ExtP` at a floor versus `ExtR`) | **differs**: orthogonal to `Y`. A `ub` operation on a lend's row is never `unr` (`Row.Suspend`), so in [SHL] terms `ub` refines `◦` |

**Why not a fourth value of `Qual`.** `Qual` (`lin`/`cancel`/`unr`) is [SHL]'s `Y` plus our third
point (`../archive/new-core/scope-835-handlers.md` §2.1). `ub` is independent of it: a suspending wait may be `lin` or
`cancel`. Folding it into `Qual` would double `kTy`, `capTag`, `capB` and every match on `Qual`,
and mix two questions.

### 1.4 Relation to `lin`/`unr`, `Row.Suspend`, `Row.ResumeO`, `Row.Unwind`

- **`lin`, `cancel`, `unr`.** Unchanged. `ub` is read by the relation only through an entry's
  order, and by typing only through the conditions below.
  - `ub` on an `unr` operation is inert. No lend row holds `unr` (`Row.Suspend`), so it is never
    performed under a borrow; it only narrows which handlers may catch it. A kinding check
    refusing it is optional.
- **`Row.Suspend`** (`Core/TreeGoal791.lean`). Unchanged. It still asks `q ≠ unr`, the data
  clauses and `CTy.SuspendC`. `Row.UBOnly` sits beside it as `Const791.UBOK`, as
  `Const791.SchedOK` does today, so `Const791.OK` and `constN_*`'s statements do not change.
  Folding it into `Row.Suspend` is possible later.
  - `Div` stays unmarked, so a callback row holding `tick` fails `Row.UBOnly`. That matches
    `Row.Unwind.divB` and `Row.ResumeO.divB` on `main`: `tick` does not cross a borrow.
- **`Row.ResumeO` / `Row.ResumeOC`** (`Core/PinDerives.lean`, `main`'s R1 under `PinLaw`).
  Untouched. R1's rows are what `PinLaw` *asserts* sound under any handler, `effHandleV` and
  `effHandleVB` included. `ub` is the class the stretch *proves* sound under the handlers of §2.
  R1 programs keep `ub = false` and stay under `PinLaw`.
- **`Row.Unwind`** (`Core/EffBorrow.lean`). Every operation is abortive, so `Row.UBOnly` holds
  vacuously (`Row.schedOnly_of_unwind` with marks for names).

## 2. The handler contract

### 2.1 Statement

`SchedOKNLeK` (`TabK835N.lean`) has three parts:
- one name `n₀`;
- an empty outer table (`names : m ≠ n₀ → T m i = none`, every clause at
  `opTableK … OpTabK.empty`);
- cancel tables inside its own (`.Sub T`).

`HandlerOKK` removes all three. Its fields are the premises of `erwpK_handleLe_le`
(`HandleK835N.lean`), which already holds at any outer table:

```lean
structure HandlerOKK (V : ι → ι → Prop) (Φ : ι → LocFam) (fl : ι → Life) (N : Nat)
    (Tin Tout : ι → OpTabK ι) (Tc : UInt32 → Option (ι → OpTabK ι))
    (n₀ : UInt32) (qs hr hs : Val) (Qin Qout : ι → PostN) : Prop where
  down    : ∀ x, (Tin x).Down
  outDown : ∀ x, (Tout x).Down
  agree   : ∀ x m i, m ≠ n₀ → Tin x m i = Tout x m i          -- `names` is the case Tout = ∅
  tags    : ∀ x i en, Tin x n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag
  wcl     : …                                                   -- as `SchedOKNLeK.wcl`
  fin     : ∀ x i en, Tin x n₀ i = some en → en.abort = false → en.q ≠ .lin → ∀ Tk,
              Tc i = some Tk → ∃ T₁, en.fin = some (cancel run at T₁) ∧
                (∀ z, (T₁ z).Le (Tk z)) ∧ ∀ z, (Tk z).Down     -- `.Sub T` is the case Tk = T
  qdown   : ∀ x, (Qout x).Down
  ret     : ∀ x k, k ≤ N → ∀ ls v ρ, Qin x k ls v ρ →
              erwpK V Φ (opTableK ∘ Tout) Qout x k ls (hr v) ρ
  op      : ∀ x i en, Tin x n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
              (en.abort = false → ∀ k ≤ N, ∀ ls v κ ρ,
                (en.PA k ls v ⋆ KapRelK V Φ fl (opTableK ∘ Tout) Qout en (fl x) (Tc i) k ls κ) ρ →
                erwpK V Φ (opTableK ∘ Tout) Qout x k ls (c (v, κ)) ρ) ∧
              (en.abort = true → …)
```

`HandlerOKKW` is the instance at `KW`: `V = KW.PostK`, `Φ = (·.Θ.view ·.c)`, `fl = (·.lo)`.

- **`erwpK_handle_ok`.** A frame of `hndVal n₀ qs hr hs` meeting `HandlerOKKW` maps `erwpK` at
  `Tin` to `erwpK` at `Tout`. This is `erwpK_handleLe_le`; the world premises (`hwk`, `hInvW`)
  are table facts, discharged at `tabNK` by `tabNK_wkLeft` and `tabNK_wkOK`.
- **`SchedOKNLeK.toHandlerOKK`.** This is the instance at `Tout = ∅`, `Tc = fun _ => some T`:
  `names` gives `agree`, `.Sub` gives `.Le`, and the other fields carry over field for field. It
  is `erwpK_handle_sched`'s present proof. `SchedOKNLe.wc` (the pool's permutation order) is not a
  contract field: the pool's proofs read it, so it stays on the scheduler's instance.
- **One frame, one name.** A kernel handler frame has one name. "Any number of names" is a
  stack of frames, or nested handlers in the program.

### 2.2 How a clause reads `κ`

At `KW` the handled table is `tabNK`, so `KapRelK`'s `en.wk f y` is the entry's order (§1.2).
- **At an unmarked entry** it is `KW.OwedR`. `contShareK_owedR_lo` says the stop's floor is
  irrelevant. `contShareK_owedR_U` says the obligation is `KapRelR`, which is `vN` at `U`
  (`vN_thunk_iff_kapRelR`). So `op` holds of any clause in `𝒱⟦clausesTy⟧`. That is E10 (§4).
- **At a `ub` entry** it is `KW.Owed x f y` at a floor `f ≤ x.lo` the clause does not know. A
  clause may resume `κ` only at worlds owed at every such floor:
  - its own world (`KW.owed_self`, every `f`);
  - a world reached by a post (`KW.owed_of_post`; posts keep the floor, `KW.PostK`);
  - or a world it can show owed by keeping `κ` only across stops that are themselves `KW.Owed`.

  That is "resume only at worlds the lender permits".

### 2.3 Three ways to meet it

1. **Unmarked operations, any handler the program types.** E10 discharges `op` (§2.2, §4). This
   covers `effHandleV`, `effHandleVB`, `effHandleT`, `effHandleL` and `reify` at unmarked
   operations.
2. **Marked operations, a clause that resumes in place: a syntactic check** (§2.4). This is any
   depth in the program, by typing.
3. **Marked operations, a handler that parks `κ`: a semantic proof** of `HandlerOKKW`. Such a
   handler sits in the top-level stack (§3), outside the program, as the scheduler does today.
   Its proof is Lean, as `hs_schedOKN` is for `HS`.

Anything else is refused: no typing rule types a handler of a `ub` operation whose clause keeps
`κ` as a value.

### 2.4 What the syntactic check accepts

The check is the handler term's shape, which the existing rules already fix, plus the marks:

- **`effHandleT`** (`hndExpr n … (.pair Hr (tailTuple E 0 Hc))`, `Core/DivHandle.lean`). Each
  clause is `tailClause`, `λp. let (x, κ) = p in resumeB (ans_j x) κ`: the answer is computed,
  then `κ` is resumed in tail position.
  - The rule gains the markers `us`.
  - When a handled operation is marked, the answering functions' row `SN` is `Row.UBOnly`:

    ```lean
    (hUB : (∃ j < E.length, us j) → SN.UBOnly)
    ```

  - The reason is `T-ShallowHandler`'s ([SHL] §6). While `ans_j x` runs, `κ` sits in the
    clause's frame, and a stop of `ans_j` captures it. An unmarked stop owes along `ExtR`, and a
    `ub` `κ` inside it is owed only along `ExtP f`. That is `not_extRFoldTransfer`'s shape with
    the clause in place of the lend frame.
- **`effHandleL`** (`lastTuple`, `Core/DivHandleLast.lean`). The work runs with `κ` held; then
  `κ` is resumed in tail position (`inl`), or cancelled and the exit runs (`inr`).
  - The rule gains the markers `us`.
  - When a handled operation is marked:
    - the work row `SW` is `Row.UBOnly`, for the same reason;
    - each marked operation's cancel row `fs j` is `Row.UBOnly` at every depth (`CTy.UBOnlyD`,
      with `CTy.SuspendC`'s recursion).
  - The second premise is there because an in-program cancel of a `ub` `κ` runs its frames
    inside the program, under the lends live there. Their stops owe along `KW.Owed` (mode
    `true`, §1.2). They reach the handlers around the last handler through the cancel tables, and
    `HandlerOKK.fin`'s `T₁.Le Tk` needs those handlers' entries to owe no more worlds. A stack
    layer's cancel runs never meet this: the scheduler cancels through `K†`, which removes the
    handler frames (tables §1).
- **`effHandleV`, `effHandleVB`.** No markers. The handled operations are unmarked by
  construction (`Row.ofEff`'s default), and `OpSig.Sig` keeps the mark, so `[sub]` cannot unmark
  a `ub` operation to reach them.
  - No new premise. These are the handlers whose clause keeps `κ` as a value.
- **`resumeH`** (`handle_resume_inst`, `Core/Chain/HandlerLaw.lean` on `rule-791`). Its clause
  `resumeCT` is `tailClause` at the answer `return x`. It is the non-vacuity witness of §3.3.

Each premise is decidable and local. Each is vacuous when no handled operation is marked, so no
derivation `main` builds changes (§6).

**These are new side conditions on two typing rules.** Under the stop rule of 2026-11-06 a new
side condition on a typing rule is a stop, so they need the user's sign-off (§8, R1). The
alternative for `effHandleL` is no markers at all. Then a `ub` operation is caught in the program
only by `effHandleT`, and a `for … break` over a borrowing generator is refused (§7.3).

## 3. The top-level theorem

### 3.1 Statement

A layer of the stack is a handler frame, optionally applied to a state:

```lean
structure Layer where
  n : UInt32; qs hr hs : Val; arg : Option Val

def Layer.plug (L : Layer) (e : Expr) : Expr :=
  match L.arg with
  | none   => hndE (hndVal L.n L.qs L.hr L.hs) e
  | some s => .app (hndE (hndVal L.n L.qs L.hr L.hs) e) s.1
```

**`StackOKKW T Q Ls`.** Each layer meets `HandlerOKKW` from the table and post it receives to the
next. The last layer posts a leak-free `Q` at the empty table. A layer with a state also needs its
run applied to the state:

```lean
∀ x k ls v ρ, Qmid x k ls v ρ → erwpK … Tout Qout x k ls (.app v s) ρ
```

At the outermost layer `Tout = ∅`. A run at the empty table reads no world
(`erwpK_empty_move`), so this premise is a one-world `erwp` statement there.

The theorem:

```lean
def Goal835 : Prop :=
  ∀ (cs : List Const791), (∀ c ∈ cs, c.OK) → (∀ c ∈ cs, c.InFrag) → (∀ c ∈ cs, c.UBOK) →
  ∀ (S : Row) (e₀ : Expr), (CTy.effOf S .unit).inFrag = true →
    CDerives LifeCtx.empty (ctx791 cs) e₀ (.comp (CTy.effOf S .unit)) →
  ∀ (Θ : LocTy) (c : Loc → Option Life) (Ls : List Layer) (Q : PostN), Θ.OK → Θ.imm = [] →
    (∀ k ls v ρ, Q k ls v ρ → ρ = PMap.empty) →
    StackOKKW (fun z => tabNK false id (CTy.effOf S .unit) LSub.empty z) Q Ls →
    OrDiverges (Ls.foldr Layer.plug (substAll (vals791 cs) e₀))
```

- **No qualified operations, no handler.** With `Ls = []`, `StackOKKW` asks for the empty table,
  so `S = []`: a closed program at `F 1`. The program handles every unmarked operation itself,
  with any rule of `CDerives`. Then `Goal835` is `BridgeN` after `FundamentalN`.
- **Marked operations** that reach the top need a layer. So do unmarked ones the program leaves
  unhandled; for those, `op` is E10's.
- **What is not quantified any more:** a scheduler name, a set of names, and a program-side
  restriction (`Expr.HndAvoids`).
- **`∀ n₀` stays.** The layers' names are arbitrary. Review F1's option (B), a fixed name set,
  would have lost it.

The proof (by reading; not built):
1. `fundamentalN_all` at the reworked `cN` gives `cN (F_S 1)` at every world, that is, `erwpK` at
   `tabNK false id (F_S 1)` (`cN_effOf` at `KW`).
2. Induction on `Ls` applies `erwpK_handle_ok` per layer, and the state premise where there is
   one.
3. The outermost table is empty, so `erwpK_empty_move` brings the run to `erwp` at the empty
   table, and `erwp_adequacy` finishes.

### 3.2 `Goal791SchedN` as the instance with one layer

Take `Ls = [⟨n₀, qs, hr, hs, some (stateValN H [])⟩]` with `Q` as in `Goal791SchedN`.

- **The contract.** `SchedOKNLeK.toHandlerOKK` at `T = rowTabK S` gives the layer's
  `HandlerOKKW`.
- **The state.** `poolAnsN_run_le` (`PoolN.lean`, one world, empty table) gives the state step:
  it runs at `Tout = ∅`, which reads no world.
- **The row.** All of `S` is at `n₀` (`SchedOKNLe.names`). (S1) becomes `Const791.UBOK`, which the
  constants' rows carry. (S2) is gone: no `handle` in `e₀` can catch a `ub` operation except
  under §2.4's check, which `[handle]` at `n₀` with tail or last clauses meets. So the restated
  `Goal791SchedN` (at `KW`, with `SchedOKNKW` for `SchedOKN` and `Const791.UBOK` for
  `Restrict835`) is `Goal835` at one layer.
- **Still a premise.** `SchedOKNKW` of the scheduler stays a premise, as `SchedOKN` is today.
  `hs_schedOKN` at `KW` is the deferred scheduler unit.
- **The one-world statement.** Today's `Goal791SchedN` (at `rowTabN` and `SchedOKN` at one world)
  is a statement over the old block. Under the in-place rework (§5) it is deleted with that
  block, as review F2 recommends; it does not follow from the new one, because `⊸` is
  contravariant.

### 3.3 Non-vacuity

- **Now.** `handlerOKKW_resume`: the layer `resumeL` (`h_ret = λx. x`, one `tailClause` at the
  answer `return x`, `resumeH`'s shape) meets `HandlerOKKW` at a marked `lin` operation, over
  every handled table whose entries owe their own world. Its clause resumes `κ` at the clause's
  world, which `KW.owedS_self` gives at every floor. The view premise is `erwpK_consistentPA`'s.
  It needs only `erwpK`, `KapRelK` and `KW`, not the reworked `cN`, so it can be built first.
  `handle_resume_inst` is its one-world template.
- **Later.** `goal835_premises_inst`: every premise of `Goal835` holds at `Ls = [resumeL]` and
  `e₀ = perform` of the marked operation. It needs `perform_compatN` at the reworked block.
  Proving the built-in scheduler `HS` meets `HandlerOKKW` is deferred.

## 4. E10 and `HandlerLawN`

**Unmarked operations fall into the case where no lend is live. Checked by reading, against the
Lean facts below.**

An unmarked resuming stop's continuation holds neither a live lend nor a `ub` continuation:
- **Lend frames.** They forward only their callbacks' stops (`FoldTwin.schedPart`,
  `IFoldTwin.schedPart`, `RebTwin.schedPart`: a frame's lender table restricted to the callback's
  resuming names). Under `Row.UBOnly` those stops are marked. The restriction becomes a filter on
  marks (`OpTabK.schedPart` keyed by `(m, i)`).
- **Tail and last clauses.** One that holds a `ub` `κ` performs only marked resuming operations
  (§2.4).
- **Stack layers.** They are outside the program.

So every unmarked entry owes along `KW.OwedR` (`tabNK_wk_owedR`), and:
- `contShareK_owedR_lo`, `contShareK_owedR_U` and `vN_thunk_iff_kapRelR` give the clause `κ` at
  `vN`'s `U`. That is E10's world step.
- `not_kapRelR_world` excludes the stuck `κ = ()` of the `not_kapRelKTyN` configurations at every
  floor. Those configurations were what blocked E10 at the one-world stop
  (`scope-835-public.md` §8).
- `owedR_not_owed` shows a `ub` stop is still not readable at `U`, which is why `effHandleV` and
  `effHandleVB` get no markers.

What follows for the three rules `MissingN` names (`Fundamental831N.lean`):

| Rule | Handled operations | `κ` at the clause | Status |
|---|---|---|---|
| `effHandleV` (`HandleVN`) | unmarked by construction | `KapRelR` = `vN` at `U` | Core's `handleV_compatC` step by step at `erwpK`; not built |
| `effHandleVB` (`HandleVBN`) | unmarked | boxed; `stop_semN` and `erwp_handleS` exist, at `erwpK` as `erwpK_handleS` | the same; not built |
| `reify` (`ReifyN`) | `Div`, unmarked (§1.4) | the loop read through `U` | the same case; not built |

**`HandlerLawN` can go.** It lives on `rule-791`, `Core/Chain/HandlerLaw.lean`; `handlerLawN_iff`
shows it is `MissingN`. Once the three rows above are chain lemmas at the reworked block, `MissingN`
is a theorem, `fundamentalN_all` needs no hypothesis, and `HandlerLawN` has nothing left to name.

`handle_resume_inst`, `semJN_resumeCT` and the `kappa_*` lemmas carry over as the template for
§3.3. `goal791SchedN_premises_inst` is restated at `Goal835`.

Not verified:
- E10 at the reworked `cN`;
- the rest of `handleV_compatC` at `erwpK` (the return clause at the outer table, the tags);
- `reify` at `KW`.

None of these has a configuration against it.

## 5. `Sch` goes away; the rework is in place

**Confirmed: `Sch` goes away.**
- Review F1's probe shows by `rfl` that `Sch` is read only through `KW.OwedS` and `finSched`
  (`tabNW`'s `.eff` clause).
- Both now read the layer's mark:
  - `KW.OwedS S m` becomes `KW.OwedB (μ || ub)`, where `KW.OwedB b := (b → Owed) ∧ (¬b → OwedR)`;
  - `finSched` becomes `μ || ub`.
- `RowRd`'s mode type `M` becomes `Bool`, with `le := (· ≤ ·)` and `sub μ b := μ || b`.
- `wk` and `sub` take the layer's mark in place of its name.
- The top mode is the constant `false`, so `vN`, `cN`, `gN`, `SemJN`, `FundamentalN` and
  `ConstN` keep their argument lists. That is review F1(B)'s benefit without its fixed name set.
- The cost moves to `CTy.eff`'s arity (§6, §8 R2).

**Confirmed: the rework is in place** (review F2). There is no parallel block. The order is the
review's:
1. The `KW` block takes the canonical names in `Goal791N.lean`.
2. Today's block moves to `Goal791N0.lean` with `₀` names, and its dependents are repointed
   mechanically.
3. Files migrate in tables §10.4's order.
4. Done-when: `Goal791N0.lean` and `CNW835N.lean` are deleted, and no `₀` name remains.

The work is the 78 proof sites in 20 files that open `cN`'s `F`/`F_Σ`, under either choice.

## 6. Carry-over table

Classes:
- **U** (unchanged): the text stands. The row names what the file depends on, none of which
  changes.
- **M** (mechanical): `Sched`/`S`/`Sch` read as marks, `.eff` patterns gain a field, renames.
- **R** (reworked): definitions or proofs change in substance.
- **D** (deleted).

### 6.1 The #835 Kripke-stop files (`35bf57a9..5e6c926d`)

| File | Class | Why |
|---|---|---|
| `SI/ErwpK.lean` | U | `erwpK`, `contShareK`, `OpEntK`/`OpTabK`, `KW`, `KW.Post`, `KW.Owed`, `kw_owed_fold`, `extP_foldFrame`, `LocTy.ExtP`; none reads a name |
| `SI/MFrameK.lean` | M | `OpTabK.schedPart` and `FoldTwin.schedPart` filter by a name predicate; keyed by `(m, i)` they filter by mark. The frames (`erwpK_M_frameGen`, `kw_owed_fold`) are unchanged |
| `SI/IFrameK.lean` | M | `IFoldTwin.schedPart` as above; `LocTy.ExtP.immFoldAt`, `ifoldTwin_owed` unchanged |
| `SI/RFrameK.lean` | M | `RebTwin.schedPart` as above; `rebTwin_owed` unchanged |
| `SI/AFrameK.lean` | U | `erwpK`, `KW.Owed`, `SealTwin`, `rwpG_M_antiFrameGV` |
| `SI/AntiStopN.lean` | U | `rwpG` only (`AFPostGV`, the validity-carrying frame) |
| `SI/IStopN.lean` | U | `rwpG_I_frameGV`; `rwpG` only |
| `SI/RebStopC.lean` | U | `rwpG_rebGV`; `rwpG` only |
| `SI/RebStopD.lean` | U | `rwpG_rebDeepGV`; `rwpG` only |
| `SI/StopFrameN.lean` | U | `rwpG_M_frameGV`; `rwpG` only |
| `KStopSpike835N.lean` | U | local copies (`KStopSpike835N.erwpK`, …); holds `extP_not_foldInv`, cited by `scope-835-kripke-stop.md` §1 |
| `Public835N.lean` | U | `LocTy.ExtP` and its laws; `KapRelP` over `cN` keeps its text (`cN`'s arguments are unchanged) |
| `LendExit835N.lean` | U | `KW.OwedR`, `KW.Owed`, `contShareK_owedR_*`; `KapRelR` over `cN` keeps its text and `vN_thunk_iff_kapRelR` stays `Iff.rfl`. Docstring says `Sched` |
| `MFrameK835N.lean` | U | `erwpK_M_frameGen`, `FoldTwin`, `KW.Owed`, `cancelTabK` |
| `IFrameK835N.lean` | U | `erwpK_I_frameGen`, `IFoldTwin`, `KW.Owed` |
| `RFrameK835N.lean` | U | `erwpK_rebGenK`, `RebTwin`, `KW.Owed` |
| `AFrameK835N.lean` | U | `erwpK_M_antiFrameGen`, `SealTwin`, `KW.Owed` |
| `MechK835N.lean` | U | `erwpK`, `rwpG`, `cancelTabK`; generic over `ι` |
| `MechK835N2.lean` | U | the same |
| `MechK835N3.lean` | U | the same |
| `MechK835N4.lean` | U | the same |
| `MechK835N5.lean` | U | the same, plus `OpTabK.DownI`/`CtxClosedI` |
| `HandleSK835N.lean` | U | `erwpK_handleS(_le)`, `opTableKS`, `KapRelK` |
| `HandleTK835N.lean` | U | `erwpK_frame_plain_or`, `erwpK_consistentPA`, `KapRelK.extF` |
| `FrameListK835N.lean` | U | `erwpK_M_frameList` over any `ι`; its `vN` reads go through `vN_local` and `vN_add_eq_bnd`, which the reworked block proves with the same statements (tables §10.2) |
| `HandleK835N.lean` | M | `erwpK_handleLe_le` unchanged; `erwpK_handle_sched(KW)` restated from `HandlerOKK` (§2.1), its proof the same application |
| `TabK835N.lean` | M | `KW.OwedS` becomes `KW.OwedB`; `finSched` becomes `||`; `CTy.SchedOnly` becomes `CTy.UBOnly`; `tabNK`/`tabRK` take `μ : Bool`; `SchedOKNLeK` stays and gains `toHandlerOKK`; the `.eff` patterns gain a field |
| `TabKW835N.lean` | M | the twins, cancel transfers and frames at the typed tables; every `CTy.SchedOnly S` becomes `CTy.UBOnly` |
| `TabKW835N2.lean` | M | `KW.OwedS.left`/`.extR` become `KW.OwedB.*`; `tabNK_wkLeft`, `tabNK_wkOK`, `erwpK_handle_schedKW_tab` |
| `FrameListKW835N.lean` | M | `tabListK` under the mode |
| `RowFamK835N.lean` | M | `RowRd.M := Bool`; `wk`/`sub` take the mark; `rdKWv`; `tabF`'s `.eff` clause reads the field. The lemmas of §9.1 keep their proofs |
| `ThenK835N.lean` | M | `gNFrame_carryKW` reads `KW.OwedB.extR`; `[then]`'s producers are over the family |
| `IterKW835N.lean` | M | `KW.OwedS.extR`/`.consistent` become `KW.OwedB.*` |
| `ReindexK835N.lean` | M | `vNW_add_eq`'s `vNW Sch` becomes the canonical `vN`; `erwpK_comap`, `LocTy.extR_add` unchanged |
| `CNW835N.lean` | R | the block becomes the canonical one in `Goal791N.lean`, `Sch` removed and the mode `false` at the top; the file is then deleted (§5) |
| `Restrict835N.lean` | R | `Row.SchedOnly` becomes `Row.UBOnly` and `Const791.SchedOK` becomes `Const791.UBOK`; `Expr.HndAvoids`, `hin_hndExpr`, `hin_qualsVal`, `hndAvoids_hndExpr`, `not_hndAvoids_hndExpr` and `Restrict835` are deleted (typing replaces (S2)); `hardestRow_schedOnly` becomes a mark check |
| `Core/Chain.lean` | M | imports |
| `scripts/AxiomCheck.lean` | M | registrations renamed or removed |

**Counts (36 Lean files under `Core/Chain`):** U 22, M 12, R 2, D 0. The deletions are inside
files: `Expr.HndAvoids` and its four lemmas, then `CNW835N.lean` once the rework moves its block.
`Core/Chain.lean` and `scripts/AxiomCheck.lean` are M.

### 6.2 Files on the branch before #835 that this touches

| Files | Class | Why |
|---|---|---|
| `Goal791N.lean` | R | the block is redefined in place at `KW` (§5); `Goal791SchedN` is restated (§3.2); `Goal835` is added |
| 20 files that open `cN`'s `F`/`F_Σ`: `Cancel791N`, `Depart831N`, `Eff835N`, `FamCancel836N`, `FamImm836N`, `Field791N`, `Fuel835N`, `HandleL835N`, `HandleT835N`, `ImmLend833N`, `ImmTie791N`, `Inst791N`, `Iter835N`, `Let835N`, `Reborrow791N`, `Stop835N`, `Then835N`, `TyEq834N`, `Unwind833N`, `Withload791N` | R | 78 proof sites re-proved at the reworked `cN` (tables §10.3), with or without the qualifier. `HandleT835N` and `HandleL835N` also read `us` and the premises of §2.4 |
| `Fundamental831N.lean` | R | `MissingN` becomes a theorem (§4); `fundamentalN_all` needs no hypothesis |
| `Kappa835N.lean` | R | `not_kapRelKTyN`, `not_kTy_world`, `not_kTy_view` and `kapRelN_not_kapRelP` are about the one-world `KapRelN` and the old `vN`. They move to `Goal791N0.lean`'s world and are restated at one world or deleted with it; not checked which |
| the other 37 files that mention the relation in statements | U | statements over `cN`/`vN`/`gN`/`SemJN`/`tabN` with unchanged arguments, proofs that never open `F`/`F_Σ`; they depend on the block only through laws whose statements stay (tables §10.2) |
| `PoolN.lean`, `PoolSpawnN.lean` | U | `SchedOKNLe`, `poolAnsN_run_le` and `hs_schedOKN` stay at one world; §3.2 reads `poolAnsN_run_le` at the empty table. `hs_schedOKN` at `KW` is the deferred unit |
| `Core/Types.lean`, `Core/EffRules.lean`, `Core/EffFin.lean`, `Core/Fundamental.lean` | M | `OpSig.ub`, `CTy.eff`'s field, `Row.ofEff`'s `us`, `OpSig.Sig`; `effHandleT`/`effHandleL` gain `us` and §2.4's premises |
| `Core/Tree*.lean`, `Frontend/**`, other `Core/*.lean` | M | `.eff` patterns and `OpSig` constructors gain the field. On the branch, `.eff` patterns with three or more fields written out: 309 in 49 files, 126 of them in `Core/Chain`; about 61 anonymous `OpSig` constructors |
| `rule-791`'s `HandlerLaw.lean` (not on this branch) | D | `HandlerLawN` goes (§4); `handle_resume_inst` and its helpers carry over to §3.3 |

## 7. What `main`'s programs see

**Nothing.** Checked against `origin/main`:`Core/Fundamental.lean`, `Core/Types.lean` and
`Core/EffFin.lean`.

- **No field exists.** `main`'s `OpSig` has `n i q A B fin rc` and `CTy.eff` has the same, so no
  `main` program is marked. After the change the field defaults to `false`. Nothing in the
  elaborator sets it (it has no surface syntax), so every derivation the checker builds has
  `ub = false` everywhere.
- **The handler rules.**
  - `effHandleV` and `effHandleVB` take `Row.ofEff n E 0 fs cs` and get no `us`, so their meaning
    is unchanged.
  - `effHandleT` and `effHandleL` take `Row.ofEff n E 0 fs` today. With `us` at its default, their
    new premises have a false antecedent, so every `main` derivation is a derivation of the new
    rule.
- **The lend rules.** `withbor1U`/`2U`/`3U`, `withloadU`, `sliceBorrowMU`/`IU` take `Row.Unwind`,
  which is abortive-only, so `Row.UBOnly` holds vacuously. The plain lends run at pure rows.
- **R1.** `CDerivesP.lendR` takes `Row.ResumeOC` (`Core/PinDerives.lean`). Neither it nor
  `PinLaw` reads the field. The eleven R1 corpus programs (`scope-835-restriction.md` §4) keep
  `PinLaw`.
- **Core's relation.** `vC`/`cC` and `fundamentalC` do not read `ub`, as they do not read `rc`
  ("read by typing only", `Core/Types.lean`). Their proofs change only where a `.eff` pattern or
  an `OpSig` constructor gains the field.
- **Corpus and golden.** Unchanged in content. This is by reading, not built.

What `main` does see is source: the kernel's types gain a field, so 185 `.eff` patterns in 38
files on `main` gain one argument (§8, R2).

## 8. Grounding against real programs

Each row says which operations are marked, which handler catches each, and how it meets §2.
Spellings follow `docs/effects-scoping.md` §6.4–§6.5 and SPEC §15.

### 8.1 The operator's watch loop

`for ev in watch[Foo]() |> merge(timers.due()) { match reconcile(&ev.obj) {…} }`. The source reads
into a borrowed buffer across `await`; `&ev.obj` is a reborrow (`w3`/`wF`); a timeout cancels the
task, and the cleanup closes the watch with IO.

| Operation | Marked | Caught by | Meets the contract by |
|---|---|---|---|
| `await` (cancellable wait) | yes: performed inside the buffer's lend callback | the scheduler, a stack layer | its proof of `HandlerOKKW` (`SchedOKNLeK.toHandlerOKK`, `hs_schedOKN` at `KW`, deferred) |
| `yield` of `watch` | yes, if the source holds the buffer across its `yield` | the `for` site: `effHandleT` (no early exit) or `effHandleL` (`break`, SPEC §15: `(force k).2`) | syntax (§2.4). The body is the answering function or work, and `reconcile`'s resuming operations (`await`, `Kube`, `Log`) are marked |
| `read`, `close`, `log` (IO) | yes | the platform, the outermost stack layer, resuming in place at host externs | `KW.owed_self` at every floor, as `resumeL` (§3.3) |
| cleanup on cancel | the cancel row of `await` and `yield` | under mode `true` (§1.2) every cleanup stop owes along `KW.Owed`; the scheduler's cancel runs reach only the stack (`K†`) | no cancel-row restriction for the scheduler. For `for … break`, `yield`'s cancel row must be `UBOnly` at every depth (§2.4), so the cleanup's resuming IO operations are marked; abortive ones are free |

**A timeout written as an in-program handler that holds `κ` does not pass.** It is a parking
handler. It goes in the stack, or asks the scheduler to cancel (§9, R4).

### 8.2 Async reconcile

`reconcile(&foo) with Kube[ConfigMap], Log, Requeue`, run as
`controller(Foo, reconcile) |> timeout(30.s) |> retry(backoff) |> log(json(&mut stderr)) |> kube(&mut client)`.

| Operation | Marked | Caught by | How |
|---|---|---|---|
| `Kube` operations (`get`/`put`) | yes: performed under the `imm` lend of `foo` | `kube(&mut client)`: an answering handler (`effHandleT`) whose answering function performs IO and `await` | syntax; its row `SN` is `UBOnly` because `await` and IO are marked |
| `Log` | yes | `log(…)`, `effHandleT` | syntax |
| `Requeue`, `Fail[KubeError]` | abortive | `retry`, the controller | no `κ`; the mark is not read |
| `await` | yes | the scheduler | contract |

### 8.3 A generator `for` loop that yields borrowed data

A generator `g` lends from data it is given and holds the lend across `yield`.

- **`yield` is marked.** `for x in g(&mut v) { M }` is `effHandleT`, or `effHandleL` with `break`.
  It passes the syntactic check; `M`'s resuming operations are marked, and with `break` so are
  those of `yield`'s cancel row.
- **What may be yielded.** A payload borrowed from data outliving the lend's bound may be yielded.
  A payload into the generator's own lent cell is excluded by `Row.Suspend`'s payload clause
  (free of `'x`, outliving `@bnd`). The qualifier does not change this.
- **A stored generator** (`U(pull …)`, `effHandleV` keeping `κ`) cannot catch a marked `yield`.
  That is the shape of `main`'s `async-r1-generator` family, which stays under R1.

### 8.4 Blocking or async IO, chosen per call

`read(&mut buf)` is one marked operation, with two handlers ([E14] in `docs/effects-scoping.md`:
"the answering level (`block_on`) vs the scheduler (#52) as two handlers of the same
operations"):

- **Blocking.** An answering handler (`effHandleT`) whose answering function calls the blocking
  host extern and returns. It resumes in place and passes the syntactic check. Its answering row
  (the host operation) is marked.
- **Async.** The scheduler parks `κ` until the read completes and meets the contract by its proof.

The choice is which handler encloses the call. The operation's type, and so the caller's type,
is the same under both, so the choice adds no colouring. A call site may switch handlers without
retyping.

## 9. Risks and open questions

- **R1. New side conditions on `effHandleT` and `effHandleL`** (§2.4): marked answering and work
  rows, and marked cancel rows for `effHandleL`.
  - They are vacuous at every derivation `main` builds.
  - Under the stop rule of 2026-11-06 they need the user's sign-off.
  - Not verified that they are needed: the argument is by reading, `not_extRFoldTransfer`'s shape
    with a clause for the lend frame, and no configuration is built.
  - Not verified that they suffice.
- **R2. The kernel types change.** `CTy.eff` and `OpSig` gain a field: 309 `.eff` patterns in 49
  files on the branch, 185 in 38 on `main`, about 61 `OpSig` constructors. Mechanical, but it is
  a change to `main`'s Core types when the stretch merges. The alternative is to widen `rc`'s slot
  to a record of marks: patterns that write `_` there survive, but two unrelated marks share a
  field. Not recommended.
- **R3. Mark propagation.** Every resuming operation performed inside a lend's callback, inside a
  tail or last clause around a marked operation, or in such an operation's cancel row (when
  last-handled) must be marked.
  - In practice library effects (IO, `Log`, `Kube`, `yield`, `await`) are declared marked.
  - Marked operations cannot be caught by κ-keeping value handlers: stored generators,
    `lib/async.bc`'s `spawn`/`spawn_logged`, `handle_with`.
  - Surface inference of the mark (as [SHL] §2.3–§2.4 and §5 infer `Y`) is not designed.
- **R4. Parking happens only at the stack.** An in-program parking handler (`spawn`, an
  in-program timeout) does not type at a marked operation.
  - Open: a parking handler as a proved constant, `U(F_{marked ++ Σ} A) ⊸ F_Σ R`, its `ConstN`
    being `HandlerOKKW`. That would give parking at any depth without a typing premise, as the
    lend constants do.
  - Not designed, not verified.
- **R5. `Goal791SchedN` as `Goal835`'s instance** (§3.2) is by reading. The state step through
  `erwpK_empty_move` and `poolAnsN_run_le` is not built.
- **R6. Tail and last handlers at marked entries at `KW`.** `scope-835-restriction.md` §2 argues
  them by reading. `handleT_compatN` and `handleL_compatN` at `KW` are not built. Not verified.
- **R7. E10 and the rest of `handleV_compatC`, `handleV_compatCB` and `reify_compatX` at the
  reworked `cN`.** Not built. Not verified (§4).
- **R8. Configurations about the old block** (`Kappa835N`'s four, `Public835N`'s `KapRelP`
  configurations). They are statements about one-world `KapRelN` or the old `vN`. Under the rework
  they move to `Goal791N0.lean`, and each is restated at one world or deleted. Not checked which.
- **R9. The Imm Frame's cancellable layers** (tables §7.2) stay open. Unchanged by this note.
- **R10. Subsumption.** A stop at an unmarked entry also meets a marked entry's obligation
  (`KW.Owed.owedR`: `KW.Owed` owes fewer worlds), so `[sub]` from unmarked to marked would be
  sound for the relation. `OpSig.Sig` keeps the mark equal, as [SHL] Fig. 5 keeps signatures
  equal. Relaxing it is an option, not needed.
- **R11. Effectful cleanup is kept.** No cancel row is restricted at the scheduler. At an
  in-program `effHandleL` of a marked operation, the cancel row's *resuming* operations are
  marked (R1); abortive operations and effects are free.

## 10. Unit plan

One agent run is about one unit. Units 2 and 3 can run in parallel; every other unit depends on
the one before.

| # | Unit | Done when | Units |
|---|---|---|---|
| 1 | **The field in the kernel.** `OpSig.ub`, `CTy.eff`'s field, `Row.ofEff`'s `us`, `OpSig.Sig`; `Row.UBOnly`, `CTy.UBOnly`, `CTy.UBOnlyD`; `effHandleT`/`effHandleL` with `us` and §2.4's premises; every pattern and constructor site | `lake build` clean, `main`'s golden and corpus unchanged, no proof changed beyond arity | 1–2 |
| 2 | **The rework in place, `Sch` out.** The `KW` block under the canonical names in `Goal791N.lean`, the old block in `Goal791N0.lean`; `KW.OwedB`, the mode `Bool`, `RowRd.M := Bool`; `schedPart` by mark; `Const791.UBOK`; `Expr.HndAvoids` and `Restrict835` deleted | build green; no `Sch`/`Sched` parameter left in `Core/Chain` | 1–2 |
| 3 | **The contract.** `HandlerOKK`, `HandlerOKKW`, `erwpK_handle_ok`, `SchedOKNLeK.toHandlerOKK`, `handlerOKKW_resume` (§3.3) | registered in `AxiomCheck`; `erwpK_handle_sched` is an instance | 1 |
| 4 | **Tables over `vr` and the callback's table step** (tables §10.7) | the frames apply to the canonical block's tables | 1–2 |
| 5 | **Re-pointing.** The 78 sites in 20 files, then the rest of tables §10.3; T and L at marked entries | `Goal791N0.lean` deleted, no `₀` name left | 2–3 |
| 6 | **E10.** `HandleVN`, `HandleVBN`, `ReifyN` at unmarked operations | `MissingN` a theorem; `fundamentalN_all` unconditional | 1 |
| 7 | **`Goal835`.** The stack theorem; `Goal791SchedN` at `KW` as its one-layer instance; `goal835_premises_inst` | both proved; `HandlerLawN` has no use | 1 |
| — | **Deferred:** `hs_schedOKN` at `KW` (`HS` meets `HandlerOKKW`) | — | 1–2 |
| | **Total (units 1–7)** | | **8–12** |

Order:
- Unit 1 comes first: the relation reads the field from the type.
- Unit 2 comes before re-pointing, because both the mark and the canonical names touch every
  re-pointed proof (review: "decide F1 first").
- Unit 3 needs only `erwpK` and `KW`.

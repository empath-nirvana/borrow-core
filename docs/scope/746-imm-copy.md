# #746: the checker inserts the derived copy at `imm`

Scope for the unit after #746 steps 1–5. Written before any code; reviewed (section 7) before the
build. Read at `origin/main` 32aae3e4. Facts marked *(run)* were checked with a prototype of section 1
built in this worktree before the review; the review may change it.

**Kernel target.** Every use of an `imm` borrow beyond its first elaborates to the kernel's copy at
`imm`: the node `CDerives.copy` (at `Imm @a A`, `axCopyTy`) or `CDerives.arrCopy` under `bangE`
(at `[Imm @a A]`), applied to the variable, its pair taken apart, in the shape of `copy_derives`
(`Core/Classes.lean`). Each inserted copy is therefore a rule node `CDerives` licenses, and the
checker only translates.

## 0. What exists

- `DerivedCopy` (`Core/Classes.lean`): `Imm @a A` and `[Imm @a A]` (`array_imm`), each linear
  (`DerivedCopy.linear`).
- `copyC`, `copyE A i e = bindE (copyC A · xᵢ) (letpair (var 0) (e.shift 1 2))`, `copyC_wf`, and
  `copy_derives`: from a split `Γ = Γ₁ ⊎ Γ₂` with `Γ₁` solo at `xᵢ : A` and `e` derived at
  `A, A, Γ₂`, `copyE A i e` is derived at `Γ`.
- The constants' typed nodes: `TExpr.copy` (`TDerivesP.copy`, from `CDerives.copy`) and
  `TExpr.arrCopy` (from `CDerives.arrCopy`), built in `Frontend/Check/Consts.lean` by `cDead`.
- The checker's split: `overlapOK T u₁ u₂` admits a slot both parts use only at a persistent type;
  otherwise `splitErr`: "`x` is used twice here, and its type `…` is linear". `Imm` is not
  persistent, so today `*r + *r` at `r : imm 'a i32` is refused there.
- Backend2 reads a `copy`/`array_copy` constant as `CopyRule.const`, and `Lint.copiesAt` admits it
  at `DerivedCopy` only (F4). The old backend compiles the erased constant, under its licence.
- No site inserts a derived copy today (SPEC §12, *Every insertion site cites its rule*).

## 1. The insertion rule

The rule is stated once, for every node at which the checker splits its context between two
**parts** that run in sequence, and applied at each such construct.

> **Copy at a split.** At a split node checked at slots `T` with environment `E`, for each
> variable `x` in scope (resolved to slot `i`, not shadowed) such that **both parts mention `x`
> free** and **`T[i]` is `DerivedCopy`** (decided by `derivedCopyB`, with `derivedCopyB_iff`), the
> node is checked as
>
>     p <- return (copyC T[i] xᵢ); let (x₁, x₂) = p; node
>
> with the first part checked where `x` names `x₁` and the second where `x` names `x₂`. The
> original slot is no longer owed (the copy consumes it); `x₁` and `x₂` are owed to the node as
> any binder of a type with a derived drop is (`Env.pushOwn`, SPEC §12). Several such variables
> nest, in slot order.

"Mention" is the checker's existing `mentionsV`/`mentionsC`, which respects binders. A variable
both parts mention is one the split would otherwise give to both, so the rule fires exactly where
`splitErr` would fire at a `DerivedCopy` slot, with two exceptions, both harmless:

- a part may mention `x` where the derivation absorbs it instead (under `<>`, `absurd`): that
  copy is then unused, owed, and dropped by its derived drop (`forget`, `HasDtor.imm`) at the end
  of its path, or, in a value, refused as unconsumed. No program the checker accepts today has
  such a split (a split at a non-persistent slot both parts use is refused today), so nothing
  accepted today changes;
- the rule is decided before the parts are checked (from the syntax and the slot's type), so each
  part is checked once. Inserting on failure would check a part again at each enclosing split,
  exponentially in the nesting.

A use that is not a split part (a merge: both `case` arms, both `<M, N>` components, `[then]`'s
continuation and finaliser) needs no copy: each side of a merge uses the variable once.

### 1.1 Per construct

| construct | parts, in order | where the copy goes | parts see |
|---|---|---|---|
| `(V, W)` | `V`, `W` | `run (copy; let (x₁, x₂); return (V, W))` | `V`: `x₁`, `W`: `x₂` |
| `V W` (value application) | `W`, `V` (`lolliE`'s order) | `run (…; return (V W))` | `W`: `x₁`, `V`: `x₂` |
| `x <- M; N` (pure head, `[let]`, `[then]` of `effBind`) | `M`, `N` | before the binding | `M`: `x₁`, `N`: `x₂` |
| `x <- M unwind (D); N` | `M`, then `N` and `D` (one merged part) | before the binding | `M`: `x₁`, `N` and `D`: `x₂` |
| `let () = V; M` | `V`, `M` | before it | `V`: `x₁`, `M`: `x₂` |
| `let (y, z) = V; M` | `V`, `M` | before it | `V`: `x₁`, `M`: `x₂` |
| `case V { … }` | `V`, the arms (one merged part) | before it | `V`: `x₁`, both arms: `x₂` |
| `M y` | `M`, the variable `y` | before it | `M`: `x₁`, `y`: `x₂` |

A value split cannot hold a binding, so its copy is under `run` (`[ret]`'s elimination `ofRet`), a
value. `run` is a value form everywhere a value is allowed except a handler's clauses
(`valFormB`), and those use only unrestricted slots, so no `imm` reaches them.

**Not split nodes**, so no rule: `<M, N>` (merge), `absurd V` and `<>` (absorb), a handler's
answer clause and clauses against its body (`[handle]`'s `Γ₁` is persistent only: an `imm` there
is refused with the existing message "a handler's clauses use only unrestricted variables"), the
relaxed lend (its body sees only the view), `!thunk` (every live slot must be `!`).

**Inside** a thunk, a clause body, a loop's or a fold's generated function, or a `def`, the rule
applies to the splits there, like everywhere: a closure capturing `r` and a later use of `r` is the
split between the thunk (a part that mentions `r`) and the later code; a handler clause whose
argument or state is `imm` and is used twice copies inside the clause's body; a loop body is a
function the elaboration generates (SPEC §14), and its splits are ordinary.

### 1.2 Where it cannot go

A program the rule does not reach is refused as today, by the kernel's split: "`x` is used twice
here, and its type `…` is linear". In particular every `mut` borrow (`Mut @a A`, `[Mut @a A]`), every
owned value (`Ref`, arrays, declared types, closures, thunks) and every capability: none is
`DerivedCopy`, and the copy constant is typed only at `Imm` (`axCopyTy`) and `[Imm]`.

## 2. The kernel rule each insertion produces

At each insertion the checker builds, with the existing builders and nothing else:

| typed node | kernel rule | builder |
|---|---|---|
| `copy` / `bangE (array_copy)` constant | `CDerives.copy` / `.bangE (.arrCopy)`, at every dead context | `cDead` (as `synConst`) |
| the variable `xᵢ` | `CDerives.var` | `rVar` |
| `copy xᵢ` | `CDerives.lolliE` | `rLolliE` |
| `return (copy xᵢ)` | `CDerives.ret` | `rRet` |
| `let (x₁, x₂) = p; node` | `CDerives.tensorE` | `rTensorE` |
| `p <- …; …` | `CDerives.bind` | `rBind` |
| (value sites) `run …` | `CDerives.ofRet` | `rOfRet` |

The erasure is `copyE A i e` for the node's erasure `e`, the copies' slots `0` and `1`
(`bindE` is `bind`'s erasure, `copyC` the constant's): a theorem `copyIt_erase` states it by
`rfl`, and the `Res`'s derivations are the checker's (`checkProgram_sound`, unchanged). So every
inserted copy is a `copy_derives` instance, a node of `CDerives`, and `TDerivesP.copy` types it
only at `axCopyTy a A`: an inserted copy is at `Imm`, whatever the checker does.

The copy constant's node carries `TInfo.name` = the variable and a flag `TInfo.inserted`, so the
typed term says which copies the checker inserted (written `copy[…]` constants have neither).
`bcc copies <file>` prints them, and `corpus/copies/<name>.txt` pins them for `corpus/<name>.bc`
(`scripts/check-corpus.sh`), as `corpus/reports/` pins the effects lines.

Nothing in `Core/`, `CDerives`, `TDerives`, the relation, the machine, Backend2 or the old backend
changes. Backend2 sees `copy` constants, `CopyRule.const`, which `Lint` checks at `DerivedCopy`.

## 3. Tests (done-when)

Accepted, each with its `corpus/copies/` pin showing the copy at `r`, and a golden output:

- `*r + *r` at `r : imm 'a i32`;
- an `imm` captured by a closure and used after it;
- an `imm` used twice inside a handler's clause (an argument or the state);
- an `imm` used twice in a loop body, and in a `fold_imm`/`for` body;
- `array_imm` used twice (`len(v)` twice).

Refused with the existing message (`corpus/reject/`): a second use of a `mut` borrow
(`two-mut.bc`, `async-r1-two-mut.bc`), of an owned value (`use-after-free.bc`, `double-free.bc`,
`array-use-after-free.bc`), of a closure (`clo-copy.bc`), of a capability
(`io-capability-twice.bc`), plus a new `reject/linear-mut-twice.bc` at `*r + *r` with `r : mut`.

`reject/double-use-in-callee.bc` uses an `array_imm` twice: it now checks. It tests that the
refusal is reported in the callee, so it moves to an `array_mut` view (still refused, same message
shape) and the `array_imm` program joins the corpus.

## 4. NOT doing

- No change to `VTy.persistent`, `overlapOK`, `Ctx.SplitP` or `splitErr`: `imm` stays linear, its
  derived copy is what allows a second use.
- No new concept: no "copyable" class, no multiplicity exemption in the checker, no new word.
- No new `CDerives`, `TExpr` or `TDerives` constructor; no new kernel lemma beyond the `rfl`
  erasure statement.
- No rewriting of the source term and no new surface or core syntax form (the rejected
  `class1-revive` added `Val.copyImm` and renamed variables in the syntax). Names are resolved to
  the copies through the checker's environment.
- No insertion in the sugar (`Frontend/Sugar.lean`, `Frontend/Elab/`): it does not know the
  kernel's slot types.
- No copy at `!A`: it is unrestricted, the split's `dup` already applies.
- No change to `*e`'s content rule (an unrestricted content only) or to `for` over owned arrays.
- `book/src/guide/linear.md` is on the unmerged `linear-book` branch: not touched; section 6 lists
  what it needs.

## 5. Tempting shortcuts — each a STOP

- **STOP:** marking `Imm` persistent, or letting `overlapOK` pass `Imm` slots. That makes `imm`
  unrestricted (decision 3 says linear with a derived copy), and no copy node would exist.
- **STOP:** a backend-side copy, or `CopyRule.derived` emitted for a split the typed term does not
  copy. The copy must be a node of the typed term.
- **STOP:** inserting in the sugar by its own type guess (`c.tyV`). The elaborator would decide.
- **STOP:** inserting the copy after a split fails and checking again: exponential, and it hides
  which rule fired.
- **STOP:** hoisting every copy to a function's entry, or copying every `imm` parameter up front
  (program-shaped, and copies nothing a nested split needs).
- **STOP:** dropping an unused copy by anything but its derived drop at a `dtor` node.
- **STOP:** any copy at a type that is not `DerivedCopy` (a `mut`, an owned value, a declared
  type, a capability). A second use of those staying refused is a linearity HARD STOP if it
  breaks.

## 6. Docs

- SPEC §12, *Every insertion site cites its rule*: the checker inserts a copy only as the `copy` /
  `array_copy` constant's node in `copy_derives`'s shape (section 2). §10: a second use of an `imm`
  borrow is its derived copy. A new entry (version bump, changelog).
- Book on main: `book/src/guide/ownership.md` and any `borrows` section that says a borrow cannot
  be used twice: an `imm` borrow can be, a `mut` borrow cannot.
- `linear.md` (branch `linear-book`), to be changed there: wherever it says the derived copy at
  `imm` exists in the kernel but is not inserted, or shows a refused second use of an `imm`, it
  becomes: the checker inserts it; and the §42 sentence (section 8).

## 7. Review

One fresh reviewer on this document, lens: shortcuts and ad hoc fixes against principled design.
One review, one targeted fix check; a Fatal finding gets one more full review.

## 8. The SPEC §42 handler-state mismatch

SPEC §42, *Declared types with no derived drop*: "The program is accepted when the value is
consumed before, lent into the computation, held as a handler's state, or under a `[then]` whose
written finaliser consumes it", and later "'commit in the body, roll back on an abort' lends the
value into `M` or holds it as a handler's state". The book's program holds a `Txn` as `in_txn`'s
state and lets a `Fail` raise pass the handler; the checker refuses it.

**Authority: the kernel rules.** A handler with a state answers `U(S ⊸ F_Σ (S' ⊗ R))` (§21): the
site handles the body, then applies the answer to the initial state. The state is a value of the
context of that binding while the handled body runs. When the handler's outer row has an operation
that may abort (the `Fail` the body raises and the handler does not handle), `[let]`'s `hW` asks
that context to be `VTy.OwnFree`, or `[then]`'s finaliser to consume it by derived drops; a type
holding `Tok` has neither (`decl_not_ownFree`, `decl_linear`). So the kernel refuses it, and the
checker agrees with the kernel. The SPEC sentence is wrong as stated.

*(run)* The refusal is at the clause's resume `k(())` of the state handler: the clause passes the
state on to the rest of the body, which may raise. The message is the existing one ("`t`, of type
`i32 * i32 * tok`, is live across a computation that may abort, …").

What the kernel does accept *(run)*: a handler that holds the value as its state **and handles the
operation that aborts** (its clause consumes the state, `roll_back(t)`): the abort then does not
pass the handler, and nothing is live across an abort. It checks and runs on Backend2
(`(i32[735], i32[-500])`, `live 0`); the old backend refuses to lower a name with both control and
abortive operations, a lowering limit of that backend (`-- check: old-backend-refuses`).

**Plan.** Fix SPEC §42's two sentences to say "held as the state of a handler that handles the
abort itself", citing `[let]`'s `hW`; add the accepted program to the corpus
(`corpus/decl-handler-state.bc`) and the refused one to `corpus/reject/` with the existing message
(`decl-handler-state-abort.bc`). No checker change and no kernel work.

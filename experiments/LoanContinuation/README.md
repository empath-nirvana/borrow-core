# Loan and typed continuation experiment

Status: **one restricted typed scalar-loan case now checks end to end** in the
[TypedCase experiment](TypedCase/README.md). It includes real capture, typed
heap storage, a second suspension, a changed typed world and registry, return,
and discharge. Its scalar argument and result use the current main `vN` facts;
its resource-aware callable and storage clauses are experimental. The draft
integration adds the checked masked resource/run modules, registry algebra, and
actual-main return bridge under `Core/Chain/SI/LoanX`;
existing typing rules, SPEC entries, and assumptions are unchanged.

The target is one shallow mutable loan sent to a handler, with the real captured
continuation stored during unrelated work, then resumed with the loan returned
and ownership restored. The original two files run against different existing
snapshots. The newer [OwnedClaim experiment](OwnedClaim/README.md) combines the
execution and owned-resource parts over the existing X snapshot; it does not
import or replace the main typed interpretation.

## Checked results

### 1. The existing X rules support a real stored continuation

`Cross821Stored.lean`, theorem `StoredLoanProbe.storedProgram_erwpX`, proves:

1. Start owning one unit cell, with its mutable-loan mask and authority available.
2. Open the loan and perform a linear operation with the exact borrowed cell as
   payload.
3. The actual handler captures a continuation using the existing capture-cell
   implementation and stores that value in a newly allocated heap cell.
4. Allocate and free another cell while the continuation is stored.
5. Retrieve the continuation by consuming its storage cell, and resume it with
   the exact borrowed cell as answer.
6. Close the loan and recover the original ownership. The capture and temporary
   storage cells are consumed. The original mask and ghost authority remain.

This uses `erwpX_handle`, `KapRelX`, the existing heap primitives, and the existing
loan opening/closing rules. There is no assumed handler contract in the final
theorem. The answer predicate is explicitly inhabited. It is an execution result
at `erwpX`, not a typing derivation or a typed logical-relation result.

### 2. A retained claim can preserve the borrowed value's interpretation

`TypedLoanOrder.lean` proposes a list of claims `(location, actual cell lifetime)`.
`Protect` keeps the family at each claimed key and the world's entire `above`
slice at that lifetime. `Future` combines this with the existing `ExtR` condition
on the continuation's physical resource. `UClaims` is a proposed thunk clause
using those futures, factored over a computation interpretation parameter.

Lean checks:

- Transport of the same mutable cell for arbitrary `CPredL`, including predicates
  that depend on the world, and actual `vN(Mut 'x A)` transport for arbitrary `A`
  with its existing uniform-stratum premise.
- An explicit change between distinct valid worlds: an unrelated fresh lend is
  added below the protected lifetime, and the same inhabited borrowed answer
  remains typed there. This is a semantic world move, separate from the X
  program's allocation trace.
- Empty claims specialize to the current `vN` thunk clause when the computation
  parameter is current `cN`. This is not a conservativity theorem for a complete
  new interpretation.
- Current `U`, instantiated with an actual `kappaC`, demands futures that forget
  the loan key when the continuation physically owns only its capture cell.
  This identifies a demand of the current interpretation; it does not prove
  that the actual continuation is untypable.

### 3. Preserving the world does not establish returned-loan identity

`same_lifetime_wrong_answer` proves a concrete counterexample to sufficiency of
the proposed protection plus an ordinary mutable-borrow answer type:

- The outstanding claim protects location **0**, lifetime **1**.
- The proposed future order permits another key at location **1**, lifetime **1**;
  both source and future worlds are valid.
- An answer carrying the borrowed cell at location **1** satisfies ordinary
  `vN(Mut 'x unit)` and has **no cell at location 0**.
- That answer composes with the continuation's owned capture cell at location
  **2**, so the wand's composition premise does not exclude it.

This does not establish that a typed source clause can manufacture the answer,
or refute language safety. It establishes that this future order and ordinary
`vN(Mut ...)` alone cannot identify which loan must be returned. The X witness's
exact answer predicate supplies an obligation the proposed typed interface still
needs to express and justify.

### 4. Owned claims compose with storage and a second operation stop

`OwnedClaim/W1.lean`, theorem `OwnedLoan.storedProgram_owned`, proves the
combined program in `erwpX`:

1. Starting from an owned unit cell and existing lifetime/mask authority, open a
   shallow mutable loan and mint matching claim/permission fragments in the
   existing authoritative-registry algebra.
2. Send the borrowed cell and its permission to a linear handler. The captured
   continuation keeps the claim and lifetime authority.
3. Store the actual captured continuation in a heap cell, allocate/free another
   cell, and perform a second operation while the first continuation is stored.
4. Give registry authority to the second operation's responder. The suspended
   computation retains the stored continuation, loan, and fragments. The reply
   contract accepts an arbitrary authoritative registry; compatibility with the
   retained fragments enforces agreement on the outstanding loan.
5. Retrieve the first continuation and resume it with a **branded return**:
   borrowed cell plus the permission for this loan. Matching follows from
   resource validity, including the same location, lifetime, and predicate.
6. Restore ownership and retire the authoritative entry, consuming both loan
   fragments. The final condition retains the retired registry and lifetime
   authority.

The theorem uses the real handler/capture rules, rather than assuming a
continuation with the desired behavior. Allocation, unrelated registry
extension, matching, and retirement use generic resource-algebra laws. A
derived ghost-update rule connects those laws to the existing masked relation;
no execution rule or handler law is added as an assumption.

The second operation remains an external stop governed by its table contract.
The theorem proves the resumption obligation for every compatible reply; it is
not a scheduler or a closed operational trace. The fixtures provide an inhabited
reply at a changed registry. This registry change is **not** yet transport
between arbitrary main-kernel `KW`/`LocTy` worlds.

The resource algebra alone does not enforce eventual return: validity is
downward closed. The branded argument, visible pending entry at a stop, and
retired-entry final condition are essential parts of the protocol. In
particular, `terminal_requires_return` excludes a successful terminal condition
while a matching nonempty borrower permission remains in an external frame,
even with arbitrary garbage ghosts.

### 5. The return contract has a precise boundary in the actual typed model

The [typed bridge](TypedBridge/README.md) uses unchanged main `Goal791N.vN/cN`.
Its shallow-return characterization records the location, **actual** cell
lifetime, and full indexed predicate family. A returned cell may use a different
member of that family at a suitable later index. Given the current world's
family-coherence and existing uniform-stratum facts, this reconstructs the
actual `vN(Mut a A)` interpretation, including recursive payload types `A`.
When the physical borrow is present, the existing `ExtR` relation supplies the
facts needed to transport that brand. This does not yet transport a parked
continuation that holds only a ghost claim.

`TypedBridge/MemberBoundary.lean` checks why the full family matters: at positive
index 1, main's `MutStep` accepts changing a cell from family member 2 to member
1, but the fixed old predicate return contract rejects that same cell. Location
and lifetime have not changed. This is an explicit downward-closed semantic
family, not a claim that a particular source program has that family.

Two further boundaries follow from the actual definitions. An ordinary `Mut`
arrow owes behavior for every compatible typed argument, rather than one
particular loan identity. And `Ref(U C)` storage containing only owned physical
cells still demands every valid future world: those owned cells do not make a
ghost loan visible to current `U`. These are requirements of the current model,
not a proof that every stored continuation is untypable.

### 6. A restricted typed stored-continuation case checks

The [TypedCase experiment](TypedCase/README.md) connects positive owned claims
to a proposed `ScalarU` and compositional `RefX` clause. Its
`complete_scalar_case` theorem checks the real stored-continuation program,
actual main `vN(Mut 'x unit)` at a changed world, and actual main `vN(Ref unit)`
at the result. It derives the typed return from registry agreement and the
owned claim. Wrong-slot and forged same-slot returns are rejected. The
experiment is replayable against this checkout with `TypedCase/check.py`.

The scope is one-shot, shallow unit/scalar loans with fixed mask and scope list.
It does not change the current `U` interpretation or prove a general fundamental
theorem, scheduler, cancellation rule, or higher-order family transport.

## What works under which conditions

The checked envelope is a **one-shot, must-resume, shallow mutable-loan
protocol**. It allows actual heap storage and further suspension, with unrelated
registry changes, provided that:

- The continuation retains its claim and lifetime authority.
- A return carries the loan-specific permission and the matching physical
  cell. Its contents may be any value satisfying the original predicate.
- Registry updates remain compatible with all outstanding fragments.
- The segment mask and scope-record list stay fixed; the location-family
  environment is empty in this probe. Changing the ghost registry does not yet
  establish transport of world-dependent typed families.
- The run returns ownership and records retirement before claiming successful
  completion.

An ordinary same-lifetime `Mut` answer does not supply this identity contract.
The earlier wrong-answer counterexample explains why. Both experiment entries
are linear and must resume; cancellation, dropping the pending continuation,
and multi-shot use are outside the checked envelope, rather than established
impossibility results. Structured task or I/O designs would additionally need
their stop, join, and cancellation rules proved against this contract.

For practical use cases, the first target is a handler or suspended operation
that temporarily receives an exclusive resource and returns that same loan on
its one completion path. A task or I/O operation could fit this pattern if its
owner survives until completion and any cancellation protocol first establishes
that no child or external operation can still use the resource. The experiment
checks the storage/stop/return structure, not those scheduler or runtime facts.
Unrestricted multi-shot invocation and dropping a pending continuation do not
meet the proved contract. Lending state that itself contains loan-bearing
closures also needs the recursive typed-storage work, beyond this shallow probe.

## Remaining typed theorem

The restricted `ScalarU`/`RefX` case now expresses and preserves this protocol
through typed heap storage. The main remaining question is how to integrate a
general owned-claim protocol into the language's recursive value/computation
interpretation. Neither the earlier `LoanU` nor the new `ScalarU` is the current
`vN` clause for `U(Mut β A → C)`.

That resource contract must then be used consistently by a masked, world-indexed
execution relation and the recursive value/computation interpretation, including
stored `U`. It must account for the floor and `FoldInv` obligations of current
`KW.Owed`, or prove their replacement sufficient. Recovering the existing
computation interpretation with zero ghost resources and an empty mask also
remains open; merely having no pending claims is a weaker condition. Simply
adding claims to `KW` leaves the incompatible unmasked `UpdVN` requirement in
place.

The next implementation step is to generalize the scalar descriptor to indexed
families, then connect the proposed callable/storage clauses to a recursive
typing theorem. The checked scalar case and value-level bridge are not yet a
fundamental theorem, a discharge of `HandlerLawN`, or a cancellation result.

## Reproduction

Toolchain: `leanprover/lean4:v4.33.1`.

- Main interface snapshot: `c1d16d42fa43fd919c97d343750f4e94bcf7b618`.
- Warm main build used: `1fa13095c93597f30149c6693c1d14a5120378f6`, whose imported
  interface files are unchanged from that snapshot.
- X snapshot: `cross-821`, `bbf8f16af3c27646c85384d1dba3f5e9f1050ce3`.

Commands used in this workspace:

```sh
cd /private/tmp/borrow-core-remove-chain-fragments
lake env lean /Users/johnthompson/repos/borrow-core/experiments/LoanContinuation/TypedLoanOrder.lean

cd /Users/johnthompson/repos/borrow-core-cross821
lake env lean /Users/johnthompson/repos/borrow-core/experiments/LoanContinuation/Cross821Stored.lean

lake env lean /Users/johnthompson/repos/borrow-core/experiments/LoanContinuation/OwnedClaim/W1.lean

cd /private/tmp/borrow-core-remove-chain-fragments
lake env lean /Users/johnthompson/repos/borrow-core/experiments/LoanContinuation/TypedBridge/MainBridge.lean
lake env lean /Users/johnthompson/repos/borrow-core/experiments/LoanContinuation/TypedBridge/MemberBoundary.lean
```

The original two files completed with exit code 0, without warnings. Printed axioms are subsets of
`[propext, Classical.choice, Quot.sound]`. The adjacent check logs record those
results; the owned-claim experiment has its own check log and reproduction notes.
The newer typed case has its own durable source tree and `check.log`.
There are no admitted proofs or new axioms. No full repository gate was
run: the experiment changes no production code and spans two separately checked
snapshots. `typed-notes.md` contains the Sol agent's detailed typed-interface
analysis and original scratch paths.

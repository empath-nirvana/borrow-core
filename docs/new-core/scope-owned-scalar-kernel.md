# Owned scalar loans in main Core: first integration slice

Status: draft kernel scope for #821 / #844 Tier 2, based on the checked
`experiments/LoanContinuation/TypedCase` case. This document is the proposed
content for a new SPEC entry. It does not itself change `SPEC.md` or a production
typing rule; docs-foreman assigns the entry and version before `Core` changes.

## Target program and done-when

The first target is `TypedCaseProof.Program.storedProgram`: an exclusive scalar
loan is sent to a linear handler; its actual captured continuation is stored in
an owned heap cell, survives unrelated allocation/free and a second suspension,
then is retrieved, resumed with the matching borrowed cell, and discharged.
The second stop may answer at a different valid typed world and registry. Its
explicit table contract does not implement an outer scheduler.

Integration is complete only when a main `CDerives` judgment types this program
(or a definitionally equivalent core term), a main semantic fundamental theorem
concludes its computation judgment, and main adequacy concludes its run. A
standalone `vN` fact for the scalar input or result, or a theorem only in the
experimental `erwpX`, does not meet this criterion.

## Evidence already checked

- `TypedCaseProof.Case.complete_scalar_case`: the full masked execution, a
  valid changed-world/registry reply, actual main `vN(Mut 'x unit)` for the
  return, and actual main `vN(Ref unit)` for the result.
- `TypedCaseProof.WorldSat.owned_return_any`: positive claim plus registry
  validity and physical return permission identify the exact scalar descriptor
  and reconstruct actual main `vN Mut` without a location side assumption.
- `TypedCaseProof.TypedResources.RefX_zero_iff`: the proposed storage clause
  agrees with main `vN Ref A` for a zero-ghost lift of a main value relation.
- Negative controls reject wrong-slot and forged same-slot returns, ghost
  erasure from the callable or stored value, and frame-preserving close without
  the return permission.
- `TypedBridge.current_update_cannot_close`: current `UpdVN` cannot turn the
  borrowed endpoint into the owned endpoint. This is why simply interpreting
  the current `U` clause at the new return is insufficient.

Run `python3 experiments/LoanContinuation/TypedCase/check.py` from the repo
root. The durable check uses the current main `Goal791N` definitions and no
new axioms or admitted proofs.

## Main-kernel boundaries that must change

1. **Execution resource and update.** Main `rwpG` and `erwpK` consume `WRes`
   and use `UpdVN`. The checked loan run uses a physical resource plus owned
   ghost claim, with frame-preserving allocation, transfer, and close. The
   main relation must carry that combined resource through ordinary steps,
   capture, heap storage, stops, and terminal posts. Its physical projection
   must retain the frame and mask guarantees required by main's borrow lemmas.
2. **Typed world.** Main `KW = (Θ,c,lo)` and `KW.Owed` require `ExtP`, `OK`,
   `ConsistentX`, floor monotonicity, and preservation of every relevant
   `FoldInv`. The experiment's `WorldSat(m,Θ)` establishes scalar registry/key
   coherence but does not imply those `KW.Owed` obligations. The new world
   interface must combine both, and every admitted stop reply must satisfy it.
3. **Recursive value and computation interpretation.** Main `vNE(U C)` uses
   physical `ExtR` and main `vNE(Ref A)` recursively stores only physical
   resources. The experiment's `ScalarU` requires a positive claim and a
   branded return contract; `RefX` retains the complete resource of its
   stored value. The kernel needs a compositional typed clause whose return
   identity is expressed by the operation protocol. It cannot be inferred
   from the ordinary unbranded `Mut` arrow alone.
4. **Typing and adequacy.** Prove the handler and storage compatibility rules,
   fundamental property, and adequacy over the resulting relation. The
   checker and lowering may use the new rule only after this kernel theorem.

## Proposed implementation order

**K-L0 — Resource/run seam.** Specify the combined resource and masked update
in main, including ghost validity and frame-preserving registry laws. Prove a
main-level scalar open/close under the new run while preserving the current
`UpdVN` and no-loan cases as explicit regressions. In particular, prove the
physical frame and world conditions needed at a stop; do not assume the
experimental stronger `FrameKept` relation is equivalent to current `rwpG`.

**K-L1 — Typed world and storage seam.** Extend the main stop world to track
the claim and scalar family coherently while retaining all `KW.Owed` fields.
Establish a resource-aware `Ref` clause and a positive-claim continuation
clause. Prove the zero-protocol embedding for recursive values and runs, not
only the isolated value-level `RefX_zero_iff`.

**K-L2 — One vertical theorem.** Add the narrow loan-return typing interface,
prove its handler compatibility, and type and conclude `storedProgram` in the
main judgment. Preserve the statements or derive replacements for the
fundamental property, adequacy, and every existing borrow guarantee. Run the
required local gate before promoting the PR from draft.

The interface design for K-L1/K-L2 is deliberately open: a general replacement
of the value resource carrier and a restricted loan-return computation former
have different compatibility costs. No new `CDerives` index is needed. Before
choosing a former, show how its return brand is supplied by a typed operation
and survives `Ref` and a second stop. This is the first kill test. A relation
that proves only the scalar result but cannot state that stored continuation
obligation is not the integration.

## Baselines and open cases

The new entry must preserve current ordinary no-loan `cN`/`vN` cases,
`goal791N` and its existing `HandlerLawN` boundary, all borrow guarantees,
and existing corpus outputs. The entry adds no permission to cancel/drop the
one-shot continuation or to resume it twice. General indexed payload families,
cross-task loans, `withlocal` across `await`, effectful cancellation, and an
outer scheduler remain open after K-L2.

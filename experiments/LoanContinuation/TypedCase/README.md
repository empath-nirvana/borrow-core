# One restricted typed scalar-loan case

**The case works.** `TypedCaseProof.Case.complete_scalar_case` proves the owned scalar loan through a real linear capture, typed heap storage, unrelated allocation/free, an additional park stop, retrieval, matching return, and ownership-recovering discharge. The same theorem includes an inhabited reply at a genuinely changed current-main location typing and registry.

This is a proposed **restricted branded callable/Ref slice** over masked execution. Its scalar argument and result facts are the actual current `Goal791N.vN` interpretation. It does not claim the unchanged ordinary `U`/unbranded arrow already implements that protocol, or a full fundamental theorem for a new recursive interpretation.

## Reproduce and inspect

Run from this checkout:

```sh
python3 experiments/LoanContinuation/TypedCase/check.py
```

`check.py` checks the new `Core/Chain/SI/LoanX` modules and the isolated typed proof against this checkout, writing `check.log`. It does not rebuild the production library broadly. The experiment was developed against current main `c1d16d42fa43fd919c97d343750f4e94bcf7b618`, using the same-semantic warm build at `/private/tmp/borrow-core-remove-chain-fragments` (`1fa13095c93597f30149c6693c1d14a5120378f6`). Relevant `Goal791N`, `LocTy`, and `ErwpK` source blobs are identical between those snapshots, as recorded in `../TypedBridge/README.md`.

All proof modules were checked individually with exit 0 and no warnings/errors before packaging. Every printed axiom set is contained in `[propext, Classical.choice, Quot.sound]` (`choice` can be printed under an open namespace). There are no admitted proofs, new axioms, unsafe code, or native_decide. The exact durable-tree replay log is `check.log`.

Important source locations:

- `Core/Chain/SI/LoanX`: masked run/heap/handler rules, registry algebra, actual-main `vN` return bridge, `LoanKW.Owed` with a concrete changed-world reply, the world-indexed `erwpKX` perform table, and one-way zero-ghost run erasure.
- `ProofTree/TypedCaseProof/Case.lean`: `complete_scalar_case`, positive/negative controls.
- `Program.lean`: the generic complete restricted program theorem.
- `ClaimHandle.lean`: generic positive ownership through actual linear capture.
- `TypedResources.lean`: compositional RefX, ownership preservation, exact zero-ghost current Ref specialization.
- `Protocol.lean`: the proposed ScalarU, admitted futures and actual-main typed application.
- `TypedStore.lean`: actual typed allocation/store/park/retrieve/resume proof.
- `WorldSat.lean`: authoritative registry/current-main family coherence and changed-world fixtures.
- `Execution.lean`: claim creation with opening and matched typed closure.

The draft PR adds the checked masked resource and execution modules, generic registry algebra, and actual-main scalar return bridge under `Core/Chain/SI/LoanX`; existing `rwpG`, `erwpK`, `Goal791N.cN`, typing rules, and SPEC remain unchanged. `OwnedClaim/W1.lean` and the earlier `TypedBridge` baselines remain unchanged. No general adequacy result is claimed.

## The program and the proof path

The program starts with a location owning unit and a registry authority. Opening creates the lender claim and borrower return permission through the generic frame-preserving registry update and folds the owned cell into its mutable loan. It then performs operation 7.

The actual must-resume handler captures `kappaC`. `claimTable` carries a POSITIVE ghost assertion on the stopped continuation share; `handle_claim_le` proves that actual capture-cell allocation preserves it. The clause consequently receives both owned claim and derived execution obligation. It does not assume a typed continuation law.

The clause constructs `ScalarU` from those facts, allocates a cell containing the real captured value, and constructs `RefX ScalarU` at that allocation. It allocates and frees another cell while κ remains stored, then performs a real operation 8 (`park8`). The park hands the registry authority to its resumer; the paused computation retains the storage cell, first κ's owned claim, and the physical loan/return permission.

The park's explicit reply may contain a different authoritative registry and a different valid main location typing. After reply, `typed_retrieve_resume` consumes the actual storage cell and invokes `ScalarU_apply`. Owned registry agreement identifies the returned loan; world satisfaction gives the coherent current-main scalar family. The application derives actual `vN(Mut 'x unit)` for the argument and runs the captured continuation in the masked relation. Matched closure consumes both fragments, retires the registry entry, restores ownership, and establishes actual `vN(Ref unit)` in the result postcondition.

The final table remains the explicit typed park8 protocol. The theorem proves the continuation for **every admitted reply**, including the concrete changed-world reply. It does not implement an outer scheduler or assert eventual resumption. Indefinite parking/divergence remains possible.

## What is typed, and what changed

`WorldSat m Θ` links authoritative scalar descriptors to actual main world keys: whenever `m γ` names `unitLoan(l,β)`, `Θ(l,β)` contains main's indexed unit family. Other registry entries are allowed; this is not a complete typing of every possible registry descriptor.

`ScalarU` is NOT an alias of KapRelX. It requires:

1. a positive owned scalar claim, including at index zero;
2. future registry/world pairs satisfying WorldSat and valid composition with the owned claim;
3. a return permission for the same slot, physically coupled to its descriptor;
4. actual current-main Mut typing derived from that agreement;
5. masked execution of the real captured value at every smaller index and the fixed scope list.

No arbitrary extra global world freezing is imposed. The owned claim preserves the relevant registry descriptor; WorldSat supplies the required current key. Scalar/unit families are independent of the world-above slice and the member index. The earlier `MemberBoundary` result explains why general higher-order families need a more general descriptor/return relation.

`RefX R` is generic: the owned storage cell carries zero ghost and composes with the stored value's COMPLETE XRes payload. Thus storing κ does not erase its claim. `RefX_preserves_owned` is a generic ownership law. `RefX_zero_iff` proves exact agreement with actual current `vN(Ref A)` when the payload is a zero-ghost lift of current `vN A`, including `A = U C`.

The proposed callable protocol is branded/relational. It does not promise that ordinary unbranded `Mut β` arrows can select which outstanding loan must be returned. No new surface syntax is prescribed in this experiment.

## The changed future is real and inhabited

The concrete original world contains the first key `(location 0, lifetime 1)`. The future adds `(location 1, lifetime 2)` and an active unrelated loan descriptor. Both main worlds are valid; both the world and registry differ. `W1_allocate` proves a generic frame-preserving allocation of the second loan's claim and return permission. `W1_admitted`, `W1_reply`, and `W1_return_actual_main` prove valid composition, an inhabited typed park reply, and actual main Mut typing at the future world.

The new loan is a surrounding-world action permitted by the park contract. `W1_main_reply_admitted` additionally checks the changed world against main `KW.Owed` at the stop floor for an owned continuation share. The enclosing scheduler/resumer implementation is outside this case. The first computation's unrelated heap allocation/free is actual code, executed while κ is heap-stored.

## Negative and baseline controls

- `wrong_return_rejected`: a legitimate permission from a different slot is not the required return.
- `forged_same_slot_rejected`: labeling a different loan descriptor with the expected slot is invalid.
- `ScalarU_no_ghost_erasure`, `ScalarRef_no_ghost_erasure`: even a small-index execution obligation cannot fabricate ownership, and the typed storage wrapper cannot lose it.
- Generic `close_without_return_impossible` from the reused algebra excludes frame-preserving close without the matching borrower permission.
- The result postcondition retains the retired authoritative registry; dropping all ghosts is not counted as successful discharge.
- `zero_protocol_stored_U`: an inhabited current-main `Ref(U(F unit))` is recovered through the generic zero-ghost Ref clause. This is a VALUE-clause specialization, not an execution-equivalence theorem.

## Compatibility harness and precise limits

`Core/Chain/SI/LoanX` now holds the previously checked cross821 masked-execution proof modules as additive main-kernel infrastructure, together with the registry algebra and actual-main scalar bridge. Main and cross cannot be imported directly together: main added structured LocFam/ImmTieL and removed the old FrameKept guard from its rwp/rwpG. These modules retain masked X's STRONGER FrameKept semantics and derive guarded owned heap rules directly. `rwpGX_erases` proves that a zero-ghost, empty-mask run with a zero-ghost post entails current `rwpG`; the converse is not claimed. No existing production import or definition is changed; `Goal791N.cN` does not yet use this relation.

The case has one shallow mutable unit/scalar loan, one-shot capture, empty stored witness, fixed scope-record list and mask, and empty execution LocFam outside the masked loan. It admits actual-main scalar world changes justified by registry coherence. It does not prove arbitrary KW/floor/FoldInv transport, recursive higher-order family compatibility, cancellation/quiescence, shared loans, nested borrow-view reconstruction, multi-shot continuations, or a general scheduler/fundamental theorem.

The mechanism demonstrated is general positive continuation ownership, compositional resource-aware storage, and resource-derived typed future admissibility. Generalizing the payload or source computation interface remains separate work. Having no pending loan is not zero protocol: registry/lifetime authority and masks may remain. No unconditional ghost/mask erasure or unchanged ordinary-U claim is made.

## Connection required in main Core

The current result is not a theorem of main `Goal791N.cN`. Main `vNE` gives
`U C` only a `WRes` and quantifies over `LocTy.ExtR` at that physical resource;
main `Ref` recursively stores that same physical-resource interpretation.
`ScalarU` and `RefX` instead retain an `XRes` ghost claim. In addition,
main `erwpK` runs `rwpG` with `UpdVN`, while this case uses the stronger masked
`erwpX` update and frame relation. The scalar `vN` facts in this experiment
bridge the return and result values, but they do not equate the two execution
relations.

A main-kernel integration must therefore establish, in order:

1. A resource-aware run and world interface that carries claims through
   capture, heap storage, stop, and close. Its world order must retain main
   `KW.Owed` obligations, including `ExtP`, `FoldInv`, views, and floors. The
   physical update rule must admit the masked loan open/close without silently
   weakening main frame guarantees.
2. A recursive typed callable/storage clause that uses the owned claim and
   branded return contract. It must compose with ordinary types and prove the
   zero-protocol baseline for the existing `U`/`Ref` fragment, not just the
   value-level `RefX_zero_iff` proved here.
3. A compatibility proof for the relevant handler and typing rule, followed by
   fundamental property and adequacy over the new relation. The concrete
   stored program must then be typed by main's judgment and concluded by
   that adequacy theorem.

The first decision for a SPEC entry is whether this is a general replacement
of the main resource interpretation or a restricted type former with an
explicit loan-return protocol. Copying `ScalarU` into `Core` alone would not
meet the integration criterion: no existing main judgment would assign it,
and no main execution theorem would consume its claim.

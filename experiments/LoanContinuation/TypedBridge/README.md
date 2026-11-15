# Bridge to actual main vN/cN

The owned-claim W1 proof remains immutable. This follow-on checks the actual main interpretation rather than defining another toy U or aliasing KapRelX.

## Artifacts and reproduction

- `MainBridge.lean`: actual recursive `Goal791N.vN/cN` extraction, reconstruction, transport, storage/domain tests, and a positive no-loan storage regression.
- `check.log`: exact-path compile, exit 0, no warnings/errors; all 12 printed headline axiom sets are subsets of `[propext, Classical.choice, Quot.sound]`.
- `MemberBoundary.lean`, `member-check.log`: independently checked production `MutStep` member-evolution counterexample. This family is downward closed; the file explicitly does not claim it is the interpretation of a particular source type.

Main source snapshot: `/Users/johnthompson/repos/borrow-core`, `c1d16d42fa43fd919c97d343750f4e94bcf7b618`.
Warm same-semantic build: `/private/tmp/borrow-core-remove-chain-fragments`, `1fa13095c93597f30149c6693c1d14a5120378f6`.
Relevant source blobs are identical in those two checkouts:

- Goal791N: `1fd45df8435abac2dfa347232f124856b6569fc0`
- SI/LocTy: `aea5c658df796fc2a10abc1070b3bedeb2cd4079`
- SI/ErwpK: `d9b0eb285998436c450d012a4e1e13ad7bdcff67`

```sh
cd /private/tmp/borrow-core-remove-chain-fragments
lake env lean /Users/johnthompson/repos/borrow-core/experiments/LoanContinuation/TypedBridge/MainBridge.lean > /Users/johnthompson/repos/borrow-core/experiments/LoanContinuation/TypedBridge/check.log 2>&1
lake env lean /Users/johnthompson/repos/borrow-core/experiments/LoanContinuation/TypedBridge/MemberBoundary.lean > /Users/johnthompson/repos/borrow-core/experiments/LoanContinuation/TypedBridge/member-check.log 2>&1
```

Production Core and SPEC were not changed. No broad rebuild or full repository gate is claimed.

## The checked physical/type bridge

`shallow_mut_iff_brand` is an equivalence with ACTUAL current `vN(Mut a A)`, restricted only to an empty stored witness. It extracts:

1. interpreted type lifetime alpha and ACTUAL cell lifetime beta, with alpha <= beta (the existing slack);
2. exact location l;
3. the full indexed family F, with `Theta(l,beta)=some F`;
4. `F = famL beta (vN A delta) Theta`, plus Mut's existing uniform-stratum requirement;
5. a physical returned cell whose predicate is SOME member `F j`, with `current_index <= j`.

`FamilyBrand` is proof-carrying metadata, NOT an owned ghost resource or a new type interpretation. `ReturnedCell` allows different contents and different indexed members of the same family. `returned_to_vN` reconstructs the real recursive interpretation, with arbitrary A (including higher-order types) when its existing semantic premises hold.

`returned_future_typed` derives reconstruction at a future world using EXISTING ExtR at the RETURNED PHYSICAL BORROW. `CellIn` supplies the relevant key and above-world agreement; the theorem does not assume an arbitrary transport axiom. It does NOT establish that a parked, claim-only continuation owes those worlds: that resource does not contain the borrow cell.

`W1_scalar_return_main` is the concrete useful bridge: the scalar/unit physical cell used by OwnedClaim/W1 has main's actual Mut type at every index whenever the current world has the coherent unit-family key. `unit_member_constant` proves why W1's fixed P descriptor suffices for this index-independent case.

## Why fixed P is not the general descriptor

`MemberBoundary.fixed_member_is_not_a_general_loan_identity` checks a production `MutStep` at POSITIVE index 1, same location and lifetime, moving from family member 2 to member 1. The predicates differ and the W1-style fixed-old-member return test rejects the resulting cell.

This establishes a limitation of the fixed-member identity scheme, not source unsoundness and not a claim that every downward-closed family is source-definable. A general owned descriptor must name stable FAMILY identity (or an equivalent justified encoding), while its return relation admits the legal current member and content. It must not equate legitimate member evolution with returning a different loan.

## Three independent interpretation boundaries

### Identity/domain

`ordinary_arrow_all_brands` eliminates ACTUAL current `cN(arr (Mut a A) C)`: it requires the body at every compatible typed brand in the world, not just the loan retained by this particular continuation. Lifting an ordinary Mut argument to a physical cell plus an existential permission does not solve this: distinct legitimate loan permissions can coexist.

The continuation's argument/answer obligation must relate the returned permission to its retained loan identity. This is a branded/relational semantic protocol contract, not merely a WRes-to-XRes carrier change. This spike does not prescribe new surface syntax or prove existing syntax can already express the contract.

### Storage/futures

`stored_U_all_worlds` eliminates ACTUAL `vN(Ref(U C))`. When its physical resources contain only owned storage/capture cells, its stored thunk must work at every valid location typing. Those cells contribute no `CellIn`; adding the heap storage wrapper does not make ordinary U see a ghost loan claim.

This is a demand theorem, NOT a proof that such a stored thunk is untypable. `plain_U_unit` and `plain_stored_U_unit` give inhabited actual-main examples at every index, so the regression does not rely on an impossible storage guard.

The owned resource must therefore survive reference composition AND participate in U's future-world admissibility through a proved world-satisfaction invariant. Authority/fragment agreement can preserve the family descriptor; it does not by itself prove that the descriptor still equals the current recursive payload interpretation.

### Execution

`current_update_cannot_close` checks that unchanged production UpdVN cannot relate the exact mutable-cell endpoint to the same location's owned-cell endpoint. This is a precise endpoint obstruction, not a blanket claim about every typed source expression. Together with the already proved owned-to-borrow stop obstruction, it confirms that adding brands only to world/value indices while keeping cN's rwpG/UpdVN segments unchanged does not embed W1. A typed, world-indexed masked execution relation is still needed.

## Exact next bounded implementation step

Keep the first integration target one-shot, shallow, scalar/unit, without cancellation, under the fixed mask/scope envelope already checked by W1:

1. Replace the fixed-member descriptor in a NEW experiment with `(identity, location, actual lifetime, indexed family F)`. Keep the claim/borrower authority laws generic; do not overwrite W1.
2. Interpret returned branded arguments as the matching owned permission composed with `ReturnedCell F n`. `returned_to_vN` is the checked physical-to-current-Mut lemma this boundary should call.
3. Introduce world satisfaction coupling the authoritative descriptor to the current location typing. The exact missing entailment is: compatible authoritative future + owned claim + world satisfaction => `BrandAt A delta Theta' brand`. For scalar unit, only the coherent key is needed; for general A, family/current-payload coherence remains a semantic obligation.
4. Make stored Ref/U carry the ghost resource compositionally. U's futures must follow the worlds justified by that owned resource, rather than silently assuming current physical-only ExtR protects it.
5. Use a branded/relational return-domain contract, and a masked typed execution layer for ret/effect segments. Re-prove the real capture/store/additional-stop/resume theorem for that restricted typed slice, with ACTUAL vN unit/Mut payloads. Do not assert ordinary unbranded U from KapRelX.

The current ordinary Mut physical shape, its lifetime slack, existing uniformity premise, indexed family/member machinery, scalar/unit interpretation, and the physical reference allocation/retrieval behavior can remain. Resource composition, U's future clause, the relational answer contract, and cN's execution instantiation cannot all remain unchanged.

Generalizing A to recursive/higher-order payloads requires compatibility of the revised mutual vN/cN interpretation and stored families; KW.Owed's floor/FoldInv obligations are not discharged here. No new global world freeze is proposed: any protection must be entailed by owned obligations and world satisfaction, or replaced by a sufficient semantic noninterference theorem.

## Empty-loan versus zero-protocol baseline

The positive plain-U storage lemmas preserve an inhabited CURRENT no-loan case. They are not a conservativity theorem for the new owned interpretation.

Having no pending loans is weaker than having no protocol resources: W1 still retains a registry authority, lifetime authority, and mask. Existing cross821 `erwp_iff_erwpX0` requires zero ghost, empty mask, and its table/post embeddings. A genuine bridge to current cN/vN must state that zero-protocol specialization explicitly, including its world-indexed execution/future conditions. No unconditional ghost/mask erasure is proved here.

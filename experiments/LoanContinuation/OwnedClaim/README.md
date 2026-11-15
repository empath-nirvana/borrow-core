# Owned claim, stored continuation, and a second stop

This is a checked **combined masked-protocol experiment**, not a proof of main's `Goal791N` interpretation. `W1.lean` is standalone and imports the existing cross821 `Core.Chain.SI.HandleX`; production Core and SPEC are unchanged.

## Reproduce

Source/build snapshot: `/Users/johnthompson/repos/borrow-core-cross821` at `bbf8f16af3c27646c85384d1dba3f5e9f1050ce3`, using its existing warm build and Lean 4.33.1.
Artifact location is in main (`c1d16d42fa43fd919c97d343750f4e94bcf7b618` before these isolated artifacts).

```sh
cd /Users/johnthompson/repos/borrow-core-cross821
lake env lean /Users/johnthompson/repos/borrow-core/experiments/LoanContinuation/OwnedClaim/W1.lean > /Users/johnthompson/repos/borrow-core/experiments/LoanContinuation/OwnedClaim/check.log 2>&1
```

The adjacent log records every headline's `#print axioms`. Allowed dependencies are only `propext`, `Classical.choice` (sometimes printed as `choice` under the open namespace), and `Quot.sound`. No full repository gate is claimed or required for this isolated experiment; no production library imports it.

## What changed semantically

No GRes/XRes validity field, machine rule, or erwpX definition was modified. The experiment uses the EXISTING registry fields:

- `reg m`: unique authoritative registry map (`auth`).
- `claim γ d`: lender fragment (`tokF`) for the loan descriptor at slot γ.
- `permit γ d`: borrower return permission (`wrF`).

A descriptor is the existing `Loan.mut l β P`, stored as a singleton `Ret`. `cellOf` couples that descriptor to the actual shallow mutable cell, its location/lifetime/payload family, and an admissible current value. Registry agreement relates the owned lender and borrower fragments. It is not inferred from generic product compatibility.

`allocate` is a GENERIC frame-preserving update creating the registry entry and BOTH fragments at a fresh slot. `open_owned` combines that update with the existing mutable loan-open rule. `close_owned` combines physical loan-end with a GENERIC frame-preserving update consuming both matching fragments and retiring the authoritative entry to `[]`.

The authority stays with the handler/run, not inside the first stored κ. The κ retains its lender fragment and existing lifetime mask authority. The handler can therefore change unrelated registry slots while κ is stored; independently stored κ fragments can coexist.

`Returned γ` is an EXPLICIT BRANDED SEMANTIC ARGUMENT CONTRACT: it returns a physical `cellOf d`, the borrower permission for γ and d, and a registry authority. `LoanU` is `KapRelX` instantiated with this contract: a genuine smaller-index masked resumption obligation over arbitrary registry replies. It is not unchanged ordinary `vN(U(Mut β A → C))`. `returned_match` derives descriptor/family agreement from actual combined ghost validity, with no external logical claim-list D.

## Combined execution theorem

`storedProgram_owned` proves, at every index and without an assumed continuation law:

1. Starting with the original owned unit cell and an authoritative registry with a fresh γ slot, create the owned claim/return permission and open its mutable loan.
2. Perform the real linear operation 7, transferring the borrower cell/permission and registry authority to its actual handler, while the captured continuation retains the lender claim.
3. The handler receives the real captured κ through `erwpX_handle`, stores it in an allocated heap cell, and performs a separate allocate/free while it remains stored.
4. Perform an ADDITIONAL real linear `park8` stop while κ is still heap-stored. Its PA gives registry authority outward; the continuation retains the storage cell, borrowed cell, and both loan-related fragment resources.
5. The park reply supplies registry authority at any compatible updated registry. Retrieve the original κ, return the branded borrowed cell, and resume through the genuine `LoanU`/`KapRelX` obligation.
6. Release the actual capture/storage cells, recover the original location's ownership, consume both matching fragments, and return an authoritative registry whose γ entry is retired.

The final table is the EXPLICIT park8 protocol, not a fully implemented scheduler/outer park handler. This is the requested additional stop with an inhabited resumption contract. It is not a claim of closed-program adequacy. The program theorem universally accepts compatible registry replies; the concrete W1 fixtures instantiate a genuinely changed one.

`W1_program` supplies concrete unit/scalar parameters. `W0` contains the original pending loan; `W1` additionally contains a NONEMPTY unrelated loan descriptor at a different location/lifetime. `W1_opens_unrelated` allocates its two permission fragments through the same generic update, and `W1_all_permissions_valid` proves all original/new fragments coexist. `W1_park_reply` and `W1_returned` inhabit the actual program's reply/return predicates. The other loan's fragments may remain with the surrounding world; the original κ need not monopolize global authority.

## Negative and positive controls

- `positive_initial_ghost`, `positive_W1_ghost`: actual initial and matching-answer guards are valid; no zero-index/PB-empty/wc-false success.
- `future_family`: authority agreement at the owned claim protects precisely its descriptor/family; no arbitrary global world freeze.
- `two_loans_coexist`: distinct loan identities may coexist at the SAME lifetime.
- `same_lifetime_wrong_return_rejected`: the different legitimate loan cannot satisfy the γ-branded return contract.
- `forged_same_slot_rejected`: pairing the wrong descriptor with the expected slot also fails registry agreement.
- `close_without_return_impossible`: authoritative close without the borrower permission is not frame-preserving; the adversarial frame holding that permission witnesses failure.
- `terminal_requires_return`: even existing EndOKX, with arbitrary garbage ghosts, cannot certify retired authority while that permission remains in the frame.
- `park_debt_visible`: every accepted park8 exposes authoritative pending debt; erasing the registry is not an accepted park boundary.
- `no_pending_after_close`: an active lender fragment cannot coexist with the retired authoritative entry, including when that fragment was placed in garbage.

These do NOT say ordinary ghost validity forbids dropping a fragment: it is downward closed. The completion/stop contracts retain authoritative ledger state. Losing a fragment cannot count as a successful ownership-recovering discharge; it can instead prevent successful completion. No eventual-return/liveness theorem is claimed.

## Exact limits

- This models a shallow mutable loan with empty stored witness and a fixed semantic payload predicate P. The concrete program does not mutate the contents; the generic return/close rule admits any returned value satisfying P.
- The modeled typed continuation is the branded flat-family `LoanU` protocol over erwpX. It does not integrate main `Goal791N.vN/cN`, ordinary unbranded U, recursive/higher-order LocTy families, HandlerLawN, or arbitrary nested borrow-view reconstruction.
- `phi` is empty; `wc` preserves the scope-record list, and both entries are `remask=false`. Registry changes are permitted; arbitrary KW/LocTy, scope-list, mask, floor, or FoldInv transport is not proved here.
- A second park stop is modeled explicitly; a general scheduler, cancellation/quiescence, shared loans, multi-shot continuations, and adequacy for a combined new typed interpretation remain outside this spike.
- Existing erwpX and its no-loan results were left unchanged. This is not a new conservativity theorem connecting the branded protocol to ordinary main U.

The bounded result is that owned claim creation, generic splitting/transfer, real capture, heap storage, an additional stop, resource-derived registry/family agreement, matching return, and ownership-recovering discharge compose in ONE checked masked-protocol proof. The next integration question is how that branded protocol should be represented by the source computation/value types, not whether the raw X operational pieces can compose.

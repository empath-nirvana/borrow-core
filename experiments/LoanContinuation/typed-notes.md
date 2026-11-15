# Typed loan continuation interface spike

Status: checked partial result. The world/type half is proved; it is not a combined typed execution theorem for a captured/stored/resumed continuation. Production repositories are unchanged.

## Sources and reproduction

Read CLAUDE.md before the experiment. No library/spec files were changed. Scratch semantic entry is in TypedLoanOrderProbe.lean:4.

Main source snapshot: /Users/johnthompson/repos/borrow-core, c1d16d42fa43fd919c97d343750f4e94bcf7b618.
Warm build used: /private/tmp/borrow-core-remove-chain-fragments, 1fa13095c93597f30149c6693c1d14a5120378f6.
Imports: Core.Chain.Goal791N and Core.Chain.LendExit835N.
The imported interface source files have identical git blob hashes in those two checkouts:

- Goal791N.lean: 1fd45df8435abac2dfa347232f124856b6569fc0
- LendExit835N.lean: e08e16c3b6520a00efcddf24e59ea611c149cbd9
- SI/ErwpK.lean: d9b0eb285998436c450d012a4e1e13ad7bdcff67
- SI/LocTy.lean: aea5c658df796fc2a10abc1070b3bedeb2cd4079

Command (no rebuild):

```sh
cd /private/tmp/borrow-core-remove-chain-fragments
lake env lean /private/tmp/typed-loan-spike/TypedLoanOrderProbe.lean > /private/tmp/typed-loan-spike/check.log 2>&1
```

Final exit code: 0. Each exported experimental result's printed axioms is a subset of `[propext, Classical.choice, Quot.sound]`. No new axioms, admitted proofs, unsafe code, or native_decide. Check log is adjacent to this note.

Earlier operational baseline, checked separately against cross821 bbf8f16af3c27646c85384d1dba3f5e9f1050ce3: /private/tmp/LoanBridgeProbe.lean. It proves owned start -> exact mut PA -> exact mut PB -> owned return using existing X loan rules. The parent agent has completed /private/tmp/StoredLoanCross821.lean:219, storedProgram_erwpX: a real linear handler heap-stores/retrieves its genuinely captured kappaC, allocates/frees an unrelated cell while it is stored, resumes with the exact borrowed cell, and returns ownership. I inspected the handler theorem and the storedClause_compat use of KapRelX. Its checked operational result still does not establish the typed world move or claim ownership connection. This typed file does not import cross821's X relation; those old modules have no LocTy/Goal791N.

## Explicit proposed semantic changes

A retained claim list D contains each loan's location and ACTUAL cell lifetime (which may differ from a type's slack lifetime). For each (l,beta), `Protect D Theta Theta'` requires both:

1. the precise stored family at key (l,beta) is unchanged;
2. `Theta'.above beta = Theta.above beta`, including the higher immutable records.

`Future D Theta Theta' rho` combines ordinary ExtR at the continuation's PHYSICAL share rho with that protection. The borrow may live outside rho while parked; that is the reason protection is additional.

`UClaims R D Theta ...` replaces U's future quantifier by Future D. It is factored over an arbitrary computation interpretation R. It does NOT silently keep current cN for active loans: that execution layer still requires a world-indexed, masked X-based relation. No HandlerLawN was strengthened or assumed.

D is presently a LOGICAL PARAMETER, not an owned ghost resource. This file proves no allocation, composition, splitting, transfer, heap-storage, or discharge law for claims. A production interpretation must carry D with the continuation's semantic resource; the external logical parameter alone is not an implementation of that requirement.

## What Lean checked

- Protect/Future are reflexive and transitive.
- UClaims is stable along Future, for arbitrary R, without assuming the desired computation transport.
- `no_loan_U`: at D=[], instantiated R=cN, UClaims is exactly current vN(thunk C). This is a CLAUSE specialization, not conservativity of a combined execution relation.
- `mutL_transport`: exact key plus above-world protection preserves the same mutable cell/family for ANY CPredL P. It does not rely on unit/True payloads; P may depend on the world and contain higher-order types. Equality of the whole above slice proves equality of famL.
- `typed_payload_transport`: produces actual current vN(Mut 'x A) after the protected world move for arbitrary A, using the exact-lifetime mutL witness and the uniform-stratum premise already required by current Mut. It does not assume a new transport theorem.
- `unrelated_lend`: any fresh unrelated lend below the claimed lifetime is permitted.
- `concrete_allowed_change`: Theta has (location 0, lifetime 1), Theta' adds (location 1, lifetime 2). In this development Life is order-dual Nat, so lifetime 2 is shorter than 1. Both worlds are OK, Theta' differs from Theta, and Future [(0,1)] holds at the actual capture-cell ownership share. Thus the guard is inhabited and admits a genuinely changed world.
- `typedBorrow_at_source` and `typedBorrow_survives_allowed_change`: the same concrete shallow borrowed resource is a real Mut 'x unit answer in both worlds, at every index.
- `typedBorrow_not_at_dropped_world`: that borrowed resource is not a Mut value in the empty world.
- `dropping_loan_allowed_by_current_U`: ordinary ExtR at an own capture cell permits forgetting the protected key and reaching the valid empty world, whereas Future with the retained claim rejects it.
- `current_U_captured_demands_drop`: instantiates the actual current vN U clause with the existing kappaC false r H K value. Any proof of that current U judgment must provide cN at the key-dropping world, for every view/list. Own-cell consistency is discharged; it is not an impossible guard. This is an exact demand of U, NOT a proof that kappaC lacks vN: a safe continuation may work there, and its answer type may be empty.

## First new integration obligation and remaining theorem

The first new boundary exposed is that ordinary U follows ExtR at the stored continuation's physical share, which contains no borrow cell and consequently protects no outstanding loan key. A claim-aware continuation proof only supplies Future-protected worlds. It cannot discharge unchanged U by merely erasing the claim.

The next combined theorem must give, for the REAL captured kappaC value and owned capture cell plus loan authority/claim:

- a loan-aware thunk judgment quantified over all Future-protected, OK resumption worlds and consistent views;
- for every smaller index and every permitted resumption list, an inhabited answer predicate PB identifying the SAME outstanding loan, not merely some value of Mut beta A;
- from PB's returned exact borrowed cell composed with the continuation's capture cell/authority/claim, execution of `kappaC false r H K (inl ()) w` in a MASKED, typed X relation;
- capture-cell release, handler continuation execution, and loan-end discharge that return ownership and consume the matching retained obligation;
- a storage/retrieval rule carrying that same obligation through a reference value;
- a no-loan specialization connecting the combined computation/value interpretation to current cN/vN where its masks and ghosts are empty.

This theorem is NOT proved in this artifact. In particular, no world-index-only modification can fix current rwpG/UpdVN's unmasked owned-to-borrow boundary. Cross821's changed masked execution layer remains essential.

Additional unfinished obligations:

- Current KW.Owed also includes floor monotonicity and preservation of FoldInv g at every g above the chosen floor. Future here contains no floor coordinate and no FoldInv preservation. This file does not establish their recovery or show that the combined design can dispense with them.
- Typed PB must preserve loan identity and admissible returned content; vN Mut alone does not identify which outstanding loan is being returned.
- Arbitrary CPredL transport is checked, but integrating the NEW UClaims meaning inside recursive vNX payload families requires redoing the interpretation closure/fixed-point/fundamental obligations. Existing vN payloads are the ones used here.
- Operational progress of unrelated code is supplied by the separate X witness; the world-lend move here is a checked semantic move, not itself a full execution trace.

Conclusion: a concrete permitted changing world, a nonempty typed returned borrow, general stored-family transport, and exact no-loan U-clause recovery are checked. The resource ownership/typed execution connection for a stored continuation remains the missing theorem; this experiment does not establish full typed continuation composition or a structural impossibility of such a design.

## Adversarial same-lifetime answer test

`same_lifetime_wrong_answer` is a negative test of the candidate's sufficiency if PB stays ordinary vN(Mut beta unit):

- Protected loan is location 0, lifetime 1; continuation capture cell is owned at location 2.
- Theta' adds a DIFFERENT key (location 1, lifetime 1), at the SAME lifetime as the outstanding loan.
- Future [(0,1)] holds; the key at (0,1) and the world above 1 are unchanged. Both worlds are OK.
- Ordinary current vN(Mut 'x unit), with x interpreted as lifetime 1, admits the answer at location 1 and its single mutable cell.
- This answer resource has no cell at location 0.
- It actually composes with the owned capture cell at location 2, so the continuation wand's resource-composition premise does not exclude it.

This is NOT a claim that a typed source program can manufacture this same-lifetime world/answer. It is a test of the semantic universal answer quantifier. It proves that protecting the outstanding key and above slice alone does not identify the returned loan. PB needs a separate identity/authority return obligation, such as the exact-location/resource matching used by the operational X probe. Strengthening Future to freeze more world entries would be a different restriction and still would not by itself establish the general PB identity law.

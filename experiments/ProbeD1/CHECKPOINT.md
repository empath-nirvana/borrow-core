# ProbeD1: checkpoint

This is a plain-language summary of where the D1 tractability probe stands. The full outcome is in
`README.md` and `DESIGN.md` §15. The Lean is in `ProbeD1/`, and `lake build ProbeD1` builds it.

> [!WARNING]
> **The verifiers' findings are not resolved yet. Do not rely on the outcomes below until they are.**
> The hygiene review passed. The content review did **not** pass, and it raised these findings:
>
> - **Major: the binder0 `U` results may be vacuous.** `thunkFRow_binder0_of`,
>   `thunkVRow_binder0_of`, `bangThunkFRow_binder0_of` and `bangThunkVRow_binder0_of` take
>   `CtxRelendable .binder0` (`Thunk.lean`) as one global hypothesis over every context with the
>   table. Each proof only uses it at the row's own context.
>   - Nothing shows the hypothesis is satisfiable, which breaks CLAUDE.md §4 (prove an added
>     hypothesis non-vacuous and pin its scope).
>   - The README itself describes a case that may break it: a live `Mut` leaf whose cell sits at a
>     stack place, at the innermost lend's lifetime, with a payload other than that entry's view.
>     `TabAtS` allows that cell, but `RelendableS` has nowhere to put it.
>   - If the hypothesis is false, all four results say nothing.
>   - Nobody has built that configuration in Lean, and nobody has checked that the hypothesis is
>     false.
>   - The fix is a per-row hypothesis at the row's own context, shown non-vacuous (for example at
>     `Γ = []`, and at a `U`-slot context through `thawRelend`), or a Lean result that settles
>     `CtxRelendable .binder0` either way.
> - **Minor findings about wording.** These do not change the Lean, but they do change what the
>   prose claims:
>   - The README says `SemS` "does not give" the context's thaw. No Lean backs that, so it should
>     read "not derived, no obstruction verified". (The claim about Δ's models at a re-lend *is*
>     backed in Lean, by `models_reLend_fails`.)
>   - "Only with" (DESIGN §2.2) and "exactly" (DESIGN §15.3, commit 5751956) claim the conditions
>     are necessary. The Lean shows only that they are sufficient.
>   - At `cbpv`, the callback at `σ·y` is proved only when its bound does not mention the binder. One
>     README sentence states it without that condition.
>   - "One reason at every placement" claims too much. At binder0, statement 0 already stops earlier,
>     at monotonicity. At `cbpv` and `binder`, the `U` introductions have further needs that only
>     those placements have. The only needs every placement shares are the context's thaw and Δ's
>     models at a re-lend.
>   - Several prose explanations of why a route stopped are written as facts, with no Lean behind
>     them (DESIGN §15.2, §15.3, and the README's note on `MonoG`). They should be marked
>     unchecked.
>   - DESIGN §13 names `MonoHide binder0` and `MonoC binder0` as the facts that would tell the
>     placements apart, but the report gives `MonoHide binder0` no status. "`MonoOwnG`'s hypothesis
>     holds at every use" looks ahead, because `MonoOwnG` has no uses yet.
>   - "Statement 0 did not hold" should read "`Statement0 p` was not proved at any placement".
>     Nothing was refuted.
>   - The README sentence "it added no way to reach a stack" contradicts itself. The meaning is
>     that the change adds no way to reach a stack besides `FutQ` and `OwnPush`.
> - **Minor, scope only.** Commit 14b8592 copies three GhostEnd files onto `targets` unchanged (the
>   diff against 5cfe062 is empty). DESIGN §2.6 allows this. Nothing in `Core/` changed.

## The question

D1 is the design built on rows and ghost end. At a stop, the lend is re-lent at a fresh lifetime
each time the computation resumes. The question is whether the fundamental lemma can be proved at
D1's world W under four conditions:
- it covers exactly the rules that the two test programs (`genSelf` and `reconB′`) use;
- it uses one world, with the arising guard read from `TW`;
- the quantifier over future worlds appears once;
- there is no second relation family beside W.

Statement 0 comes first. It defines W's clauses at `U` (thunks), `⊸` (functions) and `∀` together.
It tries the future-world quantifier at three places:
- `cbpv`: at `U` and the stop's share (OQ-8 option 2);
- `binder`: at `U`, the share, `⊸` and `∀` (option 3);
- `binder0`: at `∀` only, as in GhostEnd.

Its outcome was meant to settle OQ-8 (where the quantifier goes). With that, it would settle whether
D1 meets "two algebras that interact only at cuts".

## Statement 0: what happened

**`Statement0 p` was not proved at any of the three placements. Nothing was refuted.**

- **Proved at every placement:** the shared lemmas (`statement0Shared`), `ForceRow`, `ThawRelend`,
  `MonoHideFromMonoV`.
- **Proved at `cbpv` and `binder`:**
  - monotonicity along W's order (`MonoV`, `MonoG`, `MonoHide`);
  - carrying a context across the callback's own lend (`MonoOwnG`).

  `MonoOwnG` needed one change that the design had planned for (§13 step 2): `FutStep` now accepts
  any variable new to the stack. The design named the cost of this change in advance.
- **Callback at `σ·y`:** proved at `binder` and `binder0`. At `cbpv`, proved only when the bound
  does not mention the binder.
- **Not derived at `binder0`:** monotonicity (`MonoOwnG`, `MonoV`, `MonoG`). The design expected
  this placement to stop here.
- **Not derived anywhere:** the four `U` introductions (`ThunkFRow`, `ThunkVRow`, `BangThunkFRow`,
  `BangThunkVRow`). Two needs are common to every placement:
  - **the context's thaw** (`CtxRelendable`): not derived, and no obstruction verified;
  - **Δ's models at a re-lend.** Lean shows a configuration that `SemS` admits where a re-lend does
    not keep them (`models_reLend_fails`). That configuration is not shown to arise in `TW`.

  `cbpv` and `binder` have further needs of their own. One is the context carried to a future that
  inserts between lenders. The other is the names `StackJ` admits after the `FutStep` change.
- **At `binder0`**, the four `U` rows are proved *given* `CtxRelendable .binder0`, and statement 1's
  `TabRelend` was proved on the way. **See the warning: that hypothesis may be unsatisfiable.**

**What it decides:**
- **OQ-8: not decided.** No placement got through statement 0, and none was refuted. The design's
  rule draws no conclusion from "not derived".
- **"Interactions only at cuts": not decided.** D1's rank against D2a and D3 is where it was before
  the probe.
- **No failure of type (b) or (d) occurred.** No second guard, no second relation family, and no
  second quantifier.

## Statements 1–4

Not attempted. The design's stop rule halts the probe after statement 0 when `Statement0 p` is
proved at no placement. The one exception is statement 1's `TabRelend`, proved on the way at
binder0. Statements 5–7 and OQ-58's facts were not attempted either, and `reconB′` was not built.

## What this says about D1's tractability

The probe leaves it open. Most of the value-side cost of the quantifier is proved at `cbpv` and
`binder`: monotonicity at `U`, the own lend, the thaw and `[force]`. The open part is the `U`
introductions, and what they need is now listed. One of those needs, Δ's models at a re-lend, fails
at a configuration `SemS` admits. So that step cannot apply the premise at every re-lend while
`SemS` stands as it is. It needs another route, a change to `SemS`, or a change to what a re-lend
re-lends. Nothing here is evidence that D1 cannot be made to work, and nothing is evidence that it
can.

## What to do next (options, not a decision)

1. **Fix the review findings first.** This is needed under every option. Scope `CtxRelendable` to
   each row and show it non-vacuous, or settle it in Lean. Then correct the wording the review
   lists.
2. **Continue D1.** Settle the `U` introductions' needs:
   - Δ's models at a re-lend: rule out a variable that is off the stack but bounded by a stack
     variable, or re-lend it with the stack;
   - the context's thaw under the table, by type or from arising;
   - the names the changed `FutStep` gives, through a `StackJ` with a hygiene the rows can discharge,
     or through the renaming lemma.

   Then re-attempt statement 0, and statement 1 after it. This is what the README proposes. It is
   cheapest if the models issue turns out to be a mistake in our `SemS`, not something the design
   requires.
3. **Fall back to D3.** The closure keeps its lifetime across the stop, so there is no re-lend. The
   models-at-a-re-lend need does not come up. The cost is D3's stop change (D3.k1–k7) and scoped
   rows (D3.k12). The probe has not triggered the fallback: no machine-checked failure of type (a),
   (b) or (d) occurred. Choosing D3 now would be a judgement about cost, not something the probe
   forces.
4. **Fall back to D0.** This is the option if D3's stop change also fails. D1's A-side work carries
   over to it unchanged.

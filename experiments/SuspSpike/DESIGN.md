# SuspSpike: lends held across a suspension, for restricted classes (#645)

Question (per class): does T1, refined to admit the class, keep `fundamentalC`, adequacy and
every borrow guarantee, with Core's relation unchanged where no stop crosses a lend?

New machinery sits only at the cut, over Core's relation (`wpG`, `ewpTS`, BoLo's world). ProbeD1's
draft world is not used. GhostEnd (`experiments/GhostEnd`) is read for hints; it does not build
on main today (`GhostEnd/Program.lean:210`), so nothing here imports it.

## 0. Where the obstruction sits

`wpG` (`Core/EffDefs.lean`) is a bracket: from a run's start to its end, at a value or at a stop,
the world update is `↭` (`ResU.UpdV ρ π`) and the records proper are unchanged
(`∀ p, p ∈ ps' ↔ p ∈ ps`). A lend open at a stop is a new `mut` cell and a new record, so a stop
cannot leave a lend open. Every class therefore ends the lend at the stop (6.65's exit reads no
term, `wpG_M_frameX`) and lends the place again at the resumption. The question is at which
lifetime.

- **Fresh lifetime** (GhostEnd's `Relend`). The frozen continuation's values mention the old
  lifetime and must hold at the new one: the borrower side `RBodyOfTyped`, not derived.
- **The same lifetime** (this spike). The lender lends again at the lifetime `α` it chose at the
  first entry, and with the cell the exit handed back, so the continuation gets back exactly the
  resource it stopped with. No value is moved, so no thaw is needed. Two things must hold at the
  resumption:
  1. the cell built again is the cell the stop held: same location, lifetime, value, payload,
     and stored predicate. The stored predicate is `𝒱⟦T⟧δ` read at the frame's list; it is the
     same when the resumer's list has the stop's members (`vC_local` both ways);
  2. the continuation's share less the view lies in `Res_α` (6.27 at the next exit needs it).

  Item 1 is where the classes differ. A resumption at a list with the stop's members gives it.
  A resumption at an arbitrary `Ext`-extension does not: `Ext` pins only the records longer-lived
  than the share's borrow cells, and once the view is ended the share holds no cell at `α`.

## 1. Definitions (Lean: `SuspSpike/Defs.lean`)

- `SameMem ls ls'`: the two lists have the same members.
- **The grade** `C : UInt32 → UInt32 → Bool`, a property of operations: `C n i` marks the
  operation `i` of `n` as *call-like*.
- `contShareC en ls K Φ`: the continuation's share at a call-like stop: resumed at every list
  with the stop's members, at every answer; linear (no cancel).
- `performStopC T C`, `opTableC T C`: `opTable T` with `contShareC` at the call-like operations and
  `contShare` elsewhere.
- **Class 1** (`CallRow T C`): every operation of the row is non-abortive, linear and call-like,
  and its answers lie in every stratum (closed data, `Row.ResumeO`'s answer condition).
- **Tail closure** (`TailClosed`): a handler of a call-like operation is `effHandleT`'s shape
  (clause `λ(x, κ). (λw. κ.1 w) (g x)`), and `g`'s row is call-like too. This is what makes the
  resumption land at a list with the stop's members, uniformly in the nesting depth.

## 2. Theorems, in order

1. **Conservativity** (`Conservative.lean`):
   - `opTableC_none`: at the empty grade `opTableC T C = opTable T`, so `ewpTS` and every relation
     clause read through it are Core's, definitionally;
   - `opTableC_of_opTable`, `ewp_grade`: grading only weakens a protocol, so every computation in
     Core's relation is in the graded one (no Core result is lost at a graded row);
   - `contShareC_of_contShare`.
2. **The resumption lands in scope** (`Scope.lean`): at a table that owes continuations only at
   lists with the stop's members, every value a run answers is at a list with the start's members
   (`ewp_sameMem`).
3. **6.65 at a given lifetime, exactly** (`FrameAt.lean`): `wpG_M_frameAt`, the printed proof of
   `wpG_M_frameX` with H4's lifetime given instead of chosen, the callback given the cell the
   entry builds, and the exit reporting the cell's content. It is a restatement of the printed
   steps (6.27, 6.28, 6.24, 6.25, `TW.mutFold`/`mutUnfold`), not a new argument.
4. **Class 1's frame** (`Frame.lean`): `ewpTS_M_frameC`, 6.65 over `ewpTS` at a class-1 table:
   the stop ends the lend, the continuation's share keeps the owner, and the resumption lends again
   at the same lifetime with the same cell. Induction on the callback's `ewpTS`, as
   `ewpTS_M_frameR` is on `Relend`.
5. **Class 1's handler** (`Handler.lean`): a tail handler at the graded table resumes at the
   stop's members.
6. **Depth ≥ 3** (`Depth.lean`): the class hypothesis at a row of three call-like operations of
   three names, each clause's row the next one's; three nested lends.
7. **Classes 2 and 3** (`Stored.lean`): what the same-lifetime route needs at a resumption at an
   `Ext`-extension, as a `Prop`; and the open-cell route's statement against `wpG`'s bracket.

## 3. Kill criteria, how each is checked

- An indexed borrow frame: none of the definitions carries an index.
- An invariant beyond `↭`: the same-lifetime route uses `↭`, 6.27, 6.28 and `TW` as Core has them.
  The open-cell route (keep the lend open at a stop) needs `wpG`'s bracket changed; if a class can
  only be had that way, this criterion fires for it.
- A proof special-cased per depth or per effect: the frame lemma is one induction on `ewpTS`, at
  any table of the class; the handler lemma one induction on the handled computation.
- Two successive patches: recorded in §5 below as they happen.
- Algebra: deep handlers, cancel as built, finalisers as built; multi-shot ignored. Class 1 has
  linear continuations only; class 3's cancel is Core's.

## 4. Proof plan of item 4

`FrameAt α`: for every list `ls` with the members of the first entry's list, every owner
`ℓ ↦ own(v) ● ρ_P` with `ρ_P ⊨ 𝒱⟦T⟧(v)` and `ρ_P ∈ Res_α`, every `ρ_b ∈ Res_α`, from
`ewpTS ls e Tb_α Q_α (ρ_b ● ℓ ↦ mut(α, v, ρ_P, P̂))` conclude
`ewpTS ls e Tb Q (ρ_b ● ℓ ↦ own(v) ● ρ_P)`. Here `Tb_α` is the class table with each stop's share,
less the cell at `ℓ`, in `Res_α` (`StopView`, the §28 stop lemma with the view set aside).

Induction on the callback's `ewpTS`, its predicate the conjunction of the callback's `ewpTS` and
the goal, so that a stop whose share no longer holds the view (mode B: the borrower dropped it)
continues with the owner held beside the callback:

- a value: `Q_α`'s box puts the cell in the leftover; 6.65's exit as printed;
- a stop with the view in the share: the exit moves it to the leftover, hands back
  `ℓ ↦ own(v″) ● χ`, and the frame's stop owes, at each list with the stop's members and each
  answer, the owner and the continuation. `FrameAt α` again, at the same `α`, with the cell
  `ℓ ↦ mut(α, v″, χ, P̂)`: the one the stop held;
- a stop without the view: mode B, the owner carried through the callback's stops and given to
  its return.

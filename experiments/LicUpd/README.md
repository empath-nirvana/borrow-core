# LicUpd: `↭` with derivable `imm` views exempted (G1, #1007)

**Question.** #999's getter `fn get<'a>(j: &'a Json, k) -> Option<&'a Json>` returns an image
of the lent cell's escrow at `'a`. That image outlives the getter's own run. Today's `↭`
refuses this. #1007's G1 relaxes `↭`'s `imm` clause in the end→start direction, for views
*derivable* from the start's `imm` views (projection closure). The experiment asks:
- Does G1 accept the getter?
- Does it compose?
- Does one absorption per lifetime end recover 6.59?
- Do K4–K6 and the `Mut` getter (G1ᵐ) behave as predicted?

Build: `lake build LicUpd`. Nothing in the library imports it.

## Definitions (`LicUpd/Lic.lean`)

- `Derivable σ l ψ`: the least relation that contains the `imm` cells of `σ` and is closed under
  one projection step. The step goes from a derivable `imm(s, u, χ)` to `imm(t, v, w)` at `l`,
  when:
  - `χ(l) = own(v)`;
  - every lifetime of `t` is `⊑` some lifetime of `s`;
  - `w ≤ χ`.
- `UpdImmLic ρ₁ ρ₂`: the start's `imm` cells are in the end, as in `UpdImm`. The end's `imm`
  cells are in the start, or are derivable from the start's flattening.
- `UpdLic` is `UpdImmLic` plus `↭`'s `mut` clause, unchanged. `UpdVLic` adds `✓ρ₁ ∧ ✓ρ₂`.

## Results

| Item | Lean | Status |
|---|---|---|
| conservativity: `↭ ⊆ UpdLic` | `UpdVLic.of_updV`, `six59Lic_of_updV` | proved |
| transitivity, at every three worlds (K2 included) | `UpdImmLic.trans`, `UpdVLic.trans`, `Derivable.trans` | proved. Derivability is a closure, so no lemma per depth |
| K1 refused by today's `↭` | `k1_refused`, `k1_refused_updV` | proved, with both flattenings computed |
| K1 accepted by G1 | `k1_accepted` | proved, with both sides valid |
| frame at a one-cell frame (a copy of the lent cell) | `k1_frame_copy` | proved |
| K2: second-level image derivable through the first | `k2_derivable`, `k2_compose` | proved |
| one absorption at a lifetime's end recovers 6.59 | `lendEnd_absorb` | proved: 6.52, then 6.59, at `β := α`, the lend's own lifetime, with the 6.64 frame's `houtb`/`houtρ′` as 6.52's stratum conditions. It assumes `hbridge` |
| the bridge: a G1 callback run, with its images moved to its start, meets `↭` | `LicBridge` (`lendEnd_absorb_lic`) | **refuted as stated** (`not_licBridge`). At K1 with `c = ∅`, the statement lets `c` miss the new image. The corrected form `LicBridgeAll` (garbage minus `c|dom(ρ_P|mut,own)` in `Res_α`) is **open** |
| 6.59 under G1: a bracketed reborrow at `β ⊏ α` while a persistent image at `α` appears | `Six59Lic` | **open**, stated. This is the riskiest step: the walk equality modulo derivable images |
| 6.48 under G1 in general | `LicFrame` | **refuted** (`not_licFrame`, `licFrame_fails`). The frame `F = 1 ↦ imm({β}, t, ∅)` is a second image of K1's escrow cell. `⦇F ● ρ⦈(1) = imm({β}, t, ∅)` and `⦇F ● π⦈(1) = imm({β} ∪ {α}, t, ∅)`, so G1's start→end clause, which keeps `UpdImm`'s exact cell, fails for the composite while K1 is accepted |
| K4: G1 does not exempt a `mut` predicate change; a `mut` exemption (G2 as written) does | `k4_refused`, `k4_mutExempt_admits` | proved |
| K5: `own ● imm` at one location is undefined | `k5_own_image_undefined` | proved |
| K6: G2 read off the run's start does not compose (G2 conjures, then G1 derives) | `not_g2ThenG1Compose`, `not_g2Compose` | proved |
| G1ᵐ: `Mut` getter | `g1m_coexist_invalid`, `g1m_parent_kept`, with `k4_refused` | **fails**: see below |

### G1ᵐ: the `Mut` getter fails, so the work stops here

The start is the parent `0 ↦ mut(b, v, ρw, P̂)` with `ρw(1) = own(u)`. A `Mut 'a` getter would
end holding a top-level `1 ↦ mut(…)`.
- No valid resource holds that view beside a parent whose witness still owns `1`
  (`g1m_coexist_invalid`).
- G1 keeps `↭`'s `mut` clause, so the parent survives with its `P̂` (`g1m_parent_kept`), and
  `P̂` cannot change (`k4_refused`).
- So `P̂` would have to hold at a witness without the field. A typed `P̂` does not.

A `mut` view is exclusive: a getter must move the parent's authority over `1` to the view, not
derive a copy beside it. No end→start exemption expresses that move. Per the brief, no fallback
is attempted.

## Verdict on G1 as defined

G1 as defined is **not frame-preserving** (`not_licFrame`).
- The defect is the start→end direction. A start view whose lifetime set grows, because a
  derivable image joins it (`imm ● imm` unions the sets), is no longer the same cell.
- A repaired G1 would read that direction up to growth by derivable images' lifetimes. That
  repair is not built, and 6.48 at it is not derived.
- Transitivity, K1, K2 and the end-of-lend absorption (given the bridge) are proved.
- `Six59Lic` and `LicBridgeAll` stay open.

## What the open items are

- **`LicBridge`.** `lendEnd_absorb` needs the callback's run re-read as `c ● ρ_b ↭ ρ′ ● ρ⁺°`.
  Here `c ∈ reb_α(ρ_P)` is the outstanding images, and the frame cell `ρᵢ` is removed from both
  ends. Under G1 the run is only `ρᵢ ● ρ_b ↭_Lic ρ′ ● ρ⁺° ● ρᵢ`. Moving derivable images to the
  start, and cancelling `ρᵢ` from both sides, is the step not derived.
- **`Six59Lic`.** 6.59's closing sentence shows two aliasable walks equal, running `↭` in both
  directions (`updImm_symm`). Under G1 the end's walk may hold extra images. The equality is
  then modulo derivable images, and the existing proof does not cover that.
- **`LicFrame`.** 6.48 at `UpdVLic`.

Not derived; obstructions not verified.

## The growth clause (`Growth.lean`, `MutMask.lean`)

This follows theory's `imm-getter-growth.md`. Derivability is read per lifetime (`DerLt`). In
`UpdImmG`, start `imm` cells persist with their lifetime sets only growing, and every end
lifetime is a start lifetime at the same (location, value, witness), or is derivable.

| Item | Lean | Status |
|---|---|---|
| bridge from G1, conservativity | `Derivable.derLt`, `UpdVG.of_lic`, `UpdVG.of_updV` | written |
| transitivity | `UpdImmG.trans`, `UpdVG.trans` | written |
| (C2), (M) | `compR_get_grow_left`, `compR_get_imm_source`, `compR_get_imm_cover`, `DerLt.mono` | written |
| 6.48's `imm` half under growth | `updImmG_frame` | written |
| `licFrame_fails`'s configuration accepted | `k7_accepted` | written |
| **K8: 6.48's `mut` half fails under growth** | `updMutFrameG_fails`, `not_updMutFrameG` | written. A frame's frozen `mut` cell is masked by the new image (`mut ○ imm = imm`). Typed worlds exclude this (`NoMut`), so the repair is a premise on 6.48. **Stop point**, reported |
| the 6.59 family restated | — | not started (stopped at K8) |

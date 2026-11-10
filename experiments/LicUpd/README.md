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
| the bridge: a G1 callback run, with its images moved to its start, meets `↭` | `LicBridge` (`lendEnd_absorb_lic`) | **open**, stated |
| 6.59 under G1: a bracketed reborrow at `β ⊏ α` while a persistent image at `α` appears | `Six59Lic` | **open**, stated. This is the riskiest step: the walk equality modulo derivable images |
| 6.48 under G1 in general | `LicFrame` | **open**, stated |
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

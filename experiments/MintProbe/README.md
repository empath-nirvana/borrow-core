# MintProbe: eager same-lifetime views ("mint at the freeze", #219), stage P1

**Question.** Can borrow-core's model carry RustBelt-style sharing, with views minted at
the frame, including through a frozen `Mut`? This is option (c) of
`scratch-archive/theory/derived-views.md` and the P1 stage of `kernel/999/probe-plan.md`.

Build: `lake build MintProbe`. Nothing in the library imports it. Stage P1 works at the
paper level: `Paper/`'s `wp`, `↭` and `Ty`/`vDen`. The typed world and Core come in P2.

## What it contains

- **`Mint.lean`**, ported from bolo-formalization PR #2 (`Extensions/Views/Mint.lean`) and
  generalised.
  - `Mint α O Y` lets a view sit on any **base cell** (`Base`): `own(u)`, as in PR #2, or a
    `mut(b, u, w, P̂)` cell over the view's value and witness. The second case is the target of
    a frozen `Mut`.
  - The five facts are re-proved at the widened `Mint`: `Mint.flat`, `.hash` (6.34),
    `.lower_iff` (6.26/6.8), `.upd` (6.39), `.top` (6.29), `.post_hash` (6.38).
  - `Mint.addBase` adds one view over either base. `Mint.add`/`add_le` are the `own` case,
    and `Mint.addMut` is the `mut` case.
  - `frozen_under_imm` is the deciding check.
- **`Frame.lean`:** `wp_mint_frame`, 6.64 at a mint. `wp` and `↭` are unchanged.
- **`Shared.lean`:**
  - `shrV` at `1`/`⊗`/`⊕`/`Ref`/`[@a]`, plus **`Mut`**: a view of the `mut` target at the
    outer `α`. `α ⊑ β` holds strictly, from the share being in `Res_α`.
  - `mint_views` by induction on the type, with the `Mut` case going through `Mint.addMut`;
    `mint_shr` and `wp_S_frame`.
  - `wp_load_S`, `deref_sem`, and **`deref_mut_sem`** (load through a frozen `Mut` at the
    outer lifetime).
  - `shrV_noOwn`, `shrV_mono`, `wp_S_forget`.
- **`Uses.lean`:** `shrV_copy`, `derefN_sem` (n derefs at one `α`), `minted_projection`.
- **`Pointee.lean`:** the first pass's refutations (no run creates the view).
- **`Ground.lean`:**
  - `g1_shape`: two `deref`s through an owned `Ref (Ref S)` at one `α`.
  - `g2_shape`, `g2_value`: `&&mut T → &T`, returning `()`.
  - `frozen_mut_under_imm`: the deciding check stated at a `mut` cell.

## Stop rule: no stop

- **The deciding check holds** (`frozen_under_imm`, `frozen_mut_under_imm`). A `mut` cell under
  an `imm` witness keeps its value, by `↭`'s `imm` clause.
- **Every mint fact holds** at both base cases.
- **`wp` and `↭` are unchanged.** No headline is involved.
- **No view owns anything** (`shrV_noOwn`).

## Not done in P1

- **The owned reach below a `Mut` target is not minted.**
  - `shrV`'s `Mut` clause is one level: the target's view, with its denotation as a fact.
  - Minting further needs `mint_views` over a witness that is not `≤ O` (the `mut` cell's
    witness). That requires generalising `Le P O` to a reach predicate, with the witness-walk
    factor (`mutWit_flatR_factor` is its first step).
  - No obstruction was found.
- **P2:** the typed world, deep `vC`, `wpTS_I_frameX` at a mint, and `load`'s compat lemma.

Axioms: `[propext, Classical.choice, Quot.sound]` for every result.

# MintProbe: eager same-lifetime views ("mint at the freeze", #219), stages P1 and P2a

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
    outer `α`, with the target's own views (`Mut β S` at `α` is read as `Ref S`,
    `shrV_mut_eq`). `α ⊑ β` holds strictly, from the share being in `Res_α`.
  - **`Reach O P`** (stage P2a): where a mint over `O` may put views. Every cell of `ex(P)` is
    one of `ex(O)`, and `⦇P⦈_○` is a `○`-factor of `⦇O⦈`. `Reach.of_le` covers a `●`-factor,
    `Reach.le` is closure under `≤`, and `Reach.mutWit` passes to a `mut` cell's witness.
  - `mint_views` by induction on the type over `Reach`. The `Mut` case goes through
    `Mint.addMut`, then recurses into the target's witness. `mint_shr` and `wp_S_frame` use it.
  - `wp_load_S`, `deref_shr`, `deref_sem`, and **`deref_mut_sem`** (load through a frozen
    `Mut` at the outer lifetime, returning the target with its views).
  - `shrV_noOwn`, `shrV_mono`, `wp_S_forget`.
- **`Uses.lean`:** `shrV_copy`, `derefN_sem` (n derefs at one `α`), `minted_projection`.
- **`Pointee.lean`:** the first pass's refutations (no run creates the view).
- **`Ground.lean`:**
  - `g1_shape`: two `deref`s through an owned `Ref (Ref S)` at one `α`.
  - `g2_shape`, `g2_value`: `&&mut T → &T`, returning the target with its views (`()` at `1`).
  - `g2_deep`: through `Mut @a (Ref S)`, a further `deref` reads the cell the target owns, at
    the outer `α`.
  - `frozen_mut_under_imm`: the deciding check stated at a `mut` cell.

## Stop rule: no stop

- **The deciding check holds** (`frozen_under_imm`, `frozen_mut_under_imm`). A `mut` cell under
  an `imm` witness keeps its value, by `↭`'s `imm` clause.
- **Every mint fact holds** at both base cases.
- **`wp` and `↭` are unchanged.** No headline is involved.
- **No view owns anything** (`shrV_noOwn`).

## Not done

- **P2 proper:** the typed world, deep `vC`, `wpTS_I_frameX` at a mint, and `load`'s compat
  lemma.

Axioms: `[propext, Classical.choice, Quot.sound]` for every result.

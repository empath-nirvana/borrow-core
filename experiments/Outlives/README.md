# Outlives: which strict outlives premises admit `⊑` (#241)

Build: `lake build Outlives`. Programs: `./run.sh`. The findings, the inventory and the
recommendation are in `docs/outlives-strictness.md`; this README lists what is here.

The library imports `Core` and changes nothing in it. Every result's axioms are within
`[propext, Classical.choice, Quot.sound]`.

| file | content |
|---|---|
| `Outlives/Judgment.lean` | the outlives judgment with its box premise and its `Imm`/`Mut` premise as parameters (`VOutP`); `VOutL` (box rule `⊑`, K1), `VOutLe` (all three `⊑`), `CtxOutL`; 6.60 at each (`vC_outlivesL`, `vC_outlivesLe`) |
| `Outlives/Compat.lean` | `[]I` at `CtxOutL` (`boxIL_compatC`); `withbor` (Ref → Mut) at the non-strict side condition (`withbor2Le_compatX`, 6.173 with `MutFrame` applied at `↓@bδ`) |
| `Outlives/Derives.lean` | `LDerives`: `CDerives` with those two premises relaxed, plus `core`; `fundamentalL`, `adequacyL`, `runs_i32L` |
| `Outlives/Programs.lean` | `counterTop` and `nestTop`: Core's `counterProg` and `nestProg` with no scope, run by adequacy and by the interpreter (`4`, `8`, no cell left) |
| `Outlives/Obstructions.lean` | `borrow_cell`, `not_vC_outlives_le` (6.60 fails with the `Mut` rule `⊑`); `no_nonstrict_stratum` (a stratum holding its own `mut` cells contradicts Cantor's theorem) |
| `bc/` | lifetime bounds (B1): the instances the elaboration would make, checked and run by `bcc` of `main` |
| `sketches/k1/` | `aff-counter`, `aff-depth`, `aff-drop`, `aff-higher` under K1 alone; they check and print the corpus goldens with `k1.patch` applied, and `bcc` of `main` refuses each at the box rule |
| `sketches/all/` | the six `aff-*` programs and `lib/aff.bc` under K1, E1 and B1; unchecked |
| `k1.patch` | K1 as a library diff (`git apply` in a scratch worktree of `main`, then `lake build Core Frontend bcc`) |

# Experiments

Probes. Nothing in `Paper/`, `Support/` or `Examples/` imports anything here, and nothing here
is ever merged into them: an experiment that works becomes an entry in `SPEC.md`, and the entry
is then implemented in the library afresh. None of these libraries is a default target.

| Directory | Library | Build | Status |
|---|---|---|---|
| `CBPVSplit/` | `Experiments` | `lake build Experiments` | ported |
| `ModesLabels/` | `Experiments` | `lake build Experiments` | ported |
| `Shifts/` | `Experiments` | `lake build Experiments` | ported |
| `BorrowedClosures/` | `Experiments` (`Reborrow.lean`, `EnvCheck.lean`) | `lake build Experiments` | ported; the `fn` fork archived |
| `CBPVCore/` | `CBPVCore` | `lake build CBPVCore` | ported |
| `CBPVWorld/` | `CBPVWorld` | `lake build CBPVWorld` | ported |
| `Projection/` | `Projection` | `lake build Projection` | negative: `no_projection` refutes a same-lifetime `Imm` projection at the typed world (`FrameLife`) |
| `Relaxed/` | `Relaxed` | `lake build Relaxed` | FP and adequacy hold with `FrameLife.2` and `TW.reb`'s stratum non-strict; same-lifetime `Imm` projection still refuted, by `[TR]` 6.38 (`frame_view_excluded`) |
| `FrameEnd/` | `FrameEnd` | `lake build FrameEnd` | `Relaxed` with 6.64's exit (`TW.immEnd`) subtracting the frame-lifetime image as 6.52 does; FP and adequacy hold, and at 6.64's end the subtraction is empty (`frame_image_empty`). Same-lifetime `Imm` projection still refuted: `↭`'s `imm` clause at the projecting run (`imm_view_rejected`). The same holds for L3 via the `mut` clause (`mut_view_rejected`); L2: no |
| `Records/` | `Records` | `lake build Records` | records and variants as derived forms (`⊗`/`⊕`); `Imm̲`, outlives and 6.131 fieldwise; field read through `Imm` at the load's `'b`, field update by whole-record `withswap`; no model change |
| `Places/` | `Places` | `lake build Places` | a family of disjoint places (a tuple of `Ref`s) borrowed at one lifetime is **derivable**: nested `withbor` + `⊑Mut`/`⊑Imm` (`withborM2_wf`, `withborI2_wf`), when the second leaf and the result outlive the outer lifetime; FP and adequacy apply unchanged. Simultaneous `Mut` of `s.a`, `s.b`; sub-family and whole family passed at the same lifetime; `Imm` version; static `split_at_mut`. No model or typed-world change |
| `LeafPlaces/` | `LeafPlaces` | `lake build LeafPlaces` | unboxed structs: a struct is one block of leaf locations `b, b+1, …`, its handle the leaf family `addr b σ`. The resource model is generic in `Loc`, and nothing makes a location hold a whole record. Alloc, free and borrow of any plain shape are **derived** (`withborS_wf`, generic over nested shapes, `Mut`/`Imm`); FP and adequacy apply unchanged. New typed-world facts: block allocation (`wpTS_allocS`), borrowing returns the block's own handle (`withborS_ret`, `withborS_packed`). Checks: `&mut s.a`/`&mut s.b` together, `s.a.x` beside `s.b`, `Imm` whole struct and leaf. The machine lacks address arithmetic, so a one-word handle is a lowering; `pack` of arbitrary leaves breaks it (`crossPack`), a checker rule |
| `Recursion/` | `Recursion` | `lake build Recursion` | first probe of `docs/scope-recursion.md` §6, over `CBPVWorld` unchanged. P-μ: the boxed list `μX. 1 ⊕ Ref X` as an impredicative least fixed point over `vC`'s clauses; unroll, 6.60's shape, `Ext`-stability, a Z-combinator `freeAll : U(L ⊸ F 1)`, and a 3-cell list built and freed to empty memory (`build3Free_runs`). P-ν: `νX. F(A ⊗ U X) & F 1` as a direct greatest fixed point over `cC`'s clauses; `out`/`roll`, coiteration sound by the `∃S` candidate (`unfold_sem`), take-2-then-`close` runs to empty memory (`take2Close_runs`). P-Imm̲: the substituting clause's unrolling law for every `T` (`immReborrow_unroll`); the naive clause differs at the boxed list (`naive_ne`). No `μ`/`ν` in `VTy`/`CTy`; R4 untouched |
| `CBPVMu/` | `CBPVMu` | `lake build CBPVMu` | R4: `μ` (iso-recursive, de Bruijn) in a fork of CBPVWorld's `VTy`. Relation and shapes with a type-variable environment, `μ` as the impredicative least fixed point; unroll equations and induction principles at every type (`vC_mu_iff`, `vC_ind`); `Imm̲` at `μ` by payload substitution; 6.60, `Ext`-stability, 6.131 (`reborrow_vShape`), `relabel_obs` at `μ`. The choosers, world invariants, `Wp`, `FrameRules` and `Compatibility` (`withload_compatX`) build unchanged. FP and adequacy with `roll`/`unroll`. Programs: a list built and freed (Z-combinator `freeAll : U(L ⊸ F 1)`); a borrowed count of a list through nested `withload`s at fresh lifetimes, recursion on a fuel, runs to `3` with empty memory. Fuel-free borrowed fold: not derived. `X` under `U` and `Mut` in-place update: not done |
| `Bang/` | — | — | archived: became `Paper/`, `Support/`, `Examples/Closures.lean` |

Each experiment builds against this repository's `Paper`/`Support` (and `Examples`, for
`CBPVWorld`; `Records`, for `Places`; `Places`, for `LeafPlaces`; `CBPVWorld`, for `Recursion`). Module names are unique across the libraries: the
`Experiments` library's modules are `CBPVSplit.Split`, `ModesLabels.Modes`, `Shifts.Shifts`,
`BorrowedClosures.Reborrow` and `BorrowedClosures.EnvCheck`.

These experiments were developed in `~/repos/borrow_lang/Experiments/`; the last `borrow_lang`
commit containing them is `a31b498`. An archived experiment's README names the commits that hold
its code.

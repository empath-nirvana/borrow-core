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
| `Bang/` | — | — | archived: became `Paper/`, `Support/`, `Examples/Closures.lean` |

Each experiment builds against this repository's `Paper`/`Support` (and `Examples`, for
`CBPVWorld`). Module names are unique across the libraries: the `Experiments` library's modules
are `CBPVSplit.Split`, `ModesLabels.Modes`, `Shifts.Shifts`, `BorrowedClosures.Reborrow` and
`BorrowedClosures.EnvCheck`.

These experiments were developed in `~/repos/borrow_lang/Experiments/`; the last `borrow_lang`
commit containing them is `a31b498`. An archived experiment's README names the commits that hold
its code.

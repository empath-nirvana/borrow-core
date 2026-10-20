# Frames: frames with typed exits (#632, step 1)

Statements only, for the user to agree before anything is built. The design, the
requirement-2 check, the rewrites of the elaborator's rules and the decision menu are in
`docs/research/frames-with-exits.md`.

Build: `lake build Frames` (not a default target; the library never imports it).

| file | contents |
|---|---|
| `Frames/Defs.lean` | the slot tuple, the exit row, the frame type `frTy`, and the elaborated term of each rule |
| `Frames/Rules.lean` | `FDerives`, the 13 derived rules, with the elaborated term as index |
| `Frames/Theorems.lean` | O1 (`CDerives.shift_dead`), `FDerives.elab`, `frame_sound`, `frame_adequacy`, `core_conservative`, `Rets`/`Returns`, `accounting`, `block_returns`, `frame_handled`, `frame_unwind_leakfree` |
| `Frames/Examples.lean` | `swap_derives`/`not_returns_swap` (non-vacuity, proved), `nested_derives` (depth 4, proved), `nested_returns`, `nested_adequate` |

The `sorry`s: O1 (1), `elab` (13), `core_conservative` (1), `accounting` (13), `block_returns`
(1), `frame_handled` (1). Each carries a note on what it needs.

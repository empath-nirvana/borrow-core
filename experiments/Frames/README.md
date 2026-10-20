# Frames: frames with typed exits (#632)

Step 1 stated the design; step 2 proves it. The design, the requirement-2 check, the rewrites of
the elaborator's rules and the decision menu are in `docs/research/frames-with-exits.md`.

Build: `lake build Frames` (not a default target; the library never imports it). No `sorry`;
every result's axioms are within `[propext, Classical.choice, Quot.sound]`.

| file | contents |
|---|---|
| `Frames/Defs.lean` | the slot tuple, the exit row, the frame type `frTy`, the elaborated term of each rule, the drop glue of a skipped continuation (`dropCtxE`, `exitArmE`) |
| `Frames/Rules.lean` | `FDerives`, the 13 derived rules, with the elaborated term as index |
| `Frames/Elab.lean` | one lemma per rule: its elaboration is a `CDerives` derivation at the frame type |
| `Frames/Runs.lean` | the run invariant `RetsG` (up to a coinduction hypothesis) and its composition lemmas: plain contexts, `[then]` frames, the unwinding forms, administrative steps, `count_try`, `iterate` |
| `Frames/Accounting.lean` | one lemma per rule: its elaboration hands back the slots, at every closing substitution |
| `Frames/Theorems.lean` | `FDerives.elab`, `frame_sound`, `frame_adequacy`, `core_conservative`, `accounting`, `block_returns`, `frame_handled`, `frame_unwind_leakfree` |
| `Frames/Examples.lean` | `swap_derives`/`not_returns_swap` (non-vacuity), `nested_derives` (depth 4), `nested_returns`, `nested_adequate` |

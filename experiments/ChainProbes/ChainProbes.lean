import ChainProbes.ResumeWorldsG

/-!
# ChainProbes: probes of the chain world's resume worlds

Moved out of `Core/Chain/SI/`: no library module reads them. Each is a configuration or a
refutation at a resume world of the chain relation:

* `RebRechooseN`: re-choosing a reborrow's image at the resume; `not_rebRelabelAgreeN` and
  `not_immFrameWitSwapN` refute two ways of doing it.
* `CanonN`: the reborrow re-entry world of `not_rebReentryAgreeN` (`Core/Chain/SI/RebAgreeCex.lean`)
  at canonical images (`cex_canon`).
* `CanonAdv`: the handler-lend world (`resume_frame_short`) and the reborrow re-entry world at
  `TWNC`.
* `ResumeWorldsG`: both worlds at any list.

Build: `lake build ChainProbes`.
-/

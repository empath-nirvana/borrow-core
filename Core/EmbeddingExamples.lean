import Core.Embedding
import Paper.Examples.Programs
import Examples.Closures

/-!
# Core — BoLo's closed programs, run through the CBPV core  `[spec §3]`

Each closed program of `Paper/Examples/Programs.lean` and `Examples/Closures.lean`
(derivations `DerivesWf ∅ [] e 1`) runs from the empty memory to `()` by
`adequacy_of_derivesWf`: `embed` gives the CBPV derivation of the same term at `F 1`, and
`adequacyC` runs it.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Programs

theorem allocFree_runsC : BoCa.BoLo.Steps Adequacy.emptyMem allocFree Adequacy.emptyMem (.val .unit) :=
  adequacy_of_derivesWf d_allocFree

theorem fig2c_runsC : BoCa.BoLo.Steps Adequacy.emptyMem fig2c Adequacy.emptyMem (.val .unit) :=
  adequacy_of_derivesWf d_fig2c

theorem immBorrow_runsC :
    BoCa.BoLo.Steps Adequacy.emptyMem immBorrow Adequacy.emptyMem (.val .unit) :=
  adequacy_of_derivesWf d_immBorrow

theorem mutBorrow_runsC :
    BoCa.BoLo.Steps Adequacy.emptyMem mutBorrow Adequacy.emptyMem (.val .unit) :=
  adequacy_of_derivesWf d_mutBorrow

theorem loadClosure_runsC :
    BoCa.BoLo.Steps Adequacy.emptyMem loadClosure Adequacy.emptyMem (.val .unit) :=
  adequacy_of_derivesWf d_loadClosure

theorem aliasLoad_runsC :
    BoCa.BoLo.Steps Adequacy.emptyMem aliasLoad Adequacy.emptyMem (.val .unit) :=
  adequacy_of_derivesWf d_aliasLoad

theorem swapTwo_runsC : BoCa.BoLo.Steps Adequacy.emptyMem swapTwo Adequacy.emptyMem (.val .unit) :=
  adequacy_of_derivesWf d_swapTwo

theorem greetProg_runsC :
    BoCa.BoLo.Steps Adequacy.emptyMem greetProg Adequacy.emptyMem (.val .unit) :=
  adequacy_of_derivesWf d_greetProg

theorem ownedFn_runsC : BoCa.BoLo.Steps Adequacy.emptyMem ownedFn Adequacy.emptyMem (.val .unit) :=
  adequacy_of_derivesWf d_ownedFn

theorem mutClosure_runsC :
    BoCa.BoLo.Steps Adequacy.emptyMem mutClosure Adequacy.emptyMem (.val .unit) :=
  adequacy_of_derivesWf d_mutClosure

end BoCa.Fig16.LogRel.Core

end

import DtorUnwind.Tree.Scan

/-!
# The scan, run

Every declaration in the closure of the printed lemmas `#770` asks about, of `TW`'s and
`TWNC`'s invariants, and of the relation's resource clauses, that reads `Life` as a single
chain (`Tree/Scan.lean`). The classification of each, with its Lean evidence, is in `Tree/Comparability.lean`.
-/

open BoCa.Fig16 in
#chainScan ResU.six24 ResU.six25 ResU.six26 ResU.six27 ResU.six28 ResU.six29 ResU.six38
  ResU.six39 BoCa.Fig16.BoLo.updV_frame ResU.six52 ResU.six59 BoCa.Fig16.LogRel.wp_I_frame
  BoCa.Fig16.LogRel.wp_M_frame BoCa.Fig16.LogRel.wp_M_antiFrame BoCa.Fig16.BoLo.wp_reborrow
  BoCa.Fig16.BoLo.fresh_frame BoCa.Fig16.LogRel.Core.TW.inv BoCa.Fig16.LogRel.Core.TW.valid
  BoCa.Fig16.LogRel.Core.TW.linLife BoCa.Fig16.LogRel.Core.ptoImmS
  BoCa.Fig16.LogRel.Core.ptoMutS BoCa.Fig16.LogRel.Core.Ext BoCa.Fig16.LogRel.Core.FrameLife
  BoCa.Fig16.LogRel.Core.DtorUnwind.SI.TWNC.inv BoCa.Fig16.LogRel.Core.DtorUnwind.SI.TWNC.templ
  BoCa.Fig16.LogRel.Core.DtorUnwind.SI.TWNC.templD
  BoCa.Fig16.LogRel.Core.DtorUnwind.SI.TWNC.linDisj
  BoCa.Fig16.LogRel.Core.DtorUnwind.SI.TWNC.linLife

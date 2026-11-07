import Core.Chain.Iter835N

/-!
# `[then]` at `SemJN₀`: a finaliser that performs and raises  `[spec §19, §27]`

Interface entry E9 (`scope-831-interface.md`): Core's finaliser frame (`Core/EffFin.lean`), each
lemma at `erwp`, by induction on the index where Core inducts on `ewpTS`'s least fixed point:

* `errOkN_of_sub` (Core's `errOk_of_sub`): errors move along a first-match inclusion;
* `cfin_cancelN` (Core's `cfin_cancel`): a nested cancel past a running finaliser's `cfin`;
* `cfin_runN` (Core's `cfin_run`): a finaliser running under a cancel's `cfin`;
* `then_cancelN` (Core's `then_cancel`): a cancel run through the finaliser frame;
* `seq_raise_runN` (Core's `seq_raise_run`): a finaliser under ordinary unwinding;
* `erwp_frame_then` (Core's `ewp_frame_then_or`): the finaliser frame around an effectful
  computation;
* `then_compatN₀` (Core's `then_compatC`) and `thenDiv_compatN₀` (Core's `then_compatC_div`).

Two readings the chain adds, each where `erwp_frame_plain` adds it:

* **the index.** The finaliser `D` and the continuation `N` run at the index a stop or a value is
  reached at, below the index the frame (the context of `N` and `D`) is read at; every lemma here
  is owed up to that index `N₀`;
* **the view.** `N` and `D` are read at the run's view, from the frame beside a value or beside
  nothing, each consistent with it (the frame by `gN_splitC₀`, the value across `M`'s resumptions
  by `erwp_consistentAns`, the row's answers being read at the view).

A `Div` row is a row of the chain's table (E13), so Core's table beside the operation table (`Px`,
a tick at a row holding `Div`) and the erasure of the tick's key (`er`) have no counterpart:
`erwp_frame_then` is Core's `ewp_frame_then_or` at `Px = ∅`, `er = false`, and `[then]` at a row
holding `Div` is the same lemma (`thenDiv_compatN₀`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload cfinE ubindE errNext)

/-! ### A finaliser under a cancel's `cfin` -/

/-! ### A cancel run through the finaliser frame -/

/-! ### The finaliser frame -/

/-! ### The rules -/

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end

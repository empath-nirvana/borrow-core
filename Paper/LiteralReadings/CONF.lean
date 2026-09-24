import Paper.LiteralReadings.S6_7_WeakestPreconditionRules
import Paper.S1_Syntax.Definitions
import Paper.S3_Dynamics.Definitions
import Support.Dynamics.Machine

/-!
# Literal readings — [CONF] §3

Corollary 3.3 over `[TR]` §3's printed machine (§12.42, D6):
`TR3.corThree_unreachable`, at the closed term `free (alloc ()); ()` that `[TR]`
p. 2 types at `1`.  Nothing depends on this file.
-/

noncomputable section

namespace BoCa.TR3
open BoCa.Fig16
open BoCa.BoLo (Heap)
open BoCa.Fig16.BoLo (Entails sep wand all box top ptoOwn ptoMut ptoImm outlives_comp NoOwn noOwn_empty noOwn_compS hash_lower hash_valid hash_valid_comp hash_shift updV_compS_own hash_compS_own lower_compS_own_inv lower_get_own lower_eq_none_iff get_eq_none_of_flat get_eq_none_of_compatS_own compatS_single_of_get_none loc_infinite compS_reassoc compS_reassoc' compS_exch compS_lcomm updV_frame updV_outlives)
open BoCa.Lifetime

/-!
### Corollary 3.3 (Adequacy at 1) — literal reading

The record is in `Paper/CONF/Results.lean`.
-/
/-- No run of the printed machine from `wSeq` ends at `()`; `derives_wSeq`
types `wSeq` at `1`.
`[about ours: `[CONF]` Corollary 3.3's conclusion at `[TR]` §3's machine]` -/
theorem corThree_unreachable {μ μ' : Heap} (h : Steps μ wSeq μ' (.val .unit)) :
    False :=
  (stuck_wSeq μ).2 μ' Val.unit h

end BoCa.TR3

end

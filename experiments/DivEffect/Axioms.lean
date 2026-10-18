import DivEffect

/-! The axioms of every result `README.md` claims, and the two statements it does not. -/

open BoCa.Fig16.LogRel.Core.DivEffect

#print axioms cwp_bind
#print axioms let_compatD
#print axioms cwp_sub
#print axioms sub_compatD
#print axioms cwp_tick
#print axioms tick_compatD
#print axioms lift_compatD
#print axioms cwp_then
#print axioms then_compatD
#print axioms handle_tail
#print axioms cwp_iterate
#print axioms runtime_every_run
#print axioms fuel_every_run
#print axioms fuel_total
#print axioms reify_compat
#print axioms total_every_run_unchanged
#print axioms prog_every_run
#print axioms omega_cwp0
#print axioms omega_not_closing
#print axioms omega_not_cwp
#print axioms tick_not_unwind
#print axioms closing_of_cwp
-- not claimed proved
#print axioms handle_general
#print axioms sim_loop

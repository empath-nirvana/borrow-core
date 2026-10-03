import WorldW.Checks
import WorldW.Nil
import WorldW.HandOn
import WorldW.Record150
import WorldW.Between
import WorldW.Instances

/-!
# WorldW — axioms of every delivered result

Each `#print axioms` below must report a subset of `[propext, Classical.choice, Quot.sound]`.
-/

-- F-CLOSE (DESIGN §2)
#print axioms WorldW.closeE_anti_flat
#print axioms WorldW.close_flat_agree
#print axioms WorldW.close_flat_agree_off_anti
#print axioms WorldW.close_upd_coherent
#print axioms WorldW.upd_choice_free
#print axioms WorldW.pin_harmless
-- F1 and the compatibility checks (DESIGN §2)
#print axioms WorldW.compatW_iff_hash
#print axioms WorldW.close_frame
#print axioms WorldW.compat_resume
#print axioms WorldW.compat_at_stop
#print axioms WorldW.younger_preserved
#print axioms WorldW.close_relend_anti
#print axioms WorldW.not_closeE_anti_at_mut
#print axioms WorldW.not_holdsInjective
-- conservativity (DESIGN §1.9)
#print axioms WorldW.wpGW_nil
#print axioms WorldW.ewpTS_ewpW
-- `ewpW`'s fixed point and `σ`-monotonicity (DESIGN §4.2)
#print axioms WorldW.ewpW_fold
#print axioms WorldW.ewpW_unfold
#print axioms WorldW.ewpW_σmono_opTabW
-- reading 2: the resource core of the hand-on (DESIGN §7)
#print axioms WorldW.exit64
#print axioms WorldW.handOn64
#print axioms WorldW.handOn65
#print axioms WorldW.anti_unclosable
#print axioms WorldW.anti_handOn_needs_invariant
#print axioms WorldW.reb_restrict
#print axioms WorldW.handOn150
-- 6.150's chooser at `W` (DESIGN §3.3)
#print axioms WorldW.rebChooseTW_pin_W
-- the OQ-3 (a) arm and the argument variant (DESIGN §3.4)
#print axioms WorldW.reentryInheritA
#print axioms WorldW.reentryFreshA
#print axioms WorldW.resumeOutOfOrder
#print axioms WorldW.extentObligation_bypassed
#print axioms WorldW.argBelowExtent
#print axioms WorldW.argAboveExtent
-- non-vacuity of the negative statements (DESIGN §3.5, partly)
#print axioms WorldW.reentryInheritA_premises
#print axioms WorldW.reentryFreshA_premises
#print axioms WorldW.argBelowExtent_premises

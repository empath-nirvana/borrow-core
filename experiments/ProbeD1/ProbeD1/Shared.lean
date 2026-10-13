import ProbeD1.Bridge

/-!
# ProbeD1 — statement 0's shared lemmas, proved

`Statement0Shared` (DESIGN §4.1, §12.3) is about definitions every placement shares: W's order
(`extPreW`, `futReLend`, `futPart`, `futAvoidsTrans`, `Order.lean`), the bridge to GhostEnd's piece
(`openSFBridge`) and the nil slice the programs read (`nilSoundRet`, `Bridge.lean`). All six hold,
so the stop rule's shared clause does not fire.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1

/-- **Statement 0's shared lemmas hold.** -/
theorem statement0Shared : Statement0Shared (ℍ := ℍ) :=
  ⟨extPreW, futReLend, futPart, futAvoidsTrans, openSFBridge, nilSoundRet⟩

end ProbeD1

end

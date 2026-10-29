import NestedFold.Term

/-!
# NestedFold — the counted loop with an invariant

`countLoop_inv` is `Core/CountFold.lean`'s `countLoop_wp` with the state's relation replaced by
an invariant `I i` indexed by the counter: one `count` step, then the step `f (i, s)` taken from
`I i` to `I (i + 1)`, then the loop from `i + 1`. By induction on `len(n) − i`, as
`countLoop_wp`. The owned array traversal keeps the slots not yet visited in the invariant.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.NestedFold
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Kont)

/-- **The loop with an invariant.**  From `I i` at `i ≤ len(n)`, `count` runs to `I (len n)`,
given that the step takes `I i` to `I (i + 1)` below the bound. -/
theorem countLoop_inv (f : Val) (n : UInt32) (I : Nat → List SRec → Val → WProp)
    (hstep : ∀ i : UInt32, i < arrLen n → ∀ ls s, Entails (I i.toNat ls s)
      (wpTS ls (.app (.val f) (.val (Val.pair (Val.i32 i) s))) (fun ls' => I (i.toNat + 1) ls'))) :
    ∀ (k : Nat) (i : UInt32) (ls : List SRec) (s : Val) (ρ : WRes),
      (arrLen n).toNat - i.toNat = k → i.toNat ≤ (arrLen n).toNat → I i.toNat ls s ρ →
      wpTS ls (.app (.val (.prim .count))
        (.val (Val.pair f (Val.pair (Val.i32 n) (Val.pair (Val.i32 i) s)))))
        (fun ls' => I (arrLen n).toNat ls') ρ := by
  intro k
  induction k with
  | zero =>
      intro i ls s ρ hk hle hs
      refine wpTS_count ls f n i s _ ρ ?_
      have hi : ¬ i < arrLen n := by
        rw [UInt32.lt_iff_toNat_lt]; omega
      unfold countNext
      rw [if_neg hi]
      have e : i.toNat = (arrLen n).toNat := by omega
      rw [← e]
      exact wpTS_val ls s _ ρ hs
  | succ k ih =>
      intro i ls s ρ hk hle hs
      refine wpTS_count ls f n i s _ ρ ?_
      have hi : i < arrLen n := by
        rw [UInt32.lt_iff_toNat_lt]; omega
      have hb := arrLen_bound n
      have hi1 : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt32.toNat_add]
        have : i.toNat < (arrLen n).toNat := UInt32.lt_iff_toNat_lt.mp hi
        simp only [UInt32.toNat_one]
        exact Nat.mod_eq_of_lt (by omega)
      unfold countNext
      rw [if_pos hi]
      refine wpTS_bind
        (.appR (.val (.prim .count)) (.pairR f (.pairR (Val.i32 n) (.pairR (Val.i32 (i + 1)) .hole))))
        (.app (.val f) (.val (Val.pair (Val.i32 i) s))) ls _ ρ ?_
      refine wpTS_mono (fun ls' v σ hv => ?_) ρ (hstep i hi ls s ρ hs)
      have hv' : I (i + 1).toNat ls' v σ := by rw [hi1]; exact hv
      exact ih (i + 1) ls' v σ (by omega) (by omega) hv'

end BoCa.Fig16.LogRel.Core.NestedFold

end

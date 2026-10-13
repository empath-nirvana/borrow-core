import Core.Weaken
import Targets.I.Pins
import Targets.Base.Support

/-!
# The interaction — I4.a at tier 1 (RESTRUCTURE §3.2; DESIGN §Corrections C4)

`i4a_tier1 : I4a tier1 admClosedOp .abortive`.  PROVED AT A RESTRICTION (tier 1, abortive rows).  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Programs (alloc' free')

/-- **`I4a tier1 admClosedOp .abortive`.** -/
theorem i4a_tier1 : I4a tier1 admClosedOp .abortive := by
  intro impl Δ Γ x S d s₀ body B _ hΓ hx hΔx hΓx hxS hxB hside hspan hcls hdc hs₀ hd hbody η hη
  set A := impl.S with hA
  set bnd := Δ.meetOfDom with hbnd
  have hs₀' : CDerives Δ Γ s₀ (.val A) := hs₀ η hη
  have hd' : CDerives Δ Γ d (.val (.lolli (.ref A) .unit)) := hd η hη
  have hbody' : CDerives (Δ.extend x bnd) (⟨.mut (.var x) A, true⟩ :: Γ) body
      (.comp (CTy.effOf S (.box (.var x) B))) := hbody η hη
  have hS : S.Unwind x := rowSpan_abortive_iff_unwind.mp ⟨hspan, hcls⟩
  have hsplit := deadP_selfSplit hΓ
  -- the callback `Λ. λm. body`, under the cell
  let cbT : VTy := cbUTy x bnd (.mut (.var x) A) B S
  have hcb : CDerives Δ (⟨.ref A, false⟩ :: Γ) (.val (.lam (.val (.lam (body.shift 2 1)))))
      (.val cbT) := by
    have hdd : Ctx.Dead [(⟨.unit, false⟩ : Slot VTy), ⟨.ref A, false⟩] := .cons (.cons .nil)
    have hb := CDerives.insert_dead hdd hbody' [⟨.mut (.var x) A, true⟩] Γ rfl
    refine .thunkV rfl (.allI (S := .unit) ?_ ?_ ?_ (.lam hb))
    · exact meetOfDomL_not_mentions _ hx
    · exact hΔx
    · intro s hs hl
      rcases List.mem_cons.mp hs with rfl | hs
      · cases hl
      · exact hΓx s hs hl
  -- the unwinding borrow `withborU d`
  let wT : VTy := withbor2UTy x bnd A B S
  have hw : CDerives Δ (⟨cbT, false⟩ :: ⟨.ref A, false⟩ :: Γ) (withborUE d) (.val wT) := by
    have hdd : Ctx.Dead [(⟨cbT, false⟩ : Slot VTy), ⟨.ref A, false⟩] := .cons (.cons .nil)
    have hd2 := CDerives.insert_dead hdd hd' [] Γ rfl
    rw [shift_closed0 hdc] at hd2
    exact .withbor2U x (.cons (.cons hΓ)) hx hside hxS hxB hS hdc hd2
  -- after the call: free the cell, answer the result
  have hK : Ctx.Dead (kill Γ) := kill_dead Γ
  let Γ₂ : Ctx VTy := ⟨wT, false⟩ :: ⟨cbT, false⟩ :: ⟨.ref A, false⟩ :: kill Γ
  have hΓ₂ : Ctx.Dead Γ₂ := .cons (.cons (.cons hK))
  have hR : Ctx.Dead ((⟨.tensor (.ref A) B, false⟩ : Slot VTy) :: Γ₂) := .cons hΓ₂
  have hpair : CDerives Δ (⟨B, true⟩ :: ⟨.ref A, true⟩ :: ⟨.tensor (.ref A) B, false⟩ :: Γ₂)
      (.pair (.app free' (.var 1)) (.var 0)) (.comp (CTy.effOf S (.tensor A B))) := by
    refine .effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h) (.ret (.tensorI
      (.right (.left (deadSplit hR))) ?_ (.var (.here (.cons hR.toP)))))
    exact .lolliE (.dead (.left (deadSplit hR))) (.var (.there (.here hR.toP)))
      (.free (.cons (.cons hR.toP)))
  have hN₄ : CDerives Δ (⟨.tensor (.ref A) B, true⟩ :: Γ₂)
      (.letpair (.var 0) (.pair (.app free' (.var 1)) (.var 0)))
      (.comp (CTy.effOf S (.tensor A B))) :=
    .tensorE (.left (deadSplit hΓ₂)) (.var (.here hΓ₂.toP)) hpair
  -- the call `w c f`
  have hM₃ : CDerives Δ (⟨wT, true⟩ :: ⟨cbT, true⟩ :: ⟨.ref A, true⟩ :: Γ)
      (.app (.app (.var 0) (.var 2)) (.var 1)) (.comp (CTy.effOf S (.tensor (.ref A) B))) := by
    have hf : CDerives Δ (⟨wT, true⟩ :: ⟨cbT, false⟩ :: ⟨.ref A, false⟩ :: Γ) (.var 0)
        (.comp (.arr (.ref A) (.arr cbT (CTy.effOf S (.tensor (.ref A) B))))) :=
      .force (C := .arr (.ref A) (.arr cbT (CTy.effOf S (.tensor (.ref A) B))))
        (.here (.cons (.cons hΓ)))
    have hfc : CDerives Δ (⟨wT, true⟩ :: ⟨cbT, false⟩ :: ⟨.ref A, true⟩ :: Γ)
        (.app (.var 0) (.var 2)) (.comp (.arr cbT (CTy.effOf S (.tensor (.ref A) B)))) :=
      .app (.left (.dead (.right (deadP_splitKill hΓ)))) hf (.there (.there (.here hK.toP)))
    exact .app (.left (.right (.left (deadP_splitKill hΓ)))) hfc (.there (.here (.cons hK.toP)))
  have hN₃ : CDerives Δ (⟨wT, true⟩ :: ⟨cbT, true⟩ :: ⟨.ref A, true⟩ :: Γ)
      (.app (.val (.lam (.letpair (.var 0) (.pair (.app free' (.var 1)) (.var 0)))))
        (.app (.app (.var 0) (.var 2)) (.var 1)))
      (.comp (CTy.effOf S (.tensor A B))) :=
    .effLet (.left (.left (.left (deadP_splitKill hΓ))))
      (fun _ s hs hl => by rw [dead_not_live hΓ₂ s hs] at hl; cases hl)
      (fun _ s hs hl => by rw [dead_not_live hΓ₂ s hs] at hl; cases hl) hM₃ hN₄
  -- the three bindings
  have hN₂ := CDerives.bind (.right (.right hsplit)) (.ret hw) hN₃
  have hN₁ := CDerives.bind (.right hsplit) (.ret hcb) hN₂
  exact CDerives.bind hsplit (.ret (.lolliE hsplit hs₀' (.alloc hΓ))) hN₁

end Targets

end

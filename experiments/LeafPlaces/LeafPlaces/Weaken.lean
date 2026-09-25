import LeafPlaces.Typing

/-!
# Weakening by dead slots at the end of a context

A derivation at `Γ` is one at `Γ ++ Γ'` when every slot of `Γ'` is consumed: the de Bruijn
indices of `Γ` are unchanged, and every rule's context premise (`Split`, `Solo`, `Dead`,
`Outlives`, the Barendregt premise, `Persistent`) holds of the extended context.  It lets a
closed callback typed at `[]` sit beside a free variable.
-/

noncomputable section

namespace BoCa.LeafPlaces
open BoCa BoCa.Lifetime

variable {Γ' : Ctx Ty}

theorem dead_append (h' : Ctx.Dead Γ') : ∀ {Γ : Ctx Ty}, Ctx.Dead Γ → Ctx.Dead (Γ ++ Γ')
  | [], _ => h'
  | _ :: _, .cons h => .cons (dead_append h' h)

theorem split_append (h' : Ctx.Dead Γ') : ∀ {Γ Γ₁ Γ₂ : Ctx Ty}, Ctx.Split Γ Γ₁ Γ₂ →
    Ctx.Split (Γ ++ Γ') (Γ₁ ++ Γ') (Γ₂ ++ Γ')
  | _, _, _, .nil => h'.split
  | _, _, _, .left h => .left (split_append h' h)
  | _, _, _, .right h => .right (split_append h' h)
  | _, _, _, .dead h => .dead (split_append h' h)

theorem solo_append (h' : Ctx.Dead Γ') : ∀ {Γ : Ctx Ty} {i : Nat} {T : Ty}, Ctx.Solo Γ i T →
    Ctx.Solo (Γ ++ Γ') i T
  | _, _, _, .here h => .here (dead_append h' h)
  | _, _, _, .there h => .there (solo_append h' h)

theorem dead_not_live : ∀ {Γ : Ctx Ty}, Ctx.Dead Γ → ∀ s ∈ Γ, s.live = false
  | [], _, _, hs => absurd hs (by simp)
  | _ :: _, .cons h, s, hs => by
      rcases List.mem_cons.mp hs with rfl | hs
      · rfl
      · exact dead_not_live h s hs

theorem live_append {P : Slot Ty → Prop} (h' : Ctx.Dead Γ') {Γ : Ctx Ty}
    (h : ∀ s ∈ Γ, s.live = true → P s) : ∀ s ∈ Γ ++ Γ', s.live = true → P s := by
  intro s hs hl
  rcases List.mem_append.mp hs with hs | hs
  · exact h s hs hl
  · rw [dead_not_live h' s hs] at hl; cases hl

theorem outlives_append (h' : Ctx.Dead Γ') {Δ : LifeCtx} {Γ : Ctx Ty} {a : Life}
    (h : Ctx.Outlives Δ Γ a) : Ctx.Outlives Δ (Γ ++ Γ') a :=
  ⟨h.1, live_append h' h.2⟩

theorem persistent_append (h' : Ctx.Dead Γ') {Γ : Ctx Ty} (h : Ctx.Persistent Γ) :
    Ctx.Persistent (Γ ++ Γ') :=
  live_append (P := fun s => ∃ T, s.ty = .bang T) h' h

/-- **Weakening** by consumed slots at the end. -/
theorem DerivesWf.append_dead (h' : Ctx.Dead Γ') {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty}
    (h : DerivesWf Δ Γ e T) : DerivesWf Δ (Γ ++ Γ') e T := by
  induction h with
  | var hs => exact .var (solo_append h' hs)
  | unitI hd => exact .unitI (dead_append h' hd)
  | unitE hs _ _ ih₁ ih₂ => exact .unitE (split_append h' hs) ih₁ ih₂
  | tensorI hs _ _ ih₁ ih₂ => exact .tensorI (split_append h' hs) ih₁ ih₂
  | tensorE hs hwf _ _ ih₁ ih₂ => exact .tensorE (split_append h' hs) hwf ih₁ ih₂
  | sumI₁ _ ih => exact .sumI₁ ih
  | sumI₂ _ ih => exact .sumI₂ ih
  | sumE hs hwf _ _ _ ih₀ ih₁ ih₂ => exact .sumE (split_append h' hs) hwf ih₀ ih₁ ih₂
  | lolliI hwf _ ih => exact .lolliI hwf ih
  | lolliE hs _ _ ih₁ ih₂ => exact .lolliE (split_append h' hs) ih₁ ih₂
  | allI hx hb hnb _ ih => exact .allI hx hb (live_append h' hnb) ih
  | allE _ hlt ih => exact .allE ih hlt
  | boxIctx _ hΓ ih => exact .boxIctx ih (outlives_append h' hΓ)
  | boxE _ ih => exact .boxE ih
  | immSub _ hle ih => exact .immSub ih hle
  | mutSub _ hle ih => exact .mutSub ih hle
  | allocAx hd => exact .allocAx (dead_append h' hd)
  | freeAx hd => exact .freeAx (dead_append h' hd)
  | swapAx hd => exact .swapAx (dead_append h' hd)
  | copyAx hd => exact .copyAx (dead_append h' hd)
  | forgetImmAx hd => exact .forgetImmAx (dead_append h' hd)
  | forgetMutAx hd => exact .forgetMutAx (dead_append h' hd)
  | forgetUnkAx hd => exact .forgetUnkAx (dead_append h' hd)
  | withbor1Ax hd x hx hwf => exact .withbor1Ax (dead_append h' hd) x hx hwf
  | withbor2Ax hd x hx hside hwf => exact .withbor2Ax (dead_append h' hd) x hx hside hwf
  | withbor3Ax hd x hx hwf => exact .withbor3Ax (dead_append h' hd) x hx hwf
  | withloadAx hd x hx hwf => exact .withloadAx (dead_append h' hd) x hx hwf
  | withswapAx hd => exact .withswapAx (dead_append h' hd)
  | bangLamI hΓ hwf _ ih => exact .bangLamI (persistent_append h' hΓ) hwf ih
  | bangAllI hΓ hx hb hnb _ ih =>
      exact .bangAllI (persistent_append h' hΓ) hx hb (live_append h' hnb) ih
  | bangE _ ih => exact .bangE ih
  | copyBangAx hd => exact .copyBangAx (dead_append h' hd)
  | forgetBangAx hd => exact .forgetBangAx (dead_append h' hd)

end BoCa.LeafPlaces

end

import Paper.Examples.Programs

/-!
# Dead-slot weakening for `DerivesWf`

`DWk Γ Γ'`: `Γ'` has the live slots of `Γ` at the same positions and types; a consumed slot
may change its type; and `Γ'` may carry extra consumed slots at its end.  A derivation at `Γ`
is a derivation of the same term at `Γ'` (`DerivesWf.dwk`): no rule reads the type of a
consumed slot, and the rules that ask a context to be consumed (`Ctx.Dead`) accept extra
consumed slots.

The translation of `HandlersAsBorrows.Translate` uses it twice: to forget the types of the
padding slots of the source judgment, and to type closed code (a clause, a block) inside any
consumed context.

`[about ours]`
-/

noncomputable section

namespace HandlersAsBorrows
open BoCa BoCa.Lifetime

/-- `Γ'` agrees with `Γ` at live slots, is consumed wherever `Γ` is, and may be longer by
consumed slots. -/
inductive DWk : Ctx Ty → Ctx Ty → Prop where
  | nil {Γ' : Ctx Ty} : Ctx.Dead Γ' → DWk [] Γ'
  | live {T : Ty} {Γ Γ' : Ctx Ty} : DWk Γ Γ' → DWk (⟨T, true⟩ :: Γ) (⟨T, true⟩ :: Γ')
  | dead {T U : Ty} {Γ Γ' : Ctx Ty} : DWk Γ Γ' → DWk (⟨T, false⟩ :: Γ) (⟨U, false⟩ :: Γ')

namespace DWk

theorem refl : ∀ Γ : Ctx Ty, DWk Γ Γ
  | [] => .nil .nil
  | ⟨_, true⟩ :: Γ => .live (refl Γ)
  | ⟨_, false⟩ :: Γ => .dead (refl Γ)

theorem cons {T : Ty} {b : Bool} {Γ Γ' : Ctx Ty} (h : DWk Γ Γ') :
    DWk (⟨T, b⟩ :: Γ) (⟨T, b⟩ :: Γ') := by
  cases b
  · exact .dead h
  · exact .live h

theorem dead_of {Γ Γ' : Ctx Ty} (h : DWk Γ Γ') (hd : Ctx.Dead Γ) : Ctx.Dead Γ' := by
  induction h with
  | nil h' => exact h'
  | live _ _ => cases hd
  | dead _ ih => cases hd with | cons hd' => exact .cons (ih hd')

theorem solo {Γ Γ' : Ctx Ty} {i : Nat} {T : Ty} (hs : Ctx.Solo Γ i T) (h : DWk Γ Γ') :
    Ctx.Solo Γ' i T := by
  induction hs generalizing Γ' with
  | here hd => cases h with | live h' => exact .here (h'.dead_of hd)
  | there _ ih => cases h with | dead h' => exact .there (ih h')

theorem split {Γ Γ₁ Γ₂ Γ' : Ctx Ty} (hs : Ctx.Split Γ Γ₁ Γ₂) (h : DWk Γ Γ') :
    ∃ Γ₁' Γ₂', Ctx.Split Γ' Γ₁' Γ₂' ∧ DWk Γ₁ Γ₁' ∧ DWk Γ₂ Γ₂' := by
  induction hs generalizing Γ' with
  | nil =>
      cases h with
      | nil hd => exact ⟨_, _, hd.split, .nil hd, .nil hd⟩
  | left _ ih =>
      cases h with
      | live h' =>
          obtain ⟨A, B, hs', ha, hb⟩ := ih h'
          exact ⟨_, _, .left hs', .live ha, .dead hb⟩
  | right _ ih =>
      cases h with
      | live h' =>
          obtain ⟨A, B, hs', ha, hb⟩ := ih h'
          exact ⟨_, _, .right hs', .dead ha, .live hb⟩
  | dead _ ih =>
      cases h with
      | dead h' =>
          obtain ⟨A, B, hs', ha, hb⟩ := ih h'
          exact ⟨_, _, .dead hs', .dead ha, .dead hb⟩

/-- Every live slot of `Γ'` is a live slot of `Γ`. -/
theorem live_mem {Γ Γ' : Ctx Ty} (h : DWk Γ Γ') :
    ∀ s ∈ Γ', s.live = true → s ∈ Γ := by
  induction h with
  | nil hd =>
      intro s hs hl
      exfalso
      induction hd with
      | nil => cases hs
      | cons _ ih =>
          rcases List.mem_cons.mp hs with rfl | hs'
          · simp at hl
          · exact ih hs'
  | live _ ih =>
      intro s hs hl
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih s hs' hl)
  | dead _ ih =>
      intro s hs hl
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact absurd hl (by simp)
      · exact List.mem_cons_of_mem _ (ih s hs' hl)

theorem outlives {Δ : LifeCtx} {a : Life} {Γ Γ' : Ctx Ty} (h : DWk Γ Γ')
    (ho : Ctx.Outlives Δ Γ a) : Ctx.Outlives Δ Γ' a :=
  ⟨ho.1, fun s hs hl => ho.2 s (h.live_mem s hs hl) hl⟩

theorem persistent {Γ Γ' : Ctx Ty} (h : DWk Γ Γ') (hp : Ctx.Persistent Γ) :
    Ctx.Persistent Γ' :=
  fun s hs hl => hp s (h.live_mem s hs hl) hl

theorem noBinds {x : LifeVar} {Γ Γ' : Ctx Ty} (h : DWk Γ Γ')
    (hb : ∀ s ∈ Γ, s.live = true → s.ty.bindsB x = false) :
    ∀ s ∈ Γ', s.live = true → s.ty.bindsB x = false :=
  fun s hs hl => hb s (h.live_mem s hs hl) hl

end DWk

/-- Dead-slot weakening: a derivation survives `DWk`, at the same term. -/
theorem _root_.BoCa.DerivesWf.dwk {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty}
    (hd : DerivesWf Δ Γ e T) : ∀ {Γ'}, DWk Γ Γ' → DerivesWf Δ Γ' e T := by
  induction hd with
  | var h => intro Γ' hw; exact .var (hw.solo h)
  | unitI h => intro Γ' hw; exact .unitI (hw.dead_of h)
  | unitE hs _ _ ih₁ ih₂ =>
      intro Γ' hw
      obtain ⟨A, B, hs', ha, hb⟩ := DWk.split hs hw
      exact .unitE hs' (ih₁ ha) (ih₂ hb)
  | tensorI hs _ _ ih₁ ih₂ =>
      intro Γ' hw
      obtain ⟨A, B, hs', ha, hb⟩ := DWk.split hs hw
      exact .tensorI hs' (ih₁ ha) (ih₂ hb)
  | tensorE hs hwf _ _ ihp ihb =>
      intro Γ' hw
      obtain ⟨A, B, hs', ha, hb⟩ := DWk.split hs hw
      exact .tensorE hs' hwf (ihp ha) (ihb hb.cons.cons)
  | sumI₁ _ ih => intro Γ' hw; exact .sumI₁ (ih hw)
  | sumI₂ _ ih => intro Γ' hw; exact .sumI₂ (ih hw)
  | sumE hs hwf _ _ _ ih₀ ih₁ ih₂ =>
      intro Γ' hw
      obtain ⟨A, B, hs', ha, hb⟩ := DWk.split hs hw
      exact .sumE hs' hwf (ih₀ ha) (ih₁ hb.cons) (ih₂ hb.cons)
  | lolliI hwf _ ih => intro Γ' hw; exact .lolliI hwf (ih hw.cons)
  | lolliE hs _ _ iha ihf =>
      intro Γ' hw
      obtain ⟨A, B, hs', ha, hb⟩ := DWk.split hs hw
      exact .lolliE hs' (iha ha) (ihf hb)
  | allI hx hb hnb _ ih =>
      intro Γ' hw; exact .allI hx hb (hw.noBinds hnb) (ih hw.cons)
  | allE _ hlt ih => intro Γ' hw; exact .allE (ih hw) hlt
  | boxIctx _ hΓ ih => intro Γ' hw; exact .boxIctx (ih hw) (hw.outlives hΓ)
  | boxE _ ih => intro Γ' hw; exact .boxE (ih hw)
  | immSub _ hle ih => intro Γ' hw; exact .immSub (ih hw) hle
  | mutSub _ hle ih => intro Γ' hw; exact .mutSub (ih hw) hle
  | allocAx h => intro Γ' hw; exact .allocAx (hw.dead_of h)
  | freeAx h => intro Γ' hw; exact .freeAx (hw.dead_of h)
  | swapAx h => intro Γ' hw; exact .swapAx (hw.dead_of h)
  | copyAx h => intro Γ' hw; exact .copyAx (hw.dead_of h)
  | forgetImmAx h => intro Γ' hw; exact .forgetImmAx (hw.dead_of h)
  | forgetMutAx h => intro Γ' hw; exact .forgetMutAx (hw.dead_of h)
  | forgetUnkAx h => intro Γ' hw; exact .forgetUnkAx (hw.dead_of h)
  | withbor1Ax h x hx hwf => intro Γ' hw; exact .withbor1Ax (hw.dead_of h) x hx hwf
  | withbor2Ax h x hx hside hwf => intro Γ' hw; exact .withbor2Ax (hw.dead_of h) x hx hside hwf
  | withbor3Ax h x hx hwf => intro Γ' hw; exact .withbor3Ax (hw.dead_of h) x hx hwf
  | withloadAx h x hx hwf => intro Γ' hw; exact .withloadAx (hw.dead_of h) x hx hwf
  | withswapAx h => intro Γ' hw; exact .withswapAx (hw.dead_of h)
  | bangLamI hΓ hwf _ ih => intro Γ' hw; exact .bangLamI (hw.persistent hΓ) hwf (ih hw.cons)
  | bangAllI hΓ hx hb hnb _ ih =>
      intro Γ' hw; exact .bangAllI (hw.persistent hΓ) hx hb (hw.noBinds hnb) (ih hw.cons)
  | bangE _ ih => intro Γ' hw; exact .bangE (ih hw)
  | copyBangAx h => intro Γ' hw; exact .copyBangAx (hw.dead_of h)
  | forgetBangAx h => intro Γ' hw; exact .forgetBangAx (hw.dead_of h)

end HandlersAsBorrows

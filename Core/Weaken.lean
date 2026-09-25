import Core.Examples

/-!
# Core — weakening by dead slots at the end of a context  `[spec §3]`

A derivation at `Γ` is one at `Γ ++ Γ'` when every slot of `Γ'` is consumed: the de Bruijn
indices of `Γ` are unchanged, and every rule's context premise (`Split`, `Solo`, `Dead`,
`CtxOutlives`, `∀I`'s freshness premise, `Persistent`) holds of the extended context.  It lets a
closed callback typed at `[]` sit beside a free variable.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Lifetime (LSub LifeCtx LifeVar)

variable {Γ' : Ctx VTy}

theorem dead_append (h' : Ctx.Dead Γ') : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → Ctx.Dead (Γ ++ Γ')
  | [], _ => h'
  | _ :: _, .cons h => .cons (dead_append h' h)

theorem split_append (h' : Ctx.Dead Γ') : ∀ {Γ Γ₁ Γ₂ : Ctx VTy}, Ctx.Split Γ Γ₁ Γ₂ →
    Ctx.Split (Γ ++ Γ') (Γ₁ ++ Γ') (Γ₂ ++ Γ')
  | _, _, _, .nil => deadSplit h'
  | _, _, _, .left h => .left (split_append h' h)
  | _, _, _, .right h => .right (split_append h' h)
  | _, _, _, .dead h => .dead (split_append h' h)

theorem solo_append (h' : Ctx.Dead Γ') : ∀ {Γ : Ctx VTy} {i : Nat} {A : VTy}, Ctx.Solo Γ i A →
    Ctx.Solo (Γ ++ Γ') i A
  | _, _, _, .here h => .here (dead_append h' h)
  | _, _, _, .there h => .there (solo_append h' h)

theorem dead_not_live : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → ∀ s ∈ Γ, s.live = false
  | [], _, _, hs => absurd hs (by simp)
  | _ :: _, .cons h, s, hs => by
      rcases List.mem_cons.mp hs with rfl | hs
      · rfl
      · exact dead_not_live h s hs

theorem live_append {P : Slot VTy → Prop} (h' : Ctx.Dead Γ') {Γ : Ctx VTy}
    (h : ∀ s ∈ Γ, s.live = true → P s) : ∀ s ∈ Γ ++ Γ', s.live = true → P s := by
  intro s hs hl
  rcases List.mem_append.mp hs with hs | hs
  · exact h s hs hl
  · rw [dead_not_live h' s hs] at hl; cases hl

theorem ctxOutlives_append (h' : Ctx.Dead Γ') {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life}
    (h : CtxOutlives Δ Γ a) : CtxOutlives Δ (Γ ++ Γ') a :=
  ⟨h.1, live_append h' h.2⟩

theorem persistent_append (h' : Ctx.Dead Γ') {Γ : Ctx VTy} (h : Persistent Γ) :
    Persistent (Γ ++ Γ') :=
  live_append (P := fun s => ∃ A, s.ty = .bang A) h' h

/-- **Weakening** by consumed slots at the end. -/
theorem CDerives.append_dead (h' : Ctx.Dead Γ') {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerives Δ Γ e j) : CDerives Δ (Γ ++ Γ') e j := by
  induction h with
  | var hs => exact .var (solo_append h' hs)
  | unitI hd => exact .unitI (dead_append h' hd)
  | tensorI hs _ _ ih₁ ih₂ => exact .tensorI (split_append h' hs) ih₁ ih₂
  | sumI₁ _ ih => exact .sumI₁ ih
  | sumI₂ _ ih => exact .sumI₂ ih
  | thunkF _ ih => exact .thunkF ih
  | thunkV hC _ ih => exact .thunkV hC ih
  | ret _ ih => exact .ret ih
  | bind hs _ _ ihM ihN => exact .bind (split_append h' hs) ihM ihN
  | force hs => exact .force (solo_append h' hs)
  | lam _ ih => exact .lam ih
  | app hs _ hx ih => exact .app (split_append h' hs) ih (solo_append h' hx)
  | withI _ _ ihM ihN => exact .withI ihM ihN
  | proj₁ _ ih => exact .proj₁ ih
  | proj₂ _ ih => exact .proj₂ ih
  | topI => exact .topI
  | unitE hs _ _ ihV ihM => exact .unitE (split_append h' hs) ihV ihM
  | tensorE hs _ _ ihV ihM => exact .tensorE (split_append h' hs) ihV ihM
  | sumE hs _ _ _ ihV ih₁ ih₂ => exact .sumE (split_append h' hs) ihV ih₁ ih₂
  | zeroE hs _ ihV => exact .zeroE (split_append h' hs) ihV
  | allI hbx hΔx hΓx _ ih => exact .allI hbx hΔx (live_append h' hΓx) ih
  | allE _ hlt ih => exact .allE ih hlt
  | bangThunkF hp _ ih => exact .bangThunkF (persistent_append h' hp) ih
  | bangThunkV hp hC _ ih => exact .bangThunkV (persistent_append h' hp) hC ih
  | bangE _ ih => exact .bangE ih
  | copyBang hΓ => exact .copyBang (dead_append h' hΓ)
  | forgetBang hΓ => exact .forgetBang (dead_append h' hΓ)
  | boxI _ hΓ ih => exact .boxI ih (ctxOutlives_append h' hΓ)
  | boxE _ ih => exact .boxE ih
  | immSub _ hle ih => exact .immSub ih hle
  | mutSub _ hle ih => exact .mutSub ih hle
  | alloc hΓ => exact .alloc (dead_append h' hΓ)
  | free hΓ => exact .free (dead_append h' hΓ)
  | swap hΓ => exact .swap (dead_append h' hΓ)
  | copy hΓ => exact .copy (dead_append h' hΓ)
  | forgetImm hΓ => exact .forgetImm (dead_append h' hΓ)
  | forgetMut hΓ => exact .forgetMut (dead_append h' hΓ)
  | forgetUnk hΓ => exact .forgetUnk (dead_append h' hΓ)
  | withbor1 x hΓ hx hsc hf₁ hf₂ => exact .withbor1 x (dead_append h' hΓ) hx hsc hf₁ hf₂
  | withbor2 x hΓ hx hside hf₁ hf₂ => exact .withbor2 x (dead_append h' hΓ) hx hside hf₁ hf₂
  | withbor3 x hΓ hx hf₁ hf₂ => exact .withbor3 x (dead_append h' hΓ) hx hf₁ hf₂
  | withload x hΓ hx hf₁ hf₂ => exact .withload x (dead_append h' hΓ) hx hf₁ hf₂
  | withswap hΓ => exact .withswap (dead_append h' hΓ)
  | lolliE hs _ _ iha ihf => exact .lolliE (split_append h' hs) iha ihf
  | allEV _ hlt ih => exact .allEV ih hlt
  | ofRet _ ih => exact .ofRet ih
  | roll hA hc _ ih => exact .roll hA hc ih
  | unroll _ ih => exact .unroll ih
  | foldImm F y c R hΓ hF hG hyM hyR hR =>
      exact .foldImm F y c R (dead_append h' hΓ) hF hG hyM hyR hR
  | foldOwn F R hΓ hF hG => exact .foldOwn F R (dead_append h' hΓ) hF hG
  | foldReuse F R hΓ hF hG => exact .foldReuse F R (dead_append h' hΓ) hF hG
  | delayIn _ ih => exact .delayIn ih
  | delayOut _ ih => exact .delayOut ih
  | fixD A S hΓ => exact .fixD A S (dead_append h' hΓ)
  | strIn _ ih => exact .strIn ih
  | strOut _ ih => exact .strOut ih
  | unfoldS A S hΓ => exact .unfoldS A S (dead_append h' hΓ)

end BoCa.Fig16.LogRel.Core

end

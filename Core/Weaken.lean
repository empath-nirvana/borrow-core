import Core.Examples

/-!
# Core — weakening by dead slots at the end of a context  `[spec §3]`

A derivation at `Γ` is one at `Γ ++ Γ'` when every slot of `Γ'` is consumed: the de Bruijn
indices of `Γ` are unchanged, and every rule's context premise (`SplitP`, `SoloP`, `DeadP`,
`CtxOutlives`, `∀I`'s freshness premise, `Persistent`) holds of the extended context.  It lets a
closed callback typed at `[]` sit beside a free variable.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Lifetime (LSub LifeCtx LifeVar)

variable {Γ' : Ctx VTy}

theorem deadP_append (h' : Ctx.Dead Γ') : ∀ {Γ : Ctx VTy}, Ctx.DeadP Γ → Ctx.DeadP (Γ ++ Γ')
  | [], _ => h'.toP
  | _ :: _, .cons h => .cons (deadP_append h' h)
  | _ :: _, .drop hT h => .drop hT (deadP_append h' h)

theorem splitP_append (h' : Ctx.Dead Γ') : ∀ {Γ Γ₁ Γ₂ : Ctx VTy}, Ctx.SplitP Γ Γ₁ Γ₂ →
    Ctx.SplitP (Γ ++ Γ') (Γ₁ ++ Γ') (Γ₂ ++ Γ')
  | _, _, _, .nil => deadSplit h'
  | _, _, _, .left h => .left (splitP_append h' h)
  | _, _, _, .right h => .right (splitP_append h' h)
  | _, _, _, .dead h => .dead (splitP_append h' h)
  | _, _, _, .dup hT h => .dup hT (splitP_append h' h)

theorem soloP_append (h' : Ctx.Dead Γ') : ∀ {Γ : Ctx VTy} {i : Nat} {A : VTy}, Ctx.SoloP Γ i A →
    Ctx.SoloP (Γ ++ Γ') i A
  | _, _, _, .here h => .here (deadP_append h' h)
  | _, _, _, .there h => .there (soloP_append h' h)
  | _, _, _, .skip hS h => .skip hS (soloP_append h' h)

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
  | var hs => exact .var (soloP_append h' hs)
  | unitI hd => exact .unitI (deadP_append h' hd)
  | tensorI hs _ _ ih₁ ih₂ => exact .tensorI (splitP_append h' hs) ih₁ ih₂
  | sumI₁ _ ih => exact .sumI₁ ih
  | sumI₂ _ ih => exact .sumI₂ ih
  | thunkF _ ih => exact .thunkF ih
  | thunkV hC _ ih => exact .thunkV hC ih
  | ret _ ih => exact .ret ih
  | bind hs _ _ ihM ihN => exact .bind (splitP_append h' hs) ihM ihN
  | force hs => exact .force (soloP_append h' hs)
  | lam _ ih => exact .lam ih
  | app hs _ hx ih => exact .app (splitP_append h' hs) ih (soloP_append h' hx)
  | withI _ _ ihM ihN => exact .withI ihM ihN
  | proj₁ _ ih => exact .proj₁ ih
  | proj₂ _ ih => exact .proj₂ ih
  | topI => exact .topI
  | unitE hs _ _ ihV ihM => exact .unitE (splitP_append h' hs) ihV ihM
  | tensorE hs _ _ ihV ihM => exact .tensorE (splitP_append h' hs) ihV ihM
  | sumE hs _ _ _ ihV ih₁ ih₂ => exact .sumE (splitP_append h' hs) ihV ih₁ ih₂
  | zeroE hs _ ihV => exact .zeroE (splitP_append h' hs) ihV
  | allI hbx hΔx hΓx _ ih => exact .allI hbx hΔx (live_append h' hΓx) ih
  | allE _ hlt ih => exact .allE ih hlt
  | bangThunkF hp _ ih => exact .bangThunkF (persistent_append h' hp) ih
  | bangThunkV hp hC _ ih => exact .bangThunkV (persistent_append h' hp) hC ih
  | bangE _ ih => exact .bangE ih
  | copyBang hΓ => exact .copyBang (deadP_append h' hΓ)
  | forgetBang hΓ => exact .forgetBang (deadP_append h' hΓ)
  | boxI _ hΓ ih => exact .boxI ih (ctxOutlives_append h' hΓ)
  | boxE _ ih => exact .boxE ih
  | immSub _ hle ih => exact .immSub ih hle
  | mutSub _ hle ih => exact .mutSub ih hle
  | alloc hΓ => exact .alloc (deadP_append h' hΓ)
  | free hΓ => exact .free (deadP_append h' hΓ)
  | swap hΓ => exact .swap (deadP_append h' hΓ)
  | copy hΓ => exact .copy (deadP_append h' hΓ)
  | forgetImm hΓ => exact .forgetImm (deadP_append h' hΓ)
  | forgetMut hΓ => exact .forgetMut (deadP_append h' hΓ)
  | forgetUnk hΓ => exact .forgetUnk (deadP_append h' hΓ)
  | lit c hΓ => exact .lit c (deadP_append h' hΓ)
  | hostOp op hΓ => exact .hostOp op (deadP_append h' hΓ)
  | withbor1 x hΓ hx hsc hf₁ hf₂ => exact .withbor1 x (deadP_append h' hΓ) hx hsc hf₁ hf₂
  | withbor2 x hΓ hx hside hf₁ hf₂ => exact .withbor2 x (deadP_append h' hΓ) hx hside hf₁ hf₂
  | withbor3 x hΓ hx hf₁ hf₂ => exact .withbor3 x (deadP_append h' hΓ) hx hf₁ hf₂
  | withload x hΓ hx hf₁ hf₂ => exact .withload x (deadP_append h' hΓ) hx hf₁ hf₂
  | withswap hΓ => exact .withswap (deadP_append h' hΓ)
  | lolliE hs _ _ iha ihf => exact .lolliE (splitP_append h' hs) iha ihf
  | allEV _ hlt ih => exact .allEV ih hlt
  | ofRet _ ih => exact .ofRet ih
  | roll hA hc _ ih => exact .roll hA hc ih
  | unroll _ ih => exact .unroll ih
  | foldImm F y c R hΓ hF hG hyM hyR hR =>
      exact .foldImm F y c R (deadP_append h' hΓ) hF hG hyM hyR hR
  | foldOwn F R hΓ hF hG => exact .foldOwn F R (deadP_append h' hΓ) hF hG
  | foldReuse F R hΓ hF hG => exact .foldReuse F R (deadP_append h' hΓ) hF hG
  | nuIn hC _ ih => exact .nuIn hC ih
  | nuOut hC _ ih => exact .nuOut hC ih
  | unfoldN C S hC hΓ => exact .unfoldN C S hC (deadP_append h' hΓ)

end BoCa.Fig16.LogRel.Core

end

import Coeffects.Demand

/-!
# Coeffects — the `Imm` demand, and its parallel contraction by `copy`

`DemI U T = ∀'x ⊏ ⊓Δ. Imm 'x U ⊸ ['x] T` is a computation of `T` that demands `Imm U`.  Its
provider is `withbor` form 1 (`Ref U ⊸ DemI U T ⊸ Ref U ⊗ T`).

Unlike the `Mut` demand, it contracts **in parallel**: `parI` serves both computations from one
`Imm 'x U`, split by `copy`, at the same lifetime `'x` and with no reborrow.  So the two borrow
kinds are two coeffect structures:

| demand | sequential `⊛` | parallel `⊕` | weakening |
|---|---|---|---|
| `Mut U` | reborrow (`withbor` form 3) at `'y ⊏ 'x` (`d_seqD`) | none | `forget` |
| `Imm U` | `copy`, at `'x` (`d_parI`) | `copy`, at `'x` (`d_parI`) | `forget` |
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Coeffects
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar LSubst)
open BoCa.Programs (app2 entailsLt_of_bound)
open Optics

/-- `DemI U T = ∀'x ⊏ @b. Imm 'x U ⊸ ['x] T`. -/
abbrev demITy (U : VTy) (x : LifeVar) (b : Lifetime.Life) (T : VTy) : VTy :=
  Optics.cbTy (fun c => .imm c U) x b T

theorem imm_focusFree {V : VTy} (hV : Payload V) : FocusFree (fun c => .imm c V) :=
  fun _ _ h => h.elim id (fun h => absurd h (hV.noFree _))

theorem imm_focusInst {V : VTy} (hV : Payload V) : FocusInst (fun c => .imm c V) := by
  intro x c
  simp [VTy.instLife, VTy.applyLSub, hV.lsub, Lifetime.Life.applySub, Lifetime.assocFind]

/-- `'x ⊏ ⊓Δ` inside the callback: a demanding computation is instantiated at the provider's
own lifetime. -/
theorem entailsLt_self (Δ : LifeCtx) (x : LifeVar) :
    (FD₁ Δ x).EntailsLt (.var x) Δ.meetOfDom :=
  entailsLt_of_bound (u := Δ.meetOfDom) (by simp [Lifetime.LifeCtx.find?_extend])
    fun _ n h => ⟨n, h, le_refl n⟩

/-- `λg₁. λg₂. Λ. λm. let (m₁, m₂) = copy m; let (t₁, t₂) = (g₁ () m₁, g₂ () m₂); (t₁, t₂)`. -/
def parI : Expr :=
  .val (.lam (.val (.lam (.val (.lam (.val (.lam
    (.letpair (.app copy (.var 0))
      (.letpair (.pair (app2 (.var 5) unit' (.var 1)) (app2 (.var 4) unit' (.var 0)))
        (.pair (.var 1) (.var 0)))))))))))

/-- **Parallel contraction of the `Imm` demand.**  `parI : DemI U T₁ ⊸ DemI U T₂ ⊸
DemI U (T₁ ⊗ T₂)`: one `Imm 'x U`, copied, serves both at the same lifetime. -/
theorem d_parI {Δ : LifeCtx} {x : LifeVar} {U T₁ T₂ : VTy} (hΔ : Δ.Ok)
    (hx : Δ.find? x = none) (hU : Payload U) (hT₁ : plainV T₁ = true)
    (hT₂ : plainV T₂ = true) {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ parI (.val (.lolli (demITy U x Δ.meetOfDom T₁)
      (.lolli (demITy U x Δ.meetOfDom T₂) (demITy U x Δ.meetOfDom (.tensor T₁ T₂))))) := by
  have hD := hΓ.toP
  have hb : Δ.meetOfDom.mentions x = false :=
    Lifetime.Life.mentions_false_of_wf hx (Lifetime.meetOfDomL_wf _)
  have hG : ∀ T, plainV T = true → ¬ VFree x (demITy U x Δ.meetOfDom T) :=
    fun _ hT => cbTy_noFree (imm_focusFree hU) hT hb
  have inst : ∀ T, plainV T = true →
      VTy.instLife x (.var x) (.lolli (.imm (.var x) U) (.box (.var x) T)) =
        .lolli (.imm (.var x) U) (.box (.var x) T) :=
    fun _ hT => cbTy_inst (imm_focusInst hU) _ hT
  refine .lamV (.lamV ?_)
  refine .thunkV rfl (.allI (S := .unit) hb (fun _ _ h => hΔ.bound_mentions_false hx h) ?_
    (.ret (.lamV ?_)))
  · intro s hs hl
    simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | hs
    · exact hG _ hT₂
    · exact hG _ hT₁
    · exact dead_noLive hΓ (P := fun s => ¬ VFree x s.ty) s hs hl
  -- m = 0, Λ = 1, g₂ = 2, g₁ = 3
  refine .letpairV (A := .imm (.var x) U) (B := .imm (.var x) U)
    (.left (.dead (.right (.right (deadSplit hΓ))))) ?_ ?_
  · exact .lolliE (.left (.dead (.dead (.dead (deadSplit hΓ)))))
      (.var (.here (.cons (.cons (.cons hD))))) (.copy (.cons (.cons (.cons (.cons hD)))))
  -- m₂ = 0, m₁ = 1, m = 2, Λ = 3, g₂ = 4, g₁ = 5
  refine .letpairV (A := T₁) (B := T₂)
    (.left (.left (.dead (.dead (.left (.left (deadSplit hΓ))))))) ?_ ?_
  · refine .tensorI (.right (.left (.dead (.dead (.right (.left (deadSplit hΓ))))))) ?_ ?_
    · refine .boxE (a := .var x) (.lolliE (.dead (.left (.dead (.dead (.dead (.right
        (deadSplit hΓ))))))) (.var (.there (.here (.cons (.cons (.cons (.cons hD))))))) ?_)
      have key := CDerives.allEV (x := x) (A := .lolli (.imm (.var x) U) (.box (.var x) T₁))
        (a := .var x) (.var (.there (.there (.there (.there (.there (.here hD)))))))
        (entailsLt_self Δ x)
        (Γ := ⟨.imm (.var x) U, false⟩ :: ⟨.imm (.var x) U, false⟩ :: ⟨.imm (.var x) U, false⟩ ::
          ⟨.unit, false⟩ :: ⟨demITy U x Δ.meetOfDom T₂, false⟩ ::
          ⟨demITy U x Δ.meetOfDom T₁, true⟩ :: Γ)
      rwa [inst _ hT₁] at key
    · refine .boxE (a := .var x) (.lolliE (.left (.dead (.dead (.dead (.right (.dead
        (deadSplit hΓ))))))) (.var (.here (.cons (.cons (.cons (.cons (.cons hD))))))) ?_)
      have key := CDerives.allEV (x := x) (A := .lolli (.imm (.var x) U) (.box (.var x) T₂))
        (a := .var x) (.var (.there (.there (.there (.there (.here (.cons hD)))))))
        (entailsLt_self Δ x)
        (Γ := ⟨.imm (.var x) U, false⟩ :: ⟨.imm (.var x) U, false⟩ :: ⟨.imm (.var x) U, false⟩ ::
          ⟨.unit, false⟩ :: ⟨demITy U x Δ.meetOfDom T₂, true⟩ ::
          ⟨demITy U x Δ.meetOfDom T₁, false⟩ :: Γ)
      rwa [inst _ hT₂] at key
  -- t₂ = 0, t₁ = 1, then the consumed slots
  have hd : (Δ.extend x Δ.meetOfDom).Defines (.var x) :=
    Lifetime.LifeCtx.defines_of_wf (wf_var_self _ _ _)
  refine .boxI (.tensorI (.right (.left (.dead (.dead (.dead (.dead (.dead (.dead
    (deadSplit hΓ))))))))) (.var (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons hD)))))))))
    (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons hD)))))))))) ⟨hd, ?_⟩
  intro s hs hl
  simp only [List.mem_cons] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hs
  · exact plain_outlives hT₂
  · exact plain_outlives hT₁
  all_goals first
    | simp at hl
    | exact dead_noLive hΓ (P := fun s => VOutlives _ _ s.ty) s hs hl

end BoCa.Fig16.LogRel.Core.Coeffects

end

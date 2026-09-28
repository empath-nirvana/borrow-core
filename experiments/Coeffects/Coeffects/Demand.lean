import Optics.Lens
import Core.Stdio

/-!
# Coeffects — a demand on the context, and its contraction by reborrowing

A computation of `T` that **demands** `Mut U` of its context is, in `CDerives`, a value of the
borrow callback's type

    Dem U T  =  ∀'x ⊏ ⊓Δ. Mut 'x U ⊸ ['x] T                  (`demTy`, Optics' `cbTy`)

and its **provider** is a borrow: `withbor : Ref U ⊸ Dem U T ⊸ Ref U ⊗ T` (form 2) discharges the
demand from an owned cell, and `withbor : Mut @a U ⊸ Dem U T ⊸ Mut @a U ⊗ T` (form 3, the
reborrow) discharges it from a borrow the context already holds.

The structural rules of the demand, as closed `CDerives` derivations:

* `d_weakenD` (**weakening**, the unit of the coeffect): a computation that makes no demand is one
  that demands `Mut U` and drops it (`forget`).
* `d_seqD` (**contraction**, sequential composition): two demanding computations make one
  demanding computation. The shared demand is served to each in turn by a reborrow at an inner
  lifetime `'y ⊏ 'x`, and handed back between them. The reborrow axiom is the contraction.

There is no parallel contraction: `Mut 'x U ⊗ Mut 'x U` from one `Mut 'x U` is not a `CDerives`
derivation (the payload would be aliased mutably), so the demand's `⊕` is partial where its `⊛`
is total. `Imm`'s demand has both, by `copy` (`Imm.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Coeffects
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar LSubst)
open BoCa.Programs (app2)
open Optics

/-! ### Payloads -/

/-- What the demand needs of its payload `U`: no lifetime in it, and it outlives every lifetime.
Plain types (`plainV`), integers and opaque host types are payloads. -/
structure Payload (U : VTy) : Prop where
  noFree : ∀ z, ¬ VFree z U
  lsub : ∀ τ : LSubst, U.applyLSub τ = U
  outlives : ∀ Δ a, VOutlives Δ a U

theorem Payload.ofPlain {U : VTy} (h : plainV U = true) : Payload U :=
  ⟨fun _ => plain_noFree h, fun _ => plain_lsub h, fun _ _ => plain_outlives h⟩

theorem Payload.opq (k : Opaque) : Payload (.opq k) :=
  ⟨fun _ => by simp [VFree], fun _ => by simp [VTy.applyLSub], fun _ _ => .opq⟩

theorem mut_focusFree' {U : VTy} (hU : Payload U) : FocusFree (fun c => .mut c U) :=
  fun _ _ h => h.elim id (fun h => absurd h (hU.noFree _))

theorem mut_focusInst' {U : VTy} (hU : Payload U) : FocusInst (fun c => .mut c U) := by
  intro x c
  simp [VTy.instLife, VTy.applyLSub, hU.lsub, Lifetime.Life.applySub, Lifetime.assocFind]

/-! ### The demand type -/

/-- `Dem U T = ∀'x ⊏ @b. Mut 'x U ⊸ ['x] T`: a computation of `T` demanding `Mut U`. -/
abbrev demTy (U : VTy) (x : LifeVar) (b : Lifetime.Life) (T : VTy) : VTy :=
  Optics.cbTy (fun c => .mut c U) x b T

/-- `Λ. λv. g () v` with `g` at index `k` outside the two binders: a demanding computation
passed on at an inner lifetime. -/
def innerAt (k : Nat) : Expr := .val (.lam (.val (.lam (app2 (.var (k + 2)) unit' (.var 0)))))

/-- The reborrow of the demand at index `i` for the demanding computation at index `k`:
`withbor mᵢ (Λ. λv. gₖ () v)`. -/
def rebAt (i k : Nat) : Expr := app2 withbor (.var i) (innerAt k)

/-! ### Context facts -/

/-- In a context with exactly one live slot, every live slot has that slot's type. -/
theorem solo_live {Γ : Ctx VTy} {j : Nat} {A : VTy} (h : Ctx.Solo Γ j A) :
    ∀ s ∈ Γ, s.live = true → s.ty = A := by
  induction h with
  | here hd =>
      intro s hs hl
      rcases List.mem_cons.mp hs with rfl | hs
      · rfl
      · exact dead_noLive hd (P := fun s => s.ty = _) s hs hl
  | there _ ih =>
      intro s hs hl
      rcases List.mem_cons.mp hs with rfl | hs
      · simp at hl
      · exact ih s hs hl

theorem freshIn₁ {Δ : LifeCtx} {x y : LifeVar} (hy : Δ.find? y = none) (hxy : x ≠ y) :
    (FD₁ Δ x).find? y = none := by
  simp [Lifetime.LifeCtx.find?_extend, hy, hxy]

/-! ### One reborrow -/

/-- **The reborrow step.**  At `Δ, 'x ⊏ ⊓Δ`, with the demand `m : Mut 'x U` on one side of a
split and a demanding computation `g : Dem U T` (alone) on the other, `withbor m (Λ. λv. g () v)`
serves `g` at a fresh `'y ⊏ ⊓(Δ, 'x)` and hands `m` back: `Mut 'x U ⊗ T`. -/
theorem d_rebAt {Δ : LifeCtx} {x y : LifeVar} {U T : VTy} (hΔ : Δ.Ok)
    (hx : Δ.find? x = none) (hy : Δ.find? y = none) (hxy : x ≠ y)
    (hU : Payload U) (hT : plainV T = true)
    {Γ Γg Γm : Ctx VTy} {i k : Nat} (hs : Ctx.SplitP Γ Γg Γm)
    (hg : Ctx.Solo Γg k (demTy U x Δ.meetOfDom T)) (hm : Ctx.SoloP Γm i (.mut (.var x) U)) :
    CDerives (FD₁ Δ x) Γ (rebAt i k) (.val (.tensor (.mut (.var x) U) T)) := by
  have hy₁ := freshIn₁ hy hxy
  have hok₁ : (FD₁ Δ x).Ok := hΔ.extend hx (Lifetime.meetOfDomL_wf Δ.entries)
  refine .lolliE hs ?_ (.lolliE (splitP_left_all Γm) (.var hm)
    (.withbor3 y (kill_dead Γm).toP hy₁ (hU.noFree _) (plain_noFree hT)))
  -- the inner callback, at `Δ, 'x, 'y ⊏ ⊓(Δ, 'x)`
  refine .thunkV rfl (.allI (S := .unit)
    (Lifetime.Life.mentions_false_of_wf hy₁ (Lifetime.meetOfDomL_wf _))
    (fun _ _ h => hok₁.bound_mentions_false hy₁ h) ?_ (.ret (.lamV ?_)))
  · intro s hsΓ hl
    rw [solo_live hg s hsΓ hl]
    exact cbTy_noFree (mut_focusFree' hU) hT
      (Lifetime.Life.mentions_false_of_wf hy (Lifetime.meetOfDomL_wf _))
  refine .lolliE (.left (.dead (splitP_right_all Γg))) (.var (.here (.cons (kill_dead Γg).toP))) ?_
  have key := CDerives.allEV (x := x) (A := .lolli (.mut (.var x) U) (.box (.var x) T))
    (a := .var y) (Γ := ⟨.mut (.var y) U, false⟩ :: ⟨.unit, false⟩ :: Γg)
    (.var (.there (.there hg.toP))) (entailsLt_inner Δ x y)
  rwa [cbTy_inst (mut_focusInst' hU) _ hT] at key

/-! ### Weakening -/

/-- `Λ. λm. forget m; t`: a computation of `t` that drops the demand. -/
def weakenD (t : Expr) : Expr := .val (.lam (.val (.lam (.seq (.app forget (.var 0)) t))))

/-- **Weakening.**  A value `t : T` that makes no demand, at every context, is a computation of
`Dem U T`. -/
theorem d_weakenD {Δ : LifeCtx} {x : LifeVar} {U T : VTy} (hΔ : Δ.Ok) (hx : Δ.find? x = none)
    {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {t : Expr}
    (ht : ∀ Γ' : Ctx VTy, Ctx.Dead Γ' → CDerives (FD₁ Δ x) Γ' t (.val T)) :
    CDerives Δ Γ (weakenD t) (.val (demTy U x Δ.meetOfDom T)) := by
  refine .thunkV rfl (.allI (S := .unit)
    (Lifetime.Life.mentions_false_of_wf hx (Lifetime.meetOfDomL_wf _))
    (fun _ _ h => hΔ.bound_mentions_false hx h) (fun s hs hl => absurd hl (by
      have := dead_noLive hΓ (P := fun _ => False) s hs; tauto)) (.ret (.lamV ?_)))
  refine .seqV (.left (.dead (deadSplit hΓ))) ?_ ?_
  · exact .lolliE (.left (.dead (deadSplit hΓ))) (.var (.here (.cons hΓ.toP)))
      (.forgetMut (.cons (.cons hΓ.toP)))
  · exact .boxI (ht _ (.cons (.cons hΓ)))
      ⟨Lifetime.LifeCtx.defines_of_wf (wf_var_self _ _ _),
        fun s hs hl => absurd hl (by
          have := dead_noLive (Ctx.Dead.cons (Ctx.Dead.cons hΓ)) (P := fun _ => False) s hs
          tauto)⟩

/-! ### Contraction -/

/-- `λg₁. λg₂. Λ. λm. let (m₁, t₁) = withbor m (Λ. λv. g₁ () v);
let (m₂, t₂) = withbor m₁ (Λ. λv. g₂ () v); forget m₂; (t₁, t₂)`. -/
def seqD : Expr :=
  .val (.lam (.val (.lam (.val (.lam (.val (.lam
    (.letpair (rebAt 0 3)
      (.letpair (rebAt 1 4)
        (.seq (.app forget (.var 1)) (.pair (.var 2) (.var 0))))))))))))

/-- **Contraction.**  `seqD : Dem U T₁ ⊸ Dem U T₂ ⊸ Dem U (T₁ ⊗ T₂)`: two computations that
demand `Mut U` are one computation that demands it once.  The demand is served to each by a
reborrow and handed back between them. -/
theorem d_seqD {Δ : LifeCtx} {x y : LifeVar} {U T₁ T₂ : VTy} (hΔ : Δ.Ok)
    (hx : Δ.find? x = none) (hy : Δ.find? y = none) (hxy : x ≠ y)
    (hU : Payload U) (hT₁ : plainV T₁ = true) (hT₂ : plainV T₂ = true)
    {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ seqD (.val (.lolli (demTy U x Δ.meetOfDom T₁)
      (.lolli (demTy U x Δ.meetOfDom T₂) (demTy U x Δ.meetOfDom (.tensor T₁ T₂))))) := by
  have hD := hΓ.toP
  have hb : Δ.meetOfDom.mentions x = false :=
    Lifetime.Life.mentions_false_of_wf hx (Lifetime.meetOfDomL_wf _)
  have hG : ∀ T, plainV T = true → ¬ VFree x (demTy U x Δ.meetOfDom T) :=
    fun _ hT => cbTy_noFree (mut_focusFree' hU) hT hb
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
  refine .letpairV (A := .mut (.var x) U) (B := T₁)
    (.left (.dead (.right (.left (deadSplit hΓ))))) ?_ ?_
  · exact d_rebAt hΔ hx hy hxy hU hT₁
      (.right (.dead (.dead (.left (deadSplit hΓ)))))
      (.there (.there (.there (.here hΓ))))
      (.here (.cons (.cons (.cons hD))))
  -- t₁ = 0, m₁ = 1, m = 2, Λ = 3, g₂ = 4, g₁ = 5
  refine .letpairV (A := .mut (.var x) U) (B := T₂)
    (.right (.left (.dead (.dead (.left (.dead (deadSplit hΓ))))))) ?_ ?_
  · exact d_rebAt hΔ hx hy hxy hU hT₂
      (.dead (.right (.dead (.dead (.left (.dead (deadSplit hΓ)))))))
      (.there (.there (.there (.there (.here (.cons hΓ))))))
      (.there (.here (.cons (.cons (.cons (.cons hD))))))
  -- t₂ = 0, m₂ = 1, t₁ = 2, m₁ = 3, m = 4, Λ = 5, g₂ = 6, g₁ = 7
  refine .seqV (.right (.left (.right (.dead (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))))
    ?_ ?_
  · exact .lolliE (.dead (.left (.dead (.dead (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))))
      (.var (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons hD)))))))))
      (.forgetMut (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons hD)))))))))
  · have hd : (Δ.extend x Δ.meetOfDom).Defines (.var x) :=
      Lifetime.LifeCtx.defines_of_wf (wf_var_self _ _ _)
    refine .boxI (.tensorI (.right (.dead (.left (.dead (.dead (.dead (.dead (.dead
      (deadSplit hΓ))))))))) (.var (.there (.there (.here (.cons (.cons (.cons (.cons (.cons hD))))))))) (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons hD))))))))))
      ⟨hd, ?_⟩
    intro s hs hl
    simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hs
    · exact plain_outlives hT₂
    · simp at hl
    · exact plain_outlives hT₁
    all_goals first
      | simp at hl
      | exact dead_noLive hΓ (P := fun s => VOutlives _ _ s.ty) s hs hl

end BoCa.Fig16.LogRel.Core.Coeffects

end

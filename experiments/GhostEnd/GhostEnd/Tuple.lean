import GhostEnd.TypedD
import GhostEnd.Branch

/-!
# GhostEnd — the lend carried in a tuple across a yield, every hypothesis discharged

    withbor ℓ (Λ. λm. return (m, ()) to z.
                      perform yield 1 to u.
                      u; let (m′, w) = z in w; return forget to fg. fg m′ to r. return r)

at the row `{yield : I32 ↠ 1}`, linear and resuming. The borrow `m` is moved into the pair
`z : Mut 'x 1 ⊗ 1` before the yield, so at the stop the frame holds the lend inside a value and
`m`'s own slot is dead. `StopSafe` does not admit this frame. `LOk` does: the pair's first
component is the view at `ℓ`, dropped at the stop and re-lent at the resumption, and the second
is data.

`tuple_spans_yield` is `withbor_of_rbodyT` with every hypothesis discharged.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd.Tuple
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (performE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd.Instance (yieldOp)
open GhostEnd.Branch (mS deadOf deadPD hbx hΔx hS hT hf yieldE)

/-- The pair's type: the borrow and a unit. -/
abbrev A₁ : VTy := .tensor (.mut (.var 0) .unit) .unit

/-- `return (m, ())`. -/
def mk : Expr := .pair (.var 0) (.val Val.unit)

/-- `return forget to fg. fg m′ to r. return r`, `m′` at index `1`. -/
def nf : Expr := bindE forget (bindE (.app (.var 0) (.var 2)) (.var 0))

/-- `u; let (m′, w) = z in w; N_f`. -/
def after : Expr := .seq (.var 0) (.letpair (.var 1) (.seq (.var 0) nf))

/-- The borrower's body. -/
def body : Expr := bindE mk (bindE (yieldE 1) after)

theorem d_mk : CDerives Δ₁ ([] ++ [mS true]) mk (.comp (.ret A₁)) :=
  .ret (.tensorI (.left .nil) (.var (.here .nil)) (.unitI (.cons .nil)))

/-- The context of `N_f`: `w` dead, `m′` live, then `u`, `z`, `m` dead. -/
abbrev Γnf : Ctx VTy :=
  [⟨.unit, false⟩, ⟨.mut (.var 0) .unit, true⟩, ⟨.unit, false⟩, ⟨A₁, false⟩, mS false]

theorem d_nf : CDerives Δ₁ Γnf nf (.comp (.ret (.box (.var 0) .unit))) :=
  .bind (.dead (.right (.dead (.dead (.dead .nil)))))
    (.ret (.forgetMut (a := .var 0) (A := .unit) (.cons (.cons (.cons (.cons (.cons .nil)))))))
    (.bind (.left (.dead (.left (.dead (.dead (.dead .nil))))))
      (.app (.left (.dead (.right (.dead (.dead (.dead .nil))))))
        (.force (.here (.cons (.cons (.cons (.cons (.cons .nil)))))))
        (.there (.there (.here (.cons (.cons (.cons .nil)))))))
      (.ret (.boxI (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons .nil))))))))
        (CtxOutlives.solo (LifeCtx.defines_of_wf rfl) .unit
          (.cons (.cons (.cons (.cons (.cons (.cons .nil))))))))))

theorem d_after :
    CDerives Δ₁ ([⟨.unit, true⟩, ⟨A₁, true⟩] ++ [mS false]) after
      (.comp (.ret (.box (.var 0) .unit))) :=
  .unitE (.left (.right (.dead .nil))) (.var (.here (.cons (.cons .nil))))
    (.tensorE (.dead (.left (.dead .nil))) (.var (.there (.here (.cons .nil))))
      (.unitE (.left (.right (.dead (.dead (.dead .nil)))))
        (.var (.here (.cons (.cons (.cons (.cons .nil)))))) d_nf))

abbrev RB (Γ : Ctx VTy) (ml : Bool) (E : Expr) (A : VTy) : Prop :=
  RBodyT LifeCtx.empty 0 LifeCtx.empty.meetOfDom .unit [yieldOp] Γ ml E A

/-- The pair may span the yield: its first component is `Mut 'x 1`, its second is data. -/
theorem lok_A₁ : LOk LifeCtx.empty 0 LifeCtx.empty.meetOfDom .unit A₁ :=
  ⟨Or.inl rfl, Or.inr ⟨by simp [VFree], .unit⟩⟩

theorem rb_mid : RB [⟨A₁, true⟩] false (bindE (yieldE 1) after) (.box (.var 0) .unit) :=
  rbodyT_let hbx hΔx hT hS (Γ₁ := [⟨A₁, false⟩]) (Γ₂ := [⟨A₁, true⟩]) (ml₁ := false)
    (ml₂ := false) (A₁ := .unit) (.right (.dead .nil)) rfl rfl
    (fun s hs _ => by simp only [List.mem_singleton] at hs; subst hs; exact lok_A₁)
    (rbodyT_perform hbx hΔx hS hf (fundamentalC (.lit (.i32 1) (deadPD [A₁]))))
    (rbodyT_ret hbx hΔx (fundamentalC d_after))

theorem rb_body : RB [] true body (.box (.var 0) .unit) :=
  rbodyT_let hbx hΔx hT hS (Γ₁ := []) (Γ₂ := []) (ml₁ := true) (ml₂ := false) (A₁ := A₁)
    (.left .nil) rfl rfl (fun _ hs => by simp at hs)
    (rbodyT_ret hbx hΔx (fundamentalC d_mk)) rb_mid

/-- **The lend carried in a tuple across a yield.** From `ℓ ↦ v ⋆ 𝒱⟦1⟧(v)`, the program is in
`𝒞⟦F_{yield} (Ref 1 ⊗ 1)⟧`, at every assignment and record list. -/
theorem tuple_spans_yield (δ : LSub) (l : BoCa.Loc) (v : Val) (ls : List SRec) :
    Entails (ptoOwn l v ⋆ vC true .unit ls δ v)
      (cC (CTy.effOf [yieldOp] (.tensor (.ref .unit) .unit)) ls δ
        (.app (.app withbor (.val (.loc l))) (.val ⟨.lam (.lam body), .lam⟩))) := by
  have hδ : LifeCtx.empty.Models δ := fun x u h => by
    simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at h
  obtain ⟨β, hβ⟩ : ∃ β, LifeCtx.empty.meetOfDom.interp δ = some β :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf LifeCtx.empty.entries)
  refine withbor_of_rbodyT hδ hβ hT (by simp [VFree]) (βP := ⊤) ?_ (by decide) (by decide) rb_body l v ls
  intro ls w σ h
  rw [h.1]; exact ResU.inStratum_empty _

end GhostEnd.Tuple

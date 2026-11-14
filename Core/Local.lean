import Core.Splits

/-!
# Plain local cells, derived from allocation, lending and free `[spec §80]`

The owner never reaches the callback. The normal result returns the final contents and the
callback answer. There is no new judgment or machine rule.
-/

noncomputable section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Lifetime (LifeCtx LifeVar)

def withlocalTy (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) : VTy :=
  .lolli A (.lolli (.all x bnd (.lolli (.mut (.var x) A) (.box (.var x) B))) (.tensor A B))

def withlocalE : Expr := .val (.lam (.val (.lam
  (.letpair (.app (.app withbor (.app (.val (.prim .alloc)) (.var 1))) (.var 0))
    (.pair (.app (.val (.prim .free)) (.var 1)) (.var 0))))))

theorem withlocal_closed : closedAt 0 withlocalE = true := rfl

theorem withlocal_wf {Δ : LifeCtx} {Γ : Ctx VTy} (x : LifeVar) (A B : VTy)
    (hΓ : Ctx.Dead Γ) (hx : Δ.find? x = none)
    (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hA : ¬ VFree x A) (hB : ¬ VFree x B) :
    CDerives Δ Γ withlocalE (.val (withlocalTy x Δ.meetOfDom A B)) := by
  unfold withlocalE withlocalTy
  apply CDerives.lamV
  apply CDerives.lamV
  refine letW (A := .ref A) (B := B) ?_ ?_
  · exact appW (.var (by csolo))
      (appW (appW (.var (by csolo)) (.alloc (by cdead)))
        (.withbor2 x (by cdead) hx hside hA hB))
  · exact pairW (appW (.var (by csolo)) (.free (by cdead))) (.var (by csolo))

end BoCa.Fig16.LogRel.Core
end

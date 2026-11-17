import Core.Splits
import Core.Tied

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

/-! ### The local family `[spec §80]`

The checker's typed term has one node and one rule for every local: `TExpr.withlocal` and
`TDerivesAt.withlocal`/`TDerivesP.withlocal`, indexed by a `LocalKind`. A kind is data: it
selects the side condition (`LocalOK`), the result type (`localTy`), the erased core term
(`localE`) and the derived kernel lemma the rule erases to (`LocalKind.wf`). Adding a kind adds a
constructor and a clause to each function here; the rule, the node and their pinned templates
(`scripts/pin/`) do not change. -/

/-- The kinds of scoped local. `[spec §80]` -/
inductive LocalKind where
  /-- The plain local (`withlocalE`). -/
  | plain
  deriving DecidableEq, Repr, Inhabited

/-- The kind's side condition at the lifetime context `Δ`, the callback's fresh lifetime `x`,
the contents `A` and the callback's answer `B`. `[spec §80]` -/
def LocalOK : LocalKind → LifeCtx → LifeVar → VTy → VTy → Prop
  | .plain, Δ, x, A, B =>
      Δ.find? x = none ∧ (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) ∧ ¬ VFree x A ∧ ¬ VFree x B

/-- The kind's type at `Δ`. `[spec §80]` -/
def localTy : LocalKind → LifeCtx → LifeVar → VTy → VTy → VTy
  | .plain, Δ, x, A, B => withlocalTy x Δ.meetOfDom A B

/-- The kind's core term. `[spec §80]` -/
def localE : LocalKind → Expr
  | .plain => withlocalE

theorem LocalKind.closed : ∀ k : LocalKind, closedAt 0 (localE k) = true
  | .plain => withlocal_closed

theorem LocalKind.effFree : ∀ k : LocalKind, (localE k).effFree = true
  | .plain => rfl

/-- Every kind's term has its type, by the kind's derived kernel lemma. `[spec §80]` -/
theorem LocalKind.wf {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {A B : VTy} :
    ∀ k : LocalKind, Ctx.Dead Γ → LocalOK k Δ x A B →
      CDerives Δ Γ (localE k) (.val (localTy k Δ x A B))
  | .plain, hΓ, ⟨hx, hside, hA, hB⟩ => withlocal_wf x A B hΓ hx hside hA hB

end BoCa.Fig16.LogRel.Core
end

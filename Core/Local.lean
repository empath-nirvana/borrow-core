import Core.Splits
import Core.Tied
import Core.Consume
import Core.EffBorrow

/-!
# Local cells, derived from allocation, lending and free `[spec §80]`

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

/-! ### The unwinding local `[spec §80]`

The callback is at a row of abortive operations (`Row.Unwind`). When it unwinds, the finaliser
`localFin` frees the owner and drops its persistent contents. The lend is `withbor2UD` at the
finaliser's row `[]`. -/

/-- `withlocalu : A ⊸ U(∀'x ⊏ @b. Mut 'x A ⊸ F_Σ_M(['x] B)) ⊸ F_Σ(A ⊗ B)`. -/
def withlocalUTy (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (SM S : Row) : VTy :=
  .thunk (.arr A (.arr (cbUTy x bnd (.mut (.var x) A) B SM) (CTy.effOf S (.tensor A B))))

/-- The unwind finaliser: `λr. forget (free r)`. -/
def localFin : Expr := .val (.lam (.app forget (.app (.val (.prim .free)) (.var 0))))

/-- `λv. λcb. r ← alloc v; w ← withborU localFin; (r, b) ← w r cb; (free r, b)`. -/
def withlocalUE : Expr := .val (.lam (.val (.lam
  (bindE (.app (.val (.prim .alloc)) (.var 1))
    (bindE (withborUE localFin)
      (bindE (.app (.app (.var 0) (.var 1)) (.var 2))
        (.letpair (.var 0) (.pair (.app (.val (.prim .free)) (.var 1)) (.var 0)))))))))

theorem localFin_wf {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hA : A.Persistent) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ localFin (.val (.lolli (.ref A) .unit)) :=
  .lamV (appW (appW (.var (by csolo)) (.free (by cdead))) (release_persistent hA (by cdead)))

theorem localFin_closed : closedAt 0 localFin = true := rfl

theorem withlocalU_closed : closedAt 0 withlocalUE = true := by
  have h : closedAt 3 (withborUE localFin) = true := withborUE_closedAt rfl
  simp [withlocalUE, bindE, closedAt, Expr.val, Val.lam, Val.prim, h]

theorem withlocalU_wf {Δ : LifeCtx} {Γ : Ctx VTy} (x : LifeVar) (A B : VTy) {SM S : Row}
    (hΓ : Ctx.Dead Γ) (hx : Δ.find? x = none)
    (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hA : ¬ VFree x A) (hB : ¬ VFree x B) (hP : A.Persistent)
    (hS : SM.Unwind x) (hMS : RowLe SM S) (hSv : Row.divB S = false) :
    CDerives Δ Γ withlocalUE (.val (withlocalUTy x Δ.meetOfDom A B SM S)) := by
  unfold withlocalUE withlocalUTy
  refine .thunkV rfl (.lam (.lam ?_))
  refine .bind (A := .ref A) (part_split (.app (.val (.prim .alloc)) (.var 1)) 0 _).toP
    (.ret (appW (.var (by csolo)) (.alloc (by cdead)))) ?_
  refine .bind (part_split (withborUE localFin) 0 _).toP
    (.ret (.withbor2UD (SD := []) x (by cdead) hx hside hA hB hS hMS (RowLe.nil S) hSv
      (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) (localFin_wf hP (by cdead)))) ?_
  refine .effLet (A := .tensor (.ref A) B)
    (part_split (.app (.app (.var 0) (.var 1)) (.var 2)) 0 _).toP
    (fun _ => fun s hs hl => dead_noLive (P := fun s => s.ty.OwnFree) (by cdead) s hs hl)
    (fun _ => dead_noLive (P := fun s => ∃ A, s.ty = .bang A) (by cdead)) ?_ ?_
  · exact .app (part_split (.app (.var 0) (.var 1)) 0 _).toP
      (.app (part_split (.var 0) 0 _).toP (.force (T := withbor2UTyD x Δ.meetOfDom A B SM S)
        (C := .arr (.ref A) (.arr (cbUTy x Δ.meetOfDom (.mut (.var x) A) B SM)
          (CTy.effOf S (.tensor (.ref A) B)))) (by csolo) rfl) (by csolo))
      (by csolo)
  · exact .effSub (RowLe.nil S) (.ret (letW (.var (by csolo))
      (pairW (appW (.var (by csolo)) (.free (by cdead))) (.var (by csolo)))))

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
  /-- The unwinding local (`withlocalUE`): the callback at the abortive row `SM`, the scope at
  `S`. -/
  | unwind (SM S : Row)
  deriving Inhabited

/-- The side condition every kind shares, plain's whole: `x` fresh, `Δ ⊢ A ⊒ @b` for some
defined `@b`, and `x` free in neither `A` nor `B`. `[spec §80]` -/
abbrev LocalBase (Δ : LifeCtx) (x : LifeVar) (A B : VTy) : Prop :=
  Δ.find? x = none ∧ (∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A) ∧ ¬ VFree x A ∧ ¬ VFree x B

/-- The kind's side condition at the lifetime context `Δ`, the callback's fresh lifetime `x`,
the contents `A` and the callback's answer `B`: `LocalBase` and the kind's own. `[spec §80]` -/
def LocalOK : LocalKind → LifeCtx → LifeVar → VTy → VTy → Prop
  | .plain, Δ, x, A, B => LocalBase Δ x A B
  | .unwind SM S, Δ, x, A, B =>
      LocalBase Δ x A B ∧ A.Persistent ∧ SM.Unwind x ∧ RowLe SM S ∧ Row.divB S = false

/-- The kind's type at `Δ`. `[spec §80]` -/
def localTy : LocalKind → LifeCtx → LifeVar → VTy → VTy → VTy
  | .plain, Δ, x, A, B => withlocalTy x Δ.meetOfDom A B
  | .unwind SM S, Δ, x, A, B => withlocalUTy x Δ.meetOfDom A B SM S

/-- The kind's core term. `[spec §80]` -/
def localE : LocalKind → Expr
  | .plain => withlocalE
  | .unwind .. => withlocalUE

theorem LocalKind.closed : ∀ k : LocalKind, closedAt 0 (localE k) = true
  | .plain => withlocal_closed
  | .unwind .. => withlocalU_closed

theorem LocalKind.effFree : ∀ k : LocalKind, (localE k).effFree = true
  | .plain => rfl
  | .unwind .. => rfl

/-- Every kind's term has its type, by the kind's derived kernel lemma. `[spec §80]` -/
theorem LocalKind.wf {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {A B : VTy} :
    ∀ k : LocalKind, Ctx.Dead Γ → LocalOK k Δ x A B →
      CDerives Δ Γ (localE k) (.val (localTy k Δ x A B))
  | .plain, hΓ, ⟨hx, hside, hA, hB⟩ => withlocal_wf x A B hΓ hx hside hA hB
  | .unwind .., hΓ, ⟨⟨hx, hside, hA, hB⟩, hP, hS, hMS, hSv⟩ =>
      withlocalU_wf x A B hΓ hx hside hA hB hP hS hMS hSv

end BoCa.Fig16.LogRel.Core
end

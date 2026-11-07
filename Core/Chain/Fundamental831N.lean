import Core.Chain.Borrow834N
import Core.Chain.Rules834N
import Core.CountFold
import Core.Chain.Eff835N
import Core.Chain.Fam836N
import Core.Chain.FamCancel836N
import Core.Chain.FamFrame836N
import Core.Chain.FamImm836N
import Core.Chain.FamNew836N
import Core.Chain.FamSlice836N
import Core.Chain.FamSwap836N
import Core.Chain.FoldG836N
import Core.Chain.FoldImm836N
import Core.Chain.Fuel835N
import Core.Chain.HandleL835N
import Core.Chain.HandleT835N
import Core.Chain.ImmLend833N
import Core.Chain.Iter835N
import Core.Chain.Let835N
import Core.Chain.Mu836N
import Core.Chain.Nu837N
import Core.Chain.Rules834N
import Core.Chain.Iter835N
import Core.Chain.Unwind833N
import Core.Fundamental

/-!
# Adapters for the fundamental property's induction  `[spec §62]`

`docs/new-core/scope-831-interface.md` §14. Small facts the rules at `SemJN` (`RulesKW835N`,
`FamOpsKW835N`) and the induction on `CDerives` (`fundamentalN_all`, `FundamentalKW835N`) read:
`liveWithin_dead_ctx` (a consumed context lives within every value list), `awaitE_closed`, and
`swap` as a value (`swapV`, `swapAt`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (jdgC)
open BoCa.BoLo (Heap Kont Head eLoad eStore)

/-! ### Adapters -/

private theorem substAll_app_val (γ : List Val) (M : Expr) (w : Val)
    (hw : ∀ k, Expr.psub k γ w.val = w.val) :
    substAll γ (.app M (.val w)) = .app (substAll γ M) (.val w) := by
  show Expr.app (Expr.psub 0 γ M) (Expr.psub 0 γ w.val) = _
  rw [hw]; rfl

/-- A consumed context lives within every value list. -/
theorem liveWithin_dead_ctx : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → ∀ γ : List Val, Ctx.LiveWithin Γ γ := by
  intro Γ hd
  induction hd with
  | nil => intro γ; simp
  | cons _ ih => intro γ; cases γ with
    | nil => exact ⟨by simp, ih []⟩
    | cons v γ => exact ih γ

/-- `await_n` is closed. -/
theorem awaitE_closed {n : UInt32} : closedAt 0 (awaitE n) = true := rfl

private theorem substAll_withPairN (γ : List Val) (M N : Expr) :
    substAll γ (withPair M N) =
      .val (.lam (.case (.var 0) (.seq (.var 0) (Expr.psub 2 γ M))
        (.seq (.var 0) (Expr.psub 2 γ N)))) := by
  show Expr.psub 0 γ (.lam _) = _
  simp [Expr.psub]

private theorem withBody_substN (γ : List Val) (M N : Expr) (s : Val) :
    (Expr.case (.var 0) (.seq (.var 0) (Expr.psub 2 γ M)) (.seq (.var 0) (Expr.psub 2 γ N))).subst 0 s
      = .case (.val s) (.seq (.var 0) (Expr.psub 1 (s :: γ) M))
          (.seq (.var 0) (Expr.psub 1 (s :: γ) N)) := by
  simp [Expr.subst, Expr.psub_cons 1 s γ]

private theorem seq_subst_unitN (e : Expr) :
    (Expr.seq (.var 0) e).subst 0 Val.unit = .seq (.val .unit) (e.subst 0 Val.unit) := by
  simp [Expr.subst]

/-- `swap` as a value. -/
def swapV : Val := ⟨swap, .lam⟩

/-- The body of `swap` at the source `ℓ`, after the first β step. -/
def swapAt (l : Loc) : Val :=
  Val.lam (elet (eLoad l) (.seq (.app (.app store' (.val (.loc l))) BoCa.v1)
    (.pair (.val (.loc l)) BoCa.v0)))

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end

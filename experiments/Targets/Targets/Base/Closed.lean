import Core.Fundamental
import Targets.Base.Fill

/-!
# Base — a typed term is closed at its context

`closedAt_of_derives`: a term today's kernel types at the context `Γ` has every free variable below
`Γ.length`, so a closed program is closed.  Induction on `CDerives`; each rule's term is built from
its premises' terms under the binders its premises' contexts extend by, and its constants are closed
(`withborUE_closed`, `foldImmV_closed`, `unfoldV_closed`, …).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (performE raiseE)
open BoCa.Lifetime (LifeCtx)

/-- A split keeps the context's length on both sides. -/
theorem splitP_length {Γ Γ₁ Γ₂ : Ctx VTy} (h : Ctx.SplitP Γ Γ₁ Γ₂) :
    Γ₁.length = Γ.length ∧ Γ₂.length = Γ.length := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | left _ ih | right _ ih | dead _ ih | dup _ _ ih =>
      simp only [List.length_cons]; exact ⟨by rw [ih.1], by rw [ih.2]⟩

/-- A variable a context is solo at is below its length. -/
theorem soloP_lt {Γ : Ctx VTy} {i : Nat} {T : VTy} (h : Ctx.SoloP Γ i T) : i < Γ.length := by
  induction h with
  | here => simp
  | there _ ih | skip _ _ ih => simp only [List.length_cons]; omega

/-- A term closed at `0` is closed at every bound. -/
theorem closedAt_of_zero {e : Expr} (h : closedAt 0 e = true) (k : Nat) : closedAt k e = true :=
  closedAt_mono e h (Nat.zero_le k)

/-- **A typed term is closed at its context.** -/
theorem closedAt_of_derives {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerives Δ Γ e j) : closedAt Γ.length e = true := by
  induction h with
  | var h => simpa [closedAt] using soloP_lt h
  | force h =>
      rename_i C
      have := soloP_lt h
      cases C <;> simp [forceE, closedAt, Expr.val, Val.unit, this]
  | tensorI hs _ _ ih₁ ih₂ =>
      rw [(splitP_length hs).1] at ih₁; rw [(splitP_length hs).2] at ih₂
      simp [closedAt, ih₁, ih₂]
  | thunkF _ ih | lam _ ih | allI _ _ _ _ ih | bangThunkF _ _ ih =>
      simpa [closedAt, Expr.val, Val.lam] using ih
  | bind hs _ _ ihM ihN | effLet hs _ _ _ _ ihM ihN =>
      rw [(splitP_length hs).1] at ihM; rw [List.length_cons, (splitP_length hs).2] at ihN
      simp [closedAt, Expr.val, Val.lam, ihM, ihN]
  | app hs _ hx ihM =>
      rw [(splitP_length hs).1] at ihM
      have := soloP_lt hx; rw [(splitP_length hs).2] at this
      simp [closedAt, ihM, this]
  | withI _ _ ihM ihN =>
      simp only [List.length_cons] at ihM ihN
      simp [withPair, closedAt, Expr.val, Val.lam, ihM, ihN]
  | proj₁ _ ih | proj₂ _ ih | allE _ _ ih | allEV _ _ ih =>
      simp [closedAt, Expr.val, Val.inj₁, Val.inj₂, Val.unit, ih]
  | unitE hs _ _ ihV ihM | lolliE hs _ _ ihV ihM =>
      rw [(splitP_length hs).1] at ihV; rw [(splitP_length hs).2] at ihM
      simp [closedAt, ihV, ihM]
  | tensorE hs _ _ ihV ihM =>
      rw [(splitP_length hs).1] at ihV; rw [List.length_cons, List.length_cons,
        (splitP_length hs).2] at ihM
      simp [closedAt, ihV, ihM]
  | sumE hs _ _ _ ihV ih₁ ih₂ =>
      rw [(splitP_length hs).1] at ihV
      rw [List.length_cons, (splitP_length hs).2] at ih₁ ih₂
      simp [closedAt, ihV, ih₁, ih₂]
  | zeroE hs _ ihV =>
      rw [(splitP_length hs).1] at ihV
      simp [absurdE, closedAt, ihV]
  | withbor1U _ _ _ _ _ _ _ hdc _ _ | withbor2U _ _ _ _ _ _ _ hdc _ _
  | withbor3U _ _ _ _ _ _ hdc _ _ | sliceBorrowMU _ _ _ _ _ _ _ hdc _ _
  | sliceBorrowIU _ _ _ _ _ _ _ _ hdc _ _ =>
      exact closedAt_of_zero (withborUE_closed hdc) _
  | foldImm => exact closedAt_of_zero (foldImmV_closed _) _
  | foldOwn => exact closedAt_of_zero (foldOwnV_closed _) _
  | foldReuse => exact closedAt_of_zero (foldReuseV_closed _) _
  | unfoldN => exact closedAt_of_zero (unfoldV_closed _) _
  | effPerform _ _ _ ih | effRaise _ _ _ _ ih =>
      simp [performE, raiseE, opArgE, closedAt, Expr.val, Val.prim, Val.i32, ih]
  | effThen hs _ _ _ _ _ _ ihM ihN ihD =>
      rw [(splitP_length hs).1] at ihM
      rw [List.length_cons, (splitP_length hs).2] at ihN ihD
      simp [thenE, closedAt, Expr.val, Val.prim, Val.lam, ihM, ihN, ihD]
  | effHandleV hs _ _ _ _ _ _ _ ihc ihe =>
      rw [(splitP_length hs).1] at ihc; rw [(splitP_length hs).2] at ihe
      simp [hndExpr, closedAt, Expr.val, Val.prim, Val.i32, ihc, ihe]
  | @letPoly _ Γ' N _ _ b hcl _ _ _ ihN =>
      rw [List.length_cons] at ihN
      have hN := closedAt_of_fill hcl N 0 (Γ'.length + 1) (Nat.succ_pos _) ihN
      have hb : closedAt Γ'.length (Expr.lam b) = true := closedAt_of_zero hcl _
      simp only [closedAt, Expr.val, Val.lam, Bool.and_eq_true] at hb ⊢
      exact ⟨hN, hb⟩
  | _ =>
      first
        | assumption
        | exact closedAt_of_zero rfl _

end Targets

end

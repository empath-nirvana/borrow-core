import Core.EffFin

/-!
# Spike #1105: `κ`'s cancel at its operation's cancel row alone

`cancelTy' F` drops the handler's outer row `Σ` from `cancelTy Σ F`. The handler's semantic
engine (`ewp_handle`) asks of `κ`'s cancel table `Tk` only that it be above the entry's cancel
obligation's table (`hTc`); the cancel run is `ccatch (K†[raise …])`, with no handler frame
(`kappa_cancel_subst`, `dead_hndK`), so no clause runs during it. This file checks that the two
obligations of `ewp_handle_vals` hold at the narrower table, with no condition on `F`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Spike1105
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `κ`'s cancel branch at the cancel row `F` alone. -/
def cancelTy' (F : CTy) : CTy :=
  if F.isTop then .top else CTy.effOf F.rowOf .unit

/-- `κ`'s type, its cancel branch at `cancelTy' F`. -/
def kTy' (S : Row) (R : VTy) (q : Qual) (B : VTy) (F : CTy := .ret .unit) : VTy :=
  match q with
  | .lin => .thunk (.amp (.arr B (CTy.effOf S R)) .top)
  | .cancel => .thunk (.amp (.arr B (CTy.effOf S R)) (cancelTy' F))
  | .unr => .bang (.thunk (.amp (.arr B (CTy.effOf S R)) (cancelTy' F)))

/-- The cancel table at `F` alone. -/
def cancelTabOf' (F : CTy) (δ : LSub) : Option OpTab :=
  if F.isTop then none else some (Row.tab F.rowOf δ)

/-- **Obligation 1** (`vC_kTy_of_kapRel` at the narrower table): `κ`'s relation, with its cancel
at the table of `F` alone, gives `κ` at `kTy'`. -/
theorem vC_kTy'_of_kapRel {S : Row} {R B : VTy} {q : Qual} {F : CTy} {δ : LSub} {ls : List SRec}
    {κ : Val} {ρ : WRes} (A : VTy) (n i : UInt32)
    (h : KapRel (Row.tab S δ) (fun ls v => vC true R ls δ v)
      (OpSig.ent δ ⟨n, i, q, A, B, F, false⟩) (cancelTabOf' F δ) ls κ ρ) :
    vC true (kTy' S R q B F) ls δ κ ρ := by
  obtain ⟨hu, hk⟩ := h
  have hres : ∀ ls', Ext ls ls' ρ →
      cC (.arr B (CTy.effOf S R)) ls' δ (.app κ.1 (.val (Val.inj₁ .unit))) ρ := by
    intro ls' he w σ₁ σ₂ hB hc
    exact (cC_effOf_wp S R ls' δ _ σ₂).mpr (effWp_of_ewp (Row.keyNA_of_divB δ)
      ((hk ls' he).1 w σ₁ σ₂ hB hc))
  have hcan : q ≠ .lin → ∀ ls', Ext ls ls' ρ →
      cC (cancelTy' F) ls' δ (.app κ.1 (.val (Val.inj₂ .unit))) ρ := by
    intro hq ls' he
    unfold cancelTy'
    cases hT : F.isTop
    · simp only [Bool.false_eq_true, if_false]
      refine (cC_effOf_wp _ .unit ls' δ _ ρ).mpr (effWp_of_ewp (Row.keyNA_of_divB δ)
        ((hk ls' he).2 hq _ ?_))
      simp [cancelTabOf', hT]
    · simp only [if_true]; trivial
  cases q with
  | lin => exact fun ls' he => ⟨hres ls' he, trivial⟩
  | cancel => exact fun ls' he => ⟨hres ls' he, hcan (by simp) ls' he⟩
  | unr => exact ⟨hu rfl, fun ls' he => ⟨hres ls' he, hcan (by simp) ls' he⟩⟩

/-- **Obligation 2** (`ewp_handle`'s `hTc` at the narrower table): at every capturable entry of
the handled row's name, the entry's cancel obligation's table is below `cancelTabOf' (fs j)`: it
is that table (`OpTab.Le.refl`). No condition on `fs j`: it may hold the handled name. -/
theorem hTc' {S : Row} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {n : UInt32} {δ : LSub}
    (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32) :
    ∀ i en, Row.tab (Row.ofEff n E 0 fs ++ S) δ n i = some en → en.abort = false →
      en.q ≠ .lin → ∀ Tk, cancelTabOf' (fs i.toNat) δ = some Tk →
        ∃ T₁, en.fin = some (cancelObl T₁) ∧ T₁.Le Tk := by
  intro i en hT ha hq Tk hTk
  obtain ⟨j, hj, hji, -, rfl⟩ := Row.tab_ofEff_self hnS hlen hT
  have hcap := capB_of_ent ha hq
  rw [hji] at hTk
  simp only [cancelTabOf'] at hTk
  split at hTk
  · cases hTk
  · rename_i hnT
    cases hTk
    refine ⟨Row.tab (fs j).rowOf δ, ?_, OpTab.Le.refl _⟩
    rw [OpSig.ent_fin, if_pos hcap, finObl_eq]
    simp only [hnT, Bool.false_eq_true, if_false]

/-- **Old derivations still type**: the narrow cancel is below the old one by `[sub]`. -/
theorem rowLe_cancel (S : Row) (F : CTy) : RowLe F.rowOf (F.rowOf ++ S) :=
  RowLe.of_find fun n i o hf => by rw [Row.find_append, hf, Option.some_or]

/-- At the empty cancel row the cancel is pure, at every outer row. -/
theorem cancelTy'_nil : cancelTy' (.ret .unit) = .ret .unit := rfl

end BoCa.Fig16.LogRel.Core.Spike1105

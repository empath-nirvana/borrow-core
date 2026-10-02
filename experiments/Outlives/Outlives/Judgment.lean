import Core

/-!
# Outlives — the outlives judgment with non-strict premises, and 6.60 at it

`VOutlives Δ a T` (`Core/Types.lean`, `[TR]` p. 2 rows 2.31–2.37) has three rules with a
lifetime premise, each strict: `[@b] T ⊐ @a`, `Imm @b T ⊐ @a` and `Mut @b T ⊐ @a` from
`Δ ⊨ @a ⊏ @b`. `VOutP Rb Rr a T` is the same judgment with the box rule's premise `Rb b` and
the two borrow rules' premise `Rr b`, so that

* `VOutL Δ a` (`Rb = ⊑`, `Rr = ⊏`) relaxes the box rule only, and
* `VOutLe Δ a` (`Rb = Rr = ⊑`) relaxes all three.

Each contains `VOutlives` (`VOutP.of_vOutlives`). The paper prints `⊏` at all three rules; the
relaxations here are extensions of the judgment, read against the model the paper defines.

**6.60 at each.** `vC_outlivesL`: a value of a type that outlives `@a` in the box-relaxed sense
lies in `Res_α` (`@ρ ⊐ α`), as `vC_outlives` gives for `VOutlives`. The box case is the stratum's
monotonicity (`InStratum.mono`) at `α ⊑ β` where `vC_outlives` uses it at `α ⊏ β`: a boxed value's
resource is in `Res_β`, and `Res_β ⊆ Res_α`. `vC_outlivesLe`: for the fully relaxed judgment the
conclusion weakens to every stratum strictly below `α`; that is all a side condition whose
lifetime is then undercut by a fresh one needs (`Outlives/Compat.lean`). The fully relaxed
judgment does not give `Res_α` itself (`Outlives/Obstructions.lean`, `not_vC_outlives_le`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Outlives
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `Δ ⊢ A ⊐ @a` with the box rule's premise `Rb b` and the `Imm`/`Mut` rules' premise `Rr b`. -/
inductive VOutP (Rb Rr : Lifetime.Life → Prop) : VTy → Prop where
  | unit : VOutP Rb Rr .unit
  | tensor {A B} : VOutP Rb Rr A → VOutP Rb Rr B → VOutP Rb Rr (.tensor A B)
  | zero : VOutP Rb Rr .zero
  | sum {A B} : VOutP Rb Rr A → VOutP Rb Rr B → VOutP Rb Rr (.sum A B)
  | ref {A} : VOutP Rb Rr A → VOutP Rb Rr (.ref A)
  | bang {A} : VOutP Rb Rr (.bang A)
  | box {b A} : Rb b → VOutP Rb Rr (.box b A)
  | imm {b A} : Rr b → VOutP Rb Rr (.imm b A)
  | «mut» {b A} : Rr b → VOutP Rb Rr (.mut b A)
  | tvar {n} : VOutP Rb Rr (.tvar n)
  | mu {A} : VOutP Rb Rr A → VOutP Rb Rr (.mu A)
  | int {w} : VOutP Rb Rr (.int w)
  | opq {k} : VOutP Rb Rr (.opq k)
  | fam {L} : VOutP Rb Rr L → VOutP Rb Rr (.fam L)

/-- The box rule non-strict, the borrow rules strict: `[@b] T ⊐ @a` from `@a ⊑ @b`. -/
abbrev VOutL (Δ : LifeCtx) (a : Lifetime.Life) : VTy → Prop :=
  VOutP (Δ.EntailsLe a) (Δ.EntailsLt a)

/-- All three rules non-strict: `Δ ⊢ A ⊒ @a`. -/
abbrev VOutLe (Δ : LifeCtx) (a : Lifetime.Life) : VTy → Prop :=
  VOutP (Δ.EntailsLe a) (Δ.EntailsLe a)

/-- `Δ ⊨ Γ ⊐ @a` at the box-relaxed judgment. -/
def CtxOutL (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) : Prop :=
  Δ.Defines a ∧ ∀ s ∈ Γ, s.live = true → VOutL Δ a s.ty

theorem entailsLe_of_lt {Δ : LifeCtx} {a b : Lifetime.Life} (h : Δ.EntailsLt a b) :
    Δ.EntailsLe a b := fun δ hδ => by
  obtain ⟨m, n, hm, hn, hlt⟩ := h δ hδ
  refine ⟨m, n, hm, hn, ?_⟩
  simp only [Lifetime.SLife.Lt, Lifetime.SLife.Le] at hlt ⊢; omega

theorem entailsLe_refl {Δ : LifeCtx} {a : Lifetime.Life} (ha : Δ.Defines a) :
    Δ.EntailsLe a a := fun δ hδ => by
  obtain ⟨m, hm⟩ := ha δ hδ
  refine ⟨m, m, hm, hm, ?_⟩
  simp only [Lifetime.SLife.Le]; omega

theorem VOutP.mono {Rb Rr Rb' Rr' : Lifetime.Life → Prop} (hb : ∀ b, Rb b → Rb' b)
    (hr : ∀ b, Rr b → Rr' b) {A : VTy} (h : VOutP Rb Rr A) : VOutP Rb' Rr' A := by
  induction h with
  | unit => exact .unit
  | tensor _ _ ih₁ ih₂ => exact .tensor ih₁ ih₂
  | zero => exact .zero
  | sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂
  | ref _ ih => exact .ref ih
  | bang => exact .bang
  | box h => exact .box (hb _ h)
  | imm h => exact .imm (hr _ h)
  | «mut» h => exact .mut (hr _ h)
  | tvar => exact .tvar
  | mu _ ih => exact .mu ih
  | int => exact .int
  | opq => exact .opq
  | fam _ ih => exact .fam ih

/-- Every `VOutlives` derivation is one of the relaxed judgments'. -/
theorem VOutP.of_vOutlives {Δ : LifeCtx} {a : Lifetime.Life} {Rb Rr : Lifetime.Life → Prop}
    (hb : ∀ b, Δ.EntailsLt a b → Rb b) (hr : ∀ b, Δ.EntailsLt a b → Rr b) {A : VTy}
    (h : VOutlives Δ a A) : VOutP Rb Rr A := by
  induction h with
  | unit => exact .unit
  | tensor _ _ ih₁ ih₂ => exact .tensor ih₁ ih₂
  | zero => exact .zero
  | sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂
  | ref _ ih => exact .ref ih
  | bang => exact .bang
  | box h => exact .box (hb _ h)
  | imm h => exact .imm (hr _ h)
  | «mut» h => exact .mut (hr _ h)
  | tvar => exact .tvar
  | mu _ ih => exact .mu ih
  | int => exact .int
  | opq => exact .opq
  | fam _ ih => exact .fam ih

theorem VOutL.of_vOutlives {Δ : LifeCtx} {a : Lifetime.Life} {A : VTy} (h : VOutlives Δ a A) :
    VOutL Δ a A :=
  VOutP.of_vOutlives (fun _ h => entailsLe_of_lt h) (fun _ h => h) h

theorem VOutLe.of_vOutL {Δ : LifeCtx} {a : Lifetime.Life} {A : VTy} (h : VOutL Δ a A) :
    VOutLe Δ a A :=
  VOutP.mono (fun _ h => h) (fun _ h => entailsLe_of_lt h) h

theorem VOutP.rename {Rb Rr : Lifetime.Life → Prop} {A : VTy} (h : VOutP Rb Rr A) :
    ∀ r : Nat → Nat, VOutP Rb Rr (A.rename r) := by
  induction h with
  | unit => intro _; exact .unit
  | tensor _ _ ih₁ ih₂ => intro r; exact .tensor (ih₁ r) (ih₂ r)
  | zero => intro _; exact .zero
  | sum _ _ ih₁ ih₂ => intro r; exact .sum (ih₁ r) (ih₂ r)
  | ref _ ih => intro r; exact .ref (ih r)
  | bang => intro _; exact .bang
  | fam _ ih => intro r; exact .fam (ih r)
  | box h => intro _; exact .box h
  | imm h => intro _; exact .imm h
  | «mut» h => intro _; exact .mut h
  | tvar => intro _; exact .tvar
  | mu _ ih => intro r; exact .mu (ih _)
  | int => intro _; exact .int
  | opq => intro _; exact .opq

theorem VOutP.subst {Rb Rr : Lifetime.Life → Prop} {A : VTy} (h : VOutP Rb Rr A) :
    ∀ σ : Nat → VTy, (∀ n, VOutP Rb Rr (σ n)) → VOutP Rb Rr (A.subst σ) := by
  induction h with
  | unit => intro _ _; exact .unit
  | tensor _ _ ih₁ ih₂ => intro σ hσ; exact .tensor (ih₁ σ hσ) (ih₂ σ hσ)
  | zero => intro _ _; exact .zero
  | sum _ _ ih₁ ih₂ => intro σ hσ; exact .sum (ih₁ σ hσ) (ih₂ σ hσ)
  | ref _ ih => intro σ hσ; exact .ref (ih σ hσ)
  | bang => intro _ _; exact .bang
  | fam _ ih => intro σ hσ; exact .fam (ih σ hσ)
  | box h => intro _ _; exact .box h
  | imm h => intro _ _; exact .imm h
  | «mut» h => intro _ _; exact .mut h
  | tvar => intro σ hσ; exact hσ _
  | int => intro _ _; exact .int
  | opq => intro _ _; exact .opq
  | mu _ ih =>
      intro σ hσ
      exact .mu (ih _ (fun n => by
        cases n with
        | zero => exact .tvar
        | succ n => exact (hσ n).rename Nat.succ))

theorem VOutP.unroll {Rb Rr : Lifetime.Life → Prop} {A : VTy} (h : VOutP Rb Rr (.mu A)) :
    VOutP Rb Rr (VTy.inst (.mu A) A) := by
  cases h with
  | mu hA => exact hA.subst _ (fun n => by
      cases n with
      | zero => exact .mu hA
      | succ n => exact .tvar)

/-- **6.60 at the box-relaxed judgment.**  `vC_outlives`'s induction; only the box case
changes, from `α ⊏ β` to `α ⊑ β` under the stratum's monotonicity. -/
theorem vC_outlivesL {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α : Life}
    (hδ : Δ.Models δ) (ha : a.interp δ = some α) {T : VTy}
    (hT : VOutL Δ a T) (b : Bool) :
    ∀ (ls : List SRec) (v : Val) (ρ : WRes), vC b T ls δ v ρ → BoLo.Outlives ρ α := by
  intro ls v ρ h
  refine vC_ind δ (fun _ T _ _ ρ => VOutL Δ a T → BoLo.Outlives ρ α) ?_ b T ls v ρ h hT
  intro b T ls v ρ h hT
  cases T with
  | unit =>
      obtain ⟨rfl, -⟩ := h
      exact ResU.inStratum_empty α
  | int w =>
      obtain ⟨rfl, -⟩ := h
      exact ResU.inStratum_empty α
  | opq k =>
      obtain ⟨rfl, -⟩ := h
      exact ResU.inStratum_empty α
  | zero => exact False.elim h
  | tensor T₁ T₂ =>
      cases hT with
      | tensor h₁ h₂ =>
          obtain ⟨v₁, v₂, hs⟩ := h
          obtain ⟨-, ρ₁, ρ₂, hc, g₁, g₂⟩ := pure_sep_iff.mp hs
          exact (outlives_comp hc α).mpr ⟨g₁.2 h₁, g₂.2 h₂⟩
  | sum T₁ T₂ =>
      cases hT with
      | sum h₁ h₂ =>
          rcases h with ⟨v₁, hs⟩ | ⟨v₂, hs⟩
          · exact (pure_sep_iff.mp hs).2.2 h₁
          · exact (pure_sep_iff.mp hs).2.2 h₂
  | ref T =>
      cases hT with
      | ref h₁ =>
          obtain ⟨ℓ, w, hs⟩ := h
          obtain ⟨-, ρ₁, ρ₂, hc, rfl, g₂⟩ := pure_sep_iff.mp hs
          exact (outlives_comp hc α).mpr ⟨ResU.inStratum_single_own α ℓ w, g₂.2 h₁⟩
  | bang T =>
      obtain ⟨rfl, -⟩ := h
      exact ResU.inStratum_empty α
  | box c T =>
      cases hT with
      | box hle =>
          obtain ⟨β, hb, -, ho⟩ := h
          obtain ⟨α', β', ha', hb', hle'⟩ := hle δ hδ
          rw [ha] at ha'; cases Option.some.inj ha'
          rw [hb] at hb'; cases Option.some.inj hb'
          exact ho.mono (show (α : Life) ≤ β from hle')
  | imm c T =>
      cases hT with
      | imm hlt =>
          obtain ⟨β, hbi, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, -⟩, s, w, σ, hσ, _ls₀, hρ₁, -, hle, -⟩ := h
          subst hρ₀
          have e := eq_of_compS_empty_left hc
          subst e; subst hρ₁
          obtain ⟨α', β', ha', hb', hlt'⟩ := hlt δ hδ
          rw [ha] at ha'; cases Option.some.inj ha'
          rw [hbi] at hb'; cases Option.some.inj hb'
          exact ResU.inStratum_single ℓ (lt_of_lt_of_le (show (α : Life) < β from hlt') hle)
  | «mut» c T =>
      cases hT with
      | «mut» hlt =>
          obtain ⟨β, hbi, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, -⟩, b, w, σ, hσ, Q, hw, _ls₀, hle, hρ₁, -⟩ := h.1
          subst hρ₀
          have e := eq_of_compS_empty_left hc
          subst e; subst hρ₁
          obtain ⟨α', β', ha', hb', hlt'⟩ := hlt δ hδ
          rw [ha] at ha'; cases Option.some.inj ha'
          rw [hbi] at hb'; cases Option.some.inj hb'
          exact ResU.inStratum_single ℓ
            (show (CellU.mutOf b w σ hσ Q hw).InStratum α from
              lt_of_lt_of_le (show (α : Life) < β from hlt') hle)
  | thunk _ => cases hT
  | unk => cases hT
  | tvar _ => exact h.elim
  | mu A => exact h.2.2.2 hT.unroll
  | fam L =>
      cases hT with
      | fam hL =>
          obtain ⟨ℓ, n, hs⟩ := h
          obtain ⟨-, hs⟩ := pure_sep_iff.mp hs
          exact sepRange_closed (R := fun σ => BoLo.Outlives σ α) (ResU.inStratum_empty α)
            (fun _ _ _ hc o₁ o₂ => (outlives_comp hc α).mpr ⟨o₁, o₂⟩) (fun m σ hm => hm.2 hL) hs

/-- `@ρ ⊒ α`, read as membership in every stratum strictly below `α` (`Core.StratumLe`'s
shape, at a resource). -/
def OutlivesLe (ρ : WRes) (α : Life) : Prop := ∀ α', α' < α → BoLo.Outlives ρ α'

theorem outlivesLe_comp {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) {α : Life}
    (h₁ : OutlivesLe ρ₁ α) (h₂ : OutlivesLe ρ₂ α) : OutlivesLe ρ α :=
  fun α' h => (outlives_comp hc α').mpr ⟨h₁ α' h, h₂ α' h⟩

theorem outlivesLe_of_outlives {ρ : WRes} {α : Life} (h : BoLo.Outlives ρ α) : OutlivesLe ρ α :=
  fun _ h' => h.mono (le_of_lt h')

/-- **6.60 at the fully relaxed judgment**: every stratum strictly below `α`. -/
theorem vC_outlivesLe {Δ : LifeCtx} {δ : LSub} {a : Lifetime.Life} {α : Life}
    (hδ : Δ.Models δ) (ha : a.interp δ = some α) {T : VTy}
    (hT : VOutLe Δ a T) (b : Bool) :
    ∀ (ls : List SRec) (v : Val) (ρ : WRes), vC b T ls δ v ρ → OutlivesLe ρ α := by
  intro ls v ρ h
  refine vC_ind δ (fun _ T _ _ ρ => VOutLe Δ a T → OutlivesLe ρ α) ?_ b T ls v ρ h hT
  intro b T ls v ρ h hT
  cases T with
  | unit =>
      obtain ⟨rfl, -⟩ := h
      exact outlivesLe_of_outlives (ResU.inStratum_empty α)
  | int w =>
      obtain ⟨rfl, -⟩ := h
      exact outlivesLe_of_outlives (ResU.inStratum_empty α)
  | opq k =>
      obtain ⟨rfl, -⟩ := h
      exact outlivesLe_of_outlives (ResU.inStratum_empty α)
  | zero => exact False.elim h
  | tensor T₁ T₂ =>
      cases hT with
      | tensor h₁ h₂ =>
          obtain ⟨v₁, v₂, hs⟩ := h
          obtain ⟨-, ρ₁, ρ₂, hc, g₁, g₂⟩ := pure_sep_iff.mp hs
          exact outlivesLe_comp hc (g₁.2 h₁) (g₂.2 h₂)
  | sum T₁ T₂ =>
      cases hT with
      | sum h₁ h₂ =>
          rcases h with ⟨v₁, hs⟩ | ⟨v₂, hs⟩
          · exact (pure_sep_iff.mp hs).2.2 h₁
          · exact (pure_sep_iff.mp hs).2.2 h₂
  | ref T =>
      cases hT with
      | ref h₁ =>
          obtain ⟨ℓ, w, hs⟩ := h
          obtain ⟨-, ρ₁, ρ₂, hc, rfl, g₂⟩ := pure_sep_iff.mp hs
          exact outlivesLe_comp hc
            (outlivesLe_of_outlives (ResU.inStratum_single_own α ℓ w)) (g₂.2 h₁)
  | bang T =>
      obtain ⟨rfl, -⟩ := h
      exact outlivesLe_of_outlives (ResU.inStratum_empty α)
  | box c T =>
      cases hT with
      | box hle =>
          obtain ⟨β, hb, -, ho⟩ := h
          obtain ⟨α', β', ha', hb', hle'⟩ := hle δ hδ
          rw [ha] at ha'; cases Option.some.inj ha'
          rw [hb] at hb'; cases Option.some.inj hb'
          exact outlivesLe_of_outlives (ho.mono (show (α : Life) ≤ β from hle'))
  | imm c T =>
      cases hT with
      | imm hle₀ =>
          obtain ⟨β, hbi, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, -⟩, s, w, σ, hσ, _ls₀, hρ₁, -, hle, -⟩ := h
          subst hρ₀
          have e := eq_of_compS_empty_left hc
          subst e; subst hρ₁
          obtain ⟨α', β', ha', hb', hle'⟩ := hle₀ δ hδ
          rw [ha] at ha'; cases Option.some.inj ha'
          rw [hbi] at hb'; cases Option.some.inj hb'
          intro γ hγ
          exact ResU.inStratum_single ℓ
            (lt_of_lt_of_le hγ (le_trans (show (α : Life) ≤ β from hle') hle))
  | «mut» c T =>
      cases hT with
      | «mut» hle₀ =>
          obtain ⟨β, hbi, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, -⟩, b, w, σ, hσ, Q, hw, _ls₀, hle, hρ₁, -⟩ := h.1
          subst hρ₀
          have e := eq_of_compS_empty_left hc
          subst e; subst hρ₁
          obtain ⟨α', β', ha', hb', hle'⟩ := hle₀ δ hδ
          rw [ha] at ha'; cases Option.some.inj ha'
          rw [hbi] at hb'; cases Option.some.inj hb'
          intro γ hγ
          exact ResU.inStratum_single ℓ
            (show (CellU.mutOf b w σ hσ Q hw).InStratum γ from
              lt_of_lt_of_le hγ (le_trans (show (α : Life) ≤ β from hle') hle))
  | thunk _ => cases hT
  | unk => cases hT
  | tvar _ => exact h.elim
  | mu A => exact h.2.2.2 hT.unroll
  | fam L =>
      cases hT with
      | fam hL =>
          obtain ⟨ℓ, n, hs⟩ := h
          obtain ⟨-, hs⟩ := pure_sep_iff.mp hs
          intro γ hγ
          exact sepRange_closed (R := fun σ => BoLo.Outlives σ γ) (ResU.inStratum_empty γ)
            (fun _ _ _ hc o₁ o₂ => (outlives_comp hc γ).mpr ⟨o₁, o₂⟩)
            (fun m σ hm => hm.2 hL γ hγ) hs

end BoCa.Fig16.LogRel.Core.Outlives

end

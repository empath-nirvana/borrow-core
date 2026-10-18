import DivEffect.Frame

/-!
# DivEffect — the rules at a row holding `Div`  (§4.1, unknown 1, item 1)

`SemD Δ Γ e d S A`: `e` is at `F_{S, d} A`, the row `S` with `Div` at the name `d`.  It is
`SemC`'s form with `cwp` in place of `ewpTS`.

* **Every computation of the rest of the row** (`lift_compatD`): `SemC` at `F_S A` gives `SemD`.
  This covers `[perform]` and `[raise]` of every other name, and every rule of Core at `F_S A`.
* **`[sub]`** (`sub_compatD`): the rest of the row grows.
* **`[perform]` of `tick`** (`tick_compatD`).
* **`[let]`** (`let_compatD`): `cwp_bind`, with `let_compatC`'s side conditions.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DivEffect
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload hndE hndVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The relation's rules -/

/-- **A computation of the rest of the row is at `cwp`**: it never ticks. -/
theorem cwp_of_ewp {δ : LSub} {d : UInt32} {T : OpTab} {Q : List SRec → Val → WProp}
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : ewpTS ls e (opTable T) Q ρ) :
    cwp δ d T Q ls e ρ := by
  refine cwp_coind (W := fun ls e ρ => ewpTS ls e (opTable T) Q ρ) ?_ ls e ρ h
  intro ls e ρ h
  exact ewp_mono (divTab_mono δ d T Q _) (fun _ _ _ _ h => Or.inl h) (fun _ _ _ h => h) h

theorem ext_le {T T' : OpTab} (h : T.Le T') (d : UInt32) (en : OpEnt) :
    (OpTab.ext d 0 en T).Le (OpTab.ext d 0 en T') := by
  intro n i en' hT
  unfold OpTab.ext at hT ⊢
  by_cases hn : n = d ∧ i = 0
  · rw [if_pos hn] at hT ⊢; exact ⟨en', hT, OpEnt.Le.refl en'⟩
  · rw [if_neg hn] at hT ⊢; exact h n i en' hT

/-- **`[sub]`**: the rest of the row and the postcondition grow. -/
theorem cwp_sub {δ : LSub} {d : UInt32} {T T' : OpTab} (hT : T.Le T')
    {Q Q' : List SRec → Val → WProp} (hQ : ∀ ls v ρ, Q ls v ρ → Q' ls v ρ)
    {ls : List SRec} {e : Expr} {ρ : WRes} (h : cwp δ d T Q ls e ρ) : cwp δ d T' Q' ls e ρ := by
  have hcl : ∀ ls e ρ, Closing δ d T Q ls e ρ → Closing δ d T' Q' ls e ρ :=
    fun _ _ _ h => ewp_mono (opTable_mono _) (fun _ _ _ _ h => opTable_le (ext_le hT d _) h) hQ h
  refine cwp_coind (W := cwp δ d T Q) ?_ ls e ρ h
  intro ls e ρ h
  refine ewp_mono (divTab_mono δ d T' Q' _) (fun ls t Φ σ hd => ?_) hQ (cwp_out ls e ρ h)
  rcases hd with hd | hd
  · exact Or.inl (opTable_le hT hd)
  · exact Or.inr (performStop_mono _ ls t _ _ σ (fun ls e ρ hw => ⟨hw.1, hcl ls e ρ hw.2⟩) hd)

/-- **`tick ()`** stops at once: its continuation, the hole, answers `next` or `close`. -/
theorem cwp_tick {δ : LSub} {d : UInt32} {T : OpTab} (hTd : T d 0 = none)
    {Q : List SRec → Val → WProp} (hQ : ∀ ls w ρ, vC true nextTy ls δ w ρ → Q ls w ρ)
    (ls : List SRec) : cwp δ d T Q ls (tickE d) PMap.empty := by
  have hv : ∀ ls w ρ, vC true nextTy ls δ w ρ → owe δ d T Q (cwp δ d T Q) ls (.val w) ρ :=
    fun ls w ρ h => ⟨cwp_of_ewp (ewp_val (opTable_mono T) (hQ ls w ρ h)),
      ewp_val (opTable_mono _) (hQ ls w ρ h)⟩
  refine cwp_roll ls _ _ (ewp_fold (divTab_mono δ d T Q _) (wpG_here _ _ _ _ (Or.inr (Or.inr
    ⟨.hole, d, 0, .unit, tickEnt δ d, pure_sep_mk ⟨rfl, rfl, by simp [tickT, OpTab.ext], rfl⟩
      ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, rfl⟩, And.intro (fun h => nomatch h)
        (fun ls'' _ => And.intro (fun w τ₁ τ₂ hB hc => ?_) (fun h => absurd rfl h))⟩⟩))))
  rw [eq_of_compS_empty_left hc]
  exact hv ls'' w τ₁ hB

/-! ### The judgment -/

/-- A row that does not hold the name `d`. -/
def Row.Without (S : Row) (d : UInt32) : Prop := ∀ o ∈ S, o.n ≠ d

theorem Row.tab_without {S : Row} {d : UInt32} (h : Row.Without S d) (δ : LSub) (i : UInt32) :
    Row.tab S δ d i = none := by
  cases hf : Row.find S d i with
  | none => simp [Row.tab, hf]
  | some o =>
      obtain ⟨hm, hn, -⟩ := Row.find_mem hf
      exact absurd hn (h o hm)

/-- `Δ; Γ ⊨ e : F_{S, Div} A`, `Div` at the name `d`. -/
def SemD (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (d : UInt32) (S : Row) (A : VTy) : Prop :=
  ∀ δ γ (ls : List SRec) ρ, Δ.Models δ → gDenC ls δ Γ γ ρ →
    cwp δ d (Row.tab S δ) (fun ls v => vC true A ls δ v) ls (substAll γ e) ρ

/-- **Every computation of the rest of the row**, `[perform]` and `[raise]` of every other name
among them. -/
theorem lift_compatD {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {d : UInt32} {S : Row} {A : VTy}
    (h : SemC Δ Γ e (CTy.effOf S A)) : SemD Δ Γ e d S A :=
  fun δ γ ls ρ hδ hg => cwp_of_ewp ((cC_effOf S A ls δ _ ρ).mp (h δ γ ls ρ hδ hg))

/-- **`[sub]`**. -/
theorem sub_compatD {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {d : UInt32} {S S' : Row} {A : VTy}
    (hle : RowLe S S') (h : SemD Δ Γ e d S A) : SemD Δ Γ e d S' A :=
  fun δ γ ls ρ hδ hg => cwp_sub (Row.tab_le δ hle) (fun _ _ _ h => h) (h δ γ ls ρ hδ hg)

/-- **`[perform]` of `tick`**. -/
theorem tick_compatD {Δ : LifeCtx} {Γ : Ctx VTy} {d : UInt32} {S : Row} (hS : Row.Without S d)
    (hΓ : ∀ δ γ ls ρ, gDenC ls δ Γ γ ρ → ρ = PMap.empty) :
    SemD Δ Γ (tickE d) d S nextTy := by
  intro δ γ ls ρ _ hg
  rw [hΓ δ γ ls ρ hg]
  rw [show substAll γ (tickE d) = tickE d from psub_closedAt _ γ (by rfl) (Nat.zero_le 0)]
  exact cwp_tick (Row.tab_without hS δ 0) (fun _ _ _ h => h) ls

/-- **`[let]`** at a row holding `Div`: `M to x. N`, with `let_compatC`'s side conditions. -/
theorem let_compatD {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A B : VTy} {d : UInt32}
    {S : Row} (hS : Row.Without S d)
    (hsp : Ctx.SplitP Γ Γ₁ Γ₂) (hW : S.Weak → Γ₂.Drops) (hU : S.Unr → Persistent Γ₂)
    (hM : SemD Δ Γ₁ M d S A) (hN : SemD Δ (⟨A, true⟩ :: Γ₂) N d S B) :
    SemD Δ Γ (.app (.val (.lam N)) M) d S B := by
  intro δ γ ls ρ hδ hg
  obtain ⟨ρ₁, ρ₂, hc, hg₁, hg₂⟩ := gDenC_split hsp hg
  refine cwp_bind (Row.tab_without hS δ 0) (.appR (.val (.lam (Expr.psub 1 γ N))) .hole)
    (fun n => by simp [Kont.HasHnd]) (fun n => by simp [Kont.Catches])
    (fun ls => gDenC ls δ Γ₂ γ) (fun _ _ hs σ h => gDenC_same hs h)
    (fun _ _ _ he h => gDenC_local he h) ?_ ?_ ?_ (fun ls v => vC true A ls δ v) _ ?_
    (hM δ γ ls ρ₁ hδ hg₁) hg₂ hc
  · intro n i en hT ha ls' σ h
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    exact gDenC_noOwn (hW ⟨o, (Row.find_mem hf).1, OpSig.weak_of_ent (Or.inr ha)⟩) h
  · intro n i en hT hq ls' σ h
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    exact gDenC_persistent (hU ⟨o, (Row.find_mem hf).1, hq⟩) h
  · intro n i en hT ha hq ls' K₁ ρ' σ ρ'' hcan hσ hc'
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    exact ent_plain δ _ (fun n => by simp [Kont.HasHnd]) (by simp [Kont.Catches])
      (gDenC_noOwn (hW ⟨o, (Row.find_mem hf).1, OpSig.weak_of_ent (Or.inl hq)⟩) hσ) o hcan hc'
  · rintro ls' v σ ⟨σ₁, σ₂, hcσ, hv, hg₂'⟩
    obtain ⟨hlen, hgs⟩ := gDenC_iff.mp hg₂'
    refine cwp_roll _ _ _ (ewp_step (divTab_mono δ _ _ _ _)
      (fun μ => Step1N.head (Head.beta μ (Expr.psub 1 γ N) v) rfl) ls' _ σ ?_)
    rw [← substAll_cons_psub]
    exact cwp_out _ _ _
      (hN δ (v :: γ) ls' σ hδ (gDenC_mk (by simpa using hlen) ⟨σ₁, σ₂, hcσ, hv, hgs⟩))

end BoCa.Fig16.LogRel.Core.DivEffect

end

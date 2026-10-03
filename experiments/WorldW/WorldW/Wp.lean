import WorldW.Checks

/-!
# WorldW — `ewpW`'s fixed-point lemmas and `σ`-monotonicity (DESIGN §4.2, first bullet)

**World: the W-draft.** `ewpW` is `ewpTS` (`Core/EffDefs.lean:73`) with `τ` and `σ` threaded;
these are `ewp`'s proofs (`Core/EffWp.lean:748-806`) with the two indices carried.

`σ` is read only through `wpGW`'s selection premise `∀ p ∈ immRecs σ, p ∈ ps` (DESIGN §1.4). A
larger `σ` strengthens that premise, so `ewpW` at `σ` gives `ewpW` at every `σ′` whose 6.64
records include `σ`'s (`ewpW_σmono`), at every table that passes the stack through
(`TableW.SigmaMono`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace WorldW
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- A table is monotone in the continuations it owes. -/
def TableW.Mono (Tb : TableW) : Prop :=
  ∀ σ ls τ' t (Φ Φ' : ContW) ρ, (∀ τ σ ls e ρ, Φ τ σ ls e ρ → Φ' τ σ ls e ρ) →
    Tb σ ls τ' t Φ ρ → Tb σ ls τ' t Φ' ρ

theorem wpGW_mono {τ σ : List OEnt} {ls : List SRec} {e : Expr}
    {Q Q' : List OEnt → List SRec → Expr → WProp}
    (hQ : ∀ τ' ls t ρ, Q τ' ls t ρ → Q' τ' ls t ρ) {ρ : WRes} (h : wpGW τ σ ls e Q ρ) :
    wpGW τ σ ls e Q' ρ := by
  intro ρf fρ ps h1 h2 h3 h4 h5 h6 A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ρc, πc, t, μ, μ', ps', ls', τ', a1, a2, a3, a4, a5, a6, a7, a8,
    a9, a10, a11, a12, a13, a14, a15, a16⟩ := h ρf fρ ps h1 h2 h3 h4 h5 h6 A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, ρc, πc, t, μ, μ', ps', ls', τ', a1, a2, a3, a4, a5, a6, a7, a8,
    a9, a10, a11, a12, a13, a14, a15, hQ _ _ _ _ a16⟩

theorem ewpStepW_mono {Tb : TableW} (hTb : Tb.Mono) {Q : List SRec → Val → WProp}
    {P P' : ContW} (hP : ∀ τ σ ls e ρ, P τ σ ls e ρ → P' τ σ ls e ρ) :
    ∀ τ σ ls e ρ, ewpStepW Tb Q P τ σ ls e ρ → ewpStepW Tb Q P' τ σ ls e ρ := by
  intro τ σ ls e ρ h
  refine wpGW_mono (fun τ' ls' t ρ' h' => ?_) h
  rcases h' with h' | h'
  · exact Or.inl h'
  · exact Or.inr (hTb _ _ _ _ _ _ _ hP h')

/-- Induction on the fixed point. -/
theorem ewpW_ind {Tb : TableW} {Q : List SRec → Val → WProp} (P : ContW)
    (hP : ∀ τ σ ls e ρ, ewpStepW Tb Q P τ σ ls e ρ → P τ σ ls e ρ)
    {τ σ : List OEnt} {ls : List SRec} {e : Expr} {ρ : WRes} (h : ewpW τ σ ls e Tb Q ρ) :
    P τ σ ls e ρ :=
  h P hP

theorem ewpW_fold {Tb : TableW} (hTb : Tb.Mono) {Q : List SRec → Val → WProp}
    {τ σ : List OEnt} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : ewpStepW Tb Q (fun τ σ ls e => ewpW τ σ ls e Tb Q) τ σ ls e ρ) :
    ewpW τ σ ls e Tb Q ρ :=
  fun P hP => hP _ _ _ _ _ (ewpStepW_mono hTb (fun _ _ _ _ _ h' => h' P hP) _ _ _ _ _ h)

theorem ewpW_unfold {Tb : TableW} (hTb : Tb.Mono) {Q : List SRec → Val → WProp}
    {τ σ : List OEnt} {ls : List SRec} {e : Expr} {ρ : WRes} (h : ewpW τ σ ls e Tb Q ρ) :
    ewpStepW Tb Q (fun τ σ ls e => ewpW τ σ ls e Tb Q) τ σ ls e ρ :=
  ewpW_ind _ (fun _ _ _ _ _ h' => ewpStepW_mono hTb (fun _ _ _ _ _ h'' => ewpW_fold hTb h'')
    _ _ _ _ _ h') h

/-- The cancel table owes nothing. -/
theorem cancelTabW_mono (T : OpTab) (N : List UInt32) : (cancelTabW T N).Mono :=
  fun _ _ _ _ _ _ _ _ h => h

theorem withOwnerW_mono {Tb : TableW} (hTb : Tb.Mono) (Fr : List SRec → WProp) :
    (withOwnerW Tb Fr).Mono := by
  rintro σ ls τ' t Φ Φ' ρ hΦ ⟨ρ₁, ρ₂, hc, h₁, h₂⟩
  exact ⟨ρ₁, ρ₂, hc, hTb _ _ _ _ _ _ _ hΦ h₁, h₂⟩

theorem opTabW_mono (T : OpTab) (Fr : List SRec → WProp) : (opTabW T Fr).Mono := by
  intro σ ls τ' t Φ Φ' ρ hΦ h
  rcases h with ⟨K, n, i, v, en, h⟩ | h
  · obtain ⟨hp, hr⟩ := pure_sep_iff.mp h
    obtain ⟨ρa, ρk, hc, hA, ⟨hu, hs⟩, hH, hC⟩ := hr
    refine Or.inl ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, ⟨hu, fun ls' he => ?_⟩, hH, hC⟩⟩
    obtain ⟨h₁, h₂⟩ := hs ls' he
    exact ⟨fun w ρ₁ ρ₂ hB hc' => hΦ _ _ _ _ _ (h₁ w ρ₁ ρ₂ hB hc'), h₂⟩
  · exact Or.inr h

theorem extTabW_mono {h : Life} {Tb : TableW} (hTb : Tb.Mono) : (extTabW h Tb).Mono := by
  rintro σ ls τ' t Φ Φ' ρ hΦ ⟨h₁, h₂, h₃⟩
  exact ⟨h₁, h₂, hTb _ _ _ _ _ _ _ hΦ h₃⟩

/-! ### `σ`-monotonicity -/

/-- `σ`'s 6.64 records are among `σ′`'s. -/
def SigmaLe (σ σ' : List OEnt) : Prop := ∀ p ∈ immRecs σ, p ∈ immRecs σ'

theorem sigmaLe_append (extra σ : List OEnt) : SigmaLe σ (extra ++ σ) := by
  intro p hp
  induction extra with
  | nil => exact hp
  | cons e extra ih =>
      cases e with
      | imm r => obtain ⟨q, α⟩ := r; exact List.mem_cons_of_mem _ ih
      | «mut» _ _ _ _ => exact ih
      | anti _ _ _ _ _ _ => exact ih
      | reb _ _ _ _ _ _ _ => exact ih
      | hnd _ _ => exact ih

theorem wpGW_σmono {τ σ σ' : List OEnt} (hσ : SigmaLe σ σ') {ls : List SRec} {e : Expr}
    {Q : List OEnt → List SRec → Expr → WProp} {ρ : WRes} (h : wpGW τ σ ls e Q ρ) :
    wpGW τ σ' ls e Q ρ :=
  fun ρf fρ ps h1 h2 h3 h4 h5 h6 A k =>
    h ρf fρ ps h1 h2 h3 h4 h5 (fun p hp => h6 p (hσ p hp)) A k

/-- A table passes the stack through: its continuations at `σ` give its continuations at any
larger `σ′`. -/
def TableW.SigmaMono (Tb : TableW) : Prop :=
  ∀ σ σ' ls τ' t (Φ Φ' : ContW) ρ, SigmaLe σ σ' →
    (∀ τ ls e ρ, Φ τ σ ls e ρ → Φ' τ σ' ls e ρ) → Tb σ ls τ' t Φ ρ → Tb σ' ls τ' t Φ' ρ

/-- **`ewpW` is `σ`-monotone** at every table that passes the stack through. -/
theorem ewpW_σmono {Tb : TableW} (hTb : Tb.Mono) (hS : Tb.SigmaMono)
    {Q : List SRec → Val → WProp} {τ σ : List OEnt} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : ewpW τ σ ls e Tb Q ρ) : ∀ σ', SigmaLe σ σ' → ewpW τ σ' ls e Tb Q ρ := by
  refine ewpW_ind (fun τ σ ls e ρ => ∀ σ', SigmaLe σ σ' → ewpW τ σ' ls e Tb Q ρ) ?_ h
  intro τ σ ls e ρ hstep σ' hσ
  refine ewpW_fold hTb (wpGW_σmono hσ (wpGW_mono (fun τ' ls' t ρ' h' => ?_) hstep))
  rcases h' with h' | h'
  · exact Or.inl h'
  · exact Or.inr (hS _ _ _ _ _ _ _ _ hσ (fun _ _ _ _ h'' => h'' σ' hσ) h')

theorem cancelTabW_sigmaMono (T : OpTab) (N : List UInt32) : (cancelTabW T N).SigmaMono :=
  fun _ _ _ _ _ _ _ _ _ _ h => h

theorem withOwnerW_sigmaMono {Tb : TableW} (hS : Tb.SigmaMono) (Fr : List SRec → WProp) :
    (withOwnerW Tb Fr).SigmaMono := by
  rintro σ σ' ls τ' t Φ Φ' ρ hσ hΦ ⟨ρ₁, ρ₂, hc, h₁, h₂⟩
  exact ⟨ρ₁, ρ₂, hc, hS _ _ _ _ _ _ _ _ hσ hΦ h₁, h₂⟩

theorem opTabW_sigmaMono (T : OpTab) (Fr : List SRec → WProp) : (opTabW T Fr).SigmaMono := by
  intro σ σ' ls τ' t Φ Φ' ρ hσ hΦ h
  rcases h with ⟨K, n, i, v, en, h⟩ | h
  · obtain ⟨hp, hr⟩ := pure_sep_iff.mp h
    obtain ⟨ρa, ρk, hc, hA, ⟨hu, hs⟩, hH, hC⟩ := hr
    refine Or.inl ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, ⟨hu, fun ls' he => ?_⟩, hH, hC⟩⟩
    obtain ⟨h₁, h₂⟩ := hs ls' he
    refine ⟨fun w ρ₁ ρ₂ hB hc' => hΦ _ _ _ _ (h₁ w ρ₁ ρ₂ hB hc'), fun hq N hN hK => ?_⟩
    exact ewpW_σmono (withOwnerW_mono (cancelTabW_mono T N) Fr)
      (withOwnerW_sigmaMono (cancelTabW_sigmaMono T N) Fr) (h₂ hq N hN hK) σ' hσ
  · exact Or.inr h

theorem ewpW_σmono_opTabW {T : OpTab} {Fr : List SRec → WProp} {Q : List SRec → Val → WProp}
    {τ σ : List OEnt} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : ewpW τ σ ls e (opTabW T Fr) Q ρ) (σ' : List OEnt) (hσ : SigmaLe σ σ') :
    ewpW τ σ' ls e (opTabW T Fr) Q ρ :=
  ewpW_σmono (opTabW_mono T Fr) (opTabW_sigmaMono T Fr) h σ' hσ

end WorldW

end

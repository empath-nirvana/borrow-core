import Targets.Restricted.CoreLaws
import Targets.Restricted.Composition
import Targets.Statements.EffectSafety

/-!
# Targets — effect safety at Core σ=[] (DESIGN §9 item 7)

* `stop_irreducible`: a stop at an operation of a row takes no step (D7), from Core's unique
  decomposition (`plug_cmp`, `plug_primApp`, `head_not_opPlug`).
* `arun_rest_irr`: `ARun.rest` at an irreducible end, not only at a value: under one allocator the
  machine is deterministic (`AStep1.deterministic`), so a run is a prefix of every run that reaches
  an irreducible configuration.
* `adequateEvery_core : AdequateEvery coreW`: `wpTS_demonic`'s replay at `wpG` (`steps_replay`,
  `Alloc.replay`) with `arun_rest_irr`: from every configuration Core's world reaches, every run of
  a computation in Core's relation at a row continues to a value or to a stop of the row.
* `wlaws_core : WLaws coreW`.  **PROVED AT σ=[]**.
* `effSafe_tier1 : EffSafe tier1`, by `effSafeOfFL`.  **PROVED AT σ=[]** (tier 1, unr-free rows by
  the statement).  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun AStep1 performE raiseE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- A plugged operation its context does not catch takes no step. -/
theorem opPlug_no_step {μ μ' : Heap} {K : Kont} {r : Bool} {p : Val} {n : UInt32} {t' : Expr}
    (hn : payloadName p = some n) (hK : OpFree r n K) :
    ¬ Step1 (ℍ := ℍ) μ (K.plug (opE r p)) μ' t' := by
  rintro ⟨K', a, a', he, -, hh⟩
  rcases plug_cmp K K' (opE_not_isVal r p) hh.not_isVal he with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
  · have hK'' := plug_primApp (h₁.symm.trans (opE_eq_app r p)) hh.not_isVal
    subst hK''
    have h₀ : OpFree r n Kont.hole := by cases r <;> simp [OpFree, Kont.HasHnd, Kont.Catches]
    have ha : a = opE r p := by simpa [Kont.plug] using h₁.symm
    subst ha
    exact head_not_opPlug hn h₀ hh
  · subst h₂
    exact head_not_opPlug hn (opFree_right hK) (h₁ ▸ hh)

/-- **D7: a stop is irreducible.** -/
theorem stop_irreducible {S : Row} {μ μ' : Heap} {e e' : Expr} (h : StopsIn S e) :
    ¬ Step1 (ℍ := ℍ) μ e μ' e' := by
  rcases h with ⟨K, n, i, v, o, rfl, hK, -, -⟩ | ⟨K, n, i, v, o, rfl, hK, -, -⟩
  · exact opPlug_no_step (r := false) (payloadName_opPayload n i v) hK
  · exact opPlug_no_step (r := true) (payloadName_opPayload n i v) hK

/-- `ARun.rest` at an irreducible end. -/
theorem arun_rest_irr {A : Alloc} {i j j₁ : Nat} {μ μ' μ₁ : Heap} {e e₁ t : Expr}
    (hirr : ∀ k₂ μ₂ e₂, ¬ AStep1 (ℍ := ℍ) A j μ' t k₂ μ₂ e₂)
    (h' : ARun (ℍ := ℍ) A i μ e j₁ μ₁ e₁) :
    ARun (ℍ := ℍ) A i μ e j μ' t → ARun (ℍ := ℍ) A j₁ μ₁ e₁ j μ' t := by
  induction h' with
  | refl => exact id
  | more s' _ ih =>
      intro h
      cases h with
      | refl => exact (hirr _ _ _ s').elim
      | more s t =>
          obtain ⟨rfl, rfl, rfl⟩ := AStep1.deterministic s s'
          exact ih t

/-- **`AdequateEvery coreW`.** -/
theorem adequateEvery_core : AdequateEvery (ℍ := ℍ) (coreW (ℍ := ℍ)) := by
  intro i fρ ρf ρ ps μ S A δ e _ hF hf hc hμ h μ₁ e₁ hs
  rcases i with ⟨ls, ⟨⟩⟩
  obtain ⟨hT, htg⟩ := hF
  have hw := ewp_unfold (opTable_mono _) ((cC_effOf S A ls δ e ρ).mp h)
  obtain ⟨cs, hcs⟩ := steps_replay hs
  have hrun := hcs (Alloc.replay cs) 0 (Alloc.replay_agree cs)
  obtain ⟨_, _, _, _, _, t, μ₀, μ', _, _, _, _, _, h₄, _, _, ⟨k', h₈⟩, _, _, _, _, _, _, _, hQ⟩ :=
    hw ρf fρ ps hf hc hT htg (Alloc.replay cs) 0
  obtain rfl := ResU.Lower.functional h₄ hμ
  have ht : IsVal t ∨ StopsIn S t := by
    rcases hQ with ⟨v, rfl, -⟩ | hQ
    · exact Or.inl v.2
    · right
      rcases hQ with ⟨K, n, j, v, en, hp⟩ | ⟨K, n, j, v, en, hp⟩
      · obtain ⟨⟨rfl, hK, hT', ha⟩, -⟩ := pure_sep_iff.mp hp
        obtain ⟨o, hf', rfl⟩ := Row.tab_some hT'
        exact Or.inl ⟨K, n, j, v, o, rfl, hK, hf', ha⟩
      · obtain ⟨⟨rfl, hK, hT', ha⟩, -⟩ := pure_sep_iff.mp hp
        obtain ⟨o, hf', rfl⟩ := Row.tab_some hT'
        exact Or.inr ⟨K, n, j, v, o, rfl, hK, hf', ha⟩
  have hirr : ∀ k₂ μ₂ e₂, ¬ AStep1 (ℍ := ℍ) (Alloc.replay cs) k' μ' t k₂ μ₂ e₂ := by
    intro k₂ μ₂ e₂ hstep
    rcases ht with hv | hst
    · exact BoCa.BoLo.no_step_val (w := ⟨t, hv⟩) hstep.toStep1
    · exact stop_irreducible hst hstep.toStep1
  exact ⟨μ', t, (arun_rest_irr hirr hrun h₈).toSteps, ht⟩

/-- **`WLaws coreW`.** -/
theorem wlaws_core : WLaws (ℍ := ℍ) (coreW (ℍ := ℍ)) :=
  ⟨sliceShape_core, mono_core, extPre_core, effInterp_core, famEmpty_core, dataVals_core,
    shareMono_core, relLaws_core, adequateEvery_core⟩

/-- **`EffSafe tier1`** (P2 for Core's typing, at unr-free rows). -/
theorem effSafe_tier1 : EffSafe (ℍ := ℍ) tier1 :=
  effSafeOfFL _ _ fl_core_tier1 wlaws_core

end Targets

end

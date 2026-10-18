import DivEffect.Runtime

/-!
# DivEffect — the §4.1 candidate without `Closing`

§4.1's candidate owes a tick's continuation to the candidate at each answer, and nothing more:

    cwp₀ M Q  ≜  gfp W. ewpTS M (opTable T ∨ Π_W) Q,      Π_W(tick) = λ_. λκ. ∀ n. W (κ n)

`Ω = fix self. tick (); self ()` ignores every answer.  It is in `cwp₀` (`omega_cwp0`): each
segment runs to a tick, and the continuation at either answer is `Ω` again.  It is not in
`Closing` (`omega_not_closing`): answered *close* at every tick, it never ends.

So `cwp₀` does not give item 4.  `div_fuel 0 Ω` answers every tick *close*, and with a linear
`κ` it can do nothing else; `Ω` ignores it.  `cwp` owes `Closing` at each answer as well
(`Defs.lean`), and `Ω` is outside it (`omega_not_cwp`).  Nothing typed is `Ω`: `iterate` closes
at its back edge.  The relation has to say so, because `div_fuel`'s totality is proved from the
relation, not from the syntax.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DivEffect
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Step1N performE raiseE opPayload hndE hndVal Alloc
  ARun AStep1)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-! ### The candidate without `Closing` -/

/-- A segment of §4.1's candidate: a tick owes its continuation to `W` alone. -/
def cwpF0 (δ : LSub) (d : UInt32) (T : OpTab) (Q : List SRec → Val → WProp) (W : CPred) : CPred :=
  fun ls e => ewpTS ls e (orTab (opTable T) (tickStop δ d W)) Q

/-- **§4.1's candidate**, `gfp W. cwpF0 W`. -/
def cwp0 (δ : LSub) (d : UInt32) (T : OpTab) (Q : List SRec → Val → WProp) : CPred :=
  fun ls e ρ => ∃ W : CPred, W.Le (cwpF0 δ d T Q W) ∧ W ls e ρ

/-! ### `Ω` -/

/-- `Ω`'s body under itself (`1`) and its argument (`0`): `tick () to _. self ()`. -/
def omB (d : UInt32) : Expr := .app (.val (.lam (.app (.var 2) (.val .unit)))) (tickE d)

theorem omB_closed (d : UInt32) : closedAt 2 (omB d) = true := rfl

/-- `Ω = self ()`. -/
def omE (d : UInt32) : Expr := .app (.val (selfV (omB d))) (.val .unit)

/-- The frame of `Ω`'s tick: `[·] to _. Ω`. -/
def omK (d : UInt32) : Kont := .appR (.val (.lam (.app (.val (selfV (omB d))) (.val .unit)))) .hole

theorem om_tick (d : UInt32) : PureSteps (omE d) ((omK d).plug (tickE d)) := by
  refine (selfV_steps_in (omB_closed d) .hole .unit).trans ?_
  rw [fixV_eq (omB_closed d)]
  refine (PureSteps.beta _ _).trans ?_
  have hc : closedAt 0 (selfV (omB d)).1 = true := selfV_closed (omB_closed d)
  have ht : closedAt 0 (tickE d) = true := rfl
  simp only [omK, omB]
  generalize selfV (omB d) = σ at hc ⊢
  simp [closed_subst hc, closed_shift hc, subst_closedAt _ _ ht, Kont.plug]
  exact .refl

theorem om_back (d : UInt32) (w : Val) : PureSteps ((omK d).plug (.val w)) (omE d) := by
  refine (PureSteps.beta _ _).trans ?_
  have hc : closedAt 0 (selfV (omB d)).1 = true := selfV_closed (omB_closed d)
  simp only [omE]
  generalize selfV (omB d) = σ at hc ⊢
  simp [closed_subst hc]
  exact .refl

theorem omK_hasHnd (d n : UInt32) : (omK d).HasHnd n = false := by simp [omK, Kont.HasHnd]

/-- **`Ω` is in §4.1's candidate**, at every row and postcondition. -/
theorem omega_cwp0 (δ : LSub) (d : UInt32) (T : OpTab) (Q : List SRec → Val → WProp)
    (ls : List SRec) : cwp0 δ d T Q ls (omE d) PMap.empty := by
  let W : CPred := fun _ e ρ => ρ = PMap.empty ∧ (e = omE d ∨ ∃ w, e = (omK d).plug (.val w))
  have hM := orTab_mono (opTable_mono T) (Table.Const.mono (tickStop_const δ d W))
  have hΩ : ∀ ls, cwpF0 δ d T Q W ls (omE d) PMap.empty := by
    intro ls
    refine ewp_pureSteps hM (om_tick d) _ _ _ (ewp_fold hM (wpG_here _ _ _ _ (Or.inr (Or.inr
      ⟨omK d, d, 0, .unit, tickEnt δ d, pure_sep_mk ⟨rfl, omK_hasHnd d d, by simp [tickT, OpTab.ext], rfl⟩
        ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, rfl⟩, And.intro (fun h => nomatch h)
          (fun ls' _ => And.intro (fun w τ₁ τ₂ hB hc => ?_) (fun h => absurd rfl h))⟩⟩))))
    obtain ⟨-, rfl⟩ := vC_next hB
    exact ⟨eq_of_compS_empty_left hc, .inr ⟨w, rfl⟩⟩
  refine ⟨W, ?_, rfl, .inl rfl⟩
  rintro ls e ρ ⟨rfl, rfl | ⟨w, rfl⟩⟩
  · exact hΩ ls
  · exact ewp_pureSteps hM (om_back d w) _ _ _ (hΩ ls)

/-! ### `Ω` is not in `Closing` -/

/-- Pure steps are an allocator run of every allocator, from every count. -/
theorem PureSteps.arun {e e' : Expr} (h : PureSteps e e') (A : Alloc) (k : Nat) (μ : Heap) :
    ARun (ℍ := ℍ) A k μ e k μ e' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl _ _ _
  | head hs _ ih => exact ARun.cons (hs μ) ih

/-- A run of `wpG`'s kind, from a term that pure-steps to `Ω`, to a term that takes no step,
is the run to `Ω`'s tick. -/
theorem om_stop {d : UInt32} {e t : Expr} (he : PureSteps e (omE d)) {A : Alloc} {k k' : Nat}
    {μ μ' : Heap} (hr : ARun (ℍ := ℍ) A k μ e k' μ' t) (ht : ∀ μ₂ t₂, ¬ Step1 (ℍ := ℍ) μ' t μ₂ t₂) :
    t = (omK d).plug (tickE d) := by
  have h₀ := PureSteps.arun (ℍ := ℍ) (he.trans (om_tick d)) A k μ
  have hf : ∀ μ₂ t₂, ¬ Step1 (ℍ := ℍ) μ ((omK d).plug (tickE d)) μ₂ t₂ :=
    fun _ _ h => opPlug_no_step (r := false) (payloadName_opPayload d 0 .unit) (omK_hasHnd d d) h
  have hrest := ARun.rest_final hf hr h₀
  cases hrest with
  | refl => rfl
  | more s _ => exact (ht _ _ s.toStep1).elim

/-- A list and a resource with a configuration `wpG` can be run from. -/
def Pre (ls : List SRec) (ρ : WRes) : Prop :=
  ∃ (ρf fρ : WRes) (ps : List FrameRec), ResU.Hash ρf ρ ∧ ResU.CompS ρf ρ fρ ∧
    TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls

/-- **`Ω` is not in `Closing`**: answered *close* at every tick, it reaches its tick again.  By
induction on `Closing`'s least fixed point, with the predicate "not a term that pure-steps to
`Ω`, wherever `wpG` can be run". -/
theorem omega_not_closing (δ : LSub) (d : UInt32) (Q : List SRec → Val → WProp) :
    ¬ Closing δ d OpTab.empty Q [] (omE d) PMap.empty := by
  intro h
  have hP := ewp_ind (fun ls e ρ => Pre ls ρ → ¬ PureSteps e (omE d)) ?_ h
  · have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
    exact hP ⟨PMap.empty, PMap.empty, [], Fig16.LogRel.hash_empty, ResU.comp_empty_right _,
      TW.empty, htg⟩ .refl
  intro ls e ρ hs ⟨ρf, fρ, ps, hf, hc, hT, htg⟩ he
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, ⟨j, h₈⟩, -, -, hB,
    hT', htg', -, -, hC⟩ := hs ρf fρ ps hf hc hT htg Alloc.leastFree 0
  rcases hC with ⟨v, rfl, -⟩ | hst
  · exact absurd (om_stop he h₈ (fun _ _ => BoCa.BoLo.no_step_val)) (by
      intro h; have := congrArg IsVal h; simp [omK, Kont.plug, tickE, BoCa.BoLo.performE] at this
      exact this v.2)
  rcases hst with ⟨K₁, n, i, v, en, hp⟩ | ⟨K₁, n, i, v, en, hp⟩
  · obtain ⟨⟨rfl, hK₁, hT₁, -⟩, ρa, ρk, hcak, hA, -, hcont⟩ := pure_sep_iff.mp hp
    rcases ext_some hT₁ with ⟨rfl, rfl, rfl⟩ | hT₁
    swap
    · cases hT₁
    obtain ⟨rfl, rfl⟩ := hA
    have hst := om_stop he h₈ (fun _ _ h => opPlug_no_step (r := false)
      (payloadName_opPayload n 0 .unit) hK₁ h)
    have hK : K₁ = omK n := plug_inj_ctx (by simp [tickE, BoCa.BoLo.performE]) hst
    subst hK
    rw [eq_of_compS_empty_left hcak] at h₁ h₂
    obtain ⟨z, hzp, hz⟩ := (hash_shift ρp ρf ρk).mp ⟨fρ', h₂, h₃⟩
    have hfz : ResU.CompS ρf ρp z := ResU.CompS.comm hzp
    obtain ⟨z₀, hz₀, hY⟩ := compS_exch h₂ h₆
    have hzY : ResU.CompS z ρk fρ'p := by rwa [ResU.CompS.functional hz₀ hfz] at hY
    exact (hcont ls' (Ext.refl ls' ρk)).1 closeV PMap.empty ρk (vC_close.mpr ⟨rfl, rfl⟩)
      (ResU.comp_empty_right ρk) ⟨z, fρ'p, ps', hz, hzY, hT', htg'⟩ (om_back n closeV)
  · obtain ⟨⟨-, -, hT₁, ha⟩, -⟩ := pure_sep_iff.mp hp
    rcases ext_some hT₁ with ⟨-, -, rfl⟩ | hT₁
    · exact absurd ha (by show ¬ (false = true); simp)
    · cases hT₁

/-- So `Ω` is not in `cwp`. -/
theorem omega_not_cwp (δ : LSub) (d : UInt32) (Q : List SRec → Val → WProp) :
    ¬ cwp δ d OpTab.empty Q [] (omE d) PMap.empty :=
  fun h => omega_not_closing δ d Q (closing_of_cwp rfl h)

end BoCa.Fig16.LogRel.Core.DivEffect

end

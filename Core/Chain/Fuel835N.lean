import Core.Chain.Let835N
import Core.DivFuel

/-!
# `div_fuel` at `SemJN`  `[spec §14]`

Core's `divFuel_compatX` (`Core/DivFuel.lean`), step by step, at the chain relation (interface
entries E8, E11, E13):

    div_fuel : !U(U(1 ⊸ F_{tick, Σ} A) ⊗ I32 ⊸ F_Σ A)

* the handler's steps at `erwp`: pure steps for free (`erwp_pureSteps`, Core's `ewp_pureSteps`);
  `κ`'s resumption under a frame (`erwp_kappaC_resume_in`, Core's `ewp_kappaC_resume_in`); a tick
  under a one-clause handler of `Div`, `κ` given its cell (`erwp_hnd_tick`, Core's `hnd_tick`);
  a tick answered *close* or *next* (`fuel_tick_zeroN`, `fuel_tick_succN`, Core's
  `fuel_tick_zero`, `fuel_tick_succ`), over Core's `fuel_clause`, `FuelFrame`, `nextK_frame`,
  `spentK_frame`, read unchanged;
* **`fuel_totalN`** (Core's `fuel_total`): `div_fuel` of a computation at the row `tick, Σ` is at
  `Σ`. Core inducts on the budget and, inside, on `cwp`'s segment, and treats the spent budget by
  `Closing` (`fuel_closing`). A `Div` row is a row of the chain's table (E13), so here the
  induction is on the index alone: every tick's continuation is owed below the tick's index,
  whether it is answered *next* or *close*. An operation of `Σ` passes the handler with its frame
  (Core's `fuel_fwd`, `hnd_fwd`), its cancel carried through the plain frame
  (`tabN_plainCancel`);
* `divFuel_compatN`: the constant at `SemJN`. The callback runs at the function's own world
  (`LocTy.extR_refl`) and view.

No typed code runs after a resumption here: an answer of `Σ` goes back into the callback's own
continuation, so `let_compatN_ansC`'s `hAns` is not needed.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE hndVal kappaC
  kappaCell kappaAt clauseAt freeE)

/-- **Pure steps in front of an `erwp`, for free** (Core's `ewp_pureSteps`). -/
theorem erwp_pureSteps {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hTd : Tb.Down) {Q : PostN}
    (hQ : Q.Down) {e e' : Expr} (hs : PureSteps (ℍ := ℍ) e e') {n : Nat} {ls : List SRec}
    {ρ : WRes} (h : erwp (ℍ := ℍ) Φ Tb Q n ls e' ρ) : erwp (ℍ := ℍ) Φ Tb Q n ls e ρ := by
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl => exact h
  | head hab _ ih =>
      refine erwp_det hΦ hTd hQ (fun μ => ?_) ih
      obtain ⟨K, a, a', he, he', hh, hn⟩ := hab μ
      rw [he, he']
      exact step1Only_plug hh hn K

/-- **Resuming a `κ` that owns a cell, under a frame** (Core's `ewp_kappaC_resume_in`): the cell is
freed, one step, and `K₀[hnd H K[w]]` runs at the index left. -/
theorem erwp_kappaC_resume_in {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hL : Tb.Local)
    (hTd : Tb.Down) {Q : PostN} (hQ : Q.Down) (K₀ : Kont) (hasCancel : Bool) (ℓ : Loc) (H : Val)
    (K : Kont) (w : Val) {k : Nat} {ls : List SRec} {ρ : WRes}
    (h : (ptoOwn ℓ Val.unit ⋆
      erwp (ℍ := ℍ) Φ Tb Q (k - 1) ls (K₀.plug (hndE H (K.plug (.val w))))) ρ) :
    erwp (ℍ := ℍ) Φ Tb Q k ls
      (K₀.plug (.app (.app (kappaC hasCancel ℓ H K) (.val (Val.inj₁ .unit))) (.val w))) ρ := by
  let K₁ : Kont := K₀.comp (.appL .hole w)
  have e₀ : ∀ x, K₀.plug (.app x (.val w)) = K₁.plug x := fun x => by
    simp only [K₁, Kont.plug_comp]; rfl
  rw [e₀]
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl K₁) ?_
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl K₁) ?_
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.seq μ _) rfl K₁) ?_
  have e₁ : ∀ x, K₁.plug (.seq (freeE (.val (Val.loc ℓ))) x) =
      (K₁.comp (.seq .hole x)).plug (freeE (.val (Val.loc ℓ))) := fun x => by
    rw [Kont.plug_comp, Kont.plug_comp, Kont.plug_comp]; rfl
  show erwp (ℍ := ℍ) Φ Tb Q k ls (K₁.plug (.seq (freeE (.val (Val.loc ℓ))) _)) ρ
  rw [e₁]
  refine erwp_free hΦ hL _ ℓ Val.unit ?_
  obtain ⟨ρ₁, ρ₂, hc, hp, hq⟩ := h
  refine ⟨ρ₁, ρ₂, hc, hp, ?_⟩
  rw [Kont.plug_comp]
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.seq μ _) rfl K₁) ?_
  rw [← e₀]
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ w) rfl K₀) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, kappa_resume_subst]
  exact hq

/-- **A tick under a handler of `Div` with one clause `c`**, of a must-resume operation, in a
context `K₀` (Core's `hnd_tick`): the clause, with `κ` given its cell, at the index the
allocation leaves. -/
theorem erwp_hnd_tick {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hL : Tb.Local) (hTd : Tb.Down)
    {Q : PostN} (hQ : Q.Down) (hr c : Val) (K₀ K₁ : Kont) (hK₁ : K₁.HasHnd divEff = false)
    {n : Nat} {ls : List SRec} {ρ : WRes}
    (h : ∀ ℓ : Loc, (ptoOwn ℓ Val.unit ─⋆ erwp (ℍ := ℍ) Φ Tb Q (n - 1) ls (K₀.plug (.app (.val c)
      (.val (Val.pair .unit (kapV ℓ (hndVal divEff (qualsVal [.lin]) hr (c.pair .unit)) K₁)))))) ρ) :
    erwp (ℍ := ℍ) Φ Tb Q n ls
      (K₀.plug (hndE (hndVal divEff (qualsVal [.lin]) hr (c.pair .unit)) (K₁.plug tickE))) ρ := by
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.hop μ divEff 0 (qualsVal [.lin]) hr
    (Val.pair c .unit) c .unit K₁ (clauseAt_one c) hK₁) rfl K₀) ?_
  rw [kappaAt_lin]
  have e : K₀.plug (.app (.val c) (.pair (.val .unit)
      (kappaCell false (hndVal divEff (qualsVal [Qual.lin]) hr (c.pair Val.unit)) K₁))) =
      (K₀.comp (.appR (.val c) (.pairR .unit .hole))).plug
        (kappaCell false (hndVal divEff (qualsVal [Qual.lin]) hr (c.pair Val.unit)) K₁) := by
    rw [Kont.plug_comp]; rfl
  rw [e]
  refine erwp_kappaCell hΦ hL hTd hQ false _ K₁ _ (fun ℓ σ₁ σ₂ hp hc => ?_)
  rw [Kont.plug_comp]
  exact h ℓ σ₁ σ₂ hp hc

/-- A substitution at `0` undoes a shift by one. -/
theorem substZero_shiftOne (s : Val) (e : Expr) : Expr.subst 0 s (Expr.shift 1 0 e) = e := by
  have h := subst_shift_succ (j := 0) (d := 0) s e le_rfl
  rwa [Expr.shift_zero] at h

/-- **A tick under `div_fuel` with the budget spent** resumes `κ` with *close*, under `spent`
(Core's `fuel_tick_zero`): two steps, the cell's allocation and its release. -/
theorem fuel_tick_zeroN {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hL : Tb.Local) (hTd : Tb.Down)
    {Q : PostN} (hQ : Q.Down) {K : Kont} (hK : FuelFrame 0 K) (K₁ : Kont)
    (hK₁ : K₁.HasHnd divEff = false) {n : Nat} {ls : List SRec} {ρ : WRes}
    (h : erwp (ℍ := ℍ) Φ Tb Q (n - 1 - 1) ls (spentK.plug (hndE fuelH (K₁.plug (.val closeV)))) ρ) :
    erwp (ℍ := ℍ) Φ Tb Q n ls (K.plug (hndE fuelH (K₁.plug tickE))) ρ := by
  refine erwp_hnd_tick hΦ hL hTd hQ fuelR fuelC K K₁ hK₁ (fun ℓ σ₁ σ₂ hp hc => ?_)
  refine erwp_pureSteps hΦ hTd hQ (fuel_clause hK _) ?_
  simp only [fixSelf]
  refine erwp_pureSteps hΦ hTd hQ (PureSteps.head (fun μ => Head.case₁ μ .unit _ _) rfl) ?_
  have e : Expr.subst 0 Val.unit (.app (.val spentV) (.app (.app
      (.val ((kapV ℓ fuelH K₁).shift 1 0)) (.val (Val.inj₁ .unit))) (.val closeV))) =
      spentK.plug (.app (.app (kappaC false ℓ fuelH K₁) (.val (Val.inj₁ .unit))) (.val closeV)) := by
    simp [spentK, spentV, closeV, kapV_eq, Kont.plug]
    simp only [Expr.subst, substZero_shiftOne]
    rfl
  show erwp (ℍ := ℍ) Φ Tb Q (n - 1) ls (Expr.subst 0 Val.unit (.app (.val spentV) (.app (.app
    (.val ((kapV ℓ fuelH K₁).shift 1 0)) (.val (Val.inj₁ .unit))) (.val closeV)))) σ₂
  rw [e]
  exact erwp_kappaC_resume_in hΦ hL hTd hQ spentK false ℓ fuelH K₁ closeV
    ⟨σ₁, ρ, ResU.CompS.comm hc, hp, h⟩

/-- **A tick under `div_fuel` with budget left** resumes `κ` with *next*, under the fixed point
at one less (Core's `fuel_tick_succ`). -/
theorem fuel_tick_succN {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hL : Tb.Local) (hTd : Tb.Down)
    {Q : PostN} (hQ : Q.Down) {k : UInt32} (hk : k ≠ 0) {K : Kont} (hK : FuelFrame k K)
    (K₁ : Kont) (hK₁ : K₁.HasHnd divEff = false) {n : Nat} {ls : List SRec} {ρ : WRes}
    (h : erwp (ℍ := ℍ) Φ Tb Q (n - 1 - 1) ls
      ((nextK (fixF k)).plug (hndE fuelH (K₁.plug (.val nextV)))) ρ) :
    erwp (ℍ := ℍ) Φ Tb Q n ls (K.plug (hndE fuelH (K₁.plug tickE))) ρ := by
  refine erwp_hnd_tick hΦ hL hTd hQ fuelR fuelC K K₁ hK₁ (fun ℓ σ₁ σ₂ hp hc => ?_)
  refine erwp_pureSteps hΦ hTd hQ (fuel_clause hK _) ?_
  rw [show fixSelf fuelStep k = Val.inj₂ (fixF k) from fixSelf_succ hk]
  refine erwp_pureSteps hΦ hTd hQ (PureSteps.head (fun μ => Head.case₂ μ (fixF k) _ _) rfl) ?_
  have e : Expr.subst 0 (fixF k) (.app (.val (.lam (.app (.var 1) (.var 0))))
      (.app (.app (.val ((kapV ℓ fuelH K₁).shift 1 0)) (.val (Val.inj₁ .unit))) (.val nextV))) =
      (nextK (fixF k)).plug
        (.app (.app (kappaC false ℓ fuelH K₁) (.val (Val.inj₁ .unit))) (.val nextV)) := by
    have hc := fixF_closed k
    have hv : Val.shift 1 0 (fixF k) = fixF k := Subtype.ext (closed_shift hc 1 0)
    simp [nextK, nextV, kapV_eq, Kont.plug]
    simp only [Expr.subst, substZero_shiftOne, hv]
    simp
  show erwp (ℍ := ℍ) Φ Tb Q (n - 1) ls (Expr.subst 0 (fixF k) (.app (.val (.lam (.app (.var 1)
      (.var 0)))) (.app (.app (.val ((kapV ℓ fuelH K₁).shift 1 0)) (.val (Val.inj₁ .unit)))
        (.val nextV)))) σ₂
  rw [e]
  exact erwp_kappaC_resume_in hΦ hL hTd hQ (nextK (fixF k)) false ℓ fuelH K₁ nextV
    ⟨σ₁, ρ, ResU.CompS.comm hc, hp, h⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload hndE hndVal)

/-- The table of `tick, Σ`: the tick's entry over the table of `Σ`. -/
theorem tabN_tick (S : Row) (A : VTy) (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) :
    tabN (ℍ := ℍ) (CTy.effOf (tickSig :: S) A) δ Θ c = extTabN divEff 0
      (entN .lin nextTy (fun k v ρ => vN (ℍ := ℍ) .unit δ Θ k v ρ)
        (fun k v ρ => vN (ℍ := ℍ) nextTy δ Θ k v ρ) (finN (ℍ := ℍ) (.ret .unit) δ Θ c))
      (tabN (ℍ := ℍ) (CTy.effOf S A) δ Θ c) := rfl

/-- **`div_fuel` is total** (Core's `fuel_total`): under a frame at any budget, a computation at
the row `tick, Σ` is, handled, at `Σ`. By induction on the index: a tick's continuation, answered
*next* (the frame at one less) or *close* (the frame `spent`), is owed below the tick's index; an
operation of `Σ` passes the handler with its frame. -/
theorem fuel_totalN {S : Row} (hS : ∀ o ∈ S, o.n ≠ divEff) {A : VTy} {δ : LSub} {Θ : LocTy}
    (hΘ : Θ.Down) {c : Loc → Option Life} :
    ∀ (n : Nat) (k : UInt32) (K : Kont), FuelFrame k K → ∀ (ls : List SRec) (e : Expr) (ρ : WRes),
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN (ℍ := ℍ) (CTy.effOf (tickSig :: S) A) δ Θ c))
        (fun k _ v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) n ls e ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN (ℍ := ℍ) (CTy.effOf S A) δ Θ c))
        (fun k _ v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) n ls (K.plug (hndE fuelH e)) ρ := by
  have hΦ := LocTy.view_down hΘ c
  have hToutD := tabN_down (ℍ := ℍ) (CTy.effOf S A) δ Θ hΘ c
  have hLin := opTableN_local (tabN (ℍ := ℍ) (CTy.effOf (tickSig :: S) A) δ Θ c)
  have hLout := opTableN_local (tabN (ℍ := ℍ) (CTy.effOf S A) δ Θ c)
  have hDout := opTableN_down hToutD
  have hQ : PostN.Down (fun k (_ : List SRec) v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) :=
    fun k _ v ρ h => vN_down A δ Θ k v ρ h
  have hsame : ∀ m i, ¬ (m = divEff ∧ i = 0) →
      tabN (ℍ := ℍ) (CTy.effOf (tickSig :: S) A) δ Θ c m i =
        tabN (ℍ := ℍ) (CTy.effOf S A) δ Θ c m i := by
    intro m i h
    rw [tabN_tick]
    simp only [extTabN, h, if_false]
  have hnone : ∀ i, tabN (ℍ := ℍ) (CTy.effOf S A) δ Θ c divEff i = none := by
    intro i
    rw [tabN_effOf_find]
    cases hf : Row.find S divEff i with
    | none => rfl
    | some o => exact absurd (Row.find_mem hf).2.1 (hS o (Row.find_mem hf).1)
  have hdead : ∀ (K K₁ : Kont), K.dead = K →
      ((K.comp (hndK fuelH)).comp K₁).dead = (K.comp K₁).dead := by
    intro K K₁ hd
    rw [dead_comp, dead_comp, dead_comp, hd,
      show fuelH = hndVal divEff (qualsVal [.lin]) fuelR (Val.pair fuelC .unit) from rfl,
      dead_hndK, Kont.comp_hole]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro k K hK ls e ρ h
  have e₁ : ∀ x, K.plug (hndE fuelH x) = (K.comp (hndK fuelH)).plug x := fun x => by
    rw [Kont.plug_comp]; rfl
  rw [e₁, erwp_eq]
  refine rwpG_bind hΦ (K.comp (hndK fuelH)) ?_
  refine rwpG_mono_le (fun k' hk ls' t σ ht => ?_) (erwp_unfold_at hLin le_rfl h)
  rcases ht with ⟨v, rfl, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · -- `[ret]`
    rw [← e₁]
    exact erwp_unfold_at hLout hk (erwp_pureSteps hΦ hDout hQ (fuel_ret hK v) (erwp_val hv))
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    by_cases hmi : m = divEff ∧ i = 0
    · -- a tick: answered *close* once the budget is spent, *next* otherwise
      obtain ⟨rfl, rfl⟩ := hmi
      rw [tabN_tick] at hT
      simp only [extTabN, and_self, if_true, Option.some.injEq] at hT
      subst hT
      obtain ⟨rfl, rfl⟩ : v = Val.unit ∧ ρa = PMap.empty := hA
      obtain rfl := eq_of_compS_empty_left hcak
      rw [← e₁]
      refine erwp_unfold_at hLout hk ?_
      show erwp (ℍ := ℍ) _ _ _ k' ls' (K.plug (hndE fuelH (K₁.plug tickE))) σ
      rcases Nat.lt_or_ge k' 1 with hk1 | hk1
      · obtain rfl : k' = 0 := by omega
        exact erwp_zero
      have hres : ∀ w, vN (ℍ := ℍ) nextTy δ Θ (k' - 1 - 1) w PMap.empty →
          erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN (ℍ := ℍ) (CTy.effOf (tickSig :: S) A) δ Θ c))
            (fun k _ v ρ => vN (ℍ := ℍ) A δ Θ k v ρ) (k' - 1 - 1) ls' (K₁.plug (.val w)) σ := by
        intro w hw
        have h₁ := (hcont ls' (extF_refl ls' σ)).1 (k' - 1 - 1) (by omega) w PMap.empty σ hw
          (ResU.comp_empty_right σ)
        simp only [erwpC, show k' - 1 - 1 < n by omega, if_true] at h₁
        exact h₁
      by_cases hk0 : k = 0
      · subst hk0
        exact fuel_tick_zeroN hΦ hLout hDout hQ hK K₁ (by simpa using hK₁)
          (ih (k' - 1 - 1) (by omega) 0 spentK spentK_frame ls' _ σ
            (hres closeV (Or.inr ⟨Val.unit, rfl, rfl, rfl⟩)))
      · exact fuel_tick_succN hΦ hLout hDout hQ hk0 hK K₁ (by simpa using hK₁)
          (ih (k' - 1 - 1) (by omega) (k - 1) _ (nextK_frame k) ls' _ σ
            (hres nextV (Or.inl ⟨Val.unit, rfl, rfl, rfl⟩)))
    · -- an operation of `Σ` passes the handler with its frame
      have hT' := (hsame m i hmi) ▸ hT
      have hm : m ≠ divEff := by rintro rfl; rw [hnone] at hT'; cases hT'
      have hKo : ((K.comp (hndK fuelH)).comp K₁).HasHnd m = false := by
        rw [hasHnd_comp, hasHnd_comp, hK.1,
          show fuelH = hndVal divEff (qualsVal [.lin]) fuelR (Val.pair fuelC .unit) from rfl,
          hndK_hasHnd, hK₁]
        simpa using Ne.symm hm
      have ht' : (K.comp (hndK fuelH)).plug (K₁.plug (performE (.val (opPayload m i v)))) =
          ((K.comp (hndK fuelH)).comp K₁).plug (opE false (opPayload m i v)) := by
        simp only [Kont.plug_comp]; rfl
      rw [ht']
      refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
        ⟨(K.comp (hndK fuelH)).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT', ha⟩
          ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun k'' hk'' w τ₁ τ₂ hB hcτ => ?_,
            fun hq' => ?_⟩⟩⟩))
      · have h₁ := (hcont ls'' he).1 k'' hk'' w τ₁ τ₂ hB hcτ
        simp only [erwpC, show k'' < n by omega, if_true] at h₁ ⊢
        rw [Kont.plug_comp, ← e₁]
        exact ih k'' (by omega) k K hK ls'' _ τ₂ h₁
      · intro P hP
        show P k' ls'' (((K.comp (hndK fuelH)).comp K₁).dead.plug _) ρk
        rw [hdead K K₁ hK.2.2.1]
        exact tabN_plainCancel hΦ (CTy.effOf S A) m i en hT' ha hq' K hK.1 (hK.2.1 0) k' ls''
          K₁ ρk ((hcont ls'' he).2 hq') P hP
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    by_cases hmi : m = divEff ∧ i = 0
    · -- the tick is not abortive
      obtain ⟨rfl, rfl⟩ := hmi
      rw [tabN_tick] at hT
      simp only [extTabN, and_self, if_true, Option.some.injEq] at hT
      subst hT
      simp [entN, VTy.isZero] at ha
    · -- an abortive operation of `Σ` passes the handler
      have hT' := (hsame m i hmi) ▸ hT
      have hm : m ≠ divEff := by rintro rfl; rw [hnone] at hT'; cases hT'
      have hKo : ((K.comp (hndK fuelH)).comp K₁).Catches m = false := by
        rw [catches_comp, catches_comp, hK.2.1,
          show fuelH = hndVal divEff (qualsVal [.lin]) fuelR (Val.pair fuelC .unit) from rfl,
          hndK_catches, hK₁]
        simpa using Ne.symm hm
      have ht' : (K.comp (hndK fuelH)).plug (K₁.plug (raiseE (.val (opPayload m i v)))) =
          ((K.comp (hndK fuelH)).comp K₁).plug (opE true (opPayload m i v)) := by
        simp only [Kont.plug_comp]; rfl
      rw [ht']
      exact rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
        ⟨(K.comp (hndK fuelH)).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT', ha⟩
          ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩⟩))

/-- **`div_fuel` at `SemJN`** (Core's `divFuel_compatX`): total at the rest of the row. The
callback is forced at the function's own world (`LocTy.extR_refl`) and view, applied at `()`;
`div_fuel (t, k)` steps to the handler under the budget's frame (`divFuel_steps`), and
`fuel_totalN` takes it to the row `Σ`. -/
theorem divFuel_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {A : VTy}
    (hS : ∀ o ∈ S, o.n ≠ divEff) (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val divFuelV) (.val (divFuelTy S A)) := by
  intro δ γ Θ c n ls ρ _ _ _ _ hg
  obtain rfl := gN_deadP hΓ hg
  show erwp (ℍ := ℍ) _ _ _ n ls (substAll γ (.val divFuelV)) PMap.empty
  rw [substAll_closed divFuelV_closed]
  refine erwp_val (v := divFuelV) ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k hk v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨t, vk, σ₁, σ₂, rfl, hc, ht, ⟨⟨kk, rfl⟩, rfl⟩⟩ := hv
  obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right σ₁)
  have hΦ := LocTy.view_down hΘ'.1 c''
  have ht' := ht Θ' (LocTy.extR_refl Θ' _) hΘ' c'' hcon ls' c'' k le_rfl Val.unit PMap.empty _
    (ResU.comp_empty_right _) ⟨rfl, rfl⟩ hcon
  have hin := (cN_effOf (tickSig :: S) A δ Θ' c'' k ls' _ _).mp ht'
  refine (cN_effOf S A δ Θ' c'' k ls' _ _).mpr ?_
  refine erwp_pureSteps hΦ (opTableN_down (tabN_down _ δ Θ' hΘ'.1 c''))
    (fun k _ v ρ h => vN_down A δ Θ' k v ρ h) (divFuel_steps t kk) ?_
  exact fuel_totalN hS hΘ'.1 k kk (fuelK kk) (fuelK_frame kk) ls' _ _ hin

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end

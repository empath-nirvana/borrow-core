import Core.Chain.Let835N
import Core.DivFuel

/-!
# `div_fuel` at `SemJN₀`  `[spec §14]`

Core's `divFuel_compatX` (`Core/DivFuel.lean`), step by step, at the chain relation (interface
entries E8, E11, E13):

    div_fuel : !U(U(1 ⊸ F_{tick, Σ} A) ⊗ I32 ⊸ F_Σ A)

* the handler's steps at `erwp`: pure steps for free (`erwp_pureSteps`, Core's `ewp_pureSteps`);
  `κ`'s resumption under a frame (`erwp_kappaC_resume_in`, Core's `ewp_kappaC_resume_in`); a tick
  under a one-clause handler of `Div`, `κ` given its cell (`erwp_hnd_tick`, Core's `hnd_tick`);
  a tick answered *close* or *next* (`fuel_tick_zeroN`, `fuel_tick_succN`, Core's
  `fuel_tick_zero`, `fuel_tick_succ`), over Core's `fuel_clause`, `FuelFrame`, `nextK_frame`,
  `spentK_frame`, read unchanged;
* **`fuel_totalN₀`** (Core's `fuel_total`): `div_fuel` of a computation at the row `tick, Σ` is at
  `Σ`. Core inducts on the budget and, inside, on `cwp`'s segment, and treats the spent budget by
  `Closing` (`fuel_closing`). A `Div` row is a row of the chain's table (E13), so here the
  induction is on the index alone: every tick's continuation is owed below the tick's index,
  whether it is answered *next* or *close*. An operation of `Σ` passes the handler with its frame
  (Core's `fuel_fwd`, `hnd_fwd`), its cancel carried through the plain frame
  (`tabN_plainCancel`);
* `divFuel_compatN₀`: the constant at `SemJN₀`. The callback runs at the function's own world
  (`LocTy.extR_refl`) and view.

No typed code runs after a resumption here: an answer of `Σ` goes back into the callback's own
continuation.
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

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end

import Targets.I.Combined
import Targets.Instance.ContUse

/-!
# The interaction — route 8.4's ghost-to-run coupling, at the capture cell (TIER1-PLAN §4; decision S6)

Route 8.4 gives a linear or affine `κ` an obligation: created at `[op]`, consumed where that `κ` is
resumed or cancelled and nowhere else, so that leak freedom at a run's end yields S6's count.  The
probe of BoLo's original machine found no such obligation: `[op]` allocated nothing, so R1 (a
capture never used) ran, at the empty heap throughout, to `ff`, and was in Core's relation.

The capture cell (SPEC §25) is that obligation, and BoLo's relation sees it.

* **A closed program's relation at its pure type is BoLo's `wpTS`** (`cC_ret_eq`), and a run of
  head steps that keep the heap, ending at a value related at the empty resource, puts its start in
  the relation (`semC_of_headChain`).
* **R1 at a linear or affine operation is not in Core's relation at `F bool`** (`not_semC_R1`):
  its run allocates `κ`'s cell, never releases it, and ends at `ff`; Core's relation at a returner
  gives every run from the empty memory an end at the empty memory (`theorem32D`).
* **BoLo's world at the empty heap is the empty resource** (`lower_empty_eq`), so no resource there
  owns anything (`noOwn_of_lower_empty`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.I
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Head Kont Step1N Steps)
open BoCa.Lifetime (LSub LifeCtx)
open BoCa.BoLo (capTag kappaC kappaCBody)

/-! ### BoLo's world at the empty heap -/

/-- **BoLo's world at the empty heap is the empty resource**: every cell of a resource reappears in
its flattening (`ResU.Flat.get`), and the flattening lowers to the heap. -/
theorem lower_empty_eq {ρ : WRes} (h : ResU.Lower ρ Adequacy.emptyMem) : ρ = PMap.empty := by
  obtain ⟨σ, hσ, hm⟩ := h
  refine PMap.ext fun l => ?_
  rw [PMap.empty_get]
  cases hg : ρ.get l with
  | none => rfl
  | some ψ =>
      obtain ⟨χ, hχ, -⟩ := ResU.Flat.get hσ hg
      have hl := hm l
      rw [hχ] at hl
      simp [Adequacy.emptyMem] at hl

/-- At the empty heap no resource of the world owns anything. -/
theorem noOwn_of_lower_empty {ρ : WRes} (h : ResU.Lower ρ Adequacy.emptyMem) : NoOwn ρ := by
  rw [lower_empty_eq h]; exact noOwn_empty

/-! ### The relation at a returner, and chains of head steps -/

/-- **The relation at a returner is `wpTS`**: no protocol table occurs in it. -/
theorem cC_ret_eq (A : VTy) (ls : List SRec) (δ : LSub) (e : Expr) :
    cC (.ret A) ls δ e = wpTS ls e (fun ls'' => vC true A ls'' δ) := rfl

/-- A chain of head steps that allocate nothing, in front of `wpTS`. -/
theorem wpTS_of_headChain {e e' : Expr} {q : List (Kont × Expr × Expr)}
    (h : HeadChain (ℍ := ℍ) e q e') (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls e' Q) (wpTS ls e Q) := by
  induction h with
  | nil => exact fun _ h => h
  | cons hh hn _ ih =>
      exact fun ρ h => wpTS_step (fun μ => (Step1N.head (hh μ) hn).plug _) ls Q ρ (ih ρ h)

/-- A closed program whose run is a chain of head steps to a value related at `A` at the empty
resource is in the relation at `F A`. -/
theorem semC_of_headChain {Δ : LifeCtx} {e : Expr} {q : List (Kont × Expr × Expr)} {v : Val}
    {A : VTy} (hc : closedAt 0 e = true) (h : HeadChain (ℍ := ℍ) e q (.val v))
    (hv : ∀ ls δ, vC true A ls δ v PMap.empty) : SemC Δ [] e (.ret A) := by
  intro δ γ ls ρ _ hg
  have hρ : ρ = PMap.empty := gDenC_persistent (fun s hs => absurd hs (List.not_mem_nil)) hg
  subst hρ
  show wpTS ls (Expr.psub 0 γ e) _ PMap.empty
  rw [psub_closedAt e γ hc (le_refl 0)]
  exact wpTS_of_headChain h ls _ PMap.empty (wpTS_val ls v _ PMap.empty (hv ls δ))

/-- `ff` and `tt` are related at `bool`, at the empty resource. -/
theorem vC_ff (ls : List SRec) (δ : LSub) :
    vC true Inst.boolT ls δ (Val.inj₁ Val.unit) (PMap.empty : WRes) :=
  Or.inl ⟨Val.unit, pure_sep_mk rfl ⟨rfl, rfl⟩⟩

theorem vC_tt (ls : List SRec) (δ : LSub) :
    vC true Inst.boolT ls δ (Val.inj₂ Val.unit) (PMap.empty : WRes) :=
  Or.inr ⟨Val.unit, pure_sep_mk rfl ⟨rfl, rfl⟩⟩

/-! ### The capture cell, in Core's relation -/

open Targets.Inst (rProg dropV rH rK rRet cellAff kappaAt_cell) in
/-- **R1 at a linear or affine operation is not in Core's relation at `F bool`**: from the empty
memory its run is the catch, the allocation of `κ`'s cell at `0`, `κ`'s β-step, the clause's β-step
and its `let`, ending at `ff` with the cell still allocated; Core's relation at a returner gives
every run from the empty memory an end at the empty memory (`theorem32D`). -/
theorem not_semC_R1 (n : UInt32) {q : Qual} (qs : List Qual) (hq : q ≠ .unr) :
    ¬ SemC LifeCtx.empty [] (rProg n (q :: qs) dropV) (.ret Inst.boolT) := by
  intro h
  have hwp := h LSub.empty [] [] PMap.empty Adequacy.models_empty (gDenC_nil _ _)
  have hwp' : wpTS [] (rProg n (q :: qs) dropV) (fun _ _ => Fig16.BoLo.pure True)
      (PMap.empty : WRes) := by
    have he : substAll [] (rProg n (q :: qs) dropV) = rProg n (q :: qs) dropV :=
      Adequacy.psub_nil 0 _
    rw [he] at hwp
    exact wpTS_mono (fun _ _ _ hv => ⟨(vC_sum_unit_pure (A := .unit) (fun h => h.1) hv).1, trivial⟩)
      PMap.empty hwp
  -- the run
  have htag : capTag (qualsVal (q :: qs)).1 (0 : UInt32).toNat = q.tag := by
    rw [show (0 : UInt32).toNat = 0 from rfl, capTag_qualsVal _ 0 (by simp)]; rfl
  have hop := Head.hop (ℍ := ℍ) Adequacy.emptyMem n 0 (qualsVal (q :: qs)) ⟨rRet, .lam⟩
    ⟨Inst.clausesE [dropV.1], .pair dropV.2 .unit⟩ dropV Val.unit rK
    (Inst.clauseAt_clausesE [dropV.1] 0 dropV.2 rfl) rfl
  rw [htag, kappaAt_cell hq] at hop
  have hal := Head.alloc (ℍ := ℍ) Adequacy.emptyMem Val.unit 0 rfl
  have hb := Head.beta (ℍ := ℍ) (Adequacy.emptyMem.upd 0 Val.unit)
    (kappaCBody (cellAff q) (rH n (q :: qs) dropV) rK) (Val.loc 0)
  rw [kappaCBody_subst] at hb
  have hs : Steps Adequacy.emptyMem (rProg n (q :: qs) dropV) (Adequacy.emptyMem.upd 0 Val.unit)
      (.val (Val.inj₁ Val.unit)) :=
    .more ⟨.hole, _, _, Inst.rProg_eq n (q :: qs) dropV, rfl, hop⟩ <|
    .more ⟨.appR (.val dropV) (.pairR Val.unit
      (.appR (.val (Val.lam (kappaCBody (cellAff q) (rH n (q :: qs) dropV) rK))) .hole)),
      _, _, rfl, rfl, hal⟩ <|
    .more ⟨.appR (.val dropV) (.pairR Val.unit .hole), _, _, rfl, rfl, hb⟩ <|
    .more ⟨.hole, _, _, rfl, rfl, Head.beta _ _ (Val.pair Val.unit
      ⟨kappaC (cellAff q) 0 (rH n (q :: qs) dropV) rK, isVal_kappaC _ _ _ _⟩)⟩ <|
    .more ⟨.hole, _, _, rfl, rfl, Head.letpair _ Val.unit
      ⟨kappaC (cellAff q) 0 (rH n (q :: qs) dropV) rK, isVal_kappaC _ _ _ _⟩ (.inj₁ .unit)⟩ <|
    .refl _ _
  obtain ⟨v, hs', -⟩ := theorem32D _ (fun _ => True) hwp' hs
  obtain ⟨h₁, -⟩ := steps_from_val (v := Val.inj₁ Val.unit) hs'
  have := congrFun h₁ 0
  simp [Adequacy.emptyMem, BoCa.BoLo.Heap.upd] at this

end Targets.I

end

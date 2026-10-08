import Targets.I.Combined
import Targets.I.OpenRel
import Targets.I.Restricted.InstanceSafety
import Targets.Instance.J1

/-!
# The interaction — tier 1 at `J₁` (TIER1-PLAN §2; decision D5)

`J₁` is Core's kernel (SPEC §24) over the open types, with the row `∀`
(`Targets/Instance/J1.lean`).  Its reading is Core's kernel (`Inst.j1_read`), so B's side of tier 1
is Core's:

* **B1** (`fl_core_J₁`): `fundamentalC`, which now covers `[let-poly]` and the general `[handle]`;
* **B's guarantees** (`guarantees_J₁`): B0–B7 and the bounds, B5 from B4′ through the
  step-for-step simulation (`releasedOnceReuse_J₁`);
* **the pins** (`pins_J₁`): today's admissibility, Core's unr-free rules and outlives judgements,
  and the answering borrow form (`i4a_tier1`).

**FL at `J₁`'s open judgements** (`flOpen_J₁_mono`, beside done): at a context with no polymorphic
slot, every judgement of `J₁` is in the relation at the open types, a polymorphic function type
read through `ojdgW` as the intersection of its instances (Law 1, `oretThunk`), each instance by
`fundamentalC`.  At a context with a polymorphic slot it is not proved: `J₁` closes such a slot by
the closed λ-values Core types at every instance, and a value `ovalW` relates there need not be one.

**A's (S) properties at `J₁`**, at every effect context (`sPropsNoCancel_J₁`): S0 and S4 (from
`LiveOK`, `liveOK_of_coreClosed`), the let law (`letLaw_ourInst_J₁`), S1 (`rowAlgebra_ourInst_J₁`),
`DataDiv`, S2 and S3 (`safety_of_coreClosed`, `effSafe_of_coreClosed`).  S5 waits on its bridges,
and S6 on a route (`Targets/I/GhostCoupling.lean`).  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.I
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx)
open Targets.Inst (OVTy OCTy OJdg OurTyping ourInst AdmEff J₁ J1Der j1_read octxDen octxRFree
  rowCtx_models_nil)

/-! ### B's side -/

/-- **B1 at `J₁`**: its reading is Core's kernel, where `fundamentalC` holds. -/
theorem fl_core_J₁ : FL (B.coreB (ℍ := ℍ)) J₁.read := by
  rw [j1_read]; exact fl_core_tier1

/-- **B5 at `J₁` and BoLo**: from B4′ (B1 and B2's return conjunct) through the step-for-step
simulation (`releasedOnceReuse_of_soundContracts`). -/
theorem releasedOnceReuse_J₁ : B.ReleasedOnceReuse (ℍ := ℍ) J₁.read (B.coreB (ℍ := ℍ)) := by
  rw [j1_read]
  exact releasedOnceReuse_of_soundContracts (soundContractsOfFL_ret fl_core_tier1 adequateRetAt_core)

/-- **B's guarantees at `J₁` and BoLo.** -/
theorem guarantees_J₁ : B.Guarantees (ℍ := ℍ) J₁.read (B.coreB (ℍ := ℍ)) := by
  rw [j1_read]
  have hFL := fl_core_tier1 (ℍ := ℍ)
  have hC : B.SoundContracts (ℍ := ℍ) tier1 (B.coreB (ℍ := ℍ)) :=
    soundContractsOfFL_ret hFL adequateRetAt_core
  exact ⟨extendsB_tier1, hFL, adequate_core, soundnessOfFL _ _ hFL adequate_core, hC,
    releasedOnceReuse_of_soundContracts hC, exclusiveB_core, lifetimeSound_core, wBound_core⟩

/-- **B's guarantees at `J₁` but B5.** -/
theorem guarantees_noB5_J₁ :
    B.ExtendsB J₁.read ∧ FL (B.coreB (ℍ := ℍ)) J₁.read ∧ Adequate (ℍ := ℍ) (B.coreB (ℍ := ℍ)) ∧
      Sound (ℍ := ℍ) J₁.read ∧ B.SoundContracts (ℍ := ℍ) J₁.read (B.coreB (ℍ := ℍ)) ∧
      B.ExclusiveB (B.coreB (ℍ := ℍ)) ∧ LifetimeSound (B.coreB (ℍ := ℍ)) J₁.read.out ∧
      B.WBound (B.coreB (ℍ := ℍ)) := by
  rw [j1_read]
  have hFL := fl_core_tier1 (ℍ := ℍ)
  exact ⟨extendsB_tier1, hFL, adequate_core, soundnessOfFL _ _ hFL adequate_core,
    soundContractsOfFL_ret hFL adequateRetAt_core, exclusiveB_core, lifetimeSound_core, wBound_core⟩

/-- **`Pins` at `J₁`**: today's admissibility, Core's unr-free rules and outlives judgements, and
the answering borrow form at Core's kernel. -/
theorem pins_J₁ : Pins J₁ admClosedOp .abortive := by
  unfold Pins
  rw [j1_read]
  exact ⟨admExtends_closedOp, extendsNU_tier1, outExtends_core, i4a_tier1⟩

/-! ### FL at the open judgements, through the intersection of the instances -/

theorem admRow_iff (k : Targets.RowCon) (r : Row) : Inst.AdmRow k r ↔ AdmRow k r := Iff.rfl

/-- **FL at `J₁`'s open judgements whose context has no polymorphic slot**: the open relation
(`ovalW`, `ojdgW`) holds of every such judgement.  A judgement at `U(∀ρ:k. C)` or `!U(∀ρ:k. C)` is
read as the intersection of its instances (`oretThunk`, Law 1), and Core types the λ-value at each
instance; every other judgement is `fundamentalC` at the instance. -/
theorem flOpen_J₁_mono {Θ : Targets.RowCtx} {Δ : LifeCtx} {Γ : Ctx OVTy} {e : Expr} {j : OJdg}
    (hd : J₁.der Θ Δ Γ e j) (hΓ : octxRFree Γ) (η : Targets.RowEnv) (hη : Θ.Models η) (δ : LSub)
    (γ : List Val) (i : Idx (B.coreB (ℍ := ℍ)).Stk) (ρ : WRes) (hδ : Δ.Models δ)
    (hg : ogDenW (B.coreB (ℍ := ℍ)) i η δ Γ γ ρ) :
    ojdgW (B.coreB (ℍ := ℍ)) j i η δ (substAll γ e) ρ := by
  obtain ⟨-, hj, hcore⟩ := hd
  have h := hcore η hη (fun _ => none) (Inst.closing_none (Inst.octx_noPoly_of_rFree hΓ))
  rw [Inst.fillS_none, Inst.octxStrip_of_rFree η hΓ] at h
  rw [ogDenW_rFree _ i η δ hΓ γ] at hg
  have sem : ∀ {J' : Jdg}, CDerives Δ (octxDen η Γ) e J' →
      SemW₀ (B.coreB (ℍ := ℍ)) Δ (octxDen η Γ) e J' := fun h' => semW₀_core.mpr (fundamentalC h')
  cases j with
  | comp C =>
      rw [ojdgW_rFree _ (j := .comp C) hj i η δ]
      exact sem h δ γ i ρ hδ hg
  | val A =>
      by_cases hP : A.isPoly = true
      · simp only [Inst.J1Core, hP, if_true] at h
        obtain ⟨b, rfl, hpers, hb⟩ := h
        have hOK : A.PolyOK := by
          rcases hj with hr | ⟨-, hk⟩
          · rw [Inst.OVTy.isPoly_of_rFree hr] at hP; cases hP
          · exact hk
        match A, hP, hOK, hpers, hb with
        | .thunk (.allR ρ' k C), _, ⟨hC, hnr⟩, _, hb =>
            intro r hr
            rw [oretThunk_rFree _ false hC]
            have hd' := hb _ ⟨r, (admRow_iff k r).mpr hr, rfl⟩
            exact sem (.ret (.thunkV (OCTy.isRet_den_of_notRet hnr _) hd')) δ γ i ρ hδ hg
        | .bang (.thunk (.allR ρ' k C)), _, ⟨hC, hnr⟩, hpers, hb =>
            intro r hr
            rw [oretThunk_rFree _ true hC]
            have hd' := hb _ ⟨r, (admRow_iff k r).mpr hr, rfl⟩
            exact sem (.ret (.bangThunkV (hpers rfl) (OCTy.isRet_den_of_notRet hnr _) hd'))
              δ γ i ρ hδ hg
      · have hr : A.RFree := by
          rcases hj with hr | ⟨hp, -⟩
          · exact hr
          · exact absurd hp hP
        have hP' : A.isPoly = false := by simpa using hP
        simp only [Inst.J1Core, hP', Bool.false_eq_true, if_false] at h
        rw [ojdgW_rFree _ (j := .val A) hr i η δ]
        exact sem h δ γ i ρ hδ hg

/-! ### A's side -/

/-- **A's (S) properties at `J₁`, S4, S5 and S6 aside**, at every effect context: S0 from
`LiveOK`, the let law, S1, `DataDiv`, S2 and S3. -/
theorem sPropsNoCancel_J₁ {Ξ : EffCtx} :
    (ourInst (ℍ := ℍ) orowRF Ξ J₁).MachShape ∧ (ourInst (ℍ := ℍ) orowRF Ξ J₁).LetLaw ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).RowAlgebra ∧ (ourInst (ℍ := ℍ) orowRF Ξ J₁).DataDiv ∧
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).Safety ∧ (ourInst (ℍ := ℍ) orowRF Ξ J₁).EffSafe :=
  ⟨Inst.machShape_orow (Inst.liveOK_of_coreClosed (D := J1Der) Inst.coreClosed_J₁),
    Inst.letLaw_ourInst_J₁, Inst.rowAlgebra_ourInst_J₁, Inst.dataDiv_ourInst,
    Inst.safety_of_coreClosed (D := J1Der) Inst.coreClosed_J₁,
    Inst.effSafe_of_coreClosed (D := J1Der) Inst.coreClosed_J₁⟩

/-- **S4 at `J₁`**, at an effect context whose resuming operations are unrestricted (`CatchUnr`):
there `κ` owns no cell, and the catch keeps the store (SPEC §25). -/
theorem handlerSem_J₁ {Ξ : EffCtx} (hU : Ξ.CatchUnr) : (ourInst (ℍ := ℍ) orowRF Ξ J₁).HandlerSem :=
  Inst.handlerSem_orow (Inst.liveOK_of_coreClosed (D := J1Der) Inst.coreClosed_J₁) hU

/-- **Tier 1 at `J₁`, given what is open**: A's (E) properties, S4, S5 and S6 at every admissible
effect context, and the composite's programs and rejections.  The rest of `Tier1 J₁` is proved:
A's (S) properties but S4, S5 and S6 (`sPropsNoCancel_J₁`), B's guarantees (`guarantees_J₁`), the
world's conjuncts at `coreW` (`tier1Core_world`), and the pins (`pins_J₁`).  S4's capture laws keep
the store, which the catch of a linear or affine operation does not (SPEC §25). -/
theorem tier1_J₁_of
    (hE : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).EProps)
    (hS4 : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).HandlerSem)
    (hC : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).Cancellation
      (ourInst (ℍ := ℍ) orowRF Ξ J₁).noFinRaise)
    (hU : ∀ Ξ, AdmEff Ξ → (ourInst (ℍ := ℍ) orowRF Ξ J₁).ContUseEv)
    (hAc : Accepts (ℍ := ℍ) J₁.read .abortive) (hRj : Rejects J₁.read) :
    Tier1 (ℍ := ℍ) J₁ := by
  obtain ⟨hB, hI, -, -⟩ := tier1Core_world (ℍ := ℍ)
  refine ⟨fun Ξ hΞ => ⟨?_, hE Ξ hΞ⟩, guarantees_J₁, hB, hI, pins_J₁, hAc, hRj⟩
  obtain ⟨h0, hl, h1, hd, h2, h3⟩ := sPropsNoCancel_J₁ (ℍ := ℍ) (Ξ := Ξ)
  exact ⟨h0, hl, h1, hd, h2, h3, hS4 Ξ hΞ, hC Ξ hΞ, hU Ξ hΞ⟩

end Targets.I

end

import Targets.I.Combined
import Targets.Instance.ContUse

/-!
# The interaction — route 8.4's ghost-to-run coupling, probed (TIER1-PLAN §4; decision D5)

Route 8.4 gives `contShare` an obligation for a linear or affine `κ`: created at `[op]`, consumed
where that `κ` is resumed or cancelled and nowhere else, so that `NoOwn` at a run's end yields S6's
count.  The probe asks for that coupling at a single capture, a resume and a cancel.  At BoLo's
world and relation it does not hold, for two reasons, each checked here.

* **A closed program's relation at its pure type is BoLo's `wpTS`** (`cC_ret_eq`): no protocol
  table, and so no `contShare`, occurs in it.  Three programs of S6's teeth run, allocating nothing,
  to a value of `bool`:
  - R1, a capture never used (`dropCl`);
  - R2, a capture resumed twice (`twiceCl`);
  - R3, a linear capture cancelled (`cancelCl`).

  So each is in Core's relation at `F bool` (`semC_RProg`).  A typing system that types them there,
  and nothing else, meets FL at BoLo (`fl_core_JRp`) and fails S6 at the admissible context `ΞA`,
  once per program (`ghost_probe`).  Whatever obligation `contShare` carries, FL does not give S6
  (`not_ghostCoupling`).
* **No obligation of BoLo's world exists along those runs.**  Their heap is empty at every
  configuration: each step is a head step that keeps the heap (`HeadChain`).  BoLo's world at the
  empty heap is the empty resource (`lower_empty_eq`).  An obligation that `NoOwn` sees is an `own`
  cell, and an `own` cell lowers to a heap cell, which `[op]` does not allocate.  So `NoOwn` holds at
  every configuration of the three runs, whatever is done with `κ`.

So route 8.4 needs what BoLo's model does not have: an `own`-like obligation that `ResU.Lower` does
not lower to the heap, or `wpTS`'s run-end conditions read on the run's steps.  Both change BoLo's
definitions.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.I
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Head Kont Step1N)
open BoCa.Lifetime (LSub LifeCtx)
open Targets.Inst (OurTyping ourInst AdmEff rProg dropV twiceV cancelV cancelResumeV ΞA
  admEff_ΞA lab2A lab5A tiedAt_unit)

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

/-! ### S6's teeth, in Core's relation -/

/-- R1–R4's programs at a name, R3 and R4 at a nonzero one. -/
def RProg (e : Expr) : Prop :=
  ∃ n : UInt32, e = rProg n dropV ∨ e = rProg n twiceV ∨
    (n ≠ 0 ∧ (e = rProg n cancelV ∨ e = rProg n cancelResumeV))

/-- **Each of R1–R4 is in Core's relation at `F bool`**: its run is a chain of head steps that
allocate nothing, ending at `ff` or `tt`. -/
theorem semC_RProg {Δ : LifeCtx} {e : Expr} (h : RProg e) : SemC Δ [] e (.ret Inst.boolT) := by
  obtain ⟨n, rfl | rfl | ⟨hn, rfl | rfl⟩⟩ := h
  · exact semC_of_headChain (v := Val.inj₁ Val.unit) rfl (Inst.r1_chain (ℍ := ℍ) n) vC_ff
  · exact semC_of_headChain (v := Val.inj₂ Val.unit) rfl (Inst.r2_chain (ℍ := ℍ) n) vC_tt
  · exact semC_of_headChain (v := Val.inj₁ Val.unit) rfl (Inst.r3_chain (ℍ := ℍ) hn) vC_ff
  · exact semC_of_headChain (v := Val.inj₂ Val.unit) rfl (Inst.r4_chain (ℍ := ℍ) hn) vC_tt

/-- The typing system that types R1–R4 at the pure row's `bool` and nothing else. -/
def JRp : OurTyping orowRF :=
  ⟨fun _ _ Γ e j => Γ = [] ∧ RProg e ∧ ∀ η, j.den η = .comp (.ret Inst.boolT), OutJ.core,
    fun _ η => η⟩

/-- **FL at BoLo holds at `JRp`.** -/
theorem fl_core_JRp : FL (B.coreB (ℍ := ℍ)) JRp.read := by
  intro Θ Δ Γ e j hJ η hη
  obtain ⟨Γ', j', -, -, ⟨rfl, hR, hj'⟩, hΓe, hje⟩ := hJ η hη
  rw [← hΓe η, ← hje η, hj' η]
  exact semW₀_core.mpr (semC_RProg hR)

/-- `JRp` types R1, R2 and R3 at our instance, at the pure row's `bool`. -/
theorem der_JRp (n : UInt32) (cl : Val) (hcl : RProg (rProg n cl)) :
    ∃ Θ : RowCtx, (∀ p ∈ Θ, p.2 = Inst.anyCon) ∧
      JRp.der Θ LifeCtx.empty (Inst.liveCtx []) (rProg n cl)
        (.comp (.effF (fun η => orowRF.den ΞA (orowAlg ΞA).unit η) (.sum .unit .unit))) :=
  ⟨[], by simp, rfl, hcl, fun _ => rfl⟩

/-- **The probe at one capture, one resume and one cancel**: `JRp` meets FL at BoLo, and at the
admissible context `ΞA` S6 fails on R1 (a capture never used, at the affine `wait`), on R2 (a
capture resumed twice, at the linear `tick`) and on R3 (a linear capture cancelled, at `tick`). -/
theorem ghost_probe :
    FL (B.coreB (ℍ := ℍ)) JRp.read ∧ AdmEff ΞA ∧
    ¬ (ourInst (ℍ := ℍ) orowRF ΞA JRp).ContUse := by
  refine ⟨fl_core_JRp, admEff_ΞA, ?_⟩
  exact Inst.not_contUse_of_der_R1_orow lab2A (o := ⟨Inst.OVTy.ofV .unit, Inst.OVTy.ofV .unit, .affine⟩)
    (by simp [lab2A, ΞA]; rfl) (by decide)
    ⟨tiedAt_unit JRp _, .inl (der_JRp 2 dropV ⟨2, .inl rfl⟩)⟩

/-- S6 fails at `JRp` on R2 alone: a capture resumed twice. -/
theorem ghost_probe_resume : ¬ (ourInst (ℍ := ℍ) orowRF ΞA JRp).ContUse :=
  Inst.not_contUse_of_der_R2_orow lab5A
    ⟨tiedAt_unit JRp _, .inl (der_JRp 5 twiceV ⟨5, .inr (.inl rfl)⟩)⟩

/-- S6 fails at `JRp` on R3 alone: a linear capture cancelled. -/
theorem ghost_probe_cancel : ¬ (ourInst (ℍ := ℍ) orowRF ΞA JRp).ContUse :=
  Inst.not_contUse_of_der_R3_orow lab5A (o := ⟨Inst.OVTy.ofV .unit, Inst.OVTy.ofV .unit, .linear⟩)
    (by simp [lab5A, ΞA]; rfl) (by decide)
    ⟨tiedAt_unit JRp _, .inl (der_JRp 5 cancelV ⟨5, .inr (.inr ⟨by decide, .inl rfl⟩)⟩)⟩

/-- **The coupling route 8.4 needs, read at Core's relation**: every typing system whose programs
are in Core's relation meets S6 at every admissible effect context.  The relation at a returner is
`wpTS` (`cC_ret_eq`), so no definition of `contShare` changes which closed programs it relates. -/
def GhostCoupling : Prop :=
  ∀ J : OurTyping orowRF, FL (B.coreB (ℍ := ℍ)) J.read → ∀ Ξ, AdmEff Ξ →
    (ourInst (ℍ := ℍ) orowRF Ξ J).ContUse

/-- **Route 8.4's coupling fails at BoLo's relation.** -/
theorem not_ghostCoupling : ¬ GhostCoupling (ℍ := ℍ) := fun h =>
  (ghost_probe (ℍ := ℍ)).2.2 (h JRp fl_core_JRp ΞA admEff_ΞA)

end Targets.I

end

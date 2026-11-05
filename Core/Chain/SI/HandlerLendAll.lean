import Core.Chain.SI.HandlerLendProg
import Core.Chain.SI.AntiRebProg
import Core.Chain.SI.DeepRebProg

/-!
# The existing tests under a scheduler that lends its own cell around every resume

    yLendU = λ(v, κ). let (k, d) = (κ, alloc ()) in (λx. free d; x) (k.1 ())

`yLendU` is `yLend` (`SI/HandlerLendProg.lean`) answering `()`: it allocates a cell `d`, lends it
`imm` (`erwp_I_frame`), resumes the stored continuation inside the lend, and frees `d` when the
continuation returns. The lend is at `xTop`, longer than every lend of the task, when the
continuation's share allows it, and below the share otherwise. The clause is proved once, for
any handled computation at `T2` (`erwp_yLU`), so every task the existing tests prove at `T2` runs
under it unchanged: a `mut` lend (`progLend`), an `imm` lend (`progILend`), a reborrow of a field
(`progReb`), the same through `&mut self` (`progReb`, `bodyRM_ok`), an anti-frame (`progAnti`) and a
deep reborrow (`progDeep`), each live across `y`. Each continuation is resumed at a list that
carries the handler's records, at a lifetime no task lend relates to: round 7's configuration
(the handler's lend around the resume) with a record, for every frame rule across stops.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI.HandlerLendAll
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg
open BoCa.Fig16.LogRel.Core.Chain.SI.ILendProg
open BoCa.Fig16.LogRel.Core.Chain.SI.HandlerLendProg
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  clauseAt capTag)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- The clause's body after `let (k, d) = …`: `(λx. free d; x) (k.1 ())`. -/
def innerU : Expr := .app frE (.app (.app (.var 1) (.val (Val.inj₁ .unit))) (.val .unit))

/-- `λ(v, κ). let (k, d) = (κ, alloc ()) in (λx. free d; x) (k.1 ())`. -/
def clLendU : Val :=
  Val.lam (.letpair (.var 0)
    (.letpair (.pair (.var 0) (.app (.val (.prim .alloc)) (.val Val.unit))) innerU))

/-- **The clause's lend around the resume**, answering `()`: `d` lent `imm` at `x`, `κ`'s share
in `Res_x`, the borrow garbage to the resumed continuation. -/
theorem lendResumeU_ok {Φ : LocFam} (κ : Val) (x : Life) (d : Loc) (k : Nat) (ls : List SRec)
    (ρκ ρ : WRes) (hx : ρκ.InStratum x)
    (hK : KapRelN (ℍ := ℍ) Φ (opTableN T1) QZ yEnt none (k + 1) ls κ ρκ)
    (hρ : ResU.CompS ρκ (ResU.single d (CellU.ownOf Val.unit)) ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T1) (fun k' ls' w ρ' => Qd d k' ls' w ρ') k ls
      (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val .unit)) ρ := by
  have hshape : vShape .unk δ₀ Val.unit (PMap.empty : WRes) := ⟨rfl, trivial⟩
  have hadm : AdmWf .unk δ₀ := fun _ h => h.elim
  obtain ⟨ds, hds⟩ := lineage_list (r := recH d) hshape hadm
    (ExW.empty_of_all_imm (fun _ _ h => by simp at h))
  refine erwp_I_frame d .unk δ₀ hadm Val.unit PU (fun _ ρ h => ⟨h, trivial⟩)
    (fun _ _ _ _ h => h) (T1_ilendOK x) (fun _ _ _ _ _ _ h => h) k ls _
    PMap.empty _ ρκ ρ (inStratum_empty x) hx rfl (ResU.comp_empty_right _)
    (ResU.CompS.comm hρ) ds hds (fun BI hBI => ?_)
  have hwc : yEnt.wc ls (frameList (recH d) ds x ls) ρκ :=
    extF_of_addAt (addAt_frameList _ ds x ls) ρκ
  refine erwp_mono (Tb := opTableN T1) (Q := QZ) (fun k' ls' w ρ' h => ?_) (opTableN_local T1)
    _ _ _ _ ?_
  · have h' : ρ' = PMap.empty := h
    subst h'
    refine ⟨fun ρ₁ ρ₂ h₁ hc ρ₃ ρ₄ h₃ hc' => ?_, inStratum_empty x⟩
    obtain rfl := eq_of_compS_empty_left hc
    have h₃' : ρ₃ = PMap.empty := h₃
    subst h₃'
    obtain rfl := ResU.CompS.functional hc' (ResU.comp_empty_right _)
    exact h₁
  · exact erwp_garbage hBI (noOwn_single_imm d _ _ _ _)
      ((hK.2 _ hwc k (Nat.lt_succ_self k)).1 Val.unit PMap.empty ρκ ⟨rfl, rfl⟩
        (ResU.comp_empty_right _))

/-- **The clause**, as `erwp_clLend`, answering `()`. -/
theorem erwp_clLendU {Φ : LocFam} (hΦ : Φ.Down) (k : Nat) (ls : List SRec) (v κ : Val)
    (ρ : WRes) (hK : KapRelN (ℍ := ℍ) Φ (opTableN T1) QZ yEnt none k ls κ ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T1) QZ k ls (.app (.val clLendU) (.pair (.val v) κ.1)) ρ := by
  have hL := opTableN_local T1
  have hD := opTableN_down T1_down
  cases k with
  | zero => exact erwp_zero
  | succ k₀ =>
  have e₀ : (.app (.val clLendU) (.pair (.val v) κ.1) : Expr) =
      Kont.hole.plug (.app (.val clLendU) (.val (Val.pair v κ))) := rfl
  rw [e₀]
  refine erwp_det hΦ hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.pair v κ) (.letpair (.var 0)
      (.letpair (.pair (.var 0) (.app (.val (.prim .alloc)) (.val Val.unit))) innerU))) =
      Kont.hole.plug (.letpair (.val (Val.pair v κ))
        (.letpair (.pair (.var 0) (.app (.val (.prim .alloc)) (.val Val.unit))) innerU)) := by
    simp [Kont.plug, Expr.subst, innerU, frE, freeE, Val.inj₁, Val.unit, Val.prim, Expr.val]
  rw [e₁]
  refine erwp_det hΦ hD QZ_down (fun μ => step1Only_plug (Head.letpair μ _ _ _) rfl .hole) ?_
  have e₂ : Expr.subst 0 v (Expr.subst 0 (κ.shift 1 0)
      (.letpair (.pair (.var 0) (.app (.val (.prim .alloc)) (.val Val.unit))) innerU)) =
      (Kont.letpair (Kont.pairR κ .hole) innerU).plug
        (.app (.val (.prim .alloc)) (.val Val.unit)) := by
    simp only [Expr.subst, if_true, Val.val_shift, Kont.plug]
    rw [Expr.subst_shift 0 0 0 v _ le_rfl le_rfl, Expr.shift_zero]
    simp [innerU, frE, freeE, Expr.subst, Val.inj₁, Val.unit, Val.prim, Expr.val]
  rw [Kont.plug_hole, e₂]
  refine erwp_alloc hΦ hL _ Val.unit (fun d σ₁ σ₂ hcell hc => ?_)
  subst hcell
  rw [show k₀ + 1 - 1 = k₀ from rfl]
  have e₃ : (Kont.letpair (Kont.pairR κ .hole) innerU).plug (.val (Val.loc d)) =
      Kont.hole.plug (.letpair (.val (Val.pair κ (Val.loc d))) innerU) := rfl
  rw [e₃]
  cases k₀ with
  | zero => exact erwp_zero
  | succ k₁ =>
  refine erwp_det hΦ hD QZ_down (fun μ => step1Only_plug (Head.letpair μ _ _ _) rfl .hole) ?_
  have e₄ : Expr.subst 0 κ (Expr.subst 0 ((Val.loc d).shift 1 0) innerU) =
      (Kont.appR (.lam (.seq (freeE (.val (Val.loc d))) (.var 0))) .hole).plug
        (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val .unit)) := by
    simp [innerU, frE, freeE, Expr.subst, Expr.shift, Kont.plug, Val.inj₁, Val.unit, Val.prim,
      Val.loc, Expr.val, Val.shift]
  rw [Kont.plug_hole, e₄]
  refine erwp_bind_le (Q' := fun k' ls' w ρ' => Qd d k' ls' w ρ') hΦ _
    (fun m => by simp [Kont.HasHnd]) (fun m => by simp [Kont.Catches])
    (OpTabN.ctxClosed_of_fin T1_fin _) (k₁ + 1)
    (fun k' ls' w ρ' _ h => erwp_frE hΦ d k' ls' w ρ' h) (k₁ + 1) le_rfl ls _ _ ?_
  by_cases hS : ρ.InStratum xTop
  · exact lendResumeU_ok κ xTop d (k₁ + 1) ls ρ σ₂ hS hK hc
  · obtain ⟨x, hx⟩ := ResU.exists_stratum ρ
    exact lendResumeU_ok κ x d (k₁ + 1) ls ρ σ₂ hx hK hc

/-- `hnd_Y yLendU`: the lending scheduler, `y` must-resume. -/
def yLU : Val := hndVal 6 (qualsVal [.lin]) Stage1.idV (Val.pair clLendU .unit)

/-- **The lending scheduler at `erwp`**, for any handled computation at `T2`. -/
theorem erwp_yLU {Φ : LocFam} (hΦ : Φ.Down) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T2) QZ n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN T1) QZ n ls (hndE yLU e) ρ := by
  refine erwp_handle hΦ T2 T1 T2_down T1_down 6 (fun m i hm => by simp [T2, hm]) _ _ _ QZ QZ
    QZ_down ?_ (fun _ => none) (fun _ en _ _ hq' _ hTk => by cases hTk)
    (fun k ls v ρ hv => erwp_idV hΦ T1_down hv) ?_
  · intro i en hT _
    rcases T2_cases hT with ⟨-, rfl, rfl⟩ | ⟨h6, -, -⟩
    · exact Stage1.capTag_one .lin
    · exact absurd h6.symm Stage1.divEff_ne6
  · intro i en hT
    rcases T2_cases hT with ⟨-, rfl, rfl⟩ | ⟨h6, -, -⟩
    · refine ⟨clLendU, Stage1.clauseAt_pair0 _ _, fun _ k ls v κ ρ hsep => ?_,
        fun h => by cases h⟩
      obtain ⟨ρa, ρk, hc, ⟨-, rfl⟩, hK⟩ := hsep
      obtain rfl : ρ = ρk := eq_of_compS_empty_left hc
      exact erwp_clLendU hΦ k ls v κ ρ hK
    · exact absurd h6.symm Stage1.divEff_ne6

/-- A task at `T2`, under the lending scheduler and the runtime. -/
def underL (body : Expr) : Expr := hndE DivRuntime.rtH (hndE yLU body)

theorem underL_orDiverges {body : Expr}
    (h : ∀ n, erwp (ℍ := ℍ) Φ₀ (opTableN T2) QZ n [] body (PMap.empty : WRes)) :
    OrDiverges (ℍ := ℍ) (underL body) :=
  erwp_adequacy (Φ := Φ₀) (fun _ _ _ _ h => h)
    (fun n => erwp_rtH Φ₀_down n [] _ _ (erwp_yLU Φ₀_down n [] _ _ (h n)))

/-- `progLend`'s task (a `mut` lend across `y`) under the lending scheduler. -/
theorem lend_underL : OrDiverges (ℍ := ℍ) (underL LendProg.bodyL) :=
  underL_orDiverges (LendProg.body_ok 0)

/-- `progILend`'s task (an `imm` lend across `y`) under the lending scheduler. -/
theorem ilend_underL : OrDiverges (ℍ := ℍ) (underL ILendProg.bodyI) :=
  underL_orDiverges ILendProg.bodyI_ok

/-- `progReb`'s task (a reborrow of a field across `y`) under the lending scheduler. -/
theorem reb_underL : OrDiverges (ℍ := ℍ) (underL RebProg.bodyR) :=
  underL_orDiverges RebProg.bodyR_ok

/-- The same reborrow through `&mut self` (anti-frame, imm lend, reborrow) under the lending
scheduler. -/
theorem rebM_underL : OrDiverges (ℍ := ℍ) (underL RebProg.bodyR) :=
  underL_orDiverges AntiRebProg.bodyRM_ok

/-- `progAnti`'s task (an anti-frame across `y`) under the lending scheduler. -/
theorem anti_underL : OrDiverges (ℍ := ℍ) (underL AntiLendProg.bodyA) :=
  underL_orDiverges (AntiLendProg.bodyA_ok 0)

/-- `progDeep`'s task (a deep reborrow across `y`) under the lending scheduler. -/
theorem deep_underL : OrDiverges (ℍ := ℍ) (underL DeepRebProg.bodyD) :=
  underL_orDiverges DeepRebProg.bodyD_ok

end BoCa.Fig16.LogRel.Core.Chain.SI.HandlerLendAll

end

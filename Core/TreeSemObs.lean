import Core.TreeSemKEx
import Core.TreeCactus
import Core.TreeLend
import Core.TreeSchedProgs
import Core.EffMachine

/-!
# A bare run at a list is not one at every later list keeping its records  `[spec §62]`

Why `𝒞⟦F A⟧` (`SCmp.ret`, `Core/TreeSemC.lean`) quantifies over the later lists itself rather than
being a bare `cerwpT` run: `cerwpT` is Kripke along the re-reading of its list (`cerwpT_kripke`)
but not along `KeepRel`. `KeepKripkeRunNil` is the property at the records `F A` runs at, none
owned, and `cerwpT_not_keepKripkeNil` refutes it; `cerwpT_not_keepKripke` refutes it at any records
owned (`KeepKripkeRun`).

`twp` quantifies over the starts whose list re-reads the run's list whole (`SRecsRR`). At `[]`,
a resource holding a view has no start (`cerwpT_nil_of_imm`), so every term over it is a run there.
`KeepRel [] ls′ ρ` holds for every `ls′`. So the property would make the stuck term `() ()`, over
the view of a lend opened by the program, a run at the lend's own list owning no records; framed
beside the lend's record (`twp_frame`), with the lend's opening (`twp_lendOpen`), the closed program
`let a = alloc () in () ()` would be a run at the empty world. Adequacy (`cerwpT_adequacy`) says
that program is safe; it is stuck after two steps.

The same argument shows the depth-1 instance's resume configuration (`KEx.kontBox_depth1`) has
starts: if the run there of the stuck term held at every index and pair of locations, the closed
program `let a = alloc () in let b = alloc () in () ()`, opening the instance's two lends, would be
a run at the empty world (`d1_nonvacuous`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.Obs
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Steps Head Kont stuckE)

/-- **A bare run is Kripke along `KeepRel`**: a `cerwpT` run at `ls` owning `O`, over a covered
resource, is one at every extension, on the re-readings, at every list keeping the records of `ls`
the resource reads. Refuted by `cerwpT_not_keepKripke`. -/
def KeepKripkeRun : Prop :=
  ∀ (Tb : TableT) (Q : TPostV) (Fb F : TFrame) (n : Nat) (w w' : TWd) (ls : List (SRecT w.K))
    (ls' : List (SRecT w'.K)) (O : List (FrameRecT w.K)) (O' : List (FrameRecT w'.K)) (e : Expr)
    (ρ : TRes w.K) (ρ' : TRes w'.K), w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' →
    KeepRel w'.Θ ls ls' ρ → RecsRR w'.Θ O O' → CovR (sem w.Θ) w.K ρ →
    cerwpT (ℍ := ℍ) Tb Q Fb F n w ls O e ρ → cerwpT (ℍ := ℍ) Tb Q Fb F n w' ls' O' e ρ'

/-- **A bare run owning no records is Kripke along `KeepRel`**: `KeepKripkeRun` at `O = O′ = []`,
the records `F A` runs at (`SCmp.ret`). Refuted by `cerwpT_not_keepKripkeNil`. -/
def KeepKripkeRunNil : Prop :=
  ∀ (Tb : TableT) (Q : TPostV) (Fb F : TFrame) (n : Nat) (w w' : TWd) (ls : List (SRecT w.K))
    (ls' : List (SRecT w'.K)) (e : Expr) (ρ : TRes w.K) (ρ' : TRes w'.K), w.Ext w' ρ →
    RRw (w := w) (w' := w') ρ ρ' → KeepRel w'.Θ ls ls' ρ → CovR (sem w.Θ) w.K ρ →
    cerwpT (ℍ := ℍ) Tb Q Fb F n w ls [] e ρ → cerwpT (ℍ := ℍ) Tb Q Fb F n w' ls' [] e ρ'

theorem keepKripkeRunNil_of (H : KeepKripkeRun (ℍ := ℍ)) : KeepKripkeRunNil (ℍ := ℍ) :=
  fun Tb Q Fb F n w w' ls ls' e ρ ρ' hE hr hk hc h =>
    H Tb Q Fb F n w w' ls ls' [] [] e ρ ρ' hE hr hk .nil hc h

/-! ### The stuck term at `twp` -/

/-- The stuck term `() ()` is neither a value nor a stop of a table with no entries. -/
theorem not_post_stuckE {T : OpTabT} (hT : ∀ m i, T m i = none) {Q : TPostV} {Ψ : ContT}
    {F : TFrame} {k : Nat} {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)}
    {ρ : TRes w.K} : ¬ cerwpPostT (opTableT T) Q Ψ F k w ls O stuckE ρ := by
  rintro (⟨v, hv, -⟩ | ⟨_, m, i, _, _, _, _, h₃, -⟩)
  · exact absurd (hv ▸ v.2) (by simp [stuckE])
  · rw [hT m i] at h₃; cases h₃

/-- **A run of the stuck term is a run at every postcondition** when the stuck term meets none of
its own: from any start the stuck term is final at once, so the run's end at the start would be
one of the postcondition at the stuck term. -/
theorem twp_stuckE {F : TFrame} {P P' : TPost} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {ρ : TRes w.K} (hP : ∀ k w ls O ρ, ¬ P k w ls O stuckE ρ)
    (h : twp (ℍ := ℍ) F P n w ls O stuckE ρ) : twp (ℍ := ℍ) F P' n w ls O stuckE ρ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hf hc hS hR hI hfd j μ' e' hj hrun hfin
  have h' := h w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hf hc hS hR hI hfd j μ' e' hj hrun hfin
  cases hrun with
  | refl =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hQ, -⟩ := h'
      exact absurd hQ (hP _ _ _ _ _)
  | more hs _ => exact absurd hs (stuck_no_step (stuckAt_unit_app (ℍ := ℍ) Val.unit) .hole)

/-- Two resources apart, each covered, compose to a covered one. -/
theorem covR_compS_apart {Θ : LocTy} {K : WCactus} {a b y : TRes K} (hc : ResUT.CompS a b y)
    (hd : ∀ x, a.get x = none ∨ b.get x = none) (ha : CovR Θ K a) (hb : CovR Θ K b) :
    CovR Θ K y := by
  intro m ψ e
  rcases hd m with h | h
  · rw [ResUT.Comp.get_of_left_none hc h] at e; exact hb m ψ e
  · rw [ResUT.Comp.get_of_right_none hc h] at e; exact ha m ψ e

/-- The empty table, read at `cerwpT`'s postcondition, is downward closed. -/
theorem tbEmpty_down : (opTableT OpTabT.empty).Down := opTableT_down fun _ _ _ h => by cases h

/-- `alloc ()`. -/
def allocU : Expr := .app (.val (.prim .alloc)) (.val .unit)

/-! ### Refuted at the records `F A` runs at -/

/-- The empty world at the chain tree. -/
def w₀ : TWd := ⟨KEx.chainP, fun _ => none, tmplT _ (fun _ => none)⟩

/-- `let a = alloc () in () ()`. -/
def obsE : Expr := .app (.lam stuckE) allocU

/-- **`obsE` is a run at the empty world, if a bare run owning no records is Kripke along
`KeepRel`.** It allocates `ℓ` and opens a lend of it (a ghost update, `twp_lendOpen`), holding the
view at the lend's list `[(lendRec ℓ, α)]` and owning the lend's record. The run of the stuck term
over the view is framed off the record (`twp_frame`): a run at the lend's list owning no records,
the configuration `F A` runs at. The stuck term over the view is a run at `[]` owning none
(`cerwpT_nil_of_imm`), and `KeepRel [] [(lendRec ℓ, α)]` holds of every resource. -/
theorem obsE_cerwpT (H : KeepKripkeRunNil (ℍ := ℍ)) (n : Nat) :
    cerwpT (ℍ := ℍ) (opTableT OpTabT.empty) (fun _ _ _ _ _ ρ => ρ = PMap.empty)
      (fun _ ρf => ρf = PMap.empty) (fun _ ρf => ρf = PMap.empty) n w₀ [] [] obsE
      (PMap.empty : TRes w₀.K) := by
  have hD := cerwpPostT_down (Tb := opTableT OpTabT.empty)
    (Q := fun _ _ _ _ _ ρ => ρ = PMap.empty) (fun _ _ _ _ _ _ h => h) tbEmpty_down
    (Ψ := cerwpTC (ℍ := ℍ) (opTableT OpTabT.empty) (fun _ _ _ _ _ ρ => ρ = PMap.empty)
      (fun _ ρf => ρf = PMap.empty) n) (F := fun _ ρf => ρf = PMap.empty)
  rw [cerwpT_eq]
  refine twp_alloc_here hD (.appR (.lam stuckE) .hole) Val.unit fun l ρ₁ hc => ?_
  obtain rfl := SchedProgs.compS_empty_left_eq hc
  refine twp_lendOpen (default : Life) (Z := PMap.empty)
    (ResUT.CompS.comm (ResUT.compS_empty_right _)) (ResUT.CompS.comm (ResUT.compS_empty_right _)) ?_
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ stuckE (Val.loc l)) rfl .hole) ?_
  have hst : stuckE.subst 0 (Val.loc l) = stuckE := by simp [stuckE, Expr.subst]
  rw [Kont.plug, hst]
  have hcov := view_cov (K := w₀.K) w₀.Θ (default : Life) l
  have hin := H (opTableT OpTabT.empty) (fun _ _ _ _ _ ρ => ρ = PMap.empty)
    (fun _ ρf => ρf = PMap.empty) (fun _ ρf => ρf = PMap.empty) n w₀ w₀ [] [(lendRec l, default)]
    stuckE _ _ (TWd.Ext.refl _ _)
    (RR.refl hcov) (fun r hr => by simp [rsOfT] at hr) hcov
    (cerwpT_nil_of_imm (l := l) (ψ := viewCell (default : Life))
      (by rw [viewRes, ResUT.single_get_self]) rfl)
  rw [cerwpT_eq] at hin
  refine twp_mono (P := TPost.sep (fun _ _ _ _ _ _ => False) (fun _ _ _ => True))
    (fun _ _ _ _ _ _ ⟨_, _, _, _, _, _, h, _⟩ => h.elim) ?_
  exact twp_frame (O₁ := []) (O₂ := [lendRec l]) (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ h => by cases h) (ResUT.compS_empty_right _) hcov
    (fun _ ρf ρ₂₀ y _ hr hf hc => by
      obtain rfl := RR.of_empty hr
      subst hf
      exact SchedProgs.compS_empty_left_eq hc)
    (twp_stuckE (fun _ _ _ _ _ => not_post_stuckE fun _ _ => rfl) hin) trivial

/-- `obsE` reaches the stuck term `() ()` from the empty memory. -/
theorem obsE_steps :
    Steps (ℍ := ℍ) Adequacy.emptyMem obsE (Adequacy.emptyMem.upd 0 .unit) stuckE :=
  .more ⟨.appR (.lam stuckE) .hole, _, _, rfl, rfl, Head.alloc _ .unit 0 rfl⟩
    (.more ⟨.hole, _, _, rfl, by simp [Kont.plug, stuckE, Expr.subst],
      Head.beta _ stuckE (Val.loc 0)⟩ (.refl _ _))

/-- **A bare run owning no records is not Kripke along `KeepRel`**, with the lend's record in the
run's list and not owned by it: the configuration `F A` runs at. So `𝒞⟦F A⟧` reads the later
lists itself (`SCmp.ret`). -/
theorem cerwpT_not_keepKripkeNil : ¬ KeepKripkeRunNil (ℍ := ℍ) := fun H => by
  obtain ⟨hp, -, -⟩ := cerwpT_adequacy (ℍ := ℍ) KEx.chainP
    (Q := fun _ _ _ _ _ ρ => ρ = PMap.empty) (fun _ _ _ _ _ _ h => h) (obsE_cerwpT H) obsE_steps
  rcases hp with hv | ⟨μ', e', hs⟩
  · exact (stuckAt_unit_app (ℍ := ℍ) Val.unit).not_val hv
  · exact stuck_no_step (stuckAt_unit_app (ℍ := ℍ) Val.unit) .hole hs

/-- **A bare run is not Kripke along `KeepRel`**, at any records owned. -/
theorem cerwpT_not_keepKripke : ¬ KeepKripkeRun (ℍ := ℍ) := fun H =>
  cerwpT_not_keepKripkeNil (keepKripkeRunNil_of H)

/-! ### The depth-1 instance's resume configuration has a start -/

/-- `let a = alloc () in let b = alloc () in () ()`. -/
def obsD : Expr := .app (.lam obsE) allocU

/-- **The configuration `kontBox_depth1` concludes its resume at has a start, if the run there of
the stuck term held at every index and pair of locations.** The program allocates `ℓ₀` and `ℓ₂`,
opens a lend of `ℓ₂` at `5` and one of `ℓ₀` at `1` (`twp_lendOpen`), reaching the list
`lsD1' ℓ₀ ℓ₂`, owning both records, over both views. The run over `ℓ₀`'s view owning no records,
the configuration of `kontBox_depth1`'s second conjunct, is framed off the rest (`twp_frame`). -/
theorem obsD_cerwpT (H : ∀ (n : Nat) (l₀ l₂ : BoCa.Loc), l₀ ≠ l₂ →
      cerwpT (ℍ := ℍ) KEx.tbE (postOf (KEx.τR (KEx.lf 1))) KEx.Fb (fdNil KEx.enU Val.unit KEx.Fb)
        n KEx.wD₁ (KEx.lsD1' l₀ l₂) [] stuckE (KEx.viewR l₀ (KEx.lf 1)))
    (n : Nat) :
    cerwpT (ℍ := ℍ) (opTableT OpTabT.empty) (fun _ _ _ _ _ ρ => ρ = PMap.empty)
      (fun _ ρf => ρf = PMap.empty) (fun _ ρf => ρf = PMap.empty) n KEx.wD₁ [] [] obsD
      (PMap.empty : TRes KEx.wD₁.K) := by
  have hD := cerwpPostT_down (Tb := opTableT OpTabT.empty)
    (Q := fun _ _ _ _ _ ρ => ρ = PMap.empty) (fun _ _ _ _ _ _ h => h) tbEmpty_down
    (Ψ := cerwpTC (ℍ := ℍ) (opTableT OpTabT.empty) (fun _ _ _ _ _ ρ => ρ = PMap.empty)
      (fun _ ρf => ρf = PMap.empty) n) (F := fun _ ρf => ρf = PMap.empty)
  rw [cerwpT_eq]
  refine twp_alloc_here hD (.appR (.lam obsE) .hole) Val.unit fun la ρ₁ hc => ?_
  obtain rfl := SchedProgs.compS_empty_left_eq hc
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ obsE (Val.loc la)) rfl .hole) ?_
  have hb : obsE.subst 0 (Val.loc la) = obsE := by simp [obsE, allocU, stuckE, Expr.subst]
  rw [Kont.plug, hb]
  refine twp_alloc_here hD (.appR (.lam stuckE) .hole) Val.unit fun lb ρ₂ hc₂ => ?_
  have hab : la ≠ lb := by
    intro e
    subst e
    have := ResUT.compatS_single_own (ResUT.CompatS.symm hc₂.1)
    rw [ResUT.single_get_self] at this
    cases this
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ stuckE (Val.loc lb)) rfl .hole) ?_
  have hst : stuckE.subst 0 (Val.loc lb) = stuckE := by simp [stuckE, Expr.subst]
  rw [Kont.plug, hst]
  obtain ⟨ρ₃, hρ₃⟩ := single_compS (K := KEx.wD₁.K) hab (CellUT.ownOf Val.unit) (viewCell (KEx.lf 5))
  refine twp_lendOpen (KEx.lf 5) hc₂ hρ₃ ?_
  obtain ⟨ρ₄, hρ₄⟩ := single_compS (K := KEx.wD₁.K) hab.symm (viewCell (KEx.lf 5)) (viewCell (KEx.lf 1))
  refine twp_lendOpen (KEx.lf 1) (ResUT.CompS.comm hρ₃) hρ₄ ?_
  have hcov : CovR (sem KEx.wD₁.Θ) KEx.wD₁.K ρ₄ :=
    covR_compS_apart hρ₄ (single_disjoint hab.symm _ _) (view_cov _ _ _) (view_cov _ _ _)
  have hin := H n la lb hab
  rw [cerwpT_eq] at hin
  refine twp_mono (P := TPost.sep (fun _ _ _ _ _ _ => False) (fun _ _ _ => True))
    (fun _ _ _ _ _ _ ⟨_, _, _, _, _, _, h, _⟩ => h.elim) ?_
  exact twp_frame (O₁ := []) (O₂ := [lendRec la, lendRec lb])
    (fun _ _ _ _ _ _ _ _ _ _ => trivial) (fun _ h => by cases h) (ResUT.CompS.comm hρ₄) hcov
    (fun _ _ _ _ _ _ _ _ => ⟨trivial, trivial⟩)
    (twp_stuckE (fun _ _ _ _ _ => not_post_stuckE fun _ _ => rfl) hin) trivial

/-- `obsD` reaches the stuck term `() ()` from the empty memory. -/
theorem obsD_steps :
    Steps (ℍ := ℍ) Adequacy.emptyMem obsD ((Adequacy.emptyMem.upd 0 .unit).upd 1 .unit) stuckE :=
  .more ⟨.appR (.lam obsE) .hole, _, _, rfl, rfl, Head.alloc _ .unit 0 rfl⟩
    (.more ⟨.hole, _, _, rfl, by simp [Kont.plug, obsE, allocU, stuckE, Expr.subst],
      Head.beta _ obsE (Val.loc 0)⟩
      (.more ⟨.appR (.lam stuckE) .hole, _, _, rfl, rfl, Head.alloc _ .unit 1 rfl⟩
        (.more ⟨.hole, _, _, rfl, by simp [Kont.plug, stuckE, Expr.subst],
          Head.beta _ stuckE (Val.loc 1)⟩ (.refl _ _))))

/-- **The depth-1 instance's resume configuration is not vacuous.** At the world `wD₁` and the
resume list `lsD1' ℓ₀ ℓ₂`, owning no records, over `ℓ₀`'s view, the run `kontBox_depth1`
concludes does not hold of the stuck term at every index and pair of locations: there are starts
there (else every term would be a run). By adequacy (`cerwpT_adequacy`) on `obsD`. -/
theorem d1_nonvacuous : ¬ ∀ (n : Nat) (l₀ l₂ : BoCa.Loc), l₀ ≠ l₂ →
    cerwpT (ℍ := ℍ) KEx.tbE (postOf (KEx.τR (KEx.lf 1))) KEx.Fb (fdNil KEx.enU Val.unit KEx.Fb)
      n KEx.wD₁ (KEx.lsD1' l₀ l₂) [] stuckE (KEx.viewR l₀ (KEx.lf 1)) := fun H => by
  obtain ⟨hp, -, -⟩ := cerwpT_adequacy (ℍ := ℍ) KEx.dP₁
    (Q := fun _ _ _ _ _ ρ => ρ = PMap.empty) (fun _ _ _ _ _ _ h => h) (obsD_cerwpT H) obsD_steps
  rcases hp with hv | ⟨μ', e', hs⟩
  · exact (stuckAt_unit_app (ℍ := ℍ) Val.unit).not_val hv
  · exact stuck_no_step (stuckAt_unit_app (ℍ := ℍ) Val.unit) .hole hs

end BoCa.Fig16.Tree.Wp.Obs

end

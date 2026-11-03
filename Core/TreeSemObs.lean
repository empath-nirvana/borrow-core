import Core.TreeSemKEx
import Core.TreeCactus
import Core.TreeLend
import Core.TreeSchedProgs
import Core.EffMachine

/-!
# A bare run at a list is not one at every later list keeping its records  `[spec §62]`

Why `𝒞⟦F A⟧` (`SCmp.ret`, `Core/TreeSemC.lean`) quantifies over the later lists itself rather than
being a bare `cerwpT` run: `cerwpT` is Kripke along the re-reading of its list (`cerwpT_kripke`)
but not along `KeepRel`. `KeepKripkeRun` is the property, and `cerwpT_not_keepKripke` refutes it.

`twp` quantifies over the starts whose list re-reads the run's list whole (`SRecsRR`). At `[]`,
a resource holding a view has no start (`cerwpT_nil_of_imm`), so every term over it is a run there.
`KeepRel [] ls′ ρ` holds for every `ls′`. So the property would make the stuck term `() ()`, over
the view of a lend opened by the program, a run at the lend's own list, and with the lend's
opening (`twp_lendOpen`) the closed program `let a = alloc () in () ()` a run at the empty world.
Adequacy (`cerwpT_adequacy`) says that program is safe; it is stuck after two steps.
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

/-- The empty world at the chain tree. -/
def w₀ : TWd := ⟨KEx.chainP, fun _ => none, tmplT _ (fun _ => none)⟩

/-- `let a = alloc () in () ()`. -/
def obsE : Expr := .app (.lam stuckE) (.app (.val (.prim .alloc)) (.val .unit))

/-- The empty table, read at `cerwpT`'s postcondition, is downward closed. -/
theorem tbEmpty_down : (opTableT OpTabT.empty).Down := opTableT_down fun _ _ _ h => by cases h

/-- **`obsE` is a run at the empty world, if a bare run is Kripke along `KeepRel`.** It allocates
`ℓ` and opens a lend of it (a ghost update, `twp_lendOpen`), holding the view at the lend's list
`[(lendRec ℓ, α)]`; the stuck term over the view is a run at `[]` (`cerwpT_nil_of_imm`), and
`KeepRel [] [(lendRec ℓ, α)]` holds of every resource. -/
theorem obsE_cerwpT (H : KeepKripkeRun (ℍ := ℍ)) (n : Nat) :
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
  rw [Kont.plug, hst, ← cerwpT_eq]
  have hcov := view_cov (K := w₀.K) w₀.Θ (default : Life) l
  exact H _ _ _ _ n w₀ w₀ [] _ [lendRec l] [lendRec l] _ _ _ (TWd.Ext.refl _ _) (RR.refl hcov)
    (fun r hr => by simp [rsOfT] at hr) (.cons (lendRec_rr l) .nil) hcov
    (cerwpT_nil_of_imm (l := l) (ψ := viewCell (default : Life))
      (by rw [viewRes, ResUT.single_get_self]) rfl)

/-- `obsE` reaches the stuck term `() ()` from the empty memory. -/
theorem obsE_steps :
    Steps (ℍ := ℍ) Adequacy.emptyMem obsE (Adequacy.emptyMem.upd 0 .unit) stuckE :=
  .more ⟨.appR (.lam stuckE) .hole, _, _, rfl, rfl, Head.alloc _ .unit 0 rfl⟩
    (.more ⟨.hole, _, _, rfl, by simp [Kont.plug, stuckE, Expr.subst],
      Head.beta _ stuckE (Val.loc 0)⟩ (.refl _ _))

/-- **A bare run is not Kripke along `KeepRel`.** So `𝒞⟦F A⟧` reads the later lists itself
(`SCmp.ret`). -/
theorem cerwpT_not_keepKripke : ¬ KeepKripkeRun (ℍ := ℍ) := fun H => by
  obtain ⟨hp, -, -⟩ := cerwpT_adequacy (ℍ := ℍ) KEx.chainP
    (Q := fun _ _ _ _ _ ρ => ρ = PMap.empty) (fun _ _ _ _ _ _ h => h) (obsE_cerwpT H) obsE_steps
  rcases hp with hv | ⟨μ', e', hs⟩
  · exact (stuckAt_unit_app (ℍ := ℍ) Val.unit).not_val hv
  · exact stuck_no_step (stuckAt_unit_app (ℍ := ℍ) Val.unit) .hole hs

end BoCa.Fig16.Tree.Wp.Obs

end

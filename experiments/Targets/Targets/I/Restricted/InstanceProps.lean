import Targets.I.Restricted.Core
import Targets.I.Routes
import Targets.B.BoLo
import Targets.B.Adequacy

/-!
# The interaction — A's properties at our instance, discharged through B (RESTRUCTURE §4.3, §4.5)

A theorem that uses a B theorem to establish an A property lives here.

* `effSafe_tier1 : EffSafe tier1` (Core's form of P2), by `effSafeOfFL _ _ fl_core_tier1
  ⟨famEmpty_core, adequateEvery_core⟩`: FL at BoLo, the empty configuration and adequacy from every
  index.  PROVED AT σ=[].
* `not_effSafeDriveOfFL`: the route from FL to effect safety of driven programs fails as written.
  At `coreW`, a typing system that types `return (inr ())` at `F_S(1 ⊕ U(Loop_S 1 1))`, `S` a row
  whose loop body is not positive (`shadowOp`), meets FL (`cC` at `νX. C` holds of everything when
  `C` is not positive), and its drive is stuck at `nextE ()`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun AStep1 performE raiseE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **`EffSafe tier1`** (P2 for Core's typing, at unr-free rows). -/
theorem effSafe_tier1 : EffSafe (ℍ := ℍ) tier1 :=
  effSafeOfFL _ _ fl_core_tier1 ⟨famEmpty_core, adequateEvery_core⟩

/-! ### The route to effect safety of driven programs -/

/-- The operation `1.0 : 1 ↠ 1`, linear. -/
def op₁ : OpSig := ⟨1, 0, .lin, .unit, .unit⟩

/-- A row that reads as `[op₁]` and whose loop body is not positive. -/
def rowShadow : Row := [op₁, shadowOp op₁]

theorem rowNU_rowShadow : Row.NU rowShadow := by
  intro n i o h
  obtain ⟨-, -, rfl⟩ := find_shadow op₁ h
  exact Or.inr (by decide)

/-- The term `inr ()`. -/
abbrev inrUnit : Expr := (Val.inj₂ Val.unit).1

/-- A typing system that types `return (inr ())` at `F_S(1 ⊕ U(Loop_S 1 1))`, `S = rowShadow`, and
nothing else. -/
def jShadow : TypingJ :=
  ⟨fun _ Δ Γ e j => Δ = LifeCtx.empty ∧ e = inrUnit ∧ ∀ η, Γ η = [] ∧
      j η = .comp (CTy.effOf rowShadow (.sum .unit (.thunk (CTy.loopEff rowShadow .unit .unit)))),
    OutJ.core⟩

/-- **FL holds of `jShadow` at BoLo**: the loop type's body is not positive, so `inr ()` is in the
relation there. -/
theorem fl_core_jShadow : FL (B.coreB (ℍ := ℍ)) jShadow := by
  rintro Θ Δ Γ e j ⟨-, rfl, hj⟩ η -
  obtain ⟨hΓ, hjη⟩ := hj η
  rw [hΓ, hjη]
  intro δ γ i ρ _ hg
  obtain ⟨-, hρ, -⟩ := pure_sep_iff.mp hg
  obtain rfl : ρ = PMap.empty := hρ
  rw [show substAll γ inrUnit = inrUnit from substAll_closed (v := Val.inj₂ Val.unit) rfl γ]
  exact (cC_effOf _ _ i.1 δ _ PMap.empty).mpr (ewp_val (opTable_mono _)
    (Or.inr ⟨Val.unit, pure_sep_mk rfl (fun _ _ hN => absurd hN (not_nuOk_shadow op₁ _ _))⟩))

/-- **The route to effect safety of driven programs fails as written**: at `coreW`, `jShadow`
meets FL, the empty configuration is reached and adequacy holds from every index, and the drive of
`return (inr ())` is stuck at `nextE ()`, which is no finished drive, takes no step and stops at
no operation. -/
theorem not_effSafeDriveOfFL : ¬ EffSafeDriveOfFL (ℍ := ℍ) := by
  intro h
  have hE := h coreW jShadow fl_core_jShadow famEmpty_core adequateEvery_core
  have hreach : Relation.ReflTransGen (RStep (ℍ := ℍ) Platform.none)
      (init Platform.none inrUnit, .drive)
      (⟨Adequacy.emptyMem, nextE Val.unit, ()⟩, .drive) := .single .again
  rcases hE inrUnit rowShadow .unit rowNU_rowShadow ⟨rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩ _ hreach with
    ⟨a, ha, -⟩ | ⟨rc', hs⟩ | hstop
  · simp [nextE, Val.val_inj₁] at ha
  · rcases rstep_cases hs with ⟨hp, -⟩ | ⟨hph, -⟩ | ⟨-, l, he, -⟩
    · rcases pstep_cases hp with ⟨hst, -⟩ | ⟨K, n, i, v, w, s', o, he, -⟩
      · exact stuck_no_step (stuckAt_unit_app (Val.inj₁ Val.unit)) .hole hst
      · exact stuck_ne_op (stuckAt_unit_app (Val.inj₁ Val.unit)) .hole K false _ he
    · cases hph
    · simp [nextE, Val.val_inj₂] at he
  · rcases hstop with ⟨K, n, i, v, o, he, -⟩ | ⟨K, n, i, v, o, he, -⟩
    · exact stuck_ne_op (stuckAt_unit_app (Val.inj₁ Val.unit)) .hole K false _ he
    · exact stuck_ne_op (stuckAt_unit_app (Val.inj₁ Val.unit)) .hole K true _ he

end Targets

end

import Targets.Instance.Checks

/-!
# The Instance — S2, S3 and `DataDiv` at our instance (TIER1-PLAN §3)

* **`DataDiv`** holds at every row form, effect context and typing system (`dataDiv_ourInst`): the
  pure row's returner at a data type of A's is a returner at closed data at every row environment,
  which is what our `DivFree` reads.
* **S2 and S3 fail at today's kernel as written, at every effect context**
  (`not_safety_tier1Open`, `not_effSafe_tier1Open`).  Our instance's typing reads a row `ε` through
  `RF.den` and asks nothing of its names: today's `[perform]` types `perform (0, (0, ()))` at the
  row `ε₀ = [0.0 : 1 ↠ 1]` (`der_perform₀`), which finds the operation and is unr-free.  No label
  is named `0` (a label of `orowAlg Ξ` is a name `n ≠ 0` that `Ξ` declares), so `ε₀` admits no
  operation of a label (`not_has_ε₀`): the runner that answers nothing keeps its protocol and
  answers everything `ε₀` admits.  The program takes no step (`no_ostep_op`) and is no answer:
  S2's `SafeRuns` fails, and S3's three cases fail, its `StopsIn` asking `has ε₀ l i` of a
  label.  The configuration is the initial one, in the empty world.

`EA.WF` (`orowAlg`'s: every name a row finds is a label, at its declared signature) is what such a
row lacks; nothing in `ourInst`'s `der` or in today's rules asks it.  Whether `der`, the typing
system or S2 and S3 should read it is the user's decision.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload)
open BoCa.Lifetime (LifeCtx)
open Targets (CDerivesNU RowForm EffCtx orowRF orowAlg ORow RowEnv)

/-! ### `DataDiv` -/

section DataDiv
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

/-- A data type of A's denotes closed data at every row environment. -/
theorem data_den_of_dataTy :
    ∀ {A : OVTy}, (ourInst (ℍ := ℍ) RF Ξ J).DataTy A → ∀ η : RowEnv, (A.den η).Data
  | _, .unit, _ => VTy.DataB.unit 0
  | _, .zero, _ => VTy.DataB.zero 0
  | _, .tensor hA hB, η => VTy.DataB.tensor (data_den_of_dataTy hA η) (data_den_of_dataTy hB η)
  | _, .sum hA hB, η => VTy.DataB.sum (data_den_of_dataTy hA η) (data_den_of_dataTy hB η)

/-- **`DataDiv` at our instance**, at every row form, effect context and typing system: the pure
row's returner at a data type is `F_S A₀` at closed data `A₀` at every row environment. -/
theorem dataDiv_ourInst : (ourInst (ℍ := ℍ) RF Ξ J).DataDiv :=
  fun A hA η => ⟨_, A.den η, rfl, data_den_of_dataTy hA η⟩

end DataDiv

/-! ### S2 and S3 at today's kernel -/

/-- An operation at the reserved name `0`: `0.0 : 1 ↠ 1`, linear. -/
def op₀ : OpSig := ⟨0, 0, .lin, .unit, .unit⟩

/-- The closed row holding `op₀` alone. -/
def ε₀ : ORow := ⟨[op₀], none⟩

/-- `perform (0, (0, ()))`. -/
def perform₀ : Expr := performE (opArgE 0 0 (.val Val.unit))

theorem rowNU_op₀ : Row.NU [op₀] := by
  intro n i o h
  obtain ⟨hm, -⟩ := Row.find_mem h
  rw [List.mem_singleton] at hm
  subst hm
  exact Or.inr (by decide)

/-- **Today's kernel types `perform₀` at `F_{ε₀} 1`**, by `[perform]`: `ε₀` is unr-free and finds
`op₀`, and `[perform]` asks nothing of the name. -/
theorem der_perform₀ (Ξ : EffCtx) :
    (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).der [] perform₀
      ((ourInst (ℍ := ℍ) orowRF Ξ tier1Open).F ε₀ .unit) := by
  refine .inl ⟨[], by simp, fun _ h => absurd h List.not_mem_nil, trivial, fun η _ => ?_⟩
  show CDerivesNU LifeCtx.empty [] perform₀ (.comp (CTy.effOf [op₀] .unit))
  exact CDerivesNU.effPerform (S := [op₀]) (o := op₀) rowNU_op₀
    (Row.find_of_mem (List.pairwise_singleton _ _) (List.mem_singleton_self _)) rfl
    (CDerivesNU.unitI .nil)

/-- **`ε₀` admits no operation of a label**: a label's name is not `0`. -/
theorem not_has_ε₀ {Ξ : EffCtx} {J : OurTyping orowRF} (l : (orowAlg Ξ).Lab) (i : ℕ) :
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ J).has ε₀ l i := by
  rintro ⟨-, h⟩
  have h₁ := h (fun _ => [])
  simp only [Targets.Row.Has, ε₀, List.append_nil, Row.find, List.find?_cons,
    List.find?_nil] at h₁
  by_cases hk : l.1 = op₀.n ∧ UInt32.ofNat i = op₀.i
  · exact l.2.1 hk.1
  · simp [hk] at h₁

/-- Every runner answers every operation `ε₀` admits. -/
theorem answers_ε₀ {Ξ : EffCtx} {J : OurTyping orowRF} (R : (ourInst (ℍ := ℍ) orowRF Ξ J).Runner) :
    (ourInst (ℍ := ℍ) orowRF Ξ J).Answers R ε₀ :=
  fun l i h => absurd h (not_has_ε₀ l i)

/-- `perform₀`'s configuration takes no step of our machine. -/
theorem no_ostep_perform₀ {Ξ : EffCtx} (μ : Heap) {ev : A.Ev (orowAlg Ξ).Lab OVal Expr}
    {c' : Heap × Expr} : ¬ OStep (ℍ := ℍ) orowRF Ξ (μ, perform₀) ev c' :=
  no_ostep_op (r := false) (K := .hole) 0 0 ⟨.unit, .unit⟩ rfl rfl

/-- `perform₀` is no answer of A's. -/
theorem perform₀_not_oval : ¬ IsOVal perform₀ :=
  not_isOVal_prim_app (p := .perform) (by decide) _

/-- **S2 fails at today's kernel, at every effect context.**  `perform₀` is typed at `F_{ε₀} 1`;
the runner that answers nothing keeps its protocol and answers every operation `ε₀` admits; and
the run is stuck at once. -/
theorem not_safety_tier1Open (Ξ : EffCtx) : ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).Safety := by
  intro hS
  have hrun := ((hS _ r₀_respects ε₀ (answers_ε₀ _)).1 perform₀ .unit A.EffectSystem.DataTy.unit
    (der_perform₀ Ξ)).1
  rcases hrun _ .refl with ⟨⟨v, hv⟩, -⟩ | ⟨ev, c', hst⟩
  · have hv' : perform₀ = v.1 := hv
    exact perform₀_not_oval (by rw [hv']; exact v.2)
  · cases hst with
    | mach h => exact no_ostep_perform₀ _ h
    | io _ _ hans _ => exact hans

/-- **S3 fails at today's kernel, at every effect context.**  `perform₀` is typed at `F_{ε₀} 1`,
is no answer, takes no step, and `StopsIn ε₀` asks for a label `ε₀` admits. -/
theorem not_effSafe_tier1Open (Ξ : EffCtx) : ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).EffSafe := by
  intro hE
  rcases hE perform₀ ε₀ .unit (der_perform₀ Ξ) _ .refl with
    ⟨⟨v, hv⟩, -⟩ | ⟨ev, c', hst⟩ | ⟨K, l, i, v, o, -, hhas, -⟩
  · have hv' : perform₀ = v.1 := hv
    exact perform₀_not_oval (by rw [hv']; exact v.2)
  · exact no_ostep_perform₀ _ hst
  · exact not_has_ε₀ l i hhas

end Targets.Inst

end

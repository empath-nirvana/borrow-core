import Targets.Instance.Checks

/-!
# The Instance — `DataDiv` at our instance, and why rows are tied to the effect context

* **`DataDiv`** holds at every row form, effect context and typing system (`dataDiv_ourInst`): the
  pure row's returner at a data type of A's is a returner at closed data at every row environment,
  which is what our `DivFree` reads.
* **The tie is needed** (`safety_needs_tie`, the scope of decision D1).  Today's `[perform]` types
  `perform (0, (0, ()))` at the row `ε₀ = [0.0 : 1 ↠ 1]` (`derNU_perform₀`), which finds the
  operation and is unr-free.  No label is named `0` (a label of `orowAlg Ξ` is a name `n ≠ 0` that
  `Ξ` declares), so `ε₀` admits no operation of a label (`not_has_ε₀`), and the program is stuck at
  once and is no answer.  Read at `ε₀`, the program would break S2 and S3 at every effect context.
  `ε₀` is tied to no effect context, so our instance does not read a program at it
  (`not_der_perform₀`).  S2 and S3 at today's kernel, through the platform a runner
  gives and B's adequacy, are in `Targets/I/Restricted/InstanceSafety.lean`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload)
open BoCa.Lifetime (LifeCtx)
open Targets (CDerivesNU RowForm EffCtx orowRF orowAlg ORow RowEnv RowAt orowRF_den)

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
def op₀ : OpSig := ⟨0, 0, .lin, .unit, .unit, .ret .unit⟩

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
theorem derNU_perform₀ : CDerivesNU LifeCtx.empty [] perform₀ (.comp (CTy.effOf [op₀] .unit)) :=
  CDerivesNU.effPerform (S := [op₀]) (o := op₀) rowNU_op₀
    (Row.find_of_mem (List.pairwise_singleton _ _) (List.mem_singleton_self _)) rfl
    (CDerivesNU.unitI .nil)

/-- `ε₀` is tied to no effect context: it finds an operation of the reserved name `0`. -/
theorem not_rowAt_op₀ (Ξ : EffCtx) : ¬ RowAt Ξ [op₀] := fun h =>
  (h 0 0 op₀ (Row.find_of_mem (List.pairwise_singleton _ _) (List.mem_singleton_self _))).1 rfl

/-- **Our instance does not read `perform₀` at `ε₀`**: the row is tied to no effect context. -/
theorem not_der_perform₀ (Ξ : EffCtx) {J : OurTyping orowRF} (henv : ∀ η, J.env Ξ η = η) :
    ¬ (ourInst (ℍ := ℍ) orowRF Ξ J).der [] perform₀ ((ourInst (ℍ := ℍ) orowRF Ξ J).F ε₀ .unit) := by
  rintro ⟨hT, -⟩
  obtain ⟨S, A, he, hS⟩ := hT _ (envAt_nil Ξ)
  have he' : CTy.effOf (orowRF.den Ξ ε₀ (J.env Ξ (fun _ => []))) (OVTy.den (fun _ => []) .unit) =
      CTy.effOf S A := he
  obtain ⟨rfl, -⟩ := effOf_inj he'
  rw [henv] at hS
  exact not_rowAt_op₀ Ξ (by simpa [orowRF_den, ε₀] using hS)

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

/-- **The tie is needed** (the scope of decision D1): today's kernel types `perform₀` at `ε₀`,
which is tied to no effect context; the program is stuck at once, is no answer, and `ε₀` admits no
label's operation, so S2's runs and S3's stops would fail at every effect context; and our instance
does not read the program at `ε₀`. -/
theorem safety_needs_tie (Ξ : EffCtx) :
    CDerivesNU LifeCtx.empty [] perform₀ (.comp (CTy.effOf [op₀] .unit)) ∧ ¬ RowAt Ξ [op₀] ∧
      (∀ (μ : Heap) (ev : A.Ev (orowAlg Ξ).Lab OVal Expr) (c' : Heap × Expr),
        ¬ OStep (ℍ := ℍ) orowRF Ξ (μ, perform₀) ev c') ∧ ¬ IsOVal perform₀ ∧
      (∀ (l : (orowAlg Ξ).Lab) (i : ℕ), ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).has ε₀ l i) ∧
      ¬ (ourInst (ℍ := ℍ) orowRF Ξ tier1Open).der [] perform₀
        ((ourInst (ℍ := ℍ) orowRF Ξ tier1Open).F ε₀ .unit) :=
  ⟨derNU_perform₀, not_rowAt_op₀ Ξ, fun μ _ _ => no_ostep_perform₀ μ, perform₀_not_oval,
    not_has_ε₀, not_der_perform₀ Ξ (fun _ => rfl)⟩

end Targets.Inst

end

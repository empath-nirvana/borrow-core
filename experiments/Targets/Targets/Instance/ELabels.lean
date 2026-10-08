import Targets.Instance.J1

/-!
# The Instance — the (E) properties' labels

A's (E) properties name their labels by signature (`ForLabels`).  At our instance a label is a name
of the effect context, and its signature is the one the context declares at that name, read as A's
(`ourInst`'s `sig`).

* `sig_*_iff`: a label has one of the (E) signatures exactly when the context declares the matching
  Core signature at its name.  An `exn` label's qualifier is affine or unrestricted (both make the
  abortive `1 ↠ 0`); every other signature fixes its qualifier, the affine ones at a context with no
  resuming `unr` operation.
* `labelsAt_*`: at a context with two names at each signature the (E) programs use (`Rich`), the
  labels each (E) property names exist, distinct.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open Targets (EffCtx orowRF orowAlg)

theorem OVTy.ofV_eq_unit {A : VTy} (h : OVTy.ofV A = .unit) : A = .unit := by
  cases A <;> simp_all [OVTy.ofV]

theorem OVTy.ofV_eq_zero {A : VTy} (h : OVTy.ofV A = .zero) : A = .zero := by
  cases A <;> simp_all [OVTy.ofV]

theorem OVTy.ofV_eq_bool {A : VTy} (h : OVTy.ofV A = .sum .unit .unit) : A = boolT := by
  cases A <;> simp only [OVTy.ofV, reduceCtorEq, OVTy.sum.injEq] at h
  obtain ⟨h₁, h₂⟩ := h
  rw [OVTy.ofV_eq_unit h₁, OVTy.ofV_eq_unit h₂]
  rfl

section
variable {Ξ : EffCtx} {J : OurTyping orowRF}

local notation "𝕊" => ourInst (ℍ := ℍ) orowRF Ξ J

/-- A label's signature at our instance: the context's, read as A's. -/
theorem sig_eq (l : (orowAlg Ξ).Lab) :
    (𝕊).sig l = (Ξ l.1).map fun p => ⟨OVTy.ofV p.2.1, OVTy.ofV p.2.2, clsOf p.1 p.2.2⟩ := rfl

/-- A label has a one-operation signature exactly when the context declares one operation there,
at the same argument and answer types and a qualifier of the same class. -/
theorem sig_one_iff (l : (orowAlg Ξ).Lab) (A B : VTy) (c : Targets.A.OpClass) :
    (𝕊).sig l = [⟨OVTy.ofV A, OVTy.ofV B, c⟩] ↔
      ∃ (q : Qual) (A' B' : VTy), Ξ l.1 = [(q, A', B')] ∧ OVTy.ofV A' = OVTy.ofV A ∧
        OVTy.ofV B' = OVTy.ofV B ∧ clsOf q B' = c := by
  rw [sig_eq]
  constructor
  · intro h
    cases hΞ : Ξ l.1 with
    | nil => rw [hΞ] at h; simp at h
    | cons p rest =>
        cases rest with
        | cons p' rest => rw [hΞ] at h; simp at h
        | nil =>
            rw [hΞ] at h
            obtain ⟨q, A', B'⟩ := p
            simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
            obtain ⟨h₁, h₂, h₃⟩ := Targets.A.OpSig.mk.inj h
            exact ⟨q, A', B', rfl, h₁, h₂, h₃⟩
  · rintro ⟨q, A', B', hΞ, hA, hB, hc⟩
    rw [hΞ]
    simp [hA, hB, hc]

/-- An `exn` label: `1 ↠ 0` at an affine or unrestricted qualifier. -/
theorem sig_exn_iff (l : (orowAlg Ξ).Lab) :
    (𝕊).sig l = (𝕊).sigExn ↔ ∃ q : Qual, Ξ l.1 = [(q, .unit, .zero)] ∧ q ≠ .lin := by
  have h := sig_one_iff (ℍ := ℍ) (J := J) l .unit .zero .abortive
  refine h.trans ⟨fun ⟨q, A', B', hΞ, hA, hB, hc⟩ => ?_, fun ⟨q, hΞ, hq⟩ => ?_⟩
  · rw [OVTy.ofV_eq_unit hA, OVTy.ofV_eq_zero hB] at hΞ
    refine ⟨q, hΞ, fun hq => ?_⟩
    subst hq
    rw [OVTy.ofV_eq_zero hB] at hc
    simp [clsOf] at hc
  · refine ⟨q, .unit, .zero, hΞ, rfl, rfl, ?_⟩
    cases q <;> simp_all [clsOf, VTy.isZero]

/-- A linear label at the argument `A` and the answer `B`, `B` not `0`. -/
theorem sig_lin_iff (l : (orowAlg Ξ).Lab) {A B : VTy}
    (hA : ∀ A', OVTy.ofV A' = OVTy.ofV A → A' = A) (hB : ∀ B', OVTy.ofV B' = OVTy.ofV B → B' = B) :
    (𝕊).sig l = [⟨OVTy.ofV A, OVTy.ofV B, .linear⟩] ↔ Ξ l.1 = [(.lin, A, B)] := by
  rw [sig_one_iff]
  constructor
  · rintro ⟨q, A', B', hΞ, hA', hB', hc⟩
    rw [hA A' hA', hB B' hB'] at hΞ
    have hq : q = .lin := by
      revert hc; cases q <;> simp only [clsOf] <;> split <;> simp
    rw [hΞ, hq]
  · intro hΞ
    exact ⟨.lin, A, B, hΞ, rfl, rfl, by simp [clsOf]⟩

/-- An affine label at the argument `A` and the answer `B`, `B` not `0`, at a context with no
resuming `unr` operation. -/
theorem sig_aff_iff (hΞ : Ξ.NU) (l : (orowAlg Ξ).Lab) {A B : VTy} (hBz : B.isZero = false)
    (hA : ∀ A', OVTy.ofV A' = OVTy.ofV A → A' = A) (hB : ∀ B', OVTy.ofV B' = OVTy.ofV B → B' = B) :
    (𝕊).sig l = [⟨OVTy.ofV A, OVTy.ofV B, .affine⟩] ↔ Ξ l.1 = [(.aff, A, B)] := by
  rw [sig_one_iff]
  constructor
  · rintro ⟨q, A', B', he, hA', hB', hc⟩
    rw [hA A' hA', hB B' hB'] at he
    rw [hB B' hB'] at hc
    have hq : q = .aff := by
      cases q
      · simp [clsOf] at hc
      · rfl
      · have := hΞ l.1 .unr A B (by rw [he]; exact List.mem_singleton_self _) rfl
        rw [hBz] at this; cases this
    rw [he, hq]
  · intro he
    exact ⟨.aff, A, B, he, rfl, rfl, by simp [clsOf, hBz]⟩

theorem ofV_unit_inj : ∀ A' : VTy, OVTy.ofV A' = OVTy.ofV .unit → A' = .unit :=
  fun _ h => OVTy.ofV_eq_unit h

theorem ofV_bool_inj : ∀ A' : VTy, OVTy.ofV A' = OVTy.ofV boolT → A' = boolT :=
  fun _ h => OVTy.ofV_eq_bool h

/-- A `wait` label: `1 ↠ 1`, affine. -/
theorem sig_wait_iff (hΞ : Ξ.NU) (l : (orowAlg Ξ).Lab) :
    (𝕊).sig l = (𝕊).sigWait ↔ Ξ l.1 = [(.aff, .unit, .unit)] :=
  sig_aff_iff (J := J) hΞ l rfl ofV_unit_inj ofV_unit_inj

/-- A `yield` label: `bool ↠ 1`, affine. -/
theorem sig_yield_iff (hΞ : Ξ.NU) (l : (orowAlg Ξ).Lab) :
    (𝕊).sig l = (𝕊).sigYield ↔ Ξ l.1 = [(.aff, boolT, .unit)] :=
  sig_aff_iff (J := J) hΞ l rfl ofV_bool_inj ofV_unit_inj

/-- A `log` label: `bool ↠ 1`, linear. -/
theorem sig_log_iff (l : (orowAlg Ξ).Lab) :
    (𝕊).sig l = (𝕊).sigLog ↔ Ξ l.1 = [(.lin, boolT, .unit)] :=
  sig_lin_iff (J := J) l ofV_bool_inj ofV_unit_inj

/-- A `tick` label: `1 ↠ 1`, linear. -/
theorem sig_tick_iff (l : (orowAlg Ξ).Lab) :
    (𝕊).sig l = (𝕊).sigTick ↔ Ξ l.1 = [(.lin, .unit, .unit)] :=
  sig_lin_iff (J := J) l ofV_unit_inj ofV_unit_inj

/-- A `kube` label: `1 ↠ bool`, linear. -/
theorem sig_kube_iff (l : (orowAlg Ξ).Lab) :
    (𝕊).sig l = (𝕊).sigKube ↔ Ξ l.1 = [(.lin, .unit, boolT)] :=
  sig_lin_iff (J := J) l ofV_unit_inj ofV_bool_inj

end

/-! ### Labels from a rich context -/

section Rich
variable {Ξ : EffCtx}

/-- The label of a name the context declares at a nonempty signature of at most `2³²`
operations. -/
def labOf (n : UInt32) (h0 : n ≠ 0) (hne : Ξ n ≠ []) (hlen : (Ξ n).length ≤ 2 ^ 32) :
    (orowAlg Ξ).Lab :=
  ⟨n, h0, hne, hlen⟩

/-- **Two labels at each signature the (E) programs use**, at a rich context. -/
theorem rich_labs (hR : Rich Ξ) {E : List (Qual × VTy × VTy)} (hE : E ∈ eSigs) :
    ∃ l₁ l₂ : (orowAlg Ξ).Lab, l₁ ≠ l₂ ∧ Ξ l₁.1 = E ∧ Ξ l₂.1 = E := by
  obtain ⟨n₁, n₂, hne, h₁, h₂, e₁, e₂⟩ := hR E hE
  have hE0 : E ≠ [] := by
    intro h; subst h; simp [eSigs] at hE
  have hlen : E.length ≤ 2 ^ 32 := by
    simp only [eSigs, List.mem_cons, List.not_mem_nil, or_false] at hE
    rcases hE with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  refine ⟨labOf n₁ h₁ (by rw [e₁]; exact hE0) (by rw [e₁]; exact hlen),
    labOf n₂ h₂ (by rw [e₂]; exact hE0) (by rw [e₂]; exact hlen), ?_, e₁, e₂⟩
  intro h
  exact hne (congrArg Subtype.val h)

/-- Labels at different signatures are different labels. -/
theorem lab_ne_of_sig {l₁ l₂ : (orowAlg Ξ).Lab} (h : Ξ l₁.1 ≠ Ξ l₂.1) : l₁ ≠ l₂ :=
  fun he => h (by rw [he])

end Rich

end Targets.Inst

end

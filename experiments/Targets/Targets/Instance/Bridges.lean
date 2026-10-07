import Targets.Instance.Core
import Targets.A.NonVacuity

/-!
# The Instance — bridges from Core to A's laws (RESTRUCTURE §4.1)

Each bridge takes Core's facts (and, where one is needed, a base statement as a hypothesis), so none
needs B; where a B theorem discharges a hypothesis, the discharge lives in I.

**Proved here** (syntactic, at every row form, effect context and typing system):

* `confLaws_ourInst`: `init` puts a term in, `setT` replaces it;
* `kontLaws_ourInst` (names told apart by the row form, as `orowRF`'s are): Core's contexts compose
  (`Kont.plug_comp`), the five named frames plug as their formers, catch, stop and hold what A says
  (`Kont.HasHnd`, `hasHnd_comp`; no `ubind` and no `cfin` frame; `Kont.fins`);
* `noIO_ourInst`: the machine never answers an operation;
* `dataInj_ourInst`: answers are told apart, and an operation or a driven term is no answer;
* `liftExt_orow`: at the tail-variable rows, two distinct labels compose, and the second's row is
  below the composite (`not_reconciler_of_monoCallback`'s algebraic hypothesis).

The rest of `MachShape` and S4 are in `Targets/Instance/Machine.lean` (given `LiveOK`), the let law
and S1 at today's kernel in `Targets/Instance/J1Checks.lean`, and S2, S3 and `LiveOK` at today's
kernel in `Targets/I/Restricted/InstanceSafety.lean`.  **OPEN** (to build; RESTRUCTURE §4.1):
`noIntercept_of_core`, `unwindOrder_of_core` (S5), and S6's proof route (OQ-50, §7 Q9).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE)
open Targets (RowForm EffCtx orowRF orowAlg ORow RowEq)

variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

/-! ### Contexts -/

theorem noUnwind_comp : ∀ (K₁ K₂ : Kont), (K₁.comp K₂).NoUnwind ↔ K₁.NoUnwind ∧ K₂.NoUnwind
  | .hole, _ => by simp [Kont.comp, Kont.NoUnwind]
  | .appR f K, K₂ => by simp only [Kont.comp, Kont.NoUnwind, noUnwind_comp K K₂, and_assoc]
  | .pairL K _, K₂ | .pairR _ K, K₂ | .letpair K _, K₂ | .case K _ _, K₂ | .appL K _, K₂
  | .seq K _, K₂ | .inj₁ K, K₂ | .inj₂ K, K₂ => by
      simp only [Kont.comp, Kont.NoUnwind, noUnwind_comp K K₂]

theorem fins_of_noUnwind : ∀ (K : Kont), K.NoUnwind → K.fins = []
  | .hole, _ => rfl
  | .appR f K, h => by
      obtain ⟨hu, -, hK⟩ := h
      simp only [Kont.fins, fins_of_noUnwind K hK, List.nil_append]
      split <;> simp_all
  | .pairL K _, h | .pairR _ K, h | .letpair K _, h | .case K _ _, h | .appL K _, h
  | .seq K _, h | .inj₁ K, h | .inj₂ K, h => fins_of_noUnwind K h

theorem finE_shift (D : Expr) : finE (.lam (D.shift 1 0)) = D := by
  simp only [finE]
  rw [Expr.subst_shift 0 0 0 Val.unit D (le_refl _) (le_refl _), Expr.shift_zero]

theorem appK_hasHnd (V : Expr) (n : UInt32) : (appK V).HasHnd n = false := by
  unfold appK; split <;> rfl

theorem appK_noUnwind (V : Expr) : (appK V).NoUnwind := by
  unfold appK; split <;> exact trivial

theorem appK_fins (V : Expr) : (appK V).fins = [] := by
  unfold appK; split <;> rfl

/-! ### The machine's shape: the syntactic laws -/

theorem confLaws_ourInst : (ourInst (ℍ := ℍ) RF Ξ J).ConfLaws :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩

theorem bindK_noUnwind (N : Expr) : (bindK N).NoUnwind :=
  ⟨fun _ h => Expr.noConfusion h, fun _ h => Expr.noConfusion h, trivial⟩

theorem handleK_noUnwind (n : UInt32) (r : Expr) (cs : List Expr) : (handleK n r cs).NoUnwind :=
  ⟨fun _ h => by simp at h, fun _ h => by simp at h, trivial⟩

theorem driveK_noUnwind : driveK.NoUnwind :=
  ⟨fun _ h => Expr.noConfusion h, fun _ h => Expr.noConfusion h, trivial⟩

theorem thenK_not_noUnwind (N D : Expr) : ¬ (thenK N D).NoUnwind := fun h => h.1 _ rfl

theorem handleK_hasHnd (hinj : Function.Injective (RF.name Ξ)) (l m : (RF.alg Ξ).Lab) (r : Expr)
    (cs : List Expr) : (handleK (RF.name Ξ l) r cs).HasHnd (RF.name Ξ m) = true ↔ m = l := by
  simp only [handleK, hndValE, Kont.HasHnd, Bool.or_false, beq_iff_eq]
  exact ⟨fun h => hinj h.symm, fun h => h ▸ rfl⟩

theorem thenK_fins (N D : Expr) : List.map finE (thenK N D).fins = [D] := by
  simp only [thenK, Kont.fins, List.nil_append, List.map_cons, List.map_nil]
  rw [finE_shift]

theorem fins_map_comp (K₁ K₂ : Kont) :
    List.map finE (K₁.comp K₂).fins = List.map finE K₂.fins ++ List.map finE K₁.fins := by
  rw [fins_comp, List.map_append]

theorem fins_map_of_noUnwind (K : Kont) (h : K.NoUnwind) : List.map finE K.fins = [] := by
  rw [fins_of_noUnwind K h]; rfl

theorem appK_fins_map (V : Expr) : List.map finE (appK V).fins = [] := by
  rw [appK_fins]; rfl

/-- **The context laws**, when the row form tells names apart. -/
theorem kontLaws_ourInst (hinj : Function.Injective (RF.name Ξ)) :
    (ourInst (ℍ := ℍ) RF Ξ J).KontLaws :=
  ⟨fun _ => rfl, fun K₁ K₂ t => Kont.plug_comp K₁ K₂ t, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl, fun V _ => appK_hasHnd V.1 _,
    fun l H m => handleK_hasHnd hinj l m H.1.1 (H.2.map Subtype.val), fun _ _ _ => rfl, fun _ => rfl,
    fun K₁ K₂ _ => hasHnd_comp _ K₁ K₂, trivial, fun N => bindK_noUnwind N,
    fun V => appK_noUnwind V.1, fun _ _ => handleK_noUnwind _ _ _, fun N D => thenK_not_noUnwind N D,
    driveK_noUnwind, fun K₁ K₂ => noUnwind_comp K₁ K₂, rfl, fun _ => rfl, fun V => appK_fins_map V.1,
    fun _ _ => rfl, fun N D => thenK_fins N D, rfl, fun K₁ K₂ => fins_map_comp K₁ K₂,
    fun K h => fins_map_of_noUnwind K h⟩

theorem labelOf_ne_io (a : Expr) (l : (RF.alg Ξ).Lab) (i : ℕ) (v w : OVal) :
    labelOf RF Ξ a ≠ .io l i v w := by
  unfold labelOf
  split_ifs <;> simp

/-- **The machine never answers an operation.** -/
theorem noIO_ourInst : (ourInst (ℍ := ℍ) RF Ξ J).NoIO := by
  intro c l i v w c' h
  change OStep (ℍ := ℍ) RF Ξ c (.io l i v w) c' at h
  generalize hev : (A.Ev.io l i v w : A.Ev (RF.alg Ξ).Lab OVal Expr) = ev at h
  cases h with
  | mach _ => exact labelOf_ne_io _ _ _ _ _ hev.symm
  | again => cases hev
  | fin => cases hev

/-! ### Answers are told apart -/

theorem eq_hole_of_plug_prim {K : Kont} {e : Expr} {p : Prim} (h : K.plug e = .prim p) :
    K = .hole := by
  cases K <;> simp_all [Kont.plug]

theorem isOVal_of_plug : ∀ (K : Kont) {e : Expr}, IsOVal (K.plug e) → IsOVal e
  | .hole, _, h => h
  | .pairL K _, _, h => by cases h with | pair h₁ _ => exact isOVal_of_plug K h₁
  | .pairR _ K, _, h => by cases h with | pair _ h₂ => exact isOVal_of_plug K h₂
  | .inj₁ K, _, h => by cases h with | inj₁ h => exact isOVal_of_plug K h
  | .inj₂ K, _, h => by cases h with | inj₂ h => exact isOVal_of_plug K h
  | .appR _ K, _, h => by cases h with | storeV h => exact isOVal_of_plug K h
  | .appL K u, e, h => by
      generalize hx : (Kont.appL K u).plug e = x at h
      cases h with
      | storeV _ =>
          simp only [Kont.plug, Expr.app.injEq] at hx
          obtain ⟨hp, -⟩ := hx
          obtain rfl := eq_hole_of_plug_prim hp
          simp only [Kont.plug] at hp
          subst hp; exact .prim
      | _ => simp [Kont.plug] at hx
  | .letpair _ _, _, h | .case _ _ _, _, h | .seq _ _, _, h => by cases h

theorem not_isOVal_prim_app {p : Prim} (hp : p ≠ .store) (x : Expr) : ¬ IsOVal (.app (.prim p) x) := by
  intro h
  cases h with
  | storeV _ => exact hp rfl

theorem oval_ext_inj₁ {a b : OVal} (h : Expr.inj₁ a.1 = Expr.inj₁ b.1) : a = b :=
  Subtype.ext (Expr.inj₁.inj h)

theorem oval_ext_inj₂ {a b : OVal} (h : Expr.inj₂ a.1 = Expr.inj₂ b.1) : a = b :=
  Subtype.ext (Expr.inj₂.inj h)

/-- **Answers are told apart.** -/
theorem dataInj_ourInst : (ourInst (ℍ := ℍ) RF Ξ J).DataInj := by
  refine ⟨fun a b h => Subtype.ext h, fun a b a' b' h => ?_, fun a b h => ?_, fun a b h => ?_,
    fun a b h => ?_, fun a b h => ?_, fun a => ⟨fun h => ?_, fun h => ?_⟩,
    fun a b c => ⟨fun h => ?_, fun h => ?_⟩, fun K l i v w => ⟨fun h => ?_, fun h => ?_⟩,
    fun M w h => ?_⟩
  · have h' : Expr.pair a.1 b.1 = Expr.pair a'.1 b'.1 := congrArg Subtype.val h
    simp only [Expr.pair.injEq] at h'
    exact ⟨Subtype.ext h'.1, Subtype.ext h'.2⟩
  · exact oval_ext_inj₁ (congrArg Subtype.val h)
  · exact oval_ext_inj₂ (congrArg Subtype.val h)
  · exact Expr.noConfusion (congrArg Subtype.val h : Expr.inj₁ a.1 = Expr.inj₂ b.1)
  · exact Expr.noConfusion (congrArg Subtype.val h : Expr.unit = Expr.pair a.1 b.1)
  · exact Expr.noConfusion (congrArg Subtype.val h : Expr.unit = Expr.inj₁ a.1)
  · exact Expr.noConfusion (congrArg Subtype.val h : Expr.unit = Expr.inj₂ a.1)
  · exact Expr.noConfusion (congrArg Subtype.val h : Expr.pair a.1 b.1 = Expr.inj₁ c.1)
  · exact Expr.noConfusion (congrArg Subtype.val h : Expr.pair a.1 b.1 = Expr.inj₂ c.1)
  · have h' : K.plug ((ourInst (ℍ := ℍ) RF Ξ J).perform l i v) = w.1 := h
    by_cases hi : i < 2 ^ 32
    · rw [perform_eq (ℍ := ℍ) (l := l) v hi] at h'
      exact not_isOVal_prim_app (p := .perform) (by decide) _ (isOVal_of_plug K (h' ▸ w.2))
    · rw [perform_junk (ℍ := ℍ) (l := l) v hi] at h'
      exact not_isOVal_prim_app (p := .perform) (by decide) _ (isOVal_of_plug K (h' ▸ w.2))
  · have h' : K.plug ((ourInst (ℍ := ℍ) RF Ξ J).raise l i v) = w.1 := h
    by_cases hi : i < 2 ^ 32
    · rw [raise_eq (ℍ := ℍ) (l := l) v hi] at h'
      exact not_isOVal_prim_app (p := .raise) (by decide) _ (isOVal_of_plug K (h' ▸ w.2))
    · rw [raise_junk (ℍ := ℍ) (l := l) v hi] at h'
      exact not_isOVal_prim_app (p := .raise) (by decide) _ (isOVal_of_plug K (h' ▸ w.2))
  · have h' : driveE M = w.1 := h
    exact not_isOVal_prim_app (p := .lit (.u8 0)) (by decide) _ (h' ▸ w.2)

/-! ### The tail-variable rows: two labels compose -/

theorem rowEq_comm_ofEff {n n' : UInt32} (E E' : List (Qual × VTy × VTy)) (h : n ≠ n') :
    RowEq (Row.ofEff n E 0 ++ Row.ofEff n' E' 0) (Row.ofEff n' E' 0 ++ Row.ofEff n E 0) := by
  intro m i
  rw [Row.find_append, Row.find_append]
  by_cases hm : m = n
  · subst hm
    rw [find_ofEff_other E' h i]
    cases Row.find (Row.ofEff m E 0) m i <;> rfl
  · rw [find_ofEff_other E hm i]
    cases Row.find (Row.ofEff n' E' 0) m i <;> rfl

/-- **Two distinct labels compose, and the second's row is below the composite**, at `orowRF`. -/
theorem liftExt_orow (J' : OurTyping orowRF) :
    A.EffectSystem.LiftExt (ourInst (ℍ := ℍ) orowRF Ξ J') := by
  intro l l' hne
  refine ⟨⟨Row.ofEff l.1 (Ξ l.1) 0 ++ Row.ofEff l'.1 (Ξ l'.1) 0, none⟩, rfl,
    ⟨⟨Row.ofEff l.1 (Ξ l.1) 0, none⟩, ⟨Row.ofEff l'.1 (Ξ l'.1) 0 ++ Row.ofEff l.1 (Ξ l.1) 0, none⟩,
      rfl, rfl, ?_⟩⟩
  exact rowEq_comm_ofEff _ _ (fun h => hne (Subtype.ext h).symm)

/-- `orowRF`'s labels are names: the row form tells them apart. -/
theorem orowRF_name_injective (Ξ : EffCtx) : Function.Injective (orowRF.name Ξ) :=
  fun _ _ h => Subtype.ext h

/-- **The context laws at the tail-variable rows.** -/
theorem kontLaws_orow (J' : OurTyping orowRF) : (ourInst (ℍ := ℍ) orowRF Ξ J').KontLaws :=
  kontLaws_ourInst (orowRF_name_injective Ξ)

end Targets.Inst

end

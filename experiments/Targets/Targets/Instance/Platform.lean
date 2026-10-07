import Targets.Instance.Safety

/-!
# The Instance — the platform a runner gives, and its steps

A runner of A answers the operations of labels; a platform of Core answers operations by name and
index (RESTRUCTURE §4.1).  `platformOf R S` is the platform of the runner `R` at the row `S`: it
answers the operations of `S`, one per key (`firstOps`), that `R` answers, as `R` does, at closed
Core values.

* At a row tied to the effect context (decision D1), it keeps its protocol when `R` does
  (`platformOf_respects`): an answered operation is the label's, at the signature the effect context
  declares, which `R`'s protocol makes linear and data.
* It answers only operations of `S`, at `S`'s entries (`find_platformOf`).
* A step under the platform is a step under the runner (`rstep_of_pstep`).  The converse holds at
  a closed configuration that goes on under the platform: there the runner answers as the platform
  does (`pstep_of_io`, `Targets/I/Restricted/InstanceSafety.lean`).

A's data types and values at our instance are Core's data, read through `OVTy.ofV`
(`dataVal_ofVal`, `core_dataVal`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload)
open Targets (RowForm EffCtx orowRF orowAlg ORow RowAt Platform PStep PSteps Conf DataVal)

/-! ### A row's entries, one per key -/

/-- A row's entries that its lookup finds, one per key, in order. -/
def firstOps : Row → Row
  | [] => []
  | o :: S => o :: (firstOps S).filter (fun o' => !(decide (o'.n = o.n ∧ o'.i = o.i)))

theorem find_filter_other {o : OpSig} {n i : UInt32} (h : ¬ (n = o.n ∧ i = o.i)) :
    ∀ L : Row, Row.find (L.filter (fun o' => !(decide (o'.n = o.n ∧ o'.i = o.i)))) n i =
      Row.find L n i
  | [] => rfl
  | x :: L => by
      unfold Row.find
      by_cases hx : x.n = o.n ∧ x.i = o.i
      · have hk : ¬ (n = x.n ∧ i = x.i) := fun hk => h ⟨hk.1.trans hx.1, hk.2.trans hx.2⟩
        rw [List.filter_cons_of_neg (by simp [hx]), List.find?_cons_of_neg (by simpa using hk)]
        exact find_filter_other h L
      · rw [List.filter_cons_of_pos (by simp [hx])]
        by_cases hk : n = x.n ∧ i = x.i
        · rw [List.find?_cons_of_pos (by simpa using hk), List.find?_cons_of_pos (by simpa using hk)]
        · rw [List.find?_cons_of_neg (by simpa using hk), List.find?_cons_of_neg (by simpa using hk)]
          exact find_filter_other h L

theorem find_firstOps : ∀ (S : Row) (n i : UInt32), Row.find (firstOps S) n i = Row.find S n i
  | [], _, _ => rfl
  | o :: S, n, i => by
      unfold firstOps
      by_cases hk : n = o.n ∧ i = o.i
      · unfold Row.find
        rw [List.find?_cons_of_pos (by simpa using hk), List.find?_cons_of_pos (by simpa using hk)]
      · have e₁ : Row.find (o :: (firstOps S).filter (fun o' => !(decide (o'.n = o.n ∧ o'.i = o.i))))
            n i = Row.find ((firstOps S).filter (fun o' => !(decide (o'.n = o.n ∧ o'.i = o.i)))) n i := by
          unfold Row.find; rw [List.find?_cons_of_neg (by simpa using hk)]
        have e₂ : Row.find (o :: S) n i = Row.find S n i := by
          unfold Row.find; rw [List.find?_cons_of_neg (by simpa using hk)]
        rw [e₁, e₂, find_filter_other hk, find_firstOps S n i]

theorem uniq_firstOps : ∀ S : Row, (firstOps S).Uniq
  | [] => List.Pairwise.nil
  | o :: S => by
      unfold firstOps
      refine List.pairwise_cons.2 ⟨fun b hb => ?_, (uniq_firstOps S).filter _⟩
      have := (List.mem_filter.1 hb).2
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at this
      exact fun h => this ⟨h.1.symm, h.2.symm⟩

/-! ### Data at our instance -/

section Data
variable {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF}

/-- A data type of A's at `OVTy.ofV B` is Core data. -/
theorem data_of_dataTy_ofV {B : VTy} (h : (ourInst (ℍ := ℍ) RF Ξ J).DataTy (OVTy.ofV B)) : B.Data := by
  have := data_den_of_dataTy h (fun _ => [])
  rwa [OVTy.den_ofV] at this

/-- A Core data value at a type A reads as data is A's data value. -/
theorem dataVal_ofVal : ∀ {T : OVTy}, (ourInst (ℍ := ℍ) RF Ξ J).DataTy T →
    ∀ {B : VTy}, T = OVTy.ofV B → ∀ {v : Val}, DataVal B v →
      (ourInst (ℍ := ℍ) RF Ξ J).DataVal T (OVal.ofVal v)
  | _, .unit, B, hB, v, hv => by
      change OVTy.unit = OVTy.ofV B at hB
      cases B <;> simp [OVTy.ofV] at hB
      cases hv
      exact .unit
  | _, .zero, B, hB, v, hv => by
      change OVTy.zero = OVTy.ofV B at hB
      cases B <;> simp [OVTy.ofV] at hB
      cases hv
  | _, @A.EffectSystem.DataTy.tensor _ T₁ T₂ hA hC, B, hB, v, hv => by
      change OVTy.tensor T₁ T₂ = OVTy.ofV B at hB
      cases B <;> simp [OVTy.ofV] at hB
      obtain ⟨rfl, rfl⟩ := hB
      cases hv with
      | pair h₁ h₂ => exact .pair (dataVal_ofVal hA rfl h₁) (dataVal_ofVal hC rfl h₂)
  | _, @A.EffectSystem.DataTy.sum _ T₁ T₂ hA hC, B, hB, v, hv => by
      change OVTy.sum T₁ T₂ = OVTy.ofV B at hB
      cases B <;> simp [OVTy.ofV] at hB
      obtain ⟨rfl, rfl⟩ := hB
      cases hv with
      | inj₁ h => exact .inl (dataVal_ofVal hA rfl h)
      | inj₂ h => exact .inr (dataVal_ofVal hC rfl h)

/-- A's data value at a type it reads as data is Core data, at the Core value it is. -/
theorem core_dataVal : ∀ {T : OVTy} {w : OVal} (hw : (ourInst (ℍ := ℍ) RF Ξ J).DataVal T w)
    {B : VTy}, T = OVTy.ofV B → DataVal B ⟨w.1, isVal_of_dataVal hw⟩
  | _, _, .unit, B, hB => by
      change OVTy.unit = OVTy.ofV B at hB
      cases B <;> simp [OVTy.ofV] at hB
      exact .unit
  | _, _, @A.EffectSystem.DataVal.pair _ T₁ T₂ a b ha hb, B, hB => by
      change OVTy.tensor T₁ T₂ = OVTy.ofV B at hB
      cases B <;> simp [OVTy.ofV] at hB
      obtain ⟨rfl, rfl⟩ := hB
      exact .pair (core_dataVal ha rfl) (core_dataVal hb rfl)
  | _, _, @A.EffectSystem.DataVal.inl _ T₁ T₂ a ha, B, hB => by
      change OVTy.sum T₁ T₂ = OVTy.ofV B at hB
      cases B <;> simp [OVTy.ofV] at hB
      obtain ⟨rfl, rfl⟩ := hB
      exact .inj₁ (core_dataVal ha rfl)
  | _, _, @A.EffectSystem.DataVal.inr _ T₁ T₂ b hb, B, hB => by
      change OVTy.sum T₁ T₂ = OVTy.ofV B at hB
      cases B <;> simp [OVTy.ofV] at hB
      obtain ⟨rfl, rfl⟩ := hB
      exact .inj₂ (core_dataVal hb rfl)

/-- A's data values are closed. -/
theorem closed_of_dataVal : ∀ {T : OVTy} {w : OVal}, (ourInst (ℍ := ℍ) RF Ξ J).DataVal T w →
    closedAt 0 w.1 = true
  | _, _, .unit => rfl
  | _, _, @A.EffectSystem.DataVal.pair _ _ _ a b ha hb => by
      show closedAt 0 (.pair a.1 b.1) = true
      simp only [closedAt, Bool.and_eq_true]; exact ⟨closed_of_dataVal ha, closed_of_dataVal hb⟩
  | _, _, @A.EffectSystem.DataVal.inl _ _ _ a ha => by
      show closedAt 0 (.inj₁ a.1) = true
      exact closed_of_dataVal ha
  | _, _, @A.EffectSystem.DataVal.inr _ _ _ b hb => by
      show closedAt 0 (.inj₂ b.1) = true
      exact closed_of_dataVal hb

end Data

/-! ### The platform of a runner -/

section Plat
variable {Ξ : EffCtx} {J : OurTyping orowRF}

local notation "𝕊" => ourInst (ℍ := ℍ) orowRF Ξ J

/-- The signature of a label, at an operation its row is tied to `Ξ` at. -/
theorem sig_of_rowAt {l : (orowAlg Ξ).Lab} {k : ℕ} {q : Qual} {A B : VTy}
    (h : (Ξ l.1)[k]? = some (q, A, B)) :
    ((𝕊).sig l)[k]? = some ⟨OVTy.ofV A, OVTy.ofV B, clsOf q B⟩ := by
  have e : ((Ξ l.1).map (fun p : Qual × VTy × VTy =>
      (⟨OVTy.ofV p.2.1, OVTy.ofV p.2.2, clsOf p.1 p.2.2⟩ : Targets.A.OpSig OVTy)))[k]? =
      some ⟨OVTy.ofV A, OVTy.ofV B, clsOf q B⟩ := by
    rw [List.getElem?_map, h]; rfl
  exact e

theorem lin_of_clsOf {q : Qual} {B : VTy} (h : clsOf q B = .linear) :
    q = .lin ∧ (B.isZero && q != .lin) = false := by
  unfold clsOf at h
  by_cases h₁ : (B.isZero && q != .lin) = true
  · rw [if_pos h₁] at h; cases h
  · rw [if_neg h₁] at h
    by_cases h₂ : q = .lin
    · exact ⟨h₂, by simpa using h₁⟩
    · rw [if_neg h₂] at h; cases h

/-- `R` answers the operation `i` of the name `n`, at the name's label. -/
@[irreducible] def AnswersAt (R : (𝕊).Runner) (n i : UInt32) : Prop :=
  ∃ l : (orowAlg Ξ).Lab, l.1 = n ∧ R.answers l i.toNat

theorem answersAt_iff {R : (𝕊).Runner} {n i : UInt32} :
    AnswersAt R n i ↔ ∃ l : (orowAlg Ξ).Lab, l.1 = n ∧ R.answers l i.toNat := by
  unfold AnswersAt; exact Iff.rfl

open Classical in
/-- The operations of `S` that `R` answers, one per key. -/
@[irreducible] def answeredOps (R : (𝕊).Runner) (S : Row) : Row :=
  (firstOps S).filter fun o => decide (AnswersAt R o.n o.i)

open Classical in
/-- The platform's answer: `R`'s, at a closed Core value. -/
@[irreducible] def coOf (R : (𝕊).Runner) (s : R.St) (n i : UInt32) (v : Val) : Option (Val × R.St) :=
  if h : ∃ l : (orowAlg Ξ).Lab, l.1 = n then
    match R.co s (Classical.choose h) i.toNat (OVal.ofVal v) with
    | some (w, s') => if hw : IsVal w.1 ∧ closedAt 0 w.1 = true then some (⟨w.1, hw.1⟩, s') else none
    | none => none
  else none

/-- **The platform of the runner `R` at the row `S`.** -/
def platformOf (R : (𝕊).Runner) (S : Row) : Platform := ⟨answeredOps R S, R.St, R.s₀, coOf R⟩

theorem platformOf_ops (R : (𝕊).Runner) (S : Row) : (platformOf R S).ops = answeredOps R S := rfl

theorem platformOf_co (R : (𝕊).Runner) (S : Row) : (platformOf R S).co = coOf R := rfl

/-- The label of a name is the name's. -/
theorem choose_lab {n : UInt32} (h : ∃ l : (orowAlg Ξ).Lab, l.1 = n) {l : (orowAlg Ξ).Lab}
    (hl : l.1 = n) : Classical.choose h = l :=
  Subtype.ext ((Classical.choose_spec h).trans hl.symm)

/-- **The platform answers exactly the operations of `S` that `R` answers, at `S`'s entries.** -/
theorem find_platformOf {R : (𝕊).Runner} {S : Row} {n i : UInt32} {o : OpSig} :
    Row.find (platformOf R S).ops n i = some o ↔
      Row.find S n i = some o ∧ ∃ l : (orowAlg Ξ).Lab, l.1 = n ∧ R.answers l i.toNat := by
  rw [platformOf_ops]
  unfold answeredOps
  constructor
  · intro h
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem h
    obtain ⟨hm', hq⟩ := List.mem_filter.1 hm
    simp only [decide_eq_true_eq] at hq
    exact ⟨(find_firstOps S _ _).symm.trans (Row.find_of_mem (uniq_firstOps S) hm'),
      answersAt_iff.1 hq⟩
  · rintro ⟨hf, l, hl, ha⟩
    rw [← find_firstOps] at hf
    obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
    exact Row.find_of_mem ((uniq_firstOps S).filter _) (List.mem_filter.2 ⟨hm, by
      simp only [decide_eq_true_eq]; exact answersAt_iff.2 ⟨l, hl, ha⟩⟩)

/-- The platform's operations are the row's. -/
theorem platformOf_sub {R : (𝕊).Runner} {S : Row} :
    ∀ n i o, Row.find (platformOf R S).ops n i = some o → Row.find S n i = some o :=
  fun _ _ _ h => (find_platformOf.1 h).1

/-- The platform's answer is the runner's. -/
theorem coOf_some {R : (𝕊).Runner} {s s' : R.St} {n i : UInt32} {v w : Val}
    (h : coOf R s n i v = some (w, s')) :
    ∃ (l : (orowAlg Ξ).Lab) (w' : OVal), l.1 = n ∧ R.co s l i.toNat (OVal.ofVal v) = some (w', s') ∧
      w'.1 = w.1 ∧ closedAt 0 w.1 = true := by
  unfold coOf at h
  split at h
  · rename_i hex
    split at h
    · rename_i w' s'' hco
      split at h
      · rename_i hw
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨_, w', Classical.choose_spec hex, hco, rfl, hw.2⟩
      · cases h
    · cases h
  · cases h

/-- The runner's answer at a closed value is the platform's. -/
theorem coOf_of {R : (𝕊).Runner} {s s' : R.St} {l : (orowAlg Ξ).Lab} {i : UInt32} {v : Val}
    {w : OVal} (h : R.co s l i.toNat (OVal.ofVal v) = some (w, s')) (hw : IsVal w.1)
    (hc : closedAt 0 w.1 = true) : coOf R s l.1 i v = some (⟨w.1, hw⟩, s') := by
  unfold coOf
  have hex : ∃ l' : (orowAlg Ξ).Lab, l'.1 = l.1 := ⟨l, rfl⟩
  rw [dif_pos hex]
  have hc' : R.co s (Classical.choose hex) i.toNat (OVal.ofVal v) = some (w, s') :=
    (choose_lab hex rfl).symm ▸ h
  split
  · rename_i w₀ s₀ hco
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hco.symm.trans hc'))
    rw [dif_pos ⟨hw, hc⟩]
  · rename_i hco
    exact absurd (hco.symm.trans hc') (by simp)

/-- **The platform keeps its protocol**, at a row tied to the effect context, when the runner
does. -/
theorem platformOf_respects {R : (𝕊).Runner} (hR : R.Respects) {S : Row} (hS : RowAt Ξ S) :
    (platformOf R S).Respects := by
  have hU : (platformOf R S).ops.Uniq := by
    rw [platformOf_ops]; unfold answeredOps; exact (uniq_firstOps S).filter _
  -- an operation of the platform: its label, the signature `Ξ` declares, `R`'s protocol there
  have hop : ∀ o ∈ (platformOf R S).ops, ∃ l : (orowAlg Ξ).Lab, l.1 = o.n ∧ R.answers l o.i.toNat ∧
      Row.find S o.n o.i = some o ∧ clsOf o.q o.B = .linear ∧
      (𝕊).DataTy (OVTy.ofV o.A) ∧ (𝕊).DataTy (OVTy.ofV o.B) ∧
      ∀ s (v : OVal), (𝕊).DataVal (OVTy.ofV o.A) v →
        ∃ w s', R.co s l o.i.toNat v = some (w, s') ∧ (𝕊).DataVal (OVTy.ofV o.B) w := by
    intro o ho
    have hf : Row.find (platformOf R S).ops o.n o.i = some o := Row.find_of_mem hU ho
    obtain ⟨hfS, l, hl, ha⟩ := find_platformOf.1 hf
    obtain ⟨-, -, hΞ⟩ := hS o.n o.i o hfS
    have hsig := sig_of_rowAt (J := J) (l := l) (hl ▸ hΞ)
    obtain ⟨hcls, hdA, hdB, hco⟩ := hR l o.i.toNat _ ha hsig
    exact ⟨l, hl, ha, hfS, hcls, hdA, hdB, hco⟩
  refine ⟨hU, fun o ho => ?_, fun o ho => ?_, fun o ho => ?_, fun s o v ho hv => ?_,
    fun s s' o v w ho hv hco => ?_⟩
  · obtain ⟨-, -, -, hfS, -⟩ := hop o ho
    exact (hS o.n o.i o hfS).1
  · obtain ⟨-, -, -, -, hcls, -⟩ := hop o ho
    exact ⟨(lin_of_clsOf hcls).1, (lin_of_clsOf hcls).2⟩
  · obtain ⟨-, -, -, -, -, hdA, hdB, -⟩ := hop o ho
    exact ⟨data_of_dataTy_ofV hdA, data_of_dataTy_ofV hdB⟩
  · obtain ⟨l, hl, -, -, -, hdA, -, hco⟩ := hop o ho
    obtain ⟨w, s', hw, hdw⟩ := hco s _ (dataVal_ofVal hdA rfl hv)
    refine ⟨⟨w.1, isVal_of_dataVal hdw⟩, s', ?_⟩
    rw [platformOf_co, ← hl]
    exact coOf_of hw _ (closed_of_dataVal hdw)
  · obtain ⟨l, hl, -, -, -, hdA, -, hco'⟩ := hop o ho
    rw [platformOf_co] at hco
    obtain ⟨l', w', hl', hR', hw', -⟩ := coOf_some hco
    obtain rfl : l' = l := Subtype.ext (hl'.trans hl.symm)
    obtain ⟨w'', s'', hw'', hdw⟩ := hco' s _ (dataVal_ofVal hdA rfl hv)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hR'.symm.trans hw''))
    have := core_dataVal hdw rfl
    rwa [show (⟨w'.1, isVal_of_dataVal hdw⟩ : Val) = w from Subtype.ext hw'] at this

/-! ### Steps under the platform and under the runner -/

/-- An A-configuration under a runner, as a configuration under the platform. -/
def toConf {R : (𝕊).Runner} {S : Row} (c : (𝕊).RConf R) : Conf (platformOf R S) :=
  ⟨c.1.1, c.1.2, c.2⟩

/-- An operation at a Core index, as A's `perform`. -/
theorem perform_toNat (l : (orowAlg Ξ).Lab) (i : UInt32) (v : Val) :
    (𝕊).perform l i.toNat (OVal.ofVal v) = performE (.val (opPayload l.1 i v)) := by
  show (if i.toNat < 2 ^ 32 then performE (opArgE l.1 (UInt32.ofNat i.toNat) (OVal.ofVal v).1)
    else opJunk false) = _
  rw [if_pos i.toNat_lt, UInt32.ofNat_toNat]
  rfl

/-- A raise at a Core index, as A's `raise`. -/
theorem raise_toNat (l : (orowAlg Ξ).Lab) (i : UInt32) (v : Val) :
    (𝕊).raise l i.toNat (OVal.ofVal v) = raiseE (.val (opPayload l.1 i v)) := by
  show (if i.toNat < 2 ^ 32 then raiseE (opArgE l.1 (UInt32.ofNat i.toNat) (OVal.ofVal v).1)
    else opJunk true) = _
  rw [if_pos i.toNat_lt, UInt32.ofNat_toNat]
  rfl

/-- **A step under the platform is a step under the runner.** -/
theorem rstep_of_pstep {R : (𝕊).Runner} {S : Row} {cc cc' : Conf (platformOf R S)}
    (h : PStep (ℍ := ℍ) (platformOf R S) cc cc') :
    ∃ ev, (𝕊).RStep R ((cc.μ, cc.e), cc.s) ev ((cc'.μ, cc'.e), cc'.s) := by
  cases h with
  | mach hs =>
      obtain ⟨K, a, a', rfl, rfl, hh⟩ := hs
      exact ⟨_, .mach (OStep.mach hh)⟩
  | @plat μ s s' K n i v w o hK hf hco =>
      obtain ⟨-, l, rfl, ha⟩ := find_platformOf.1 hf
      rw [platformOf_co] at hco
      obtain ⟨l', w', hl', hR, hw', -⟩ := coOf_some hco
      have hll : l' = l := Subtype.ext hl'
      rw [hll] at hR
      have hst : (𝕊).RStep R ((μ, K.plug (performE (.val (opPayload l.1 i v)))), s)
          (.io l i.toNat (OVal.ofVal v) w') ((μ, K.plug w'.1), s') :=
        A.EffectSystem.RStep.io (S := 𝕊) (R := R)
          (c := (μ, K.plug (performE (.val (opPayload l.1 i v))))) (s := s) (s' := s') (K := K)
          (l := l) (i := i.toNat) (v := OVal.ofVal v) (w := w')
          (by show _ = K.plug ((𝕊).perform l i.toNat (OVal.ofVal v)); rw [perform_toNat]; rfl)
          hK ha hR
      rw [show K.plug w'.1 = K.plug (Expr.val w) by rw [hw']] at hst
      exact ⟨_, hst⟩

end Plat

end Targets.Inst

end

import Core.Chain.SI.Fin
import Core.Chain.SI.Adequacy

/-!
# The step-indexed relation at Core's types, for the fragment without borrows

`sV A n v σ` and `sC C n e σ`: Core's `𝒱⟦A⟧`/`𝒞⟦C⟧` (`Core/Relation.lean`, `vCE`/`cC`) with
`ewp` in place of `wpTS`/`ewpTS`/`cwp`, over exact fragments, at the step index `n`. A row is read
as a protocol (`sProt`) exactly as `cC` reads it as an operation table (`effTab`): each layer an
entry, the first match winning; a capturable operation's cancel obligation is the cancel run at
its cancel row's protocol (`finObl`); an abortive one is a raise whose payload is in `𝒱⟦A⟧`
owning nothing, its abandoned context owning nothing. A row that holds `Div` is read like any
other: `tick` is one entry, `1 ↠ Next`. There is no `cwp` and no `Closing`.

`⊸`, `∀`-free: the arrow reads its argument at every later index (the step-indexed `−∗`).

Not transcribed here: `Imm`, `Mut`, `[@a]`, `Unk`, type variables, `μ`, families, opaque host
types (each read as empty), and `∀'x`, `νX` (empty). These are the borrow model and the recursive
types.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  ubindE ccatchE kappaC errVal clauseAt capTag)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

theorem protNoneDown : Prot.none.Down where
  pa := fun _ _ _ h => by cases h
  canc := fun _ _ _ _ h => by cases h
  rais := fun _ _ _ h => by cases h

mutual
/-- `𝒱⟦A⟧` at the step index. -/
def sV : VTy → Nat → Val → Heap → Prop
  | .unit, _, v, σ => v = Val.unit ∧ σ = emp
  | .tensor A B, n, v, σ => ∃ v₁ v₂ σ₁ σ₂, v = Val.pair v₁ v₂ ∧ Disj σ₁ σ₂ ∧ σ = un σ₁ σ₂ ∧
      sV A n v₁ σ₁ ∧ sV B n v₂ σ₂
  | .zero, _, _, _ => False
  | .sum A B, n, v, σ => (∃ v₁, v = Val.inj₁ v₁ ∧ sV A n v₁ σ) ∨ (∃ v₂, v = Val.inj₂ v₂ ∧ sV B n v₂ σ)
  | .thunk C, n, v, σ => sC C n (forceE C v.1) σ
  | .ref A, n, v, σ => ∃ ℓ u σ', v = Val.loc ℓ ∧ σ' ℓ = none ∧ σ = un (single ℓ u) σ' ∧ sV A n u σ'
  | .bang A, n, v, σ => σ = emp ∧ sV A n v σ
  | .int w, _, v, σ => v.IsInt w ∧ σ = emp
  | _, _, _, _ => False
/-- `𝒞⟦C⟧` at the step index. -/
def sC : CTy → Nat → Expr → Heap → Prop
  | .ret A, n, e, σ => ewp (ℍ := ℍ) Prot.none (fun k v σ => sV A k v σ) n e σ
  | .arr A C, n, e, σ => ∀ k, k ≤ n → ∀ v σv, Disj σ σv → sV A k v σv →
      sC C k (.app e (.val v)) (un σ σv)
  | .amp C D, n, e, σ => sC C n (.app e (.val (Val.inj₁ .unit))) σ ∧
      sC D n (.app e (.val (Val.inj₂ .unit))) σ
  | .top, _, _, _ => True
  | .eff m i q A B fin rc C, n, e, σ =>
      ewp (ℍ := ℍ) (sProt (.eff m i q A B fin rc C)) (sRet (.eff m i q A B fin rc C)) n e σ
  | _, _, _, _ => False
/-- The protocol of a row's layers. -/
def sProt : CTy → Prot
  | .eff m i q A B fin _ C =>
      ⟨fun m' i' => if m' = m ∧ i' = i then
          (if B.isZero && q != .lin then none
           else some ⟨fun k v σ => sV A k v σ, fun k v σ => sV B k v σ,
             if capB q B then sFin fin else none⟩)
        else (sProt C).perf m' i',
       fun m' i' => if m' = m ∧ i' = i then
          (if B.isZero && q != .lin then some (fun k v σ => sV A k v σ ∧ σ = emp) else none)
        else (sProt C).rais m' i'⟩
  | _ => Prot.none
/-- The cancel obligation of a cancel row: `none` at `⊤`, else the cancel run at its operations. -/
def sFin : CTy → Option (Nat → Expr → Heap → Prop)
  | .top => none
  | .eff m i q A B fin rc C => some (cancelObl (ℍ := ℍ) (sProt (.eff m i q A B fin rc C)).perf)
  | _ => some (cancelObl (ℍ := ℍ) (fun _ _ => none))
/-- The answer relation of a row. -/
def sRet : CTy → Post
  | .ret A => fun k v σ => sV A k v σ
  | .eff _ _ _ _ _ _ _ C => sRet C
  | _ => fun _ _ _ => False
end

/-! ### Downward closure -/

theorem cancelProt_down_of {P : Prot} (hP : P.Down) : (cancelProt P.perf).Down where
  pa := hP.pa
  canc := hP.canc
  rais := fun m i R h n v σ hr => by
    simp only [cancelProt] at h
    split at h
    · cases h; exact hr
    · cases h

theorem cancelObl_down_of {P : Prot} (hP : P.Down) {n : Nat} {x : Expr} {σ : Heap}
    (h : cancelObl (ℍ := ℍ) P.perf (n + 1) x σ) : cancelObl (ℍ := ℍ) P.perf n x σ :=
  ewp_down (cancelProt_down_of hP) (fun _ _ _ h => h) n x σ h

mutual
theorem sV_down : ∀ (A : VTy) (n : Nat) (v : Val) (σ : Heap),
    sV (ℍ := ℍ) A (n + 1) v σ → sV (ℍ := ℍ) A n v σ
  | .unit, _, _, _, h => by simpa [sV] using h
  | .tensor A B, n, v, σ, h => by
      simp only [sV] at h ⊢
      obtain ⟨v₁, v₂, σ₁, σ₂, h₁, h₂, h₃, h₄, h₅⟩ := h
      exact ⟨v₁, v₂, σ₁, σ₂, h₁, h₂, h₃, sV_down A n v₁ σ₁ h₄, sV_down B n v₂ σ₂ h₅⟩
  | .zero, _, _, _, h => by simp [sV] at h
  | .sum A B, n, v, σ, h => by
      simp only [sV] at h ⊢
      rcases h with ⟨v₁, h₁, h₂⟩ | ⟨v₂, h₁, h₂⟩
      · exact .inl ⟨v₁, h₁, sV_down A n v₁ σ h₂⟩
      · exact .inr ⟨v₂, h₁, sV_down B n v₂ σ h₂⟩
  | .thunk C, n, v, σ, h => by
      simp only [sV] at h ⊢
      exact sC_down C n _ σ h
  | .ref A, n, v, σ, h => by
      simp only [sV] at h ⊢
      obtain ⟨ℓ, u, σ', h₁, h₂, h₃, h₄⟩ := h
      exact ⟨ℓ, u, σ', h₁, h₂, h₃, sV_down A n u σ' h₄⟩
  | .bang A, n, v, σ, h => by
      simp only [sV] at h ⊢
      exact ⟨h.1, sV_down A n v σ h.2⟩
  | .int _, _, _, _, h => by simpa [sV] using h
  | .imm _ _, _, _, _, h => by simp [sV] at h
  | .mut _ _, _, _, _, h => by simp [sV] at h
  | .box _ _, _, _, _, h => by simp [sV] at h
  | .unk, _, _, _, h => by simp [sV] at h
  | .tvar _, _, _, _, h => by simp [sV] at h
  | .mu _, _, _, _, h => by simp [sV] at h
  | .fam _, _, _, _, h => by simp [sV] at h
  | .opq _, _, _, _, h => by simp [sV] at h
theorem sC_down : ∀ (C : CTy) (n : Nat) (e : Expr) (σ : Heap),
    sC (ℍ := ℍ) C (n + 1) e σ → sC (ℍ := ℍ) C n e σ
  | .ret A, n, e, σ, h => by
      simp only [sC] at h ⊢
      exact ewp_down protNoneDown (fun k v σ h => sV_down A k v σ h) n e σ h
  | .arr A C, n, e, σ, h => by
      simp only [sC] at h ⊢
      exact fun k hk => h k (by omega)
  | .amp C D, n, e, σ, h => by
      simp only [sC] at h ⊢
      exact ⟨sC_down C n _ σ h.1, sC_down D n _ σ h.2⟩
  | .top, _, _, _, _ => by simp [sC]
  | .eff m i q A B fin rc C, n, e, σ, h => by
      simp only [sC] at h ⊢
      exact ewp_down (sProt_down (.eff m i q A B fin rc C)) (sRet_down (.eff m i q A B fin rc C)) n e σ h
  | .all _ _ _, _, _, _, h => by simp [sC] at h
  | .nu _, _, _, _, h => by simp [sC] at h
theorem sProt_down : ∀ C : CTy, (sProt (ℍ := ℍ) C).Down
  | .eff m i q A B fin rc C => by
      have hC := sProt_down C
      have hfin : ∀ F, sFin (ℍ := ℍ) fin = some F → ∀ n e σ, F (n + 1) e σ → F n e σ :=
        sFin_down fin
      refine ⟨fun m' i' s h n v σ hp => ?_, fun m' i' s F h hF n e σ hp => ?_,
        fun m' i' R h n v σ hp => ?_⟩
      · simp only [sProt] at h
        split at h
        · split at h
          · cases h
          · cases h; exact sV_down A n v σ hp
        · exact hC.pa _ _ _ h n v σ hp
      · simp only [sProt] at h
        split at h
        · split at h
          · cases h
          · cases h
            simp only at hF
            split at hF
            · exact hfin F hF n e σ hp
            · cases hF
        · exact hC.canc _ _ _ _ h hF n e σ hp
      · simp only [sProt] at h
        split at h
        · split at h
          · cases h; exact ⟨sV_down A n v σ hp.1, hp.2⟩
          · cases h
        · exact hC.rais _ _ _ h n v σ hp
  | .ret _ => by simp only [sProt]; exact protNoneDown
  | .arr _ _ => by simp only [sProt]; exact protNoneDown
  | .amp _ _ => by simp only [sProt]; exact protNoneDown
  | .top => by simp only [sProt]; exact protNoneDown
  | .all _ _ _ => by simp only [sProt]; exact protNoneDown
  | .nu _ => by simp only [sProt]; exact protNoneDown
theorem sFin_down : ∀ (F : CTy) (G : Nat → Expr → Heap → Prop), sFin (ℍ := ℍ) F = some G →
    ∀ n e σ, G (n + 1) e σ → G n e σ
  | .top, _, h => by simp [sFin] at h
  | .eff m i q A B fin rc C, G, h => by
      simp only [sFin, Option.some.injEq] at h
      subst h
      exact fun n e σ hp => cancelObl_down_of (sProt_down (.eff m i q A B fin rc C)) hp
  | .ret _, G, h => by
      simp only [sFin, Option.some.injEq] at h; subst h
      exact fun n e σ hp => cancelObl_down_of (P := Prot.none) protNoneDown hp
  | .arr _ _, G, h => by
      simp only [sFin, Option.some.injEq] at h; subst h
      exact fun n e σ hp => cancelObl_down_of (P := Prot.none) protNoneDown hp
  | .amp _ _, G, h => by
      simp only [sFin, Option.some.injEq] at h; subst h
      exact fun n e σ hp => cancelObl_down_of (P := Prot.none) protNoneDown hp
  | .all _ _ _, G, h => by
      simp only [sFin, Option.some.injEq] at h; subst h
      exact fun n e σ hp => cancelObl_down_of (P := Prot.none) protNoneDown hp
  | .nu _, G, h => by
      simp only [sFin, Option.some.injEq] at h; subst h
      exact fun n e σ hp => cancelObl_down_of (P := Prot.none) protNoneDown hp
theorem sRet_down : ∀ C : CTy, (sRet (ℍ := ℍ) C).Down
  | .ret A => fun n v σ h => by simp only [sRet] at h ⊢; exact sV_down A n v σ h
  | .eff _ _ _ _ _ _ _ C => by simp only [sRet]; exact sRet_down C
  | .arr _ _ => fun _ _ _ h => by simp [sRet] at h
  | .amp _ _ => fun _ _ _ h => by simp [sRet] at h
  | .top => fun _ _ _ h => by simp [sRet] at h
  | .all _ _ _ => fun _ _ _ h => by simp [sRet] at h
  | .nu _ => fun _ _ _ h => by simp [sRet] at h
end

theorem sV_le {A : VTy} {k n : Nat} (hkn : k ≤ n) {v : Val} {σ : Heap}
    (h : sV (ℍ := ℍ) A n v σ) : sV (ℍ := ℍ) A k v σ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  clear hkn
  induction d with
  | zero => exact h
  | succ d ihd => exact ihd (sV_down A _ v σ (by rwa [← Nat.add_assoc] at h))

theorem sFin_le {F : CTy} {G : Nat → Expr → Heap → Prop} (hG : sFin (ℍ := ℍ) F = some G)
    {k n : Nat} (hkn : k ≤ n) {e : Expr} {σ : Heap} (h : G n e σ) : G k e σ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  clear hkn
  induction d with
  | zero => exact h
  | succ d ihd => exact ihd (sFin_down F G hG _ e σ (by rwa [← Nat.add_assoc] at h))

/-! ### Rows -/

/-- `F_Σ R`'s relation is `ewp` at the row's protocol and `𝒱⟦R⟧`. -/
theorem sC_effOf (S : Row) (R : VTy) (k : Nat) (e : Expr) (σ : Heap) :
    sC (ℍ := ℍ) (CTy.effOf S R) k e σ ↔
      ewp (ℍ := ℍ) (sProt (ℍ := ℍ) (CTy.effOf S R)) (fun k v σ => sV (ℍ := ℍ) R k v σ) k e σ := by
  cases S with
  | nil => simp only [CTy.effOf, sC, sProt]
  | cons o S =>
      simp only [CTy.effOf, sC]
      have : sRet (ℍ := ℍ) (CTy.effOf S R) = fun k v σ => sV (ℍ := ℍ) R k v σ := by
        induction S with
        | nil => simp only [CTy.effOf, sRet]
        | cons o' S ih => simp only [CTy.effOf, sRet]; exact ih
      simp only [sRet, this]

/-- A row's protocol does not depend on the answer type under it. -/
theorem sProt_effOf_base (S : Row) (A R : VTy) :
    sProt (ℍ := ℍ) (CTy.effOf S A) = sProt (ℍ := ℍ) (CTy.effOf S R) := by
  induction S with
  | nil => simp only [CTy.effOf, sProt]
  | cons o S ih => simp only [CTy.effOf, sProt, ih]

/-- An entry of a row's protocol is one of its operations'. -/
theorem sProt_perf_mem {S : Row} {A : VTy} {m i : UInt32} {s : OpSpec}
    (h : (sProt (ℍ := ℍ) (CTy.effOf S A)).perf m i = some s) : ∃ o ∈ S, o.n = m := by
  induction S with
  | nil => simp [CTy.effOf, sProt, Prot.none] at h
  | cons o S ih =>
      simp only [CTy.effOf, sProt] at h
      split at h
      · rename_i hmi; exact ⟨o, by simp, hmi.1.symm⟩
      · obtain ⟨o', ho', h'⟩ := ih h; exact ⟨o', by simp [ho'], h'⟩

theorem sProt_rais_mem {S : Row} {A : VTy} {m i : UInt32} {R : Nat → Val → Heap → Prop}
    (h : (sProt (ℍ := ℍ) (CTy.effOf S A)).rais m i = some R) : ∃ o ∈ S, o.n = m := by
  induction S with
  | nil => simp [CTy.effOf, sProt, Prot.none] at h
  | cons o S ih =>
      simp only [CTy.effOf, sProt] at h
      split at h
      · rename_i hmi; exact ⟨o, by simp, hmi.1.symm⟩
      · obtain ⟨o', ho', h'⟩ := ih h; exact ⟨o', by simp [ho'], h'⟩

/-- Past an effect's own layers, another name's lookup is the rest's. -/
theorem ofEff_perf_ne {n m : UInt32} (hm : m ≠ n) (S : Row) (A : VTy) :
    ∀ (E : List (Qual × VTy × VTy)) (k : Nat) (fs : Nat → CTy) (cs : Nat → Bool) (i : UInt32),
      (sProt (ℍ := ℍ) (CTy.effOf (Row.ofEff n E k fs cs ++ S) A)).perf m i =
        (sProt (ℍ := ℍ) (CTy.effOf S A)).perf m i ∧
      (sProt (ℍ := ℍ) (CTy.effOf (Row.ofEff n E k fs cs ++ S) A)).rais m i =
        (sProt (ℍ := ℍ) (CTy.effOf S A)).rais m i
  | [], _, _, _, _ => by simp [Row.ofEff]
  | (q, B₁, B₂) :: E, k, fs, cs, i => by
      simp only [Row.ofEff, List.cons_append, CTy.effOf, sProt]
      rw [if_neg (fun h => hm h.1), if_neg (fun h => hm h.1)]
      exact ofEff_perf_ne hm S A E (k + 1) _ _ i

/-- The effect's own entries: the `j`-th operation, at index `k + j`. -/
theorem ofEff_perf_n {n : UInt32} {S : Row} (hS : ∀ o ∈ S, o.n ≠ n) (A : VTy) :
    ∀ (E : List (Qual × VTy × VTy)) (k : Nat) (fs : Nat → CTy) (cs : Nat → Bool) (i : UInt32)
      (s : OpSpec),
      (sProt (ℍ := ℍ) (CTy.effOf (Row.ofEff n E k fs cs ++ S) A)).perf n i = some s →
      ∃ j, ∃ hj : j < E.length, i = UInt32.ofNat (k + j) ∧
        (E[j].2.2.isZero && E[j].1 != .lin) = false ∧
        s = ⟨fun k v σ => sV (ℍ := ℍ) E[j].2.1 k v σ, fun k v σ => sV (ℍ := ℍ) E[j].2.2 k v σ,
          if capB E[j].1 E[j].2.2 then sFin (ℍ := ℍ) (fs j) else none⟩
  | [], _, _, _, i, s, h => by
      obtain ⟨o, ho, hon⟩ := sProt_perf_mem (by simpa [Row.ofEff] using h)
      exact absurd hon (hS o ho)
  | (q, B₁, B₂) :: E, k, fs, cs, i, s, h => by
      simp only [Row.ofEff, List.cons_append, CTy.effOf, sProt] at h
      split at h
      · rename_i hi
        split at h
        · cases h
        · rename_i hab
          cases h
          refine ⟨0, by simp, by simpa using hi.2, by simpa using hab, rfl⟩
      · obtain ⟨j, hj, hi, hab, rfl⟩ := ofEff_perf_n hS A E (k + 1) _ _ i s h
        refine ⟨j + 1, by simpa using hj, by rw [hi]; congr 1; omega, by simpa using hab, ?_⟩
        simp

/-- No raise of the effect's name, when none of its operations is abortive. -/
theorem ofEff_rais_n {n : UInt32} {S : Row} (hS : ∀ o ∈ S, o.n ≠ n) (A : VTy) :
    ∀ (E : List (Qual × VTy × VTy)) (k : Nat) (fs : Nat → CTy) (cs : Nat → Bool),
      (∀ o ∈ E, (o.2.2.isZero && o.1 != .lin) = false) → ∀ i,
      (sProt (ℍ := ℍ) (CTy.effOf (Row.ofEff n E k fs cs ++ S) A)).rais n i = none
  | [], _, _, _, _, i => by
      simp only [Row.ofEff, List.nil_append]
      cases h : (sProt (ℍ := ℍ) (CTy.effOf S A)).rais n i with
      | none => rfl
      | some R =>
          obtain ⟨o, ho, hon⟩ := sProt_rais_mem h
          exact absurd hon (hS o ho)
  | (q, B₁, B₂) :: E, k, fs, cs, hE, i => by
      simp only [Row.ofEff, List.cons_append, CTy.effOf, sProt]
      split
      · have := hE (q, B₁, B₂) (by simp)
        simp only at this
        rw [this]; rfl
      · exact ofEff_rais_n hS A E (k + 1) _ _ (fun o ho => hE o (by simp [ho])) i

/-- A cancel row's entries are entries of the row it puts ahead of `Σ`. -/
theorem sProt_rowOf_perf (S : Row) (R : VTy) : ∀ (F : CTy) (m i : UInt32) (s : OpSpec),
    (sProt (ℍ := ℍ) F).perf m i = some s →
      (sProt (ℍ := ℍ) (CTy.effOf (F.rowOf ++ S) R)).perf m i = some s
  | .eff m₀ i₀ q A B fin rc C, m, i, s, h => by
      simp only [CTy.rowOf, List.cons_append, CTy.effOf, sProt] at h ⊢
      by_cases hmi : m = m₀ ∧ i = i₀
      · rw [if_pos hmi] at h ⊢; exact h
      · rw [if_neg hmi] at h ⊢; exact sProt_rowOf_perf S R C m i s h
  | .ret _, _, _, _, h => by simp [sProt, Prot.none] at h
  | .arr _ _, _, _, _, h => by simp [sProt, Prot.none] at h
  | .amp _ _, _, _, _, h => by simp [sProt, Prot.none] at h
  | .top, _, _, _, h => by simp [sProt, Prot.none] at h
  | .all _ _ _, _, _, _, h => by simp [sProt, Prot.none] at h
  | .nu _, _, _, _, h => by simp [sProt, Prot.none] at h

/-- The cancel obligation of a cancel row that is not `⊤` is a cancel run at some operations,
each an entry of the row it puts ahead of `Σ`. -/
theorem sFin_cases {F : CTy} {G : Nat → Expr → Heap → Prop} (hG : sFin (ℍ := ℍ) F = some G)
    (S : Row) (R : VTy) : ∃ Pc : UInt32 → UInt32 → Option OpSpec,
      G = cancelObl (ℍ := ℍ) Pc ∧
      ∀ m i s, Pc m i = some s → (sProt (ℍ := ℍ) (CTy.effOf (F.rowOf ++ S) R)).perf m i = some s := by
  cases F with
  | eff m i q A B fin rc C =>
      simp only [sFin, Option.some.injEq] at hG
      exact ⟨_, hG.symm, sProt_rowOf_perf S R _⟩
  | top => simp [sFin] at hG
  | _ =>
      simp only [sFin, Option.some.injEq] at hG
      exact ⟨fun _ _ => none, hG.symm, fun _ _ _ h => by cases h⟩

/-! ### `κ` -/

/-- `κ` as a value. -/
def kapVal (hc : Bool) (ℓ : Loc) (H : Val) (K : Kont) : Val := ⟨kappaC hc ℓ H K, IsVal.lam⟩

/-- **`κ` is in `𝒱⟦kTy⟧`**: owning its cell and the continuation's resources, resumed at every
answer in `𝒱⟦B⟧` it is `hnd H K[w]`'s `ewp`, and, at a cancellable operation whose cancel row is
not `⊤`, cancelled it runs the cancelled region at the row's obligation. -/
theorem kap_sem {S : Row} {R : VTy} {q : Qual} {B : VTy} {F : CTy} {H : Val} {k : Nat} {K : Kont}
    {σk : Heap} {ℓ : Loc} (hq : q ≠ .unr) (hℓ : σk ℓ = none)
    (hres : ∀ j, j ≤ k → ∀ w σw, Disj σk σw → sV (ℍ := ℍ) B j w σw →
      ewp (ℍ := ℍ) (sProt (ℍ := ℍ) (CTy.effOf S R)) (fun k v σ => sV (ℍ := ℍ) R k v σ) j
        (hndE H (K.plug (.val w))) (un σk σw))
    (hcan : q = .cancel → ∀ G, sFin (ℍ := ℍ) F = some G →
      G k (K.dead.plug (raiseE (.val (cancelVal none)))) σk) :
    sV (ℍ := ℍ) (kTy S R q B F) k (kapVal (cellCancel q) ℓ H K) (un (single ℓ Val.unit) σk) := by
  have hP := sProt_down (ℍ := ℍ) (CTy.effOf S R)
  have hQ : Post.Down (fun k v σ => sV (ℍ := ℍ) R k v σ) := fun n v σ h => sV_down R n v σ h
  have key : ∀ j, j ≤ k → ∀ w σw, Disj (un (single ℓ Val.unit) σk) σw → sV (ℍ := ℍ) B j w σw →
      sC (ℍ := ℍ) (CTy.effOf S R) j
        (.app (.app (kappaC (cellCancel q) ℓ H K) (.val (Val.inj₁ .unit))) (.val w))
        (un (un (single ℓ Val.unit) σk) σw) := by
    intro j hj w σw hd hw
    rw [sC_effOf]
    obtain ⟨hdℓ, hdk⟩ := disj_un_left.1 hd
    have h₀ := hres (j - 6) (by omega) w σw hdk (sV_le (by omega) hw)
    have hℓ' : un σk σw ℓ = none := un_eq_none.2 ⟨hℓ, single_disj.1 hdℓ⟩
    rw [un_assoc]
    exact ewp_le hP hQ (by omega) (ewp_resume hℓ' h₀)
  cases q with
  | lin =>
      simp only [kTy, sV, forceE, sC]
      exact ⟨fun j hj w σw hd hw => key j hj w σw hd hw, trivial⟩
  | cancel =>
      simp only [kTy, sV, forceE, sC]
      refine ⟨fun j hj w σw hd hw => key j hj w σw hd hw, ?_⟩
      unfold cancelTy
      split
      · simp [sC]
      · rename_i hF
        rw [sC_effOf]
        have hG : ∃ G, sFin (ℍ := ℍ) F = some G := by
          cases F <;> simp_all [sFin, CTy.isTop]
        obtain ⟨G, hG⟩ := hG
        obtain ⟨Pc, rfl, hPc⟩ := sFin_cases hG S .unit
        have hc := sFin_le hG (k := k - 5) (by omega) (hcan rfl _ hG)
        have h₀ := ewp_ccatch (ℍ := ℍ) (Q' := fun k v σ => sV (ℍ := ℍ) .unit k v σ) hPc
          (fun _ => by simp [sV]) (k - 5) _ σk hc
        exact ewp_le (sProt_down _) (fun n v σ h => sV_down _ n v σ h) (by omega)
          (ewp_cancelK hℓ h₀)
  | unr => exact absurd rfl hq

/-! ### The handler rule at types, with no `hdv` -/

theorem un_eq_emp {a b : Heap} (h : un a b = emp) : a = emp ∧ b = emp := by
  constructor <;> funext ℓ <;> have := congrFun h ℓ <;> simp only [un, emp] at this ⊢ <;>
    split at this <;> simp_all

/-- The clauses' tuple, in `𝒱⟦clausesTy⟧`: the `j`-th clause is in `𝒱⟦clauseTy⟧`. -/
theorem clauses_sem (S : Row) (R : VTy) : ∀ (E : List (Qual × VTy × VTy)) (fs : Nat → CTy)
    (hs : Val) (k : Nat), sV (ℍ := ℍ) (clausesTy S R E fs) k hs emp →
      ∀ j (hj : j < E.length), ∃ c, clauseAt hs.1 j = some c ∧
        sV (ℍ := ℍ) (clauseTy S R E[j] (fs j)) k c emp
  | [], _, _, _, _, j, hj => absurd hj (by simp)
  | o :: E, fs, hs, k, h, j, hj => by
      simp only [clausesTy, sV] at h
      obtain ⟨c, r, σ₁, σ₂, rfl, -, he, hc, hr⟩ := h
      obtain ⟨rfl, rfl⟩ := un_eq_emp he.symm
      cases j with
      | zero => exact ⟨c, by simp [clauseAt, Val.pair, c.2], hc⟩
      | succ j =>
          obtain ⟨c', hc', h'⟩ := clauses_sem S R E (fun j => fs (j + 1)) r k hr j
            (by simpa using hj)
          exact ⟨c', by simpa [clauseAt, Val.pair] using hc', by simpa using h'⟩

/-- **`[handle]` at the step-indexed relation, with no `hdv`**: the handled row may hold `Div`.
The handler's operations are must-resume or cancellable (no abortive clause, no unrestricted
`κ`); every other premise is `effHandleV`'s. -/
theorem handle_sem {n : UInt32} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy} {cs : Nat → Bool}
    {S : Row} {A R : VTy} {hr hs : Val}
    (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hE : ∀ o ∈ E, o.1 ≠ .unr ∧ (o.2.2.isZero && o.1 != .lin) = false)
    (hhr : ∀ k, sV (ℍ := ℍ) (retTy S A R) k hr emp)
    (hhs : ∀ k, sV (ℍ := ℍ) (clausesTy S R E fs) k hs emp) :
    ∀ k e σ, sC (ℍ := ℍ) (CTy.effOf (Row.ofEff n E 0 fs cs ++ S) A) k e σ →
      sC (ℍ := ℍ) (CTy.effOf S R) k (hndE (hndVal n (qualsVal (E.map Prod.fst)) hr hs) e) σ := by
  intro k e σ h
  rw [sC_effOf] at h ⊢
  have hEab : ∀ o ∈ E, (o.2.2.isZero && o.1 != .lin) = false := fun o ho => (hE o ho).2
  refine ewp_handle ?_ (sProt_down _) k e σ h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k v σ hq
    have := hhr (k + 1)
    simp only [retTy, sV, forceE, sC] at this
    have h' := this.2 k (by omega) v σ (disj_emp_left σ) (sV_down A k v σ hq)
    rw [sC_effOf, un_emp_left] at h'
    exact h'
  · intro m i s hm h
    rw [(ofEff_perf_ne hm S A E 0 fs cs i).1, sProt_effOf_base S A R] at h
    exact h
  · intro m i R' h
    have hm : m ≠ n := by
      rintro rfl
      rw [ofEff_rais_n hnS A E 0 fs cs hEab i] at h
      cases h
    rw [(ofEff_perf_ne hm S A E 0 fs cs i).2, sProt_effOf_base S A R] at h
    exact ⟨hm, R', h, fun _ _ _ h => h⟩
  · intro i s h
    obtain ⟨j, hj, hi, hab, rfl⟩ := ofEff_perf_n hnS A E 0 fs cs i s h
    have hjn : i.toNat = j := by
      subst hi
      simp only [Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨c, hc, -⟩ := clauses_sem S R E fs hs 0 (hhs 0) j hj
    refine ⟨c, E[j].1, by rw [hjn]; exact hc, ?_, (hE _ (List.getElem_mem hj)).1, ?_⟩
    · rw [hjn]
      have := capTag_qualsVal (E.map Prod.fst) j (by simpa using hj)
      simpa using this
    · intro k v σa ℓ K σk hd hℓ hA hK
      obtain ⟨c', hc', hcs⟩ := clauses_sem S R E fs hs k (hhs k) j hj
      rw [hc] at hc'
      cases hc'
      rw [show E[j] = (E[j].1, E[j].2.1, E[j].2.2) from rfl] at hcs
      simp only [clauseTy, hab, Bool.false_eq_true, if_false, sV, forceE, sC] at hcs
      have hq : E[j].1 ≠ .unr := (hE _ (List.getElem_mem hj)).1
      have hκ := kap_sem (S := S) (R := R) (q := E[j].1) (B := E[j].2.2) (F := fs j)
        (H := hndVal n (qualsVal (E.map Prod.fst)) hr hs) (k := k) (K := K) (σk := σk) (ℓ := ℓ)
        hq hℓ (fun j' hj' w σw hdw hw => hK.1 j' hj' w σw hdw hw) ?_
      · have hres := hcs.2 k le_rfl (Val.pair v (kapVal (cellCancel E[j].1) ℓ
          (hndVal n (qualsVal (E.map Prod.fst)) hr hs) K)) (un σa (un (single ℓ Val.unit) σk))
          (disj_emp_left _) ⟨v, _, σa, un (single ℓ Val.unit) σk, rfl, hd, rfl, hA, hκ⟩
        rw [sC_effOf, un_emp_left] at hres
        exact hres
      · intro hc G hG
        refine hK.2 G ?_
        have hB : E[j].2.2.isZero = false := by
          revert hab; rw [hc]; cases E[j].2.2.isZero <;> simp
        simp [capB, hB, hG, hc]

end BoCa.Fig16.LogRel.Core.Chain.SI

end

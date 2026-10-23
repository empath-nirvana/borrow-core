import Rewrite.OblTail

/-!
# Rewrite — R0's translation and a type's obligations  `[spec §12, §54]`

R0's type translation (`trV`, `Rewrite/Types.lean`) keeps every obligation whose source is not an
operation of its name (`Rewrite/Obl.lean`): `o ∈ obl A`, `¬ o.of n` give `o ∈ obl (trV a A)`
(`obl_trV`), at a type whose rows are returner chains over `F` (`rowsV`). The converse does not
hold: R0 answers a computation at a row holding `n` with a sum `A ⊕ P_n`, so a thunk's finish
`F_{n} 1` becomes `F (1 ⊕ P_n)`, which has no destructor (a `cell`), and a payload adds its own.
R0 adds obligations and discharges only its name's.
-/

namespace Rewrite
open BoCa.Fig16.LogRel.Core (VTy CTy OpSig Row Count FShape toFShape isX0)

section
variable (a : AbortName)

/-- The obligation's source is not an operation of `n`. -/
abbrev kept (o : Ob) : Prop := o.of a.n = false

theorem clB_trV : ∀ (k : Nat) (A : VTy),
    BoCa.Fig16.LogRel.Core.Check.VTy.clB k (trV a A) = BoCa.Fig16.LogRel.Core.Check.VTy.clB k A
  | k, .tensor A B | k, .sum A B => by
      simp only [trV, BoCa.Fig16.LogRel.Core.Check.VTy.clB, clB_trV k A, clB_trV k B]
  | k, .ref A | k, .imm _ A | k, .mut _ A | k, .box _ A | k, .bang A | k, .fam A => by
      simp only [trV, BoCa.Fig16.LogRel.Core.Check.VTy.clB, clB_trV k A]
  | k, .mu A => by simp only [trV, BoCa.Fig16.LogRel.Core.Check.VTy.clB, clB_trV (k + 1) A]
  | _, .thunk _ | _, .unit | _, .zero | _, .unk | _, .tvar _ | _, .int _ | _, .opq _ => rfl

theorem occB_trV : ∀ (k : Nat) (A : VTy),
    BoCa.Fig16.LogRel.Core.Check.VTy.occB k (trV a A) = BoCa.Fig16.LogRel.Core.Check.VTy.occB k A
  | k, .tensor A B | k, .sum A B => by
      simp only [trV, BoCa.Fig16.LogRel.Core.Check.VTy.occB, occB_trV k A, occB_trV k B]
  | k, .ref A | k, .imm _ A | k, .mut _ A | k, .box _ A | k, .bang A | k, .fam A => by
      simp only [trV, BoCa.Fig16.LogRel.Core.Check.VTy.occB, occB_trV k A]
  | k, .mu A => by simp only [trV, BoCa.Fig16.LogRel.Core.Check.VTy.occB, occB_trV (k + 1) A]
  | _, .thunk _ | _, .unit | _, .zero | _, .unk | _, .tvar _ | _, .int _ | _, .opq _ => rfl

theorem polyB_trV : ∀ A : VTy,
    BoCa.Fig16.LogRel.Core.Check.VTy.polyB (trV a A) = BoCa.Fig16.LogRel.Core.Check.VTy.polyB A
  | .tensor A B | .sum A B => by
      simp only [trV, BoCa.Fig16.LogRel.Core.Check.VTy.polyB, polyB_trV A, polyB_trV B]
  | .box _ A => by simp only [trV, BoCa.Fig16.LogRel.Core.Check.VTy.polyB, polyB_trV A]
  | .tvar _ => rfl
  | .ref A | .imm _ A | .mut _ A | .bang A | .fam A | .mu A => by
      simp only [trV, BoCa.Fig16.LogRel.Core.Check.VTy.polyB, BoCa.Fig16.LogRel.Core.Check.VTy.occB,
        occB_trV a]
  | .thunk _ | .unit | .zero | .unk | .int _ | .opq _ => rfl

theorem isX0_trV (A : VTy) : isX0 (trV a A) = isX0 A := by
  cases A with
  | tvar k => cases k <;> rfl
  | _ => rfl

theorem shape_trV : ∀ A : VTy,
    Frontend.Check.FShape.wfB (toFShape (trV a A)) = Frontend.Check.FShape.wfB (toFShape A) ∧
    Frontend.Check.FShape.guardedB (toFShape (trV a A)) = Frontend.Check.FShape.guardedB (toFShape A)
  | .tensor A B | .sum A B => by
      simp only [trV, toFShape, Frontend.Check.FShape.wfB, Frontend.Check.FShape.guardedB,
        (shape_trV A).1, (shape_trV B).1, and_self]
  | .tvar k => by cases k <;> exact ⟨rfl, rfl⟩
  | .ref B => by
      cases B with
      | tvar k => cases k <;> exact ⟨rfl, rfl⟩
      | _ => exact ⟨by simp only [trV, toFShape, Frontend.Check.FShape.wfB,
          BoCa.Fig16.LogRel.Core.Check.VTy.clB, clB_trV a], rfl⟩
  | .imm _ _ | .mut _ _ | .box _ _ | .bang _ | .fam _ | .mu _ | .thunk _ | .unit | .zero | .unk
  | .int _ | .opq _ => ⟨by simp only [trV, toFShape, Frontend.Check.FShape.wfB,
      BoCa.Fig16.LogRel.Core.Check.VTy.clB, clB_trV a], rfl⟩

theorem trV_unit (R : VTy) : trV a R = .unit ↔ R = .unit := by
  cases R <;> simp [trV]

/-- Whether R0 answers a chain with a sum: its first layer's. -/
def hasOf : CTy → Bool
  | .eff m _ _ _ _ _ _ C => m == a.n || chainHas a.n C
  | _ => false

/-- R0's translation of a computation type is its chain translation at `hasOf`. -/
theorem trC_eq : ∀ C : CTy, trC a C = trChain a (hasOf a C) C
  | .eff m i c w A B fin C => by simp only [trC, trChain, hasOf]
  | .ret R => by simp [trC, trChain, hasOf]
  | .arr _ _ | .amp _ _ | .top | .all _ _ _ | .nu _ => by simp [trC, trChain, hasOf]

theorem endsRet_trChain : ∀ (has : Bool) (C : CTy), endsRet C = true → endsRet (trChain a has C) = true
  | has, .eff m i c w A B fin C, h => by
      simp only [endsRet] at h
      simp only [trChain]; split <;> (try simp only [endsRet]) <;> exact endsRet_trChain has C h
  | _, .ret _, _ => rfl
  | _, .arr _ _, h | _, .amp _ _, h | _, .top, h | _, .all _ _ _, h | _, .nu _, h => by
      simp [endsRet] at h

theorem effObl_trChain : ∀ (has : Bool) (C : CTy) (o : Ob), o ∈ effObl C → kept a o →
    o ∈ effObl (trChain a has C)
  | has, .eff m i c w A B fin C, o, ho, hk => by
      simp only [effObl, List.mem_append] at ho
      simp only [trChain]
      by_cases hm : (m == a.n) = true
      · simp only [hm, if_true]
        rcases ho with ho | ho
        · split at ho <;> simp_all [kept, Ob.of]
        · exact effObl_trChain has C o ho hk
      · simp only [hm, Bool.false_eq_true, if_false, effObl, List.mem_append, clB_trV a]
        rcases ho with ho | ho
        · exact .inl ho
        · exact .inr (effObl_trChain has C o ho hk)
  | has, .ret R, o, ho, _ => by
      simp only [effObl] at ho
      simp only [trChain, effObl]
      split at ho
      · simp at ho
      · rename_i hp
        split
        · simp_all [BoCa.Fig16.LogRel.Core.Check.VTy.polyB, polyB_trV a]
        · simp_all [polyB_trV a]
  | _, .arr _ _, _, ho, _ | _, .amp _ _, _, ho, _ | _, .top, _, ho, _ | _, .all _ _ _, _, ho, _
  | _, .nu _, _, ho, _ => by simpa [trChain, effObl] using ho

theorem leafObl_trC : ∀ (C : CTy), rowsC C = true → ∀ o, o ∈ leafObl C → kept a o →
    o ∈ leafObl (trC a C)
  | .eff m i c w A B fin C, h, o, ho, hk => by
      simp only [rowsC, Bool.and_eq_true] at h
      simp only [leafObl, List.mem_append] at ho
      simp only [trC]
      by_cases hm : (m == a.n) = true
      · simp only [hm, if_true]
        rw [leafObl_chain _ (endsRet_trChain a _ C h.1.2)]
        rcases ho with ho | ho
        · split at ho <;> simp_all [kept, Ob.of]
        · exact effObl_trChain a _ C o ho hk
      · simp only [hm, Bool.false_eq_true, if_false, leafObl, List.mem_append, clB_trV a]
        rcases ho with ho | ho
        · exact .inl ho
        · exact .inr (effObl_trChain a _ C o ho hk)
  | .ret R, _, o, ho, _ => by simpa [trC, leafObl, polyB_trV a] using ho
  | .amp C D, h, o, ho, hk => by
      simp only [rowsC, Bool.and_eq_true] at h
      simp only [leafObl, List.mem_append] at ho
      simp only [trC, leafObl, List.mem_append]
      rcases ho with ho | ho
      · exact .inl (leafObl_trC C h.1 o ho hk)
      · exact .inr (leafObl_trC D h.2 o ho hk)
  | .arr A D, h, o, ho, hk => by
      simp only [rowsC, Bool.and_eq_true] at h
      simp only [leafObl, List.mem_append] at ho
      simp only [trC, leafObl, List.mem_append, clB_trV a]
      rcases ho with ho | ho
      · exact .inl ho
      · exact .inr (leafObl_trC D h.2 o ho hk)
  | .top, _, o, ho, _ | .all _ _ _, _, o, ho, _ | .nu _, _, o, ho, _ => by simpa [trC, leafObl] using ho

theorem ampFin_trChain : ∀ (has : Bool) (D : CTy) (o : Ob), o ∈ ampFin D → kept a o →
    o ∈ ampFin (trChain a has D)
  | has, .eff m i c w A B fin D, o, ho, hk => by
      simp only [ampFin, List.mem_cons] at ho
      simp only [trChain]
      by_cases hm : (m == a.n) = true
      · simp only [hm, if_true]
        rcases ho with ho | ho
        · subst ho; simp_all [kept, Ob.of]
        · exact ampFin_trChain has D o ho hk
      · simp only [hm, Bool.false_eq_true, if_false, ampFin, List.mem_cons]
        rcases ho with ho | ho
        · exact .inl ho
        · exact .inr (ampFin_trChain has D o ho hk)
  | has, .ret R, o, ho, _ => by
      have hc : ∀ X : VTy, X ≠ .unit → ampFin (.ret X) = [.cell "a thunk"] := by
        intro X hX; cases X <;> simp_all [ampFin]
      by_cases hu : R = .unit
      · subst hu; simp [ampFin] at ho
      · rw [hc R hu] at ho
        simp only [trChain]
        split
        · rw [hc _ (by simp)]; exact ho
        · rw [hc _ (fun h => hu ((trV_unit a R).mp h))]; exact ho
  | _, .arr _ _, _, ho, _ | _, .amp _ _, _, ho, _ | _, .top, _, ho, _ | _, .all _ _ _, _, ho, _
  | _, .nu _, _, ho, _ => by simpa [trChain, ampFin] using ho

mutual
/-- **R0's translation keeps every obligation that is not its name's** (at a type whose rows are
returner chains over `F`). -/
theorem obl_trV : ∀ (alg : Bool) (A : VTy), rowsV A = true → ∀ o, o ∈ obl alg A → kept a o →
    o ∈ obl alg (trV a A)
  | alg, .tensor A B, h, o, ho, hk | alg, .sum A B, h, o, ho, hk => by
      simp only [rowsV, Bool.and_eq_true] at h
      simp only [obl, List.mem_append] at ho
      simp only [trV, obl, List.mem_append]
      rcases ho with ho | ho
      · exact .inl (obl_trV alg A h.1 o ho hk)
      · exact .inr (obl_trV alg B h.2 o ho hk)
  | alg, .ref A, h, o, ho, hk => by
      simp only [rowsV] at h
      simp only [obl] at ho
      simp only [trV, obl, isX0_trV a]
      split at ho
      · simp at ho
      · rename_i hx; simp only [hx, if_false]; exact obl_trV false A h o ho hk
  | alg, .tvar 0, _, o, ho, _ => by simpa [trV, obl] using ho
  | _, .tvar (_ + 1), _, o, ho, _ => by simpa [trV, obl] using ho
  | _, .box _ A, h, o, ho, hk => by
      simp only [rowsV] at h; simp only [obl] at ho; simp only [trV, obl]
      exact obl_trV false A h o ho hk
  | _, .mu A, h, o, ho, hk => by
      simp only [rowsV] at h
      simp only [obl, List.mem_append] at ho
      simp only [trV, obl, List.mem_append, (shape_trV a A).1, (shape_trV a A).2]
      rcases ho with ho | ho
      · exact .inl ho
      · exact .inr (obl_trV true A h o ho hk)
  | _, .thunk C, h, o, ho, hk => by
      simp only [rowsV] at h
      simp only [obl] at ho
      simp only [trV, obl, trC_eq a C]
      exact thunkObl_trChain (hasOf a C) C h o ho hk
  | _, .unit, _, o, ho, _ | _, .zero, _, o, ho, _ | _, .int _, _, o, ho, _ | _, .unk, _, o, ho, _
  | _, .bang _, _, o, ho, _ | _, .imm _ _, _, o, ho, _ | _, .mut _ _, _, o, ho, _ => by
      simp [obl] at ho
  | _, .fam (.ref A), h, o, ho, hk => by
      simp only [rowsV] at h; simp only [obl] at ho; simp only [trV, obl]
      exact obl_trV false A h o ho hk
  | _, .fam (.imm _ _), _, o, ho, _ | _, .fam (.mut _ _), _, o, ho, _ => by simp [obl] at ho
  | _, .fam (.unit), _, o, ho, _ | _, .fam (.tensor _ _), _, o, ho, _ | _, .fam .zero, _, o, ho, _
  | _, .fam (.sum _ _), _, o, ho, _ | _, .fam (.thunk _), _, o, ho, _ | _, .fam (.box _ _), _, o, ho, _
  | _, .fam (.bang _), _, o, ho, _ | _, .fam .unk, _, o, ho, _ | _, .fam (.tvar _), _, o, ho, _
  | _, .fam (.mu _), _, o, ho, _ | _, .fam (.int _), _, o, ho, _ | _, .fam (.opq _), _, o, ho, _
  | _, .fam (.fam _), _, o, ho, _ => by simpa [trV, obl] using ho
  | _, .opq _, _, o, ho, _ => by simpa [trV, obl] using ho
/-- A thunk's obligations under R0's chain translation. -/
theorem thunkObl_trChain : ∀ (has : Bool) (C : CTy), rowsC C = true → ∀ o, o ∈ thunkObl C →
    kept a o → o ∈ thunkObl (trChain a has C)
  | has, .eff m i c w A B fin C, h, o, ho, hk => by
      simp only [rowsC, Bool.and_eq_true] at h
      simp only [thunkObl, List.mem_cons] at ho
      simp only [trChain]
      by_cases hm : (m == a.n) = true
      · simp only [hm, if_true]
        rcases ho with ho | ho
        · subst ho; simp_all [kept, Ob.of]
        · exact thunkObl_trChain has C h.2 o ho hk
      · simp only [hm, Bool.false_eq_true, if_false, thunkObl, List.mem_cons]
        rcases ho with ho | ho
        · exact .inl ho
        · exact .inr (thunkObl_trChain has C h.2 o ho hk)
  | _, .amp X D, _, o, ho, hk => by
      simp only [thunkObl] at ho
      simp only [trChain, thunkObl, trC_eq a D]
      exact ampFin_trChain a _ D o ho hk
  | _, .nu (.amp X D), h, o, ho, hk => by
      simp only [rowsC, Bool.and_eq_true] at h
      simp only [thunkObl] at ho
      simp only [trChain, trC, thunkObl, trC_eq a D]
      exact nuFin_trChain (hasOf a D) (leafObl X) (leafObl (trC a X)) D
        (fun o ho hk => leafObl_trC a X h.1 o ho hk) h.2 o ho hk
  | _, .nu (.eff m i c w A B fin C), h, o, ho, _ => by
      simp only [rowsC, Bool.and_eq_true] at h
      have he : endsRet (trC a (.eff m i c w A B fin C)) = true := by
        rw [trC_eq a]; exact endsRet_trChain a _ _ (by simp only [endsRet]; exact h.1.2)
      rw [show trChain a _ (.nu (.eff m i c w A B fin C)) = .nu (trC a (.eff m i c w A B fin C))
        from rfl, thunkObl_nu_ret _ he]
      simpa [thunkObl] using ho
  | _, .ret _, _, o, ho, _ | _, .arr _ _, _, o, ho, _ | _, .top, _, o, ho, _
  | _, .all _ _ _, _, o, ho, _ => by simpa [trChain, thunkObl] using ho
  | _, .nu (.ret _), _, o, ho, _ | _, .nu (.arr _ _), _, o, ho, _ | _, .nu .top, _, o, ho, _
  | _, .nu (.all _ _ _), _, o, ho, _ | _, .nu (.nu _), _, o, ho, _ => by
      simpa [trChain, trC, thunkObl] using ho
/-- A codata thunk's finish under R0's chain translation, its observations' obligations kept. -/
theorem nuFin_trChain : ∀ (has : Bool) (lc lc' : List Ob) (D : CTy),
    (∀ o, o ∈ lc → kept a o → o ∈ lc') → rowsC D = true → ∀ o, o ∈ nuFin lc D → kept a o →
    o ∈ nuFin lc' (trChain a has D)
  | has, lc, lc', .eff m i c w A B fin D, hl, h, o, ho, hk => by
      simp only [rowsC, Bool.and_eq_true] at h
      simp only [nuFin, List.mem_cons] at ho
      simp only [trChain]
      by_cases hm : (m == a.n) = true
      · simp only [hm, if_true]
        rcases ho with ho | ho
        · subst ho; simp_all [kept, Ob.of]
        · exact nuFin_trChain has lc lc' D hl h.2 o ho hk
      · simp only [hm, Bool.false_eq_true, if_false, nuFin, List.mem_cons]
        rcases ho with ho | ho
        · exact .inl ho
        · exact .inr (nuFin_trChain has lc lc' D hl h.2 o ho hk)
  | has, lc, lc', .ret R, hl, h, o, ho, hk => by
      simp only [rowsC] at h
      simp only [nuFin, List.mem_append] at ho
      have hR : o ∈ obl false R → o ∈ obl false (trV a R) := fun ho => obl_trV false R h o ho hk
      cases has <;> simp only [trChain, Bool.false_eq_true, if_false, if_true, nuFin,
        List.mem_append]
      all_goals
        rcases ho with (ho | ho) | ho
        · exact .inl (.inl (hl o ho hk))
        · refine .inl (.inr ?_)
          by_cases hp : (BoCa.Fig16.LogRel.Core.Check.VTy.polyB R && BoCa.Fig16.LogRel.Core.Check.VTy.clB 0 R) = true
          · simp [hp] at ho
          · rw [if_neg hp] at ho
            rw [if_neg (by simp_all [BoCa.Fig16.LogRel.Core.Check.VTy.polyB, BoCa.Fig16.LogRel.Core.Check.VTy.clB, polyB_trV a, clB_trV a])]
            exact ho
        · refine .inr ?_
          first
            | exact hR ho
            | (simp only [obl, List.mem_append]; exact .inl (hR ho))
  | _, _, _, .arr _ _, _, _, o, ho, _ | _, _, _, .amp _ _, _, _, o, ho, _
  | _, _, _, .top, _, _, o, ho, _ | _, _, _, .all _ _ _, _, _, o, ho, _
  | _, _, _, .nu _, _, _, o, ho, _ => by simpa [trChain, nuFin] using ho
end

end


/-! ### Rows over `F` are kept, and the rules compose -/

section
variable (a : TailName)

mutual
theorem rowsV_tV (hSN : a.SN = []) : ∀ A : VTy, rowsV A = true → rowsV (tV a A) = true
  | .tensor A B, h | .sum A B, h => by
      simp only [rowsV, Bool.and_eq_true] at h
      simp only [tV, rowsV, Bool.and_eq_true]; exact ⟨rowsV_tV hSN A h.1, rowsV_tV hSN B h.2⟩
  | .thunk C, h => by simp only [rowsV] at h; simp only [tV, rowsV]; exact rowsC_tC hSN C h
  | .ref A, h | .imm _ A, h | .mut _ A, h | .box _ A, h | .bang A, h | .mu A, h | .fam A, h => by
      simp only [rowsV] at h; simp only [tV, rowsV]; exact rowsV_tV hSN A h
  | .unit, _ | .zero, _ | .unk, _ | .tvar _, _ | .int _, _ | .opq _, _ => rfl
theorem rowsC_tC (hSN : a.SN = []) : ∀ C : CTy, rowsC C = true → rowsC (tC a C) = true
  | .ret A, h => by simp only [rowsC] at h; simp only [tC, rowsC]; exact rowsV_tV hSN A h
  | .arr A C, h => by
      simp only [rowsC, Bool.and_eq_true] at h
      simp only [tC, rowsC, Bool.and_eq_true]; exact ⟨rowsV_tV hSN A h.1, rowsC_tC hSN C h.2⟩
  | .amp C D, h => by
      simp only [rowsC, Bool.and_eq_true] at h
      simp only [tC, rowsC, Bool.and_eq_true]; exact ⟨rowsC_tC hSN C h.1, rowsC_tC hSN D h.2⟩
  | .top, _ => rfl
  | .all _ _ C, h | .nu C, h => by simp only [rowsC] at h; simp only [tC, rowsC]; exact rowsC_tC hSN C h
  | .eff m i c w A B fin C, h => by
      simp only [rowsC, Bool.and_eq_true] at h
      rw [tC_eff a hSN]
      split
      · exact rowsC_tC hSN C h.2
      · simp only [rowsC, Bool.and_eq_true]
        exact ⟨⟨⟨⟨rowsV_tV hSN A h.1.1.1.1, rowsV_tV hSN B h.1.1.1.2⟩, rowsC_tC hSN fin h.1.1.2⟩,
          endsRet_tC a hSN C h.1.2⟩, rowsC_tC hSN C h.2⟩
end
end

section
variable (a : AbortName)

mutual
theorem rowsV_trV (hP : rowsV a.P = true) : ∀ A : VTy, rowsV A = true → rowsV (trV a A) = true
  | .tensor A B, h | .sum A B, h => by
      simp only [rowsV, Bool.and_eq_true] at h
      simp only [trV, rowsV, Bool.and_eq_true]; exact ⟨rowsV_trV hP A h.1, rowsV_trV hP B h.2⟩
  | .thunk C, h => by
      simp only [rowsV] at h; simp only [trV, rowsV, trC_eq a C]; exact rowsC_trChain hP _ C h
  | .ref A, h | .imm _ A, h | .mut _ A, h | .box _ A, h | .bang A, h | .mu A, h | .fam A, h => by
      simp only [rowsV] at h; simp only [trV, rowsV]; exact rowsV_trV hP A h
  | .unit, _ | .zero, _ | .unk, _ | .tvar _, _ | .int _, _ | .opq _, _ => rfl
theorem rowsC_trChain (hP : rowsV a.P = true) :
    ∀ (has : Bool) (C : CTy), rowsC C = true → rowsC (trChain a has C) = true
  | has, .ret A, h => by
      simp only [rowsC] at h; simp only [trChain]
      split
      · simp only [rowsC, rowsV, Bool.and_eq_true]; exact ⟨rowsV_trV hP A h, hP⟩
      · simp only [rowsC]; exact rowsV_trV hP A h
  | _, .arr A C, h => by
      simp only [rowsC, Bool.and_eq_true] at h
      simp only [trChain, rowsC, Bool.and_eq_true, trC_eq a C]
      exact ⟨rowsV_trV hP A h.1, rowsC_trChain hP _ C h.2⟩
  | _, .amp C D, h => by
      simp only [rowsC, Bool.and_eq_true] at h
      simp only [trChain, rowsC, Bool.and_eq_true, trC_eq a C, trC_eq a D]
      exact ⟨rowsC_trChain hP _ C h.1, rowsC_trChain hP _ D h.2⟩
  | _, .top, _ => rfl
  | _, .all _ _ C, h | _, .nu C, h => by
      simp only [rowsC] at h; simp only [trChain, rowsC, trC_eq a C]; exact rowsC_trChain hP _ C h
  | has, .eff m i c w A B fin C, h => by
      simp only [rowsC, Bool.and_eq_true] at h
      simp only [trChain]
      split
      · exact rowsC_trChain hP has C h.2
      · simp only [rowsC, Bool.and_eq_true, trC_eq a fin]
        exact ⟨⟨⟨⟨rowsV_trV hP A h.1.1.1.1, rowsV_trV hP B h.1.1.1.2⟩, rowsC_trChain hP _ fin h.1.1.2⟩,
          endsRet_trChain a has C h.1.2⟩, rowsC_trChain hP has C h.2⟩
end
end

/-- **A rule's step** of a run's type translation: R0's at an abortive name, or R1's. -/
inductive Step where
  | abort (a : AbortName)
  | tail (a : TailName)

/-- The step's name. -/
def Step.n : Step → UInt32
  | .abort a => a.n
  | .tail a => a.n

/-- The step's translation of a value type. -/
def Step.ty : Step → VTy → VTy
  | .abort a => trV a
  | .tail a => tV a

/-- The step's premises: R0's payload has rows over `F`; R1's works perform nothing (`Σ_N = []`,
the licence's conjunct). -/
def Step.ok : Step → Prop
  | .abort a => rowsV a.P = true
  | .tail a => a.SN = []

/-- **The run's translation keeps every obligation that is not an eliminated name's**: the steps
of a run (R0's names, then R1's, in their order), composed, at a type whose rows are returner
chains over `F`. This is G-qual's check (`lostObligation`), at once over every eliminated name. -/
theorem obl_steps : ∀ (ss : List Step), (∀ s ∈ ss, s.ok) → ∀ (A : VTy), rowsV A = true →
    ∀ o, o ∈ obl false A → (∀ s ∈ ss, o.of s.n = false) →
      o ∈ obl false (ss.foldl (fun A s => s.ty A) A)
  | [], _, _, _, o, ho, _ => ho
  | s :: ss, hok, A, h, o, ho, hk => by
      simp only [List.foldl]
      have hs := hok s (by simp)
      have hks : o.of s.n = false := hk s (by simp)
      cases s with
      | abort a =>
        exact obl_steps ss (fun s hs' => hok s (by simp [hs'])) (trV a A) (rowsV_trV a hs A h) o
          (obl_trV a false A h o ho hks) (fun s hs' => hk s (by simp [hs']))
      | tail a =>
        have hm : o ∈ obl false (tV a A) := by
          rw [obl_tV a hs false A h, List.mem_filter]
          refine ⟨ho, ?_⟩
          simp only [Step.n] at hks
          simp [keep, hks]
        exact obl_steps ss (fun s hs' => hok s (by simp [hs'])) (tV a A) (rowsV_tV a hs A h) o hm
          (fun s hs' => hk s (by simp [hs']))

end Rewrite

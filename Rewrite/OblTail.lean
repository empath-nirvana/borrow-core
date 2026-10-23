import Rewrite.Obl
import Rewrite.Tail

/-!
# Rewrite — R1's translation and a type's obligations  `[spec §12, §54]`

R1's type translation (`tV`, `Rewrite/Tail.lean`) discharges exactly the obligations whose source
is an operation of its name (`Rewrite/Obl.lean`): `obl (tV a A) = (obl A).filter (keep a)`
(`obl_tV`), at a works' row `Σ_N = []` and a type whose rows are returner chains over `F` (`rowsV`).
-/

namespace Rewrite
open BoCa.Fig16.LogRel.Core (VTy CTy OpSig Row Count FShape toFShape isX0)

/-! ### R1's translation discharges exactly the name's obligations -/

mutual
/-- Every returner chain of a value type, at any depth, ends in `F A`: the rows the checker writes
(`CTy.effOf`). -/
def rowsV : VTy → Bool
  | .tensor A B | .sum A B => rowsV A && rowsV B
  | .thunk C => rowsC C
  | .ref A | .imm _ A | .mut _ A | .box _ A | .bang A | .mu A | .fam A => rowsV A
  | .unit | .zero | .unk | .tvar _ | .int _ | .opq _ => true
/-- Every returner chain of a computation type ends in `F A`. -/
def rowsC : CTy → Bool
  | .ret A => rowsV A
  | .arr A C => rowsV A && rowsC C
  | .amp C D => rowsC C && rowsC D
  | .top => true
  | .all _ _ C | .nu C => rowsC C
  | .eff _ _ _ _ A B fin C => rowsV A && rowsV B && rowsC fin && endsRet C && rowsC C
end

section
variable (a : TailName)

/-- The obligations R1 keeps: those whose source is not an operation of `n`. -/
def keep (o : Ob) : Bool := !o.of a.n

theorem clB_tV : ∀ (k : Nat) (A : VTy), BoCa.Fig16.LogRel.Core.Check.VTy.clB k (tV a A) = BoCa.Fig16.LogRel.Core.Check.VTy.clB k A
  | k, .tensor A B | k, .sum A B => by simp only [tV, BoCa.Fig16.LogRel.Core.Check.VTy.clB, clB_tV k A, clB_tV k B]
  | k, .ref A | k, .imm _ A | k, .mut _ A | k, .box _ A | k, .bang A | k, .fam A => by
      simp only [tV, BoCa.Fig16.LogRel.Core.Check.VTy.clB, clB_tV k A]
  | k, .mu A => by simp only [tV, BoCa.Fig16.LogRel.Core.Check.VTy.clB, clB_tV (k + 1) A]
  | _, .thunk _ | _, .unit | _, .zero | _, .unk | _, .tvar _ | _, .int _ | _, .opq _ => rfl

theorem occB_tV : ∀ (k : Nat) (A : VTy), BoCa.Fig16.LogRel.Core.Check.VTy.occB k (tV a A) = BoCa.Fig16.LogRel.Core.Check.VTy.occB k A
  | k, .tensor A B | k, .sum A B => by simp only [tV, BoCa.Fig16.LogRel.Core.Check.VTy.occB, occB_tV k A, occB_tV k B]
  | k, .ref A | k, .imm _ A | k, .mut _ A | k, .box _ A | k, .bang A | k, .fam A => by
      simp only [tV, BoCa.Fig16.LogRel.Core.Check.VTy.occB, occB_tV k A]
  | k, .mu A => by simp only [tV, BoCa.Fig16.LogRel.Core.Check.VTy.occB, occB_tV (k + 1) A]
  | _, .thunk _ | _, .unit | _, .zero | _, .unk | _, .tvar _ | _, .int _ | _, .opq _ => rfl

theorem polyB_tV : ∀ A : VTy, BoCa.Fig16.LogRel.Core.Check.VTy.polyB (tV a A) = BoCa.Fig16.LogRel.Core.Check.VTy.polyB A
  | .tensor A B | .sum A B => by simp only [tV, BoCa.Fig16.LogRel.Core.Check.VTy.polyB, polyB_tV A, polyB_tV B]
  | .box _ A => by simp only [tV, BoCa.Fig16.LogRel.Core.Check.VTy.polyB, polyB_tV A]
  | .tvar _ => rfl
  | .ref A | .imm _ A | .mut _ A | .bang A | .fam A | .mu A => by
      simp only [tV, BoCa.Fig16.LogRel.Core.Check.VTy.polyB, BoCa.Fig16.LogRel.Core.Check.VTy.occB, occB_tV a]
  | .thunk _ | .unit | .zero | .unk | .int _ | .opq _ => rfl

theorem isX0_tV (A : VTy) : isX0 (tV a A) = isX0 A := by
  cases A with
  | tvar k => cases k <;> rfl
  | _ => rfl

theorem shape_tV : ∀ A : VTy,
    Frontend.Check.FShape.wfB (toFShape (tV a A)) = Frontend.Check.FShape.wfB (toFShape A) ∧
    Frontend.Check.FShape.guardedB (toFShape (tV a A)) = Frontend.Check.FShape.guardedB (toFShape A)
  | .tensor A B | .sum A B => by
      simp only [tV, toFShape, Frontend.Check.FShape.wfB, Frontend.Check.FShape.guardedB,
        (shape_tV A).1, (shape_tV B).1, and_self]
  | .tvar k => by cases k <;> exact ⟨rfl, rfl⟩
  | .ref B => by
      cases B with
      | tvar k => cases k <;> exact ⟨rfl, rfl⟩
      | _ => exact ⟨by simp only [tV, toFShape, Frontend.Check.FShape.wfB, BoCa.Fig16.LogRel.Core.Check.VTy.clB, clB_tV a], rfl⟩
  | .imm _ _ | .mut _ _ | .box _ _ | .bang _ | .fam _ | .mu _ | .thunk _ | .unit | .zero | .unk
  | .int _ | .opq _ => ⟨by simp only [tV, toFShape, Frontend.Check.FShape.wfB, BoCa.Fig16.LogRel.Core.Check.VTy.clB, clB_tV a], rfl⟩

/-- At `Σ_N = []` a returner chain's rest translates as the chain itself. -/
theorem tChain_eq (hSN : a.SN = []) :
    ∀ (has : Bool) (ks : List (UInt32 × UInt32)) (C : CTy), tChain a has ks C = tC a C
  | has, ks, .eff m i c w A B fin C => by
      simp only [tChain, tC, tChain_eq hSN has ks C, tChain_eq hSN (m == a.n || chainHas a.n C)
        ((m, i) :: chainKeys C) C]
  | has, _, .ret R => by
      cases has <;> simp [tChain, tC, TailName.extra, hSN, stackOps]
  | _, _, .arr _ _ | _, _, .amp _ _ | _, _, .top | _, _, .all _ _ _ | _, _, .nu _ => by
      simp [tChain, tC]

/-- At `Σ_N = []`, a returner chain's layer of `n` is removed and every other layer kept. -/
theorem tC_eff (hSN : a.SN = []) (m i : UInt32) (c : Count) (w : BoCa.Fig16.LogRel.Core.World)
    (A B : VTy) (fin C : CTy) :
    tC a (.eff m i c w A B fin C) =
      if m == a.n then tC a C else .eff m i c w (tV a A) (tV a B) (tC a fin) (tC a C) := by
  simp only [tC, tChain_eq a hSN]

theorem endsRet_tC (hSN : a.SN = []) : ∀ C : CTy, endsRet C = true → endsRet (tC a C) = true
  | .eff m i c w A B fin C, h => by
      rw [tC_eff a hSN]; simp only [endsRet] at h
      split <;> (try simp only [endsRet]) <;> exact endsRet_tC hSN C h
  | .ret _, _ => rfl
  | .arr _ _, h | .amp _ _, h | .top, h | .all _ _ _, h | .nu _, h => by simp [endsRet] at h

/-- A codata observation that is a returner chain ending in `F A` has its chain's obligations. -/
theorem leafObl_chain : ∀ C : CTy, endsRet C = true → leafObl C = effObl C
  | .eff .., _ => rfl
  | .ret _, _ => rfl
  | .arr _ _, h | .amp _ _, h | .top, h | .all _ _ _, h | .nu _, h => by simp [endsRet] at h

/-- A codata thunk whose body is a returner chain has no destructor of its own shape. -/
theorem thunkObl_nu_ret : ∀ X : CTy, endsRet X = true → thunkObl (.nu X) = [.cell "a thunk"]
  | .eff .., _ | .ret _, _ => rfl
  | .arr _ _, h | .amp _ _, h | .top, h | .all _ _ _, h | .nu _, h => by simp [endsRet] at h

theorem tV_unit (R : VTy) : tV a R = .unit ↔ R = .unit := by
  cases R <;> simp [tV]

theorem effObl_tC (hSN : a.SN = []) : ∀ C : CTy, effObl (tC a C) = (effObl C).filter (keep a)
  | .eff m i c w A B fin C => by
      rw [tC_eff a hSN]
      by_cases hm : (m == a.n) = true
      · simp only [hm, if_true, effObl, List.filter_append, effObl_tC hSN C]
        have : ((if BoCa.Fig16.LogRel.Core.Check.VTy.clB 0 A && BoCa.Fig16.LogRel.Core.Check.VTy.clB 0 B then [] else [Ob.leaf m i]).filter (keep a)) = [] := by
          split <;> simp [keep, Ob.of, hm]
        rw [this, List.nil_append]
      · simp only [hm, Bool.false_eq_true, if_false, effObl, List.filter_append, effObl_tC hSN C,
          clB_tV]
        congr 1
        split <;> simp [keep, Ob.of, hm]
  | .ret A => by
      simp only [tC, effObl, polyB_tV]; split <;> simp [keep, Ob.of]
  | .arr _ _ | .amp _ _ | .top | .all _ _ _ | .nu _ => by simp [tC, effObl, keep, Ob.of]

theorem leafObl_tC (hSN : a.SN = []) :
    ∀ C : CTy, rowsC C = true → leafObl (tC a C) = (leafObl C).filter (keep a)
  | .eff m i c w A B fin C, h => by
      simp only [rowsC, Bool.and_eq_true] at h
      have hr : endsRet C = true := h.1.2
      rw [tC_eff a hSN]
      by_cases hm : (m == a.n) = true
      · simp only [hm, if_true, leafObl, List.filter_append,
          leafObl_chain (tC a C) (endsRet_tC a hSN C hr), effObl_tC a hSN C]
        have : ((if BoCa.Fig16.LogRel.Core.Check.VTy.clB 0 A && BoCa.Fig16.LogRel.Core.Check.VTy.clB 0 B then [] else [Ob.leaf m i]).filter (keep a)) = [] := by
          split <;> simp [keep, Ob.of, hm]
        rw [this, List.nil_append]
      · simp only [hm, Bool.false_eq_true, if_false, leafObl, List.filter_append, effObl_tC a hSN C,
          clB_tV]
        congr 1
        split <;> simp [keep, Ob.of, hm]
  | .ret A, _ => by
      simp only [tC, leafObl, polyB_tV]; split <;> simp [keep, Ob.of]
  | .amp C D, h => by
      simp only [rowsC, Bool.and_eq_true] at h
      simp only [tC, leafObl, List.filter_append, leafObl_tC hSN C h.1, leafObl_tC hSN D h.2]
  | .arr A D, h => by
      simp only [rowsC, Bool.and_eq_true] at h
      simp only [tC, leafObl, List.filter_append, leafObl_tC hSN D h.2, clB_tV]
      congr 1
      split <;> simp [keep, Ob.of]
  | .top, _ | .all _ _ _, _ | .nu _, _ => by simp [tC, leafObl, keep, Ob.of]

theorem ampFin_tC (hSN : a.SN = []) : ∀ D : CTy, ampFin (tC a D) = (ampFin D).filter (keep a)
  | .eff m i c w A B fin D => by
      rw [tC_eff a hSN]
      by_cases hm : (m == a.n) = true
      · simp [hm, ampFin, ampFin_tC hSN D, keep, Ob.of]
      · simp only [hm, Bool.false_eq_true, if_false, ampFin, ampFin_tC hSN D, List.filter_cons]
        simp [keep, Ob.of, hm]
  | .ret R => by
      by_cases hu : R = .unit
      · subst hu; rfl
      · have hu' : tV a R ≠ .unit := fun h => hu ((tV_unit a R).mp h)
        have hc : ∀ X : VTy, X ≠ .unit → ampFin (.ret X) = [.cell "a thunk"] := by
          intro X hX; cases X <;> simp_all [ampFin]
        simp only [tC, hc _ hu', hc _ hu]; simp [keep, Ob.of]
  | .arr _ _ | .amp _ _ | .top | .all _ _ _ | .nu _ => by simp [tC, ampFin, keep, Ob.of]

mutual
/-- **R1's translation discharges exactly the obligations of `n`'s operations** (at `Σ_N = []`, at
a type whose rows are returner chains over `F`): `obl (⟦A⟧) = obl A ∖ Obl_n`. -/
theorem obl_tV (hSN : a.SN = []) :
    ∀ (alg : Bool) (A : VTy), rowsV A = true → obl alg (tV a A) = (obl alg A).filter (keep a)
  | alg, .tensor A B, h | alg, .sum A B, h => by
      simp only [rowsV, Bool.and_eq_true] at h
      simp only [tV, obl, List.filter_append, obl_tV hSN alg A h.1, obl_tV hSN alg B h.2]
  | alg, .ref A, h => by
      simp only [rowsV] at h
      simp only [tV, obl, isX0_tV]; split
      · rfl
      · exact obl_tV hSN false A h
  | alg, .tvar 0, _ => by cases alg <;> simp [tV, obl, keep, Ob.of]
  | _, .tvar (_ + 1), _ => by simp [tV, obl, keep, Ob.of]
  | _, .box _ A, h => by simp only [rowsV] at h; simp only [tV, obl]; exact obl_tV hSN false A h
  | _, .mu A, h => by
      simp only [rowsV] at h
      simp only [tV, obl, List.filter_append, (shape_tV a A).1, (shape_tV a A).2, obl_tV hSN true A h]
      congr 1; split <;> simp [keep, Ob.of]
  | _, .thunk C, h => by
      simp only [rowsV] at h
      simp only [tV, obl]; exact thunkObl_tC hSN C h
  | _, .unit, _ | _, .zero, _ | _, .int _, _ | _, .unk, _ | _, .bang _, _ | _, .imm _ _, _
  | _, .mut _ _, _ => by simp [tV, obl]
  | _, .fam (.ref A), h => by
      simp only [rowsV] at h
      simp only [tV, obl]; exact obl_tV hSN false A h
  | _, .fam (.imm _ _), _ | _, .fam (.mut _ _), _ => by simp [tV, obl]
  | _, .fam (.unit), _ | _, .fam (.tensor _ _), _ | _, .fam .zero, _ | _, .fam (.sum _ _), _
  | _, .fam (.thunk _), _ | _, .fam (.box _ _), _ | _, .fam (.bang _), _ | _, .fam .unk, _
  | _, .fam (.tvar _), _ | _, .fam (.mu _), _ | _, .fam (.int _), _ | _, .fam (.opq _), _
  | _, .fam (.fam _), _ => by simp [tV, obl, keep, Ob.of]
  | _, .opq _, _ => by simp [tV, obl, keep, Ob.of]
/-- A thunk's obligations under R1's translation. -/
theorem thunkObl_tC (hSN : a.SN = []) :
    ∀ C : CTy, rowsC C = true → thunkObl (tC a C) = (thunkObl C).filter (keep a)
  | .eff m i c w A B fin C, h => by
      simp only [rowsC, Bool.and_eq_true] at h
      rw [tC_eff a hSN]
      by_cases hm : (m == a.n) = true
      · simp [hm, thunkObl, thunkObl_tC hSN C h.2, keep, Ob.of]
      · simp only [hm, Bool.false_eq_true, if_false, thunkObl, thunkObl_tC hSN C h.2,
          List.filter_cons]
        simp [keep, Ob.of, hm]
  | .amp X D, _ => by simp only [tC, thunkObl]; exact ampFin_tC a hSN D
  | .nu (.amp X D), h => by
      simp only [rowsC, Bool.and_eq_true] at h
      simp only [tC, thunkObl]
      exact nuFin_tC hSN X D h.1 h.2
  | .ret _, _ | .arr _ _, _ | .top, _ | .all _ _ _, _ => by simp [tC, thunkObl, keep, Ob.of]
  | .nu (.ret _), _ | .nu (.arr _ _), _ | .nu .top, _ | .nu (.all _ _ _), _ | .nu (.nu _), _ => by
      simp [tC, thunkObl, keep, Ob.of]
  | .nu (.eff m i c w A B fin C), h => by
      simp only [rowsC, Bool.and_eq_true] at h
      have he : endsRet (tC a (.eff m i c w A B fin C)) = true :=
        endsRet_tC a hSN _ (by simp only [endsRet]; exact h.1.2)
      rw [show tC a (.nu (.eff m i c w A B fin C)) = .nu (tC a (.eff m i c w A B fin C)) from rfl,
        thunkObl_nu_ret _ he]
      simp [thunkObl, keep, Ob.of]
/-- A codata thunk's finish under R1's translation. -/
theorem nuFin_tC (hSN : a.SN = []) : ∀ (X D : CTy), rowsC X = true → rowsC D = true →
    nuFin (leafObl (tC a X)) (tC a D) = (nuFin (leafObl X) D).filter (keep a)
  | X, .eff m i c w A B fin D, hX, h => by
      simp only [rowsC, Bool.and_eq_true] at h
      rw [tC_eff a hSN]
      by_cases hm : (m == a.n) = true
      · simp [hm, nuFin, nuFin_tC hSN X D hX h.2, keep, Ob.of]
      · simp only [hm, Bool.false_eq_true, if_false, nuFin, nuFin_tC hSN X D hX h.2,
          List.filter_cons]
        simp [keep, Ob.of, hm]
  | X, .ret R, hX, h => by
      simp only [rowsC] at h
      have hR := obl_tV hSN false R h
      simp only [tC, nuFin, List.filter_append, leafObl_tC a hSN X hX, hR, polyB_tV, clB_tV]
      congr 2; split <;> simp [keep, Ob.of]
  | _, .arr _ _, _, _ | _, .amp _ _, _, _ | _, .top, _, _ | _, .all _ _ _, _, _ | _, .nu _, _, _ => by
      simp [tC, nuFin, keep, Ob.of]
end

end

end Rewrite

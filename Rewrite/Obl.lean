import Frontend.Check.Program

/-!
# Rewrite — a type's obligations  `[spec §12, §54]`

**A type's obligations** (`obl`) are the reasons its values have no destructor, by the structural
recursion of `dtorB` (SPEC §12, `Frontend/Check/Steps.lean`), each with its source:

* `op m i c`: an operation `m.i` (at the count `c`) of a thunk's finish row, which a destructor
  would have to perform (`U(C & F_Σ 1)`, `U(νX. C & F_Σ R)`), or of a row that stands where
  `dtorB` needs no row (a thunk's top-level returner chain);
* `leaf m i`: an operation `m.i` of a codata observation whose signature is not closed, or whose
  returner chain does not end in `F A` (`CTy.effLeafB`);
* `cell k`: a value of no destructor that no operation accounts for: a thunk of `F A` or of
  `A ⊸ C`, a type variable, `μ` outside `FShape`, a family of other leaves, an opaque handle, a
  codata answer or observation leaf that is not closed or polymorphic.

`dtorB alg A = true ↔ obl alg A = []` (`dtorB_iff_obl`): droppability is the absence of
obligations. An operation's contribution is its own entries, so eliminating a name discharges the
obligations whose source is one of its operations (`Ob.of`) and no other: R1's type translation
gives `obl (⟦A⟧) = (obl A).filter (¬ of n)` (`obl_tV`), at a works' row `Σ_N = []` (every name R1
admits in the corpus) and at a type whose rows are returner chains over `F` (`wfV`, every row the
checker writes). The guard checks the statement per binder (G-qual, `Rewrite/Guard.lean`).
-/

namespace Rewrite
open BoCa.Fig16.LogRel.Core (VTy CTy OpSig Row Count FShape toFShape isX0)


/-- **An obligation**, with its source. -/
inductive Ob where
  | op (n i : UInt32) (c : Count)
  | leaf (n i : UInt32)
  | cell (k : String)
  deriving DecidableEq, Repr

/-- The obligation's source is an operation of the name `n`. -/
def Ob.of (n : UInt32) : Ob → Bool
  | .op m _ _ | .leaf m _ => m == n
  | .cell _ => false

/-- A returner chain ends in `F A`. -/
def endsRet : CTy → Bool
  | .eff _ _ _ _ _ _ _ C => endsRet C
  | .ret _ => true
  | _ => false

mutual
/-- **The obligations of `A`** (`alg`: of `T[1/X]` at a `μ` body `T`, as `dtorB`'s mode). -/
def obl : Bool → VTy → List Ob
  | alg, .tensor A B => obl alg A ++ obl alg B
  | alg, .sum A B => obl alg A ++ obl alg B
  | alg, .ref A => if alg && isX0 A then [] else obl false A
  | alg, .tvar 0 => if alg then [] else [.cell "a type variable"]
  | _, .tvar (_ + 1) => [.cell "a type variable"]
  | _, .box _ A => obl false A
  | _, .mu A =>
    (if Frontend.Check.FShape.wfB (toFShape A) && Frontend.Check.FShape.guardedB (toFShape A) then []
     else [.cell "a μ outside FShape"]) ++ obl true A
  | _, .thunk C => thunkObl C
  | _, .unit | _, .zero | _, .int _ | _, .unk | _, .bang _ | _, .imm _ _ | _, .mut _ _ => []
  | _, .fam (.ref A) => obl false A
  | _, .fam (.imm _ _) => []
  | _, .fam (.mut _ _) => []
  | _, .fam (.unit) | _, .fam (.tensor _ _) | _, .fam .zero | _, .fam (.sum _ _) | _, .fam (.thunk _)
  | _, .fam (.box _ _) | _, .fam (.bang _) | _, .fam .unk | _, .fam (.tvar _) | _, .fam (.mu _)
  | _, .fam (.int _) | _, .fam (.opq _) | _, .fam (.fam _) => [.cell "a family"]
  | _, .opq _ => [.cell "an opaque handle"]
/-- A thunk's obligations: its top-level returner chain's operations, then `U(C & F 1)`'s and
`U(νX. C & F R)`'s. -/
def thunkObl : CTy → List Ob
  | .eff n i c _ _ _ _ C => .op n i c :: thunkObl C
  | .amp _ D => ampFin D
  | .nu (.amp C D) => nuFin (leafObl C) D
  | .ret _ | .arr _ _ | .top | .all _ _ _ | .nu (.ret _) | .nu (.arr _ _) | .nu .top
  | .nu (.all _ _ _) | .nu (.nu _) | .nu (.eff _ _ _ _ _ _ _ _) => [.cell "a thunk"]
/-- `U(C & D)`'s finish `D`: its row's operations, then `F 1`. -/
def ampFin : CTy → List Ob
  | .eff n i c _ _ _ _ D => .op n i c :: ampFin D
  | .ret .unit => []
  | .ret (.tensor _ _) | .ret .zero | .ret (.sum _ _) | .ret (.thunk _) | .ret (.ref _)
  | .ret (.imm _ _) | .ret (.mut _ _) | .ret (.box _ _) | .ret (.bang _) | .ret .unk
  | .ret (.tvar _) | .ret (.mu _) | .ret (.int _) | .ret (.opq _) | .ret (.fam _)
  | .arr _ _ | .amp _ _ | .top | .all _ _ _ | .nu _ => [.cell "a thunk"]
/-- `U(νX. C & D)`'s finish `D`, `lc` its observations' obligations: its row's operations, then
`F R`'s, `R` its answer. -/
def nuFin (lc : List Ob) : CTy → List Ob
  | .eff n i c _ _ _ _ D => .op n i c :: nuFin lc D
  | .ret R => lc ++ (if BoCa.Fig16.LogRel.Core.Check.VTy.polyB R && BoCa.Fig16.LogRel.Core.Check.VTy.clB 0 R then [] else [.cell "a codata answer"]) ++ obl false R
  | .arr _ _ | .amp _ _ | .top | .all _ _ _ | .nu _ => [.cell "a thunk"]
/-- A codata observation's obligations (`CTy.nuLeafB`). -/
def leafObl : CTy → List Ob
  | .ret A => if BoCa.Fig16.LogRel.Core.Check.VTy.polyB A then [] else [.cell "a codata leaf"]
  | .amp C D => leafObl C ++ leafObl D
  | .eff n i _ _ A B _ C => (if BoCa.Fig16.LogRel.Core.Check.VTy.clB 0 A && BoCa.Fig16.LogRel.Core.Check.VTy.clB 0 B then [] else [.leaf n i]) ++ effObl C
  | .arr A D => (if BoCa.Fig16.LogRel.Core.Check.VTy.clB 0 A then [] else [.cell "a codata leaf"]) ++ leafObl D
  | .top | .all _ _ _ | .nu _ => [.cell "a codata leaf"]
/-- A codata observation's returner chain's obligations (`CTy.effLeafB`). -/
def effObl : CTy → List Ob
  | .ret A => if BoCa.Fig16.LogRel.Core.Check.VTy.polyB A then [] else [.cell "a codata leaf"]
  | .eff n i _ _ A B _ C => (if BoCa.Fig16.LogRel.Core.Check.VTy.clB 0 A && BoCa.Fig16.LogRel.Core.Check.VTy.clB 0 B then [] else [.leaf n i]) ++ effObl C
  | .arr _ _ | .amp _ _ | .top | .all _ _ _ | .nu _ => [.cell "a codata leaf"]
end

/-! ### Droppability is the absence of obligations -/

open BoCa.Fig16.LogRel.Core.Check (CTy.nuLeafB CTy.effLeafB CTy.nuOkB) in
mutual
theorem effObl_iff : ∀ C : CTy, CTy.effLeafB C = true ↔ effObl C = []
  | .ret A => by
      simp only [CTy.effLeafB, effObl]; by_cases h : BoCa.Fig16.LogRel.Core.Check.VTy.polyB A = true <;> simp_all
  | .eff n i q w A B fin C => by
      simp only [CTy.effLeafB, effObl, List.append_eq_nil_iff, Bool.and_eq_true, ← effObl_iff C]
      by_cases h : (BoCa.Fig16.LogRel.Core.Check.VTy.clB 0 A && BoCa.Fig16.LogRel.Core.Check.VTy.clB 0 B) = true
      · simp only [Bool.and_eq_true] at h; simp [h]
      · simp only [Bool.and_eq_true, not_and] at h
        by_cases hA : BoCa.Fig16.LogRel.Core.Check.VTy.clB 0 A = true
        · simp [hA, h hA]
        · simp [hA]
  | .arr _ _ | .amp _ _ | .top | .all _ _ _ | .nu _ => by simp [CTy.effLeafB, effObl]

theorem leafObl_iff : ∀ C : CTy, CTy.nuLeafB C = true ↔ leafObl C = []
  | .ret A => by
      simp only [CTy.nuLeafB, leafObl]; by_cases h : BoCa.Fig16.LogRel.Core.Check.VTy.polyB A = true <;> simp_all
  | .amp C D => by
      simp only [CTy.nuLeafB, leafObl, Bool.and_eq_true, List.append_eq_nil_iff, leafObl_iff C,
        leafObl_iff D]
  | .eff n i q w A B fin C => by
      simp only [CTy.nuLeafB, leafObl]
      exact effObl_iff (.eff n i q w A B fin C) |>.trans (by simp [effObl])
  | .arr A D => by
      simp only [CTy.nuLeafB, leafObl, Bool.and_eq_true, List.append_eq_nil_iff, ← leafObl_iff D]
      by_cases h : BoCa.Fig16.LogRel.Core.Check.VTy.clB 0 A = true <;> simp_all
  | .top | .all _ _ _ | .nu _ => by simp [CTy.nuLeafB, leafObl]
end

/-- `U(C & D)` has a destructor exactly when `D` is `F 1`. -/
theorem ampFin_nil : ∀ D : CTy, ampFin D = [] ↔ D = .ret .unit
  | .eff .. => by simp [ampFin]
  | .ret A => by cases A <;> simp [ampFin]
  | .arr _ _ | .amp _ _ | .top | .all _ _ _ | .nu _ => by simp [ampFin]

open Frontend.Check (dtorB) in
open BoCa.Fig16.LogRel.Core.Check (CTy.nuLeafB CTy.effLeafB CTy.nuOkB) in
mutual
/-- **Droppability is the absence of obligations**: `dtorB alg A` exactly when `obl alg A = []`. -/
theorem dtorB_iff_obl : ∀ (alg : Bool) (A : VTy), dtorB alg A = true ↔ obl alg A = []
  | alg, .tensor A B => by
      simp only [dtorB, obl, Bool.and_eq_true, List.append_eq_nil_iff, dtorB_iff_obl alg A,
        dtorB_iff_obl alg B]
  | alg, .sum A B => by
      simp only [dtorB, obl, Bool.and_eq_true, List.append_eq_nil_iff, dtorB_iff_obl alg A,
        dtorB_iff_obl alg B]
  | alg, .ref A => by
      simp only [dtorB, obl, Bool.or_eq_true, dtorB_iff_obl false A]
      by_cases h : (alg && isX0 A) = true <;> simp_all
  | alg, .tvar 0 => by cases alg <;> simp [dtorB, obl]
  | _, .tvar (_ + 1) => by simp [dtorB, obl]
  | _, .box _ A => by simp only [dtorB, obl, dtorB_iff_obl false A]
  | _, .mu A => by
      simp only [dtorB, obl, Bool.and_eq_true, List.append_eq_nil_iff, dtorB_iff_obl true A]
      by_cases h : (Frontend.Check.FShape.wfB (toFShape A) &&
        Frontend.Check.FShape.guardedB (toFShape A)) = true
      · simp only [Bool.and_eq_true] at h; simp [h]
      · simp only [Bool.and_eq_true, not_and] at h
        by_cases h1 : Frontend.Check.FShape.wfB (toFShape A) = true
        · simp [h1, h h1]
        · simp [h1]
  | alg, .thunk C => by rw [show obl alg (.thunk C) = thunkObl C by cases alg <;> rfl]; exact thunk_iff_obl alg C
  | _, .unit | _, .zero | _, .int _ | _, .unk | _, .bang _ | _, .imm _ _ | _, .mut _ _ => by
      simp [dtorB, obl]
  | _, .fam (.ref A) => by simp only [dtorB, obl, dtorB_iff_obl false A]
  | _, .fam (.imm _ _) | _, .fam (.mut _ _) => by simp [dtorB, obl]
  | _, .fam (.unit) | _, .fam (.tensor _ _) | _, .fam .zero | _, .fam (.sum _ _) | _, .fam (.thunk _)
  | _, .fam (.box _ _) | _, .fam (.bang _) | _, .fam .unk | _, .fam (.tvar _) | _, .fam (.mu _)
  | _, .fam (.int _) | _, .fam (.opq _) | _, .fam (.fam _) => by simp [dtorB, obl]
  | _, .opq _ => by simp [dtorB, obl]
/-- A thunk has a destructor exactly when it has no obligation. -/
theorem thunk_iff_obl : ∀ (alg : Bool) (C : CTy), dtorB alg (.thunk C) = true ↔ thunkObl C = []
  | _, .eff .. | _, .ret _ | _, .arr _ _ | _, .top | _, .all _ _ _ => by simp [dtorB, thunkObl]
  | _, .amp X D => by
      cases D
      case ret A => cases A <;> simp [dtorB, thunkObl, ampFin]
      all_goals simp [dtorB, thunkObl, ampFin]
  | _, .nu (.amp X D) => by
      cases D
      case ret R =>
        simp only [dtorB, thunkObl, nuFin, CTy.nuOkB, CTy.nuLeafB, Bool.and_eq_true,
          List.append_eq_nil_iff, leafObl_iff X, dtorB_iff_obl false R]
        by_cases hp : BoCa.Fig16.LogRel.Core.Check.VTy.polyB R = true <;> by_cases hc : BoCa.Fig16.LogRel.Core.Check.VTy.clB 0 R = true <;> simp_all
      all_goals simp [dtorB, thunkObl, nuFin]
  | _, .nu (.ret _) | _, .nu (.arr _ _) | _, .nu .top | _, .nu (.all _ _ _) | _, .nu (.nu _)
  | _, .nu (.eff _ _ _ _ _ _ _ _) => by simp [dtorB, thunkObl]
end

end Rewrite

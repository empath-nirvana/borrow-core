import Targets.Base.Typing

/-!
# The Instance — the open types (RESTRUCTURE §4.2)

Core's `VTy` and `CTy` have no row-variable former, so the library reads a type that mentions row
variables as the family of its closed instances.  Within one derivation a variable of the context
then has one type at each environment, and one let-bound function is not used at two rows in one
body; E1, E2, E6 and E10 need exactly that.

`OVTy`, `OCTy` are Core's formers over open rows, with two more computation formers:

* `effF S A`: the returner at the row family `S` (at each row environment `η`, `F_{S η} A`).  A row
  of the row form `RF`, with its variables, is read through `RF.den` into such a family
  (`Targets/Instance/Core.lean`'s `F`).
* `allR ρ k C`: the row `∀`, binding the row variable `ρ` at the constraint `k`, which the family
  representation cannot express.

`den η` instantiates the row variables (at `allR` it reads `C` at `η`; the typing systems read
`den` only at `∀`-free types, where it gives the library's families).  `ofV`, `ofC` embed Core's
closed types, and `den η (ofV A) = A`.
-/

noncomputable section

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar)
open Targets (RVar RowEnv RowCon)

mutual
/-- Open value types: Core's formers over open rows. -/
inductive OVTy where
  | unit
  | tensor (A B : OVTy)
  | zero
  | sum (A B : OVTy)
  | thunk (C : OCTy)
  | ref (A : OVTy)
  | imm (a : Lifetime.Life) (A : OVTy)
  | mut (a : Lifetime.Life) (A : OVTy)
  | box (a : Lifetime.Life) (A : OVTy)
  | bang (A : OVTy)
  | unk
  | tvar (n : Nat)
  | mu (A : OVTy)
  | int (w : Width)
  | fam (L : OVTy)
  | opq (k : Opaque)
/-- Open computation types: Core's formers, the returner at a row family, and the row `∀`. -/
inductive OCTy where
  | ret (A : OVTy)
  | arr (A : OVTy) (C : OCTy)
  | amp (C D : OCTy)
  | top
  | all (x : LifeVar) (b : Lifetime.Life) (C : OCTy)
  | nu (C : OCTy)
  | eff (n i : UInt32) (q : Qual) (A B : VTy) (C : OCTy)
  /-- `F_S A`, `S` a row family over the row environment. -/
  | effF (S : RowEnv → Row) (A : OVTy)
  /-- `∀ρ:k. C`, the row `∀`. -/
  | allR (ρ : RVar) (k : RowCon) (C : OCTy)
end

mutual
/-- The instance of an open value type at a row environment. -/
def OVTy.den (η : RowEnv) : OVTy → VTy
  | .unit => .unit
  | .tensor A B => .tensor (OVTy.den η A) (OVTy.den η B)
  | .zero => .zero
  | .sum A B => .sum (OVTy.den η A) (OVTy.den η B)
  | .thunk C => .thunk (OCTy.den η C)
  | .ref A => .ref (OVTy.den η A)
  | .imm a A => .imm a (OVTy.den η A)
  | .mut a A => .mut a (OVTy.den η A)
  | .box a A => .box a (OVTy.den η A)
  | .bang A => .bang (OVTy.den η A)
  | .unk => .unk
  | .tvar n => .tvar n
  | .mu A => .mu (OVTy.den η A)
  | .int w => .int w
  | .fam L => .fam (OVTy.den η L)
  | .opq k => .opq k
/-- The instance of an open computation type at a row environment. -/
def OCTy.den (η : RowEnv) : OCTy → CTy
  | .ret A => .ret (OVTy.den η A)
  | .arr A C => .arr (OVTy.den η A) (OCTy.den η C)
  | .amp C D => .amp (OCTy.den η C) (OCTy.den η D)
  | .top => .top
  | .all x b C => .all x b (OCTy.den η C)
  | .nu C => .nu (OCTy.den η C)
  | .eff n i q A B C => .eff n i q A B (OCTy.den η C)
  | .effF S A => CTy.effOf (S η) (OVTy.den η A)
  | .allR _ _ C => OCTy.den η C
end

mutual
/-- Core's value types, as open types with no row variable. -/
def OVTy.ofV : VTy → OVTy
  | .unit => .unit
  | .tensor A B => .tensor (OVTy.ofV A) (OVTy.ofV B)
  | .zero => .zero
  | .sum A B => .sum (OVTy.ofV A) (OVTy.ofV B)
  | .thunk C => .thunk (OCTy.ofC C)
  | .ref A => .ref (OVTy.ofV A)
  | .imm a A => .imm a (OVTy.ofV A)
  | .mut a A => .mut a (OVTy.ofV A)
  | .box a A => .box a (OVTy.ofV A)
  | .bang A => .bang (OVTy.ofV A)
  | .unk => .unk
  | .tvar n => .tvar n
  | .mu A => .mu (OVTy.ofV A)
  | .int w => .int w
  | .fam L => .fam (OVTy.ofV L)
  | .opq k => .opq k
/-- Core's computation types, as open types with no row variable. -/
def OCTy.ofC : CTy → OCTy
  | .ret A => .ret (OVTy.ofV A)
  | .arr A C => .arr (OVTy.ofV A) (OCTy.ofC C)
  | .amp C D => .amp (OCTy.ofC C) (OCTy.ofC D)
  | .top => .top
  | .all x b C => .all x b (OCTy.ofC C)
  | .nu C => .nu (OCTy.ofC C)
  | .eff n i q A B C => .eff n i q A B (OCTy.ofC C)
end

mutual
theorem OVTy.den_ofV (η : RowEnv) : ∀ A : VTy, OVTy.den η (OVTy.ofV A) = A
  | .unit | .zero | .unk | .tvar _ | .int _ | .opq _ => rfl
  | .tensor A B | .sum A B => by
      simp only [OVTy.ofV, OVTy.den, OVTy.den_ofV η A, OVTy.den_ofV η B]
  | .thunk C => by simp only [OVTy.ofV, OVTy.den, OCTy.den_ofC η C]
  | .ref A | .bang A | .mu A | .fam A => by simp only [OVTy.ofV, OVTy.den, OVTy.den_ofV η A]
  | .imm _ A | .mut _ A | .box _ A => by simp only [OVTy.ofV, OVTy.den, OVTy.den_ofV η A]
theorem OCTy.den_ofC (η : RowEnv) : ∀ C : CTy, OCTy.den η (OCTy.ofC C) = C
  | .ret A => by simp only [OCTy.ofC, OCTy.den, OVTy.den_ofV η A]
  | .arr A C => by simp only [OCTy.ofC, OCTy.den, OVTy.den_ofV η A, OCTy.den_ofC η C]
  | .amp C D => by simp only [OCTy.ofC, OCTy.den, OCTy.den_ofC η C, OCTy.den_ofC η D]
  | .top => rfl
  | .all _ _ C | .nu C | .eff _ _ _ _ _ C => by simp only [OCTy.ofC, OCTy.den, OCTy.den_ofC η C]
end

mutual
/-- No row `∀` anywhere. -/
def OVTy.RFree : OVTy → Prop
  | .tensor A B | .sum A B => OVTy.RFree A ∧ OVTy.RFree B
  | .thunk C => OCTy.RFree C
  | .ref A | .imm _ A | .mut _ A | .box _ A | .bang A | .mu A | .fam A => OVTy.RFree A
  | .unit | .zero | .unk | .tvar _ | .int _ | .opq _ => True
/-- No row `∀` anywhere. -/
def OCTy.RFree : OCTy → Prop
  | .ret A => OVTy.RFree A
  | .arr A C => OVTy.RFree A ∧ OCTy.RFree C
  | .amp C D => OCTy.RFree C ∧ OCTy.RFree D
  | .top => True
  | .all _ _ C | .nu C | .eff _ _ _ _ _ C => OCTy.RFree C
  | .effF _ A => OVTy.RFree A
  | .allR _ _ _ => False
end

mutual
theorem OVTy.rFree_ofV : ∀ A : VTy, OVTy.RFree (OVTy.ofV A)
  | .unit | .zero | .unk | .tvar _ | .int _ | .opq _ => trivial
  | .tensor A B | .sum A B => ⟨OVTy.rFree_ofV A, OVTy.rFree_ofV B⟩
  | .thunk C => OCTy.rFree_ofC C
  | .ref A | .bang A | .mu A | .fam A => OVTy.rFree_ofV A
  | .imm _ A | .mut _ A | .box _ A => OVTy.rFree_ofV A
theorem OCTy.rFree_ofC : ∀ C : CTy, OCTy.RFree (OCTy.ofC C)
  | .ret A => OVTy.rFree_ofV A
  | .arr A C => ⟨OVTy.rFree_ofV A, OCTy.rFree_ofC C⟩
  | .amp C D => ⟨OCTy.rFree_ofC C, OCTy.rFree_ofC D⟩
  | .top => trivial
  | .all _ _ C | .nu C | .eff _ _ _ _ _ C => OCTy.rFree_ofC C
end

/-- An open judgement's subject: a value at an open value type, or a computation at an open
computation type. -/
inductive OJdg
  | val (A : OVTy)
  | comp (C : OCTy)

/-- Its instance at a row environment. -/
def OJdg.den (η : RowEnv) : OJdg → Jdg
  | .val A => .val (A.den η)
  | .comp C => .comp (C.den η)

/-- No row `∀`. -/
def OJdg.RFree : OJdg → Prop
  | .val A => A.RFree
  | .comp C => C.RFree

/-- Core's judgement subject, as an open one. -/
def OJdg.ofJ : Jdg → OJdg
  | .val A => .val (OVTy.ofV A)
  | .comp C => .comp (OCTy.ofC C)

theorem OJdg.den_ofJ (η : RowEnv) : ∀ j : Jdg, (OJdg.ofJ j).den η = j
  | .val A => by simp only [OJdg.ofJ, OJdg.den, OVTy.den_ofV]
  | .comp C => by simp only [OJdg.ofJ, OJdg.den, OCTy.den_ofC]

theorem OJdg.rFree_ofJ : ∀ j : Jdg, (OJdg.ofJ j).RFree
  | .val A => OVTy.rFree_ofV A
  | .comp C => OCTy.rFree_ofC C

/-- A context's instance at a row environment. -/
def octxDen (η : RowEnv) (Γ : Ctx OVTy) : Ctx VTy := Γ.map fun s => ⟨s.ty.den η, s.live⟩

/-- Core's context, as an open one. -/
def octxOf (Γ : Ctx VTy) : Ctx OVTy := Γ.map fun s => ⟨OVTy.ofV s.ty, s.live⟩

theorem octxDen_octxOf (η : RowEnv) (Γ : Ctx VTy) : octxDen η (octxOf Γ) = Γ := by
  induction Γ with
  | nil => rfl
  | cons s Γ ih => simp only [octxOf, octxDen, List.map_cons, OVTy.den_ofV] at ih ⊢; rw [ih]

/-- No row `∀` in a context. -/
def octxRFree (Γ : Ctx OVTy) : Prop := ∀ s ∈ Γ, s.ty.RFree

theorem octxRFree_octxOf (Γ : Ctx VTy) : octxRFree (octxOf Γ) := by
  intro s hs
  simp only [octxOf, List.mem_map] at hs
  obtain ⟨s', -, rfl⟩ := hs
  exact OVTy.rFree_ofV s'.ty

end Targets.Inst

end

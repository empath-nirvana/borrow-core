import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Support.Lifetimes.Substitution
import Support.LogicalRelation.Facts
import Support.Statics.Contexts

/-!
# CBPVWorld — Types

Call-by-push-value types, the index of the typed world's records.

* Value types `VTy ::= 1 | A ⊗ B | 0 | A ⊕ B | U C | Ref A | Imm @a A | Mut @a A | [@a] A | !A | Unk`.
* Computation types `CTy ::= F A | A ⊸ C | C & D | ⊤ | ∀'x ⊏ @b. C`.

`VTy.recV` is the value-type eliminator with `U C` a leaf: the typed world never looks inside
a computation type.  Beside the formers: the free lifetime variables `VFree`/`CFree`, the
reborrow metafunction `Imm̲` (`VTy.immReborrow`), capture-avoiding lifetime substitution
(`VTy.applyLSub`/`CTy.applyLSub`, `CTy.instLife`), the outlives judgment `VOutlives` and
scoping `VScoped`.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.CBPVWorld
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar LSubst)

mutual
/-- Value types. -/
inductive VTy where
  | unit
  | tensor (A B : VTy)
  | zero
  | sum (A B : VTy)
  /-- `U C`. -/
  | thunk (C : CTy)
  /-- `Ref A`. -/
  | ref (A : VTy)
  /-- `Imm @a A`. -/
  | imm (a : Lifetime.Life) (A : VTy)
  /-- `Mut @a A`. -/
  | mut (a : Lifetime.Life) (A : VTy)
  /-- `[@a] A`. -/
  | box (a : Lifetime.Life) (A : VTy)
  /-- `!A`. -/
  | bang (A : VTy)
  /-- `Unk`. -/
  | unk
/-- Computation types. -/
inductive CTy where
  /-- `F A`. -/
  | ret (A : VTy)
  /-- `A ⊸ C`. -/
  | arr (A : VTy) (C : CTy)
  /-- `C & D`. -/
  | amp (C D : CTy)
  /-- `⊤`. -/
  | top
  /-- `∀'x ⊏ @b. C`. -/
  | all (x : LifeVar) (b : Lifetime.Life) (C : CTy)
end

/-- The value-type eliminator with `U C` a leaf. -/
@[elab_as_elim]
theorem VTy.recV {motive : VTy → Prop}
    (unit : motive .unit)
    (tensor : ∀ A B, motive A → motive B → motive (.tensor A B))
    (zero : motive .zero)
    (sum : ∀ A B, motive A → motive B → motive (.sum A B))
    (thunk : ∀ C, motive (.thunk C))
    (ref : ∀ A, motive A → motive (.ref A))
    (imm : ∀ a A, motive A → motive (.imm a A))
    («mut» : ∀ a A, motive A → motive (.mut a A))
    (box : ∀ a A, motive A → motive (.box a A))
    (bang : ∀ A, motive A → motive (.bang A))
    (unk : motive .unk) : ∀ A, motive A
  | .unit => unit
  | .tensor A B => tensor A B (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk A)
      (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk B)
  | .zero => zero
  | .sum A B => sum A B (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk A)
      (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk B)
  | .thunk C => thunk C
  | .ref A => ref A (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk A)
  | .imm a A => imm a A (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk A)
  | .mut a A => «mut» a A (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk A)
  | .box a A => box a A (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk A)
  | .bang A => bang A (VTy.recV unit tensor zero sum thunk ref imm «mut» box bang unk A)
  | .unk => unk

/-- `A ⊸ B` at value type: `U (A ⊸ F B)`, BoLo's arrow read call-by-value. -/
abbrev VTy.lolli (A B : VTy) : VTy := .thunk (.arr A (.ret B))

/-- `∀'x ⊏ @b. A` at value type: `U (∀'x ⊏ @b. F A)`, BoLo's `∀` read call-by-value. -/
abbrev VTy.all (x : LifeVar) (b : Lifetime.Life) (A : VTy) : VTy := .thunk (.all x b (.ret A))

/-! ### Free lifetime variables -/

mutual
/-- `'x` occurs free in `A`; `∀'y ⊏ @b. C` binds `'y` in `C` and not in `@b`. -/
def VFree (x : LifeVar) : VTy → Prop
  | .unit => False
  | .zero => False
  | .unk => False
  | .tensor A B => VFree x A ∨ VFree x B
  | .sum A B => VFree x A ∨ VFree x B
  | .thunk C => CFree x C
  | .ref A => VFree x A
  | .bang A => VFree x A
  | .imm a A => a.mentions x = true ∨ VFree x A
  | .mut a A => a.mentions x = true ∨ VFree x A
  | .box a A => a.mentions x = true ∨ VFree x A
/-- `'x` occurs free in `C`. -/
def CFree (x : LifeVar) : CTy → Prop
  | .ret A => VFree x A
  | .arr A C => VFree x A ∨ CFree x C
  | .amp C D => CFree x C ∨ CFree x D
  | .top => False
  | .all y b C => b.mentions x = true ∨ (x ≠ y ∧ CFree x C)
end

/-! ### The reborrow metafunction -/

/-- `Imm̲ 'b A`: the view a load through an immutable borrow at `'b` gives of a payload of
type `A`.  `1`, `0`, `⊗`, `⊕` structurally; `U C ↦ Unk` (codata has no safe view, as `⊸`
and `∀` in BoLo); `Ref A ↦ Imm 'b A`; `Imm @a A` kept; `Mut @a A ↦ Imm 'b A`;
`[@a] A ↦ Imm̲ 'b A`; `!A` kept whole (it holds no resource); `Unk ↦ Unk`. -/
def VTy.immReborrow (b : Lifetime.Life) : VTy → VTy
  | .unit => .unit
  | .tensor A B => .tensor (A.immReborrow b) (B.immReborrow b)
  | .zero => .zero
  | .sum A B => .sum (A.immReborrow b) (B.immReborrow b)
  | .thunk _ => .unk
  | .ref A => .imm b A
  | .imm a A => .imm a A
  | .mut _ A => .imm b A
  | .box _ A => A.immReborrow b
  | .bang A => .bang A
  | .unk => .unk

/-! ### Lifetime substitution -/

mutual
/-- One past the largest lifetime index anywhere in `A`, binders included. -/
def VTy.lifeBound : VTy → Nat
  | .unit => 0
  | .zero => 0
  | .unk => 0
  | .tensor A B => max A.lifeBound B.lifeBound
  | .sum A B => max A.lifeBound B.lifeBound
  | .thunk C => C.lifeBound
  | .ref A => A.lifeBound
  | .bang A => A.lifeBound
  | .imm a A => max a.varBound A.lifeBound
  | .mut a A => max a.varBound A.lifeBound
  | .box a A => max a.varBound A.lifeBound
/-- One past the largest lifetime index anywhere in `C`, binders included. -/
def CTy.lifeBound : CTy → Nat
  | .ret A => A.lifeBound
  | .arr A C => max A.lifeBound C.lifeBound
  | .amp C D => max C.lifeBound D.lifeBound
  | .top => 0
  | .all x b C => max (x + 1) (max b.varBound C.lifeBound)
end

mutual
/-- `A` with the simultaneous lifetime substitution `σ` applied. -/
def VTy.applyLSub (σ : LSubst) : VTy → VTy
  | .unit => .unit
  | .zero => .zero
  | .unk => .unk
  | .tensor A B => .tensor (A.applyLSub σ) (B.applyLSub σ)
  | .sum A B => .sum (A.applyLSub σ) (B.applyLSub σ)
  | .thunk C => .thunk (C.applyLSub σ)
  | .ref A => .ref (A.applyLSub σ)
  | .bang A => .bang (A.applyLSub σ)
  | .imm a A => .imm (a.applySub σ) (A.applyLSub σ)
  | .mut a A => .mut (a.applySub σ) (A.applyLSub σ)
  | .box a A => .box (a.applySub σ) (A.applyLSub σ)
/-- `C` with the simultaneous lifetime substitution `σ` applied, renaming a `∀` binder where
it would capture (`Ty.applyLSub`'s `∀` clause). -/
def CTy.applyLSub (σ : LSubst) : CTy → CTy
  | .ret A => .ret (A.applyLSub σ)
  | .arr A C => .arr (A.applyLSub σ) (C.applyLSub σ)
  | .amp C D => .amp (C.applyLSub σ) (D.applyLSub σ)
  | .top => .top
  | .all y b C =>
      if lsubCaptures (lsubDrop σ y) y then
        .all (max (y + 1) (max (lsubRangeBound (lsubDrop σ y)) C.lifeBound)) (b.applySub σ)
          (C.applyLSub ((y, Lifetime.Life.var
            (max (y + 1) (max (lsubRangeBound (lsubDrop σ y)) C.lifeBound))) :: lsubDrop σ y))
      else
        .all y (b.applySub σ) (C.applyLSub (lsubDrop σ y))
end

/-- `A[@a/'x]`. -/
def VTy.instLife (x : LifeVar) (a : Lifetime.Life) (A : VTy) : VTy := A.applyLSub [(x, a)]

/-- `C[@a/'x]` — the substitution `∀E` performs. -/
def CTy.instLife (x : LifeVar) (a : Lifetime.Life) (C : CTy) : CTy := C.applyLSub [(x, a)]

theorem CTy.applyLSub_all_captures {σ : LSubst} {y : LifeVar} {b : Lifetime.Life} {C : CTy}
    (h : lsubCaptures (lsubDrop σ y) y = true) :
    (CTy.all y b C).applyLSub σ
      = .all (max (y + 1) (max (lsubRangeBound (lsubDrop σ y)) C.lifeBound)) (b.applySub σ)
          (C.applyLSub ((y, Lifetime.Life.var
            (max (y + 1) (max (lsubRangeBound (lsubDrop σ y)) C.lifeBound))) :: lsubDrop σ y)) := by
  rw [CTy.applyLSub, if_pos h]

theorem CTy.applyLSub_all_not_captures {σ : LSubst} {y : LifeVar} {b : Lifetime.Life} {C : CTy}
    (h : lsubCaptures (lsubDrop σ y) y = false) :
    (CTy.all y b C).applyLSub σ = .all y (b.applySub σ) (C.applyLSub (lsubDrop σ y)) := by
  rw [CTy.applyLSub, if_neg (by simp [h])]

mutual
/-- A variable free in `A` is below `A.lifeBound`. -/
theorem lt_vLifeBound {x : LifeVar} : ∀ {A : VTy}, VFree x A → x < A.lifeBound
  | .unit, h => h.elim
  | .zero, h => h.elim
  | .unk, h => h.elim
  | .tensor A B, h => by
      rcases h with h | h
      · exact Nat.lt_of_lt_of_le (lt_vLifeBound h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (lt_vLifeBound h) (Nat.le_max_right _ _)
  | .sum A B, h => by
      rcases h with h | h
      · exact Nat.lt_of_lt_of_le (lt_vLifeBound h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (lt_vLifeBound h) (Nat.le_max_right _ _)
  | .thunk C, h => lt_cLifeBound (C := C) h
  | .ref A, h => lt_vLifeBound (A := A) h
  | .bang A, h => lt_vLifeBound (A := A) h
  | .imm a A, h => by
      rcases h with h | h
      · exact Nat.lt_of_lt_of_le (lt_varBound h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (lt_vLifeBound h) (Nat.le_max_right _ _)
  | .mut a A, h => by
      rcases h with h | h
      · exact Nat.lt_of_lt_of_le (lt_varBound h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (lt_vLifeBound h) (Nat.le_max_right _ _)
  | .box a A, h => by
      rcases h with h | h
      · exact Nat.lt_of_lt_of_le (lt_varBound h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (lt_vLifeBound h) (Nat.le_max_right _ _)
/-- A variable free in `C` is below `C.lifeBound`. -/
theorem lt_cLifeBound {x : LifeVar} : ∀ {C : CTy}, CFree x C → x < C.lifeBound
  | .ret A, h => lt_vLifeBound (A := A) h
  | .arr A C, h => by
      rcases h with h | h
      · exact Nat.lt_of_lt_of_le (lt_vLifeBound h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (lt_cLifeBound h) (Nat.le_max_right _ _)
  | .amp C D, h => by
      rcases h with h | h
      · exact Nat.lt_of_lt_of_le (lt_cLifeBound h) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (lt_cLifeBound h) (Nat.le_max_right _ _)
  | .top, h => h.elim
  | .all y b C, h => by
      rcases h with h | ⟨-, h⟩
      · exact Nat.lt_of_lt_of_le (lt_varBound h)
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
      · exact Nat.lt_of_lt_of_le (lt_cLifeBound h)
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
end

/-- `Imm̲` introduces only its index. -/
theorem vFree_immReborrow {x y : LifeVar} : ∀ (A : VTy),
    VFree y (A.immReborrow (.var x)) → y = x ∨ VFree y A := by
  intro A
  induction A using VTy.recV with
  | unit => intro h; exact h.elim
  | zero => intro h; exact h.elim
  | unk => intro h; exact h.elim
  | thunk C => intro h; exact h.elim
  | tensor A B ihA ihB =>
      rintro (h | h)
      · rcases ihA h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rcases ihB h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
  | sum A B ihA ihB =>
      rintro (h | h)
      · rcases ihA h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rcases ihB h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
  | ref A _ =>
      rintro (h | h)
      · left; simp only [Lifetime.Life.mentions, beq_iff_eq] at h; exact h
      · exact Or.inr h
  | imm a A _ => intro h; exact Or.inr h
  | «mut» a A _ =>
      rintro (h | h)
      · left; simp only [Lifetime.Life.mentions, beq_iff_eq] at h; exact h
      · exact Or.inr (Or.inr h)
  | box a A ih =>
      intro h
      rcases ih h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
  | bang A _ => intro h; exact Or.inr h

/-! ### Outlives and scoping -/

/-- `Δ ⊢ A ⊐ @a` on value types: `[TR]` p. 2's rules (`OutlivesRules`), with `0` outliving
every lifetime (it has no values). -/
inductive VOutlives (Δ : LifeCtx) (a : Lifetime.Life) : VTy → Prop where
  | unit : VOutlives Δ a .unit
  | tensor {A B} : VOutlives Δ a A → VOutlives Δ a B → VOutlives Δ a (.tensor A B)
  | zero : VOutlives Δ a .zero
  | sum {A B} : VOutlives Δ a A → VOutlives Δ a B → VOutlives Δ a (.sum A B)
  | ref {A} : VOutlives Δ a A → VOutlives Δ a (.ref A)
  | bang {A} : VOutlives Δ a (.bang A)
  | box {b A} : Δ.EntailsLt a b → VOutlives Δ a (.box b A)
  | imm {b A} : Δ.EntailsLt a b → VOutlives Δ a (.imm b A)
  | «mut» {b A} : Δ.EntailsLt a b → VOutlives Δ a (.mut b A)

/-- `Δ ⊨ Γ ⊐ @a`: `@a` is defined under `Δ` and every live slot outlives it (`Ctx.Outlives`). -/
def CtxOutlives (Δ : LifeCtx) (Γ : Ctx VTy) (a : Lifetime.Life) : Prop :=
  Δ.Defines a ∧ ∀ s ∈ Γ, s.live = true → VOutlives Δ a s.ty

/-- `A` is scoped in `Δ`: its free lifetime variables are in `dom(Δ)`. -/
def VScoped (Δ : LifeCtx) (A : VTy) : Prop := ∀ y, VFree y A → ∃ u, Δ.find? y = some u

/-! ### The borrow axioms' types

`[TR]` p. 3's axiom table read call-by-value (`VTy.lolli`, `VTy.all`), at arbitrary value-type
payloads. -/

/-- `swap : Ref A ⊸ B ⊸ Ref B ⊗ A`. -/
def axSwapTy (A B : VTy) : VTy := .lolli (.ref A) (.lolli B (.tensor (.ref B) A))

/-- `copy : Imm @a A ⊸ Imm @a A ⊗ Imm @a A`. -/
def axCopyTy (a : Lifetime.Life) (A : VTy) : VTy :=
  .lolli (.imm a A) (.tensor (.imm a A) (.imm a A))

/-- `forget : Imm @a A ⊸ 1`. -/
def axForgetImmTy (a : Lifetime.Life) (A : VTy) : VTy := .lolli (.imm a A) .unit

/-- `forget : Mut @a A ⊸ 1`. -/
def axForgetMutTy (a : Lifetime.Life) (A : VTy) : VTy := .lolli (.mut a A) .unit

/-- `forget : Unk ⊸ 1`. -/
def axForgetUnkTy : VTy := .lolli .unk .unit

/-- `withbor : Ref A ⊸ (∀'x ⊏ @bnd. Imm 'x A ⊸ ['x] B) ⊸ Ref A ⊗ B`. -/
def axWithbor1Ty (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) : VTy :=
  .lolli (.ref A)
    (.lolli (.all x bnd (.lolli (.imm (.var x) A) (.box (.var x) B))) (.tensor (.ref A) B))

/-- `withbor : Ref A ⊸ (∀'x ⊏ @bnd. Mut 'x A ⊸ ['x] B) ⊸ Ref A ⊗ B`. -/
def axWithbor2Ty (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) : VTy :=
  .lolli (.ref A)
    (.lolli (.all x bnd (.lolli (.mut (.var x) A) (.box (.var x) B))) (.tensor (.ref A) B))

/-- `withbor : Mut @a A ⊸ (∀'x ⊏ @bnd. Mut 'x A ⊸ ['x] B) ⊸ Mut @a A ⊗ B`. -/
def axWithbor3Ty (a : Lifetime.Life) (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) : VTy :=
  .lolli (.mut a A)
    (.lolli (.all x bnd (.lolli (.mut (.var x) A) (.box (.var x) B))) (.tensor (.mut a A) B))

/-- `withload : Imm @a A ⊸ (∀'x ⊏ @bnd. Imm̲ 'x A ⊸ ['x] B) ⊸ B`. -/
def axWithloadTy (a : Lifetime.Life) (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) : VTy :=
  .lolli (.imm a A)
    (.lolli (.all x bnd (.lolli (VTy.immReborrow (.var x) A) (.box (.var x) B))) B)

/-- `withswap : Mut @a A ⊸ (A ⊸ A ⊗ B) ⊸ Mut @a A ⊗ B`. -/
def axWithswapTy (a : Lifetime.Life) (A B : VTy) : VTy :=
  .lolli (.mut a A) (.lolli (.lolli A (.tensor A B)) (.tensor (.mut a A) B))

end BoCa.Fig16.LogRel.CBPVWorld

end

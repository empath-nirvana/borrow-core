import Core

/-!
# NestedFold — the class `P` and its binders

`P d A`, at `d` type variables in scope, is the class of #595's design §4.2. A closed `A` is a
leaf, whatever its former. Otherwise `A` is a variable in scope, a `⊗`/`⊕` of members, a
`Ref S` or an array `[Ref S]` of a member, or `μB` with `B` a member at `d + 1` whose head is not
a variable (`Hd`). `PB` is the decidable check (`PB_iff`), and `P_of_FShape` puts every
`FShape` body in the class.

A **binder** is a stack `B :: Bs` of `μ` bodies, innermost first: the binder of `μB` met under
the binders `Bs`. `env Bs` gives each variable in scope its closed type, so a position `A` under
`Bs` holds a value of `A.subst (env Bs)`. `rIn Bs A` lists the binders of the `μ`s inside `A`
that are not closed, `aIn Bs A` the element types of its arrays that are not closed, neither
looking inside another binder's body for arrays. `reach B₀` is the list of binders of
`μB₀`; `reach_ok` shows it meets `KeysOK`, the closure the traversal's proof uses, at every
body in the class.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.NestedFold
open BoCa
open BoCa.Fig16

/-! ### Closedness, decided -/

/-- `Cl k A` as a `Bool`. -/
def clB : Nat → VTy → Bool
  | k, .tensor A B => clB k A && clB k B
  | k, .sum A B => clB k A && clB k B
  | k, .ref A => clB k A
  | k, .imm _ A => clB k A
  | k, .mut _ A => clB k A
  | k, .box _ A => clB k A
  | k, .bang A => clB k A
  | k, .fam A => clB k A
  | k, .tvar n => decide (n < k)
  | k, .mu A => clB (k + 1) A
  | _, .unit => true
  | _, .zero => true
  | _, .thunk _ => true
  | _, .unk => true
  | _, .int _ => true
  | _, .opq _ => true

theorem clB_iff : ∀ (k : Nat) (A : VTy), clB k A = true ↔ A.Cl k
  | k, .tensor A B => by simp [clB, VTy.Cl, clB_iff k A, clB_iff k B]
  | k, .sum A B => by simp [clB, VTy.Cl, clB_iff k A, clB_iff k B]
  | k, .ref A => by simp [clB, VTy.Cl, clB_iff k A]
  | k, .imm _ A => by simp [clB, VTy.Cl, clB_iff k A]
  | k, .mut _ A => by simp [clB, VTy.Cl, clB_iff k A]
  | k, .box _ A => by simp [clB, VTy.Cl, clB_iff k A]
  | k, .bang A => by simp [clB, VTy.Cl, clB_iff k A]
  | k, .fam A => by simp [clB, VTy.Cl, clB_iff k A]
  | k, .tvar n => by simp [clB, VTy.Cl]
  | k, .mu A => by simp [clB, VTy.Cl, clB_iff (k + 1) A]
  | _, .unit => by simp [clB, VTy.Cl]
  | _, .zero => by simp [clB, VTy.Cl]
  | _, .thunk _ => by simp [clB, VTy.Cl]
  | _, .unk => by simp [clB, VTy.Cl]
  | _, .int _ => by simp [clB, VTy.Cl]
  | _, .opq _ => by simp [clB, VTy.Cl]

/-! ### The class -/

/-- The head of a body is not a variable: `μ` passes it to its body. `Guarded`, generalised. -/
def head : VTy → Prop
  | .tvar _ => False
  | .mu B => head B
  | _ => True

/-- A body is a leaf (closed) or its head is not a variable. -/
def Hd (B : VTy) : Prop := B.Cl 0 ∨ head B

/-- **The class `P`.**  `[design §4.2]` -/
def P : Nat → VTy → Prop
  | d, .tvar i => i < d
  | d, .tensor A B => P d A ∧ P d B
  | d, .sum A B => P d A ∧ P d B
  | d, .ref S => P d S
  | d, .fam (.ref S) => P d S
  | _, .fam L => L.Cl 0
  | d, .mu B => B.Cl 1 ∨ (P (d + 1) B ∧ Hd B)
  | _, A => A.Cl 0

/-- A body in the class: `μB₀` is in the fold's domain. -/
def PBody (B : VTy) : Prop := P 1 B ∧ Hd B

/-- `head` as a `Bool`. -/
def headB : VTy → Bool
  | .tvar _ => false
  | .mu B => headB B
  | _ => true

theorem headB_iff : ∀ B : VTy, headB B = true ↔ head B
  | .tvar _ => by simp [headB, head]
  | .mu B => by simp [headB, head, headB_iff B]
  | .unit | .tensor _ _ | .zero | .sum _ _ | .thunk _ | .ref _ | .imm _ _ | .mut _ _ | .box _ _
  | .bang _ | .unk | .int _ | .fam _ | .opq _ => by simp [headB, head]

/-- `P` as a `Bool`. -/
def PB : Nat → VTy → Bool
  | d, .tvar i => decide (i < d)
  | d, .tensor A B => PB d A && PB d B
  | d, .sum A B => PB d A && PB d B
  | d, .ref S => PB d S
  | d, .fam (.ref S) => PB d S
  | _, .fam L => clB 0 L
  | d, .mu B => clB 1 B || (PB (d + 1) B && (clB 0 B || headB B))
  | _, A => clB 0 A

theorem PB_iff : ∀ (d : Nat) (A : VTy), PB d A = true ↔ P d A
  | d, .tvar i => by simp [PB, P]
  | d, .tensor A B => by simp [PB, P, PB_iff d A, PB_iff d B]
  | d, .sum A B => by simp [PB, P, PB_iff d A, PB_iff d B]
  | d, .ref S => by simp [PB, P, PB_iff d S]
  | d, .fam (.ref S) => by simp [PB, P, PB_iff d S]
  | d, .fam (.unit) | d, .fam (.tensor _ _) | d, .fam (.zero) | d, .fam (.sum _ _)
  | d, .fam (.thunk _) | d, .fam (.imm _ _) | d, .fam (.mut _ _) | d, .fam (.box _ _)
  | d, .fam (.bang _) | d, .fam (.unk) | d, .fam (.tvar _) | d, .fam (.mu _) | d, .fam (.int _)
  | d, .fam (.fam _) | d, .fam (.opq _) => by simp only [PB, P, clB_iff]
  | d, .mu B => by simp [PB, P, PB_iff (d + 1) B, clB_iff, headB_iff, Hd]
  | _, .unit | _, .zero | _, .thunk _ | _, .imm _ _ | _, .mut _ _ | _, .box _ _ | _, .bang _
  | _, .unk | _, .int _ | _, .opq _ => by simp only [PB, P, clB_iff]

instance (d : Nat) (A : VTy) : Decidable (P d A) := decidable_of_iff _ (PB_iff d A)

instance (B : VTy) : Decidable (PBody B) :=
  decidable_of_iff (PB 1 B && (clB 0 B || headB B)) (by simp [PBody, PB_iff, clB_iff, headB_iff, Hd])

/-- A closed type is in the class at every depth. -/
theorem P_of_closed : ∀ {A : VTy} (d : Nat), A.Cl 0 → P d A
  | .tvar _, _, h => absurd h (Nat.not_lt_zero _)
  | .tensor A B, d, h => ⟨P_of_closed (A := A) d h.1, P_of_closed (A := B) d h.2⟩
  | .sum A B, d, h => ⟨P_of_closed (A := A) d h.1, P_of_closed (A := B) d h.2⟩
  | .ref S, d, h => P_of_closed (A := S) d h
  | .fam (.ref S), d, h => P_of_closed (A := S) d h
  | .fam (.unit), _, h | .fam (.tensor _ _), _, h | .fam (.zero), _, h | .fam (.sum _ _), _, h
  | .fam (.thunk _), _, h | .fam (.imm _ _), _, h | .fam (.mut _ _), _, h | .fam (.box _ _), _, h
  | .fam (.bang _), _, h | .fam (.unk), _, h | .fam (.tvar _), _, h | .fam (.mu _), _, h
  | .fam (.int _), _, h | .fam (.fam _), _, h | .fam (.opq _), _, h => h
  | .mu _, _, h => Or.inl h
  | .unit, _, h | .zero, _, h | .thunk _, _, h | .imm _ _, _, h | .mut _ _, _, h | .box _ _, _, h
  | .bang _, _, h | .unk, _, h | .int _, _, h | .opq _, _, h => h

/-- **`P ⊇ FShape`**: every body of the class `FShape` is a body of `P`. -/
theorem P_of_FShape : ∀ {F : FShape}, F.WF → P 1 F.ty
  | .leaf _, h => P_of_closed 1 h
  | .refX, _ => Nat.zero_lt_one
  | .varX, _ => Nat.zero_lt_one
  | .tensor _ _, h => ⟨P_of_FShape h.1, P_of_FShape h.2⟩
  | .sum _ _, h => ⟨P_of_FShape h.1, P_of_FShape h.2⟩

theorem Hd_of_FShape : ∀ {F : FShape}, F.WF → F.Guarded → Hd F.ty
  | .leaf _, h, _ => Or.inl h
  | .refX, _, _ => Or.inr trivial
  | .varX, _, hg => hg.elim
  | .tensor _ _, _, _ => Or.inr trivial
  | .sum _ _, _, _ => Or.inr trivial

theorem pBody_of_FShape {F : FShape} (hF : F.WF) (hG : F.Guarded) : PBody F.ty :=
  ⟨P_of_FShape hF, Hd_of_FShape hF hG⟩

/-! ### Binders and the closed types in scope -/

/-- A binder: the bodies of the enclosing `μ`s, innermost first. -/
abbrev Stack := List VTy

/-- The closed type of each variable in scope. -/
def env : Stack → Nat → VTy
  | [] => VTy.tvar
  | B :: Bs => VTy.scons (.mu (B.subst (VTy.upS (env Bs)))) (env Bs)

/-- The closed type of the binder `B :: Bs`. -/
abbrev closedOf (B : VTy) (Bs : Stack) : VTy := .mu (B.subst (VTy.upS (env Bs)))

theorem env_cons_zero (B : VTy) (Bs : Stack) : env (B :: Bs) 0 = closedOf B Bs := rfl

/-- Variable `i` in scope has the closed type of its binder `Bs.drop i`. -/
theorem env_drop : ∀ (Bs : Stack) (i : Nat) (B : VTy) (Bs' : Stack), Bs.drop i = B :: Bs' →
    env Bs i = closedOf B Bs'
  | [], _, _, _, h => by simp at h
  | C :: Cs, 0, B, Bs', h => by
      simp only [List.drop_zero, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | C :: Cs, i + 1, B, Bs', h => by
      simp only [List.drop_succ_cons] at h
      exact env_drop Cs i B Bs' h

/-- The unrolling of a binder's closed type is its body under the binder's environment. -/
theorem inst_closedOf (B : VTy) (Bs : Stack) :
    VTy.inst (closedOf B Bs) (B.subst (VTy.upS (env Bs))) = B.subst (env (B :: Bs)) := by
  unfold VTy.inst
  rw [VTy.subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [VTy.upS, VTy.scons, env]
      rw [VTy.subst_rename]
      have : (VTy.scons (closedOf B Bs) VTy.tvar ∘ Nat.succ) = VTy.tvar := by
        funext m; rfl
      rw [this, VTy.subst_id]

/-- The root's closed type is `μB₀`. -/
theorem closedOf_root (B₀ : VTy) : closedOf B₀ [] = .mu B₀ := by
  have : VTy.upS (env []) = VTy.tvar := by
    funext n; cases n <;> rfl
  simp only [closedOf, this, VTy.subst_id]

/-! ### The binders and arrays of a position -/

/-- The binders of the `μ`s inside `A` that are not closed, at every depth. -/
def rIn (Bs : Stack) : VTy → List Stack
  | .tensor A B => rIn Bs A ++ rIn Bs B
  | .sum A B => rIn Bs A ++ rIn Bs B
  | .ref S => rIn Bs S
  | .fam (.ref S) => rIn Bs S
  | .mu B => if clB 0 (.mu B) then [] else (B :: Bs) :: rIn (B :: Bs) B
  | _ => []

/-- The element types of the arrays of `A` that are not closed, outside any inner binder. -/
def aIn : VTy → List VTy
  | .tensor A B => aIn A ++ aIn B
  | .sum A B => aIn A ++ aIn B
  | .ref S => aIn S
  | .fam (.ref S) => if clB 0 S then [] else S :: aIn S
  | _ => []

/-- The binders of `μB₀`: the root and every binder inside its body. -/
def reach (B₀ : VTy) : List Stack := [B₀] :: rIn [B₀] B₀

/-- The binders a traversal can call are listed: each binder's body is in the class, and the
binders inside it are listed. -/
def KeysOK (ks : List Stack) : Prop :=
  ∀ B Bs, (B :: Bs) ∈ ks → P (Bs.length + 1) B ∧ Hd B ∧ ∀ c ∈ rIn (B :: Bs) B, c ∈ ks

/-- Every suffix of a binder is listed. -/
def Anc (ks : List Stack) (Bs : Stack) : Prop := ∀ i, i < Bs.length → Bs.drop i ∈ ks

theorem anc_cons {ks : List Stack} {B : VTy} {Bs : Stack} (h : (B :: Bs) ∈ ks) (hA : Anc ks Bs) :
    Anc ks (B :: Bs) := fun i hi => by
  cases i with
  | zero => simpa using h
  | succ i => simpa using hA i (by simpa using hi)

theorem anc_drop {ks : List Stack} {Bs : Stack} (hA : Anc ks Bs) (i : Nat) :
    Anc ks (Bs.drop i) := fun j hj => by
  rw [List.drop_drop]
  exact hA (i + j) (by simp at hj; omega)

/-- A binder listed by `rIn Bs A` with `A` in the class has its body in the class. -/
theorem rIn_P : ∀ (A : VTy) (Bs : Stack), P Bs.length A → ∀ c ∈ rIn Bs A,
    ∃ B Bs', c = B :: Bs' ∧ P (Bs'.length + 1) B ∧ Hd B
  | .tensor A B, Bs, h, c, hc => by
      simp only [rIn, List.mem_append] at hc
      rcases hc with hc | hc
      · exact rIn_P A Bs h.1 c hc
      · exact rIn_P B Bs h.2 c hc
  | .sum A B, Bs, h, c, hc => by
      simp only [rIn, List.mem_append] at hc
      rcases hc with hc | hc
      · exact rIn_P A Bs h.1 c hc
      · exact rIn_P B Bs h.2 c hc
  | .ref S, Bs, h, c, hc => rIn_P S Bs h c hc
  | .fam (.ref S), Bs, h, c, hc => rIn_P S Bs h c hc
  | .mu B, Bs, h, c, hc => by
      simp only [rIn] at hc
      split at hc
      · simp at hc
      · rename_i hcl
        have hP : P (Bs.length + 1) B ∧ Hd B := by
          rcases h with h | h
          · exact absurd ((clB_iff 0 (.mu B)).mpr h) hcl
          · exact h
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact ⟨B, Bs, rfl, hP⟩
        · exact rIn_P B (B :: Bs) hP.1 c hc
  | .unit, _, _, _, hc | .zero, _, _, _, hc | .thunk _, _, _, _, hc | .imm _ _, _, _, _, hc
  | .mut _ _, _, _, _, hc | .box _ _, _, _, _, hc | .bang _, _, _, _, hc | .unk, _, _, _, hc
  | .int _, _, _, _, hc | .opq _, _, _, _, hc | .tvar _, _, _, _, hc => by simp [rIn] at hc
  | .fam (.unit), _, _, _, hc | .fam (.tensor _ _), _, _, _, hc | .fam (.zero), _, _, _, hc
  | .fam (.sum _ _), _, _, _, hc | .fam (.thunk _), _, _, _, hc | .fam (.imm _ _), _, _, _, hc
  | .fam (.mut _ _), _, _, _, hc | .fam (.box _ _), _, _, _, hc | .fam (.bang _), _, _, _, hc
  | .fam (.unk), _, _, _, hc | .fam (.tvar _), _, _, _, hc | .fam (.mu _), _, _, _, hc
  | .fam (.int _), _, _, _, hc | .fam (.fam _), _, _, _, hc | .fam (.opq _), _, _, _, hc => by
      simp [rIn] at hc

/-- A binder listed by `rIn Bs A` lists the binders inside its own body. -/
theorem rIn_closed : ∀ (A : VTy) (Bs : Stack) (B : VTy) (Bs' : Stack), (B :: Bs') ∈ rIn Bs A →
    ∀ c ∈ rIn (B :: Bs') B, c ∈ rIn Bs A
  | .tensor A₁ A₂, Bs, B, Bs', h, c, hc => by
      simp only [rIn, List.mem_append] at h ⊢
      rcases h with h | h
      · exact Or.inl (rIn_closed A₁ Bs B Bs' h c hc)
      · exact Or.inr (rIn_closed A₂ Bs B Bs' h c hc)
  | .sum A₁ A₂, Bs, B, Bs', h, c, hc => by
      simp only [rIn, List.mem_append] at h ⊢
      rcases h with h | h
      · exact Or.inl (rIn_closed A₁ Bs B Bs' h c hc)
      · exact Or.inr (rIn_closed A₂ Bs B Bs' h c hc)
  | .ref S, Bs, B, Bs', h, c, hc => rIn_closed S Bs B Bs' h c hc
  | .fam (.ref S), Bs, B, Bs', h, c, hc => rIn_closed S Bs B Bs' h c hc
  | .mu B₁, Bs, B, Bs', h, c, hc => by
      simp only [rIn] at h ⊢
      split at h
      · simp at h
      · rw [if_neg (by assumption)]
        simp only [List.mem_cons] at h ⊢
        rcases h with h | h
        · simp only [List.cons.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Or.inr hc
        · exact Or.inr (rIn_closed B₁ (B₁ :: Bs) B Bs' h c hc)
  | .unit, _, _, _, h, _, _ | .zero, _, _, _, h, _, _ | .thunk _, _, _, _, h, _, _
  | .imm _ _, _, _, _, h, _, _ | .mut _ _, _, _, _, h, _, _ | .box _ _, _, _, _, h, _, _
  | .bang _, _, _, _, h, _, _ | .unk, _, _, _, h, _, _ | .int _, _, _, _, h, _, _
  | .opq _, _, _, _, h, _, _ | .tvar _, _, _, _, h, _, _ => by simp [rIn] at h
  | .fam (.unit), _, _, _, h, _, _ | .fam (.tensor _ _), _, _, _, h, _, _
  | .fam (.zero), _, _, _, h, _, _ | .fam (.sum _ _), _, _, _, h, _, _
  | .fam (.thunk _), _, _, _, h, _, _ | .fam (.imm _ _), _, _, _, h, _, _
  | .fam (.mut _ _), _, _, _, h, _, _ | .fam (.box _ _), _, _, _, h, _, _
  | .fam (.bang _), _, _, _, h, _, _ | .fam (.unk), _, _, _, h, _, _
  | .fam (.tvar _), _, _, _, h, _, _ | .fam (.mu _), _, _, _, h, _, _
  | .fam (.int _), _, _, _, h, _, _ | .fam (.fam _), _, _, _, h, _, _
  | .fam (.opq _), _, _, _, h, _, _ => by simp [rIn] at h

/-- **The binders of a body in the class are closed under the traversal's calls.** -/
theorem reach_ok {B₀ : VTy} (h : PBody B₀) : KeysOK (reach B₀) := by
  intro B Bs hm
  simp only [reach, List.mem_cons] at hm
  rcases hm with e | hm
  · simp only [List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨h.1, h.2, fun c hc => List.mem_cons_of_mem _ hc⟩
  · obtain ⟨B', Bs', e, hP, hH⟩ := rIn_P B₀ [B₀] h.1 _ hm
    simp only [List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨hP, hH, fun c hc => List.mem_cons_of_mem _ (rIn_closed B₀ [B₀] B Bs hm c hc)⟩

theorem root_mem (B₀ : VTy) : [B₀] ∈ reach B₀ := List.mem_cons_self

theorem anc_root (B₀ : VTy) : Anc (reach B₀) [B₀] := fun i hi => by
  have : i = 0 := by simpa using hi
  subst this
  exact root_mem B₀

end BoCa.Fig16.LogRel.Core.NestedFold

end

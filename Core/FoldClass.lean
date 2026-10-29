import Core.FoldReuse

/-!
# Core — the fold class `P` and its binders  `[spec §6]`

`P d A`, at `d` type variables in scope, is the class of bodies the general owned fold covers. A
closed `A` is a leaf, whatever its former. Otherwise `A` is a variable in scope, a `⊗`/`⊕` of
members, a `Ref S` or an array `[Ref S]` of a member, or `μB` with `B` a member at `d + 1` whose
head is not a variable (`Hd`). `PB` decides it (`PB_iff`), and every `FShape` body is in the class
(`pBody_of_FShape`).

A **stack** `B :: Bs` is the binder of a `μB` met under the binders `Bs`, innermost first.
`env Bs` gives each variable in scope its closed type, so a position `A` under `Bs` holds a
value of `A.subst (env Bs)`. A **key** (`Bnd`) names a binder the fold calls: a `μ` (`mu b`) or an
array whose element type is not closed (`arr Bs S`, the array of `S` under `Bs`). `keysIn Bs A`
lists the keys of a position in preorder, not looking past a closed leaf; `keys B₀` is the list
of `μB₀`'s keys, the root first. `keys_ok` shows it meets `KeysOK`, the closure the traversal's
proof uses, at every body in the class.
-/

namespace BoCa.Fig16.LogRel.Core

deriving instance DecidableEq for VTy, CTy

end BoCa.Fig16.LogRel.Core

noncomputable section

namespace BoCa.Fig16.LogRel.Core.FoldP
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

/-- **The class `P`.**  `[spec §6]` -/
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

/-- `PBody` as a `Bool`. -/
def pBodyB (B : VTy) : Bool := PB 1 B && (clB 0 B || headB B)

theorem pBodyB_iff (B : VTy) : pBodyB B = true ↔ PBody B := by
  simp [pBodyB, PBody, PB_iff, clB_iff, headB_iff, Hd]

instance (d : Nat) (A : VTy) : Decidable (P d A) := decidable_of_iff _ (PB_iff d A)

instance (B : VTy) : Decidable (PBody B) := decidable_of_iff _ (pBodyB_iff B)

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

/-- A member of the class at depth `d` has its free variables below `d`. -/
theorem Cl_of_P : ∀ {A : VTy} {d : Nat}, P d A → A.Cl d
  | .tvar _, _, h => h
  | .tensor _ _, _, h => ⟨Cl_of_P h.1, Cl_of_P h.2⟩
  | .sum _ _, _, h => ⟨Cl_of_P h.1, Cl_of_P h.2⟩
  | .ref S, _, h => Cl_of_P (A := S) h
  | .fam (.ref S), _, h => Cl_of_P (A := S) h
  | .fam (.unit), d, h | .fam (.tensor _ _), d, h | .fam (.zero), d, h | .fam (.sum _ _), d, h
  | .fam (.thunk _), d, h | .fam (.imm _ _), d, h | .fam (.mut _ _), d, h | .fam (.box _ _), d, h
  | .fam (.bang _), d, h | .fam (.unk), d, h | .fam (.tvar _), d, h | .fam (.mu _), d, h
  | .fam (.int _), d, h | .fam (.fam _), d, h | .fam (.opq _), d, h =>
      VTy.Cl_mono _ h (Nat.zero_le d)
  | .mu B, d, h => by
      rcases h with h | ⟨h, -⟩
      · exact VTy.Cl_mono B h (by omega)
      · exact Cl_of_P (A := B) h
  | .unit, d, h | .zero, d, h | .thunk _, d, h | .imm _ _, d, h | .mut _ _, d, h | .box _ _, d, h
  | .bang _, d, h | .unk, d, h | .int _, d, h | .opq _, d, h => VTy.Cl_mono _ h (Nat.zero_le d)

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

/-! ### Keys -/

/-- A binder the fold calls: a `μ`, or an array of a non-closed element type under a stack. -/
inductive Bnd where
  | mu (b : Stack)
  | arr (Bs : Stack) (S : VTy)
  deriving DecidableEq

/-- The keys of a position, in preorder: each non-closed `μ` and each array of a non-closed
element type, then the keys inside it. -/
def keysIn (Bs : Stack) : VTy → List Bnd
  | .tensor A B => keysIn Bs A ++ keysIn Bs B
  | .sum A B => keysIn Bs A ++ keysIn Bs B
  | .ref S => keysIn Bs S
  | .fam (.ref S) => if clB 0 S then [] else .arr Bs S :: keysIn Bs S
  | .mu B => if clB 0 (.mu B) then [] else .mu (B :: Bs) :: keysIn (B :: Bs) B
  | _ => []

/-- The keys of `μB₀`: the root, then the keys of its body. -/
def keys (B₀ : VTy) : List Bnd := .mu [B₀] :: keysIn [B₀] B₀

/-- The keys a traversal can call are listed: each `μ` key's body is in the class and the keys
inside it are listed, and each array key's element type is in the class and the keys inside it
are listed. -/
def KeysOK (ks : List Bnd) : Prop :=
  (∀ B Bs, .mu (B :: Bs) ∈ ks → P (Bs.length + 1) B ∧ Hd B ∧ ∀ c ∈ keysIn (B :: Bs) B, c ∈ ks) ∧
  ∀ Bs S, .arr Bs S ∈ ks → P Bs.length S ∧ ∀ c ∈ keysIn Bs S, c ∈ ks

/-- Every suffix of a binder is listed. -/
def Anc (ks : List Bnd) (Bs : Stack) : Prop := ∀ i, i < Bs.length → .mu (Bs.drop i) ∈ ks

theorem anc_cons {ks : List Bnd} {B : VTy} {Bs : Stack} (h : .mu (B :: Bs) ∈ ks) (hA : Anc ks Bs) :
    Anc ks (B :: Bs) := fun i hi => by
  cases i with
  | zero => simpa using h
  | succ i => simpa using hA i (by simpa using hi)

theorem anc_drop {ks : List Bnd} {Bs : Stack} (hA : Anc ks Bs) (i : Nat) :
    Anc ks (Bs.drop i) := fun j hj => by
  rw [List.drop_drop]
  exact hA (i + j) (by simp at hj; omega)

/-- What a key of a position in the class carries: a `μ` key's body is in the class with its
head not a variable, and an array key's element type is in the class. -/
def KeyP : Bnd → Prop
  | .mu [] => False
  | .mu (B :: Bs) => P (Bs.length + 1) B ∧ Hd B
  | .arr Bs S => P Bs.length S

/-- A key listed by `keysIn Bs A` with `A` in the class carries `KeyP`. -/
theorem keysIn_P : ∀ (A : VTy) (Bs : Stack), P Bs.length A → ∀ c ∈ keysIn Bs A, KeyP c
  | .tensor A B, Bs, h, c, hc => by
      simp only [keysIn, List.mem_append] at hc
      rcases hc with hc | hc
      · exact keysIn_P A Bs h.1 c hc
      · exact keysIn_P B Bs h.2 c hc
  | .sum A B, Bs, h, c, hc => by
      simp only [keysIn, List.mem_append] at hc
      rcases hc with hc | hc
      · exact keysIn_P A Bs h.1 c hc
      · exact keysIn_P B Bs h.2 c hc
  | .ref S, Bs, h, c, hc => keysIn_P S Bs h c hc
  | .fam (.ref S), Bs, h, c, hc => by
      simp only [keysIn] at hc
      split at hc
      · simp at hc
      · simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact h
        · exact keysIn_P S Bs h c hc
  | .mu B, Bs, h, c, hc => by
      simp only [keysIn] at hc
      split at hc
      · simp at hc
      · rename_i hcl
        have hP : P (Bs.length + 1) B ∧ Hd B := by
          rcases h with h | h
          · exact absurd ((clB_iff 0 (.mu B)).mpr h) hcl
          · exact h
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact hP
        · exact keysIn_P B (B :: Bs) hP.1 c hc
  | .unit, _, _, _, hc | .zero, _, _, _, hc | .thunk _, _, _, _, hc | .imm _ _, _, _, _, hc
  | .mut _ _, _, _, _, hc | .box _ _, _, _, _, hc | .bang _, _, _, _, hc | .unk, _, _, _, hc
  | .int _, _, _, _, hc | .opq _, _, _, _, hc | .tvar _, _, _, _, hc => by simp [keysIn] at hc
  | .fam (.unit), _, _, _, hc | .fam (.tensor _ _), _, _, _, hc | .fam (.zero), _, _, _, hc
  | .fam (.sum _ _), _, _, _, hc | .fam (.thunk _), _, _, _, hc | .fam (.imm _ _), _, _, _, hc
  | .fam (.mut _ _), _, _, _, hc | .fam (.box _ _), _, _, _, hc | .fam (.bang _), _, _, _, hc
  | .fam (.unk), _, _, _, hc | .fam (.tvar _), _, _, _, hc | .fam (.mu _), _, _, _, hc
  | .fam (.int _), _, _, _, hc | .fam (.fam _), _, _, _, hc | .fam (.opq _), _, _, _, hc => by
      simp [keysIn] at hc

/-- The keys inside a key listed by `keysIn Bs A` are listed by it too. -/
def keysOf : Bnd → List Bnd
  | .mu [] => []
  | .mu (B :: Bs) => keysIn (B :: Bs) B
  | .arr Bs S => keysIn Bs S

theorem keysIn_closed : ∀ (A : VTy) (Bs : Stack) (k : Bnd), k ∈ keysIn Bs A →
    ∀ c ∈ keysOf k, c ∈ keysIn Bs A
  | .tensor A₁ A₂, Bs, k, h, c, hc => by
      simp only [keysIn, List.mem_append] at h ⊢
      rcases h with h | h
      · exact Or.inl (keysIn_closed A₁ Bs k h c hc)
      · exact Or.inr (keysIn_closed A₂ Bs k h c hc)
  | .sum A₁ A₂, Bs, k, h, c, hc => by
      simp only [keysIn, List.mem_append] at h ⊢
      rcases h with h | h
      · exact Or.inl (keysIn_closed A₁ Bs k h c hc)
      · exact Or.inr (keysIn_closed A₂ Bs k h c hc)
  | .ref S, Bs, k, h, c, hc => keysIn_closed S Bs k h c hc
  | .fam (.ref S), Bs, k, h, c, hc => by
      simp only [keysIn] at h ⊢
      split at h
      · simp at h
      · rw [if_neg (by assumption)]
        simp only [List.mem_cons] at h ⊢
        rcases h with rfl | h
        · exact Or.inr hc
        · exact Or.inr (keysIn_closed S Bs k h c hc)
  | .mu B₁, Bs, k, h, c, hc => by
      simp only [keysIn] at h ⊢
      split at h
      · simp at h
      · rw [if_neg (by assumption)]
        simp only [List.mem_cons] at h ⊢
        rcases h with rfl | h
        · exact Or.inr hc
        · exact Or.inr (keysIn_closed B₁ (B₁ :: Bs) k h c hc)
  | .unit, _, _, h, _, _ | .zero, _, _, h, _, _ | .thunk _, _, _, h, _, _
  | .imm _ _, _, _, h, _, _ | .mut _ _, _, _, h, _, _ | .box _ _, _, _, h, _, _
  | .bang _, _, _, h, _, _ | .unk, _, _, h, _, _ | .int _, _, _, h, _, _
  | .opq _, _, _, h, _, _ | .tvar _, _, _, h, _, _ => by simp [keysIn] at h
  | .fam (.unit), _, _, h, _, _ | .fam (.tensor _ _), _, _, h, _, _
  | .fam (.zero), _, _, h, _, _ | .fam (.sum _ _), _, _, h, _, _
  | .fam (.thunk _), _, _, h, _, _ | .fam (.imm _ _), _, _, h, _, _
  | .fam (.mut _ _), _, _, h, _, _ | .fam (.box _ _), _, _, h, _, _
  | .fam (.bang _), _, _, h, _, _ | .fam (.unk), _, _, h, _, _
  | .fam (.tvar _), _, _, h, _, _ | .fam (.mu _), _, _, h, _, _
  | .fam (.int _), _, _, h, _, _ | .fam (.fam _), _, _, h, _, _
  | .fam (.opq _), _, _, h, _, _ => by simp [keysIn] at h

/-- **The keys of a body in the class are closed under the traversal's calls.** -/
theorem keys_ok {B₀ : VTy} (h : PBody B₀) : KeysOK (keys B₀) := by
  have hall : ∀ k ∈ keys B₀, KeyP k ∧ ∀ c ∈ keysOf k, c ∈ keys B₀ := by
    intro k hk
    simp only [keys, List.mem_cons] at hk
    rcases hk with rfl | hk
    · exact ⟨h, fun c hc => List.mem_cons_of_mem _ hc⟩
    · exact ⟨keysIn_P B₀ [B₀] h.1 k hk,
        fun c hc => List.mem_cons_of_mem _ (keysIn_closed B₀ [B₀] k hk c hc)⟩
  refine ⟨fun B Bs hm => ?_, fun Bs S hm => ?_⟩
  · obtain ⟨hP, hc⟩ := hall _ hm
    exact ⟨hP.1, hP.2, hc⟩
  · obtain ⟨hP, hc⟩ := hall _ hm
    exact ⟨hP, hc⟩

theorem root_mem (B₀ : VTy) : Bnd.mu [B₀] ∈ keys B₀ := List.mem_cons_self

theorem root_idx (B₀ : VTy) : (keys B₀).idxOf (.mu [B₀]) = 0 := by
  simp [keys, List.idxOf_cons_self]

theorem anc_root (B₀ : VTy) : Anc (keys B₀) [B₀] := fun i hi => by
  have : i = 0 := by simpa using hi
  subst this
  exact root_mem B₀

end BoCa.Fig16.LogRel.Core.FoldP

end

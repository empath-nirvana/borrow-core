import Frontend.Check.Rules
import Core.Classes

/-!
# Frontend — Check — steps shared by the checker's cases

The checker's environment, the messages it reports, the deciders of fold shapes and
destructors, the implicit drops (SPEC §12), and the steps that combine checked premises through a
rule builder once its side conditions are decided: closing binders, splitting and merging
contexts, `boxed`, application to a variable, `<,>`, `case` and `Fun`.
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (Jdg FShape HasDtor dtorAlgs DerivedDrop Linear)

/-! ### Fold shapes and destructors, decided -/

/-- `FShape.WF`, decided. -/
def FShape.wfB : FShape → Bool
  | .leaf A => VTy.clB 0 A
  | .refX => true
  | .varX => true
  | .tensor F G => FShape.wfB F && FShape.wfB G
  | .sum F G => FShape.wfB F && FShape.wfB G

theorem FShape.wfB_sound : ∀ F : FShape, FShape.wfB F = true → F.WF
  | .leaf A, h => VTy.clB_sound 0 A h
  | .refX, _ => trivial
  | .varX, _ => trivial
  | .tensor F G, h => by
      simp only [FShape.wfB, Bool.and_eq_true] at h
      exact ⟨wfB_sound F h.1, wfB_sound G h.2⟩
  | .sum F G, h => by
      simp only [FShape.wfB, Bool.and_eq_true] at h
      exact ⟨wfB_sound F h.1, wfB_sound G h.2⟩

/-- `FShape.Guarded`, decided. -/
def FShape.guardedB : FShape → Bool
  | .varX => false
  | _ => true

theorem FShape.guardedB_sound : ∀ F : FShape, FShape.guardedB F = true → F.Guarded
  | .leaf _, _ => trivial
  | .refX, _ => trivial
  | .varX, h => by simp [FShape.guardedB] at h
  | .tensor _ _, _ => trivial
  | .sum _ _, _ => trivial

/-! ### Destructors (SPEC §12) -/

open BoCa.Fig16.LogRel.Core.FoldP (clB keysIn resO PBody pBodyB pBodyB_iff Bnd Stack) in
/-- `HasDtor`, decided: `dtorB false A` for `A`; `dtorB true A` for a position `A` of a `μ` body:
`A⟨1⟩` has a destructor, and so has the body of each key inside `A` (the recursion of `dtorAt` and
`algsIn`). -/
def dtorB : Bool → CVTy → Bool
  | alg, .tensor A B => dtorB alg A && dtorB alg B
  | alg, .sum A B => dtorB alg A && dtorB alg B
  | alg, .ref A => if alg && !clB 0 A then dtorB true A else dtorB false A
  | alg, .tvar _ => alg
  | _, .box _ A => dtorB false A
  | alg, .mu A => if alg && !clB 0 (.mu A) then dtorB true A else pBodyB A && dtorB true A
  | _, .thunk (.amp _ (.ret .unit)) => true
  | _, .thunk (.nu (.amp C (.ret R))) =>
      CTy.nuOkB (.amp C (.ret R)) && VTy.clB 0 R && dtorB false R
  | _, .thunk _ => false
  | _, .unit | _, .zero | _, .int _ | _, .unk | _, .bang _ | _, .imm _ _ | _, .mut _ _ => true
  | alg, .fam (.ref A) => if alg && !clB 0 A then dtorB true A else dtorB false A
  | _, .fam (.imm _ _) => true
  | _, .fam (.mut _ _) => true
  | _, .fam _ => false
  | _, .opq _ => false

/-- At a thunk `dtorB` does not depend on the mode. -/
theorem dtorB_thunk : ∀ (b : Bool) (C : CCTy), dtorB b (.thunk C) = dtorB false (.thunk C)
  | _, .amp _ (.ret .unit) | _, .nu (.amp _ (.ret _)) | _, .nu (.ret _) | _, .nu (.arr _ _)
  | _, .nu .top | _, .nu (.all _ _ _) | _, .nu (.nu _) | _, .nu (.eff _ _ _ _ _ _ _ _)
  | _, .nu (.amp _ (.arr _ _)) | _, .nu (.amp _ (.amp _ _)) | _, .nu (.amp _ .top)
  | _, .nu (.amp _ (.all _ _ _)) | _, .nu (.amp _ (.nu _)) | _, .nu (.amp _ (.eff _ _ _ _ _ _ _ _))
  | _, .ret _ | _, .arr _ _ | _, .top | _, .all _ _ _ | _, .eff _ _ _ _ _ _ _ _
  | _, .amp _ (.ret (.tensor _ _)) | _, .amp _ (.ret .zero) | _, .amp _ (.ret (.sum _ _))
  | _, .amp _ (.ret (.thunk _)) | _, .amp _ (.ret (.ref _)) | _, .amp _ (.ret (.imm _ _))
  | _, .amp _ (.ret (.mut _ _)) | _, .amp _ (.ret (.box _ _)) | _, .amp _ (.ret (.bang _))
  | _, .amp _ (.ret .unk) | _, .amp _ (.ret (.tvar _)) | _, .amp _ (.ret (.mu _))
  | _, .amp _ (.ret (.int _)) | _, .amp _ (.ret (.fam _)) | _, .amp _ (.ret (.opq _))
  | _, .amp _ (.arr _ _) | _, .amp _ (.amp _ _) | _, .amp _ .top | _, .amp _ (.all _ _ _)
  | _, .amp _ (.nu _) | _, .amp _ (.eff _ _ _ _ _ _ _ _) => rfl

open BoCa.Fig16.LogRel.Core.FoldP (clB) in
/-- At a closed type the two modes agree. -/
theorem dtorB_closed : ∀ (A : CVTy), clB 0 A = true → dtorB true A = dtorB false A
  | .tensor A B, h => by
      simp only [BoCa.Fig16.LogRel.Core.FoldP.clB, Bool.and_eq_true] at h
      simp only [dtorB, dtorB_closed A h.1, dtorB_closed B h.2]
  | .sum A B, h => by
      simp only [BoCa.Fig16.LogRel.Core.FoldP.clB, Bool.and_eq_true] at h
      simp only [dtorB, dtorB_closed A h.1, dtorB_closed B h.2]
  | .ref A, h => by
      simp only [BoCa.Fig16.LogRel.Core.FoldP.clB] at h
      simp [dtorB, h]
  | .fam (.ref A), h => by
      simp only [BoCa.Fig16.LogRel.Core.FoldP.clB] at h
      simp [dtorB, h]
  | .mu A, h => by simp [dtorB, h]
  | .tvar _, h => by simp [BoCa.Fig16.LogRel.Core.FoldP.clB] at h
  | .thunk C, _ => dtorB_thunk true C
  | .unit, _ | .zero, _ | .box _ _, _ | .bang _, _ | .unk, _ | .int _, _
  | .opq _, _ | .imm _ _, _ | .mut _ _, _ => rfl
  | .fam .unit, _ | .fam (.tensor _ _), _ | .fam .zero, _ | .fam (.sum _ _), _
  | .fam (.thunk _), _ | .fam (.imm _ _), _ | .fam (.mut _ _), _ | .fam (.box _ _), _
  | .fam (.bang _), _ | .fam .unk, _ | .fam (.tvar _), _ | .fam (.mu _), _ | .fam (.int _), _
  | .fam (.fam _), _ | .fam (.opq _), _ => rfl

open BoCa.Fig16.LogRel.Core.FoldP (keysIn resO Bnd Stack) in
/-- What `dtorB true A` gives at a position `A` under the stack `Bs`: `A⟨1⟩` has a destructor,
and so has the body of each key of `A`. -/
abbrev AlgDtor (Bs : Stack) (A : CVTy) : Prop :=
  HasDtor (resO dtorAlgs Bs A) ∧
    (∀ B Bs', Bnd.mu (B :: Bs') ∈ keysIn Bs A → HasDtor (resO dtorAlgs (B :: Bs') B)) ∧
    ∀ Bs' S, Bnd.arr Bs' S ∈ keysIn Bs A → HasDtor (resO dtorAlgs Bs' S)

open BoCa.Fig16.LogRel.Core.FoldP (clB keysIn resO resO_leaf Bnd Stack) in
/-- A closed position's `AlgDtor` is its own destructor. -/
theorem algDtor_closed {A : CVTy} (hc : clB 0 A = true) (h : HasDtor A) (Bs : Stack) :
    AlgDtor Bs A := by
  refine ⟨by rwa [resO_leaf dtorAlgs Bs hc], fun B Bs' hm => ?_, fun Bs' S hm => ?_⟩
  · rw [BoCa.Fig16.LogRel.Core.keysIn_toFShape.keysIn_closed Bs hc] at hm; cases hm
  · rw [BoCa.Fig16.LogRel.Core.keysIn_toFShape.keysIn_closed Bs hc] at hm; cases hm

open BoCa.Fig16.LogRel.Core.FoldP (keysIn resO Stack) in
/-- A position the fold passes through: `A⟨1⟩` is `A`, and it has no key. -/
theorem algDtorLeaf (A : CVTy) (h : HasDtor A) (Bs : Stack)
    (hr : resO dtorAlgs Bs A = A := by rfl) (hk : keysIn Bs A = [] := by rfl) : AlgDtor Bs A :=
  ⟨by rwa [hr], ⟨fun B Bs' hm => (by rw [hk] at hm; cases hm),
    fun Bs' S hm => (by rw [hk] at hm; cases hm)⟩⟩

mutual
/-- **`dtorB false` is sound for `HasDtor`.** -/
theorem dtorB_sound : ∀ (A : CVTy), dtorB false A = true → HasDtor A
  | .tensor A B, h => by
      simp only [dtorB, Bool.and_eq_true] at h
      exact .tensor (dtorB_sound A h.1) (dtorB_sound B h.2)
  | .sum A B, h => by
      simp only [dtorB, Bool.and_eq_true] at h
      exact .sum (dtorB_sound A h.1) (dtorB_sound B h.2)
  | .ref A, h => .ref (dtorB_sound A (by simpa [dtorB] using h))
  | .tvar _, h => by simp [dtorB] at h
  | .box _ A, h => .box (dtorB_sound A (by simpa [dtorB] using h))
  | .mu A, h => by
      simp only [dtorB, Bool.false_and, Bool.false_eq_true, if_false, Bool.and_eq_true] at h
      obtain ⟨h₁, h₂, h₃⟩ := dtorB_soundA A h.2 [A]
      exact .mu ((BoCa.Fig16.LogRel.Core.FoldP.pBodyB_iff A).mp h.1) h₁ h₂ h₃
  | .thunk (.amp _ (.ret .unit)), _ => .close
  | .thunk (.nu (.amp C (.ret R))), h => by
      simp only [dtorB, Bool.and_eq_true] at h
      exact .nu (CTy.nuOkB_sound _ h.1.1) (VTy.clB_sound 0 R h.1.2) (dtorB_sound R h.2)
  | .thunk (.nu (.ret _)), h | .thunk (.nu (.arr _ _)), h | .thunk (.nu .top), h
  | .thunk (.nu (.all _ _ _)), h | .thunk (.nu (.nu _)), h
  | .thunk (.nu (.amp _ (.arr _ _))), h | .thunk (.nu (.amp _ (.amp _ _))), h
  | .thunk (.nu (.amp _ .top)), h | .thunk (.nu (.amp _ (.all _ _ _))), h
  | .thunk (.nu (.amp _ (.nu _))), h => by simp [dtorB] at h
  | .thunk (.ret _), h | .thunk (.arr _ _), h | .thunk .top, h
  | .thunk (.all _ _ _), h => by simp [dtorB] at h
  | .thunk (.amp _ (.ret (.tensor _ _))), h | .thunk (.amp _ (.ret .zero)), h
  | .thunk (.amp _ (.ret (.sum _ _))), h | .thunk (.amp _ (.ret (.thunk _))), h
  | .thunk (.amp _ (.ret (.ref _))), h | .thunk (.amp _ (.ret (.imm _ _))), h
  | .thunk (.amp _ (.ret (.mut _ _))), h | .thunk (.amp _ (.ret (.box _ _))), h
  | .thunk (.amp _ (.ret (.bang _))), h | .thunk (.amp _ (.ret .unk)), h
  | .thunk (.amp _ (.ret (.tvar _))), h | .thunk (.amp _ (.ret (.mu _))), h
  | .thunk (.amp _ (.ret (.int _))), h | .thunk (.amp _ (.ret (.fam _))), h
  | .thunk (.amp _ (.ret (.opq _))), h
  | .thunk (.amp _ (.arr _ _)), h
  | .thunk (.amp _ (.amp _ _)), h | .thunk (.amp _ .top), h
  | .thunk (.amp _ (.all _ _ _)), h | .thunk (.amp _ (.nu _)), h => by simp [dtorB] at h
  | .unit, _ => .unit
  | .zero, _ => .zero
  | .int _, _ => .int
  | .opq _, h => by simp [dtorB] at h
  | .unk, _ => .unk
  | .bang _, _ => .bang
  | .imm _ _, _ => .imm
  | .mut _ _, _ => .mut
  | .fam (.ref A), h => .array (dtorB_sound A (by simpa [dtorB] using h))
  | .fam (.imm _ _), _ => .arrayImm
  | .fam (.mut _ _), _ => .arrayMut
  | .fam .unit, h | .fam (.tensor _ _), h | .fam .zero, h | .fam (.sum _ _), h
  | .fam (.thunk _), h | .fam (.box _ _), h
  | .fam (.bang _), h | .fam .unk, h | .fam (.tvar _), h | .fam (.mu _), h
  | .fam (.int _), h | .fam (.fam _), h => by simp [dtorB] at h

/-- **`dtorB true` is sound for `AlgDtor`.** -/
theorem dtorB_soundA : ∀ (A : CVTy), dtorB true A = true → ∀ Bs, AlgDtor Bs A
  | .tensor A B, h, Bs => by
      by_cases hc : BoCa.Fig16.LogRel.Core.FoldP.clB 0 (.tensor A B) = true
      · exact algDtor_closed hc (dtorB_sound _ (by rwa [← dtorB_closed _ hc])) Bs
      · simp only [dtorB, Bool.and_eq_true] at h
        obtain ⟨a₁, a₂, a₃⟩ := dtorB_soundA A h.1 Bs
        obtain ⟨b₁, b₂, b₃⟩ := dtorB_soundA B h.2 Bs
        refine ⟨?_, fun B' Bs' hm => ?_, fun Bs' S hm => ?_⟩
        · simp only [BoCa.Fig16.LogRel.Core.FoldP.resO, if_neg hc]; exact .tensor a₁ b₁
        · simp only [BoCa.Fig16.LogRel.Core.FoldP.keysIn, List.mem_append] at hm
          exact hm.elim (a₂ B' Bs') (b₂ B' Bs')
        · simp only [BoCa.Fig16.LogRel.Core.FoldP.keysIn, List.mem_append] at hm
          exact hm.elim (a₃ Bs' S) (b₃ Bs' S)
  | .sum A B, h, Bs => by
      by_cases hc : BoCa.Fig16.LogRel.Core.FoldP.clB 0 (.sum A B) = true
      · exact algDtor_closed hc (dtorB_sound _ (by rwa [← dtorB_closed _ hc])) Bs
      · simp only [dtorB, Bool.and_eq_true] at h
        obtain ⟨a₁, a₂, a₃⟩ := dtorB_soundA A h.1 Bs
        obtain ⟨b₁, b₂, b₃⟩ := dtorB_soundA B h.2 Bs
        refine ⟨?_, fun B' Bs' hm => ?_, fun Bs' S hm => ?_⟩
        · simp only [BoCa.Fig16.LogRel.Core.FoldP.resO, if_neg hc]; exact .sum a₁ b₁
        · simp only [BoCa.Fig16.LogRel.Core.FoldP.keysIn, List.mem_append] at hm
          exact hm.elim (a₂ B' Bs') (b₂ B' Bs')
        · simp only [BoCa.Fig16.LogRel.Core.FoldP.keysIn, List.mem_append] at hm
          exact hm.elim (a₃ Bs' S) (b₃ Bs' S)
  | .ref A, h, Bs => by
      by_cases hc : BoCa.Fig16.LogRel.Core.FoldP.clB 0 A = true
      · exact algDtor_closed (A := .ref A) hc
          (dtorB_sound _ (by rwa [← dtorB_closed (.ref A) hc])) Bs
      · simp only [dtorB, hc, Bool.not_false, Bool.and_self, if_true] at h
        obtain ⟨a₁, a₂, a₃⟩ := dtorB_soundA A h Bs
        refine ⟨?_, fun B' Bs' hm => a₂ B' Bs' hm, fun Bs' S hm => a₃ Bs' S hm⟩
        simp only [BoCa.Fig16.LogRel.Core.FoldP.resO, if_neg hc]; exact a₁
  | .fam (.ref A), h, Bs => by
      by_cases hc : BoCa.Fig16.LogRel.Core.FoldP.clB 0 A = true
      · exact algDtor_closed (A := .fam (.ref A)) hc
          (dtorB_sound _ (by rwa [← dtorB_closed (.fam (.ref A)) hc])) Bs
      · simp only [dtorB, hc, Bool.not_false, Bool.and_self, if_true] at h
        obtain ⟨a₁, a₂, a₃⟩ := dtorB_soundA A h Bs
        refine ⟨?_, fun B' Bs' hm => ?_, fun Bs' S hm => ?_⟩
        · simp only [BoCa.Fig16.LogRel.Core.FoldP.resO, if_neg hc]; exact .unit
        · simp only [BoCa.Fig16.LogRel.Core.FoldP.keysIn, if_neg hc, List.mem_cons,
            reduceCtorEq, false_or] at hm
          exact a₂ B' Bs' hm
        · simp only [BoCa.Fig16.LogRel.Core.FoldP.keysIn, if_neg hc, List.mem_cons,
            BoCa.Fig16.LogRel.Core.FoldP.Bnd.arr.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩ | hm
          · exact a₁
          · exact a₃ Bs' S hm
  | .mu A, h, Bs => by
      by_cases hc : BoCa.Fig16.LogRel.Core.FoldP.clB 0 (.mu A) = true
      · exact algDtor_closed hc (dtorB_sound _ (by rwa [← dtorB_closed _ hc])) Bs
      · simp only [dtorB, hc, Bool.not_false, Bool.and_self, if_true] at h
        obtain ⟨a₁, a₂, a₃⟩ := dtorB_soundA A h (A :: Bs)
        refine ⟨?_, fun B' Bs' hm => ?_, fun Bs' S hm => ?_⟩
        · simp only [BoCa.Fig16.LogRel.Core.FoldP.resO, if_neg hc]; exact .unit
        · simp only [BoCa.Fig16.LogRel.Core.FoldP.keysIn, if_neg hc, List.mem_cons,
            BoCa.Fig16.LogRel.Core.FoldP.Bnd.mu.injEq, List.cons.injEq] at hm
          rcases hm with ⟨rfl, rfl⟩ | hm
          · exact a₁
          · exact a₂ B' Bs' hm
        · simp only [BoCa.Fig16.LogRel.Core.FoldP.keysIn, if_neg hc, List.mem_cons,
            reduceCtorEq, false_or] at hm
          exact a₃ Bs' S hm
  | .tvar _, _, Bs => by
      refine ⟨by simp [BoCa.Fig16.LogRel.Core.FoldP.resO, dtorAlgs]; exact .unit,
        fun _ _ hm => by simp [BoCa.Fig16.LogRel.Core.FoldP.keysIn] at hm,
        fun _ _ hm => by simp [BoCa.Fig16.LogRel.Core.FoldP.keysIn] at hm⟩
  | .box a A, h, Bs => algDtorLeaf (.box a A) (dtorB_sound _ h) Bs
  | .thunk (.amp C (.ret .unit)), _, Bs => algDtorLeaf (.thunk (.amp C (.ret .unit))) .close Bs
  | .thunk (.nu (.amp C (.ret R))), h, Bs => by
      simp only [dtorB, Bool.and_eq_true] at h
      exact algDtorLeaf _ (.nu (CTy.nuOkB_sound _ h.1.1) (VTy.clB_sound 0 R h.1.2) (dtorB_sound R h.2)) Bs
  | .thunk (.nu (.ret _)), h, _ | .thunk (.nu (.arr _ _)), h, _ | .thunk (.nu .top), h, _
  | .thunk (.nu (.all _ _ _)), h, _ | .thunk (.nu (.nu _)), h, _
  | .thunk (.nu (.amp _ (.arr _ _))), h, _ | .thunk (.nu (.amp _ (.amp _ _))), h, _
  | .thunk (.nu (.amp _ .top)), h, _ | .thunk (.nu (.amp _ (.all _ _ _))), h, _
  | .thunk (.nu (.amp _ (.nu _))), h, _ => by simp [dtorB] at h
  | .thunk (.ret _), h, _ | .thunk (.arr _ _), h, _ | .thunk .top, h, _
  | .thunk (.all _ _ _), h, _ => by simp [dtorB] at h
  | .thunk (.amp _ (.ret (.tensor _ _))), h, _ | .thunk (.amp _ (.ret .zero)), h, _
  | .thunk (.amp _ (.ret (.sum _ _))), h, _ | .thunk (.amp _ (.ret (.thunk _))), h, _
  | .thunk (.amp _ (.ret (.ref _))), h, _ | .thunk (.amp _ (.ret (.imm _ _))), h, _
  | .thunk (.amp _ (.ret (.mut _ _))), h, _ | .thunk (.amp _ (.ret (.box _ _))), h, _
  | .thunk (.amp _ (.ret (.bang _))), h, _ | .thunk (.amp _ (.ret .unk)), h, _
  | .thunk (.amp _ (.ret (.tvar _))), h, _ | .thunk (.amp _ (.ret (.mu _))), h, _
  | .thunk (.amp _ (.ret (.int _))), h, _ | .thunk (.amp _ (.ret (.fam _))), h, _
  | .thunk (.amp _ (.ret (.opq _))), h, _
  | .thunk (.amp _ (.arr _ _)), h, _
  | .thunk (.amp _ (.amp _ _)), h, _ | .thunk (.amp _ .top), h, _
  | .thunk (.amp _ (.all _ _ _)), h, _ | .thunk (.amp _ (.nu _)), h, _ => by simp [dtorB] at h
  | .unit, _, Bs => algDtorLeaf .unit .unit Bs
  | .zero, _, Bs => algDtorLeaf .zero .zero Bs
  | .int w, _, Bs => algDtorLeaf (.int w) .int Bs
  | .unk, _, Bs => algDtorLeaf .unk .unk Bs
  | .bang A, _, Bs => algDtorLeaf (.bang A) .bang Bs
  | .imm a A, _, Bs => algDtorLeaf (.imm a A) .imm Bs
  | .mut a A, _, Bs => algDtorLeaf (.mut a A) .mut Bs
  | .opq _, h, _ => by simp [dtorB] at h
  | .fam (.imm a A), _, Bs => algDtorLeaf (.fam (.imm a A)) .arrayImm Bs
  | .fam (.mut a A), _, Bs => algDtorLeaf (.fam (.mut a A)) .arrayMut Bs
  | .fam .unit, h, _ | .fam (.tensor _ _), h, _ | .fam .zero, h, _ | .fam (.sum _ _), h, _
  | .fam (.thunk _), h, _ | .fam (.box _ _), h, _
  | .fam (.bang _), h, _ | .fam .unk, h, _ | .fam (.tvar _), h, _ | .fam (.mu _), h, _
  | .fam (.int _), h, _ | .fam (.fam _), h, _ | .fam (.opq _), h, _ => by simp [dtorB] at h
end

/-- `A` has a destructor. -/
def hasDtorB (A : CVTy) : Bool := dtorB false A

theorem hasDtorB_sound {A : CVTy} (h : hasDtorB A = true) : HasDtor A := dtorB_sound A h

open BoCa.Fig16.LogRel.Core.FoldP (clB keysIn resO resO_leaf pBodyB_iff Bnd Stack) in
mutual
/-- **`dtorB false` is complete for `HasDtor`.** -/
theorem dtorB_complete : ∀ A : CVTy, HasDtor A → dtorB false A = true
  | .tensor A B, h => by
      cases h with
      | tensor h₁ h₂ => simp [dtorB, dtorB_complete A h₁, dtorB_complete B h₂]
  | .sum A B, h => by
      cases h with
      | sum h₁ h₂ => simp [dtorB, dtorB_complete A h₁, dtorB_complete B h₂]
  | .ref A, h => by
      cases h with
      | ref h => simpa [dtorB] using dtorB_complete A h
  | .tvar _, h => by cases h
  | .box _ A, h => by
      cases h with
      | box h => simpa [dtorB] using dtorB_complete A h
  | .mu A, h => by
      cases h with
      | mu hP h₁ h₂ h₃ =>
          simp only [dtorB, Bool.false_and, Bool.false_eq_true, if_false, Bool.and_eq_true]
          exact ⟨(pBodyB_iff A).mpr hP, dtorB_completeA A [A] ⟨h₁, h₂, h₃⟩⟩
  | .thunk (.amp _ (.ret .unit)), _ => rfl
  | .thunk (.nu (.amp C (.ret R))), h => by
      cases h with
      | nu hC hRc h =>
          simp [dtorB, CTy.nuOkB_complete _ hC, VTy.clB_complete 0 R hRc, dtorB_complete R h]
  | .thunk (.nu (.ret _)), h | .thunk (.nu (.arr _ _)), h | .thunk (.nu .top), h
  | .thunk (.nu (.all _ _ _)), h | .thunk (.nu (.nu _)), h | .thunk (.nu (.eff _ _ _ _ _ _ _ _)), h
  | .thunk (.nu (.amp _ (.arr _ _))), h | .thunk (.nu (.amp _ (.amp _ _))), h
  | .thunk (.nu (.amp _ .top)), h | .thunk (.nu (.amp _ (.all _ _ _))), h
  | .thunk (.nu (.amp _ (.nu _))), h | .thunk (.nu (.amp _ (.eff _ _ _ _ _ _ _ _))), h
  | .thunk (.ret _), h | .thunk (.arr _ _), h | .thunk .top, h
  | .thunk (.all _ _ _), h | .thunk (.eff _ _ _ _ _ _ _ _), h
  | .thunk (.amp _ (.ret (.tensor _ _))), h | .thunk (.amp _ (.ret .zero)), h
  | .thunk (.amp _ (.ret (.sum _ _))), h | .thunk (.amp _ (.ret (.thunk _))), h
  | .thunk (.amp _ (.ret (.ref _))), h | .thunk (.amp _ (.ret (.imm _ _))), h
  | .thunk (.amp _ (.ret (.mut _ _))), h | .thunk (.amp _ (.ret (.box _ _))), h
  | .thunk (.amp _ (.ret (.bang _))), h | .thunk (.amp _ (.ret .unk)), h
  | .thunk (.amp _ (.ret (.tvar _))), h | .thunk (.amp _ (.ret (.mu _))), h
  | .thunk (.amp _ (.ret (.int _))), h | .thunk (.amp _ (.ret (.fam _))), h
  | .thunk (.amp _ (.ret (.opq _))), h
  | .thunk (.amp _ (.arr _ _)), h
  | .thunk (.amp _ (.amp _ _)), h | .thunk (.amp _ .top), h
  | .thunk (.amp _ (.all _ _ _)), h | .thunk (.amp _ (.nu _)), h
  | .thunk (.amp _ (.eff _ _ _ _ _ _ _ _)), h => by cases h
  | .unit, _ | .zero, _ | .int _, _ | .unk, _ | .bang _, _ | .imm _ _, _ | .mut _ _, _ => rfl
  | .opq _, h => by cases h
  | .fam (.ref A), h => by
      cases h with
      | array h => simpa [dtorB] using dtorB_complete A h
  | .fam (.imm _ _), _ | .fam (.mut _ _), _ => rfl
  | .fam .unit, h | .fam (.tensor _ _), h | .fam .zero, h | .fam (.sum _ _), h
  | .fam (.thunk _), h | .fam (.box _ _), h
  | .fam (.bang _), h | .fam .unk, h | .fam (.tvar _), h | .fam (.mu _), h
  | .fam (.int _), h | .fam (.fam _), h | .fam (.opq _), h => by cases h

/-- **`dtorB true` is complete for `AlgDtor`**, at every stack: the recursion carries the stack
as `AlgDtor` does, `A :: Bs` under a `μ` that is not closed. -/
theorem dtorB_completeA : ∀ (A : CVTy) (Bs : Stack), AlgDtor Bs A → dtorB true A = true
  | .tensor A B, Bs, h => by
      by_cases hc : clB 0 (.tensor A B) = true
      · have h₁ := h.1
        rw [resO_leaf dtorAlgs Bs hc] at h₁
        rw [dtorB_closed _ hc]
        exact dtorB_complete _ h₁
      · obtain ⟨h₁, h₂, h₃⟩ := h
        simp only [BoCa.Fig16.LogRel.Core.FoldP.resO, if_neg hc] at h₁
        cases h₁ with
        | tensor ha hb =>
          have hA : AlgDtor Bs A := ⟨ha, fun B' Bs' hm => h₂ B' Bs' (by
              simp only [keysIn, List.mem_append]; exact .inl hm),
            fun Bs' S hm => h₃ Bs' S (by simp only [keysIn, List.mem_append]; exact .inl hm)⟩
          have hB : AlgDtor Bs B := ⟨hb, fun B' Bs' hm => h₂ B' Bs' (by
              simp only [keysIn, List.mem_append]; exact .inr hm),
            fun Bs' S hm => h₃ Bs' S (by simp only [keysIn, List.mem_append]; exact .inr hm)⟩
          simp [dtorB, dtorB_completeA A Bs hA, dtorB_completeA B Bs hB]
  | .sum A B, Bs, h => by
      by_cases hc : clB 0 (.sum A B) = true
      · have h₁ := h.1
        rw [resO_leaf dtorAlgs Bs hc] at h₁
        rw [dtorB_closed _ hc]
        exact dtorB_complete _ h₁
      · obtain ⟨h₁, h₂, h₃⟩ := h
        simp only [BoCa.Fig16.LogRel.Core.FoldP.resO, if_neg hc] at h₁
        cases h₁ with
        | sum ha hb =>
          have hA : AlgDtor Bs A := ⟨ha, fun B' Bs' hm => h₂ B' Bs' (by
              simp only [keysIn, List.mem_append]; exact .inl hm),
            fun Bs' S hm => h₃ Bs' S (by simp only [keysIn, List.mem_append]; exact .inl hm)⟩
          have hB : AlgDtor Bs B := ⟨hb, fun B' Bs' hm => h₂ B' Bs' (by
              simp only [keysIn, List.mem_append]; exact .inr hm),
            fun Bs' S hm => h₃ Bs' S (by simp only [keysIn, List.mem_append]; exact .inr hm)⟩
          simp [dtorB, dtorB_completeA A Bs hA, dtorB_completeA B Bs hB]
  | .ref A, Bs, h => by
      by_cases hc : clB 0 A = true
      · have h₁ := h.1
        rw [resO_leaf dtorAlgs Bs (A := .ref A) hc] at h₁
        cases h₁ with
        | ref h₁ => simp [dtorB, hc, dtorB_complete A h₁]
      · obtain ⟨h₁, h₂, h₃⟩ := h
        simp only [BoCa.Fig16.LogRel.Core.FoldP.resO, if_neg hc] at h₁
        simp only [dtorB, hc, Bool.not_false, Bool.and_self, if_true]
        exact dtorB_completeA A Bs ⟨h₁, h₂, h₃⟩
  | .tvar _, _, _ => rfl
  | .box a A, Bs, h => by
      have h₁ := h.1
      simp only [BoCa.Fig16.LogRel.Core.FoldP.resO] at h₁
      cases h₁ with
      | box h₁ => simpa [dtorB] using dtorB_complete A h₁
  | .mu A, Bs, h => by
      by_cases hc : clB 0 (.mu A) = true
      · have h₁ := h.1
        rw [resO_leaf dtorAlgs Bs hc] at h₁
        cases h₁ with
        | mu hP h₁ h₂ h₃ =>
            simp only [dtorB, hc, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false,
              Bool.and_eq_true]
            exact ⟨(pBodyB_iff A).mpr hP, dtorB_completeA A [A] ⟨h₁, h₂, h₃⟩⟩
      · obtain ⟨-, h₂, h₃⟩ := h
        have hroot : HasDtor (resO dtorAlgs (A :: Bs) A) :=
          h₂ A Bs (by simp [keysIn, hc])
        have hA : AlgDtor (A :: Bs) A := ⟨hroot,
          fun B' Bs' hm => h₂ B' Bs' (by simp only [keysIn, if_neg hc]; exact .tail _ hm),
          fun Bs' S hm => h₃ Bs' S (by simp only [keysIn, if_neg hc]; exact .tail _ hm)⟩
        simp only [dtorB, hc, Bool.not_false, Bool.and_self, if_true]
        exact dtorB_completeA A (A :: Bs) hA
  | .thunk (.amp _ (.ret .unit)), _, _ => rfl
  | .thunk (.nu (.amp C (.ret R))), _, h => by
      have h₁ := h.1
      simp only [BoCa.Fig16.LogRel.Core.FoldP.resO] at h₁
      cases h₁ with
      | nu hC hRc h =>
          simp [dtorB, CTy.nuOkB_complete _ hC, VTy.clB_complete 0 R hRc, dtorB_complete R h]
  | .thunk (.nu (.ret _)), _, h | .thunk (.nu (.arr _ _)), _, h | .thunk (.nu .top), _, h
  | .thunk (.nu (.all _ _ _)), _, h | .thunk (.nu (.nu _)), _, h
  | .thunk (.nu (.eff _ _ _ _ _ _ _ _)), _, h
  | .thunk (.nu (.amp _ (.arr _ _))), _, h | .thunk (.nu (.amp _ (.amp _ _))), _, h
  | .thunk (.nu (.amp _ .top)), _, h | .thunk (.nu (.amp _ (.all _ _ _))), _, h
  | .thunk (.nu (.amp _ (.nu _))), _, h | .thunk (.nu (.amp _ (.eff _ _ _ _ _ _ _ _))), _, h
  | .thunk (.ret _), _, h | .thunk (.arr _ _), _, h | .thunk .top, _, h
  | .thunk (.all _ _ _), _, h | .thunk (.eff _ _ _ _ _ _ _ _), _, h
  | .thunk (.amp _ (.ret (.tensor _ _))), _, h | .thunk (.amp _ (.ret .zero)), _, h
  | .thunk (.amp _ (.ret (.sum _ _))), _, h | .thunk (.amp _ (.ret (.thunk _))), _, h
  | .thunk (.amp _ (.ret (.ref _))), _, h | .thunk (.amp _ (.ret (.imm _ _))), _, h
  | .thunk (.amp _ (.ret (.mut _ _))), _, h | .thunk (.amp _ (.ret (.box _ _))), _, h
  | .thunk (.amp _ (.ret (.bang _))), _, h | .thunk (.amp _ (.ret .unk)), _, h
  | .thunk (.amp _ (.ret (.tvar _))), _, h | .thunk (.amp _ (.ret (.mu _))), _, h
  | .thunk (.amp _ (.ret (.int _))), _, h | .thunk (.amp _ (.ret (.fam _))), _, h
  | .thunk (.amp _ (.ret (.opq _))), _, h
  | .thunk (.amp _ (.arr _ _)), _, h
  | .thunk (.amp _ (.amp _ _)), _, h | .thunk (.amp _ .top), _, h
  | .thunk (.amp _ (.all _ _ _)), _, h | .thunk (.amp _ (.nu _)), _, h
  | .thunk (.amp _ (.eff _ _ _ _ _ _ _ _)), _, h => by
      have h₁ := h.1
      simp only [BoCa.Fig16.LogRel.Core.FoldP.resO] at h₁
      cases h₁
  | .unit, _, _ | .zero, _, _ | .int _, _, _ | .unk, _, _ | .bang _, _, _ | .imm _ _, _, _
  | .mut _ _, _, _ => rfl
  | .opq _, _, h => by
      have h₁ := h.1
      simp only [BoCa.Fig16.LogRel.Core.FoldP.resO] at h₁
      cases h₁
  | .fam (.ref A), Bs, h => by
      by_cases hc : clB 0 A = true
      · have h₁ := h.1
        rw [resO_leaf dtorAlgs Bs (A := .fam (.ref A)) hc] at h₁
        cases h₁ with
        | array h₁ => simp [dtorB, hc, dtorB_complete A h₁]
      · obtain ⟨-, h₂, h₃⟩ := h
        have hS : HasDtor (resO dtorAlgs Bs A) := h₃ Bs A (by simp [keysIn, hc])
        have hA : AlgDtor Bs A := ⟨hS,
          fun B' Bs' hm => h₂ B' Bs' (by simp only [keysIn, if_neg hc]; exact .tail _ hm),
          fun Bs' S hm => h₃ Bs' S (by simp only [keysIn, if_neg hc]; exact .tail _ hm)⟩
        simp only [dtorB, hc, Bool.not_false, Bool.and_self, if_true]
        exact dtorB_completeA A Bs hA
  | .fam (.imm _ _), _, _ | .fam (.mut _ _), _, _ => rfl
  | .fam .unit, _, h | .fam (.tensor _ _), _, h | .fam .zero, _, h | .fam (.sum _ _), _, h
  | .fam (.thunk _), _, h | .fam (.box _ _), _, h
  | .fam (.bang _), _, h | .fam .unk, _, h | .fam (.tvar _), _, h | .fam (.mu _), _, h
  | .fam (.int _), _, h | .fam (.fam _), _, h | .fam (.opq _), _, h => by
      have h₁ := h.1
      simp only [BoCa.Fig16.LogRel.Core.FoldP.resO] at h₁
      cases h₁
end

/-- **`hasDtorB` decides `HasDtor`.**  `[spec §12]` -/
theorem hasDtorB_iff (A : CVTy) : hasDtorB A = true ↔ HasDtor A :=
  ⟨dtorB_sound A, dtorB_complete A⟩

instance : DecidablePred HasDtor := fun A => decidable_of_iff _ (hasDtorB_iff A)

instance : DecidablePred DerivedDrop := fun A =>
  inferInstanceAs (Decidable (¬ A.Persistent ∧ HasDtor A))


/-- What the checker knows at a point besides `Δ` and the slot types `T`: the declarations in
scope, the name of each slot (a dead binder has none), the lifetime names, a `def`'s type
parameters, and the slots **owed** to the current tail position (SPEC §12): variables with a
destructor that the computation being checked must consume on every path, the checker dropping
them where it does not. `own` is indexed like `vars`; a slot past its end is not owed. -/
structure Env where
  scope : Scope
  vars : List (Option String)
  lenv : List (String × LifeVar)
  tps : List (String × CVTy)
  own : List Bool
  /-- The number of extern slots, at the end of `vars` (SPEC §11). -/
  nExt : Nat
  /-- The current row (SPEC §19): the row of the returner chain `F_Σ B` the computation being
  checked has, set where a computation is checked against one; `none` in a value, where a
  computation is synthesized with no type expected. `[spec §19]` -/
  row : Option CRow

/-- The depth bound for elaborating a type. -/
def tyFuel : Nat := 65536

def Env.tyEnv (E : Env) (Δ : LifeCtx) : TyEnv := ⟨E.scope, Δ, Δ, E.lenv, [], [], E.tps, []⟩
def Env.elabV (E : Env) (Δ : LifeCtx) (A : VTy) : Except Error CVTy := Frontend.Check.elabV tyFuel (E.tyEnv Δ) A
def Env.elabC (E : Env) (Δ : LifeCtx) (C : CTy) : Except Error CCTy := Frontend.Check.elabC tyFuel (E.tyEnv Δ) C
def Env.elabS (E : Env) (Δ : LifeCtx) (σ : Shape) : Except Error CShape :=
  Frontend.Check.elabS tyFuel (E.tyEnv Δ) σ
def Env.elabL (E : Env) (Δ : LifeCtx) (a : Life) : Except Error CLife := elabLife Δ E.lenv a
def Env.elabRow (E : Env) (Δ : LifeCtx) (sp : Span) (r : Row) : Except Error CRow :=
  Frontend.Check.elabRow tyFuel (E.tyEnv Δ) sp r

/-- Types and lifetimes in messages, with the lifetime names in scope. -/
def Env.ppV (E : Env) (A : CVTy) : String := Frontend.Check.ppV E.lenv 0 0 A
def Env.ppC (E : Env) (C : CCTy) : String := Frontend.Check.ppC E.lenv 0 C
def Env.ppL (E : Env) (a : CLife) : String := ppLifeP E.lenv 1 a

/-! ### Rows  `[spec §19]` -/

/-- `C` as a returner chain `F_Σ A`: its row and answer. -/
def effRow? : CCTy → Option (CRow × CVTy)
  | .ret A => some ([], A)
  | .eff n i q A B fin rc C => (effRow? C).map fun (S, R) => (⟨n, i, q, A, B, fin, rc⟩ :: S, R)
  | _ => none

/-- The environment of a computation checked against `C`: the row of `C` when it is a returner
chain.  `[spec §19]` -/
def Env.atC (E : Env) (C : CCTy) : Env :=
  match effRow? C with
  | some (S, _) => { E with row := some S }
  | none => E

/-- A value: nothing owed, and no row. -/
def Env.forVal (E : Env) : Env := { E with own := [], row := none }

def ppRow (E : Env) (S : CRow) : String :=
  "[" ++ ", ".intercalate (S.map fun o =>
    s!"{o.n}.{o.i} {qualStr o.q} {E.ppV o.A} ~> {E.ppV o.B}") ++ "]"

theorem Row.cancels_of_unr {S : CRow} (h : S.Unr) : S.Cancels := by
  obtain ⟨o, ho, hq⟩ := h
  exact ⟨o, ho, by rw [hq]; decide⟩

/-- The operation `k.i` of the current row, found as itself. -/
def findOp (E : Env) (sp : Span) (what : String) (k i : Nat) :
    Except Error (Σ S : CRow, {o : COpSig // BoCa.Fig16.LogRel.Core.Row.find S o.n o.i = some o}) :=
  match E.row with
  | none => throw ⟨sp, s!"`{what}[{k}.{i}]` is not checked at a row: its type is not known " ++
      "to be `F[…] A`; ascribe the computation"⟩
  | some S =>
    if k < 2 ^ 32 ∧ i < 2 ^ 32 then
      match h : BoCa.Fig16.LogRel.Core.Row.find S (UInt32.ofNat k) (UInt32.ofNat i) with
      | some o =>
        have hm := BoCa.Fig16.LogRel.Core.Row.find_mem h
        pure ⟨S, o, by rw [hm.2.1, hm.2.2]; exact h⟩
      | none => throw ⟨sp, s!"the operation {k}.{i} is not in the row `{ppRow E S}`"⟩
    else throw ⟨sp, s!"the operation {k}.{i}: a name and an index are below 2^32"⟩

/-- `κ`'s type `kTy S R q B`, read back: the qualifier and the operation's answer. -/
def kRead : CVTy → Option (CQual × CVTy)
  | .thunk (.amp (.arr B _) .top) => some (.lin, B)
  | .thunk (.amp (.arr B _) _) => some (.cancel, B)
  | .bang (.thunk (.amp (.arr B _) _)) => some (.unr, B)
  | _ => none

/-- The operations a clause's type may be the type of: a control operation `A ↠^q B` (its
argument `A ⊗ κ`), then an abortive one `A ↠^cancel 0`. -/
def clauseCands : CVTy → List (CQual × CVTy × CVTy)
  | .bang (.thunk (.arr (.tensor A K) _)) =>
      (match kRead K with | some (q, B) => [(q, A, B)] | none => []) ++
        [(.cancel, .tensor A K, .zero)]
  | .bang (.thunk (.arr A _)) => [(.cancel, A, .zero)]
  | _ => []

/-- The first candidate whose clause type is `c`. -/
def firstClause (S : CRow) (R c : CVTy) :
    List (CQual × CVTy × CVTy) → Option {e // BoCa.Fig16.LogRel.Core.clauseTy S R e = c}
  | [] => none
  | e :: es => if h : BoCa.Fig16.LogRel.Core.clauseTy S R e = c then some ⟨e, h⟩
      else firstClause S R c es

/-- The operations `E` of a handler read back from the type of its clauses' tuple, with
`clausesTy S R E` that type. An abortive operation is read as cancellable: `cancel` and `unr` give
it the same clause type. -/
def clausesRead (S : CRow) (R : CVTy) :
    (Tc : CVTy) → Option {E // BoCa.Fig16.LogRel.Core.clausesTy S R E = Tc}
  | .unit => some ⟨[], rfl⟩
  | .tensor c rest => do
    let ⟨e, he⟩ ← firstClause S R c (clauseCands c)
    let ⟨E, hE⟩ ← clausesRead S R rest
    pure ⟨e :: E, by subst he hE; rfl⟩
  | _ => none

/-- The operations a clause's type under BOXED-κ may be the type of (`[spec §28]`): a control
operation `A ↠^q B` (its argument `A ⊗ [@d] κ`), then an abortive one. -/
def clauseCandsB : CVTy → List (CQual × CVTy × CVTy)
  | .bang (.thunk (.arr (.tensor A (.box d K)) _)) =>
      (match kRead K with | some (q, B) => [(q, A, B)] | none => []) ++
        [(.cancel, .tensor A (.box d K), .zero)]
  | .bang (.thunk (.arr A _)) => [(.cancel, A, .zero)]
  | _ => []

/-- The first candidate whose clause type under BOXED-κ at `@d` is `c`. -/
def firstClauseB (S : CRow) (R : CVTy) (d : CLife) (c : CVTy) :
    List (CQual × CVTy × CVTy) → Option {e // BoCa.Fig16.LogRel.Core.clauseTyB S R d e = c}
  | [] => none
  | e :: es => if h : BoCa.Fig16.LogRel.Core.clauseTyB S R d e = c then some ⟨e, h⟩
      else firstClauseB S R d c es

/-- The operations `E` of a handler whose clauses receive `κ` boxed at `@d`, read back from the
type of its clauses' tuple, with `clausesTyB S R d E` that type.  `[spec §28]` -/
def clausesReadB (S : CRow) (R : CVTy) (d : CLife) :
    (Tc : CVTy) → Option {E // BoCa.Fig16.LogRel.Core.clausesTyB S R d E = Tc}
  | .unit => some ⟨[], rfl⟩
  | .tensor c rest => do
    let ⟨e, he⟩ ← firstClauseB S R d c (clauseCandsB c)
    let ⟨E, hE⟩ ← clausesReadB S R d rest
    pure ⟨e :: E, by subst he hE; rfl⟩
  | _ => none

/-- The lifetime a clause tuple's type boxes its continuations at: that of its first clause whose
argument is `A ⊗ [@d] κ`, `κ` a continuation's type. -/
def clausesBoxOf : CVTy → Option CLife
  | .tensor (.bang (.thunk (.arr (.tensor _ (.box d K)) _))) rest =>
      if (kRead K).isSome then some d else clausesBoxOf rest
  | .tensor _ rest => clausesBoxOf rest
  | _ => none

/-- A clause tuple's type read as BOXED-κ's: its boxing lifetime, and its operations. Where it reads,
the checker prefers it to `clausesRead`, which would read a clause `!U(A ⊗ [@d] κ ⊸ F_Σ R)` as an
abortive operation's.  `[spec §28]` -/
def clausesReadBoxed (S : CRow) (R : CVTy) (Tc : CVTy) :
    Option (Σ d : CLife, {E // BoCa.Fig16.LogRel.Core.clausesTyB S R d E = Tc}) := do
  let d ← clausesBoxOf Tc
  let r ← clausesReadB S R d Tc
  pure ⟨d, r⟩

/-- `h_ret`'s type `!U(A -o F_S R)` read back. -/
def retRead (Tr : CVTy) :
    Option (Σ' (S : CRow) (A R : CVTy), BoCa.Fig16.LogRel.Core.retTy S A R = Tr) :=
  match Tr with
  | .bang (.thunk (.arr A C)) =>
    match effRow? C with
    | some (S, R) =>
      if h : BoCa.Fig16.LogRel.Core.retTy S A R = .bang (.thunk (.arr A C)) then some ⟨S, A, R, h⟩ else none
    | none => none
  | _ => none

/-! ### Messages -/

def Env.slotName (E : Env) (i : Nat) : String :=
  match E.vars[i]? with
  | some (some x) => s!"`{x}`"
  | _ => "a hidden slot"

/-- The first slot both sides use whose type is not persistent. -/
def firstOverlap : List CVTy → List Bool → List Bool → Option Nat
  | A :: T, a :: as, b :: bs =>
      if a && b && !A.persistent then some 0 else (firstOverlap T as bs).map (· + 1)
  | _, _, _ => none

def Env.slotTy (E : Env) (T : List CVTy) (i : Nat) : String := (T[i]?.map E.ppV).getD "?"

def splitErr (E : Env) (T : List CVTy) (sp : Span) (u₁ u₂ : List Bool) : Error :=
  match firstOverlap T u₁ u₂ with
  | some i => ⟨sp, s!"{E.slotName i} is used twice here, and its type `{E.slotTy T i}` is " ++
      "linear"⟩
  | none => ⟨sp, "internal error: context split"⟩

/-- The first slot `a` uses that `b` neither uses nor absorbs. -/
def firstMissing : List Bool → List Bool → List Bool → Option Nat
  | a :: as, b :: bs, c :: cs => if a && !(b || c) then some 0 else (firstMissing as bs cs).map (· + 1)
  | _, _, _ => none

/-- `B` occurs in `A`. -/
def occursTy (B : CVTy) : CVTy → Bool
  | .tensor X Y => .tensor X Y == B || occursTy B X || occursTy B Y
  | .sum X Y => .sum X Y == B || occursTy B X || occursTy B Y
  | .ref X => .ref X == B || occursTy B X
  | .box a X => .box a X == B || occursTy B X
  | .bang X => .bang X == B || occursTy B X
  | .mu X => .mu X == B || occursTy B X
  | .fam X => .fam X == B || occursTy B X
  | A => A == B

/-- The fix a message names for a value whose type holds a field marked `must_close` (SPEC §42):
the declaration, the field and the function that consumes it. Message text only: the refusal is
the kernel's. -/
def Env.closeHint (E : Env) (A : CVTy) (abort : Bool) : String :=
  let holds (n : String) : Bool := match E.elabV LifeCtx.empty (.name .none n) with
    | .ok N => occursTy N A
    | .error _ => false
  match E.scope.closes.find? (holds ·.1) with
  | some (n, g, f) =>
    let fix := match f with
      | some f => s!"pass it to `{f}`"
      | none => s!"consume it with a `match` on `{n}`"
    let at_ := if abort then " before the computation that may abort, or close it in a `finally`"
      else " before its scope ends"
    s!": `{n}` holds the field `{g}`, marked `must_close`; {fix}{at_}"
  | none => ""

/-- Why slot `i` was not dropped where a path does not consume it. -/
def Env.notDropped (E : Env) (T : List CVTy) (i : Nat) : String :=
  match T[i]? with
  | some A => if hasDtorB A then "" else
      s!", and its type `{E.ppV A}` is linear and has no derived drop" ++ E.closeHint A false
  | none => ""

/-- The two parts of a `case` or a `<,>` do not consume the same variables. -/
def mergeErr (E : Env) (T : List CVTy) (sp : Span) (what₁ what₂ intro : String)
    (u₁ w₁ u₂ w₂ : List Bool) : Error :=
  match firstMissing u₁ u₂ w₂, firstMissing u₂ u₁ w₁ with
  | some i, _ => ⟨sp, s!"{intro}{E.slotName i} is consumed in {what₁} but not in {what₂}" ++
      E.notDropped T i⟩
  | _, some i => ⟨sp, s!"{intro}{E.slotName i} is consumed in {what₂} but not in {what₁}" ++
      E.notDropped T i⟩
  | _, _ => ⟨sp, "internal error: merge"⟩

/-- A binder's variable is neither consumed nor dropped when its scope closes. -/
def unconsumed (E : Env) (sp : Span) (x : String) (A : CVTy) : Error :=
  if hasDtorB A then
    ⟨sp, s!"`{x}` is not consumed in its scope, and it cannot be dropped where its scope ends"⟩
  else ⟨sp, s!"`{x}` is not consumed in its scope, and its type `{E.ppV A}` is linear and " ++
    "has no derived drop" ++ E.closeHint A false⟩

def mismatch (sp : Span) (want got : String) : Error :=
  ⟨sp, s!"type mismatch: expected `{want}`, but this has type `{got}`"⟩

/-! ### Small steps shared by the cases -/

section
variable {Δ : LifeCtx} {T : List CVTy}

def convV (E : Env) (sp : Span) (A : CVTy) : (Σ B : CVTy, Res Δ T (.val B)) → Except Error (Res Δ T (.val A))
  | ⟨B, r⟩ => if h : B = A then pure (h ▸ r) else throw (mismatch sp (E.ppV A) (E.ppV B))

/-- A computation of `D` at `C`: equal, or `F_Σ′ A` within `F_Σ A` by `[sub]` (SPEC §19). -/
def convC (E : Env) (sp : Span) (C : CCTy) : (Σ D : CCTy, Res Δ T (.comp D)) → Except Error (Res Δ T (.comp C))
  | ⟨D, r⟩ =>
    if h : D = C then pure (h ▸ r) else
    match effRow? D, effRow? C with
    | some (S', A'), some (S, _) =>
      if hD : effOf S' A' = D then
        if hC : effOf S A' = C then
          if hle : rowLeB S' S = true then pure (hC ▸ rEffSub (at_ sp) hle (hD ▸ r))
          else throw ⟨sp, s!"type mismatch: expected `{E.ppC C}`, but this has type " ++
            s!"`{E.ppC D}`: its row `{ppRow E S'}` is not within `{ppRow E S}`"⟩
        else throw (mismatch sp (E.ppC C) (E.ppC D))
      else throw (mismatch sp (E.ppC C) (E.ppC D))
    | _, _ => throw (mismatch sp (E.ppC C) (E.ppC D))

def popL {A : CVTy} {P : List Bool → Prop} (E : Env) (sp : Span) (x : String) (F : Fam (A :: T) P) :
    Except Error (Fam T (fun L => P (true :: L))) :=
  match F.popLive with
  | some F' => pure F'
  | none => throw (unconsumed E sp x A)

def popD {A : CVTy} {P : List Bool → Prop} (sp : Span) (F : Fam (A :: T) P) :
    Except Error (Fam T (fun L => P (false :: L))) :=
  match F.popDead with
  | some F' => pure F'
  | none => throw ⟨sp, "internal error: a dead binder is used"⟩

def withPop {j : Jdg} {t : TExpr} {s : CRow} {p : Pins} (sp : Span)
    (F : Fam (withT T) (fun L => TTied p s Δ (mkCtx (withT T) L) t j)) :
    Except Error (Fam T (fun L => TTied p s Δ (BoCa.Fig16.LogRel.Core.withCtx (mkCtx T L)) t j)) :=
  match popWith F with
  | some F' => pure F'
  | none => throw ⟨sp, "internal error: a dead binder is used"⟩

end

/-- The variable bound in slot `i`, if `x` names one. -/
def lookupVar (x : String) : List (Option String) → Option Nat
  | [] => none
  | y :: ys => if y == some x then some 0 else (lookupVar x ys).map (· + 1)

/-- A slot that is not owed: a dead binder. -/
def Env.push (E : Env) (x : Option String) : Env := { E with vars := x :: E.vars, own := false :: E.own }

/-- A binder's live slot `x : A`, owed to its scope when `A` is linear and has a derived drop
(SPEC §12). -/
def Env.pushOwn (E : Env) (x : String) (A : CVTy) : Env :=
  { E with vars := some x :: E.vars, own := (!A.persistent && hasDtorB A) :: E.own }

/-- A binder owes exactly the slot with a derived drop.  `[spec §12]` -/
theorem Env.pushOwn_own (E : Env) (x : String) (A : CVTy) :
    (E.pushOwn x A).own.head? = some (decide (DerivedDrop A)) := by
  simp only [Env.pushOwn, List.head?_cons, Option.some.injEq]
  rw [Bool.eq_iff_iff]
  simp [DerivedDrop, Linear, hasDtorB_iff]

/-- Nothing owed: a value, or a computation that is not in tail position. -/
def Env.clearOwn (E : Env) : Env := { E with own := [] }



/-- What is still owed after the slots `u` are consumed. -/
def Env.minus (E : Env) (u : List Bool) : Env := { E with own := andL E.own (u.map (! ·)) }

/-- The owed slots a computation mentions by name, where the name is not shadowed. -/
def Env.ownIn (E : Env) (p : String → Bool) : Env :=
  { E with own := (List.range E.own.length).map fun i =>
      E.own.getD i false && match E.vars[i]? with
        | some (some x) => lookupVar x E.vars == some i && p x
        | _ => false }

/-- The environment of a `def`'s body at a use: its own scope, no variables or lifetimes of the
use site but the persistent externs (the operations of SPEC §11, which carry no authority; a
capability is not persistent), its type parameters bound. -/
def Env.forDef (E : Env) (T : List CVTy) (d : DefInfo) (tps : List (String × CVTy)) : Env :=
  let n := E.vars.length
  let vars := (List.range n).map fun i =>
    if n ≤ i + E.nExt && (T[i]?.map (·.persistent)).getD false then E.vars.getD i none else none
  ⟨d.scope, vars, [], tps, [], E.nExt, none⟩

def inDef (x : String) (sp : Span) (e : Error) : Error :=
  { e with msg := s!"{e.msg}\n  in the body of `{x}`, used at {sp.start.render}" }

def thunkvLam : String :=
  "the body of `thunkv` must erase to a λ: `fun`, `Fun` or `<M, N>`, possibly under " ++
  "`delay_in`/`delay_out`/`stream_in`/`stream_out` or an ascription (syntax-core §6.4); " ++
  "eta-expand it"

def notBang (E : Env) (T : List CVTy) (sp : Span) : Option Nat → Error
  | some i => ⟨sp, s!"`!thunk` promotes only over `!` types, but {E.slotName i}, of type " ++
      s!"`{E.slotTy T i}`, is used inside"⟩
  | none => ⟨sp, thunkvLam⟩

section
variable {Δ : LifeCtx} {T : List CVTy}

/-! ### Drops (SPEC §12) -/

mutual
/-- `x` occurs free in a value-judged expression. -/
def mentionsV (x : String) : Val → Bool
  | .var _ y | .clone _ y => y == x
  | .defApp .. | .unit _ | .const .. | .sugar .. => false
  | .pair _ V W | .app _ V W => mentionsV x V || mentionsV x W
  | .inl _ V | .inr _ V | .unbang _ V | .boxed _ _ V | .unbox _ V | .sub _ V _ | .roll _ V
  | .unroll _ V | .inst _ V _ | .ascribe _ V _ | .shorten _ _ _ _ V | .mark _ _ V => mentionsV x V
  | .thunk _ M | .thunkv _ M | .bangThunk _ M | .bangThunkv _ M | .run _ M => mentionsC x M
  | .lend _ y _ => y.name == x

/-- `x` occurs free in a computation. -/
def mentionsC (x : String) : Comp → Bool
  | .ret _ V | .absurd _ V => mentionsV x V
  | .bind _ y _ M N => mentionsC x M || (y.name != x && mentionsC x N)
  | .force _ y => y.name == x
  | .lam _ y _ M => y.name != x && mentionsC x M
  | .app _ M y => mentionsC x M || y.name == x
  | .with_ _ M N => mentionsC x M || mentionsC x N
  | .proj _ _ M | .lamL _ _ _ M | .inst _ M _ | .nuIn _ M | .nuOut _ M
  | .ascribe _ M _ => mentionsC x M
  | .top _ => false
  | .letUnit _ V M => mentionsV x V || mentionsC x M
  | .letPair _ y z V M => mentionsV x V || (y.name != x && z.name != x && mentionsC x M)
  | .case _ V y M z N => mentionsV x V || (y.name != x && mentionsC x M) ||
      (z.name != x && mentionsC x N)
  | .loop _ _ src V M N => mentionsV x V || (!src.bound.contains x && mentionsC x M) || mentionsC x N
  | .perform _ _ _ V | .abort _ _ _ V => mentionsV x V
  | .handle _ _ _ hr hc M => mentionsV x hr || mentionsV x hc || mentionsC x M
  | .unwind _ y _ M D N => mentionsC x M || mentionsC x D || (y.name != x && mentionsC x N)
  | .withbor2r _ _ _ _ _ _ p m M => p.name == x || (m.name != x && mentionsC x M)
end

/-- A path's terminal computation: every form except those that pass what is owed on to a tail
position (`x <- M; N`, `let`, `case`, `<M, N>`, `fun`, `Fun`, `nu_in`, an ascription). -/
def _root_.Frontend.Comp.terminal : Comp → Bool
  | .bind .. | .letUnit .. | .letPair .. | .case .. | .with_ .. | .lam .. | .lamL ..
  | .nuIn .. | .ascribe .. | .unwind .. => false
  | _ => true

/-- The slots to drop before a terminal computation: owed, and neither used nor absorbed by it. -/
def owedLeft : List Bool → List Bool → List Bool → Nat → List Nat
  | o :: os, u :: us, w :: ws, i => (if o && !u && !w then [i] else []) ++ owedLeft os us ws (i + 1)
  | _, _, _, _ => []

section
variable {Δ : LifeCtx} {T : List CVTy}

/-- `dtorE A xᵢ; M` for the slot `i`. -/
def dropOne {C : CCTy} (sp : Span) (i : Nat) (r : Res Δ T (.comp C)) :
    Except Error (Res Δ T (.comp C)) :=
  match hi : T[i]? with
  | some A =>
    if hA : hasDtorB A = true then
      if h : overlapOK T (oneL T i) r.F.u = true then
        pure (rDrop (at_ sp) (at_ sp) i A hi (hasDtorB_sound hA)
          (BoCa.Fig16.LogRel.Core.dtorE_closed (hasDtorB_sound hA))
          (BoCa.Fig16.LogRel.Core.dtorE_effFree A) r h)
      else throw ⟨sp, "internal error: a dropped slot is used"⟩
    else throw ⟨sp, "internal error: an owed slot has no destructor"⟩
  | none => throw ⟨sp, "internal error: an owed slot is out of range"⟩

/-- The binders' slots `0 … k − 1` of a scope whose body can leave none of them live, each with a
derived drop, consumed by it at the head of the body (`drop_derives`): the body neither uses such
a slot nor can weaken it, as under `boxed[@a]`, whose context must outlive `@a` (`[]I`), a slot
of `Unk` among them. Such a slot is not owed (an owed one is dropped at the terminal), so its type
is persistent or a borrow, and its drop does nothing observable.  `[spec §12]` -/
def dropStuck {C : CCTy} (sp : Span) (k : Nat) (r : Res Δ T (.comp C)) :
    Except Error (Res Δ T (.comp C)) :=
  (List.range k).foldlM (init := r) fun r i =>
    if !(r.F.u.getD i false) && !(r.F.w.getD i true) && (T[i]?.map hasDtorB).getD false then
      dropOne sp i r
    else pure r

/-- Drop what the terminal computation `r` leaves owed, the lowest index (the most recently
bound variable) first. -/
def dropOwed {C : CCTy} (E : Env) (sp : Span) (r : Res Δ T (.comp C)) :
    Except Error (Res Δ T (.comp C)) :=
  (owedLeft E.own r.F.u r.F.w 0).foldr (fun i acc => do dropOne sp i (← acc)) (pure r)

end

/-- `boxed[@a] V`. -/
def boxIt {A : CVTy} (E : Env) (T : List CVTy) (sp : Span) (a : CLife) (r : Res Δ T (.val A)) :
    Except Error (Res Δ T (.val (.box a A))) :=
  if hwf : a.wf Δ = true then
    if hs : usedSat (outlivesB Δ a) T r.F.u = true then pure (rBoxI (at_ sp) a hwf r hs)
    else match firstBad (outlivesB Δ a) T r.F.u with
      | some i => throw ⟨sp, s!"`boxed[{E.ppL a}]`: {E.slotName i}, of type `{E.slotTy T i}`, " ++
          s!"is used inside, and it cannot be shown to outlive `{E.ppL a}`"⟩
      | none => throw ⟨sp, "internal error: boxed"⟩
  else throw ⟨sp, s!"`boxed[{E.ppL a}]`: the lifetime is not defined here"⟩

/-- `M x`. -/
def appIt {A : CVTy} {C : CCTy} (E : Env) (T : List CVTy) (sp : Span) (x : Ident)
    (rM : Res Δ T (.comp (.arr A C))) : Except Error (Res Δ T (.comp C)) :=
  match lookupVar x.name E.vars with
  | none => throw ⟨x.span, s!"application `M x` takes a variable, and `{x.name}` is not one " ++
      "in scope; bind it first"⟩
  | some i =>
    if hi : T[i]? = some A then
      if h : overlapOK T rM.F.u (oneL T i) = true then pure (rApp { sp, name := x.name } rM i hi h)
      else throw (splitErr E T sp rM.F.u (oneL T i))
    else throw (mismatch x.span (E.ppV A) (E.slotTy T i))

/-- `<M, N>`: both components at the pair's context. -/
def withIt {C D : CCTy} (E : Env) (T : List CVTy) (sp : Span) (r₁ : Res Δ (withT T) (.comp C))
    (r₂ : Res Δ (withT T) (.comp D)) : Except Error (Res Δ T (.comp (.amp C D))) := do
  let F₁ ← withPop sp r₁.F
  let F₂ ← withPop sp r₂.F
  if s₁ : subL F₁.u (orL F₂.u F₂.w) = true then
    if s₂ : subL F₂.u (orL F₁.u F₁.w) = true then pure (rWith (at_ sp) r₁.t r₂.t (F₁.merge F₂ s₁ s₂))
    else throw (mergeErr E T sp "the first component" "the second" "in this `<M, N>`, "
      F₁.u F₁.w F₂.u F₂.w)
  else throw (mergeErr E T sp "the first component" "the second" "in this `<M, N>`, "
    F₁.u F₁.w F₂.u F₂.w)

/-- `case V { inl x -> M | inr y -> N }`: both arms at one context. -/
def caseIt {A B : CVTy} {C : CCTy} (E : Env) (T : List CVTy) (sp : Span) (x y : Ident)
    (rV : Res Δ T (.val (.sum A B))) (r₁ : Res Δ (A :: T) (.comp C))
    (r₂ : Res Δ (B :: T) (.comp C)) : Except Error (Res Δ T (.comp C)) := do
  let r₁ ← dropStuck x.span 1 r₁
  let r₂ ← dropStuck y.span 1 r₂
  let F₁ ← popL E x.span x.name r₁.F
  let F₂ ← popL E y.span y.name r₂.F
  if s₁ : subL F₁.u (orL F₂.u F₂.w) = true then
    if s₂ : subL F₂.u (orL F₁.u F₁.w) = true then
      let F := F₁.merge F₂ s₁ s₂
      if h : overlapOK T rV.F.u F.u = true then pure (rSumE (atB sp [x.name, y.name]) rV F h)
      else throw (splitErr E T sp rV.F.u F.u)
    else throw (mergeErr E T sp "the `inl` arm" "the `inr` arm" "in this `case`, " F₁.u F₁.w F₂.u F₂.w)
  else throw (mergeErr E T sp "the `inl` arm" "the `inr` arm" "in this `case`, " F₁.u F₁.w F₂.u F₂.w)

/-- `Fun 'x < @b. M`. -/
def funIt {v : LifeVar} {bl : CLife} {C : CCTy} (E : Env) (T : List CVTy) (sp : Span)
    (name : String) (rM : Res (Δ.extend v bl) (.unit :: T) (.comp C)) :
    Except Error (Res Δ T (.comp (.all v bl C))) := do
  if hbx : bl.mentions v = false then
    if hΔx : boundsAvoidB Δ v = true then
      let F ← popD sp rM.F
      if hs : usedSat (fun A => !vfreeB v A) T F.u = true then pure (rAllI (at_ sp) hbx hΔx F hs)
      else match firstBad (fun A => !vfreeB v A) T F.u with
        | some i => throw ⟨sp, s!"`Fun '{name}`: {E.slotName i}, of type `{E.slotTy T i}`, is " ++
            s!"used inside, and its type mentions `'{name}` ({ppLVar v})"⟩
        | none => throw ⟨sp, "internal error: Fun"⟩
    else throw ⟨sp, s!"`Fun '{name}`: its number {ppLVar v} occurs in a bound of the lifetime context"⟩
  else throw ⟨sp, s!"`Fun '{name}`: its bound mentions its own number {ppLVar v}"⟩

/-- `fun (x : 1) -> M` at `1 -o F_Σ B` whose body does not use `x`: `[λ-dead]`, the binder's
slot closed dead.  `[spec §26]` -/
def lamDeadIt (sp : Span) {S : CRow} {B : CVTy} (rM : Res Δ (.unit :: T) (.comp (effOf S B))) :
    Option (Res Δ T (.comp (.arr .unit (effOf S B)))) :=
  rM.F.popDead.map (rLamDead (at_ sp))

/-- `fun (x : A) -> M`, `M` checked under the binder's slot: `[λ-dead]` (SPEC §26) when `A` is `1`,
`M`'s type is a returner chain `F_Σ B` and `M` does not use `x`; `[λ]` otherwise, the binder's
slot closed live. -/
def lamIt {A : CVTy} {C : CCTy} (E : Env) (sp : Span) (x : Ident) (rM : Res Δ (A :: T) (.comp C)) :
    Except Error (Res Δ T (.comp (.arr A C))) :=
  match A, rM with
  | .unit, rM =>
    match effRow? C with
    | some (S, B) =>
      if hC : effOf S B = C then
        match lamDeadIt sp (hC ▸ rM) with
        | some r => pure (hC ▸ r)
        | none => rLam { sp, name := x.name } <$> popL E x.span x.name rM.F
      else rLam { sp, name := x.name } <$> popL E x.span x.name rM.F
    | none => rLam { sp, name := x.name } <$> popL E x.span x.name rM.F
  | _, rM => do
    let rM ← dropStuck x.span 1 rM
    rLam { sp, name := x.name } <$> popL E x.span x.name rM.F

/-! ### Effectful bindings  `[spec §19]` -/

/-- A computation at the row `S′`, at the row `S` by `[sub]`. -/
def liftRow (E : Env) (sp : Span) {S' : CRow} {A : CVTy} (S : CRow)
    (r : Res Δ T (.comp (effOf S' A))) : Except Error (Res Δ T (.comp (effOf S A))) :=
  if hle : rowLeB S' S = true then pure (rEffSub (at_ sp) hle r)
  else throw ⟨sp, s!"this computation performs the operations `{ppRow E S'}`, which are not " ++
    s!"within the row `{ppRow E S}` here"⟩

/-- A synthesized computation at the row `S`: a returner chain within it. -/
def atRow (E : Env) (sp : Span) (S : CRow) :
    (Σ C : CCTy, Res Δ T (.comp C)) → Except Error (Σ B : CVTy, Res Δ T (.comp (effOf S B)))
  | ⟨C, r⟩ =>
    match effRow? C with
    | some (S', B) =>
      if hC : effOf S' B = C then do pure ⟨B, ← liftRow E sp S (hC ▸ r)⟩
      else throw ⟨sp, "internal error: a returner chain"⟩
    | none => throw ⟨sp, s!"after a computation that performs operations, this must have a " ++
        s!"type `F[…] B`, but it has type `{E.ppC C}`"⟩

/-- The finaliser of an effectful binding: the destructors of the non-persistent slots `u` (the
slots the rest of the computation uses), under the binder's dead slot, at the pure row (SPEC §24:
a finaliser lets no raise escape). It runs when an abortive operation of the bound computation
stops the rest. SPEC §19's drop glue: `[then]`'s `D`, inserted as SPEC §12 inserts destructors. -/
def finalOf (E : Env) (sp : Span) (S : CRow) (u : List Bool) :
    Except Error (Res Δ (.unit :: T) (.comp (effOf [] .unit))) := do
  -- The row has an operation that resumes and may be cancelled (`capB`): the finaliser runs at
  -- its cancel. Otherwise only an abort stops the rest.
  let cancels := S.any fun o => BoCa.Fig16.LogRel.Core.capB o.q o.B
  let idx := (List.range T.length).filter fun i =>
    u.getD i false && !((T[i]?.map (·.persistent)).getD true)
  let r0 : Res Δ (.unit :: T) (.comp (.ret .unit)) := rRet (at_ sp) (rUnit (at_ sp))
  let r ← idx.foldlM (init := r0) fun r i => do
    match T[i]? with
    | some A =>
      if hasDtorB A then dropOne sp (i + 1) r
      else if cancels then
        throw ⟨sp, s!"{E.slotName i}, of type `{E.ppV A}`, is live across an operation that " ++
          "may be cancelled: the cancel runs a finaliser (`[then]`) that consumes it by its " ++
          "derived drop, and its type is linear with no derived drop" ++ E.closeHint A true⟩
      else throw ⟨sp, s!"{E.slotName i}, of type `{E.ppV A}`, is live across a computation " ++
        "that may abort, and its type is linear with no derived drop, and an abort abandons " ++
        "only a value that holds no owned cell" ++ E.closeHint A true⟩
    | none => throw ⟨sp, "internal error: a slot is out of range"⟩
  pure r

/-- A marked scheme's derived node, over its checked term (SPEC §3). -/
def markIt {j : Jdg} (sp : Span) (k : SchemeMark) (r : Res Δ T j) : Except Error (Res Δ T j) :=
  match rMarked (at_ sp) k r with
  | some r' => pure r'
  | none => err sp s!"internal error: a marked scheme ({repr k}) is not the scheme's term"

/-- `[then]` at the row `S`: `N` (its binder `x` closed) and the finaliser `D` at one context. -/
def thenIt (E : Env) (sp : Span) (x : String) {S : CRow} {A B : CVTy} {tN : TExpr} {sN : CRow} {pN : Pins}
    (rM : Res Δ T (.comp (effOf S A)))
    (FN : Fam T (fun L => TTied pN sN Δ (mkCtx (A :: T) (true :: L)) tN (.comp (effOf S B))))
    (rD : Res Δ (.unit :: T) (.comp (effOf [] .unit))) :
    Except Error (Res Δ T (.comp (effOf S B))) := do
  if hNZ : Row.nzB S = true then
    if hUq : Row.uniqB S = true then
      let FD ← popD sp rD.F
      if s₁ : subL FN.u (orL FD.u FD.w) = true then
        if s₂ : subL FD.u (orL FN.u FN.w) = true then
          let F := FN.merge FD s₁ s₂
          let F' : Fam T (fun L => (TTied pN sN Δ (mkCtx (A :: T) (true :: L)) tN (.comp (effOf S B)) ∧
              TTied rD.pins rD.sigs Δ (mkCtx (.unit :: T) (false :: L)) rD.t
                (.comp (effOf [] .unit))) ∧
              (S.UnrD → BoCa.Fig16.LogRel.Core.Ctx.Banged (mkCtx T L))) ←
            if hu : Row.unrDB S = true then
              if hs : usedSat isBangB T F.u = true then
                pure ((F.restrict isBangB hs).map fun _ ⟨h, hp⟩ => ⟨h, fun _ => persistent_of hp⟩)
              else match firstBad isBangB T F.u with
                | some i => throw ⟨sp, s!"{E.slotName i}, of type `{E.slotTy T i}`, is used " ++
                    s!"after an operation of the row `{ppRow E S}`, which may resume more than " ++
                    "once: it must be a `!` type"⟩
                | none => throw ⟨sp, "internal error: an unrestricted row"⟩
            else pure (F.map fun _ h => ⟨h, fun hU => absurd (Row.unrDB_iff.mpr hU) (by simp [hu])⟩)
          if h : overlapOK T rM.F.u F'.u = true then
            pure (rEffThen (atB sp [x]) (Row.nzB_sound hNZ) (Row.uniqB_sound hUq) rM F' h)
          else throw (splitErr E T sp rM.F.u F'.u)
        else throw (mergeErr E T sp "the finaliser" "the rest" "after this computation, "
          FD.u FD.w FN.u FN.w)
      else throw (mergeErr E T sp "the rest" "the finaliser" "after this computation, "
        FN.u FN.w FD.u FD.w)
    else throw ⟨sp, s!"the row `{ppRow E S}` has an operation twice"⟩
  else throw ⟨sp, s!"the row `{ppRow E S}` has an operation of the reserved name 0"⟩

/-- `x <- M; N` whose head `M` performs operations, at the row `S` (SPEC §19). At a row with no
cancellable or unrestricted operation, or when every slot `N` uses holds no owned cell (and is `!`
at an unrestricted row), `[let]`; otherwise `[then]`, with the finaliser `finalOf`: the
destructors of the slots `N` uses. -/
def effBind (E : Env) (sp : Span) (x : Ident) {S : CRow} {A B : CVTy}
    (rM : Res Δ T (.comp (effOf S A))) (rN : Res Δ (A :: T) (.comp (effOf S B))) :
    Except Error (Res Δ T (.comp (effOf S B))) := do
  let rN ← dropStuck x.span 1 rN
  let FN ← popL E x.span x.name rN.F
  if hw : Row.cancelsB S = true then
    let p : CVTy → Bool := fun A => ownFreeB A && (!Row.unrB S || isBangB A)
    if hs : usedSat p T FN.u = true then
      let FN' := (FN.restrict p hs).map fun _ ⟨h, hp⟩ =>
        (⟨h, fun _ s hsm hl => ownFreeB_sound _ (by
            have := hp s hsm hl
            simp only [p, Bool.and_eq_true] at this
            exact this.1),
          fun hU s hsm hl => isBangB_sound (by
            have := hp s hsm hl
            simp only [p, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at this
            rcases this.2 with h' | h'
            · exact absurd (Row.unrB_iff.mpr hU) (by simp [h'])
            · exact h')⟩ :
          TTied rN.pins rN.sigs Δ (mkCtx (A :: T) (true :: _)) rN.t (.comp (effOf S B)) ∧
            (S.Cancels → (mkCtx T _).OwnFree) ∧
            (S.Unr → BoCa.Fig16.LogRel.Core.Ctx.Banged (mkCtx T _)))
      if h : overlapOK T rM.F.u FN'.u = true then pure (rScope (at_ sp) (rEffLet (atB sp [x.name]) rM FN' h))
      else throw (splitErr E T sp rM.F.u FN'.u)
    else
      let rD ← finalOf E sp S FN.u
      thenIt E sp x.name rM FN rD
  else
    let FN' := FN.map fun _ h =>
      (⟨h, fun hW => absurd (Row.cancelsB_iff.mpr hW) (by simp [hw]),
        fun hU => absurd (Row.cancelsB_iff.mpr (Row.cancels_of_unr hU)) (by simp [hw])⟩ :
        TTied rN.pins rN.sigs Δ (mkCtx (A :: T) (true :: _)) rN.t (.comp (effOf S B)) ∧
          (S.Cancels → (mkCtx T _).OwnFree) ∧
          (S.Unr → BoCa.Fig16.LogRel.Core.Ctx.Banged (mkCtx T _)))
    if h : overlapOK T rM.F.u FN'.u = true then pure (rScope (at_ sp) (rEffLet (atB sp [x.name]) rM FN' h))
    else throw (splitErr E T sp rM.F.u FN'.u)

end

end Frontend.Check

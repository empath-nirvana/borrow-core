import Frontend.Check.Conv
import Core.Classes

/-!
# Frontend — Check — steps shared by the checker's cases

The checker's environment, the messages it reports, the deciders of fold shapes and
consumes, the implicit consumes (SPEC §12), and the steps that combine checked premises through a
rule builder once its side conditions are decided: closing binders, splitting and merging
contexts, `boxed`, application to a variable, `<,>`, `case` and `Fun`.
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (Jdg FShape Consumable consumeAlgs LinearConsumable Linear)

/-! ### Fold shapes and consumes, decided -/

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

/-! ### Consumes (SPEC §12) -/

open BoCa.Fig16.LogRel.Core.FoldP (clB keysIn resO PBody pBodyB pBodyB_iff Bnd Stack) in
/-- `Consumable`, decided: `consumableAtB false A` for `A`; `consumableAtB true A` for a position `A` of a `μ` body:
`A⟨1⟩` is consumable, and so has the body of each key inside `A` (the recursion of `consumeAt` and
`algsIn`). -/
def consumableAtB : Bool → CVTy → Bool
  | alg, .tensor A B => consumableAtB alg A && consumableAtB alg B
  | alg, .sum A B => consumableAtB alg A && consumableAtB alg B
  | alg, .ref A => if alg && !clB 0 A then consumableAtB true A else consumableAtB false A
  | alg, .tvar _ => alg
  | _, .box _ A => consumableAtB false A
  | alg, .mu A => if alg && !clB 0 (.mu A) then consumableAtB true A else pBodyB A && consumableAtB true A
  | _, .thunk (.amp _ (.ret .unit)) => true
  | _, .thunk (.nu (.amp C (.ret R))) =>
      CTy.nuOkB (.amp C (.ret R)) && VTy.clB 0 R && consumableAtB false R
  | _, .thunk _ | _, .code _ _ _ => false
  | _, .unit | _, .zero | _, .int _ | _, .unk | _, .bang _ | _, .imm _ _ | _, .mut _ _ => true
  | alg, .fam (.ref A) => if alg && !clB 0 A then consumableAtB true A else consumableAtB false A
  | _, .fam (.imm _ _) => true
  | _, .fam (.mut _ _) => true
  | _, .fam _ => false
  | _, .opq _ => false

/-- At a thunk `consumableAtB` does not depend on the mode. -/
theorem consumableAtB_thunk : ∀ (b : Bool) (C : CCTy), consumableAtB b (.thunk C) = consumableAtB false (.thunk C)
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
  | _, .amp _ (.ret (.code _ _ _))
  | _, .amp _ (.arr _ _) | _, .amp _ (.amp _ _) | _, .amp _ .top | _, .amp _ (.all _ _ _)
  | _, .amp _ (.nu _) | _, .amp _ (.eff _ _ _ _ _ _ _ _) => rfl

open BoCa.Fig16.LogRel.Core.FoldP (clB) in
/-- At a closed type the two modes agree. -/
theorem consumableAtB_closed : ∀ (A : CVTy), clB 0 A = true → consumableAtB true A = consumableAtB false A
  | .tensor A B, h => by
      simp only [BoCa.Fig16.LogRel.Core.FoldP.clB, Bool.and_eq_true] at h
      simp only [consumableAtB, consumableAtB_closed A h.1, consumableAtB_closed B h.2]
  | .sum A B, h => by
      simp only [BoCa.Fig16.LogRel.Core.FoldP.clB, Bool.and_eq_true] at h
      simp only [consumableAtB, consumableAtB_closed A h.1, consumableAtB_closed B h.2]
  | .ref A, h => by
      simp only [BoCa.Fig16.LogRel.Core.FoldP.clB] at h
      simp [consumableAtB, h]
  | .fam (.ref A), h => by
      simp only [BoCa.Fig16.LogRel.Core.FoldP.clB] at h
      simp [consumableAtB, h]
  | .mu A, h => by simp [consumableAtB, h]
  | .tvar _, h => by simp [BoCa.Fig16.LogRel.Core.FoldP.clB] at h
  | .thunk C, _ => consumableAtB_thunk true C
  | .unit, _ | .zero, _ | .box _ _, _ | .bang _, _ | .unk, _ | .int _, _
  | .opq _, _ | .imm _ _, _ | .mut _ _, _ | .code _ _ _, _ => rfl
  | .fam .unit, _ | .fam (.tensor _ _), _ | .fam .zero, _ | .fam (.sum _ _), _
  | .fam (.thunk _), _ | .fam (.code _ _ _), _ | .fam (.imm _ _), _ | .fam (.mut _ _), _ | .fam (.box _ _), _
  | .fam (.bang _), _ | .fam .unk, _ | .fam (.tvar _), _ | .fam (.mu _), _ | .fam (.int _), _
  | .fam (.fam _), _ | .fam (.opq _), _ => rfl

open BoCa.Fig16.LogRel.Core.FoldP (keysIn resO Bnd Stack) in
/-- What `consumableAtB true A` gives at a position `A` under the stack `Bs`: `A⟨1⟩` is consumable,
and so has the body of each key of `A`. -/
abbrev AlgConsume (Bs : Stack) (A : CVTy) : Prop :=
  Consumable (resO consumeAlgs Bs A) ∧
    (∀ B Bs', Bnd.mu (B :: Bs') ∈ keysIn Bs A → Consumable (resO consumeAlgs (B :: Bs') B)) ∧
    ∀ Bs' S, Bnd.arr Bs' S ∈ keysIn Bs A → Consumable (resO consumeAlgs Bs' S)

open BoCa.Fig16.LogRel.Core.FoldP (clB keysIn resO resO_leaf Bnd Stack) in
/-- A closed position's `AlgConsume` is its own consume. -/
theorem algConsume_closed {A : CVTy} (hc : clB 0 A = true) (h : Consumable A) (Bs : Stack) :
    AlgConsume Bs A := by
  refine ⟨by rwa [resO_leaf consumeAlgs Bs hc], fun B Bs' hm => ?_, fun Bs' S hm => ?_⟩
  · rw [BoCa.Fig16.LogRel.Core.keysIn_toFShape.keysIn_closed Bs hc] at hm; cases hm
  · rw [BoCa.Fig16.LogRel.Core.keysIn_toFShape.keysIn_closed Bs hc] at hm; cases hm

open BoCa.Fig16.LogRel.Core.FoldP (keysIn resO Stack) in
/-- A position the fold passes through: `A⟨1⟩` is `A`, and it has no key. -/
theorem algConsumeLeaf (A : CVTy) (h : Consumable A) (Bs : Stack)
    (hr : resO consumeAlgs Bs A = A := by rfl) (hk : keysIn Bs A = [] := by rfl) : AlgConsume Bs A :=
  ⟨by rwa [hr], ⟨fun B Bs' hm => (by rw [hk] at hm; cases hm),
    fun Bs' S hm => (by rw [hk] at hm; cases hm)⟩⟩

mutual
/-- **`consumableAtB false` is sound for `Consumable`.** -/
theorem consumableAtB_sound : ∀ (A : CVTy), consumableAtB false A = true → Consumable A
  | .tensor A B, h => by
      simp only [consumableAtB, Bool.and_eq_true] at h
      exact .tensor (consumableAtB_sound A h.1) (consumableAtB_sound B h.2)
  | .sum A B, h => by
      simp only [consumableAtB, Bool.and_eq_true] at h
      exact .sum (consumableAtB_sound A h.1) (consumableAtB_sound B h.2)
  | .ref A, h => .ref (consumableAtB_sound A (by simpa [consumableAtB] using h))
  | .tvar _, h => by simp [consumableAtB] at h
  | .box _ A, h => .box (consumableAtB_sound A (by simpa [consumableAtB] using h))
  | .mu A, h => by
      simp only [consumableAtB, Bool.false_and, Bool.false_eq_true, if_false, Bool.and_eq_true] at h
      obtain ⟨h₁, h₂, h₃⟩ := consumableAtB_soundA A h.2 [A]
      exact .mu ((BoCa.Fig16.LogRel.Core.FoldP.pBodyB_iff A).mp h.1) h₁ h₂ h₃
  | .thunk (.amp _ (.ret .unit)), _ => .close
  | .thunk (.nu (.amp C (.ret R))), h => by
      simp only [consumableAtB, Bool.and_eq_true] at h
      exact .nu (CTy.nuOkB_sound _ h.1.1) (VTy.clB_sound 0 R h.1.2) (consumableAtB_sound R h.2)
  | .thunk (.nu (.ret _)), h | .thunk (.nu (.arr _ _)), h | .thunk (.nu .top), h
  | .thunk (.nu (.all _ _ _)), h | .thunk (.nu (.nu _)), h
  | .thunk (.nu (.amp _ (.arr _ _))), h | .thunk (.nu (.amp _ (.amp _ _))), h
  | .thunk (.nu (.amp _ .top)), h | .thunk (.nu (.amp _ (.all _ _ _))), h
  | .thunk (.nu (.amp _ (.nu _))), h => by simp [consumableAtB] at h
  | .thunk (.ret _), h | .thunk (.arr _ _), h | .thunk .top, h
  | .thunk (.all _ _ _), h => by simp [consumableAtB] at h
  | .thunk (.amp _ (.ret (.tensor _ _))), h | .thunk (.amp _ (.ret .zero)), h
  | .thunk (.amp _ (.ret (.sum _ _))), h | .thunk (.amp _ (.ret (.thunk _))), h
  | .thunk (.amp _ (.ret (.ref _))), h | .thunk (.amp _ (.ret (.imm _ _))), h
  | .thunk (.amp _ (.ret (.mut _ _))), h | .thunk (.amp _ (.ret (.box _ _))), h
  | .thunk (.amp _ (.ret (.bang _))), h | .thunk (.amp _ (.ret .unk)), h
  | .thunk (.amp _ (.ret (.tvar _))), h | .thunk (.amp _ (.ret (.mu _))), h
  | .thunk (.amp _ (.ret (.int _))), h | .thunk (.amp _ (.ret (.fam _))), h
  | .thunk (.amp _ (.ret (.opq _))), h | .thunk (.amp _ (.ret (.code _ _ _))), h
  | .thunk (.amp _ (.arr _ _)), h
  | .thunk (.amp _ (.amp _ _)), h | .thunk (.amp _ .top), h
  | .thunk (.amp _ (.all _ _ _)), h | .thunk (.amp _ (.nu _)), h => by simp [consumableAtB] at h
  | .unit, _ => .unit
  | .zero, _ => .zero
  | .int _, _ => .int
  | .opq _, h | .code _ _ _, h => by simp [consumableAtB] at h
  | .unk, _ => .unk
  | .bang _, _ => .bang
  | .imm _ _, _ => .imm
  | .mut _ _, _ => .mut
  | .fam (.ref A), h => .array (consumableAtB_sound A (by simpa [consumableAtB] using h))
  | .fam (.imm _ _), _ => .arrayImm
  | .fam (.mut _ _), _ => .arrayMut
  | .fam .unit, h | .fam (.tensor _ _), h | .fam .zero, h | .fam (.sum _ _), h
  | .fam (.thunk _), h | .fam (.code _ _ _), h | .fam (.box _ _), h
  | .fam (.bang _), h | .fam .unk, h | .fam (.tvar _), h | .fam (.mu _), h
  | .fam (.int _), h | .fam (.fam _), h => by simp [consumableAtB] at h

/-- **`consumableAtB true` is sound for `AlgConsume`.** -/
theorem consumableAtB_soundA : ∀ (A : CVTy), consumableAtB true A = true → ∀ Bs, AlgConsume Bs A
  | .tensor A B, h, Bs => by
      by_cases hc : BoCa.Fig16.LogRel.Core.FoldP.clB 0 (.tensor A B) = true
      · exact algConsume_closed hc (consumableAtB_sound _ (by rwa [← consumableAtB_closed _ hc])) Bs
      · simp only [consumableAtB, Bool.and_eq_true] at h
        obtain ⟨a₁, a₂, a₃⟩ := consumableAtB_soundA A h.1 Bs
        obtain ⟨b₁, b₂, b₃⟩ := consumableAtB_soundA B h.2 Bs
        refine ⟨?_, fun B' Bs' hm => ?_, fun Bs' S hm => ?_⟩
        · simp only [BoCa.Fig16.LogRel.Core.FoldP.resO, if_neg hc]; exact .tensor a₁ b₁
        · simp only [BoCa.Fig16.LogRel.Core.FoldP.keysIn, List.mem_append] at hm
          exact hm.elim (a₂ B' Bs') (b₂ B' Bs')
        · simp only [BoCa.Fig16.LogRel.Core.FoldP.keysIn, List.mem_append] at hm
          exact hm.elim (a₃ Bs' S) (b₃ Bs' S)
  | .sum A B, h, Bs => by
      by_cases hc : BoCa.Fig16.LogRel.Core.FoldP.clB 0 (.sum A B) = true
      · exact algConsume_closed hc (consumableAtB_sound _ (by rwa [← consumableAtB_closed _ hc])) Bs
      · simp only [consumableAtB, Bool.and_eq_true] at h
        obtain ⟨a₁, a₂, a₃⟩ := consumableAtB_soundA A h.1 Bs
        obtain ⟨b₁, b₂, b₃⟩ := consumableAtB_soundA B h.2 Bs
        refine ⟨?_, fun B' Bs' hm => ?_, fun Bs' S hm => ?_⟩
        · simp only [BoCa.Fig16.LogRel.Core.FoldP.resO, if_neg hc]; exact .sum a₁ b₁
        · simp only [BoCa.Fig16.LogRel.Core.FoldP.keysIn, List.mem_append] at hm
          exact hm.elim (a₂ B' Bs') (b₂ B' Bs')
        · simp only [BoCa.Fig16.LogRel.Core.FoldP.keysIn, List.mem_append] at hm
          exact hm.elim (a₃ Bs' S) (b₃ Bs' S)
  | .ref A, h, Bs => by
      by_cases hc : BoCa.Fig16.LogRel.Core.FoldP.clB 0 A = true
      · exact algConsume_closed (A := .ref A) hc
          (consumableAtB_sound _ (by rwa [← consumableAtB_closed (.ref A) hc])) Bs
      · simp only [consumableAtB, hc, Bool.not_false, Bool.and_self, if_true] at h
        obtain ⟨a₁, a₂, a₃⟩ := consumableAtB_soundA A h Bs
        refine ⟨?_, fun B' Bs' hm => a₂ B' Bs' hm, fun Bs' S hm => a₃ Bs' S hm⟩
        simp only [BoCa.Fig16.LogRel.Core.FoldP.resO, if_neg hc]; exact a₁
  | .fam (.ref A), h, Bs => by
      by_cases hc : BoCa.Fig16.LogRel.Core.FoldP.clB 0 A = true
      · exact algConsume_closed (A := .fam (.ref A)) hc
          (consumableAtB_sound _ (by rwa [← consumableAtB_closed (.fam (.ref A)) hc])) Bs
      · simp only [consumableAtB, hc, Bool.not_false, Bool.and_self, if_true] at h
        obtain ⟨a₁, a₂, a₃⟩ := consumableAtB_soundA A h Bs
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
      · exact algConsume_closed hc (consumableAtB_sound _ (by rwa [← consumableAtB_closed _ hc])) Bs
      · simp only [consumableAtB, hc, Bool.not_false, Bool.and_self, if_true] at h
        obtain ⟨a₁, a₂, a₃⟩ := consumableAtB_soundA A h (A :: Bs)
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
      refine ⟨by simp [BoCa.Fig16.LogRel.Core.FoldP.resO, consumeAlgs]; exact .unit,
        fun _ _ hm => by simp [BoCa.Fig16.LogRel.Core.FoldP.keysIn] at hm,
        fun _ _ hm => by simp [BoCa.Fig16.LogRel.Core.FoldP.keysIn] at hm⟩
  | .box a A, h, Bs => algConsumeLeaf (.box a A) (consumableAtB_sound _ h) Bs
  | .thunk (.amp C (.ret .unit)), _, Bs => algConsumeLeaf (.thunk (.amp C (.ret .unit))) .close Bs
  | .thunk (.nu (.amp C (.ret R))), h, Bs => by
      simp only [consumableAtB, Bool.and_eq_true] at h
      exact algConsumeLeaf _ (.nu (CTy.nuOkB_sound _ h.1.1) (VTy.clB_sound 0 R h.1.2) (consumableAtB_sound R h.2)) Bs
  | .thunk (.nu (.ret _)), h, _ | .thunk (.nu (.arr _ _)), h, _ | .thunk (.nu .top), h, _
  | .thunk (.nu (.all _ _ _)), h, _ | .thunk (.nu (.nu _)), h, _
  | .thunk (.nu (.amp _ (.arr _ _))), h, _ | .thunk (.nu (.amp _ (.amp _ _))), h, _
  | .thunk (.nu (.amp _ .top)), h, _ | .thunk (.nu (.amp _ (.all _ _ _))), h, _
  | .thunk (.nu (.amp _ (.nu _))), h, _ => by simp [consumableAtB] at h
  | .thunk (.ret _), h, _ | .thunk (.arr _ _), h, _ | .thunk .top, h, _
  | .thunk (.all _ _ _), h, _ => by simp [consumableAtB] at h
  | .thunk (.amp _ (.ret (.tensor _ _))), h, _ | .thunk (.amp _ (.ret .zero)), h, _
  | .thunk (.amp _ (.ret (.sum _ _))), h, _ | .thunk (.amp _ (.ret (.thunk _))), h, _
  | .thunk (.amp _ (.ret (.ref _))), h, _ | .thunk (.amp _ (.ret (.imm _ _))), h, _
  | .thunk (.amp _ (.ret (.mut _ _))), h, _ | .thunk (.amp _ (.ret (.box _ _))), h, _
  | .thunk (.amp _ (.ret (.bang _))), h, _ | .thunk (.amp _ (.ret .unk)), h, _
  | .thunk (.amp _ (.ret (.tvar _))), h, _ | .thunk (.amp _ (.ret (.mu _))), h, _
  | .thunk (.amp _ (.ret (.int _))), h, _ | .thunk (.amp _ (.ret (.fam _))), h, _
  | .thunk (.amp _ (.ret (.opq _))), h, _ | .thunk (.amp _ (.ret (.code _ _ _))), h, _
  | .thunk (.amp _ (.arr _ _)), h, _
  | .thunk (.amp _ (.amp _ _)), h, _ | .thunk (.amp _ .top), h, _
  | .thunk (.amp _ (.all _ _ _)), h, _ | .thunk (.amp _ (.nu _)), h, _ => by simp [consumableAtB] at h
  | .unit, _, Bs => algConsumeLeaf .unit .unit Bs
  | .zero, _, Bs => algConsumeLeaf .zero .zero Bs
  | .int w, _, Bs => algConsumeLeaf (.int w) .int Bs
  | .unk, _, Bs => algConsumeLeaf .unk .unk Bs
  | .bang A, _, Bs => algConsumeLeaf (.bang A) .bang Bs
  | .imm a A, _, Bs => algConsumeLeaf (.imm a A) .imm Bs
  | .mut a A, _, Bs => algConsumeLeaf (.mut a A) .mut Bs
  | .opq _, h, _ | .code _ _ _, h, _ => by simp [consumableAtB] at h
  | .fam (.imm a A), _, Bs => algConsumeLeaf (.fam (.imm a A)) .arrayImm Bs
  | .fam (.mut a A), _, Bs => algConsumeLeaf (.fam (.mut a A)) .arrayMut Bs
  | .fam .unit, h, _ | .fam (.tensor _ _), h, _ | .fam .zero, h, _ | .fam (.sum _ _), h, _
  | .fam (.thunk _), h, _ | .fam (.code _ _ _), h, _ | .fam (.box _ _), h, _
  | .fam (.bang _), h, _ | .fam .unk, h, _ | .fam (.tvar _), h, _ | .fam (.mu _), h, _
  | .fam (.int _), h, _ | .fam (.fam _), h, _ | .fam (.opq _), h, _ => by simp [consumableAtB] at h
end

/-- `A` is consumable. -/
def consumableB (A : CVTy) : Bool := consumableAtB false A

theorem consumableB_sound {A : CVTy} (h : consumableB A = true) : Consumable A := consumableAtB_sound A h

open BoCa.Fig16.LogRel.Core.FoldP (clB keysIn resO resO_leaf pBodyB_iff Bnd Stack) in
mutual
/-- **`consumableAtB false` is complete for `Consumable`.** -/
theorem consumableAtB_complete : ∀ A : CVTy, Consumable A → consumableAtB false A = true
  | .tensor A B, h => by
      cases h with
      | tensor h₁ h₂ => simp [consumableAtB, consumableAtB_complete A h₁, consumableAtB_complete B h₂]
  | .sum A B, h => by
      cases h with
      | sum h₁ h₂ => simp [consumableAtB, consumableAtB_complete A h₁, consumableAtB_complete B h₂]
  | .ref A, h => by
      cases h with
      | ref h => simpa [consumableAtB] using consumableAtB_complete A h
  | .tvar _, h => by cases h
  | .box _ A, h => by
      cases h with
      | box h => simpa [consumableAtB] using consumableAtB_complete A h
  | .mu A, h => by
      cases h with
      | mu hP h₁ h₂ h₃ =>
          simp only [consumableAtB, Bool.false_and, Bool.false_eq_true, if_false, Bool.and_eq_true]
          exact ⟨(pBodyB_iff A).mpr hP, consumableAtB_completeA A [A] ⟨h₁, h₂, h₃⟩⟩
  | .thunk (.amp _ (.ret .unit)), _ => rfl
  | .thunk (.nu (.amp C (.ret R))), h => by
      cases h with
      | nu hC hRc h =>
          simp [consumableAtB, CTy.nuOkB_complete _ hC, VTy.clB_complete 0 R hRc, consumableAtB_complete R h]
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
  | .thunk (.amp _ (.ret (.opq _))), h | .thunk (.amp _ (.ret (.code _ _ _))), h
  | .thunk (.amp _ (.arr _ _)), h
  | .thunk (.amp _ (.amp _ _)), h | .thunk (.amp _ .top), h
  | .thunk (.amp _ (.all _ _ _)), h | .thunk (.amp _ (.nu _)), h
  | .thunk (.amp _ (.eff _ _ _ _ _ _ _ _)), h => by cases h
  | .unit, _ | .zero, _ | .int _, _ | .unk, _ | .bang _, _ | .imm _ _, _ | .mut _ _, _ => rfl
  | .opq _, h => by cases h
  | .fam (.ref A), h => by
      cases h with
      | array h => simpa [consumableAtB] using consumableAtB_complete A h
  | .fam (.imm _ _), _ | .fam (.mut _ _), _ => rfl
  | .fam .unit, h | .fam (.tensor _ _), h | .fam .zero, h | .fam (.sum _ _), h
  | .fam (.thunk _), h | .fam (.code _ _ _), h | .fam (.box _ _), h
  | .fam (.bang _), h | .fam .unk, h | .fam (.tvar _), h | .fam (.mu _), h
  | .fam (.int _), h | .fam (.fam _), h | .fam (.opq _), h => by cases h

/-- **`consumableAtB true` is complete for `AlgConsume`**, at every stack: the recursion carries the stack
as `AlgConsume` does, `A :: Bs` under a `μ` that is not closed. -/
theorem consumableAtB_completeA : ∀ (A : CVTy) (Bs : Stack), AlgConsume Bs A → consumableAtB true A = true
  | .tensor A B, Bs, h => by
      by_cases hc : clB 0 (.tensor A B) = true
      · have h₁ := h.1
        rw [resO_leaf consumeAlgs Bs hc] at h₁
        rw [consumableAtB_closed _ hc]
        exact consumableAtB_complete _ h₁
      · obtain ⟨h₁, h₂, h₃⟩ := h
        simp only [BoCa.Fig16.LogRel.Core.FoldP.resO, if_neg hc] at h₁
        cases h₁ with
        | tensor ha hb =>
          have hA : AlgConsume Bs A := ⟨ha, fun B' Bs' hm => h₂ B' Bs' (by
              simp only [keysIn, List.mem_append]; exact .inl hm),
            fun Bs' S hm => h₃ Bs' S (by simp only [keysIn, List.mem_append]; exact .inl hm)⟩
          have hB : AlgConsume Bs B := ⟨hb, fun B' Bs' hm => h₂ B' Bs' (by
              simp only [keysIn, List.mem_append]; exact .inr hm),
            fun Bs' S hm => h₃ Bs' S (by simp only [keysIn, List.mem_append]; exact .inr hm)⟩
          simp [consumableAtB, consumableAtB_completeA A Bs hA, consumableAtB_completeA B Bs hB]
  | .sum A B, Bs, h => by
      by_cases hc : clB 0 (.sum A B) = true
      · have h₁ := h.1
        rw [resO_leaf consumeAlgs Bs hc] at h₁
        rw [consumableAtB_closed _ hc]
        exact consumableAtB_complete _ h₁
      · obtain ⟨h₁, h₂, h₃⟩ := h
        simp only [BoCa.Fig16.LogRel.Core.FoldP.resO, if_neg hc] at h₁
        cases h₁ with
        | sum ha hb =>
          have hA : AlgConsume Bs A := ⟨ha, fun B' Bs' hm => h₂ B' Bs' (by
              simp only [keysIn, List.mem_append]; exact .inl hm),
            fun Bs' S hm => h₃ Bs' S (by simp only [keysIn, List.mem_append]; exact .inl hm)⟩
          have hB : AlgConsume Bs B := ⟨hb, fun B' Bs' hm => h₂ B' Bs' (by
              simp only [keysIn, List.mem_append]; exact .inr hm),
            fun Bs' S hm => h₃ Bs' S (by simp only [keysIn, List.mem_append]; exact .inr hm)⟩
          simp [consumableAtB, consumableAtB_completeA A Bs hA, consumableAtB_completeA B Bs hB]
  | .ref A, Bs, h => by
      by_cases hc : clB 0 A = true
      · have h₁ := h.1
        rw [resO_leaf consumeAlgs Bs (A := .ref A) hc] at h₁
        cases h₁ with
        | ref h₁ => simp [consumableAtB, hc, consumableAtB_complete A h₁]
      · obtain ⟨h₁, h₂, h₃⟩ := h
        simp only [BoCa.Fig16.LogRel.Core.FoldP.resO, if_neg hc] at h₁
        simp only [consumableAtB, hc, Bool.not_false, Bool.and_self, if_true]
        exact consumableAtB_completeA A Bs ⟨h₁, h₂, h₃⟩
  | .tvar _, _, _ => rfl
  | .box a A, Bs, h => by
      have h₁ := h.1
      simp only [BoCa.Fig16.LogRel.Core.FoldP.resO] at h₁
      cases h₁ with
      | box h₁ => simpa [consumableAtB] using consumableAtB_complete A h₁
  | .mu A, Bs, h => by
      by_cases hc : clB 0 (.mu A) = true
      · have h₁ := h.1
        rw [resO_leaf consumeAlgs Bs hc] at h₁
        cases h₁ with
        | mu hP h₁ h₂ h₃ =>
            simp only [consumableAtB, hc, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false,
              Bool.and_eq_true]
            exact ⟨(pBodyB_iff A).mpr hP, consumableAtB_completeA A [A] ⟨h₁, h₂, h₃⟩⟩
      · obtain ⟨-, h₂, h₃⟩ := h
        have hroot : Consumable (resO consumeAlgs (A :: Bs) A) :=
          h₂ A Bs (by simp [keysIn, hc])
        have hA : AlgConsume (A :: Bs) A := ⟨hroot,
          fun B' Bs' hm => h₂ B' Bs' (by simp only [keysIn, if_neg hc]; exact .tail _ hm),
          fun Bs' S hm => h₃ Bs' S (by simp only [keysIn, if_neg hc]; exact .tail _ hm)⟩
        simp only [consumableAtB, hc, Bool.not_false, Bool.and_self, if_true]
        exact consumableAtB_completeA A (A :: Bs) hA
  | .thunk (.amp _ (.ret .unit)), _, _ => rfl
  | .thunk (.nu (.amp C (.ret R))), _, h => by
      have h₁ := h.1
      simp only [BoCa.Fig16.LogRel.Core.FoldP.resO] at h₁
      cases h₁ with
      | nu hC hRc h =>
          simp [consumableAtB, CTy.nuOkB_complete _ hC, VTy.clB_complete 0 R hRc, consumableAtB_complete R h]
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
        rw [resO_leaf consumeAlgs Bs (A := .fam (.ref A)) hc] at h₁
        cases h₁ with
        | array h₁ => simp [consumableAtB, hc, consumableAtB_complete A h₁]
      · obtain ⟨-, h₂, h₃⟩ := h
        have hS : Consumable (resO consumeAlgs Bs A) := h₃ Bs A (by simp [keysIn, hc])
        have hA : AlgConsume Bs A := ⟨hS,
          fun B' Bs' hm => h₂ B' Bs' (by simp only [keysIn, if_neg hc]; exact .tail _ hm),
          fun Bs' S hm => h₃ Bs' S (by simp only [keysIn, if_neg hc]; exact .tail _ hm)⟩
        simp only [consumableAtB, hc, Bool.not_false, Bool.and_self, if_true]
        exact consumableAtB_completeA A Bs hA
  | .fam (.imm _ _), _, _ | .fam (.mut _ _), _, _ => rfl
  | .fam .unit, _, h | .fam (.tensor _ _), _, h | .fam .zero, _, h | .fam (.sum _ _), _, h
  | .fam (.thunk _), _, h | .fam (.box _ _), _, h
  | .fam (.bang _), _, h | .fam .unk, _, h | .fam (.tvar _), _, h | .fam (.mu _), _, h
  | .fam (.int _), _, h | .fam (.fam _), _, h | .fam (.opq _), _, h => by
      have h₁ := h.1
      simp only [BoCa.Fig16.LogRel.Core.FoldP.resO] at h₁
      cases h₁
end

/-- **`consumableB` decides `Consumable`.**  `[spec §12]` -/
theorem consumableB_iff (A : CVTy) : consumableB A = true ↔ Consumable A :=
  ⟨consumableAtB_sound A, consumableAtB_complete A⟩

instance : DecidablePred Consumable := fun A => decidable_of_iff _ (consumableB_iff A)

instance : DecidablePred LinearConsumable := fun A =>
  inferInstanceAs (Decidable (¬ A.Persistent ∧ Consumable A))


/-- What the checker knows at a point besides `Δ` and the slot types `T`: the declarations in
scope, the name of each slot (a dead binder has none), the lifetime names, a `def`'s type
parameters, and the slots **owed** to the current tail position (SPEC §12): variables with a
consume that the computation being checked must consume on every path, the checker consuming
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
  /-- The slots owed to the computation a value is in, held for the values in it: a computation
  inside a value (`thunk M`, `thunkv N`, `run M`) is owed those it mentions (SPEC §12 *Captured
  variables*). Indexed like `vars`; a slot past its end is not held.  `[spec §12]` -/
  cap : List Bool := []

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

/-- The environment of a computation checked against `C`: the row of `C` when it is a returner
chain.  `[spec §19]` -/
def Env.atC (E : Env) (C : CCTy) : Env :=
  match effRow? C with
  | some (S, _) => { E with row := some S }
  | none => E

/-- `a ∨ b` pointwise, a slot past the end of one list taken from the other. -/
def orPad : List Bool → List Bool → List Bool
  | a :: as, b :: bs => (a || b) :: orPad as bs
  | [], bs => bs
  | as, [] => as

/-- A value: nothing owed, what the computation it is in is owed held for the computations inside
it (`Env.cap`), and no row.  `[spec §12]` -/
def Env.forVal (E : Env) : Env := { E with own := [], cap := orPad E.own E.cap, row := none }

/-- A row as the core text writes it, each entry with its cancel row at every depth (`ppEff`).
`[spec §19, §27]` -/
def ppRow (E : Env) (S : CRow) : String :=
  "[" ++ ", ".intercalate (ppEff E.lenv (BoCa.Fig16.LogRel.Core.CTy.effOf S .unit)).1 ++ "]"

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

/-- The operations a computation type's calls perform: its row under its arguments and
lifetime binders, both branches of a `&` (a continuation's resume and cancel). -/
def retRowOf : CCTy → CRow
  | .arr _ C => retRowOf C
  | .all _ _ C => retRowOf C
  | .amp C D => retRowOf C ++ retRowOf D
  | .nu C => retRowOf C
  | C => C.rowOf

/-- The operations (`n.i`) a checked term performs, read from its derivation: its `[perform]`,
`await` and `[raise]` nodes, under each `[sub]` what its subterm performs (its source row is the
row the subterm is checked at, which may hold more), the row of each call (a leaf whose
judgment is a computation type), and inside `handle_n` none of the name `n`. The finaliser's row
`Σ_D` of `[then]` is the site's operations among these (`finC`); the kernel checks `D` at it.
`[spec §27]` -/
def opKeysOf : Nat → TExpr → List (UInt32 × UInt32)
  | 0, _ => []
  | k + 1, t =>
    let keys (S : CRow) := S.map fun o => (o.n, o.i)
    let inner (n : UInt32) (tc te : TExpr) :=
      opKeysOf k tc ++ (opKeysOf k te).filter (·.1 != n)
    match t with
    | .effPerform _ _ _ o t' => (o.n, o.i) :: opKeysOf k t'
    | .effAwait _ _ _ _ a c => [(a.n, a.i), (c.n, c.i)]
    | .effRaise _ _ _ o _ t' => (o.n, o.i) :: opKeysOf k t'
    | .effSub _ _ _ _ _ t' => opKeysOf k t'
    | .effHandleV _ _ _ _ _ _ n _ _ _ _ _ _ tc te => inner n tc te
    | .effHandleVB _ _ _ _ _ _ n _ _ _ _ _ _ _ tc te => inner n tc te
    | .effHandleT _ _ _ _ _ _ n _ _ _ _ _ tc te => inner n tc te
    | .effHandleL _ _ _ _ _ _ _ n _ _ _ _ _ tc te => inner n tc te
    | t => match t.children with
      | [] => match t.jdg with
        | .comp C => keys (retRowOf C)
        | _ => []
      | cs => cs.flatMap fun c => opKeysOf k c.2

/-- The cancel row `F` whose `cancelTy S F` is the cancel branch `C` of a `κ`: `C`'s layers ahead
of `S`'s, counted by `S`'s length (the clause's type, rebuilt at it, is then compared whole).
`[spec §27]` -/
def finOfBranch (S : CRow) (C : CCTy) : CCTy :=
  let R := C.rowOf
  BoCa.Fig16.LogRel.Core.CTy.effOf (R.take (R.length - S.length)) .unit

/-- The cancel row a `κ`'s type `K` is at, read back from its cancel branch (`finOfBranch`).
`[spec §27]` -/
def kFin (S : CRow) : CVTy → CCTy
  | .thunk (.amp _ C) => finOfBranch S C
  | .bang (.thunk (.amp _ C)) => finOfBranch S C
  | _ => .ret .unit

/-- The cancel row a clause's type gives its operation: `κ`'s (`kFin`), read only at a capturable
operation (`capB`); the empty cancel row at any other.  `[spec §27]` -/
def clauseFin (S : CRow) (c : CVTy) (e : CQual × CVTy × CVTy) : CCTy :=
  if BoCa.Fig16.LogRel.Core.capB e.1 e.2.2 then
    match c with
    | .bang (.thunk (.arr (.tensor _ K) _)) => kFin S K
    | _ => .ret .unit
  else .ret .unit

/-- The first candidate whose clause type, at its cancel row (`clauseFin`), is `c` up to `[α]`
(`tyEqV`). -/
def firstClause (S : CRow) (R c : CVTy) :
    List (CQual × CVTy × CVTy) → Option ((CQual × CVTy × CVTy) × CCTy)
  | [] => none
  | e :: es =>
    let F := clauseFin S c e
    if tyEqV (BoCa.Fig16.LogRel.Core.clauseTy S R e F) c then some (e, F)
      else firstClause S R c es

/-- The operations `E` of a handler, each with its cancel row, read back from the type of its
clauses' tuple, with `clausesTy S R E fs` that type up to `[α]`. An abortive operation is read as
cancellable: `cancel` and `unr` give it the same clause type.  `[spec §19, §27]` -/
def clausesReadF (S : CRow) (R : CVTy) : (Tc : CVTy) → Option (List ((CQual × CVTy × CVTy) × CCTy))
  | .unit => some []
  | .tensor c rest => do
    let e ← firstClause S R c (clauseCands c)
    let E ← clausesReadF S R rest
    pure (e :: E)
  | _ => none

/-- The operations `E` of a handler read back from the type of its clauses' tuple
(`clausesReadF`, its cancel rows aside). -/
def clausesRead (S : CRow) (R : CVTy) (Tc : CVTy) : Option (List (CQual × CVTy × CVTy)) :=
  (clausesReadF S R Tc).map (·.map Prod.fst)

/-- The cancel rows read with a handler's operations, as `Row.ofEff`'s `fs`: the `j`-th, and the
empty cancel row past the end.  `[spec §27]` -/
def finsOf (Fs : List CCTy) : Nat → CCTy := fun j => Fs.getD j (.ret .unit)

/-- The operations a clause's type under BOXED-κ may be the type of (`[spec §28]`): a control
operation `A ↠^q B` (its argument `A ⊗ [@d] κ`), then an abortive one. -/
def clauseCandsB : CVTy → List (CQual × CVTy × CVTy)
  | .bang (.thunk (.arr (.tensor A (.box d K)) _)) =>
      (match kRead K with | some (q, B) => [(q, A, B)] | none => []) ++
        [(.cancel, .tensor A (.box d K), .zero)]
  | .bang (.thunk (.arr A _)) => [(.cancel, A, .zero)]
  | _ => []

/-- The cancel row a clause's type under BOXED-κ gives its operation, as `clauseFin`.
`[spec §27, §28]` -/
def clauseFinB (S : CRow) (c : CVTy) (e : CQual × CVTy × CVTy) : CCTy :=
  if BoCa.Fig16.LogRel.Core.capB e.1 e.2.2 then
    match c with
    | .bang (.thunk (.arr (.tensor _ (.box _ K)) _)) => kFin S K
    | _ => .ret .unit
  else .ret .unit

/-- The first candidate whose clause type under BOXED-κ at `@d`, at its cancel row, is `c` up to
`[α]`. -/
def firstClauseB (S : CRow) (R : CVTy) (d : CLife) (c : CVTy) :
    List (CQual × CVTy × CVTy) → Option ((CQual × CVTy × CVTy) × CCTy)
  | [] => none
  | e :: es =>
    let F := clauseFinB S c e
    if tyEqV (BoCa.Fig16.LogRel.Core.clauseTyB S R d e F) c then some (e, F)
      else firstClauseB S R d c es

/-- The operations `E` of a handler whose clauses receive `κ` boxed at `@d`, each with its cancel
row, read back from the type of its clauses' tuple, with `clausesTyB S R d E fs` that type up to
`[α]`.  `[spec §27, §28]` -/
def clausesReadB (S : CRow) (R : CVTy) (d : CLife) : (Tc : CVTy) →
    Option (List ((CQual × CVTy × CVTy) × CCTy))
  | .unit => some []
  | .tensor c rest => do
    let e ← firstClauseB S R d c (clauseCandsB c)
    let E ← clausesReadB S R d rest
    pure (e :: E)
  | _ => none

/-- The lifetime a clause tuple's type boxes its continuations at: that of its first clause whose
argument is `A ⊗ [@d] κ`, `κ` a continuation's type. -/
def clausesBoxOf : CVTy → Option CLife
  | .tensor (.bang (.thunk (.arr (.tensor _ (.box d K)) _))) rest =>
      if (kRead K).isSome then some d else clausesBoxOf rest
  | .tensor _ rest => clausesBoxOf rest
  | _ => none

/-- A reading of a handler's clause tuple: BOXED-κ's at `@d` (SPEC §28), or the plain one, each
with its operations' cancel rows `Fs` (SPEC §27). -/
inductive ClausesAt where
  | boxed (d : CLife) (Es : List (CQual × CVTy × CVTy)) (Fs : List CCTy)
  | plain (Es : List (CQual × CVTy × CVTy)) (Fs : List CCTy)

/-- The clause tuple's type a reading rebuilds: `clausesTyB S R d E fs` or `clausesTy S R E fs`. -/
def ClausesAt.ty (S : CRow) (R : CVTy) : ClausesAt → CVTy
  | .boxed d Es Fs => BoCa.Fig16.LogRel.Core.clausesTyB S R d Es (finsOf Fs)
  | .plain Es Fs => BoCa.Fig16.LogRel.Core.clausesTy S R Es (finsOf Fs)

/-- A clause tuple's type read back, up to `[α]`: as BOXED-κ's where it reads so, which the checker
prefers to the plain reading (that would read a clause `!U(A ⊗ [@d] κ ⊸ F_Σ R)` as an abortive
operation's); else plainly. The handler's clauses are then carried to the type the reading
rebuilds (`ClausesAt.ty`, `convVal`).  `[spec §19, §28]` -/
def clausesReadAt (S : CRow) (R : CVTy) (Tc : CVTy) : Option ClausesAt :=
  match (do let d ← clausesBoxOf Tc; let Es ← clausesReadB S R d Tc; pure (d, Es)) with
  | some (d, Es) => some (.boxed d (Es.map Prod.fst) (Es.map Prod.snd))
  | none => (clausesReadF S R Tc).map fun Es => .plain (Es.map Prod.fst) (Es.map Prod.snd)

/-- `h_ret`'s type `!U(A -o F_S R)` read back. -/
def retRead (Tr : CVTy) :
    Option (Σ' (S : CRow) (A R : CVTy), BoCa.Fig16.LogRel.Core.retTy S A R = Tr) :=
  match Tr with
  | .bang (.thunk (.arr A C)) =>
    match effRowOf? C with
    | some ⟨S, R, h⟩ => some ⟨S, A, R, by rw [← h]; rfl⟩
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

/-- `B` occurs in `A`, up to `[α]`. -/
def occursTy (B : CVTy) : CVTy → Bool
  | .tensor X Y => tyEqV (.tensor X Y) B || occursTy B X || occursTy B Y
  | .sum X Y => tyEqV (.sum X Y) B || occursTy B X || occursTy B Y
  | .ref X => tyEqV (.ref X) B || occursTy B X
  | .box a X => tyEqV (.box a X) B || occursTy B X
  | .bang X => tyEqV (.bang X) B || occursTy B X
  | .mu X => tyEqV (.mu X) B || occursTy B X
  | .fam X => tyEqV (.fam X) B || occursTy B X
  | A => tyEqV A B

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

/-- Why slot `i` was not consumed where a path does not consume it. -/
def Env.notConsumed (E : Env) (T : List CVTy) (i : Nat) : String :=
  match T[i]? with
  | some A => if consumableB A then "" else
      s!", and its type `{E.ppV A}` is linear and is not consumable" ++ E.closeHint A false
  | none => ""

/-- The two parts of a `case` or a `<,>` do not consume the same variables. -/
def mergeErr (E : Env) (T : List CVTy) (sp : Span) (what₁ what₂ intro : String)
    (u₁ w₁ u₂ w₂ : List Bool) : Error :=
  match firstMissing u₁ u₂ w₂, firstMissing u₂ u₁ w₁ with
  | some i, _ => ⟨sp, s!"{intro}{E.slotName i} is consumed in {what₁} but not in {what₂}" ++
      E.notConsumed T i⟩
  | _, some i => ⟨sp, s!"{intro}{E.slotName i} is consumed in {what₂} but not in {what₁}" ++
      E.notConsumed T i⟩
  | _, _ => ⟨sp, "internal error: merge"⟩

/-- A binder's variable is neither consumed nor consumed when its scope closes. -/
def unconsumed (E : Env) (sp : Span) (x : String) (A : CVTy) : Error :=
  if consumableB A then
    ⟨sp, s!"`{x}` is not consumed in its scope, and it cannot be consumed where its scope ends"⟩
  else ⟨sp, s!"`{x}` is not consumed in its scope, and its type `{E.ppV A}` is linear and " ++
    "is not consumable" ++ E.closeHint A false⟩

def mismatch (sp : Span) (want got : String) : Error :=
  ⟨sp, s!"type mismatch: expected `{want}`, but this has type `{got}`"⟩

/-! ### Small steps shared by the cases -/

section
variable {Δ : LifeCtx} {T : List CVTy}

/-- A value of `B` at `A`: equal, or equal up to the names of lifetime binders by `[α]`
(`convVal`, SPEC §3). -/
def convV (E : Env) (sp : Span) (A : CVTy) (r : Σ B : CVTy, Res Δ T (.val B)) :
    Except Error (Res Δ T (.val A)) :=
  match convVal (at_ sp) A r with
  | some r' => pure r'
  | none => throw (mismatch sp (E.ppV A) (E.ppV r.1))

/-- A computation of `D` at `C`: equal, equal up to the names of lifetime binders by `[α]`
(SPEC §3), or `F_Σ′ A` within `F_Σ A` by `[sub]` (SPEC §19) then `[α]` (`convComp`). -/
def convC (E : Env) (sp : Span) (C : CCTy) (r : Σ D : CCTy, Res Δ T (.comp D)) :
    Except Error (Res Δ T (.comp C)) :=
  match convComp (at_ sp) C r with
  | .ok r' => pure r'
  | .error .mismatch => throw (mismatch sp (E.ppC C) (E.ppC r.1))
  | .error (.row S' S) => throw ⟨sp, s!"type mismatch: expected `{E.ppC C}`, but this has type " ++
      s!"`{E.ppC r.1}`: its row `{ppRow E S'}` is not within `{ppRow E S}`"⟩

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
def Env.push (E : Env) (x : Option String) : Env :=
  { E with vars := x :: E.vars, own := false :: E.own, cap := false :: E.cap }

/-- A binder's live slot `x : A`, owed to its scope when `A` is linear and is consumable
(SPEC §12). -/
def Env.pushOwn (E : Env) (x : String) (A : CVTy) : Env :=
  { E with vars := some x :: E.vars, own := (!A.persistent && consumableB A) :: E.own,
           cap := false :: E.cap }

/-- A binder owes exactly the slot that is consumable.  `[spec §12]` -/
theorem Env.pushOwn_own (E : Env) (x : String) (A : CVTy) :
    (E.pushOwn x A).own.head? = some (decide (LinearConsumable A)) := by
  simp only [Env.pushOwn, List.head?_cons, Option.some.injEq]
  rw [Bool.eq_iff_iff]
  simp [LinearConsumable, Linear, consumableB_iff]

/-- Nothing owed: a terminal computation, checked before what it leaves owed is consumed. What it
was owed is held for the values in it (`Env.cap`).  `[spec §12]` -/
def Env.clearOwn (E : Env) : Env := { E with own := [], cap := orPad E.own E.cap }



/-- What is still owed after the slots `u` are consumed. -/
def Env.minus (E : Env) (u : List Bool) : Env :=
  { E with own := andL E.own (u.map (! ·)), cap := andL E.cap (u.map (! ·)) }

/-- The owed slots a computation mentions by name, where the name is not shadowed. -/
def Env.ownIn (E : Env) (p : String → Bool) : Env :=
  { E with own := (List.range E.own.length).map fun i =>
      E.own.getD i false && match E.vars[i]? with
        | some (some x) => lookupVar x E.vars == some i && p x
        | _ => false }

/-- The environment of a computation inside a value (`thunk M`, `thunkv N`, `run M`): owed the
slots owed to the computation the value is in that it mentions, as the head of `x <- M; N` is,
and holding nothing.  `[spec §12]` -/
def Env.capture (E : Env) (p : String → Bool) : Env :=
  ({ E with own := orPad E.own E.cap, cap := [] } : Env).ownIn p

/-- The environment of a `def`'s body at a use: its own scope, no variables or lifetimes of the
use site but the persistent externs (the operations of SPEC §11, which carry no authority; a
capability is not persistent), its type parameters bound. -/
def Env.forDef (E : Env) (T : List CVTy) (d : DefInfo) (tps : List (String × CVTy)) : Env :=
  let n := E.vars.length
  let vars := (List.range n).map fun i =>
    if n ≤ i + E.nExt && (T[i]?.map (·.persistent)).getD false then E.vars.getD i none else none
  ⟨d.scope, vars, [], tps, [], E.nExt, none, []⟩

def inDef (x : String) (sp : Span) (e : Error) : Error :=
  { e with msg := s!"{e.msg}\n  in the body of `{x}`, used at {sp.start.render}" }

def thunkvLam : String :=
  "the body of `thunkv` must erase to a λ: `fun`, `Fun` or `<M, N>`, possibly under " ++
  "`delay_in`/`delay_out`/`stream_in`/`stream_out` or an ascription (syntax-core §6.4); " ++
  "eta-expand it"

def notBang (E : Env) (T : List CVTy) (sp : Span) : Option Nat → Error
  | some i => ⟨sp, s!"`!thunk` promotes only over flat types (scalars and tuples of them), but " ++
      s!"{E.slotName i}, of type `{E.slotTy T i}`, which is not flat, is used inside: capture it " ++
      "in an ordinary closure"⟩
  | none => ⟨sp, thunkvLam⟩

section
variable {Δ : LifeCtx} {T : List CVTy}

/-! ### Consumes (SPEC §12) -/

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
position (`x <- M; N`, `let`, `case`, `<M, N>`, `fun`, `Fun`, `nu_in`, an ascription) and the
handler site, which owes its handled body the owed variables the body mentions.  `[spec §12]` -/
def _root_.Frontend.Comp.terminal : Comp → Bool
  | .bind .. | .letUnit .. | .letPair .. | .case .. | .with_ .. | .lam .. | .lamL ..
  | .nuIn .. | .ascribe .. | .unwind .. | .handle .. => false
  | _ => true

/-- The slots to consume before a terminal computation: owed, and neither used nor absorbed by it. -/
def owedLeft : List Bool → List Bool → List Bool → Nat → List Nat
  | o :: os, u :: us, w :: ws, i => (if o && !u && !w then [i] else []) ++ owedLeft os us ws (i + 1)
  | _, _, _, _ => []

section
variable {Δ : LifeCtx} {T : List CVTy}

/-- `consumeE A xᵢ; M` for the slot `i`. -/
def consumeOne {C : CCTy} (sp : Span) (i : Nat) (r : Res Δ T (.comp C)) :
    Except Error (Res Δ T (.comp C)) :=
  match hi : T[i]? with
  | some A =>
    if hA : consumableB A = true then
      if h : overlapOK T (oneL T i) r.F.u = true then
        pure (rConsume (at_ sp) (at_ sp) i A hi (consumableB_sound hA)
          (BoCa.Fig16.LogRel.Core.consumeE_closed (consumableB_sound hA))
          (BoCa.Fig16.LogRel.Core.consumeE_effFree A) r h)
      else throw ⟨sp, "internal error: a consumed slot is used"⟩
    else throw ⟨sp, "internal error: an owed slot is not consumable"⟩
  | none => throw ⟨sp, "internal error: an owed slot is out of range"⟩

/-- The binders' slots `0 … k − 1` of a scope whose body can leave none of them live, each with a
consume, consumed by it at the head of the body (`consumeSlot_derives`): the body neither uses such
a slot nor can weaken it, as under `boxed[@a]`, whose context must outlive `@a` (`[]I`), a slot
of `Unk` among them. Such a slot is not owed (an owed one is consumed at the terminal), so its type
is persistent or a borrow, and its consume does nothing observable.  `[spec §12]` -/
def consumeStuck {C : CCTy} (sp : Span) (k : Nat) (r : Res Δ T (.comp C)) :
    Except Error (Res Δ T (.comp C)) :=
  (List.range k).foldlM (init := r) fun r i =>
    if !(r.F.u.getD i false) && !(r.F.w.getD i true) && (T[i]?.map consumableB).getD false then
      consumeOne sp i r
    else pure r

/-- Consume what the terminal computation `r` leaves owed, the lowest index (the most recently
bound variable) first. -/
def consumeOwed {C : CCTy} (E : Env) (sp : Span) (r : Res Δ T (.comp C)) :
    Except Error (Res Δ T (.comp C)) :=
  (owedLeft E.own r.F.u r.F.w 0).foldr (fun i acc => do consumeOne sp i (← acc)) (pure r)

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
    match hi : T[i]? with
    | some B =>
      -- `M` at `B -o C`, `B` the argument's type up to `[α]` (`convComp`).
      match convComp (at_ sp) (.arr B C) ⟨_, rM⟩ with
      | .ok rM =>
        if h : overlapOK T rM.F.u (oneL T i) = true then pure (rApp { sp, name := x.name } rM i hi h)
        else throw (splitErr E T sp rM.F.u (oneL T i))
      | .error _ => throw (mismatch x.span (E.ppV A) (E.slotTy T i))
    | none => throw ⟨x.span, "internal error: variable out of range"⟩

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
  let r₁ ← consumeStuck x.span 1 r₁
  let r₂ ← consumeStuck y.span 1 r₂
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
    match effRowOf? C with
    | some ⟨_, _, hC⟩ =>
      match lamDeadIt sp (hC ▸ rM) with
      | some r => pure (hC ▸ r)
      | none => rLam { sp, name := x.name } <$> popL E x.span x.name rM.F
    | none => rLam { sp, name := x.name } <$> popL E x.span x.name rM.F
  | _, rM => do
    let rM ← consumeStuck x.span 1 rM
    rLam { sp, name := x.name } <$> popL E x.span x.name rM.F

/-! ### Effectful bindings  `[spec §19]` -/

/-- A computation at the row `S′`, at the row `S`: `[sub]`, or `[sub]` then `[α]` (`convRow`). -/
def liftRow (E : Env) (sp : Span) {S' : CRow} {A : CVTy} (S : CRow)
    (r : Res Δ T (.comp (effOf S' A))) : Except Error (Res Δ T (.comp (effOf S A))) :=
  match convRow (at_ sp) S r with
  | .ok r' => pure r'
  | .error _ => throw ⟨sp, s!"this computation performs the operations `{ppRow E S'}`, which are " ++
    s!"not within the row `{ppRow E S}` here"⟩

/-- A synthesized computation at the row `S`: a returner chain within it. -/
def atRow (E : Env) (sp : Span) (S : CRow) :
    (Σ C : CCTy, Res Δ T (.comp C)) → Except Error (Σ B : CVTy, Res Δ T (.comp (effOf S B)))
  | ⟨C, r⟩ =>
    match effRowOf? C with
    | some ⟨_, B, hC⟩ => do pure ⟨B, ← liftRow E sp S (hC ▸ r)⟩
    | none => throw ⟨sp, s!"after a computation that performs operations, this must have a " ++
        s!"type `F[…] B`, but it has type `{E.ppC C}`"⟩

/-- The finaliser of an effectful binding: the consumes of the non-persistent slots `u` (the
slots the rest of the computation uses), under the binder's dead slot, at the pure row (SPEC §24:
a finaliser lets no raise escape). It runs when an abortive operation of the bound computation
stops the rest. SPEC §19's consume glue: `[then]`'s `D`, inserted as SPEC §12 inserts consumes. -/
def finalOf (E : Env) (sp : Span) (S : CRow) (u : List Bool) :
    Except Error (Res Δ (.unit :: T) (.comp (effOf [] .unit))) := do
  -- The row has an operation that resumes and may be cancelled (`capB`): the finaliser runs at
  -- its cancel. Otherwise only an abort stops the rest.
  let cancels := S.any fun o => BoCa.Fig16.LogRel.Core.capB o.q o.B
  let idx := (List.range T.length).filter fun i =>
    u.getD i false && !((T[i]?.map (·.persistent)).getD true)
  let r0 : Res Δ (.unit :: T) (.comp (.ret .unit)) := rRet (at_ sp) (rUnit (at_ sp))
  for i in idx do
    match T[i]? with
    | some A =>
      unless consumableB A do
        if cancels then
          throw ⟨sp, s!"{E.slotName i}, of type `{E.ppV A}`, is live across an operation that " ++
            "may be cancelled: the cancel runs a finaliser (`[then]`) that consumes it by its " ++
            "consume, and its type is linear and not consumable" ++ E.closeHint A true⟩
        else throw ⟨sp, s!"{E.slotName i}, of type `{E.ppV A}`, is live across a computation " ++
          "that may abort, and its type is linear and not consumable, and an abort abandons " ++
          "only a value that holds no owned cell" ++ E.closeHint A true⟩
    | none => throw ⟨sp, "internal error: a slot is out of range"⟩
  -- In reverse binding order, as at the end of a path (SPEC §12, `consumeOwed`): the lowest index,
  -- the most recently bound slot, is consumed first, so it is wrapped last, outermost.
  idx.reverse.foldlM (init := r0) fun r i => consumeOne sp (i + 1) r

/-- A marked scheme's derived node, over its checked term (SPEC §3). -/
def markIt {j : Jdg} (sp : Span) (k : SchemeMark) (r : Res Δ T j) : Except Error (Res Δ T j) :=
  match rMarked (at_ sp) k r with
  | some r' => pure r'
  | none => err sp s!"internal error: a marked scheme ({repr k}) is not the scheme's term"

/-- `[then]` with `M` at its row `SM` and the finaliser at its row `SD` (non-empty), the cancel-row
premises decided: `rowLeB` (`Σ_M ≤ Σ`, `Σ_D ≤ Σ`), `thenFinB` (each cancel row of `Σ_M` read holds
`F ⋈ Σ_D`), `pendPersB` on `Σ_M`, `Div` not in `Σ_D`.  `[spec §27]` -/
def thenAt (E : Env) (sp : Span) (x : String) {S SM SD : CRow} {A B : CVTy} {tN : TExpr}
    {sN : CRow} {pN : Pins} (hNZ : S.NZ) (hUq : S.Uniq)
    (rM : Res Δ T (.comp (effOf SM A)))
    (rD : Res Δ (.unit :: T) (.comp (effOf SD .unit)))
    (F' : Fam T (fun L => (TTied pN sN Δ (mkCtx (A :: T) (true :: L)) tN (.comp (effOf S B)) ∧
      TTied rD.pins rD.sigs Δ (mkCtx (.unit :: T) (false :: L)) rD.t (.comp (effOf SD .unit))) ∧
      (S.UnrD → BoCa.Fig16.LogRel.Core.Ctx.Banged (mkCtx T L)))) :
    Except Error (Res Δ T (.comp (effOf S B))) :=
  if h : overlapOK T rM.F.u F'.u = true then
    if hMS : rowLeB SM S = true then
      if hDS : rowLeB SD S = true then
        if hfin : thenFinB SM S SD = true then
          if hSD : BoCa.Fig16.LogRel.Core.Row.divB SD = false then
            let fin := fun (hP : SD.UnrD → SM.PendPers) =>
              rEffThenD (atB sp [x]) hNZ hUq (rowLeB_sound hMS) (rowLeB_sound hDS) hfin hP hSD
                rM F' h
            if hu : Row.unrDB SD = true then
              if hp : pendPersB SM = true then pure (fin fun _ => pendPersB_sound hp)
              else throw ⟨sp, s!"the finaliser may meet an operation that resumes more " ++
                s!"than once, so the errors pending below it, those of the row " ++
                s!"`{ppRow E SM}`, must have persistent arguments"⟩
            else pure (fin fun hU => absurd (Row.unrDB_iff.mpr hU) (by simp [hu]))
          else throw ⟨sp, "a finaliser may not loop: its row holds `Div`"⟩
        else
          let bad := SM.filter fun o => o.finRead && match BoCa.Fig16.LogRel.Core.Row.find S o.n o.i with
            | some o' => !thenLeB o.fin SD o'.fin
            | none => true
          throw ⟨sp, s!"the finaliser performs `{ppRow E SD}`, which runs when a " ++
            s!"continuation captured below it is cancelled: the cancel row of " ++
            ", ".intercalate (bad.map fun o => s!"{o.n}.{o.i}") ++
            s!" must hold what the finaliser performs (SPEC §27)"⟩
      else throw ⟨sp, s!"the finaliser's row `{ppRow E SD}` is not within `{ppRow E S}`"⟩
    else throw ⟨sp, s!"the row `{ppRow E SM}` of the computation is not within `{ppRow E S}`"⟩
  else throw (splitErr E T sp rM.F.u F'.u)

/-- `[then]` at the row `S`: `N` (its binder `x` closed) and the finaliser `D` at one context, `D`
at its own row `SD`. At `SD = []`, `effThenA`, `M` at `S`; else `[then]` (`thenAt`), `M` at its own
row `SM` where the checker found one (`rMs`, SPEC §27: a capturable operation the finaliser
performs is then not one of `M`'s, whose cancel row would have to hold it), else at `S`.
`[spec §27]` -/
def thenIt (E : Env) (sp : Span) (x : String) {S SD : CRow} {A B : CVTy} {tN : TExpr} {sN : CRow}
    {pN : Pins}
    (rM : Res Δ T (.comp (effOf S A)))
    (rMs : Option (Σ SM : CRow, Res Δ T (.comp (effOf SM A))))
    (FN : Fam T (fun L => TTied pN sN Δ (mkCtx (A :: T) (true :: L)) tN (.comp (effOf S B))))
    (rD : Res Δ (.unit :: T) (.comp (effOf SD .unit))) :
    Except Error (Res Δ T (.comp (effOf S B))) := do
  if hNZ : Row.nzB S = true then
    if hUq : Row.uniqB S = true then
      let FD ← popD sp rD.F
      if s₁ : subL FN.u (orL FD.u FD.w) = true then
        if s₂ : subL FD.u (orL FN.u FN.w) = true then
          let F := FN.merge FD s₁ s₂
          let F' : Fam T (fun L => (TTied pN sN Δ (mkCtx (A :: T) (true :: L)) tN (.comp (effOf S B)) ∧
              TTied rD.pins rD.sigs Δ (mkCtx (.unit :: T) (false :: L)) rD.t
                (.comp (effOf SD .unit))) ∧
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
          if h0 : SD.isEmpty = true then
            if h : overlapOK T rM.F.u F'.u = true then
              pure (rEffThen (atB sp [x]) (List.isEmpty_iff.mp h0) (Row.nzB_sound hNZ)
                (Row.uniqB_sound hUq) rM F' h)
            else throw (splitErr E T sp rM.F.u F'.u)
          else
            -- The finaliser performs (SPEC §27): `[then]` at its row `SD`, `M` at its own row.
            match rMs with
            | some ⟨_, rM'⟩ => thenAt E sp x (Row.nzB_sound hNZ) (Row.uniqB_sound hUq) rM' rD F'
            | none => thenAt E sp x (Row.nzB_sound hNZ) (Row.uniqB_sound hUq) rM rD F'
        else throw (mergeErr E T sp "the finaliser" "the rest" "after this computation, "
          FD.u FD.w FN.u FN.w)
      else throw (mergeErr E T sp "the rest" "the finaliser" "after this computation, "
        FN.u FN.w FD.u FD.w)
    else throw ⟨sp, s!"the row `{ppRow E S}` has an operation twice"⟩
  else throw ⟨sp, s!"the row `{ppRow E S}` has an operation of the reserved name 0"⟩

/-- `x <- M; N` whose head `M` performs operations, at the row `S` (SPEC §19). At a row with no
cancellable or unrestricted operation, or when every slot `N` uses holds no owned cell (and is `!`
at an unrestricted row), `[let]`; otherwise `[then]`, with the finaliser `finalOf`: the
consumes of the slots `N` uses. -/
def effBind (E : Env) (sp : Span) (x : Ident) {S : CRow} {A B : CVTy}
    (rM : Res Δ T (.comp (effOf S A))) (rN : Res Δ (A :: T) (.comp (effOf S B))) :
    Except Error (Res Δ T (.comp (effOf S B))) := do
  let rN ← consumeStuck x.span 1 rN
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
      thenIt E sp x.name rM none FN rD
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

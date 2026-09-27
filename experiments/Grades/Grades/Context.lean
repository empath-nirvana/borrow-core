import Grades.Algebra
import Core.Fundamental

/-!
# Grades — graded contexts and their premises

A graded slot carries a type and a grade.  A **profile** fixes the endpoint type conditions:
which types a droppable grade may sit at (`drop`), which types promotion may scale (`prom`), and
whether the erased-position rules are present.  A copyable grade always asks for a persistent type
(`VTy.persistent`).

* `Profile.core` is Core as it stands: `drop = persistent`, `prom = !`-types, no erasure.
* `Profile.graded` is the one-principle reading: `drop = forgettable` (`Imm`, `Mut`, persistent
  types), `prom = persistent` (implied by the copyable condition at `ω · Γ`), erasure present.

The premises: `GSplit` (per-slot `g = g₁ + g₂`, the sum's type condition checked), `GDead`
(every slot droppable), `GSolo` (one live slot, the rest droppable), and the scaling `ω · Γ`.
`GCtx.erase` reads a graded context as a Core context (live iff the grade is not `[0,0]`) and
`GCtx.embed` grades a Core context by the defaults-by-type rule (`dflt`).
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Graded
open BoCa
open Grades
open Grades.Grade

/-- `Imm`, `Mut` and persistent types: a value of one may be dropped (the lender reclaims a
borrow, and a persistent value holds nothing). -/
def VTy.forgettable : VTy → Bool
  | .imm _ _ => true
  | .mut _ _ => true
  | T => T.persistent

/-- `!A`. -/
def VTy.isBang : VTy → Bool
  | .bang _ => true
  | _ => false

theorem VTy.persistent_of_isBang : ∀ {T : VTy}, VTy.isBang T = true → T.persistent = true
  | .bang _, _ => rfl

theorem VTy.forgettable_of_persistent : ∀ {T : VTy}, T.persistent = true → VTy.forgettable T = true
  | .imm _ _, _ => rfl
  | .mut _ _, _ => rfl
  | .unit, h | .zero, h | .unk, h | .int _, h | .bang _, h | .tvar _, h | .tensor _ _, h
  | .sum _ _, h | .box _ _, h | .mu _, h | .thunk _, h | .ref _, h => h

/-- The endpoint type conditions of a grading discipline. -/
structure Profile where
  /-- Types a droppable grade other than `[0,0]` may sit at. -/
  drop : VTy → Bool
  /-- Types a live slot may have under promotion. -/
  prom : VTy → Bool
  /-- The erased-position rules are present. -/
  erasure : Bool

/-- Core as it stands. -/
def Profile.core : Profile := ⟨VTy.persistent, VTy.isBang, false⟩

/-- The graded reading: affine at forgettable types, promotion at persistent types, erasure. -/
def Profile.graded : Profile := ⟨VTy.forgettable, VTy.persistent, true⟩

/-- `g` may sit at `T` under `P`. -/
def Profile.Ok (P : Profile) (g : Grade) (T : VTy) : Prop := g.ok (P.drop T) T.persistent = true

structure GSlot where
  ty : VTy
  g : Grade

abbrev GCtx := List GSlot

/-- A graded context as a Core context: a slot is live iff its grade is not `[0,0]`. -/
def GCtx.erase (Γ : GCtx) : Ctx VTy := Γ.map fun s => ⟨s.ty, s.g.live⟩

/-- The default grade of a live slot: `[0,∞]` at a persistent type, `[1,1]` otherwise. -/
def dflt (T : VTy) : Grade := if T.persistent then .unrestricted else .linear

/-- A Core context, graded by the defaults: a dead slot at `[0,0]`, a live one at `dflt`. -/
def GCtx.embed (Γ : Ctx VTy) : GCtx := Γ.map fun s => ⟨s.ty, if s.live then dflt s.ty else .erased⟩

/-- `r · Γ`. -/
def GCtx.scale (r : Grade) (Γ : GCtx) : GCtx := Γ.map fun s => ⟨s.ty, r * s.g⟩

@[simp] theorem erase_nil : GCtx.erase [] = [] := rfl
@[simp] theorem erase_cons (s : GSlot) (Γ : GCtx) :
    GCtx.erase (s :: Γ) = ⟨s.ty, s.g.live⟩ :: GCtx.erase Γ := rfl
@[simp] theorem embed_nil : GCtx.embed [] = [] := rfl
@[simp] theorem embed_cons (s : Slot VTy) (Γ : Ctx VTy) :
    GCtx.embed (s :: Γ) = ⟨s.ty, if s.live then dflt s.ty else .erased⟩ :: GCtx.embed Γ := rfl

theorem dflt_live (T : VTy) : (dflt T).live = true := by
  unfold dflt; split <;> rfl

theorem dflt_ok_core (T : VTy) : Profile.core.Ok (dflt T) T := by
  unfold dflt Profile.Ok Profile.core
  split <;> simp_all [Grade.ok, Grade.droppable, Grade.copyable, Grade.live, Grade.lo, Grade.hi]

theorem erase_embed : ∀ Γ : Ctx VTy, (GCtx.embed Γ).erase = Γ
  | [] => rfl
  | ⟨T, true⟩ :: Γ => by simp [dflt_live, erase_embed Γ]
  | ⟨T, false⟩ :: Γ => by simp [erase_embed Γ]; rfl

theorem erase_scale_ω : ∀ Γ : GCtx, (GCtx.scale ω Γ).erase = Γ.erase
  | [] => rfl
  | s :: Γ => by
      simp only [GCtx.scale, List.map_cons, erase_cons] at *
      rw [live_ω_mul]
      exact congrArg _ (erase_scale_ω Γ)

/-! ### The premises -/

/-- `Γ = Γ₁ + Γ₂`, slot by slot, the sum's type condition checked. -/
inductive GSplit (P : Profile) : GCtx → GCtx → GCtx → Prop where
  | nil : GSplit P [] [] []
  | cons {Γ Γ₁ Γ₂ : GCtx} {T : VTy} {g g₁ g₂ : Grade} (hg : g = g₁ + g₂) (hok : P.Ok g T) :
      GSplit P Γ Γ₁ Γ₂ → GSplit P (⟨T, g⟩ :: Γ) (⟨T, g₁⟩ :: Γ₁) (⟨T, g₂⟩ :: Γ₂)

/-- The slot may be dropped: its grade's lower endpoint is `0`, at a type the grade allows. -/
def GDrop (P : Profile) (s : GSlot) : Prop := s.g.droppable = true ∧ P.Ok s.g s.ty

/-- Every slot may be dropped. -/
def GDead (P : Profile) (Γ : GCtx) : Prop := ∀ s ∈ Γ, GDrop P s

/-- `Γ = x : T` up to droppable slots: slot `i` is live at `T`, the others droppable. -/
inductive GSolo (P : Profile) : GCtx → Nat → VTy → Prop where
  | here {Γ : GCtx} {T : VTy} {g : Grade} (hl : g.live = true) (hok : P.Ok g T) (hd : GDead P Γ) :
      GSolo P (⟨T, g⟩ :: Γ) 0 T
  | there {Γ : GCtx} {s : GSlot} {i : Nat} {T : VTy} (hs : GDrop P s) :
      GSolo P Γ i T → GSolo P (s :: Γ) (i + 1) T

/-- Every slot's grade may sit at its type. -/
def GOk (P : Profile) (Γ : GCtx) : Prop := ∀ s ∈ Γ, P.Ok s.g s.ty

/-- Every live slot's type satisfies the profile's promotion condition. -/
def PromOk (P : Profile) (Γ : GCtx) : Prop := ∀ s ∈ Γ, s.g.live = true → P.prom s.ty = true

theorem GDead.nil (P : Profile) : GDead P [] := fun _ h => absurd h (by simp)

theorem GDead.cons {P : Profile} {s : GSlot} {Γ : GCtx} (hs : GDrop P s) (h : GDead P Γ) :
    GDead P (s :: Γ) := by
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact hs
  · exact h t ht

theorem GDead.head {P : Profile} {s : GSlot} {Γ : GCtx} (h : GDead P (s :: Γ)) : GDrop P s :=
  h s List.mem_cons_self

theorem GDead.tail {P : Profile} {s : GSlot} {Γ : GCtx} (h : GDead P (s :: Γ)) : GDead P Γ :=
  fun t ht => h t (List.mem_cons_of_mem _ ht)

theorem ok_erased (P : Profile) (T : VTy) : P.Ok .erased T := by
  unfold Profile.Ok; cases P.drop T <;> cases T.persistent <;> rfl

theorem gdrop_erased (P : Profile) (T : VTy) : GDrop P ⟨T, .erased⟩ := ⟨rfl, ok_erased P T⟩

/-! ### Every profile: a graded split is a Core split -/

/-- A graded split reads as `Ctx.SplitP` of the erasures: two live summands make a copyable
sum, whose type condition is persistence (`Ctx.SplitP.dup`). -/
theorem GSplit.toSplitP {P : Profile} : ∀ {Γ Γ₁ Γ₂ : GCtx}, GSplit P Γ Γ₁ Γ₂ →
    Ctx.SplitP Γ.erase Γ₁.erase Γ₂.erase
  | _, _, _, .nil => .nil
  | _, _, _, .cons (T := T) (g₁ := g₁) (g₂ := g₂) hg hok h => by
      subst hg
      have ih := h.toSplitP
      simp only [erase_cons]
      rw [live_add]
      cases h₁ : g₁.live <;> cases h₂ : g₂.live
      · exact .dead ih
      · exact .right ih
      · exact .left ih
      · have hc := copyable_add g₁ g₂ h₁ h₂
        have hp : T.persistent = true := by
          have := hok
          simp only [Profile.Ok, Grade.ok, hc, Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
          exact this.2
        exact .dup hp ih

/-! ### The Core profile: dead and solo are `Ctx.DeadP` and `Ctx.SoloP` -/

theorem gdrop_core_toDeadP {s : GSlot} (hs : GDrop Profile.core s) {Γ : Ctx VTy}
    (h : Ctx.DeadP Γ) : Ctx.DeadP (⟨s.ty, s.g.live⟩ :: Γ) := by
  obtain ⟨hd, hok⟩ := hs
  cases hl : s.g.live
  · exact .cons h
  · refine .drop ?_ h
    simp only [Profile.Ok, Profile.core, Grade.ok, hd, hl, Bool.and_self, Bool.not_true,
      Bool.false_or, Bool.and_eq_true] at hok
    exact hok.1

theorem GDead.toDeadP : ∀ {Γ : GCtx}, GDead Profile.core Γ → Ctx.DeadP Γ.erase
  | [], _ => .nil
  | _ :: _, h => gdrop_core_toDeadP h.head (GDead.toDeadP h.tail)

theorem gdrop_core_toSoloP {s : GSlot} (hs : GDrop Profile.core s) {Γ : Ctx VTy} {i : Nat}
    {T : VTy} (h : Ctx.SoloP Γ i T) : Ctx.SoloP (⟨s.ty, s.g.live⟩ :: Γ) (i + 1) T := by
  obtain ⟨hd, hok⟩ := hs
  cases hl : s.g.live
  · exact .there h
  · refine .skip ?_ h
    simp only [Profile.Ok, Profile.core, Grade.ok, hd, hl, Bool.and_self, Bool.not_true,
      Bool.false_or, Bool.and_eq_true] at hok
    exact hok.1

theorem GSolo.toSoloP : ∀ {Γ : GCtx} {i : Nat} {T : VTy}, GSolo Profile.core Γ i T →
    Ctx.SoloP Γ.erase i T
  | _, _, _, .here hl _ hd => by
      simp only [erase_cons, hl]
      exact .here hd.toDeadP
  | _, _, _, .there hs h => gdrop_core_toSoloP hs h.toSoloP

/-- Under the Core profile, a promotable context's erasure is `!Γ`. -/
theorem PromOk.toPersistent {Γ : GCtx} (h : PromOk Profile.core Γ) : Persistent Γ.erase := by
  intro s hs hl
  simp only [GCtx.erase, List.mem_map] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have hb : VTy.isBang t.ty = true := h t ht hl
  revert hb
  cases t.ty <;> simp [VTy.isBang]

/-! ### The Core premises, graded by the defaults -/

theorem SplitP.toGSplit : ∀ {Γ Γ₁ Γ₂ : Ctx VTy}, Ctx.SplitP Γ Γ₁ Γ₂ →
    GSplit Profile.core (GCtx.embed Γ) (GCtx.embed Γ₁) (GCtx.embed Γ₂)
  | _, _, _, .nil => .nil
  | _, _, _, .left (T := T) h => .cons (Grade.add_zero _).symm (dflt_ok_core T) (SplitP.toGSplit h)
  | _, _, _, .right (T := T) h => .cons (Grade.zero_add _).symm (dflt_ok_core T) (SplitP.toGSplit h)
  | _, _, _, .dead (T := T) h => .cons rfl (ok_erased _ T) (SplitP.toGSplit h)
  | _, _, _, .dup (T := T) hT h =>
      .cons (by rw [show dflt T = .unrestricted by simp [dflt, hT]]; rfl) (dflt_ok_core T)
        (SplitP.toGSplit h)

theorem DeadP.toGDead : ∀ {Γ : Ctx VTy}, Ctx.DeadP Γ → GDead Profile.core (GCtx.embed Γ)
  | _, .nil => GDead.nil _
  | _, .cons (T := T) h => GDead.cons (gdrop_erased _ T) (DeadP.toGDead h)
  | _, .drop (T := T) hT h => GDead.cons (by
      refine ⟨by simp [dflt, hT]; rfl, ?_⟩
      simp only [ite_true]
      exact dflt_ok_core T) (DeadP.toGDead h)

theorem SoloP.toGSolo : ∀ {Γ : Ctx VTy} {i : Nat} {T : VTy}, Ctx.SoloP Γ i T →
    GSolo Profile.core (GCtx.embed Γ) i T
  | _, _, _, .here (T := T) h => .here (dflt_live T) (dflt_ok_core T) (DeadP.toGDead h)
  | _, _, _, .there (S := S) h => .there (gdrop_erased _ S) (SoloP.toGSolo h)
  | _, _, _, .skip (S := S) hS h => .there (by
      refine ⟨by simp [dflt, hS]; rfl, ?_⟩
      simp only [ite_true]
      exact dflt_ok_core S) (SoloP.toGSolo h)

/-- `!Γ`, graded by the defaults, is fixed by `ω ·`, well graded and promotable. -/
theorem Persistent.toGraded : ∀ {Γ : Ctx VTy}, Persistent Γ →
    GCtx.scale ω (GCtx.embed Γ) = GCtx.embed Γ ∧ GOk Profile.core (GCtx.scale ω (GCtx.embed Γ)) ∧
      PromOk Profile.core (GCtx.embed Γ)
  | [], _ => ⟨rfl, fun _ h => by simp [GCtx.scale] at h, fun _ h => absurd h (by simp)⟩
  | s :: Γ, hp => by
      have hp' : Persistent Γ := fun t ht hl => hp t (List.mem_cons_of_mem _ ht) hl
      obtain ⟨ih₁, ih₂, ih₃⟩ := Persistent.toGraded hp'
      obtain ⟨T, l⟩ := s
      cases l with
      | false =>
          refine ⟨?_, ?_, ?_⟩
          · simp only [GCtx.scale, List.map_cons, embed_cons] at ih₁ ⊢
            rw [ih₁]; rfl
          · intro t ht
            simp only [GCtx.scale, embed_cons, List.map_cons, List.mem_cons] at ht
            rcases ht with rfl | ht
            · exact ok_erased _ _
            · exact ih₂ t ht
          · intro t ht hl
            rcases List.mem_cons.mp ht with rfl | ht
            · exact absurd hl (by simp [Grade.live])
            · exact ih₃ t ht hl
      | true =>
          obtain ⟨A, hA⟩ := hp ⟨T, true⟩ List.mem_cons_self rfl
          simp only at hA
          subst hA
          refine ⟨?_, ?_, ?_⟩
          · simp only [GCtx.scale, List.map_cons, embed_cons] at ih₁ ⊢
            rw [ih₁]; rfl
          · intro t ht
            simp only [GCtx.scale, embed_cons, List.map_cons, List.mem_cons] at ht
            rcases ht with rfl | ht
            · rfl
            · exact ih₂ t ht
          · intro t ht hl
            rcases List.mem_cons.mp ht with rfl | ht
            · rfl
            · exact ih₃ t ht hl

/-! ### The graded profile: one principle -/

/-- The surface default by type: `[0,∞]` at a persistent type, `[0,1]` at `Imm`/`Mut`, `[1,1]`
otherwise.  Only `[0,0]` (`ghost`) and `[1,∞]` (`must_use`) are ever written. -/
def surfaceDefault (T : VTy) : Grade :=
  if T.persistent then .unrestricted else if VTy.forgettable T then .affine else .linear

theorem surfaceDefault_ok (T : VTy) : Profile.graded.Ok (surfaceDefault T) T := by
  unfold surfaceDefault Profile.Ok Profile.graded
  by_cases hp : T.persistent = true
  · simp [hp, VTy.forgettable_of_persistent hp, Grade.ok, Grade.droppable, Grade.live,
      Grade.copyable, Grade.lo, Grade.hi]
  · by_cases hf : VTy.forgettable T = true
    · simp [hp, hf, Grade.ok, Grade.droppable, Grade.live, Grade.copyable, Grade.lo, Grade.hi]
    · simp [hp, hf, Grade.ok, Grade.droppable, Grade.live, Grade.copyable, Grade.lo, Grade.hi]

/-- Under the graded profile, a well-graded `ω · Γ` is promotable: `hi = ∞` already asks for a
persistent type, so promotion needs no premise of its own. -/
theorem promOk_graded {Γ : GCtx} (h : GOk Profile.graded (GCtx.scale ω Γ)) :
    PromOk Profile.graded Γ := by
  intro s hs hl
  have hok := h ⟨s.ty, ω * s.g⟩ (List.mem_map.mpr ⟨s, hs, rfl⟩)
  rw [ω_mul_live s.g hl] at hok
  simp only [Profile.Ok, Profile.graded, Grade.ok] at hok
  show s.ty.persistent = true
  generalize VTy.forgettable s.ty = f at hok
  generalize s.ty.persistent = p at hok ⊢
  revert hok; cases f <;> cases p <;> decide

/-- Scaling a live slot of non-persistent type by `ω` is ill graded, under every profile. -/
theorem scale_nonpersistent_rejected (P : Profile) {T : VTy} (hT : T.persistent = false)
    {g : Grade} (hg : g.live = true) : ¬ GOk P (GCtx.scale ω [⟨T, g⟩]) := by
  intro h
  have hok := h ⟨T, ω * g⟩ List.mem_cons_self
  rw [ω_mul_live g hg] at hok
  simp [Profile.Ok, Grade.ok, hT, Grade.copyable, Grade.hi] at hok

end BoCa.Fig16.LogRel.Core.Graded

end

import Grades.Soundness
import Core.Weaken
import Core.Folds
import Core.DelayPrograms

/-!
# Grades — constants that become derived, and the no-ω-poison check

**Constants.**  `copy : !A ⊸ !A ⊗ !A`, `forget : !A ⊸ 1` and `forget : Unk ⊸ 1` are derivable in
`CDerives` as it stands, from `λ`, `⊗`, variables and `Ctx.SplitP.dup`/`Ctx.DeadP.drop`
(`copyBang_core`, `forgetBang_core`, `forgetUnk_core`).  Under the graded profile,
`forget : Imm @a A ⊸ 1` and `forget : Mut @a A ⊸ 1` are derivable too: the binder is at `[0,1]`
and the body drops it (`forgetImm_graded`, `forgetMut_graded`).  `copy : Imm @a A ⊸ …` stays a
constant: `Imm` is not persistent, so `[0,∞]` may not sit at it.

**No ω-poison.**  The only rule whose conclusion context is scaled is promotion
(`bangThunkF`/`bangThunkV`, at `GCtx.scale ω Γ`); no rule scales a premise.  The fold, `fixD` and
`unfoldS` rules are constants at a droppable context.  Scaling a live non-persistent slot is
ill graded (`scale_nonpersistent_rejected`).  Every `CDerives` derivation, the fold, `fixD` and
`unfoldS` programs included, is a graded derivation whose non-persistent slots are `[1,1]`
(`embed_copyable`); two instances are spelled out: the delay driver's state and step
(`fs_graded`) and the fold program's free function (`progOpen_graded`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Graded
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open Grades
open Grades.Grade

/-! ### Constants derivable in `CDerives` as it stands -/

theorem deadP_selfSplit : ∀ {Γ : Ctx VTy}, Ctx.DeadP Γ → Ctx.SplitP Γ Γ Γ
  | _, .nil => .nil
  | _, .cons h => .dead (deadP_selfSplit h)
  | _, .drop hT h => .dup hT (deadP_selfSplit h)

/-- `copy : !A ⊸ !A ⊗ !A` without the constant. -/
theorem copyBang_core {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    CDerives Δ Γ copy (.val (.thunk (.arr (.bang A) (.ret (.tensor (.bang A) (.bang A)))))) :=
  .thunkV rfl (.lam (.ret (.tensorI (.dup rfl (deadP_selfSplit hΓ)) (.var (.here hΓ))
    (.var (.here hΓ)))))

/-- `forget : !A ⊸ 1` without the constant. -/
theorem forgetBang_core {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    CDerives Δ Γ forget (.val (.thunk (.arr (.bang A) (.ret .unit)))) :=
  .thunkV rfl (.lam (.ret (.unitI (.drop rfl hΓ))))

/-- `forget : Unk ⊸ 1` without the constant. -/
theorem forgetUnk_core {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) :
    CDerives Δ Γ forget (.val axForgetUnkTy) :=
  .thunkV rfl (.lam (.ret (.unitI (.drop rfl hΓ))))

/-! ### Constants derivable under the graded profile -/

/-- `forget : Imm @a A ⊸ 1`: the binder at `[0,1]`, dropped. -/
theorem forgetImm_graded {Δ : LifeCtx} {Γ : GCtx} {a : Lifetime.Life} {A : VTy}
    (hΓ : GDead Profile.graded Γ) : GDerives Profile.graded Δ Γ forget (.val (axForgetImmTy a A)) :=
  .thunkV rfl (.lam (g := .affine) rfl (.ret (.unitI (GDead.cons ⟨rfl, rfl⟩ hΓ))))

/-- `forget : Mut @a A ⊸ 1`: the binder at `[0,1]`, dropped. -/
theorem forgetMut_graded {Δ : LifeCtx} {Γ : GCtx} {a : Lifetime.Life} {A : VTy}
    (hΓ : GDead Profile.graded Γ) : GDerives Profile.graded Δ Γ forget (.val (axForgetMutTy a A)) :=
  .thunkV rfl (.lam (g := .affine) rfl (.ret (.unitI (GDead.cons ⟨rfl, rfl⟩ hΓ))))

/-- `[0,1]` does not sit at `Imm` under the Core profile: Core has no affine drop there. -/
theorem affine_imm_not_core (a : Lifetime.Life) (A : VTy) : ¬ Profile.core.Ok .affine (.imm a A) := by
  simp [Profile.Ok, Profile.core, Grade.ok, VTy.persistent, Grade.droppable, Grade.live,
    Grade.copyable, Grade.lo, Grade.hi]

/-! ### No ω-poison -/

/-- The default grading puts `[0,∞]` only at persistent types. -/
theorem embed_copyable : ∀ (Γ : Ctx VTy), ∀ s ∈ GCtx.embed Γ, s.g.copyable = true →
    s.ty.persistent = true := by
  intro Γ s hs hc
  simp only [GCtx.embed, List.mem_map] at hs
  obtain ⟨⟨T, l⟩, -, rfl⟩ := hs
  cases l with
  | false => exact absurd hc (by simp [Grade.copyable, Grade.hi])
  | true =>
      simp only [ite_true, dflt] at hc ⊢
      revert hc; cases T.persistent <;> decide

/-- The delay driver's `f s` inside `⟨·, ·⟩`: the step `f : U(S ⊸ D A)` and the state `S = Ref 1`
are each `[1,1]`.  `fixD` charges neither at `ω`. -/
theorem fs_graded {A : VTy} :
    GDerives Profile.graded LifeCtx.empty
      [⟨.unit, .erased⟩, ⟨.sum .unit .unit, .erased⟩,
       ⟨.thunk (.arr (.ref .unit) (.delay A)), .linear⟩, ⟨.ref .unit, .linear⟩]
      (.app (.var 2) (.var 3)) (.comp (.delay A)) :=
  (CDerives.toGraded (d_fs (A := A) (S := .ref .unit))).mono Profile.core_le_graded

/-- The fold program open in a fold `g : !U(∀'a. Imm 'a M ⊸ F R)` (at `[0,∞]`) and a free
function `U(M ⊸ F 1)` (at `[1,1]`), for `M` the boxed list. -/
theorem progOpen_graded {R : VTy} {build : Expr}
    (hb : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives LifeCtx.empty Γ build (.val listL))
    (hM : ∀ z, ¬ VFree z listL) (hR0 : ∀ z, ¬ VFree z R) (hR : ∀ Δ a, VOutlives Δ a R)
    (hinst : VTy.instLife 0 (.var 0) (VTy.lolli (.imm (.var 0) listL) R) =
      VTy.lolli (.imm (.var 0) listL) R) :
    GDerives Profile.graded LifeCtx.empty
      [⟨fTy listL R, .unrestricted⟩, ⟨.lolli listL .unit, .linear⟩] (progOpen build)
      (.comp (.ret R)) :=
  (CDerives.toGraded (d_progOpen hb hM hR0 hR hinst)).mono Profile.core_le_graded

/-! ### Grades at the defaults carry no information -/

/-- A context graded by the defaults is the grading of its erasure: at default grades, a graded
context is a Core context (with `erase_embed`, a bijection). -/
theorem embed_erase : ∀ {Γ : GCtx}, (∀ s ∈ Γ, s.g = .erased ∨ s.g = dflt s.ty) →
    GCtx.embed (GCtx.erase Γ) = Γ
  | [], _ => rfl
  | ⟨T, g⟩ :: Γ, h => by
      have ih := embed_erase (Γ := Γ) fun s hs => h s (List.mem_cons_of_mem _ hs)
      simp only [erase_cons, embed_cons, ih]
      rcases h ⟨T, g⟩ List.mem_cons_self with h1 | h1
      · have : g = .erased := h1
        subst this; rfl
      · have : g = dflt T := h1
        subst this; simp [dflt_live]

/-! ### Promotion over a persistent capture -/

/-- `x : I32 ⊢ thunk (return x) : !U(F I32)`, promoted over `ω · (x : I32)`.  Under the Core
profile the promotion premise fails: `I32` is persistent but not a `!`-type. -/
theorem promote_int (w : Width) :
    GDerives Profile.graded LifeCtx.empty (GCtx.scale ω [⟨.int w, .linear⟩])
      (.val (.lam (.var 1))) (.val (.bang (.thunk (.ret (.int w))))) :=
  .bangThunkF (fun s hs => by simp [GCtx.scale] at hs; subst hs; rfl)
    (fun s hs _ => by simp at hs; subst hs; rfl)
    (.ret (.var (.there (gdrop_erased _ _) (.here rfl rfl (GDead.nil _)))))

theorem promote_int_not_core (w : Width) : ¬ PromOk Profile.core [⟨.int w, .linear⟩] :=
  fun h => absurd (h _ List.mem_cons_self rfl) (by simp [Profile.core, VTy.isBang])

end BoCa.Fig16.LogRel.Core.Graded

end

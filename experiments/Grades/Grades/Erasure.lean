import Grades.Derived

/-!
# Grades — erasure: a capability token at grade `0`

A slot at `[0,0]` is dead: a variable leaf may not use it (`erased_not_solo`), a split sends it
to both sides at `[0,0]` (`erased_add`), and a dead context drops it.  The only place it may
appear is an erased position: the argument of an erased application `app0`, which mentions it
at no cost.  At run time the erased parameter receives `inj₁ ()` (`ghostV`), a constant holding
`∅`.

The program: a capability `tok : Cap` (`Cap = Ref 1`, an owned type that could never be dropped
if it were held) is a grade-`0` parameter of `main`, passed at grade `0` to `use`, which passes
it at grade `0` to a privileged operation `priv` and then runs `cImmBorrow` (allocate a cell,
borrow it immutably, load through the borrow, end the borrow, free the cell):

    main = λ⁰tok. (λ⁰t. priv [t] to u. u; cImmBorrow) [tok]
    priv = λ⁰t. ()

`main_derives` types it under `Profile.graded`; `prog_runs` runs `main [inj₁ ()]` from the empty
memory to `()` and the empty memory.  `prog_runs_any` runs `main v` to the same result for
**every** value `v` in the token's place: the token's value is never inspected.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Graded
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open Grades
open Grades.Grade

/-! ### Grade `0` is unusable at run time -/

theorem erased_not_solo {P : Profile} {A : VTy} {Γ : GCtx} : ¬ GSolo P (⟨A, .erased⟩ :: Γ) 0 A := by
  intro h
  cases h with
  | here hl => exact absurd hl (by decide)

theorem erased_add : ∀ g₁ g₂ : Grade, g₁ + g₂ = .erased → g₁ = .erased ∧ g₂ = .erased := by
  decide

/-! ### The program -/

/-- The capability's type, `Ref 1`. -/
abbrev capT : VTy := .ref .unit

/-- `U(Ghost Cap ⊸ F 1)`: a function with an erased `Cap` parameter. -/
abbrev capFnTy : VTy := .thunk (.arr (ghost capT) (.ret .unit))

/-- `priv = λ⁰t. ()`. -/
def privE : Expr := .val (.lam (.val .unit))

/-- `use`'s body, at `t` (index `0`) and `tok` (index `1`):
`priv to p. p [t] to u. u; cImmBorrow`. -/
def useE : Expr :=
  bindE privE (bindE (.app (.var 0) (.val ghostV)) (.seq (.var 0) cImmBorrow))

/-- `main`'s body, at `tok` (index `0`): `(λ⁰t. useE) to f. f [tok]`. -/
def mainBody : Expr := bindE (.val (.lam useE)) (.app (.var 0) (.val ghostV))

def mainE : Expr := .val (.lam mainBody)

/-- `main [inj₁ ()]`. -/
def prog : Expr := .app mainE (.val ghostV)

theorem d_priv {Δ : LifeCtx} {Γ : GCtx} (hΓ : GDead Profile.graded Γ) :
    GDerives Profile.graded Δ Γ privE (.val capFnTy) :=
  .thunkV rfl (.lam0 rfl (.ret (.unitI (GDead.cons (gdrop_erased _ _) hΓ))))

theorem gdead_erased {P : Profile} : ∀ {Γ : GCtx}, (∀ s ∈ Γ, s.g = .erased) → GDead P Γ := by
  intro Γ h s hs
  obtain ⟨T, g⟩ := s
  obtain rfl : g = .erased := h _ hs
  exact gdrop_erased P T

theorem gsplit_erased {P : Profile} : ∀ {Γ : GCtx}, (∀ s ∈ Γ, s.g = .erased) → GSplit P Γ Γ Γ
  | [], _ => .nil
  | ⟨T, g⟩ :: Γ, h => by
      obtain rfl : g = .erased := h _ List.mem_cons_self
      exact .cons rfl (ok_erased P T)
        (gsplit_erased fun s hs => h s (List.mem_cons_of_mem _ hs))

/-- The `cImmBorrow` part, with every slot of the context at `[0,0]`. -/
theorem d_cImmBorrow_erased :
    GDerives Profile.graded LifeCtx.empty
      [⟨.unit, .erased⟩, ⟨capFnTy, .erased⟩, ⟨capT, .erased⟩, ⟨capT, .erased⟩]
      cImmBorrow (.comp (.ret .unit)) :=
  (CDerives.toGraded (CDerives.append_dead
    (Γ' := [⟨.unit, false⟩, ⟨capFnTy, false⟩, ⟨capT, false⟩, ⟨capT, false⟩])
    (by repeat constructor) cImmBorrow_derives)).mono Profile.core_le_graded

theorem d_use :
    GDerives Profile.graded LifeCtx.empty [⟨capT, .erased⟩, ⟨capT, .erased⟩] useE
      (.comp (.ret .unit)) := by
  -- `priv to p`
  refine .bind (gsplit_erased (by simp)) (.ret (d_priv (gdead_erased (by simp))))
    (g := .linear) rfl ?_
  -- `p [t] to u`
  refine .bind (Γ₁ := [⟨capFnTy, .linear⟩, ⟨capT, .erased⟩, ⟨capT, .erased⟩])
    (Γ₂ := [⟨capFnTy, .erased⟩, ⟨capT, .erased⟩, ⟨capT, .erased⟩])
    (.cons rfl rfl (gsplit_erased (by simp)))
    (.app0 (i := 1) rfl ⟨.erased, rfl⟩
      (.force (C := .arr (ghost capT) (.ret .unit)) (.here rfl rfl (gdead_erased (by simp)))))
    (g := .linear) rfl ?_
  -- `u; cImmBorrow`
  exact .unitE (Γ₁ := [⟨.unit, .linear⟩, ⟨capFnTy, .erased⟩, ⟨capT, .erased⟩, ⟨capT, .erased⟩])
    (.cons rfl rfl (gsplit_erased (by simp)))
    (.var (.here rfl rfl (gdead_erased (by simp)))) d_cImmBorrow_erased

theorem d_mainBody :
    GDerives Profile.graded LifeCtx.empty [⟨capT, .erased⟩] mainBody (.comp (.ret .unit)) :=
  .bind (gsplit_erased (by simp)) (.ret (.thunkV rfl (.lam0 rfl d_use))) (g := .linear) rfl
    (.app0 (Γ := [⟨capFnTy, .linear⟩, ⟨capT, .erased⟩]) (i := 1) rfl ⟨.erased, rfl⟩
      (.force (C := .arr (ghost capT) (.ret .unit)) (.here rfl rfl (gdead_erased (by simp)))))

/-- `main : Ghost Cap ⊸ F 1`, the token at grade `0` throughout. -/
theorem main_derives :
    GDerives Profile.graded LifeCtx.empty [] mainE (.comp (.arr (ghost capT) (.ret .unit))) :=
  .lam0 rfl d_mainBody

theorem prog_sem : SemC (ℍ := ℍ) LifeCtx.empty [] prog (.ret .unit) :=
  app0_compat (fundamentalGraded main_derives)

/-- `main [inj₁ ()]` runs from the empty memory to `()` and the empty memory. -/
theorem prog_runs : BoCa.BoLo.Steps (ℍ := ℍ) Adequacy.emptyMem prog Adequacy.emptyMem (.val .unit) :=
  corollary33 prog prog_sem

/-- `main v` runs to `()` and the empty memory for every `v` in the token's place: the erased
slot is dead in `main`'s body, so its value is never inspected. -/
theorem prog_runs_any (v : Val) :
    BoCa.BoLo.Steps (ℍ := ℍ) Adequacy.emptyMem (.app mainE (.val v)) Adequacy.emptyMem
      (.val .unit) := by
  have hb : SemC (ℍ := ℍ) LifeCtx.empty [⟨capT, false⟩] mainBody (.ret .unit) :=
    fundamentalGraded d_mainBody
  have h1 := hb LSub.empty [v] [] PMap.empty Adequacy.models_empty
    (gDenC_dead_cons _ v (gDenC_nil _ _))
  rw [substAll_cons', Adequacy.psub_nil] at h1
  have h2 : cC (.ret .unit) [] LSub.empty (.app mainE (.val v)) PMap.empty :=
    cC_head (.ret .unit) (fun μ => Head.beta μ mainBody v) [] LSub.empty PMap.empty h1
  obtain ⟨w, hs, rfl⟩ := theorem32 _ (· = Val.unit) h2
  exact hs

end BoCa.Fig16.LogRel.Core.Graded

end

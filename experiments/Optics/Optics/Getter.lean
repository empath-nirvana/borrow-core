import Optics.Programs

/-!
# Optics — `Imm` as a getter  (stage 2)

A getter from `S` onto the view family `G` is a closed value with the typing

    run : S(@a) ⊸ (∀'x ⊏ ⊓Δ. G('x) ⊸ ['x] T) ⊸ T

and a characterisation of its runs.  Nothing comes back beside `T`: the lender's side is not
threaded through the callback, so there is no put.  `withload` is the instance
(`immGetter`): `Imm @a A ⊸ (∀'x ⊏ ⊓Δ. Imm̲ 'x A ⊸ ['x] T) ⊸ T`.

* `immGetter.runs`: every run of `withload s g` loads the cell `s`, hands its content to `g`,
  and does nothing else.  So the put is the identity: `withload` itself never writes
  (`withload_read`: with the reading callback, the heap is unchanged and the result is the
  content).
* `copy_runs` and `get_copy`: `copy` duplicates the handle and changes nothing, and two reads
  through the two copies return the same content and leave the heap unchanged, the view
  commuting with duplication (Clarke et al. Def 3.3's comonoid condition, at runs).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Optics
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Kont)
open BoCa.Programs (app2 alloc' free' unitNoLeak)

attribute [local simp] Expr.subst Expr.shift Val.val_shift Expr.shift_zero

/-- `S(@a) ⊸ (∀'x ⊏ @b. G('x) ⊸ ['x] T) ⊸ T`. -/
def getterTy (S G : Lifetime.Life → VTy) (a : Lifetime.Life) (x : LifeVar) (b : Lifetime.Life)
    (T : VTy) : VTy :=
  .lolli (S a) (.lolli (cbTy G x b T) T)

/-- A getter: a closed value, its typing, and its runs. -/
structure Getter (S G : Lifetime.Life → VTy) where
  run : Val
  closed : closedAt 0 run.1 = true
  Adm : LifeCtx → Lifetime.Life → LifeVar → Prop
  wf : ∀ {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {x : LifeVar} {T : VTy},
    Adm Δ a x → plainV T = true → Ctx.Dead Γ →
    CDerives Δ Γ (.val run) (.val (getterTy S G a x Δ.meetOfDom T))
  Obs : Heap → Heap → Val → Val → Val → Prop
  runs : ∀ {μ μ' : Heap} {s g w : Val}, closedAt 0 s.1 = true → closedAt 0 g.1 = true →
    (Steps μ (app2 (.val run) s.1 g.1) μ' w.1 ↔ Obs μ μ' s g w)

/-- `withload` as a value. -/
def withloadV : Val := .lam (.val (.lam (.app (.app v0 unit') (.app load' v1))))

theorem withloadV_eq : withloadV.1 = withload := rfl

/-- `withload s g`: `s` is a cell `ℓ`, and `g` runs on its content from the same heap. -/
theorem steps_withload_iff {μ μ' : Heap} {s g w : Val} (hg : closedAt 0 g.1 = true) :
    Steps μ (app2 (.val withloadV) s.1 g.1) μ' w.1 ↔
      ∃ (ℓ : Loc) (v : Val), s = .loc ℓ ∧ μ ℓ = some v ∧ Steps μ (app2 g.1 unit' v.1) μ' w.1 := by
  rw [show Expr.val withloadV = lam2 (.app (.app v0 unit') (.app load' v1)) from rfl,
    steps_app2_iff]
  have e : ((Expr.app (.app v0 unit') (.app load' v1)).subst 1 (s.shift 1 0)).subst 0 g
      = .app (.app g.1 unit') (.app load' s.1) := by
    simp [v0, v1, unit', load', closed_subst hg,
      Expr.subst_shift 0 0 0 g s.1 (le_refl _) (le_refl _)]
  rw [e, steps_appR_iff]
  constructor
  · rintro ⟨μm, v, hl, h⟩
    obtain ⟨ℓ, rfl, hℓ, rfl⟩ := steps_load_val_iff.mp hl
    exact ⟨ℓ, v, rfl, hℓ, h⟩
  · rintro ⟨ℓ, v, rfl, hℓ, h⟩
    exact ⟨μ, v, steps_load_iff.mpr ⟨hℓ, rfl⟩, h⟩

/-- **The `Imm` getter**: `withload : Imm @a A ⊸ (∀'x ⊏ ⊓Δ. Imm̲ 'x A ⊸ ['x] T) ⊸ T`. -/
def immGetter (A : VTy) (hA : plainV A = true) :
    Getter (fun a => .imm a A) (fun c => A.immReborrow c) where
  run := withloadV
  closed := rfl
  Adm Δ _ x := Δ.find? x = none
  wf {Δ Γ a x T} hx hT hΓ := .withload x hΓ.toP hx (plain_noFree hA) (plain_noFree hT)
  Obs μ μ' s g w := ∃ (ℓ : Loc) (v : Val), s = .loc ℓ ∧ μ ℓ = some v ∧
    Steps μ (app2 g.1 unit' v.1) μ' w.1
  runs _ hg := steps_withload_iff hg

/-- `Λ. λy. y`: the reading callback. -/
def readG : Val := .lam (.val (.lam (.var 0)))

/-- **The put is the identity**: reading through `withload` returns the content and leaves the
heap as it was, on every run. -/
theorem withload_read {μ μ' : Heap} {s w : Val} :
    Steps μ (app2 (.val withloadV) s.1 readG.1) μ' w.1 ↔
      ∃ ℓ : Loc, s = .loc ℓ ∧ μ ℓ = some w ∧ μ' = μ := by
  rw [steps_withload_iff rfl]
  constructor
  · rintro ⟨ℓ, v, rfl, hℓ, h⟩
    rw [show readG.1 = lam2 (.var 0) from rfl, steps_app2_unit_iff] at h
    simp only [Expr.subst] at h
    obtain ⟨rfl, rfl⟩ := steps_val_iff.mp h
    exact ⟨ℓ, rfl, hℓ, rfl⟩
  · rintro ⟨ℓ, rfl, hℓ, rfl⟩
    refine ⟨ℓ, w, rfl, hℓ, ?_⟩
    rw [show readG.1 = lam2 (.var 0) from rfl, steps_app2_unit_iff]
    simp only [Expr.subst]
    exact .refl _ _

/-- `copy s` returns `(s, s)` and changes nothing. -/
theorem copy_runs {μ μ' : Heap} {s w : Val} :
    Steps μ (.app copy s.1) μ' w.1 ↔ μ' = μ ∧ w = .pair s s := by
  rw [show copy = Expr.val (Val.lam (.pair v0 v0)) from rfl, steps_beta_iff]
  simp only [Expr.subst, v0, if_true]
  exact steps_val_iff (v := Val.pair s s)

/-- `let (i, j) = copy s; (withload i read, withload j read)`. -/
def getTwice (s : Val) : Expr :=
  .letpair (.app copy s.1)
    (.pair (app2 (.val withloadV) (.var 1) readG.1) (app2 (.val withloadV) (.var 0) readG.1))

/-- **The view commutes with duplication**: two reads through the two copies of an `Imm` return
the same content, and the heap is unchanged. -/
theorem get_copy {μ μ' : Heap} {s w : Val} (hs : closedAt 0 s.1 = true) :
    Steps μ (getTwice s) μ' w.1 ↔
      ∃ (ℓ : Loc) (v : Val), s = .loc ℓ ∧ μ ℓ = some v ∧ μ' = μ ∧ w = .pair v v := by
  rw [getTwice, steps_letpairK_iff]
  have e : ((Expr.pair (app2 (.val withloadV) (.var 1) readG.1)
      (app2 (.val withloadV) (.var 0) readG.1)).subst 0 (s.shift 1 0)).subst 0 s
      = .pair (app2 (.val withloadV) s.1 readG.1) (app2 (.val withloadV) s.1 readG.1) := by
    simp [app2, withloadV, readG, v0, v1, unit', load', closed_shift hs, closed_subst hs]
  constructor
  · rintro ⟨μm, p, hc, h⟩
    obtain ⟨rfl, rfl⟩ := copy_runs.mp hc
    rw [steps_letpair_iff, e, steps_pairL_iff] at h
    obtain ⟨μ₁, a, ha, h⟩ := h
    obtain ⟨b, rfl, hb⟩ := steps_pairR_iff.mp h
    obtain ⟨k, hk, hka, rfl⟩ := withload_read.mp ha
    obtain ⟨k', hk', hkb, rfl⟩ := withload_read.mp hb
    have hkk : k' = k := by rw [hk] at hk'; simpa using hk'.symm
    rw [hkk] at hkb
    have hab : b = a := Option.some.inj (hkb.symm.trans hka)
    rw [hab]
    exact ⟨k, a, hk, hka, rfl, rfl⟩
  · rintro ⟨ℓ, v, rfl, hℓ, rfl, rfl⟩
    refine ⟨μ', .pair (.loc ℓ) (.loc ℓ), copy_runs.mpr ⟨rfl, rfl⟩, ?_⟩
    rw [steps_letpair_iff, e, steps_pairL_iff]
    exact ⟨μ', v, withload_read.mpr ⟨ℓ, rfl, hℓ, rfl⟩,
      steps_pairR_iff.mpr ⟨v, rfl, withload_read.mpr ⟨ℓ, rfl, hℓ, rfl⟩⟩⟩

end BoCa.Fig16.LogRel.Core.Optics

end

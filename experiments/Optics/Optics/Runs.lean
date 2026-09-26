import Core.Steps
import Core.FoldImm

/-!
# Optics — runs as equations

Every law in this experiment is a statement about `Steps`, the machine's runs, and never about
typing.  This file turns the machine's step relation into equations between runs: a run of a
redex is a run of its contractum (`steps_beta_iff`, `steps_load_iff`, …), and a run of `K[e]` to
a value is a run of `e` to a value followed by a run of `K[v]` (`steps_plug_iff`).  Each is an
`↔`, so a law proved with them holds on every run and every run it describes exists.

`alloc` is the machine's only nondeterministic step; no term in this experiment's laws allocates.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Optics
open BoCa
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-! ### Values and contexts -/

/-- A run from a value is empty. -/
theorem steps_val_iff {μ μ' : Heap} {v w : Val} :
    Steps μ v.1 μ' w.1 ↔ μ' = μ ∧ w = v := by
  constructor
  · exact steps_from_val
  · rintro ⟨rfl, rfl⟩; exact .refl _ _

/-- A run of `K[e]` to a value runs `e` to a value, then `K[v]`. -/
theorem steps_plug_iff (K : Kont) {μ μ' : Heap} {e : Expr} {w : Val} :
    Steps μ (K.plug e) μ' w.1 ↔
      ∃ (μm : Heap) (v : Val), Steps μ e μm v.1 ∧ Steps μm (K.plug v.1) μ' w.1 := by
  constructor
  · intro h; exact steps_plug_inv K h rfl rfl
  · rintro ⟨μm, v, h₁, h₂⟩; exact (h₁.plug K).trans h₂

/-- A step determined at the redex: every run continues from it. -/
theorem steps_det_iff {μ μ₁ μ' : Heap} {e e₁ : Expr} {w : Val} (hnv : ¬ IsVal e)
    (hs : Step1 μ e μ₁ e₁) (hu : ∀ ν e', Step1 μ e ν e' → ν = μ₁ ∧ e' = e₁) :
    Steps μ e μ' w.1 ↔ Steps μ₁ e₁ μ' w.1 :=
  ⟨fun h => steps_peel h hnv hu, fun h => .more hs h⟩

/-! ### Redexes: the only step is the head step -/

/-- The only step of an application of a value to a value is its head step. -/
theorem step1_app_head {μ μ₁ : Heap} {f v : Val} {e₁ : Expr}
    (h : Step1 μ (.app f.1 v.1) μ₁ e₁) : Head μ (.app f.1 v.1) μ₁ e₁ :=
  step1_top h fun K c hE hK => by
    cases K with
    | hole => exact absurd rfl hK
    | appR g K =>
        simp only [Kont.plug, Expr.app.injEq] at hE
        exact K.isVal_of_plug (hE.2 ▸ v.2)
    | appL K u =>
        simp only [Kont.plug, Expr.app.injEq] at hE
        exact K.isVal_of_plug (hE.1 ▸ f.2)
    | _ => simp [Kont.plug] at hE

theorem step1_seq_head {μ μ₁ : Heap} {e e₁ : Expr}
    (h : Step1 μ (.seq (.val .unit) e) μ₁ e₁) : Head μ (.seq (.val .unit) e) μ₁ e₁ :=
  step1_top h fun K c hE hK => by
    cases K with
    | hole => exact absurd rfl hK
    | seq K u =>
        simp only [Kont.plug, Expr.seq.injEq] at hE
        exact K.isVal_of_plug (hE.1 ▸ IsVal.unit)
    | _ => simp [Kont.plug] at hE

theorem step1_case_head {μ μ₁ : Heap} {v : Val} {e₁ e₂ e' : Expr}
    (h : Step1 μ (.case v.1 e₁ e₂) μ₁ e') : Head μ (.case v.1 e₁ e₂) μ₁ e' :=
  step1_top h fun K c hE hK => by
    cases K with
    | hole => exact absurd rfl hK
    | case K u₁ u₂ =>
        simp only [Kont.plug, Expr.case.injEq] at hE
        exact K.isVal_of_plug (hE.1 ▸ v.2)
    | _ => simp [Kont.plug] at hE

/-! ### Runs of redexes -/

/-- `(λb) v` runs as `b[v]`. -/
theorem steps_beta_iff {μ μ' : Heap} {b : Expr} {v w : Val} :
    Steps μ (.app (.val (.lam b)) v.1) μ' w.1 ↔ Steps μ (b.subst 0 v) μ' w.1 :=
  steps_det_iff (by simp [Expr.val]) (Step1.head (.beta μ b v))
    (fun _ _ h => step1_beta_inv h)

/-- `let (x, y) = (v₁, v₂); b` runs as `b[v₁, v₂]`. -/
theorem steps_letpair_iff {μ μ' : Heap} {b : Expr} {v₁ v₂ w : Val} :
    Steps μ (.letpair (Val.pair v₁ v₂).1 b) μ' w.1 ↔
      Steps μ ((b.subst 0 (v₂.shift 1 0)).subst 0 v₁) μ' w.1 := by
  refine steps_det_iff (by simp) (Step1.head (.letpair μ v₁ v₂ b)) (fun _ _ h => ?_)
  obtain ⟨u₁, u₂, hu, rfl, rfl⟩ := step1_letpair_inv h
  obtain ⟨rfl, rfl⟩ : v₁ = u₁ ∧ v₂ = u₂ := by
    have := congrArg Subtype.val hu
    simp only [Val.val_pair, Expr.pair.injEq] at this
    exact ⟨Subtype.ext this.1, Subtype.ext this.2⟩
  exact ⟨rfl, rfl⟩

/-- `(); e` runs as `e`. -/
theorem steps_seq_iff {μ μ' : Heap} {e : Expr} {w : Val} :
    Steps μ (.seq (.val .unit) e) μ' w.1 ↔ Steps μ e μ' w.1 := by
  refine steps_det_iff (by simp) (Step1.head (.seq μ e)) (fun _ _ h => ?_)
  have hh := step1_seq_head h
  generalize hE : Expr.seq (.val .unit) e = E at hh
  cases hh <;> simp_all

/-- `case (inj₁ v) {b₁ | b₂}` runs as `b₁[v]`. -/
theorem steps_case₁_iff {μ μ' : Heap} {v w : Val} {b₁ b₂ : Expr} :
    Steps μ (.case (Val.inj₁ v).1 b₁ b₂) μ' w.1 ↔ Steps μ (b₁.subst 0 v) μ' w.1 := by
  refine steps_det_iff (by simp) (Step1.head (.case₁ μ v b₁ b₂)) (fun _ _ h => ?_)
  have hh := step1_case_head (v := Val.inj₁ v) h
  generalize hE : Expr.case (Val.inj₁ v).1 b₁ b₂ = E at hh
  cases hh with
  | case₁ u _ _ =>
      simp only [Val.val_inj₁, Expr.case.injEq, Expr.inj₁.injEq] at hE
      obtain ⟨hv, rfl, rfl⟩ := hE
      obtain rfl : v = u := Subtype.ext hv
      exact ⟨rfl, rfl⟩
  | _ => simp_all

/-- `case (inj₂ v) {b₁ | b₂}` runs as `b₂[v]`. -/
theorem steps_case₂_iff {μ μ' : Heap} {v w : Val} {b₁ b₂ : Expr} :
    Steps μ (.case (Val.inj₂ v).1 b₁ b₂) μ' w.1 ↔ Steps μ (b₂.subst 0 v) μ' w.1 := by
  refine steps_det_iff (by simp) (Step1.head (.case₂ μ v b₁ b₂)) (fun _ _ h => ?_)
  have hh := step1_case_head (v := Val.inj₂ v) h
  generalize hE : Expr.case (Val.inj₂ v).1 b₁ b₂ = E at hh
  cases hh with
  | case₂ u _ _ =>
      simp only [Val.val_inj₂, Expr.case.injEq, Expr.inj₂.injEq] at hE
      obtain ⟨hv, rfl, rfl⟩ := hE
      obtain rfl : v = u := Subtype.ext hv
      exact ⟨rfl, rfl⟩
  | _ => simp_all

/-- `load ℓ` runs to the content of `ℓ`, and changes nothing. -/
theorem steps_load_iff {μ μ' : Heap} {ℓ : Loc} {w : Val} :
    Steps μ (.app load' (Val.loc ℓ).1) μ' w.1 ↔ μ ℓ = some w ∧ μ' = μ := by
  constructor
  · intro h
    generalize hE₀ : Expr.app load' (Val.loc ℓ).1 = E₀ at h
    cases h with
    | refl => exact absurd (hE₀ ▸ w.2) (by simp [load'])
    | more hs t =>
        subst hE₀
        have hh := step1_app_head (f := Val.prim .load) (v := Val.loc ℓ) hs
        generalize hE : Expr.app (Val.prim .load).1 (Val.loc ℓ).1 = E at hh
        cases hh with
        | load k u hk =>
            simp only [Val.val_prim, Val.val_loc, Expr.app.injEq, Expr.loc.injEq] at hE
            obtain ⟨-, rfl⟩ := hE
            obtain ⟨rfl, rfl⟩ := steps_val_iff.mp t
            exact ⟨hk, rfl⟩
        | _ => simp_all
  · rintro ⟨hℓ, rfl⟩
    exact .more (Step1.head (.load _ ℓ w hℓ)) (.refl _ _)

/-- `store ℓ v` writes `v` at a defined `ℓ` and returns `()`. -/
theorem steps_store_iff {μ μ' : Heap} {ℓ : Loc} {v w : Val} :
    Steps μ (.app (.app store' (Val.loc ℓ).1) v.1) μ' w.1 ↔
      (∃ u, μ ℓ = some u) ∧ μ' = μ.upd ℓ v ∧ w = Val.unit := by
  constructor
  · intro h
    generalize hE₀ : Expr.app (.app store' (Val.loc ℓ).1) v.1 = E₀ at h
    cases h with
    | refl => exact absurd (hE₀ ▸ w.2) (by simp [store'])
    | more hs t =>
        subst hE₀
        have hh := step1_app_head (f := Val.storeV (Val.loc ℓ)) (v := v) hs
        generalize hE : Expr.app (Val.storeV (Val.loc ℓ)).1 v.1 = E at hh
        cases hh with
        | store k u u' hk =>
            simp only [Val.val_storeV, Val.val_loc, Expr.app.injEq, Expr.loc.injEq] at hE
            obtain ⟨⟨-, rfl⟩, hv⟩ := hE
            obtain rfl : v = u := Subtype.ext hv
            obtain ⟨rfl, hw⟩ := steps_val_iff.mp t
            exact ⟨⟨u', hk⟩, rfl, hw⟩
        | _ => simp_all
  · rintro ⟨⟨u, hℓ⟩, rfl, rfl⟩
    exact .more (Step1.head (.store _ ℓ v u hℓ)) (.refl _ _)

/-! ### Evaluation order -/

/-- `f e`: the argument first. -/
theorem steps_appR_iff {μ μ' : Heap} {f e : Expr} {w : Val} :
    Steps μ (.app f e) μ' w.1 ↔
      ∃ (μm : Heap) (v : Val), Steps μ e μm v.1 ∧ Steps μm (.app f v.1) μ' w.1 :=
  steps_plug_iff (.appR f .hole)

/-- `e v`: then the function. -/
theorem steps_appL_iff {μ μ' : Heap} {e : Expr} {v w : Val} :
    Steps μ (.app e v.1) μ' w.1 ↔
      ∃ (μm : Heap) (u : Val), Steps μ e μm u.1 ∧ Steps μm (.app u.1 v.1) μ' w.1 :=
  steps_plug_iff (.appL .hole v)

theorem steps_letpairK_iff {μ μ' : Heap} {e b : Expr} {w : Val} :
    Steps μ (.letpair e b) μ' w.1 ↔
      ∃ (μm : Heap) (v : Val), Steps μ e μm v.1 ∧ Steps μm (.letpair v.1 b) μ' w.1 :=
  steps_plug_iff (.letpair .hole b)

theorem steps_seqK_iff {μ μ' : Heap} {e b : Expr} {w : Val} :
    Steps μ (.seq e b) μ' w.1 ↔
      ∃ (μm : Heap) (v : Val), Steps μ e μm v.1 ∧ Steps μm (.seq v.1 b) μ' w.1 :=
  steps_plug_iff (.seq .hole b)

theorem steps_caseK_iff {μ μ' : Heap} {e b₁ b₂ : Expr} {w : Val} :
    Steps μ (.case e b₁ b₂) μ' w.1 ↔
      ∃ (μm : Heap) (v : Val), Steps μ e μm v.1 ∧ Steps μm (.case v.1 b₁ b₂) μ' w.1 :=
  steps_plug_iff (.case .hole b₁ b₂)

/-- `(v, e)` runs `e`. -/
theorem steps_pairR_iff {μ μ' : Heap} {v : Val} {e : Expr} {w : Val} :
    Steps μ (.pair v.1 e) μ' w.1 ↔ ∃ u : Val, w = .pair v u ∧ Steps μ e μ' u.1 := by
  rw [show Expr.pair v.1 e = (Kont.pairR v .hole).plug e from rfl, steps_plug_iff]
  constructor
  · rintro ⟨μm, u, h₁, h₂⟩
    obtain ⟨rfl, rfl⟩ := steps_val_iff (v := Val.pair v u).mp h₂
    exact ⟨u, rfl, h₁⟩
  · rintro ⟨u, rfl, h⟩
    exact ⟨μ', u, h, .refl _ _⟩

/-- `(e₁, e₂)` runs `e₁`, then `e₂`. -/
theorem steps_pairL_iff {μ μ' : Heap} {e₁ e₂ : Expr} {w : Val} :
    Steps μ (.pair e₁ e₂) μ' w.1 ↔
      ∃ (μm : Heap) (v : Val), Steps μ e₁ μm v.1 ∧ Steps μm (.pair v.1 e₂) μ' w.1 :=
  steps_plug_iff (.pairL .hole e₂)

/-- `inj₁ e` runs `e`. -/
theorem steps_inj₁_iff {μ μ' : Heap} {e : Expr} {w : Val} :
    Steps μ (.inj₁ e) μ' w.1 ↔ ∃ u : Val, w = .inj₁ u ∧ Steps μ e μ' u.1 := by
  rw [show Expr.inj₁ e = (Kont.inj₁ .hole).plug e from rfl, steps_plug_iff]
  constructor
  · rintro ⟨μm, u, h₁, h₂⟩
    obtain ⟨rfl, rfl⟩ := steps_val_iff (v := Val.inj₁ u).mp h₂
    exact ⟨u, rfl, h₁⟩
  · rintro ⟨u, rfl, h⟩
    exact ⟨μ', u, h, .refl _ _⟩

/-- `inj₂ e` runs `e`. -/
theorem steps_inj₂_iff {μ μ' : Heap} {e : Expr} {w : Val} :
    Steps μ (.inj₂ e) μ' w.1 ↔ ∃ u : Val, w = .inj₂ u ∧ Steps μ e μ' u.1 := by
  rw [show Expr.inj₂ e = (Kont.inj₂ .hole).plug e from rfl, steps_plug_iff]
  constructor
  · rintro ⟨μm, u, h₁, h₂⟩
    obtain ⟨rfl, rfl⟩ := steps_val_iff (v := Val.inj₂ u).mp h₂
    exact ⟨u, rfl, h₁⟩
  · rintro ⟨u, rfl, h⟩
    exact ⟨μ', u, h, .refl _ _⟩

/-! ### Two-argument application of a closed `λλ` -/

/-- `(λλX) a b` runs as `X[a, b]`. -/
theorem steps_app2_iff {μ μ' : Heap} {X : Expr} {a b w : Val} :
    Steps μ (BoCa.Programs.app2 (lam2 X) a.1 b.1) μ' w.1 ↔
      Steps μ ((X.subst 1 (a.shift 1 0)).subst 0 b) μ' w.1 := by
  simp only [BoCa.Programs.app2, lam2]
  rw [steps_appL_iff]
  constructor
  · rintro ⟨μm, u, h₁, h₂⟩
    have h₁' := steps_beta_iff (b := Expr.val (Val.lam X)) (v := a) |>.mp h₁
    simp only [Expr.val, Val.val_lam, Expr.subst] at h₁'
    obtain ⟨rfl, rfl⟩ := steps_val_iff (v := Val.lam (X.subst 1 (a.shift 1 0))) |>.mp h₁'
    exact steps_beta_iff.mp h₂
  · intro h
    refine ⟨μ, Val.lam (X.subst 1 (a.shift 1 0)), ?_, steps_beta_iff.mpr h⟩
    refine steps_beta_iff (b := Expr.val (Val.lam X)) (v := a) |>.mpr ?_
    simp only [Expr.val, Val.val_lam, Expr.subst]
    exact .refl _ _


/-- `(λλX) () b` runs as `X[(), b]`. -/
theorem steps_app2_unit_iff {μ μ' : Heap} {X : Expr} {b w : Val} :
    Steps μ (BoCa.Programs.app2 (lam2 X) unit' b.1) μ' w.1 ↔
      Steps μ ((X.subst 1 (Val.unit.shift 1 0)).subst 0 b) μ' w.1 :=
  steps_app2_iff (a := Val.unit)

/-! ### Eliminating a value -/

/-- `let (x, y) = s; b` at a value runs only at a pair. -/
theorem steps_letpair_val_iff {μ μ' : Heap} {s w : Val} {b : Expr} :
    Steps μ (.letpair s.1 b) μ' w.1 ↔
      ∃ v₁ v₂ : Val, s = .pair v₁ v₂ ∧
        Steps μ ((b.subst 0 (v₂.shift 1 0)).subst 0 v₁) μ' w.1 := by
  constructor
  · intro h
    obtain ⟨μm, v₁, v₂, h₁, h₂⟩ := steps_letpair_inv h
    obtain ⟨rfl, rfl⟩ := steps_val_iff.mp h₁
    exact ⟨v₁, v₂, rfl, h₂⟩
  · rintro ⟨v₁, v₂, rfl, h⟩
    exact steps_letpair_iff.mpr h

/-- `case s {b₁ | b₂}` at a value runs only at an injection. -/
theorem steps_case_val_iff {μ μ' : Heap} {s w : Val} {b₁ b₂ : Expr} :
    Steps μ (.case s.1 b₁ b₂) μ' w.1 ↔
      (∃ v : Val, s = .inj₁ v ∧ Steps μ (b₁.subst 0 v) μ' w.1) ∨
      (∃ v : Val, s = .inj₂ v ∧ Steps μ (b₂.subst 0 v) μ' w.1) := by
  constructor
  · intro h
    have hstep : ∃ μ₁ e₁, Step1 μ (.case s.1 b₁ b₂) μ₁ e₁ := by
      generalize hE : Expr.case s.1 b₁ b₂ = E at h
      cases h with
      | refl => exact absurd (hE ▸ w.2) (by simp)
      | more hs _ => subst hE; exact ⟨_, _, hs⟩
    obtain ⟨μ₁, e₁, hs⟩ := hstep
    have hh := step1_case_head hs
    generalize hE : Expr.case s.1 b₁ b₂ = E at hh
    cases hh with
    | case₁ v _ _ =>
        simp only [Expr.case.injEq] at hE
        obtain ⟨hv, rfl, rfl⟩ := hE
        obtain rfl : s = .inj₁ v := Subtype.ext hv
        exact .inl ⟨v, rfl, steps_case₁_iff.mp h⟩
    | case₂ v _ _ =>
        simp only [Expr.case.injEq] at hE
        obtain ⟨hv, rfl, rfl⟩ := hE
        obtain rfl : s = .inj₂ v := Subtype.ext hv
        exact .inr ⟨v, rfl, steps_case₂_iff.mp h⟩
    | _ => simp at hE
  · rintro (⟨v, rfl, h⟩ | ⟨v, rfl, h⟩)
    · exact steps_case₁_iff.mpr h
    · exact steps_case₂_iff.mpr h

/-- `load m` at a value runs only at a location. -/
theorem steps_load_val_iff {μ μ' : Heap} {m w : Val} :
    Steps μ (.app load' m.1) μ' w.1 ↔ ∃ ℓ, m = .loc ℓ ∧ μ ℓ = some w ∧ μ' = μ := by
  constructor
  · intro h
    have hstep : ∃ μ₁ e₁, Step1 μ (.app load' m.1) μ₁ e₁ ∧ Steps μ₁ e₁ μ' w.1 := by
      generalize hE : Expr.app load' m.1 = E at h
      cases h with
      | refl => exact absurd (hE ▸ w.2) (by simp [load'])
      | more hs t => subst hE; exact ⟨_, _, hs, t⟩
    obtain ⟨μ₁, e₁, hs, t⟩ := hstep
    have hh := step1_app_head (f := Val.prim .load) (v := m) hs
    generalize hE : Expr.app (Val.prim .load).1 m.1 = E at hh
    cases hh with
    | load k u hk =>
        simp only [Val.val_prim, Expr.app.injEq] at hE
        obtain ⟨-, hm⟩ := hE
        obtain rfl : m = .loc k := Subtype.ext hm
        obtain ⟨rfl, rfl⟩ := steps_val_iff.mp t
        exact ⟨k, rfl, hk, rfl⟩
    | _ => simp_all
  · rintro ⟨ℓ, rfl, h⟩
    exact steps_load_iff.mpr h

/-- **`withswap m f`**: `m` is a cell `ℓ`; `f` runs on its content `s` to `(s′, t)`; `s′` is
stored back in `ℓ`; the result is `(ℓ, t)`. -/
theorem steps_withswap_iff {μ μ' : Heap} {m f w : Val} (hm : closedAt 0 m.1 = true) :
    Steps μ (BoCa.Programs.app2 withswap m.1 f.1) μ' w.1 ↔
      ∃ (ℓ : Loc) (s : Val) (μ₁ : Heap) (s' t : Val), m = .loc ℓ ∧ μ ℓ = some s ∧
        Steps μ (.app f.1 s.1) μ₁ (Val.pair s' t).1 ∧ (∃ u, μ₁ ℓ = some u) ∧
        μ' = μ₁.upd ℓ s' ∧ w = .pair (.loc ℓ) t := by
  rw [show withswap = lam2 (.letpair (.app v0 (.app load' v1))
    (.seq (.app (.app store' v3) v1) (.pair v3 v0))) from rfl, steps_app2_iff]
  have e : ((Expr.letpair (.app v0 (.app load' v1))
      (.seq (.app (.app store' v3) v1) (.pair v3 v0))).subst 1 (m.shift 1 0)).subst 0 f
      = .letpair (.app f.1 (.app load' m.1)) (.seq (.app (.app store' m.1) v1) (.pair m.1 v0)) := by
    simp [v0, v1, v3, load', store', Expr.subst, Val.val_shift, closed_shift hm, closed_subst hm]
  rw [e, steps_letpairK_iff]
  constructor
  · rintro ⟨μm, v, h₁, h₂⟩
    obtain ⟨μa, s, hl, hfs⟩ := steps_appR_iff.mp h₁
    obtain ⟨ℓ, rfl, hℓ, rfl⟩ := steps_load_val_iff.mp hl
    obtain ⟨s', t, rfl, h₃⟩ := steps_letpair_val_iff.mp h₂
    have e₂ : (((Expr.seq (.app (.app store' (Val.loc ℓ).1) v1) (.pair (Val.loc ℓ).1 v0)).subst 0
        (t.shift 1 0)).subst 0 s')
        = .seq (.app (.app store' (Val.loc ℓ).1) s'.1) (Val.pair (.loc ℓ) t).1 := by
      simp [v0, v1, store', Expr.subst, Val.val_shift,
        Expr.subst_shift 0 0 0 s' t.1 (le_refl _) (le_refl _), Expr.shift_zero]
    rw [e₂, steps_seqK_iff] at h₃
    obtain ⟨μs, u, hst, hrest⟩ := h₃
    obtain ⟨hdom, rfl, rfl⟩ := steps_store_iff.mp hst
    have hrest' := steps_seq_iff.mp hrest
    obtain ⟨rfl, rfl⟩ := steps_val_iff.mp hrest'
    exact ⟨ℓ, s, μm, s', t, rfl, hℓ, hfs, hdom, rfl, rfl⟩
  · rintro ⟨ℓ, s, μ₁, s', t, rfl, hℓ, hfs, hdom, rfl, rfl⟩
    refine ⟨μ₁, .pair s' t, steps_appR_iff.mpr ⟨μ, s, steps_load_iff.mpr ⟨hℓ, rfl⟩, hfs⟩, ?_⟩
    refine steps_letpair_iff.mpr ?_
    have e₂ : (((Expr.seq (.app (.app store' (Val.loc ℓ).1) v1) (.pair (Val.loc ℓ).1 v0)).subst 0
        (t.shift 1 0)).subst 0 s')
        = .seq (.app (.app store' (Val.loc ℓ).1) s'.1) (Val.pair (.loc ℓ) t).1 := by
      simp [v0, v1, store', Expr.subst, Val.val_shift,
        Expr.subst_shift 0 0 0 s' t.1 (le_refl _) (le_refl _), Expr.shift_zero]
    rw [e₂, steps_seqK_iff]
    exact ⟨_, Val.unit, steps_store_iff.mpr ⟨hdom, rfl, rfl⟩, steps_seq_iff.mpr (.refl _ _)⟩

/-- `let (m, t) = e; forget m; t` runs `e` to a pair and returns its second component. -/
theorem steps_forgetFst_iff {μ μ' : Heap} {e : Expr} {w : Val} :
    Steps μ (.letpair e (.seq (.app forget (.var 1)) (.var 0))) μ' w.1 ↔
      ∃ m : Val, Steps μ e μ' (Val.pair m w).1 := by
  rw [steps_letpairK_iff]
  have e₀ : ∀ m t : Val, (((Expr.seq (.app forget (.var 1)) (.var 0)).subst 0 (t.shift 1 0)).subst 0 m)
      = .seq (.app forget m.1) t.1 := fun m t => by
    simp [forget, unit', Expr.subst, Val.val_shift,
      Expr.subst_shift 0 0 0 m t.1 (le_refl _) (le_refl _), Expr.shift_zero]
  have hf : ∀ {μ μ' : Heap} {m u : Val}, Steps μ (.app forget m.1) μ' u.1 ↔ μ' = μ ∧ u = Val.unit :=
    fun {μ μ' m u} => by
      rw [show forget = Expr.val (Val.lam unit') from rfl, steps_beta_iff]
      exact steps_val_iff (v := Val.unit)
  constructor
  · rintro ⟨μm, v, h₁, h₂⟩
    obtain ⟨m, t, rfl, h₃⟩ := steps_letpair_val_iff.mp h₂
    rw [e₀, steps_seqK_iff] at h₃
    obtain ⟨μf, u, hfg, hrest⟩ := h₃
    obtain ⟨rfl, rfl⟩ := hf.mp hfg
    obtain ⟨rfl, rfl⟩ := steps_val_iff.mp (steps_seq_iff.mp hrest)
    exact ⟨m, h₁⟩
  · rintro ⟨m, h⟩
    refine ⟨μ', .pair m w, h, steps_letpair_iff.mpr ?_⟩
    rw [e₀, steps_seqK_iff]
    exact ⟨μ', Val.unit, hf.mpr ⟨rfl, rfl⟩, steps_seq_iff.mpr (.refl _ _)⟩

end BoCa.Fig16.LogRel.Core.Optics

end

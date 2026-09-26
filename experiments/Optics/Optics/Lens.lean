import Optics.Runs
import Core.FamilyPrograms
import Core.BlockBorrow

/-!
# Optics — the borrow optic interface  (stage 1)

An optic from a source `S` onto a focus family `F` is a closed value `run` with the typing, at
every admissible `Δ` and fresh callback binder `'x`,

    run : S ⊸ W(∀'x ⊏ ⊓Δ. F('x) ⊸ ['x] T) ⊸ S ⊗ O(T, G)          (G the callback's type)

for every result type `T` in `plainV` (no lifetime, outlives every lifetime).  `W` wraps the
callback (`id`, or `!` for an optic that may drop it) and `O` says what comes back beside the
source (`T` for a lens).  This is the continuation form of a lens: the borrower receives the
focus at a fresh lifetime, and the lender keeps the residual until the callback returns.  `S`
and `F` are indexed by a lifetime `@a`, used only by a borrowed source `Mut @a U`.

Every instance is a closed `CDerives` derivation built from existing rules, so `fundamentalC`
covers it (`Optic.sem`).  The other half of the interface is `runs`: every run of `run s g` to a
value returns **the source `s` itself** paired with the callback's result, and what happens in
between is `Obs`.  That is the continuation form of Riley's Rezip law (`ev ∘ Unzip = id`): the
residual reassembles exactly the source.

| instance | term | source → focus |
|---|---|---|
| `idLens` | `withbor` (form 2) | `Ref V → Mut 'x V`, focus `s` |
| `reLens` | `withbor` (form 3) | `Mut @a V → Mut 'x V`, focus `s` |
| `fstLens` | `withbor` on the first leaf, the second leaf kept | `Ref A ⊗ Ref B → Mut 'x A`, focus `x` of `(x, y)` |
| `famLens` | `withborF2` (`Family.lean`) | `Ref A ⊗ Ref B → Mut 'x A ⊗ Mut 'x B`, focus `s` |
| `Optic.comp` | nesting, the inner optic at `'y ⊏ 'x` | `S → Mut 'x U`, then `Mut 'x U → F('y)` |
| `Optic.lift` | `withswap` around the optic | `Mut @a S → F('x)`, for any optic on an owned `S` |
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Optics
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Kont)
open BoCa.Programs (app2 entailsLt_of_bound interp_meet_left interp_meet_right)

/-! ### Types -/

/-- The callback's type `∀'x ⊏ @b. F('x) ⊸ ['x] T`. -/
def cbTy (F : Lifetime.Life → VTy) (x : LifeVar) (b : Lifetime.Life) (T : VTy) : VTy :=
  .all x b (.lolli (F (.var x)) (.box (.var x) T))

/-- `S(@a) ⊸ W(G) ⊸ S(@a) ⊗ O(T, G)`, with `G = ∀'x ⊏ @b. F('x) ⊸ ['x] T`. -/
def opticTy (S F : Lifetime.Life → VTy) (W : VTy → VTy) (O : VTy → VTy → VTy)
    (a : Lifetime.Life) (x : LifeVar) (b : Lifetime.Life) (T : VTy) : VTy :=
  .lolli (S a) (.lolli (W (cbTy F x b T)) (.tensor (S a) (O T (cbTy F x b T))))

/-- Every value in the heap is closed: what a run of a closed program keeps. -/
def HeapClosed (μ : Heap) : Prop := ∀ ℓ v, μ ℓ = some v → closedAt 0 v.1 = true

/-- A borrow optic: a closed value, its typing at every admissible context, and its runs. -/
structure Optic (S F : Lifetime.Life → VTy) (W : VTy → VTy) (O : VTy → VTy → VTy) where
  run : Val
  closed : closedAt 0 run.1 = true
  /-- The lifetime contexts, source lifetimes and callback binders `run` is typed at. -/
  Adm : LifeCtx → Lifetime.Life → LifeVar → Prop
  wf : ∀ {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {x : LifeVar} {T : VTy},
    Adm Δ a x → plainV T = true → Ctx.Dead Γ →
    CDerives Δ Γ (.val run) (.val (opticTy S F W O a x Δ.meetOfDom T))
  /-- What a run does between receiving `(s, g)` and returning `(s, t)`. -/
  Obs : Heap → Heap → Val → Val → Val → Prop
  /-- **Rezip.** Every run to a value returns the source unchanged. -/
  runs : ∀ {μ μ' : Heap} {s g w : Val}, HeapClosed μ → closedAt 0 s.1 = true →
    closedAt 0 g.1 = true →
    (Steps μ (app2 (.val run) s.1 g.1) μ' w.1 ↔ ∃ t : Val, w = .pair s t ∧ Obs μ μ' s g t)

/-- A lens: the callback is linear and its result is all that comes back beside the source. -/
abbrev Lens (S F : Lifetime.Life → VTy) := Optic S F id (fun T _ => T)

/-- The Fundamental Property at every instance, with no new case. -/
theorem Optic.sem {S F : Lifetime.Life → VTy} {W : VTy → VTy} {O : VTy → VTy → VTy}
    (L : Optic S F W O) {Δ : LifeCtx} {a : Lifetime.Life} {x : LifeVar} {T : VTy}
    (h : L.Adm Δ a x) (hT : plainV T = true) :
    SemV Δ [] (.val L.run) (opticTy S F W O a x Δ.meetOfDom T) :=
  fundamentalC (L.wf h hT .nil)

/-- The callback is run on the focus `f s`, and nothing else happens. -/
def LensObs (Dom : Val → Prop) (f : Val → Val) (μ μ' : Heap) (s g t : Val) : Prop :=
  Dom s ∧ Steps μ (app2 g.1 unit' (f s).1) μ' t.1

/-! ### Closed terms and substitution -/

attribute [local simp] Expr.subst Expr.shift Val.val_shift Expr.shift_zero closed_subst
  closed_shift subst_shift_succ

theorem closedV_shift {v : Val} (h : closedAt 0 v.1 = true) (d c : Nat) : v.shift d c = v :=
  Val.ext (closed_shift h d c)

/-- `withbor` as a value. -/
def withborV : Val := .lam (.val (.lam (.pair v1 (.app (.app v0 unit') v1))))

theorem withborV_eq : withborV.1 = withbor := rfl

theorem withborV_closed : closedAt 0 withborV.1 = true := rfl

/-- `withbor s g` runs as `(s, g () s)`. -/
theorem steps_withbor_iff {μ μ' : Heap} {s g w : Val} :
    Steps μ (app2 (.val withborV) s.1 g.1) μ' w.1 ↔
      ∃ t : Val, w = .pair s t ∧ Steps μ (app2 g.1 unit' s.1) μ' t.1 := by
  rw [show Expr.val withborV = lam2 (.pair v1 (.app (.app v0 unit') v1)) from rfl,
    steps_app2_iff]
  have e : ((Expr.pair v1 (.app (.app v0 unit') v1)).subst 1 (s.shift 1 0)).subst 0 g
      = .pair s.1 (app2 g.1 unit' s.1) := by
    simp [v0, v1, unit', app2, Expr.subst_shift 0 0 0 g s.1 (le_refl _) (le_refl _)]
  rw [e]
  exact steps_pairR_iff

/-! ### Instances: `withbor` -/

/-- **Identity lens**: `withbor : Ref V ⊸ (∀'x ⊏ ⊓Δ. Mut 'x V ⊸ ['x] T) ⊸ Ref V ⊗ T`, the
second `withbor` axiom, at a payload with no lifetime. -/
def idLens (V : VTy) (hV : plainV V = true) : Lens (fun _ => .ref V) (fun c => .mut c V) where
  run := withborV
  closed := rfl
  Adm Δ _ x := Δ.find? x = none
  wf {Δ Γ a x T} hx hT hΓ :=
    .withbor2 x hΓ.toP hx ⟨.top, Lifetime.LifeCtx.defines_of_wf rfl, plain_outlives hV⟩
      (plain_noFree hV) (plain_noFree hT)
  Obs := LensObs (fun _ => True) id
  runs _ _ _ := by
    rw [steps_withbor_iff]; simp [LensObs]

/-- **Reborrow**: `withbor : Mut @a V ⊸ (∀'x ⊏ ⊓Δ. Mut 'x V ⊸ ['x] T) ⊸ Mut @a V ⊗ T`, the
third `withbor` axiom. -/
def reLens (V : VTy) (hV : plainV V = true) : Lens (fun a => .mut a V) (fun c => .mut c V) where
  run := withborV
  closed := rfl
  Adm Δ _ x := Δ.find? x = none
  wf {Δ Γ a x T} hx hT hΓ := .withbor3 x hΓ.toP hx (plain_noFree hV) (plain_noFree hT)
  Obs := LensObs (fun _ => True) id
  runs _ _ _ := by
    rw [steps_withbor_iff]; simp [LensObs]

/-- The `Imm` form: `withbor : Ref V ⊸ (∀'x ⊏ ⊓Δ. Imm 'x V ⊸ ['x] T) ⊸ Ref V ⊗ T`, the first
`withbor` axiom; the same term. -/
def idImm (V : VTy) (hV : plainV V = true) : Lens (fun _ => .ref V) (fun c => .imm c V) where
  run := withborV
  closed := rfl
  Adm Δ _ x := Δ.find? x = none
  wf {Δ Γ a x T} hx hT hΓ :=
    .withbor1 x hΓ.toP hx (fun z hz => absurd hz (plain_noFree hV)) (plain_noFree hV)
      (plain_noFree hT)
  Obs := LensObs (fun _ => True) id
  runs _ _ _ := by
    rw [steps_withbor_iff]; simp [LensObs]

/-! ### Instance: a leaf of a place-record, the other leaf kept by the lender -/

/-- `λp. λg. let (x, y) = p; let (x′, t) = withbor x g; ((x′, y), t)`: the first leaf is lent,
and the lender holds the second (the residual) until the callback returns. -/
def fstV : Val :=
  .lam (.val (.lam (.letpair (.var 1)
    (.letpair (app2 (.val withborV) (.var 1) (.var 2))
      (.pair (.pair (.var 1) (.var 2)) (.var 0))))))

theorem fstV_closed : closedAt 0 fstV.1 = true := rfl

/-- `fst : Ref A ⊗ Ref B ⊸ (∀'x ⊏ ⊓Δ. Mut 'x A ⊸ ['x] T) ⊸ (Ref A ⊗ Ref B) ⊗ T`. -/
theorem d_fst {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {A B T : VTy} (hA : plainV A = true)
    (hT : plainV T = true) (hx : Δ.find? x = none) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val fstV)
      (.val (opticTy (fun _ => refs2 A B) (fun c => .mut c A) id (fun T _ => T) a x
        Δ.meetOfDom T)) := by
  refine .lamV (.lamV ?_)
  refine letW (A := .ref A) (B := .ref B) (.var (by csolo)) ?_
  refine letW (A := .ref A) (B := T)
    (appW (.var (by csolo)) (appW (.var (by csolo))
      (.withbor2 x (by cdead) hx ⟨.top, Lifetime.LifeCtx.defines_of_wf rfl, plain_outlives hA⟩
        (plain_noFree hA) (plain_noFree hT)))) ?_
  exact pairW (pairW (.var (by csolo)) (.var (by csolo))) (.var (by csolo))

/-- **Field lens**: `Ref A ⊗ Ref B → Mut 'x A`, focus the first leaf. -/
def fstLens (A B : VTy) (hA : plainV A = true) :
    Lens (fun _ => refs2 A B) (fun c => .mut c A) where
  run := fstV
  closed := rfl
  Adm Δ _ x := Δ.find? x = none
  wf hx hT hΓ := d_fst hA hT hx hΓ
  Obs := LensObs (fun s => ∃ x y, s = .pair x y) (fun s => match s with
    | ⟨.pair x _, h⟩ => ⟨x, h.pair_left⟩
    | s => s)
  runs {μ μ' s g w} _ hs hg := by
    rw [show Expr.val fstV = lam2 (.letpair (.var 1)
      (.letpair (app2 (.val withborV) (.var 1) (.var 2))
        (.pair (.pair (.var 1) (.var 2)) (.var 0)))) from rfl, steps_app2_iff]
    have e₁ : ((Expr.letpair (.var 1) (.letpair (app2 (.val withborV) (.var 1) (.var 2))
        (.pair (.pair (.var 1) (.var 2)) (.var 0)))).subst 1 (s.shift 1 0)).subst 0 g
        = .letpair s.1 (.letpair (app2 (.val withborV) (.var 1) g.1)
            (.pair (.pair (.var 1) (.var 2)) (.var 0))) := by
      simp [app2, closed_subst withborV_closed, closedV_shift hs, closedV_shift hg,
        closed_subst hs]
    rw [e₁, steps_letpair_val_iff]
    constructor
    · rintro ⟨x, y, rfl, h⟩
      have hy : closedAt 0 y.1 = true := by
        simp only [Val.val_pair, closedAt, Bool.and_eq_true] at hs; exact hs.2
      have hx : closedAt 0 x.1 = true := by
        simp only [Val.val_pair, closedAt, Bool.and_eq_true] at hs; exact hs.1
      have e₂ : ((Expr.letpair (app2 (.val withborV) (.var 1) g.1)
          (.pair (.pair (.var 1) (.var 2)) (.var 0))).subst 0 (y.shift 1 0)).subst 0 x
          = .letpair (app2 (.val withborV) x.1 g.1) (.pair (.pair (.var 1) y.1) (.var 0)) := by
        simp [app2, closed_subst withborV_closed, closedV_shift hx, closedV_shift hy,
          closed_subst hg, closed_subst hy]
      rw [e₂, steps_letpairK_iff] at h
      obtain ⟨μm, v, h₁, h₂⟩ := h
      obtain ⟨t, rfl, hgx⟩ := steps_withbor_iff.mp h₁
      rw [steps_letpair_iff] at h₂
      have e₃ : ((Expr.pair (.pair (.var 1) y.1) (.var 0)).subst 0 (t.shift 1 0)).subst 0 x
          = (Val.pair (.pair x y) t).1 := by
        simp [closed_subst hy, Expr.subst_shift 0 0 0 x t.1 (le_refl _) (le_refl _)]
      rw [e₃] at h₂
      obtain ⟨rfl, rfl⟩ := steps_val_iff.mp h₂
      exact ⟨t, rfl, ⟨x, y, rfl⟩, hgx⟩
    · rintro ⟨t, rfl, ⟨x, y, rfl⟩, h⟩
      have hy : closedAt 0 y.1 = true := by
        simp only [Val.val_pair, closedAt, Bool.and_eq_true] at hs; exact hs.2
      have hx : closedAt 0 x.1 = true := by
        simp only [Val.val_pair, closedAt, Bool.and_eq_true] at hs; exact hs.1
      refine ⟨x, y, rfl, ?_⟩
      have e₂ : ((Expr.letpair (app2 (.val withborV) (.var 1) g.1)
          (.pair (.pair (.var 1) (.var 2)) (.var 0))).subst 0 (y.shift 1 0)).subst 0 x
          = .letpair (app2 (.val withborV) x.1 g.1) (.pair (.pair (.var 1) y.1) (.var 0)) := by
        simp [app2, closed_subst withborV_closed, closedV_shift hx, closedV_shift hy,
          closed_subst hg, closed_subst hy]
      rw [e₂, steps_letpairK_iff]
      refine ⟨μ', .pair x t, steps_withbor_iff.mpr ⟨t, rfl, h⟩, ?_⟩
      rw [steps_letpair_iff]
      have e₃ : ((Expr.pair (.pair (.var 1) y.1) (.var 0)).subst 0 (t.shift 1 0)).subst 0 x
          = (Val.pair (.pair x y) t).1 := by
        simp [closed_subst hy, Expr.subst_shift 0 0 0 x t.1 (le_refl _) (le_refl _)]
      rw [e₃]
      exact .refl _ _

/-! ### Lifting through a mutable borrow: `withswap` -/

/-- `withswap` as a value. -/
def withswapV : Val := .lam (.val (.lam (.letpair (.app v0 (.app load' v1))
  (.seq (.app (.app store' v3) v1) (.pair v3 v0)))))

theorem withswapV_eq : withswapV.1 = withswap := rfl

/-- `λs. run s g`, the callback `withswap` receives, with `g` at index 1. -/
def liftCb (run : Val) : Expr := .val (.lam (app2 (.val run) (.var 0) (.var 1)))

/-- `λm. λg. withswap m (λs. run s g)`. -/
def liftV (run : Val) : Val := .lam (.val (.lam (app2 (.val withswapV) (.var 1) (liftCb run))))

theorem liftV_closed {run : Val} (h : closedAt 0 run.1 = true) : closedAt 0 (liftV run).1 = true := by
  simp [liftV, liftCb, app2, closedAt, withswapV, v0, v1, v3, load', store',
    closedAt_mono _ h (Nat.zero_le _)]

/-- `lift : Mut @a S ⊸ W(G) ⊸ Mut @a S ⊗ O(T, G)` from an optic on the owned `S`. -/
theorem d_lift {S : VTy} {F : Lifetime.Life → VTy} {W : VTy → VTy} {O : VTy → VTy → VTy}
    (L : Optic (fun _ => S) F W O) {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {x : LifeVar}
    {T : VTy} (h : L.Adm Δ a x) (hT : plainV T = true) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (liftV L.run))
      (.val (opticTy (fun a => .mut a S) F W O a x Δ.meetOfDom T)) := by
  refine .lamV (.lamV ?_)
  refine .lolliE (.left (.right (deadSplit hΓ))) ?_
    (.lolliE (.dead (.left (deadSplit hΓ))) (.var (.there (.here hΓ.toP)))
      (.withswap (a := a) (A := S) (B := O T (cbTy F x Δ.meetOfDom T))
        (.cons (.cons hΓ.toP))))
  refine .lamV ?_
  exact .lolliE (.right (.left (.dead (deadSplit hΓ)))) (.var (.there (.here (.cons hΓ.toP))))
    (.lolliE (.left (.dead (.dead (deadSplit hΓ)))) (.var (.here (.cons (.cons hΓ.toP))))
      (L.wf h hT (.cons (.cons (.cons hΓ)))))

/-- The lifted run: `m` is a cell `ℓ` holding `s`, the optic runs on `s` at the same heap, and
`s` itself is stored back. -/
def liftObs (Obs : Heap → Heap → Val → Val → Val → Prop) (μ μ' : Heap) (m g t : Val) : Prop :=
  ∃ (ℓ : Loc) (s : Val) (μ₁ : Heap), m = .loc ℓ ∧ μ ℓ = some s ∧ Obs μ μ₁ s g t ∧
    (∃ u, μ₁ ℓ = some u) ∧ μ' = μ₁.upd ℓ s

/-- **Lift**: an optic on an owned `S` is an optic on `Mut @a S`, through `withswap`. -/
def Optic.lift {S : VTy} {F : Lifetime.Life → VTy} {W : VTy → VTy} {O : VTy → VTy → VTy}
    (L : Optic (fun _ => S) F W O) : Optic (fun a => .mut a S) F W O where
  run := liftV L.run
  closed := liftV_closed L.closed
  Adm := L.Adm
  wf h hT hΓ := d_lift L h hT hΓ
  Obs := liftObs L.Obs
  runs {μ μ' m g w} hμ hm hg := by
    rw [show Expr.val (liftV L.run) = lam2 (app2 (.val withswapV) (.var 1) (liftCb L.run)) from rfl,
      steps_app2_iff]
    have e : ((app2 (.val withswapV) (.var 1) (liftCb L.run)).subst 1 (m.shift 1 0)).subst 0 g
        = app2 withswap m.1 (Val.lam (app2 (.val L.run) (.var 0) g.1)).1 := by
      simp [app2, liftCb, withswapV, withswap, lam2, v0, v1, v3, load', store',
        closed_subst L.closed, closedV_shift hm, closedV_shift hg, closed_subst hm]
    have hcb : closedAt 0 (Val.lam (app2 (.val L.run) (.var 0) g.1)).1 = true := by
      simp [app2, closedAt, closedAt_mono _ L.closed (Nat.zero_le _),
        closedAt_mono _ hg (Nat.zero_le _)]
    rw [e, steps_withswap_iff hm]
    constructor
    · rintro ⟨ℓ, s, μ₁, s', t, rfl, hℓ, hfs, hdom, rfl, rfl⟩
      have hs := hμ ℓ s hℓ
      rw [steps_beta_iff] at hfs
      have e₂ : (app2 (.val L.run) (.var 0) g.1).subst 0 s = app2 (.val L.run) s.1 g.1 := by
        simp [app2, closed_subst L.closed, closed_subst hg]
      rw [e₂, L.runs hμ hs hg] at hfs
      obtain ⟨t', ht, hobs⟩ := hfs
      obtain ⟨rfl, rfl⟩ : s' = s ∧ t = t' := by
        have := congrArg Subtype.val ht
        simp only [Val.val_pair, Expr.pair.injEq] at this
        exact ⟨Subtype.ext this.1, Subtype.ext this.2⟩
      exact ⟨t, rfl, ℓ, s', μ₁, rfl, hℓ, hobs, hdom, rfl⟩
    · rintro ⟨t, rfl, ℓ, s, μ₁, rfl, hℓ, hobs, hdom, rfl⟩
      have hs := hμ ℓ s hℓ
      refine ⟨ℓ, s, μ₁, s, t, rfl, hℓ, ?_, hdom, rfl, rfl⟩
      rw [steps_beta_iff]
      have e₂ : (app2 (.val L.run) (.var 0) g.1).subst 0 s = app2 (.val L.run) s.1 g.1 := by
        simp [app2, closed_subst L.closed, closed_subst hg]
      rw [e₂, L.runs hμ hs hg]
      exact ⟨t, rfl, hobs⟩

/-- **The lender's cell is unchanged**: after any run of a lifted optic, the cell holds exactly
what it held before, whatever the callback did. -/
theorem Optic.lift_cell {S : VTy} {F : Lifetime.Life → VTy} {W : VTy → VTy}
    {O : VTy → VTy → VTy} (L : Optic (fun _ => S) F W O) {μ μ' : Heap} {ℓ : Loc} {g w : Val}
    (hμ : HeapClosed μ) (hg : closedAt 0 g.1 = true)
    (h : Steps μ (app2 (.val L.lift.run) (Val.loc ℓ).1 g.1) μ' w.1) : μ' ℓ = μ ℓ := by
  obtain ⟨t, -, ℓ', s, μ₁, hℓ', hs, -, -, rfl⟩ := (L.lift.runs hμ rfl hg).mp h
  obtain rfl : ℓ = ℓ' := by simpa using hℓ'
  simp [BoLo.Heap.upd, hs]

/-! ### Composition: nesting, the inner optic at `'y ⊏ 'x` -/

/-- `F` mentions only its lifetime argument. -/
def FocusFree (F : Lifetime.Life → VTy) : Prop := ∀ z c, VFree z (F c) → c.mentions z = true

/-- `F` commutes with instantiating its lifetime variable. -/
def FocusInst (F : Lifetime.Life → VTy) : Prop :=
  ∀ (x : LifeVar) (c : Lifetime.Life), VTy.instLife x c (F (.var x)) = F c

theorem mut_focusFree {V : VTy} (hV : plainV V = true) : FocusFree (fun c => .mut c V) :=
  fun _ _ h => h.elim id (fun h => absurd h (plain_noFree hV))

theorem mut_focusInst {V : VTy} (hV : plainV V = true) : FocusInst (fun c => .mut c V) := by
  intro x c
  simp [VTy.instLife, VTy.applyLSub, plain_lsub hV, Lifetime.Life.applySub,
    Lifetime.assocFind]

/-- The callback's type mentions no variable but its bound's. -/
theorem cbTy_noFree {F : Lifetime.Life → VTy} (hF : FocusFree F) {x z : LifeVar}
    {b : Lifetime.Life} {T : VTy} (hT : plainV T = true) (hb : b.mentions z = false) :
    ¬ VFree z (cbTy F x b T) := by
  simp only [cbTy, VTy.all, VTy.lolli, VFree, CFree, hb, Bool.false_eq_true, false_or, not_and]
  intro hzx h
  rcases h with h | h | h
  · have := hF z _ h
    simp [Lifetime.Life.mentions] at this
    exact hzx this
  · simp [Lifetime.Life.mentions] at h
    exact hzx h
  · exact plain_noFree hT h

/-- `∀E` at the inner lifetime renames the callback's binder. -/
theorem cbTy_inst {F : Lifetime.Life → VTy} (hF : FocusInst F) {x : LifeVar}
    (c : Lifetime.Life) {T : VTy} (hT : plainV T = true) :
    VTy.instLife x c (.lolli (F (.var x)) (.box (.var x) T)) = .lolli (F c) (.box c T) := by
  have h := hF x c
  simp only [VTy.instLife] at h ⊢
  simp [VTy.lolli, VTy.applyLSub, CTy.applyLSub, h, plain_lsub hT, Lifetime.Life.applySub,
    Lifetime.assocFind]

/-- `Λ. λv. g () v`: the outer callback, passed on at the inner lifetime. -/
def innerE (g : Expr) : Expr := .val (.lam (.val (.lam (app2 g unit' (.var 0)))))

/-- `Λ. λm. let (m′, t) = run₂ m (Λ. λv. g () v); forget m′; t`, with `g` written as it
appears under all four binders. -/
def compCb (run₂ : Val) (g : Expr) : Expr :=
  .val (.lam (.val (.lam (.letpair (app2 (.val run₂) (.var 0) (innerE g))
    (.seq (.app forget (.var 1)) (.var 0))))))

/-- `λs. λg. run₁ s (compCb run₂ g)`. -/
def compV (run₁ run₂ : Val) : Val :=
  .lam (.val (.lam (app2 (.val run₁) (.var 1) (compCb run₂ (.var 4)))))

theorem compV_closed {r₁ r₂ : Val} (h₁ : closedAt 0 r₁.1 = true) (h₂ : closedAt 0 r₂.1 = true) :
    closedAt 0 (compV r₁ r₂).1 = true := by
  simp [compV, compCb, innerE, app2, closedAt, forget, unit', closedAt_mono _ h₁ (Nat.zero_le _),
    closedAt_mono _ h₂ (Nat.zero_le _)]

/-- What the composite needs of its lifetime context: the two binders fresh and distinct, each
optic admissible at its own. -/
def CompAdm (A₁ : LifeCtx → Lifetime.Life → LifeVar → Prop)
    (A₂ : LifeCtx → Lifetime.Life → LifeVar → Prop) (Δ : LifeCtx) (a : Lifetime.Life) :
    LifeVar → Prop := fun _ =>
  ∃ x₁ y, A₁ Δ a x₁ ∧ A₂ (FD₁ Δ x₁) (.var x₁) y ∧ Δ.Ok ∧ Δ.find? x₁ = none ∧
    Δ.find? y = none ∧ x₁ ≠ y

/-- The composite's typing: `S ⊸ (∀'x ⊏ ⊓Δ. F('x) ⊸ ['x] T) ⊸ S ⊗ T`. -/
theorem d_comp {S F : Lifetime.Life → VTy} {U : VTy}
    (L₁ : Lens S (fun c => .mut c U)) (L₂ : Lens (fun a => .mut a U) F)
    (hF : FocusFree F) (hFi : FocusInst F) {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life}
    {x : LifeVar} {T : VTy} (h : CompAdm L₁.Adm L₂.Adm Δ a x) (hT : plainV T = true)
    (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (compV L₁.run L₂.run))
      (.val (opticTy S F id (fun T _ => T) a x Δ.meetOfDom T)) := by
  obtain ⟨x₁, y, h₁, h₂, hΔ, hx₁, hy, hxy⟩ := h
  have hy₁ : (FD₁ Δ x₁).find? y = none := by
    simp [Lifetime.LifeCtx.find?_extend, Ne.symm hxy, hxy, hy]
  have hok₁ : (FD₁ Δ x₁).Ok := hΔ.extend hx₁ (Lifetime.meetOfDomL_wf Δ.entries)
  have hG : ∀ z, Δ.find? z = none → ¬ VFree z (cbTy F x Δ.meetOfDom T) := fun z hz =>
    cbTy_noFree hF hT (Lifetime.Life.mentions_false_of_wf hz (Lifetime.meetOfDomL_wf _))
  have hD := hΓ.toP
  refine .lamV (.lamV ?_)
  refine .lolliE (.left (.right (deadSplit hΓ))) ?_
    (.lolliE (.dead (.left (deadSplit hΓ))) (.var (.there (.here hD)))
      (L₁.wf h₁ hT (.cons (.cons hΓ))))
  -- the outer callback, at `Δ, 'x₁ ⊏ ⊓Δ`
  refine .thunkV rfl (.allI (S := .unit)
    (Lifetime.Life.mentions_false_of_wf hx₁ (Lifetime.meetOfDomL_wf _))
    (fun _ _ h => hΔ.bound_mentions_false hx₁ h) ?_ (.ret (.lamV ?_)))
  · intro t ht hl
    simp only [List.mem_cons] at ht
    rcases ht with rfl | rfl | ht
    · exact hG x₁ hx₁
    · simp at hl
    · exact dead_noLive hΓ (P := fun t => ¬ VFree x₁ t.ty) t ht hl
  refine .letpairV (A := .mut (.var x₁) U) (B := T) (.left (.dead (.left (.dead (deadSplit hΓ))))) ?_ ?_
  · refine .lolliE (.right (.dead (.left (.dead (deadSplit hΓ))))) ?_
      (.lolliE (.left (.dead (.dead (.dead (deadSplit hΓ))))) (.var (.here (.cons (.cons (.cons hD)))))
        (L₂.wf h₂ hT (.cons (.cons (.cons (.cons hΓ))))))
    -- the inner callback, at `Δ, 'x₁, 'y ⊏ ⊓(Δ, 'x₁)`
    refine .thunkV rfl (.allI (S := .unit)
      (Lifetime.Life.mentions_false_of_wf hy₁ (Lifetime.meetOfDomL_wf _))
      (fun _ _ h => hok₁.bound_mentions_false hy₁ h) ?_ (.ret (.lamV ?_)))
    · intro t ht hl
      simp only [List.mem_cons] at ht
      rcases ht with rfl | rfl | rfl | rfl | ht
      · simp at hl
      · simp at hl
      · exact hG y hy
      · simp at hl
      · exact dead_noLive hΓ (P := fun t => ¬ VFree y t.ty) t ht hl
    refine .lolliE (.left (.dead (.dead (.dead (.right (.dead (deadSplit hΓ))))))) (.var (.here ?_)) ?_
    · exact .cons (.cons (.cons (.cons (.cons hD))))
    have key : CDerives (FD₂ Δ x₁ y)
        (⟨F (.var y), false⟩ :: ⟨.unit, false⟩ :: ⟨.mut (.var x₁) U, false⟩ :: ⟨.unit, false⟩ ::
          ⟨cbTy F x Δ.meetOfDom T, true⟩ :: ⟨S a, false⟩ :: Γ)
        (.app (.var 4) unit') (.val (.lolli (F (.var y)) (.box (.var y) T))) := by
      have := CDerives.allEV (x := x) (A := .lolli (F (.var x)) (.box (.var x) T)) (a := .var y)
        (Γ := ⟨F (.var y), false⟩ :: ⟨.unit, false⟩ :: ⟨.mut (.var x₁) U, false⟩ :: ⟨.unit, false⟩ ::
          ⟨cbTy F x Δ.meetOfDom T, true⟩ :: ⟨S a, false⟩ :: Γ)
        (.var (.there (.there (.there (.there (.here (.cons hD))))))) (entailsLt_inner Δ x₁ y)
      rwa [cbTy_inst hFi _ hT] at this
    exact key
  · refine .seqV (.right (.left (.dead (.dead (.dead (.dead (deadSplit hΓ))))))) ?_ ?_
    · exact .lolliE (.dead (.left (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))
        (.var (.there (.here (.cons (.cons (.cons (.cons hD)))))))
        (.forgetMut (.cons (.cons (.cons (.cons (.cons (.cons hD)))))))
    · exact .boxI (.var (.here (.cons (.cons (.cons (.cons (.cons hD)))))))
        (CtxOutlives.solo (Lifetime.LifeCtx.defines_of_wf (wf_var_self _ _ _)) (plain_outlives hT)
          (.cons (.cons (.cons (.cons (.cons hΓ))))))

/-- `Λ. λv. g () v` as a value. -/
def innerV (g : Val) : Val := .lam (.val (.lam (app2 g.1 unit' (.var 0))))

theorem innerV_closed {g : Val} (hg : closedAt 0 g.1 = true) : closedAt 0 (innerV g).1 = true := by
  simp [innerV, app2, unit', closedAt, closedAt_mono _ hg (Nat.zero_le _)]

/-- `innerV g` runs as `g`. -/
theorem steps_innerV_iff {μ μ' : Heap} {g z t : Val} (hg : closedAt 0 g.1 = true) :
    Steps μ (app2 (innerV g).1 unit' z.1) μ' t.1 ↔ Steps μ (app2 g.1 unit' z.1) μ' t.1 := by
  rw [show (innerV g).1 = lam2 (app2 g.1 unit' (.var 0)) from rfl,
    steps_app2_unit_iff]
  simp [app2, unit', closed_subst hg, closedV_shift hg]

/-- The outer callback with `g` substituted. -/
def compCbV (run₂ g : Val) : Val :=
  .lam (.val (.lam (.letpair (app2 (.val run₂) (.var 0) (innerV g).1)
    (.seq (.app forget (.var 1)) (.var 0)))))

/-- **Composition**: a lens onto `Mut 'x U`, then an optic from `Mut 'x U`, nested. -/
def Optic.comp {S F : Lifetime.Life → VTy} {U : VTy}
    (L₁ : Lens S (fun c => .mut c U)) (L₂ : Lens (fun a => .mut a U) F)
    (hF : FocusFree F) (hFi : FocusInst F) (Dom₁ : Val → Prop) (f₁ : Val → Val)
    (h₁ : L₁.Obs = LensObs Dom₁ f₁)
    (hf₁ : ∀ s, closedAt 0 s.1 = true → Dom₁ s → closedAt 0 (f₁ s).1 = true) :
    Lens S F where
  run := compV L₁.run L₂.run
  closed := compV_closed L₁.closed L₂.closed
  Adm := CompAdm L₁.Adm L₂.Adm
  wf h hT hΓ := d_comp L₁ L₂ hF hFi h hT hΓ
  Obs μ μ' s g t := Dom₁ s ∧ L₂.Obs μ μ' (f₁ s) (innerV g) t
  runs {μ μ' s g w} hμ hs hg := by
    have hcb : closedAt 0 (compCbV L₂.run g).1 = true := by
      simp [compCbV, app2, closedAt, forget, unit', closedAt_mono _ L₂.closed (Nat.zero_le _),
        closedAt_mono _ (innerV_closed hg) (Nat.zero_le _)]
    rw [show Expr.val (compV L₁.run L₂.run) = lam2 (app2 (.val L₁.run) (.var 1)
      (compCb L₂.run (.var 4))) from rfl, steps_app2_iff]
    have e : ((app2 (.val L₁.run) (.var 1) (compCb L₂.run (.var 4))).subst 1 (s.shift 1 0)).subst 0 g
        = app2 (.val L₁.run) s.1 (compCbV L₂.run g).1 := by
      simp [app2, compCb, compCbV, innerE, innerV, forget, unit', closed_subst L₁.closed,
        closed_subst L₂.closed, closedV_shift hs, closedV_shift hg, closed_subst hs]
    rw [e, L₁.runs hμ hs hcb, h₁]
    simp only [LensObs]
    refine exists_congr fun t => and_congr_right fun _ => and_congr_right fun hd => ?_
    have hfs := hf₁ s hs hd
    rw [show (compCbV L₂.run g).1 = lam2 (.letpair (app2 (.val L₂.run) (.var 0) (innerV g).1)
      (.seq (.app forget (.var 1)) (.var 0))) from rfl,
      steps_app2_unit_iff]
    have e₂ : ((Expr.letpair (app2 (.val L₂.run) (.var 0) (innerV g).1)
        (.seq (.app forget (.var 1)) (.var 0))).subst 1 (Val.unit.shift 1 0)).subst 0 (f₁ s)
        = .letpair (app2 (.val L₂.run) (f₁ s).1 (innerV g).1)
            (.seq (.app forget (.var 1)) (.var 0)) := by
      simp [app2, forget, unit', closed_subst L₂.closed, closed_subst (innerV_closed hg)]
    rw [e₂, steps_letpairK_iff]
    constructor
    · rintro ⟨μm, v, h₁', h₂'⟩
      obtain ⟨t', rfl, hobs⟩ := (L₂.runs hμ hfs (innerV_closed hg)).mp h₁'
      rw [steps_letpair_iff] at h₂'
      have e₃ : (((Expr.seq (.app forget (.var 1)) (.var 0)).subst 0 (t'.shift 1 0)).subst 0 (f₁ s))
          = .seq (.app forget (f₁ s).1) t'.1 := by
        simp [forget, unit', Expr.subst_shift 0 0 0 (f₁ s) t'.1 (le_refl _) (le_refl _)]
      rw [e₃, steps_seqK_iff] at h₂'
      obtain ⟨μf, u, hfg, hrest⟩ := h₂'
      rw [show forget = Expr.val (Val.lam unit') from rfl, steps_beta_iff] at hfg
      obtain ⟨rfl, rfl⟩ := steps_val_iff (v := Val.unit).mp hfg
      obtain ⟨rfl, rfl⟩ := steps_val_iff.mp (steps_seq_iff.mp hrest)
      exact hobs
    · intro hobs
      refine ⟨μ', .pair (f₁ s) t, (L₂.runs hμ hfs (innerV_closed hg)).mpr ⟨t, rfl, hobs⟩, ?_⟩
      rw [steps_letpair_iff]
      have e₃ : (((Expr.seq (.app forget (.var 1)) (.var 0)).subst 0 (t.shift 1 0)).subst 0 (f₁ s))
          = .seq (.app forget (f₁ s).1) t.1 := by
        simp [forget, unit', Expr.subst_shift 0 0 0 (f₁ s) t.1 (le_refl _) (le_refl _)]
      rw [e₃, steps_seqK_iff]
      refine ⟨μ', Val.unit, ?_, steps_seq_iff.mpr (.refl _ _)⟩
      rw [show forget = Expr.val (Val.lam unit') from rfl, steps_beta_iff]
      exact .refl _ _

/-- **Composition law**: composing two lenses composes their foci. -/
theorem Optic.comp_obs {S F : Lifetime.Life → VTy} {U : VTy}
    (L₁ : Lens S (fun c => .mut c U)) (L₂ : Lens (fun a => .mut a U) F)
    (hF : FocusFree F) (hFi : FocusInst F) (Dom₁ : Val → Prop) (f₁ : Val → Val)
    (h₁ : L₁.Obs = LensObs Dom₁ f₁)
    (hf₁ : ∀ s, closedAt 0 s.1 = true → Dom₁ s → closedAt 0 (f₁ s).1 = true)
    (Dom₂ : Val → Prop) (f₂ : Val → Val) (h₂ : L₂.Obs = LensObs Dom₂ f₂)
    {μ μ' : Heap} {s g t : Val} (hg : closedAt 0 g.1 = true) :
    (Optic.comp L₁ L₂ hF hFi Dom₁ f₁ h₁ hf₁).Obs μ μ' s g t ↔
      LensObs (fun s => Dom₁ s ∧ Dom₂ (f₁ s)) (f₂ ∘ f₁) μ μ' s g t := by
  show Dom₁ s ∧ L₂.Obs μ μ' (f₁ s) (innerV g) t ↔ _
  rw [h₂]
  simp only [LensObs, Function.comp, steps_innerV_iff hg, and_assoc]

/-! ### Instance: the family borrow `withborF2` as a lens onto the family -/

theorem fam_focusFree {A B : VTy} (hA : plainV A = true) (hB : plainV B = true) :
    FocusFree (fun c => famTy2 mutM c A B) := by
  intro z c h
  simp only [famTy2, mutM, VFree] at h
  rcases h with (h | h) | (h | h)
  · exact h
  · exact absurd h (plain_noFree hA)
  · exact h
  · exact absurd h (plain_noFree hB)

theorem fam_focusInst {A B : VTy} (hA : plainV A = true) (hB : plainV B = true) :
    FocusInst (fun c => famTy2 mutM c A B) := by
  intro x c
  simp [famTy2, mutM, VTy.instLife, VTy.applyLSub, plain_lsub hA, plain_lsub hB,
    Lifetime.Life.applySub, Lifetime.assocFind]

/-- `withborF2` as a value. -/
def famV : Val := .lam (.val (.lam (.letpair (.var 1)
    (.letpair (.app (.app withbor (.var 1)) outer2)
      (.letpair (.var 0) (.pair (.pair (.var 3) (.var 1)) (.var 0)))))))

theorem famV_eq : famV.1 = withborF2 := rfl

/-- `Λ. λmy. g () (x, my)`. -/
def famInner (g x : Val) : Val := .lam (.val (.lam (app2 g.1 unit' (.pair x.1 (.var 0)))))

/-- `Λ. λmx. let (y′, t) = withbor y (Λ. λmy. g () (mx, my)); (y′, t)`. -/
def famOuter (g y : Val) : Val :=
  .lam (.val (.lam (.letpair (app2 withbor y.1
    (.val (.lam (.val (.lam (app2 g.1 unit' (.pair (.var 2) (.var 0))))))))
    (.pair (.var 1) (.var 0)))))

/-- **Product**: `withborF2 : Ref A ⊗ Ref B → Mut 'x A ⊗ Mut 'x B`, focus the pair itself. -/
def famLens (A B : VTy) (hA : plainV A = true) (hB : plainV B = true) :
    Lens (fun _ => refs2 A B) (fun c => famTy2 mutM c A B) where
  run := famV
  closed := rfl
  Adm Δ _ _ := ∃ x y, Δ.Ok ∧ Δ.find? x = none ∧ Δ.find? y = none ∧ x ≠ y
  wf {Δ Γ a c T} h hT hΓ := by
    obtain ⟨x, y, hΔ, hx, hy, hxy⟩ := h
    have hcb : ∀ z, Δ.find? z = none → ¬ VFree z (cbTy2 mutM c Δ.meetOfDom A B T) := fun z hz =>
      cbTy_noFree (F := fun c => famTy2 mutM c A B) (fam_focusFree hA hB) hT
        (Lifetime.Life.mentions_false_of_wf hz (Lifetime.meetOfDomL_wf _))
    have s : FamSide mutM Δ c x y A B T :=
      ⟨hΔ, hx, hy, hxy, plain_noFree hA, plain_noFree hB, plain_noFree hT, plain_noFree hA,
        plain_noFree hB, plain_noFree hT, hcb x hx, hcb y hy,
        cbTy_inst (F := fun c => famTy2 mutM c A B) (fam_focusInst hA hB) _ hT⟩
    exact withborM2_wf s ⟨.top, Lifetime.LifeCtx.defines_of_wf rfl, plain_outlives hA⟩
      (plain_outlives hB) (plain_outlives hT) hΓ
  Obs := LensObs (fun s => ∃ x y, s = .pair x y) id
  runs {μ μ' s g w} _ hs hg := by
    rw [show Expr.val famV = lam2 (.letpair (.var 1)
      (.letpair (.app (.app withbor (.var 1)) outer2)
        (.letpair (.var 0) (.pair (.pair (.var 3) (.var 1)) (.var 0))))) from rfl, steps_app2_iff]
    have e₁ : ((Expr.letpair (.var 1) (.letpair (.app (.app withbor (.var 1)) outer2)
        (.letpair (.var 0) (.pair (.pair (.var 3) (.var 1)) (.var 0))))).subst 1 (s.shift 1 0)).subst 0 g
        = .letpair s.1 (.letpair (app2 withbor (.var 1)
            (.val (.lam (.val (.lam (.letpair (app2 withbor (.var 2)
              (.val (.lam (.val (.lam (app2 g.1 unit' (.pair (.var 2) (.var 0))))))))
              (.pair (.var 1) (.var 0))))))))
          (.letpair (.var 0) (.pair (.pair (.var 3) (.var 1)) (.var 0)))) := by
      simp [app2, outer2, inner2, withbor, lam2, v0, v1, unit', closedV_shift hs, closedV_shift hg,
        closed_subst hs, closed_shift hg, closed_subst hg]
    rw [e₁, steps_letpair_val_iff]
    simp only [LensObs, id]
    constructor
    · rintro ⟨x, y, rfl, h⟩
      have hx : closedAt 0 x.1 = true := by
        simp only [Val.val_pair, closedAt, Bool.and_eq_true] at hs; exact hs.1
      have hy : closedAt 0 y.1 = true := by
        simp only [Val.val_pair, closedAt, Bool.and_eq_true] at hs; exact hs.2
      have e₂ : ((Expr.letpair (app2 withbor (.var 1)
            (.val (.lam (.val (.lam (.letpair (app2 withbor (.var 2)
              (.val (.lam (.val (.lam (app2 g.1 unit' (.pair (.var 2) (.var 0))))))))
              (.pair (.var 1) (.var 0))))))))
          (.letpair (.var 0) (.pair (.pair (.var 3) (.var 1)) (.var 0)))).subst 0 (y.shift 1 0)).subst 0 x
          = .letpair (app2 (.val withborV) x.1 (famOuter g y).1)
              (.letpair (.var 0) (.pair (.pair (.var 3) (.var 1)) (.var 0))) := by
        simp [app2, famOuter, withbor, withborV, lam2, v0, v1, unit', closedV_shift hx,
          closedV_shift hy, closed_subst hx, closed_subst hy, closed_shift hg, closed_subst hg,
          closed_shift hx, closed_shift hy]
      rw [e₂, steps_letpairK_iff] at h
      obtain ⟨μm, v, h₁, h₂⟩ := h
      obtain ⟨t₁, rfl, ho⟩ := steps_withbor_iff.mp h₁
      rw [show (famOuter g y).1 = lam2 (.letpair (app2 withbor y.1
          (.val (.lam (.val (.lam (app2 g.1 unit' (.pair (.var 2) (.var 0))))))))
          (.pair (.var 1) (.var 0))) from rfl, steps_app2_unit_iff] at ho
      have e₃ : ((Expr.letpair (app2 withbor y.1
          (.val (.lam (.val (.lam (app2 g.1 unit' (.pair (.var 2) (.var 0))))))))
          (.pair (.var 1) (.var 0))).subst 1 (Val.unit.shift 1 0)).subst 0 x
          = .letpair (app2 (.val withborV) y.1 (famInner g x).1) (.pair (.var 1) (.var 0)) := by
        simp [app2, famInner, withbor, withborV, lam2, v0, v1, unit', closed_subst hy,
          closed_shift hg, closed_subst hg, closed_shift hx]
      rw [e₃, steps_letpairK_iff] at ho
      obtain ⟨μn, v', hi, hp⟩ := ho
      obtain ⟨t₂, rfl, hgi⟩ := steps_withbor_iff.mp hi
      rw [steps_letpair_iff] at hp
      have e₄ : (((Expr.pair (.var 1) (.var 0)).subst 0 (t₂.shift 1 0)).subst 0 y)
          = (Val.pair y t₂).1 := by
        simp [Expr.subst_shift 0 0 0 y t₂.1 (le_refl _) (le_refl _)]
      rw [e₄] at hp
      obtain ⟨rfl, rfl⟩ := steps_val_iff.mp hp
      rw [show (famInner g x).1 = lam2 (app2 g.1 unit' (.pair x.1 (.var 0))) from rfl,
        steps_app2_unit_iff] at hgi
      have e₅ : ((app2 g.1 unit' (.pair x.1 (.var 0))).subst 1 (Val.unit.shift 1 0)).subst 0 y
          = app2 g.1 unit' (Val.pair x y).1 := by
        simp [app2, unit', closed_subst hg, closed_subst hx]
      rw [e₅] at hgi
      rw [steps_letpair_iff] at h₂
      have e₆ : (((Expr.letpair (.var 0) (.pair (.pair (.var 3) (.var 1)) (.var 0))).subst 0
          ((Val.pair y t₂).shift 1 0)).subst 0 x)
          = .letpair (Val.pair y t₂).1 (.pair (.pair x.1 (.var 1)) (.var 0)) := by
        simp [closed_subst hx, closed_shift hx, Expr.subst_shift 0 0 0 x y.1 (le_refl _) (le_refl _),
          Expr.subst_shift 0 0 0 x t₂.1 (le_refl _) (le_refl _)]
      rw [e₆, steps_letpair_iff] at h₂
      have e₇ : (((Expr.pair (.pair x.1 (.var 1)) (.var 0)).subst 0 (t₂.shift 1 0)).subst 0 y)
          = (Val.pair (.pair x y) t₂).1 := by
        simp [closed_subst hx, Expr.subst_shift 0 0 0 y t₂.1 (le_refl _) (le_refl _)]
      rw [e₇] at h₂
      obtain ⟨rfl, rfl⟩ := steps_val_iff.mp h₂
      exact ⟨t₂, rfl, ⟨x, y, rfl⟩, hgi⟩
    · rintro ⟨t, rfl, ⟨x, y, rfl⟩, hgi⟩
      have hx : closedAt 0 x.1 = true := by
        simp only [Val.val_pair, closedAt, Bool.and_eq_true] at hs; exact hs.1
      have hy : closedAt 0 y.1 = true := by
        simp only [Val.val_pair, closedAt, Bool.and_eq_true] at hs; exact hs.2
      refine ⟨x, y, rfl, ?_⟩
      have e₂ : ((Expr.letpair (app2 withbor (.var 1)
            (.val (.lam (.val (.lam (.letpair (app2 withbor (.var 2)
              (.val (.lam (.val (.lam (app2 g.1 unit' (.pair (.var 2) (.var 0))))))))
              (.pair (.var 1) (.var 0))))))))
          (.letpair (.var 0) (.pair (.pair (.var 3) (.var 1)) (.var 0)))).subst 0 (y.shift 1 0)).subst 0 x
          = .letpair (app2 (.val withborV) x.1 (famOuter g y).1)
              (.letpair (.var 0) (.pair (.pair (.var 3) (.var 1)) (.var 0))) := by
        simp [app2, famOuter, withbor, withborV, lam2, v0, v1, unit', closedV_shift hx,
          closedV_shift hy, closed_subst hx, closed_subst hy, closed_shift hg, closed_subst hg,
          closed_shift hx, closed_shift hy]
      rw [e₂, steps_letpairK_iff]
      refine ⟨μ', .pair x (.pair y t), steps_withbor_iff.mpr ⟨_, rfl, ?_⟩, ?_⟩
      · rw [show (famOuter g y).1 = lam2 (.letpair (app2 withbor y.1
            (.val (.lam (.val (.lam (app2 g.1 unit' (.pair (.var 2) (.var 0))))))))
            (.pair (.var 1) (.var 0))) from rfl, steps_app2_unit_iff]
        have e₃ : ((Expr.letpair (app2 withbor y.1
            (.val (.lam (.val (.lam (app2 g.1 unit' (.pair (.var 2) (.var 0))))))))
            (.pair (.var 1) (.var 0))).subst 1 (Val.unit.shift 1 0)).subst 0 x
            = .letpair (app2 (.val withborV) y.1 (famInner g x).1) (.pair (.var 1) (.var 0)) := by
          simp [app2, famInner, withbor, withborV, lam2, v0, v1, unit', closed_subst hy,
            closed_shift hg, closed_subst hg, closed_shift hx]
        rw [e₃, steps_letpairK_iff]
        refine ⟨μ', .pair y t, steps_withbor_iff.mpr ⟨t, rfl, ?_⟩, ?_⟩
        · rw [show (famInner g x).1 = lam2 (app2 g.1 unit' (.pair x.1 (.var 0))) from rfl,
            steps_app2_unit_iff]
          have e₅ : ((app2 g.1 unit' (.pair x.1 (.var 0))).subst 1 (Val.unit.shift 1 0)).subst 0 y
              = app2 g.1 unit' (Val.pair x y).1 := by
            simp [app2, unit', closed_subst hg, closed_subst hx]
          rw [e₅]; exact hgi
        · rw [steps_letpair_iff]
          have e₄ : (((Expr.pair (.var 1) (.var 0)).subst 0 (t.shift 1 0)).subst 0 y)
              = (Val.pair y t).1 := by
            simp [Expr.subst_shift 0 0 0 y t.1 (le_refl _) (le_refl _)]
          rw [e₄]; exact .refl _ _
      · rw [steps_letpair_iff]
        have e₆ : (((Expr.letpair (.var 0) (.pair (.pair (.var 3) (.var 1)) (.var 0))).subst 0
            ((Val.pair y t).shift 1 0)).subst 0 x)
            = .letpair (Val.pair y t).1 (.pair (.pair x.1 (.var 1)) (.var 0)) := by
          simp [closed_subst hx, closed_shift hx, Expr.subst_shift 0 0 0 x y.1 (le_refl _) (le_refl _),
            Expr.subst_shift 0 0 0 x t.1 (le_refl _) (le_refl _)]
        rw [e₆, steps_letpair_iff]
        have e₇ : (((Expr.pair (.pair x.1 (.var 1)) (.var 0)).subst 0 (t.shift 1 0)).subst 0 y)
            = (Val.pair (.pair x y) t).1 := by
          simp [closed_subst hx, Expr.subst_shift 0 0 0 y t.1 (le_refl _) (le_refl _)]
        rw [e₇]; exact .refl _ _

/-! ### The accessor form: `over` -/

/-- `Λ. λmv. let (mv′, t) = withswap mv f; forget mv′; t`, with `f` at index 2. -/
def setCb (f : Expr) : Expr :=
  .val (.lam (.val (.lam (.letpair (app2 withswap (.var 0) f)
    (.seq (.app forget (.var 1)) (.var 0))))))

/-- `λm. λf. lift m (setCb f)`: run `f : V ⊸ V ⊗ T` on the focus, through `Mut @a S`. -/
def overV (run : Val) : Val :=
  .lam (.val (.lam (app2 (.val (liftV run)) (.var 1) (setCb (.var 2)))))

/-- `Mut @a S ⊸ (V ⊸ V ⊗ T) ⊸ Mut @a S ⊗ T`. -/
def overTy (S V : VTy) (a : Lifetime.Life) (T : VTy) : VTy :=
  .lolli (.mut a S) (.lolli (.lolli V (.tensor V T)) (.tensor (.mut a S) T))

/-- The accessor form of a lens, derived from `lift` and `withswap`. -/
theorem d_over {S V : VTy} (hV : plainV V = true) (L : Lens (fun _ => S) (fun c => .mut c V))
    {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {x : LifeVar} {T : VTy}
    (h : L.Adm Δ a x) (hΔ : Δ.Ok) (hx : Δ.find? x = none) (hT : plainV T = true)
    (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val (overV L.run)) (.val (overTy S V a T)) := by
  have hD := hΓ.toP
  have hf : ¬ VFree x (.lolli V (.tensor V T)) := by
    simp only [VTy.lolli, VFree, CFree, not_or]
    exact ⟨plain_noFree hV, plain_noFree hV, plain_noFree hT⟩
  refine .lamV (.lamV ?_)
  refine .lolliE (.left (.right (deadSplit hΓ))) ?_
    (.lolliE (.dead (.left (deadSplit hΓ))) (.var (.there (.here hD)))
      (d_lift L (T := T) h hT (.cons (.cons hΓ))))
  refine .thunkV rfl (.allI (S := .unit)
    (Lifetime.Life.mentions_false_of_wf hx (Lifetime.meetOfDomL_wf _))
    (fun _ _ h => hΔ.bound_mentions_false hx h) ?_ (.ret (.lamV ?_)))
  · intro t ht hl
    simp only [List.mem_cons] at ht
    rcases ht with rfl | rfl | ht
    · exact hf
    · simp at hl
    · exact dead_noLive hΓ (P := fun t => ¬ VFree x t.ty) t ht hl
  refine .letpairV (A := .mut (.var x) V) (B := T) (.left (.dead (.left (.dead (deadSplit hΓ)))))
    ?_ ?_
  · exact .lolliE (.right (.dead (.left (.dead (deadSplit hΓ)))))
      (.var (.there (.there (.here (.cons hD)))))
      (.lolliE (.left (.dead (.dead (.dead (deadSplit hΓ))))) (.var (.here (.cons (.cons (.cons hD)))))
        (.withswap (.cons (.cons (.cons (.cons hD))))))
  · refine .seqV (.right (.left (.dead (.dead (.dead (.dead (deadSplit hΓ))))))) ?_ ?_
    · exact .lolliE (.dead (.left (.dead (.dead (.dead (.dead (deadSplit hΓ)))))))
        (.var (.there (.here (.cons (.cons (.cons (.cons hD)))))))
        (.forgetMut (.cons (.cons (.cons (.cons (.cons (.cons hD)))))))
    · exact .boxI (.var (.here (.cons (.cons (.cons (.cons (.cons hD)))))))
        (CtxOutlives.solo (Lifetime.LifeCtx.defines_of_wf (wf_var_self _ _ _)) (plain_outlives hT)
          (.cons (.cons (.cons (.cons (.cons hΓ))))))

/-- **A split of a mutable borrow at a fresh lifetime**: `Mut @a (Ref A ⊗ Ref B)` lends
`Mut 'x A ⊗ Mut 'x B` at `'x ⊏ ⊓Δ`, the family lens lifted through `withswap`. -/
def splitMut (A B : VTy) (hA : plainV A = true) (hB : plainV B = true) :
    Lens (fun a => .mut a (refs2 A B)) (fun c => famTy2 mutM c A B) :=
  (famLens A B hA hB).lift

end BoCa.Fig16.LogRel.Core.Optics

end

import Optics.Getter

/-!
# Optics — the decisive test (a): a variant payload borrowed with the tag frozen  (stage 3)

The owned variant of cells `Ref A ⊕ Ref B` has an affine optic onto `Mut 'x A` (a prism followed
by the identity lens, Clarke et al. Def 3.24's affine traversal), from `case` and `withbor`:

    prism ≜ λs. λg. case s { inj₁ r ⇒ let (r′, t) = withbor r g in (inj₁ r′, inj₁ t)
                           | inj₂ r ⇒ (inj₂ r, inj₂ g) }

    prism  : Ref A ⊕ Ref B ⊸ G ⊸ (Ref A ⊕ Ref B) ⊗ (T ⊕ G)      G = ∀'x ⊏ ⊓Δ. Mut 'x A ⊸ ['x] T
    prismB : Ref A ⊕ Ref B ⊸ !G ⊸ (Ref A ⊕ Ref B) ⊗ (T ⊕ 1)

In the linear form the callback comes back unused when there is no focus; `prismB` takes it
under `!` and drops it.  `Optic.lift` (`withswap`) turns either into an optic from
`Mut @a (Ref A ⊕ Ref B)`: a fresh-lifetime `Mut 'x A` of the payload, lent while the variant
sits in a cell that is itself only borrowed.  Every piece is an existing rule; nothing is added.

**Tag law** (`prismLift_runs`, `tag_frozen`): on every run the cell holding the variant holds
exactly what it held before, so its tag is unchanged.  If it held `inj₁ r`, the callback ran on
the payload cell `r`, and the cell holds `inj₁ r` again; if it held `inj₂ r`, nothing ran and
the heap is unchanged.

`variantProg` borrows a variant cell mutably, writes its payload through the lifted prism, ends
the borrows and frees everything; `adequacyC` runs it to `()` with no cell left, and the
interpreter shows the tag kept and the payload written (`variantObs_eval`), and at the other
tag nothing written (`variantObs₂_eval`).
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

/-- `Ref A ⊕ Ref B`. -/
abbrev vcell (A B : VTy) : VTy := .sum (.ref A) (.ref B)

/-- `λs. λg. case s {inj₁ r ⇒ let (r′, t) = withbor r g; (inj₁ r′, inj₁ t) | inj₂ r ⇒ b₂}`. -/
def prismOf (b₂ : Expr) : Val :=
  .lam (.val (.lam (.case (.var 1)
    (.letpair (app2 (.val withborV) (.var 0) (.var 1)) (.pair (.inj₁ (.var 1)) (.inj₁ (.var 0))))
    b₂)))

/-- The linear prism: the unused callback comes back. -/
def prismV : Val := prismOf (.pair (.inj₂ (.var 0)) (.inj₂ (.var 1)))

/-- The `!` prism: the unused callback is dropped. -/
def prismBV : Val := prismOf (.pair (.inj₂ (.var 0)) (.inj₂ unit'))

/-- The shared branch: the payload cell lent to `g` by `withbor`; `hg` reads the callback slot. -/
theorem d_prismBranch₁ {Δ : LifeCtx} {Γ : Ctx VTy} {x : LifeVar} {A B T GT Out : VTy}
    (hA : plainV A = true) (hT : plainV T = true) (hx : Δ.find? x = none) (hΓ : Ctx.Dead Γ)
    (hg : CDerives Δ (⟨.ref A, false⟩ :: ⟨GT, true⟩ :: ⟨vcell A B, false⟩ :: Γ) (.var 1)
      (.val (cbTy (fun c => .mut c A) x Δ.meetOfDom T))) :
    CDerives Δ (⟨.ref A, true⟩ :: ⟨GT, true⟩ :: ⟨vcell A B, false⟩ :: Γ)
      (.letpair (app2 (.val withborV) (.var 0) (.var 1)) (.pair (.inj₁ (.var 1)) (.inj₁ (.var 0))))
      (.val (.tensor (vcell A B) (.sum T Out))) := by
  have hD := hΓ.toP
  refine .letpairV (A := .ref A) (B := T) (.left (.left (.dead (deadSplit hΓ)))) ?_ ?_
  · exact .lolliE (.right (.left (.dead (deadSplit hΓ)))) hg
      (.lolliE (.left (.dead (.dead (deadSplit hΓ)))) (.var (.here (.cons (.cons hD))))
        (.withbor2 x (.cons (.cons (.cons hD))) hx
          ⟨.top, Lifetime.LifeCtx.defines_of_wf rfl, plain_outlives hA⟩ (plain_noFree hA)
          (plain_noFree hT)))
  · exact .tensorI (.right (.left (.dead (.dead (.dead (deadSplit hΓ))))))
      (.sumI₁ (.var (.there (.here (.cons (.cons (.cons hD)))))))
      (.sumI₁ (.var (.here (.cons (.cons (.cons (.cons hD)))))))

/-- The linear prism's typing. -/
theorem d_prism {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {x : LifeVar} {A B T : VTy}
    (hA : plainV A = true) (hT : plainV T = true) (hx : Δ.find? x = none) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val prismV)
      (.val (opticTy (fun _ => vcell A B) (fun c => .mut c A) id (fun T G => .sum T G) a x
        Δ.meetOfDom T)) := by
  have hD := hΓ.toP
  refine .lamV (.lamV (.caseV (.right (.left (deadSplit hΓ))) (.var (.there (.here hD))) ?_ ?_))
  · exact d_prismBranch₁ hA hT hx hΓ (.var (.there (.here (.cons hD))))
  · exact .tensorI (.left (.right (.dead (deadSplit hΓ))))
      (.sumI₂ (.var (.here (.cons (.cons hD)))))
      (.sumI₂ (.var (.there (.here (.cons hD)))))

/-- The `!` prism's typing. -/
theorem d_prismB {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {x : LifeVar} {A B T : VTy}
    (hA : plainV A = true) (hT : plainV T = true) (hx : Δ.find? x = none) (hΓ : Ctx.Dead Γ) :
    CDerives Δ Γ (.val prismBV)
      (.val (opticTy (fun _ => vcell A B) (fun c => .mut c A) .bang (fun T _ => .sum T .unit) a x
        Δ.meetOfDom T)) := by
  have hD := hΓ.toP
  refine .lamV (.lamV (.caseV (.right (.left (deadSplit hΓ))) (.var (.there (.here hD))) ?_ ?_))
  · exact d_prismBranch₁ hA hT hx hΓ (.bangE (.var (.there (.here (.cons hD)))))
  · exact .tensorI (.left (.right (.dead (deadSplit hΓ))))
      (.sumI₂ (.var (.here (.cons (.cons hD)))))
      (.sumI₂ (.unitI (.cons (.drop rfl (.cons hD)))))

/-! ### Runs -/

/-- The branch at `inj₁ r`: `g` runs on the payload cell. -/
theorem steps_branch₁_iff {μ μ' : Heap} {r g w : Val} :
    Steps μ (.letpair (app2 (.val withborV) r.1 g.1) (.pair (.inj₁ (.var 1)) (.inj₁ (.var 0))))
      μ' w.1 ↔ ∃ t : Val, w = .pair (.inj₁ r) (.inj₁ t) ∧ Steps μ (app2 g.1 unit' r.1) μ' t.1 := by
  rw [steps_letpairK_iff]
  have e : ∀ t : Val, (((Expr.pair (.inj₁ (.var 1)) (.inj₁ (.var 0))).subst 0 (t.shift 1 0)).subst 0 r)
      = (Val.pair (.inj₁ r) (.inj₁ t)).1 := fun t => by
    simp [Expr.subst_shift 0 0 0 r t.1 (le_refl _) (le_refl _)]
  constructor
  · rintro ⟨μm, v, h₁, h₂⟩
    obtain ⟨t, rfl, hgt⟩ := steps_withbor_iff.mp h₁
    rw [steps_letpair_iff, e] at h₂
    obtain ⟨rfl, rfl⟩ := steps_val_iff.mp h₂
    exact ⟨t, rfl, hgt⟩
  · rintro ⟨t, rfl, h⟩
    refine ⟨μ', .pair r t, steps_withbor_iff.mpr ⟨t, rfl, h⟩, ?_⟩
    rw [steps_letpair_iff, e]
    exact .refl _ _

/-- What a prism run does, `b` the result at the other tag. -/
def prismObs (b : Val → Val) (μ μ' : Heap) (s g t : Val) : Prop :=
  (∃ r t' : Val, s = .inj₁ r ∧ t = .inj₁ t' ∧ Steps μ (app2 g.1 unit' r.1) μ' t'.1) ∨
  (∃ r : Val, s = .inj₂ r ∧ t = .inj₂ (b g) ∧ μ' = μ)

theorem steps_prismOf_iff {b₂ : Expr} {b : Val → Val} {μ μ' : Heap} {s g w : Val}
    (hg : closedAt 0 g.1 = true)
    (hb : ∀ r : Val, ((b₂.subst 2 ((s.shift 1 0).shift 1 0)).subst 1 g).subst 0 r
      = (Val.pair (.inj₂ r) (.inj₂ (b g))).1) :
    Steps μ (app2 (.val (prismOf b₂)) s.1 g.1) μ' w.1 ↔
      ∃ t : Val, w = .pair s t ∧ prismObs b μ μ' s g t := by
  rw [show Expr.val (prismOf b₂) = lam2 (.case (.var 1)
    (.letpair (app2 (.val withborV) (.var 0) (.var 1)) (.pair (.inj₁ (.var 1)) (.inj₁ (.var 0))))
    b₂) from rfl, steps_app2_iff]
  have e : ((Expr.case (.var 1)
      (.letpair (app2 (.val withborV) (.var 0) (.var 1)) (.pair (.inj₁ (.var 1)) (.inj₁ (.var 0))))
      b₂).subst 1 (s.shift 1 0)).subst 0 g
      = .case s.1 (.letpair (app2 (.val withborV) (.var 0) g.1)
          (.pair (.inj₁ (.var 1)) (.inj₁ (.var 0)))) ((b₂.subst 2 ((s.shift 1 0).shift 1 0)).subst 1 g) := by
    simp [app2, withborV, v0, v1, unit', closed_shift hg, closedV_shift hg,
      Expr.subst_shift 0 0 0 g s.1 (le_refl _) (le_refl _)]
  rw [e, steps_case_val_iff]
  have e₁ : ∀ r : Val, (Expr.letpair (app2 (.val withborV) (.var 0) g.1)
      (.pair (.inj₁ (.var 1)) (.inj₁ (.var 0)))).subst 0 r
      = .letpair (app2 (.val withborV) r.1 g.1) (.pair (.inj₁ (.var 1)) (.inj₁ (.var 0))) :=
    fun r => by simp [app2, withborV, v0, v1, unit', closed_subst hg]
  constructor
  · rintro (⟨r, rfl, h⟩ | ⟨r, rfl, h⟩)
    · rw [e₁, steps_branch₁_iff] at h
      obtain ⟨t, rfl, h⟩ := h
      exact ⟨.inj₁ t, rfl, .inl ⟨r, t, rfl, rfl, h⟩⟩
    · rw [hb r] at h
      obtain ⟨rfl, rfl⟩ := steps_val_iff.mp h
      exact ⟨.inj₂ (b g), rfl, .inr ⟨r, rfl, rfl, rfl⟩⟩
  · rintro ⟨t, rfl, (⟨r, t', rfl, rfl, h⟩ | ⟨r, rfl, rfl, rfl⟩)⟩
    · exact .inl ⟨r, rfl, by rw [e₁, steps_branch₁_iff]; exact ⟨t', rfl, h⟩⟩
    · exact .inr ⟨r, rfl, by rw [hb r]; exact .refl _ _⟩

/-! ### The prisms as optics -/

/-- **The linear prism** onto the first case's payload. -/
def prism (A B : VTy) (hA : plainV A = true) :
    Optic (fun _ => vcell A B) (fun c => .mut c A) id (fun T G => .sum T G) where
  run := prismV
  closed := rfl
  Adm Δ _ x := Δ.find? x = none
  wf hx hT hΓ := d_prism hA hT hx hΓ
  Obs := prismObs id
  runs {μ μ' s g w} _ hs hg := steps_prismOf_iff hg fun r => by
    simp [closed_subst hg]

/-- **The `!` prism** onto the first case's payload. -/
def prismB (A B : VTy) (hA : plainV A = true) :
    Optic (fun _ => vcell A B) (fun c => .mut c A) .bang (fun T _ => .sum T .unit) where
  run := prismBV
  closed := rfl
  Adm Δ _ x := Δ.find? x = none
  wf hx hT hΓ := d_prismB hA hT hx hΓ
  Obs := prismObs (fun _ => .unit)
  runs {μ μ' s g w} _ hs hg := steps_prismOf_iff hg fun r => by simp [unit']

/-- **The runs of the lifted `!` prism**: at `inj₁ r` the callback runs on the payload cell `r`
and the variant's cell gets `inj₁ r` back; at `inj₂ r` nothing happens. -/
theorem prismLift_runs {A B : VTy} (hA : plainV A = true) {μ μ' : Heap} {ℓ : Loc} {g w : Val}
    (hμ : HeapClosed μ) (hg : closedAt 0 g.1 = true) :
    Steps μ (app2 (.val (prismB A B hA).lift.run) (Val.loc ℓ).1 g.1) μ' w.1 ↔
      (∃ (r t : Val) (μ₁ : Heap), μ ℓ = some (.inj₁ r) ∧ Steps μ (app2 g.1 unit' r.1) μ₁ t.1 ∧
        (∃ u, μ₁ ℓ = some u) ∧ μ' = μ₁.upd ℓ (.inj₁ r) ∧ w = .pair (.loc ℓ) (.inj₁ t)) ∨
      (∃ r : Val, μ ℓ = some (.inj₂ r) ∧ μ' = μ ∧ w = .pair (.loc ℓ) (.inj₂ .unit)) := by
  rw [(prismB A B hA).lift.runs hμ rfl hg]
  simp only [Optic.lift, liftObs, prismB, prismObs]
  constructor
  · rintro ⟨t, rfl, ℓ₀, s, μ₁, hℓ₀, hs, hobs, hdom, rfl⟩
    obtain rfl : ℓ = ℓ₀ := by simpa using hℓ₀
    rcases hobs with ⟨r, t', rfl, rfl, h⟩ | ⟨r, rfl, rfl, rfl⟩
    · exact .inl ⟨r, t', μ₁, hs, h, hdom, rfl, rfl⟩
    · exact .inr ⟨r, hs, upd_self hs, rfl⟩
  · rintro (⟨r, t, μ₁, hs, h, hdom, rfl, rfl⟩ | ⟨r, hs, rfl, rfl⟩)
    · exact ⟨.inj₁ t, rfl, ℓ, .inj₁ r, μ₁, rfl, hs, .inl ⟨r, t, rfl, rfl, h⟩, hdom, rfl⟩
    · exact ⟨.inj₂ .unit, rfl, ℓ, .inj₂ r, μ', rfl, hs, .inr ⟨r, rfl, rfl, rfl⟩, ⟨_, hs⟩,
        (upd_self hs).symm⟩

/-- **The tag is frozen**: on every run of the lifted prism, the variant's cell holds what it
held before; in particular its tag. -/
theorem tag_frozen {A B : VTy} (hA : plainV A = true) {μ μ' : Heap} {ℓ : Loc} {g w : Val}
    (hμ : HeapClosed μ) (hg : closedAt 0 g.1 = true)
    (h : Steps μ (app2 (.val (prismB A B hA).lift.run) (Val.loc ℓ).1 g.1) μ' w.1) :
    μ' ℓ = μ ℓ :=
  (prismB A B hA).lift_cell hμ hg h

/-- The same law for the linear prism. -/
theorem tag_frozen_lin {A B : VTy} (hA : plainV A = true) {μ μ' : Heap} {ℓ : Loc} {g w : Val}
    (hμ : HeapClosed μ) (hg : closedAt 0 g.1 = true)
    (h : Steps μ (app2 (.val (prism A B hA).lift.run) (Val.loc ℓ).1 g.1) μ' w.1) :
    μ' ℓ = μ ℓ :=
  (prism A B hA).lift_cell hμ hg h

/-! ### A program: writing a variant's payload through a mutable borrow of its cell

    let (c, u) = withbor (alloc (inj₁ (alloc (inj₁ ())))) (Λ. λm.
                   let (m′, r) = (lift prismB) m (! Λ. λp. let (p′, u) = withswap p setG;
                                                               u; forget p′; ());
                   forget m′; drop r; ());
    u; case (free c) {inj₁ x ⇒ drop (free x) | inj₂ y ⇒ drop (free y)}

`m : Mut 'a (Ref B ⊕ Ref B)` is the borrowed variant cell; the lifted prism lends its payload
cell at `'x ⊏ 'a`. -/

/-- `lift prismB` as a value. -/
def liftPrismBV : Val := liftV prismBV

theorem liftPrismB_run (A B : VTy) (hA : plainV A = true) :
    (prismB (ℍ := ℍ) A B hA).lift.run = liftPrismBV := rfl

/-- The setter at `D1`, binder `1`, under `!`. -/
theorem d_setterB {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives D1 Γ setBorrower
      (.val (.bang (cbTy (fun c => .mut c BB) 1 D1.meetOfDom .unit))) := by
  refine .bangThunkV (fun s hs hl => absurd hl (by
      have := dead_noLive hΓ (P := fun _ => False) s hs; simpa using fun h => this h)) rfl
    (allI_fresh (S := .unit) d1_ok rfl hΓ (.ret (.lamV ?_)))
  exact letW (A := .mut (.var 1) BB) (B := .unit)
      (appW (d_setG (by cdead)) (appW (.var (by csolo)) (.withswap (by cdead)))) <|
    seqW (.var (by csolo)) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead)))
      (.boxI (.unitI (by cdead)) ⟨Lifetime.LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩)

/-- The borrower: the lifted prism on `m`, the result dropped. -/
def varCb : Expr :=
  .val (.lam (.val (.lam (.letpair (app2 (.val liftPrismBV) (.var 0) setBorrower)
    (.seq (.app forget (.var 1)) (.seq (dropB (.var 0)) unit'))))))

theorem d_varCb (ℍ : BoCa.Host) [BoCa.HostIs ℍ] :
    CDerives LifeCtx.empty [] varCb
      (.val (cbTy (fun c => .mut c (vcell BB BB)) 0 LifeCtx.empty.meetOfDom .unit)) := by
  refine callbackW ok_empty rfl .nil ?_
  refine letW (A := .mut (.var 0) (vcell BB BB)) (B := .sum .unit .unit)
    (appW (d_setterB (by cdead)) (appW (.var (by csolo))
      (liftPrismB_run (ℍ := ℍ) BB BB rfl ▸
        (prismB BB BB rfl).lift.wf (Δ := D1) (a := .var 0) (x := 1) (T := .unit) rfl rfl (by cdead)))) ?_
  refine seqW (appW (.var (by csolo)) (.forgetMut (by cdead))) ?_
  exact seqW (d_dropB (.var (by csolo)) (by cdead))
    (.boxI (.unitI (by cdead)) ⟨Lifetime.LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩)

/-- `case (free c) {inj₁ x ⇒ drop (free x) | inj₂ y ⇒ drop (free y)}`, `c` at index `i`. -/
def freeVar (i : Nat) : Expr :=
  .case (.app free' (.var i)) (dropB (.app free' (.var 0))) (dropB (.app free' (.var 0)))

/-- The program at the variant `e`. -/
def variantProgAt (e : Expr) : Expr :=
  .letpair (app2 (.val withborV) (.app alloc' e) varCb) (.seq (.var 0) (freeVar 1))

/-- The same run, returning the variant's tag with its payload's content. -/
def variantObsAt (e : Expr) : Expr :=
  .letpair (app2 (.val withborV) (.app alloc' e) varCb)
    (.seq (.var 0) (.case (.app free' (.var 1)) (.inj₁ (.app free' (.var 0)))
      (.inj₂ (.app free' (.var 0)))))

def variantProg : Expr := variantProgAt (.inj₁ (.app alloc' (.inj₁ unit')))

theorem d_variantProgAt (ℍ : BoCa.Host) [BoCa.HostIs ℍ] {e : Expr}
    (he : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ → CDerives LifeCtx.empty Γ e (.val (vcell BB BB))) :
    CDerives LifeCtx.empty [] (variantProgAt e) (.val .unit) := by
  refine letW (A := .ref (vcell BB BB)) (B := .unit)
    (appW (d_varCb ℍ) (appW (appW (he (by cdead)) (.alloc (by cdead)))
      (.withbor2 0 (by cdead) rfl ⟨.top, Lifetime.LifeCtx.defines_of_wf rfl, plain_outlives rfl⟩
        (by simp [VFree]) (by simp [VFree])))) ?_
  refine seqW (.var (by csolo)) ?_
  exact caseW (appW (.var (by csolo)) (.free (by cdead)))
    (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead))
    (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead))

theorem d_variantProg (ℍ : BoCa.Host) [BoCa.HostIs ℍ] :
    CDerives LifeCtx.empty [] variantProg (.val .unit) :=
  d_variantProgAt ℍ fun hΓ => .sumI₁ (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead)))

theorem variantProg_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem variantProg Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret (d_variantProg ℍ))

theorem variantProg_eval : unitNoLeak (eval variantProg) = true := by decide

/-- At `inj₁`: the tag is kept and the payload written, `inj₁ (inj₂ ())`. -/
theorem variantObs_eval :
    (match eval (variantObsAt (.inj₁ (.app alloc' (.inj₁ unit')))) with
      | .value ⟨.inj₁ (.inj₂ .unit), _⟩ false => true
      | _ => false) = true := by decide

/-- At `inj₂`: the callback does not run, and the variant is as it was, `inj₂ (inj₁ ())`. -/
theorem variantObs₂_eval :
    (match eval (variantObsAt (.inj₂ (.app alloc' (.inj₁ unit')))) with
      | .value ⟨.inj₂ (.inj₁ .unit), _⟩ false => true
      | _ => false) = true := by decide

theorem variantProg₂_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem (variantProgAt (.inj₂ (.app alloc' (.inj₁ unit'))))
      Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret (d_variantProgAt ℍ fun hΓ =>
    .sumI₂ (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead)))))

end BoCa.Fig16.LogRel.Core.Optics

end

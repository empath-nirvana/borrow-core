import HandlersControl.Reentry

/-!
# The capture rule's modes, where BoLo + `!` has them

A handler that receives the rest of the computation as a value `k : B ⊸ R` (`Behind.lean`) can use
it in four ways.  Each is checked here against the paper's rules.

* **Multi-shot, `!`.**  `k` can be copied only at `!(B ⊸ R)`, and a `λ` has a `!` type only over a
  context of `!` slots (`lam_bang_persistent`, by inversion of `DerivesWf`): the promotion premise
  `!Γ` of SPEC §2 is exactly "the continuation captures only persistent values".
  - `twoShot`: `choose` resumed twice with a continuation that captures a `!` function; typed,
    safe, run (`twoShot_eval`: `(inj₂ (), inj₁ ())`).
  - `multiShot_ref_refused`: a continuation capturing a `Ref` (or any non-`!` slot) is never `!`.
* **Linear, dropped.**  `forget` has no typing at a function type (`forget_not_lolli`): BoLo cannot
  discard a continuation.  Abort is encoded by resuming the continuation into its own finalizer:
  the continuation takes `B ⊕ 1`, and its `inj₂` branch releases what it captured (`abortProg`,
  typed, safe: the captured cell is freed; run).
* **Owned, resumed later.**  The handler stores `k` in a cell, does other work, and resumes it
  (`laterProg`: typed, safe, run).  Crossing a *borrow scope* is `Outlives.lean`.
* **Borrowed, used in place.**  The tail-resumptive case, where no continuation is reified at all:
  `HandlersAsBorrows`.

`[about ours]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace HandlersControl
open BoCa BoCa.Lifetime BoCa.Programs HandlersAsBorrows.Xi

/-! ## Inversion: a `λ` at a `!` type is over persistent slots -/

/-- `T` is `!U` under boxes. -/
def Bangish : Ty → Prop
  | .bang _ => True
  | .box _ T => Bangish T
  | _ => False

theorem lam_bang_persistent {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty}
    (h : DerivesWf Δ Γ e T) : ∀ {b : Expr}, e = .lam b → Bangish T → Ctx.Persistent Γ := by
  induction h with
  | bangLamI hΓ _ _ _ => intro _ _ _; exact hΓ
  | bangAllI hΓ _ _ _ _ _ => intro _ _ _; exact hΓ
  | boxIctx _ _ ih => intro b he hb; exact ih he hb
  | boxE _ ih => intro b he hb; exact ih he hb
  | bangE _ ih => intro b he _; exact ih he trivial
  | lolliI _ _ _ => intro _ _ hb; exact hb.elim
  | allI _ _ _ _ _ => intro _ _ hb; exact hb.elim
  | immSub _ _ _ => intro _ _ hb; exact hb.elim
  | mutSub _ _ _ => intro _ _ hb; exact hb.elim
  | swapAx _ => intro _ _ hb; exact hb.elim
  | copyAx _ => intro _ _ hb; exact hb.elim
  | forgetImmAx _ => intro _ _ hb; exact hb.elim
  | forgetMutAx _ => intro _ _ hb; exact hb.elim
  | forgetUnkAx _ => intro _ _ hb; exact hb.elim
  | withbor1Ax _ _ _ _ => intro _ _ hb; exact hb.elim
  | withbor2Ax _ _ _ _ _ => intro _ _ hb; exact hb.elim
  | withbor3Ax _ _ _ _ => intro _ _ hb; exact hb.elim
  | withloadAx _ _ _ _ => intro _ _ hb; exact hb.elim
  | withswapAx _ => intro _ _ hb; exact hb.elim
  | copyBangAx _ => intro _ _ hb; exact hb.elim
  | forgetBangAx _ => intro _ _ hb; exact hb.elim
  | _ => intro _ he _; cases he

/-- **Multi-shot only over persistent captures.**  A continuation whose context holds a live
non-`!` slot (a `Ref`, a borrow, data) has no `!` type, so it cannot be copied. -/
theorem multiShot_refused {Δ : LifeCtx} {Γ : Ctx Ty} {U : Ty} (hU : ∀ V, U ≠ .bang V)
    {b : Expr} {T : Ty} : ¬ DerivesWf Δ (⟨U, true⟩ :: Γ) (.val (.lam b)) (.bang T) := by
  intro h
  obtain ⟨V, hV⟩ := lam_bang_persistent h rfl trivial ⟨U, true⟩ List.mem_cons_self rfl
  exact hU V hV

theorem multiShot_ref_refused {Δ : LifeCtx} {Γ : Ctx Ty} {U : Ty} {b : Expr} {T : Ty} :
    ¬ DerivesWf Δ (⟨.ref U, true⟩ :: Γ) (.val (.lam b)) (.bang T) :=
  multiShot_refused (fun _ h => by cases h)

theorem multiShot_imm_refused {Δ : LifeCtx} {Γ : Ctx Ty} {a : Life} {U : Ty} {b : Expr} {T : Ty} :
    ¬ DerivesWf Δ (⟨.imm a U, true⟩ :: Γ) (.val (.lam b)) (.bang T) :=
  multiShot_refused (fun _ h => by cases h)

/-! ## `forget` has no typing at a function type -/

/-- `()` is typed only in a consumed context. -/
theorem unit_dead {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty} (h : DerivesWf Δ Γ e T) :
    e = .unit → Ctx.Dead Γ := by
  induction h with
  | unitI hd => intro _; exact hd
  | boxIctx _ _ ih => exact ih
  | boxE _ ih => exact ih
  | immSub _ _ ih => exact ih
  | mutSub _ _ ih => exact ih
  | bangE _ ih => exact ih
  | _ => intro he; cases he

/-- Strip boxes. -/
def unbox : Ty → Ty
  | .box _ T => unbox T
  | T => T

/-- The types `forget` has: the axiom types, and `∀`/`!∀` from `Λ.()`. -/
def ForgetTy (T : Ty) : Prop :=
  (∃ X, unbox T = .lolli X .unit ∧
      ((∃ a U, X = .imm a U) ∨ (∃ a U, X = .mut a U) ∨ X = .unk ∨ ∃ U, X = .bang U)) ∨
    (∃ x c U, unbox T = .all x c U) ∨ (∃ x c U, unbox T = .bang (.all x c U))

theorem forget_types {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr} {T : Ty} (h : DerivesWf Δ Γ e T) :
    e = forget → ForgetTy T := by
  induction h with
  | lolliI _ hb _ =>
      intro he
      simp only [forget, Expr.val, Val.lam, unit'] at he
      cases he
      exact absurd (unit_dead hb rfl) (by intro h'; cases h')
  | bangLamI _ _ hb _ =>
      intro he
      simp only [forget, Expr.val, Val.lam, unit'] at he
      cases he
      exact absurd (unit_dead hb rfl) (by intro h'; cases h')
  | allI _ _ _ _ _ => intro _; exact .inr (.inl ⟨_, _, _, rfl⟩)
  | bangAllI _ _ _ _ _ _ => intro _; exact .inr (.inr ⟨_, _, _, rfl⟩)
  | boxIctx _ _ ih => intro he; exact ih he
  | boxE _ ih => intro he; exact ih he
  | immSub _ _ ih =>
      intro he
      rcases ih he with ⟨X, hX, _⟩ | ⟨x, c, U, hU⟩ | ⟨x, c, U, hU⟩ <;> simp [unbox] at *
  | mutSub _ _ ih =>
      intro he
      rcases ih he with ⟨X, hX, _⟩ | ⟨x, c, U, hU⟩ | ⟨x, c, U, hU⟩ <;> simp [unbox] at *
  | bangE _ ih =>
      intro he
      rcases ih he with ⟨X, hX, _⟩ | ⟨x, c, U, hU⟩ | ⟨x, c, U, hU⟩
      · simp [unbox] at hX
      · simp [unbox] at hU
      · simp only [unbox, Ty.bang.injEq] at hU
        subst hU
        exact .inr (.inl ⟨x, c, U, rfl⟩)
  | forgetImmAx _ => intro _; exact .inl ⟨_, rfl, .inl ⟨_, _, rfl⟩⟩
  | forgetMutAx _ => intro _; exact .inl ⟨_, rfl, .inr (.inl ⟨_, _, rfl⟩)⟩
  | forgetUnkAx _ => intro _; exact .inl ⟨_, rfl, .inr (.inr (.inl rfl))⟩
  | forgetBangAx _ => intro _; exact .inl ⟨_, rfl, .inr (.inr (.inr ⟨_, rfl⟩))⟩
  | _ =>
      intro he
      simp_all [forget, copy, swap, withbor, withload, withswap, lam2, elet, Expr.val, Val.lam,
        Val.prim, Val.unit, unit', v0, v1, v2, v3]

/-- **A continuation cannot be forgotten**: `forget` has no type `(T₁ ⊸ T₂) ⊸ 1`. -/
theorem forget_not_lolli {Δ : LifeCtx} {Γ : Ctx Ty} {T₁ T₂ : Ty} :
    ¬ DerivesWf Δ Γ forget (.lolli (.lolli T₁ T₂) .unit) := by
  intro h
  rcases forget_types h rfl with ⟨X, hX, hk⟩ | ⟨x, c, U, hU⟩ | ⟨x, c, U, hU⟩
  · simp only [unbox, Ty.lolli.injEq] at hX
    obtain ⟨rfl, -⟩ := hX
    rcases hk with ⟨a, U, h'⟩ | ⟨a, U, h'⟩ | h' | ⟨U, h'⟩ <;> cases h'
  · simp [unbox] at hU
  · simp [unbox] at hU

/-! ## Multi-shot: `choose`, resumed twice -/

/-- The request type of `choose`: done with `B`, or a request with a `!` continuation. -/
abbrev CT : Ty := .sum B (.tensor .unit (.bang (.lolli B B)))

/-- The body: `let g = !notB; choose((), !λb. g b)`.  The continuation captures `g`, which is
persistent. -/
def chooseBody : Expr := elet notB (.inj₂ (.pair unit' (lam (.app (.var 1) (.var 0)))))

/-- The multi-shot handler: resume with `inj₁ ()` and with `inj₂ ()`. -/
def twoShotH : Expr :=
  lam (.case (.var 0) (.app dupB (.var 0))
    (.letpair (.var 0) (.seq (.var 1) (.letpair (.app copy (.var 0))
      (.pair (.app (.var 1) (.inj₁ unit')) (.app (.var 0) (.inj₂ unit')))))))

def twoShot : Expr := .app twoShotH chooseBody

theorem d_notB_bang {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ Γ notB (.bang (.lolli B B)) :=
  .bangLamI hΓ.persistent rfl (.sumE (T₁ := .unit) (T₂ := .unit) (.left hΓ.split) rfl
    (.var (.here hΓ)) (.sumI₂ (.var (.here (by dead)))) (.sumI₁ (.var (.here (by dead)))))

theorem d_chooseBody {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) : DerivesWf Δ Γ chooseBody CT := by
  refine .lolliE hΓ.split (d_notB_bang hΓ) (.lolliI rfl ?_)
  -- ctx: g
  refine .sumI₂ (.tensorI (.right hΓ.split) (.unitI (by dead)) ?_)
  have hp : Ctx.Persistent (⟨Ty.bang (.lolli B B), true⟩ :: Γ) := by
    intro s hs hl
    rcases List.mem_cons.mp hs with rfl | hs'
    · exact ⟨_, rfl⟩
    · exact hΓ.persistent s hs' hl
  exact .bangLamI hp rfl
    (.lolliE (.left (.right hΓ.split)) (.var (.here (by dead)))
      (.bangE (.var (.there (.here (by dead))))))

theorem d_twoShotH {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ Γ twoShotH (.lolli CT (.tensor B B)) := by
  refine .lolliI rfl (.sumE (T₁ := B) (T₂ := .tensor .unit (.bang (.lolli B B))) (.left hΓ.split)
    rfl (.var (.here hΓ))
    (.lolliE (.left (.dead hΓ.split)) (.var (.here (by dead))) (d_dupB (by dead))) ?_)
  -- ctx: q, c
  refine .tensorE (T₁ := .unit) (T₂ := .bang (.lolli B B)) (.left (.dead hΓ.split)) rfl
    (.var (.here (by dead))) ?_
  -- ctx: k, u, q, c
  refine .unitE (.right (.left (.dead (.dead hΓ.split)))) (.var (.there (.here (by dead)))) ?_
  refine .tensorE (T₁ := .bang (.lolli B B)) (T₂ := .bang (.lolli B B))
    (.left (.dead (.dead (.dead hΓ.split)))) rfl
    (.lolliE (.left (.dead (.dead (.dead hΓ.split)))) (.var (.here (by dead)))
      (.copyBangAx (by dead))) ?_
  -- ctx: k2, k1, k, u, q, c
  exact .tensorI (.right (.left (.dead (.dead (.dead (.dead hΓ.split))))))
    (.lolliE (.dead (.right (.dead (.dead (.dead (.dead hΓ.split))))))
      (.sumI₁ (.unitI (by dead))) (.bangE (.var (.there (.here (by dead))))))
    (.lolliE (.right (.dead (.dead (.dead (.dead (.dead hΓ.split))))))
      (.sumI₂ (.unitI (by dead))) (.bangE (.var (.here (by dead)))))

theorem d_twoShot : DerivesWf LifeCtx.empty [] twoShot (.tensor B B) :=
  .lolliE .nil (d_chooseBody .nil) (d_twoShotH .nil)

def twoShotU : Expr := .letpair twoShot (.seq (dropB (.var 1)) (dropB (.var 0)))

theorem d_twoShotU : DerivesWf LifeCtx.empty [] twoShotU .unit :=
  .tensorE (T₁ := B) (T₂ := B) .nil rfl d_twoShot
    (.unitE (.right (.left .nil))
      (.sumE (T₁ := .unit) (T₂ := .unit) (.dead (.left .nil)) rfl (.var (.there (.here .nil)))
        (.var (.here (by dead))) (.var (.here (by dead))))
      (d_dropB (by dead)))

theorem twoShotU_runs : BoLo.Steps Adequacy.emptyMem twoShotU Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_twoShotU

/-- **Run**: the continuation `not` is resumed twice. -/
theorem twoShot_eval :
    (match eval twoShot with
      | .value ⟨.pair (.inj₂ .unit) (.inj₁ .unit), _⟩ false => true
      | _ => false) = true := by decide

/-! ## Linear, dropped: abort through the continuation's finalizer -/

/-- A request with a continuation that takes `resume ⊕ abort`. -/
abbrev AT : Ty := .sum .unit (.tensor .unit (.lolli B .unit))

/-- `let r = alloc (); raise((), λx. case x {y ⇒ y; free r | z ⇒ z; free r})`. -/
def abortBody : Expr :=
  elet (.app alloc' unit')
    (.inj₂ (.pair unit' (lam (.case (.var 0) (.seq (.var 0) (.app free' (.var 2)))
      (.seq (.var 0) (.app free' (.var 2)))))))

/-- The aborting handler: it never resumes normally, it resumes into `abort`. -/
def abortH : Expr :=
  lam (.case (.var 0) (.var 0) (.letpair (.var 0) (.seq (.var 1) (.app (.var 0) (.inj₂ unit')))))

def abortProg : Expr := .app abortH abortBody

theorem d_abortProg : DerivesWf LifeCtx.empty [] abortProg .unit := by
  refine .lolliE (T₁ := AT) .nil ?_ ?_
  · refine .lolliE (T₁ := .ref .unit) .nil (.lolliE .nil (.unitI .nil) (.allocAx .nil))
      (.lolliI rfl (.sumI₂ (.tensorI (.right .nil) (.unitI (by dead)) (.lolliI rfl ?_))))
    -- ctx: x, r
    have br : DerivesWf LifeCtx.empty [⟨.unit, true⟩, ⟨B, false⟩, ⟨.ref .unit, true⟩]
        (.seq (.var 0) (.app free' (.var 2))) .unit :=
      .unitE (.left (.dead (.right .nil))) (.var (.here (by dead)))
        (.lolliE (.dead (.dead (.left .nil))) (.var (.there (.there (.here .nil))))
          (.freeAx (by dead)))
    exact .sumE (T₁ := .unit) (T₂ := .unit) (.left (.right .nil)) rfl (.var (.here (by dead))) br br
  · refine .lolliI rfl (.sumE (T₁ := .unit) (T₂ := .tensor .unit (.lolli B .unit)) (.left .nil) rfl
      (.var (.here .nil)) (.var (.here (by dead))) ?_)
    -- ctx: q, c
    refine .tensorE (T₁ := .unit) (T₂ := .lolli B .unit) (.left (.dead .nil)) rfl
      (.var (.here (by dead))) ?_
    -- ctx: k, u, q, c
    exact .unitE (.right (.left (.dead (.dead .nil)))) (.var (.there (.here (by dead))))
      (.lolliE (.right (.dead (.dead (.dead .nil)))) (.sumI₂ (.unitI (by dead)))
        (.var (.here (by dead))))

/-- **Safe**: the captured cell is released on the abort path; memory ends empty. -/
theorem abortProg_runs : BoLo.Steps Adequacy.emptyMem abortProg Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_abortProg

theorem abortProg_eval : unitNoLeak (eval abortProg) = true := by decide

/-! ## Owned, resumed later -/

/-- The handler stores the continuation in a cell, does other work (a `flip`-free `()`), then
takes it back and resumes it: `λc. case c {r ⇒ r | (u, k) ⇒ u; let q = alloc k; …; (free q) b}`. -/
def laterH : Expr :=
  lam (.case (.var 0) (.var 0)
    (.letpair (.var 0) (.seq (.var 1)
      (elet (.app alloc' (.var 0)) (.seq unit' (.app (.app free' (.var 0)) (.inj₁ unit')))))))

/-- One `flip`-style request whose continuation captures a cell `r`. -/
def laterBody : Expr :=
  elet (.app alloc' unit')
    (.inj₂ (.pair unit' (lam (.seq (.app free' (.var 1)) (.pair (.var 0) (.inj₂ unit'))))))

def laterProg : Expr := .app laterH laterBody

theorem d_laterProg : DerivesWf LifeCtx.empty [] laterProg (.tensor B B) := by
  refine .lolliE (T₁ := .sum (.tensor B B) (.tensor .unit (.lolli B (.tensor B B)))) .nil ?_ ?_
  · refine .lolliE (T₁ := .ref .unit) .nil (.lolliE .nil (.unitI .nil) (.allocAx .nil))
      (.lolliI rfl (.sumI₂ (.tensorI (.right .nil) (.unitI (by dead)) (.lolliI rfl ?_))))
    -- ctx: b, r
    exact .unitE (.right (.left .nil))
      (.lolliE (.dead (.left .nil)) (.var (.there (.here .nil))) (.freeAx (by dead)))
      (.tensorI (.left (.dead .nil)) (.var (.here (by dead))) (.sumI₂ (.unitI (by dead))))
  · refine .lolliI rfl (.sumE (T₁ := .tensor B B) (T₂ := .tensor .unit (.lolli B (.tensor B B)))
      (.left .nil) rfl (.var (.here .nil)) ?_ ?_)
    · exact .var (.here (by dead))
    · -- ctx: q, c
      refine .tensorE (T₁ := .unit) (T₂ := .lolli B (.tensor B B)) (.left (.dead .nil)) rfl
        (.var (.here (by dead))) ?_
      -- ctx: k, u, q, c
      refine .unitE (.right (.left (.dead (.dead .nil)))) (.var (.there (.here (by dead)))) ?_
      -- ctx: k, u, q, c; store `k`, then take it back and resume
      refine .lolliE (T₁ := .ref (.lolli B (.tensor B B))) (.left (.dead (.dead (.dead .nil))))
        (.lolliE (.left (.dead (.dead (.dead .nil)))) (.var (.here (by dead))) (.allocAx (by dead)))
        (.lolliI rfl ?_)
      -- ctx: cell, k, u, q, c
      exact .unitE (.right (.dead (.dead (.dead (.dead .nil))))) (.unitI (by dead))
        (.lolliE (.right (.dead (.dead (.dead (.dead .nil))))) (.sumI₁ (.unitI (by dead)))
          (.lolliE (.left (.dead (.dead (.dead (.dead .nil))))) (.var (.here (by dead)))
            (.freeAx (by dead))))

def laterU : Expr := .letpair laterProg (.seq (dropB (.var 1)) (dropB (.var 0)))

theorem d_laterU : DerivesWf LifeCtx.empty [] laterU .unit :=
  .tensorE (T₁ := B) (T₂ := B) .nil rfl d_laterProg
    (.unitE (.right (.left .nil))
      (.sumE (T₁ := .unit) (T₂ := .unit) (.dead (.left .nil)) rfl (.var (.there (.here .nil)))
        (.var (.here (by dead))) (.var (.here (by dead))))
      (d_dropB (by dead)))

/-- **Safe**: the continuation, stored and resumed later, releases its captured cell. -/
theorem laterU_runs : BoLo.Steps Adequacy.emptyMem laterU Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_laterU

theorem laterProg_eval :
    (match eval laterProg with
      | .value ⟨.pair (.inj₁ .unit) (.inj₂ .unit), _⟩ false => true
      | _ => false) = true := by decide

end HandlersControl

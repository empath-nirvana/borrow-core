import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S3_Dynamics.Definitions
import Support.Statics.Contexts
import Support.Statics.Presupposed
import Support.Syntax.Terms

/-!
# Examples — the typing rules and the axiom table, inhabited

Each typing rule of `[TR]` p. 2 and each line of the axiom table of `[TR]` p. 3,
derived at a concrete instance in `DerivesWf`, the judgment
`Fig16.LogRel.Typed.fundamentalProperty` and `Fig16.LogRel.Typed.adequacy` take as
hypothesis (§C.26).  §1 is the rules; §2 is the axiom table.

`[about ours: instances of [TR] p. 2's rules and p. 3's axiom table]`
-/

noncomputable section

namespace BoCa.Programs

open BoCa BoCa.Lifetime

/-! ## Lifetime contexts and entailments -/

/-- `['a ⊏ ⊤]`, with `'a` the variable `0`. -/
def D1 : LifeCtx := LifeCtx.empty.extend 0 .top

/-- `['b ⊏ 'a, 'a ⊏ ⊤]`: `'b` (the variable `1`) is strictly shorter than `'a`. -/
def D3 : LifeCtx := (LifeCtx.empty.extend 0 .top).extend 1 (.var 0)

/-- `'a`. -/
def av : Life := .var 0

/-- `'b`. -/
def bv : Life := .var 1

/-- `Δ ⊨ @a` from the scoping check `Life.wf`. -/
theorem _root_.BoCa.Lifetime.LifeCtx.defines_of_wf {Δ : LifeCtx} {a : Life} (h : a.wf Δ = true) : Δ.Defines a :=
  fun _ hδ => Life.interp_defined_of_wf hδ h

/-- `Δ ⊨ 'x ⊏ Δ('x)`: a bound variable is strictly shorter than its bound, which is
what `⟦Δ⟧` asks of every `δ`. -/
theorem entailsLt_bound {Δ : LifeCtx} {x : LifeVar} {u : Life} (h : Δ.find? x = some u) :
    Δ.EntailsLt (.var x) u :=
  fun _ hδ => hδ x u h

/-- `Δ ⊨ 'x ⊏ ⊤` for a bound `'x`. -/
theorem entailsLt_top {Δ : LifeCtx} {x : LifeVar} {u : Life} (h : Δ.find? x = some u) :
    Δ.EntailsLt (.var x) .top := by
  intro δ hδ
  obtain ⟨m, n, hm, _, hlt⟩ := hδ x u h
  refine ⟨m, SLife.top, hm, rfl, ?_⟩
  simp only [SLife.Lt, SLife.top] at hlt ⊢
  exact Nat.lt_of_le_of_lt (Nat.zero_le n) hlt

/-- `Δ ⊨ @a ⊑ @a` for a `Δ`-scoped `@a`. -/
theorem entailsLe_refl {Δ : LifeCtx} {a : Life} (h : a.wf Δ = true) : Δ.EntailsLe a a := by
  intro δ hδ
  obtain ⟨n, hn⟩ := Life.interp_defined_of_wf hδ h
  exact ⟨n, n, hn, hn, Nat.le_refl n⟩

/-- `[]I`'s context premise on a consumed context: `dom(Γ)` is the live slots, and
there are none, so only `Δ ⊨ @a` is asked. -/
theorem _root_.BoCa.Ctx.Dead.outlives {Δ : LifeCtx} {Γ : Ctx Ty} {a : Life} (ha : Δ.Defines a)
    (h : Ctx.Dead Γ) : Ctx.Outlives Δ Γ a := by
  refine ⟨ha, ?_⟩
  induction h with
  | nil => intro s hs; cases hs
  | cons _ ih =>
      intro s hs hl
      cases hs with
      | head => exact absurd hl (by simp)
      | tail _ hs' => exact ih s hs' hl

/-! ## 1. The rules of `[TR]` p. 2 -/

/-- `1I`: `•; • ⊢ () : 1`. -/
theorem d_unit : DerivesWf LifeCtx.empty [] (.val .unit) .unit := .unitI .nil

/-- `⊗I`: `((), ()) : 1 ⊗ 1`. -/
theorem d_pair : DerivesWf LifeCtx.empty [] (.pair unit' unit') (.tensor .unit .unit) :=
  .tensorI .nil (.unitI .nil) (.unitI .nil)

/-- `⊸I` and `ID`: `λx.x : 1 ⊸ 1`. -/
theorem d_id : DerivesWf LifeCtx.empty [] (.val (.lam (.var 0))) (.lolli .unit .unit) :=
  .lolliI rfl (.var (.here .nil))

/-- `⊸E`: `(λx.x) () : 1`. -/
theorem d_app : DerivesWf LifeCtx.empty [] (.app (.val (.lam (.var 0))) unit') .unit :=
  .lolliE .nil (.unitI .nil) d_id

/-- `1E`: `(); () : 1`. -/
theorem d_seq : DerivesWf LifeCtx.empty [] (.seq unit' unit') .unit :=
  .unitE .nil (.unitI .nil) (.unitI .nil)

/-- `⊕I` at `i = 1`: `inj₁ () : 1 ⊕ 1`. -/
theorem d_inj : DerivesWf LifeCtx.empty [] (.inj₁ unit') (.sum .unit .unit) :=
  .sumI₁ (.unitI .nil)

/-- `⊗E`: `let (x, y) = ((), ()); (x, y) : 1 ⊗ 1`. -/
theorem d_letpair :
    DerivesWf LifeCtx.empty []
      (.letpair (.pair unit' unit') (.pair (.var 1) (.var 0))) (.tensor .unit .unit) :=
  .tensorE .nil rfl (.tensorI .nil (.unitI .nil) (.unitI .nil))
    (.tensorI (.right (.left .nil)) (.var (.there (.here .nil))) (.var (.here (.cons .nil))))

/-- `⊕E`: `case (inj₁ ()) {x ⇒ x, y ⇒ y} : 1`. -/
theorem d_case :
    DerivesWf LifeCtx.empty [] (.case (.inj₁ unit') (.var 0) (.var 0)) .unit :=
  .sumE .nil rfl (.sumI₁ (.unitI .nil)) (.var (.here .nil)) (.var (.here .nil))

/-- `∀I`: `Λ.() : ∀'a ⊏ ⊤. 1`.  `Λ.e ≜ λ_.e` (§12.14), so the premise's context
carries a consumed slot for the phantom binder. -/
theorem d_forall : DerivesWf LifeCtx.empty [] (.val (.lam unit')) (.all 0 .top .unit) :=
  .allI (S := .unit) rfl rfl (fun _ hs => absurd hs (by simp)) (.unitI (.cons .nil))

/-- `∀E`: at `['b ⊏ 'a, 'a ⊏ ⊤]`, `(Λ.()) [] : 1`, instantiating a binder bounded by
`'a` at the strictly shorter `'b`.  `e[] ≜ e ()`. -/
theorem d_forallE : DerivesWf D3 [] (.app (.val (.lam unit')) unit') .unit :=
  .allE (x := 2) (b := av) (T := .unit) (a := bv)
    (.allI (S := .unit) rfl rfl (fun _ hs => absurd hs (by simp)) (.unitI (.cons .nil)))
    (entailsLt_bound rfl)

/-- `[l]I` on a consumed context: `λx.x : ['a](1 ⊸ 1)`. -/
theorem d_boxIctx : DerivesWf D1 [] (.val (.lam (.var 0))) (.box av (.lolli .unit .unit)) :=
  .boxIctx (.lolliI rfl (.var (.here .nil))) (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) .nil)

/-- `[l]I` at `1`: `() : ['a]1`. -/
theorem d_box1 : DerivesWf D1 [] unit' (.box av .unit) :=
  .boxIctx (.unitI .nil) (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) .nil)

/-- `[l]I` at an outer borrow's lifetime, with the borrow live in the context:
`['b ⊏ 'a, 'a ⊏ ⊤]; x : Imm 'a 1 ⊢ x : ['b](Imm 'a 1)`, from
`Δ ⊢ Imm 'a 1 ⊐ 'b`, which holds because `Δ ⊨ 'b ⊏ 'a` (§12.24). -/
theorem d_outerBorrow :
    DerivesWf D3 [⟨.imm av .unit, true⟩] (.var 0) (.box bv (.imm av .unit)) :=
  .boxIctx (.var (.here .nil)) ⟨LifeCtx.defines_of_wf rfl, by
    intro s hs _
    simp only [List.mem_singleton] at hs
    subst hs
    exact .imm (entailsLt_bound rfl)⟩

/-- `[l]I` at `⊤`, on the empty context: `λx.x : [⊤](1 ⊸ 1)`.  `Δ ⊨ ⊤` holds at
every `Δ`, and the context premise asks nothing of a context with no live slot
(§C.25). -/
theorem d_boxTop :
    DerivesWf LifeCtx.empty [] (.val (.lam (.var 0))) (.box .top (.lolli .unit .unit)) :=
  .boxIctx (.lolliI rfl (.var (.here .nil))) (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) .nil)

/-- `[l]E`: `() : 1` from `() : ['a]1`. -/
theorem d_boxE : DerivesWf D1 [] unit' .unit := .boxE d_box1

/-- `⊑Imm` (§12.4's conclusion at `@a`), at `'a ⊑ 'a`. -/
theorem d_immSub :
    DerivesWf D1 [⟨.imm av .unit, true⟩] (.var 0) (.imm av .unit) :=
  .immSub (.var (.here .nil)) (entailsLe_refl rfl)

/-- `⊑Mut`, at `'a ⊑ 'a`. -/
theorem d_mutSub :
    DerivesWf D1 [⟨.mut av .unit, true⟩] (.var 0) (.mut av .unit) :=
  .mutSub (.var (.here .nil)) (entailsLe_refl rfl)

/-- `alloc : 1 ⊸ Ref 1`. -/
theorem d_alloc : DerivesWf D1 [] (.val (.prim .alloc)) (.lolli .unit (.ref .unit)) :=
  .allocAx .nil

/-- `free : Ref 1 ⊸ 1`. -/
theorem d_free : DerivesWf D1 [] (.val (.prim .free)) (.lolli (.ref .unit) .unit) :=
  .freeAx .nil

/-! ## 2. The axiom table of `[TR]` p. 3

Each line at `T₁ = T₂ = 1` and `@a = 'a`, in `['a ⊏ ⊤]`.  The `∀` binder of the
`withbor` and `withload` lines is the variable `1`, fresh for that context, and
`⊓Δ` is `'a ⊓ ⊤`. -/

theorem d_swap : DerivesWf D1 [] swap (axSwapTy .unit .unit) :=
  .swapAx .nil

theorem d_copy : DerivesWf D1 [] copy (axCopyTy av .unit) :=
  .copyAx .nil

theorem d_forgetImm : DerivesWf D1 [] forget (axForgetImmTy av .unit) :=
  .forgetImmAx .nil

theorem d_forgetMut : DerivesWf D1 [] forget (axForgetMutTy av .unit) :=
  .forgetMutAx .nil

theorem d_forgetUnk : DerivesWf D1 [] forget axForgetUnkTy :=
  .forgetUnkAx .nil

theorem d_withbor1 :
    DerivesWf D1 [] withbor (axWithbor1Ty 1 D1.meetOfDom .unit .unit) :=
  .withbor1Ax .nil 1 rfl rfl

/-- The second line, with its side condition `Δ ⊢ 1 ⊐ ⊤`. -/
theorem d_withbor2 :
    DerivesWf D1 [] withbor (axWithbor2Ty 1 D1.meetOfDom .unit .unit) :=
  .withbor2Ax .nil 1 rfl ⟨.top, LifeCtx.defines_of_wf rfl, .unit⟩ rfl

theorem d_withbor3 :
    DerivesWf D1 [] withbor (axWithbor3Ty av 1 D1.meetOfDom .unit .unit) :=
  .withbor3Ax .nil 1 rfl rfl

theorem d_withload :
    DerivesWf D1 [] withload (axWithloadTy av 1 D1.meetOfDom .unit .unit) :=
  .withloadAx .nil 1 rfl rfl

theorem d_withswap : DerivesWf D1 [] withswap (axWithswapTy av .unit .unit) :=
  .withswapAx .nil

/-! ## Facts about the statics

`LifeCtx.freshVar` allocates a binder the axiom table's `∀` accepts; `Imm̲ 'b` is
idempotent; `Ty.wfB` is sound for `Δ ⊢ T`. -/

theorem _root_.BoCa.Lifetime.freshOfL_not_mem : ∀ (t : List (LifeVar × Life)) (y : LifeVar),
    freshOfL t ≤ y → assocFind y t = none := by
  intro t
  induction t with
  | nil => intro y _; rfl
  | cons e t ih =>
    obtain ⟨x, u⟩ := e
    intro y hy
    simp only [freshOfL] at hy
    obtain ⟨hx1, hx2⟩ := Nat.max_le.mp hy
    have hx : ¬ (x = y) := fun he => Nat.not_succ_le_self x (he ▸ hx1)
    simp only [assocFind, if_neg hx]
    exact ih y hx2

/-- `LifeCtx.freshVar` is outside `dom(Δ)`: the freshness premise of `∀I` and of the
`withbor`/`withload` lines. -/
theorem _root_.BoCa.Lifetime.LifeCtx.freshVar_fresh (Δ : LifeCtx) : Δ.find? Δ.freshVar = none :=
  freshOfL_not_mem Δ.entries Δ.freshVar (Nat.le_refl _)

/-- `Imm̲ 'b` is idempotent: its image is fixed by every `Imm̲ 'c`. -/
theorem _root_.BoCa.Ty.immReborrow_idem (b c : Life) (T : Ty) :
    (T.immReborrow c).immReborrow b = T.immReborrow c := by
  induction T <;> simp [Ty.immReborrow, *]

/-- `Ty.wfB` is sound for `Δ ⊢ T` (`WfTy`). -/
theorem _root_.BoCa.wfTy_of_wfB : ∀ {T : Ty} {Δ : LifeCtx}, T.wfB Δ = true → WfTy Δ T := by
  intro T
  induction T with
  | unit => intro _ _; exact .unit
  | unk => intro Δ h; simp [Ty.wfB] at h
  | ref T ih => intro Δ h; exact .ref (ih h)
  | sum T₁ T₂ ih₁ ih₂ =>
      intro Δ h; simp only [Ty.wfB, Bool.and_eq_true] at h; exact .sum (ih₁ h.1) (ih₂ h.2)
  | tensor T₁ T₂ ih₁ ih₂ =>
      intro Δ h; simp only [Ty.wfB, Bool.and_eq_true] at h; exact .tensor (ih₁ h.1) (ih₂ h.2)
  | lolli T₁ T₂ ih₁ ih₂ =>
      intro Δ h; simp only [Ty.wfB, Bool.and_eq_true] at h; exact .lolli (ih₁ h.1) (ih₂ h.2)
  | fn T₁ T₂ ih₁ ih₂ =>
      intro Δ h; simp only [Ty.wfB, Bool.and_eq_true] at h; exact .fn (ih₁ h.1) (ih₂ h.2)
  | box a T ih =>
      intro Δ h; simp only [Ty.wfB, Bool.and_eq_true] at h
      exact .box (ih h.2) (LifeCtx.defines_of_wf h.1)
  | imm a T ih =>
      intro Δ h; simp only [Ty.wfB, Bool.and_eq_true] at h
      exact .imm (ih h.2) (LifeCtx.defines_of_wf h.1)
  | «mut» a T ih =>
      intro Δ h; simp only [Ty.wfB, Bool.and_eq_true] at h
      exact .mut (ih h.2) (LifeCtx.defines_of_wf h.1)
  | all y b T ih =>
      intro Δ h; simp only [Ty.wfB, Bool.and_eq_true] at h
      exact .all (LifeCtx.defines_of_wf h.1.2) (ih h.2)

end BoCa.Programs

end

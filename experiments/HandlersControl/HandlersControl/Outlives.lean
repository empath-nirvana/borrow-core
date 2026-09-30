import HandlersControl.Capture

/-!
# The closure outlives rule (T2, #173) at BoLo: the box

`[TR]` p. 2 has no outlives rule at `⊸` (`lolli_not_outlives`), so a closure alone never crosses a
borrow scope.  The capture-bounded closure T2 asks for is already a type: `[@c](T₁ ⊸ T₂)`.
* Introduction is `[]I` (row 2.13): every live slot the closure captures must outlive `@c`.
* It outlives `@a` exactly when `@c ⊐ @a` (row 2.35; `box_lolli_outlives_iff`).
* Its semantics is `[TR]` 6.62/6.60 at the box, already in the Fundamental Property.

`crossProg` is an owned continuation that captures a borrow and is resumed after an inner scope ends:

    withbor c₁ (Λ'a. λy.                      -- y : Imm 'a 1
      withbor c₂ (Λ'c. λz. forget z;          -- 'c ⊏ 'a
        let k = □(λu. u; forget y);           -- k : ['c](1 ⊸ 1), captures y (y outlives 'c)
        let (c₃, k′) = withbor c₃ (Λ'x. λw.   -- 'x ⊏ 'c
                          forget w; □k);      -- k leaves 'x: ['c](…) outlives 'x
        free c₃; k′ (); □()); …)

Typed (`d_crossProg`), safe (`crossProg_runs`), run (`crossProg_eval`).  Without the box the inner
callback's result `1 ⊸ 1` would need `Δ ⊢ 1 ⊸ 1 ⊐ 'x`, which no rule gives.

`[about ours]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace HandlersControl
open BoCa BoCa.Lifetime BoCa.Programs HandlersAsBorrows.Xi

/-- **The capture-bounded closure outlives `@a` iff its bound does.** -/
theorem box_lolli_outlives_iff (Δ : LifeCtx) (a c : Life) (T₁ T₂ : Ty) :
    OutlivesRules Δ a (.box c (.lolli T₁ T₂)) ↔ Δ.EntailsLt a c :=
  ⟨fun h => by cases h with | box h => exact h, fun h => .box h⟩

/-- The lifetime contexts: `'a = 0 ⊏ ⊤`, `'c = 1 ⊏ 'a ⊓ ⊤`, `'x = 2 ⊏ 'c ⊓ 'a ⊓ ⊤`. -/
abbrev Dc : LifeCtx := D1.extend 1 D1.meetOfDom
abbrev Dx : LifeCtx := Dc.extend 2 Dc.meetOfDom

theorem hca : Dc.EntailsLt (.var 1) (.var 0) :=
  entailsLt_of_bound rfl (fun _ _ h => interp_meet_left h)

theorem hxc : Dx.EntailsLt (.var 2) (.var 1) :=
  entailsLt_of_bound rfl (fun _ _ h => interp_meet_left h)

/-- The continuation's type, bounded at `'c`. -/
abbrev KT : Ty := .box (.var 1) (.lolli .unit .unit)

def innerCb : Expr := lam (lam (.seq (.app forget (.var 0)) (.var 2)))

def bodyC : Expr :=
  .seq (.app forget (.var 0))
    (elet (lam (.seq (.var 0) (.app forget (.var 3))))
      (.letpair (app2 withbor (.app alloc' unit') innerCb)
        (.seq (.app free' (.var 1)) (.seq (.app (.var 0) unit') unit'))))

def midCb : Expr := lam (lam bodyC)

def bodyA : Expr :=
  .letpair (app2 withbor (.app alloc' unit') midCb) (.seq (.var 0) (.seq (.app free' (.var 1)) unit'))

def crossProg : Expr :=
  .letpair (app2 withbor (.app alloc' unit') (lam (lam bodyA))) (.seq (.var 0) (.app free' (.var 1)))

abbrev Ia : Ty := .imm (.var 0) .unit
abbrev Ic : Ty := .imm (.var 1) .unit
abbrev Ix : Ty := .imm (.var 2) .unit

theorem d_innerCb :
    DerivesWf Dc [⟨KT, true⟩, ⟨Ic, false⟩, ⟨.unit, false⟩, ⟨Ia, false⟩, ⟨.unit, false⟩]
      innerCb (.all 2 Dc.meetOfDom (.lolli Ix (.box (.var 2) KT))) := by
  refine .allI (S := .unit) rfl rfl
    (noBinds_cons rfl (Ctx.Dead.noBinds (by dead) 2)) (.lolliI rfl ?_)
  -- ctx: w, _, k, z, _, y, _
  refine .unitE (.left (.dead (.right (.dead (.dead (.dead (.dead .nil)))))))
    (.lolliE (.left (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))
      (.var (.here (by dead))) (.forgetImmAx (by dead)))
    (.boxIctx (.var (.there (.there (.here (by dead))))) ?_)
  exact Ctx.Outlives.consD (Ctx.Outlives.consD (Ctx.Outlives.consL (.box hxc)
    (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (by dead))))

theorem d_bodyC :
    DerivesWf Dc [⟨Ic, true⟩, ⟨.unit, false⟩, ⟨Ia, true⟩, ⟨.unit, false⟩] bodyC (.box (.var 1) .unit) := by
  refine .unitE (.left (.dead (.right (.dead .nil))))
    (.lolliE (.left (.dead (.dead (.dead .nil)))) (.var (.here (by dead))) (.forgetImmAx (by dead))) ?_
  -- ctx: z(d), _, y, _
  refine .lolliE (T₁ := KT) (.dead (.dead (.left (.dead .nil))))
    (.boxIctx (.lolliI rfl
        (.unitE (.left (.dead (.dead (.right (.dead .nil))))) (.var (.here (by dead)))
          (.lolliE (.dead (.dead (.dead (.left (.dead .nil)))))
            (.var (.there (.there (.there (.here (by dead)))))) (.forgetImmAx (by dead)))))
      (Ctx.Outlives.consD (Ctx.Outlives.consD (Ctx.Outlives.consL (.imm hca)
        (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (by dead))))))
    (.lolliI rfl ?_)
  -- ctx: k, z, _, y, _
  refine .tensorE (T₁ := .ref .unit) (T₂ := KT) (.left (.dead (.dead (.dead (.dead .nil))))) rfl
    (.lolliE (.left (.dead (.dead (.dead (.dead .nil))))) d_innerCb
      (.lolliE (.dead (.dead (.dead (.dead (.dead .nil)))))
        (.lolliE (.dead (.dead (.dead (.dead (.dead .nil))))) (.unitI (by dead)) (.allocAx (by dead)))
        (.withbor1Ax (by dead) 2 rfl rfl))) ?_
  -- ctx: k', c3, k, z, _, y, _
  exact .unitE (.right (.left (.dead (.dead (.dead (.dead (.dead .nil)))))))
    (.lolliE (.dead (.left (.dead (.dead (.dead (.dead (.dead .nil)))))))
      (.var (.there (.here (by dead)))) (.freeAx (by dead)))
    (.unitE (.left (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))
      (.lolliE (.right (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))
        (.unitI (by dead)) (.boxE (.var (.here (by dead)))))
      (.boxIctx (.unitI (by dead)) (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (by dead))))

theorem d_bodyA : DerivesWf D1 [⟨Ia, true⟩, ⟨.unit, false⟩] bodyA (.box (.var 0) .unit) := by
  refine .tensorE (T₁ := .ref .unit) (T₂ := .unit) (.left (.dead .nil)) rfl
    (.lolliE (.left (.dead .nil))
      (.allI (S := .unit) rfl rfl (noBinds_cons rfl (Ctx.Dead.noBinds (by dead) 1))
        (.lolliI rfl d_bodyC))
      (.lolliE (.dead (.dead .nil))
        (.lolliE (.dead (.dead .nil)) (.unitI (by dead)) (.allocAx (by dead)))
        (.withbor1Ax (by dead) 1 rfl rfl))) ?_
  -- ctx: u2, c2, y, _
  exact .unitE (.left (.right (.dead (.dead .nil)))) (.var (.here (by dead)))
    (.unitE (.dead (.left (.dead (.dead .nil))))
      (.lolliE (.dead (.left (.dead (.dead .nil)))) (.var (.there (.here (by dead))))
        (.freeAx (by dead)))
      (.boxIctx (.unitI (by dead)) (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (by dead))))

/-- **Typed.** -/
theorem d_crossProg : DerivesWf LifeCtx.empty [] crossProg .unit := by
  refine .tensorE (T₁ := .ref .unit) (T₂ := .unit) .nil rfl
    (.lolliE .nil (.allI (S := .unit) rfl rfl (Ctx.Dead.noBinds .nil 0) (.lolliI rfl d_bodyA))
      (.lolliE .nil (.lolliE .nil (.unitI .nil) (.allocAx .nil)) (.withbor1Ax .nil 0 rfl rfl))) ?_
  exact .unitE (.left (.right .nil)) (.var (.here (by dead)))
    (.lolliE (.dead (.left .nil)) (.var (.there (.here .nil))) (.freeAx (by dead)))

/-- **Safe**, by the Fundamental Property. -/
theorem crossProg_runs : BoLo.Steps Adequacy.emptyMem crossProg Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_crossProg

theorem crossProg_eval : unitNoLeak (eval crossProg) = true := by decide

end HandlersControl

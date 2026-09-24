import Examples.CallBorrowed
/-!
# `FnMut`: state-passing code through a mutable borrow  `[spec §2]`

    let f = λp. let (e, u) = p; u; (case e {x ⇒ inj₂ x, y ⇒ inj₁ y}, ());
    let (f₁, f₂) = copy f;
    let (c, v) = withbor (alloc (inj₁ ())) (Λ. λm.
                   let (m₁, u₁) = withswap m (λe. f₁ (e, ())); u₁;
                   let (m₂, u₂) = withswap m₁ (λe. f₂ (e, ())); u₂; forget m₂; ());
    v; case (free c) {x ⇒ x, y ⇒ y}

`f : fn (1 ⊕ 1 ⊗ 1) (1 ⊕ 1 ⊗ 1)` is closed code that takes its environment by value and returns
it updated.  `withswap` hands the `Mut` borrow's payload to such code and stores what it returns,
so each call runs the code on the environment in place — `FnMut`'s behaviour — with the code
held beside the borrow, not inside it.
-/

noncomputable section

namespace BoCa.Programs
open BoCa BoCa.Lifetime

/-- `fn (1 ⊕ 1 ⊗ 1) (1 ⊕ 1 ⊗ 1)`. -/
abbrev MF : Ty := .fn (.tensor B .unit) (.tensor B .unit)

/-- `λp. let (e, u) = p; u; (case e {x ⇒ inj₂ x, y ⇒ inj₁ y}, ())`: flip the environment. -/
def flipCode : Expr :=
  lam (.letpair (.var 0) (.seq (.var 0)
    (.pair (.case (.var 1) (.inj₂ (.var 0)) (.inj₁ (.var 0))) unit')))

def mutBody : Expr :=
  .letpair (app2 withswap (.var 0) (lam (.app (.var 4) (.pair (.var 0) unit'))))
    (.seq (.var 0) (.letpair (app2 withswap (.var 1) (lam (.app (.var 5) (.pair (.var 0) unit'))))
      (.seq (.var 0) (.seq (.app forget (.var 1)) unit'))))

def mutCaller : Expr := lam (lam mutBody)

def fnMut : Expr :=
  elet flipCode
    (.letpair (.app copy (.var 0))
      (.letpair (app2 withbor (.app alloc' (.inj₁ unit')) mutCaller)
        (.seq (.var 0) (dropB (.app free' (.var 1))))))

theorem d_flipCode : DerivesWf LifeCtx.empty [] flipCode MF :=
  .fnI .nil (by rfl)
    (.tensorE (T₁ := B) (T₂ := .unit) (.left .nil) (by rfl) (.var (.here .nil))
      (.unitE (.left (.right (.dead .nil))) (.var (.here (.cons (.cons .nil))))
        (.tensorI (.dead (.left (.dead .nil)))
          (.sumE (.dead (.left (.dead .nil))) (by rfl) (.var (.there (.here (.cons .nil))))
            (.sumI₂ (.var (.here (.cons (.cons (.cons .nil)))))) (.sumI₁ (.var (.here (.cons (.cons (.cons .nil)))))))
          (.unitI (.cons (.cons (.cons .nil)))))))

theorem d_mutBody :
    DerivesWf D1 [⟨.mut (.var 0) B, true⟩, ⟨.unit, false⟩, ⟨MF, true⟩, ⟨MF, true⟩, ⟨MF, false⟩]
      mutBody (.box (.var 0) .unit) :=
  .tensorE (T₁ := .mut (.var 0) B) (T₂ := .unit) (.left (.dead (.right (.left (.dead .nil))))) (by rfl)
    (.lolliE (.right (.dead (.dead (.left (.dead .nil)))))
      (.lolliI (by rfl)
        (.fnE (.left (.dead (.dead (.dead (.right (.dead .nil))))))
          (.tensorI (.left (.dead (.dead (.dead (.dead (.dead .nil)))))) (.var (.here (.cons (.cons (.cons (.cons (.cons .nil))))))) (.unitI (.cons (.cons (.cons (.cons (.cons (.cons .nil))))))))
          (.var (.there (.there (.there (.there (.here (.cons .nil)))))))))
      (.lolliE (.left (.dead (.dead (.dead (.dead .nil))))) (.var (.here (.cons (.cons (.cons (.cons .nil)))))) (.withswapAx (.cons (.cons (.cons (.cons (.cons .nil))))))))
    (.unitE (.left (.right (.dead (.dead (.right (.dead (.dead .nil))))))) (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons .nil))))))))
      (.tensorE (T₁ := .mut (.var 0) B) (T₂ := .unit) (.dead (.left (.dead (.dead (.left (.dead (.dead .nil))))))) (by rfl)
        (.lolliE (.dead (.right (.dead (.dead (.left (.dead (.dead .nil)))))))
          (.lolliI (by rfl)
            (.fnE (.left (.dead (.dead (.dead (.dead (.right (.dead (.dead .nil))))))))
              (.tensorI (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))) (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons .nil))))))))) (.unitI (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons .nil))))))))))
              (.var (.there (.there (.there (.there (.there (.here (.cons (.cons .nil)))))))))))
          (.lolliE (.dead (.left (.dead (.dead (.dead (.dead (.dead .nil))))))) (.var (.there (.here (.cons (.cons (.cons (.cons (.cons .nil)))))))) (.withswapAx (.cons (.cons (.cons (.cons (.cons (.cons (.cons .nil))))))))))
        (.unitE (.left (.right (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))))) (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons .nil))))))))))
          (.unitE (.dead (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil)))))))))
            (.lolliE (.dead (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead .nil))))))))) (.var (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons .nil)))))))))) (.forgetMutAx (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons .nil)))))))))))
            (.boxIctx (.unitI (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons .nil))))))))))
              (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons .nil)))))))))))))))

theorem d_mutCaller :
    DerivesWf LifeCtx.empty [⟨MF, true⟩, ⟨MF, true⟩, ⟨MF, false⟩] mutCaller
      (.all 0 LifeCtx.empty.meetOfDom (.lolli (.mut (.var 0) B) (.box (.var 0) .unit))) :=
  .allI (S := .unit) rfl rfl (by decide) (.lolliI rfl d_mutBody)

theorem d_fnMut : DerivesWf LifeCtx.empty [] fnMut .unit :=
  .lolliE .nil d_flipCode
    (.lolliI (by rfl)
      (.tensorE (T₁ := MF) (T₂ := MF) (.left .nil) (by rfl)
        (.lolliE (.left .nil) (.var (.here .nil)) (.copyFnAx (.cons .nil)))
        (.tensorE (T₁ := .ref B) (T₂ := .unit) (.left (.left (.dead .nil))) (by rfl)
          (.lolliE (.left (.left (.dead .nil))) d_mutCaller
            (.lolliE (.dead (.dead (.dead .nil)))
              (.lolliE (.dead (.dead (.dead .nil))) (.sumI₁ (.unitI (.cons (.cons (.cons .nil))))) (.allocAx (.cons (.cons (.cons .nil)))))
              (.withbor2Ax (.cons (.cons (.cons .nil))) 0 rfl ⟨.top, LifeCtx.defines_of_wf rfl, .sum .unit .unit⟩ (by rfl))))
          (.unitE (.left (.right (.dead (.dead (.dead .nil))))) (.var (.here (.cons (.cons (.cons (.cons .nil))))))
            (.sumE (.dead (.left (.dead (.dead (.dead .nil))))) (by rfl)
              (.lolliE (.dead (.left (.dead (.dead (.dead .nil))))) (.var (.there (.here (.cons (.cons (.cons .nil)))))) (.freeAx (.cons (.cons (.cons (.cons (.cons .nil)))))))
              (.var (.here (.cons (.cons (.cons (.cons (.cons .nil))))))) (.var (.here (.cons (.cons (.cons (.cons (.cons .nil))))))))))))

/-- The code runs twice on the borrowed environment, and the program leaves no cell. -/
theorem fnMut_runs : BoLo.Steps Adequacy.emptyMem fnMut Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_fnMut

theorem fnMut_eval : unitNoLeak (eval fnMut) = true := by decide

/-- Without the final `case`, the program returns the environment after the two calls:
`inj₁ ()` flipped twice. -/
theorem fnMut_stored :
    (match eval (elet flipCode (.letpair (.app copy (.var 0))
        (.letpair (app2 withbor (.app alloc' (.inj₁ unit')) mutCaller)
          (.seq (.var 0) (.app free' (.var 1)))))) with
      | .value ⟨.inj₁ .unit, _⟩ false => true
      | _ => false) = true := by decide

end BoCa.Programs

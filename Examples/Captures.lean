import Examples.CallBorrowed
/-!
# A capturing closure, called through an immutable borrow  `[spec §2]`

    let (r, u) = withbor (alloc ()) (Λ. λx.                     -- x : Imm 'a 1
      let (c, w) = withbor (alloc (x, code)) (Λ. λy.
                     withload y (Λ. λq.                         -- q : Imm 'a 1 ⊗ fn (Imm 'a 1 ⊗ 1) 1
                       let (x₁, f) = q; let (x₂, x₃) = copy x₁; let (f₁, f₂) = copy f;
                       f₁ (x₂, ()); f₂ (x₃, ()); ()));
      w; let (x₄, g) = free c; forget x₄; forget g; ());
    u; free r

The closure is the pair `(x, code)`: its environment `x : Imm 'a 1`, and closed code
`code = λp. let (x′, u) = p; forget x′; u : fn (Imm 'a 1 ⊗ 1) 1`.  Loading it through a borrow
gives `Imm̲ 'c (Imm 'a 1 ⊗ fn …) = Imm 'a 1 ⊗ fn …`: the environment is already a borrow and the
code is kept, so the loader copies both and calls the code twice on the environment.
-/

noncomputable section

namespace BoCa.Programs
open BoCa BoCa.Lifetime

/-- `Imm 'a 1`, the captured borrow. -/
abbrev CA : Ty := .imm (.var 0) .unit
/-- The code's type, `fn (Imm 'a 1 ⊗ 1) 1`. -/
abbrev CF : Ty := .fn (.tensor CA .unit) .unit
/-- The closure, environment and code. -/
abbrev CP : Ty := .tensor CA CF


/-- `λp. let (x′, u) = p; forget x′; u`. -/
def capCode : Expr := lam (.letpair (.var 0) (.seq (.app forget (.var 1)) (.var 0)))

/-- `Λ. λq. let (x₁, f) = q; let (x₂, x₃) = copy x₁; let (f₁, f₂) = copy f;
f₁ (x₂, ()); f₂ (x₃, ()); ()`. -/
def capLoader : Expr :=
  lam (lam (.letpair (.var 0) (.letpair (.app copy (.var 1)) (.letpair (.app copy (.var 2))
    (.seq (.app (.var 1) (.pair (.var 3) unit')) (.seq (.app (.var 0) (.pair (.var 2) unit')) unit'))))))

def capInner : Expr := lam (lam (app2 withload (.var 0) capLoader))

def capOuterBody : Expr :=
  .letpair (app2 withbor (.app alloc' (.pair (.var 0) capCode)) capInner)
    (.seq (.var 0) (.letpair (.app free' (.var 1))
      (.seq (.app forget (.var 1)) (.seq (.app forget (.var 0)) unit'))))

def capOuter : Expr := lam (lam capOuterBody)

def captures : Expr :=
  .letpair (app2 withbor (.app alloc' unit') capOuter) (.seq (.var 0) (.app free' (.var 1)))

theorem d_capCode {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) (hwf : (Ty.tensor CA .unit).scopedB Δ = true) :
    DerivesWf Δ Γ capCode CF :=
  .fnI hΓ hwf
    (.tensorE (T₁ := CA) (T₂ := .unit) (.left hΓ.split) (by simpa using hwf) (.var (.here hΓ))
      (.unitE (.right (.left (.dead hΓ.split)))
        (.lolliE (.dead (.left (.dead hΓ.split))) (.var (.there (.here (.cons hΓ))))
          (.forgetImmAx (.cons (.cons (.cons hΓ)))))
        (.var (.here (.cons (.cons hΓ))))))


theorem d_capLoader {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf D2 Γ capLoader
      (.all 2 D2.meetOfDom
        (.lolli (Ty.immReborrow (.var 2) CP) (.box (.var 2) (.box (.var 1) .unit)))) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds hΓ 2)
    (.lolliI rfl
      (.tensorE (T₁ := CA) (T₂ := CF) (.left (.dead hΓ.split)) (by rfl) (.var (.here (.cons hΓ)))
        (.tensorE (T₁ := CA) (T₂ := CA) (.right (.left (.dead (.dead hΓ.split)))) (by rfl)
          (.lolliE (.dead (.left (.dead (.dead hΓ.split)))) (.var (.there (.here (.cons (.cons hΓ))))) (.copyAx (.cons (.cons (.cons (.cons hΓ))))))
          (.tensorE (T₁ := CF) (T₂ := CF) (.right (.right (.left (.dead (.dead (.dead hΓ.split)))))) (by rfl)
            (.lolliE (.dead (.dead (.left (.dead (.dead (.dead hΓ.split)))))) (.var (.there (.there (.here (.cons (.cons (.cons hΓ))))))) (.copyFnAx (.cons (.cons (.cons (.cons (.cons (.cons hΓ))))))))
            (.unitE (.right (.left (.right (.left (.dead (.dead (.dead (.dead hΓ.split))))))))
              (.fnE (.dead (.right (.dead (.left (.dead (.dead (.dead (.dead hΓ.split))))))))
                (.tensorI (.dead (.dead (.dead (.left (.dead (.dead (.dead (.dead hΓ.split)))))))) (.var (.there (.there (.there (.here (.cons (.cons (.cons (.cons hΓ))))))))) (.unitI (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ))))))))))
                (.var (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons hΓ))))))))))
              (.unitE (.left (.dead (.left (.dead (.dead (.dead (.dead (.dead hΓ.split))))))))
                (.fnE (.right (.dead (.left (.dead (.dead (.dead (.dead (.dead hΓ.split))))))))
                  (.tensorI (.dead (.dead (.left (.dead (.dead (.dead (.dead (.dead hΓ.split)))))))) (.var (.there (.there (.here (.cons (.cons (.cons (.cons (.cons hΓ))))))))) (.unitI (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ))))))))))
                  (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ))))))))))
                (.boxIctx (.boxIctx (.unitI (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ)))))))))
                    (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ))))))))))
                  (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ))))))))))))))))

theorem d_capInner {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf D1 Γ capInner (.all 1 D1.meetOfDom (.lolli (.imm (.var 1) CP) (.box (.var 1) .unit))) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds hΓ 1)
    (.lolliI rfl
      (.lolliE (.right (.dead hΓ.split)) (d_capLoader (.cons (.cons hΓ)))
        (.lolliE (.left (.dead hΓ.split)) (.var (.here (.cons hΓ)))
          (.withloadAx (T₂ := .box (.var 1) .unit) (.cons (.cons hΓ)) 2 rfl (by rfl)))))

theorem d_capOuterBody {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf D1 (⟨CA, true⟩ :: ⟨.unit, false⟩ :: Γ) capOuterBody (.box (.var 0) .unit) :=
  .tensorE (T₁ := .ref CP) (T₂ := .unit) (.left (.dead hΓ.split)) (by rfl)
    (.lolliE (.right (.dead hΓ.split)) (d_capInner (.cons (.cons hΓ)))
      (.lolliE (.left (.dead hΓ.split))
        (.lolliE (.left (.dead hΓ.split))
          (.tensorI (.left (.dead hΓ.split)) (.var (.here (.cons hΓ))) (d_capCode (.cons (.cons hΓ)) (by rfl)))
          (.allocAx (.cons (.cons hΓ))))
        (.withbor1Ax (.cons (.cons hΓ)) 1 rfl (by rfl))))
    (.unitE (.left (.right (.dead (.dead hΓ.split)))) (.var (.here (.cons (.cons (.cons hΓ)))))
      (.tensorE (T₁ := CA) (T₂ := CF) (.dead (.left (.dead (.dead hΓ.split)))) (by rfl)
        (.lolliE (.dead (.left (.dead (.dead hΓ.split)))) (.var (.there (.here (.cons (.cons hΓ))))) (.freeAx (.cons (.cons (.cons (.cons hΓ))))))
        (.unitE (.right (.left (.dead (.dead (.dead (.dead hΓ.split))))))
          (.lolliE (.dead (.left (.dead (.dead (.dead (.dead hΓ.split)))))) (.var (.there (.here (.cons (.cons (.cons (.cons hΓ))))))) (.forgetImmAx (.cons (.cons (.cons (.cons (.cons (.cons hΓ))))))))
          (.unitE (.left (.dead (.dead (.dead (.dead (.dead hΓ.split))))))
            (.lolliE (.left (.dead (.dead (.dead (.dead (.dead hΓ.split)))))) (.var (.here (.cons (.cons (.cons (.cons (.cons hΓ))))))) (.forgetFnAx (.cons (.cons (.cons (.cons (.cons (.cons hΓ))))))))
            (.boxIctx (.unitI (.cons (.cons (.cons (.cons (.cons (.cons hΓ)))))))
              (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (.cons (.cons (.cons (.cons (.cons (.cons hΓ))))))))))))

theorem d_capOuter :
    DerivesWf LifeCtx.empty [] capOuter
      (.all 0 LifeCtx.empty.meetOfDom (.lolli (.imm (.var 0) .unit) (.box (.var 0) .unit))) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds .nil 0) (.lolliI rfl (d_capOuterBody .nil))

theorem d_captures : DerivesWf LifeCtx.empty [] captures .unit :=
  .tensorE .nil rfl
    (.lolliE .nil d_capOuter
      (.lolliE .nil (.lolliE .nil (.unitI .nil) (.allocAx .nil)) (.withbor1Ax .nil 0 rfl rfl)))
    d_useFree

/-- The closure is called twice through the borrow, and the program leaves no cell. -/
theorem captures_runs : BoLo.Steps Adequacy.emptyMem captures Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_captures

theorem captures_eval : unitNoLeak (eval captures) = true := by decide

end BoCa.Programs

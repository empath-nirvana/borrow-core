import Paper.Examples.Programs
/-!
# A borrowed function, called  `[spec §2]`

    let (r, u) = withbor (alloc (λx.x)) (Λ. λb. withload b (Λ. λy.
                   let (y₁, y₂) = copy y; y₁ (); y₂ (); ()));
    u; (free r) ()

`λx.x` over a dead context is promoted to `!(1 ⊸ 1)` (`bangLamI`).  `Imm̲ 'b (!(1 ⊸ 1)) = !(1 ⊸ 1)`,
so the loader receives callable code: it copies it and calls it twice through the borrow, and the
program calls it again after `free`.  Under the baseline the same program with `1 ⊸ 1`
(`Programs.loadClosure`) receives `Unk` and can only `forget` it.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Programs
open BoCa BoCa.Lifetime

/-- The loader `Λ. λy. let (y₁, y₂) = copy y; y₁ (); y₂ (); ()`. -/
def fnLoader : Expr :=
  lam (lam (.letpair (.app copy (.var 0))
    (.seq (.app (.var 1) unit') (.seq (.app (.var 0) unit') unit'))))

def fnBorrower : Expr := lam (lam (app2 withload (.var 0) fnLoader))

def callBorrowed : Expr :=
  .letpair (app2 withbor (.app alloc' (lam (.var 0))) fnBorrower)
    (.seq (.var 0) (.app (.app free' (.var 1)) unit'))

theorem d_fnLoader {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf D1 Γ fnLoader
      (.all 1 D1.meetOfDom
        (.lolli (Ty.immReborrow (.var 1) (.bang (.lolli .unit .unit))) (.box (.var 1) (.box (.var 0) .unit)))) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds hΓ 1)
    (.lolliI rfl
      (.tensorE (T₁ := .bang (.lolli .unit .unit)) (T₂ := .bang (.lolli .unit .unit)) (.left (.dead hΓ.split)) rfl
        (.lolliE (.left (.dead hΓ.split)) (.var (.here (.cons hΓ))) (.copyBangAx (.cons (.cons hΓ))))
        (.unitE (.right (.left (.dead (.dead hΓ.split))))
          (.lolliE (.dead (.right (.dead (.dead hΓ.split)))) (.unitI (.cons (.cons (.cons (.cons hΓ))))) (.bangE (.var (.there (.here (.cons (.cons hΓ)))))))
          (.unitE (.left (.dead (.dead (.dead hΓ.split))))
            (.lolliE (.right (.dead (.dead (.dead hΓ.split)))) (.unitI (.cons (.cons (.cons (.cons hΓ))))) (.bangE (.var (.here (.cons (.cons (.cons hΓ)))))))
            (.boxIctx (.boxIctx (.unitI (.cons (.cons (.cons (.cons hΓ)))))
                (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (.cons (.cons (.cons (.cons hΓ))))))
              (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (.cons (.cons (.cons (.cons hΓ))))))))))

theorem d_fnBorrower :
    DerivesWf LifeCtx.empty [] fnBorrower
      (.all 0 LifeCtx.empty.meetOfDom
        (.lolli (.imm (.var 0) (.bang (.lolli .unit .unit))) (.box (.var 0) .unit))) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds .nil 0)
    (.lolliI rfl
      (.lolliE (.right (.dead .nil)) (d_fnLoader (.cons (.cons .nil)))
        (.lolliE (.left (.dead .nil)) (.var (.here (.cons .nil)))
          (.withloadAx (T₂ := .box (.var 0) .unit) (.cons (.cons .nil)) 1 rfl rfl))))

theorem d_callBorrowed : DerivesWf LifeCtx.empty [] callBorrowed .unit :=
  .tensorE .nil rfl
    (.lolliE .nil d_fnBorrower
      (.lolliE .nil (.lolliE .nil (.bangLamI (Ctx.Dead.persistent .nil) rfl (.var (.here .nil))) (.allocAx .nil))
        (.withbor1Ax .nil 0 rfl rfl)))
    (.unitE (.left (.right .nil)) (.var (.here (.cons .nil)))
      (.lolliE (.dead (.right .nil)) (.unitI (.cons (.cons .nil))) (.bangE (.lolliE (.dead (.left .nil)) (.var (.there (.here .nil))) (.freeAx (.cons (.cons .nil)))))))

/-- A borrowed closure is called, and the program leaves no cell. -/
theorem callBorrowed_runs :
    BoLo.Steps Adequacy.emptyMem callBorrowed Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_callBorrowed


theorem callBorrowed_eval : unitNoLeak (eval callBorrowed) = true := by decide

end BoCa.Programs

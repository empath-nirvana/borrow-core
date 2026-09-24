import Examples.FnMut
/-!
# Closures that own their environment, and closures borrowed mutably  `[spec §2]`

## A closure that owns its environment, called through an immutable borrow

    let code = Λ. λp. let (x, u) = p; forget x; u;          -- !(∀'c ⊏ ⊤. (Imm 'c 1 ⊗ 1) ⊸ 1)
    let (c, w) = withbor (alloc (alloc (), code)) (Λ. λy.
                   withload y (Λ. λq.                       -- q : Imm 'b 1 ⊗ !(∀'c …)
                     let (x, f) = q; let (x₁, x₂) = copy x; let (f₁, f₂) = copy f;
                     f₁ [] (x₁, ()); f₂ [] (x₂, ()); ()));
    w; let (r, g) = free c; free r; forget g

The environment is an owned `Ref 1`.  Loading it through a borrow views it as `Imm 'b 1` at the
load's own lifetime `'b`, so the code is lifetime-polymorphic and closed: `!I` at a `Λ`.
`Imm̲ 'b (!T) = !T` keeps the code, and each call instantiates it at `'b`.
-/

noncomputable section

namespace BoCa.Programs
open BoCa BoCa.Lifetime

/-- The code's type, `!(∀'c ⊏ ⊤. (Imm 'c 1 ⊗ 1) ⊸ 1)`. -/
abbrev OC : Ty := .bang (.all 5 .top (.lolli (.tensor (.imm (.var 5) .unit) .unit) .unit))
/-- The closure, `Ref 1 ⊗ OC`. -/
abbrev OP : Ty := .tensor (.ref .unit) OC
/-- The loader's view of the environment, `Imm 'b 1`. -/
abbrev OA : Ty := .imm (.var 1) .unit


def ownCode : Expr := lam (lam (.letpair (.var 0) (.seq (.app forget (.var 1)) (.var 0))))

def ownLoader : Expr :=
  lam (lam (.letpair (.var 0) (.letpair (.app copy (.var 1)) (.letpair (.app copy (.var 2))
    (.seq (.app (inst (.var 1)) (.pair (.var 3) unit'))
      (.seq (.app (inst (.var 0)) (.pair (.var 2) unit')) unit'))))))

def ownBorrower : Expr := lam (lam (app2 withload (.var 0) ownLoader))

def ownedFn : Expr :=
  .letpair (app2 withbor (.app alloc' (.pair (.app alloc' unit') ownCode)) ownBorrower)
    (.seq (.var 0) (.letpair (.app free' (.var 1)) (.seq (.app free' (.var 1)) (.app forget (.var 0)))))

theorem d_ownCode {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) : DerivesWf LifeCtx.empty Γ ownCode OC :=
  .bangAllI (S := .unit) hΓ.persistent rfl rfl (Ctx.Dead.noBinds hΓ 5)
    (.lolliI (by rfl)
      (.tensorE (T₁ := .imm (.var 5) .unit) (T₂ := .unit) (.left (.dead hΓ.split)) (by rfl) (.var (.here (.cons hΓ)))
        (.unitE (.right (.left (.dead (.dead hΓ.split))))
          (.lolliE (.dead (.left (.dead (.dead hΓ.split)))) (.var (.there (.here (.cons (.cons hΓ))))) (.forgetImmAx (.cons (.cons (.cons (.cons hΓ))))))
          (.var (.here (.cons (.cons (.cons hΓ))))))))

theorem d_ownLoader {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf D1 Γ ownLoader
      (.all 1 D1.meetOfDom (.lolli (Ty.immReborrow (.var 1) OP) (.box (.var 1) (.box (.var 0) .unit)))) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds hΓ 1)
    (.lolliI (by rfl)
      (.tensorE (T₁ := OA) (T₂ := OC) (.left (.dead hΓ.split)) (by rfl) (.var (.here (.cons hΓ)))
        (.tensorE (T₁ := OA) (T₂ := OA) (.right (.left (.dead (.dead hΓ.split)))) (by rfl)
          (.lolliE (.dead (.left (.dead (.dead hΓ.split)))) (.var (.there (.here (.cons (.cons hΓ))))) (.copyAx (.cons (.cons (.cons (.cons hΓ))))))
          (.tensorE (T₁ := OC) (T₂ := OC) (.right (.right (.left (.dead (.dead (.dead hΓ.split)))))) (by rfl)
            (.lolliE (.dead (.dead (.left (.dead (.dead (.dead hΓ.split)))))) (.var (.there (.there (.here (.cons (.cons (.cons hΓ))))))) (.copyBangAx (.cons (.cons (.cons (.cons (.cons (.cons hΓ))))))))
            (.unitE (.right (.left (.right (.left (.dead (.dead (.dead (.dead hΓ.split))))))))
              (.lolliE (T₁ := .tensor OA .unit) (T₂ := .unit) (.dead (.right (.dead (.left (.dead (.dead (.dead (.dead hΓ.split))))))))
                (.tensorI (.dead (.dead (.dead (.left (.dead (.dead (.dead (.dead hΓ.split)))))))) (.var (.there (.there (.there (.here (.cons (.cons (.cons (.cons hΓ))))))))) (.unitI (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ))))))))))
                (.allE (.bangE (.var (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons hΓ)))))))))) (entailsLt_of_bound rfl (fun _ n _ => ⟨_, rfl, Nat.zero_le n⟩))))
              (.unitE (.left (.dead (.left (.dead (.dead (.dead (.dead (.dead hΓ.split))))))))
                (.lolliE (T₁ := .tensor OA .unit) (T₂ := .unit) (.right (.dead (.left (.dead (.dead (.dead (.dead (.dead hΓ.split))))))))
                  (.tensorI (.dead (.dead (.left (.dead (.dead (.dead (.dead (.dead hΓ.split)))))))) (.var (.there (.there (.here (.cons (.cons (.cons (.cons (.cons hΓ))))))))) (.unitI (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ))))))))))
                  (.allE (.bangE (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ)))))))))) (entailsLt_of_bound rfl (fun _ n _ => ⟨_, rfl, Nat.zero_le n⟩))))
                (.boxIctx (.boxIctx (.unitI (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ)))))))))
                    (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ))))))))))
                  (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons hΓ))))))))))))))))

theorem d_ownBorrower :
    DerivesWf LifeCtx.empty [] ownBorrower
      (.all 0 LifeCtx.empty.meetOfDom (.lolli (.imm (.var 0) OP) (.box (.var 0) .unit))) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds .nil 0)
    (.lolliI rfl
      (.lolliE (.right (.dead .nil)) (d_ownLoader (.cons (.cons .nil)))
        (.lolliE (.left (.dead .nil)) (.var (.here (.cons .nil)))
          (.withloadAx (T₂ := .box (.var 0) .unit) (.cons (.cons .nil)) 1 rfl (by rfl)))))

theorem d_ownedFn : DerivesWf LifeCtx.empty [] ownedFn .unit :=
  .tensorE (T₁ := .ref OP) (T₂ := .unit) .nil (by rfl)
    (.lolliE .nil d_ownBorrower
      (.lolliE .nil
        (.lolliE .nil (.tensorI .nil (.lolliE .nil (.unitI .nil) (.allocAx .nil)) (d_ownCode .nil))
          (.allocAx .nil))
        (.withbor1Ax .nil 0 rfl (by rfl))))
    (.unitE (.left (.right .nil)) (.var (.here (.cons .nil)))
      (.tensorE (T₁ := .ref .unit) (T₂ := OC) (.dead (.left .nil)) (by rfl)
        (.lolliE (.dead (.left .nil)) (.var (.there (.here .nil))) (.freeAx (.cons (.cons .nil))))
        (.unitE (.right (.left (.dead (.dead .nil))))
          (.lolliE (.dead (.left (.dead (.dead .nil)))) (.var (.there (.here (.cons (.cons .nil))))) (.freeAx (.cons (.cons (.cons (.cons .nil))))))
          (.lolliE (.left (.dead (.dead (.dead .nil)))) (.var (.here (.cons (.cons (.cons .nil))))) (.forgetBangAx (.cons (.cons (.cons (.cons .nil)))))))))

/-- The owned environment is read twice through the borrow, and the program leaves no cell. -/
theorem ownedFn_runs : BoLo.Steps Adequacy.emptyMem ownedFn Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_ownedFn

theorem ownedFn_eval : unitNoLeak (eval ownedFn) = true := by decide

/-! ## A closure borrowed mutably as a whole

    let (c, v) = withbor (alloc (inj₁ (), flip)) (Λ. λm.
                   let (m₁, u₁) = withswap m step; u₁;
                   let (m₂, u₂) = withswap m₁ step; u₂; forget m₂; ());
    v; let (e, g) = free c; case e {x ⇒ x, y ⇒ y}; forget g

    step = λp. let (e, f) = p; let (f₁, f₂) = copy f; let (e′, r) = f₁ (e, ()); ((e′, f₂), r)

The cell holds the whole closure `(env, code)`, `1 ⊕ 1 ⊗ !((1 ⊕ 1 ⊗ 1) ⊸ (1 ⊕ 1 ⊗ 1))`.  A `Mut`
borrow of it needs the payload to outlive the borrow (`withbor`'s second form), which
`Δ ⊢ !T ⊐ @a` supplies; each `withswap` runs the code on the environment and puts the closure
back.
-/

/-- The code's type. -/
abbrev MC : Ty := .bang (.lolli (.tensor B .unit) (.tensor B .unit))
/-- The closure. -/
abbrev MT : Ty := .tensor B MC

def stepFn : Expr :=
  lam (.letpair (.var 0) (.letpair (.app copy (.var 0))
    (.letpair (.app (.var 1) (.pair (.var 3) unit')) (.pair (.pair (.var 1) (.var 2)) (.var 0)))))

def mutBody2 : Expr :=
  .letpair (app2 withswap (.var 0) stepFn)
    (.seq (.var 0) (.letpair (app2 withswap (.var 1) stepFn)
      (.seq (.var 0) (.seq (.app forget (.var 1)) unit'))))

def mutCaller2 : Expr := lam (lam mutBody2)

def mutClosure : Expr :=
  .letpair (app2 withbor (.app alloc' (.pair (.inj₁ unit') flipCode)) mutCaller2)
    (.seq (.var 0) (.letpair (.app free' (.var 1)) (.seq (dropB (.var 1)) (.app forget (.var 0)))))

theorem d_flipBang {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) : DerivesWf LifeCtx.empty Γ flipCode MC :=
  .bangLamI hΓ.persistent (by rfl)
    (.tensorE (T₁ := B) (T₂ := .unit) (.left hΓ.split) (by rfl) (.var (.here hΓ))
      (.unitE (.left (.right (.dead hΓ.split))) (.var (.here (.cons (.cons hΓ))))
        (.tensorI (.dead (.left (.dead hΓ.split)))
          (.sumE (.dead (.left (.dead hΓ.split))) (by rfl) (.var (.there (.here (.cons hΓ))))
            (.sumI₂ (.var (.here (.cons (.cons (.cons hΓ)))))) (.sumI₁ (.var (.here (.cons (.cons (.cons hΓ)))))))
          (.unitI (.cons (.cons (.cons hΓ)))))))

theorem d_step {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ Γ stepFn (.lolli MT (.tensor MT .unit)) :=
  .lolliI (by rfl)
    (.tensorE (T₁ := B) (T₂ := MC) (.left hΓ.split) (by rfl) (.var (.here hΓ))
      (.tensorE (T₁ := MC) (T₂ := MC) (.left (.right (.dead hΓ.split))) (by rfl)
        (.lolliE (.left (.dead (.dead hΓ.split))) (.var (.here (.cons (.cons hΓ)))) (.copyBangAx (.cons (.cons (.cons hΓ)))))
        (.tensorE (T₁ := B) (T₂ := .unit) (.right (.left (.dead (.left (.dead hΓ.split))))) (by rfl)
          (.lolliE (T₁ := .tensor B .unit) (T₂ := .tensor B .unit) (.dead (.right (.dead (.left (.dead hΓ.split)))))
            (.tensorI (.dead (.dead (.dead (.left (.dead hΓ.split))))) (.var (.there (.there (.there (.here (.cons hΓ)))))) (.unitI (.cons (.cons (.cons (.cons (.cons hΓ)))))))
            (.bangE (.var (.there (.here (.cons (.cons (.cons hΓ))))))))
          (.tensorI (.right (.left (.left (.dead (.dead (.dead (.dead hΓ.split)))))))
            (.tensorI (.dead (.left (.right (.dead (.dead (.dead (.dead hΓ.split))))))) (.var (.there (.here (.cons (.cons (.cons (.cons (.cons hΓ)))))))) (.var (.there (.there (.here (.cons (.cons (.cons (.cons hΓ)))))))))
            (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons hΓ))))))))))))

theorem d_mutBody2 :
    DerivesWf D1 [⟨.mut (.var 0) MT, true⟩, ⟨.unit, false⟩] mutBody2 (.box (.var 0) .unit) :=
  .tensorE (T₁ := .mut (.var 0) MT) (T₂ := .unit) (.left (.dead .nil)) (by rfl)
    (.lolliE (.right (.dead .nil)) (d_step (.cons (.cons .nil)))
      (.lolliE (.left (.dead .nil)) (.var (.here (.cons .nil))) (.withswapAx (.cons (.cons .nil)))))
    (.unitE (.left (.right (.dead (.dead .nil)))) (.var (.here (.cons (.cons (.cons .nil)))))
      (.tensorE (T₁ := .mut (.var 0) MT) (T₂ := .unit) (.dead (.left (.dead (.dead .nil)))) (by rfl)
        (.lolliE (.dead (.right (.dead (.dead .nil)))) (d_step (.cons (.cons (.cons (.cons .nil)))))
          (.lolliE (.dead (.left (.dead (.dead .nil)))) (.var (.there (.here (.cons (.cons .nil))))) (.withswapAx (.cons (.cons (.cons (.cons .nil)))))))
        (.unitE (.left (.right (.dead (.dead (.dead (.dead .nil)))))) (.var (.here (.cons (.cons (.cons (.cons (.cons .nil)))))))
          (.unitE (.dead (.left (.dead (.dead (.dead (.dead .nil))))))
            (.lolliE (.dead (.left (.dead (.dead (.dead (.dead .nil)))))) (.var (.there (.here (.cons (.cons (.cons (.cons .nil))))))) (.forgetMutAx (.cons (.cons (.cons (.cons (.cons (.cons .nil))))))))
            (.boxIctx (.unitI (.cons (.cons (.cons (.cons (.cons (.cons .nil)))))))
              (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (.cons (.cons (.cons (.cons (.cons (.cons .nil))))))))))))

theorem d_mutCaller2 :
    DerivesWf LifeCtx.empty [] mutCaller2
      (.all 0 LifeCtx.empty.meetOfDom (.lolli (.mut (.var 0) MT) (.box (.var 0) .unit))) :=
  .allI (S := .unit) rfl rfl (Ctx.Dead.noBinds .nil 0) (.lolliI rfl d_mutBody2)

theorem d_mutClosure : DerivesWf LifeCtx.empty [] mutClosure .unit :=
  .tensorE (T₁ := .ref MT) (T₂ := .unit) .nil (by rfl)
    (.lolliE .nil d_mutCaller2
      (.lolliE .nil
        (.lolliE .nil (.tensorI .nil (.sumI₁ (.unitI .nil)) (d_flipBang .nil)) (.allocAx .nil))
        (.withbor2Ax .nil 0 rfl
          ⟨.top, LifeCtx.defines_of_wf rfl, .tensor (.sum .unit .unit) .bang⟩ (by rfl))))
    (.unitE (.left (.right .nil)) (.var (.here (.cons .nil)))
      (.tensorE (T₁ := B) (T₂ := MC) (.dead (.left .nil)) (by rfl)
        (.lolliE (.dead (.left .nil)) (.var (.there (.here .nil))) (.freeAx (.cons (.cons .nil))))
        (.unitE (.right (.left (.dead (.dead .nil))))
          (.sumE (.dead (.left (.dead (.dead .nil)))) (by rfl) (.var (.there (.here (.cons (.cons .nil)))))
            (.var (.here (.cons (.cons (.cons (.cons .nil)))))) (.var (.here (.cons (.cons (.cons (.cons .nil)))))))
          (.lolliE (.left (.dead (.dead (.dead .nil)))) (.var (.here (.cons (.cons (.cons .nil))))) (.forgetBangAx (.cons (.cons (.cons (.cons .nil)))))))))

/-- The closure is borrowed mutably and run twice, and the program leaves no cell. -/
theorem mutClosure_runs : BoLo.Steps Adequacy.emptyMem mutClosure Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_mutClosure

theorem mutClosure_eval : unitNoLeak (eval mutClosure) = true := by decide

end BoCa.Programs

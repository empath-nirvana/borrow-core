import Frontend.Check.Steps

/-!
# Frontend — Check — constants and derived forms
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check

section
variable {Δ : LifeCtx} {T : List CVTy}

def synConst (_E : Env) (Δ : LifeCtx) (T : List CVTy) (sp : Span) (_c : Const) :
    Except Error (Σ A : CVTy, Res Δ T (.val A)) :=
  err sp "constants are not checked yet"

def shortenIt {A : CVTy} (_E : Env) (T : List CVTy) (sp : Span) (_m : Mode) (_s : CShape)
    (_a : CLife) (_r : Res Δ T (.val A)) : Except Error (Σ B : CVTy, Res Δ T (.val B)) :=
  err sp "`shorten` is not checked yet"

end

end Frontend.Check

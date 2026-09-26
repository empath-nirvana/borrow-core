import Frontend.Check.Rules

/-!
# Frontend — Check — steps shared by the checker's cases

The checker's environment, the messages it reports, and the steps that combine checked
premises through a rule builder once its side conditions are decided: closing binders,
splitting and merging contexts, `boxed`, application to a variable, `<,>`, `case` and `Fun`.
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (CDerives Jdg)

/-- What the checker knows at a point besides `Δ` and the slot types `T`: the declarations in
scope, the name of each slot (a dead binder has none), the lifetime names and a `def`'s type
parameters. -/
structure Env where
  scope : Scope
  vars : List (Option String)
  lenv : List (String × LifeVar)
  tps : List (String × CVTy)

/-- The depth bound for elaborating a type. -/
def tyFuel : Nat := 65536

def Env.tyEnv (E : Env) (Δ : LifeCtx) : TyEnv := ⟨E.scope, Δ, Δ, E.lenv, [], [], E.tps⟩
def Env.elabV (E : Env) (Δ : LifeCtx) (A : VTy) : Except Error CVTy := Frontend.Check.elabV tyFuel (E.tyEnv Δ) A
def Env.elabC (E : Env) (Δ : LifeCtx) (C : CTy) : Except Error CCTy := Frontend.Check.elabC tyFuel (E.tyEnv Δ) C
def Env.elabS (E : Env) (Δ : LifeCtx) (σ : Shape) : Except Error CShape :=
  Frontend.Check.elabS tyFuel (E.tyEnv Δ) σ
def Env.elabL (E : Env) (Δ : LifeCtx) (a : Life) : Except Error CLife := elabLife Δ E.lenv a

/-- Types and lifetimes in messages, with the lifetime names in scope. -/
def Env.ppV (E : Env) (A : CVTy) : String := Frontend.Check.ppV E.lenv 0 0 A
def Env.ppC (E : Env) (C : CCTy) : String := Frontend.Check.ppC E.lenv 0 C
def Env.ppL (E : Env) (a : CLife) : String := ppLifeP E.lenv 1 a

/-! ### Messages -/

def Env.slotName (E : Env) (i : Nat) : String :=
  match E.vars[i]? with
  | some (some x) => s!"`{x}`"
  | _ => "a hidden slot"

/-- The first slot both sides use whose type is not persistent. -/
def firstOverlap : List CVTy → List Bool → List Bool → Option Nat
  | A :: T, a :: as, b :: bs =>
      if a && b && !A.persistent then some 0 else (firstOverlap T as bs).map (· + 1)
  | _, _, _ => none

def Env.slotTy (E : Env) (T : List CVTy) (i : Nat) : String := (T[i]?.map E.ppV).getD "?"

def splitErr (E : Env) (T : List CVTy) (sp : Span) (u₁ u₂ : List Bool) : Error :=
  match firstOverlap T u₁ u₂ with
  | some i => ⟨sp, s!"{E.slotName i} is used twice here, and its type `{E.slotTy T i}` is not " ++
      "persistent"⟩
  | none => ⟨sp, "internal error: context split"⟩

/-- The first slot `a` uses that `b` neither uses nor absorbs. -/
def firstMissing : List Bool → List Bool → List Bool → Option Nat
  | a :: as, b :: bs, c :: cs => if a && !(b || c) then some 0 else (firstMissing as bs cs).map (· + 1)
  | _, _, _ => none

/-- The two parts of a `case` or a `<,>` do not consume the same variables. -/
def mergeErr (E : Env) (sp : Span) (what₁ what₂ intro : String) (u₁ w₁ u₂ w₂ : List Bool) : Error :=
  match firstMissing u₁ u₂ w₂, firstMissing u₂ u₁ w₁ with
  | some i, _ => ⟨sp, s!"{intro}{E.slotName i} is consumed in {what₁} but not in {what₂}"⟩
  | _, some i => ⟨sp, s!"{intro}{E.slotName i} is consumed in {what₂} but not in {what₁}"⟩
  | _, _ => ⟨sp, "internal error: merge"⟩

def unconsumed (E : Env) (sp : Span) (x : String) (A : CVTy) : Error :=
  ⟨sp, s!"`{x}` is not consumed in its scope, and its type `{E.ppV A}` is not persistent " ++
    "(or it cannot be dropped where its scope ends)"⟩

def mismatch (sp : Span) (want got : String) : Error :=
  ⟨sp, s!"type mismatch: expected `{want}`, but this has type `{got}`"⟩

/-! ### Small steps shared by the cases -/

section
variable {Δ : LifeCtx} {T : List CVTy}

def convV (E : Env) (sp : Span) (A : CVTy) : (Σ B : CVTy, Res Δ T (.val B)) → Except Error (Res Δ T (.val A))
  | ⟨B, r⟩ => if h : B = A then pure (h ▸ r) else throw (mismatch sp (E.ppV A) (E.ppV B))

def convC (E : Env) (sp : Span) (C : CCTy) : (Σ D : CCTy, Res Δ T (.comp D)) → Except Error (Res Δ T (.comp C))
  | ⟨D, r⟩ => if h : D = C then pure (h ▸ r) else throw (mismatch sp (E.ppC C) (E.ppC D))

def popL {A : CVTy} {P : List Bool → Prop} (E : Env) (sp : Span) (x : String) (F : Fam (A :: T) P) :
    Except Error (Fam T (fun L => P (true :: L))) :=
  match F.popLive with
  | some F' => pure F'
  | none => throw (unconsumed E sp x A)

def popD {A : CVTy} {P : List Bool → Prop} (sp : Span) (F : Fam (A :: T) P) :
    Except Error (Fam T (fun L => P (false :: L))) :=
  match F.popDead with
  | some F' => pure F'
  | none => throw ⟨sp, "internal error: a dead binder is used"⟩

def withPop {j : Jdg} {e : CExpr} (sp : Span)
    (F : Fam (withT T) (fun L => CDerives Δ (mkCtx (withT T) L) e j)) :
    Except Error (Fam T (fun L => CDerives Δ (BoCa.Fig16.LogRel.Core.withCtx (mkCtx T L)) e j)) :=
  match popWith F with
  | some F' => pure F'
  | none => throw ⟨sp, "internal error: a dead binder is used"⟩

end

/-- The variable bound in slot `i`, if `x` names one. -/
def lookupVar (x : String) : List (Option String) → Option Nat
  | [] => none
  | y :: ys => if y == some x then some 0 else (lookupVar x ys).map (· + 1)

def Env.push (E : Env) (x : Option String) : Env := { E with vars := x :: E.vars }

/-- The environment of a `def`'s body at a use: its own scope, no variables or lifetimes of the
use site, its type parameters bound. -/
def Env.forDef (E : Env) (d : DefInfo) (tps : List (String × CVTy)) : Env :=
  ⟨d.scope, E.vars.map (fun _ => none), [], tps⟩

def inDef (x : String) (sp : Span) (e : Error) : Error :=
  { e with msg := s!"{e.msg}\n  in the body of `{x}`, used at {sp.start.render}" }

def thunkvLam : String :=
  "the body of `thunkv` must erase to a λ: `fun`, `Fun` or `<M, N>`, possibly under " ++
  "`delay_in`/`delay_out`/`stream_in`/`stream_out` or an ascription (syntax-core §6.4); " ++
  "eta-expand it"

def notBang (E : Env) (T : List CVTy) (sp : Span) : Option Nat → Error
  | some i => ⟨sp, s!"`!thunk` promotes only over `!` types, but {E.slotName i}, of type " ++
      s!"`{E.slotTy T i}`, is used inside"⟩
  | none => ⟨sp, thunkvLam⟩

section
variable {Δ : LifeCtx} {T : List CVTy}

/-- `boxed[@a] V`. -/
def boxIt {A : CVTy} (E : Env) (T : List CVTy) (sp : Span) (a : CLife) (r : Res Δ T (.val A)) :
    Except Error (Res Δ T (.val (.box a A))) :=
  if hwf : a.wf Δ = true then
    if hs : usedSat (outlivesB Δ a) T r.F.u = true then pure (rBoxI a hwf r hs)
    else match firstBad (outlivesB Δ a) T r.F.u with
      | some i => throw ⟨sp, s!"`boxed[{E.ppL a}]`: {E.slotName i}, of type `{E.slotTy T i}`, " ++
          s!"is used inside, and it cannot be shown to outlive `{E.ppL a}`"⟩
      | none => throw ⟨sp, "internal error: boxed"⟩
  else throw ⟨sp, s!"`boxed[{E.ppL a}]`: the lifetime is not defined here"⟩

/-- `M x`. -/
def appIt {A : CVTy} {C : CCTy} (E : Env) (T : List CVTy) (sp : Span) (x : Ident)
    (rM : Res Δ T (.comp (.arr A C))) : Except Error (Res Δ T (.comp C)) :=
  match lookupVar x.name E.vars with
  | none => throw ⟨x.span, s!"application `M x` takes a variable, and `{x.name}` is not one " ++
      "in scope; bind it first"⟩
  | some i =>
    if hi : T[i]? = some A then
      if h : overlapOK T rM.F.u (oneL T i) = true then pure (rApp rM i hi h)
      else throw (splitErr E T sp rM.F.u (oneL T i))
    else throw (mismatch x.span (E.ppV A) (E.slotTy T i))

/-- `<M, N>`: both components at the pair's context. -/
def withIt {C D : CCTy} (E : Env) (T : List CVTy) (sp : Span) (r₁ : Res Δ (withT T) (.comp C))
    (r₂ : Res Δ (withT T) (.comp D)) : Except Error (Res Δ T (.comp (.amp C D))) := do
  let F₁ ← withPop sp r₁.F
  let F₂ ← withPop sp r₂.F
  if s₁ : subL F₁.u (orL F₂.u F₂.w) = true then
    if s₂ : subL F₂.u (orL F₁.u F₁.w) = true then pure (rWith r₁.e r₂.e (F₁.merge F₂ s₁ s₂))
    else throw (mergeErr E sp "the first component" "the second" "in this `<M, N>`, "
      F₁.u F₁.w F₂.u F₂.w)
  else throw (mergeErr E sp "the first component" "the second" "in this `<M, N>`, "
    F₁.u F₁.w F₂.u F₂.w)

/-- `case V { inl x -> M | inr y -> N }`: both arms at one context. -/
def caseIt {A B : CVTy} {C : CCTy} (E : Env) (T : List CVTy) (sp : Span) (x y : Ident)
    (rV : Res Δ T (.val (.sum A B))) (r₁ : Res Δ (A :: T) (.comp C))
    (r₂ : Res Δ (B :: T) (.comp C)) : Except Error (Res Δ T (.comp C)) := do
  let F₁ ← popL E x.span x.name r₁.F
  let F₂ ← popL E y.span y.name r₂.F
  if s₁ : subL F₁.u (orL F₂.u F₂.w) = true then
    if s₂ : subL F₂.u (orL F₁.u F₁.w) = true then
      let F := F₁.merge F₂ s₁ s₂
      if h : overlapOK T rV.F.u F.u = true then pure (rSumE rV F h)
      else throw (splitErr E T sp rV.F.u F.u)
    else throw (mergeErr E sp "the `inl` arm" "the `inr` arm" "in this `case`, " F₁.u F₁.w F₂.u F₂.w)
  else throw (mergeErr E sp "the `inl` arm" "the `inr` arm" "in this `case`, " F₁.u F₁.w F₂.u F₂.w)

/-- `Fun 'x < @b. M`. -/
def funIt {v : LifeVar} {bl : CLife} {C : CCTy} (E : Env) (T : List CVTy) (sp : Span)
    (name : String) (rM : Res (Δ.extend v bl) (.unit :: T) (.comp C)) :
    Except Error (Res Δ T (.comp (.all v bl C))) := do
  if hbx : bl.mentions v = false then
    if hΔx : boundsAvoidB Δ v = true then
      let F ← popD sp rM.F
      if hs : usedSat (fun A => !vfreeB v A) T F.u = true then pure (rAllI hbx hΔx F hs)
      else match firstBad (fun A => !vfreeB v A) T F.u with
        | some i => throw ⟨sp, s!"`Fun '{name}`: {E.slotName i}, of type `{E.slotTy T i}`, is " ++
            s!"used inside, and its type mentions `'{name}` ({ppLVar v})"⟩
        | none => throw ⟨sp, "internal error: Fun"⟩
    else throw ⟨sp, s!"`Fun '{name}`: its number {ppLVar v} occurs in a bound of the lifetime context"⟩
  else throw ⟨sp, s!"`Fun '{name}`: its bound mentions its own number {ppLVar v}"⟩

end

end Frontend.Check

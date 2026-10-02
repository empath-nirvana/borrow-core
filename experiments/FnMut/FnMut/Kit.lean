import FnMut.Core.Splits
import FnMut.Types
import Support.Dynamics.Interpreter

/-!
# FnMut — derivation kit

The context splits that copy persistent slots (`partP`), their value-level wrappers, the tactics
`cdeadP`/`csoloP`, and the host-operation and literal rules: copied from `Core/IntPrograms.lean`,
whose import closure is outside the fork.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Splits that copy persistent slots -/

/-- The split of `Γ` at which `e` receives the live slots it mentions and the rest receives the
others, every persistent live slot going to both sides. -/
def partP (e : Expr) : Nat → Ctx VTy → Ctx VTy × Ctx VTy
  | _, [] => ([], [])
  | i, s :: Γ =>
      let p := partP e (i + 1) Γ
      if s.live then
        if s.ty.persistent then (⟨s.ty, true⟩ :: p.1, ⟨s.ty, true⟩ :: p.2)
        else if occ i e then (⟨s.ty, true⟩ :: p.1, ⟨s.ty, false⟩ :: p.2)
        else (⟨s.ty, false⟩ :: p.1, ⟨s.ty, true⟩ :: p.2)
      else (s :: p.1, s :: p.2)

theorem partP_split (e : Expr) :
    ∀ (i : Nat) (Γ : Ctx VTy), Ctx.SplitP Γ (partP e i Γ).1 (partP e i Γ).2
  | _, [] => .nil
  | i, ⟨T, true⟩ :: Γ => by
      cases hp : T.persistent
      · cases h : occ i e
        · simpa [partP, hp, h] using Ctx.SplitP.right (T := T) (partP_split e (i + 1) Γ)
        · simpa [partP, hp, h] using Ctx.SplitP.left (T := T) (partP_split e (i + 1) Γ)
      · simpa [partP, hp] using Ctx.SplitP.dup (T := T) hp (partP_split e (i + 1) Γ)
  | i, ⟨T, false⟩ :: Γ => .dead (partP_split e (i + 1) Γ)

section
variable {Δ : LifeCtx} {Γ : Ctx VTy}

theorem appP {f a : Expr} {A B : VTy} (ha : CDerives Δ (partP a 0 Γ).1 a (.val A))
    (hf : CDerives Δ (partP a 0 Γ).2 f (.val (.lolli A B))) : CDerives Δ Γ (.app f a) (.val B) :=
  .lolliE (partP_split a 0 Γ) ha hf

theorem pairP {e₁ e₂ : Expr} {A B : VTy} (h₁ : CDerives Δ (partP e₁ 0 Γ).1 e₁ (.val A))
    (h₂ : CDerives Δ (partP e₁ 0 Γ).2 e₂ (.val B)) :
    CDerives Δ Γ (.pair e₁ e₂) (.val (.tensor A B)) :=
  .tensorI (partP_split e₁ 0 Γ) h₁ h₂

theorem letP {ep eb : Expr} {A B C : VTy}
    (hp : CDerives Δ (partP ep 0 Γ).1 ep (.val (.tensor A B)))
    (hb : CDerives Δ (⟨B, true⟩ :: ⟨A, true⟩ :: (partP ep 0 Γ).2) eb (.val C)) :
    CDerives Δ Γ (.letpair ep eb) (.val C) :=
  .letpairV (partP_split ep 0 Γ) hp hb

theorem caseP {es e₁ e₂ : Expr} {A B C : VTy}
    (h₀ : CDerives Δ (partP es 0 Γ).1 es (.val (.sum A B)))
    (h₁ : CDerives Δ (⟨A, true⟩ :: (partP es 0 Γ).2) e₁ (.val C))
    (h₂ : CDerives Δ (⟨B, true⟩ :: (partP es 0 Γ).2) e₂ (.val C)) :
    CDerives Δ Γ (.case es e₁ e₂) (.val C) :=
  .caseV (partP_split es 0 Γ) h₀ h₁ h₂

theorem bindP {e b : Expr} {A C : VTy} (he : CDerives Δ (partP e 0 Γ).1 e (.val A))
    (hb : CDerives Δ (⟨A, true⟩ :: (partP e 0 Γ).2) b (.val C)) :
    CDerives Δ Γ (bindE e b) (.val C) :=
  .eletV (partP_split e 0 Γ) he hb

end

/-- `Γ` consumed, up to live persistent slots. -/
syntax "cdeadP" : tactic
macro_rules
  | `(tactic| cdeadP) => `(tactic| first | exact Ctx.DeadP.nil | exact Ctx.Dead.toP (by assumption) | (refine Ctx.DeadP.cons ?_; cdeadP) | (refine Ctx.DeadP.drop (by decide) ?_; cdeadP))

/-- `Γ = x : A`, up to live persistent slots elsewhere. -/
syntax "csoloP" : tactic
macro_rules
  | `(tactic| csoloP) => `(tactic| first | (refine Ctx.SoloP.here ?_; cdeadP) | (refine Ctx.SoloP.there ?_; csoloP) | (refine Ctx.SoloP.skip (by decide) ?_; csoloP))

/-! ### Terms -/

/-- `op a`: a host operation applied. -/
def hop (op : HostOp) (a : Expr) : Expr := .app (.val (.prim (.host op))) a

/-- The literal `i32[n]`. -/
def i32E (n : UInt32) : Expr := .val (Val.i32 n)

theorem d_hop {Δ : LifeCtx} {Γ : Ctx VTy} (op : HostOp) {a : Expr}
    (ha : CDerives Δ (partP a 0 Γ).1 a (.val (hostArg op)))
    (hΓ : Ctx.DeadP (partP a 0 Γ).2) : CDerives Δ Γ (hop op a) (.val (hostRes op)) :=
  appP ha (.bangE (.hostOp op hΓ))

theorem d_i32 {Δ : LifeCtx} {Γ : Ctx VTy} (n : UInt32) (hΓ : Ctx.DeadP Γ) :
    CDerives Δ Γ (i32E n) (.val .i32) :=
  .lit (.i32 n) hΓ

/-- The integer an expression is, if it is a 32-bit literal. -/
def i32Of : Expr → Option UInt32
  | .prim (.lit (.i32 n)) => some n
  | _ => none

/-- A run's 32-bit literal, when it ends with no cell left. -/
def i32NoLeak : Outcome → Option UInt32
  | .value v false => i32Of v.1
  | _ => none

end BoCa.Fig16.LogRel.Core

end

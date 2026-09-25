import Records.Encoding

/-!
# Splitting a context by the variables a subterm uses

`part e i Γ` sends the live slots of `Γ` that `e` mentions (at de Bruijn offset `i`) to the
left and the rest to the right.  The wrappers `appW`, `seqW`, `pairW`, `letW` and `caseW` are
the binary rules of `DerivesWf` at that split, so a derivation of a closed program only has to
name its leaves; `solo` and `dead` close them.
-/

noncomputable section

namespace BoCa.Records
open BoCa BoCa.Lifetime

/-- `occ i e`: de Bruijn variable `i` occurs free in `e`. -/
def occ : Nat → Expr → Bool
  | i, .var j => i == j
  | _, .unit => false
  | i, .pair a b => occ i a || occ i b
  | i, .inj₁ a => occ i a
  | i, .inj₂ a => occ i a
  | i, .lam b => occ (i + 1) b
  | _, .loc _ => false
  | _, .prim _ => false
  | i, .seq a b => occ i a || occ i b
  | i, .letpair a b => occ i a || occ (i + 2) b
  | i, .case a b c => occ i a || occ (i + 1) b || occ (i + 1) c
  | i, .app a b => occ i a || occ i b

/-- The split of `Γ` at which `e` receives the live slots it mentions. -/
def part (e : Expr) : Nat → Ctx Ty → Ctx Ty × Ctx Ty
  | _, [] => ([], [])
  | i, s :: Γ =>
      let p := part e (i + 1) Γ
      if s.live then
        if occ i e then (⟨s.ty, true⟩ :: p.1, ⟨s.ty, false⟩ :: p.2)
        else (⟨s.ty, false⟩ :: p.1, ⟨s.ty, true⟩ :: p.2)
      else (s :: p.1, s :: p.2)

theorem part_split (e : Expr) : ∀ (i : Nat) (Γ : Ctx Ty), Ctx.Split Γ (part e i Γ).1 (part e i Γ).2
  | _, [] => .nil
  | i, ⟨T, true⟩ :: Γ => by
      cases h : occ i e
      · simpa [part, h] using Ctx.Split.right (T := T) (part_split e (i + 1) Γ)
      · simpa [part, h] using Ctx.Split.left (T := T) (part_split e (i + 1) Γ)
  | i, ⟨T, false⟩ :: Γ => .dead (part_split e (i + 1) Γ)

variable {Δ : LifeCtx} {Γ : Ctx Ty}

theorem appW {f a : Expr} {T₁ T₂ : Ty} (ha : DerivesWf Δ (part a 0 Γ).1 a T₁)
    (hf : DerivesWf Δ (part a 0 Γ).2 f (.lolli T₁ T₂)) : DerivesWf Δ Γ (.app f a) T₂ :=
  .lolliE (part_split a 0 Γ) ha hf

theorem seqW {e₁ e₂ : Expr} {T : Ty} (h₁ : DerivesWf Δ (part e₁ 0 Γ).1 e₁ .unit)
    (h₂ : DerivesWf Δ (part e₁ 0 Γ).2 e₂ T) : DerivesWf Δ Γ (.seq e₁ e₂) T :=
  .unitE (part_split e₁ 0 Γ) h₁ h₂

theorem pairW {e₁ e₂ : Expr} {T₁ T₂ : Ty} (h₁ : DerivesWf Δ (part e₁ 0 Γ).1 e₁ T₁)
    (h₂ : DerivesWf Δ (part e₁ 0 Γ).2 e₂ T₂) : DerivesWf Δ Γ (.pair e₁ e₂) (.tensor T₁ T₂) :=
  .tensorI (part_split e₁ 0 Γ) h₁ h₂

theorem letW {ep eb : Expr} {T₁ T₂ T : Ty} (hwf : (Ty.tensor T₁ T₂).scopedB Δ = true)
    (hp : DerivesWf Δ (part ep 0 Γ).1 ep (.tensor T₁ T₂))
    (hb : DerivesWf Δ (⟨T₂, true⟩ :: ⟨T₁, true⟩ :: (part ep 0 Γ).2) eb T) :
    DerivesWf Δ Γ (.letpair ep eb) T :=
  .tensorE (part_split ep 0 Γ) hwf hp hb

theorem caseW {es e₁ e₂ : Expr} {T₁ T₂ T : Ty} (hwf : (Ty.sum T₁ T₂).scopedB Δ = true)
    (h₀ : DerivesWf Δ (part es 0 Γ).1 es (.sum T₁ T₂))
    (h₁ : DerivesWf Δ (⟨T₁, true⟩ :: (part es 0 Γ).2) e₁ T)
    (h₂ : DerivesWf Δ (⟨T₂, true⟩ :: (part es 0 Γ).2) e₂ T) :
    DerivesWf Δ Γ (.case es e₁ e₂) T :=
  .sumE (part_split es 0 Γ) hwf h₀ h₁ h₂

theorem part_dead (e : Expr) : ∀ {i : Nat} {Γ : Ctx Ty}, Ctx.Dead Γ →
    Ctx.Dead (part e i Γ).1 ∧ Ctx.Dead (part e i Γ).2
  | _, [], _ => ⟨.nil, .nil⟩
  | i, _ :: _, .cons h => ⟨.cons (part_dead e (i := i + 1) h).1, .cons (part_dead e (i := i + 1) h).2⟩

/-- `Γ` consumed. -/
syntax "dead" : tactic
macro_rules
  | `(tactic| dead) => `(tactic| first | exact Ctx.Dead.nil | assumption | apply kill_dead | (apply Ctx.Dead.cons; dead) | exact (part_dead _ (by dead)).1 | exact (part_dead _ (by dead)).2)

/-- `Γ = x : T` at the goal's index. -/
syntax "solo" : tactic
macro_rules
  | `(tactic| solo) => `(tactic| first | (apply Ctx.Solo.here; dead) | (apply Ctx.Solo.there; solo))

end BoCa.Records

end

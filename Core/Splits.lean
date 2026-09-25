import Core.Records

/-!
# Core — splitting a context by the variables a subterm uses  `[spec §5]`

`part e i Γ` sends the live slots of `Γ` that `e` mentions (at de Bruijn offset `i`) to the
left and the rest to the right.  The wrappers `appW`, `seqW`, `pairW`, `letW`, `caseW` and
`eletW` are the value-level rules of `CDerives` at that split, so a derivation of a closed
program only names its leaves; the tactics `cdead` and `csolo` close them.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Lifetime (LSub LifeCtx LifeVar)

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
def part (e : Expr) : Nat → Ctx VTy → Ctx VTy × Ctx VTy
  | _, [] => ([], [])
  | i, s :: Γ =>
      let p := part e (i + 1) Γ
      if s.live then
        if occ i e then (⟨s.ty, true⟩ :: p.1, ⟨s.ty, false⟩ :: p.2)
        else (⟨s.ty, false⟩ :: p.1, ⟨s.ty, true⟩ :: p.2)
      else (s :: p.1, s :: p.2)

theorem part_split (e : Expr) :
    ∀ (i : Nat) (Γ : Ctx VTy), Ctx.Split Γ (part e i Γ).1 (part e i Γ).2
  | _, [] => .nil
  | i, ⟨T, true⟩ :: Γ => by
      cases h : occ i e
      · simpa [part, h] using Ctx.Split.right (T := T) (part_split e (i + 1) Γ)
      · simpa [part, h] using Ctx.Split.left (T := T) (part_split e (i + 1) Γ)
  | i, ⟨T, false⟩ :: Γ => .dead (part_split e (i + 1) Γ)

theorem part_dead (e : Expr) : ∀ {i : Nat} {Γ : Ctx VTy}, Ctx.Dead Γ →
    Ctx.Dead (part e i Γ).1 ∧ Ctx.Dead (part e i Γ).2
  | _, [], _ => ⟨.nil, .nil⟩
  | i, _ :: _, .cons h =>
      ⟨.cons (part_dead e (i := i + 1) h).1, .cons (part_dead e (i := i + 1) h).2⟩

variable {Δ : LifeCtx} {Γ : Ctx VTy}

theorem appW {f a : Expr} {A B : VTy} (ha : CDerives Δ (part a 0 Γ).1 a (.val A))
    (hf : CDerives Δ (part a 0 Γ).2 f (.val (.lolli A B))) : CDerives Δ Γ (.app f a) (.val B) :=
  .lolliE (part_split a 0 Γ) ha hf

theorem seqW {e₁ e₂ : Expr} {C : VTy} (h₁ : CDerives Δ (part e₁ 0 Γ).1 e₁ (.val .unit))
    (h₂ : CDerives Δ (part e₁ 0 Γ).2 e₂ (.val C)) : CDerives Δ Γ (.seq e₁ e₂) (.val C) :=
  .seqV (part_split e₁ 0 Γ) h₁ h₂

theorem pairW {e₁ e₂ : Expr} {A B : VTy} (h₁ : CDerives Δ (part e₁ 0 Γ).1 e₁ (.val A))
    (h₂ : CDerives Δ (part e₁ 0 Γ).2 e₂ (.val B)) :
    CDerives Δ Γ (.pair e₁ e₂) (.val (.tensor A B)) :=
  .tensorI (part_split e₁ 0 Γ) h₁ h₂

theorem letW {ep eb : Expr} {A B C : VTy}
    (hp : CDerives Δ (part ep 0 Γ).1 ep (.val (.tensor A B)))
    (hb : CDerives Δ (⟨B, true⟩ :: ⟨A, true⟩ :: (part ep 0 Γ).2) eb (.val C)) :
    CDerives Δ Γ (.letpair ep eb) (.val C) :=
  .letpairV (part_split ep 0 Γ) hp hb

theorem caseW {es e₁ e₂ : Expr} {A B C : VTy}
    (h₀ : CDerives Δ (part es 0 Γ).1 es (.val (.sum A B)))
    (h₁ : CDerives Δ (⟨A, true⟩ :: (part es 0 Γ).2) e₁ (.val C))
    (h₂ : CDerives Δ (⟨B, true⟩ :: (part es 0 Γ).2) e₂ (.val C)) :
    CDerives Δ Γ (.case es e₁ e₂) (.val C) :=
  .caseV (part_split es 0 Γ) h₀ h₁ h₂

theorem eletW {e b : Expr} {A C : VTy} (he : CDerives Δ (part e 0 Γ).1 e (.val A))
    (hb : CDerives Δ (⟨A, true⟩ :: (part e 0 Γ).2) b (.val C)) :
    CDerives Δ Γ (elet e b) (.val C) :=
  .eletV (part_split e 0 Γ) he hb

/-- A callback `thunk Λ. return (λx. body)` at a fresh `'x ⊏ ⊓Δ`. -/
theorem callbackW {body : Expr} {x : LifeVar} {A B : VTy} (hΔ : Δ.Ok) (hx : Δ.find? x = none)
    (hΓ : Ctx.Dead Γ)
    (h : CDerives (Δ.extend x Δ.meetOfDom) (⟨A, true⟩ :: ⟨.unit, false⟩ :: Γ) body (.val B)) :
    CDerives Δ Γ (.val (.lam (.val (.lam body)))) (.val (.all x Δ.meetOfDom (.lolli A B))) :=
  .thunkV rfl (allI_fresh hΔ hx hΓ (.ret (.lamV h)))

/-- `Γ` consumed. -/
syntax "cdead" : tactic
macro_rules
  | `(tactic| cdead) => `(tactic| first | exact Ctx.Dead.nil | assumption | apply kill_dead | (apply Ctx.Dead.cons; cdead) | exact (part_dead _ (by cdead)).1 | exact (part_dead _ (by cdead)).2 | exact Ctx.Dead.toP (by cdead))

/-- `Γ = x : A` at the goal's index. -/
syntax "csolo" : tactic
macro_rules
  | `(tactic| csolo) => `(tactic| first | (apply Ctx.Solo.here; cdead) | (apply Ctx.Solo.there; csolo) | exact Ctx.Solo.toP (by csolo))

/-! ### Side conditions on concrete contexts -/

/-- Types built from `1`, `0`, `⊕`, `⊗`, `!` and `μ`/`X` over them: they hold no borrow and
outlive every lifetime. -/
def dataB : VTy → Bool
  | .unit => true
  | .zero => true
  | .sum A B => dataB A && dataB B
  | .tensor A B => dataB A && dataB B
  | .bang _ => true
  | .tvar _ => true
  | .mu A => dataB A
  | _ => false

theorem outlives_of_dataB {Δ : LifeCtx} {a : Lifetime.Life} :
    ∀ {A : VTy}, dataB A = true → VOutlives Δ a A
  | .unit, _ => .unit
  | .zero, _ => .zero
  | .sum _ _, h => by
      simp only [dataB, Bool.and_eq_true] at h
      exact .sum (outlives_of_dataB h.1) (outlives_of_dataB h.2)
  | .tensor _ _, h => by
      simp only [dataB, Bool.and_eq_true] at h
      exact .tensor (outlives_of_dataB h.1) (outlives_of_dataB h.2)
  | .bang _, _ => .bang
  | .tvar _, _ => .tvar
  | .mu _, h => .mu (outlives_of_dataB (by simpa [dataB] using h))

/-- `[]I`'s premise at a context whose live slots are data. -/
theorem outlives_ctx {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} (ha : Δ.Defines a)
    (h : (Γ.all fun s => !s.live || dataB s.ty) = true) : CtxOutlives Δ Γ a := by
  refine ⟨ha, fun s hs hl => outlives_of_dataB ?_⟩
  have := List.all_eq_true.mp h s hs
  simpa [hl] using this

end BoCa.Fig16.LogRel.Core

end

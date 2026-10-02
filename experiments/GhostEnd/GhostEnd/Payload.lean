import GhostEnd.Table

/-!
# GhostEnd — `'x` inside a borrow's payload (#268, item 1)

`LOk` (`Values.lean`) excludes a frame value whose type has `'x` inside a borrow's payload. This
file shows that such a payload does not reach a stop of the single-lend borrower: the borrow
constants and the table exclude it. Four short lemmas.

**1. Strictness agrees at the fresh lifetime** (`payload_strict`). The model's `Mut` stratum is
strict: a cell `mut(α, v, σ, P̂)` has its witness `σ ∈ Res_α`, every borrow cell of `σ` strictly
longer-lived than `α`. `withbor` (2)'s side condition is non-strict, `Δ ⊢ T₁ ⊒ @b` at an `@b`
defined in `Δ` (`[TR]` p. 3, read non-strict, `[spec §23]`). They agree because the lend's
lifetime is strictly below `@bδ`: 6.60 at `⊒` (`vC_outlivesLe`) puts the payload in `Res_α` for
every `α ⊏ @bδ`, and `withbor2_compatX` applies 6.65 at `↓@bδ`, whose H4 chooses the lend below
it. The strict inequality is the freshness of `'x`, not the side condition.

**2. Freshness excludes `'x` from every payload the borrow constants hand over**
(`payFree_handed`). `withbor` (1)–(3) hand `Imm 'x T₁` or `Mut 'x T₁`, and `withload` hands
`Imm̲ 'x T₁`, each with `'x ∉ T₁` (`hfree₁`, the printed "`'b` does not occur free in `T₁`",
6.172–6.174). `Imm̲` decouples inner lifetimes: `Imm̲ 'x (Imm @a S) = Imm @a S` keeps `@a`. `'x`
is still excluded, since `'x ∉ Imm @a S` says `@a` does not mention `'x` either. In general
`Imm̲ 'x T₁` mentions `'x` only as the lifetime of a borrow it forms, never inside a payload
(`payFree_immReborrow`).

**3. A borrow whose payload mentions `'x` is an inner lend** (`lend_in_scope_below`). Such a
payload is typed inside `'x`'s scope, so the borrow was opened there. A `withbor` in a context
`Δ, 'x` lends at `α ⊏ ⊓(Δ, 'x)δ ⊑ δ('x)`: strictly below the lend at `'x`. That is item 3's case,
a nested lend, not a value of the single-lend stop.

**4. At a stop no borrow payload holds a cell at or below the lend** (`tabAt_wit`). Every run
keeps the table (`wpG_tabAt`), and under it every borrow cell of the share is at a lifetime
`⊒ α`, so its witness is in `Res_α`. Neither the lend's own cell nor an inner lend's cell can sit
inside a payload of a frozen share, whatever the frame value's type says.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### 1. Strictness -/

/-- **The payload is strictly above every lend below the side condition's lifetime.** At
`Δ ⊢ T₁ ⊒ @b` (`withbor` (2)'s side condition, non-strict), every `α ⊏ @bδ` has the payload in
`Res_α`, the strict stratum a `mut` cell at `α` holds its witness in. -/
theorem payload_strict {Δ : LifeCtx} {δ : LSub} (hδ : Δ.Models δ) {T : VTy}
    (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b T) :
    ∃ β : Life, ∀ α, α ⊏ β → ∀ ls w σ, vC true T ls δ w σ → σ.InStratum α := by
  obtain ⟨b, hdef, hO⟩ := hside
  obtain ⟨β, hb⟩ := hdef δ hδ
  exact ⟨β, fun α hα ls w σ h => vC_outlivesLe hδ hb hO true ls w σ h α hα⟩

/-- `withbor2_compatX`'s instance: the payload is in `Res_{↓@bδ}`, the stratum 6.65 is applied at,
and so in `Res_α` at the lend `α ⊑ ↓@bδ` that 6.65's H4 chooses. -/
theorem payload_strict_down {Δ : LifeCtx} {δ : LSub} (hδ : Δ.Models δ) {T : VTy}
    (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b T) :
    ∃ β : Life, ∀ α, α ≤ Life.down β → ∀ ls w σ, vC true T ls δ w σ → σ.InStratum α := by
  obtain ⟨β, hβ⟩ := payload_strict hδ hside
  exact ⟨β, fun α hα ls w σ h =>
    (hβ (Life.down β) (Life.down_sqsubset β) ls w σ h).mono hα⟩

/-! ### 2. Freshness -/

/-- **`'x` occurs in no borrow's payload of `A`**: under `Ref`, `Imm`, `Mut` and `!` the payload
is free of `'x`; elsewhere by parts. `'x` may still be the lifetime of a borrow `A` forms. -/
def PayFree (x : LifeVar) : VTy → Prop
  | .tensor A B => PayFree x A ∧ PayFree x B
  | .sum A B => PayFree x A ∧ PayFree x B
  | .thunk C => ¬ CFree x C
  | .ref A => ¬ VFree x A
  | .imm _ A => ¬ VFree x A
  | .mut _ A => ¬ VFree x A
  | .bang A => ¬ VFree x A
  | .box _ A => PayFree x A
  | .fam A => PayFree x A
  | .mu A => PayFree x A
  | _ => True

/-- A type free of `'x` has `'x` in no payload. -/
theorem payFree_of_not_free {x : LifeVar} : ∀ (A : VTy), ¬ VFree x A → PayFree x A
  | .unit, _ => trivial
  | .zero, _ => trivial
  | .unk, _ => trivial
  | .int _, _ => trivial
  | .opq _, _ => trivial
  | .tvar _, _ => trivial
  | .tensor A B, h => ⟨payFree_of_not_free A (fun h' => h (Or.inl h')),
      payFree_of_not_free B (fun h' => h (Or.inr h'))⟩
  | .sum A B, h => ⟨payFree_of_not_free A (fun h' => h (Or.inl h')),
      payFree_of_not_free B (fun h' => h (Or.inr h'))⟩
  | .thunk _, h => h
  | .ref _, h => h
  | .imm _ _, h => fun h' => h (Or.inr h')
  | .mut _ _, h => fun h' => h (Or.inr h')
  | .bang _, h => h
  | .box _ A, h => payFree_of_not_free A (fun h' => h (Or.inr h'))
  | .fam A, h => payFree_of_not_free A h
  | .mu A, h => payFree_of_not_free A h

/-- **`Imm̲ 'x` at a payload substitution free of `'x`.** Every borrow `immG` forms has as its
payload `pay` applied to a sub-payload of `A`, which is free of `'x`. -/
theorem payFree_immG {x : LifeVar} : ∀ (A : VTy) (pay : Nat → VTy), ¬ VFree x A →
    (∀ n, ¬ VFree x (pay n)) → PayFree x (VTy.immG (.var x) pay A)
  | .unit, _, _, _ => trivial
  | .zero, _, _, _ => trivial
  | .unk, _, _, _ => trivial
  | .int _, _, _, _ => trivial
  | .opq _, _, _, _ => trivial
  | .tvar _, _, _, _ => trivial
  | .thunk _, _, _, _ => trivial
  | .tensor A B, pay, h, hp => ⟨payFree_immG A pay (fun h' => h (Or.inl h')) hp,
      payFree_immG B pay (fun h' => h (Or.inr h')) hp⟩
  | .sum A B, pay, h, hp => ⟨payFree_immG A pay (fun h' => h (Or.inl h')) hp,
      payFree_immG B pay (fun h' => h (Or.inr h')) hp⟩
  | .ref A, pay, h, hp => fun h' =>
      (vFree_subst A pay h').elim h (fun ⟨n, hn⟩ => hp n hn)
  | .imm _ A, pay, h, hp => fun h' =>
      (vFree_subst A pay h').elim (fun h'' => h (Or.inr h'')) (fun ⟨n, hn⟩ => hp n hn)
  | .mut _ A, pay, h, hp => fun h' =>
      (vFree_subst A pay h').elim (fun h'' => h (Or.inr h'')) (fun ⟨n, hn⟩ => hp n hn)
  | .bang A, pay, h, hp => fun h' =>
      (vFree_subst A pay h').elim h (fun ⟨n, hn⟩ => hp n hn)
  | .box _ A, pay, h, hp => payFree_immG A pay (fun h' => h (Or.inr h')) hp
  | .fam A, pay, h, hp => payFree_immG A pay h hp
  | .mu A, pay, h, hp => payFree_immG A _ h (fun n => by
      cases n with
      | zero =>
          intro h'
          exact (vFree_subst (.mu A) pay h').elim h (fun ⟨n, hn⟩ => hp n hn)
      | succ n => exact hp n)

/-- **`Imm̲ 'x T₁` has `'x` in no payload** when `'x ∉ T₁`: it mentions `'x` only as the lifetime
of a borrow it forms. -/
theorem payFree_immReborrow {x : LifeVar} {A : VTy} (h : ¬ VFree x A) :
    PayFree x (A.immReborrow (.var x)) := by
  rw [VTy.immReborrow_eq_immG]
  exact payFree_immG A _ h (fun _ h' => h')

/-- **The decoupled clause.** `Imm̲ 'x (Imm @a S) = Imm @a S`, and freshness (`'x ∉ Imm @a S`)
excludes `'x` from it entirely, the kept lifetime `@a` included. -/
theorem immReborrow_imm_not_free {x : LifeVar} {a : Lifetime.Life} {S : VTy}
    (h : ¬ VFree x (.imm a S)) :
    (VTy.imm a S).immReborrow (.var x) = .imm a S ∧ ¬ VFree x ((VTy.imm a S).immReborrow (.var x)) :=
  ⟨rfl, h⟩

/-- **Every type a borrow constant hands to the borrower at `'x` has `'x` in no payload**:
`Imm 'x T₁` (`withbor` (1)), `Mut 'x T₁` (`withbor` (2), (3)) and `Imm̲ 'x T₁` (`withload`), from
the rules' `'x ∉ T₁`. -/
theorem payFree_handed {x : LifeVar} {A : VTy} (h : ¬ VFree x A) :
    PayFree x (.imm (.var x) A) ∧ PayFree x (.mut (.var x) A) ∧
      PayFree x (A.immReborrow (.var x)) :=
  ⟨h, h, payFree_immReborrow h⟩

/-! ### 3. A lend opened in `'x`'s scope is below `'x` -/

/-- `⊓(Δ, 'x ⊏ b)δ ⊑ δ('x)`. -/
theorem meetOfDom_extend_le {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life} {δ : LSub}
    {αx : Life} (hx : δ.find? x = some αx) {m : Life}
    (hm : (Δ.extend x b).meetOfDom.interp δ = some m) : m ≤ αx := by
  have e : (Δ.extend x b).meetOfDom = .meet (.var x) Δ.meetOfDom := rfl
  rw [e] at hm
  simp only [Lifetime.Life.interp, hx] at hm
  cases hr : Δ.meetOfDom.interp δ with
  | none => rw [hr] at hm; exact absurd hm (by simp [Option.bind])
  | some n =>
      rw [hr] at hm
      cases Option.some.inj hm
      show OrderDual.ofDual αx ≤ Lifetime.SLife.meet (OrderDual.ofDual αx) n
      exact Nat.le_max_left _ _

/-- **A `withbor` in `'x`'s scope lends below `'x`.** The constant's type bounds its lifetime by
`⊓(Δ, 'x)` (`withbor` (1)–(3), `withload`: `∀'y ⊏ ⊓Δ`), so every lend it opens is strictly below
the lend at `'x`. A borrow whose payload mentions `'x` is therefore an inner lend. -/
theorem lend_in_scope_below {Δ : LifeCtx} {x : LifeVar} {b : Lifetime.Life} {δ : LSub}
    {αx : Life} (hx : δ.find? x = some αx) {α : Life}
    (hlt : LtLife δ (Δ.extend x b).meetOfDom α) : α ⊏ αx := by
  obtain ⟨m, hm, hαm⟩ := hlt
  exact lt_of_lt_of_le hαm (meetOfDom_extend_le hx hm)

/-! ### 4. The table: no payload holds a cell at or below the lend -/

/-- **Under the table, every borrow cell's witness is in `Res_α`.** So at a stop (`wpG_tabAt`) no
borrow payload of the frozen share holds the lend's cell, an inner lend's cell, or any cell at a
lifetime `⊑ α`. -/
theorem tabAt_wit {l : BoCa.Loc} {α : Life} {ρ : WRes} (ht : TabAt l α ρ) {k : BoCa.Loc}
    {ψ : CellU BoCa.Loc BoCa.Val} (e : ρ.get k = some ψ) : ψ.wit.InStratum α :=
  CellU.wit_inStratum_of_down (ht.1 k ψ e)

end GhostEnd

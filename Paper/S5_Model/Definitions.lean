import Paper.S1_Syntax.Definitions
import Paper.S3_Dynamics.Definitions
import Support.Dynamics.Machine
import Support.Model.Prelude

/-!
# [TR] §5 Model  (physical pp. 4–6)

The stratified carrier (Fig. 16 rows 1–5)

    SProp_α ≜ Res_α → ℙ          Res_α ≜ Loc ⇀ Cell_α
    Cell_α  ≜ own(Val) + imm(Imm_α) + mut(Mut_α)
    Imm_α   ≜ {(ᾱ : ℘⁺(Life), v : Val, ρ : Res_⊔ᾱ) ∣ ⊓ᾱ ⊐ α}
    Mut_α   ≜ {(β ⊐ α, v : Val, ρ : Res_β, P̂ : Val → SProp_β) ∣ P̂(v)(ρ)}

the unstratified one (rows 6–9)

    P ∈ SProp ≜ Res → ℙ     ρ ∈ Res ≜ Loc ⇀ᶠⁱⁿ Cell     ψ ∈ Cell ≜ ⋃_α Cell_α
    α, β ∈ Life ≜ (ℕ, ⊑ ≜ >, ⊔ ≜ min, ⊓ ≜ max, ⊤ ≜ 0)

the operations of p. 5 — `@ψ`, `@ρ`, `↓α`, `▸◂`, `▷◁`, `●`, `○`, `ρ₁ ▸◁ ρ₂`,
`ρ₁ ◐ ρ₂`, `ρ∣ι`, `ex(ρ)_◐`, `ag(ρ)_◐`, `⦇ρ⦈ ≜ ex(ρ)_● ● ag(ρ)`, `✓ρ ≜ ⦇ρ⦈ defined`,
`⟦ψ⟧`, `⟦ρ⟧`, `ρ₁ # ρ₂ ≜ ρ₁ ▸◂ ρ₂ ∧ ✓(ρ₁ ● ρ₂)`, `ρ₁ ↭ ρ₂`, `reb_α(ρ)` — and the
propositions of p. 6:

    ℓ ↦ v          (ρ) ≜ ρ = ℓ ↦ own(v)
    ℓ ↦ Imm α P̂    (ρ) ≜ ∃ β̄, v, ρ′. ρ = ℓ ↦ imm(β̄, v, ρ′) ∧ P̂(v)(ρ′) ∧ α ⊑ ⊔β̄
    ℓ ↦ Mut α P̂    (ρ) ≜ ∃ β ⊒ α, v, ρ′. ρ = ℓ ↦ mut(β, v, ρ′, P̂)
    [α] P          (ρ) ≜ P(ρ) ∧ @ρ ⊐ α
    wp (e) {Q̂}     (ρ) ≜ ∀ ρ_f # ρ. ∃ ρ′ # ρ_f, ρ⁺ # (ρ_f ● ρ′), v.
                           (⟦ρ_f ● ρ⟧, e) →* (⟦ρ_f ● ρ′ ● ρ⁺⟧, v) ∧ ρ ↭ ρ′ ● ρ⁺ ∧ ρ⁺∣own = ∅ ∧ Q̂(v)(ρ′)
    ⌜P_Meta⌝ (ρ) ≜ ρ = ∅ ∧ P_Meta     P₁ ⋆ P₂ (ρ) ≜ ∃ ρ₁, ρ₂. ρ = ρ₁ ● ρ₂ ∧ P₁(ρ₁) ∧ P₂(ρ₂)
    P₁ ─⋆ P₂ (ρ) ≜ ∀ ρ₁, ρ₂. P₁(ρ₁) ⇒ ρ ● ρ₁ = ρ₂ ⇒ P₂(ρ₂)     emp ≜ ⌜⊤⌝     !P ≜ emp ∧ P
    ⊤, ⊥, ∧, ∨, ⇒, ∀ P̂, ∃ P̂ pointwise      И P̂ ≜ ∃ β. ∀ α ⊏ β. [α] P̂(α)
    ↺_α P (ρ) ≜ ∃ ρ′ ∈ reb_α(ρ). P(ρ′)

Partial operations are graphs — relations `R a b c` read "`a ◐ b` is defined
and equals `c`" (G4).  `Res` is finite at every depth (`PMap`, G1), and a
stratum is membership (`InStratum`, row 5.48).  Rows are numbered as in
`Paper/INDEX.md` (*Definitions*); tags as in `CLAUDE.md`.
-/

noncomputable section

namespace BoCa.Fig16

/-!
### 5.2 · `Res_α ≜ Loc ⇀ Cell_α` · [TR] p. 4, strata row 2 · `[repair]`

The harpoon is bare at this row in both documents; `Res_α` is finite at every depth (`docs/adjudications.md` §12.33, D10, G1).

### 5.7 · `ρ ∈ Res ≜ Loc ⇀ᶠⁱⁿ Cell` · [TR] p. 4, strata row 7 · `[as printed]`
-/
/-- `Loc ⇀ᶠⁱⁿ A`, a partial map with finite domain. -/
structure PMap (Loc A : Type) where
  /-- `ρ(ℓ)`. -/
  get : Loc → Option A
  /-- The `fin` mark of `[TR]` p. 4 row 7. -/
  finite : FinDom get

end BoCa.Fig16

namespace BoCa.Fig16.PMap
variable {Loc A B : Type}

/-- The empty resource. -/
def empty : PMap Loc A where
  get := fun _ => none
  finite := ⟨[], fun _ h => absurd rfl h⟩

@[simp] theorem empty_get (l : Loc) : (empty (A := A)).get l = none := rfl

def map (f : A → B) (p : PMap Loc A) : PMap Loc B where
  get := fun l => (p.get l).map f
  finite := by
    obtain ⟨d, hd⟩ := p.finite
    refine ⟨d, fun l hl => hd l (fun e => ?_)⟩
    simp only [e, Option.map_none] at hl
    exact hl rfl

@[simp] theorem map_get (f : A → B) (p : PMap Loc A) (l : Loc) :
    (p.map f).get l = (p.get l).map f := rfl

theorem ext {p q : PMap Loc A} (h : ∀ l, p.get l = q.get l) : p = q := by
  cases p with
  | mk g hg =>
    cases q with
    | mk g' hg' =>
      have hgg : g = g' := funext h
      subst hgg
      rfl

end BoCa.Fig16.PMap

namespace BoCa.Fig16

/-!
### 5.9 · `α, β ∈ Life ≜ (ℕ, ⊑ ≜ >, ⊔ ≜ min, ⊓ ≜ max, ⊤ ≜ 0)` · [TR] p. 4, strata row 9 · `[repair]`

`>` is given to `⊏`, as [CONF] Fig. 11 labels it, and `⊑` is the reflexive order (`docs/adjudications.md` §12.3, G5).
-/
abbrev Life : Type := ℕᵒᵈ

/-- `℘⁺(Life)` at the sets where `⊓ᾱ` and `⊔ᾱ` are defined (G2). -/
structure LSet where
  /-- `x ∈ ᾱ`. -/
  mem : Life → Prop
  /-- `⊔ᾱ ≜ min ᾱ` — the longest lifetime in `ᾱ`. -/
  join : Life
  /-- `⊓ᾱ ≜ max ᾱ` — the shortest lifetime in `ᾱ`. -/
  meet : Life
  /-- `⊔ᾱ ∈ ᾱ`; in particular `ᾱ ≠ ∅`, which is the `+` of `℘⁺`. -/
  join_mem : mem join
  /-- `⊓ᾱ ∈ ᾱ`. -/
  meet_mem : mem meet
  /-- `⊔ᾱ` is the longest, i.e. the `⊑`-greatest. -/
  join_greatest : ∀ x, mem x → x ≤ join
  /-- `⊓ᾱ` is the shortest, i.e. the `⊑`-least. -/
  meet_least : ∀ x, mem x → meet ≤ x

end BoCa.Fig16

namespace BoCa.Fig16.LSet

theorem meet_le_join (s : LSet) : s.meet ≤ s.join := s.join_greatest _ s.meet_mem

end BoCa.Fig16.LSet

namespace BoCa.Fig16
variable (Loc Val : Type)

/-!
### 5.4 · `Imm_α ≜ {(ᾱ : ℘⁺(Life), v : Val, ρ : Res_⊔ᾱ) ∣ ⊓ᾱ ⊐ α}` · [TR] p. 4, strata row 4 · `[encoding]`

`℘⁺(Life)` is `LSet` (G2): every `ᾱ` satisfying `⊓ᾱ ⊐ α` has a greatest element, so the set `Imm_α` is unchanged.
-/
/-- `Imm_α`, one layer.  `[variant: `Res` is finite at every depth (G1; `docs/adjudications.md` D10 and §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
structure ImmF (α : Life) (below : ∀ β, α < β → Type) : Type where
  /-- `ᾱ : ℘⁺(Life)`. -/
  ls : LSet
  /-- `⊓ᾱ ⊐ α`. -/
  hls : α < ls.meet
  /-- `v : Val`. -/
  v : Val
  /-- `ρ : Res_{⊔ᾱ}`. -/
  ρ : PMap Loc (below ls.join (lt_of_lt_of_le hls ls.meet_le_join))

/-!
### 5.5 · `Mut_α ≜ {(β ⊐ α, v : Val, ρ : Res_β, P̂ : Val → SProp_β) ∣ P̂(v)(ρ)}` · [TR] p. 4, strata row 5 · `[as printed]`
-/
/-- `Mut_α`, one layer.  `[variant: `Res` is finite at every depth (G1; `docs/adjudications.md` D10 and §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
structure MutF (α : Life) (below : ∀ β, α < β → Type) : Type where
  /-- The cell's own lifetime. -/
  β : Life
  /-- `β ⊐ α`; this makes the recursion well-founded. -/
  hβ : α < β
  /-- `v : Val`. -/
  v : Val
  /-- `ρ : Res_β`. -/
  ρ : PMap Loc (below β hβ)
  /-- `P̂ : Val → SProp_β`. -/
  P : Val → PMap Loc (below β hβ) → Prop
  /-- `| P̂(v)(ρ)` — the printed refinement. -/
  hw : P v ρ

/-!
### 5.3 · `Cell_α ≜ own(Val) + imm(Imm_α) + mut(Mut_α)` · [TR] p. 4, strata row 3 · `[as printed]`
-/
/-- `Cell_α`, one layer.  `[variant: `Res` is finite at every depth (G1; `docs/adjudications.md` D10 and §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
inductive CellF (α : Life) (below : ∀ β, α < β → Type) : Type where
  /-- `own(Val)`. -/
  | own (v : Val)
  /-- `imm(Imm_α)`. -/
  | imm (i : ImmF Loc Val α below)
  /-- `mut(Mut_α)`. -/
  | mut (m : MutF Loc Val α below)

/-!
### 5.58 · — neither document prints the recursion, only the measure — · [TR] p. 4, row 3 · `[repair]`

Well-founded recursion on the lifetime index; [CONF] p. 415:20: *"using stratification, but using a very different measure"*.  The printed row is the equation `Cell_eq`.
-/
/-- `Cell_α`.  `[about ours: the construction, not the row]` -/
def Cell : Life → Type :=
  WellFounded.fix (invImage OrderDual.ofDual Nat.lt_wfRel).wf (CellF Loc Val)

/-- `Res_α`.  `[variant: the harpoon is bare at this row in both documents;
finiteness is taken from row 7 and made hereditary]` -/
abbrev Res (α : Life) : Type := PMap Loc (Cell Loc Val α)

/-!
### 5.1 · `SProp_α ≜ Res_α → ℙ` · [TR] p. 4, strata row 1 · `[as printed]`
-/
/-- `SProp_α`.  `[variant: `Res` is finite at every depth (G1; `docs/adjudications.md` D10 and §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
abbrev SProp (α : Life) : Type := Res Loc Val α → Prop

/-- Fig. 16 row 3 as an equation; propositional, so the constructors go through
`cast`.  `[variant: `Res` is finite at every depth (G1; `docs/adjudications.md` D10 and §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
theorem Cell_eq (α : Life) :
    Cell Loc Val α = CellF Loc Val α (fun β _ => Cell Loc Val β) :=
  WellFounded.fix_eq (invImage OrderDual.ofDual Nat.lt_wfRel).wf (CellF Loc Val) α

/-- `Imm_α`.  `[variant: `Res` is finite at every depth (G1; `docs/adjudications.md` D10 and §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
abbrev Imm (α : Life) : Type := ImmF Loc Val α (fun β _ => Cell Loc Val β)

/-- `Mut_α`.  `[variant: `Res` is finite at every depth (G1; `docs/adjudications.md` D10 and §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
abbrev Mut (α : Life) : Type := MutF Loc Val α (fun β _ => Cell Loc Val β)

/-!
### 5.8 · `ψ ∈ Cell ≜ ⋃_α Cell_α` · [TR] p. 4, strata row 8 · `[encoding]`

An inductive whose payloads are the strata; `ImmU`/`MutU` are ours.
-/
/-- The `imm` payload of the union.  `[about ours: the union's `imm` payload, decomposed]` -/
structure ImmU : Type where
  /-- `ᾱ : ℘⁺(Life)`. -/
  ls : LSet
  /-- `v : Val`. -/
  v : Val
  /-- `ρ : Res_{⊔ᾱ}`. -/
  ρ : Res Loc Val ls.join

/-- The `mut` payload of the union.  `[about ours: the union's `mut` payload, decomposed]` -/
structure MutU : Type where
  /-- The cell's own lifetime. -/
  β : Life
  /-- `v : Val`. -/
  v : Val
  /-- `ρ : Res_β`. -/
  ρ : Res Loc Val β
  /-- `P̂ : Val → SProp_β`. -/
  P : Val → SProp Loc Val β
  /-- `| P̂(v)(ρ)`. -/
  hw : P v ρ

/-- `ψ ∈ Cell ≜ ⋃_α Cell_α`.  `[variant: `Res` is finite at every depth (G1; `docs/adjudications.md` D10 and §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
inductive CellU : Type where
  /-- `own(Val)`. -/
  | own (v : Val)
  /-- `imm(Imm)`. -/
  | imm (i : ImmU Loc Val)
  /-- `mut(Mut)`. -/
  | mut (m : MutU Loc Val)

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- One layer of a stratum, forgetting the side condition. -/
def CellF.toU {α : Life} :
    CellF Loc Val α (fun β _ => Cell Loc Val β) → CellU Loc Val
  | .own v => .own v
  | .imm i => .imm ⟨i.ls, i.v, i.ρ⟩
  | .mut m => .mut ⟨m.β, m.v, m.ρ, m.P, m.hw⟩

/-- `own(v)`.  `[as printed]` -/
def CellU.ownOf (v : Val) : CellU Loc Val := .own v

end BoCa.Fig16

namespace BoCa.Fig16
variable (Loc Val : Type)

/-- `ρ ∈ Res ≜ Loc ⇀ᶠⁱⁿ Cell`.  `[variant: `Res` is finite at every depth (G1; `docs/adjudications.md` D10 and §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
abbrev ResU : Type := PMap Loc (CellU Loc Val)

/-!
### 5.6 · `P ∈ SProp ≜ Res → ℙ` · [TR] p. 4, strata row 6 · `[as printed]`
-/
/-- `P ∈ SProp ≜ Res → ℙ`.  `[variant: `Res` is finite at every depth (G1; `docs/adjudications.md` D10 and §12.33); of the two printed `Res` rows only row 7, and only in `[TR]`, carries the mark]` -/
abbrev SPropU : Type := ResU Loc Val → Prop

end BoCa.Fig16

namespace BoCa.Fig16.Life

/-- `⊤ ≜ 0`.  `[as printed]` -/
abbrev top : Life := ⊤

/-- `α ⊔ β ≜ min α β`.  `[as printed]` -/
abbrev join (a b : Life) : Life := a ⊔ b

/-- `α ⊓ β ≜ max α β`.  `[as printed]` -/
abbrev meet (a b : Life) : Life := a ⊓ b

/-- `α ⊏ β ≜ α > β`, strict (`docs/adjudications.md` §12.3).  `[as printed]` -/
abbrev Sqsubset (a b : Life) : Prop := a < b

/-- `α ⊐ β ≜ β ⊏ α`, strict.  `[as printed]` -/
abbrev Sqsupset (a b : Life) : Prop := b < a

end BoCa.Fig16.Life

namespace BoCa.Fig16

/-! `[about ours]` -/
@[inherit_doc] scoped infix:50 " ⊐ " => Life.Sqsupset

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### 5.10 · `@ψ ≜ ⊤` if own; `α` if `mut(α,_,_,_)`; `⊓ᾱ` if `imm(ᾱ,_,_,_)` · [TR] p. 5, operation row 1 · `[as printed]`
-/
/-- `@ψ`.  `[variant: [TR] writes the own case argumentless and the imm case
4-ary; the arities of Imm_α and of every other clause on the page are used]` -/
def CellU.at : CellU Loc Val → Life
  | .own _ => ⊤
  | .imm i => i.ls.meet
  | .mut m => m.β

/-! `[about ours]` -/
@[simp] theorem CellU.at_ownOf (v : Val) : (ownOf (Loc := Loc) v).at = ⊤ := rfl

/-- The tag of a cell. -/
def CellU.kind : CellU Loc Val → Kind
  | .own _ => .own
  | .imm _ => .imm
  | .mut _ => .mut

@[simp] theorem CellU.kind_ownOf (v : Val) :
    (CellU.ownOf (Loc := Loc) v).kind = Kind.own := rfl

/-- The meet over an explicitly given list. -/
def ResU.atOn (ρ : ResU Loc Val) : List Loc → Life
  | [] => ⊤
  | l :: d => ((ρ.get l).elim ⊤ CellU.at) ⊓ ResU.atOn ρ d

theorem ResU.atOn_ub (ρ : ResU Loc Val) (d : List Loc) :
    ∀ l ψ, l ∈ d → ρ.get l = some ψ → ρ.atOn d ≤ ψ.at := by
  induction d with
  | nil => intro l ψ h; exact absurd h (by simp)
  | cons k d ih =>
      intro l ψ hmem hget
      show ((ρ.get k).elim ⊤ CellU.at) ⊓ ResU.atOn ρ d ≤ ψ.at
      rcases List.mem_cons.mp hmem with rfl | hmem
      · rw [hget]; exact inf_le_left
      · exact le_trans inf_le_right (ih l ψ hmem hget)

theorem ResU.atOn_lub (ρ : ResU Loc Val) (d : List Loc) (b : Life)
    (hb : ∀ l ψ, ρ.get l = some ψ → b ≤ ψ.at) : b ≤ ρ.atOn d := by
  induction d with
  | nil => exact le_top
  | cons k d ih =>
      show b ≤ ((ρ.get k).elim ⊤ CellU.at) ⊓ ResU.atOn ρ d
      cases hk : ρ.get k with
      | none => exact le_inf le_top ih
      | some ψ => exact le_inf (hb k ψ hk) ih

end BoCa.Fig16

namespace BoCa.Fig16.Life

/-!
### 5.12 · `↓α ≜ α + 1` · [TR] p. 5, operation row 3 · `[as printed]`
-/
/-- `↓α ≜ α + 1`, the next-shorter lifetime (`[TR]` p. 5).  `[as printed]` -/
def down (a : Life) : Life := OrderDual.toDual (OrderDual.ofDual a + 1)

end BoCa.Fig16.Life

namespace BoCa.Fig16.LSet

/-! `[about ours]` -/
/-- `ᾱ₁ ∪ ᾱ₂`, set union (`[TR]` p. 5); `join` and `meet` are recomputed.
`[as printed]` -/
def union (s t : LSet) : LSet where
  mem x := s.mem x ∨ t.mem x
  join := s.join ⊔ t.join
  meet := s.meet ⊓ t.meet
  join_mem := by
    rcases Nat.le_total s.join t.join with h | h
    · rw [sup_eq_left.mpr (show t.join ≤ s.join from h)]; exact Or.inl s.join_mem
    · rw [sup_eq_right.mpr (show s.join ≤ t.join from h)]; exact Or.inr t.join_mem
  meet_mem := by
    rcases Nat.le_total s.meet t.meet with h | h
    · rw [inf_eq_right.mpr (show t.meet ≤ s.meet from h)]; exact Or.inr t.meet_mem
    · rw [inf_eq_left.mpr (show s.meet ≤ t.meet from h)]; exact Or.inl s.meet_mem
  join_greatest := by
    intro x hx
    rcases hx with h | h
    · exact Nat.le_trans (minLeL _ _) (s.join_greatest x h)
    · exact Nat.le_trans (minLeR _ _) (t.join_greatest x h)
  meet_least := by
    intro x hx
    rcases hx with h | h
    · exact Nat.le_trans (s.meet_least x h) (leMaxL _ _)
    · exact Nat.le_trans (t.meet_least x h) (leMaxR _ _)

end BoCa.Fig16.LSet

namespace BoCa.Fig16

@[inherit_doc LSet.union] scoped infixl:65 " ∪ " => LSet.union

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

theorem ImmU.ext {i j : ImmU Loc Val} (hs : i.ls = j.ls) (hv : i.v = j.v)
    (hρ : i.ρ ≍ j.ρ) : i = j := by
  obtain ⟨s₁, v₁, ρ₁⟩ := i
  obtain ⟨s₂, v₂, ρ₂⟩ := j
  simp only at hs hv hρ
  subst hs; subst hv
  simp only [heq_eq_eq] at hρ
  subst hρ; rfl

/-!
### 5.17 · `ρ₁ ▸◁ ρ₂ ≜ ∀ℓ ∈ dom(ρ₁) ∩ dom(ρ₂). ρ₁(ℓ) ▸◁ ρ₂(ℓ)` · [TR] p. 5, operation row 8 · `[as printed]`

The half-filled glyph is a metavariable over the two cell compatibilities; the row is one schema with both instances supplied.
-/
/-- `ρ₁ ▶◁ ρ₂`, the pointwise lift of a cell-level relation `C`.
`[variant: written as a schema in an arbitrary cell-level relation, where the
print's metavariable ranges over two]` -/
def ResU.Compat (C : CellU Loc Val → CellU Loc Val → Prop) (ρ₁ ρ₂ : ResU Loc Val) : Prop :=
  ∀ l ψ₁ ψ₂, ρ₁.get l = some ψ₁ → ρ₂.get l = some ψ₂ → C ψ₁ ψ₂

/-!
### 5.18 · `ρ₁ ◖ ρ₂ ≜ ρ₁/dom(ρ₂) ⊎ ρ₂/dom(ρ₁) ⊎ [ℓ ↦ ψ₁ ◖ ψ₂ ∣ …]`, guarded by `ρ₁ ▸◁ ρ₂` · [TR] p. 5, operation row 9 · `[as printed]`

[TR]'s guarded reading; [CONF] Fig. 16 prints it unguarded.
-/
/-- The three pieces of `ρ₁ ◐ ρ₂` at one location. -/
def OptComp (C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop) :
    Option (CellU Loc Val) → Option (CellU Loc Val) → Option (CellU Loc Val) → Prop
  | none, none, o => o = none
  | some ψ, none, o => o = some ψ
  | none, some ψ, o => o = some ψ
  | some ψ₁, some ψ₂, o => ∃ ψ, o = some ψ ∧ C ψ₁ ψ₂ ψ

/-- `ρ₁ ◐ ρ₂ = ρ`, a schema in the cell-level guard `R` and composition `C`.
`[variant: written as a schema in an arbitrary guard and composition, where the
print's two metavariables range over two correlated pairs; guard and `ρ₂(ℓ)`
from `[TR]`]` -/
def ResU.Comp (R : CellU Loc Val → CellU Loc Val → Prop)
    (C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop)
    (ρ₁ ρ₂ ρ : ResU Loc Val) : Prop :=
  ResU.Compat R ρ₁ ρ₂ ∧ ∀ l, OptComp C (ρ₁.get l) (ρ₂.get l) (ρ.get l)

/-! `[about ours]` -/
theorem optRestrict_eq_none {o : Option (CellU Loc Val)} (k : Kind) (e : o = none) :
    (o.bind fun ψ => if ψ.kind = k then some ψ else none) = none := by subst e; rfl

/-!
### 5.19 · `ρ∣ι ≜ [ℓ ↦ ψ ∣ ρ(ℓ) = ψ = ι(…)]`, `ι ∈ {own, mut, imm}` · [TR] p. 5, operation row 10 · `[as printed]`

Single-tag, as printed; the multi-tag restriction is row 5.51 and the domain restriction row 5.64.
-/
/-- `ρ|ι`.  `[as printed]` -/
def ResU.restrict (ρ : ResU Loc Val) (k : Kind) : ResU Loc Val where
  get := fun l => (ρ.get l).bind fun ψ => if ψ.kind = k then some ψ else none
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    exact ⟨d, fun l hl => hd l (fun e => hl (optRestrict_eq_none k e))⟩

/-!
### 5.24 · `⟦ψ⟧ ≜ v` when `ψ` is `own(v)`, `mut(_,v,_,_)` or `imm(_,v,_)` · [TR] p. 5, operation row 15 · `[as printed]`
-/
def CellU.erase : CellU Loc Val → Val
  | .own v => v
  | .imm i => i.v
  | .mut m => m.v

/-! `[about ours]` -/
@[simp] theorem CellU.erase_ownOf (v : Val) : (CellU.ownOf (Loc := Loc) v).erase = v := rfl

end BoCa.Fig16

namespace BoCa.Fig16.LSet

/-- A singleton lifetime set. -/
def singleton (a : Life) : LSet where
  mem x := x = a
  join := a
  meet := a
  join_mem := rfl
  meet_mem := rfl
  join_greatest := fun _ h => Nat.le_of_eq h.symm
  meet_least := fun _ h => Nat.le_of_eq h

end BoCa.Fig16.LSet

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-- `Res` at the `Loc` and `Val` of `[TR]` §3. -/
abbrev WRes : Type := ResU BoCa.Loc BoCa.Val

/-- `SProp` at the `Loc` and `Val` of `[TR]` §3. -/
abbrev WProp : Type := SPropU BoCa.Loc BoCa.Val

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
### 5.34 · `⌜P_Meta⌝ (ρ) ≜ ρ = ∅ ∧ P_Meta` · [TR] p. 6, proposition row 6 · `[as printed]`
-/
/-- `⌜P_meta⌝ (ρ) ≜ ρ = ∅ ∧ P_meta`. -/
def pure (p : Prop) : SPropU Loc Val := fun ρ => ρ = PMap.empty ∧ p

/-!
### 5.37 · `emp ≜ ⌜⊤⌝` · [TR] p. 6, proposition row 9 · `[as printed]`
-/
def emp : SPropU Loc Val := pure True

/-!
### 5.39 · `⊤ (ρ) ≜ ⊤` · [TR] p. 6, proposition row 11 · `[as printed]`
-/
def top : SPropU Loc Val := fun _ => True

/-!
### 5.40 · `⊥ (ρ) ≜ ⊥` · [TR] p. 6, proposition row 12 · `[as printed]`
-/
def bot : SPropU Loc Val := fun _ => False

/-!
### 5.41 · `P₁ ∧ P₂ (ρ) ≜ P₁(ρ) ∧ P₂(ρ)` · [TR] p. 6, proposition row 13 · `[as printed]`
-/
def and (P Q : SPropU Loc Val) : SPropU Loc Val := fun ρ => P ρ ∧ Q ρ

/-!
### 5.38 · `!P ≜ emp ∧ P` · [TR] p. 6, proposition row 10 · `[as printed]`
-/
/-- `!P ≜ emp ∧ P`. -/
def bang (P : SPropU Loc Val) : SPropU Loc Val := and emp P

/-!
### 5.42 · `P₁ ∨ P₂ (ρ) ≜ P₁(ρ) ∨ P₂(ρ)` · [TR] p. 6, proposition row 14 · `[as printed]`
-/
def or (P Q : SPropU Loc Val) : SPropU Loc Val := fun ρ => P ρ ∨ Q ρ

/-!
### 5.43 · `P₁ ⇒ P₂ (ρ) ≜ P₁(ρ) ⇒ P₂(ρ)` · [TR] p. 6, proposition row 15 · `[as printed]`
-/
def imp (P Q : SPropU Loc Val) : SPropU Loc Val := fun ρ => P ρ → Q ρ

/-!
### 5.44 · `∀ P̂ (ρ) ≜ ∀x. P̂(x)(ρ)` · [TR] p. 6, proposition row 16 · `[encoding]`

`x` ranges over an arbitrary Lean type.
-/
def all {A : Type} (Φ : A → SPropU Loc Val) : SPropU Loc Val := fun ρ => ∀ x, Φ x ρ

/-!
### 5.45 · `∃ P̂ (ρ) ≜ ∃x. P̂(x)(ρ)` · [TR] p. 6, proposition row 17 · `[encoding]`
-/
def ex {A : Type} (Φ : A → SPropU Loc Val) : SPropU Loc Val := fun ρ => ∃ x, Φ x ρ

end BoCa.Fig16.BoLo

namespace BoCa.Fig16

/-! `[about ours]` -/
@[inherit_doc] scoped infix:50 " ⊏ " => Life.Sqsubset

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### 5.48 · — presupposed, never written — · [TR] pp. 4–5 · `[repair]`

The strata are distinct types here, so membership in a stratum is a predicate (G3).
-/
/-- `ψ ∈ Cell_α`.  `[about ours: the membership that ⋃_α Cell_α presupposes, written out]` -/
def CellU.InStratum (α : Life) : CellU Loc Val → Prop
  | .own _ => True
  | .imm i => i.ls.meet ⊐ α
  | .mut m => m.β ⊐ α

/-! `[about ours]` -/
def CellU.toLayer (α : Life) :
    (ψ : CellU Loc Val) → ψ.InStratum α → CellF Loc Val α (fun β _ => Cell Loc Val β)
  | .own v, _ => .own v
  | .imm i, h => .imm ⟨i.ls, h, i.v, i.ρ⟩
  | .mut m, h => .mut ⟨m.β, h, m.v, m.ρ, m.P, m.hw⟩

theorem CellF.toU_inStratum {α : Life}
    (x : CellF Loc Val α (fun β _ => Cell Loc Val β)) : (CellF.toU x).InStratum α := by
  cases x with
  | own v => exact trivial
  | imm i => exact i.hls
  | «mut» m => exact m.hβ

theorem CellU.toU_toLayer {α : Life} (ψ : CellU Loc Val) (h : ψ.InStratum α) :
    CellF.toU (ψ.toLayer α h) = ψ := by cases ψ <;> rfl

@[simp] theorem CellU.inStratum_ownOf (α : Life) (v : Val) :
    (ownOf (Loc := Loc) v).InStratum α := trivial

theorem CellU.InStratum.sup {a b : Life} {ψ : CellU Loc Val}
    (h₁ : ψ.InStratum a) (h₂ : ψ.InStratum b) : ψ.InStratum (a ⊔ b) := by
  cases ψ
  · exact trivial
  · exact sup_lt_iff.mpr ⟨h₁, h₂⟩
  · exact sup_lt_iff.mpr ⟨h₁, h₂⟩

/-- The strata grow as `α` shortens. -/
theorem CellU.InStratum.mono {α α' : Life} (h : α' ≤ α) {ψ : CellU Loc Val}
    (hψ : ψ.InStratum α) : ψ.InStratum α' := by
  cases ψ
  · exact trivial
  · exact lt_of_le_of_lt h hψ
  · exact lt_of_le_of_lt h hψ

/-- `ρ ∈ Res_α` — every cell of `ρ` lies in stratum `α`. -/
def ResU.InStratum (α : Life) (ρ : ResU Loc Val) : Prop :=
  ∀ l ψ, ρ.get l = some ψ → ψ.InStratum α

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable (Loc Val)

/-! `[about ours]` -/
/-- `Res_α` as a subset of `Res`. -/
abbrev ResS (α : Life) : Type := { ρ : ResU Loc Val // ρ.InStratum α }

/-- `SProp_α ≜ Res_α → ℙ`, read on the union. -/
abbrev SPropS (α : Life) : Type := ResS Loc Val α → Prop

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

theorem ResU.InStratum.sup {a b : Life} {ρ : ResU Loc Val}
    (h₁ : ρ.InStratum a) (h₂ : ρ.InStratum b) : ρ.InStratum (a ⊔ b) :=
  fun l ψ e => (h₁ l ψ e).sup (h₂ l ψ e)

theorem ResU.InStratum.mono {α α' : Life} (h : α' ≤ α) {ρ : ResU Loc Val}
    (hρ : ρ.InStratum α) : ρ.InStratum α' := fun l ψ e => (hρ l ψ e).mono h

theorem ResU.InStratum.inf_left {a b : Life} {ρ : ResU Loc Val}
    (h : ρ.InStratum a) : ρ.InStratum (a ⊓ b) := by
  intro l ψ e
  cases ψ with
  | own v => exact trivial
  | imm i => exact lt_of_le_of_lt inf_le_left (h l _ e)
  | «mut» m => exact lt_of_le_of_lt inf_le_left (h l _ e)

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
### 5.32 · `[α] P  (ρ) ≜ P(ρ) ∧ @ρ ⊐ α` · [TR] p. 6, proposition row 4 · `[repair]`

`@ρ ⊐ α` is universal over the borrow cells of `ρ`, as [TR] Lemma 6.121 (p. 32) reads it: *"it suffices if `@(ℓ ↦ own(v)) ⊐ α`, which holds by definition"* (`docs/adjudications.md` §C.25).  Read as a single strict comparison of the meet, it differs at `α = ⊤` on borrow-free resources.
-/
/-- `@ρ ⊐ α`: membership in `Res_α`.  `[repair]` (`[TR]` p. 5, as pp. 32–33 use it; §C.25) -/
def Outlives (ρ : ResU Loc Val) (α : Life) : Prop := ρ.InStratum α

/-- `[α]P`.  `[as printed]` -/
def box (α : Life) (P : SPropU Loc Val) : SPropU Loc Val :=
  fun ρ => P ρ ∧ Outlives ρ α

/-!
### 5.46 · `И P̂ ≜ ∃β. ∀α ⊏ β. [α] P̂(α)` · [TR] p. 6, proposition row 18 · `[as printed]`

[TR]'s row, with `[α]`; [CONF] Fig. 19 prints it without.
-/
/-- `⋔P̂`.  `[as printed]` (`[TR]` p. 6's row) -/
def fresh (P : Life → SPropU Loc Val) : SPropU Loc Val :=
  fun ρ => ∃ β, ∀ α, α ⊏ β → box α (P α) ρ

end BoCa.Fig16.BoLo

namespace BoCa.Fig16
variable {Loc Val : Type}

/-! `[about ours]` -/
theorem CellF.toLayer_toU {α : Life} (x : CellF Loc Val α (fun β _ => Cell Loc Val β))
    (h : (CellF.toU x).InStratum α) : (CellF.toU x).toLayer α h = x := by
  cases x <;> rfl

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable (Loc Val)

/-- `Cell_α` as a subset of `Cell`. -/
abbrev CellS (α : Life) : Type := { ψ : CellU Loc Val // ψ.InStratum α }

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### 5.51 · — `ρ∣own,mut` is used from [TR] Def. 6.3 on with no defining row — · [TR] p. 5 gives only single-tag `ρ∣ι` · `[repair]`
-/
/-- `ρ|ῑ` for a set of tags; `ResU.restrict` is the one-tag instance.
`[variant: `[TR]` p. 5 prints `ρ|ι` at a single tag and uses `ρ|own,mut` from
§6 on without a defining row; this is the multi-tag form those uses need]` -/
def ResU.restrictOn (ρ : ResU Loc Val) (p : Kind → Bool) : ResU Loc Val where
  get := fun l => (ρ.get l).bind fun ψ => if p ψ.kind then some ψ else none
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l hl => hd l (fun e => hl ?_)⟩
    show (ρ.get l).bind _ = none
    rw [e]; rfl

/-- `ρ|own,mut` (`[TR]` Definition 6.3, Lemma 6.52).  `[variant: as
`ResU.restrictOn`]` -/
def ResU.exclPart (ρ : ResU Loc Val) : ResU Loc Val :=
  ρ.restrictOn (fun k => !(k == Kind.imm))

/-!
### 5.52 · `ℓ ↦ ψ` — used from [TR] Lemma 6.17 on, defined nowhere · [TR] pp. 5–6 · `[repair]`

Equality of locations is decided classically (G8).
-/
open Classical in
/-- `ℓ ↦ ψ`, the singleton resource.  `[about ours: the notation both documents use without a defining row]` -/
noncomputable def ResU.single (l : Loc) (ψ : CellU Loc Val) : ResU Loc Val where
  get := fun l' => if l' = l then some ψ else none
  finite := by
    refine ⟨[l], fun l' h => ?_⟩
    by_cases e : l' = l
    · exact e ▸ List.mem_singleton.mpr rfl
    · exact absurd (if_neg e) h

/-! `[about ours]` -/
open Classical in
@[simp] theorem ResU.single_get_self (l : Loc) (ψ : CellU Loc Val) :
    (ResU.single l ψ).get l = some ψ := if_pos rfl

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
### 5.29 · `ℓ ↦ v  (ρ) ≜ ρ = ℓ ↦ own(v)` · [TR] p. 6, proposition row 1 · `[as printed]`
-/
noncomputable def ptoOwn (l : Loc) (v : Val) : SPropU Loc Val :=
  fun ρ => ρ = ResU.single l (CellU.ownOf v)

end BoCa.Fig16.BoLo

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### 5.53 · `ρ/ℓ` — the `/` of `ρ₁/dom(ρ₂)` and of `π(ℓ)/ℓ` · [TR] p. 5, rows 9 and 19 · `[repair]`

Domain subtraction, used on p. 5 and defined nowhere; [CONF] Fig. 19 writes `π(ℓ) ∖ ℓ`.
-/
open Classical in
/-- `ρ/ℓ`.  `[about ours: the notation both documents use without a defining row]` -/
noncomputable def ResU.del (ρ : ResU Loc Val) (l : Loc) : ResU Loc Val where
  get := fun l' => if l' = l then none else ρ.get l'
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l' h => hd l' (fun e => h ?_)⟩
    show (if l' = l then none else ρ.get l') = none
    by_cases f : l' = l
    · exact if_pos f
    · rw [if_neg f]; exact e

/-! `[about ours]` -/
open Classical in
@[simp] theorem ResU.del_get_self (ρ : ResU Loc Val) (l : Loc) :
    (ρ.del l).get l = none := if_pos rfl

/-!
### 5.55 · — the index set of the `ex`/`ag` comprehensions and of `dom(ρ′)` — · [TR] p. 5, rows 11, 12, 19 · `[repair]`

The location index set of the family reading of rows 5.20 and 5.21 (`docs/adjudications.md` §12.36, G6).
-/
/-- `d` lists the locations of `ρ` carrying a cell of tag `k`, each once.
`[about ours: the index set of the printed comprehension, named]` -/
def ResU.Sites (ρ : ResU Loc Val) (k : Kind) (d : List Loc) : Prop :=
  d.Nodup ∧ ∀ l, l ∈ d ↔ ∃ ψ, ρ.get l = some ψ ∧ ψ.kind = k

/-- `d` lists `dom(ρ)`, each location once.  `[about ours: the index set of a
printed family, named, as `ResU.Sites` names the walks']` -/
def ResU.Dom (ρ : ResU Loc Val) (d : List Loc) : Prop :=
  d.Nodup ∧ ∀ l, l ∈ d ↔ ∃ ψ, ρ.get l = some ψ

/-!
### 5.56 · `⨀` — the iterated composition, with no printed empty case · [TR] p. 5, rows 11, 12, 19 · `[repair]`

The empty case `⨀∅ = ∅` is ours; `BigComp.perm` proves the fold order-independent.
-/
/-- `⨀_◐`, folded right with `∅` at the end.  `[about ours: the fold shape of a
printed iterated operator, and the existential over its order]` -/
inductive BigComp (R : CellU Loc Val → CellU Loc Val → Prop)
    (C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop) :
    List (ResU Loc Val) → ResU Loc Val → Prop where
  | nil : BigComp R C [] PMap.empty
  | cons {σ τ ρ : ResU Loc Val} {σs : List (ResU Loc Val)} :
      BigComp R C σs τ → ResU.Comp R C σ τ ρ → BigComp R C (σ :: σs) ρ

/-!
### 5.57 · — the paper's `SProp_α ⊆ SProp_{α′} ⊆ SProp` is a set inclusion — · [TR] p. 4, rows 1 and 6 · `[repair]`

The inclusion is extension by falsity outside the smaller stratum; `SPropS.toU_range` identifies `SProp_α` with the propositions that hold only in `Res_α`.
-/
/-- `SProp_α ⊆ SProp_{α'}`, as the image of the inclusion of subsets. -/
def SPropS.embed {a a' : Life} (P : Val → SPropS Loc Val a) : Val → SPropS Loc Val a' :=
  fun v r => ∃ h : r.val.InStratum a, P v ⟨r.val, h⟩

/-- `P̂ ∧ Q̂`, the invariant `○` clause 3 builds, at the stratum `α ⊓ β`. -/
def SPropS.conj {a b : Life} (P : Val → SPropS Loc Val a) (Q : Val → SPropS Loc Val b) :
    Val → SPropS Loc Val (a ⊓ b) :=
  fun v r => SPropS.embed P v r ∧ SPropS.embed Q v r

/-! `[about ours]` -/
theorem SPropS.conj_holds {a b : Life} {P : Val → SPropS Loc Val a}
    {Q : Val → SPropS Loc Val b} {v : Val} {ρ : ResU Loc Val}
    (ha : ρ.InStratum a) (hb : ρ.InStratum b)
    (hP : P v ⟨ρ, ha⟩) (hQ : Q v ⟨ρ, hb⟩) :
    SPropS.conj P Q v ⟨ρ, ha.mono inf_le_left⟩ := ⟨⟨ha, hP⟩, ⟨hb, hQ⟩⟩

/-- `SProp_α ⊆ SProp`.  `[about ours: the encoding of a set-theoretic
inclusion, not a change of statement]` -/
def SPropS.toU {a : Life} (P : SPropS Loc Val a) : SPropU Loc Val :=
  fun ρ => ∃ h : ρ.InStratum a, P ⟨ρ, h⟩

/-- Restriction along `Res_α ⊆ Res`. -/
def SPropU.toS (a : Life) (P : SPropU Loc Val) : SPropS Loc Val a := fun r => P r.val

/-! `[about ours]` -/
theorem SPropU.toU_toS_iff (a : Life) (P : SPropU Loc Val) (ρ : ResU Loc Val) :
    SPropS.toU (SPropU.toS a P) ρ ↔ (P ρ ∧ ρ.InStratum a) :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- The image of `SPropS.toU` is `{P | ∀ρ. P(ρ) ⇒ ρ ∈ Res_α}`.  `[about ours]` -/
theorem SPropS.toU_range (a : Life) (P : SPropU Loc Val) :
    (∃ Q : SPropS Loc Val a, SPropS.toU Q = P) ↔ ∀ ρ, P ρ → ρ.InStratum a := by
  constructor
  · rintro ⟨Q, rfl⟩ ρ h
    exact h.1
  · intro h
    refine ⟨SPropU.toS a P, funext fun ρ => propext ?_⟩
    rw [SPropU.toU_toS_iff]
    exact ⟨fun k => k.1, fun k => ⟨k, h ρ k⟩⟩

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-- `SProp_β ⊆ SProp` at a family. -/
def ofS {b : Life} (Q : Val → SPropS Loc Val b) : Val → SPropU Loc Val :=
  fun v => SPropS.toU (Q v)

end BoCa.Fig16.BoLo

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- Unfold one layer of `Cell_α`. -/
def Cell.toF {α : Life} (ψ : Cell Loc Val α) : CellF Loc Val α (fun β _ => Cell Loc Val β) :=
  cast (Cell_eq Loc Val α) ψ

/-! `[about ours]` -/
/-- The injection `Cell_α ↪ Cell`. -/
def Cell.toU {α : Life} (ψ : Cell Loc Val α) : CellU Loc Val := CellF.toU ψ.toF

theorem Cell.toU_inStratum {α : Life} (ψ : Cell Loc Val α) : ψ.toU.InStratum α :=
  CellF.toU_inStratum ψ.toF

/-- The injection `Res_α ↪ Res`. -/
def Res.toU {α : Life} (ρ : Res Loc Val α) : ResU Loc Val := ρ.map Cell.toU

theorem Res.toU_inStratum {α : Life} (ρ : Res Loc Val α) : ρ.toU.InStratum α := by
  intro l ψ e
  have he : Option.map Cell.toU (ρ.get l) = some ψ := e
  cases f : ρ.get l with
  | none => rw [f] at he; exact absurd he (by simp)
  | some ψ' =>
      rw [f] at he
      simp only [Option.map_some, Option.some.injEq] at he
      exact he ▸ ψ'.toU_inStratum

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable (Loc Val)
variable {Loc Val}

/-- The forward half of `Res.stratumEquiv`, named. -/
def Res.toS {α : Life} (ρ : Res Loc Val α) : ResS Loc Val α := ⟨ρ.toU, ρ.toU_inStratum⟩

@[simp] theorem Res.val_toS {α : Life} (ρ : Res Loc Val α) : (ρ.toS).val = ρ.toU := rfl

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-- The witness of an `imm` cell, as a member of `Res`. -/
def ImmU.res (i : ImmU Loc Val) : ResU Loc Val := i.ρ.toU

/-- The witness of a `mut` cell, as a member of `Res`. -/
def MutU.res (m : MutU Loc Val) : ResU Loc Val := m.ρ.toU

/-- The witness of a cell (`∅` for `own`).  `[about ours]` -/
def CellU.wit : CellU Loc Val → ResU Loc Val
  | .own _ => PMap.empty
  | .imm i => i.res
  | .mut m => m.res

@[simp] theorem CellU.wit_ownOf (v : Val) :
    (CellU.ownOf (Loc := Loc) v).wit = PMap.empty := rfl

/-!
### 5.20 · `ex(ρ)_◖ ≜ ρ∣own ◖ ρ∣mut ◖ ⨀{ex(ρ′)_◖ ∣ ∃ℓ. ρ(ℓ) = mut(_,_,ρ′,_)}` · [TR] p. 5, operation row 11 · `[repair]`

The comprehension is read as a family indexed by locations (`docs/adjudications.md` §12.36, G6).
-/
mutual

/-- `ex(ρ)_◐ = σ`, the exclusive walk as a graph.  `w` pairs each `mut` location
with the walk of its witness; `hs` indexes them, `hb` is `⨀`, `hnm` is
`ρ|own ◐ ρ|mut`, `hσ` the outer `◐`.
`[variant: the printed comprehension is a set and this is the family it indexes
(convention G6); the recursive subscript is `[TR]`'s generic `◐`, not
`[CONF]` Fig. 18a's `•`]` -/
inductive ExW (R : CellU Loc Val → CellU Loc Val → Prop)
    (C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop) :
    ResU Loc Val → ResU Loc Val → Prop where
  | mk {ρ σ nm b : ResU Loc Val} {w : List (Loc × ResU Loc Val)}
      (hs : ResU.Sites ρ Kind.mut (w.map Prod.fst))
      (hw : ExWits R C ρ w)
      (hb : BigComp R C (w.map Prod.snd) b)
      (hnm : ResU.Comp R C (ρ.restrict Kind.own) (ρ.restrict Kind.mut) nm)
      (hσ : ResU.Comp R C nm b σ) :
      ExW R C ρ σ

/-- The family `{ex(ρ′)_◐ | ∃ℓ. ρ(ℓ) = mut(_,_,ρ′,_)}`, tagged by location. -/
inductive ExWits (R : CellU Loc Val → CellU Loc Val → Prop)
    (C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop) :
    ResU Loc Val → List (Loc × ResU Loc Val) → Prop where
  | nil {ρ : ResU Loc Val} : ExWits R C ρ []
  | cons {ρ e : ResU Loc Val} {l : Loc} {w : List (Loc × ResU Loc Val)}
      (ψ : CellU Loc Val) (hψ : ρ.get l = some ψ) (hk : ψ.kind = Kind.mut)
      (he : ExW R C ψ.wit e) (hw : ExWits R C ρ w) :
      ExWits R C ρ ((l, e) :: w)

end

/-- Fold one layer of `Cell_α`. -/
def Cell.ofF {α : Life} (x : CellF Loc Val α (fun β _ => Cell Loc Val β)) : Cell Loc Val α :=
  cast (Cell_eq Loc Val α).symm x

/-! `[about ours]` -/
@[simp] theorem Cell.toF_ofF {α : Life} (x : CellF Loc Val α (fun β _ => Cell Loc Val β)) :
    (Cell.ofF x).toF = x := cast_right _ x

@[simp] theorem Cell.ofF_toF {α : Life} (ψ : Cell Loc Val α) : Cell.ofF ψ.toF = ψ :=
  cast_left _ ψ

/-- Its inverse on the cells that lie in the stratum. -/
def CellU.toStratum (α : Life) (ψ : CellU Loc Val) (h : ψ.InStratum α) : Cell Loc Val α :=
  Cell.ofF (ψ.toLayer α h)

def optToStratum (α : Life) : (o : Option (CellU Loc Val)) →
    (∀ ψ, o = some ψ → ψ.InStratum α) → Option (Cell Loc Val α)
  | none, _ => none
  | some ψ, h => some (ψ.toStratum α (h ψ rfl))

theorem optToStratum_eq_none {α : Life} {o : Option (CellU Loc Val)}
    (k : ∀ ψ, o = some ψ → ψ.InStratum α) (e : o = none) : optToStratum α o k = none := by
  subst e; rfl

def ResU.toStratum {α : Life} (ρ : ResU Loc Val) (h : ρ.InStratum α) : Res Loc Val α where
  get := fun l => optToStratum α (ρ.get l) (fun ψ e => h l ψ e)
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l hl => hd l (fun e => ?_)⟩
    exact hl (optToStratum_eq_none _ e)

theorem CellU.toU_toStratum {α : Life} (ψ : CellU Loc Val) (h : ψ.InStratum α) :
    (ψ.toStratum α h).toU = ψ := by
  unfold Cell.toU CellU.toStratum
  rw [Cell.toF_ofF, CellU.toU_toLayer]

theorem optToStratum_toU {α : Life} (o : Option (CellU Loc Val))
    (k : ∀ ψ, o = some ψ → ψ.InStratum α) :
    Option.map Cell.toU (optToStratum α o k) = o := by
  cases o with
  | none => rfl
  | some ψ => exact congrArg some (CellU.toU_toStratum ψ _)

theorem ResU.toU_toStratum {α : Life} (ρ : ResU Loc Val) (h : ρ.InStratum α) :
    (ρ.toStratum h).toU = ρ :=
  PMap.ext fun l => optToStratum_toU (ρ.get l) _

theorem Cell.toStratum_toU {α : Life} (ψ : Cell Loc Val α) (h : ψ.toU.InStratum α) :
    ψ.toU.toStratum α h = ψ := by
  unfold CellU.toStratum
  rw [show ψ.toU.toLayer α h = ψ.toF from CellF.toLayer_toU ψ.toF h, Cell.ofF_toF]

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable (Loc Val)
variable {Loc Val}

/-- `Cell_α ≃ {ψ ∈ Cell | ψ ∈ Cell_α}`.  `[about ours: the inclusion is between
sets in the paper and has to be proved here, because the strata are distinct types]` -/
def Cell.stratumEquiv (α : Life) : Equiv (Cell Loc Val α) (CellS Loc Val α) where
  toFun ψ := ⟨ψ.toU, ψ.toU_inStratum⟩
  invFun c := c.val.toStratum α c.property
  leftInv ψ := Cell.toStratum_toU ψ _
  rightInv c := Subtype.ext (CellU.toU_toStratum c.val c.property)

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-! `[about ours]` -/
theorem optToStratum_map {α : Life} (o : Option (Cell Loc Val α))
    (k : ∀ ψ, Option.map Cell.toU o = some ψ → ψ.InStratum α) :
    optToStratum α (Option.map Cell.toU o) k = o := by
  cases o with
  | none => rfl
  | some ψ => exact congrArg some (Cell.toStratum_toU ψ _)

theorem Res.toStratum_toU {α : Life} (ρ : Res Loc Val α) (h : ρ.toU.InStratum α) :
    ρ.toU.toStratum h = ρ :=
  PMap.ext fun l => optToStratum_map (ρ.get l) _

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}
variable (Loc Val)
variable {Loc Val}

/-- `Res_α ≃ {ρ ∈ Res | ρ ∈ Res_α}`.  `[about ours: as Cell.stratumEquiv]` -/
def Res.stratumEquiv (α : Life) : Equiv (Res Loc Val α) (ResS Loc Val α) where
  toFun ρ := ⟨ρ.toU, ρ.toU_inStratum⟩
  invFun r := r.val.toStratum r.property
  leftInv ρ := Res.toStratum_toU ρ _
  rightInv r := Subtype.ext (ResU.toU_toStratum r.val r.property)

/-! `[about ours]` -/
def ResS.toRes {α : Life} (r : ResS Loc Val α) : Res Loc Val α := r.val.toStratum r.property

@[simp] theorem ResS.toS_toRes {α : Life} (r : ResS Loc Val α) : r.toRes.toS = r :=
  (Res.stratumEquiv α).rightInv r

@[simp] theorem Res.toRes_toS {α : Life} (ρ : Res Loc Val α) : ρ.toS.toRes = ρ :=
  (Res.stratumEquiv α).leftInv ρ

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

@[simp] theorem ResS.toU_toRes {α : Life} (r : ResS Loc Val α) : r.toRes.toU = r.val :=
  ResU.toU_toStratum r.val r.property

/-- `imm(ᾱ, v, ρ)`, with `h` the print's `ρ : Res_{⊔ᾱ}`.  `[as printed]` -/
def CellU.immOf (s : LSet) (v : Val) (ρ : ResU Loc Val)
    (h : ρ.InStratum s.join) : CellU Loc Val :=
  .imm ⟨s, v, ResS.toRes ⟨ρ, h⟩⟩

@[simp] theorem CellU.at_immOf (s : LSet) (v : Val) (ρ : ResU Loc Val)
    (h : ρ.InStratum s.join) : (immOf s v ρ h).at = s.meet := rfl

/-- `mut(β, v, ρ, P̂)`, with `h` the print's `ρ : Res_β` and `hw` the refinement
`P̂(v)(ρ)`.  `[as printed]` -/
def CellU.mutOf (b : Life) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum b)
    (P : Val → SPropS Loc Val b) (hw : P v ⟨ρ, h⟩) : CellU Loc Val :=
  .mut ⟨b, v, ResS.toRes ⟨ρ, h⟩, fun v r => P v r.toS, by
    show P v (ResS.toRes ⟨ρ, h⟩).toS
    rw [ResS.toS_toRes]
    exact hw⟩

@[simp] theorem CellU.at_mutOf (b : Life) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum b)
    (P : Val → SPropS Loc Val b) (hw : P v ⟨ρ, h⟩) : (mutOf b v ρ h P hw).at = b := rfl

@[simp] theorem CellU.inStratum_immOf (α : Life) (s : LSet) (v : Val) (ρ : ResU Loc Val)
    (h : ρ.InStratum s.join) : (immOf s v ρ h).InStratum α ↔ s.meet ⊐ α := Iff.rfl

@[simp] theorem CellU.inStratum_mutOf (α : Life) (b : Life) (v : Val) (ρ : ResU Loc Val)
    (h : ρ.InStratum b) (P : Val → SPropS Loc Val b) (hw : P v ⟨ρ, h⟩) :
    (mutOf b v ρ h P hw).InStratum α ↔ b ⊐ α := Iff.rfl

@[simp] theorem CellU.kind_immOf (s : LSet) (v : Val) (ρ : ResU Loc Val)
    (h : ρ.InStratum s.join) : (CellU.immOf s v ρ h).kind = Kind.imm := rfl

@[simp] theorem CellU.kind_mutOf (b : Life) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum b)
    (P : Val → SPropS Loc Val b) (hw : P v ⟨ρ, h⟩) :
    (CellU.mutOf b v ρ h P hw).kind = Kind.mut := rfl

@[simp] theorem CellU.erase_immOf (s : LSet) (v : Val) (ρ : ResU Loc Val)
    (h : ρ.InStratum s.join) : (CellU.immOf s v ρ h).erase = v := rfl

@[simp] theorem CellU.erase_mutOf (b : Life) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum b)
    (P : Val → SPropS Loc Val b) (hw : P v ⟨ρ, h⟩) :
    (CellU.mutOf b v ρ h P hw).erase = v := rfl

@[simp] theorem CellU.wit_immOf (s : LSet) (v : Val) (ρ : ResU Loc Val)
    (h : ρ.InStratum s.join) : (CellU.immOf s v ρ h).wit = ρ :=
  ResS.toU_toRes ⟨ρ, h⟩

@[simp] theorem CellU.wit_mutOf (b : Life) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum b)
    (P : Val → SPropS Loc Val b) (hw : P v ⟨ρ, h⟩) :
    (CellU.mutOf b v ρ h P hw).wit = ρ :=
  ResS.toU_toRes ⟨ρ, h⟩

/-!
### 5.13 · `ψ₁ ▸◂ ψ₂ ≜ ∃ᾱ₁,ᾱ₂,v,ρ. ψ₁ = imm(ᾱ₁,v,ρ) ∧ ψ₂ = imm(ᾱ₂,v,ρ)` · [TR] p. 5, operation row 4 · `[as printed]`
-/
/-- `ψ₁ ▶◀ ψ₂`.  The two extra binders are the print's typing constraints
`ρ : Res_{⊔ᾱᵢ}`.  `[as printed]` -/
def CellU.CompatS (ψ₁ ψ₂ : CellU Loc Val) : Prop :=
  ∃ (s₁ s₂ : LSet) (v : Val) (ρ : ResU Loc Val)
    (h₁ : ρ.InStratum s₁.join) (h₂ : ρ.InStratum s₂.join),
    ψ₁ = CellU.immOf s₁ v ρ h₁ ∧ ψ₂ = CellU.immOf s₂ v ρ h₂

/-!
### 5.15 · `ψ₁ ● ψ₂ ≜ imm(ᾱ₁ ∪ ᾱ₂, v, ρ)` when both are `imm` at the same `v`, ρ · [TR] p. 5, operation row 6 · `[as printed]`
-/
/-- `ψ₁ ● ψ₂ = ψ`, as a graph.  `[as printed]` (as a graph — G4) -/
def CellU.CompS (ψ₁ ψ₂ ψ : CellU Loc Val) : Prop :=
  ∃ (s₁ s₂ : LSet) (v : Val) (ρ : ResU Loc Val)
    (h₁ : ρ.InStratum s₁.join) (h₂ : ρ.InStratum s₂.join)
    (h₃ : ρ.InStratum (s₁ ∪ s₂).join),
    ψ₁ = CellU.immOf s₁ v ρ h₁ ∧ ψ₂ = CellU.immOf s₂ v ρ h₂ ∧
    ψ = CellU.immOf (s₁ ∪ s₂) v ρ h₃

/-! `[about ours]` -/
theorem CellU.immOf_inj {s₁ s₂ : LSet} {v₁ v₂ : Val} {ρ₁ ρ₂ : ResU Loc Val}
    {h₁ : ρ₁.InStratum s₁.join} {h₂ : ρ₂.InStratum s₂.join}
    (e : immOf s₁ v₁ ρ₁ h₁ = immOf s₂ v₂ ρ₂ h₂) : s₁ = s₂ ∧ v₁ = v₂ ∧ ρ₁ = ρ₂ := by
  simp only [immOf] at e
  injection e with e'
  refine ⟨congrArg ImmU.ls e', congrArg ImmU.v e', ?_⟩
  have := congrArg ImmU.res e'
  simpa [ImmU.res] using this

/-- Every `imm` cell is an `immOf`. -/
theorem ImmU.immOf_eta (i : ImmU Loc Val) :
    CellU.immOf i.ls i.v i.res i.ρ.toU_inStratum = .imm i := by
  show CellU.imm _ = CellU.imm i
  refine congrArg CellU.imm (ImmU.ext rfl rfl ?_)
  simp only [heq_eq_eq]
  exact Res.toRes_toS i.ρ

theorem CellU.immOf_congr {s s' : LSet} {v v' : Val} {ρ ρ' : ResU Loc Val}
    (hs : s = s') (hv : v = v') (hρ : ρ = ρ')
    (h : ρ.InStratum s.join) (h' : ρ'.InStratum s'.join) :
    CellU.immOf s v ρ h = CellU.immOf s' v' ρ' h' := by
  subst hs; subst hv; subst hρ; rfl

/-- `●` is single-valued. -/
theorem CellU.CompS.functional {ψ₁ ψ₂ ψ ψ' : CellU Loc Val}
    (h : CellU.CompS ψ₁ ψ₂ ψ) (h' : CellU.CompS ψ₁ ψ₂ ψ') : ψ = ψ' := by
  obtain ⟨s₁, s₂, v, ρ, k₁, k₂, k₃, e₁, e₂, e₃⟩ := h
  obtain ⟨t₁, t₂, w, σ, m₁, m₂, m₃, f₁, f₂, f₃⟩ := h'
  obtain ⟨hs₁, hv₁, hρ₁⟩ := CellU.immOf_inj (e₁.symm.trans f₁)
  obtain ⟨hs₂, -, -⟩ := CellU.immOf_inj (e₂.symm.trans f₂)
  subst hs₁; subst hs₂; subst hv₁; subst hρ₁
  rw [e₃, f₃]

/-- `ρ₁ ▶◀ ρ₂`, the schema at `▶◀`.  `[as printed]` -/
abbrev ResU.CompatS (ρ₁ ρ₂ : ResU Loc Val) : Prop := ResU.Compat CellU.CompatS ρ₁ ρ₂

/-- `ρ₁ ● ρ₂ = ρ`, the schema at `●`; [TR]'s guarded row.  `[as printed]` -/
abbrev ResU.CompS (ρ₁ ρ₂ ρ : ResU Loc Val) : Prop :=
  ResU.Comp CellU.CompatS CellU.CompS ρ₁ ρ₂ ρ

/-- `ex(ρ)_●` — the exclusive walk at the strict operator. -/
abbrev ExS (ρ σ : ResU Loc Val) : Prop := ExW CellU.CompatS CellU.CompS ρ σ

/-!
### 5.28 · `reb_α(ρ) ≜ {ρ′ ∣ @ρ ⊐ α ∧ ∃π : dom(ρ′) → Res. ρ ≥ ⨀_● π(ℓ) ∧ …}` · [TR] p. 5, operation row 19 · `[repair]`

The `imm` clause `ρ(ℓ) = imm(_,_,_) ⇒ ρ′(ℓ) = ρ(ℓ)` is read at a nonempty subset of the lifetimes, same value and witness, following [CONF] 415:24: *"`ρ′` must be just like a subresource of the original resource `ρ` … its imm locations are preserved at their original lifetimes"* (`docs/adjudications.md` §12.67(b)).  `π` is a `Nodup` association list on `dom(ρ′)`; `ρ ≥ x` is row 5.54.
-/
/-- The body of `reb_α`'s `∀ ℓ ∈ dom(π), v, ρ″` at `ℓ` and its piece `p = π(ℓ)`,
in the printed order: own, mut, imm.
`[variant: the `imm` clause at a nonempty subset of `ρ(ℓ)`'s lifetime set,
`docs/adjudications.md` §12.67]` (`[TR]` p. 5's `reb_α`) -/
def ResU.RebAt (α : Life) (ρ ρ' : ResU Loc Val) (l : Loc) (p : ResU Loc Val) : Prop :=
  (∃ ψ, p.get l = some ψ) ∧
  (∀ v : Val, ρ.get l = some (CellU.ownOf v) →
      ∃ h : (p.del l).InStratum (LSet.singleton α).join,
        ρ'.get l = some (CellU.immOf (LSet.singleton α) v (p.del l) h)) ∧
  (∀ (b : Life) (v : Val) (χ : ResU Loc Val) (hb : χ.InStratum b)
      (P : Val → SPropS Loc Val b) (hw : P v ⟨χ, hb⟩),
      ρ.get l = some (CellU.mutOf b v χ hb P hw) →
        (∃ h : χ.InStratum (LSet.singleton α).join,
            ρ'.get l = some (CellU.immOf (LSet.singleton α) v χ h)) ∧
        ResU.Dom p [l]) ∧
  (∀ (s : LSet) (v : Val) (χ : ResU Loc Val) (h : χ.InStratum s.join),
      ρ.get l = some (CellU.immOf s v χ h) →
        (∃ (t : LSet) (ht : χ.InStratum t.join), (∀ x, t.mem x → s.mem x) ∧
            ρ'.get l = some (CellU.immOf t v χ ht)) ∧ ResU.Dom p [l])

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
### 5.35 · `P₁ ⋆ P₂ (ρ) ≜ ∃ρ₁,ρ₂. ρ = ρ₁ ● ρ₂ ∧ P₁(ρ₁) ∧ P₂(ρ₂)` · [TR] p. 6, proposition row 7 · `[as printed]`
-/
/-- `P₁ ⋆ P₂`; definedness of `●` is asserted by its graph (G4).  `[as printed]` -/
def sep (P Q : SPropU Loc Val) : SPropU Loc Val :=
  fun ρ => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ P ρ₁ ∧ Q ρ₂

/-!
### 5.36 · `P₁ –⋆ P₂ (ρ) ≜ ∀ρ₁,ρ₂. P₁(ρ₁) ⇒ ρ ● ρ₁ = ρ₂ ⇒ P₂(ρ₂)` · [TR] p. 6, proposition row 8 · `[as printed]`
-/
/-- `P₁ ─⋆ P₂`, in [TR]'s composition order.  `[as printed]` -/
def wand (P Q : SPropU Loc Val) : SPropU Loc Val :=
  fun ρ => ∀ ρ₁ ρ₂, P ρ₁ → ResU.CompS ρ ρ₁ ρ₂ → Q ρ₂

end BoCa.Fig16.BoLo

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### 5.54 · `ρ₁ ≤ ρ₃ ≜ ∃ρ₂ ▶◀ ρ₁. ρ₁ ● ρ₂ = ρ₃` — `≥` used in `reb_α`, `≤` in [TR] Def. 6.3 · [CONF] p. 415:24 fn. 1 (printed); [TR] p. 5, row 19 (used) · `[as printed]`

[TR] uses the order without a defining row; this is [CONF]'s footnote (`docs/adjudications.md` §12.37).
-/
/-- `ρ ≤ ρ′`; the operands of `▶◀` are transposed (Lemma 6.1).  `[as printed]` -/
def ResU.Le (ρ σ : ResU Loc Val) : Prop := ∃ τ, ResU.CompS ρ τ σ

/-- `ρ′ ∈ reb_α(ρ)`: `@ρ ⊐ α` (as `ResU.InStratum`, §C.25), `π` as a list of pairs over
`dom(ρ′)`, `ρ ≥ ⨀_● π(ℓ)`, and `ResU.RebAt` at each member.  `[as printed]` -/
def ResU.Reb (α : Life) (ρ ρ' : ResU Loc Val) : Prop :=
  ρ.InStratum α ∧
  ∃ (π : List (Loc × ResU Loc Val)) (b : ResU Loc Val),
    ρ'.Dom (π.map Prod.fst) ∧
    BigComp CellU.CompatS CellU.CompS (π.map Prod.snd) b ∧
    ResU.Le b ρ ∧
    ∀ l p, (l, p) ∈ π → ResU.RebAt α ρ ρ' l p

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
### 5.47 · `↺_α P (ρ) ≜ ∃ρ′ ∈ reb_α(ρ). P(ρ′)` · [TR] p. 6, proposition row 19 · `[as printed]`
-/
/-- `↻_α P`.  `[as printed]` (`[TR]` p. 6's row) -/
def reborrow (α : Life) (P : SPropU Loc Val) : SPropU Loc Val :=
  fun ρ => ∃ ρ', ResU.Reb α ρ ρ' ∧ P ρ'

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.Life

/-!
### 5.59 · — ⊑ appears in [TR] p. 4 row 9 as the STRICT `>` — · [TR] p. 4, row 9 · `[repair]`

The reflexive closure of `⊏` (`docs/adjudications.md` §12.3, G5).
-/
/-- `α ⊑ β`, the reflexive closure of `⊏` (G5). -/
abbrev Sqsubseteq (a b : Life) : Prop := a ≤ b

end BoCa.Fig16.Life

namespace BoCa.Fig16

/-! `[about ours]` -/
@[inherit_doc] scoped infix:50 " ⊑ " => Life.Sqsubseteq

end BoCa.Fig16

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### 5.11 · `@ρ ≜ ⊓_{ψ ∈ cod(ρ)} @ψ` · [TR] p. 5, operation row 2 · `[encoding]`

A graph (the greatest lower bound) plus a function; totality is `ResU.exists_atLife`, from row 5.7's `fin`.
-/
/-- `@ρ`, as its graph.  `[as printed]` (as a graph — G4; `⊑` is ours, G5) -/
def ResU.AtLife (ρ : ResU Loc Val) (a : Life) : Prop :=
  (∀ l ψ, ρ.get l = some ψ → a ⊑ ψ.at) ∧
  (∀ b, (∀ l ψ, ρ.get l = some ψ → b ⊑ ψ.at) → b ⊑ a)

theorem ResU.atLife_atOn (ρ : ResU Loc Val) (d : List Loc)
    (hd : ∀ l ψ, ρ.get l = some ψ → l ∈ d) : ρ.AtLife (ρ.atOn d) :=
  ⟨fun l ψ h => ρ.atOn_ub d l ψ (hd l ψ h) h, fun b hb => ρ.atOn_lub d b hb⟩

/-! `[about ours]` -/
/-- `@ρ` is total.  `[about ours: the totality of the printed `@ρ`, which is what
the `fin` mark of [TR] p. 4 row 7 is needed for]` -/
theorem ResU.exists_atLife (ρ : ResU Loc Val) : ∃ a, ρ.AtLife a := by
  obtain ⟨d, hd⟩ := ρ.finite
  exact ⟨ρ.atOn d, ρ.atLife_atOn d (fun l ψ e => hd l (by rw [e]; simp))⟩

/-- `@ρ` as a function.  `[as printed]` -/
noncomputable def ResU.at (ρ : ResU Loc Val) : Life := Classical.choose ρ.exists_atLife

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
variable {Loc Val : Type}

/-!
### 5.30 · `ℓ ↦ Imm α P̂  (ρ) ≜ ∃β̄,v,ρ′. ρ = ℓ ↦ imm(β̄,v,ρ′) ∧ P̂(v)(ρ′) ∧ α ⊑ ⊔β̄` · [TR] p. 6, proposition row 2 · `[repair]`

The last conjunct is `α ⊑ ⊓β̄` (`docs/adjudications.md` §12.67(a)), and `⊑` is reflexive (§12.3, G5).
-/
/-- `ℓ ↦ Imm α P̂`.  `[variant: `⊓β̄` for the printed `⊔β̄`, `docs/adjudications.md` §12.67]` -/
noncomputable def ptoImm (l : Loc) (α : Life) (P : Val → SPropU Loc Val) :
    SPropU Loc Val :=
  fun ρ => ∃ (s : LSet) (v : Val) (σ : ResU Loc Val) (h : σ.InStratum s.join),
    ρ = ResU.single l (CellU.immOf s v σ h) ∧ P v σ ∧ α ⊑ s.meet

/-!
### 5.31 · `ℓ ↦ Mut α P̂  (ρ) ≜ ∃β ⊒ α, v, ρ′. ρ = ℓ ↦ mut(β,v,ρ′,P̂)` · [TR] p. 6, proposition row 3 · `[repair]`

`⊒` is reflexive (§12.3, G5); the stored invariant is matched through `ofS`.
-/
noncomputable def ptoMut (l : Loc) (α : Life) (P : Val → SPropU Loc Val) :
    SPropU Loc Val :=
  fun ρ => ∃ (b : Life) (v : Val) (σ : ResU Loc Val) (h : σ.InStratum b)
      (Q : Val → SPropS Loc Val b) (hw : Q v ⟨σ, h⟩),
    α ⊑ b ∧ ρ = ResU.single l (CellU.mutOf b v σ h Q hw) ∧ ofS Q = P

/-!
### 5.63 · `ρ⁺∣own = ∅` is named; `ℓ ↦ _` has no printed counterpart · [TR] p. 6, row 5 · `[repair]`

`NoOwn` names [TR] p. 6's `ρ⁺∣own = ∅`; `ptoAny` is the wildcard `ℓ ↦ _` of Lemmas 6.95 and 6.119.
-/
/-- `ℓ ↦ _` — a single cell at `ℓ`, of any kind. -/
noncomputable def ptoAny (l : Loc) : SPropU Loc Val :=
  fun ρ => ∃ ψ, ρ = ResU.single l ψ

end BoCa.Fig16.BoLo

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-- `ρ|own = ∅` — the printed side condition on the discarded fragment. -/
def NoOwn (ρ : WRes) : Prop := ρ.restrict Kind.own = PMap.empty

end BoCa.Fig16.BoLo

namespace BoCa.Fig16
variable {Loc Val : Type}

/-! `[about ours]` -/
theorem ResU.restrict_eq_some {ρ : ResU Loc Val} {k : Kind} {l : Loc} {ψ : CellU Loc Val} :
    (ρ.restrict k).get l = some ψ ↔ (ρ.get l = some ψ ∧ ψ.kind = k) := by
  have hdef : (ρ.restrict k).get l
      = (ρ.get l).bind (fun ψ => if ψ.kind = k then some ψ else none) := rfl
  rw [hdef]
  cases hf : ρ.get l with
  | none => simp
  | some ψ' =>
      simp only [Option.bind_some]
      by_cases hk : ψ'.kind = k
      · rw [if_pos hk]
        exact ⟨fun he => by cases Option.some.inj he; exact ⟨rfl, hk⟩, fun he => he.1⟩
      · rw [if_neg hk]
        refine ⟨fun he => absurd he (by simp), fun he => ?_⟩
        cases Option.some.inj he.1
        exact absurd he.2 hk

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

theorem noOwn_iff {ρ : WRes} :
    NoOwn ρ ↔ ∀ l ψ, ρ.get l = some ψ → ψ.kind ≠ Kind.own := by
  constructor
  · intro h l ψ hl hk
    have hs : (ρ.restrict Kind.own).get l = some ψ := ResU.restrict_eq_some.mpr ⟨hl, hk⟩
    rw [h] at hs
    exact absurd hs (by simp)
  · intro h
    refine PMap.ext fun l => ?_
    cases e : (ρ.restrict Kind.own).get l with
    | none => rfl
    | some ψ =>
        obtain ⟨hg, hk⟩ := ResU.restrict_eq_some.mp e
        exact absurd hk (h l ψ hg)

/-- `ρ⁺|own = ∅` is closed under `●`.  `[about ours: the closure the printed
proofs of 6.135 and 6.148 use in one step]` -/
theorem noOwn_compS {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ)
    (h₁ : NoOwn ρ₁) (h₂ : NoOwn ρ₂) : NoOwn ρ := by
  refine noOwn_iff.mpr fun l ψ hl => ?_
  have hc := h.2 l
  cases e₁ : ρ₁.get l <;> cases e₂ : ρ₂.get l <;> rw [e₁, e₂] at hc
  · rw [hc] at hl; exact absurd hl (by simp)
  · rw [hc] at hl; cases Option.some.inj hl; exact noOwn_iff.mp h₂ l _ e₂
  · rw [hc] at hl; cases Option.some.inj hl; exact noOwn_iff.mp h₁ l _ e₁
  · obtain ⟨χ, hχ, hC⟩ := hc
    rw [hχ] at hl
    cases Option.some.inj hl
    obtain ⟨s₁, s₂, w, χw, k₁, k₂, k₃, -, -, e⟩ := hC
    rw [e]
    simp

end BoCa.Fig16.BoLo

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### 5.64 · `ρ∣dom(ρ′)` — a domain restriction, used from [TR] Lemma 6.56 on with no defining row · [TR] p. 18, Lemmas 6.56 and 6.57 · `[repair]`

With it, `ρ/dom(ρ′)`, which [TR] p. 5 writes in `◐`'s defining row.
-/
/-- `ρ|dom(σ)`.  `[about ours: the notation `[TR]` §6 uses without a defining row]` -/
def ResU.restrictDom (ρ σ : ResU Loc Val) : ResU Loc Val where
  get := fun l => if (σ.get l).isSome then ρ.get l else none
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l hl => hd l (fun e => hl ?_)⟩
    show (if (σ.get l).isSome then ρ.get l else none) = none
    rw [e]; exact ite_self none

/-- `ρ/dom(σ)`.  `[about ours: the notation both documents use without a defining row]` -/
def ResU.delDom (ρ σ : ResU Loc Val) : ResU Loc Val where
  get := fun l => if (σ.get l).isSome then none else ρ.get l
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l hl => hd l (fun e => hl ?_)⟩
    show (if (σ.get l).isSome then none else ρ.get l) = none
    rw [e]; exact ite_self none

/-!
### 5.67 · — [CONF] §4.3's characterisation of `✓` — · [CONF] p. 415:21, not in [TR] §5 · `[as printed]`

Recorded in `Paper/S5_Model/Remarks.lean`; `CellU.CompatS.imm_imm` is its *same object* clause at `●`.
-/
/-- Two compatible `imm` cells agree on the value and on the witness. -/
theorem CellU.CompatS.imm_imm {i₁ i₂ : ImmU Loc Val}
    (h : CellU.CompatS (.imm i₁) (.imm i₂)) : i₁.v = i₂.v ∧ i₁.res = i₂.res := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, e₁, e₂⟩ := h
  rw [← ImmU.immOf_eta i₁] at e₁
  rw [← ImmU.immOf_eta i₂] at e₂
  obtain ⟨-, hv₁, hρ₁⟩ := CellU.immOf_inj e₁
  obtain ⟨-, hv₂, hρ₂⟩ := CellU.immOf_inj e₂
  exact ⟨hv₁.trans hv₂.symm, hρ₁.trans hρ₂.symm⟩

/-- `ψ₁ ● ψ₂` as a function of its `▶◀` guard.  `[as printed]` (the printed
equation is `compS_immOf`) -/
def CellU.compS : (ψ₁ ψ₂ : CellU Loc Val) → ψ₁.CompatS ψ₂ → CellU Loc Val
  | .imm i₁, .imm i₂, h =>
      CellU.immOf (i₁.ls ∪ i₂.ls) i₁.v i₁.res
        (by
          have e : i₁.ρ.toU = i₂.ρ.toU := (CellU.CompatS.imm_imm h).2
          have k₂ : ResU.InStratum i₂.ls.join i₁.ρ.toU := by
            rw [e]; exact i₂.ρ.toU_inStratum
          exact ResU.InStratum.sup i₁.ρ.toU_inStratum k₂)
  | .own _, _, h => absurd h (by rintro ⟨_, _, _, _, _, _, e, -⟩; simp [CellU.immOf] at e)
  | .mut _, _, h => absurd h (by rintro ⟨_, _, _, _, _, _, e, -⟩; simp [CellU.immOf] at e)
  | .imm _, .own _, h => absurd h (by rintro ⟨_, _, _, _, _, _, -, e⟩; simp [CellU.immOf] at e)
  | .imm _, .mut _, h => absurd h (by rintro ⟨_, _, _, _, _, _, -, e⟩; simp [CellU.immOf] at e)

/-! `[about ours]` -/
theorem CellU.compS_spec : ∀ (ψ₁ ψ₂ : CellU Loc Val) (h : ψ₁.CompatS ψ₂),
    CellU.CompS ψ₁ ψ₂ (CellU.compS ψ₁ ψ₂ h)
  | .imm i₁, .imm i₂, h => by
      have hv : i₁.v = i₂.v := (CellU.CompatS.imm_imm h).1
      have hρ : i₁.res = i₂.res := (CellU.CompatS.imm_imm h).2
      have k₁ : ResU.InStratum i₁.ls.join i₁.res := i₁.ρ.toU_inStratum
      have k₂ : ResU.InStratum i₂.ls.join i₁.res := by rw [hρ]; exact i₂.ρ.toU_inStratum
      refine ⟨i₁.ls, i₂.ls, i₁.v, i₁.res, k₁, k₂, ResU.InStratum.sup k₁ k₂,
        (ImmU.immOf_eta i₁).symm, ?_, rfl⟩
      exact ((CellU.immOf_congr rfl hv hρ k₂ i₂.ρ.toU_inStratum).trans (ImmU.immOf_eta i₂)).symm
  | .own _, _, h => absurd h (by rintro ⟨_, _, _, _, _, _, e, -⟩; simp [CellU.immOf] at e)
  | .mut _, _, h => absurd h (by rintro ⟨_, _, _, _, _, _, e, -⟩; simp [CellU.immOf] at e)
  | .imm _, .own _, h => absurd h (by rintro ⟨_, _, _, _, _, _, -, e⟩; simp [CellU.immOf] at e)
  | .imm _, .mut _, h => absurd h (by rintro ⟨_, _, _, _, _, _, -, e⟩; simp [CellU.immOf] at e)

/-- The printed equation for `●`.  `[as printed]` -/
theorem CellU.compS_immOf {s₁ s₂ : LSet} {v : Val} {ρ : ResU Loc Val}
    {h₁ : ρ.InStratum s₁.join} {h₂ : ρ.InStratum s₂.join}
    (h : CellU.CompatS (CellU.immOf s₁ v ρ h₁) (CellU.immOf s₂ v ρ h₂))
    (h₃ : ρ.InStratum (s₁ ∪ s₂).join) :
    CellU.compS _ _ h = CellU.immOf (s₁ ∪ s₂) v ρ h₃ :=
  CellU.CompS.functional (CellU.compS_spec _ _ h)
    ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, rfl, rfl, rfl⟩

/-!
### 5.16 · `ψ₁ ○ ψ₂ ≜` five clauses (`ψ₁`; `ψ₁ ● ψ₂`; `mut(α⊓β,v,ρ,P̂∧Q̂)`; `ψᵢ`; `ψᵢ`) · [TR] p. 5, operation row 7 · `[as printed]`

Clause (4) is two constructors and clause (5) four.
-/
/-- `ψ₁ ○ ψ₂ = ψ`, as a graph.  `[as printed]` -/
inductive CellU.CompR : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop where
  /-- (1) `ψ₁` if `ψ₁ = ψ₂`. -/
  | same (ψ : CellU Loc Val) : CellU.CompR ψ ψ ψ
  /-- (2) `ψ₁ ● ψ₂` if `ψ₁ ▶◀ ψ₂`. -/
  | strict {ψ₁ ψ₂ : CellU Loc Val} (h : ψ₁.CompatS ψ₂) :
      CellU.CompR ψ₁ ψ₂ (CellU.compS ψ₁ ψ₂ h)
  /-- (3) `mut(α ⊓ β, v, ρ, P̂ ∧ Q̂)`. -/
  | mutMut (a b : Life) (v : Val) (ρ : ResU Loc Val)
      (ha : ρ.InStratum a) (hb : ρ.InStratum b)
      (P : Val → SPropS Loc Val a) (Q : Val → SPropS Loc Val b)
      (hP : P v ⟨ρ, ha⟩) (hQ : Q v ⟨ρ, hb⟩) :
      CellU.CompR (CellU.mutOf a v ρ ha P hP) (CellU.mutOf b v ρ hb Q hQ)
        (CellU.mutOf (a ⊓ b) v ρ ha.inf_left (SPropS.conj P Q)
          (SPropS.conj_holds ha hb hP hQ))
  /-- (4), `i = 1`. -/
  | mutOwn (a : Life) (v : Val) (ρ : ResU Loc Val) (ha : ρ.InStratum a)
      (P : Val → SPropS Loc Val a) (hP : P v ⟨ρ, ha⟩) :
      CellU.CompR (CellU.mutOf a v ρ ha P hP) (CellU.ownOf v)
        (CellU.mutOf a v ρ ha P hP)
  /-- (4), `i = 2`. -/
  | ownMut (a : Life) (v : Val) (ρ : ResU Loc Val) (ha : ρ.InStratum a)
      (P : Val → SPropS Loc Val a) (hP : P v ⟨ρ, ha⟩) :
      CellU.CompR (CellU.ownOf v) (CellU.mutOf a v ρ ha P hP)
        (CellU.mutOf a v ρ ha P hP)
  /-- (5), `i = 1`, against `own(v)`. -/
  | immOwn (s : LSet) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum s.join) :
      CellU.CompR (CellU.immOf s v ρ h) (CellU.ownOf v) (CellU.immOf s v ρ h)
  /-- (5), `i = 2`, against `own(v)`. -/
  | ownImm (s : LSet) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum s.join) :
      CellU.CompR (CellU.ownOf v) (CellU.immOf s v ρ h) (CellU.immOf s v ρ h)
  /-- (5), `i = 1`, against `mut(β, v, ρ, P̂)`. -/
  | immMut (s : LSet) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum s.join)
      (b : Life) (hb : ρ.InStratum b) (P : Val → SPropS Loc Val b) (hP : P v ⟨ρ, hb⟩) :
      CellU.CompR (CellU.immOf s v ρ h) (CellU.mutOf b v ρ hb P hP)
        (CellU.immOf s v ρ h)
  /-- (5), `i = 2`, against `mut(β, v, ρ, P̂)`. -/
  | mutImm (s : LSet) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum s.join)
      (b : Life) (hb : ρ.InStratum b) (P : Val → SPropS Loc Val b) (hP : P v ⟨ρ, hb⟩) :
      CellU.CompR (CellU.mutOf b v ρ hb P hP) (CellU.immOf s v ρ h)
        (CellU.immOf s v ρ h)

/-!
### 5.14 · `ψ₁ ▷◁ ψ₂ ≜ ψ₁ ▸◂ ψ₂ ∨ ∃i,ᾱ,β,v,ρ,P̂. {ψ₁,ψ₂} ∈ {imm(ᾱ,v,ρ), own(v), mut(β,v,ρ,P̂)}` · [TR] p. 5, operation row 5 · `[repair]`

`⋈` is read as the domain of `○` (`docs/adjudications.md` §12.35).
-/
/-- `ψ₁ ⋈ ψ₂`, the domain of `○`.  `[variant: the domain of `○`, `docs/adjudications.md` §12.35]` -/
def CellU.CompatR (ψ₁ ψ₂ : CellU Loc Val) : Prop := ∃ ψ, CellU.CompR ψ₁ ψ₂ ψ

/-- `ρ₁ ⋈ ρ₂`, the schema at `⋈`.  `[variant: via `CellU.CompatR`]` -/
abbrev ResU.CompatR (ρ₁ ρ₂ : ResU Loc Val) : Prop := ResU.Compat CellU.CompatR ρ₁ ρ₂

/-! `[about ours]` -/
/-- The three-way union at one location, as a function of the guard. -/
def optCompS : (o₁ o₂ : Option (CellU Loc Val)) →
    (∀ ψ₁ ψ₂, o₁ = some ψ₁ → o₂ = some ψ₂ → CellU.CompatS ψ₁ ψ₂) → Option (CellU Loc Val)
  | none, none, _ => none
  | some ψ, none, _ => some ψ
  | none, some ψ, _ => some ψ
  | some ψ₁, some ψ₂, h => some (CellU.compS ψ₁ ψ₂ (h ψ₁ ψ₂ rfl rfl))

theorem optCompS_eq_none {o₁ o₂ : Option (CellU Loc Val)}
    (k : ∀ ψ₁ ψ₂, o₁ = some ψ₁ → o₂ = some ψ₂ → CellU.CompatS ψ₁ ψ₂)
    (e₁ : o₁ = none) (e₂ : o₂ = none) : optCompS o₁ o₂ k = none := by
  subst e₁; subst e₂; rfl

/-- `ρ₁ ● ρ₂` as a function of its `▶◀` guard. -/
def ResU.compS (ρ₁ ρ₂ : ResU Loc Val) (h : ResU.CompatS ρ₁ ρ₂) : ResU Loc Val where
  get := fun l => optCompS (ρ₁.get l) (ρ₂.get l) (fun ψ₁ ψ₂ e₁ e₂ => h l ψ₁ ψ₂ e₁ e₂)
  finite := by
    obtain ⟨d₁, k₁⟩ := ρ₁.finite
    obtain ⟨d₂, k₂⟩ := ρ₂.finite
    refine ⟨d₁ ++ d₂, fun l hl => ?_⟩
    cases e₁ : ρ₁.get l with
    | none =>
        cases e₂ : ρ₂.get l with
        | none => exact absurd (optCompS_eq_none _ e₁ e₂) hl
        | some ψ => exact List.mem_append.mpr (Or.inr (k₂ l (by rw [e₂]; simp)))
    | some ψ => exact List.mem_append.mpr (Or.inl (k₁ l (by rw [e₁]; simp)))

/-- `ρ₁ ○ ρ₂ = ρ`, the schema at `⋈`/`○`.  `[variant: via `CellU.CompatR`]` -/
abbrev ResU.CompR (ρ₁ ρ₂ ρ : ResU Loc Val) : Prop :=
  ResU.Comp CellU.CompatR CellU.CompR ρ₁ ρ₂ ρ

/-- `○` as a function of its guard.  `[about ours: the function form of a graph
the print gives by cases]` -/
noncomputable def CellU.compR (ψ₁ ψ₂ : CellU Loc Val) (h : ψ₁.CompatR ψ₂) : CellU Loc Val :=
  h.choose

noncomputable def optCompR : (o₁ o₂ : Option (CellU Loc Val)) →
    (∀ ψ₁ ψ₂, o₁ = some ψ₁ → o₂ = some ψ₂ → CellU.CompatR ψ₁ ψ₂) → Option (CellU Loc Val)
  | none, none, _ => none
  | some ψ, none, _ => some ψ
  | none, some ψ, _ => some ψ
  | some ψ₁, some ψ₂, h => some (CellU.compR ψ₁ ψ₂ (h ψ₁ ψ₂ rfl rfl))

theorem optCompR_eq_none {o₁ o₂ : Option (CellU Loc Val)}
    (k : ∀ ψ₁ ψ₂, o₁ = some ψ₁ → o₂ = some ψ₂ → CellU.CompatR ψ₁ ψ₂)
    (e₁ : o₁ = none) (e₂ : o₂ = none) : optCompR o₁ o₂ k = none := by
  subst e₁; subst e₂; rfl

/-- `ρ₁ ○ ρ₂` as a function of its `⋈` guard.  `[about ours: the function form
of a graph the print gives by cases]` -/
noncomputable def ResU.compR (ρ₁ ρ₂ : ResU Loc Val) (h : ResU.CompatR ρ₁ ρ₂) : ResU Loc Val where
  get := fun l => optCompR (ρ₁.get l) (ρ₂.get l) (fun ψ₁ ψ₂ e₁ e₂ => h l ψ₁ ψ₂ e₁ e₂)
  finite := by
    obtain ⟨d₁, k₁⟩ := ρ₁.finite
    obtain ⟨d₂, k₂⟩ := ρ₂.finite
    refine ⟨d₁ ++ d₂, fun l hl => ?_⟩
    cases e₁ : ρ₁.get l with
    | none =>
        cases e₂ : ρ₂.get l with
        | none => exact absurd (optCompR_eq_none _ e₁ e₂) hl
        | some ψ => exact List.mem_append.mpr (Or.inr (k₂ l (by rw [e₂]; simp)))
    | some ψ => exact List.mem_append.mpr (Or.inl (k₁ l (by rw [e₁]; simp)))

/-- `ex(ρ)_○`. -/
abbrev ExR (ρ σ : ResU Loc Val) : Prop := ExW CellU.CompatR CellU.CompR ρ σ

/-!
### 5.21 · `ag(ρ)_◖ ≜ ρ∣imm ○ ◯{ag(ρ′) ∣ …mut…} ○ ◯{ex(ρ′)_○ ○ ag(ρ′) ∣ …imm…}` · [TR] p. 5, operation row 12 · `[repair]`

A family indexed by locations, as row 5.20 (§12.36, G6); the left-hand subscript, which occurs nowhere on the right, is dropped, as in [CONF] Fig. 18a.
-/
mutual

/-- `ag(ρ) = σ`, the aliasable walk as a graph, at `○`.
`[variant: the printed comprehensions are sets and these are the families they
index (convention G6); the vestigial `◐` on the printed left-hand side is
dropped, following `[CONF]` Fig. 18a's unsubscripted `A⦇ρ⦈`]` -/
inductive AgW : ResU Loc Val → ResU Loc Val → Prop where
  | mk {ρ σ a bm bi : ResU Loc Val} {wm wi : List (Loc × ResU Loc Val)}
      (hsm : ResU.Sites ρ Kind.mut (wm.map Prod.fst))
      (hsi : ResU.Sites ρ Kind.imm (wi.map Prod.fst))
      (hwm : AgWitsM ρ wm)
      (hwi : AgWitsI ρ wi)
      (hbm : BigComp CellU.CompatR CellU.CompR (wm.map Prod.snd) bm)
      (hbi : BigComp CellU.CompatR CellU.CompR (wi.map Prod.snd) bi)
      (ha : ResU.CompR (ρ.restrict Kind.imm) bm a)
      (hσ : ResU.CompR a bi σ) :
      AgW ρ σ

/-- The family `{ag(ρ′) | ∃ℓ. ρ(ℓ) = mut(_,_,ρ′,_)}`, tagged by location. -/
inductive AgWitsM : ResU Loc Val → List (Loc × ResU Loc Val) → Prop where
  | nil {ρ : ResU Loc Val} : AgWitsM ρ []
  | cons {ρ e : ResU Loc Val} {l : Loc} {w : List (Loc × ResU Loc Val)}
      (ψ : CellU Loc Val) (hψ : ρ.get l = some ψ) (hk : ψ.kind = Kind.mut)
      (he : AgW ψ.wit e) (hw : AgWitsM ρ w) :
      AgWitsM ρ ((l, e) :: w)

/-- The family `{ex(ρ′)_○ ○ ag(ρ′) | ∃ℓ. ρ(ℓ) = imm(_,_,ρ′)}`, tagged by location. -/
inductive AgWitsI : ResU Loc Val → List (Loc × ResU Loc Val) → Prop where
  | nil {ρ : ResU Loc Val} : AgWitsI ρ []
  | cons {ρ p : ResU Loc Val} {l : Loc} {w : List (Loc × ResU Loc Val)}
      (ψ : CellU Loc Val) (hψ : ρ.get l = some ψ) (hk : ψ.kind = Kind.imm)
      (e a : ResU Loc Val) (hex : ExR ψ.wit e) (hag : AgW ψ.wit a)
      (hp : ResU.CompR e a p) (hw : AgWitsI ρ w) :
      AgWitsI ρ ((l, p) :: w)

end

/-!
### 5.22 · `⦇ρ⦈ ≜ ex(ρ)_● ● ag(ρ)` · [TR] p. 5, operation row 13 · `[as printed]`
-/
/-- `⦇ρ⦈ = σ`.  `[as printed]` (as a graph — G4) -/
def ResU.Flat (ρ σ : ResU Loc Val) : Prop :=
  ∃ e a, ExS ρ e ∧ AgW ρ a ∧ ResU.CompS e a σ

/-!
### 5.23 · `✓ρ ≜ ⦇ρ⦈ defined` · [TR] p. 5, operation row 14 · `[as printed]`
-/
def ResU.Valid (ρ : ResU Loc Val) : Prop := ∃ σ, ResU.Flat ρ σ

/-!
### 5.25 · `⟦ρ⟧ ≜ [ℓ ↦ v ∣ ⟦⦇ρ⦈(ℓ)⟧ = v]`, `✓ρ` · [TR] p. 5, operation row 16 · `[as printed]`

[TR]'s row, with the inner erasure and the `✓ρ` guard; [CONF] Fig. 18a prints neither.
-/
/-- `⟦ρ⟧ = m`; the guard `✓ρ` is carried by the existential.  `[as printed]` (as
a graph — G4) -/
def ResU.Lower (ρ : ResU Loc Val) (m : Loc → Option Val) : Prop :=
  ∃ σ, ResU.Flat ρ σ ∧ ∀ l, m l = (σ.get l).map CellU.erase

/-!
### 5.26 · `ρ₁ # ρ₂ ≜ ρ₁ ▸◂ ρ₂ ∧ ✓(ρ₁ ● ρ₂)` · [TR] p. 5, operation row 17 · `[as printed]`
-/
/-- `ρ₁ # ρ₂`; the first conjunct is redundant and kept as printed.  `[as printed]` -/
def ResU.Hash (ρ₁ ρ₂ : ResU Loc Val) : Prop :=
  ResU.CompatS ρ₁ ρ₂ ∧ ∃ ρ, ResU.CompS ρ₁ ρ₂ ρ ∧ ResU.Valid ρ

/-!
### 5.60 · `⦇ρ⦈(ℓ)` — an application of a partial term · [TR] p. 5, row 18 · `[repair]`

"Some flattening of ρ carries ψ at ℓ" (G4); false when `⦇ρ⦈` is undefined.
-/
/-- `⦇ρ⦈(ℓ) = ψ`.  `[about ours: the application `⦇ρ⦈(ℓ)` of a printed term, at the graph]` -/
def ResU.FlatAt (ρ : ResU Loc Val) (l : Loc) (ψ : CellU Loc Val) : Prop :=
  ∃ σ, ResU.Flat ρ σ ∧ σ.get l = some ψ

/-!
### 5.27 · `ρ₁ ↭ ρ₂ ≜ {∀ℓ,… (⦇ρ₁⦈(ℓ)=mut(α,_,_,P̂) ⇔ ⦇ρ₂⦈(ℓ)=mut(α,_,_,P̂)) ∧ (⦇ρ₁⦈(ℓ)=imm(β̄,v,ρ) ⇔ ⦇ρ₂⦈(ℓ)=mut(β̄,v,ρ))}`, `✓ρ₁ ∧ ✓ρ₂` · [TR] p. 5, operation row 18 · `[repair]`

The second clause's right-hand side is read as `imm`, following [CONF] Fig. 18b (`docs/adjudications.md` §12.39, D3).
-/
/-- Clause `imm ⇔ imm` of `↭`, with lifetime set, value and witness fixed.
`[as printed]` -/
def ResU.UpdImm (ρ₁ ρ₂ : ResU Loc Val) : Prop :=
  ∀ (l : Loc) (s : LSet) (v : Val) (χ : ResU Loc Val) (h : χ.InStratum s.join),
    ρ₁.FlatAt l (CellU.immOf s v χ h) ↔ ρ₂.FlatAt l (CellU.immOf s v χ h)

/-- Clause `mut ⇔ mut` of `↭`: `β` and `P̂` fixed, value and witness free on each
side.  `[as printed]` -/
def ResU.UpdMut (ρ₁ ρ₂ : ResU Loc Val) : Prop :=
  ∀ (l : Loc) (b : Life) (P : Val → SPropS Loc Val b),
    (∃ (v : Val) (χ : ResU Loc Val) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
        ρ₁.FlatAt l (CellU.mutOf b v χ h P hw)) ↔
    (∃ (v : Val) (χ : ResU Loc Val) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
        ρ₂.FlatAt l (CellU.mutOf b v χ h P hw))

/-!
### 5.62 · — [CONF] Fig. 18b's unguarded ↭, and the `wp` row read at it — · not in [TR] §5 · `[repair]`

Both printed readings of `↭` are carried (`docs/adjudications.md` D3).
-/
/-- `ρ₁ ↭ ρ₂` as [CONF] Fig. 18b prints it, unguarded.  `[as printed]` -/
def ResU.Upd (ρ₁ ρ₂ : ResU Loc Val) : Prop := ρ₁.UpdImm ρ₂ ∧ ρ₁.UpdMut ρ₂

/-- `ρ₁ ↭ ρ₂` as [TR] p. 5 prints it, guarded by `✓ρ₁ ∧ ✓ρ₂`.  `[as printed]` -/
def ResU.UpdV (ρ₁ ρ₂ : ResU Loc Val) : Prop := ρ₁.Upd ρ₂ ∧ ρ₁.Valid ∧ ρ₂.Valid

end BoCa.Fig16

namespace BoCa.Fig16.BoLo
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-!
### 5.33 · `wp (e) {Q̂} (ρ) ≜ ∀ρ_f # ρ. ∃ρ′ # ρ_f, ρ⁺ # (ρ_f ● ρ′), v. (⟦ρ_f ● ρ⟧,e) →* (⟦ρ_f ● ρ′ ● ρ⁺⟧,v) ∧ ρ ↭ ρ′ ● ρ⁺ ∧ ρ⁺∣own = ∅ ∧ Q̂(v)(ρ′)` · [TR] p. 6, proposition row 5 · `[repair]`

`→*` is `BoLo.Steps`, which adds the frames `K; e` and `injᵢ K` (`docs/adjudications.md` §12.42, D6).  At the typed world, `∀ρ_f # ρ` ranges over the frames completing `ρ` to a tagged `Typed.TW` world, and the post-configuration is one too (§12.72).
-/
/-- `wp(e){Q̂}`, with `↭` guarded.  `fρ` is `ρ_f ● ρ`, `fρ'` is `ρ_f ● ρ′`,
`fρ'p` is `ρ_f ● ρ′ ● ρ⁺` and `π` is `ρ′ ● ρ⁺`, each by its graph.  `[as printed]`
(`[TR]` p. 6's row; the printed compositions and lowerings appear as their
graphs — G4) -/
def wp (e : Expr) (Q : Val → WProp) : WProp := fun ρ =>
  ∀ ρf : WRes, ResU.Hash ρf ρ →
    ∃ (ρ' ρp fρ fρ' fρ'p π : WRes) (v : Val) (μ μ' : Heap),
      ResU.Hash ρ' ρf ∧
      ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
      ResU.CompS ρf ρ fρ ∧ ResU.Lower fρ μ ∧
      ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
      Steps μ e μ' (.val v) ∧
      ResU.CompS ρ' ρp π ∧ ResU.UpdV ρ π ∧
      NoOwn ρp ∧
      Q v ρ'

/-- `wp` with [CONF] Fig. 18b's unguarded `↭`.  `[variant: `wp` above with the `↭`
of `[CONF]` Fig. 18b (p. 415:22) in place of `[TR]` p. 5's, and otherwise
identical]` -/
def wpU (e : Expr) (Q : Val → WProp) : WProp := fun ρ =>
  ∀ ρf : WRes, ResU.Hash ρf ρ →
    ∃ (ρ' ρp fρ fρ' fρ'p π : WRes) (v : Val) (μ μ' : Heap),
      ResU.Hash ρ' ρf ∧
      ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
      ResU.CompS ρf ρ fρ ∧ ResU.Lower fρ μ ∧
      ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
      Steps μ e μ' (.val v) ∧
      ResU.CompS ρ' ρp π ∧ ResU.Upd ρ π ∧
      NoOwn ρp ∧
      Q v ρ'

end BoCa.Fig16.BoLo

end

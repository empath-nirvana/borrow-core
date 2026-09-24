import Paper.S5_Model.Definitions
import Support.Model.Cells
import Support.Model.Prelude

/-!
# [TR] §6.2 Non-standard Lemmas — Definitions 6.1–6.3  (pp. 9, 13, 17)

* **Definition 6.1** (p. 9).  Let `⦇ρ⦈_○ ≔ ag(ρ) ○ ex(ρ)_○`.
* **Definition 6.2** (p. 13).  Let `ψ ∼ ψ′ ≔ (ψ = mut(α, _, _, P̂) ∧ ψ′ = mut(α, _, _, P̂))
  ∨ (ψ = ψ′ = imm(α, v, ρ))`.
* **Definition 6.3** (p. 17).  `ρ ⊟ ρ′ ≜ ρ∣own,mut ● ρ″` where
  - `ρ′∣own,mut = ∅`;
  - `ρ″ ≤ ρ∣imm`;
  - if `ℓ ∈ dom(ρ∣imm) ∖ dom(ρ′)` then `ℓ ∈ dom(ρ″)`;
  - if `ℓ ∈ dom(ρ∣imm) ∩ dom(ρ′)` and `ρ(ℓ) = imm(α, ρᵢ, v)` and `ρ′(ℓ) = imm(β, ρᵢ, v)` then
    if `α ∖ β = ∅`, then `ℓ ∉ ρ″`; if `α ∖ β ≠ ∅`, then `ρ′(ℓ) = imm(α ∖ β, ρᵢ, v)`.

  *"Intuitively, `ρ ⊟ ρ′` is `ρ` without the immutable borrows in `ρ′`.  But since
  immutable borrows can alias at the same location, 'without' means removing the
  lifetimes of borrows from `ρ′`, but keeping the lifetimes only in `ρ`."*

Row numbers are those of `Paper/INDEX.md` (*Definitions*).
-/

noncomputable section

namespace BoCa.Fig16
variable {Loc Val : Type}

/-!
### 5.61 · `⦇ρ⦈_○ ≜ ag(ρ) ○ ex(ρ)_○` — [TR] Definition 6.1 · [TR] p. 9 · `[as printed]`

As a graph (G4).
-/
/-- `⦇ρ⦈_○ = σ`, `[TR]` Definition 6.1 (p. 9).  `[as printed]` (as a graph, G4) -/
def ResU.FlatR (ρ σ : ResU Loc Val) : Prop :=
  ∃ a e, AgW ρ a ∧ ExR ρ e ∧ ResU.CompR a e σ

/-!
### 5.65 · `ψ ∼ ψ′ ≔ (ψ = mut(α,_,_,P̂) ∧ ψ′ = mut(α,_,_,P̂)) ∨ (ψ = ψ′ = imm(ᾱ,v,ρ))` — [TR] Definition 6.2 · [TR] p. 13 · `[as printed]`

[TR] §6 unfolds `↭` through it (Lemmas 6.39, 6.40, 6.44, 6.59) as "dom(⦇ρ₁⦈∣imm,mut) =
dom(⦇ρ₂⦈∣imm,mut) and for every ℓ in that domain, ⦇ρ₁⦈(ℓ) ∼ ⦇ρ₂⦈(ℓ)"; `upd_iff_sim`
proves that form equal to [CONF] Fig. 18b's two clauses.
-/
/-- `ψ ∼ ψ′`, `[TR]` Definition 6.2 (p. 13).  `α` and `P̂` are bound outside the
`mut` conjunction, the value and witness (`_`) inside each conjunct; an `own`
cell is related to nothing.  `[as printed]` -/
def CellU.Sim (ψ ψ' : CellU Loc Val) : Prop :=
  (∃ (a : Life) (P : Val → SPropS Loc Val a),
      (∃ (v : Val) (χ : ResU Loc Val) (h : χ.InStratum a) (hw : P v ⟨χ, h⟩),
          ψ = CellU.mutOf a v χ h P hw) ∧
      (∃ (v : Val) (χ : ResU Loc Val) (h : χ.InStratum a) (hw : P v ⟨χ, h⟩),
          ψ' = CellU.mutOf a v χ h P hw)) ∨
  (∃ (s : LSet) (v : Val) (χ : ResU Loc Val) (h : χ.InStratum s.join),
      ψ = CellU.immOf s v χ h ∧ ψ' = CellU.immOf s v χ h)

/-- `∼` is reflexive on a borrow cell. -/
theorem CellU.Sim.refl {ψ : CellU Loc Val} (hk : ψ.kind ≠ Kind.own) :
    CellU.Sim ψ ψ := by
  rcases CellU.rep ψ with ⟨v, rfl⟩ | ⟨s, v, χ, hh, rfl⟩ | ⟨b, v, χ, hh, P, hw, rfl⟩
  · exact absurd (by simp : (CellU.ownOf (Loc := Loc) v).kind = Kind.own) hk
  · exact Or.inr ⟨s, v, χ, hh, rfl, rfl⟩
  · exact Or.inl ⟨b, P, ⟨v, χ, hh, hw, rfl⟩, ⟨v, χ, hh, hw, rfl⟩⟩

/-- `ρ|imm,mut`, used by `[TR]` §6 from Lemma 6.39 on; p. 5 defines only the
single-tag `ρ|ι`.  `[variant: as `ResU.restrictOn`; no defining row is printed for
the multi-tag restriction]` -/
def ResU.borrowPart (ρ : ResU Loc Val) : ResU Loc Val :=
  ρ.restrictOn (fun k => !(k == Kind.own))

/-- The form `[TR]` §6's proofs unfold `↭` to, at two named flattenings (G4). -/
def ResU.SimForm (σ₁ σ₂ : ResU Loc Val) : Prop :=
  (∀ l : Loc, (∃ ψ, σ₁.borrowPart.get l = some ψ) ↔
      (∃ ψ, σ₂.borrowPart.get l = some ψ)) ∧
  (∀ (l : Loc) (ψ₁ : CellU Loc Val), σ₁.borrowPart.get l = some ψ₁ →
      ∃ ψ₂, σ₂.get l = some ψ₂ ∧ CellU.Sim ψ₁ ψ₂)

/-!
### 5.66 · `ρ ⊟ ρ′ ≜ ρ∣own,mut ● ρ″ where …` — [TR] Definition 6.3 · [TR] p. 17 · `[repair]`

The fourth bullet's single prime in `ρ′(ℓ) = imm(ᾱ ∖ β̄, ρᵢ, v)` is read as `ρ″`
(`docs/adjudications.md` §12.34; literal reading `ResU.SubL`).  The third bullet is
read through the paragraph printed below it, so `ρ″(ℓ) = ρ(ℓ)` off `dom(ρ′)`
(`ResU.SubKeep`, §12.58, §12.64); on it `⊟` is a function
(`ResU.SubKeep.functional`).  `ResU.Sub` is the bullets alone.
-/
/-- The fourth bullet of `[TR]` Definition 6.3 (p. 17), its second sub-case read
as a constraint on `ρ″`.  `[variant: the printed single prime is read as `ρ″`,
§12.34]` -/
def ResU.SubClause (ρ ρ' ρ'' : ResU Loc Val) : Prop :=
  ∀ (l : Loc) (s s' : LSet) (v : Val) (ρi : ResU Loc Val)
    (h : ρi.InStratum s.join) (h' : ρi.InStratum s'.join),
    ρ.get l = some (CellU.immOf s v ρi h) →
    ρ'.get l = some (CellU.immOf s' v ρi h') →
    (LSet.DiffEmpty s s' → ρ''.get l = none) ∧
    (∀ u : LSet, LSet.Diff s s' u → ¬ LSet.DiffEmpty s s' →
        ∃ hu : ρi.InStratum u.join, ρ''.get l = some (CellU.immOf u v ρi hu))

/-- The same bullet as printed: the second sub-case constrains `ρ′`.  `[as printed]` -/
def ResU.SubClauseL (ρ ρ' ρ'' : ResU Loc Val) : Prop :=
  ∀ (l : Loc) (s s' : LSet) (v : Val) (ρi : ResU Loc Val)
    (h : ρi.InStratum s.join) (h' : ρi.InStratum s'.join),
    ρ.get l = some (CellU.immOf s v ρi h) →
    ρ'.get l = some (CellU.immOf s' v ρi h') →
    (LSet.DiffEmpty s s' → ρ''.get l = none) ∧
    (∀ u : LSet, LSet.Diff s s' u → ¬ LSet.DiffEmpty s s' →
        ∃ hu : ρi.InStratum u.join, ρ'.get l = some (CellU.immOf u v ρi hu))

/-- `[TR]` Definition 6.3's bullets without the paragraph below them.
`[variant: bullets only; last sub-case's prime read as `ρ″`, §12.34, §12.64]` -/
def ResU.Sub (ρ ρ' χ : ResU Loc Val) : Prop :=
  ∃ ρ'' : ResU Loc Val,
    ρ'.exclPart = PMap.empty ∧
    ResU.Le ρ'' (ρ.restrict Kind.imm) ∧
    (∀ l, (ρ.restrict Kind.imm).get l ≠ none → ρ'.get l = none → ρ''.get l ≠ none) ∧
    ResU.SubClause ρ ρ' ρ'' ∧
    ResU.CompS ρ.exclPart ρ'' χ

/-- `ρ ⊟ ρ′ = χ`, `[TR]` Definition 6.3 with the last sub-case literal.
`[variant: `ρ|own,mut` restricts on two tags where the printed `ρ|ι` takes one]` -/
def ResU.SubL (ρ ρ' χ : ResU Loc Val) : Prop :=
  ∃ ρ'' : ResU Loc Val,
    ρ'.exclPart = PMap.empty ∧
    ResU.Le ρ'' (ρ.restrict Kind.imm) ∧
    (∀ l, (ρ.restrict Kind.imm).get l ≠ none → ρ'.get l = none → ρ''.get l ≠ none) ∧
    ResU.SubClauseL ρ ρ' ρ'' ∧
    ResU.CompS ρ.exclPart ρ'' χ

/-- `ρ ⊟ ρ′ = χ`, `[TR]` Definition 6.3 (p. 17): the bullets with the third read
through the paragraph below them (§12.64).  `[as printed]` (the fourth bullet's
single prime read as `ρ″`, §12.34) -/
def ResU.SubKeep (ρ ρ' χ : ResU Loc Val) : Prop :=
  ∃ ρ'' : ResU Loc Val,
    ρ'.exclPart = PMap.empty ∧
    ResU.Le ρ'' (ρ.restrict Kind.imm) ∧
    (∀ l, (ρ.restrict Kind.imm).get l ≠ none → ρ'.get l = none →
      ρ''.get l = (ρ.restrict Kind.imm).get l) ∧
    ResU.SubClause ρ ρ' ρ'' ∧
    ResU.CompS ρ.exclPart ρ'' χ

end BoCa.Fig16

end

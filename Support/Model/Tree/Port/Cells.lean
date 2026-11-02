import Support.Model.Tree.Port.Split

/-!
# Cell facts, `↭`, and Definitions 6.1–6.2 at the tree-stratified carrier

`Support/Model/Cells.lean`, `Support/Model/CellFacts.lean`, row 5.27 (`↭`) and `[TR]`
Definitions 6.1–6.2 read at `CellUT K`. The `mut` cell's lifetime is a set `β̄` (clause 3
restated, `Tree/CarrierOps.lean`), so every place the printed text writes a `mut` cell's `β`
it writes `β̄` and the antichain proof; `↭`'s `mut` clause fixes `β̄` and `P̂` as the printed
one fixes `β` and `P̂`.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

variable {Loc Val : Type} {K : WCactus}

/-- The lifetime set of an `imm` cell (`Support/Model/Cells.lean`'s `CellU.lsOf`). -/
def CellUT.lsOfI : CellUT Loc Val K → Option TSet
  | .imm i => some i.ls
  | _ => none

@[simp] theorem CellUT.lsOfI_immOf (s : TSet) (v : Val) (ρ : ResUT Loc Val K)
    (h : ρ.InStratum s) : CellUT.lsOfI (CellUT.immOf s v ρ h) = some s := rfl

@[simp] theorem CellUT.lsOfI_ownOf (v : Val) :
    CellUT.lsOfI (CellUT.ownOf (K := K) (Loc := Loc) v) = none := rfl

@[simp] theorem CellUT.lsOfI_mutOf (b : TSet) [Fact (K.Anti b)] (v : Val) (ρ : ResUT Loc Val K)
    (h : ρ.InStratum b) (P : Val → SPropST Loc Val K b) (hw : P v ⟨ρ, h⟩) :
    CellUT.lsOfI (CellUT.mutOf b v ρ h P hw) = none := rfl

/-- The invariant of a `mut` cell as a predicate on `Res`, false outside `Res_β̄`. -/
def MutT.pred (m : MutT Loc Val K) : Val → ResUT Loc Val K → Prop :=
  fun v r => ∃ h : r.InStratum m.ls, m.P v (ResUT.toStratum r h)

theorem CellUT.ownOf_ne_immOf {v v' : Val} {s : TSet} {ρ : ResUT Loc Val K}
    {h : ρ.InStratum s} : CellUT.ownOf v ≠ CellUT.immOf s v' ρ h := by
  intro e; simp [CellUT.ownOf, CellUT.immOf] at e

theorem CellUT.ownOf_ne_mutOf {v v' : Val} {b : TSet} [Fact (K.Anti b)] {ρ : ResUT Loc Val K}
    {h : ρ.InStratum b} {P : Val → SPropST Loc Val K b} {hw : P v' ⟨ρ, h⟩} :
    CellUT.ownOf v ≠ CellUT.mutOf b v' ρ h P hw := by
  intro e; simp [CellUT.ownOf, CellUT.mutOf] at e

theorem CellUT.immOf_ne_mutOf {s : TSet} {v v' : Val} {ρ ρ' : ResUT Loc Val K}
    {h : ρ.InStratum s} {b : TSet} [Fact (K.Anti b)] {h' : ρ'.InStratum b}
    {P : Val → SPropST Loc Val K b} {hw : P v' ⟨ρ', h'⟩} :
    CellUT.immOf s v ρ h ≠ CellUT.mutOf b v' ρ' h' P hw := by
  intro e; simp [CellUT.immOf, CellUT.mutOf] at e

/-- `mut(β̄₁, …) = mut(β̄₂, …)` gives `β̄₁ = β̄₂`: the printed `CellU.mutOf_at`. -/
theorem CellUT.mutOf_ls {b₁ b₂ : TSet} [Fact (K.Anti b₁)] [Fact (K.Anti b₂)] {v₁ v₂ : Val}
    {ρ₁ ρ₂ : ResUT Loc Val K} {h₁ : ρ₁.InStratum b₁} {h₂ : ρ₂.InStratum b₂}
    {P₁ : Val → SPropST Loc Val K b₁} {P₂ : Val → SPropST Loc Val K b₂}
    {hw₁ : P₁ v₁ ⟨ρ₁, h₁⟩} {hw₂ : P₂ v₂ ⟨ρ₂, h₂⟩}
    (e : CellUT.mutOf b₁ v₁ ρ₁ h₁ P₁ hw₁ = CellUT.mutOf b₂ v₂ ρ₂ h₂ P₂ hw₂) : b₁ = b₂ :=
  (CellUT.mutOf_injSet e).1

/-- The printed `CellU.mutOf_inj`: at one lifetime set, value, witness and invariant. -/
theorem CellUT.mutOf_inj {b : TSet} [Fact (K.Anti b)] {v₁ v₂ : Val} {ρ₁ ρ₂ : ResUT Loc Val K}
    {h₁ : ρ₁.InStratum b} {h₂ : ρ₂.InStratum b} {P₁ P₂ : Val → SPropST Loc Val K b}
    {hw₁ : P₁ v₁ ⟨ρ₁, h₁⟩} {hw₂ : P₂ v₂ ⟨ρ₂, h₂⟩}
    (e : CellUT.mutOf b v₁ ρ₁ h₁ P₁ hw₁ = CellUT.mutOf b v₂ ρ₂ h₂ P₂ hw₂) :
    v₁ = v₂ ∧ ρ₁ = ρ₂ ∧ P₁ = P₂ := by
  obtain ⟨-, hv, hρ, hP⟩ := CellUT.mutOf_injSet e
  exact ⟨hv, hρ, funext fun w => funext fun r => propext (hP r.val r.property r.property w)⟩

/-! ### The printed-shape `mut` lemmas -/

theorem CellUT.kind_mutOf_ne_own' (b : TSet) [Fact (K.Anti b)] (v : Val) (ρ : ResUT Loc Val K)
    (h : ρ.InStratum b) (P : Val → SPropST Loc Val K b) (hw : P v ⟨ρ, h⟩) :
    (CellUT.mutOf b v ρ h P hw).kind ≠ Kind.own := fun hk => Kind.noConfusion hk

/-- Every `mut` cell is a `mutOf`, with its antichain fact (`CellUT.rep`). -/
theorem CellUT.rep' (ψ : CellUT Loc Val K) :
    (∃ v : Val, ψ = CellUT.ownOf v) ∨
    (∃ (s : TSet) (v : Val) (ρ : ResUT Loc Val K) (h : ρ.InStratum s),
        ψ = CellUT.immOf s v ρ h) ∨
    (∃ (b : TSet) (_ : Fact (K.Anti b)) (v : Val) (ρ : ResUT Loc Val K) (h : ρ.InStratum b)
        (P : Val → SPropST Loc Val K b) (hw : P v ⟨ρ, h⟩), ψ = CellUT.mutOf b v ρ h P hw) :=
  CellUT.rep ψ

/-! ### Row 5.27: `↭` -/

/-- Clause `imm ⇔ imm` of `↭`, lifetime set, value and witness fixed. -/
def ResUT.UpdImm (ρ₁ ρ₂ : ResUT Loc Val K) : Prop :=
  ∀ (l : Loc) (s : TSet) (v : Val) (χ : ResUT Loc Val K) (h : χ.InStratum s),
    ρ₁.FlatAt l (CellUT.immOf s v χ h) ↔ ρ₂.FlatAt l (CellUT.immOf s v χ h)

/-- Clause `mut ⇔ mut` of `↭`: `β̄` and `P̂` fixed, value and witness free on each side. -/
def ResUT.UpdMut (ρ₁ ρ₂ : ResUT Loc Val K) : Prop :=
  ∀ (l : Loc) (b : TSet) [Fact (K.Anti b)] (P : Val → SPropST Loc Val K b),
    (∃ (v : Val) (χ : ResUT Loc Val K) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
        ρ₁.FlatAt l (CellUT.mutOf b v χ h P hw)) ↔
    (∃ (v : Val) (χ : ResUT Loc Val K) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
        ρ₂.FlatAt l (CellUT.mutOf b v χ h P hw))

/-- `ρ₁ ↭ ρ₂`, unguarded. -/
def ResUT.Upd (ρ₁ ρ₂ : ResUT Loc Val K) : Prop := ρ₁.UpdImm ρ₂ ∧ ρ₁.UpdMut ρ₂

/-- `ρ₁ ↭ ρ₂`, guarded by `✓ρ₁ ∧ ✓ρ₂`. -/
def ResUT.UpdV (ρ₁ ρ₂ : ResUT Loc Val K) : Prop := ρ₁.Upd ρ₂ ∧ ρ₁.Valid ∧ ρ₂.Valid

/-! ### Definitions 6.1 and 6.2 -/

/-- `⦇ρ⦈_○ = σ`, Definition 6.1. -/
def ResUT.FlatR (ρ σ : ResUT Loc Val K) : Prop :=
  ∃ a e, AgWT ρ a ∧ ExRT ρ e ∧ ResUT.CompR a e σ

/-- `ψ ∼ ψ′`, Definition 6.2, with the `mut` cell's lifetime set for its lifetime. -/
def CellUT.Sim (ψ ψ' : CellUT Loc Val K) : Prop :=
  (∃ (b : TSet) (_ : Fact (K.Anti b)) (P : Val → SPropST Loc Val K b),
      (∃ (v : Val) (χ : ResUT Loc Val K) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
          ψ = CellUT.mutOf b v χ h P hw) ∧
      (∃ (v : Val) (χ : ResUT Loc Val K) (h : χ.InStratum b) (hw : P v ⟨χ, h⟩),
          ψ' = CellUT.mutOf b v χ h P hw)) ∨
  (∃ (s : TSet) (v : Val) (χ : ResUT Loc Val K) (h : χ.InStratum s),
      ψ = CellUT.immOf s v χ h ∧ ψ' = CellUT.immOf s v χ h)

theorem CellUT.Sim.refl {ψ : CellUT Loc Val K} (hk : ψ.kind ≠ Kind.own) : CellUT.Sim ψ ψ := by
  rcases CellUT.rep ψ with ⟨v, rfl⟩ | ⟨s, v, χ, hh, rfl⟩ | ⟨b, a, v, χ, hh, P, hw, rfl⟩
  · exact absurd (by simp : (CellUT.ownOf (K := K) (Loc := Loc) v).kind = Kind.own) hk
  · exact Or.inr ⟨s, v, χ, hh, rfl, rfl⟩
  · exact Or.inl ⟨b, a, P, ⟨v, χ, hh, hw, rfl⟩, ⟨v, χ, hh, hw, rfl⟩⟩

/-- `ρ∣imm,mut`. -/
def ResUT.borrowPart (ρ : ResUT Loc Val K) : ResUT Loc Val K :=
  ρ.restrictOn (fun k => !(k == Kind.own))

/-- `ρ∣own,mut`. -/
def ResUT.exclPart (ρ : ResUT Loc Val K) : ResUT Loc Val K :=
  ρ.restrictOn (fun k => !(k == Kind.imm))

/-- The form `[TR]` §6's proofs unfold `↭` to. -/
def ResUT.SimForm (σ₁ σ₂ : ResUT Loc Val K) : Prop :=
  (∀ l : Loc, (∃ ψ, σ₁.borrowPart.get l = some ψ) ↔
      (∃ ψ, σ₂.borrowPart.get l = some ψ)) ∧
  (∀ (l : Loc) (ψ₁ : CellUT Loc Val K), σ₁.borrowPart.get l = some ψ₁ →
      ∃ ψ₂, σ₂.get l = some ψ₂ ∧ CellUT.Sim ψ₁ ψ₂)


end BoCa.Fig16.Tree

end

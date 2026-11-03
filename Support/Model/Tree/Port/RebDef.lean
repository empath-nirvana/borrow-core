import Support.Model.Tree.Port.Six27

/-!
# `reb_α` (row 5.28) and `↺_α` (row 5.47) at the tree-stratified carrier

`[spec §62]`. `Paper/S5_Model/Definitions.lean`'s `ResU.RebAt`, `ResU.Reb` and `BoLo.reborrow`, read at
`CellUT K`. The places that change, each a reading of the tree carrier already named in
`Tree/Carrier.lean`:

* `@ρ ⊐ α` and `p/ℓ ∈ Res_{⊔{α}}`: the stratum `{α}` (`TSet.single α`), which is `Res_α` at the
  chain.
* The `mut` clause quantifies over the cell's antichain `b` with its antichain fact, as
  `CellUT.mutOf` takes it.
* The `imm` clause's "nonempty subset of the lifetimes" (`∀ x, t.mem x → s.mem x`) is
  `t.set ⊆ s.set`; `TSet`s are nonempty.

Row 5.64's `ρ|dom(σ)` and `ρ/dom(σ)` compare no lifetimes and are transcribed as printed.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

variable {Loc Val : Type} {K : WCactus}

/-- The body of `reb_α`'s `∀ ℓ ∈ dom(π), v, ρ″` at `ℓ` and its piece `p = π(ℓ)`, in the printed
order: own, mut, imm. -/
def ResUT.RebAt (α : Life) (ρ ρ' : ResUT Loc Val K) (l : Loc) (p : ResUT Loc Val K) : Prop :=
  (∃ ψ, p.get l = some ψ) ∧
  (∀ v : Val, ρ.get l = some (CellUT.ownOf v) →
      ∃ h : (p.del l).InStratum (TSet.single α),
        ρ'.get l = some (CellUT.immOf (TSet.single α) v (p.del l) h)) ∧
  (∀ (b : TSet) [Fact (K.Anti b)] (v : Val) (χ : ResUT Loc Val K) (hb : χ.InStratum b)
      (P : Val → SPropST Loc Val K b) (hw : P v ⟨χ, hb⟩),
      ρ.get l = some (CellUT.mutOf b v χ hb P hw) →
        (∃ h : χ.InStratum (TSet.single α),
            ρ'.get l = some (CellUT.immOf (TSet.single α) v χ h)) ∧
        ResUT.Dom p [l]) ∧
  (∀ (s : TSet) (v : Val) (χ : ResUT Loc Val K) (h : χ.InStratum s),
      ρ.get l = some (CellUT.immOf s v χ h) →
        (∃ (t : TSet) (ht : χ.InStratum t), t.set ⊆ s.set ∧
            ρ'.get l = some (CellUT.immOf t v χ ht)) ∧ ResUT.Dom p [l])

/-- `ρ′ ∈ reb_α(ρ)`: `@ρ ⊐ α`, `π` as a list of pairs over `dom(ρ′)`, `ρ ≥ ⨀_● π(ℓ)`, and
`ResUT.RebAt` at each member. -/
def ResUT.Reb (α : Life) (ρ ρ' : ResUT Loc Val K) : Prop :=
  ρ.InStratum (TSet.single α) ∧
  ∃ (π : List (Loc × ResUT Loc Val K)) (b : ResUT Loc Val K),
    ρ'.Dom (π.map Prod.fst) ∧
    BigCompT CellUT.CompatS CellUT.CompS (π.map Prod.snd) b ∧
    ResUT.Le b ρ ∧
    ∀ l p, (l, p) ∈ π → ResUT.RebAt α ρ ρ' l p

/-- `ρ|dom(σ)` (row 5.64). -/
def ResUT.restrictDom (ρ σ : ResUT Loc Val K) : ResUT Loc Val K where
  get := fun l => if (σ.get l).isSome then ρ.get l else none
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l hl => hd l (fun e => hl ?_)⟩
    show (if (σ.get l).isSome then ρ.get l else none) = none
    rw [e]; exact ite_self none

/-- `ρ/dom(σ)` (row 5.64). -/
def ResUT.delDom (ρ σ : ResUT Loc Val K) : ResUT Loc Val K where
  get := fun l => if (σ.get l).isSome then none else ρ.get l
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l hl => hd l (fun e => hl ?_)⟩
    show (if (σ.get l).isSome then none else ρ.get l) = none
    rw [e]; exact ite_self none

end BoCa.Fig16.Tree

namespace BoCa.Fig16.Tree.BoLo
open BoCa.Fig16 BoCa.Fig16.Tree

variable {Loc Val : Type} {K : WCactus}

/-- `↻_α P` (row 5.47). -/
def reborrow (α : Life) (P : ResUT Loc Val K → Prop) : ResUT Loc Val K → Prop :=
  fun ρ => ∃ ρ', ResUT.Reb α ρ ρ' ∧ P ρ'

end BoCa.Fig16.Tree.BoLo

end

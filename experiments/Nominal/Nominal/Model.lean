import Nominal.Action
import Support.Dynamics.Machine

/-!
# Nominal — the printed model over the nominal carrier

`Paper/S5_Model`'s operations and propositions (`[TR]` pp. 5–6), on `Carrier.lean`'s cells:

* `ψ₁ ▶◀ ψ₂` and `ψ₁ ● ψ₂` (`CellU.CompatS`, `CellU.CompS`): two `imm` cells at one value and
  witness compose, their lifetime sets united;
* `ψ₁ ○ ψ₂` (`CellU.CompR`), the five printed clauses;
* the schema `ρ₁ ◐ ρ₂` (`Comp`), `ρ∣ι`, `⨀`, the walks `ex(ρ)` and `ag(ρ)`, `⦇ρ⦈`, `✓ρ`, `⟦ρ⟧`,
  `ρ₁ # ρ₂`, `↭`, `ρ⁺∣own = ∅`;
* `⌜−⌝`, `emp`, `⋆`, `─⋆`, `∃`, `ℓ ↦ v`, and the printed `wp` (row 5.33), over `BoLo.Steps`.

A cell's data (`kind`, `erase`, `wit`, `lts`, `pu`) determines it (`CellU.ext_data`), and the
cell-level relations are written on that data; `compatS_iff_immOf`, `compS_iff_immOf` give the
printed `immOf` forms.

**Changes from `Paper/S5_Model`**, each where the print uses a chain:

| print | here | why |
|---|---|---|
| `imm(ᾱ, v, ρ : Res_⊔ᾱ)` | `ρ : Res_ᾱ` | `⊔ᾱ` need not exist; `Res_⊔ᾱ` is "strictly outlives every member" |
| `ᾱ₁ ∪ ᾱ₂` with `⊓`, `⊔` recomputed | `Finset` union | `⊓`, `⊔` are not stored |
| `○` clause 3: `mut(α ⊓ β, …)` | only for comparable `α`, `β`, at the shorter | `α ⊓ β` need not exist |
| `↭`'s `mut` clause at `P̂ : Val → SProp_β` | `P̂` read on the union (`pu`) | `ofS` is injective at each `β` |

Everything else is the print's: the walks, `⦇ρ⦈ ≜ ex(ρ)_● ● ag(ρ)`, `✓`, `⟦ρ⟧`, `#`, `↭` guarded,
and `wp` with the printed `→*`. Core's typed world (`TW`, tagged record lists, allocator runs in
`wpTS`) is not ported; see the README.
-/

noncomputable section
open Classical

namespace Nominal
open BoCa
open BoCa.Fig16 (PMap Kind)

set_option linter.unusedSectionVars false

variable {L : Type} [PartialOrder L] [WellFoundedGT L]

/-! ### Cells -/

/-- `ψ₁ ▶◀ ψ₂`: two `imm` cells at one value and witness. -/
def CellU.CompatS (ψ₁ ψ₂ : CellU L) : Prop :=
  ψ₁.kind = .imm ∧ ψ₂.kind = .imm ∧ ψ₁.erase = ψ₂.erase ∧ ψ₁.wit = ψ₂.wit

/-- `ψ₁ ● ψ₂ = ψ`: the `imm` cell at the union of the lifetime sets. -/
def CellU.CompS (ψ₁ ψ₂ ψ : CellU L) : Prop :=
  CellU.CompatS ψ₁ ψ₂ ∧ ψ.kind = .imm ∧ ψ.erase = ψ₁.erase ∧ ψ.wit = ψ₁.wit ∧
    ψ.lts = ψ₁.lts ∪ ψ₂.lts

/-- `ψ` is `mut(b, v, ρ, P)`. -/
def CellU.IsMut (ψ : CellU L) (b : L) (v : Val) (ρ : ResU L) (P : Val → ResU L → Prop) : Prop :=
  ψ.kind = .mut ∧ ψ.lts = {b} ∧ ψ.erase = v ∧ ψ.wit = ρ ∧ ψ.pu = P

/-- `ψ` is `imm(s, v, ρ)`. -/
def CellU.IsImm (ψ : CellU L) (s : Finset L) (v : Val) (ρ : ResU L) : Prop :=
  ψ.kind = .imm ∧ ψ.lts = s ∧ ψ.erase = v ∧ ψ.wit = ρ

/-- `ψ` is `own(v)`. -/
def CellU.IsOwn (ψ : CellU L) (v : Val) : Prop := ψ.kind = .own ∧ ψ.erase = v

/-- `ψ₁ ○ ψ₂ = ψ`, the five printed clauses. Clause (3), `mut(α ⊓ β, v, ρ, P̂ ∧ Q̂)`, is taken
when `α` and `β` are comparable, at the shorter. -/
inductive CellU.CompR : CellU L → CellU L → CellU L → Prop where
  | same (ψ : CellU L) : CellU.CompR ψ ψ ψ
  | strict {ψ₁ ψ₂ ψ : CellU L} : CellU.CompS ψ₁ ψ₂ ψ → CellU.CompR ψ₁ ψ₂ ψ
  | mutMutL {ψ₁ ψ₂ ψ : CellU L} {a b : L} {v : Val} {ρ : ResU L} {P Q : Val → ResU L → Prop} :
      ψ₁.IsMut a v ρ P → ψ₂.IsMut b v ρ Q → a ≤ b → ψ.IsMut a v ρ (fun u σ => P u σ ∧ Q u σ) →
      CellU.CompR ψ₁ ψ₂ ψ
  | mutMutR {ψ₁ ψ₂ ψ : CellU L} {a b : L} {v : Val} {ρ : ResU L} {P Q : Val → ResU L → Prop} :
      ψ₁.IsMut a v ρ P → ψ₂.IsMut b v ρ Q → b ≤ a → ψ.IsMut b v ρ (fun u σ => P u σ ∧ Q u σ) →
      CellU.CompR ψ₁ ψ₂ ψ
  | mutOwn {ψ₁ ψ₂ : CellU L} {a : L} {v : Val} {ρ : ResU L} {P : Val → ResU L → Prop} :
      ψ₁.IsMut a v ρ P → ψ₂.IsOwn v → CellU.CompR ψ₁ ψ₂ ψ₁
  | ownMut {ψ₁ ψ₂ : CellU L} {a : L} {v : Val} {ρ : ResU L} {P : Val → ResU L → Prop} :
      ψ₁.IsOwn v → ψ₂.IsMut a v ρ P → CellU.CompR ψ₁ ψ₂ ψ₂
  | immOwn {ψ₁ ψ₂ : CellU L} {s : Finset L} {v : Val} {ρ : ResU L} :
      ψ₁.IsImm s v ρ → ψ₂.IsOwn v → CellU.CompR ψ₁ ψ₂ ψ₁
  | ownImm {ψ₁ ψ₂ : CellU L} {s : Finset L} {v : Val} {ρ : ResU L} :
      ψ₁.IsOwn v → ψ₂.IsImm s v ρ → CellU.CompR ψ₁ ψ₂ ψ₂
  | immMut {ψ₁ ψ₂ : CellU L} {s : Finset L} {b : L} {v : Val} {ρ : ResU L}
      {P : Val → ResU L → Prop} :
      ψ₁.IsImm s v ρ → ψ₂.IsMut b v ρ P → CellU.CompR ψ₁ ψ₂ ψ₁
  | mutImm {ψ₁ ψ₂ : CellU L} {s : Finset L} {b : L} {v : Val} {ρ : ResU L}
      {P : Val → ResU L → Prop} :
      ψ₁.IsMut b v ρ P → ψ₂.IsImm s v ρ → CellU.CompR ψ₁ ψ₂ ψ₂

/-- `ψ₁ ⋈ ψ₂`, the domain of `○`. -/
def CellU.CompatR (ψ₁ ψ₂ : CellU L) : Prop := ∃ ψ, CellU.CompR ψ₁ ψ₂ ψ

theorem CellU.compatS_iff_immOf (ψ₁ ψ₂ : CellU L) : CellU.CompatS ψ₁ ψ₂ ↔
    ∃ (s₁ s₂ : Finset L) (h₁' : s₁.Nonempty) (h₂' : s₂.Nonempty) (v : Val) (ρ : ResU L)
      (h₁ : ρ.InStratum s₁) (h₂ : ρ.InStratum s₂),
      ψ₁ = CellU.immOf s₁ h₁' v ρ h₁ ∧ ψ₂ = CellU.immOf s₂ h₂' v ρ h₂ := by
  constructor
  · rintro ⟨k₁, k₂, he, hw⟩
    cases ψ₁ with
    | own _ => cases k₁
    | «mut» _ => cases k₁
    | imm i₁ =>
      cases ψ₂ with
      | own _ => cases k₂
      | «mut» _ => cases k₂
      | imm i₂ =>
        have h₂ : (CellU.imm i₁).wit.InStratum i₂.ls := hw ▸ CellU.wit_inStratum_imm i₂
        refine ⟨i₁.ls, i₂.ls, i₁.hne, i₂.hne, i₁.v, (CellU.imm i₁).wit,
          CellU.wit_inStratum_imm i₁, h₂, CellU.imm_eta i₁, ?_⟩
        rw [CellU.imm_eta i₂]
        exact CellU.ext_data rfl he.symm (by rw [CellU.wit_immOf, CellU.wit_immOf, hw]; rfl) rfl rfl
  · rintro ⟨s₁, s₂, h₁', h₂', v, ρ, h₁, h₂, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl, by simp⟩

theorem CellU.compS_iff_immOf (ψ₁ ψ₂ ψ : CellU L) : CellU.CompS ψ₁ ψ₂ ψ ↔
    ∃ (s₁ s₂ : Finset L) (h₁' : s₁.Nonempty) (h₂' : s₂.Nonempty) (v : Val) (ρ : ResU L)
      (h₁ : ρ.InStratum s₁) (h₂ : ρ.InStratum s₂) (h₃ : ρ.InStratum (s₁ ∪ s₂)),
      ψ₁ = CellU.immOf s₁ h₁' v ρ h₁ ∧ ψ₂ = CellU.immOf s₂ h₂' v ρ h₂ ∧
      ψ = CellU.immOf (s₁ ∪ s₂) (h₁'.mono Finset.subset_union_left) v ρ h₃ := by
  constructor
  · rintro ⟨hc, k, he, hw, hl⟩
    obtain ⟨s₁, s₂, h₁', h₂', v, ρ, h₁, h₂, rfl, rfl⟩ := (CellU.compatS_iff_immOf _ _).mp hc
    have h₃ : ρ.InStratum (s₁ ∪ s₂) := by
      intro l c e
      have a₁ := h₁ l c e
      have a₂ := h₂ l c e
      cases c with
      | own _ => trivial
      | imm i =>
          refine ⟨a₁.1, fun t ht s hs => ?_⟩
          rcases Finset.mem_union.mp hs with hs | hs
          · exact a₁.2 t ht s hs
          · exact a₂.2 t ht s hs
      | «mut» m =>
          refine ⟨a₁.1, fun t ht s hs => ?_⟩
          rcases Finset.mem_union.mp hs with hs | hs
          · exact a₁.2 t ht s hs
          · exact a₂.2 t ht s hs
    refine ⟨s₁, s₂, h₁', h₂', v, ρ, h₁, h₂, h₃, rfl, rfl, ?_⟩
    refine CellU.ext_data (by rw [k]; rfl) he (by rw [hw]; simp) (by rw [hl]; rfl) ?_
    cases ψ with
    | own _ => cases k
    | «mut» _ => cases k
    | imm _ => rfl
  · rintro ⟨s₁, s₂, h₁', h₂', v, ρ, h₁, h₂, h₃, rfl, rfl, rfl⟩
    exact ⟨⟨rfl, rfl, rfl, by simp⟩, rfl, rfl, by simp, rfl⟩

/-! ### Resources -/

/-- `ρ₁ ▶◁ ρ₂`, the pointwise lift of a cell-level relation. -/
def Compat (C : CellU L → CellU L → Prop) (ρ₁ ρ₂ : ResU L) : Prop :=
  ∀ l ψ₁ ψ₂, ρ₁.get l = some ψ₁ → ρ₂.get l = some ψ₂ → C ψ₁ ψ₂

/-- The three pieces of `ρ₁ ◐ ρ₂` at one location. -/
def OptComp (C : CellU L → CellU L → CellU L → Prop) :
    Option (CellU L) → Option (CellU L) → Option (CellU L) → Prop
  | none, none, o => o = none
  | some ψ, none, o => o = some ψ
  | none, some ψ, o => o = some ψ
  | some ψ₁, some ψ₂, o => ∃ ψ, o = some ψ ∧ C ψ₁ ψ₂ ψ

/-- `ρ₁ ◐ ρ₂ = ρ`, guarded by `ρ₁ ▸◁ ρ₂`. -/
def Comp (R : CellU L → CellU L → Prop) (C : CellU L → CellU L → CellU L → Prop)
    (ρ₁ ρ₂ ρ : ResU L) : Prop :=
  Compat R ρ₁ ρ₂ ∧ ∀ l, OptComp C (ρ₁.get l) (ρ₂.get l) (ρ.get l)

/-- `ρ₁ ● ρ₂ = ρ`. -/
abbrev ResU.CompS (ρ₁ ρ₂ ρ : ResU L) : Prop := Comp CellU.CompatS CellU.CompS ρ₁ ρ₂ ρ

/-- `ρ₁ ○ ρ₂ = ρ`. -/
abbrev ResU.CompR (ρ₁ ρ₂ ρ : ResU L) : Prop := Comp CellU.CompatR CellU.CompR ρ₁ ρ₂ ρ

/-- `ρ∣ι`. -/
def ResU.restrict (ρ : ResU L) (k : Kind) : ResU L where
  get := fun l => (ρ.get l).bind fun ψ => if ψ.kind = k then some ψ else none
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l hl => hd l (fun e => hl ?_)⟩
    show (ρ.get l).bind _ = none
    rw [e]; rfl

/-- `d` lists the locations of `ρ` carrying a cell of tag `k`, each once. -/
def ResU.Sites (ρ : ResU L) (k : Kind) (d : List Loc) : Prop :=
  d.Nodup ∧ ∀ l, l ∈ d ↔ ∃ ψ, ρ.get l = some ψ ∧ ψ.kind = k

/-- `⨀_◐`, folded right with `∅` at the end. -/
inductive BigComp (R : CellU L → CellU L → Prop) (C : CellU L → CellU L → CellU L → Prop) :
    List (ResU L) → ResU L → Prop where
  | nil : BigComp R C [] PMap.empty
  | cons {σ τ ρ : ResU L} {σs : List (ResU L)} :
      BigComp R C σs τ → Comp R C σ τ ρ → BigComp R C (σ :: σs) ρ

mutual
/-- `ex(ρ)_◐ = σ`, the exclusive walk. -/
inductive ExW (R : CellU L → CellU L → Prop) (C : CellU L → CellU L → CellU L → Prop) :
    ResU L → ResU L → Prop where
  | mk {ρ σ nm b : ResU L} {w : List (Loc × ResU L)}
      (hs : ResU.Sites ρ Kind.mut (w.map Prod.fst))
      (hw : ExWits R C ρ w)
      (hb : BigComp R C (w.map Prod.snd) b)
      (hnm : Comp R C (ρ.restrict Kind.own) (ρ.restrict Kind.mut) nm)
      (hσ : Comp R C nm b σ) :
      ExW R C ρ σ

/-- `{ex(ρ′)_◐ ∣ ∃ℓ. ρ(ℓ) = mut(_,_,ρ′,_)}`, tagged by location. -/
inductive ExWits (R : CellU L → CellU L → Prop) (C : CellU L → CellU L → CellU L → Prop) :
    ResU L → List (Loc × ResU L) → Prop where
  | nil {ρ : ResU L} : ExWits R C ρ []
  | cons {ρ e : ResU L} {l : Loc} {w : List (Loc × ResU L)}
      (ψ : CellU L) (hψ : ρ.get l = some ψ) (hk : ψ.kind = Kind.mut)
      (he : ExW R C ψ.wit e) (hw : ExWits R C ρ w) :
      ExWits R C ρ ((l, e) :: w)
end

/-- `ex(ρ)_●`. -/
abbrev ExS (ρ σ : ResU L) : Prop := ExW CellU.CompatS CellU.CompS ρ σ

/-- `ex(ρ)_○`. -/
abbrev ExR (ρ σ : ResU L) : Prop := ExW CellU.CompatR CellU.CompR ρ σ

mutual
/-- `ag(ρ) = σ`, the aliasable walk. -/
inductive AgW : ResU L → ResU L → Prop where
  | mk {ρ σ a bm bi : ResU L} {wm wi : List (Loc × ResU L)}
      (hsm : ResU.Sites ρ Kind.mut (wm.map Prod.fst))
      (hsi : ResU.Sites ρ Kind.imm (wi.map Prod.fst))
      (hwm : AgWitsM ρ wm)
      (hwi : AgWitsI ρ wi)
      (hbm : BigComp CellU.CompatR CellU.CompR (wm.map Prod.snd) bm)
      (hbi : BigComp CellU.CompatR CellU.CompR (wi.map Prod.snd) bi)
      (ha : ResU.CompR (ρ.restrict Kind.imm) bm a)
      (hσ : ResU.CompR a bi σ) :
      AgW ρ σ

/-- `{ag(ρ′) ∣ ∃ℓ. ρ(ℓ) = mut(_,_,ρ′,_)}`, tagged by location. -/
inductive AgWitsM : ResU L → List (Loc × ResU L) → Prop where
  | nil {ρ : ResU L} : AgWitsM ρ []
  | cons {ρ e : ResU L} {l : Loc} {w : List (Loc × ResU L)}
      (ψ : CellU L) (hψ : ρ.get l = some ψ) (hk : ψ.kind = Kind.mut)
      (he : AgW ψ.wit e) (hw : AgWitsM ρ w) :
      AgWitsM ρ ((l, e) :: w)

/-- `{ex(ρ′)_○ ○ ag(ρ′) ∣ ∃ℓ. ρ(ℓ) = imm(_,_,ρ′)}`, tagged by location. -/
inductive AgWitsI : ResU L → List (Loc × ResU L) → Prop where
  | nil {ρ : ResU L} : AgWitsI ρ []
  | cons {ρ p : ResU L} {l : Loc} {w : List (Loc × ResU L)}
      (ψ : CellU L) (hψ : ρ.get l = some ψ) (hk : ψ.kind = Kind.imm)
      (e a : ResU L) (hex : ExR ψ.wit e) (hag : AgW ψ.wit a)
      (hp : ResU.CompR e a p) (hw : AgWitsI ρ w) :
      AgWitsI ρ ((l, p) :: w)
end

/-- `⦇ρ⦈ = σ`. -/
def ResU.Flat (ρ σ : ResU L) : Prop := ∃ e a, ExS ρ e ∧ AgW ρ a ∧ ResU.CompS e a σ

/-- `✓ρ`. -/
def ResU.Valid (ρ : ResU L) : Prop := ∃ σ, ResU.Flat ρ σ

/-- `⟦ρ⟧ = m`. -/
def ResU.Lower (ρ : ResU L) (m : Loc → Option Val) : Prop :=
  ∃ σ, ResU.Flat ρ σ ∧ ∀ l, m l = (σ.get l).map CellU.erase

/-- `ρ₁ # ρ₂`. -/
def ResU.Hash (ρ₁ ρ₂ : ResU L) : Prop :=
  Compat CellU.CompatS ρ₁ ρ₂ ∧ ∃ ρ, ResU.CompS ρ₁ ρ₂ ρ ∧ ResU.Valid ρ

/-- `⦇ρ⦈(ℓ) = ψ`. -/
def ResU.FlatAt (ρ : ResU L) (l : Loc) (ψ : CellU L) : Prop :=
  ∃ σ, ResU.Flat ρ σ ∧ σ.get l = some ψ

/-- `↭`, clause `imm ⇔ imm`: lifetimes, value and witness fixed. -/
def ResU.UpdImm (ρ₁ ρ₂ : ResU L) : Prop :=
  ∀ l ψ, ψ.kind = .imm → (ρ₁.FlatAt l ψ ↔ ρ₂.FlatAt l ψ)

/-- `↭`, clause `mut ⇔ mut`: `β` and `P̂` fixed, value and witness free. -/
def ResU.UpdMut (ρ₁ ρ₂ : ResU L) : Prop :=
  ∀ (l : Loc) (b : L) (P : Val → ResU L → Prop),
    (∃ ψ, ρ₁.FlatAt l ψ ∧ ψ.kind = .mut ∧ ψ.lts = {b} ∧ ψ.pu = P) ↔
    (∃ ψ, ρ₂.FlatAt l ψ ∧ ψ.kind = .mut ∧ ψ.lts = {b} ∧ ψ.pu = P)

/-- `ρ₁ ↭ ρ₂`, guarded by `✓ρ₁ ∧ ✓ρ₂`. -/
def ResU.UpdV (ρ₁ ρ₂ : ResU L) : Prop :=
  (ρ₁.UpdImm ρ₂ ∧ ρ₁.UpdMut ρ₂) ∧ ρ₁.Valid ∧ ρ₂.Valid

/-- `ρ∣own = ∅`. -/
def NoOwn (ρ : ResU L) : Prop := ∀ l ψ, ρ.get l = some ψ → ψ.kind ≠ .own

/-! ### Propositions -/

/-- `⌜p⌝`. -/
def pureN (p : Prop) : WPropN L := fun ρ => ρ = PMap.empty ∧ p

/-- `emp`. -/
def empN : WPropN L := pureN True

/-- `P₁ ⋆ P₂`. -/
def sepN (P Q : WPropN L) : WPropN L := fun ρ => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ P ρ₁ ∧ Q ρ₂

/-- `P₁ ─⋆ P₂`. -/
def wandN (P Q : WPropN L) : WPropN L := fun ρ => ∀ ρ₁ ρ₂, P ρ₁ → ResU.CompS ρ ρ₁ ρ₂ → Q ρ₂

/-- `∃ P̂`. -/
def exN {A : Type} (Φ : A → WPropN L) : WPropN L := fun ρ => ∃ x, Φ x ρ

/-- `ℓ ↦ v`. -/
def ptoOwnN (l : Loc) (v : Val) : WPropN L := fun ρ => ρ = ResU.single l (CellU.own v)

scoped notation "⌜" p "⌝ₙ" => pureN p
scoped infixr:35 " ⋆ₙ " => sepN
scoped infixr:27 " ─⋆ₙ " => wandN

/-! ### `wp` -/

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- `wp (e) {Q̂}` (`[TR]` p. 6, row 5.33). -/
def wpN (e : Expr) (Q : Val → WPropN L) : WPropN L := fun ρ =>
  ∀ ρf : ResU L, ρf.Hash ρ →
    ∃ (ρ' ρp fρ fρ' fρ'p πr : ResU L) (v : Val) (μ μ' : BoCa.BoLo.Heap),
      ρ'.Hash ρf ∧
      ResU.CompS ρf ρ' fρ' ∧ ρp.Hash fρ' ∧
      ResU.CompS ρf ρ fρ ∧ fρ.Lower μ ∧
      ResU.CompS fρ' ρp fρ'p ∧ fρ'p.Lower μ' ∧
      BoCa.BoLo.Steps (ℍ := ℍ) μ e μ' (.val v) ∧
      ResU.CompS ρ' ρp πr ∧ ρ.UpdV πr ∧
      NoOwn ρp ∧
      Q v ρ'

end Nominal

end

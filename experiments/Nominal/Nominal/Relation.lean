import Nominal.ModelEquiv
import Core.Relation

/-!
# Nominal — Core's relation over the nominal carrier, at `DenseCarrier`'s fragment and `Imm`

The value relation `vN` and the computation relation `cN` at `1`, `⊗`, `U`, `Ref`, `[@a]`, `Imm`,
`Mut`, `F`, `⊸`, `⊤`, `∀`, over `Model.lean`'s carrier and printed `wp`, with lifetimes in any
partial order `L` with `⊤` and no infinite ascending chain (`Lft = WithTop Atom` is one). The
types and terms are Core's (`VTy`, `CTy`, `Expr`, `forceE`).

**Every change from Core's clauses (`Core/Relation.lean`), and why.**

| Core | here | why |
|---|---|---|
| `δ : LSub` (values `ℕ`), `Life.interp` | `δ : LSubN L`, `interpN` | lifetimes are `L`'s |
| `@(a ⊔ b)δ = max`, `@(a ⊓ b)δ = min` | the longer / shorter when comparable, else undefined | `⊔`, `⊓` need not exist |
| `∀ α : Life` | `∀ α : L` | the `∀` ranges over the partial order |
| `[α]P`: `ρ ∈ Res_α` | `boxE`: no cell of `ρ` at or beneath `α` (reading (b)) | `[@a] T` is what survives the end of `@a`; on a chain it is `ρ ∈ Res_α` |
| `ptoMutS`: `α ⊑ b`, payload `⊆ Res_b` | `ptoMutN`: `α ≤ b`, payload `⊆ Res_{b}` (reading (a)) | as Core; strata are set-indexed |
| `ptoImmS`: `α ⊑ ⊓β̄` | `ptoImmN`: `α ≤ m` for every `m ∈ β̄` | `⊓β̄` need not exist |
| records `ls`, `Ext` at `U`, `ls₀` at `Mut`, `CohE` at `Imm`, `wpTS` | none; the printed `wp` | the typed world is not ported |
| the type-variable environment `η`, `μ`, `ν`, rows | not in the fragment | — |

The observable view of an `Imm` payload (`b = false`, `U` read as `True`) is Core's.
-/

noncomputable section
open Classical

namespace Nominal
open BoCa
open BoCa.Fig16 (PMap Kind)
open BoCa.Fig16.LogRel.Core (VTy CTy forceE)
open BoCa.Lifetime (LifeVar LifeCtx)

set_option linter.unusedSectionVars false

/-! ### Readings of lifetime variables -/

/-- `δ : LifeVar ⇀ L`, an association list. -/
structure LSubN (L : Type) where
  entries : List (LifeVar × L)

namespace LSubN
variable {L L' L'' : Type}

def find? (δ : LSubN L) (x : LifeVar) : Option L := Lifetime.assocFind x δ.entries

def extend (δ : LSubN L) (x : LifeVar) (α : L) : LSubN L := ⟨(x, α) :: δ.entries⟩

/-- `δ` moved by a map of lifetimes. -/
def map (φ : L → L') (δ : LSubN L) : LSubN L' := ⟨δ.entries.map fun p => (p.1, φ p.2)⟩

theorem find?_extend (δ : LSubN L) (x : LifeVar) (α : L) (y : LifeVar) :
    (δ.extend x α).find? y = if x = y then some α else δ.find? y := by
  simp only [find?, extend, Lifetime.assocFind]

theorem find?_extend_self (δ : LSubN L) (x : LifeVar) (α : L) :
    (δ.extend x α).find? x = some α := by
  rw [find?_extend, if_pos rfl]

theorem find?_extend_ne (δ : LSubN L) {x y : LifeVar} (α : L) (h : x ≠ y) :
    (δ.extend x α).find? y = δ.find? y := by
  rw [find?_extend, if_neg h]

theorem assocFind_map (φ : L → L') (x : LifeVar) :
    ∀ es : List (LifeVar × L),
      Lifetime.assocFind x (es.map fun p => (p.1, φ p.2)) = (Lifetime.assocFind x es).map φ
  | [] => rfl
  | (y, v) :: t => by
      simp only [List.map_cons, Lifetime.assocFind]
      split_ifs
      · rfl
      · exact assocFind_map φ x t

theorem find?_map (φ : L → L') (δ : LSubN L) (x : LifeVar) :
    (δ.map φ).find? x = (δ.find? x).map φ :=
  assocFind_map φ x δ.entries

theorem map_extend (φ : L → L') (δ : LSubN L) (x : LifeVar) (α : L) :
    (δ.extend x α).map φ = (δ.map φ).extend x (φ α) := rfl

theorem map_map (φ : L → L') (ψ : L' → L'') (δ : LSubN L) :
    (δ.map φ).map ψ = δ.map (ψ ∘ φ) := by
  simp [map, Function.comp_def]

theorem map_congr {φ ψ : L → L'} {δ : LSubN L} (h : ∀ p ∈ δ.entries, φ p.2 = ψ p.2) :
    δ.map φ = δ.map ψ := by
  simp only [map, LSubN.mk.injEq]
  exact List.map_congr_left fun p hp => by rw [h p hp]

theorem map_id (δ : LSubN L) : δ.map (fun x => x) = δ := by
  cases δ; simp [map]

end LSubN

section Interp
variable {L : Type} [PartialOrder L] [OrderTop L]

/-- The longer of two comparable lifetimes; undefined on incomparable ones. -/
def joinN (m n : L) : Option L := if n ≤ m then some m else if m ≤ n then some n else none

/-- The shorter of two comparable lifetimes; undefined on incomparable ones. -/
def meetN (m n : L) : Option L := if m ≤ n then some m else if n ≤ m then some n else none

/-- `@aδ` over `L`. -/
def interpN (δ : LSubN L) : Lifetime.Life → Option L
  | .var x => δ.find? x
  | .top => some ⊤
  | .join a b => (interpN δ a).bind fun m => (interpN δ b).bind fun n => joinN m n
  | .meet a b => (interpN δ a).bind fun m => (interpN δ b).bind fun n => meetN m n

/-- `@aδ` as a connective's argument. -/
def atLifeN [WellFoundedGT L] (δ : LSubN L) (a : Lifetime.Life) (F : L → WPropN L) :
    WPropN L :=
  fun ρ => ∃ α, interpN δ a = some α ∧ F α ρ

/-- `α ⊏ @bδ`. -/
def LtLifeN (δ : LSubN L) (b : Lifetime.Life) (α : L) : Prop :=
  ∃ β, interpN δ b = some β ∧ α < β

/-- `δ ∈ ⟦Δ⟧` over `L`. -/
def ModelsN (Δ : LifeCtx) (δ : LSubN L) : Prop :=
  ∀ x u, Δ.find? x = some u → ∃ m n, δ.find? x = some m ∧ interpN δ u = some n ∧ m < n

end Interp

/-! ### The relation -/

variable {L : Type} [PartialOrder L] [OrderTop L] [WellFoundedGT L]
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- `ℓ ↦ M_α P̂`: a `mut` cell at `b ⊒ α` storing `P̂`; `P̂` holds only in `Res_{b}`. -/
def ptoMutN (l : Loc) (α : L) (P : Val → WPropN L) : WPropN L := fun ρ =>
  ∃ (b : L) (u : Val) (σ : ResU L) (h : σ.InStratum {b}) (hw : P u σ),
    α ≤ b ∧ (∀ u' σ', P u' σ' → σ'.InStratum {b}) ∧
    ρ = ResU.single l (CellU.mutOf b u σ h P hw)

/-- `ℓ ↦ I_α P̂`: an `imm` cell `imm(β̄, u, σ)` with `α ⊑ m` for every `m ∈ β̄` whose payload
holds. -/
def ptoImmN (l : Loc) (α : L) (P : Val → WPropN L) : WPropN L := fun ρ =>
  ∃ (s : Finset L) (hs : s.Nonempty) (u : Val) (σ : ResU L) (h : σ.InStratum s),
    (∀ m ∈ s, α ≤ m) ∧ P u σ ∧ ρ = ResU.single l (CellU.immOf s hs u σ h)

mutual
/-- `𝒱⟦A⟧δ(v)`. `b = false` is the observable view an `Imm` payload is held at. -/
def vN : Bool → VTy → LSubN L → Val → WPropN L
  | _, .unit, _, v => pureN (v = .unit)
  | b, .tensor A B, δ, v =>
      exN fun v₁ => exN fun v₂ => sepN (pureN (v = .pair v₁ v₂))
        (sepN (vN b A δ v₁) (vN b B δ v₂))
  | true, .thunk C, δ, v => fun ρ => cN C δ (forceE C (.val v)) ρ
  | false, .thunk _, _, _ => fun _ => True
  | b, .ref A, δ, v =>
      exN fun ℓ => exN fun v' => sepN (pureN (v = .loc ℓ)) (sepN (ptoOwnN ℓ v') (vN b A δ v'))
  | b, .box a A, δ, v => atLifeN δ a fun α => boxE α (vN b A δ v)
  | _, .imm a A, δ, v =>
      atLifeN δ a fun α => exN fun ℓ => sepN (pureN (v = .loc ℓ)) (ptoImmN ℓ α (vN false A δ))
  | _, .mut a A, δ, v =>
      atLifeN δ a fun α => exN fun ℓ => sepN (pureN (v = .loc ℓ)) (ptoMutN ℓ α (vN true A δ))
  | _, .zero, _, _ | _, .sum _ _, _, _ | _, .bang _, _, _ | _, .unk, _, _ | _, .tvar _, _, _
  | _, .mu _, _, _ | _, .int _, _, _ | _, .fam _, _, _ | _, .opq _, _, _ => fun _ => False

/-- `𝒞⟦C⟧δ(e)`. -/
def cN : CTy → LSubN L → Expr → WPropN L
  | .ret A, δ, e => wpN (ℍ := ℍ) e (vN true A δ)
  | .arr A C, δ, e => fun ρ => ∀ v, wandN (vN true A δ v) (cN C δ (.app e (.val v))) ρ
  | .top, _, _ => fun _ => True
  | .all x c C, δ, e => fun ρ =>
      ∀ α : L, wandN (pureN (LtLifeN δ c α)) (cN C (δ.extend x α) (.app e (.val .unit))) ρ
  | .amp _ _, _, _ | .nu _, _, _ | .eff _ _ _ _ _ _ _, _, _ => fun _ => False
end

/-- `⊛_{x ∈ dom(Γ)} 𝒱⟦Γ(x)⟧δ(γ(x))`. -/
def gSepN (δ : LSubN L) : Ctx VTy → List Val → WPropN L
  | [], _ => empN
  | _ :: _, [] => empN
  | s :: Γ, v :: γ => if s.live then sepN (vN (ℍ := ℍ) true s.ty δ v) (gSepN δ Γ γ) else gSepN δ Γ γ

/-- `𝒢⟦Γ⟧δ(γ)`. -/
def gDenN (δ : LSubN L) (Γ : Ctx VTy) (γ : List Val) : WPropN L :=
  sepN (pureN (Ctx.LiveWithin Γ γ)) (gSepN (ℍ := ℍ) δ Γ γ)

/-- `Δ; Γ ⊨ e : C`. -/
def SemN (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (C : CTy) : Prop :=
  ∀ (δ : LSubN L) γ ρ, ModelsN Δ δ → gDenN (ℍ := ℍ) δ Γ γ ρ →
    cN (ℍ := ℍ) C δ (BoCa.Fig16.LogRel.substAll γ e) ρ

end Nominal

end

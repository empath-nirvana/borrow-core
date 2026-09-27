import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S5_Model.Definitions
import Support.Lifetimes.Interpretation
import Support.LogicalRelation.ClosingSubstitutions
import Support.Model.Cells
import Support.Model.Prelude
import Core.Types

/-!
# Core — frame records  `[spec §3, §4]`

`Support/TypedWorld`'s layer `Records`, with records typed at `VTy`.  The records the typed world keeps: frame records and their lineages, root, chain and `Mut` positions, coherence of a record with the world, tags, and the Kripke order `Ext`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `δ` interprets every lifetime variable free in `T` — `𝒱⟦T⟧δ` is only ever taken at
`δ ∈ 𝒟⟦Δ⟧` with `T` well formed under `Δ` (`[TR]` 6.151's statement). -/
def AdmWf : VTy → LSub → Prop := fun T δ => ∀ x, VFree x T → ∃ α, δ.find? x = some α

/-- A frame taken by `[TR]` 6.64: the location `le`, the value `v` it held, the payload
resource `R` moved into the borrow, and the `(T, δ)` with `R ∈ 𝒱⟦T⟧δ(v)`.
`[about ours: our record of 6.64's `P̂ = 𝒱⟦T⟧δ`]` -/
structure FrameRec where
  le : Loc
  v : Val
  R : WRes
  T : VTy
  δ : LSub

/-- `RefPos T v ℓ S`: the value `v` of type `T` holds, at a `Ref S` reached from `T` through
`⊗`, `⊕`, `[@a]` and the unrolling of `μ`, the location `ℓ`.  One constructor per case of `[TR]` 6.131's
induction that recurses (`⊗`: *"Apply IH"* at both components; `⊕`: *"Analogous to
`T = T₁ ⊗ T₂`"*; `[@a]`: *"Apply [] L … Apply IH"*) and the one that stops at an owned cell
(`Ref T′`).  `[about ours: the positions 6.131's induction visits, named]` -/
inductive RefPos : VTy → Val → Loc → VTy → Prop
  | ref (S : VTy) (l : Loc) : RefPos (.ref S) (Val.loc l) l S
  | tensorL {T₁ T₂ : VTy} {v₁ v₂ : Val} {l : Loc} {S : VTy} :
      RefPos T₁ v₁ l S → RefPos (.tensor T₁ T₂) (Val.pair v₁ v₂) l S
  | tensorR {T₁ T₂ : VTy} {v₁ v₂ : Val} {l : Loc} {S : VTy} :
      RefPos T₂ v₂ l S → RefPos (.tensor T₁ T₂) (Val.pair v₁ v₂) l S
  | sumL {T₁ T₂ : VTy} {v₁ : Val} {l : Loc} {S : VTy} :
      RefPos T₁ v₁ l S → RefPos (.sum T₁ T₂) (Val.inj₁ v₁) l S
  | sumR {T₁ T₂ : VTy} {v₂ : Val} {l : Loc} {S : VTy} :
      RefPos T₂ v₂ l S → RefPos (.sum T₁ T₂) (Val.inj₂ v₂) l S
  | box {a : Lifetime.Life} {T : VTy} {v : Val} {l : Loc} {S : VTy} :
      RefPos T v l S → RefPos (.box a T) v l S
  /-- A closed `μX. A` is read at its unrolling `A[μX. A/X]`. -/
  | mu {A : VTy} {v : Val} {l : Loc} {S : VTy} : (VTy.mu A).Cl 0 →
      RefPos (VTy.inst (.mu A) A) v l S → RefPos (.mu A) v l S
  /-- The leaf at `ℓ + i`, `i < n`, of a family `(ℓ, n)`.  `[spec §9]` -/
  | fam {L : VTy} {ℓ : Loc} {c : UInt32} {i : Nat} {l : Loc} {S : VTy} : i < c.toNat →
      RefPos L (Val.loc (ℓ + i)) l S → RefPos (.fam L) (Val.arr ℓ c) l S

/-- `Chain R T v p ℓ S u`: `ℓ ↦ own(u)` is in `R`, reached from `(T, v)` by a chain of
`RefPos` steps whose intermediate values are read off `R`; `S` is `ℓ`'s pointee type and `p`
the location of the chain's previous step (`none` at a first step).
`[about ours: the borrow nodes 6.131's `Ref` case produces, iterated]` -/
inductive Chain (R : WRes) : VTy → Val → Option Loc → Loc → VTy → Val → Prop
  | one {T : VTy} {v : Val} {l : Loc} {S : VTy} {u : Val} :
      RefPos T v l S → R.get l = some (CellU.ownOf u) → Chain R T v none l S u
  | step {T : VTy} {v : Val} {l₁ : Loc} {S₁ : VTy} {u₁ : Val} {p : Option Loc} {l : Loc}
      {S : VTy} {u : Val} :
      RefPos T v l₁ S₁ → R.get l₁ = some (CellU.ownOf u₁) → Chain R S₁ u₁ p l S u →
      Chain R T v (some (p.getD l₁)) l S u

/-- `MutPos T v ℓ S`: the value `v` of type `T` holds, at a `Mut @a S` reached from `T`
through `⊗`, `⊕`, `[@a]` and the unrolling of `μ`, the location `ℓ` — `[TR]` 6.131's positions that stop at a
mutable borrow (`Imm̲ 'b (Mut @a S) = Imm 'b S`, `[CONF]` Fig. 9).
`[about ours: the positions 6.131's induction visits, named]` -/
inductive MutPos : VTy → Val → Loc → VTy → Prop
  | mut (a : Lifetime.Life) (S : VTy) (l : Loc) : MutPos (.mut a S) (Val.loc l) l S
  | tensorL {T₁ T₂ : VTy} {v₁ v₂ : Val} {l : Loc} {S : VTy} :
      MutPos T₁ v₁ l S → MutPos (.tensor T₁ T₂) (Val.pair v₁ v₂) l S
  | tensorR {T₁ T₂ : VTy} {v₁ v₂ : Val} {l : Loc} {S : VTy} :
      MutPos T₂ v₂ l S → MutPos (.tensor T₁ T₂) (Val.pair v₁ v₂) l S
  | sumL {T₁ T₂ : VTy} {v₁ : Val} {l : Loc} {S : VTy} :
      MutPos T₁ v₁ l S → MutPos (.sum T₁ T₂) (Val.inj₁ v₁) l S
  | sumR {T₁ T₂ : VTy} {v₂ : Val} {l : Loc} {S : VTy} :
      MutPos T₂ v₂ l S → MutPos (.sum T₁ T₂) (Val.inj₂ v₂) l S
  | box {a : Lifetime.Life} {T : VTy} {v : Val} {l : Loc} {S : VTy} :
      MutPos T v l S → MutPos (.box a T) v l S
  /-- A closed `μX. A` is read at its unrolling `A[μX. A/X]`. -/
  | mu {A : VTy} {v : Val} {l : Loc} {S : VTy} : (VTy.mu A).Cl 0 →
      MutPos (VTy.inst (.mu A) A) v l S → MutPos (.mu A) v l S
  /-- The leaf at `ℓ + i`, `i < n`, of a family `(ℓ, n)`.  `[spec §9]` -/
  | fam {L : VTy} {ℓ : Loc} {c : UInt32} {i : Nat} {l : Loc} {S : VTy} : i < c.toNat →
      MutPos L (Val.loc (ℓ + i)) l S → MutPos (.fam L) (Val.arr ℓ c) l S

/-- A leaf of a family, named by its location.  `[spec §9]` -/
theorem RefPos.fam_at {L S : VTy} {ℓ : Nat} {n : UInt32} {m : Nat} {l : Loc} (h₁ : ℓ ≤ m)
    (h₂ : m < ℓ + n.toNat) (h : RefPos L (Val.loc m) l S) : RefPos (.fam L) (Val.arr ℓ n) l S := by
  obtain ⟨i, rfl⟩ : ∃ i, m = ℓ + i := ⟨m - ℓ, by omega⟩
  exact RefPos.fam (by omega) h

/-- A leaf of a family, named by its location.  `[spec §9]` -/
theorem MutPos.fam_at {L S : VTy} {ℓ : Nat} {n : UInt32} {m : Nat} {l : Loc} (h₁ : ℓ ≤ m)
    (h₂ : m < ℓ + n.toNat) (h : MutPos L (Val.loc m) l S) : MutPos (.fam L) (Val.arr ℓ n) l S := by
  obtain ⟨i, rfl⟩ : ∃ i, m = ℓ + i := ⟨m - ℓ, by omega⟩
  exact MutPos.fam (by omega) h

/-- `δ′` agrees with `δ` on the free lifetime variables of `T`. -/
def AgreeOn (T : VTy) (δ' δ : LSub) : Prop := ∀ y, VFree y T → δ'.find? y = δ.find? y

/-- The program's type `Imm @a S′` at `δ′` is coherent with the view at `m`: `m` is a
record's cell and `S′` is its type, or `m` is a chain position and `S′` its pointee type; in
both, `δ′` agrees with the record's `δ` on `S′`.  The index `a` is not mentioned: `⊑Imm`
changes it and nothing here.  `[about ours: our coherence]` -/
def Coh (rs : List FrameRec) (m : Loc) (S' : VTy) (δ' : LSub) : Prop :=
  (∃ r ∈ rs, m = r.le ∧ S' = r.T ∧ AgreeOn r.T δ' r.δ) ∨
  (∃ r ∈ rs, ∃ p u, Chain r.R r.T r.v p m S' u ∧ AgreeOn S' δ' r.δ)

/-- `GPos R T v ℓ S`: from `(T, v)`, zero or more `Ref` steps read off `R`, then a `Mut @a S`
position at `ℓ`.  `[about ours: the positions 6.131's induction visits, named]` -/
inductive GPos (R : WRes) : VTy → Val → Loc → VTy → Prop
  | here {T : VTy} {v : Val} {m : Loc} {S : VTy} : MutPos T v m S → GPos R T v m S
  | step {T : VTy} {v : Val} {l : Loc} {S₀ : VTy} {u₀ : Val} {m : Loc} {S : VTy} :
      RefPos T v l S₀ → R.get l = some (CellU.ownOf u₀) → GPos R S₀ u₀ m S → GPos R T v m S

/-- `d` is the sub-record of `r` at a `Mut` position: `d.le` is a `GPos` of `r` at pointee
type `d.T`, `r`'s escrow holds there a `mut` cell whose value and witness are `d`'s, and `d`
is read at `r`'s `δ`.  `[about ours: our record of 6.122's ↺m position]` -/
def SubRec (r d : FrameRec) : Prop :=
  d.δ = r.δ ∧ GPos r.R r.T r.v d.le d.T ∧
  ∃ ζ : CellU Loc Val, r.R.get d.le = some ζ ∧ ζ.kind = Kind.mut ∧ ζ.erase = d.v ∧ ζ.wit = d.R

/-- `LinPath r p d`: `d` is `r`, or a sub-record of a sub-record … of `r`, along the `mut`
locations `p`.  `[about ours: our lineage]` -/
inductive LinPath : FrameRec → List Loc → FrameRec → Prop
  | nil (r : FrameRec) : LinPath r [] r
  | cons {r d e : FrameRec} {p : List Loc} : SubRec r d → LinPath d p e → LinPath r (d.le :: p) e

/-- `d` is in `r`'s lineage.  `[about ours]` -/
def DescR (r d : FrameRec) : Prop := ∃ p, LinPath r p d

/-- `d` is a proper sub-record in `r`'s lineage.  `[about ours]` -/
def Desc (r d : FrameRec) : Prop := ∃ p, p ≠ [] ∧ LinPath r p d

/-- `r` is relevant to `ρ`: an `imm` cell of `ρ` sits at `r`'s location or at a chain
position of `r` — the two places `Coh` looks.  `[about ours]` -/
def Rel (r : FrameRec) (ρ : WRes) : Prop :=
  ∃ (m : Loc) (ψ : CellU Loc Val), ρ.get m = some ψ ∧ ψ.kind = Kind.imm ∧
    (m = r.le ∨ ∃ p S u, Chain r.R r.T r.v p m S u)

/-- `rs′` keeps the records of `rs` relevant to `ρ`.  `[about ours]` -/
def Keeps (rs rs' : List FrameRec) (ρ : WRes) : Prop := ∀ r ∈ rs, Rel r ρ → r ∈ rs'

/-- A record with the lifetime of its frame.  `[about ours]` -/
abbrev SRec := FrameRec × Life

/-- The records, forgetting their lifetimes.  `[about ours]` -/
def rsOf (ls : List SRec) : List FrameRec := ls.map Prod.fst

/-- `ρ` holds a borrow cell no longer-lived than `b`: a `mut` or `imm` cell with
`@ψ ⊑ b`.  `[about ours]` -/
def CellIn (ρ : WRes) (b : Life) : Prop :=
  ∃ (m : Loc) (ψ : CellU Loc Val), ρ.get m = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.at ⊑ b

/-- `ls′` extends `ls` at `ρ`: the records relevant to `ρ` are kept (`Keeps`), and
the records strictly longer-lived than any borrow cell of `ρ` — `mut` or `imm` — are exactly
the same.  `[about ours: our stratified Kripke order; docs/adjudications.md §12.72]` -/
def Ext (ls ls' : List SRec) (ρ : WRes) : Prop :=
  Keeps (rsOf ls) (rsOf ls') ρ ∧
    ∀ b, CellIn ρ b → ∀ x : SRec, x.2 ⊐ b → (x ∈ ls ↔ x ∈ ls')

/-- A `wp` over tagged record lists: the parameter of the relation, so that the relation's
lemmas, none of which unfolds `wp`, are stated once.  `[about ours]` -/
abbrev WpOp := List SRec → Expr → (List SRec → Val → WProp) → WProp

/-- A lineage location of `p`: an `own` or `mut` cell of the escrow of a member of `p`'s
lineage — a chain position, or a sub-record's location.  `[about ours]` -/
def LinLoc (p : FrameRec) (m : Loc) : Prop :=
  ∃ d, DescR p d ∧ ∃ ζ : CellU Loc Val, d.R.get m = some ζ ∧ ζ.kind ≠ Kind.imm

/-- `p`'s frame is at `α`, and its lineage's views are no longer (`⊑`, non-strict).  `[about ours: an
invariant of the typed world, 6.150 H11's choice of `β` read at a record]`  `[spec §4]` -/
def FrameLife (W : WRes) (p : FrameRec) (α : Life) : Prop :=
  (∀ a, AgW W a → ∀ (ζ : CellU Loc Val) t, a.get p.le = some ζ → ζ.lsOf = some t →
    ∀ y, t.mem y → y = α) ∧
  (∀ a, AgW W a → ∀ m, LinLoc p m → ∀ (ψ : CellU Loc Val) s, a.get m = some ψ →
    ψ.lsOf = some s → ∀ x, s.mem x → x ⊑ α)

mutual
/-- `S` at `δ` and `S′` at `δ′` are one value type.  `[about ours]` -/
def TyEq : VTy → LSub → VTy → LSub → Prop
  | .unit, _, .unit, _ => True
  | .zero, _, .zero, _ => True
  | .unk, _, .unk, _ => True
  | .int w, _, .int w', _ => w = w'
  | .tensor A B, δ, .tensor A' B', δ' => TyEq A δ A' δ' ∧ TyEq B δ B' δ'
  | .sum A B, δ, .sum A' B', δ' => TyEq A δ A' δ' ∧ TyEq B δ B' δ'
  | .thunk C, δ, .thunk C', δ' => CTyEq C δ C' δ'
  | .ref A, δ, .ref A', δ' => TyEq A δ A' δ'
  | .bang A, δ, .bang A', δ' => TyEq A δ A' δ'
  | .box a A, δ, .box a' A', δ' => a.interp δ = a'.interp δ' ∧ TyEq A δ A' δ'
  | .imm a A, δ, .imm a' A', δ' => a.interp δ = a'.interp δ' ∧ TyEq A δ A' δ'
  | .mut a A, δ, .mut a' A', δ' => a.interp δ = a'.interp δ' ∧ TyEq A δ A' δ'
  | .tvar n, _, .tvar n', _ => n = n'
  | .mu A, δ, .mu A', δ' => TyEq A δ A' δ'
  | .fam A, δ, .fam A', δ' => TyEq A δ A' δ'
  | _, _, _, _ => False
/-- `C` at `δ` and `C′` at `δ′` are one computation type.  `[about ours]` -/
def CTyEq : CTy → LSub → CTy → LSub → Prop
  | .ret A, δ, .ret A', δ' => TyEq A δ A' δ'
  | .arr A C, δ, .arr A' C', δ' => TyEq A δ A' δ' ∧ CTyEq C δ C' δ'
  | .amp C D, δ, .amp C' D', δ' => CTyEq C δ C' δ' ∧ CTyEq D δ D' δ'
  | .top, _, .top, _ => True
  | .all x b C, δ, .all x' b' C', δ' =>
      b.interp δ = b'.interp δ' ∧ ∀ α : Life, CTyEq C (δ.extend x α) C' (δ'.extend x' α)
  | .nu C, δ, .nu C', δ' => CTyEq C δ C' δ'
  | _, _, _, _ => False
end

end BoCa.Fig16.LogRel.Core

end

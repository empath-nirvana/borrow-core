import Paper.S1_Syntax.Definitions
import Paper.S2_Statics.Definitions
import Paper.S5_Model.Definitions
import Support.Lifetimes.Interpretation
import Support.LogicalRelation.ClosingSubstitutions
import Support.Model.Cells
import Support.Model.Prelude

/-!
# Relaxed — Records

`[about ours]`.  The records the typed world keeps: frame records and their lineages, root, chain and `Mut` positions, coherence of a record with the world, tags, and the Kripke order `Ext`.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Relaxed
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `δ` interprets every lifetime variable free in `T` — `𝒱⟦T⟧δ` is only ever taken at
`δ ∈ 𝒟⟦Δ⟧` with `T` well formed under `Δ` (`[TR]` 6.151's statement). -/
def AdmWf : Ty → LSub → Prop := fun T δ => ∀ x, LFree x T → ∃ α, δ.find? x = some α

/-- A frame taken by `[TR]` 6.64: the location `le`, the value `v` it held, the payload
resource `R` moved into the borrow, and the `(T, δ)` with `R ∈ 𝒱⟦T⟧δ(v)`.
`[about ours: our record of 6.64's `P̂ = 𝒱⟦T⟧δ`]` -/
structure FrameRec where
  le : Loc
  v : Val
  R : WRes
  T : Ty
  δ : LSub

/-- `RefPos T v ℓ S`: the value `v` of type `T` holds, at a `Ref S` reached from `T` through
`⊗`, `⊕` and `[@a]`, the location `ℓ`.  One constructor per case of `[TR]` 6.131's
induction that recurses (`⊗`: *"Apply IH"* at both components; `⊕`: *"Analogous to
`T = T₁ ⊗ T₂`"*; `[@a]`: *"Apply [] L … Apply IH"*) and the one that stops at an owned cell
(`Ref T′`).  `[about ours: the positions 6.131's induction visits, named]` -/
inductive RefPos : Ty → Val → Loc → Ty → Prop
  | ref (S : Ty) (l : Loc) : RefPos (.ref S) (Val.loc l) l S
  | tensorL {T₁ T₂ : Ty} {v₁ v₂ : Val} {l : Loc} {S : Ty} :
      RefPos T₁ v₁ l S → RefPos (.tensor T₁ T₂) (Val.pair v₁ v₂) l S
  | tensorR {T₁ T₂ : Ty} {v₁ v₂ : Val} {l : Loc} {S : Ty} :
      RefPos T₂ v₂ l S → RefPos (.tensor T₁ T₂) (Val.pair v₁ v₂) l S
  | sumL {T₁ T₂ : Ty} {v₁ : Val} {l : Loc} {S : Ty} :
      RefPos T₁ v₁ l S → RefPos (.sum T₁ T₂) (Val.inj₁ v₁) l S
  | sumR {T₁ T₂ : Ty} {v₂ : Val} {l : Loc} {S : Ty} :
      RefPos T₂ v₂ l S → RefPos (.sum T₁ T₂) (Val.inj₂ v₂) l S
  | box {a : Lifetime.Life} {T : Ty} {v : Val} {l : Loc} {S : Ty} :
      RefPos T v l S → RefPos (.box a T) v l S

/-- `Chain R T v p ℓ S u`: `ℓ ↦ own(u)` is in `R`, reached from `(T, v)` by a chain of
`RefPos` steps whose intermediate values are read off `R`; `S` is `ℓ`'s pointee type and `p`
the location of the chain's previous step (`none` at a first step).
`[about ours: the borrow nodes 6.131's `Ref` case produces, iterated]` -/
inductive Chain (R : WRes) : Ty → Val → Option Loc → Loc → Ty → Val → Prop
  | one {T : Ty} {v : Val} {l : Loc} {S : Ty} {u : Val} :
      RefPos T v l S → R.get l = some (CellU.ownOf u) → Chain R T v none l S u
  | step {T : Ty} {v : Val} {l₁ : Loc} {S₁ : Ty} {u₁ : Val} {p : Option Loc} {l : Loc}
      {S : Ty} {u : Val} :
      RefPos T v l₁ S₁ → R.get l₁ = some (CellU.ownOf u₁) → Chain R S₁ u₁ p l S u →
      Chain R T v (some (p.getD l₁)) l S u

/-- `MutPos T v ℓ S`: the value `v` of type `T` holds, at a `Mut @a S` reached from `T`
through `⊗`, `⊕` and `[@a]`, the location `ℓ` — `[TR]` 6.131's positions that stop at a
mutable borrow (`Imm̲ 'b (Mut @a S) = Imm 'b S`, `[CONF]` Fig. 9).
`[about ours: the positions 6.131's induction visits, named]` -/
inductive MutPos : Ty → Val → Loc → Ty → Prop
  | mut (a : Lifetime.Life) (S : Ty) (l : Loc) : MutPos (.mut a S) (Val.loc l) l S
  | tensorL {T₁ T₂ : Ty} {v₁ v₂ : Val} {l : Loc} {S : Ty} :
      MutPos T₁ v₁ l S → MutPos (.tensor T₁ T₂) (Val.pair v₁ v₂) l S
  | tensorR {T₁ T₂ : Ty} {v₁ v₂ : Val} {l : Loc} {S : Ty} :
      MutPos T₂ v₂ l S → MutPos (.tensor T₁ T₂) (Val.pair v₁ v₂) l S
  | sumL {T₁ T₂ : Ty} {v₁ : Val} {l : Loc} {S : Ty} :
      MutPos T₁ v₁ l S → MutPos (.sum T₁ T₂) (Val.inj₁ v₁) l S
  | sumR {T₁ T₂ : Ty} {v₂ : Val} {l : Loc} {S : Ty} :
      MutPos T₂ v₂ l S → MutPos (.sum T₁ T₂) (Val.inj₂ v₂) l S
  | box {a : Lifetime.Life} {T : Ty} {v : Val} {l : Loc} {S : Ty} :
      MutPos T v l S → MutPos (.box a T) v l S

/-- `δ′` agrees with `δ` on the free lifetime variables of `T`. -/
def AgreeOn (T : Ty) (δ' δ : LSub) : Prop := ∀ y, LFree y T → δ'.find? y = δ.find? y

/-- The program's type `Imm @a S′` at `δ′` is coherent with the view at `m`: `m` is a
record's cell and `S′` is its type, or `m` is a chain position and `S′` its pointee type; in
both, `δ′` agrees with the record's `δ` on `S′`.  The index `a` is not mentioned: `⊑Imm`
changes it and nothing here.  `[about ours: our coherence]` -/
def Coh (rs : List FrameRec) (m : Loc) (S' : Ty) (δ' : LSub) : Prop :=
  (∃ r ∈ rs, m = r.le ∧ S' = r.T ∧ AgreeOn r.T δ' r.δ) ∨
  (∃ r ∈ rs, ∃ p u, Chain r.R r.T r.v p m S' u ∧ AgreeOn S' δ' r.δ)

/-- `GPos R T v ℓ S`: from `(T, v)`, zero or more `Ref` steps read off `R`, then a `Mut @a S`
position at `ℓ`.  `[about ours: the positions 6.131's induction visits, named]` -/
inductive GPos (R : WRes) : Ty → Val → Loc → Ty → Prop
  | here {T : Ty} {v : Val} {m : Loc} {S : Ty} : MutPos T v m S → GPos R T v m S
  | step {T : Ty} {v : Val} {l : Loc} {S₀ : Ty} {u₀ : Val} {m : Loc} {S : Ty} :
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
invariant of the typed world, 6.150 H11's choice of `β` read at a record]` -/
def FrameLife (W : WRes) (p : FrameRec) (α : Life) : Prop :=
  (∀ a, AgW W a → ∀ (ζ : CellU Loc Val) t, a.get p.le = some ζ → ζ.lsOf = some t →
    ∀ y, t.mem y → y = α) ∧
  (∀ a, AgW W a → ∀ m, LinLoc p m → ∀ (ψ : CellU Loc Val) s, a.get m = some ψ →
    ψ.lsOf = some s → ∀ x, s.mem x → x ⊑ α)

/-- `S` at `δ` and `S′` at `δ′` are one type.  `[about ours]` -/
def TyEq : Ty → LSub → Ty → LSub → Prop
  | .unit, _, .unit, _ => True
  | .unk, _, .unk, _ => True
  | .tensor A B, δ, .tensor A' B', δ' => TyEq A δ A' δ' ∧ TyEq B δ B' δ'
  | .sum A B, δ, .sum A' B', δ' => TyEq A δ A' δ' ∧ TyEq B δ B' δ'
  | .lolli A B, δ, .lolli A' B', δ' => TyEq A δ A' δ' ∧ TyEq B δ B' δ'
  | .ref A, δ, .ref A', δ' => TyEq A δ A' δ'
  | .bang A, δ, .bang A', δ' => TyEq A δ A' δ'
  | .box a A, δ, .box a' A', δ' => a.interp δ = a'.interp δ' ∧ TyEq A δ A' δ'
  | .imm a A, δ, .imm a' A', δ' => a.interp δ = a'.interp δ' ∧ TyEq A δ A' δ'
  | .mut a A, δ, .mut a' A', δ' => a.interp δ = a'.interp δ' ∧ TyEq A δ A' δ'
  | .all x b A, δ, .all x' b' A', δ' =>
      b.interp δ = b'.interp δ' ∧ ∀ α : Life, TyEq A (δ.extend x α) A' (δ'.extend x' α)
  | _, _, _, _ => False

end BoCa.Fig16.LogRel.Relaxed

end

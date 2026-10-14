import Nominal.CoreRelation

/-!
# Nominal — Core's typed world over the nominal carrier

`Core/World.lean`'s `vShape`, `TW`, `Tagged` and `wpTS`, with what they read from
`Core/FrameRecords.lean` (the lineage: `GPos`, `SubRec`, `LinPath`, `Desc`, `LinLoc`, `FrameLife`)
and from `Paper/S5_Model` (`reb_α`: `ResU.RebAt`, `ResU.Reb`; `ρ/ℓ`, `dom`, `≤`, `ρ∣dom(σ)`,
`ρ∣own,mut`), on the nominal carrier, at the fragment's types.

Changes from Core, each where Core uses a chain or `Relation.lean` already changed a clause:
`[α]` in `vShape` read as in the relation (reading (b)); `LSet.singleton α` as `{α}`; a lent
cell's lifetime set `t ⊆ s` for `t.mem ⊆ s.mem`; the strata `Res_α` as `Res_{α}`; `StratumLe`'s
`β′ ⊏ β` over the partial order. Where Core's constructors name a cell by `immOf`/`mutOf` with its
proof arguments, the cell is named by its data (`CellU.IsImm`, kind/value/witness), which is the
same set of cells (`CellU.ext_data`).

`TW`'s premises are at the fragment's `vShape` (`False` outside it, as the relation).
-/

noncomputable section
open Classical

namespace Nominal
open BoCa
open BoCa.Fig16 (PMap Kind)
open BoCa.Fig16.LogRel.Core (VTy CTy forceE RefPos MutPos VFree)
open BoCa.Lifetime (LifeVar LifeCtx)

set_option linter.unusedSectionVars false

variable {L : Type} [PartialOrder L] [OrderTop L] [WellFoundedGT L]

/-! ### Resource operations -/

/-- `ρ/ℓ`. -/
def ResU.del (ρ : ResU L) (l : Loc) : ResU L where
  get := fun l' => if l' = l then none else ρ.get l'
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l' h => hd l' (fun e => h ?_)⟩
    show (if l' = l then none else ρ.get l') = none
    by_cases f : l' = l
    · exact if_pos f
    · rw [if_neg f]; exact e

/-- `d` lists `dom(ρ)`, each location once. -/
def ResU.Dom (ρ : ResU L) (d : List Loc) : Prop :=
  d.Nodup ∧ ∀ l, l ∈ d ↔ ∃ ψ, ρ.get l = some ψ

/-- `ρ ≤ σ`. -/
def ResU.Le (ρ σ : ResU L) : Prop := ∃ τ, ResU.CompS ρ τ σ

/-- `ρ∣dom(σ)`. -/
def ResU.restrictDom (ρ σ : ResU L) : ResU L where
  get := fun l => if (σ.get l).isSome then ρ.get l else none
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l hl => hd l (fun e => hl ?_)⟩
    show (if (σ.get l).isSome then ρ.get l else none) = none
    rw [e]; exact ite_self none

/-- `ρ∣own,mut`. -/
def ResU.exclPart (ρ : ResU L) : ResU L where
  get := fun l => (ρ.get l).bind fun ψ => if ψ.kind = .imm then none else some ψ
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l hl => hd l (fun e => hl ?_)⟩
    show (ρ.get l).bind _ = none
    rw [e]; rfl

/-- `reb_α(ρ)` at one location (`Paper`'s `ResU.RebAt`): an owned cell becomes `imm({α}, v,
p/ℓ)`, a `mut` cell `imm({α}, v, χ)`, an `imm` cell keeps a nonempty part of its lifetimes. -/
def ResU.RebAt (α : L) (ρ ρ' : ResU L) (l : Loc) (p : ResU L) : Prop :=
  (∃ ψ, p.get l = some ψ) ∧
  (∀ v : Val, ρ.get l = some (CellU.own v) →
      ∃ ψ', ρ'.get l = some ψ' ∧ ψ'.IsImm {α} v (p.del l)) ∧
  (∀ (v : Val) (χ : ResU L), (∃ ψ, ρ.get l = some ψ ∧ ψ.kind = .mut ∧ ψ.erase = v ∧
      ψ.wit = χ) →
      (∃ ψ', ρ'.get l = some ψ' ∧ ψ'.IsImm {α} v χ) ∧ ResU.Dom p [l]) ∧
  (∀ (s : Finset L) (v : Val) (χ : ResU L), (∃ ψ, ρ.get l = some ψ ∧ ψ.IsImm s v χ) →
      (∃ (t : Finset L) (ψ' : CellU L), t.Nonempty ∧ t ⊆ s ∧ ρ'.get l = some ψ' ∧
        ψ'.IsImm t v χ) ∧ ResU.Dom p [l])

/-- `ρ′ ∈ reb_α(ρ)` (`Paper`'s `ResU.Reb`). -/
def ResU.Reb (α : L) (ρ ρ' : ResU L) : Prop :=
  ρ.InStratum {α} ∧
  ∃ (ps : List (Loc × ResU L)) (b : ResU L),
    ρ'.Dom (ps.map Prod.fst) ∧
    BigComp CellU.CompatS CellU.CompS (ps.map Prod.snd) b ∧
    ResU.Le b ρ ∧
    ∀ l p, (l, p) ∈ ps → ResU.RebAt α ρ ρ' l p

/-! ### `vShape` -/

/-- `𝒱⟦A⟧`'s shape (Core's `vShapeE none`) at the fragment: `U` positions `True`, the `Mut`
clause's stored predicate contained in the shape. -/
def vShapeN : VTy → LSubN L → Val → WPropN L
  | .unit, _, v => pureN (v = .unit)
  | .tensor A B, δ, v =>
      exN fun v₁ => exN fun v₂ => sepN (pureN (v = .pair v₁ v₂))
        (sepN (vShapeN A δ v₁) (vShapeN B δ v₂))
  | .thunk _, _, _ => fun _ => True
  | .box a A, δ, v => atLifeN δ a fun α => boxE α (vShapeN A δ v)
  | .ref A, δ, v =>
      exN fun ℓ => exN fun v' => sepN (pureN (v = .loc ℓ)) (sepN (ptoOwnN ℓ v') (vShapeN A δ v'))
  | .imm a A, δ, v =>
      atLifeN δ a fun α => exN fun ℓ => sepN (pureN (v = .loc ℓ)) (ptoImmN ℓ α (vShapeN A δ))
  | .mut a A, δ, v =>
      atLifeN δ a fun α => exN fun ℓ => sepN (pureN (v = .loc ℓ))
        (fun ρ => ∃ P, ptoMutN ℓ α P ρ ∧ ∀ u σ, P u σ → vShapeN A δ u σ)
  | .zero, _, _ | .sum _ _, _, _ | .bang _, _, _ | .unk, _, _ | .tvar _, _, _ | .mu _, _, _
  | .int _, _, _ | .fam _, _, _ | .opq _, _, _ => fun _ => False

/-- `δ` reads every lifetime variable free in `T`. -/
def AdmWfN (T : VTy) (δ : LSubN L) : Prop := ∀ x, VFree x T → ∃ α, δ.find? x = some α

/-! ### The lineage -/

/-- From `(T, v)`, `Ref` steps read off `R`, then a `Mut` position at `m` (Core's `GPos`). -/
inductive GPosN (R : ResU L) : VTy → Val → Loc → VTy → Prop
  | here {T : VTy} {v : Val} {m : Loc} {S : VTy} : MutPos T v m S → GPosN R T v m S
  | step {T : VTy} {v : Val} {l : Loc} {S₀ : VTy} {u₀ : Val} {m : Loc} {S : VTy} :
      RefPos T v l S₀ → R.get l = some (CellU.own u₀) → GPosN R S₀ u₀ m S → GPosN R T v m S

/-- `d` is the sub-record of `r` at a `Mut` position (Core's `SubRec`). -/
def SubRecN (r d : FrameRecN L) : Prop :=
  d.δ = r.δ ∧ GPosN r.R r.T r.v d.le d.T ∧
  ∃ ζ : CellU L, r.R.get d.le = some ζ ∧ ζ.kind = .mut ∧ ζ.erase = d.v ∧ ζ.wit = d.R

/-- `d` is `r`, or a sub-record of a sub-record … of `r` (Core's `LinPath`). -/
inductive LinPathN : FrameRecN L → List Loc → FrameRecN L → Prop
  | nil (r : FrameRecN L) : LinPathN r [] r
  | cons {r d e : FrameRecN L} {p : List Loc} : SubRecN r d → LinPathN d p e →
      LinPathN r (d.le :: p) e

/-- `d` is in `r`'s lineage. -/
def DescRN (r d : FrameRecN L) : Prop := ∃ p, LinPathN r p d

/-- `d` is a proper sub-record in `r`'s lineage. -/
def DescN (r d : FrameRecN L) : Prop := ∃ p, p ≠ [] ∧ LinPathN r p d

/-- A lineage location of `p`. -/
def LinLocN (p : FrameRecN L) (m : Loc) : Prop :=
  ∃ d, DescRN p d ∧ ∃ ζ : CellU L, d.R.get m = some ζ ∧ ζ.kind ≠ .imm

/-- The lifetime set of an `imm` cell. -/
def CellU.lsOf (ψ : CellU L) : Option (Finset L) := if ψ.kind = .imm then some ψ.lts else none

/-- `p`'s frame is at `α`, and its lineage's views are no longer (Core's `FrameLife`). -/
def FrameLifeN (W : ResU L) (p : FrameRecN L) (α : L) : Prop :=
  (∀ a, AgW W a → ∀ (ζ : CellU L) t, a.get p.le = some ζ → ζ.lsOf = some t →
    ∀ y ∈ t, y = α) ∧
  (∀ a, AgW W a → ∀ m, LinLocN p m → ∀ (ψ : CellU L) s, a.get m = some ψ →
    ψ.lsOf = some s → ∀ x ∈ s, x ≤ α)

/-- `W`'s lifetimes are all `⊒ β`. -/
def StratumLeN (W : ResU L) (β : L) : Prop := ∀ β', β' < β → W.InStratum {β'}

/-! ### The typed world -/

/-- **The typed world** (Core's `TW`): one constructor per operation of the printed proofs. -/
inductive TWN : ResU L → List (FrameRecN L) → List (FrameRecN L) → Prop
  | empty : TWN PMap.empty [] []
  | alloc {W W' : ResU L} {ps rs : List (FrameRecN L)} {μ : BoCa.BoLo.Heap} {l : Loc} {v : Val} :
      TWN W ps rs → W.Lower μ → μ l = none →
      ResU.CompS W (ResU.single l (CellU.own v)) W' → W'.Valid → TWN W' ps rs
  | immFrame {W X Z R W' : ResU L} {ps rs ds : List (FrameRecN L)} {l : Loc} {v : Val} {α : L}
      (T : VTy) (δ : LSubN L) (h : R.InStratum {α}) :
      TWN W ps rs → AdmWfN T δ → ResU.CompS (ResU.single l (CellU.own v)) R X →
      ResU.CompS X Z W → vShapeN T δ v R →
      ResU.CompS (ResU.single l (CellU.immOf {α} (Finset.singleton_nonempty α) v R h)) Z W' →
      W'.Valid → (∀ d, d ∈ ds ↔ DescN ⟨l, v, R, T, δ⟩ d) →
      TWN W' (⟨l, v, R, T, δ⟩ :: ps) (⟨l, v, R, T, δ⟩ :: (ds ++ rs))
  | reb {W W' c : ResU L} {ps rs : List (FrameRecN L)} (r : FrameRecN L) {le : Loc}
      {s : Finset L} {β : L} (x : LifeVar) :
      TWN W ps rs → r ∈ rs → (∃ ψ, W.get le = some ψ ∧ ψ.IsImm s r.v r.R) →
      ¬ VFree x r.T → ResU.Reb β r.R c →
      vShapeN (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v c →
      StratumLeN W β → ResU.CompS W c W' → W'.Valid → TWN W' ps rs
  | rebDeep {W W' c : ResU L} {ps rs : List (FrameRecN L)} (r : FrameRecN L) {p : Option Loc}
      {l₀ : Loc} {S₀ : VTy} {u₀ : Val} {s : Finset L} {w₀ : ResU L} {β : L} (x : LifeVar) :
      TWN W ps rs → r ∈ rs → ChainN r.R r.T r.v p l₀ S₀ u₀ →
      (∃ ψ, W.get l₀ = some ψ ∧ ψ.IsImm s u₀ w₀) → ¬ VFree x S₀ → ResU.Reb β w₀ c →
      vShapeN (S₀.immReborrow (.var x)) (r.δ.extend x β) u₀ c →
      W.InStratum {β} → ResU.CompS W c W' → W'.Valid → TWN W' ps rs
  | mutFold {W X Z ρ W' : ResU L} {ps rs : List (FrameRecN L)} {l : Loc} {v : Val} :
      TWN W ps rs → ResU.CompS (ResU.single l (CellU.own v)) ρ X → ResU.CompS X Z W →
      (∃ ψ : CellU L, ψ.kind = .mut ∧ ψ.erase = v ∧ ψ.wit = ρ ∧
        ResU.CompS (ResU.single l ψ) Z W') → W'.Valid → TWN W' ps rs
  | mutUnfold {W X Z ρ W' : ResU L} {ps rs : List (FrameRecN L)} {l : Loc} {v : Val} :
      TWN W ps rs →
      (∃ ψ : CellU L, ψ.kind = .mut ∧ ψ.erase = v ∧ ψ.wit = ρ ∧
        ResU.CompS (ResU.single l ψ) Z W) →
      ResU.CompS (ResU.single l (CellU.own v)) ρ X → ResU.CompS X Z W' → W'.Valid →
      TWN W' ps rs
  | free {W W' : ResU L} {ps rs : List (FrameRecN L)} {l : Loc} {v : Val} :
      TWN W ps rs → ResU.CompS (ResU.single l (CellU.own v)) W' W → W'.Valid → TWN W' ps rs
  | store {W Z W' : ResU L} {ps rs : List (FrameRecN L)} {l : Loc} {v₁ v₂ : Val} :
      TWN W ps rs → ResU.CompS (ResU.single l (CellU.own v₁)) Z W →
      ResU.CompS (ResU.single l (CellU.own v₂)) Z W' → W'.Valid → TWN W' ps rs
  | immEnd {W Y X' W' : ResU L} {ps rs ps' rs' : List (FrameRecN L)} (r : FrameRecN L)
      {s : Finset L} :
      TWN W ps rs → r ∈ ps →
      (∃ ψ : CellU L, ψ.IsImm s r.v r.R ∧ ResU.CompS (ResU.single r.le ψ) Y W) →
      ResU.CompS (ResU.single r.le (CellU.own r.v)) r.R X' → ResU.CompS X' Y W' →
      W'.Valid → (∀ r', r' ∈ ps' ↔ (r' ∈ ps ∧ r' ≠ r)) →
      (∀ d, d ∈ rs' ↔ ∃ p ∈ ps', DescRN p d) → TWN W' ps' rs'
  | rebEnd {W W' c : ResU L} {ps rs : List (FrameRecN L)} (r : FrameRecN L) {le : Loc}
      {s : Finset L} {β : L} :
      TWN W ps rs → r ∈ rs → (∃ ψ, W'.get le = some ψ ∧ ψ.IsImm s r.v r.R) →
      ResU.Reb β r.R c → ResU.CompS W' (c.restrictDom r.R.exclPart) W →
      W'.InStratum {β} → TWN W' ps rs
  | rebEndDeep {W W' c : ResU L} {ps rs : List (FrameRecN L)} (r : FrameRecN L)
      {p : Option Loc} {l₀ : Loc} {S₀ : VTy} {u₀ : Val} {s : Finset L} {w₀ : ResU L} {β : L} :
      TWN W ps rs → r ∈ rs → ChainN r.R r.T r.v p l₀ S₀ u₀ →
      (∃ ψ, W'.get l₀ = some ψ ∧ ψ.IsImm s u₀ w₀) → ResU.Reb β w₀ c →
      ResU.CompS W' (c.restrictDom w₀.exclPart) W → W'.InStratum {β} → TWN W' ps rs

/-- A tagged list agrees with the world (Core's `Tagged`). -/
def TaggedN (W : ResU L) (ps : List (FrameRecN L)) (ls : List (SRecN L)) : Prop :=
  ∀ x ∈ ls, ∃ p ∈ ps, DescRN p x.1 ∧ FrameLifeN W p x.2

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- **Core's `wp`** (`wpTS`): `[TR]` p. 6's `wp` at tagged typed worlds, under every allocator. -/
def wpTSN : WpOpN L := fun ls e Q ρ =>
  ∀ (ρf fρ : ResU L) (ps : List (FrameRecN L)), ρf.Hash ρ → ResU.CompS ρf ρ fρ →
    TWN fρ ps (rsOfN ls) → TaggedN fρ ps ls → ∀ (A : BoCa.BoLo.Alloc) (k : Nat),
    ∃ (ρ' ρp fρ' fρ'p πr : ResU L) (v : Val) (μ μ' : BoCa.BoLo.Heap)
      (ps' : List (FrameRecN L)) (ls' : List (SRecN L)),
      ρ'.Hash ρf ∧ ResU.CompS ρf ρ' fρ' ∧ ρp.Hash fρ' ∧ fρ.Lower μ ∧
      ResU.CompS fρ' ρp fρ'p ∧ fρ'p.Lower μ' ∧
      (∃ k', BoCa.BoLo.ARun (ℍ := ℍ) A k μ e k' μ' (.val v)) ∧
      ResU.CompS ρ' ρp πr ∧ ρ.UpdV πr ∧ NoOwn ρp ∧
      TWN fρ'p ps' (rsOfN ls') ∧ TaggedN fρ'p ps' ls' ∧
      (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls) ∧ Q ls' v ρ'

end Nominal

end

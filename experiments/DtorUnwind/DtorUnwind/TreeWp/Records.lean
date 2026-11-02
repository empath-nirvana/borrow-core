import DtorUnwind.TreeWp.World
import DtorUnwind.Tree.Port.Six34to39
import DtorUnwind.Tree.Port.ReborrowLowering

/-!
# Frame records and canonical images over the tree world

`SI/TWNC.lean`'s typed world with canonical images, read over the tree-stratified carrier with
store types as codes (`TreeWp/Codes.lean`). Each piece is the `SI/`/`Core/` one with the
carrier's names (`CellUT`, `TSet`, `K.le`), and with the record's type a code:

* **Records** (`FrameRecT`): location, value, escrow and code, as `Core/FrameRecords.lean`'s
  `FrameRec` with `T : KTy`. A code names its lifetimes, so there is no substitution `δ` and no
  `AdmWf`; `𝒱⟦T⟧δ` is `T.interp Θ` read at the tree.
* **Positions, chains, lineages** (`RefPosT`, `MutPosT`, `ChainT`, `GPosT`, `SubRecT`,
  `LinPathT`, `DescRT`, `DescT`, `LinLocT`, `FrameLifeT`): `Core/FrameRecords.lean`'s, at the
  codes' formers (`1`, `+`, `Imm`, `Mut`, `[a]`, `ref`).
* **`Imm̲ 'b`** (`KTy.immReborrow`): `Core/Types.lean`'s `VTy.immReborrow` at the codes' formers,
  at a lifetime `b` (codes are closed, so no variable is introduced and extended).
* **Reborrow premises** (`RebRecLeT`, `RebEndRecT`, `RebCellLeT`): `SI/TWN.lean`'s, with `⊑`, `⊏`
  read in `K`.
* **Templates and canonical images** (`TmplSpecT`, `tmplT`, `canonT`, and the deep ones):
  `SI/TWNC.lean`'s, the typing read through `interp`, the choice made at the current tree and
  code typing. A template is covered (`TmplSpecT`'s last clause).
* **`TWNT`**: `TWNC`'s constructors over `TRes K`, and one more, `reread`: the tree grows or a
  location no `mut` cell is at is re-typed, the world and every record re-read (`RecRR`). At no
  growth the re-reading is the identity (`TWNT.reread_refl`).

**Open: templates across a re-reading.** A template is the `Classical` choice at `(K, Θ)`; after
`reread` the choice at `(K′, Θ′)` need not be the re-reading of the one at `(K, Θ)`, so `TWNC`'s
template invariant (`TemplAt`: every view at a record's roots carries the template's witness) is
not carried by `reread` as stated. Carrying the template with the record fixes it for records
proper but leaves sub-records' templates undetermined (a sub-record is named by its lineage,
which fixes location, value, escrow and code only). Not derived, obstruction not verified.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

/-! ### `Imm̲ 'b` at the codes -/

/-- `Imm̲ 'b A` (`VTy.immReborrow`) at the codes' formers: `1`, `+` structurally; `ref A ↦ Imm 'b A`;
`Imm @a A` kept; `Mut @a A ↦ Imm 'b A`; `[@a] A ↦ Imm̲ 'b A`. -/
def KTy.immReborrow (b : Life) : KTy → KTy
  | .unit => .unit
  | .sum A B => .sum (A.immReborrow b) (B.immReborrow b)
  | .imm a A => .imm a A
  | .mut _ A => .imm b A
  | .box _ A => A.immReborrow b
  | .ref A => .imm b A

/-! ### Records -/

/-- A frame record over the tree carrier: the location `le`, the value `v` it held, the escrow
`R`, and the code `T` with `R ∈ ⟦T⟧`. -/
structure FrameRecT (K : WCactus) where
  le : BoCa.Loc
  v : BoCa.Val
  R : TRes K
  T : KTy

variable {K : WCactus}

/-- `RefPos` at the codes. -/
inductive RefPosT : KTy → BoCa.Val → BoCa.Loc → KTy → Prop
  | ref (S : KTy) (l : BoCa.Loc) : RefPosT (.ref S) (BoCa.Val.loc l) l S
  | sumL {T₁ T₂ : KTy} {v₁ : BoCa.Val} {l : BoCa.Loc} {S : KTy} :
      RefPosT T₁ v₁ l S → RefPosT (.sum T₁ T₂) (BoCa.Val.inj₁ v₁) l S
  | sumR {T₁ T₂ : KTy} {v₂ : BoCa.Val} {l : BoCa.Loc} {S : KTy} :
      RefPosT T₂ v₂ l S → RefPosT (.sum T₁ T₂) (BoCa.Val.inj₂ v₂) l S
  | box {a : Life} {T : KTy} {v : BoCa.Val} {l : BoCa.Loc} {S : KTy} :
      RefPosT T v l S → RefPosT (.box a T) v l S

/-- `MutPos` at the codes. -/
inductive MutPosT : KTy → BoCa.Val → BoCa.Loc → KTy → Prop
  | mut (a : Life) (S : KTy) (l : BoCa.Loc) : MutPosT (.mut a S) (BoCa.Val.loc l) l S
  | sumL {T₁ T₂ : KTy} {v₁ : BoCa.Val} {l : BoCa.Loc} {S : KTy} :
      MutPosT T₁ v₁ l S → MutPosT (.sum T₁ T₂) (BoCa.Val.inj₁ v₁) l S
  | sumR {T₁ T₂ : KTy} {v₂ : BoCa.Val} {l : BoCa.Loc} {S : KTy} :
      MutPosT T₂ v₂ l S → MutPosT (.sum T₁ T₂) (BoCa.Val.inj₂ v₂) l S
  | box {a : Life} {T : KTy} {v : BoCa.Val} {l : BoCa.Loc} {S : KTy} :
      MutPosT T v l S → MutPosT (.box a T) v l S

/-- `Chain` over the tree carrier: `ℓ ↦ own(u)` in `R`, reached from `(T, v)` by `ref` steps
whose intermediate values are read off `R`. -/
inductive ChainT (R : TRes K) : KTy → BoCa.Val → Option BoCa.Loc → BoCa.Loc → KTy → BoCa.Val →
    Prop
  | one {T : KTy} {v : BoCa.Val} {l : BoCa.Loc} {S : KTy} {u : BoCa.Val} :
      RefPosT T v l S → R.get l = some (CellUT.ownOf u) → ChainT R T v none l S u
  | step {T : KTy} {v : BoCa.Val} {l₁ : BoCa.Loc} {S₁ : KTy} {u₁ : BoCa.Val}
      {p : Option BoCa.Loc} {l : BoCa.Loc} {S : KTy} {u : BoCa.Val} :
      RefPosT T v l₁ S₁ → R.get l₁ = some (CellUT.ownOf u₁) → ChainT R S₁ u₁ p l S u →
      ChainT R T v (some (p.getD l₁)) l S u

/-- `GPos` over the tree carrier: `ref` steps read off `R`, then a `Mut` position. -/
inductive GPosT (R : TRes K) : KTy → BoCa.Val → BoCa.Loc → KTy → Prop
  | here {T : KTy} {v : BoCa.Val} {m : BoCa.Loc} {S : KTy} : MutPosT T v m S → GPosT R T v m S
  | step {T : KTy} {v : BoCa.Val} {l : BoCa.Loc} {S₀ : KTy} {u₀ : BoCa.Val} {m : BoCa.Loc}
      {S : KTy} :
      RefPosT T v l S₀ → R.get l = some (CellUT.ownOf u₀) → GPosT R S₀ u₀ m S → GPosT R T v m S

/-- `SubRec`: `d` is the sub-record of `r` at a `Mut` position. -/
def SubRecT (r d : FrameRecT K) : Prop :=
  GPosT r.R r.T r.v d.le d.T ∧
  ∃ ζ : TCell K, r.R.get d.le = some ζ ∧ ζ.kind = Kind.mut ∧ ζ.erase = d.v ∧ ζ.wit = d.R

/-- `LinPath` over the tree carrier. -/
inductive LinPathT : FrameRecT K → List BoCa.Loc → FrameRecT K → Prop
  | nil (r : FrameRecT K) : LinPathT r [] r
  | cons {r d e : FrameRecT K} {p : List BoCa.Loc} :
      SubRecT r d → LinPathT d p e → LinPathT r (d.le :: p) e

/-- `d` is in `r`'s lineage. -/
def DescRT (r d : FrameRecT K) : Prop := ∃ p, LinPathT r p d

/-- `d` is a proper sub-record in `r`'s lineage. -/
def DescT (r d : FrameRecT K) : Prop := ∃ p, p ≠ [] ∧ LinPathT r p d

/-- A lineage location of `p`. -/
def LinLocT (p : FrameRecT K) (m : BoCa.Loc) : Prop :=
  ∃ d, DescRT p d ∧ ∃ ζ : TCell K, d.R.get m = some ζ ∧ ζ.kind ≠ Kind.imm

/-- `FrameLife` read in `K`: `p`'s frame is at `α`, and its lineage's views are no longer. -/
def FrameLifeT (K : WCactus) (W : TRes K) (p : FrameRecT K) (α : Life) : Prop :=
  (∀ a, AgWT W a → ∀ (ζ : TCell K) t, a.get p.le = some ζ → ζ.lsOfI = some t →
    ∀ y ∈ t.set, y = α) ∧
  (∀ a, AgWT W a → ∀ m, LinLocT p m → ∀ (ψ : TCell K) s, a.get m = some ψ →
    ψ.lsOfI = some s → ∀ x ∈ s.set, K.le x α)

/-! ### The reborrow premises -/

/-- `RebRecLe` read in `K`. -/
def RebRecLeT (K : WCactus) (W : TRes K) (ps : List (FrameRecT K)) (w₀ : TRes K) (β : Life) :
    Prop :=
  ∀ p ∈ ps, ∀ α, FrameLifeT K W p α →
    (∃ m, LinLocT p m ∧ ∃ ζ : TCell K, w₀.get m = some ζ ∧ ζ.kind ≠ Kind.imm) → K.le β α

/-- `RebEndRec` read in `K`. -/
def RebEndRecT (K : WCactus) (W' : TRes K) (rs : List (FrameRecT K)) (w₀ : TRes K) (β : Life) :
    Prop :=
  ∀ r ∈ rs, ∀ l₀ m S u, ChainT r.R r.T r.v (some l₀) m S u →
    (∃ ζ : TCell K, w₀.get l₀ = some ζ ∧ ζ.kind ≠ Kind.imm) →
    ∀ a', AgWT W' a' → ∀ (ψ : TCell K) s, a'.get m = some ψ → ψ.lsOfI = some s →
      ∀ x ∈ s.set, K.lt x β →
      ∃ (ζ : TCell K) (t : TSet) (y : Life), a'.get l₀ = some ζ ∧ ζ.lsOfI = some t ∧
        y ∈ t.set ∧ K.lt x y

/-- `RebCellLe` read in `K`. -/
def RebCellLeT (K : WCactus) (W : TRes K) (l₀ : BoCa.Loc) (β : Life) : Prop :=
  ∀ a, AgWT W a → ∃ (ψ : TCell K) (t : TSet) (y : Life), a.get l₀ = some ψ ∧
    ψ.lsOfI = some t ∧ y ∈ t.set ∧ K.lt β y

/-! ### Re-taking an image at `β` -/

open Classical in
/-- `relCell` over the tree carrier: the cell `reb_β`'s `own`/`mut` clauses put at `m`, over the
same value and witness, where `R(m)` is not `imm`; otherwise the cell unchanged. -/
def relCellT (R : TRes K) (β : Life) (m : BoCa.Loc) (ψ : TCell K) : TCell K :=
  if h : ψ.kind = Kind.imm ∧ (∃ ζ : TCell K, R.get m = some ζ ∧ ζ.kind ≠ Kind.imm) ∧
      ψ.wit.InStratum (TSet.single β) then
    CellUT.immOf (TSet.single β) ψ.erase ψ.wit h.2.2
  else ψ

/-- `c` with each cell passed through `relCellT`. -/
def relResT (R : TRes K) (β : Life) (c : TRes K) : TRes K where
  get m := (c.get m).map (relCellT R β m)
  finite := by
    obtain ⟨d, hd⟩ := c.finite
    exact ⟨d, fun l hl => hd l (fun e => hl (by simp [e]))⟩

theorem relResT_get (R : TRes K) (β : Life) (c : TRes K) (m : BoCa.Loc) :
    (relResT R β c).get m = (c.get m).map (relCellT R β m) := rfl

theorem relCellT_props (R : TRes K) (β : Life) (m : BoCa.Loc) (ψ : TCell K) :
    (relCellT R β m ψ).erase = ψ.erase ∧ (relCellT R β m ψ).wit = ψ.wit ∧
    (relCellT R β m ψ).kind = ψ.kind := by
  unfold relCellT
  split
  · rename_i h
    exact ⟨by simp [CellUT.immOf, CellUT.erase], by simp, by simp [h.1]⟩
  · exact ⟨rfl, rfl, rfl⟩

/-! ### Templates and canonical images -/

/-- A typed image of an escrow `R` of code `T` holding `v`, at some lifetime, with `ag` defined
and covered: what `TW.reb` asks of an image (`TmplSpec`), the typing read through `interp`. -/
def TmplSpecT (K : WCactus) (Θ : CodeTy) (R : TRes K) (T : KTy) (v : BoCa.Val) (c : TRes K) :
    Prop :=
  ∃ β : Life, ResUT.Reb β R c ∧ ((T.immReborrow β).interp Θ).P K v c ∧ (∃ A, AgWT c A) ∧
    CovR (sem Θ) K c

open Classical in
/-- **The template of an escrow** (`tmpl`): one typed image, the `Classical` choice. -/
def tmplT (K : WCactus) (Θ : CodeTy) (R : TRes K) (T : KTy) (v : BoCa.Val) : TRes K :=
  if h : ∃ c, TmplSpecT K Θ R T v c then Classical.choose h else PMap.empty

theorem tmplT_spec {Θ : CodeTy} {R : TRes K} {T : KTy} {v : BoCa.Val}
    (h : ∃ c, TmplSpecT K Θ R T v c) : TmplSpecT K Θ R T v (tmplT K Θ R T v) := by
  unfold tmplT; rw [dif_pos h]; exact Classical.choose_spec h

/-- The record's template (`tmpl r`). -/
def tmplR (K : WCactus) (Θ : CodeTy) (r : FrameRecT K) : TRes K := tmplT K Θ r.R r.T r.v

/-- **The canonical image at `β`** (`canon`): the record's template re-taken at `β`. -/
def canonT (K : WCactus) (Θ : CodeTy) (r : FrameRecT K) (β : Life) : TRes K :=
  relResT r.R β (tmplR K Θ r)

theorem canonT_get {Θ : CodeTy} {r : FrameRecT K} {β : Life} {m : BoCa.Loc} {ψ : TCell K}
    (e : (canonT K Θ r β).get m = some ψ) :
    ∃ ζ, (tmplR K Θ r).get m = some ζ ∧ ψ.wit = ζ.wit := by
  rw [canonT, relResT_get] at e
  obtain ⟨ζ, eζ, rfl⟩ := Option.map_eq_some_iff.mp e
  exact ⟨ζ, eζ, (relCellT_props r.R β m ζ).2.1⟩

/-- Two canonical images of one record carry the same witness at every location both hold. -/
theorem canonT_wit {Θ : CodeTy} {r : FrameRecT K} {β β' : Life} {m : BoCa.Loc} {ψ ψ' : TCell K}
    (e : (canonT K Θ r β).get m = some ψ) (e' : (canonT K Θ r β').get m = some ψ') :
    ψ.wit = ψ'.wit := by
  obtain ⟨ζ, eζ, w⟩ := canonT_get e
  obtain ⟨ζ', eζ', w'⟩ := canonT_get e'
  rw [eζ] at eζ'; cases Option.some.inj eζ'
  exact w.trans w'.symm

open Classical in
/-- **A chain view's template** (`tmplD`), chosen at the current tree. -/
def tmplDT (K : WCactus) (Θ : CodeTy) (S₀ : KTy) (u₀ : BoCa.Val) (w₀ : TRes K) : TRes K :=
  tmplT K Θ w₀ S₀ u₀

/-- **The canonical image of a chain view at `β`** (`canonD`). -/
def canonDT (K : WCactus) (Θ : CodeTy) (S₀ : KTy) (u₀ : BoCa.Val) (w₀ : TRes K) (β : Life) :
    TRes K :=
  relResT w₀ β (tmplDT K Θ S₀ u₀ w₀)

/-! ### Records re-read -/

/-- **A record re-read** at a grown tree: location, value, code kept; escrow re-read. -/
def RecRR {K K' : WCactus} (Θ' : CodeTy) (r : FrameRecT K) (r' : FrameRecT K') : Prop :=
  r'.le = r.le ∧ r'.v = r.v ∧ r'.T = r.T ∧ RR (sem Θ') r.R r'.R

/-! ### The typed world over the tree -/

/-- **`TWNC` over the tree world.** `TWNT K Θ W ps rs`: the configuration `W` at the tree `K` and
the code typing `Θ`, reached from `∅` by the operations; `ps` the frames taken and not ended,
`rs` with their lineages. `TWNC`'s constructors, read over `TRes K`, and `reread`. -/
inductive TWNT : (K : WCactus) → CodeTy → TRes K → List (FrameRecT K) → List (FrameRecT K) →
    Prop
  | empty {K : WCactus} {Θ : CodeTy} : TWNT K Θ PMap.empty [] []
  | alloc {K : WCactus} {Θ : CodeTy} {W W' : TRes K} {ps rs : List (FrameRecT K)}
      {μ : BoCa.Loc → Option BoCa.Val} {l : BoCa.Loc} {v : BoCa.Val} :
      TWNT K Θ W ps rs → ResUT.Lower W μ → μ l = none →
      ResUT.CompS W (ResUT.single l (CellUT.ownOf v)) W' → ResUT.Valid W' → TWNT K Θ W' ps rs
  | immFrame {K : WCactus} {Θ : CodeTy} {W X Z R W' : TRes K} {ps rs ds : List (FrameRecT K)}
      {l : BoCa.Loc} {v : BoCa.Val} {α : Life} (T : KTy) (h : R.InStratum (TSet.single α)) :
      TWNT K Θ W ps rs → ResUT.CompS (ResUT.single l (CellUT.ownOf v)) R X →
      ResUT.CompS X Z W → (T.interp Θ).P K v R →
      ResUT.CompS (ResUT.single l (CellUT.immOf (TSet.single α) v R h)) Z W' →
      ResUT.Valid W' → (∀ d, d ∈ ds ↔ DescT ⟨l, v, R, T⟩ d) →
      TWNT K Θ W' (⟨l, v, R, T⟩ :: ps) (⟨l, v, R, T⟩ :: (ds ++ rs))
  | reb {K : WCactus} {Θ : CodeTy} {W W' c : TRes K} {ps rs : List (FrameRecT K)}
      (r : FrameRecT K) {le : BoCa.Loc} {s : TSet} {β : Life} {hs : r.R.InStratum s} :
      TWNT K Θ W ps rs → r ∈ rs → W.get le = some (CellUT.immOf s r.v r.R hs) →
      ResUT.Reb β r.R c → ((r.T.immReborrow β).interp Θ).P K r.v c →
      RebRecLeT K W ps r.R β → c = canonT K Θ r β → ResUT.CompS W c W' → ResUT.Valid W' →
      TWNT K Θ W' ps rs
  | rebDeep {K : WCactus} {Θ : CodeTy} {W W' c : TRes K} {ps rs : List (FrameRecT K)}
      (r : FrameRecT K) {p : Option BoCa.Loc} {l₀ : BoCa.Loc} {S₀ : KTy} {u₀ : BoCa.Val}
      {s : TSet} {w₀ : TRes K} {hs : w₀.InStratum s} {β : Life} :
      TWNT K Θ W ps rs → r ∈ rs → ChainT r.R r.T r.v p l₀ S₀ u₀ →
      W.get l₀ = some (CellUT.immOf s u₀ w₀ hs) → ResUT.Reb β w₀ c →
      ((S₀.immReborrow β).interp Θ).P K u₀ c →
      RebCellLeT K W l₀ β → RebRecLeT K W ps w₀ β → c = canonDT K Θ S₀ u₀ w₀ β →
      ResUT.CompS W c W' → ResUT.Valid W' → TWNT K Θ W' ps rs
  | mutFold {K : WCactus} {Θ : CodeTy} {W X Z ρ W' : TRes K} {ps rs : List (FrameRecT K)}
      {l : BoCa.Loc} {v : BoCa.Val} {b : TSet} [Fact (K.Anti b)] {hstr : ρ.InStratum b}
      {P : BoCa.Val → SPropST BoCa.Loc BoCa.Val K b} {hw : P v ⟨ρ, hstr⟩} :
      TWNT K Θ W ps rs → ResUT.CompS (ResUT.single l (CellUT.ownOf v)) ρ X →
      ResUT.CompS X Z W → ResUT.CompS (ResUT.single l (CellUT.mutOf b v ρ hstr P hw)) Z W' →
      ResUT.Valid W' → TWNT K Θ W' ps rs
  | mutUnfold {K : WCactus} {Θ : CodeTy} {W X Z ρ W' : TRes K} {ps rs : List (FrameRecT K)}
      {l : BoCa.Loc} {v : BoCa.Val} {b : TSet} [Fact (K.Anti b)] {hstr : ρ.InStratum b}
      {P : BoCa.Val → SPropST BoCa.Loc BoCa.Val K b} {hw : P v ⟨ρ, hstr⟩} :
      TWNT K Θ W ps rs → ResUT.CompS (ResUT.single l (CellUT.mutOf b v ρ hstr P hw)) Z W →
      ResUT.CompS (ResUT.single l (CellUT.ownOf v)) ρ X → ResUT.CompS X Z W' →
      ResUT.Valid W' → TWNT K Θ W' ps rs
  | free {K : WCactus} {Θ : CodeTy} {W W' : TRes K} {ps rs : List (FrameRecT K)} {l : BoCa.Loc}
      {v : BoCa.Val} :
      TWNT K Θ W ps rs → ResUT.CompS (ResUT.single l (CellUT.ownOf v)) W' W →
      ResUT.Valid W' → TWNT K Θ W' ps rs
  | store {K : WCactus} {Θ : CodeTy} {W Z W' : TRes K} {ps rs : List (FrameRecT K)}
      {l : BoCa.Loc} {v₁ v₂ : BoCa.Val} :
      TWNT K Θ W ps rs → ResUT.CompS (ResUT.single l (CellUT.ownOf v₁)) Z W →
      ResUT.CompS (ResUT.single l (CellUT.ownOf v₂)) Z W' → ResUT.Valid W' →
      TWNT K Θ W' ps rs
  | immEnd {K : WCactus} {Θ : CodeTy} {W Y X' W' : TRes K} {ps rs ps' rs' : List (FrameRecT K)}
      (r : FrameRecT K) {s : TSet} {hs : r.R.InStratum s} :
      TWNT K Θ W ps rs → r ∈ ps →
      ResUT.CompS (ResUT.single r.le (CellUT.immOf s r.v r.R hs)) Y W →
      ResUT.CompS (ResUT.single r.le (CellUT.ownOf r.v)) r.R X' → ResUT.CompS X' Y W' →
      ResUT.Valid W' → (∀ r', r' ∈ ps' ↔ (r' ∈ ps ∧ r' ≠ r)) →
      (∀ d, d ∈ rs' ↔ ∃ p ∈ ps', DescRT p d) → TWNT K Θ W' ps' rs'
  | rebEnd {K : WCactus} {Θ : CodeTy} {W W' c : TRes K} {ps rs : List (FrameRecT K)}
      (r : FrameRecT K) {le : BoCa.Loc} {s : TSet} {β : Life} {hs : r.R.InStratum s} :
      TWNT K Θ W ps rs → r ∈ rs → W'.get le = some (CellUT.immOf s r.v r.R hs) →
      ResUT.Reb β r.R c → ResUT.CompS W' (c.restrictDom r.R.exclPart) W →
      RebEndRecT K W' rs r.R β → TWNT K Θ W' ps rs
  | rebEndDeep {K : WCactus} {Θ : CodeTy} {W W' c : TRes K} {ps rs : List (FrameRecT K)}
      (r : FrameRecT K) {p : Option BoCa.Loc} {l₀ : BoCa.Loc} {S₀ : KTy} {u₀ : BoCa.Val}
      {s : TSet} {w₀ : TRes K} {hs : w₀.InStratum s} {β : Life} :
      TWNT K Θ W ps rs → r ∈ rs → ChainT r.R r.T r.v p l₀ S₀ u₀ →
      W'.get l₀ = some (CellUT.immOf s u₀ w₀ hs) → ResUT.Reb β w₀ c →
      ResUT.CompS W' (c.restrictDom w₀.exclPart) W → RebEndRecT K W' rs w₀ β →
      TWNT K Θ W' ps rs
  /-- **The tree grows, or a location no `mut` cell is at is re-typed**: the world and every
  record re-read. -/
  | reread {K K' : WCactus} {Θ Θ' : CodeTy} {W : TRes K} {W' : TRes K'}
      {ps rs : List (FrameRecT K)} {ps' rs' : List (FrameRecT K')} :
      TWNT K Θ W ps rs → K.Ext K' → AgreeOn Θ Θ' W → RR (sem Θ') W W' →
      List.Forall₂ (RecRR Θ') ps ps' → List.Forall₂ (RecRR Θ') rs rs' → TWNT K' Θ' W' ps' rs'

theorem TWNT.valid {K : WCactus} {Θ : CodeTy} {W : TRes K} {ps rs : List (FrameRecT K)}
    (h : TWNT K Θ W ps rs) : ResUT.Valid W := by
  induction h with
  | empty => exact ⟨PMap.empty, ⟨PMap.empty, PMap.empty, exW_empty, agW_empty,
      G.comp_empty_right _⟩⟩
  | alloc _ _ _ _ hv _ => exact hv
  | immFrame _ _ _ _ _ _ _ hv _ _ => exact hv
  | reb _ _ _ _ _ _ _ _ _ hv _ => exact hv
  | rebDeep _ _ _ _ _ _ _ _ _ _ _ hv _ => exact hv
  | mutFold _ _ _ _ hv _ => exact hv
  | mutUnfold _ _ _ _ hv _ => exact hv
  | free _ _ hv _ => exact hv
  | store _ _ _ hv _ => exact hv
  | immEnd _ _ _ _ _ _ hv _ _ _ => exact hv
  | rebEnd _ _ _ _ _ hW _ ih => exact (ResUT.Valid.split hW ih).1
  | rebEndDeep _ _ _ _ _ _ hW _ ih => exact (ResUT.Valid.split hW ih).1
  | reread _ _ _ hr _ _ ih => exact WitRel.ResUT.Valid.sim ih hr.rsim

/-- A covered record is its own re-reading where nothing grows. -/
theorem RecRR.refl {Θ : CodeTy} {r : FrameRecT K} (hR : CovR (sem Θ) K r.R) :
    RecRR (K' := K) Θ r r :=
  ⟨rfl, rfl, rfl, RR.refl hR⟩

/-- **Nothing changes where nothing grows**: `reread` at `K' = K`, `Θ' = Θ` is the world itself,
by `RR.refl`. -/
theorem TWNT.reread_refl {Θ : CodeTy} {W : TRes K} {ps rs : List (FrameRecT K)}
    (h : TWNT K Θ W ps rs) (hW : CovR (sem Θ) K W)
    (hps : ∀ r ∈ ps, CovR (sem Θ) K r.R) (hrs : ∀ r ∈ rs, CovR (sem Θ) K r.R) :
    TWNT K Θ W ps rs :=
  .reread h (WCactus.Ext.refl K) (AgreeOn.refl Θ W) (RR.refl hW)
    (List.forall₂_same.mpr fun r hr => RecRR.refl (hps r hr))
    (List.forall₂_same.mpr fun r hr => RecRR.refl (hrs r hr))

end BoCa.Fig16.Tree.Wp

end

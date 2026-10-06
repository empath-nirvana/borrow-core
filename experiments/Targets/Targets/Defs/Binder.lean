import Restrat
import Targets.Defs.World

/-!
# Targets — the freeze binder's actions (DESIGN §2, D11)

"Freeze is a binder over internal locations, lifetimes and instances; resume and placement
instantiate it" (user, 2026-10-04).  Each part has its own action.

* **Locations.**  A permutation `π : Equiv.Perm Loc` acts on everything that names a location:
  terms, values, contexts and heaps (`Expr.renameLoc`, `Val.renameLoc`, `Kont.renameLoc`,
  `Heap.renameLoc`: local copies of `TwoRun/Rename.lean`'s `Expr.rename`, `Kont.rename`,
  `Heap.rename`, recorded as a duplicate because `TwoRun` does not build on this branch);
  resources (`ResU.mapLoc`: keys renamed, and the locations inside cells — values, witnesses and
  stored predicates — by the stratum recursion Restrat's `relRU` uses, a stored predicate taken to
  its image, which for a permutation is its conjugate); records and indices fieldwise; predicates,
  entries and tables by conjugation.  Array steps compute `ℓ + j`, so the action is taken at
  permutations **affine on the blocks** a configuration's arrays name (`BlockAffine`).
* **Lifetimes.**  A re-stratification `θ : Restrat.Emb c` (strictly monotone on `Life = ℕᵒᵈ`, the
  identity at and above the cut `c`) acts on resources by `θ.relRU`, on substitutions by
  `LSub.mapN θ.toNat`, on records and indices fieldwise, and on predicates, entries and tables by
  direct image (`θ` is injective, not invertible).
* **Instances.**  Names are static per site (OQ-14 (a)), so the instance half is vacuous today.
* **The lend stack.**  W's own action on σ (`StkAct`): a group action of location permutations and
  a monoid action of re-stratifications, fixing `nil`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Locations: terms, values, contexts, heaps -/

/-- `e` with every location `ℓ` replaced by `π ℓ` (`TwoRun`'s `Expr.rename` at a permutation). -/
def _root_.BoCa.Expr.renameLoc (π : Equiv.Perm Loc) : Expr → Expr
  | .var i         => .var i
  | .unit          => .unit
  | .pair e₁ e₂    => .pair (e₁.renameLoc π) (e₂.renameLoc π)
  | .inj₁ e        => .inj₁ (e.renameLoc π)
  | .inj₂ e        => .inj₂ (e.renameLoc π)
  | .lam b         => .lam (b.renameLoc π)
  | .loc ℓ         => .loc (π ℓ)
  | .prim p        => .prim p
  | .seq e₁ e₂     => .seq (e₁.renameLoc π) (e₂.renameLoc π)
  | .letpair e₁ e₂ => .letpair (e₁.renameLoc π) (e₂.renameLoc π)
  | .case e e₁ e₂  => .case (e.renameLoc π) (e₁.renameLoc π) (e₂.renameLoc π)
  | .app f a       => .app (f.renameLoc π) (a.renameLoc π)

theorem isVal_renameLoc (π : Equiv.Perm Loc) {e : Expr} (h : IsVal e) : IsVal (e.renameLoc π) := by
  induction h with
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | inj₁ _ ih => exact .inj₁ ih
  | inj₂ _ ih => exact .inj₂ ih
  | lam => exact .lam
  | loc => exact .loc
  | prim => exact .prim
  | storeV _ ih => exact .storeV ih

/-- `v` with every location `ℓ` replaced by `π ℓ`. -/
def _root_.BoCa.Val.renameLoc (π : Equiv.Perm Loc) (v : Val) : Val :=
  ⟨v.1.renameLoc π, isVal_renameLoc π v.2⟩

/-- `K` with every location `ℓ` replaced by `π ℓ` (`TwoRun`'s `Kont.rename`). -/
def _root_.BoCa.BoLo.Kont.renameLoc (π : Equiv.Perm Loc) : Kont → Kont
  | .hole          => .hole
  | .pairL K e     => .pairL (K.renameLoc π) (e.renameLoc π)
  | .pairR v K     => .pairR (v.renameLoc π) (K.renameLoc π)
  | .letpair K e   => .letpair (K.renameLoc π) (e.renameLoc π)
  | .case K e₁ e₂  => .case (K.renameLoc π) (e₁.renameLoc π) (e₂.renameLoc π)
  | .appR f K      => .appR (f.renameLoc π) (K.renameLoc π)
  | .appL K v      => .appL (K.renameLoc π) (v.renameLoc π)
  | .seq K e       => .seq (K.renameLoc π) (e.renameLoc π)
  | .inj₁ K        => .inj₁ (K.renameLoc π)
  | .inj₂ K        => .inj₂ (K.renameLoc π)

/-- The cell at `ℓ` moved to `π ℓ`, its value renamed (`TwoRun`'s `Heap.rename`). -/
def _root_.BoCa.BoLo.Heap.renameLoc (π : Equiv.Perm Loc) (μ : Heap) : Heap :=
  fun ℓ => (μ (π.symm ℓ)).map (Val.renameLoc π)

/-! ### Locations: resources, by the stratum recursion -/

/-- A partial map with its keys moved by `π`. -/
def pmapRekey {A : Type} (π : Equiv.Perm Loc) (p : PMap Loc A) : PMap Loc A where
  get l := p.get (π.symm l)
  finite := by
    obtain ⟨d, hd⟩ := p.finite
    exact ⟨d.map π, fun l hl => List.mem_map.mpr ⟨π.symm l, hd _ hl, by simp⟩⟩

/-- One layer of the location action on cells, given the action on the strata above. -/
def locLayer (π : Equiv.Perm Loc) (α : Life)
    (rec : ∀ β, α < β → Cell Loc Val β → Cell Loc Val β) :
    CellF Loc Val α (fun β _ => Cell Loc Val β) → CellF Loc Val α (fun β _ => Cell Loc Val β)
  | .own v => .own (v.renameLoc π)
  | .imm i =>
      .imm ⟨i.ls, i.hls, i.v.renameLoc π,
        (pmapRekey π i.ρ).map (rec i.ls.join (lt_of_lt_of_le i.hls i.ls.meet_le_join))⟩
  | .mut m =>
      .mut ⟨m.β, m.hβ, m.v.renameLoc π, (pmapRekey π m.ρ).map (rec m.β m.hβ),
        fun v r => ∃ v₀ r₀, v = v₀.renameLoc π ∧ (pmapRekey π r₀).map (rec m.β m.hβ) = r ∧
          m.P v₀ r₀,
        ⟨m.v, m.ρ, rfl, rfl, m.hw⟩⟩

/-- `π·ψ` on `Cell_α`, by well-founded recursion on the stratum, as Restrat's `relC`. -/
def cellLoc (π : Equiv.Perm Loc) : ∀ α : Life, Cell Loc Val α → Cell Loc Val α :=
  WellFounded.fix (invImage OrderDual.ofDual Nat.lt_wfRel).wf
    (C := fun α => Cell Loc Val α → Cell Loc Val α)
    (fun α rec x => Cell.ofF (locLayer π α (fun β h => rec β h) x.toF))

/-- `π·ρ` on `Res_α`. -/
def resLoc (π : Equiv.Perm Loc) (α : Life) (ρ : Res Loc Val α) : Res Loc Val α :=
  (pmapRekey π ρ).map (cellLoc π α)

/-- A stored invariant moved by `π`: its image. -/
def predLoc (π : Equiv.Perm Loc) (β : Life) (P : Val → SProp Loc Val β) :
    Val → SProp Loc Val β :=
  fun v r => ∃ v₀ r₀, v = v₀.renameLoc π ∧ resLoc π β r₀ = r ∧ P v₀ r₀

/-- `π·ψ` on the union `Cell`. -/
def cellULoc (π : Equiv.Perm Loc) : CellU Loc Val → CellU Loc Val
  | .own v => .own (v.renameLoc π)
  | .imm i => .imm ⟨i.ls, i.v.renameLoc π, resLoc π i.ls.join i.ρ⟩
  | .mut m => .mut ⟨m.β, m.v.renameLoc π, resLoc π m.β m.ρ, predLoc π m.β m.P,
      ⟨m.v, m.ρ, rfl, rfl, m.hw⟩⟩

/-- `π·ρ` on `Res`: keys renamed, and the locations inside every cell. -/
def _root_.BoCa.Fig16.ResU.mapLoc (π : Equiv.Perm Loc) (ρ : WRes) : WRes :=
  (pmapRekey π ρ).map (cellULoc π)

/-! ### Locations: records, indices, predicates, entries, tables -/

/-- A frame record with its locations renamed, fieldwise. -/
def _root_.BoCa.Fig16.LogRel.Core.FrameRec.renameLoc (π : Equiv.Perm Loc) (r : FrameRec) :
    FrameRec :=
  ⟨π r.le, r.v.renameLoc π, r.R.mapLoc π, r.T, r.δ⟩

/-- A tagged record with its locations renamed. -/
def srecLoc (π : Equiv.Perm Loc) (x : SRec) : SRec := (x.1.renameLoc π, x.2)

/-- What suspended computations hold, its locations renamed. -/
def heldLoc (π : Equiv.Perm Loc) (h : List FrameRec × List SRec) : List FrameRec × List SRec :=
  (h.1.map (FrameRec.renameLoc π), h.2.map (srecLoc π))

/-- The composite of two re-stratifications at one cut. -/
def _root_.Restrat.Emb.comp {c : Life} (θ θ' : Restrat.Emb c) : Restrat.Emb c where
  f x := θ (θ' x)
  strictMono := θ.strictMono.comp θ'.strictMono
  fix x hx := by
    show θ.f (θ'.f x) = x
    rw [θ'.fix x hx, θ.fix x hx]

/-- **W's action on its lend stacks**: a group action of location permutations and a monoid
action of re-stratifications, fixing `nil`. -/
structure StkAct (M : SemWorld) where
  loc  : Equiv.Perm Loc → M.Stk → M.Stk
  life : ∀ {c : Life}, Restrat.Emb c → M.Stk → M.Stk
  loc_one  : ∀ σ, loc 1 σ = σ
  loc_mul  : ∀ π π' σ, loc (π * π') σ = loc π (loc π' σ)
  loc_nil  : ∀ π, loc π M.nil = M.nil
  life_id  : ∀ c σ, life (Restrat.Emb.id c) σ = σ
  life_comp : ∀ c (θ θ' : Restrat.Emb c) σ,
    life (Restrat.Emb.comp θ θ') σ = life θ (life θ' σ)
  life_nil : ∀ c (θ : Restrat.Emb c), life θ M.nil = M.nil

/-- An index with its locations renamed: `(ls.map (SRec.renameLoc π), a.loc π σ)`. -/
def idxLocAct {M : SemWorld} (a : StkAct M) (π : Equiv.Perm Loc) (i : Idx M.Stk) : Idx M.Stk :=
  (i.1.map (srecLoc π), a.loc π i.2)

/-- A predicate conjugated by `π`: `(π • Φ) i e ρ := Φ (π⁻¹ i) (π⁻¹ e) (π⁻¹ ρ)`. -/
def predLocAct {M : SemWorld} (a : StkAct M) (π : Equiv.Perm Loc)
    (Φ : Idx M.Stk → Expr → WProp) : Idx M.Stk → Expr → WProp :=
  fun i e ρ => Φ (idxLocAct a π⁻¹ i) (e.renameLoc π⁻¹) (ρ.mapLoc π⁻¹)

/-- An entry conjugated by `π`. -/
def entLocAct {M : SemWorld} (a : StkAct M) (π : Equiv.Perm Loc) (en : OpEntI (Idx M.Stk)) :
    OpEntI (Idx M.Stk) :=
  ⟨en.q, en.abort, fun i v ρ => en.PA (idxLocAct a π⁻¹ i) (v.renameLoc π⁻¹) (ρ.mapLoc π⁻¹),
    fun i v ρ => en.PB (idxLocAct a π⁻¹ i) (v.renameLoc π⁻¹) (ρ.mapLoc π⁻¹)⟩

/-- A table conjugated by `π`. -/
def tabLocAct {M : SemWorld} (a : StkAct M) (π : Equiv.Perm Loc) (T : OpTabI (Idx M.Stk)) :
    OpTabI (Idx M.Stk) :=
  fun n j => (T n j).map (entLocAct a π)

/-! ### Lifetimes -/

/-- A frame record re-stratified: its witness by `θ.relRU`, its substitution by `θ.toNat`. -/
def _root_.BoCa.Fig16.LogRel.Core.FrameRec.restrat {c : Life} (θ : Restrat.Emb c)
    (r : FrameRec) : FrameRec :=
  ⟨r.le, r.v, θ.relRU r.R, r.T, Restrat.LSub.mapN θ.toNat r.δ⟩

/-- A tagged record re-stratified: the record, and its frame lifetime moved. -/
def srecRestrat {c : Life} (θ : Restrat.Emb c) (x : SRec) : SRec := (x.1.restrat θ, θ x.2)

/-- What suspended computations hold, re-stratified. -/
def heldRestrat {c : Life} (θ : Restrat.Emb c) (h : List FrameRec × List SRec) :
    List FrameRec × List SRec :=
  (h.1.map (FrameRec.restrat θ), h.2.map (srecRestrat θ))

/-- An index re-stratified, fieldwise. -/
def idxLifeAct {M : SemWorld} (a : StkAct M) {c : Life} (θ : Restrat.Emb c) (i : Idx M.Stk) :
    Idx M.Stk :=
  (i.1.map (srecRestrat θ), a.life θ i.2)

/-- `θ ▹ Φ`: a predicate's direct image along a re-stratification. -/
def predImgLife {M : SemWorld} (a : StkAct M) {c : Life} (θ : Restrat.Emb c)
    (Φ : Idx M.Stk → Expr → WProp) : Idx M.Stk → Expr → WProp :=
  fun i e ρ => ∃ i₀ ρ₀, i = idxLifeAct a θ i₀ ∧ ρ = θ.relRU ρ₀ ∧ Φ i₀ e ρ₀

/-- An entry's direct image along a re-stratification. -/
def entImgLife {M : SemWorld} (a : StkAct M) {c : Life} (θ : Restrat.Emb c)
    (en : OpEntI (Idx M.Stk)) : OpEntI (Idx M.Stk) :=
  ⟨en.q, en.abort,
    fun i v ρ => ∃ i₀ ρ₀, i = idxLifeAct a θ i₀ ∧ ρ = θ.relRU ρ₀ ∧ en.PA i₀ v ρ₀,
    fun i v ρ => ∃ i₀ ρ₀, i = idxLifeAct a θ i₀ ∧ ρ = θ.relRU ρ₀ ∧ en.PB i₀ v ρ₀⟩

/-- A table's direct image along a re-stratification. -/
def tabImgLife {M : SemWorld} (a : StkAct M) {c : Life} (θ : Restrat.Emb c)
    (T : OpTabI (Idx M.Stk)) : OpTabI (Idx M.Stk) :=
  fun n j => (T n j).map (entImgLife a θ)

/-! ### Blocks: the ranges a configuration's arrays name -/

/-- A set of ranges `(ℓ, n)`, each the block `[ℓ, ℓ + n)`. -/
abbrev Ranges := Loc × Nat → Prop

/-- `π` moves each range of `rs` as a block. -/
def BlockAffine (π : Equiv.Perm Loc) (rs : Ranges) : Prop :=
  ∀ p, rs p → ∀ j, j < p.2 → π (p.1 + j) = π p.1 + j

/-- The ranges of the array values `Val.arr ℓ n` occurring in a term (under binders too). -/
def _root_.BoCa.Expr.arrRanges : Expr → Ranges
  | .pair (.loc ℓ) (.prim (.lit (.i32 n))), q => q = (ℓ, n.toNat)
  | .pair a b, q | .seq a b, q | .letpair a b, q | .app a b, q => a.arrRanges q ∨ b.arrRanges q
  | .inj₁ a, q | .inj₂ a, q | .lam a, q => a.arrRanges q
  | .case a b c, q => a.arrRanges q ∨ b.arrRanges q ∨ c.arrRanges q
  | _, _ => False

/-- In a heap: in a stored value. -/
def _root_.BoCa.BoLo.Heap.arrRanges (μ : Heap) : Ranges :=
  fun q => ∃ m v, μ m = some v ∧ v.1.arrRanges q

/-- In a context: in a term or value of one of its frames. -/
def _root_.BoCa.BoLo.Kont.arrRanges : Kont → Ranges
  | .hole, _ => False
  | .pairL K e, q | .letpair K e, q | .seq K e, q => K.arrRanges q ∨ e.arrRanges q
  | .pairR v K, q | .appL K v, q => K.arrRanges q ∨ v.1.arrRanges q
  | .case K e₁ e₂, q => K.arrRanges q ∨ e₁.arrRanges q ∨ e₂.arrRanges q
  | .appR f K, q => f.arrRanges q ∨ K.arrRanges q
  | .inj₁ K, q | .inj₂ K, q => K.arrRanges q

end Targets

namespace BoCa.Fig16

/-- In a resource: in a cell's value or, recursively, in its witness. -/
inductive ResU.arrRanges : BoLo.WRes → Targets.Ranges
  | val {ρ : BoLo.WRes} {m : Loc} {ψ : CellU Loc Val} {q : Loc × Nat} :
      ρ.get m = some ψ → ψ.erase.1.arrRanges q → ResU.arrRanges ρ q
  | wit {ρ : BoLo.WRes} {m : Loc} {ψ : CellU Loc Val} {q : Loc × Nat} :
      ρ.get m = some ψ → ResU.arrRanges ψ.wit q → ResU.arrRanges ρ q

end BoCa.Fig16

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)

/-- A configuration every array of which lies within the ranges `rs`. -/
def RangesIn (rs : Ranges) (μ : Heap) (e : Expr) : Prop :=
  ∀ q, (e.arrRanges q ∨ μ.arrRanges q) → ∃ p, rs p ∧ p.1 ≤ q.1 ∧ q.1 + q.2 ≤ p.1 + p.2

/-- A run every configuration of which names arrays only within the ranges `rs`. -/
inductive StepsIn (rs : Ranges) : Heap → Expr → Heap → Expr → Prop
  | refl (μ : Heap) (e : Expr) : RangesIn rs μ e → StepsIn rs μ e μ e
  | more {μ μ₁ μ' : Heap} {e e₁ e' : Expr} : RangesIn rs μ e → Step1 (ℍ := ℍ) μ e μ₁ e₁ →
      StepsIn rs μ₁ e₁ μ' e' → StepsIn rs μ e μ' e'

end Targets

end

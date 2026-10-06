import Restrat
import Targets.I.World
import Targets.B.Binder

/-!
# The interaction — the freeze binder at W, beside done (DESIGN §5 I2.c; RESTRUCTURE §3.2)

"Freeze is a binder over internal locations, lifetimes and instances; resume and placement
instantiate it" (user, 2026-10-04).  The world half of the binder: the location and lifetime
actions on resources, records, indices and tables, W's action on its lend stacks `StkAct`, the
statements `FreezeBinderLoc`, `FreezeBinderLife`, `FreezeBinder`, and the binder's first check
`NotVDenNaturalArises`.  I2's fields are exactly what the binder acts on,
so it stays available at the same `M`, beside done.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

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
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **The binder at W, locations**: equivariance under a block-affine permutation of a
configuration that arises. -/
def FreezeBinderLoc (M : SemWorld) (a : StkAct M) : Prop :=
  (∀ π fρ ps i, BlockAffine π (ResU.arrRanges fρ) →
     (M.Fam fρ ps i ↔ M.Fam (fρ.mapLoc π) (ps.map (FrameRec.renameLoc π)) (idxLocAct a π i))) ∧
  (∀ π i, M.held (idxLocAct a π i) = heldLoc π (M.held i)) ∧
  (∀ π i i' ρ, M.Ext i i' ρ ↔ M.Ext (idxLocAct a π i) (idxLocAct a π i') (ρ.mapLoc π)) ∧
  (∀ π ps i ps' i' t, M.Stop (ps, i) (ps', i') t ↔
     M.Stop (ps.map (FrameRec.renameLoc π), idxLocAct a π i)
       (ps'.map (FrameRec.renameLoc π), idxLocAct a π i') (t.renameLoc π)) ∧
  (∀ π i i' (ρ₁ ρ₂ ρ₃ : WRes), M.Upd i i' ρ₁ ρ₂ ρ₃ ↔
     M.Upd (idxLocAct a π i) (idxLocAct a π i') (ρ₁.mapLoc π) (ρ₂.mapLoc π) (ρ₃.mapLoc π)) ∧
  (∀ π fρ ps i ρ ρf b A δ v, M.Fam fρ ps i → ResU.CompS ρf ρ fρ →
     BlockAffine π (ResU.arrRanges fρ ⊔ v.1.arrRanges) →
     (M.val b A i δ v ρ ↔ M.val b A (idxLocAct a π i) δ (v.renameLoc π) (ρ.mapLoc π))) ∧
  (∀ π fρ ps i ρ ρf C δ e, M.Fam fρ ps i → ResU.CompS ρf ρ fρ →
     BlockAffine π (ResU.arrRanges fρ ⊔ e.arrRanges) →
     (M.comp C i δ e ρ ↔ M.comp C (idxLocAct a π i) δ (e.renameLoc π) (ρ.mapLoc π))) ∧
  (∀ π fρ ps i ρ ρf T en n K Φ, M.Fam fρ ps i → ResU.CompS ρf ρ fρ →
     BlockAffine π (ResU.arrRanges fρ ⊔ Kont.arrRanges K) →
     (M.share T en n i K Φ ρ ↔
       M.share (tabLocAct a π T) (entLocAct a π en) n (idxLocAct a π i) (K.renameLoc π)
         (predLocAct a π Φ) (ρ.mapLoc π)))

/-- **The binder at W, lifetimes**: instantiation along a re-stratification below a cut, of a
configuration that arises.  Every clause is forward. -/
def FreezeBinderLife (M : SemWorld) (a : StkAct M) : Prop :=
  (∀ c (θ : Restrat.Emb c) fρ ps i, M.Fam fρ ps i →
     M.Fam (θ.relRU fρ) (ps.map (FrameRec.restrat θ)) (idxLifeAct a θ i)) ∧
  (∀ c (θ : Restrat.Emb c) i, M.held (idxLifeAct a θ i) = heldRestrat θ (M.held i)) ∧
  (∀ c (θ : Restrat.Emb c) i i' ρ, M.Ext i i' ρ →
     M.Ext (idxLifeAct a θ i) (idxLifeAct a θ i') (θ.relRU ρ)) ∧
  (∀ c (θ : Restrat.Emb c) ps i ps' i' t, M.Stop (ps, i) (ps', i') t →
     M.Stop (ps.map (FrameRec.restrat θ), idxLifeAct a θ i)
       (ps'.map (FrameRec.restrat θ), idxLifeAct a θ i') t) ∧
  (∀ c (θ : Restrat.Emb c) i i' (ρ₁ ρ₂ ρ₃ : WRes), M.Upd i i' ρ₁ ρ₂ ρ₃ →
     M.Upd (idxLifeAct a θ i) (idxLifeAct a θ i') (θ.relRU ρ₁) (θ.relRU ρ₂) (θ.relRU ρ₃)) ∧
  (∀ c (θ : Restrat.Emb c) fρ ps i ρ ρf b A δ v, M.Fam fρ ps i → ResU.CompS ρf ρ fρ →
     M.val b A i δ v ρ →
     M.val b A (idxLifeAct a θ i) (Restrat.LSub.mapN θ.toNat δ) v (θ.relRU ρ)) ∧
  (∀ c (θ : Restrat.Emb c) fρ ps i ρ ρf C δ e, M.Fam fρ ps i → ResU.CompS ρf ρ fρ →
     M.comp C i δ e ρ →
     M.comp C (idxLifeAct a θ i) (Restrat.LSub.mapN θ.toNat δ) e (θ.relRU ρ)) ∧
  (∀ c (θ : Restrat.Emb c) fρ ps i ρ ρf T en n K Φ, M.Fam fρ ps i → ResU.CompS ρf ρ fρ →
     M.share T en n i K Φ ρ →
     M.share (tabImgLife a θ T) (entImgLife a θ en) n (idxLifeAct a θ i) K (predImgLife a θ Φ)
       (θ.relRU ρ))

/-- **The freeze binder at W.** -/
def FreezeBinder (M : SemWorld) (a : StkAct M) : Prop :=
  FreezeBinderLoc M a ∧ FreezeBinderLife M a

/-- **The arising check of `Restrat.Open.not_vDenNatural`'s witness at `coreW`**: some
configuration Core's world reaches holds the witness resource `MutCounterexample.ρ₀` (a `mut` cell
storing an `imm` cell at the lifetime the shift `n ↦ n + 1` leaves out) as a part of its world. -/
def NotVDenNaturalArises : Prop :=
  ∃ (fρ ρf : WRes) (ps : List FrameRec) (ls : List SRec),
    (coreW (ℍ := ℍ)).Fam fρ ps (ls, ()) ∧ ResU.CompS ρf Restrat.MutCounterexample.ρ₀ fρ

end Targets

end

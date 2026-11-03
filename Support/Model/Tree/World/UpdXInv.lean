import Support.Model.Tree.World.UpdX
import Support.Model.Tree.World.Coherent
import Support.Model.Tree.World.TInvReread

/-!
# Row 5.27's `mut` clause across a re-reading: the invariant read off the location typing

`[spec §62]`. Row 5.27's `↭` asks of a `mut` cell of the flattening that the other side carry a `mut` cell with
the same `β̄` **and the same `P̂`**. `UpdX` (`World/UpdX.lean`) compares `β̄`, re-read as
`min_{K′} β̄`. This file shows the `P̂` part needs no separate clause in `TWNT` worlds:
there a flattened `mut` cell's invariant is the location typing's type of its location, read at
the tree, on the cell's own stratum. That is exactly what the re-reading of a cell stores
(`RC.mut`'s `hP`), so on both sides of an update `P̂` is `Θ ℓ` read at that side's tree.

* **A flattened `mut` cell is a stored cell.** `○` makes a `mut` cell from two `mut` operands only
  by clause 3, and `●` makes none. In a world with one `mut` cell per location at any depth
  (`MutOne`, an invariant of `TWNT`: `TWNT.mutOne`) the two operands are one cell, and clause 3 of
  a cell with itself is the cell (`CellUT.CompR.functional` against clause 1). So every `mut` cell
  of `⦇ρ⦈` sits at depth of `ρ` (`flat_mut_cellAt`).
* **A stored cell is covered.** `CovR` reaches every depth (`CellAt.cov`), and `Cov`'s `mut` clause
  is `P̂ = Θ ℓ` read at `K` on `Res_β̄` (`flat_mut_inv`).
* **Across the re-reading** (`UpdX.inv`): at every location where both flattenings carry a `mut`
  cell, the two invariants are one type `τ = Θ ℓ`, read at `K` and at `K′`. At the identity
  re-reading two `mut` cells with one `β̄` then have one `P̂` (`updX_refl_mut`): row 5.27's clause
  as printed.
* **What the world must keep** (`InvKept`): the code typing of the end keeps the start's code at
  every unmasked `mut` cell of the start's flattening. It composes (`InvKept.trans`), is kept
  beside a frame (`InvKept.frame`) and by agreeing typings (`InvKept.of_agree`), and with `UpdX`
  gives row 5.27's `mut` clause (`UpdX.inv`).

Without `MutOne` the clause is not implied: clause 3 of two covered cells at distinct lifetimes is
not covered (`clause3_not_cov`, `World/Clause3.lean`).
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K K' : WCactus}

/-! ### `mut` cells through the walks -/

/-- Every `mut` cell of `ρ` at `x` satisfies `A x`. -/
def MutIn (A : BoCa.Loc → TCell K → Prop) (ρ : TRes K) : Prop :=
  ∀ x ψ, ρ.get x = some ψ → ψ.kind = Kind.mut → A x ψ

/-- `A` admits at most one `mut` cell per location. -/
def MutUniq (A : BoCa.Loc → TCell K → Prop) : Prop :=
  ∀ x ψ₁ ψ₂, A x ψ₁ → A x ψ₂ → ψ₁.kind = Kind.mut → ψ₂.kind = Kind.mut → ψ₁ = ψ₂

/-- A composition makes a `mut` cell only as one of its operands, when two `mut` operands are
equal. -/
def MutKeep (C : TCell K → TCell K → TCell K → Prop) : Prop :=
  ∀ ψ₁ ψ₂ ψ, C ψ₁ ψ₂ ψ → ψ.kind = Kind.mut →
    (ψ₁.kind = Kind.mut → ψ₂.kind = Kind.mut → ψ₁ = ψ₂) →
    (ψ = ψ₁ ∧ ψ₁.kind = Kind.mut) ∨ (ψ = ψ₂ ∧ ψ₂.kind = Kind.mut)

/-- **`○` keeps `mut` cells**: clause 3 of a cell with itself is clause 1. -/
theorem mutKeep_compR : MutKeep (K := K) CellUT.CompR := by
  intro ψ₁ ψ₂ ψ h hk heq
  rcases h.inv with ⟨_, rfl⟩ | ⟨k, rfl⟩ |
      ⟨s, t, _, _, v, ρ, hs, ht, P, Q, hP, hQ, e₁, e₂, rfl⟩ |
      ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, ki, -⟩ | ⟨rfl, -, ki⟩
  · exact Or.inl ⟨rfl, hk⟩
  · rw [CellUT.CompS.kind (CellUT.compS_spec _ _ k)] at hk; cases hk
  · have k₁ : ψ₁.kind = Kind.mut := by rw [e₁]; rfl
    have k₂ : ψ₂.kind = Kind.mut := by rw [e₂]; rfl
    have e := heq k₁ k₂
    subst e
    exact Or.inl ⟨CellUT.CompR.functional h (CellUT.CompR.same _), k₁⟩
  · exact Or.inl ⟨rfl, hk⟩
  · exact Or.inr ⟨rfl, hk⟩
  · rw [ki] at hk; cases hk
  · rw [ki] at hk; cases hk

/-- **`●` makes no `mut` cell.** -/
theorem mutKeep_compS : MutKeep (K := K) CellUT.CompS := by
  intro ψ₁ ψ₂ ψ h hk _
  rw [CellUT.CompS.kind h] at hk; cases hk

theorem MutIn.mono {A B : BoCa.Loc → TCell K → Prop} (hAB : ∀ x ψ, A x ψ → B x ψ)
    {ρ : TRes K} (h : MutIn A ρ) : MutIn B ρ :=
  fun x ψ e hk => hAB x ψ (h x ψ e hk)

theorem MutIn.comp {R : TCell K → TCell K → Prop} {C : TCell K → TCell K → TCell K → Prop}
    (hC : MutKeep C) {A : BoCa.Loc → TCell K → Prop} (hA : MutUniq A) {ρ₁ ρ₂ ρ : TRes K}
    (h : G.Comp R C ρ₁ ρ₂ ρ) (h₁ : MutIn A ρ₁) (h₂ : MutIn A ρ₂) : MutIn A ρ := by
  intro x ψ e hk
  rcases G.Comp.get h x with ⟨-, -, e'⟩ | ⟨ζ, e₁, -, e'⟩ | ⟨ζ, -, e₂, e'⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁, e₂, e', hc⟩
  · rw [e'] at e; cases e
  · rw [e'] at e; cases e; exact h₁ x _ e₁ hk
  · rw [e'] at e; cases e; exact h₂ x _ e₂ hk
  · rw [e'] at e; cases e
    rcases hC _ _ _ hc hk (fun k₁ k₂ => hA x _ _ (h₁ x _ e₁ k₁) (h₂ x _ e₂ k₂) k₁ k₂) with
      ⟨rfl, k⟩ | ⟨rfl, k⟩
    · exact h₁ x _ e₁ k
    · exact h₂ x _ e₂ k

theorem MutIn.bigComp {R : TCell K → TCell K → Prop} {C : TCell K → TCell K → TCell K → Prop}
    (hC : MutKeep C) {A : BoCa.Loc → TCell K → Prop} (hA : MutUniq A) {xs : List (TRes K)}
    {b : TRes K} (h : G.BigComp R C xs b) (hx : ∀ x ∈ xs, MutIn A x) : MutIn A b := by
  induction h with
  | nil => intro x ψ e; simp at e
  | cons _ hc ih =>
      exact MutIn.comp hC hA hc (hx _ (List.mem_cons_self ..))
        (ih fun x hx' => hx x (List.mem_cons_of_mem _ hx'))

theorem MutIn.restrict (ρ : TRes K) (k : Kind) :
    MutIn (CellAt ρ) (G.restrict CellUT.kind ρ k) :=
  fun _ _ e _ => .top (ResUT.restrict_eq_some.mp e).1

theorem MutUniq.of_sub {W ρ : TRes K} (hW : MutOne W)
    (hsub : ∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ) : MutUniq (CellAt ρ) :=
  fun x _ _ h₁ h₂ k₁ k₂ => hW x _ _ (hsub _ _ h₁ k₁) (hsub _ _ h₂ k₂) k₁ k₂

/-- **The exclusive walk's `mut` cells sit at depth**, in a world with one `mut` cell per
location. -/
theorem ExW.mutIn {R : TCell K → TCell K → Prop} {C : TCell K → TCell K → TCell K → Prop}
    (hC : MutKeep C) {W : TRes K} (hW : MutOne W) {ρ σ : TRes K}
    (h : G.ExW CellUT.kind CellUT.wit R C ρ σ) :
    (∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ) → MutIn (CellAt ρ) σ := by
  refine G.ExW.rec (motive_1 := fun ρ σ _ => (∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ) →
      MutIn (CellAt ρ) σ)
    (motive_2 := fun ρ w _ => (∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ) →
      ∀ q ∈ w, MutIn (CellAt ρ) q.2) ?mk ?nil ?cons h
  case mk =>
    intro ρ₀ σ₀ nm b w _ _ hb hnm hσ ih hsub
    have hu := MutUniq.of_sub hW hsub
    have hb' : MutIn (CellAt ρ₀) b := MutIn.bigComp hC hu hb fun x hx => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      exact ih hsub q hq
    exact MutIn.comp hC hu hσ (MutIn.comp hC hu hnm (MutIn.restrict _ _) (MutIn.restrict _ _)) hb'
  case nil => intro _ _ q hq; cases hq
  case cons =>
    intro ρ₀ e l w ψ hψ _ _ _ ihe ihw hsub q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact (ihe fun y φ h k => hsub y φ (.nest hψ h) k).mono fun _ _ h => .nest hψ h
    · exact ihw hsub q hq'

/-- **The aliasable walk's `mut` cells sit at depth**, in a world with one `mut` cell per
location. -/
theorem AgW.mutIn {W : TRes K} (hW : MutOne W) {ρ σ : TRes K} (h : AgWT ρ σ) :
    (∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ) → MutIn (CellAt ρ) σ := by
  refine G.AgW.rec (motive_1 := fun ρ σ _ => (∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ) →
      MutIn (CellAt ρ) σ)
    (motive_2 := fun ρ w _ => (∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ) →
      ∀ q ∈ w, MutIn (CellAt ρ) q.2)
    (motive_3 := fun ρ w _ => (∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ) →
      ∀ q ∈ w, MutIn (CellAt ρ) q.2)
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ₀ σ₀ a bm bi wm wi _ _ _ _ hbm hbi ha hσ ihm ihi hsub
    have hu := MutUniq.of_sub hW hsub
    have hbm' : MutIn (CellAt ρ₀) bm := MutIn.bigComp mutKeep_compR hu hbm fun x hx => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      exact ihm hsub q hq
    have hbi' : MutIn (CellAt ρ₀) bi := MutIn.bigComp mutKeep_compR hu hbi fun x hx => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
      exact ihi hsub q hq
    exact MutIn.comp mutKeep_compR hu hσ
      (MutIn.comp mutKeep_compR hu ha (MutIn.restrict _ _) hbm') hbi'
  case nilM => intro _ _ q hq; cases hq
  case consM =>
    intro ρ₀ e l w ψ hψ _ _ _ ihe ihw hsub q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact (ihe fun y φ h k => hsub y φ (.nest hψ h) k).mono fun _ _ h => .nest hψ h
    · exact ihw hsub q hq'
  case nilI => intro _ _ q hq; cases hq
  case consI =>
    intro ρ₀ p l w ψ hψ _ e a hex _ hp _ iha ihw hsub q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · have hsub' : ∀ y φ, CellAt ψ.wit y φ → φ.kind = Kind.mut → CellAt W y φ := fun y φ h k => hsub y φ (.nest hψ h) k
      have hu := MutUniq.of_sub hW hsub'
      exact (MutIn.comp mutKeep_compR hu hp (ExW.mutIn mutKeep_compR hW hex hsub')
        (iha hsub')).mono fun _ _ h => .nest hψ h
    · exact ihw hsub q hq'

/-- **Every `mut` cell of `⦇ρ⦈` sits at depth of `ρ`**, when `ρ`'s cells at depth are cells of a
world with one `mut` cell per location. -/
theorem flat_mut_cellAt {W ρ σ : TRes K} (hW : MutOne W)
    (hsub : ∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ) (h : ResUT.Flat ρ σ) : MutIn (CellAt ρ) σ := by
  obtain ⟨e, a, he, ha, hσ⟩ := h
  exact MutIn.comp mutKeep_compS (MutUniq.of_sub hW hsub) hσ
    (ExW.mutIn mutKeep_compS hW he hsub) (AgW.mutIn hW ha hsub)

/-! ### The invariant of a flattened `mut` cell -/

/-- A cell at depth of a covered resource is covered. -/
theorem CellAt.cov {Θ : LocTy} {ρ : TRes K} {y : BoCa.Loc} {ψ : TCell K} (h : CellAt ρ y ψ) :
    CovR Θ K ρ → Cov Θ K y ψ := by
  induction h with
  | top e => exact fun hc => hc _ _ e
  | nest e _ ih => exact fun hc => ih (Cov.wit (hc _ _ e))

/-- **The invariant of a flattened `mut` cell is the location typing's type, read at the tree on
the cell's stratum.** -/
theorem flat_mut_inv {Θ : LocTy} {W ρ σ : TRes K} (hW : MutOne W)
    (hsub : ∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ) (hc : CovR Θ K ρ) (h : ResUT.Flat ρ σ)
    {l : BoCa.Loc} {m : TMut K} (e : σ.get l = some (.mut m)) :
    ∃ τ, Θ l = some τ ∧ ∀ w r, m.P w r ↔ τ.P K w r.toU := by
  have hcov := (flat_mut_cellAt hW hsub h l _ e rfl).cov hc
  cases hcov with
  | «mut» _ _ τ hΘ hP _ => exact ⟨τ, hΘ, hP⟩

/-- A resource whose `mut` cells at depth are cells of a world with one `mut` cell per location,
and which is covered. -/
def MutCov (Θ : LocTy) (K : WCactus) (ρ : TRes K) : Prop :=
  CovR Θ K ρ ∧ ∃ W : TRes K, MutOne W ∧ ∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ

/-! ### The location typing kept at the `mut` cells of a flattening -/

/-- **`Θ′` keeps `Θ`'s code at every `mut` cell of `⦇ρ⦈` outside `E`.** The invariant a `mut` cell
stores is its location's code read at the world (`flat_mut_inv`), so this is what row 5.27's
"the same `P̂`" asks of the world when `ρ` is updated to a resource at `Θ′`.

**Departure (D2, `docs/new-core/scope-781.md` §8).** `P̂` in `↭`'s `mut` clause is read as "the
same code at `ℓ`, each side read at its own world" (`InvKept`, `XInv`), not as equal predicates.
A `○` composite's `P̂ ∧ Q̂` re-read is not the re-read of the composite, and a flattened `mut`
cell's `P̂` is its location's code (`flat_mut_inv`). At the identity re-reading the two agree
(`updX_refl_mut`). The printed technique not built: `P̂` compared as a predicate across `↭`. -/
def InvKept (Θ Θ' : CodeTy) (E : BoCa.Loc → Prop) (ρ : TRes K) : Prop :=
  ∀ σ, ResUT.Flat ρ σ → ∀ l (m : TMut K), σ.get l = some (.mut m) → ¬ E l → Θ' l = Θ l

theorem InvKept.refl (Θ : CodeTy) (E : BoCa.Loc → Prop) (ρ : TRes K) : InvKept Θ Θ E ρ :=
  fun _ _ _ _ _ _ => rfl

theorem InvKept.mono {Θ Θ' : CodeTy} {E F : BoCa.Loc → Prop} (hEF : ∀ l, E l → F l)
    {ρ : TRes K} (h : InvKept Θ Θ' E ρ) : InvKept Θ Θ' F ρ :=
  fun σ hσ l m e hF => h σ hσ l m e fun hE => hF (hEF l hE)

theorem XCell.mut_right {Θ : LocTy} {m : TMut K} {ψ' : TCell K'} (h : XCell Θ (.mut m) ψ') :
    ∃ m', ψ' = .mut m' := by
  cases ψ' with
  | own _ => cases h.1
  | imm _ => cases h.1
  | «mut» m' => exact ⟨m', rfl⟩

/-- **Along an update, kept codes compose**: an unmasked `mut` cell of the start is an unmasked
`mut` cell of the middle (`UpdX`). -/
theorem InvKept.trans {Θ₀ Θ₁ Θ₂ : CodeTy} {Θx : LocTy} {E E' : BoCa.Loc → Prop} {ρ₀ : TRes K}
    {ρ₁ : TRes K'} (h₁ : InvKept Θ₀ Θ₁ E ρ₀) (hu : UpdX Θx E E' ρ₀ ρ₁)
    (h₂ : InvKept Θ₁ Θ₂ E' ρ₁) : InvKept Θ₀ Θ₂ E ρ₀ := by
  intro σ hσ l m e hE
  obtain ⟨σa, σ₁, hσa, hσ₁, hx⟩ := hu
  obtain rfl := ResUT.Flat.functional hσa hσ
  obtain ⟨hE', ψ', e', hc⟩ := (hx l).1 _ e (by simp [CellUT.kind]) hE
  obtain ⟨m', rfl⟩ := hc.mut_right
  rw [h₂ σ₁ hσ₁ l m' e' hE', h₁ σa hσa l m e hE]

/-- **A re-typing that agrees where `ρ` holds a `mut` cell keeps every code a flattened `mut`
cell reads.** -/
theorem InvKept.of_agree {Θ Θ' : CodeTy} {E : BoCa.Loc → Prop} {ρ W : TRes K} (hW : MutOne W)
    (hsub : ∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ) (hag : AgreeOn Θ Θ' ρ) :
    InvKept Θ Θ' E ρ :=
  fun _ hσ l _ e _ => hag l ((flat_mut_cellAt hW hsub hσ l _ e rfl).holdsMut.1 rfl)

theorem compR_mut_side {ψ₁ ψ₂ ψ : TCell K} (h : CellUT.CompR ψ₁ ψ₂ ψ)
    (hk : ψ.kind = Kind.mut) : ψ₁.kind = Kind.mut ∨ ψ₂.kind = Kind.mut := by
  rcases h.inv with ⟨_, rfl⟩ | ⟨k, rfl⟩ |
      ⟨s, t, _, _, v, ρ, hs, ht, P, Q, hP, hQ, e₁, -, -⟩ |
      ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, ki, -⟩ | ⟨rfl, -, ki⟩
  · exact Or.inl hk
  · rw [CellUT.CompS.kind (CellUT.compS_spec _ _ k)] at hk; cases hk
  · exact Or.inl (by rw [e₁]; rfl)
  · exact Or.inl hk
  · exact Or.inr hk
  · rw [ki] at hk; cases hk
  · rw [ki] at hk; cases hk

theorem TCell.eq_mut {ψ : TCell K} (hk : ψ.kind = Kind.mut) : ∃ m, ψ = .mut m := by
  cases ψ with
  | own _ => cases hk
  | imm _ => cases hk
  | «mut» m => exact ⟨m, rfl⟩

/-- **A frame beside the run**: codes kept at the run's part, and the re-typing agreeing at the
frame's `mut` cells, keep the codes at the composite. -/
theorem InvKept.frame {Θ Θ' : CodeTy} {E : BoCa.Loc → Prop} {ρ₁ ρ₂ ρ W : TRes K}
    (hc : ResUT.CompS ρ₁ ρ₂ ρ) (h₁ : InvKept Θ Θ' E ρ₁) (hW : MutOne W)
    (hsub : ∀ y φ, CellAt ρ₂ y φ → φ.kind = Kind.mut → CellAt W y φ) (hag : AgreeOn Θ Θ' ρ₂) :
    InvKept Θ Θ' E ρ := by
  intro σ hσ l m e hE
  obtain ⟨σ₁, σ₂, hσ₁, hσ₂, hσc⟩ := BoLo.flat_compR hc hσ
  have side₁ : ∀ ψ, σ₁.get l = some ψ → ψ.kind = Kind.mut → Θ' l = Θ l := fun ψ e₁ k => by
    obtain ⟨m₁, rfl⟩ := TCell.eq_mut k
    exact h₁ σ₁ hσ₁ l m₁ e₁ hE
  have side₂ : ∀ ψ, σ₂.get l = some ψ → ψ.kind = Kind.mut → Θ' l = Θ l := fun ψ e₂ k =>
    hag l ((flat_mut_cellAt hW hsub hσ₂ l ψ e₂ k).holdsMut.1 k)
  rcases G.Comp.get hσc l with ⟨-, -, e'⟩ | ⟨ζ, e₁, -, e'⟩ | ⟨ζ, -, e₂, e'⟩ |
      ⟨ζ₁, ζ₂, ζ, e₁, e₂, e', hcz⟩
  · rw [e'] at e; cases e
  · rw [e'] at e; cases e; exact side₁ _ e₁ rfl
  · rw [e'] at e; cases e; exact side₂ _ e₂ rfl
  · rw [e'] at e; cases e
    rcases compR_mut_side hcz rfl with k | k
    · exact side₁ _ e₁ k
    · exact side₂ _ e₂ k

/-! ### Row 5.27's `P̂` across the re-reading -/

/-- `ψ` and `ψ'` at `l`, if both `mut`, store one code `A`, kept from `Θ` to `Θ′`, read at
`(Θ, K)` and at `(Θ′, K′)`: the invariant `RC.mut` gives a re-read cell. Departure D2 (see
`InvKept`). -/
def XInv (Θ Θ' : CodeTy) (K K' : WCactus) (l : BoCa.Loc) (ψ : TCell K) (ψ' : TCell K') : Prop :=
  ∀ m m', ψ = .mut m → ψ' = .mut m' →
    ∃ A, Θ l = some A ∧ Θ' l = some A ∧ (∀ w r, m.P w r ↔ (A.interp Θ).P K w r.toU) ∧
      (∀ w r, m'.P w r ↔ (A.interp Θ').P K' w r.toU)

theorem sem_some {Θ : CodeTy} {l : BoCa.Loc} {τ : KSem} (h : sem Θ l = some τ) :
    ∃ A, Θ l = some A ∧ τ = A.interp Θ := by
  unfold sem at h
  cases e : Θ l with
  | none => rw [e] at h; cases h
  | some A => rw [e] at h; exact ⟨A, rfl, (Option.some.inj h).symm⟩

/-- **Row 5.27's `P̂` across the re-reading.** Where the two flattenings of an update carry a
`mut` cell at an unmasked `ℓ`, the two invariants are one code `A`, kept from `Θ` to `Θ′`, read at
each side's world. Together with `UpdX`'s `β̄` clause this is the printed
`mut(β, _, _, P̂) ⇔ mut(β, _, _, P̂)` with `P̂` re-read as `RC.mut` re-reads it. -/
theorem UpdX.inv {Θx : LocTy} {Θ Θ' : CodeTy} {E E' : BoCa.Loc → Prop} {ρ : TRes K}
    {ρ' : TRes K'} (h : UpdX Θx E E' ρ ρ') (hm : MutCov (sem Θ) K ρ) (hm' : MutCov (sem Θ') K' ρ')
    (hk : InvKept Θ Θ' E ρ) :
    ∃ σ σ', ResUT.Flat ρ σ ∧ ResUT.Flat ρ' σ' ∧ (∀ l, XOpt Θx (E l) (E' l) (σ.get l) (σ'.get l)) ∧
      ∀ l ψ ψ', σ.get l = some ψ → σ'.get l = some ψ' → ¬ E l → XInv Θ Θ' K K' l ψ ψ' := by
  obtain ⟨σ, σ', hσ, hσ', hx⟩ := h
  obtain ⟨hc, W, hW, hsub⟩ := hm
  obtain ⟨hc', W', hW', hsub'⟩ := hm'
  refine ⟨σ, σ', hσ, hσ', hx, fun l ψ ψ' e e' hE m m' hψ hψ' => ?_⟩
  subst hψ hψ'
  obtain ⟨τ, hΘ, hP⟩ := flat_mut_inv hW hsub hc hσ e
  obtain ⟨τ', hΘ', hP'⟩ := flat_mut_inv hW' hsub' hc' hσ' e'
  obtain ⟨A, hA, rfl⟩ := sem_some hΘ
  obtain ⟨A', hA', rfl⟩ := sem_some hΘ'
  have hl := hk σ hσ l m e hE
  rw [hl, hA] at hA'
  cases Option.some.inj hA'
  exact ⟨A, hA, hl.trans hA, hP, hP'⟩

/-- **At the identity re-reading the clause is row 5.27's**: two `mut` cells with one `β̄` and
the invariants `XInv` gives have one `P̂`. -/
theorem updX_refl_mut {Θ : CodeTy} {l : BoCa.Loc} {m m' : TMut K}
    (h : XInv Θ Θ K K l (.mut m) (.mut m')) :
    ∀ w (r : ResT BoCa.Loc BoCa.Val K m.ls) (r' : ResT BoCa.Loc BoCa.Val K m'.ls),
      r.toU = r'.toU → (m.P w r ↔ m'.P w r') := by
  intro w r r' er
  obtain ⟨A, -, -, hP, hP'⟩ := h m m' rfl rfl
  rw [hP, hP', er]

end BoCa.Fig16.Tree.Wp

end

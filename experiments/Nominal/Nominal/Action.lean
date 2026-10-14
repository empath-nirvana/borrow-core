import Nominal.Carrier

/-!
# Nominal — order automorphisms act on the carrier

An order automorphism `π : L ≃o L` acts on every layer of the carrier:

* on strata: `S ↦ π S` (`mapS`), and `Above (π T) (π S) ↔ Above T S`;
* `relC π S : Cell_S → Cell_{πS}`, by the recursion that builds `Cell` (`Restrat`'s `relC`, on a
  partial order and with set-indexed strata): every lifetime is moved by `π`, every witness is
  moved, and a `mut` cell's stored predicate `P̂ : Val → SProp_{β}` is moved to its image
  `π·P̂ (v)(ρ′) ≜ ∃ρ. ρ′ = π·ρ ∧ P̂(v)(ρ)`;
* `relU π` on the union and `relRU π` on resources.

**The action is a bijection**, with inverse the action of `π⁻¹` (`relU_symm_relU`,
`relU_relU_symm`). This is what separates it from the moves refuted on Core's carrier: there the
re-slotting is an order embedding that is not onto (`DenseCarrier`'s `exists_gap`), so a moved
stored predicate is the image on the image only, and the relation at the moved reading holds at
cells outside it (`not_reslotInvC`, `Restrat`'s `mut_not_natural`). Here `π` is onto, the image of
`P̂` is its whole transport `P̂ ∘ π⁻¹` (`pu_relU`, `img_apply`), and nothing is left outside.

Every datum moves as it should: tag and value are kept, the witness is moved (`wit_relU`), the
lifetimes are moved (`lts_relU`), the stored predicate is transported (`pu_relU`), and stratum
membership and survival are carried (`inStratum_relU`, `survives_relU`).
-/

noncomputable section
open Classical

namespace Nominal
open BoCa
open BoCa.Fig16 (PMap)

set_option linter.unusedSectionVars false

variable {L : Type} [PartialOrder L] [WellFoundedGT L]

/-! ### Strata -/

/-- `π S`. -/
def mapS (π : L ≃o L) (S : Finset L) : Finset L := S.map π.toEquiv.toEmbedding

theorem mem_mapS {π : L ≃o L} {S : Finset L} {y : L} : y ∈ mapS π S ↔ ∃ x ∈ S, π x = y :=
  Finset.mem_map

theorem mem_mapS_apply {π : L ≃o L} {S : Finset L} {x : L} : π x ∈ mapS π S ↔ x ∈ S := by
  rw [mem_mapS]
  exact ⟨fun ⟨y, hy, e⟩ => π.injective e ▸ hy, fun h => ⟨x, h, rfl⟩⟩

theorem mapS_singleton (π : L ≃o L) (b : L) : mapS π {b} = {π b} := rfl

theorem mapS_nonempty {π : L ≃o L} {S : Finset L} : (mapS π S).Nonempty ↔ S.Nonempty :=
  Finset.map_nonempty

theorem above_mapS (π : L ≃o L) {T S : Finset L} : Above (mapS π T) (mapS π S) ↔ Above T S := by
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨mapS_nonempty.mp hne, fun t ht s hs =>
      π.lt_iff_lt.mp (h (π t) (mem_mapS_apply.mpr ht) (π s) (mem_mapS_apply.mpr hs))⟩
  · rintro ⟨hne, h⟩
    refine ⟨mapS_nonempty.mpr hne, fun t' ht' s' hs' => ?_⟩
    obtain ⟨t, ht, rfl⟩ := mem_mapS.mp ht'
    obtain ⟨s, hs, rfl⟩ := mem_mapS.mp hs'
    exact π.lt_iff_lt.mpr (h t ht s hs)

theorem mapS_symm_mapS (π : L ≃o L) (S : Finset L) : mapS π.symm (mapS π S) = S := by
  ext x
  rw [mem_mapS]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := mem_mapS.mp hy
    simpa using hz
  · intro hx
    exact ⟨π x, mem_mapS_apply.mpr hx, by simp⟩

theorem mapS_union (π : L ≃o L) (S T : Finset L) : mapS π (S ∪ T) = mapS π S ∪ mapS π T :=
  Finset.map_union S T

theorem mapS_injective (π : L ≃o L) : Function.Injective (mapS π) := by
  intro S T h
  rw [← mapS_symm_mapS π S, ← mapS_symm_mapS π T, h]

/-! ### Cells, by well-founded recursion on the strata -/

/-- One layer of the action, given the action on the strata above. -/
def layer (π : L ≃o L) (S : Finset L) (rec : ∀ T, Above T S → Cell T → Cell (mapS π T)) :
    CellF S (fun T _ => Cell T) → CellF (mapS π S) (fun T _ => Cell T)
  | .own v => .own v
  | .imm i => .imm ⟨mapS π i.ls, (above_mapS π).mpr i.hls, i.v, i.ρ.map (rec i.ls i.hls)⟩
  | .mut m => .mut ⟨π m.β, (above_mapS π (T := {m.β})).mpr m.hβ, m.v,
      m.ρ.map (rec {m.β} m.hβ), fun v r => ∃ r₀, r₀.map (rec {m.β} m.hβ) = r ∧ m.P v r₀,
      ⟨m.ρ, rfl, m.hw⟩⟩

/-- `π·x` on `Cell_S`. -/
def relC (π : L ≃o L) : ∀ S : Finset L, Cell S → Cell (mapS π S) :=
  WellFounded.fix above_wf (C := fun S => Cell S → Cell (mapS π S))
    (fun S rec x => Cell.ofF (layer π S (fun T h => rec T h) x.toF))

theorem relC_eq (π : L ≃o L) (S : Finset L) (x : Cell S) :
    relC π S x = Cell.ofF (layer π S (fun T _ => relC π T) x.toF) := by
  unfold relC
  rw [WellFounded.fix_eq]

/-- `π·ρ` on `Res_S`. -/
def relR (π : L ≃o L) (S : Finset L) (ρ : Res S) : Res (mapS π S) := ρ.map (relC π S)

/-- The stored predicate of a moved `mut` cell: the image. -/
def relP (π : L ≃o L) (b : L) (P : Val → Res ({b} : Finset L) → Prop) :
    Val → Res ({π b} : Finset L) → Prop :=
  fun v r => ∃ r₀, relR π {b} r₀ = r ∧ P v r₀

/-- `π·ψ` on the union. -/
def relU (π : L ≃o L) : CellU L → CellU L
  | .own v => .own v
  | .imm i => .imm ⟨mapS π i.ls, mapS_nonempty.mpr i.hne, i.v, relR π i.ls i.ρ⟩
  | .mut m => .mut ⟨π m.β, m.v, relR π {m.β} m.ρ, relP π m.β m.P, ⟨m.ρ, rfl, m.hw⟩⟩

/-- `π·ρ` on `Res`. -/
def relRU (π : L ≃o L) (ρ : ResU L) : ResU L := ρ.map (relU π)

@[simp] theorem relRU_get (π : L ≃o L) (ρ : ResU L) (l : Loc) :
    (relRU π ρ).get l = (ρ.get l).map (relU π) := rfl

theorem relC_toU (π : L ≃o L) (S : Finset L) (x : Cell S) :
    (relC π S x).toU = relU π x.toU := by
  rw [relC_eq]
  unfold Cell.toU
  rw [Cell.toF_ofF]
  generalize x.toF = y
  cases y <;> rfl

theorem relR_toU (π : L ≃o L) (S : Finset L) (ρ : Res S) :
    (relR π S ρ).toU = relRU π ρ.toU := by
  refine PMap.ext fun l => ?_
  show ((ρ.get l).map (relC π S)).map Cell.toU = ((ρ.get l).map Cell.toU).map (relU π)
  cases ρ.get l with
  | none => rfl
  | some x => exact congrArg some (relC_toU π S x)

/-! ### The data of a moved cell -/

/-- The image of a predicate on resources. -/
def img (π : L ≃o L) (P : Val → ResU L → Prop) : Val → ResU L → Prop :=
  fun u σ => ∃ σ₀, relRU π σ₀ = σ ∧ P u σ₀

@[simp] theorem kind_relU (π : L ≃o L) (ψ : CellU L) : (relU π ψ).kind = ψ.kind := by
  cases ψ <;> rfl

@[simp] theorem erase_relU (π : L ≃o L) (ψ : CellU L) : (relU π ψ).erase = ψ.erase := by
  cases ψ <;> rfl

theorem wit_relU (π : L ≃o L) (ψ : CellU L) : (relU π ψ).wit = relRU π ψ.wit := by
  cases ψ with
  | own v => exact PMap.ext fun l => rfl
  | imm i => exact relR_toU π _ i.ρ
  | «mut» m => exact relR_toU π _ m.ρ

theorem lts_relU (π : L ≃o L) (ψ : CellU L) : (relU π ψ).lts = mapS π ψ.lts := by
  cases ψ <;> rfl

theorem inStratum_relU (π : L ≃o L) (S : Finset L) (ψ : CellU L) :
    (relU π ψ).InStratum (mapS π S) ↔ ψ.InStratum S := by
  cases ψ with
  | own v => exact Iff.rfl
  | imm i => exact above_mapS π
  | «mut» m => exact above_mapS π (T := {m.β})

theorem inStratum_relRU (π : L ≃o L) (S : Finset L) (ρ : ResU L) :
    (relRU π ρ).InStratum (mapS π S) ↔ ρ.InStratum S := by
  constructor
  · intro h l ψ hψ
    exact (inStratum_relU π S ψ).mp (h l _ (by rw [relRU_get, hψ]; rfl))
  · intro h l ψ' hψ'
    rw [relRU_get] at hψ'
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.mp hψ'
    exact (inStratum_relU π S ψ).mpr (h l ψ hψ)

theorem inStratum_relRU_singleton (π : L ≃o L) (b : L) (ρ : ResU L) :
    (relRU π ρ).InStratum {π b} ↔ ρ.InStratum {b} :=
  inStratum_relRU π {b} ρ

theorem survives_relU (π : L ≃o L) (α : L) (ψ : CellU L) :
    (relU π ψ).Survives (π α) ↔ ψ.Survives α := by
  cases ψ with
  | own v => exact Iff.rfl
  | imm i =>
      show (∀ m ∈ mapS π i.ls, ¬ m ≤ π α) ↔ (∀ m ∈ i.ls, ¬ m ≤ α)
      constructor
      · intro h m hm
        exact fun hle => h (π m) (mem_mapS_apply.mpr hm) (π.le_iff_le.mpr hle)
      · intro h m' hm'
        obtain ⟨m, hm, rfl⟩ := mem_mapS.mp hm'
        exact fun hle => h m hm (π.le_iff_le.mp hle)
  | «mut» m => exact not_congr π.le_iff_le

theorem survives_relRU (π : L ≃o L) (α : L) (ρ : ResU L) :
    (relRU π ρ).Survives (π α) ↔ ρ.Survives α := by
  constructor
  · intro h l ψ hψ
    exact (survives_relU π α ψ).mp (h l _ (by rw [relRU_get, hψ]; rfl))
  · intro h l ψ' hψ'
    rw [relRU_get] at hψ'
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.mp hψ'
    exact (survives_relU π α ψ).mpr (h l ψ hψ)

/-- The stored predicate of a moved cell is the image of the stored predicate. -/
theorem pu_relU (π : L ≃o L) (ψ : CellU L) : (relU π ψ).pu = img π ψ.pu := by
  cases ψ with
  | own v => funext u σ; exact propext ⟨False.elim, fun ⟨_, _, h⟩ => h⟩
  | imm i => funext u σ; exact propext ⟨False.elim, fun ⟨_, _, h⟩ => h⟩
  | «mut» m =>
      funext u σ
      apply propext
      constructor
      · rintro ⟨h, r₀, hr₀, hP⟩
        refine ⟨r₀.toU, ?_, r₀.toU_inStratum, by rw [Res.toStratum_toU]; exact hP⟩
        exact (relR_toU π _ r₀).symm.trans ((congrArg Res.toU hr₀).trans (ResU.toU_toStratum σ h))
      · rintro ⟨σ₀, rfl, h₀, hP⟩
        refine ⟨(inStratum_relRU_singleton π m.β σ₀).mpr h₀, σ₀.toStratum h₀, ?_, hP⟩
        apply Res.toU_injective
        exact (relR_toU π _ _).trans ((congrArg (relRU π) (ResU.toU_toStratum σ₀ h₀)).trans
          (ResU.toU_toStratum _ _).symm)

/-! ### The action is a bijection -/

theorem relRU_congr_of {π π' : L ≃o L} {S : Finset L}
    (h : ∀ ψ, ψ.InStratum S → relU π' (relU π ψ) = ψ) {ρ : ResU L} (hρ : ρ.InStratum S) :
    relRU π' (relRU π ρ) = ρ := by
  refine PMap.ext fun l => ?_
  show (((ρ.get l).map (relU π)).map (relU π')) = ρ.get l
  cases e : ρ.get l with
  | none => rfl
  | some ψ => exact congrArg some (h ψ (hρ l ψ e))

/-- The action of `π⁻¹` undoes the action of `π`, stratum by stratum. -/
theorem relU_symm_relU_toU (π : L ≃o L) :
    ∀ (S : Finset L) (x : Cell S), relU π.symm (relU π x.toU) = x.toU := by
  intro S
  refine (above_wf (L := L)).induction
    (C := fun S => ∀ x : Cell S, relU π.symm (relU π x.toU) = x.toU) S ?_
  intro S ih
  · have hcell : ∀ T, Above T S → ∀ ψ : CellU L, ψ.InStratum T →
        relU π.symm (relU π ψ) = ψ := by
      intro T hT ψ hψ
      have := ih T hT (ψ.toStratum T hψ)
      rwa [CellU.toU_toStratum] at this
    intro x
    unfold Cell.toU
    generalize x.toF = y
    cases y with
    | own v => rfl
    | imm i =>
        refine CellU.ext_data (by rfl) (by rfl) ?_ ?_ ?_
        · rw [wit_relU, wit_relU]
          exact relRU_congr_of (hcell i.ls i.hls) (Res.toU_inStratum i.ρ)
        · rw [lts_relU, lts_relU]
          exact mapS_symm_mapS π i.ls
        · rw [pu_relU, pu_relU]
          funext u σ
          exact propext ⟨fun ⟨_, _, ⟨_, _, h⟩⟩ => h.elim, False.elim⟩
    | «mut» m =>
        refine CellU.ext_data (by rfl) (by rfl) ?_ ?_ ?_
        · rw [wit_relU, wit_relU]
          exact relRU_congr_of (hcell {m.β} m.hβ) (Res.toU_inStratum m.ρ)
        · rw [lts_relU, lts_relU]
          exact mapS_symm_mapS π {m.β}
        · rw [pu_relU, pu_relU]
          funext u σ
          apply propext
          constructor
          · rintro ⟨σ₁, rfl, σ₀, rfl, hP⟩
            have h₀ : σ₀.InStratum {m.β} := hP.1
            rw [relRU_congr_of (hcell {m.β} m.hβ) h₀]
            exact hP
          · intro hP
            have h₀ : σ.InStratum {m.β} := hP.1
            exact ⟨relRU π σ, relRU_congr_of (hcell {m.β} m.hβ) h₀, σ, rfl, hP⟩

/-- Every cell lies in the stratum `∅`. -/
theorem CellU.inStratum_empty (ψ : CellU L) : ψ.InStratum ∅ := by
  cases ψ with
  | own v => trivial
  | imm i => exact ⟨i.hne, fun _ _ _ hs => absurd hs (Finset.notMem_empty _)⟩
  | «mut» m => exact ⟨Finset.singleton_nonempty _, fun _ _ _ hs => absurd hs (Finset.notMem_empty _)⟩

/-- **`π⁻¹` undoes `π`.** -/
theorem relU_symm_relU (π : L ≃o L) (ψ : CellU L) : relU π.symm (relU π ψ) = ψ := by
  have := relU_symm_relU_toU π ∅ (ψ.toStratum ∅ ψ.inStratum_empty)
  rwa [CellU.toU_toStratum] at this

/-- **`π` undoes `π⁻¹`.** -/
theorem relU_relU_symm (π : L ≃o L) (ψ : CellU L) : relU π (relU π.symm ψ) = ψ := by
  have := relU_symm_relU π.symm ψ
  rwa [OrderIso.symm_symm] at this

theorem relRU_symm_relRU (π : L ≃o L) (ρ : ResU L) : relRU π.symm (relRU π ρ) = ρ :=
  PMap.ext fun l => by
    show (((ρ.get l).map (relU π)).map (relU π.symm)) = ρ.get l
    cases ρ.get l with
    | none => rfl
    | some ψ => exact congrArg some (relU_symm_relU π ψ)

theorem relRU_relRU_symm (π : L ≃o L) (ρ : ResU L) : relRU π (relRU π.symm ρ) = ρ := by
  have := relRU_symm_relRU π.symm ρ
  rwa [OrderIso.symm_symm] at this

/-- The action on cells, as a bijection. -/
def actU (π : L ≃o L) : CellU L ≃ CellU L where
  toFun := relU π
  invFun := relU π.symm
  left_inv := relU_symm_relU π
  right_inv := relU_relU_symm π

/-- The action on resources, as a bijection. -/
def actR (π : L ≃o L) : ResU L ≃ ResU L where
  toFun := relRU π
  invFun := relRU π.symm
  left_inv := relRU_symm_relRU π
  right_inv := relRU_relRU_symm π

theorem relU_injective (π : L ≃o L) : Function.Injective (relU (L := L) π) := (actU π).injective
theorem relRU_injective (π : L ≃o L) : Function.Injective (relRU (L := L) π) :=
  (actR π).injective
theorem relRU_surjective (π : L ≃o L) : Function.Surjective (relRU (L := L) π) :=
  (actR π).surjective

/-- **The image of a stored predicate is its whole transport**: `π·P̂ = P̂ ∘ π⁻¹`. -/
theorem img_apply (π : L ≃o L) (P : Val → ResU L → Prop) (u : Val) (σ : ResU L) :
    img π P u (relRU π σ) ↔ P u σ :=
  ⟨fun ⟨_, e, h⟩ => relRU_injective π e ▸ h, fun h => ⟨σ, rfl, h⟩⟩

theorem img_self (π : L ≃o L) {P : Val → ResU L → Prop} {u : Val} {σ : ResU L} (h : P u σ) :
    img π P u (relRU π σ) := ⟨σ, rfl, h⟩

theorem img_eq (π : L ≃o L) (P : Val → ResU L → Prop) :
    img π P = fun u σ => P u (relRU π.symm σ) := by
  funext u σ
  conv_lhs => rw [← relRU_relRU_symm π σ]
  exact propext (img_apply π P u _)

/-! ### `immOf`, `mutOf`, `own` and singletons under the action -/

theorem relU_own (π : L ≃o L) (v : Val) : relU π (CellU.own v : CellU L) = .own v := rfl

theorem relU_immOf (π : L ≃o L) (s : Finset L) (hs : s.Nonempty) (v : Val) (ρ : ResU L)
    (h : ρ.InStratum s) :
    relU π (CellU.immOf s hs v ρ h) = CellU.immOf (mapS π s) (mapS_nonempty.mpr hs) v
      (relRU π ρ) ((inStratum_relRU π s ρ).mpr h) := by
  refine CellU.ext_data (by rfl) (by rfl) ?_ ?_ ?_
  · rw [wit_relU, CellU.wit_immOf, CellU.wit_immOf]
  · rfl
  · rw [pu_relU, CellU.pu_immOf, CellU.pu_immOf]
    funext u σ
    exact propext ⟨fun ⟨_, _, h⟩ => h, False.elim⟩

theorem relU_mutOf (π : L ≃o L) (b : L) (v : Val) (ρ : ResU L) (h : ρ.InStratum {b})
    (P : Val → ResU L → Prop) (hw : P v ρ) :
    relU π (CellU.mutOf b v ρ h P hw) = CellU.mutOf (π b) v (relRU π ρ)
      ((inStratum_relRU_singleton π b ρ).mpr h) (img π P) (img_self π hw) := by
  refine CellU.ext_data (by rfl) (by rfl) ?_ ?_ ?_
  · rw [wit_relU, CellU.wit_mutOf, CellU.wit_mutOf]
  · rfl
  · rw [pu_relU, CellU.pu_mutOf, CellU.pu_mutOf]
    funext u σ
    apply propext
    constructor
    · rintro ⟨σ₀, rfl, hP, h₀⟩
      exact ⟨⟨σ₀, rfl, hP⟩, (inStratum_relRU_singleton π b σ₀).mpr h₀⟩
    · rintro ⟨⟨σ₀, rfl, hP⟩, h₁⟩
      exact ⟨σ₀, rfl, hP, (inStratum_relRU_singleton π b σ₀).mp h₁⟩

open Classical in
/-- `ℓ ↦ ψ`. -/
def ResU.single (l : Loc) (ψ : CellU L) : ResU L where
  get := fun l' => if l' = l then some ψ else none
  finite := by
    refine ⟨[l], fun l' h => ?_⟩
    by_cases e : l' = l
    · exact e ▸ List.mem_singleton.mpr rfl
    · exact absurd (if_neg e) h

theorem ResU.single_get (l : Loc) (ψ : CellU L) (l' : Loc) :
    (ResU.single l ψ).get l' = if l' = l then some ψ else none := rfl

@[simp] theorem ResU.single_get_self (l : Loc) (ψ : CellU L) :
    (ResU.single l ψ).get l = some ψ := if_pos rfl

theorem ResU.single_get_eq_some {l l' : Loc} {ψ ψ' : CellU L}
    (h : (ResU.single l ψ).get l' = some ψ') : l' = l ∧ ψ' = ψ := by
  rw [ResU.single_get] at h
  by_cases e : l' = l
  · rw [if_pos e] at h; exact ⟨e, (Option.some.inj h).symm⟩
  · rw [if_neg e] at h; cases h

theorem relRU_single (π : L ≃o L) (l : Loc) (ψ : CellU L) :
    relRU π (ResU.single l ψ) = ResU.single l (relU π ψ) := by
  refine PMap.ext fun l' => ?_
  rw [relRU_get, ResU.single_get, ResU.single_get]
  by_cases e : l' = l
  · rw [if_pos e, if_pos e]; rfl
  · rw [if_neg e, if_neg e]; rfl

@[simp] theorem relRU_empty (π : L ≃o L) : relRU π (PMap.empty : ResU L) = PMap.empty :=
  PMap.ext fun _ => rfl

theorem relRU_eq_empty (π : L ≃o L) {ρ : ResU L} : relRU π ρ = PMap.empty ↔ ρ = PMap.empty := by
  constructor
  · intro h
    rw [← relRU_symm_relRU π ρ, h, relRU_empty]
  · rintro rfl; exact relRU_empty π

theorem single_injective {l : Loc} : Function.Injective (ResU.single (L := L) l) := by
  intro ψ ψ' h
  have := congrArg (fun r => PMap.get r l) h
  simpa using this

end Nominal

end

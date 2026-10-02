import Restrat.Carrier
import Support.Model.Cells
import Support.Model.CellFacts
import Support.Model.Composition
import Support.Model.Compatibility
import Paper.S6_1_StandardLemmas.Lemmas

/-!
# Restrat — naturality of the cell constructors and of `●` and `○`

* `relU_immOf`, `relU_mutOf`: `e·imm(ᾱ, v, ρ) = imm(eᾱ, v, e·ρ)` and
  `e·mut(β, v, ρ, P̂) = mut(eβ, v, e·ρ, e·P̂)`, with `e·P̂` the image (`relS`).
* `ofS_relS`: the image commutes with `SProp_β ⊆ SProp`.
* `isImage_of_cells`: a resource every cell of which is moved is a moved resource.
* `▶◀`, `●`, `⋈`, `○`: each is preserved and reflected, and the composite of two moved cells is
  a moved cell (`Nat3`).  The generic `ρ₁ ◐ ρ₂ = ρ` (row 5.18) and `⨀` (row 5.56) inherit it
  (`comp_fwd`, `comp_bwd`, `bigComp_fwd`, `bigComp_bwd`).
-/

noncomputable section

namespace Restrat
open BoCa.Fig16

namespace Emb
variable {c : Life} (e : Emb c) {Loc Val : Type}

theorem res_toU_injective {α : Life} :
    Function.Injective (Res.toU (Loc := Loc) (Val := Val) (α := α)) := by
  intro x y h
  rw [← Res.toRes_toS x, ← Res.toRes_toS y]
  exact congrArg ResS.toRes (Subtype.ext h)

/-- The moved stored invariant, at the stratified carrier: the image. -/
def relS (b : Life) (P : Val → SPropS Loc Val b) : Val → SPropS Loc Val (e b) :=
  fun v r => ∃ r₀ : ResS Loc Val b, e.relRU r₀.val = r.val ∧ P v r₀

theorem relS_holds {b : Life} {v : Val} {ρ : ResU Loc Val} (h : ρ.InStratum b)
    {P : Val → SPropS Loc Val b} (hw : P v ⟨ρ, h⟩) :
    e.relS b P v ⟨e.relRU ρ, (e.inStratum_relRU b ρ).mpr h⟩ := ⟨⟨ρ, h⟩, rfl, hw⟩

theorem relS_iff {b : Life} (P : Val → SPropS Loc Val b) (v : Val) (ρ : ResU Loc Val)
    (h : ρ.InStratum b) (h' : (e.relRU ρ).InStratum (e b)) :
    e.relS b P v ⟨e.relRU ρ, h'⟩ ↔ P v ⟨ρ, h⟩ := by
  constructor
  · rintro ⟨r₀, h₀, hP⟩
    have : r₀ = ⟨ρ, h⟩ := Subtype.ext (e.relRU_injective h₀)
    rwa [← this]
  · intro hP; exact ⟨⟨ρ, h⟩, rfl, hP⟩

theorem toRes_relRU {α : Life} (ρ : ResU Loc Val) (h : ρ.InStratum α)
    (h' : (e.relRU ρ).InStratum (e α)) :
    e.relR α (ResS.toRes ⟨ρ, h⟩) = ResS.toRes ⟨e.relRU ρ, h'⟩ := by
  apply res_toU_injective
  rw [e.relR_toU, ResS.toU_toRes, ResS.toU_toRes]

theorem relU_immOf (s : LSet) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum s.join) :
    e.relU (CellU.immOf s v ρ h) =
      CellU.immOf (e.mapL s) v (e.relRU ρ) ((e.inStratum_relRU s.join ρ).mpr h) := by
  show CellU.imm ⟨e.mapL s, v, e.relR s.join (ResS.toRes ⟨ρ, h⟩)⟩ =
    CellU.imm ⟨e.mapL s, v, ResS.toRes ⟨e.relRU ρ, (e.inStratum_relRU s.join ρ).mpr h⟩⟩
  rw [e.toRes_relRU ρ h ((e.inStratum_relRU s.join ρ).mpr h)]
  rfl

theorem relP_toS (b : Life) (P : Val → SPropS Loc Val b) :
    e.relP b (fun v r => P v r.toS) = fun v r => e.relS b P v r.toS := by
  funext v r
  apply propext
  constructor
  · rintro ⟨r₀, h₀, hP⟩
    refine ⟨r₀.toS, ?_, hP⟩
    show e.relRU r₀.toU = r.toU
    rw [← h₀, e.relR_toU]
  · rintro ⟨r₀, h₀, hP⟩
    refine ⟨r₀.toRes, ?_, by show P v r₀.toRes.toS; rw [ResS.toS_toRes]; exact hP⟩
    apply res_toU_injective
    rw [e.relR_toU, ResS.toU_toRes]
    exact h₀

theorem relU_mutOf (b : Life) (v : Val) (ρ : ResU Loc Val) (h : ρ.InStratum b)
    (P : Val → SPropS Loc Val b) (hw : P v ⟨ρ, h⟩) :
    e.relU (CellU.mutOf b v ρ h P hw) =
      CellU.mutOf (e b) v (e.relRU ρ) ((e.inStratum_relRU b ρ).mpr h) (e.relS b P)
        (e.relS_holds h hw) := by
  show CellU.mut _ = CellU.mut _
  congr 1
  refine MutU.ext rfl rfl ?_ ?_
  · exact heq_of_eq (e.toRes_relRU ρ h _)
  · exact heq_of_eq (e.relP_toS b P)

/-! ### The image of a proposition -/

/-- The image of a proposition: `(e·P)(ρ′) ≜ ∃ρ. ρ′ = e·ρ ∧ P(ρ)`. -/
def img (P : SPropU Loc Val) : SPropU Loc Val := fun r => ∃ r₀, e.relRU r₀ = r ∧ P r₀

/-- The image of a family. -/
def relW (P : Val → SPropU Loc Val) : Val → SPropU Loc Val := fun v => e.img (P v)

theorem img_relRU (P : SPropU Loc Val) (ρ : ResU Loc Val) : e.img P (e.relRU ρ) ↔ P ρ := by
  constructor
  · rintro ⟨r₀, h₀, hP⟩; rwa [← e.relRU_injective h₀]
  · intro hP; exact ⟨ρ, rfl, hP⟩

theorem ofS_relS (b : Life) (Q : Val → SPropS Loc Val b) :
    BoLo.ofS (e.relS b Q) = e.relW (BoLo.ofS Q) := by
  funext v r
  apply propext
  constructor
  · rintro ⟨h, r₀, h₀, hQ⟩
    exact ⟨r₀.val, h₀, r₀.property, hQ⟩
  · rintro ⟨r₀, rfl, h₀, hQ⟩
    exact ⟨(e.inStratum_relRU b r₀).mpr h₀, ⟨r₀, h₀⟩, rfl, hQ⟩

/-! ### Moved resources -/

open Classical in
/-- A preimage of a cell, where one exists. -/
def preU (χ : CellU Loc Val) : Option (CellU Loc Val) :=
  if h : ∃ ψ, χ = e.relU ψ then some (Classical.choose h) else none

theorem isImage_of_cells {σ : ResU Loc Val}
    (h : ∀ l χ, σ.get l = some χ → ∃ ψ, χ = e.relU ψ) : ∃ ρ, σ = e.relRU ρ := by
  classical
  refine ⟨⟨fun l => (σ.get l).bind e.preU, ?_⟩, ?_⟩
  · obtain ⟨d, hd⟩ := σ.finite
    refine ⟨d, fun l hl => hd l (fun k => hl ?_)⟩
    show (σ.get l).bind e.preU = none
    rw [k]; rfl
  · refine PMap.ext fun l => ?_
    rw [relRU_get]
    show σ.get l = Option.map e.relU ((σ.get l).bind e.preU)
    cases hσ : σ.get l with
    | none => rfl
    | some χ =>
        have hex := h l χ hσ
        show some χ = Option.map e.relU (e.preU χ)
        unfold preU
        rw [dif_pos hex]
        exact congrArg some (Classical.choose_spec hex)

/-! ### `▶◀` and `●` -/

theorem compatS_iff (ψ₁ ψ₂ : CellU Loc Val) :
    CellU.CompatS (e.relU ψ₁) (e.relU ψ₂) ↔ CellU.CompatS ψ₁ ψ₂ := by
  rw [CellU.compatS_iff, CellU.compatS_iff, kind_relU, kind_relU, erase_relU, erase_relU,
    wit_relU, wit_relU]
  exact and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    ⟨fun h => e.relRU_injective h, fun h => by rw [h]⟩

theorem compS_fwd {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompS ψ₁ ψ₂ ψ) :
    CellU.CompS (e.relU ψ₁) (e.relU ψ₂) (e.relU ψ) := by
  obtain ⟨s₁, s₂, v, ρ, h₁, h₂, h₃, rfl, rfl, rfl⟩ := h
  rw [e.relU_immOf, e.relU_immOf, e.relU_immOf]
  refine ⟨e.mapL s₁, e.mapL s₂, v, e.relRU ρ, _, _, ?_, rfl, rfl, ?_⟩
  · rw [← e.mapL_union]; exact (e.inStratum_relRU _ ρ).mpr h₃
  · exact CellU.immOf_congr (e.mapL_union s₁ s₂) rfl rfl _ _

/-- `ψ₁ ● ψ₂ = ψ` reflected, with the composite of two moved cells moved. -/
theorem compS_bwd {ψ₁ ψ₂ χ : CellU Loc Val} (h : CellU.CompS (e.relU ψ₁) (e.relU ψ₂) χ) :
    ∃ ψ, χ = e.relU ψ ∧ CellU.CompS ψ₁ ψ₂ ψ := by
  have k : CellU.CompatS ψ₁ ψ₂ := (e.compatS_iff ψ₁ ψ₂).mp (CellU.CompS.compat h)
  have h' := CellU.compS_spec ψ₁ ψ₂ k
  exact ⟨_, CellU.CompS.functional h (e.compS_fwd h'), h'⟩

/-! ### `⋈` and `○` -/

theorem compatR_iff (ψ₁ ψ₂ : CellU Loc Val) :
    CellU.CompatR (e.relU ψ₁) (e.relU ψ₂) ↔ CellU.CompatR ψ₁ ψ₂ := by
  rw [CellU.compatR_iff, CellU.compatR_iff, kind_relU, kind_relU, erase_relU, erase_relU,
    wit_relU, wit_relU]
  exact and_congr_right fun _ =>
    ⟨fun h k₁ k₂ => e.relRU_injective (h k₁ k₂), fun h k₁ k₂ => by rw [h k₁ k₂]⟩

/-- The `mut ∘ mut` clause of `○` moves to the clause at the moved operands. -/
theorem relU_mutMut (a b : Life) (v : Val) (ρ : ResU Loc Val)
    (ha : ρ.InStratum a) (hb : ρ.InStratum b)
    (P : Val → SPropS Loc Val a) (Q : Val → SPropS Loc Val b)
    (hP : P v ⟨ρ, ha⟩) (hQ : Q v ⟨ρ, hb⟩) :
    e.relU (CellU.mutOf (a ⊓ b) v ρ ha.inf_left (SPropS.conj P Q)
        (SPropS.conj_holds ha hb hP hQ)) =
      CellU.mutOf (e a ⊓ e b) v (e.relRU ρ) ((e.inStratum_relRU a ρ).mpr ha).inf_left
        (SPropS.conj (e.relS a P) (e.relS b Q))
        (SPropS.conj_holds _ _ (e.relS_holds ha hP) (e.relS_holds hb hQ)) := by
  rw [e.relU_mutOf]
  refine CellU.mutOf_congr (e.map_inf a b) _ _ _ _ _ _ _ _ ?_
  intro r hr hr' w
  constructor
  · rintro ⟨r₀, h₀, ⟨ka, kP⟩, ⟨kb, kQ⟩⟩
    refine ⟨⟨?_, ⟨r₀.val, ka⟩, h₀, kP⟩, ⟨?_, ⟨r₀.val, kb⟩, h₀, kQ⟩⟩
    · have h₀' : e.relRU r₀.val = r := h₀
      show ResU.InStratum (e a) r
      rw [← h₀']; exact (e.inStratum_relRU a _).mpr ka
    · have h₀' : e.relRU r₀.val = r := h₀
      show ResU.InStratum (e b) r
      rw [← h₀']; exact (e.inStratum_relRU b _).mpr kb
  · rintro ⟨⟨ka, ⟨r₁, k₁⟩, h₁, kP⟩, ⟨kb, ⟨r₂, k₂⟩, h₂, kQ⟩⟩
    have h12 : r₁ = r₂ := e.relRU_injective (h₁.trans h₂.symm)
    subst h12
    exact ⟨⟨r₁, k₁.inf_left⟩, h₁, ⟨k₁, kP⟩, ⟨k₂, kQ⟩⟩

theorem compR_fwd {ψ₁ ψ₂ ψ : CellU Loc Val} (h : CellU.CompR ψ₁ ψ₂ ψ) :
    CellU.CompR (e.relU ψ₁) (e.relU ψ₂) (e.relU ψ) := by
  cases h with
  | same χ => exact CellU.CompR.same _
  | strict k =>
      have k' := (e.compatS_iff _ _).mpr k
      rw [CellU.CompS.functional (e.compS_fwd (CellU.compS_spec _ _ k))
        (CellU.compS_spec _ _ k')]
      exact CellU.CompR.strict k'
  | mutMut a b v ρ ha hb P Q hP hQ =>
      rw [e.relU_mutMut a b v ρ ha hb P Q hP hQ, e.relU_mutOf, e.relU_mutOf]
      exact CellU.CompR.mutMut _ _ _ _ _ _ _ _ _ _
  | mutOwn a v ρ ha P hP =>
      rw [e.relU_mutOf, relU_ownOf]; exact CellU.CompR.mutOwn _ _ _ _ _ _
  | ownMut a v ρ ha P hP =>
      rw [e.relU_mutOf, relU_ownOf]; exact CellU.CompR.ownMut _ _ _ _ _ _
  | immOwn s v ρ hs =>
      rw [e.relU_immOf, relU_ownOf]; exact CellU.CompR.immOwn _ _ _ _
  | ownImm s v ρ hs =>
      rw [e.relU_immOf, relU_ownOf]; exact CellU.CompR.ownImm _ _ _ _
  | immMut s v ρ hs b hb P hP =>
      rw [e.relU_immOf, e.relU_mutOf]; exact CellU.CompR.immMut _ _ _ _ _ _ _ _
  | mutImm s v ρ hs b hb P hP =>
      rw [e.relU_immOf, e.relU_mutOf]; exact CellU.CompR.mutImm _ _ _ _ _ _ _ _

/-- `ψ₁ ○ ψ₂ = ψ` reflected, with the composite of two moved cells moved. -/
theorem compR_bwd {ψ₁ ψ₂ χ : CellU Loc Val} (h : CellU.CompR (e.relU ψ₁) (e.relU ψ₂) χ) :
    ∃ ψ, χ = e.relU ψ ∧ CellU.CompR ψ₁ ψ₂ ψ := by
  obtain ⟨ψ, hψ⟩ := (e.compatR_iff ψ₁ ψ₂).mp ⟨χ, h⟩
  exact ⟨ψ, CellU.CompR.functional h (e.compR_fwd hψ), hψ⟩

/-! ### The schema `ρ₁ ◐ ρ₂ = ρ`, and `⨀` -/

/-- A cell-level relation preserved and reflected. -/
def Nat2 (R : CellU Loc Val → CellU Loc Val → Prop) : Prop :=
  ∀ ψ₁ ψ₂, R (e.relU ψ₁) (e.relU ψ₂) ↔ R ψ₁ ψ₂

/-- A cell-level composition preserved, and reflected with its value moved. -/
structure Nat3 (C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop) : Prop where
  fwd : ∀ {ψ₁ ψ₂ ψ}, C ψ₁ ψ₂ ψ → C (e.relU ψ₁) (e.relU ψ₂) (e.relU ψ)
  bwd : ∀ {ψ₁ ψ₂ χ}, C (e.relU ψ₁) (e.relU ψ₂) χ → ∃ ψ, χ = e.relU ψ ∧ C ψ₁ ψ₂ ψ

theorem nat2S : e.Nat2 (CellU.CompatS (Loc := Loc) (Val := Val)) := e.compatS_iff
theorem nat2R : e.Nat2 (CellU.CompatR (Loc := Loc) (Val := Val)) := e.compatR_iff
theorem nat3S : e.Nat3 (CellU.CompS (Loc := Loc) (Val := Val)) := ⟨e.compS_fwd, e.compS_bwd⟩
theorem nat3R : e.Nat3 (CellU.CompR (Loc := Loc) (Val := Val)) := ⟨e.compR_fwd, e.compR_bwd⟩

variable {e}

theorem compat_iff {R : CellU Loc Val → CellU Loc Val → Prop} (hR : e.Nat2 R)
    (ρ₁ ρ₂ : ResU Loc Val) : ResU.Compat R (e.relRU ρ₁) (e.relRU ρ₂) ↔ ResU.Compat R ρ₁ ρ₂ := by
  constructor
  · intro h l ψ₁ ψ₂ e₁ e₂
    exact (hR ψ₁ ψ₂).mp (h l _ _ (by rw [relRU_get, e₁]; rfl) (by rw [relRU_get, e₂]; rfl))
  · intro h l χ₁ χ₂ e₁ e₂
    rw [relRU_get] at e₁ e₂
    obtain ⟨ψ₁, f₁, rfl⟩ := Option.map_eq_some_iff.mp e₁
    obtain ⟨ψ₂, f₂, rfl⟩ := Option.map_eq_some_iff.mp e₂
    exact (hR ψ₁ ψ₂).mpr (h l ψ₁ ψ₂ f₁ f₂)

theorem optComp_fwd {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : e.Nat3 C) {o₁ o₂ o : Option (CellU Loc Val)} (h : OptComp C o₁ o₂ o) :
    OptComp C (o₁.map e.relU) (o₂.map e.relU) (o.map e.relU) := by
  cases o₁ <;> cases o₂ <;> simp only [OptComp, Option.map_none, Option.map_some] at h ⊢
  · rw [h]; rfl
  · rw [h]; rfl
  · rw [h]; rfl
  · obtain ⟨ψ, rfl, hψ⟩ := h
    exact ⟨_, rfl, hC.fwd hψ⟩

theorem optComp_bwd {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
    (hC : e.Nat3 C) {o₁ o₂ : Option (CellU Loc Val)} {o' : Option (CellU Loc Val)}
    (h : OptComp C (o₁.map e.relU) (o₂.map e.relU) o') :
    ∃ o, o' = o.map e.relU ∧ OptComp C o₁ o₂ o := by
  cases o₁ <;> cases o₂ <;> simp only [OptComp, Option.map_none, Option.map_some] at h ⊢
  · exact ⟨none, h, rfl⟩
  · exact ⟨some _, h, rfl⟩
  · exact ⟨some _, h, rfl⟩
  · obtain ⟨χ, rfl, hχ⟩ := h
    obtain ⟨ψ, rfl, hψ⟩ := hC.bwd hχ
    exact ⟨some ψ, rfl, ψ, rfl, hψ⟩

theorem comp_fwd {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} (hR : e.Nat2 R)
    (hC : e.Nat3 C) {ρ₁ ρ₂ ρ : ResU Loc Val} (h : ResU.Comp R C ρ₁ ρ₂ ρ) :
    ResU.Comp R C (e.relRU ρ₁) (e.relRU ρ₂) (e.relRU ρ) :=
  ⟨(compat_iff hR ρ₁ ρ₂).mpr h.1, fun l => optComp_fwd hC (h.2 l)⟩

theorem comp_bwd {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} (hR : e.Nat2 R)
    (hC : e.Nat3 C) {ρ₁ ρ₂ σ : ResU Loc Val}
    (h : ResU.Comp R C (e.relRU ρ₁) (e.relRU ρ₂) σ) :
    ∃ ρ, σ = e.relRU ρ ∧ ResU.Comp R C ρ₁ ρ₂ ρ := by
  obtain ⟨ρ, rfl⟩ : ∃ ρ, σ = e.relRU ρ := by
    refine e.isImage_of_cells fun l χ hχ => ?_
    obtain ⟨o, ho, -⟩ := optComp_bwd hC (h.2 l)
    rw [hχ] at ho
    cases o with
    | none => cases ho
    | some ψ => exact ⟨ψ, Option.some.inj ho⟩
  refine ⟨ρ, rfl, (compat_iff hR ρ₁ ρ₂).mp h.1, fun l => ?_⟩
  obtain ⟨o, ho, hc⟩ := optComp_bwd hC (h.2 l)
  rw [relRU_get] at ho
  rwa [Option.map_injective e.relU_injective ho]

theorem comp_iff {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} (hR : e.Nat2 R)
    (hC : e.Nat3 C) (ρ₁ ρ₂ ρ : ResU Loc Val) :
    ResU.Comp R C (e.relRU ρ₁) (e.relRU ρ₂) (e.relRU ρ) ↔ ResU.Comp R C ρ₁ ρ₂ ρ := by
  refine ⟨fun h => ?_, comp_fwd hR hC⟩
  obtain ⟨ρ', h', hc⟩ := comp_bwd hR hC h
  rwa [e.relRU_injective h']

@[simp] theorem relRU_empty : e.relRU (PMap.empty : ResU Loc Val) = PMap.empty :=
  PMap.ext fun _ => rfl

theorem bigComp_fwd {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} (hR : e.Nat2 R)
    (hC : e.Nat3 C) {σs : List (ResU Loc Val)} {ρ : ResU Loc Val} (h : BigComp R C σs ρ) :
    BigComp R C (σs.map e.relRU) (e.relRU ρ) := by
  induction h with
  | nil => rw [relRU_empty]; exact BigComp.nil
  | cons _ hc ih => exact BigComp.cons ih (comp_fwd hR hC hc)

theorem bigComp_bwd {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} (hR : e.Nat2 R)
    (hC : e.Nat3 C) : ∀ {σs : List (ResU Loc Val)} {ρ' : ResU Loc Val},
    BigComp R C (σs.map e.relRU) ρ' → ∃ ρ, ρ' = e.relRU ρ ∧ BigComp R C σs ρ
  | [], ρ', h => by
      cases h; exact ⟨PMap.empty, relRU_empty.symm, BigComp.nil⟩
  | σ :: σs, ρ', h => by
      cases h with
      | cons hb hc =>
          obtain ⟨τ, rfl, hτ⟩ := bigComp_bwd hR hC hb
          obtain ⟨ρ, rfl, hρ⟩ := comp_bwd hR hC hc
          exact ⟨ρ, rfl, BigComp.cons hτ hρ⟩

/-! ### Restrictions, singletons, deletion -/

theorem relRU_restrict (ρ : ResU Loc Val) (k : Kind) :
    e.relRU (ρ.restrict k) = (e.relRU ρ).restrict k := by
  refine PMap.ext fun l => ?_
  show Option.map e.relU ((ρ.get l).bind _) = (Option.map e.relU (ρ.get l)).bind _
  cases ρ.get l with
  | none => rfl
  | some ψ =>
      simp only [Option.bind_some, Option.map_some, kind_relU]
      split_ifs <;> rfl

theorem relRU_single (l : Loc) (ψ : CellU Loc Val) :
    e.relRU (ResU.single l ψ) = ResU.single l (e.relU ψ) := by
  classical
  refine PMap.ext fun l' => ?_
  rw [relRU_get]
  show Option.map e.relU (if l' = l then some ψ else none) = if l' = l then some _ else none
  split_ifs <;> rfl

theorem relRU_del (ρ : ResU Loc Val) (l : Loc) :
    e.relRU (ρ.del l) = (e.relRU ρ).del l := by
  classical
  refine PMap.ext fun l' => ?_
  rw [relRU_get]
  show Option.map e.relU (if l' = l then none else ρ.get l') =
    if l' = l then none else Option.map e.relU (ρ.get l')
  split_ifs <;> rfl

theorem sites_iff (ρ : ResU Loc Val) (k : Kind) (d : List Loc) :
    ResU.Sites (e.relRU ρ) k d ↔ ResU.Sites ρ k d := by
  refine and_congr_right fun _ => forall_congr' fun l => iff_congr Iff.rfl ?_
  rw [relRU_get]
  constructor
  · rintro ⟨χ, hχ, hk⟩
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.mp hχ
    exact ⟨ψ, hψ, by rwa [kind_relU] at hk⟩
  · rintro ⟨ψ, hψ, hk⟩
    exact ⟨e.relU ψ, by rw [hψ]; rfl, by rwa [kind_relU]⟩

theorem dom_iff (ρ : ResU Loc Val) (d : List Loc) :
    ResU.Dom (e.relRU ρ) d ↔ ResU.Dom ρ d := by
  refine and_congr_right fun _ => forall_congr' fun l => iff_congr Iff.rfl ?_
  rw [relRU_get]
  constructor
  · rintro ⟨χ, hχ⟩
    obtain ⟨ψ, hψ, -⟩ := Option.map_eq_some_iff.mp hχ
    exact ⟨ψ, hψ⟩
  · rintro ⟨ψ, hψ⟩
    exact ⟨e.relU ψ, by rw [hψ]; rfl⟩

end Emb

end Restrat

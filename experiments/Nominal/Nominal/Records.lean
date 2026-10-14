import Nominal.Equivariance

/-!
# Nominal — Core's frame records over the nominal carrier

`Core/FrameRecords.lean`'s records and the record-level definitions Core's relation reads, on the
nominal carrier: a record `⟨ℓ, v, R, T, δ⟩` (`FrameRecN`) with its frame lifetime (`SRecN`), the
chain positions (`ChainN`, over Core's `RefPos`), relevance (`RelN`), `KeepsN`, `CellInN`, the
Kripke order `ExtN`, coherence (`CohN`, `CohEN`) and type equality modulo readings (`TyEqN`,
`CTyEqN`).

Where Core compares a cell's lifetime `@ψ` with a lifetime, the comparison is read on the cell's
lifetime set: `@ψ ⊑ b` (`CellIn`) as "some member is at or beneath `b`" — on a chain `⊓ᾱ ⊑ b` —
and `x ⊐ ⊓ᾱ` (the list a payload is read at, `Relation`'s `ls₀`) as "`x` strictly outlives some
member" — on a chain `x ⊐ min ᾱ`.

An order automorphism `π` acts on a record by moving its resource and its reading
(`FrameRecN.act`), and on a tagged record by moving its tag too (`SRecN.act`). Every definition
here is carried by `π` and invariant (`chainN_act_iff`, `relN_act_iff`, `extN_act_iff`,
`cohEN_act_iff`, `tyEqN_map`).
-/

noncomputable section
open Classical

namespace Nominal
open BoCa
open BoCa.Fig16 (PMap Kind)
open BoCa.Fig16.LogRel.Core (VTy CTy forceE RefPos VFree)
open BoCa.Lifetime (LifeVar LifeCtx)

set_option linter.unusedSectionVars false

variable {L : Type} [PartialOrder L] [OrderTop L] [WellFoundedGT L]

/-- A frame record: the location `le`, the value `v` it held, the payload resource `R`, and the
`(T, δ)` with `R ∈ 𝒱⟦T⟧δ(v)`. -/
structure FrameRecN (L : Type) [PartialOrder L] [WellFoundedGT L] where
  le : Loc
  v : Val
  R : ResU L
  T : VTy
  δ : LSubN L

/-- A record with the lifetime of its frame. -/
abbrev SRecN (L : Type) [PartialOrder L] [WellFoundedGT L] := FrameRecN L × L

/-- The records, forgetting their lifetimes. -/
def rsOfN (ls : List (SRecN L)) : List (FrameRecN L) := ls.map Prod.fst

/-- `Chain R T v p ℓ S u`: `ℓ ↦ own(u)` in `R`, reached from `(T, v)` by `RefPos` steps whose
intermediate values are read off `R` (Core's `Chain`). -/
inductive ChainN (R : ResU L) : VTy → Val → Option Loc → Loc → VTy → Val → Prop
  | one {T : VTy} {v : Val} {l : Loc} {S : VTy} {u : Val} :
      RefPos T v l S → R.get l = some (CellU.own u) → ChainN R T v none l S u
  | step {T : VTy} {v : Val} {l₁ : Loc} {S₁ : VTy} {u₁ : Val} {p : Option Loc} {l : Loc}
      {S : VTy} {u : Val} :
      RefPos T v l₁ S₁ → R.get l₁ = some (CellU.own u₁) → ChainN R S₁ u₁ p l S u →
      ChainN R T v (some (p.getD l₁)) l S u

/-- `δ′` agrees with `δ` on the free lifetime variables of `T`. -/
def AgreeOnN (T : VTy) (δ' δ : LSubN L) : Prop := ∀ y, VFree y T → δ'.find? y = δ.find? y

/-- Coherence of a view at `m` with the records (Core's `Coh`). -/
def CohN (rs : List (FrameRecN L)) (m : Loc) (S' : VTy) (δ' : LSubN L) : Prop :=
  (∃ r ∈ rs, m = r.le ∧ S' = r.T ∧ AgreeOnN r.T δ' r.δ) ∨
  (∃ r ∈ rs, ∃ p u, ChainN r.R r.T r.v p m S' u ∧ AgreeOnN S' δ' r.δ)

mutual
/-- `S` at `δ` and `S′` at `δ′` are one value type (Core's `TyEq`). -/
def TyEqN : VTy → LSubN L → VTy → LSubN L → Prop
  | .unit, _, .unit, _ => True
  | .zero, _, .zero, _ => True
  | .unk, _, .unk, _ => True
  | .int w, _, .int w', _ => w = w'
  | .opq k, _, .opq k', _ => k = k'
  | .tensor A B, δ, .tensor A' B', δ' => TyEqN A δ A' δ' ∧ TyEqN B δ B' δ'
  | .sum A B, δ, .sum A' B', δ' => TyEqN A δ A' δ' ∧ TyEqN B δ B' δ'
  | .thunk C, δ, .thunk C', δ' => CTyEqN C δ C' δ'
  | .ref A, δ, .ref A', δ' => TyEqN A δ A' δ'
  | .bang A, δ, .bang A', δ' => TyEqN A δ A' δ'
  | .box a A, δ, .box a' A', δ' => interpN δ a = interpN δ' a' ∧ TyEqN A δ A' δ'
  | .imm a A, δ, .imm a' A', δ' => interpN δ a = interpN δ' a' ∧ TyEqN A δ A' δ'
  | .mut a A, δ, .mut a' A', δ' => interpN δ a = interpN δ' a' ∧ TyEqN A δ A' δ'
  | .tvar n, _, .tvar n', _ => n = n'
  | .mu A, δ, .mu A', δ' => TyEqN A δ A' δ'
  | .fam A, δ, .fam A', δ' => TyEqN A δ A' δ'
  | _, _, _, _ => False
/-- `C` at `δ` and `C′` at `δ′` are one computation type (Core's `CTyEq`). -/
def CTyEqN : CTy → LSubN L → CTy → LSubN L → Prop
  | .ret A, δ, .ret A', δ' => TyEqN A δ A' δ'
  | .arr A C, δ, .arr A' C', δ' => TyEqN A δ A' δ' ∧ CTyEqN C δ C' δ'
  | .amp C D, δ, .amp C' D', δ' => CTyEqN C δ C' δ' ∧ CTyEqN D δ D' δ'
  | .top, _, .top, _ => True
  | .all x b C, δ, .all x' b' C', δ' =>
      interpN δ b = interpN δ' b' ∧ ∀ α : L, CTyEqN C (δ.extend x α) C' (δ'.extend x' α)
  | .nu C, δ, .nu C', δ' => CTyEqN C δ C' δ'
  | .eff n i q A B fin C, δ, .eff n' i' q' A' B' fin' C', δ' =>
      n = n' ∧ i = i' ∧ q = q' ∧ TyEqN A δ A' δ' ∧ TyEqN B δ B' δ' ∧ CTyEqN fin δ fin' δ' ∧
        CTyEqN C δ C' δ'
  | _, _, _, _ => False
end

/-- `Coh` up to `TyEq` (Core's `CohE`). -/
def CohEN (rs : List (FrameRecN L)) (m : Loc) (S : VTy) (δ : LSubN L) : Prop :=
  ∃ S₀ δ₀, TyEqN S δ S₀ δ₀ ∧ CohN rs m S₀ δ₀

/-- `r` is relevant to `ρ`: an `imm` cell of `ρ` at `r`'s location or at a chain position. -/
def RelN (r : FrameRecN L) (ρ : ResU L) : Prop :=
  ∃ (m : Loc) (ψ : CellU L), ρ.get m = some ψ ∧ ψ.kind = .imm ∧
    (m = r.le ∨ ∃ p S u, ChainN r.R r.T r.v p m S u)

/-- `rs′` keeps the records of `rs` relevant to `ρ`. -/
def KeepsN (rs rs' : List (FrameRecN L)) (ρ : ResU L) : Prop := ∀ r ∈ rs, RelN r ρ → r ∈ rs'

/-- `ρ` holds a borrow cell no longer-lived than `b`: a `mut` or `imm` cell some lifetime of
which is at or beneath `b` (on a chain `@ψ ⊑ b`). -/
def CellInN (ρ : ResU L) (b : L) : Prop :=
  ∃ (m : Loc) (ψ : CellU L), ρ.get m = some ψ ∧ ψ.kind ≠ .own ∧ ∃ t ∈ ψ.lts, t ≤ b

/-- `ls′` extends `ls` at `ρ` (Core's `Ext`): the relevant records are kept, and the records
strictly longer-lived than any borrow cell of `ρ` are the same. -/
def ExtN (ls ls' : List (SRecN L)) (ρ : ResU L) : Prop :=
  KeepsN (rsOfN ls) (rsOfN ls') ρ ∧ ∀ b, CellInN ρ b → ∀ x : SRecN L, b < x.2 → (x ∈ ls ↔ x ∈ ls')

theorem ExtN.refl (ls : List (SRecN L)) (ρ : ResU L) : ExtN ls ls ρ :=
  ⟨fun _ h _ => h, fun _ _ _ _ => Iff.rfl⟩

/-! ### The action on records -/

/-- `π·r`: the resource and the reading moved. -/
def FrameRecN.act (π : L ≃o L) (r : FrameRecN L) : FrameRecN L :=
  ⟨r.le, r.v, relRU π r.R, r.T, r.δ.map π⟩

/-- `π·(r, t)`: the tag moved too. -/
def SRecN.act (π : L ≃o L) (x : SRecN L) : SRecN L := (x.1.act π, π x.2)

theorem LSubN.map_symm_map (π : L ≃o L) (δ : LSubN L) : (δ.map π).map π.symm = δ := by
  rw [LSubN.map_map]
  conv_rhs => rw [← LSubN.map_id δ]
  exact LSubN.map_congr fun p _ => π.symm_apply_apply p.2

theorem FrameRecN.act_symm_act (π : L ≃o L) (r : FrameRecN L) : (r.act π).act π.symm = r := by
  obtain ⟨le, v, R, T, δ⟩ := r
  simp only [FrameRecN.act, relRU_symm_relRU, LSubN.map_symm_map]

theorem FrameRecN.act_act_symm (π : L ≃o L) (r : FrameRecN L) : (r.act π.symm).act π = r := by
  have := FrameRecN.act_symm_act π.symm r
  rwa [OrderIso.symm_symm] at this

theorem SRecN.act_symm_act (π : L ≃o L) (x : SRecN L) : (x.act π).act π.symm = x := by
  obtain ⟨r, t⟩ := x
  simp only [SRecN.act, FrameRecN.act_symm_act, OrderIso.symm_apply_apply]

theorem SRecN.act_act_symm (π : L ≃o L) (x : SRecN L) : (x.act π.symm).act π = x := by
  have := SRecN.act_symm_act π.symm x
  rwa [OrderIso.symm_symm] at this

theorem FrameRecN.act_injective (π : L ≃o L) : Function.Injective (FrameRecN.act (L := L) π) :=
  fun a b h => by rw [← FrameRecN.act_symm_act π a, h, FrameRecN.act_symm_act]

theorem SRecN.act_injective (π : L ≃o L) : Function.Injective (SRecN.act (L := L) π) :=
  fun a b h => by rw [← SRecN.act_symm_act π a, h, SRecN.act_symm_act]

theorem SRecN.act_surjective (π : L ≃o L) : Function.Surjective (SRecN.act (L := L) π) :=
  fun x => ⟨x.act π.symm, SRecN.act_act_symm π x⟩

/-- `π·ls`. -/
def actL (π : L ≃o L) (ls : List (SRecN L)) : List (SRecN L) := ls.map (SRecN.act π)

theorem actL_symm_actL (π : L ≃o L) (ls : List (SRecN L)) : actL π.symm (actL π ls) = ls := by
  unfold actL
  rw [List.map_map]
  conv_rhs => rw [← List.map_id ls]
  exact List.map_congr_left fun x _ => SRecN.act_symm_act π x

theorem actL_actL_symm (π : L ≃o L) (ls : List (SRecN L)) : actL π (actL π.symm ls) = ls := by
  have := actL_symm_actL π.symm ls
  rwa [OrderIso.symm_symm] at this

theorem actL_surjective (π : L ≃o L) : Function.Surjective (actL (L := L) π) :=
  fun ls => ⟨actL π.symm ls, actL_actL_symm π ls⟩

theorem mem_actL (π : L ≃o L) {ls : List (SRecN L)} {x : SRecN L} :
    x.act π ∈ actL π ls ↔ x ∈ ls := by
  unfold actL
  rw [List.mem_map]
  exact ⟨fun ⟨y, hy, e⟩ => SRecN.act_injective π e ▸ hy, fun h => ⟨x, h, rfl⟩⟩

theorem rsOfN_actL (π : L ≃o L) (ls : List (SRecN L)) :
    rsOfN (actL π ls) = (rsOfN ls).map (FrameRecN.act π) := by
  simp [rsOfN, actL, SRecN.act, List.map_map, Function.comp_def]

theorem mem_rsOfN_act (π : L ≃o L) {ls : List (SRecN L)} {r : FrameRecN L} :
    r.act π ∈ rsOfN (actL π ls) ↔ r ∈ rsOfN ls := by
  rw [rsOfN_actL, List.mem_map]
  exact ⟨fun ⟨y, hy, e⟩ => FrameRecN.act_injective π e ▸ hy, fun h => ⟨r, h, rfl⟩⟩

/-! ### Invariance of the record layer -/

section Invariance
variable (π : L ≃o L)

theorem relRU_get_own_iff {R : ResU L} {l : Loc} {u : Val} :
    (relRU π R).get l = some (CellU.own u) ↔ R.get l = some (CellU.own u) := by
  rw [relRU_get]
  constructor
  · intro h
    obtain ⟨ψ, hψ, e⟩ := Option.map_eq_some_iff.mp h
    have hk : ψ.kind = .own := by rw [← kind_relU π, e]; rfl
    cases ψ with
    | own w => cases e; exact hψ
    | imm _ => cases hk
    | «mut» _ => cases hk
  · intro h
    rw [h]; rfl

theorem chainN_act_iff {R : ResU L} {T : VTy} {v : Val} {p : Option Loc} {m : Loc} {S : VTy}
    {u : Val} : ChainN (relRU π R) T v p m S u ↔ ChainN R T v p m S u := by
  constructor
  · intro h
    induction h with
    | one hp he => exact .one hp ((relRU_get_own_iff π).mp he)
    | step hp he _ ih => exact .step hp ((relRU_get_own_iff π).mp he) ih
  · intro h
    induction h with
    | one hp he => exact .one hp ((relRU_get_own_iff π).mpr he)
    | step hp he _ ih => exact .step hp ((relRU_get_own_iff π).mpr he) ih

theorem agreeOnN_map {T : VTy} {δ' δ : LSubN L} :
    AgreeOnN T (δ'.map π) (δ.map π) ↔ AgreeOnN T δ' δ := by
  unfold AgreeOnN
  refine forall_congr' fun y => imp_congr_right fun _ => ?_
  rw [LSubN.find?_map, LSubN.find?_map]
  exact Option.map_injective π.injective |>.eq_iff

theorem cohN_act_iff {rs : List (FrameRecN L)} {m : Loc} {S : VTy} {δ : LSubN L} :
    CohN (rs.map (FrameRecN.act π)) m S (δ.map π) ↔ CohN rs m S δ := by
  unfold CohN
  have hmem : ∀ r, r ∈ rs.map (FrameRecN.act π) ↔ ∃ r₀ ∈ rs, r₀.act π = r := fun r => List.mem_map
  constructor
  · rintro (⟨r, hr, h₁, h₂, h₃⟩ | ⟨r, hr, p, u, hc, ha⟩)
    · obtain ⟨r₀, hr₀, rfl⟩ := (hmem r).mp hr
      exact Or.inl ⟨r₀, hr₀, h₁, h₂, (agreeOnN_map π).mp h₃⟩
    · obtain ⟨r₀, hr₀, rfl⟩ := (hmem r).mp hr
      exact Or.inr ⟨r₀, hr₀, p, u, (chainN_act_iff π).mp hc, (agreeOnN_map π).mp ha⟩
  · rintro (⟨r, hr, h₁, h₂, h₃⟩ | ⟨r, hr, p, u, hc, ha⟩)
    · exact Or.inl ⟨r.act π, (hmem _).mpr ⟨r, hr, rfl⟩, h₁, h₂, (agreeOnN_map π).mpr h₃⟩
    · exact Or.inr ⟨r.act π, (hmem _).mpr ⟨r, hr, rfl⟩, p, u, (chainN_act_iff π).mpr hc,
        (agreeOnN_map π).mpr ha⟩

theorem interpN_map_eq_iff {δ δ' : LSubN L} {a a' : Lifetime.Life} :
    interpN (δ.map π) a = interpN (δ'.map π) a' ↔ interpN δ a = interpN δ' a' := by
  rw [interpN_map, interpN_map]
  exact (Option.map_injective π.injective).eq_iff

mutual
theorem tyEqN_map : ∀ (S S' : VTy) (δ δ' : LSubN L),
    TyEqN S (δ.map π) S' (δ'.map π) ↔ TyEqN S δ S' δ'
  | .unit, S', _, _ => by cases S' <;> simp [TyEqN]
  | .zero, S', _, _ => by cases S' <;> simp [TyEqN]
  | .unk, S', _, _ => by cases S' <;> simp [TyEqN]
  | .int _, S', _, _ => by cases S' <;> simp [TyEqN]
  | .opq _, S', _, _ => by cases S' <;> simp [TyEqN]
  | .tvar _, S', _, _ => by cases S' <;> simp [TyEqN]
  | .tensor A B, S', δ, δ' => by
      cases S' with
      | tensor A' B' =>
          simp only [TyEqN]
          rw [tyEqN_map A A' δ δ', tyEqN_map B B' δ δ']
      | _ => simp [TyEqN]
  | .sum A B, S', δ, δ' => by
      cases S' with
      | sum A' B' =>
          simp only [TyEqN]
          rw [tyEqN_map A A' δ δ', tyEqN_map B B' δ δ']
      | _ => simp [TyEqN]
  | .thunk C, S', δ, δ' => by
      cases S' with
      | thunk C' => simp only [TyEqN]; exact ctyEqN_map C C' δ δ'
      | _ => simp [TyEqN]
  | .ref A, S', δ, δ' => by
      cases S' with
      | ref A' => simp only [TyEqN]; exact tyEqN_map A A' δ δ'
      | _ => simp [TyEqN]
  | .bang A, S', δ, δ' => by
      cases S' with
      | bang A' => simp only [TyEqN]; exact tyEqN_map A A' δ δ'
      | _ => simp [TyEqN]
  | .mu A, S', δ, δ' => by
      cases S' with
      | mu A' => simp only [TyEqN]; exact tyEqN_map A A' δ δ'
      | _ => simp [TyEqN]
  | .fam A, S', δ, δ' => by
      cases S' with
      | fam A' => simp only [TyEqN]; exact tyEqN_map A A' δ δ'
      | _ => simp [TyEqN]
  | .box a A, S', δ, δ' => by
      cases S' with
      | box a' A' =>
          simp only [TyEqN]
          rw [interpN_map_eq_iff π, tyEqN_map A A' δ δ']
      | _ => simp [TyEqN]
  | .imm a A, S', δ, δ' => by
      cases S' with
      | imm a' A' =>
          simp only [TyEqN]
          rw [interpN_map_eq_iff π, tyEqN_map A A' δ δ']
      | _ => simp [TyEqN]
  | .mut a A, S', δ, δ' => by
      cases S' with
      | «mut» a' A' =>
          simp only [TyEqN]
          rw [interpN_map_eq_iff π, tyEqN_map A A' δ δ']
      | _ => simp [TyEqN]

theorem ctyEqN_map : ∀ (C C' : CTy) (δ δ' : LSubN L),
    CTyEqN C (δ.map π) C' (δ'.map π) ↔ CTyEqN C δ C' δ'
  | .top, C', _, _ => by cases C' <;> simp [CTyEqN]
  | .ret A, C', δ, δ' => by
      cases C' with
      | ret A' => simp only [CTyEqN]; exact tyEqN_map A A' δ δ'
      | _ => simp [CTyEqN]
  | .arr A C, C', δ, δ' => by
      cases C' with
      | arr A' C'' =>
          simp only [CTyEqN]
          rw [tyEqN_map A A' δ δ', ctyEqN_map C C'' δ δ']
      | _ => simp [CTyEqN]
  | .amp C D, C', δ, δ' => by
      cases C' with
      | amp C'' D' =>
          simp only [CTyEqN]
          rw [ctyEqN_map C C'' δ δ', ctyEqN_map D D' δ δ']
      | _ => simp [CTyEqN]
  | .nu C, C', δ, δ' => by
      cases C' with
      | nu C'' => simp only [CTyEqN]; exact ctyEqN_map C C'' δ δ'
      | _ => simp [CTyEqN]
  | .eff n i q A B fin C, C', δ, δ' => by
      cases C' with
      | eff n' i' q' A' B' fin' C'' =>
          simp only [CTyEqN]
          rw [tyEqN_map A A' δ δ', tyEqN_map B B' δ δ', ctyEqN_map fin fin' δ δ',
            ctyEqN_map C C'' δ δ']
      | _ => simp [CTyEqN]
  | .all x b C, C', δ, δ' => by
      cases C' with
      | all x' b' C'' =>
          simp only [CTyEqN]
          rw [interpN_map_eq_iff π]
          refine and_congr_right fun _ => ?_
          rw [π.surjective.forall]
          refine forall_congr' fun α => ?_
          rw [← LSubN.map_extend, ← LSubN.map_extend]
          exact ctyEqN_map C C'' (δ.extend x α) (δ'.extend x' α)
      | _ => simp [CTyEqN]
end

theorem cohEN_act_iff {rs : List (FrameRecN L)} {m : Loc} {S : VTy} {δ : LSubN L} :
    CohEN (rs.map (FrameRecN.act π)) m S (δ.map π) ↔ CohEN rs m S δ := by
  unfold CohEN
  constructor
  · rintro ⟨S₀, δ₀', h₁, h₂⟩
    have e : δ₀' = (δ₀'.map π.symm).map π := by
      rw [LSubN.map_map]
      conv_lhs => rw [← LSubN.map_id δ₀']
      exact LSubN.map_congr fun p _ => (π.apply_symm_apply p.2).symm
    rw [e] at h₁ h₂
    exact ⟨S₀, δ₀'.map π.symm, (tyEqN_map π S S₀ δ _).mp h₁, (cohN_act_iff π).mp h₂⟩
  · rintro ⟨S₀, δ₀, h₁, h₂⟩
    exact ⟨S₀, δ₀.map π, (tyEqN_map π S S₀ δ δ₀).mpr h₁, (cohN_act_iff π).mpr h₂⟩

theorem relN_act_iff {r : FrameRecN L} {ρ : ResU L} :
    RelN (r.act π) (relRU π ρ) ↔ RelN r ρ := by
  unfold RelN
  constructor
  · rintro ⟨m, ψ', e, hk, h⟩
    rw [relRU_get] at e
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.mp e
    refine ⟨m, ψ, hψ, by rwa [kind_relU] at hk, ?_⟩
    rcases h with h | ⟨p, S, u, hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, S, u, (chainN_act_iff π).mp hc⟩
  · rintro ⟨m, ψ, hψ, hk, h⟩
    refine ⟨m, relU π ψ, by rw [relRU_get, hψ]; rfl, by rw [kind_relU, hk], ?_⟩
    rcases h with h | ⟨p, S, u, hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨p, S, u, (chainN_act_iff π).mpr hc⟩

theorem keepsN_act_iff {ls ls' : List (SRecN L)} {ρ : ResU L} :
    KeepsN (rsOfN (actL π ls)) (rsOfN (actL π ls')) (relRU π ρ) ↔
      KeepsN (rsOfN ls) (rsOfN ls') ρ := by
  unfold KeepsN
  constructor
  · intro h r hr hrel
    exact (mem_rsOfN_act π).mp (h (r.act π) ((mem_rsOfN_act π).mpr hr)
      ((relN_act_iff π).mpr hrel))
  · intro h r' hr' hrel
    rw [rsOfN_actL, List.mem_map] at hr'
    obtain ⟨r, hr, rfl⟩ := hr'
    exact (mem_rsOfN_act π).mpr (h r hr ((relN_act_iff π).mp hrel))

theorem cellInN_act_iff {ρ : ResU L} {b : L} : CellInN (relRU π ρ) (π b) ↔ CellInN ρ b := by
  unfold CellInN
  constructor
  · rintro ⟨m, ψ', e, hk, t', ht', hle⟩
    rw [relRU_get] at e
    obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.mp e
    rw [lts_relU, mem_mapS] at ht'
    obtain ⟨t, ht, rfl⟩ := ht'
    exact ⟨m, ψ, hψ, by rwa [kind_relU] at hk, t, ht, π.le_iff_le.mp hle⟩
  · rintro ⟨m, ψ, hψ, hk, t, ht, hle⟩
    exact ⟨m, relU π ψ, by rw [relRU_get, hψ]; rfl, by rw [kind_relU]; exact hk, π t,
      by rw [lts_relU]; exact mem_mapS_apply.mpr ht, π.le_iff_le.mpr hle⟩

/-- **The Kripke order is invariant.** -/
theorem extN_act_iff {ls ls' : List (SRecN L)} {ρ : ResU L} :
    ExtN (actL π ls) (actL π ls') (relRU π ρ) ↔ ExtN ls ls' ρ := by
  unfold ExtN
  rw [keepsN_act_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h b hb x hx
    have := h (π b) ((cellInN_act_iff π).mpr hb) (x.act π) (π.lt_iff_lt.mpr hx)
    rwa [mem_actL, mem_actL] at this
  · intro h b' hb' x' hx'
    obtain ⟨b, rfl⟩ := π.surjective b'
    obtain ⟨x, rfl⟩ := SRecN.act_surjective π x'
    rw [mem_actL, mem_actL]
    exact h b ((cellInN_act_iff π).mp hb') x (π.lt_iff_lt.mp hx')

end Invariance

end Nominal

end

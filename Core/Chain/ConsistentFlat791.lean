import Core.Chain.SI.LocTy

/-!
# Consistency on the whole flattening is not kept by taking a part  `[spec §62]`

The per-lend world's first reading (`docs/new-core/chain-interpretation.md` Appendix A.5) read
consistency over the whole flattening (`Consistent`). `↭` keeps that on the whole resource
(`consistent_of_updN`), but a run returns only a part `ρ′` of its post-configuration
`π = ρ′ ● ρp`, and the part's flattening can show a `mut` cell the whole's hides.

The configuration (`flat_part_config`): `ρ′ = m ↦ imm(t, (), ℓ ↦ mut(a, (), ∅, ⊤))`, an `imm`
cell whose escrow holds a `mut` cell at `ℓ`, and `ρp = ℓ ↦ imm(s, (), ∅)`, an `imm` cell at the
escrowed location. In `ρ = ρ′ ● ρp`'s aliasable walk the two meet at `ℓ` as
`mut(a, …) ○ imm(s, …) = imm(s, …)` (`CellU.CompR.mutImm`), so `⦇ρ⦈` has no `mut` cell and every
view is consistent with `ρ`; `⦇ρ′⦈` has `ℓ ↦ mut(a, …)`, which the view `c = ∅` does not type.
`ρ ↭ ρ` at every index, `ρp` owns nothing, and the zero-step run of a value from `ρ` returning
`ρ′` is an `erwp` run (`erwp_val_split`). The exclusive walk of `ρ′` is empty, so `ρ′` is
consistent on the exclusive walk (`ConsistentX`), as `erwp_consistent` says it must be.

Not built: a frame (`TWNC`, `Tagged`) at which this resource is a run's start. The world holding
it is an `imm` frame of a `Mut` value with an `imm` reborrow of the borrowed cell (`TWNC.immFrame`,
then `TWNC.reb`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.ConsistentFlat791
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI

/-! ### A zero-step run that returns a part -/

/-- **A final term whose postcondition holds at a part of the resource**: the run returns `ρ′`
and leaves `ρp`, which owns nothing, in the post-configuration. -/
theorem rwpG_here_split {Φ : LocFam} {Q : PostG} {n : Nat} {ls : List SRec} {e : Expr}
    {ρ ρ' ρp : WRes} (hfin : ∀ μ, Final (ℍ := ℍ) μ e) (hs : ResU.CompS ρ' ρp ρ)
    (hno : NoOwn ρp) (h : Q n ls e ρ') : rwpG (ℍ := ℍ) Φ Q n ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' e' hj hrun _
  cases hrun with
  | more hs' _ => exact absurd hs' (hfin _ _ _)
  | refl =>
  have hvρ : ResU.Valid ρ := (hash_valid hf).2
  have hvf : ResU.Valid fρ := hash_valid_comp hf hc
  -- `ρf ● (ρ′ ● ρp) = (ρf ● ρ′) ● ρp`
  obtain ⟨fρ', h₁, h₂⟩ := (ResU.CompS.assoc ρf ρ' ρp fρ).mp ⟨ρ, hs, hc⟩
  have hvf' : ResU.Valid fρ' := (ResU.Valid.split h₂ hvf).1
  refine ⟨ρ', ρp, fρ', fρ, ρ, ps, ls, ?_, h₁, ?_, h₂, hl, hs, UpdVN.refl Φ _ hvρ, hno, hT, htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, by simpa using h⟩
  · exact ⟨(ResU.CompS.comm h₁).1, fρ', ResU.CompS.comm h₁, hvf'⟩
  · exact ⟨(ResU.CompS.comm h₂).1, fρ, ResU.CompS.comm h₂, hvf⟩

/-- **A value returned at a part**: `erwp` of a value from `ρ = ρ′ ● ρp` holds wherever its
postcondition holds at `ρ′`. -/
theorem erwp_val_split {Φ : LocFam} {Tb : TableN} {Q : PostN} {n : Nat} {ls : List SRec}
    {v : Val} {ρ ρ' ρp : WRes} (hs : ResU.CompS ρ' ρp ρ) (hno : NoOwn ρp)
    (h : Q n ls v ρ') : erwp (ℍ := ℍ) Φ Tb Q n ls v.1 ρ := by
  rw [erwp_eq]
  exact rwpG_here_split (fun μ => final_val μ v) hs hno (Or.inl ⟨v, rfl, h⟩)

/-! ### Two cells at two locations -/

open Classical in
/-- `m ↦ ψ ● ℓ ↦ φ` at two distinct locations. -/
def two (m l : Loc) (ψ φ : CellU Loc Val) : WRes where
  get := fun x => if x = m then some ψ else if x = l then some φ else none
  finite := by
    refine ⟨[m, l], fun x h => ?_⟩
    by_cases hm : x = m
    · simp [hm]
    · by_cases hl : x = l
      · simp [hl]
      · simp [hm, hl] at h

theorem two_get_m {m l : Loc} (ψ φ : CellU Loc Val) : (two m l ψ φ).get m = some ψ := by
  simp [two]

theorem two_get_l {m l : Loc} (hml : m ≠ l) (ψ φ : CellU Loc Val) :
    (two m l ψ φ).get l = some φ := by
  simp [two, Ne.symm hml]

theorem two_get_ne {m l x : Loc} (hm : x ≠ m) (hl : x ≠ l) (ψ φ : CellU Loc Val) :
    (two m l ψ φ).get x = none := by
  simp [two, hm, hl]

/-- Two singletons at distinct locations compose to `two`, at any composition. -/
theorem comp_two {R : CellU Loc Val → CellU Loc Val → Prop}
    {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop} {m l : Loc} (hml : m ≠ l)
    (ψ φ : CellU Loc Val) :
    ResU.Comp R C (ResU.single m ψ) (ResU.single l φ) (two m l ψ φ) := by
  refine ⟨ResU.Compat.of_disjoint fun x => ?_, fun x => ?_⟩
  · by_cases hx : x = m
    · subst hx; exact Or.inr (ResU.single_get_ne _ hml)
    · exact Or.inl (ResU.single_get_ne _ hx)
  · by_cases hm : x = m
    · subst hm
      rw [ResU.single_get_self, ResU.single_get_ne _ hml, two_get_m]
      rfl
    · by_cases hl : x = l
      · subst hl
        rw [ResU.single_get_ne _ hm, ResU.single_get_self, two_get_l hml]
        rfl
      · rw [ResU.single_get_ne _ hm, ResU.single_get_ne _ hl, two_get_ne hm hl]
        rfl

/-! ### The configuration -/

/-- The payload `⊤` of the escrowed cell. -/
def topP (a : Life) : Val → SPropS Loc Val a := fun _ _ => True

/-- `ℓ ↦ mut(a, (), ∅, ⊤)`. -/
def mutX (a : Life) : CellU Loc Val :=
  CellU.mutOf a Val.unit PMap.empty (ResU.inStratum_empty a) (topP a) trivial

/-- The escrow `ℓ ↦ mut(a, (), ∅, ⊤)`, in `Res_{⊔t}`. -/
def escX (l : Loc) (a : Life) : WRes := ResU.single l (mutX a)

theorem escX_inStratum (l : Loc) (a : Life) (t : LSet) (hta : t.join < a) : (escX l a).InStratum t.join :=
  ResU.inStratum_single l (show a ⊐ t.join from hta)

/-- `m ↦ imm(t, (), ℓ ↦ mut(a, (), ∅, ⊤))`. -/
def immM (l : Loc) (a : Life) (t : LSet) (hta : t.join < a) : CellU Loc Val := CellU.immOf t Val.unit (escX l a) (escX_inStratum l a t hta)

/-- `ℓ ↦ imm(s, (), ∅)`. -/
def immL (s : LSet) : CellU Loc Val := CellU.immOf s Val.unit PMap.empty (ResU.inStratum_empty s.join)

/-- The part returned: `ρ′ = m ↦ imm(t, (), ℓ ↦ mut(a, …))`. -/
def rhoR (m l : Loc) (a : Life) (t : LSet) (hta : t.join < a) : WRes := ResU.single m (immM l a t hta)

/-- The part left: `ρp = ℓ ↦ imm(s, (), ∅)`. -/
def rhoP (l : Loc) (s : LSet) : WRes := ResU.single l (immL s)

/-- The whole: `ρ = ρ′ ● ρp`. -/
def rhoW (m l : Loc) (a : Life) (s t : LSet) (hta : t.join < a) : WRes := two m l (immM l a t hta) (immL s)

theorem rho_compS (m l : Loc) (hml : m ≠ l) (a : Life) (s t : LSet) (hta : t.join < a) :
    ResU.CompS (rhoR m l a t hta) (rhoP l s) (rhoW m l a s t hta) :=
  comp_two hml _ _

theorem exR_escX (l : Loc) (a : Life) : ExR (escX l a) (escX l a) :=
  ExW.single_mut exW_empty (ResU.comp_empty_right _)

theorem agW_escX (l : Loc) (a : Life) : AgW (escX l a) PMap.empty := AgW.single_mut agW_empty

/-- `⦇ℓ ↦ mut(a, (), ∅, ⊤)⦈_○` is itself. -/
theorem flatR_escX (l : Loc) (a : Life) : ResU.FlatR (escX l a) (escX l a) :=
  ⟨PMap.empty, escX l a, agW_escX l a, exR_escX l a, ResU.comp_empty_left _⟩

/-- `ag(ρ′) = m ↦ imm(t, …) ● ℓ ↦ mut(a, …)`: the escrow's walk under the `imm` cell. -/
theorem agW_rhoR (m l : Loc) (hml : m ≠ l) (a : Life) (t : LSet) (hta : t.join < a) :
    AgW (rhoR m l a t hta) (two m l (immM l a t hta) (mutX a)) :=
  AgW.single_imm (flatR_escX l a) (comp_two hml _ _)

theorem exS_rhoR (m l : Loc) (a : Life) (t : LSet) (hta : t.join < a) :
    ExS (rhoR m l a t hta) PMap.empty :=
  ExW.empty_of_all_imm fun x ψ hx => by
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hx; exact CellU.kind_immOf _ _ _ _

theorem flat_rhoR (m l : Loc) (hml : m ≠ l) (a : Life) (t : LSet) (hta : t.join < a) :
    ResU.Flat (rhoR m l a t hta) (two m l (immM l a t hta) (mutX a)) :=
  ⟨PMap.empty, _, exS_rhoR m l a t hta, agW_rhoR m l hml a t hta, ResU.comp_empty_left _⟩

theorem agW_rhoP (l : Loc) (s : LSet) : AgW (rhoP l s) (rhoP l s) :=
  AgW.single_imm ⟨PMap.empty, PMap.empty, agW_empty, exW_empty, ResU.comp_empty_right _⟩
    (ResU.comp_empty_right _)

/-- `mut(a, (), ∅, ⊤) ○ imm(s, (), ∅) = imm(s, (), ∅)`, so `ag(ρ) = ρ`. -/
theorem compR_hide (m l : Loc) (hml : m ≠ l) (a : Life) (s t : LSet) (hta : t.join < a) :
    ResU.CompR (two m l (immM l a t hta) (mutX a)) (rhoP l s) (rhoW m l a s t hta) := by
  have hC : CellU.CompR (mutX a) (immL s) (immL s) :=
    CellU.CompR.mutImm s Val.unit PMap.empty _ a _ (topP a) trivial
  unfold rhoP rhoW
  refine ⟨fun x ψ₁ ψ₂ e₁ e₂ => ?_, fun x => ?_⟩
  · obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e₂
    rw [two_get_l hml] at e₁
    cases Option.some.inj e₁
    exact ⟨_, hC⟩
  · by_cases hm : x = m
    · subst hm
      rw [two_get_m, ResU.single_get_ne _ hml, two_get_m]
      rfl
    · by_cases hl : x = l
      · subst hl
        rw [two_get_l hml, ResU.single_get_self, two_get_l hml]
        exact ⟨_, rfl, hC⟩
      · rw [two_get_ne hm hl, ResU.single_get_ne _ hl, two_get_ne hm hl]
        rfl

theorem exS_rhoW (m l : Loc) (hml : m ≠ l) (a : Life) (s t : LSet) (hta : t.join < a) :
    ExS (rhoW m l a s t hta) PMap.empty :=
  ExW.empty_of_all_imm fun x ψ hx => by
    by_cases hm : x = m
    · subst hm; rw [rhoW, two_get_m] at hx; cases Option.some.inj hx
      exact CellU.kind_immOf _ _ _ _
    · by_cases hl : x = l
      · subst hl; rw [rhoW, two_get_l hml] at hx; cases Option.some.inj hx
        exact CellU.kind_immOf _ _ _ _
      · rw [rhoW, two_get_ne hm hl] at hx; cases hx

/-- `⦇ρ⦈ = ρ`: two `imm` cells, no `mut` cell. -/
theorem flat_rhoW (m l : Loc) (hml : m ≠ l) (a : Life) (s t : LSet) (hta : t.join < a) :
    ResU.Flat (rhoW m l a s t hta) (rhoW m l a s t hta) := by
  refine ⟨PMap.empty, rhoW m l a s t hta, exS_rhoW m l hml a s t hta, ?_,
    ResU.comp_empty_left _⟩
  exact (AgW.split (rho_compS m l hml a s t hta)).mpr
    ⟨_, _, agW_rhoR m l hml a t hta, agW_rhoP l s, compR_hide m l hml a s t hta⟩

theorem valid_rhoW (m l : Loc) (hml : m ≠ l) (a : Life) (s t : LSet) (hta : t.join < a) :
    ResU.Valid (rhoW m l a s t hta) := ⟨_, flat_rhoW m l hml a s t hta⟩

theorem noOwn_rhoP (l : Loc) (s : LSet) : NoOwn (rhoP l s) :=
  by
  classical
  refine PMap.ext fun x => ?_
  cases hgg : ((rhoP l s).restrict Kind.own).get x with
  | none => simp
  | some ψ =>
      exfalso
      obtain ⟨hdd, hk⟩ := ResU.restrict_eq_some.mp hgg
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hdd
      exact absurd hk (by simp [immL])

/-- Every view is consistent with the whole on its flattening. -/
theorem consistent_rhoW (m l : Loc) (hml : m ≠ l) (a : Life) (s t : LSet) (hta : t.join < a)
    (c : Loc → Option Life) : Consistent c (rhoW m l a s t hta) := by
  intro x ψ hx hk
  obtain ⟨σ, hσ, hg⟩ := hx
  obtain rfl := ResU.Flat.functional hσ (flat_rhoW m l hml a s t hta)
  exfalso
  by_cases hm : x = m
  · subst hm; rw [rhoW, two_get_m] at hg; cases Option.some.inj hg
    exact absurd hk (by simp [immM])
  · by_cases hl : x = l
    · subst hl; rw [rhoW, two_get_l hml] at hg; cases Option.some.inj hg
      exact absurd hk (by simp [immL])
    · rw [rhoW, two_get_ne hm hl] at hg; cases hg

/-- The part's flattening has `ℓ ↦ mut(a, …)`: the empty view is not consistent with it. -/
theorem not_consistent_rhoR (m l : Loc) (hml : m ≠ l) (a : Life) (t : LSet) (hta : t.join < a) :
    ¬ Consistent (fun _ => none) (rhoR m l a t hta) := by
  intro h
  have := h l (mutX a) ⟨_, flat_rhoR m l hml a t hta, two_get_l hml _ _⟩
    (CellU.kind_mutOf _ _ _ _ _ _)
  cases this

/-- …and the part's exclusive walk is empty: it is consistent on the exclusive walk. -/
theorem consistentX_rhoR (m l : Loc) (a : Life) (t : LSet) (hta : t.join < a)
    (c : Loc → Option Life) : ConsistentX c (rhoR m l a t hta) := by
  intro e he x ψ hg _
  obtain rfl := ExS.functional he (exS_rhoR m l a t hta)
  cases hg

/-- **The configuration.** A resource `ρ = ρ′ ● ρp` with `ρp` owning nothing, `ρ ↭ ρ` at every
location typing and index, the empty view consistent with `ρ` on its flattening and not with
`ρ′`; the zero-step run of `()` from `ρ` returning exactly `ρ′` is an `erwp` run at every table
and index; and `ρ′` is consistent on its exclusive walk. -/
theorem flat_part_config :
    ∃ (ρ ρ' ρp : WRes), ResU.CompS ρ' ρp ρ ∧ NoOwn ρp ∧ ResU.Valid ρ ∧
      (∀ (Φ : LocFam) n, UpdVN Φ n ρ ρ) ∧ Consistent (fun _ => none) ρ ∧
      ¬ Consistent (fun _ => none) ρ' ∧ ConsistentX (fun _ => none) ρ' ∧
      ∀ (Φ : LocFam) (Tb : TableN) n ls,
        erwp (ℍ := ℍ) Φ Tb (fun _ _ _ r => r = ρ') n ls Val.unit.1 ρ := by
  have hml : (1 : Loc) ≠ 0 := by decide
  let a : Life := OrderDual.toDual 0
  let t : LSet := LSet.singleton (OrderDual.toDual 1)
  have hta : t.join < a := show OrderDual.toDual 1 < OrderDual.toDual 0 from
    OrderDual.toDual_lt_toDual.mpr (by decide)
  let s : LSet := LSet.singleton (OrderDual.toDual 1)
  refine ⟨rhoW 1 0 a s t hta, rhoR 1 0 a t hta, rhoP 0 s, rho_compS 1 0 hml a s t hta,
    noOwn_rhoP 0 s, valid_rhoW 1 0 hml a s t hta,
    fun Φ n => UpdVN.refl Φ n (valid_rhoW 1 0 hml a s t hta),
    consistent_rhoW 1 0 hml a s t hta _, not_consistent_rhoR 1 0 hml a t hta,
    consistentX_rhoR 1 0 a t hta _, fun Φ Tb n ls => ?_⟩
  exact erwp_val_split (rho_compS 1 0 hml a s t hta) (noOwn_rhoP 0 s) rfl

end BoCa.Fig16.LogRel.Core.Chain.SI.ConsistentFlat791

end

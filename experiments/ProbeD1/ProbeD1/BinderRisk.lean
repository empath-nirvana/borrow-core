import ProbeD1.BinderArise

/-!
# ProbeD1 — the known risk: `mut_not_natural` (`BINDER.md` §4, item 3)

* **`NotVDenNaturalArises`** (`notVDenNaturalArises`): Restrat's witness resource `ρ₀` is a part of a
  tagged `TW` world, by the history of `BINDER.md` §4.2: `ℓ′` allocated, a 6.64 frame at `ℓ′` at `1`,
  `ℓ` allocated holding `loc ℓ′`, and `ℓ` folded into `mut(2, loc ℓ′, ℓ′ ↦ imm({1}, (), ∅), Q)`. The
  last step is `TW.mutFold`, which takes any stored predicate: the proof shows that `ρ₀` is a part of
  a world `TW`'s constructors build, not one a run of a program produces. It is not arising in
  DESIGN §11's sense, and it carries no refutation.
* **At the view slot** (`mutWitnessThaws`): at the witness's own map, the slot holding the view of a
  6.65 entry at `Mut '0 (Imm '1 1)` is re-established from the view handed at the instantiated
  reading (`vC_mut_bound`). The image of the old stored invariant, which `mut_not_natural` is about,
  is never formed.
* **At the retained part** the mechanism does apply, as a fact about our statement:
  `not_mutPayloadInst` (`BinderRefute.lean`) breaks the support conjunct of a retained `Mut` cell
  whose payload type reads an internal lifetime, at a configuration not shown to arise. The revised
  W asks a retained leaf's payload type to read external lifetimes only (`RetainedPay`,
  `BinderJ.lean`), which the instantiation fixes (`agree_of_payExt`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS)
open Restrat.MutCounterexample (ℓ ℓ' L L_lt immCell Q hw σ_in ρ₀)

/-! ### At the view slot -/

/-- The witness's map `n ↦ n + 1` below `⊤` is an instantiation of `mwσ`, whose cut is `⊤`. -/
theorem mwInstAt : InstAt mwαs mwι := by
  intro c θ h
  have hc : (⊤ : Life) = c := congrArg Sigma.fst (Option.some.inj h)
  subst hc
  rfl

/-- **`MutWitnessThaws`**: `vC_mut_bound` at the witness. -/
theorem mutWitnessThaws : MutWitnessThaws := by
  refine ⟨mwInstAt, fun δ ls ls' ρ ρv _ _ hvc hcoh hv => ?_⟩
  have hi : innerAt mwσ mwαs mwX.l = some (mwX, lifeN 2) := by simp [innerAt]
  have hTy : TyEq (.imm (.var 1) .unit) (extS δ mwσ mwαs) mwX.T (extS δ mwσ mwαs) :=
    TyEq.refl _ _
  have hatl := (hcoh mwX.l mwX (lifeN 2) rfl hi).2
  have hT : CoreStable (.imm (.var 1) .unit : VTy) := trivial
  refine ⟨vC_mut_bound mwι hT rfl rfl hTy hvc hatl hv, fun l' e' α' hl' hi' => ?_⟩
  cases hl'
  rw [innerAt_inst_some mwι hi] at hi'
  obtain ⟨rfl, rfl⟩ : mwX = e' ∧ mwι.life1 (lifeN 2) = α' := by simpa using hi'
  exact ⟨⟨trivial, TyEq.refl _ _⟩, fun ψ hψ => (hv.2 ψ hψ).1⟩

/-! ### `NotVDenNaturalArises`: a `TW` history of the witness resource -/

/-- `ℓ′`'s frame record: the value `()`, an empty payload, at the type `1`. -/
abbrev nvR : FrameRec := ⟨ℓ', .unit, PMap.empty, .unit, ⟨[]⟩⟩

theorem nv_descR {d : FrameRec} (h : DescR nvR d) : d = nvR := by
  obtain ⟨p, hlin⟩ := h
  cases hlin with
  | nil => rfl
  | cons hsub _ =>
      obtain ⟨-, -, ζ, hζ, -⟩ := hsub
      rw [PMap.empty_get] at hζ; exact absurd hζ (by simp)

theorem nv_not_desc (d : FrameRec) : ¬ Desc nvR d := by
  rintro ⟨p, hp, hlin⟩
  cases hlin with
  | nil => exact hp rfl
  | cons hsub _ =>
      obtain ⟨-, -, ζ, hζ, -⟩ := hsub
      rw [PMap.empty_get] at hζ; exact absurd hζ (by simp)

theorem agW_immCell : AgW (ResU.single ℓ' (immCell 1) : WRes) (ResU.single ℓ' (immCell 1)) :=
  AgW.single_imm ⟨PMap.empty, PMap.empty, agW_empty, exW_empty, ResU.comp_empty_right _⟩
    (ResU.comp_empty_right _)

/-- `⦇ℓ′ ↦ imm({1}, (), ∅)⦈` is itself. -/
theorem flat_immCell : ResU.Flat (ResU.single ℓ' (immCell 1) : WRes) (ResU.single ℓ' (immCell 1)) := by
  refine ⟨PMap.empty, ResU.single ℓ' (immCell 1), ExW.empty_of_all_imm (fun l ψ h => ?_),
    agW_immCell, compS_empty_left _⟩
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some h
  rfl

theorem nv_tw₁ : TW (ResU.single ℓ' (CellU.ownOf .unit) : WRes) [] [] :=
  TW.alloc TW.empty lower_empty rfl (compS_empty_left _) (ResU.valid_single_own _ _)

/-- **The 6.64 frame at `ℓ′`**, at `1`, the type `1`: its record `nvR` has no descendant. -/
theorem nv_tw₂ : TW (ResU.single ℓ' (immCell 1) : WRes) [nvR] [nvR] := by
  have := TW.immFrame (W := ResU.single ℓ' (CellU.ownOf .unit))
    (X := ResU.single ℓ' (CellU.ownOf .unit)) (Z := PMap.empty) (R := PMap.empty)
    (W' := ResU.single ℓ' (immCell 1)) (ps := []) (rs := []) (ds := []) (l := ℓ') (v := .unit)
    (α := L 1) .unit ⟨[]⟩ (ResU.inStratum_empty _) nv_tw₁ (fun _ hx => hx.elim)
    (ResU.comp_empty_right _) (ResU.comp_empty_right _) ⟨rfl, rfl⟩ (ResU.comp_empty_right _)
    ⟨_, flat_immCell⟩ (fun d => ⟨fun h => by simp at h, fun h => (nv_not_desc d h).elim⟩)
  simpa using this

/-- **The witness resource's world**: `ℓ` allocated holding `loc ℓ′`, then folded by `TW.mutFold`
at `2`, storing Restrat's `Q` over `ℓ′ ↦ imm({1}, (), ∅)`. -/
theorem nv_tw : TW ρ₀ [nvR] [nvR] := by
  have hℓ : (ℓ : BoCa.Loc) ≠ ℓ' := by decide
  obtain ⟨x, σ', hx, -, hσ', hTx, -⟩ := alloc_world (ρf := PMap.empty)
    (ρ := ResU.single ℓ' (immCell 1)) (σ := ResU.single ℓ' (immCell 1)) (l := ℓ) (.loc ℓ')
    ⟨(compS_empty_left _).1, _, compS_empty_left _, ⟨_, flat_immCell⟩⟩ (compS_empty_left _)
    nv_tw₂ (μ := fun l => ((ResU.single ℓ' (immCell 1) : WRes).get l).map CellU.erase)
    ⟨_, flat_immCell, fun _ => rfl⟩ (by simp [ResU.single_get_ne _ hℓ])
  rw [eq_of_compS_empty_left hσ'] at hTx
  have hv₀ : ResU.Valid ρ₀ := ResU.valid_single_mut_of_wit hx (TW.valid hTx)
  exact TW.mutFold hTx (ResU.CompS.comm hx) (ResU.comp_empty_right x) (ResU.comp_empty_right _) hv₀

theorem nv_tagged : Tagged ρ₀ [nvR] [(nvR, L 1)] := by
  intro x hx
  rw [List.mem_singleton] at hx
  subst hx
  refine ⟨nvR, List.mem_singleton_self _, ⟨[], LinPath.nil _⟩, fun a ha ζ t hζ ht y hy => ?_,
    fun a _ m hm => ?_⟩
  · have ha' : AgW (ResU.single ℓ' (immCell 1) : WRes) a := AgW.single_mut_inv ha
    rw [AgW.functional ha' agW_immCell] at hζ
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hζ
    simp only [immCell, CellU.lsOf, CellU.immOf, Option.some.injEq] at ht
    subst ht
    exact hy
  · obtain ⟨d, hd, ζ, hζ, -⟩ := hm
    rw [nv_descR hd, PMap.empty_get] at hζ
    exact absurd hζ (by simp)

/-- **`NotVDenNaturalArises`**: `ρ₀` is a part of a tagged `TW` world, at `ρ_f = ∅`. -/
theorem notVDenNaturalArises : Targets.NotVDenNaturalArises (ℍ := ℍ) :=
  ⟨ρ₀, PMap.empty, [nvR], [(nvR, L 1)], ⟨nv_tw, nv_tagged⟩, compS_empty_left ρ₀⟩

/-! ### `MutWitnessThaws` is not vacuous -/

/-- **`MutWitnessThaws`'s hypotheses are met** at the witness's shape: the slot's cell is `x`'s view
at `2`, storing `𝒱⟦Imm '1 1⟧` at the stack's reading over `ℓ′ ↦ imm({1}, (), ∅)`, coherent with
`ℓ′`'s record at `1`; the handed view is the cell at `3` storing it at the instantiated reading over
`ℓ′ ↦ imm({2}, (), ∅)`, coherent with the moved record at `2`. A configuration exhibited, not one
shown to arise (`MutWitnessThawsInhabited` asks it at `ArisesI`). -/
def MutWitnessThawsMet : Prop :=
  ∃ (δ : LSub) (ls ls' : List SRec) (ρ ρv : WRes), RecsOutside mwαs ls ∧
    KeepsS (mwι.recs ls) ls' ρ ∧ vC true mwTy ls (extS δ mwσ mwαs) (.loc mwX.l) ρ ∧
    CohS mwσ mwαs (extS δ mwσ mwαs) mwTy (.loc mwX.l) ρ ∧
    vwEW (mwι.sub (extS δ mwσ mwαs)) mwX true (mwι.life1 (lifeN 2)) ls' ρv

/-- The stack's reading at the empty substitution: `'0 ↦ 2`, `'1 ↦ 1`. -/
abbrev mwS : LSub := extS ⟨[]⟩ mwσ mwαs

/-- The payload type of `x`'s entry. -/
abbrev mwPay : VTy := .imm (.var 1) .unit

theorem ofS_toS {b : Life} (P : Val → SPropU BoCa.Loc Val)
    (hsupp : ∀ v r, P v r → r.InStratum b) : ofS (fun v => SPropU.toS b (P v)) = P := by
  funext v r
  apply propext
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨hsupp v r h, h⟩

/-- `𝒱⟦Imm '1 1⟧` at a reading sending `'1` to `n` lies in every stratum below `n`. -/
theorem mwPay_supp {s : LSub} {n : ℕ} (hs : s.find? 1 = some n) {b : Life} (hb : b < L n)
    (ls : List SRec) : ∀ (w : Val) (r : WRes), vC true mwPay ls s w r → r.InStratum b := by
  intro w r h
  obtain ⟨α, hα, ℓ₀, hk⟩ := h
  have hα' : α = n := Option.some.inj (hα.symm.trans hs)
  obtain ⟨-, S, u, σ, hσ, ls₀, rfl, -, hle, -⟩ := pure_sep_iff.mp hk
  refine ResU.inStratum_single _ ?_
  show b < S.meet
  rw [hα'] at hle
  exact lt_of_lt_of_le hb hle

/-- `𝒱⟦Imm '1 1⟧` holds at `ℓ′ ↦ imm({n}, (), ∅)`, coherent with `ℓ′`'s record. -/
theorem mwPay_holds {s : LSub} {n : ℕ} (hs : s.find? 1 = some n) {ls : List SRec}
    (hr : nvR ∈ rsOf ls) (hn : ∀ x ∈ ls, ¬ L n < x.2) :
    vC true mwPay ls s (.loc ℓ') (ResU.single ℓ' (immCell n)) := by
  refine ⟨L n, hs, ℓ', pure_sep_mk ⟨rfl, .unit, ⟨[]⟩, trivial, Or.inl ⟨nvR, hr, rfl, rfl,
    fun _ hy => hy.elim⟩⟩ ⟨LSet.singleton (L n), .unit, PMap.empty, ResU.inStratum_empty _, [], rfl,
    ⟨rfl, rfl⟩, le_rfl, fun x => ?_⟩⟩
  simp only [List.not_mem_nil, false_iff, not_and]
  exact fun hx => hn x hx

theorem σ_in₃ : (ResU.single ℓ' (immCell 2) : WRes).InStratum (L 3) :=
  ResU.inStratum_single _ (show L 3 < L 2 from L_lt (by norm_num))

theorem mwS_find₁ : mwS.find? 1 = some 1 := rfl
theorem mwS_find₀ : mwS.find? 0 = some 2 := rfl
theorem mwS'_find₁ : (mwι.sub mwS).find? 1 = some 2 := rfl
theorem mwS'_find₀ : (mwι.sub mwS).find? 0 = some 3 := rfl

/-- The list: `ℓ′`'s record at `1`. -/
abbrev mwLs : List SRec := [(nvR, L 1)]

/-- The instantiated list: the record moved to `2`. -/
abbrev mwLs' : List SRec := [(nvR, L 2)]

theorem mwLs'_eq : mwι.recs mwLs = mwLs' := rfl

/-- The stored invariant of the slot's cell, at `2`. -/
def mwP₁ : Val → SPropS BoCa.Loc Val (L 2) := fun v => SPropU.toS (L 2) (vC true mwPay mwLs mwS v)

/-- The stored invariant of the handed view, at `3`. -/
def mwP₂ : Val → SPropS BoCa.Loc Val (L 3) :=
  fun v => SPropU.toS (L 3) (vC true mwPay mwLs' (mwι.sub mwS) v)

theorem mwHw₁ : mwP₁ (.loc ℓ') ⟨ResU.single ℓ' (immCell 1), σ_in⟩ :=
  mwPay_holds mwS_find₁ (by simp [rsOf]) (by simp)

theorem mwHw₂ : mwP₂ (.loc ℓ') ⟨ResU.single ℓ' (immCell 2), σ_in₃⟩ :=
  mwPay_holds mwS'_find₁ (by simp [rsOf]) (by simp)

theorem ofS_mwP₁ : ofS mwP₁ = vC true mwPay mwLs mwS :=
  ofS_toS _ (mwPay_supp mwS_find₁ (L_lt (by norm_num)) mwLs)

theorem ofS_mwP₂ : ofS mwP₂ = vC true mwPay mwLs' (mwι.sub mwS) :=
  ofS_toS _ (mwPay_supp mwS'_find₁ (L_lt (by norm_num)) mwLs')

/-- The slot's cell: `x`'s view at `2`. -/
abbrev mwρ : WRes :=
  ResU.single 0 (CellU.mutOf (L 2) (.loc ℓ') (ResU.single ℓ' (immCell 1)) σ_in mwP₁ mwHw₁)

/-- The handed view at `3`. -/
abbrev mwρv : WRes :=
  ResU.single 0 (CellU.mutOf (L 3) (.loc ℓ') (ResU.single ℓ' (immCell 2)) σ_in₃ mwP₂ mwHw₂)

theorem mutWitnessThaws_met : MutWitnessThawsMet := by
  refine ⟨⟨[]⟩, mwLs, mwLs', mwρ, mwρv, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha x hx _ p hp
    simp only [mwLs, List.mem_singleton] at hx
    subst hx
    simp at hp
  · rintro x - ⟨m, ψ, hg, hk, -⟩
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hg
    exact absurd hk (by simp)
  · refine ⟨L 2, mwS_find₀, 0, pure_sep_mk rfl ⟨L 2, .loc ℓ', _, σ_in, mwP₁, mwHw₁, mwLs, le_rfl,
      rfl, ofS_mwP₁, fun x => ?_, fun ls' u' σ' h => ?_⟩⟩
    · simp only [mwLs, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨rfl, L_lt (by norm_num)⟩
      · rintro ⟨h, -⟩; exact h
    · exact mwPay_supp mwS_find₁ (L_lt (by norm_num)) ls' u' σ' h
  · intro l e α hl hi
    cases hl
    have hi' : innerAt mwσ mwαs mwX.l = some (mwX, lifeN 2) := by simp [innerAt]
    rw [hi'] at hi
    obtain ⟨rfl, rfl⟩ : mwX = e ∧ lifeN 2 = α := by simpa using hi
    refine ⟨⟨trivial, TyEq.refl _ _⟩, fun ψ hψ => ?_⟩
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hψ
    rfl
  · refine ⟨⟨L 3, .loc ℓ', _, σ_in₃, mwP₂, mwHw₂, mwLs', le_rfl, rfl, ofS_mwP₂, fun x => ?_,
      fun ls' u' σ' h => mwPay_supp mwS'_find₁ (L_lt (by norm_num)) ls' u' σ' h⟩, fun ψ hψ => ?_⟩
    · simp only [mwLs', List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨rfl, L_lt (by norm_num)⟩
      · rintro ⟨h, -⟩; exact h
    · obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hψ
      exact ⟨rfl, fun t ht => by simp [CellU.lsOf, CellU.mutOf] at ht⟩

/-! ### `ViewSlotInst` at a type Core reads without a thunk -/

/-- **`ViewSlotInst` at a `CoreStable` slot type, the outermost lend below `⊤`**: the slot at a
bound place is re-established from the view handed at the instantiation (`vC_mut_bound`,
`vC_imm_bound`). At any other type `CohS` at a bound place is false. `ViewSlotInst` as stated, at
every type and with no bound on the outermost lend, is not derived: at an outermost lend at `⊤`
the cut is `⊤`, which is where `CohEInst` fails (`not_cohEInst`). -/
def ViewSlotInstCS : Prop :=
  ∀ (σ : LStack) (αs : List Life) (s : LSub) (ls ls' : List SRec) (A : VTy) (l : BoCa.Loc)
    (e : LEnt) (α : Life) (ρ ρv : WRes) (ι : Inst), CoreStable A → OuterBelowTop αs →
    innerAt σ αs l = some (e, α) → InstAt αs ι → RecsOutside αs ls → KeepsS (ι.recs ls) ls' ρ →
    vC true A ls s (.loc l) ρ → CohS σ αs s A (.loc l) ρ →
    vwEW (ι.sub s) e true (ι.life1 α) ls' ρv →
    vC true A ls' (ι.sub s) (.loc l) ρv ∧ CohS σ (ι.life αs) (ι.sub s) A (.loc l) ρv

theorem viewSlotInstCS : ViewSlotInstCS := by
  intro σ αs s ls ls' A l e α ρ ρv ι hA hob hi hat hro hks hvc hcoh hv
  have hel : e.l = l := (innerAt_mem hi).2
  have hco := hcoh l e α rfl hi
  have hcohI : (∀ ψ, ρv.get l = some ψ → ψ.at = ι.life1 α) →
      CohKind (ι.sub s) e A → CohS σ (ι.life αs) (ι.sub s) A (.loc l) ρv := by
    intro hat' hk' l' e' α' hl' hi'
    cases hl'
    rw [innerAt_inst_some ι hi] at hi'
    obtain ⟨rfl, rfl⟩ : e = e' ∧ ι.life1 α = α' := by simpa using hi'
    exact ⟨hk', hat'⟩
  have hat' : ∀ ψ, ρv.get l = some ψ → ψ.at = ι.life1 α :=
    fun ψ hψ => (hv.2 ψ (by rw [hel]; exact hψ)).1
  cases A with
  | «mut» a T =>
      obtain ⟨hkind, hTy⟩ := hco.1
      have hk : e.k = .mut := by
        cases hek : e.k with
        | «mut» => rfl
        | imm u₀ => rw [hek] at hkind; exact hkind.elim
      exact ⟨vC_mut_bound ι (T := T) hA hel hk hTy hvc hco.2 hv,
        hcohI hat' ⟨by rw [hk]; trivial, tyEq_inst ι T hA hTy⟩⟩
  | imm a T =>
      obtain ⟨hkind, hTy⟩ := hco.1
      obtain ⟨u₀, hk⟩ : ∃ u₀, e.k = .imm u₀ := by
        cases hek : e.k with
        | «mut» => rw [hek] at hkind; exact hkind.elim
        | imm u₀ => exact ⟨u₀, rfl⟩
      exact ⟨vC_imm_bound hat hob (T := T) hA hro hel hk hTy hvc hco.2 hks hv,
        hcohI hat' ⟨by rw [hk]; trivial, tyEq_inst ι T hA hTy⟩⟩
  | unit => exact hco.1.elim
  | zero => exact hco.1.elim
  | unk => exact hco.1.elim
  | int _ => exact hco.1.elim
  | opq _ => exact hco.1.elim
  | tvar _ => exact hco.1.elim
  | tensor _ _ => exact hco.1.elim
  | sum _ _ => exact hco.1.elim
  | thunk _ => exact hco.1.elim
  | bang _ => exact hco.1.elim
  | box _ _ => exact hco.1.elim
  | ref _ => exact hco.1.elim
  | mu _ => exact hco.1.elim
  | fam _ => exact hco.1.elim

/-! ### The guard's top-level part; the statements at every type -/

theorem pvlTop : PVLTop :=
  fun _ _ _ _ _ h l ψ hg ho e α hi => h.1 l ψ (ExAt.top hg) ho e α hi

/-- `MutPayloadInstAll` has `MutPayloadInst`'s refuting instance. -/
theorem not_mutPayloadInstAll : ¬ MutPayloadInstAll :=
  fun h => not_mutPayloadInst fun T ls₀ s b c θ _ => h T ls₀ s b c θ

/-- `InstEquivLeafAll` has `InstEquivLeaf`'s refuting instance. -/
theorem not_instEquivLeafAll : ¬ InstEquivLeafAll :=
  fun h => not_instEquivLeaf fun A b αs ls s v ρ c θ hc hro _ => h A b αs ls s v ρ c θ hc hro

/-! ### `ViewTypeCoincidence`: the guard sees cells, not types -/

/-- The coherence records of `gT_violator` at `⊤`, which the instantiation at `⊤` leaves alone. -/
abbrev gls₀ : List SRec := [(gr₁, ⊤), (gr₂, ⊤), (gr₃, ⊤)]

theorem gT_violator₀ : vC true gT gls₀ gs₂ (.inj₂ (.loc 0)) gw₁ := by
  refine Or.inr ⟨.loc 0, pure_sep_mk rfl ⟨lifeN 2, rfl, 0, pure_sep_mk ⟨rfl, ?c₁⟩ ?p₁⟩⟩
  case c₁ => exact (coh_mem (r := gr₁) (t := ⊤) (by simp)).1
  case p₁ =>
    refine ⟨LSet.singleton (lifeN 2), Val.loc 1, gw₂, gw₂_in, lsAbove gls₀ (lifeN 2), rfl, ?_,
      le_rfl, fun x => mem_lsAbove⟩
    refine ⟨lifeN 2, rfl, 1, pure_sep_mk ⟨rfl, ?c₂⟩ ?p₂⟩
    case c₂ =>
      exact (coh_mem (L := lsAbove gls₀ (lifeN 2)) (r := gr₂) (t := ⊤)
        (mem_lsAbove.mpr ⟨by simp, by decide⟩)).1
    case p₂ =>
      refine ⟨LSet.singleton (lifeN 1), Val.loc 2, gw₃, gw₃_in,
        lsAbove (lsAbove gls₀ (lifeN 2)) (lifeN 1), rfl, ?_,
        show lifeN 2 ≤ lifeN 1 from by decide, fun x => mem_lsAbove⟩
      refine ⟨lifeN 2, rfl, 2, pure_sep_mk ⟨rfl, ?c₃⟩ ?p₃⟩
      case c₃ =>
        exact (coh_mem (L := lsAbove (lsAbove gls₀ (lifeN 2)) (lifeN 1)) (r := gr₃) (t := ⊤)
          (mem_lsAbove.mpr ⟨mem_lsAbove.mpr ⟨by simp, by decide⟩, by decide⟩)).1
      case p₃ =>
        exact ⟨LSet.singleton (lifeN 0), Val.unit, PMap.empty, ResU.inStratum_empty _,
          lsAbove (lsAbove (lsAbove gls₀ (lifeN 2)) (lifeN 1)) (lifeN 0), rfl, ⟨rfl, rfl⟩,
          show lifeN 2 ≤ lifeN 0 from by decide, fun x => mem_lsAbove⟩

/-- **`ViewTypeCoincidence`**: `1 ⊕ Imm 'x (Imm 'x (Imm 'x 1))` and `1 ⊕ 0` are one relation at
`'x ↦ 1` (the nested branch has no resource, `gB_unsat`), and two at the instantiation's `'x ↦ 2`,
where the gap at `1` is the nested branch's room (`gT_violator₀`). So a cell at a bound place being
its entry's view does not make a slot holding it typed as the entry's payload, and `CohS` asks the
types up to `TyEq`. -/
theorem viewTypeCoincidence : ViewTypeCoincidence := by
  refine ⟨gT, .sum .unit .zero, gs₁, gls₀, ⊤, gθ, fun u σ' => ⟨?_, ?_⟩, fun h => ?_⟩
  · rintro (⟨v₁, hv⟩ | ⟨v₂, hv⟩)
    · exact Or.inl ⟨v₁, hv⟩
    · obtain ⟨-, h₂⟩ := pure_sep_iff.mp hv
      exact (gB_unsat _ _ _ h₂).elim
  · rintro (⟨v₁, hv⟩ | ⟨v₂, hv⟩)
    · exact Or.inl ⟨v₁, hv⟩
    · obtain ⟨-, h₂⟩ := pure_sep_iff.mp hv
      exact h₂.elim
  · have hrec : Inst.recs (Inst.ofEmb gθ) gls₀ = gls₀ := by
      simp [Inst.recs, Inst.ofEmb]
    rw [hrec, gθ_sub] at h
    rcases (h (.inj₂ (.loc 0)) gw₁).mp gT_violator₀ with ⟨v₁, hv⟩ | ⟨v₂, hv⟩
    · obtain ⟨hv', -⟩ := pure_sep_iff.mp hv
      cases hv'
    · obtain ⟨-, h₂⟩ := pure_sep_iff.mp hv
      exact h₂.elim

end ProbeD1

end

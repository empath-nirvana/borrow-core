import ProbeD1.NxGuard

/-!
# ProbeD1 — the two-cell guard gap at the pair (`NEXT.md` item 1a): the configuration and the gate

The configuration `pc` of `NEXT.md` §1.4, built in the typed world and the revised arising set:

* **The world.** `TW.alloc` three times (`alloc_world`): the payload's places `1` and `2`, each
  owning `()`, then the owner `0` holding `(loc 1, loc 2)` (`pW₀`). `TW.immFrame` at the owner at
  `pα = 1` over `Ref 1 ⊗ Ref 1` (`pW₁`): its record `pRec` has no descendant (its payload holds no
  `mut` cell), and its frame is tagged at `pα` (`frameLife_frame`).
* **The configuration.** `pc₀` is `ArisesI.nil` at `pW₀`. The 6.64 lend of the owner (`LendImmI`)
  gives `pc`: one entry `pE` named `'0` at `pα`, the local part the frame's `imm` cell `pψ`, which
  arises as the lend's view (`ArisesVI.view`).
* **The index.** `SemIdxM` and `gRLM` at the view at the empty reading: the view is a `vRLM` value
  at `Imm '0 (Ref 1 ⊗ Ref 1)` (Core's `Imm` clause, coherent with `pRec`; `CohS` by the entry;
  `RetainedPay` vacuous at a lent place).
* **The program.** `withload p cb` at `withloadU`'s type at the empty row, the callback
  `Λ. λa. let (a₁, a₂) = a in forget a₁; forget a₂; ()`.
* **The own push and the reborrow.** The own push `pEn` at `pβ = 2` (place `3`, variable `'1`,
  payload `1`). [TR] 6.150's step `TW.reb` at `pRec` at `pβ`: the payload's two `own` cells become
  `imm({2}, (), ∅)` at `1` and `2` (`pcb`), composed into the world (`pW₂`, valid by its
  flattening), tagged (`tagged_reb`).
* **Link (d)** at every configuration of the pair's shape (`pairGuardRejectsU_of`), then the gate
  `withloadUPairGapReal`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty)

/-! ### Resources with cells at two and three places -/

/-- A resource with cells at two places. -/
def nxRes2 (a b : BoCa.Loc) (x y : CellU BoCa.Loc Val) : WRes where
  get := fun l => if l = a then some x else if l = b then some y else none
  finite := by
    refine ⟨[a, b], fun l h => ?_⟩
    by_cases e : l = a
    · exact List.mem_cons.mpr (Or.inl e)
    · by_cases f : l = b
      · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr f))
      · exfalso; apply h
        show (if l = a then some x else if l = b then some y else none) = none
        rw [if_neg e, if_neg f]

theorem nxRes2_a {a b : BoCa.Loc} (x y : CellU BoCa.Loc Val) : (nxRes2 a b x y).get a = some x := by
  show (if a = a then some x else _) = some x; rw [if_pos rfl]

theorem nxRes2_b {a b : BoCa.Loc} (x y : CellU BoCa.Loc Val) (h : b ≠ a) :
    (nxRes2 a b x y).get b = some y := by
  show (if b = a then some x else if b = b then some y else none) = some y
  rw [if_neg h, if_pos rfl]

theorem nxRes2_ne {a b l : BoCa.Loc} (x y : CellU BoCa.Loc Val) (ha : l ≠ a) (hb : l ≠ b) :
    (nxRes2 a b x y).get l = none := by
  show (if l = a then some x else if l = b then some y else none) = none
  rw [if_neg ha, if_neg hb]

/-- A resource with cells at three places. -/
def nxRes3 (a b c : BoCa.Loc) (x y z : CellU BoCa.Loc Val) : WRes where
  get := fun l =>
    if l = a then some x else if l = b then some y else if l = c then some z else none
  finite := by
    refine ⟨[a, b, c], fun l h => ?_⟩
    by_cases e : l = a
    · exact List.mem_cons.mpr (Or.inl e)
    · by_cases f : l = b
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl f)))
      · by_cases g : l = c
        · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr g))))
        · exfalso; apply h
          show (if l = a then some x else if l = b then some y else if l = c then some z
            else none) = none
          rw [if_neg e, if_neg f, if_neg g]

theorem nxRes3_a {a b c : BoCa.Loc} (x y z : CellU BoCa.Loc Val) :
    (nxRes3 a b c x y z).get a = some x := by
  show (if a = a then some x else _) = some x; rw [if_pos rfl]

theorem nxRes3_b {a b c : BoCa.Loc} (x y z : CellU BoCa.Loc Val) (h : b ≠ a) :
    (nxRes3 a b c x y z).get b = some y := by
  show (if b = a then some x else if b = b then some y else _) = some y
  rw [if_neg h, if_pos rfl]

theorem nxRes3_c {a b c : BoCa.Loc} (x y z : CellU BoCa.Loc Val) (ha : c ≠ a) (hb : c ≠ b) :
    (nxRes3 a b c x y z).get c = some z := by
  show (if c = a then some x else if c = b then some y else if c = c then some z else none)
    = some z
  rw [if_neg ha, if_neg hb, if_pos rfl]

theorem nxRes3_ne {a b c l : BoCa.Loc} (x y z : CellU BoCa.Loc Val) (ha : l ≠ a) (hb : l ≠ b)
    (hc : l ≠ c) : (nxRes3 a b c x y z).get l = none := by
  show (if l = a then some x else if l = b then some y else if l = c then some z else none) = none
  rw [if_neg ha, if_neg hb, if_neg hc]

/-! ### The pair's objects -/

/-- The pair's value: the owner holds the two places. -/
abbrev pV : Val := .pair (.loc 1) (.loc 2)

/-- The lend's lifetime. -/
abbrev pα : Life := lifeN 1

/-- The own push's lifetime, below the lend. -/
abbrev pβ : Life := lifeN 2

/-- The payload: `1 ↦ own(())`, `2 ↦ own(())`. -/
def pR : WRes := nxRes2 1 2 (CellU.ownOf .unit) (CellU.ownOf .unit)

theorem pR_1 : pR.get 1 = some (CellU.ownOf .unit) := nxRes2_a _ _
theorem pR_2 : pR.get 2 = some (CellU.ownOf .unit) := nxRes2_b _ _ (by decide)
theorem pR_ne {l : BoCa.Loc} (h1 : l ≠ 1) (h2 : l ≠ 2) : pR.get l = none := nxRes2_ne _ _ h1 h2

theorem pR_strat (γ : Life) : pR.InStratum γ := by
  intro l ψ e
  by_cases e1 : l = 1
  · subst e1; rw [pR_1] at e; cases e; exact trivial
  · by_cases e2 : l = 2
    · subst e2; rw [pR_2] at e; cases e; exact trivial
    · rw [pR_ne e1 e2] at e; cases e

/-- The frame's `imm` cell at the owner: `imm({1}, (loc 1, loc 2), pR)`. -/
def pψ : CellU BoCa.Loc Val := CellU.immOf (LSet.singleton pα) pV pR (pR_strat _)

/-- The world before the lend. -/
def pW₀ : WRes := nxRes3 0 1 2 (CellU.ownOf pV) (CellU.ownOf .unit) (CellU.ownOf .unit)

/-- The world after the lend: the frame's cell. -/
def pW₁ : WRes := ResU.single 0 pψ

/-- A reborrowed cell: `imm({2}, (), ∅)`. -/
def pImm : CellU BoCa.Loc Val :=
  CellU.immOf (LSet.singleton pβ) .unit PMap.empty (ResU.inStratum_empty _)

/-- [TR] 6.150's reborrow of the payload at `pβ`. -/
def pcb : WRes := nxRes2 1 2 pImm pImm

/-- The world after the reborrow. -/
def pW₂ : WRes := nxRes3 0 1 2 pψ pImm pImm

/-- The lend's entry: place `0`, variable `'0`, payload `Ref 1 ⊗ Ref 1`, a 6.64 entry. -/
def pE : LEnt := ⟨0, 0, pairTy, .imm pV, fun _ => true⟩

/-- The frame's record. -/
def pRec : FrameRec := ⟨0, pV, pR, pairTy, ⟨[]⟩⟩

/-- The records: `pRec` tagged at the lend's lifetime. -/
def pls : List SRec := [(pRec, pα)]

/-- The configuration before the lend. -/
def pc₀ : Cfg := ⟨pW₀, PMap.empty, pW₀, [], [], [], []⟩

/-- The configuration after the lend. -/
def pc : Cfg := ⟨pW₁, PMap.empty, pW₁, [pRec], pls, [pE], [pα]⟩

/-- The own push: place `3`, variable `'1`, payload `1`. -/
def pEn : LEnt := ⟨3, 1, .unit, .imm .unit, fun _ => true⟩

/-! ### Compositions of disjoint resources -/

/-- **Disjoint parts compose to their union**, at either operator. -/
theorem nxComp_disjoint {R : CellU BoCa.Loc Val → CellU BoCa.Loc Val → Prop}
    {C : CellU BoCa.Loc Val → CellU BoCa.Loc Val → CellU BoCa.Loc Val → Prop} {ρ₁ ρ₂ ρ : WRes}
    (hd : ∀ l, ρ₁.get l = none ∨ ρ₂.get l = none)
    (h : ∀ l, ρ.get l = (ρ₁.get l).or (ρ₂.get l)) : ResU.Comp R C ρ₁ ρ₂ ρ := by
  refine ⟨ResU.Compat.of_disjoint hd, fun l => ?_⟩
  rw [h l]
  rcases hd l with e | e
  · rw [e]; cases ρ₂.get l <;> rfl
  · rw [e]; cases ρ₁.get l <;> rfl

theorem nxCompS_disjoint {ρ₁ ρ₂ ρ : WRes} (hd : ∀ l, ρ₁.get l = none ∨ ρ₂.get l = none)
    (h : ∀ l, ρ.get l = (ρ₁.get l).or (ρ₂.get l)) : ResU.CompS ρ₁ ρ₂ ρ := nxComp_disjoint hd h

theorem comp_pR' {R : CellU BoCa.Loc Val → CellU BoCa.Loc Val → Prop}
    {C : CellU BoCa.Loc Val → CellU BoCa.Loc Val → CellU BoCa.Loc Val → Prop} :
    ResU.Comp R C (ResU.single 1 (CellU.ownOf .unit)) (ResU.single 2 (CellU.ownOf .unit)) pR := by
  refine nxComp_disjoint (fun l => ?_) (fun l => ?_)
  · by_cases e1 : l = 1
    · subst e1; exact Or.inr (ResU.single_get_ne _ (by decide))
    · exact Or.inl (ResU.single_get_ne _ e1)
  · by_cases e1 : l = 1
    · subst e1; rw [pR_1, ResU.single_get_self]; rfl
    · by_cases e2 : l = 2
      · subst e2; rw [pR_2, ResU.single_get_ne _ (by decide), ResU.single_get_self]; rfl
      · rw [pR_ne e1 e2, ResU.single_get_ne _ e1, ResU.single_get_ne _ e2]; rfl

theorem comp_pR :
    ResU.CompS (ResU.single 1 (CellU.ownOf .unit)) (ResU.single 2 (CellU.ownOf .unit)) pR :=
  comp_pR'

theorem pW₀_0 : pW₀.get 0 = some (CellU.ownOf pV) := nxRes3_a _ _ _
theorem pW₀_1 : pW₀.get 1 = some (CellU.ownOf .unit) := nxRes3_b _ _ _ (by decide)
theorem pW₀_2 : pW₀.get 2 = some (CellU.ownOf .unit) := nxRes3_c _ _ _ (by decide) (by decide)
theorem pW₀_ne {l : BoCa.Loc} (h0 : l ≠ 0) (h1 : l ≠ 1) (h2 : l ≠ 2) : pW₀.get l = none :=
  nxRes3_ne _ _ _ h0 h1 h2

theorem comp_pW₀ : ResU.CompS pR (ResU.single 0 (CellU.ownOf pV)) pW₀ := by
  refine nxCompS_disjoint (fun l => ?_) (fun l => ?_)
  · by_cases e0 : l = 0
    · subst e0; exact Or.inl (pR_ne (by decide) (by decide))
    · exact Or.inr (ResU.single_get_ne _ e0)
  · by_cases e0 : l = 0
    · subst e0; rw [pW₀_0, pR_ne (by decide) (by decide), ResU.single_get_self]; rfl
    · rw [ResU.single_get_ne _ e0]
      by_cases e1 : l = 1
      · subst e1; rw [pW₀_1, pR_1]; rfl
      · by_cases e2 : l = 2
        · subst e2; rw [pW₀_2, pR_2]; rfl
        · rw [pW₀_ne e0 e1 e2, pR_ne e1 e2]; rfl

/-- The owner and its payload. -/
theorem comp_owner_pR : ResU.CompS (ResU.single 0 (CellU.ownOf pV)) pR pW₀ :=
  ResU.CompS.comm comp_pW₀

/-! ### The world before the lend: three allocations -/

/-- **`pW₀` is a typed world**: `1` and `2` allocated holding `()`, then `0` holding
`(loc 1, loc 2)` (`alloc_world` three times). -/
theorem pW₀_tw : TW pW₀ [] [] := by
  -- `1`
  obtain ⟨x₁, σ₁, hx₁, hf₁, hσ₁, hT₁, hμ₁, -, -⟩ := alloc_world (ρf := PMap.empty)
    (ρ := PMap.empty) (σ := PMap.empty) (l := 1) (μ := fun _ => none) Val.unit
    hash_empty_empty (ResU.comp_empty_left _) TW.empty lower_empty rfl
  obtain rfl := ResU.CompS.functional hx₁ (ResU.comp_empty_left _)
  obtain rfl := ResU.CompS.functional hσ₁ (ResU.comp_empty_left _)
  -- `2`
  obtain ⟨x₂, σ₂, hx₂, hf₂, hσ₂, hT₂, hμ₂, -, -⟩ := alloc_world (ρf := PMap.empty)
    (ρ := ResU.single 1 (CellU.ownOf .unit)) (l := 2) Val.unit hf₁ (ResU.comp_empty_left _)
    hT₁ hμ₁ rfl
  obtain rfl := ResU.CompS.functional hx₂ comp_pR
  obtain rfl := ResU.CompS.functional hσ₂ (ResU.comp_empty_left _)
  -- `0`
  obtain ⟨x₃, σ₃, hx₃, -, hσ₃, hT₃, -, -, -⟩ := alloc_world (ρf := PMap.empty) (ρ := pR) (l := 0)
    pV hf₂ (ResU.comp_empty_left _) hT₂ hμ₂ rfl
  obtain rfl := ResU.CompS.functional hx₃ comp_pW₀
  obtain rfl := ResU.CompS.functional hσ₃ (ResU.comp_empty_left _)
  exact hT₃

/-! ### The lend: `TW.immFrame` at the owner -/

theorem pψ_kind : pψ.kind = Kind.imm := CellU.kind_immOf _ _ _ _

theorem pψ_wit : pψ.wit = pR := CellU.wit_immOf _ _ _ _

/-- The flattening of the frame's cell: the cell, and its payload's `own` cells. -/
def pσ₁ : WRes := nxRes3 0 1 2 pψ (CellU.ownOf .unit) (CellU.ownOf .unit)

theorem pσ₁_0 : pσ₁.get 0 = some pψ := nxRes3_a _ _ _
theorem pσ₁_1 : pσ₁.get 1 = some (CellU.ownOf .unit) := nxRes3_b _ _ _ (by decide)
theorem pσ₁_2 : pσ₁.get 2 = some (CellU.ownOf .unit) := nxRes3_c _ _ _ (by decide) (by decide)
theorem pσ₁_ne {l : BoCa.Loc} (h0 : l ≠ 0) (h1 : l ≠ 1) (h2 : l ≠ 2) : pσ₁.get l = none :=
  nxRes3_ne _ _ _ h0 h1 h2

/-- `⦇pR⦈_○ = pR`: two `own` cells. -/
theorem pR_flatR : ResU.FlatR pR pR := by
  refine ⟨PMap.empty, pR, ?_, ?_, ResU.comp_empty_left _⟩
  · exact (AgW.split comp_pR).mpr ⟨PMap.empty, PMap.empty, AgW.single_own 1 Val.unit,
      AgW.single_own 2 Val.unit, ResU.comp_empty_left _⟩
  · exact (ExR.split_of_compS comp_pR).mpr ⟨_, _, ExW.single_own 1 Val.unit,
      ExW.single_own 2 Val.unit, comp_pR'⟩

theorem comp_pψ_pR : ResU.CompR (ResU.single 0 pψ) pR pσ₁ := by
  refine nxComp_disjoint (fun l => ?_) (fun l => ?_)
  · by_cases e0 : l = 0
    · subst e0; exact Or.inr (pR_ne (by decide) (by decide))
    · exact Or.inl (ResU.single_get_ne _ e0)
  · by_cases e0 : l = 0
    · subst e0; rw [pσ₁_0, ResU.single_get_self]; rfl
    · rw [ResU.single_get_ne _ e0]
      by_cases e1 : l = 1
      · subst e1; rw [pσ₁_1, pR_1]; rfl
      · by_cases e2 : l = 2
        · subst e2; rw [pσ₁_2, pR_2]; rfl
        · rw [pσ₁_ne e0 e1 e2, pR_ne e1 e2]; rfl

/-- **The world after the lend is valid**: `ex = ∅` (no `own` or `mut` cell), `ag` the frame's
cell beside its payload's `own` cells. -/
theorem pW₁_valid : ResU.Valid pW₁ := by
  refine ⟨pσ₁, PMap.empty, pσ₁, ExW.empty_of_all_imm (fun l ψ h => ?_), ?_,
    ResU.comp_empty_left _⟩
  · obtain ⟨-, rfl⟩ := ResU.single_get_eq_some h; exact pψ_kind
  · exact AgW.single_imm pR_flatR comp_pψ_pR

/-- The record's payload holds no `mut` cell, so it has no descendant. -/
theorem pRec_not_desc (d : FrameRec) : ¬ Desc pRec d := by
  rintro ⟨p, hp, hlin⟩
  cases hlin with
  | nil => exact hp rfl
  | @cons _ d' _ _ hsub _ =>
      obtain ⟨-, -, ζ, hζ, hk, -⟩ := hsub
      change pR.get _ = some ζ at hζ
      by_cases e1 : d'.le = 1
      · rw [e1, pR_1] at hζ; cases hζ; exact Kind.noConfusion hk
      · by_cases e2 : d'.le = 2
        · rw [e2, pR_2] at hζ; cases hζ; exact Kind.noConfusion hk
        · rw [pR_ne e1 e2] at hζ; cases hζ

theorem pairTy_closed (y : LifeVar) : ¬ VFree y pairTy := by
  rintro (h | h) <;> exact h

/-- `vShape (Ref 1 ⊗ Ref 1)` at the payload. -/
theorem pR_shape (δ : LSub) : vShape pairTy δ pV pR := by
  refine ⟨.loc 1, .loc 2, pure_sep_iff.mpr ⟨rfl, ResU.single 1 (CellU.ownOf .unit),
    ResU.single 2 (CellU.ownOf .unit), comp_pR, ?_, ?_⟩⟩
  · exact ⟨1, .unit, pure_sep_iff.mpr ⟨rfl, _, PMap.empty, ResU.comp_empty_right _, rfl,
      rfl, rfl⟩⟩
  · exact ⟨2, .unit, pure_sep_iff.mpr ⟨rfl, _, PMap.empty, ResU.comp_empty_right _, rfl,
      rfl, rfl⟩⟩

/-- **The lend's world is typed**: `TW.immFrame` at the owner. -/
theorem pW₁_tw : TW pW₁ [pRec] [pRec] := by
  have := TW.immFrame (W := pW₀) (X := pW₀) (Z := PMap.empty) (R := pR) (W' := pW₁) (ps := [])
    (rs := []) (ds := []) (l := 0) (v := pV) (α := pα) pairTy ⟨[]⟩ (pR_strat _) pW₀_tw
    (fun y hy => absurd hy (pairTy_closed y)) comp_owner_pR (ResU.comp_empty_right _)
    (pR_shape _) (ResU.comp_empty_right _) pW₁_valid
    (fun d => ⟨fun h => absurd h (by simp), fun h => absurd h (pRec_not_desc d)⟩)
  exact this

/-- The frame is at `pα`. -/
theorem pW₁_frameLife : FrameLife pW₁ pRec pα :=
  (frameLife_frame (W := pW₀) (X := pW₀) (Z := PMap.empty) (R := pR) (W' := pW₁) (l := 0)
    (v := pV) (α := pα) pairTy ⟨[]⟩ (TW.valid pW₀_tw) comp_owner_pR (ResU.comp_empty_right _)
    (ResU.comp_empty_right _) (TW.inv pW₀_tw)).1

theorem pW₁_tagged : Tagged pW₁ [pRec] pls := by
  intro x hx
  rw [pls, List.mem_singleton] at hx
  subst hx
  exact ⟨pRec, List.mem_singleton_self _, ⟨[], LinPath.nil _⟩, pW₁_frameLife⟩

/-! ### The configuration -/

theorem pα_lt_top : pα < ⊤ := by decide

theorem pβ_lt_pα : pβ < pα := by decide

theorem pW₀_valid : ResU.Valid pW₀ := TW.valid pW₀_tw

/-- **The configuration before the lend arises** (`ArisesI.nil`). -/
theorem pc₀_arises : ArisesI (ℍ := ℍ) pc₀ :=
  ArisesI.nil pW₀_tw (fun _ hx => absurd hx List.not_mem_nil)
    ⟨ResU.Compat.of_disjoint (fun _ => Or.inl rfl), pW₀, ResU.comp_empty_left _, pW₀_valid⟩
    (ResU.comp_empty_left _)

theorem hash_empty_pW₁ : ResU.Hash (PMap.empty : WRes) pW₁ :=
  ⟨ResU.Compat.of_disjoint (fun _ => Or.inl rfl), pW₁, ResU.comp_empty_left _, pW₁_valid⟩

/-- **The 6.64 lend of the owner** (`LendImmI`): the entry pushed at `pα`, fresh below the
(empty) records and below `⊤`. -/
theorem pLend : LendImmI pc₀ pc pE := by
  refine ⟨⟨rfl, rfl, List.not_mem_nil, List.not_mem_nil, pα, pV, pR, pW₀, PMap.empty,
    PMap.empty, ⟨[]⟩, pR_strat _, [], rfl, rfl, List.isChain_singleton _,
    ResU.inStratum_empty _, fun y hy => absurd hy (pairTy_closed y), comp_owner_pR,
    ResU.comp_empty_right _, ResU.comp_empty_right _, pR_shape _, ResU.comp_empty_right _,
    pW₁_valid, fun d => ⟨fun h => absurd h (by simp), fun h => absurd h (pRec_not_desc d)⟩, rfl,
    rfl, ResU.comp_empty_right _, hash_empty_pW₁, ResU.comp_empty_left _, pW₁_tagged⟩,
    fun α _ _x hx => absurd hx List.not_mem_nil, fun α hα => ?_⟩
  cases hα
  exact pα_lt_top

/-- **The configuration after the lend arises.** -/
theorem pc_arises : ArisesI (ℍ := ℍ) pc := ArisesI.lendImm pc₀_arises pLend

/-- **The lend's view arises** at `pc`, its cell the local part. -/
theorem pView : ArisesVI (ℍ := ℍ) (pc.at PMap.empty (ResU.single pE.l pψ)) (.loc pE.l)
    (viewTy pE) :=
  ArisesVI.view pc₀_arises (Or.inr pLend) (ResU.comp_empty_right _) (ResU.comp_empty_right _)

/-! ### The index at the view -/

/-- The stack's reading at the empty substitution: `'0 ↦ 1`. -/
abbrev pS : LSub := extS ⟨[]⟩ [pE] [pα]

theorem pS_find0 : pS.find? 0 = some 1 := rfl

/-- **Core's relation at `Ref 1 ⊗ Ref 1` holds of the payload**, in either mode, at every list and
reading. -/
theorem pR_vC (b : Bool) (ls : List SRec) (s : LSub) : vCE none b pairTy ls s pV pR := by
  refine ⟨.loc 1, .loc 2, pure_sep_iff.mpr ⟨rfl, ResU.single 1 (CellU.ownOf .unit),
    ResU.single 2 (CellU.ownOf .unit), comp_pR, ?_, ?_⟩⟩
  · exact ⟨1, .unit, pure_sep_iff.mpr ⟨rfl, _, PMap.empty, ResU.comp_empty_right _, rfl,
      rfl, rfl⟩⟩
  · exact ⟨2, .unit, pure_sep_iff.mpr ⟨rfl, _, PMap.empty, ResU.comp_empty_right _, rfl,
      rfl, rfl⟩⟩

/-- **The frame's cell at the payload's relation**, at the list `pls` (no record of it is
strictly longer-lived than the cell). -/
theorem pψ_ptoImmS (b : Bool) (s : LSub) :
    ptoImmS 0 pα pls (fun ls₀ => vCE none b pairTy ls₀ s) pW₁ := by
  refine ⟨LSet.singleton pα, pV, pR, pR_strat _, [], rfl, pR_vC b [] s, le_rfl, fun x => ?_⟩
  simp only [List.not_mem_nil, false_iff, not_and]
  intro hx
  rw [pls, List.mem_singleton] at hx
  subst hx
  exact lt_irrefl _

theorem pψ_atExactly : AtExactly pα pψ :=
  ⟨rfl, fun t ht y hy => by
    simp only [pψ, CellU.lsOf_immOf, Option.some.injEq] at ht
    subst ht; exact hy⟩

/-- **The view is `pE`'s view** at the stack's reading. -/
theorem pψ_view (s : LSub) : vwEW s pE true pα pls pW₁ := by
  refine ⟨pψ_ptoImmS true s, fun ψ hψ => ?_⟩
  obtain rfl := Option.some.inj ((ResU.single_get_self _ _).symm.trans hψ)
  exact pψ_atExactly

/-- A cell under the frame's cell is one of its payload's `own` cells. -/
theorem pR_deepAt_own {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val} (h : DeepAt pR l ψ) :
    ψ.kind = Kind.own := by
  have hown : ∀ m φ, pR.get m = some φ → φ = CellU.ownOf .unit := by
    intro m φ e
    by_cases e1 : m = 1
    · subst e1; rw [pR_1] at e; exact (Option.some.inj e).symm
    · by_cases e2 : m = 2
      · subst e2; rw [pR_2] at e; exact (Option.some.inj e).symm
      · rw [pR_ne e1 e2] at e; cases e
  cases h with
  | top e => rw [hown _ _ e]; rfl
  | wit e hd =>
      rw [hown _ _ e] at hd
      cases hd with
      | top e' => exact absurd e' (by simp [CellU.ownOf, CellU.wit])
      | wit e' _ => exact absurd e' (by simp [CellU.ownOf, CellU.wit])

/-- **The guard's views at the view.** -/
theorem pW₁_placeViews : PlaceViewsL pS [pE] [pα] pls pW₁ := by
  have hi : innerAt [pE] [pα] 0 = some (pE, pα) := by simp [innerAt, pE]
  refine ⟨fun l ψ hex hk e α hin => ?_, fun l ψ hd hk hl => ?_⟩
  · cases hex with
    | top e₀ =>
        obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e₀
        rw [hi] at hin
        obtain ⟨rfl, rfl⟩ : pE = e ∧ pα = α := by simpa using hin
        exact pψ_view pS
    | wit e₀ hm _ =>
        obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e₀
        exact absurd hm (by rw [pψ_kind]; exact fun h => Kind.noConfusion h)
  · cases hd with
    | top e₀ =>
        obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e₀
        exact ⟨pE, pα, List.mem_singleton_self _, rfl, pψ_view pS⟩
    | wit e₀ hd' =>
        obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e₀
        rw [pψ_wit] at hd'
        exact absurd (pR_deepAt_own hd') hk

theorem pW₁_tab : TabAtS [pE] [pα] pW₁ := by
  refine ⟨fun a ha => ?_, fun a _ k ψ hk e₀ => ?_⟩
  · cases ha
    exact ResU.inStratum_single _ (GhostEnd.down_lt pα)
  · obtain ⟨rfl, -⟩ := ResU.single_get_eq_some e₀
    exact absurd (List.mem_singleton_self _) hk

/-- **`SemSM`'s index at the view**, at the judgement `pairΔ; pairΓ ⊢ _ : F 1`. -/
theorem pSemIdx : SemIdxM pairΔ pairΓ (.ret .unit) ⟨[]⟩ [pE] [pα] pls pW₁ := by
  refine ⟨⟨fun x hx => absurd hx (by simp [CTy.binders, VTy.binders]), fun s hs _ x hx => ?_⟩,
    ⟨fun y hy => absurd hy (by simp [CFree, VFree]), fun s hs _ y hy => ?_⟩,
    ⟨rfl, List.isChain_singleton _, by simp [pE]⟩, ?_, ⟨by simp [pE], fun e he y hy => ?_,
      fun e he => ?_⟩, fun y hy => absurd rfl hy, ?_, ?_, ?_, pW₁_tab, pW₁_placeViews⟩
  · rw [List.mem_singleton] at hs; subst hs
    simp [VTy.binders] at hx
  · rw [List.mem_singleton] at hs; subst hs
    rcases hy with h | h
    · have : y = 0 := by simpa [Lifetime.Life.mentions] using h
      subst this
      exact ⟨.top, rfl⟩
    · exact absurd h (pairTy_closed y)
  · intro o ho
    cases ho
    exact pα_lt_top
  · rw [List.mem_singleton] at he; subst he
    exact absurd hy (pairTy_closed y)
  · rw [List.mem_singleton] at he; subst he
    exact Or.inl ⟨.top, rfl⟩
  · intro x u hu
    simp [LifeCtx.find?, LifeCtx.extend, LifeCtx.empty, Lifetime.assocFind] at hu
    obtain ⟨rfl, rfl⟩ := hu
    exact ⟨1, 0, rfl, rfl, show (0 : ℕ) < 1 from Nat.zero_lt_one⟩
  · intro a ha x hx hlt
    simp only [pls, List.mem_singleton] at ha hx; subst ha; subst hx
    exact absurd hlt (lt_irrefl _)
  · intro e a _ p hp
    simp [boundBefore] at hp

/-- **The view is a `vRLM` value at `Imm '0 (Ref 1 ⊗ Ref 1)`**: Core's `Imm` clause coherent with
`pRec`, `CohS` at `pE`, and `RetainedPay` vacuous at the lent place. -/
theorem pView_vRLM :
    vRLM (ℍ := ℍ) .binder0 none [pE] ⟨[]⟩ (.imm (.var 0) pairTy) [pα] pls (.loc 0) pW₁ := by
  rw [vRLM_imm_eq, vRLJ_imm_eq]
  refine ⟨⟨1, pS_find0, 0, pure_sep_iff.mpr ⟨⟨rfl, pairTy, pS, TyEq.refl _ _,
    Or.inl ⟨pRec, List.mem_singleton_self _, rfl, rfl, fun y hy => absurd hy (pairTy_closed y)⟩⟩,
    pψ_ptoImmS false pS⟩⟩, fun l e α hl hin => ?_, fun l hl hin => ?_⟩
  · cases hl
    have hi : innerAt [pE] [pα] 0 = some (pE, pα) := by simp [innerAt, pE]
    rw [hi] at hin
    obtain ⟨rfl, rfl⟩ : pE = e ∧ pα = α := by simpa using hin
    refine ⟨⟨trivial, TyEq.refl _ _⟩, fun ψ hψ => ?_⟩
    obtain rfl := Option.some.inj ((ResU.single_get_self _ _).symm.trans hψ)
    rfl
  · cases hl
    exact absurd hin (by simp [innerAt, pE])

/-- **The context at the view.** -/
theorem pgRLM : gRLM (ℍ := ℍ) .binder0 [pE] ⟨[]⟩ [pα] pls pairΓ [.loc 0] pW₁ :=
  pure_sep_iff.mpr ⟨trivial, pW₁, PMap.empty, ResU.comp_empty_right _, pView_vRLM, rfl, trivial⟩

/-- **The pair configuration** (`PairCfg`) at `pc`. -/
theorem pairCfg : PairCfg (ℍ := ℍ) pc pE pα pψ PMap.empty pRec 1 2 ⟨[]⟩ .unit :=
  ⟨pc_arises, rfl, rfl, rfl, rfl, ResU.single_get_self _ _, pView, List.mem_singleton_self _,
    List.mem_singleton_self _, rfl, rfl, rfl, pψ_wit, pR_1, pR_2, by decide, by simp [pc, pE],
    by simp [pc, pE], pSemIdx, pgRLM⟩

/-! ### The program at `withloadU`'s type -/

/-- `Imm '0 (Ref 1 ⊗ Ref 1)`. -/
abbrev pIMM : VTy := .imm (.var 0) pairTy

/-- `Imm '1 1`. -/
abbrev pI : VTy := .imm (.var 1) .unit

/-- The callback's body under `Λ. λa.`: `let (a₂, a₁) = a in forget a₂; forget a₁; ()`. -/
abbrev pCbBody : Expr :=
  .letpair (.var 0) (.seq (.app forget (.var 0)) (.seq (.app forget (.var 1)) (.val .unit)))

/-- The callback: `Λ. λa. let (a₂, a₁) = a in forget a₂; forget a₁; ()`. -/
abbrev pCbE : Expr := .val (.lam (.val (.lam pCbBody)))

theorem pairΔ_find_one : pairΔ.find? 1 = none := rfl

/-- **The callback is typed at `withloadU`'s callback type**, `U (∀'1 ⊏ ⊓Δ. Imm̲ '1 (Ref 1 ⊗ Ref 1) ⊸
F (['1] 1))`: it consumes both `imm` leaves (`forget`) and answers `()` boxed. -/
theorem pCbE_typed :
    Targets.CDerivesNU pairΔ [⟨pIMM, false⟩] pCbE
      (.comp (.ret (cbUTy 1 pairΔ.meetOfDom (pairTy.immReborrow (.var 1)) .unit []))) := by
  refine .ret (.thunkV rfl (.allI (S := .unit) rfl (fun y u hu => ?_) (fun s hs hl => ?_)
    (.lam ?_)))
  · simp [LifeCtx.find?, LifeCtx.extend, LifeCtx.empty, Lifetime.assocFind] at hu
    obtain ⟨-, rfl⟩ := hu
    rfl
  · rw [List.mem_singleton] at hs; subst hs; exact absurd hl (by simp)
  · refine .tensorE (.left (.dead (.dead .nil))) (.var (.here (.cons (.cons .nil)))) ?_
    refine .unitE (.left (.right (.dead (.dead (.dead .nil)))))
      (.lolliE (.left (.dead (.dead (.dead (.dead .nil)))))
        (.var (.here (.cons (.cons (.cons (.cons .nil))))))
        (.forgetImm (.cons (.cons (.cons (.cons (.cons .nil))))))) ?_
    refine .unitE (.dead (.left (.dead (.dead (.dead .nil)))))
      (.lolliE (.dead (.left (.dead (.dead (.dead .nil)))))
        (.var (.there (.here (.cons (.cons (.cons .nil))))))
        (.forgetImm (.cons (.cons (.cons (.cons (.cons .nil))))))) ?_
    refine .ret (.boxI (.unitI (.cons (.cons (.cons (.cons (.cons .nil)))))) ⟨fun δ hδ => ?_,
      fun s hs hl => ?_⟩)
    · obtain ⟨m, n, hm, -, -⟩ := hδ 1 pairΔ.meetOfDom rfl
      exact ⟨m, hm⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl | rfl <;> exact absurd hl (by simp)

/-- **`PairWithloadUTyped`**: `withload p cb` at `withloadU`'s type at the empty row. -/
theorem pairProgU_typed : ProbeRules pairΔ pairΓ (pairProgU pCbE) (.comp (.ret .unit)) := by
  refine probeRules_of_nu (.bind (.right .nil) pCbE_typed ?_)
  refine .bind (.right (.right .nil))
    (.ret (.withloadU (a := .var 0) (A := pairTy) (B := .unit) (S := []) 1
      (.cons (.cons .nil)) pairΔ_find_one (pairTy_closed 1) (fun h => h)
      (fun o ho => absurd ho List.not_mem_nil))) ?_
  exact .app (.left (.right (.left .nil)))
    (.app (.left (.dead (.right .nil))) (.force (.here (.cons (.cons .nil))))
      (.there (.there (.here .nil))))
    (.there (.here (.cons .nil)))

theorem pairWithloadUTyped : PairWithloadUTyped := ⟨pCbE, .unit, pairProgU_typed⟩

/-! ### The own push -/

/-- **An own push of `withloadU`'s callback at `pc`'s index**: `pEn` at `pβ`, below the lend and the
bound, its variable and place new, its payload type `1` closed. `ViewAt` is vacuous at the
argument type `Imm '1 1 ⊗ Imm '1 1`. -/
theorem pOwnPush (ρc : WRes) (hρc : ∀ ψ, ¬ DeepAt ρc 3 ψ) (hb : ρc.InStratum pβ) :
    OwnPushI ⟨[]⟩ (pairCbUC 1 .unit) ρc ([pE], [pα]) pEn pβ := by
  refine ⟨1, pairΔ.meetOfDom, _, rfl, rfl,
    by simp [CTy.binders, VTy.binders, pairTy_immReborrow],
    ⟨⟨List.IsChain.cons_cons pβ_lt_pα (List.isChain_singleton _), hb, by simp [pE, pEn],
      by simp [pE, pEn], fun y hy => absurd hy (by simp [pEn, VFree])⟩, hρc⟩, ⟨1, ?_, pβ_lt_pα⟩,
    fun A D h => ?_⟩
  · show (pairΔ.meetOfDom).interp pS = some 1
    rfl
  · cases h
    trivial

/-! ### [TR] 6.150's reborrow at `pβ` -/

theorem pcb_1 : pcb.get 1 = some pImm := nxRes2_a _ _
theorem pcb_2 : pcb.get 2 = some pImm := nxRes2_b _ _ (by decide)
theorem pcb_ne {l : BoCa.Loc} (h1 : l ≠ 1) (h2 : l ≠ 2) : pcb.get l = none := nxRes2_ne _ _ h1 h2

theorem comp_pcb' {R : CellU BoCa.Loc Val → CellU BoCa.Loc Val → Prop}
    {C : CellU BoCa.Loc Val → CellU BoCa.Loc Val → CellU BoCa.Loc Val → Prop} :
    ResU.Comp R C (ResU.single 1 pImm) (ResU.single 2 pImm) pcb := by
  refine nxComp_disjoint (fun l => ?_) (fun l => ?_)
  · by_cases e1 : l = 1
    · subst e1; exact Or.inr (ResU.single_get_ne _ (by decide))
    · exact Or.inl (ResU.single_get_ne _ e1)
  · by_cases e1 : l = 1
    · subst e1; rw [pcb_1, ResU.single_get_self]; rfl
    · by_cases e2 : l = 2
      · subst e2; rw [pcb_2, ResU.single_get_ne _ (by decide), ResU.single_get_self]; rfl
      · rw [pcb_ne e1 e2, ResU.single_get_ne _ e1, ResU.single_get_ne _ e2]; rfl

theorem comp_pcb : ResU.CompS (ResU.single 1 pImm) (ResU.single 2 pImm) pcb := comp_pcb'

theorem single_del_self (l : BoCa.Loc) (ψ : CellU BoCa.Loc Val) :
    (ResU.single l ψ).del l = (PMap.empty : WRes) := by
  refine PMap.ext fun l' => ?_
  by_cases h : l' = l
  · subst h; exact ResU.del_get_self _ _
  · rw [ResU.del_get_ne _ h, ResU.single_get_ne _ h]; rfl

/-- `reb_β`'s clauses at one of the payload's `own` cells, its piece the cell itself. -/
theorem pRebAt {l : BoCa.Loc} (hl : pR.get l = some (CellU.ownOf .unit))
    (hc : pcb.get l = some pImm) :
    ResU.RebAt pβ pR pcb l (ResU.single l (CellU.ownOf .unit)) := by
  refine ⟨⟨_, ResU.single_get_self _ _⟩, fun v hv => ?_, fun b v χ hb P hw hv => ?_,
    fun s v χ h hv => ?_⟩
  · rw [hl] at hv
    obtain rfl : Val.unit = v := by simpa [CellU.ownOf] using hv
    rw [single_del_self]
    exact ⟨ResU.inStratum_empty _, hc⟩
  · rw [hl] at hv; simp [CellU.ownOf, CellU.mutOf] at hv
  · rw [hl] at hv; simp [CellU.ownOf, CellU.immOf] at hv

/-- **`reb_{pβ}(pR) ∋ pcb`**: `π` takes each `own` cell as its own piece. -/
theorem pReb : ResU.Reb pβ pR pcb := by
  refine ⟨pR_strat _, [(1, ResU.single 1 (CellU.ownOf .unit)),
    (2, ResU.single 2 (CellU.ownOf .unit))], pR, ⟨by decide, fun l => ⟨fun h => ?_, fun h => ?_⟩⟩,
    BigComp.cons (BigComp.cons BigComp.nil (ResU.comp_empty_right _)) comp_pR,
    ⟨PMap.empty, ResU.comp_empty_right _⟩, fun l p hp => ?_⟩
  · simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact ⟨_, pcb_1⟩
    · exact ⟨_, pcb_2⟩
  · obtain ⟨ψ, hψ⟩ := h
    by_cases e1 : l = 1
    · subst e1; simp
    · by_cases e2 : l = 2
      · subst e2; simp
      · rw [pcb_ne e1 e2] at hψ; cases hψ
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact pRebAt pR_1 pcb_1
    · exact pRebAt pR_2 pcb_2

/-- The shape of `Imm '1 1` at a reborrowed cell. -/
theorem pImm_shape (l : BoCa.Loc) :
    vShape (.imm (.var 1) .unit) (LSub.extend ⟨[]⟩ 1 pβ) (.loc l) (ResU.single l pImm) :=
  ⟨2, rfl, l, pure_sep_iff.mpr ⟨rfl, LSet.singleton pβ, .unit, PMap.empty,
    ResU.inStratum_empty _, rfl, ⟨rfl, rfl⟩, le_rfl⟩⟩

/-- **[TR] 6.150's reborrow of `pRec`'s payload at `pβ`** (`PairReb`). -/
theorem pPairReb : PairReb pRec 1 pβ pcb :=
  ⟨pReb, ⟨.loc 1, .loc 2, pure_sep_iff.mpr ⟨rfl, _, _, comp_pcb, pImm_shape 1, pImm_shape 2⟩⟩⟩

theorem pStratumLe : StratumLe pW₁ pβ := fun _ hβ' =>
  ResU.inStratum_single _ (lt_trans hβ' pβ_lt_pα)

theorem pW₂_0 : pW₂.get 0 = some pψ := nxRes3_a _ _ _
theorem pW₂_1 : pW₂.get 1 = some pImm := nxRes3_b _ _ _ (by decide)
theorem pW₂_2 : pW₂.get 2 = some pImm := nxRes3_c _ _ _ (by decide) (by decide)
theorem pW₂_ne {l : BoCa.Loc} (h0 : l ≠ 0) (h1 : l ≠ 1) (h2 : l ≠ 2) : pW₂.get l = none :=
  nxRes3_ne _ _ _ h0 h1 h2

theorem comp_pW₁_pcb : ResU.CompS pW₁ pcb pW₂ := by
  refine nxCompS_disjoint (fun l => ?_) (fun l => ?_)
  · by_cases e0 : l = 0
    · subst e0; exact Or.inr (pcb_ne (by decide) (by decide))
    · exact Or.inl (ResU.single_get_ne _ e0)
  · by_cases e0 : l = 0
    · subst e0
      show _ = ((ResU.single 0 pψ).get 0).or _
      rw [pW₂_0, ResU.single_get_self]; rfl
    · show _ = ((ResU.single 0 pψ).get l).or _
      rw [ResU.single_get_ne _ e0]
      by_cases e1 : l = 1
      · subst e1; rw [pW₂_1, pcb_1]; rfl
      · by_cases e2 : l = 2
        · subst e2; rw [pW₂_2, pcb_2]; rfl
        · rw [pW₂_ne e0 e1 e2, pcb_ne e1 e2]; rfl

/-- `ag(pcb) = pcb`: two `imm` cells over nothing. -/
theorem pcb_agW : AgW pcb pcb := by
  have h1 : AgW (ResU.single 1 pImm) (ResU.single 1 pImm) :=
    AgW.single_imm ⟨PMap.empty, PMap.empty, agW_empty, exW_empty, ResU.comp_empty_left _⟩
      (ResU.comp_empty_right _)
  have h2 : AgW (ResU.single 2 pImm) (ResU.single 2 pImm) :=
    AgW.single_imm ⟨PMap.empty, PMap.empty, agW_empty, exW_empty, ResU.comp_empty_left _⟩
      (ResU.comp_empty_right _)
  exact (AgW.split comp_pcb).mpr ⟨_, _, h1, h2, comp_pcb'⟩

theorem pσ₁_pcb : ResU.CompR pσ₁ pcb pW₂ := by
  refine ⟨fun l ψ₁ ψ₂ e₁ e₂ => ?_, fun l => ?_⟩
  · by_cases e1 : l = 1
    · subst e1; rw [pσ₁_1] at e₁; rw [pcb_1] at e₂; cases e₁; cases e₂
      exact ⟨_, CellU.CompR.ownImm _ _ _ _⟩
    · by_cases e2 : l = 2
      · subst e2; rw [pσ₁_2] at e₁; rw [pcb_2] at e₂; cases e₁; cases e₂
        exact ⟨_, CellU.CompR.ownImm _ _ _ _⟩
      · rw [pcb_ne e1 e2] at e₂; cases e₂
  · by_cases e0 : l = 0
    · subst e0; rw [pσ₁_0, pcb_ne (by decide) (by decide), pW₂_0]; rfl
    · by_cases e1 : l = 1
      · subst e1; rw [pσ₁_1, pcb_1, pW₂_1]; exact ⟨_, rfl, CellU.CompR.ownImm _ _ _ _⟩
      · by_cases e2 : l = 2
        · subst e2; rw [pσ₁_2, pcb_2, pW₂_2]; exact ⟨_, rfl, CellU.CompR.ownImm _ _ _ _⟩
        · rw [pσ₁_ne e0 e1 e2, pcb_ne e1 e2, pW₂_ne e0 e1 e2]; rfl

/-- **The world after the reborrow is valid**: `ex = ∅`, and `ag` is the world itself, each
reborrowed cell absorbing the frozen `own` cell under the frame's cell (`○`'s `own`/`imm`
clause). -/
theorem pW₂_valid : ResU.Valid pW₂ := by
  refine ⟨pW₂, PMap.empty, pW₂, ExW.empty_of_all_imm (fun l ψ h => ?_), ?_,
    ResU.comp_empty_left _⟩
  · by_cases e0 : l = 0
    · subst e0; rw [pW₂_0] at h; cases h; exact pψ_kind
    · by_cases e1 : l = 1
      · subst e1; rw [pW₂_1] at h; cases h; rfl
      · by_cases e2 : l = 2
        · subst e2; rw [pW₂_2] at h; cases h; rfl
        · rw [pW₂_ne e0 e1 e2] at h; cases h
  · exact (AgW.split comp_pW₁_pcb).mpr ⟨pσ₁, pcb, AgW.single_imm pR_flatR comp_pψ_pR, pcb_agW,
      pσ₁_pcb⟩

theorem pW₁_get0 : pW₁.get pRec.le = some (CellU.immOf (LSet.singleton pα) pRec.v pRec.R
    (pR_strat _)) := ResU.single_get_self _ _

/-- **The reborrow is a typed-world step** (`TW.reb` at `pRec`). -/
theorem pW₂_tw : TW pW₂ [pRec] (rsOf pls) :=
  TW.reb pRec 1 pW₁_tw (List.mem_singleton_self _) pW₁_get0 (pairTy_closed 1) pReb pPairReb.2
    pStratumLe comp_pW₁_pcb pW₂_valid

theorem pW₂_tagged : Tagged pW₂ [pRec] pls :=
  tagged_reb pW₁_tw (List.mem_singleton_self _) pW₁_get0 pReb pStratumLe comp_pW₁_pcb pW₁_tagged

/-! ### Link (d) and the gate -/

/-- **Link (d) at every configuration of the pair's shape**: one entry named `'0`, a record over
`Ref 1 ⊗ Ref 1` owning two distinct places the stack does not lend. At every reading the clause of
`U (pairCbUC x B)` offers, the reborrow at the reading's lifetime holds `imm` cells exactly there
at both places (`pairRebCells`). At an instance below the bound, at the instantiated reading, the
lifetime is below the instantiated lend (`pairBoundBelow`), and the table's first conjunct fails;
at an own push, `OwnOKI` gives the pushed stack's shape, and `loadGuardFails2` applies
(`pairCallbackGuardFails`). -/
theorem pairGuardRejectsU_of {c : Cfg} {e : LEnt} {α : Life} {r : FrameRec} {l₁ l₂ : BoCa.Loc}
    {δ : LSub} {x : LifeVar} {B : VTy} (hσ : c.σ = [e]) (hαs : c.αs = [α]) (hx : e.x = 0)
    (hT : r.T = pairTy) (hv : r.v = .pair (.loc l₁) (.loc l₂))
    (h₁ : r.R.get l₁ = some (CellU.ownOf .unit)) (h₂ : r.R.get l₂ = some (CellU.ownOf .unit))
    (hne : l₁ ≠ l₂) (hn₁ : l₁ ∉ c.σ.map LEnt.l) (hn₂ : l₂ ∉ c.σ.map LEnt.l) :
    PairGuardRejectsU c δ r x B := by
  rintro ρk δ' σ' αs' β cb ρ ⟨ι, -, -, hcase⟩ ⟨hreb, hsh⟩ hc
  rw [hT, hv] at hsh
  obtain ⟨⟨χ₁, k₁, e₁⟩, ⟨χ₂, k₂, e₂⟩⟩ := pairRebCells r.R cb β l₁ l₂ x r.δ h₁ h₂ hreb hsh
  have hg := pairCallbackGuardFails c.σ (ι.life c.αs) β cb ρk ρ l₁ l₂ hne hn₁ hn₂
    ⟨_, χ₁, k₁, e₁⟩ ⟨_, χ₂, k₂, e₂⟩ hc
  rcases hcase with ⟨rfl, rfl, hlt⟩ | ⟨en, hpush, rfl, rfl⟩
  · rw [hσ, hαs] at hlt
    have hβ : β < ι.life1 α := pairBoundBelow (ι.sub δ) e (ι.life1 α) β hx hlt
    refine hg.1 (ι.life1 α) ?_ hβ
    rw [hαs]; rfl
  · obtain ⟨x', c', C', -, -, -, hok, -, -⟩ := hpush
    have hvar := hok.var
    refine hg.2 en ⟨?_, hok.chain, ?_⟩
    · rw [hσ, hαs]; rfl
    · rw [hσ] at hvar ⊢
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hvar ⊢
      exact List.nodup_cons.mpr ⟨by simpa using hvar, List.nodup_singleton _⟩

theorem empty_not_deepAt (l : BoCa.Loc) (ψ : CellU BoCa.Loc Val) : ¬ DeepAt (PMap.empty : WRes) l ψ := by
  intro h
  cases h with
  | top e => exact absurd e (by simp)
  | wit e _ => exact absurd e (by simp)

/-- **`WithloadUPairGapReal`: the two-cell gap is real at `withload`'s unwinding typing, at the
configuration `pc`.** `pc` arises (a `TW` history and a 6.64 lend), its view arises, and the
judgement's index holds there with the view as the context. The program is typed at `withloadU`'s
type. One own push at the index has a closed payload type, and [TR] 6.150's step `TW.reb`
reborrows the record's payload at its lifetime into a tagged typed world. At every reading the
callback's clause offers, the reborrow at the reading's lifetime fails the guard. -/
theorem withloadUPairGapReal : WithloadUPairGapReal (ℍ := ℍ) :=
  ⟨pc, pE, pα, pψ, PMap.empty, pRec, 1, 2, ⟨[]⟩, .unit, pCbE, 1, pEn, pβ, PMap.empty, pcb, pW₂,
    pairCfg, pairProgU_typed, pOwnPush _ (empty_not_deepAt 3) (ResU.inStratum_empty _),
    fun y h => h, pairTy_closed 1, pPairReb, pStratumLe, comp_pW₁_pcb, pW₂_tw, pW₂_tagged,
    pairGuardRejectsU_of rfl rfl rfl rfl rfl pR_1 pR_2 (by decide) (by simp [pc, pE])
      (by simp [pc, pE])⟩

end ProbeD1

end

import ProbeD1.BinderRows

/-!
# ProbeD1 — the arising check of `k`: PlaceViews at the world (`BINDER.md` §2.5, §2.7)

`PVArises`: `PlaceViewsW` holds at the world of every configuration of the revised arising set
`ArisesI`. With `PVLocal` it gives `KNotInArises`: no configuration of `ArisesI` has `k`'s stack,
lifetimes and local part. That is a fact in the proving direction. It says that the refutation at
`k` cannot pass DESIGN §11, not that `k` does not arise: `ArisesI` is not shown to
over-approximate what arises.

* **`↭` keeps PlaceViews at the world** (`pvwUpd`): its `mut` clause keeps a `mut` cell's lifetime
  and stored invariant at the flattening, its `imm` clause keeps an `imm` cell.
* **A run** (`pvwRun`): [TR] 6.48 (`updV_frame`) carries the run's `↭` on the local part to the
  world, the frame `ρ_f`, with the garbage joining it.
* **A lend's start** (`pvwLendMut`, `pvwLendImm`): 6.65's and 6.64's openings. At the lent place the
  folded cell is the world's flattening there (`flatAt_fold_mut_self`, `flatAt_fold_imm_self`), at
  its exact lifetime, its invariant or value the entry's. Elsewhere the flattening is unchanged
  (`flatAt_fold_mut_ne`, `flatAt_fold_imm_ne`): a `mut` fold keeps the walks off the place, and an
  `imm` fold moves the payload's exclusive cells under the `imm` cell into the aliasable walk, where
  validity leaves them the only contribution.
* **The arising set** (`arisesInv`, `pvArises`) by induction on `ArisesI`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS)

/-! ### `k` under W -/

/-- **`k`'s slot fails W's `Mut` leaf**: `CohS` asks the payload `1` to be the entry's `Unk` up to
the reading. -/
theorem kSlotNotW : KSlotNotW := by
  intro δ h
  have hi : innerAt kσ [kα] 0 = some (kEnt, kα) := by simp [innerAt]
  exact (h 0 kEnt kα rfl hi).1.2

/-- **`k`'s entry is not the own lend at `kC`**: its payload `Unk` is not the view's `1`. -/
theorem kNotViewAt : KNotViewAt := by
  intro h
  cases h.2.2

/-! ### Locations of a composite -/

theorem optComp_det {C : CellU BoCa.Loc Val → CellU BoCa.Loc Val → CellU BoCa.Loc Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ ψ', C ψ₁ ψ₂ ψ → C ψ₁ ψ₂ ψ' → ψ = ψ') :
    ∀ {o₁ o₂ o o' : Option (CellU BoCa.Loc Val)}, OptComp C o₁ o₂ o → OptComp C o₁ o₂ o' → o = o'
  | none, none, _, _, h, h' => h.trans h'.symm
  | some _, none, _, _, h, h' => h.trans h'.symm
  | none, some _, _, _, h, h' => h.trans h'.symm
  | some _, some _, _, _, ⟨_, h, hc⟩, ⟨_, h', hc'⟩ => by rw [h, h', hC _ _ _ _ hc hc']

/-- A composite's cell at a location is determined by its operands' cells there. -/
theorem comp_get_det {R : CellU BoCa.Loc Val → CellU BoCa.Loc Val → Prop}
    {C : CellU BoCa.Loc Val → CellU BoCa.Loc Val → CellU BoCa.Loc Val → Prop}
    (hC : ∀ ψ₁ ψ₂ ψ ψ', C ψ₁ ψ₂ ψ → C ψ₁ ψ₂ ψ' → ψ = ψ') {x y z x' y' z' : WRes}
    (h : ResU.Comp R C x y z) (h' : ResU.Comp R C x' y' z') {l : BoCa.Loc}
    (hx : x.get l = x'.get l) (hy : y.get l = y'.get l) : z.get l = z'.get l := by
  have h1 := h.2 l
  rw [hx, hy] at h1
  exact optComp_det hC h1 (h'.2 l)

theorem comp_get_of_none_left {R : CellU BoCa.Loc Val → CellU BoCa.Loc Val → Prop}
    {C : CellU BoCa.Loc Val → CellU BoCa.Loc Val → CellU BoCa.Loc Val → Prop}
    {x y z : WRes} (h : ResU.Comp R C x y z) {l : BoCa.Loc} (hx : x.get l = none) :
    z.get l = y.get l := by
  have h1 := h.2 l
  rw [hx] at h1
  cases e : y.get l with
  | none => rw [e] at h1; exact h1
  | some ψ => rw [e] at h1; exact h1

theorem comp_get_of_none_right {R : CellU BoCa.Loc Val → CellU BoCa.Loc Val → Prop}
    {C : CellU BoCa.Loc Val → CellU BoCa.Loc Val → CellU BoCa.Loc Val → Prop}
    {x y z : WRes} (h : ResU.Comp R C x y z) {l : BoCa.Loc} (hy : y.get l = none) :
    z.get l = x.get l := by
  have h1 := h.2 l
  rw [hy] at h1
  cases e : x.get l with
  | none => rw [e] at h1; exact h1
  | some ψ => rw [e] at h1; exact h1

theorem none_of_comp_none_left {R : CellU BoCa.Loc Val → CellU BoCa.Loc Val → Prop}
    {C : CellU BoCa.Loc Val → CellU BoCa.Loc Val → CellU BoCa.Loc Val → Prop}
    {x y z : WRes} (h : ResU.Comp R C x y z) {l : BoCa.Loc} (hz : z.get l = none) :
    x.get l = none := by
  cases e : x.get l with
  | none => rfl
  | some ψ =>
      obtain ⟨ζ, hζ⟩ := comp_some h e
      rw [hz] at hζ; exact absurd hζ (by simp)

theorem none_of_comp_none_right {R : CellU BoCa.Loc Val → CellU BoCa.Loc Val → Prop}
    {C : CellU BoCa.Loc Val → CellU BoCa.Loc Val → CellU BoCa.Loc Val → Prop}
    {x y z : WRes} (h : ResU.Comp R C x y z) {l : BoCa.Loc} (hz : z.get l = none) :
    y.get l = none := by
  cases e : y.get l with
  | none => rfl
  | some ψ =>
      obtain ⟨ζ, hζ⟩ := comp_some_r h e
      rw [hz] at hζ; exact absurd hζ (by simp)

theorem compS_det : ∀ ψ₁ ψ₂ ψ ψ' : CellU BoCa.Loc Val, CellU.CompS ψ₁ ψ₂ ψ → CellU.CompS ψ₁ ψ₂ ψ' →
    ψ = ψ' := fun _ _ _ _ h h' => CellU.CompS.functional h h'

theorem compR_det : ∀ ψ₁ ψ₂ ψ ψ' : CellU BoCa.Loc Val, CellU.CompR ψ₁ ψ₂ ψ → CellU.CompR ψ₁ ψ₂ ψ' →
    ψ = ψ' := fun _ _ _ _ h h' => CellU.CompR.functional h h'

/-- The exclusive walk of a single `imm` cell has nothing off its place. -/
theorem ex_single_imm_ne {ℓ : BoCa.Loc} {s : LSet} {v : Val} {χ : WRes}
    {h : χ.InStratum s.join} {e : WRes} (he : ExS (ResU.single ℓ (CellU.immOf s v χ h)) e)
    {l : BoCa.Loc} (hl : l ≠ ℓ) : e.get l = none := by
  cases eg : e.get l with
  | none => rfl
  | some φ =>
      exfalso
      cases ExS.exAt he eg with
      | top e' => exact hl (ResU.single_get_eq_some e').1
      | wit em hk _ =>
          obtain ⟨-, rfl⟩ := ResU.single_get_eq_some em
          exact absurd hk (by simp)

/-! ### The flattening at a lend's fold -/

/-- **6.65's fold, at the place**: the world's flattening there is the folded `mut` cell. -/
theorem flatAt_fold_mut_self {ℓ : BoCa.Loc} {b : Life} {v : Val} {χ : WRes}
    {hstr : χ.InStratum b} {P : Val → SPropS BoCa.Loc Val b} {hw : P v ⟨χ, hstr⟩} {Z W' : WRes}
    (hW' : ResU.CompS (ResU.single ℓ (CellU.mutOf b v χ hstr P hw)) Z W')
    {ψ : CellU BoCa.Loc Val} (h : W'.FlatAt ℓ ψ) : ψ = CellU.mutOf b v χ hstr P hw := by
  obtain ⟨σ', ⟨e, a, he, ha, hc⟩, hg⟩ := h
  obtain ⟨e₁, e₂, he₁, he₂, hec⟩ := (ExS.split hW').mp he
  obtain ⟨e₀, he₀, hc₀⟩ := ExW.single_mut_inv he₁
  have hk : (CellU.mutOf b v χ hstr P hw).kind ≠ Kind.imm := by simp
  have g₁ := (ResU.CompS.get_left_of_ne_imm hc₀ (ResU.single_get_self _ _) hk).2
  have g₂ := (ResU.CompS.get_left_of_ne_imm hec g₁ hk).2
  have g₃ := (ResU.CompS.get_left_of_ne_imm hc g₂ hk).2
  rw [g₃] at hg
  exact (Option.some.inj hg).symm

/-- **6.65's fold, off the place**: the flattening is unchanged. -/
theorem flatAt_fold_mut_ne {ℓ : BoCa.Loc} {v : Val} {b : Life} {ρp : WRes}
    {hstr : ρp.InStratum b} {P : Val → SPropS BoCa.Loc Val b} {hw : P v ⟨ρp, hstr⟩}
    {X Z W W' : WRes} (hX : ResU.CompS (ResU.single ℓ (CellU.ownOf v)) ρp X)
    (hW : ResU.CompS X Z W)
    (hW' : ResU.CompS (ResU.single ℓ (CellU.mutOf b v ρp hstr P hw)) Z W')
    (hv : ResU.Valid W) {l : BoCa.Loc} (hl : l ≠ ℓ) {ψ : CellU BoCa.Loc Val}
    (h : W'.FlatAt l ψ) : W.FlatAt l ψ := by
  obtain ⟨σ', ⟨e', a', he', ha', hc'⟩, hg⟩ := h
  obtain ⟨σ, e, a, he, ha, hc⟩ := hv
  refine ⟨σ, ⟨e, a, he, ha, hc⟩, ?_⟩
  rw [← hg]
  have haa : a = a' := AgW.functional ha ((mut_fold_ag hX hW hW' a').mpr ha')
  obtain ⟨eX, eZ, heX, heZ, heXZ⟩ := (ExS.split hW).mp he
  obtain ⟨eo, ep, heo, hep, heop⟩ := (ExS.split hX).mp heX
  obtain ⟨em, eZ', hem, heZ', hemZ⟩ := (ExS.split hW').mp he'
  obtain ⟨ep', hep', hmp⟩ := ExW.single_mut_inv hem
  rw [ExS.functional hep' hep] at hmp
  rw [ExS.functional heZ' heZ] at hemZ
  rw [ExS.functional heo (ExW.single_own ℓ v)] at heop
  have g₁ : eX.get l = ep.get l := comp_get_of_none_left heop (ResU.single_get_ne _ hl)
  have g₂ : em.get l = ep.get l := comp_get_of_none_left hmp (ResU.single_get_ne _ hl)
  have g₃ : e.get l = e'.get l := comp_get_det compS_det heXZ hemZ (g₁.trans g₂.symm) rfl
  exact comp_get_det compS_det hc hc' g₃ (by rw [haa])

/-- **6.64's fold, at the place**: the world's flattening there is the folded `imm` cell, the
payload's walks having nothing at the place (validity before the fold). -/
theorem flatAt_fold_imm_self {ℓ : BoCa.Loc} {v : Val} {α : Life} {R X Z W W' : WRes}
    {h : R.InStratum (LSet.singleton α).join}
    (hX : ResU.CompS (ResU.single ℓ (CellU.ownOf v)) R X) (hW : ResU.CompS X Z W)
    (hW' : ResU.CompS (ResU.single ℓ (CellU.immOf (LSet.singleton α) v R h)) Z W')
    (hv : ResU.Valid W) {ψ : CellU BoCa.Loc Val} (hψ : W'.FlatAt ℓ ψ) :
    ψ = CellU.immOf (LSet.singleton α) v R h := by
  obtain ⟨σ', ⟨e', a', he', ha', hc'⟩, hg⟩ := hψ
  obtain ⟨σ, e, a, he, ha, hc⟩ := hv
  obtain ⟨eX, eZ, heX, heZ, heXZ⟩ := (ExS.split hW).mp he
  obtain ⟨eo, eR, heo, heR, heoR⟩ := (ExS.split hX).mp heX
  rw [ExS.functional heo (ExW.single_own ℓ v)] at heoR
  obtain ⟨aX, aZ, haX, haZ, haXZ⟩ := (AgW.split hW).mp ha
  have haR : AgW R aX := (own_cell_ag hX aX).mp haX
  have hko : (CellU.ownOf v : CellU BoCa.Loc Val).kind ≠ Kind.imm := by simp
  obtain ⟨gR, gX⟩ := ResU.CompS.get_left_of_ne_imm heoR (ResU.single_get_self _ _) hko
  obtain ⟨gZ, ge⟩ := ResU.CompS.get_left_of_ne_imm heXZ gX hko
  obtain ⟨ga, -⟩ := ResU.CompS.get_left_of_ne_imm hc ge hko
  have gaX : aX.get ℓ = none := none_of_comp_none_left haXZ ga
  have gaZ : aZ.get ℓ = none := none_of_comp_none_right haXZ ga
  obtain ⟨ei, eZ', hei, heZ', heiZ⟩ := (ExS.split hW').mp he'
  rw [ExS.functional heZ' heZ] at heiZ
  obtain ⟨ai, aZ', hai, haZ', haiZ⟩ := (AgW.split hW').mp ha'
  rw [AgW.functional haZ' haZ] at haiZ
  obtain ⟨eR', aR', p, heR', haR', hp, hip⟩ := AgW.single_imm_inv hai
  rw [ExR.functional heR' (ExS.toExR heR), AgW.functional haR' haR] at hp
  have gi : ei.get ℓ = none := by
    cases eg : ei.get ℓ with
    | none => rfl
    | some φ =>
        exfalso
        have hφ := ExS.immFree hei ℓ φ eg
        cases ExS.exAt hei eg with
        | top e₀ =>
            obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e₀
            exact hφ (by simp)
        | wit em hk _ =>
            obtain ⟨-, rfl⟩ := ResU.single_get_eq_some em
            exact absurd hk (by simp)
  have gp : p.get ℓ = none := by rw [comp_get_of_none_right hp gaX]; exact gR
  have gai : ai.get ℓ = some (CellU.immOf (LSet.singleton α) v R h) := by
    rw [comp_get_of_none_right hip gp]; exact ResU.single_get_self _ _
  have ga' : a'.get ℓ = some (CellU.immOf (LSet.singleton α) v R h) := by
    rw [comp_get_of_none_right haiZ gaZ]; exact gai
  have ge' : e'.get ℓ = none := by rw [comp_get_of_none_left heiZ gi]; exact gZ
  rw [comp_get_of_none_left hc' ge', ga'] at hg
  exact (Option.some.inj hg).symm

/-- **6.64's fold, off the place**: the flattening is unchanged. A payload cell in the exclusive
walk moves under the `imm` cell into the aliasable walk, where validity before the fold leaves it
the only contribution; every other location reads the same walks. -/
theorem flatAt_fold_imm_ne {ℓ : BoCa.Loc} {v : Val} {α : Life} {R X Z W W' : WRes}
    {h : R.InStratum (LSet.singleton α).join}
    (hX : ResU.CompS (ResU.single ℓ (CellU.ownOf v)) R X) (hW : ResU.CompS X Z W)
    (hW' : ResU.CompS (ResU.single ℓ (CellU.immOf (LSet.singleton α) v R h)) Z W')
    (hv : ResU.Valid W) {l : BoCa.Loc} (hl : l ≠ ℓ) {ψ : CellU BoCa.Loc Val}
    (hψ : W'.FlatAt l ψ) : W.FlatAt l ψ := by
  obtain ⟨σ', ⟨e', a', he', ha', hc'⟩, hg⟩ := hψ
  obtain ⟨σ, e, a, he, ha, hc⟩ := hv
  refine ⟨σ, ⟨e, a, he, ha, hc⟩, ?_⟩
  rw [← hg]
  obtain ⟨eX, eZ, heX, heZ, heXZ⟩ := (ExS.split hW).mp he
  obtain ⟨eo, eR, heo, heR, heoR⟩ := (ExS.split hX).mp heX
  rw [ExS.functional heo (ExW.single_own ℓ v)] at heoR
  obtain ⟨aX, aZ, haX, haZ, haXZ⟩ := (AgW.split hW).mp ha
  have haR : AgW R aX := (own_cell_ag hX aX).mp haX
  obtain ⟨ei, eZ', hei, heZ', heiZ⟩ := (ExS.split hW').mp he'
  rw [ExS.functional heZ' heZ] at heiZ
  obtain ⟨ai, aZ', hai, haZ', haiZ⟩ := (AgW.split hW').mp ha'
  rw [AgW.functional haZ' haZ] at haiZ
  obtain ⟨eR', aR', p, heR', haR', hp, hip⟩ := AgW.single_imm_inv hai
  rw [ExR.functional heR' (ExS.toExR heR), AgW.functional haR' haR] at hp
  have gX : eX.get l = eR.get l := comp_get_of_none_left heoR (ResU.single_get_ne _ hl)
  have ge' : e'.get l = eZ.get l := comp_get_of_none_left heiZ (ex_single_imm_ne hei hl)
  have gai : ai.get l = p.get l := comp_get_of_none_left hip (ResU.single_get_ne _ hl)
  cases hR : eR.get l with
  | none =>
      have ge : e.get l = eZ.get l := comp_get_of_none_left heXZ (gX.trans hR)
      have gp : p.get l = aX.get l := comp_get_of_none_left hp hR
      have ga : a.get l = a'.get l := comp_get_det compR_det haXZ haiZ (gai.trans gp).symm rfl
      exact comp_get_det compS_det hc hc' (ge.trans ge'.symm) ga
  | some φ =>
      have hφ : φ.kind ≠ Kind.imm := ExS.immFree heR l φ hR
      obtain ⟨gZ, ge⟩ := ResU.CompS.get_left_of_ne_imm heXZ (gX.trans hR) hφ
      obtain ⟨ga, gσ⟩ := ResU.CompS.get_left_of_ne_imm hc ge hφ
      have gaX : aX.get l = none := none_of_comp_none_left haXZ ga
      have gaZ : aZ.get l = none := none_of_comp_none_right haXZ ga
      have gp : p.get l = some φ := by rw [comp_get_of_none_right hp gaX]; exact hR
      have ga' : a'.get l = some φ := by rw [comp_get_of_none_right haiZ gaZ, gai, gp]
      rw [gσ, comp_get_of_none_left hc' (ge'.trans gZ), ga']

/-! ### PlaceViews at the world, transition by transition -/

theorem pvwNil : PVWNil := fun _ _ _ _ hi => by simp [innerAt] at hi

theorem pvwHide : PVWHide := by
  intro N σ αs W hW l e α hi ψ hψ
  rw [innerAt_hideS] at hi
  obtain ⟨⟨e₀, α₀⟩, hi₀, he⟩ := Option.map_eq_some_iff.mp hi
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact hW l e₀ α₀ hi₀ ψ hψ

/-- **`↭` keeps PlaceViews at the world** ([TR] p. 5, row 18): its `mut` clause, read backwards,
gives a `mut` cell of the old flattening at the same place, lifetime and stored invariant, which is
all `mutPred` reads; its `imm` clause gives the same `imm` cell. -/
theorem pvwUpd : PVWUpd := by
  intro σ αs W W' hW hU l e α hi ψ hψ
  obtain ⟨⟨hUI, hUM⟩, -, -⟩ := hU
  rcases CellU.rep ψ with ⟨v, rfl⟩ | ⟨s, v, χ, hs, rfl⟩ | ⟨b, v, χ, hs, P, hw, rfl⟩
  · exact ⟨fun _ hk => absurd hk (by simp), fun _ _ hk => absurd hk (by simp)⟩
  · exact hW l e α hi _ ((hUI l s v χ hs).mpr hψ)
  · obtain ⟨v', χ', hs', hw', hψ'⟩ := (hUM l b P).mpr ⟨v, χ, hs, hw, hψ⟩
    obtain ⟨hm, -⟩ := hW l e α hi _ hψ'
    refine ⟨fun hk _ => ?_, fun _ _ hk' => absurd hk' (by simp)⟩
    obtain ⟨hat, δ', ls₀, hP⟩ := hm hk (by simp)
    refine ⟨hat, δ', ls₀, ?_⟩
    rw [mutPred_mutOf] at hP ⊢
    exact hP

/-- **A run keeps PlaceViews at the world**: [TR] 6.48 (`updV_frame`) at the frame `ρ_f`, the
local part and the run's update `π = ρ' ● ρ_p`, the garbage joining the frame; then `pvwUpd`. -/
theorem pvwRun : PVWRun (ℍ := ℍ) := by
  intro c c' e t hh hc hW hR
  obtain ⟨hσ, hαs, A, k, k', μ, μ', ρp, fρ', π, -, hc₁, -, -, hc₂, hlow', -, hπ, hU, -⟩ := hR
  rw [hσ, hαs]
  obtain ⟨bc, hbc, hbc'⟩ := compS_reassoc hc₁ hc₂
  rw [ResU.CompS.functional hbc hπ] at hbc'
  have hv' : ResU.Valid c'.fρ := by
    obtain ⟨σ, hf, -⟩ := hlow'
    exact ⟨σ, hf⟩
  exact pvwUpd c.σ c.αs c.fρ c'.fρ hW (updV_frame hc hbc' hh ⟨hbc'.1, c'.fρ, hbc', hv'⟩ hU)

/-- **A 6.65 lend opens with PlaceViews at its place** (`lendMut_placeView`, at the world): the
folded cell is at exactly the lend's lifetime and stores the entry's view; elsewhere the
flattening is unchanged. -/
theorem pvwLendMut : PVWLendMut := by
  intro c c' e hv hW hL
  obtain ⟨hk, hσ, -, -, -, -, -, α, v, ρp, X, ρc, Z, hstr, P, hw, hαs, -, -, hX, -, hW0, hW', -,
    -, -, -, -, δ, hview⟩ := hL
  rw [hσ, hαs]
  intro l e' α' hi ψ hψ
  rw [innerAt_cons] at hi
  by_cases hle : e.l = l
  · rw [if_pos hle] at hi
    obtain ⟨rfl, rfl⟩ : e = e' ∧ α = α' := by simpa using hi
    subst hle
    obtain rfl := flatAt_fold_mut_self hW' hψ
    refine ⟨fun _ _ => ⟨rfl, ?_⟩, fun u hku _ => absurd (hk.symm.trans hku) (by simp)⟩
    obtain ⟨el, ex, eT, ek, ecr⟩ := e
    simp only at hk
    subst hk
    obtain ⟨b, u, χ, hχ, Q, hwQ, ls₀, -, hρ, hQ, -, -⟩ := hview
    have hcell := congrArg (fun r => PMap.get r el) hρ
    simp only [ResU.single_get_self, Option.some.injEq] at hcell
    refine ⟨δ, ls₀, ?_⟩
    rw [hcell, mutPred_mutOf, hQ]
  · rw [if_neg hle] at hi
    exact hW l e' α' hi ψ (flatAt_fold_mut_ne hX hW0 hW' hv (Ne.symm hle) hψ)

/-- **A 6.64 lend opens with PlaceViews at its place**: the folded `imm` cell is at exactly the
lend's lifetime and holds the entry's value; elsewhere the flattening is unchanged. -/
theorem pvwLendImm : PVWLendImm := by
  intro c c' e hv hW hL
  obtain ⟨hσ, -, -, -, α, v, R, X, ρc, Z, δ, h, ds, hk, hαs, -, -, -, hX, -, hW0, -, hW', -⟩ := hL
  rw [hσ, hαs]
  intro l e' α' hi ψ hψ
  rw [innerAt_cons] at hi
  by_cases hle : e.l = l
  · rw [if_pos hle] at hi
    obtain ⟨rfl, rfl⟩ : e = e' ∧ α = α' := by simpa using hi
    subst hle
    obtain rfl := flatAt_fold_imm_self hX hW0 hW' hv hψ
    refine ⟨fun hkm _ => absurd (hk.symm.trans hkm) (by simp), fun u hku _ => ⟨rfl, ?_⟩⟩
    exact LKind.imm.inj (hk.symm.trans hku)
  · rw [if_neg hle] at hi
    exact hW l e' α' hi ψ (flatAt_fold_imm_ne hX hW0 hW' hv (Ne.symm hle) hψ)

/-- **The local part reads it**: a top-level `mut` cell of a part of a valid world is in the
world's exclusive walk, and no other contribution meets it. -/
theorem pvLocal : PVLocal := by
  intro fρ ρf ρ hv hc l ψ hg hk
  obtain ⟨σ, e, a, he, ha, hσ⟩ := hv
  have hk' : ψ.kind ≠ Kind.imm := by rw [hk]; simp
  have hg' : fρ.get l = some ψ :=
    (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hc) hg hk').2
  have he' : e.get l = some ψ := ExS.get_of_ne_imm he hg' hk'
  exact ⟨σ, ⟨e, a, he, ha, hσ⟩, (ResU.CompS.get_left_of_ne_imm hσ he' hk').2⟩

/-! ### The arising set -/

/-- **`ArisesInv`**: each transition of `ArisesI` keeps the frame, the local part and validity. -/
theorem arisesInv : ArisesInv (ℍ := ℍ) := by
  intro c h
  refine ArisesI.rec
    (motive_1 := fun c _ => ResU.Hash c.ρf c.ρ ∧ ResU.CompS c.ρf c.ρ c.fρ ∧ ResU.Valid c.fρ)
    (motive_2 := fun _ _ _ _ => True) (motive_3 := fun _ _ _ _ => True)
    ?nil ?run ?part ?lendMut ?lendImm ?hide (fun _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ => trivial) (fun _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ => trivial) h
  case nil =>
    intro fρ ρf ρ ps ls htw _ hh hc
    exact ⟨hh, hc, TW.valid htw⟩
  case run =>
    intro c c' Δ Γ e₀ j γ t _ _ _ hR _ _
    obtain ⟨-, -, A, k, k', μ, μ', ρp, fρ', π, -, hc₁, -, -, hc₂, hlow', -, -, -, -, -, -, -, -,
      hfr⟩ := hR
    obtain ⟨bc, hbc, hbc'⟩ := compS_reassoc hc₁ hc₂
    obtain ⟨ab, hab, hab'⟩ := compS_reassoc' (ResU.CompS.comm hbc) hbc'
    rw [ResU.CompS.functional hab hfr] at hab'
    have hv' : ResU.Valid c'.fρ := by
      obtain ⟨σ, hf, -⟩ := hlow'
      exact ⟨σ, hf⟩
    exact ⟨⟨hab'.1, c'.fρ, hab', hv'⟩, hab', hv'⟩
  case part =>
    intro c ρ₁ ρ₂ ρf' _ h₁₂ hf' hh ih
    obtain ⟨-, hc, hv⟩ := ih
    obtain ⟨ab, hab, hab'⟩ := compS_reassoc' (ResU.CompS.comm h₁₂) hc
    rw [ResU.CompS.functional hab hf'] at hab'
    exact ⟨hh, hab', hv⟩
  case lendMut =>
    intro c c' e _ hL _
    obtain ⟨⟨-, -, -, -, -, -, -, α, v, ρp, X, ρc, Z, hstr, P, hw, -, -, -, -, -, -, -, hv', -,
      hh', hc', -⟩, -⟩ := hL
    exact ⟨hh', hc', hv'⟩
  case lendImm =>
    intro c c' e _ hL _
    obtain ⟨⟨-, -, -, -, α, v, R, X, ρc, Z, δ, h, ds, -, -, -, -, -, -, -, -, -, -, hv', -, -, -,
      -, hh', hc', -⟩, -⟩ := hL
    exact ⟨hh', hc', hv'⟩
  case hide =>
    intro c N _ ih
    exact ih

/-- **`PVArises`**: PlaceViews holds at the world of every configuration of the revised arising
set. -/
theorem pvArises : PVArises (ℍ := ℍ) := by
  intro c h
  refine ArisesI.rec (motive_1 := fun c _ => PlaceViewsW c.σ c.αs c.fρ)
    (motive_2 := fun _ _ _ _ => True) (motive_3 := fun _ _ _ _ => True)
    ?nil ?run ?part ?lendMut ?lendImm ?hide (fun _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ => trivial) (fun _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ => trivial) h
  case nil =>
    intro fρ ρf ρ ps ls _ _ _ _
    exact pvwNil _
  case run =>
    intro c c' Δ Γ e₀ j γ t hA _ _ hR ih _
    obtain ⟨hh, hc, -⟩ := arisesInv c hA
    exact pvwRun c c' _ t hh hc ih hR
  case part =>
    intro c ρ₁ ρ₂ ρf' _ _ _ _ ih
    exact ih
  case lendMut =>
    intro c c' e hA hL ih
    exact pvwLendMut c c' e (arisesInv c hA).2.2 ih hL.1
  case lendImm =>
    intro c c' e hA hL ih
    exact pvwLendImm c c' e (arisesInv c hA).2.2 ih hL.1
  case hide =>
    intro c N _ ih
    exact pvwHide N c.σ c.αs c.fρ ih

/-- **`KNotInArises`**: no configuration of the revised arising set has `k`'s stack, lifetimes and
local part. Its local cell would be the world's flattening at the lent place (`pvLocal`), which
PlaceViews makes the entry's view (`pvArises`): `𝒱⟦1⟧` is not `𝒱⟦Unk⟧` at `loc 0`. This is in
the proving direction: it does not say that `k` does not arise. -/
theorem kNotInArises : KNotInArises (ℍ := ℍ) := by
  intro c h hσ hαs hρ
  have hW := pvArises c h
  obtain ⟨-, hc, hv⟩ := arisesInv c h
  have hflat : c.fρ.FlatAt 0 kCell :=
    pvLocal c.fρ c.ρf c.ρ hv hc 0 kCell (by rw [hρ]; exact kρ_get) (by simp)
  rw [hσ, hαs] at hW
  obtain ⟨-, δ', ls₀, hP⟩ := (hW 0 kEnt kα (by simp [innerAt]) kCell hflat).1 rfl (by simp)
  rw [mutPred_mutOf] at hP
  have h₁ : ofS (GhostEnd.unitQ kα) (Val.loc 0) PMap.empty := by
    rw [hP]; exact ⟨rfl, trivial⟩
  obtain ⟨-, -, h₂⟩ := h₁
  exact loc_ne_unit h₂

/-! ### The stack's places at the arising set -/

theorem hideS_map_l' (N : UInt32 → Bool) (σ : LStack) : (hideS N σ).map LEnt.l = σ.map LEnt.l := by
  unfold hideS; rw [List.map_map]; rfl

/-- **The places of an arising stack are distinct**: each lend opens at a place new to the stack
(`LendMut`, `LendImm`), and no other transition changes the places. So `PVLUpdN` and `PVLRunsN`,
`PVLUpd` and `PVLRuns` at distinct places, hold at every stack `ArisesI` reaches. -/
theorem placesNodupArises : ∀ c : Cfg, ArisesI (ℍ := ℍ) c → (c.σ.map LEnt.l).Nodup := by
  intro c h
  refine ArisesI.rec (motive_1 := fun c _ => (c.σ.map LEnt.l).Nodup)
    (motive_2 := fun _ _ _ _ => True) (motive_3 := fun _ _ _ _ => True)
    ?nil ?run ?part ?lendMut ?lendImm ?hide (fun _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ => trivial) (fun _ => trivial) (fun _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ => trivial) h
  case nil =>
    intro fρ ρf ρ ps ls _ _ _ _
    exact List.nodup_nil
  case run =>
    intro c c' Δ Γ e₀ j γ t _ _ _ hR ih _
    rw [hR.1]; exact ih
  case part =>
    intro c ρ₁ ρ₂ ρf' _ _ _ _ ih
    exact ih
  case lendMut =>
    intro c c' e _ hL ih
    obtain ⟨⟨-, hσ, -, -, -, -, hel, -⟩, -⟩ := hL
    rw [hσ, List.map_cons]
    exact List.nodup_cons.mpr ⟨hel, ih⟩
  case lendImm =>
    intro c c' e _ hL ih
    obtain ⟨⟨hσ, -, -, hel, -⟩, -⟩ := hL
    rw [hσ, List.map_cons]
    exact List.nodup_cons.mpr ⟨hel, ih⟩
  case hide =>
    intro c N _ ih
    show ((hideS N c.σ).map LEnt.l).Nodup
    rw [hideS_map_l']; exact ih

/-- **`PVLUpd` at every stack `ArisesI` reaches**: `PVLUpdN` and `placesNodupArises`. -/
theorem pvlUpd_arises {c : Cfg} (hA : ArisesI (ℍ := ℍ) c) (s : LSub) (ls : List SRec)
    {ρ π : WRes} (hok : StackOK c.σ c.αs) (h : PlaceViewsL s c.σ c.αs ls ρ)
    (hu : ResU.UpdV ρ π) : PlaceViewsL s c.σ c.αs ls π :=
  pvlUpdN s c.σ c.αs ls ρ π hok (placesNodupArises c hA) h hu

end ProbeD1

end

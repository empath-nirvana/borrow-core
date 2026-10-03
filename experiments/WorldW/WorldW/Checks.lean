import WorldW.Coherence

/-!
# WorldW — definition checks (DESIGN §2)

**World: the W-draft.** These check our draft definitions, not OQ-9 (a) and not a printed lemma.

## F-CLOSE: the closure does not depend on the anti step's choice

* `closeE_anti_flat` (in `WorldW/Refold.lean`): one anti step changes `⦇·⦈` at its place only.
* `close_flat_agree`: two closures of one resource by one list have one flattening off the
  pending anti places, and `mut(β, v, _, P̂)` with the same `β`, `v`, `P̂` at them.
  **Corrected** from DESIGN §2 (correction 1, recorded there): the design's second conjunct
  claimed `mut` at the place of *every* anti entry of `τ`; a later 6.65 entry at the same place
  unfolds it again (the nested `withbor3` list `[mut ℓ α, anti ℓ α₀ α₀ …, mut ℓ α₀]`), and there
  both closures hold `own`. The corrected conjunct is at the anti entries no later 6.65 entry at
  their place follows. The design's first conjunct is `close_flat_agree_off_anti`.
* `close_upd_coherent`: two closures are `↭`-related. Proved after **correction 2** (recorded in
  DESIGN §2): `CloseE`'s 6.150 step now asks that the image is a reborrow image at the entry's
  lifetime (`ResU.Reb β σR χ`, the printed H16). Without it the image's cells may sit at lifetimes
  the pin does not cover, and the statement is false at a resource the design admits.
* `upd_choice_free`: conjunct (37) holds at one pair of closures iff at every pair.
* `pin_harmless`: where the lifetimes are in the order arising obligations have, the pin removes
  no split.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace WorldW
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- Each closing step's result is valid, a marker's is its input. -/
theorem closePre_valid : ∀ {τ τ₂ : List OEnt} {π π' : WRes}, ClosePre τ τ₂ π π' →
    ResU.Valid π → ResU.Valid π'
  | _, _, _, _, .nil _ _, hv => hv
  | _, _, _, _, @ClosePre.cons e _ _ _ _ _ hstep hrest, hv => by
      refine closePre_valid hrest ?_
      cases e with
      | imm r => obtain ⟨p, α⟩ := r; obtain ⟨_, _, _, _, _, hv'⟩ := hstep; exact hv'
      | «mut» l α T δ => obtain ⟨_, _, _, _, _, _, _, _, _, hv'⟩ := hstep; exact hv'
      | anti l α β T δ P => obtain ⟨_, _, _, _, _, _, _, _, _, _, hv'⟩ := hstep; exact hv'
      | reb _ _ _ _ _ _ _ => exact hstep.2.2.2
      | hnd _ _ => have e : _ = _ := hstep; rw [e]; exact hv

/-- **Two closures of one resource by one list.** Off the pending anti places their flattenings
agree; at a pending anti place both carry `mut(β, v, _, P̂)` with the entry's `β`, `P̂` and one
`v`. (DESIGN §2's `close_flat_agree`, corrected: see the module docstring.) -/
theorem close_flat_agree {τ : List OEnt} {π π₁ π₂ F₁ F₂ : WRes} :
    Close τ π π₁ → Close τ π π₂ → ResU.Flat π₁ F₁ → ResU.Flat π₂ F₂ →
    (∀ m, ¬ PendingAt τ m → F₁.get m = F₂.get m) ∧
    (∀ i (hi : i < τ.length) l α β T δ P, τ[i] = .anti l α β T δ P →
      (∀ e ∈ τ.drop (i + 1), e.isMutAt l = false) → ∃ v,
      (∃ χ h hw, F₁.get l = some (CellU.mutOf β v χ h P hw)) ∧
      (∃ χ h hw, F₂.get l = some (CellU.mutOf β v χ h P hw))) := by
  intro h₁ h₂ hF₁ hF₂
  obtain ⟨U, A₁, A₂, hr₁, hr₂, hs₁, hs₂⟩ :=
    close_pair h₁ h₂ (.nil π) (.nil π) rfl (fun _ h => absurd h List.not_mem_nil)
      (fun _ h => absurd h List.not_mem_nil)
  simp only [List.map_nil] at hs₁ hs₂
  have hvU : ResU.Valid U := refolds_valid_start hr₁ ⟨F₁, hF₁⟩
  obtain ⟨FU, hFU⟩ := hvU
  obtain ⟨hoff₁, hat₁⟩ := refolds_flat hr₁ ⟨FU, hFU⟩ hFU hF₁
  obtain ⟨hoff₂, hat₂⟩ := refolds_flat hr₂ ⟨FU, hFU⟩ hFU hF₂
  have hpl : ∀ (A : List Fold), A.map Fold.shape = pendAfter [] τ → ∀ m,
      ¬ PendingAt τ m → ∀ f ∈ A, f.l ≠ m := by
    intro A hA m hm f hf e
    have : m ∈ (pendAfter [] τ).map Shape.l := by
      rw [← hA, List.map_map]; exact e ▸ List.mem_map_of_mem (f := Shape.l ∘ Fold.shape) hf
    rcases pendAfter_places this with ⟨h, -⟩ | h
    · exact absurd h List.not_mem_nil
    · exact hm h
  refine ⟨fun m hm => ?_, fun i hi l α β T δ P he hτ => ?_⟩
  · rw [hoff₁ m (hpl A₁ hs₁ m hm), hoff₂ m (hpl A₂ hs₂ m hm)]
  · have hmem := pendAfter_mem (S := []) i hi he hτ
    have hfind : ∀ (A : List Fold), A.map Fold.shape = pendAfter [] τ →
        ∃ f ∈ A, f.shape = (⟨l, β, P⟩ : Shape) := by
      intro A hA
      rw [← hA] at hmem
      obtain ⟨f, hf, e⟩ := List.mem_map.mp hmem
      exact ⟨f, hf, e⟩
    obtain ⟨⟨fl, fβ, fP, fρ⟩, hf, hfs⟩ := hfind A₁ hs₁
    obtain ⟨⟨gl, gβ, gP, gρ⟩, hg, hgs⟩ := hfind A₂ hs₂
    simp only [Fold.shape, Shape.mk.injEq] at hfs hgs
    obtain ⟨rfl, rfl, hfP⟩ := hfs
    obtain ⟨rfl, rfl, hgP⟩ := hgs
    cases eq_of_heq hfP
    cases eq_of_heq hgP
    obtain ⟨v, χ, h, hw, hF₁l, hFUl⟩ := hat₁ _ hf
    obtain ⟨v', χ', h', hw', hF₂l, hFUl'⟩ := hat₂ _ hg
    simp only at hF₁l hFUl hF₂l hFUl'
    rw [hFUl] at hFUl'
    have hv : v = v' := by
      have := Option.some.inj hFUl'
      simpa [CellU.ownOf] using this
    subst hv
    exact ⟨v, ⟨χ, h, hw, hF₁l⟩, ⟨χ', h', hw', hF₂l⟩⟩

/-- DESIGN §2's first conjunct of `close_flat_agree`, as stated there: off every anti entry's
place the two flattenings agree. -/
theorem close_flat_agree_off_anti {τ : List OEnt} {π π₁ π₂ F₁ F₂ : WRes}
    (h₁ : Close τ π π₁) (h₂ : Close τ π π₂) (hF₁ : ResU.Flat π₁ F₁) (hF₂ : ResU.Flat π₂ F₂) :
    ∀ m, (∀ e ∈ τ, ¬ e.IsAntiAt m) → F₁.get m = F₂.get m := by
  intro m hm
  refine (close_flat_agree h₁ h₂ hF₁ hF₂).1 m ?_
  rintro ⟨i, hi, α, β, T, δ, P, he, -⟩
  have hmem : OEnt.anti m α β T δ P ∈ τ := he ▸ List.getElem_mem hi
  exact hm _ hmem (show m = m from rfl)

/-- `↭` from the pointwise agreement `close_flat_agree` gives. -/
theorem close_upd_of_valid {τ : List OEnt} {π π₁ π₂ : WRes} (h₁ : Close τ π π₁)
    (h₂ : Close τ π π₂) (hv₁ : ResU.Valid π₁) : ResU.UpdV π₁ π₂ := by
  obtain ⟨U, A₁, A₂, hr₁, hr₂, -, -⟩ :=
    close_pair h₁ h₂ (.nil π) (.nil π) rfl (fun _ h => absurd h List.not_mem_nil)
      (fun _ h => absurd h List.not_mem_nil)
  have hv₂ : ResU.Valid π₂ := refolds_valid_end hr₂ (refolds_valid_start hr₁ hv₁)
  obtain ⟨F₁, hF₁⟩ := hv₁
  obtain ⟨F₂, hF₂⟩ := hv₂
  obtain ⟨hoff, hat⟩ := close_flat_agree h₁ h₂ hF₁ hF₂
  refine ⟨⟨fun l s v χ h => ?_, fun l b P => ?_⟩, ⟨F₁, hF₁⟩, ⟨F₂, hF₂⟩⟩
  · rw [ResU.flatAt_iff hF₁, ResU.flatAt_iff hF₂]
    by_cases hp : PendingAt τ l
    · obtain ⟨i, hi, α, β, T, δ, P, he, hτ⟩ := hp
      obtain ⟨w, ⟨χ₁, h₁', hw₁, e₁⟩, ⟨χ₂, h₂', hw₂, e₂⟩⟩ := hat i hi l α β T δ P he hτ
      rw [e₁, e₂]
      exact ⟨fun c => absurd (Option.some.inj c).symm CellU.immOf_ne_mutOf,
        fun c => absurd (Option.some.inj c).symm CellU.immOf_ne_mutOf⟩
    · rw [hoff l hp]
  · by_cases hp : PendingAt τ l
    · obtain ⟨i, hi, α, β, T, δ, P', he, hτ⟩ := hp
      obtain ⟨w, ⟨χ₁, h₁', hw₁, e₁⟩, ⟨χ₂, h₂', hw₂, e₂⟩⟩ := hat i hi l α β T δ P' he hτ
      simp only [ResU.flatAt_iff hF₁, ResU.flatAt_iff hF₂, e₁, e₂]
      constructor
      · rintro ⟨u, ζ, k, kw, c⟩
        have c' := Option.some.inj c
        obtain rfl : β = b := CellU.mutOf_at c'
        obtain ⟨-, -, rfl⟩ := CellU.mutOf_inj c'
        exact ⟨w, χ₂, h₂', hw₂, rfl⟩
      · rintro ⟨u, ζ, k, kw, c⟩
        have c' := Option.some.inj c
        obtain rfl : β = b := CellU.mutOf_at c'
        obtain ⟨-, -, rfl⟩ := CellU.mutOf_inj c'
        exact ⟨w, χ₁, h₁', hw₁, rfl⟩
    · simp only [ResU.flatAt_iff hF₁, ResU.flatAt_iff hF₂, hoff l hp]

/-- **F-CLOSE.** Two closures of one valid resource by one list are `↭`-related. -/
theorem close_upd_coherent {τ : List OEnt} {π π₁ π₂ : WRes} (hv : ResU.Valid π) :
    Close τ π π₁ → Close τ π π₂ → ResU.UpdV π₁ π₂ :=
  fun h₁ h₂ => close_upd_of_valid h₁ h₂ (closePre_valid h₁ hv)

theorem updV_symm {ρ₁ ρ₂ : WRes} (h : ResU.UpdV ρ₁ ρ₂) : ResU.UpdV ρ₂ ρ₁ :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

/-- **(37) holds at one pair of closures iff it holds at every pair** (6.49 and the symmetry of
`↭`). -/
theorem upd_choice_free {τ τ' : List OEnt} {ρ π ρc πc ρc' πc' : WRes} :
    Close τ ρ ρc → Close τ' π πc → ResU.UpdV ρc πc →
    Close τ ρ ρc' → Close τ' π πc' → ResU.UpdV ρc' πc' := by
  intro hρ hπ hu hρ' hπ'
  have h₁ : ResU.UpdV ρc ρc' := close_upd_of_valid hρ hρ' hu.2.1
  have h₂ : ResU.UpdV πc πc' := close_upd_of_valid hπ hπ' hu.2.2
  exact ResU.UpdV.trans (ResU.UpdV.trans (updV_symm h₁) hu) h₂

/-- **Where the lifetimes are in the order arising obligations have, the pin removes no split.**
A split in `Res_β` holds no `imm` cell at a lifetime `β′ ⊏ β`. -/
theorem pin_harmless {l : BoCa.Loc} {α β : Life} {T : VTy} {δ : LSub}
    {P : Val → SPropS BoCa.Loc Val β} {τ : List OEnt} {ρP : WRes}
    (hw : OblWf (.anti l α β T δ P :: τ)) (hs : ρP.InStratum β) : AntiPin l τ ρP := by
  rintro e he β' hβ' m ψ hm ⟨t, ht, hmem⟩
  have hlt : β' ⊏ β :=
    hw 0 (by simp) l α β T δ P rfl e (by simpa using he) β' hβ'
  have hψ := hs m ψ hm
  rcases CellU.rep ψ with ⟨v, rfl⟩ | ⟨s, v, w, hw', rfl⟩ | ⟨b, v, w, hw', Q, hq, rfl⟩
  · simp at ht
  · simp only [CellU.lsOf_immOf, Option.some.injEq] at ht
    subst ht
    have h₁ := (CellU.inStratum_immOf β _ v w hw').mp hψ
    have h₂ := LSet.meet_least _ β' hmem
    exact absurd (lt_trans (lt_of_lt_of_le h₁ h₂) hlt) (lt_irrefl _)
  · simp at ht

/-! ## F1: where `CompatW` is `#`

At 6.65 and 6.66 entries the σ-component of `#` is `#` itself (6.24, an iff between the `mut`
cell and its unfolded `own(v) ● ρ_v`): a frame compatible with the resource is compatible with
every closure, and closing the composite is closing the part. -/

/-- A 6.65 step keeps `#` with any frame, both ways (6.24 and 6.46). -/
theorem hash_iff_of_mut_step {τr : List OEnt} {l : BoCa.Loc} {α : Life} {T : VTy} {δ : LSub}
    {ρf ρ ρ' : WRes} (h : CloseE τr (.mut l α T δ) ρ ρ') : ResU.Hash ρf ρ ↔ ResU.Hash ρf ρ' := by
  obtain ⟨v, χ, hχ, Q, hw, Y, hg, hY, hc, -⟩ := h
  have hd := ResU.del_compS hg
  have hW : ResU.CompS χ (ResU.single l (CellU.ownOf v)) Y := ResU.CompS.comm hY
  constructor
  · intro hH
    obtain ⟨y, hy, hyH⟩ := (hash_shift ρf (ρ.del l) _).mp ⟨ρ, hd, hH⟩
    obtain ⟨x, hx, hxH⟩ := (hash_shift ρf (ρ.del l) Y).mpr ⟨y, hy, (ResU.six24 hW).mp hyH⟩
    rwa [ResU.CompS.functional hx hc] at hxH
  · intro hH
    obtain ⟨y, hy, hyH⟩ := (hash_shift ρf (ρ.del l) Y).mp ⟨ρ', hc, hH⟩
    obtain ⟨x, hx, hxH⟩ := (hash_shift ρf (ρ.del l) _).mpr ⟨y, hy, (ResU.six24 hW).mpr hyH⟩
    rwa [ResU.CompS.functional hx hd] at hxH

/-- An anti step keeps `#` with any frame, both ways (6.24 and 6.46). -/
theorem hash_iff_of_antiE {l : BoCa.Loc} {β : Life} {P : Val → SPropS BoCa.Loc Val β}
    {ρP ρf ρ ρ' : WRes} (h : CloseEAnti l β P ρP ρ ρ') : ResU.Hash ρf ρ ↔ ResU.Hash ρf ρ' := by
  obtain ⟨v, hs, hw, X, rest, hX, hρ, hρ', -⟩ := h
  have hW : ResU.CompS ρP (ResU.single l (CellU.ownOf v)) X := ResU.CompS.comm hX
  constructor
  · intro hH
    obtain ⟨y, hy, hyH⟩ := (hash_shift ρf rest X).mp ⟨ρ, ResU.CompS.comm hρ, hH⟩
    obtain ⟨x, hx, hxH⟩ := (hash_shift ρf rest _).mpr ⟨y, hy, (ResU.six24 hW).mpr hyH⟩
    rwa [ResU.CompS.functional hx (ResU.CompS.comm hρ')] at hxH
  · intro hH
    obtain ⟨y, hy, hyH⟩ := (hash_shift ρf rest _).mp ⟨ρ', ResU.CompS.comm hρ', hH⟩
    obtain ⟨x, hx, hxH⟩ := (hash_shift ρf rest X).mpr ⟨y, hy, (ResU.six24 hW).mp hyH⟩
    rwa [ResU.CompS.functional hx (ResU.CompS.comm hρ)] at hxH

/-- A 6.65, 6.66 or marker step on a frame-compatible resource is the same step on the composite,
the frame beside. -/
theorem closeE_frame_excl {τr : List OEnt} {e : OEnt} (he : e.isMut ∨ e.isAnti ∨ ¬ e.isLend)
    {ρf ρ ρ' X : WRes} (h : CloseE τr e ρ ρ') (hH : ResU.Hash ρf ρ') (hX : ResU.CompS ρf ρ X) :
    ∃ X', CloseE τr e X X' ∧ ResU.CompS ρf ρ' X' := by
  cases e with
  | «mut» l α T δ =>
      obtain ⟨v, χ, hχ, Q, hw, Y, hg, hY, hc, -⟩ := h
      have hfl : ρf.get l = none := compS_left_none_of_right hX hg kind_mutOf_ne
      obtain ⟨-, X', hX', hvX'⟩ := hH
      refine ⟨X', ⟨v, χ, hχ, Q, hw, Y, ?_, hY, ?_, hvX'⟩, hX'⟩
      · rw [compS_get_right hX hfl]; exact hg
      · have hXd := compS_del_right hX hfl
        obtain ⟨ab, hab, habc⟩ := compS_reassoc' hc hX'
        rwa [ResU.CompS.functional hab hXd] at habc
  | anti l α β T δ P =>
      obtain ⟨ρP, hpin, v, hs, hw, Xa, rest, hXa, hρ, hρ', -⟩ := h
      obtain ⟨-, X', hX', hvX'⟩ := hH
      -- `X = Xa ● (ρf ● rest)`
      obtain ⟨fr, hfr, hXfr⟩ := compS_reassoc' (ResU.CompS.comm hρ) hX
      obtain ⟨y, hy, hyX⟩ := compS_reassoc' (ResU.CompS.comm hρ') hX'
      cases ResU.CompS.functional hy hfr
      refine ⟨X', ⟨ρP, hpin, v, hs, hw, Xa, fr, hXa, ?_, ResU.CompS.comm hyX, hvX'⟩, hX'⟩
      exact ResU.CompS.comm hXfr
  | imm r => simp [OEnt.isMut, OEnt.isAnti, OEnt.isLend] at he
  | reb _ _ _ _ _ _ _ => simp [OEnt.isMut, OEnt.isAnti, OEnt.isLend] at he
  | hnd n h' =>
      have e : ρ' = ρ := h
      subst e
      exact ⟨X, rfl, hX⟩

theorem hash_iff_of_step_excl {τr : List OEnt} {e : OEnt}
    (he : e.isMut ∨ e.isAnti ∨ ¬ e.isLend) {ρf ρ ρ' : WRes} (h : CloseE τr e ρ ρ') :
    ResU.Hash ρf ρ ↔ ResU.Hash ρf ρ' := by
  cases e with
  | «mut» l α T δ => exact hash_iff_of_mut_step h
  | anti l α β T δ P => obtain ⟨ρP, -, ha⟩ := h; exact hash_iff_of_antiE ha
  | imm r => simp [OEnt.isMut, OEnt.isAnti, OEnt.isLend] at he
  | reb _ _ _ _ _ _ _ => simp [OEnt.isMut, OEnt.isAnti, OEnt.isLend] at he
  | hnd n h' => have e : ρ' = ρ := h; rw [e]

theorem closePre_hash_iff : ∀ {τ τ₂ : List OEnt} {ρ ρc : WRes}, ClosePre τ τ₂ ρ ρc →
    (∀ e ∈ τ, e.isMut ∨ e.isAnti ∨ ¬ e.isLend) → ∀ {ρf : WRes},
    (ResU.Hash ρf ρ ↔ ResU.Hash ρf ρc) ∧
    (ResU.Hash ρf ρ → ∀ X, ResU.CompS ρf ρ X → ∃ Xc, ClosePre τ τ₂ X Xc ∧ ResU.CompS ρf ρc Xc)
  | _, _, _, _, .nil _ _, _, _ => ⟨Iff.rfl, fun _ X hX => ⟨X, .nil _ _, hX⟩⟩
  | _, _, _, _, @ClosePre.cons e _ _ _ _ _ hstep hrest, hτ, ρf => by
      have he := hτ e List.mem_cons_self
      obtain ⟨ih₁, ih₂⟩ := closePre_hash_iff hrest (fun e' h' => hτ e' (List.mem_cons_of_mem _ h'))
        (ρf := ρf)
      have hstepH := hash_iff_of_step_excl he hstep (ρf := ρf)
      refine ⟨hstepH.trans ih₁, fun hH X hX => ?_⟩
      obtain ⟨X₁, hX₁, hc₁⟩ := closeE_frame_excl he hstep (hstepH.mp hH) hX
      obtain ⟨Xc, hXc, hc⟩ := ih₂ (hstepH.mp hH) X₁ hc₁
      exact ⟨Xc, .cons hX₁ hXc, hc⟩

/-- **F1.** At 6.65, 6.66 and marker entries, the σ-component of `#` is `#`. -/
theorem compatW_iff_hash {τ : List OEnt} (hτ : ∀ e ∈ τ, e.isMut ∨ e.isAnti ∨ ¬ e.isLend)
    {ρf ρ : WRes} (hh : Holds τ ρ) : CompatW τ ρf ρ ↔ ResU.Hash ρf ρ := by
  constructor
  · intro h
    obtain ⟨ρc, hρc⟩ := hh
    exact ((closePre_hash_iff hρc hτ).1).mpr (h ρc hρc).1
  · intro hH ρc hρc
    obtain ⟨h₁, h₂⟩ := closePre_hash_iff hρc hτ (ρf := ρf)
    exact ⟨h₁.mp hH, h₂ hH⟩

/-! ## Compatibility at a resume (DESIGN §2, `compat_resume`, `close_frame`) -/

/-- **`close_frame`**: a frame `R` with `CompatW τ R ρ` is inert under closing: closing `ρ ● R` is
closing `ρ`, `R` beside. -/
theorem close_frame {τ : List OEnt} {R ρ X ρc : WRes} (hc : CompatW τ R ρ)
    (hX : ResU.CompS R ρ X) (hρc : Close τ ρ ρc) :
    ∃ Xc, Close τ X Xc ∧ ResU.CompS R ρc Xc :=
  (hc ρc hρc).2 X hX

/-- **`compat_resume`**: a resumer's frame `ρs ● ρo` — the stop's pieces and the resumer's own
resources — is compatible with the closure of the share and inert under it, when each piece is. -/
theorem compat_resume {τ' : List OEnt} {ρs ρo ρk ρsk ρso : WRes}
    (hsk : ResU.CompS ρs ρk ρsk) (hso : ResU.CompS ρs ρo ρso)
    (hs : CompatW τ' ρs ρk) (ho : CompatW τ' ρo ρsk) : CompatW τ' ρso ρk := by
  intro ρc hρc
  obtain ⟨hsH, hsI⟩ := hs ρc hρc
  obtain ⟨Xs, hXs, hcXs⟩ := hsI ρsk hsk
  obtain ⟨hoH, hoI⟩ := ho Xs hXs
  refine ⟨?_, fun X hX => ?_⟩
  · obtain ⟨-, w, hw, hvw⟩ := hoH
    obtain ⟨y, hy, hyw⟩ := compS_reassoc' hcXs hw
    obtain ⟨z, hz, hzw⟩ := compS_reassoc hy hyw
    have hy' : ResU.CompS ρs ρo y := ResU.CompS.comm hy
    cases ResU.CompS.functional hy' hso
    exact ⟨hyw.1, w, hyw, hvw⟩
  · -- `X = ρso ● ρk = ρo ● (ρs ● ρk) = ρo ● ρsk`
    obtain ⟨y, hy, hyX⟩ := compS_reassoc (ResU.CompS.comm hso) hX
    cases ResU.CompS.functional hy hsk
    obtain ⟨Xc, hXc, hcXc⟩ := hoI X hyX
    obtain ⟨y', hy', hy'X⟩ := compS_reassoc' hcXs hcXc
    cases ResU.CompS.functional (ResU.CompS.comm hy') hso
    exact ⟨Xc, hXc, hy'X⟩

/-! ## Exclusivity at a stop (DESIGN §2, `holds_exclusive`)

**Correction 3** (recorded in DESIGN §2): the design's (i), *no two entries of `τ` consume the same
pair*, contradicts its own (ii), *the entries consuming an exclusive key at one location form an
alternating chain*, once that chain has two anti entries: both consume `(ℓ, own)`. A doubly
nested `withbor3` (a `withbor3` on the relend of another) closes exactly such a list,
`[mut ℓ α₂, anti ℓ α₁ α₁ …, mut ℓ α₁, anti ℓ α₀ α₀ …]`. `not_holdsInjective` is that list closed
at a single valid cell. (i) holds at most for the `imm` keys; at the exclusive keys exclusivity is
(ii)'s alternation, with the lifetimes nested by the entry lemmas (not a resource fact). -/

/-- What an exit consumes at a location: the unfolded `own` cell, a `mut` cell at a lifetime, or
the component of an `imm` cell at one lifetime. -/
inductive OKey
  | own
  | mutAt (γ : Life)
  | immAt (γ : Life)

def OEnt.Consumes : OEnt → BoCa.Loc → OKey → Prop
  | .imm (p, α), m, k => m = p.le ∧ k = .immAt α
  | .mut l α _ _, m, k => m = l ∧ k = .mutAt α
  | .anti l _ _ _ _ _, m, k => m = l ∧ k = .own
  | .reb _ _ _ σR _ β χ, m, k => ((χ.restrictDom σR.exclPart).get m).isSome ∧ k = .immAt β
  | .hnd .., _, _ => False

/-- `e` consumes an exclusive key (`own` or `mutAt`) at `m`: a `mut` or `anti` entry at `m`. -/
def OEnt.ConsumesExcl (m : BoCa.Loc) : OEnt → Bool
  | .mut l _ _ _ => l == m
  | .anti l _ _ _ _ _ => l == m
  | _ => false

/-- DESIGN §2's (i), as stated there. -/
def HoldsInjective : Prop :=
  ∀ (τ : List OEnt) (ρ : WRes), ResU.Valid ρ → Holds τ ρ →
    ∀ i j (hi : i < τ.length) (hj : j < τ.length), i ≠ j →
      ∀ m k, τ[i].Consumes m k → τ[j].Consumes m k → False

/-- DESIGN §2's (ii): at one location the exclusive entries alternate, `mut l α` then
`anti l _ β …`, then `mut l β`. -/
def ChainStep : OEnt → OEnt → Prop
  | .mut l _ _ _, .anti l' _ _ _ _ _ => l = l'
  | .anti l _ β _ _ _, .mut l' β' _ _ => l = l' ∧ β = β'
  | _, _ => False

def HoldsChain : Prop :=
  ∀ (τ : List OEnt) (ρ : WRes), ResU.Valid ρ → Holds τ ρ → ∀ m : BoCa.Loc,
    List.IsChain ChainStep (τ.filter (fun e => e.ConsumesExcl m))

/-- A single `mut` cell over the empty witness is valid (6.24 from `ℓ ↦ own(v)`). -/
theorem valid_single_mut_empty (l : BoCa.Loc) (β : Life) (v : Val)
    (P : Val → SPropS BoCa.Loc Val β) (hw : P v ⟨PMap.empty, ResU.inStratum_empty β⟩) :
    ResU.Valid (ResU.single l (CellU.mutOf β v PMap.empty (ResU.inStratum_empty β) P hw)) := by
  have hW : ResU.CompS PMap.empty (ResU.single l (CellU.ownOf v)) (ResU.single l (CellU.ownOf v)) :=
    compS_empty_left _
  have hH : ResU.Hash PMap.empty (ResU.single l (CellU.ownOf v)) :=
    ⟨hW.1, _, hW, ResU.valid_single_own l v⟩
  obtain ⟨-, c, hc, hvc⟩ := (ResU.six24 hW).mpr hH
  rwa [eq_of_compS_empty_left hc] at hvc

/-- One 6.65 step on a single `mut` cell over the empty witness gives the `own` cell. -/
theorem close_mut_single {l : BoCa.Loc} {α : Life} {T : VTy} {δ : LSub} {v : Val}
    {Q : Val → SPropS BoCa.Loc Val α} {hw : Q v ⟨PMap.empty, ResU.inStratum_empty α⟩}
    (τr : List OEnt) :
    CloseE τr (.mut l α T δ)
      (ResU.single l (CellU.mutOf α v PMap.empty (ResU.inStratum_empty α) Q hw))
      (ResU.single l (CellU.ownOf v)) := by
  refine ⟨v, PMap.empty, ResU.inStratum_empty α, Q, hw, ResU.single l (CellU.ownOf v),
    ResU.single_get_self _ _, ResU.comp_empty_right _, ?_, ResU.valid_single_own l v⟩
  rw [single_del_self']
  exact compS_empty_left _
where
  single_del_self' : (ResU.single l (CellU.mutOf α v PMap.empty (ResU.inStratum_empty α) Q hw)).del l
      = PMap.empty := by
    classical
    refine PMap.ext fun k => ?_
    by_cases hk : k = l
    · subst hk; rw [ResU.del_get_self]; rfl
    · rw [ResU.del_get_ne _ hk, single_get_none _ hk]; rfl

/-- One anti step refolding a single `own` cell over the empty split. -/
theorem close_anti_single {l : BoCa.Loc} {α β : Life} {T : VTy} {δ : LSub} {v : Val}
    {P : Val → SPropS BoCa.Loc Val β} (hw : P v ⟨PMap.empty, ResU.inStratum_empty β⟩)
    (τr : List OEnt) :
    CloseE τr (.anti l α β T δ P) (ResU.single l (CellU.ownOf v))
      (ResU.single l (CellU.mutOf β v PMap.empty (ResU.inStratum_empty β) P hw)) := by
  refine ⟨PMap.empty, fun _ _ _ _ m ψ e => absurd (e.symm.trans (PMap.empty_get m)) (by simp),
    v, ResU.inStratum_empty β, hw, ResU.single l (CellU.ownOf v), PMap.empty,
    ResU.comp_empty_right _, ResU.comp_empty_right _, ResU.comp_empty_right _,
    valid_single_mut_empty l β v P hw⟩

/-- **(i) as stated fails at a closable list with two anti entries at one place** — the shape a
doubly nested `withbor3` closes. -/
theorem not_holdsInjective : ¬ HoldsInjective := by
  intro h
  let l : BoCa.Loc := 0
  let a₀ : Life := OrderDual.toDual 0
  let a₁ : Life := OrderDual.toDual 1
  let a₂ : Life := OrderDual.toDual 2
  let P : (β : Life) → Val → SPropS BoCa.Loc Val β := fun _ _ _ => True
  let τ : List OEnt :=
    [.mut l a₂ .unit ⟨[]⟩, .anti l a₁ a₁ .unit ⟨[]⟩ (P a₁), .mut l a₁ .unit ⟨[]⟩,
      .anti l a₀ a₀ .unit ⟨[]⟩ (P a₀)]
  let ρ := ResU.single l (CellU.mutOf a₂ Val.unit PMap.empty (ResU.inStratum_empty a₂)
    (P a₂) trivial)
  have hρ : ResU.Valid ρ := valid_single_mut_empty l a₂ Val.unit (P a₂) trivial
  have hh : Holds τ ρ :=
    ⟨_, .cons (close_mut_single _) (.cons (close_anti_single (P := P a₁) trivial _)
      (.cons (close_mut_single _) (.cons (close_anti_single (P := P a₀) trivial _)
        (.nil _ _))))⟩
  exact h τ ρ hρ hh 1 3 (by simp [τ]) (by simp [τ]) (by decide) l .own
    ⟨rfl, rfl⟩ ⟨rfl, rfl⟩

/-! ## The other checks (DESIGN §2), as named statements -/

/-- **`close_relend_anti`**, first half: the nested `withbor3` closes in context order — the relend
first, then the refold at the outer lend's lifetime and predicate. -/
theorem close_relend_anti {l : BoCa.Loc} {α α₀ β : Life} {T : VTy} {δ : LSub} {v : Val}
    {χ : WRes} {hχ : χ.InStratum α} {Q : Val → SPropS BoCa.Loc Val α} {hw : Q v ⟨χ, hχ⟩}
    {P : Val → SPropS BoCa.Loc Val β} {hχβ : χ.InStratum β} (hP : P v ⟨χ, hχβ⟩) {π : WRes}
    (hπ : π.get l = some (CellU.mutOf α v χ hχ Q hw)) (hv : ResU.Valid π) :
    ∃ π', ResU.CompS (π.del l) (ResU.single l (CellU.mutOf β v χ hχβ P hP)) π' ∧
      Close [.mut l α T δ, .anti l α₀ β T δ P] π π' := by
  have hd := ResU.del_compS hπ
  have hvm := (ResU.Valid.split hd hv).2
  obtain ⟨W, hW⟩ := ResU.compS_own_of_valid_mut hvm
  have hH : ResU.Hash (π.del l) W := (ResU.six24 hW).mp ⟨hd.1, π, hd, hv⟩
  obtain ⟨-, π₁, hπ₁, hv₁⟩ := hH
  obtain ⟨-, π', hπ', hv'⟩ := (ResU.six24 (P := P) (hw := hP) hW).mpr ⟨hπ₁.1, π₁, hπ₁, hv₁⟩
  refine ⟨π', hπ', .cons ⟨v, χ, hχ, Q, hw, W, hπ, ResU.CompS.comm hW, hπ₁, hv₁⟩
    (.cons ⟨χ, fun _ _ _ _ m ψ _ => ?_, v, hχβ, hP, W, π.del l, ResU.CompS.comm hW,
      ResU.CompS.comm hπ₁, ResU.CompS.comm hπ', hv'⟩ (.nil _ _))⟩
  simp at *

/-- **`close_relend_anti`**, second half: the reverse order is undefined — an anti step needs the
unfolded `own` cell at its place. -/
theorem not_closeE_anti_at_mut {τr : List OEnt} {l : BoCa.Loc} {α₀ β : Life} {T : VTy}
    {δ : LSub} {P : Val → SPropS BoCa.Loc Val β} {π π' : WRes} {ψ : CellU BoCa.Loc Val}
    (hπ : π.get l = some ψ) (hk : ψ.kind = Kind.mut) :
    ¬ CloseE τr (.anti l α₀ β T δ P) π π' := by
  rintro ⟨ρP, -, ha⟩
  obtain ⟨v, hv⟩ := closeEAnti_get_own ha
  rw [hπ] at hv; cases Option.some.inj hv; simp at hk

/-- **`younger_preserved`**: at a stop, the 6.64 entries a run hands on are younger than `α` when
those it held are and a record at `α` is present at both ends (`StopW`'s freshness conjunct). -/
theorem younger_preserved {τ τ' : List OEnt} {ps ps' : List FrameRec} {ls ls' : List SRec}
    {t : Expr} {ρf ρp ρ' π : WRes} {α : Life} (hs : StopW τ ps ps' ls ls' t τ' ρf ρp ρ' π)
    (ht : ¬ ∃ v : Val, t = .val v) (hx : ∃ x ∈ ls, x ∈ ls' ∧ x.2 = α)
    (hy : YoungerThan τ α) : YoungerThan τ' α := by
  intro q hq
  by_cases hqτ : OEnt.imm q ∈ τ
  · exact hy q hqτ
  · obtain ⟨x, hx, hx', rfl⟩ := hx
    exact (hs.2 ht).2.2.1 q hq hqτ x hx hx'

/-- **`compat_at_stop`**: at a stop, the stopped world's pieces a resumer's frame inherits — the
stop's frame, its leftover and the argument — are compatible with the closure of the share and
inert under it. **Correction 4** (recorded in DESIGN §2): the composite of the frame with the stop
resource is a premise (`hf`); `StopW` alone does not assert it, and the conclusion's `ρs` needs
it. -/
theorem compat_at_stop {τ τ' : List OEnt} {ps ps' : List FrameRec} {ls ls' : List SRec}
    {t : Expr} {ρf ρp ρ' π ρa ρk : WRes}
    (hs : StopW τ ps ps' ls ls' t τ' ρf ρp ρ' π) (ht : ¬ ∃ v, t = .val v)
    (hπ : ResU.CompS ρ' ρp π) (hk : ResU.CompS ρa ρk ρ') (hak : CompatW τ' ρa ρk)
    (hf : ∃ X, ResU.CompS ρf π X) :
    ∃ ρs, (∃ ρpa, ResU.CompS ρp ρa ρpa ∧ ResU.CompS ρf ρpa ρs) ∧ CompatW τ' ρs ρk := by
  obtain ⟨-, -, -, hfπ, hpρ'⟩ := hs.2 ht
  -- `π = (ρa ● ρk) ● ρp = (ρp ● ρa) ● ρk`
  obtain ⟨ρpa', hρpa', hπ'⟩ := compS_exch hk hπ
  have hpa : ResU.CompS ρp ρa ρpa' := ResU.CompS.comm hρpa'
  have h₁ : CompatW τ' ρpa' ρk :=
    compat_resume hk hρpa' hak hpρ'
  obtain ⟨X, hX⟩ := hf
  obtain ⟨ρs, hρs, hX'⟩ := compS_reassoc' hπ' hX
  exact ⟨ρs, ⟨ρpa', hpa, hρs⟩, compat_resume hπ' (ResU.CompS.comm hρs) h₁ hfπ⟩

/-- **F0** (DESIGN §2), stated: at the nested-copy configuration the frame holds a copy of the open
view nested in another cell's witness; it passes the verbatim frame premise, `CompatW` excludes
it, and no resource owning the lent place is compatible with it. -/
def FrameCopyBlocksExit : Prop :=
  ∃ (p : FrameRec) (α : Life) (ρf ρ fρ : WRes) (ps : List FrameRec) (ls : List SRec),
    ResU.Hash ρf ρ ∧ ResU.CompS ρf ρ fρ ∧
    TW fρ (p :: ps) (rsOf ls) ∧ Tagged fρ (p :: ps) ls ∧
    OpenInv [] ls (.imm (p, α)) ρ ∧
    ¬ CompatW [.imm (p, α)] ρf ρ ∧
    ∀ ρ', (ptoOwn p.le p.v ⋆ fun _ => True) ρ' → ¬ ResU.Hash ρ' ρf

/-- Why the pin exists (DESIGN §2), stated: without it, the anti step of `[anti l …, reb … β′ χ]`
with `β ⊏ β′` has two results on one resource that the `reb` step does not bring together. -/
def UnpinnedIncoherent : Prop :=
  ∃ (l : BoCa.Loc) (β β' : Life) (P : Val → SPropS BoCa.Loc Val β) (rb : OEnt)
    (π ρP₁ ρP₂ π₁ π₂ π₁' π₂' : WRes),
    rb.rebLife? = some β' ∧ β ⊏ β' ∧
    CloseEAnti l β P ρP₁ π π₁ ∧ CloseEAnti l β P ρP₂ π π₂ ∧
    CloseE [] rb π₁ π₁' ∧ CloseE [] rb π₂ π₂' ∧ ¬ ResU.UpdV π₁' π₂'

/-- **F2** at a 6.65 lend (DESIGN §2), stated: a `mut` cell of `π` at `(α, Q̂)` that `⦇ρc⦈` lacks is
closed by a `mut` entry of `τ′` at `l` and `α`. -/
def EntryRecordedMut : Prop :=
  ∀ {τ τ' : List OEnt} {ρ ρc π πc : WRes} {l : BoCa.Loc} {α : Life}
    {Q : Val → SPropS BoCa.Loc Val α} {v : Val} {χ : WRes} {h : χ.InStratum α}
    {hw : Q v ⟨χ, h⟩},
    Close τ ρ ρc → Close τ' π πc → ResU.UpdV ρc πc →
    (∀ v' χ' h' hw', ¬ ρc.FlatAt l (CellU.mutOf α v' χ' h' Q hw')) →
    π.get l = some (CellU.mutOf α v χ h Q hw) → ∃ T δ, OEnt.mut l α T δ ∈ τ'

/-- **`closed_compatW`** (DESIGN §2), stated: closed data is compatible with the closure and inert
under it. -/
def ClosedCompatW : Prop :=
  ∀ {τ : List OEnt} {R ρ : WRes}, (∀ α, R.InStratum α) → ResU.Hash R ρ → Holds τ ρ →
    CompatW τ R ρ

end WorldW

end

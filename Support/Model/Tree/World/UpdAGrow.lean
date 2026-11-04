import Support.Model.Tree.World.UpdATrans

/-!
# The world grows along a run beside a re-read frame  `[spec §62]`

`UpdA.trans`'s side condition `hw` (`docs/new-core/scope-806.md`, appendix, R2/R4) at the worlds
`twp_bind` holds: the middle world is `ρf ● ρ`, the end world `ρf′ ● ρ′` with `ρf′` the frame
re-read, the run `ρ ↭ ρ′` beside the end world, and the re-read frame holding nothing where only
one side of the run is masked.

* A non-`own` cell of `⦇ρf ● ρ⦈ = ⦇ρf⦈ ○ ⦇ρ⦈` has a non-`own` operand.
* The run's operand leaves the end mask off through the run's start side; its `imm` part is kept
  into `⦇ρ′⦈`, below the end world's cell (`compR_get_imm`), or absorbed.
* The frame's operand is re-read into `⦇ρf′⦈` (`Flat.rrLs`), so the end mask is off by `NoneAt`;
  its `imm` part is below the end world's cell.
* An `imm` composite is absorbed through each `imm` operand (`cellAbs_compR`).
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K K' : WCactus}

/-- A non-`own` composite has a non-`own` operand. -/
theorem CellUT.CompR.nonown_operand {φ₁ φ₂ ψ : TCell K} (h : CellUT.CompR φ₁ φ₂ ψ)
    (hk : ψ.kind ≠ Kind.own) : φ₁.kind ≠ Kind.own ∨ φ₂.kind ≠ Kind.own := by
  have e := CellUT.CompR.kind_eq h
  cases k₁ : φ₁.kind <;> cases k₂ : φ₂.kind <;> simp_all [kcomb]

/-- **The world grows along a run beside a re-read frame**: `UpdA.trans`'s `hw` at the middle
world `ρf ● ρ` and the end world `ρf′ ● ρ′`. Where the middle mask is off, a non-`own` cell of the
middle world's flattening leaves the end mask off, and an `imm` one is absorbed by the end
world's flattening. -/
theorem UpdA.grow {Θ : LocTy} (hK : K.Ext K') {E E' : BoCa.Loc → Prop} {ρf ρ fρ : TRes K}
    {ρf' ρ' fρ' : TRes K'} (h : UpdA Θ E E' ρ ρ' fρ') (hr : RR Θ ρf ρf')
    (hc : ResUT.CompS ρf ρ fρ) (hc' : ResUT.CompS ρf' ρ' fρ')
    (hn : NoneAt (MaskDiff E E') ρf') :
    ∀ τw τw', ResUT.Flat fρ τw → ResUT.Flat fρ' τw' → ∀ l χ, τw.get l = some χ →
      χ.kind ≠ Kind.own → ¬ E l → ¬ E' l ∧
        (χ.kind = Kind.imm → ∃ χ', τw'.get l = some χ' ∧ CellAbs Θ χ χ') := by
  intro τw τw' hτw hτw' l χ eχ hkχ hEl
  obtain ⟨σ, σ', τx, hσ, hσ', hτx, hx⟩ := h
  obtain rfl := ResUT.Flat.functional hτx hτw'
  obtain ⟨σf, σ₁, hσf, hσ₁, hcomp⟩ := BoLo.flat_compR hc hτw
  obtain rfl := ResUT.Flat.functional hσ hσ₁
  obtain ⟨σf', σ₂', hσf', hσ₂', hcomp'⟩ := BoLo.flat_compR hc' hτx
  obtain rfl := ResUT.Flat.functional hσ' hσ₂'
  obtain ⟨σf₁, hσf₁, hsf⟩ := ResUT.Flat.rrLs hK hσf hr
  obtain rfl := ResUT.Flat.functional hσf₁ hσf'
  -- the frame's cell, re-read
  have reF : ∀ φ, σf.get l = some φ → ∃ φ', σf₁.get l = some φ' ∧ LsSim Θ φ' φ := by
    intro φ e
    have := hsf l; rw [e] at this
    revert this; cases σf₁.get l with
    | none => intro h; cases h
    | some φ' => intro h; cases h with | some h => exact ⟨φ', rfl, h⟩
  -- each non-`own` operand leaves the end mask off; each `imm` one is absorbed
  have opF : ∀ φ, σf.get l = some φ → ¬ E' l ∧
      (φ.kind = Kind.imm → ∃ χ', τx.get l = some χ' ∧ CellAbs Θ φ χ') := by
    intro φ e
    obtain ⟨φ', e', hsm⟩ := reF φ e
    refine ⟨fun hE' => ?_, fun hk => ?_⟩
    · have := hn σf₁ hσf₁ l (Or.inr ⟨hE', hEl⟩)
      rw [e'] at this; cases this
    · obtain ⟨χ', eχ', hle⟩ := compR_get_imm hcomp' (Or.inl e') (hsm.1.trans hk)
      exact ⟨χ', eχ', (LsSim.xcell hsm).abs_of_le hk hle⟩
  have opR : ∀ φ, σ.get l = some φ → φ.kind ≠ Kind.own → ¬ E' l ∧
      (φ.kind = Kind.imm → ∃ χ', τx.get l = some χ' ∧ CellAbs Θ φ χ') := by
    intro φ e hk
    obtain ⟨hE', hd⟩ := (hx l).1 φ e hk hEl
    refine ⟨hE', fun hkφ => ?_⟩
    rcases hd with ⟨φ', e', hxc⟩ | ha | ⟨hkm, -⟩
    · obtain ⟨χ', eχ', hle⟩ := compR_get_imm hcomp' (Or.inr e') (hxc.1.trans hkφ)
      exact ⟨χ', eχ', hxc.abs_of_le hkφ hle⟩
    · exact ha
    · rw [hkφ] at hkm; cases hkm
  rcases G.Comp.get hcomp l with ⟨-, -, f⟩ | ⟨ζ, f₁, -, f⟩ | ⟨ζ, -, f₂, f⟩ |
      ⟨ζ₁, ζ₂, ζ, f₁, f₂, f, hC⟩
  · rw [f] at eχ; cases eχ
  · rw [f] at eχ; cases eχ; exact opF _ f₁
  · rw [f] at eχ; cases eχ; exact opR _ f₂ hkχ
  · rw [f] at eχ; cases eχ
    have hE' : ¬ E' l := by
      rcases CellUT.CompR.nonown_operand hC hkχ with k | k
      · exact (opF _ f₁).1
      · exact (opR _ f₂ k).1
    refine ⟨hE', fun hk => ?_⟩
    have nonown : ∀ {φ : TCell K}, φ.kind = Kind.imm → φ.kind ≠ Kind.own :=
      fun k c => Kind.noConfusion (k.symm.trans c)
    have pick : ∃ χ', τx.get l = some χ' := by
      rcases CellUT.CompR.imm_operand hC hk with k | k
      · obtain ⟨χ', eχ', -⟩ := (opF _ f₁).2 k; exact ⟨χ', eχ'⟩
      · obtain ⟨χ', eχ', -⟩ := (opR _ f₂ (nonown k)).2 k; exact ⟨χ', eχ'⟩
    obtain ⟨χ', eχ'⟩ := pick
    refine ⟨χ', eχ', cellAbs_compR hC hk (fun k => ?_) (fun k => ?_)⟩
    · obtain ⟨χ₀, e₀, ha⟩ := (opF _ f₁).2 k
      rw [eχ'] at e₀; cases e₀; exact ha
    · obtain ⟨χ₀, e₀, ha⟩ := (opR _ f₂ (nonown k)).2 k
      rw [eχ'] at e₀; cases e₀; exact ha

/-! ### A plain update, then a run along the walks -/

/-- **`UpdX` then `UpdA`** (`twp_extend`, `twp_update`, the heap rules): a segment-start update
gives no cell up, so it is `UpdA` at the empty middle world (`UpdX.toA`), where `UpdA.trans`'s
world-growth condition reads no cell. The other side conditions are `UpdA.trans`'s. -/
theorem UpdX.transA {K'' : WCactus} {Θ₁ Θ₂ : LocTy} (hK₁ : K.Ext K') (hK : K'.Ext K'')
    {E E' E'' : BoCa.Loc → Prop} {ρ : TRes K} {ρ' : TRes K'} {ρ'' fρ'' : TRes K''}
    (h : UpdX Θ₁ E E' ρ ρ') (h' : UpdA Θ₂ E' E'' ρ' ρ'' fρ'')
    {W : TRes K} (hW : MutOne W) (hsub : ∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ)
    {W' : TRes K'} (hW' : MutOne W')
    (hsub' : ∀ y φ, CellAt ρ' y φ → φ.kind = Kind.mut → CellAt W' y φ)
    (hcl : ImmMaskClosed E' ρ') : UpdA Θ₂ E E'' ρ ρ'' fρ'' :=
  UpdA.trans hK₁ hK (UpdX.toA (fρ' := (PMap.empty : TRes K')) h ⟨PMap.empty, flat_empty⟩) h'
    hW hsub hW' hsub' hcl (fun τw' _ hτw' _ l χ e => by
      obtain rfl := ResUT.Flat.functional hτw' flat_empty
      simp at e)

/-! ### Masks -/

/-- The masks may be replaced by equal ones. -/
theorem UpdA.congr {Θ : LocTy} {E E' F F' : BoCa.Loc → Prop} (hF : ∀ l, F l ↔ E l)
    (hF' : ∀ l, F' l ↔ E' l) {ρ : TRes K} {ρ' fρ' : TRes K'} (h : UpdA Θ E E' ρ ρ' fρ') :
    UpdA Θ F F' ρ ρ' fρ' := by
  obtain ⟨σ, σ', τw, hσ, hσ', hτw, hx⟩ := h
  refine ⟨σ, σ', τw, hσ, hσ', hτw, fun l => ⟨fun ψ e hk hE₀ => ?_, fun ψ' e hk hE₀ => ?_⟩⟩
  · obtain ⟨h₁, rest⟩ := (hx l).1 ψ e hk (fun c => hE₀ ((hF l).mpr c))
    refine ⟨fun c => h₁ ((hF' l).mp c), ?_⟩
    rcases rest with r | r | ⟨hkm, m, ζ, χ, hEm, hb, eχ, ha⟩
    · exact Or.inl r
    · exact Or.inr (Or.inl r)
    · exact Or.inr (Or.inr ⟨hkm, m, ζ, χ, fun c => hEm ((hF m).mp c), hb, eχ, ha⟩)
  · obtain ⟨h₁, rest⟩ := (hx l).2 ψ' e hk (fun c => hE₀ ((hF' l).mpr c))
    exact ⟨fun c => h₁ ((hF l).mp c), rest⟩

/-- A closed mask may be replaced by an equal one. -/
theorem ImmMaskClosed.congr {E F : BoCa.Loc → Prop} (hF : ∀ l, F l ↔ E l) {ρ : TRes K}
    (h : ImmMaskClosed E ρ) : ImmMaskClosed F ρ :=
  fun y ζ c k hy ev hev x ξ hx => (hF x).mpr (h y ζ c k ((hF y).mp hy) ev hev x ξ hx)

/-- **Masking a location on both sides keeps `UpdA`**, the run's end a part of the end world and
the start closed at the widened mask. A `mut` cell leaving with an ancestor the new mask covers
sits beneath an ancestor it does not (`Beneath.unmasked`, the re-anchoring of `UpdA.trans`); that
ancestor is an `imm` cell of `⦇ρ⦈` unmasked by the run, so the run keeps it into `⦇ρ′⦈`, below
the end world's cell, or gives it up to the end world. -/
theorem UpdA.widen {Θ : LocTy} {E E' : BoCa.Loc → Prop} (F : BoCa.Loc → Prop) {ρ : TRes K}
    {ρ' f' fρ' : TRes K'} (h : UpdA Θ E E' ρ ρ' fρ') (hw : ResUT.CompS f' ρ' fρ')
    {W : TRes K} (hW : MutOne W) (hsub : ∀ y φ, CellAt ρ y φ → φ.kind = Kind.mut → CellAt W y φ)
    (hcl : ImmMaskClosed (fun l => E l ∨ F l) ρ) :
    UpdA Θ (fun l => E l ∨ F l) (fun l => E' l ∨ F l) ρ ρ' fρ' := by
  obtain ⟨σ, σ', τw, hσ, hσ', hτw, hx⟩ := h
  obtain ⟨σf, σ₂, -, hσ₂, hcw⟩ := BoLo.flat_compR hw hτw
  obtain rfl := ResUT.Flat.functional hσ' hσ₂
  -- an `imm` cell of the start unmasked by the run is absorbed by the end world
  have absA : ∀ m φ, ¬ E m → σ.get m = some φ → φ.kind = Kind.imm →
      ∃ χ, τw.get m = some χ ∧ CellAbs Θ φ χ := by
    intro m φ hEm e hk
    obtain ⟨-, hd⟩ := (hx m).1 φ e (by rw [hk]; decide) hEm
    rcases hd with ⟨φ', e', hxc⟩ | ha | ⟨hkm, -⟩
    · obtain ⟨χ, eχ, hle⟩ := compR_get_imm hcw (Or.inr e') (hxc.1.trans hk)
      exact ⟨χ, eχ, hxc.abs_of_le hk hle⟩
    · exact ha
    · rw [hk] at hkm; cases hkm
  refine ⟨σ, σ', τw, hσ, hσ', hτw, fun l => ⟨fun ψ e hk hE₀ => ?_, fun ψ' e hk hE₀ => ?_⟩⟩
  · have hEl : ¬ E l := fun c => hE₀ (Or.inl c)
    have hFl : ¬ F l := fun c => hE₀ (Or.inr c)
    obtain ⟨h₁, rest⟩ := (hx l).1 ψ e hk hEl
    refine ⟨fun c => c.elim h₁ hFl, ?_⟩
    rcases rest with r | r | ⟨hkm, m, ζ, χ, -, hb, -, -⟩
    · exact Or.inl r
    · exact Or.inr (Or.inl r)
    · obtain ⟨m₂, ζ₂, hEm₂, hb₂⟩ := hb.unmasked hW hσ hsub hcl hkm hE₀
      obtain ⟨χ₂, eχ₂, ha₂⟩ := absA m₂ ζ₂ (fun c => hEm₂ (Or.inl c)) hb₂.1 hb₂.2.1
      exact Or.inr (Or.inr ⟨hkm, m₂, ζ₂, χ₂, hEm₂, hb₂, eχ₂, ha₂⟩)
  · obtain ⟨h₁, rest⟩ := (hx l).2 ψ' e hk (fun c => hE₀ (Or.inl c))
    exact ⟨fun c => c.elim h₁ (fun f => hE₀ (Or.inr f)), rest⟩

end BoCa.Fig16.Tree.Wp

end

import Core.Chain.SI.UpdN

/-!
# `↭` with a mask, and `[TR]` 6.48 at a mask  `[spec §62]`

`docs/new-core/scope-821-loans.md`, stage 1, change 2: `UpdVN Φ k ρ π` becomes
`UpdVNm Φ k M ρ π`, `UpdN`'s `imm` and `mut` clauses read only at locations outside `M`.

`updVNm_frame` is `[TR]` 6.48 at a mask, by `updVN_frame`'s proof (`SI/UpdN.lean`): the same three
cases at `ℓ ∉ M`, the aliasable case through the immutable ancestor, the `mut ○ mut` composite by
`compR_stepN`. The ancestor step reads the `imm` clause at the ancestor's location, which may lie
in `M`. The scope's restriction "the lent cell's payload is empty (`ρ_P = ∅`)" closes that case:
`MaskShallow M ρ` says every `imm` cell of `ρ`'s flattening at a masked location has the empty
witness, so nothing lies beneath it (`ancestor_unmasked`), and the ancestor of an unmasked
location is unmasked.

`not_endpointMaskCompose` is a configuration at `UpdVNm`: a mask that each of two consecutive runs
draws from its own start and end does not compose. This is the composition `rwpG_compose` performs
at its `↭` line (`UpdVN.trans` after `updVN_frame`), read at the scope's mask.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

/-! ### The clause -/

/-- `↭`'s `imm` clause at the locations outside `M`. -/
def UpdImmM (M : Set Loc) (ρ₁ ρ₂ : WRes) : Prop :=
  ∀ l, l ∉ M → ∀ (s : LSet) (v : Val) (χ : WRes) (h : χ.InStratum s.join),
    ρ₁.FlatAt l (CellU.immOf s v χ h) ↔ ρ₂.FlatAt l (CellU.immOf s v χ h)

/-- **`UpdN` with a mask**: its `imm` and `mut` clauses at the locations outside `M`. -/
def UpdNm (Φ : LocFam) (n : Nat) (M : Set Loc) (ρ₁ ρ₂ : WRes) : Prop :=
  UpdImmM M ρ₁ ρ₂ ∧
  (∀ l, l ∉ M → ∀ ψ, ρ₁.FlatAt l ψ → ψ.kind = Kind.mut →
    ∃ ψ', ρ₂.FlatAt l ψ' ∧ MutStep Φ n l ψ ψ') ∧
  (∀ l, l ∉ M → ∀ ψ', ρ₂.FlatAt l ψ' → ψ'.kind = Kind.mut →
    ∃ ψ, ρ₁.FlatAt l ψ ∧ MutStep Φ n l ψ ψ')

/-- `UpdNm`, guarded by `✓ρ₁ ∧ ✓ρ₂` as `UpdVN`. -/
def UpdVNm (Φ : LocFam) (n : Nat) (M : Set Loc) (ρ₁ ρ₂ : WRes) : Prop :=
  UpdNm Φ n M ρ₁ ρ₂ ∧ ρ₁.Valid ∧ ρ₂.Valid

theorem UpdNm.of_updN {Φ : LocFam} {n : Nat} (M : Set Loc) {ρ₁ ρ₂ : WRes}
    (h : UpdN Φ n ρ₁ ρ₂) : UpdNm Φ n M ρ₁ ρ₂ :=
  ⟨fun l _ => h.1 l, fun l _ => h.2.1 l, fun l _ => h.2.2 l⟩

/-- **At the empty mask, `UpdNm` is `UpdN`.** -/
theorem updNm_empty_iff {Φ : LocFam} {n : Nat} {ρ₁ ρ₂ : WRes} :
    UpdNm Φ n ∅ ρ₁ ρ₂ ↔ UpdN Φ n ρ₁ ρ₂ :=
  ⟨fun h => ⟨fun l => h.1 l (by simp), fun l => h.2.1 l (by simp), fun l => h.2.2 l (by simp)⟩,
    UpdNm.of_updN ∅⟩

theorem updVNm_empty_iff {Φ : LocFam} {n : Nat} {ρ₁ ρ₂ : WRes} :
    UpdVNm Φ n ∅ ρ₁ ρ₂ ↔ UpdVN Φ n ρ₁ ρ₂ := by
  unfold UpdVNm UpdVN
  rw [updNm_empty_iff]

/-- A larger mask asks less. -/
theorem UpdNm.mono {Φ : LocFam} {n : Nat} {M M' : Set Loc} (hM : M ⊆ M') {ρ₁ ρ₂ : WRes}
    (h : UpdNm Φ n M ρ₁ ρ₂) : UpdNm Φ n M' ρ₁ ρ₂ :=
  ⟨fun l hl => h.1 l (fun hm => hl (hM hm)), fun l hl => h.2.1 l (fun hm => hl (hM hm)),
    fun l hl => h.2.2 l (fun hm => hl (hM hm))⟩

theorem UpdVNm.mono {Φ : LocFam} {n : Nat} {M M' : Set Loc} (hM : M ⊆ M') {ρ₁ ρ₂ : WRes}
    (h : UpdVNm Φ n M ρ₁ ρ₂) : UpdVNm Φ n M' ρ₁ ρ₂ :=
  ⟨h.1.mono hM, h.2⟩

/-- `UpdVNm` is downward closed in the index. -/
theorem UpdVNm.down {Φ : LocFam} (hΦ : Φ.Down) {n n' : Nat} (hn : n' ≤ n) {M : Set Loc}
    {ρ₁ ρ₂ : WRes} (h : UpdVNm Φ n M ρ₁ ρ₂) : UpdVNm Φ n' M ρ₁ ρ₂ := by
  refine ⟨⟨h.1.1, fun l hl ψ hψ hk => ?_, fun l hl ψ' hψ hk => ?_⟩, h.2⟩
  · obtain ⟨ψ', h', hs⟩ := h.1.2.1 l hl ψ hψ hk
    exact ⟨ψ', h', hs.trans hΦ hn (MutStep.refl hs.2.1)⟩
  · obtain ⟨ψ, h', hs⟩ := h.1.2.2 l hl ψ' hψ hk
    exact ⟨ψ, h', hs.trans hΦ hn (MutStep.refl hs.2.1)⟩

/-- **`[TR]` 6.49 at a mask**: the two runs' masks together. -/
theorem UpdNm.trans {Φ : LocFam} (hΦ : Φ.Down) {n n' : Nat} (hn : n' ≤ n) {M₁ M₂ : Set Loc}
    {ρ₁ ρ₂ ρ₃ : WRes} (h₁ : UpdNm Φ n M₁ ρ₁ ρ₂) (h₂ : UpdNm Φ n' M₂ ρ₂ ρ₃) :
    UpdNm Φ n' (M₁ ∪ M₂) ρ₁ ρ₃ := by
  refine ⟨fun l hl s v χ hs => ?_, fun l hl ψ h hk => ?_, fun l hl ψ'' h hk => ?_⟩ <;>
    simp only [Set.mem_union, not_or] at hl
  · exact (h₁.1 l hl.1 s v χ hs).trans (h₂.1 l hl.2 s v χ hs)
  · obtain ⟨ψ', h', hs₁⟩ := h₁.2.1 l hl.1 ψ h hk
    obtain ⟨ψ'', h'', hs₂⟩ := h₂.2.1 l hl.2 ψ' h' hs₁.2.1
    exact ⟨ψ'', h'', hs₁.trans hΦ hn hs₂⟩
  · obtain ⟨ψ', h', hs₂⟩ := h₂.2.2 l hl.2 ψ'' h hk
    obtain ⟨ψ, h₀, hs₁⟩ := h₁.2.2 l hl.1 ψ' h' hs₂.1
    exact ⟨ψ, h₀, hs₁.trans hΦ hn hs₂⟩

theorem UpdVNm.trans {Φ : LocFam} (hΦ : Φ.Down) {n n' : Nat} (hn : n' ≤ n) {M₁ M₂ : Set Loc}
    {ρ₁ ρ₂ ρ₃ : WRes} (h₁ : UpdVNm Φ n M₁ ρ₁ ρ₂) (h₂ : UpdVNm Φ n' M₂ ρ₂ ρ₃) :
    UpdVNm Φ n' (M₁ ∪ M₂) ρ₁ ρ₃ :=
  ⟨h₁.1.trans hΦ hn h₂.1, h₁.2.1, h₂.2.2⟩

theorem UpdVNm.refl (Φ : LocFam) (n : Nat) (M : Set Loc) {ρ : WRes} (h : ρ.Valid) :
    UpdVNm Φ n M ρ ρ :=
  ⟨UpdNm.of_updN M (UpdN.refl Φ n ρ), h, h⟩

/-! ### At one location of two flattenings -/

theorem cellUpdN_of_updNm {Φ : LocFam} {n : Nat} {M : Set Loc} {ρ₁ ρ₂ σ₁ σ₂ : WRes}
    (h : UpdNm Φ n M ρ₁ ρ₂) (h₁ : ResU.Flat ρ₁ σ₁) (h₂ : ResU.Flat ρ₂ σ₂) {l : Loc}
    (hl : l ∉ M) : CellUpdN Φ n l (σ₁.get l) (σ₂.get l) := by
  refine ⟨fun s v χ hh => ?_, fun ψ hψ hk => ?_, fun ψ' hψ hk => ?_⟩
  · rw [← ResU.flatAt_iff h₁, ← ResU.flatAt_iff h₂]
    exact h.1 l hl s v χ hh
  · obtain ⟨ψ', h', hs⟩ := h.2.1 l hl ψ ((ResU.flatAt_iff h₁ _ _).mpr hψ) hk
    exact ⟨ψ', (ResU.flatAt_iff h₂ _ _).mp h', hs⟩
  · obtain ⟨ψ, h', hs⟩ := h.2.2 l hl ψ' ((ResU.flatAt_iff h₂ _ _).mpr hψ) hk
    exact ⟨ψ, (ResU.flatAt_iff h₁ _ _).mp h', hs⟩

/-- `UpdNm` read off a pair of flattenings at the locations outside `M`. -/
theorem updNm_of_flat {Φ : LocFam} {n : Nat} {M : Set Loc} {ρ₁ ρ₂ σ₁ σ₂ : WRes}
    (h₁ : ResU.Flat ρ₁ σ₁) (h₂ : ResU.Flat ρ₂ σ₂)
    (hc : ∀ l, l ∉ M → CellUpdN Φ n l (σ₁.get l) (σ₂.get l)) : UpdNm Φ n M ρ₁ ρ₂ := by
  refine ⟨fun l hl s v χ hh => ?_, fun l hl ψ hψ hk => ?_, fun l hl ψ' hψ hk => ?_⟩
  · rw [ResU.flatAt_iff h₁, ResU.flatAt_iff h₂]
    exact (hc l hl).1 s v χ hh
  · obtain ⟨ψ', h', hs⟩ := (hc l hl).2.1 ψ ((ResU.flatAt_iff h₁ _ _).mp hψ) hk
    exact ⟨ψ', (ResU.flatAt_iff h₂ _ _).mpr h', hs⟩
  · obtain ⟨ψ, h', hs⟩ := (hc l hl).2.2 ψ' ((ResU.flatAt_iff h₂ _ _).mp hψ) hk
    exact ⟨ψ, (ResU.flatAt_iff h₁ _ _).mpr h', hs⟩

/-! ### The immutable ancestor at a mask -/

/-- **`ρ_P = ∅` at the mask**: every `imm` cell of `ρ`'s flattening at a location of `M` has the
empty witness. -/
def MaskShallow (M : Set Loc) (ρ : WRes) : Prop :=
  ∀ l, l ∈ M → ∀ (s : LSet) (v : Val) (χ : WRes) (h : χ.InStratum s.join),
    ρ.FlatAt l (CellU.immOf s v χ h) → χ = PMap.empty

theorem maskShallow_empty (ρ : WRes) : MaskShallow ∅ ρ := fun _ h => absurd h (by simp)

theorem updImmM_symm {M : Set Loc} {ρ₁ ρ₂ : WRes} (h : UpdImmM M ρ₁ ρ₂) : UpdImmM M ρ₂ ρ₁ :=
  fun l hl s v χ hs => (h l hl s v χ hs).symm

/-- An `imm` cell of `ag(ρ)` is the flattening's cell there. -/
theorem flat_of_ag_imm {ρ e a σ : WRes} (he : ExS ρ e) (hc : ResU.CompS e a σ) {m : Loc}
    {s : LSet} {u : Val} {χ : WRes} {hh : χ.InStratum s.join}
    (hg : a.get m = some (CellU.immOf s u χ hh)) : σ.get m = some (CellU.immOf s u χ hh) := by
  have hex : e.get m = none := by
    cases f : e.get m with
    | none => rfl
    | some ξ =>
        exact absurd (CellU.CompatS.kinds (hc.1 m ξ _ f hg)).1 (ExS.immFree he m ξ f)
  rcases ResU.Comp.get hc m with ⟨-, f₂, -⟩ | ⟨ζ, -, f₂, -⟩ | ⟨ζ, -, f₂, f⟩ |
      ⟨ζ₁, ζ₂, ζ, f₁, -, -, -⟩
  · rw [hg] at f₂; exact absurd f₂ (by simp)
  · rw [hg] at f₂; exact absurd f₂ (by simp)
  · exact f.trans (congrArg some (Option.some.inj (f₂.symm.trans hg)))
  · rw [hex] at f₁; exact absurd f₁ (by simp)

/-- **The ancestor of an unmasked cell is unmasked**: beneath an `imm` cell with the empty
witness lies nothing. -/
theorem ancestor_unmasked {M : Set Loc} {ρ e a σ : WRes} (hsh : MaskShallow M ρ)
    (he : ExS ρ e) (ha : AgW ρ a) (hc : ResU.CompS e a σ) {m n : Loc} {s : LSet} {u : Val}
    {χ : WRes} {hh : χ.InStratum s.join} {ev av p : WRes} {ξ : CellU Loc Val}
    (hm : a.get m = some (CellU.immOf s u χ hh)) (hev : ExR χ ev) (hav : AgW χ av)
    (hp : ResU.CompR ev av p) (hpn : p.get n = some ξ) : m ∉ M := by
  intro hmM
  have hχ : χ = PMap.empty :=
    hsh m hmM s u χ hh ⟨σ, ⟨e, a, he, ha, hc⟩, flat_of_ag_imm he hc hm⟩
  subst hχ
  obtain rfl : ev = PMap.empty := ExR.functional hev exW_empty
  obtain rfl : av = PMap.empty := AgW.functional hav agW_empty
  obtain rfl : p = PMap.empty := ResU.CompR.functional hp (ResU.comp_empty_right _)
  rw [PMap.empty_get] at hpn
  cases hpn

/-- `updImm_ag_imm_wit_factor` at an unmasked location. -/
theorem updImmM_ag_imm_wit_factor {M : Set Loc} {ρ₂ ρ₃ e₂ a₂ σ₂ e₃ a₃ σ₃ : WRes}
    (h : UpdImmM M ρ₂ ρ₃)
    (he₂ : ExS ρ₂ e₂) (ha₂ : AgW ρ₂ a₂) (hc₂ : ResU.CompS e₂ a₂ σ₂)
    (he₃ : ExS ρ₃ e₃) (ha₃ : AgW ρ₃ a₃) (hc₃ : ResU.CompS e₃ a₃ σ₃)
    {m : Loc} (hmM : m ∉ M) {s : LSet} {u : Val} {χ : WRes} {hh : χ.InStratum s.join}
    (hg : a₂.get m = some (CellU.immOf s u χ hh)) :
    ∃ ev av p z, ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧ ResU.CompR p z a₃ := by
  have hσ₂ := flat_of_ag_imm he₂ hc₂ hg
  have hσ₃ : σ₃.get m = some (CellU.immOf s u χ hh) :=
    (ResU.flatAt_iff ⟨e₃, a₃, he₃, ha₃, hc₃⟩ m _).mp
      ((h m hmM s u χ hh).mp ((ResU.flatAt_iff ⟨e₂, a₂, he₂, ha₂, hc₂⟩ m _).mpr hσ₂))
  exact ResU.flat_imm_wit_factor he₃ ha₃ hc₃ hσ₃

/-- `updImm_ag_nonimm_transfer` at a mask, its ancestor unmasked by `MaskShallow`. -/
theorem updImmM_ag_nonimm_transfer {M : Set Loc} {ρ₂ ρ₃ e₂ a₂ σ₂ e₃ a₃ σ₃ : WRes}
    (h : UpdImmM M ρ₂ ρ₃) (hsh : MaskShallow M ρ₂)
    (he₂ : ExS ρ₂ e₂) (ha₂ : AgW ρ₂ a₂) (hc₂ : ResU.CompS e₂ a₂ σ₂)
    (he₃ : ExS ρ₃ e₃) (ha₃ : AgW ρ₃ a₃) (hc₃ : ResU.CompS e₃ a₃ σ₃)
    {n : Loc} {φ : CellU Loc Val} (hg : a₂.get n = some φ)
    (hk : φ.kind ≠ Kind.imm) :
    ∃ (χ ev av p z : WRes) (ξ : CellU Loc Val),
      ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧ ResU.CompR p z a₃ ∧
      p.get n = some ξ ∧ ξ.kind ≠ Kind.imm ∧
      ξ.wit = φ.wit ∧ ξ.erase = φ.erase := by
  obtain ⟨m, s, u, χ, hh, ev, av, p, ξ, hm, hev, hav, hp, hpn, hξk, hξw, hξe⟩ :=
    AgW.nonimm_beneath_imm ha₂ n φ hg hk
  have hmM := ancestor_unmasked hsh he₂ ha₂ hc₂ hm hev hav hp hpn
  obtain ⟨ev', av', p', z, hev', hav', hp', hz⟩ :=
    updImmM_ag_imm_wit_factor h he₂ ha₂ hc₂ he₃ ha₃ hc₃ hmM hm
  rw [ExR.functional hev' hev, AgW.functional hav' hav] at hp'
  rw [ResU.CompR.functional hp' hp] at hz
  exact ⟨χ, ev, av, p, z, ξ, hev, hav, hp, hz, hpn, hξk, hξw, hξe⟩

/-- An `own` cell has the empty witness. -/
private theorem wit_own' (ψ : CellU Loc Val) (hk : ψ.kind = Kind.own) :
    ψ.wit = (PMap.empty : WRes) := by
  rcases CellU.rep ψ with ⟨u, rfl⟩ | ⟨s, u, τ, m, rfl⟩ | ⟨c, u, τ, m, Q, k, rfl⟩
  · simp
  · simp at hk
  · simp at hk

/-- What a `○`-factorisation carries over (`SI/UpdN.lean`'s `factor_carry`). -/
private theorem factor_carry' {n : Loc} (p z a : WRes) (ξ ζ : CellU Loc Val)
    (hC : ResU.CompR p z a) (hp : p.get n = some ξ) (ha : a.get n = some ζ)
    (hζo : ζ.kind ≠ Kind.own) :
    ζ.erase = ξ.erase ∧ (ξ.kind ≠ Kind.own → ζ.wit = ξ.wit) := by
  rcases ResU.Comp.get hC n with ⟨f₁, -, -⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
      ⟨ψ₁, ψ₂, ψ, f₁, -, f, hcc⟩
  · rw [hp] at f₁
    exact absurd f₁ (by simp)
  · have e₁ : ξ = ψ := Option.some.inj (hp.symm.trans f₁)
    have e₂ : ζ = ψ := Option.some.inj (ha.symm.trans f)
    rw [e₁, e₂]
    exact ⟨rfl, fun _ => rfl⟩
  · rw [hp] at f₁
    exact absurd f₁ (by simp)
  · have e₁ : ξ = ψ₁ := Option.some.inj (hp.symm.trans f₁)
    have e₂ : ζ = ψ := Option.some.inj (ha.symm.trans f)
    subst e₁
    subst e₂
    refine ⟨(CellU.CompR.erase hcc).2, fun hξo => ?_⟩
    rcases CellU.CompR.wit_of_ne_own hcc hζo with ⟨-, e⟩ | ⟨k₂, e⟩
    · exact e
    · exact e.trans (CellU.CompR.wit hcc hξo k₂).symm

/-- **The ancestor step at a mask** (`agMutCarry`): both sides' ancestors unmasked by
`MaskShallow`. -/
theorem agMutCarryM {M : Set Loc} {ρ₂ ρ₃ e₂ a₂ σ₂ e₃ a₃ σ₃ : WRes}
    (h : UpdImmM M ρ₂ ρ₃) (hs₂ : MaskShallow M ρ₂) (hs₃ : MaskShallow M ρ₃)
    (he₂ : ExS ρ₂ e₂) (ha₂ : AgW ρ₂ a₂) (hc₂ : ResU.CompS e₂ a₂ σ₂)
    (he₃ : ExS ρ₃ e₃) (ha₃ : AgW ρ₃ a₃) (hc₃ : ResU.CompS e₃ a₃ σ₃)
    {x : Loc} {φ ψ' : CellU Loc Val} (hg : a₂.get x = some φ) (hk : φ.kind = Kind.mut)
    (hσ₃ : σ₃.get x = some ψ') (hk' : ψ'.kind = Kind.mut) :
    a₃.get x = some ψ' ∧ ψ'.erase = φ.erase ∧ ψ'.wit = φ.wit := by
  have hφk : φ.kind ≠ Kind.imm := by rw [hk]; simp
  have hφo : φ.kind ≠ Kind.own := by rw [hk]; simp
  have hψk : ψ'.kind ≠ Kind.imm := by rw [hk']; simp
  have hψo : ψ'.kind ≠ Kind.own := by rw [hk']; simp
  obtain ⟨κ, ev, av, p, z, ξ, -, -, -, hz, hpn, hξk, hξw, hξe⟩ :=
    updImmM_ag_nonimm_transfer h hs₂ he₂ ha₂ hc₂ he₃ ha₃ hc₃ hg hφk
  have hocc : ∃ ζ, a₃.get x = some ζ := by
    rcases ResU.Comp.get hz x with ⟨f₁, -, -⟩ | ⟨ψ, -, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
        ⟨ψ₁, ψ₂, ψ, -, -, f, -⟩
    · rw [hpn] at f₁
      exact absurd f₁ (by simp)
    · exact ⟨ψ, f⟩
    · rw [hpn] at f₁
      exact absurd f₁ (by simp)
    · exact ⟨ψ, f⟩
  obtain ⟨ζ, hζ⟩ := hocc
  have he₃n : e₃.get x = none := by
    cases f : e₃.get x with
    | none => rfl
    | some ξ' =>
        have hk₀ := (CellU.CompatS.kinds (hc₃.1 x ξ' ζ f hζ)).1
        exact absurd hk₀ (ExS.immFree he₃ x ξ' f)
  have ha₃n : a₃.get x = σ₃.get x := by
    rcases ResU.Comp.get hc₃ x with ⟨-, f₂, -⟩ | ⟨ψ, f₁, -, -⟩ | ⟨ψ, -, f₂, f⟩ |
        ⟨ψ₁, ψ₂, ψ, f₁, -, -, -⟩
    · rw [hζ] at f₂
      exact absurd f₂ (by simp)
    · rw [he₃n] at f₁
      exact absurd f₁ (by simp)
    · rw [f₂, f]
    · rw [he₃n] at f₁
      exact absurd f₁ (by simp)
  have hgt : a₃.get x = some ψ' := ha₃n.trans hσ₃
  obtain ⟨heL, hwL⟩ := factor_carry' p z a₃ ξ ψ' hz hpn hgt hψo
  refine ⟨hgt, heL.trans hξe, ?_⟩
  by_cases hξo : ξ.kind = Kind.own
  · have hχe : φ.wit = (PMap.empty : WRes) := hξw.symm.trans (wit_own' ξ hξo)
    obtain ⟨κ', ev', av', p', z', ξ', -, -, -, hz', hpn', hξk', hξw', hξe'⟩ :=
      updImmM_ag_nonimm_transfer (updImmM_symm h) hs₃ he₃ ha₃ hc₃ he₂ ha₂ hc₂ hgt hψk
    obtain ⟨-, hwR⟩ := factor_carry' p' z' a₂ ξ' φ hz' hpn' hg hφo
    by_cases hξo' : ξ'.kind = Kind.own
    · rw [hχe, ← hξw', wit_own' ξ' hξo']
    · exact ((hwR hξo').trans hξw').symm
  · exact (hwL hξo).trans hξw

/-- `updImm_ag_imm_eq` at an unmasked location. -/
theorem updImmM_ag_imm_eq {M : Set Loc} {ρ₂ ρ₃ e₂ a₂ σ₂ e₃ a₃ σ₃ : WRes}
    (h : UpdImmM M ρ₂ ρ₃)
    (he₂ : ExS ρ₂ e₂) (ha₂ : AgW ρ₂ a₂) (hc₂ : ResU.CompS e₂ a₂ σ₂)
    (he₃ : ExS ρ₃ e₃) (ha₃ : AgW ρ₃ a₃) (hc₃ : ResU.CompS e₃ a₃ σ₃)
    {n : Loc} (hnM : n ∉ M) {ψ : CellU Loc Val} (hg : a₂.get n = some ψ)
    (hk : ψ.kind = Kind.imm) : a₃.get n = some ψ := by
  obtain ⟨s, hs, hψ⟩ := CellU.imm_eta hk
  rw [hψ] at hg ⊢
  have hσ₂ := flat_of_ag_imm he₂ hc₂ hg
  have hσ₃ : σ₃.get n = some (CellU.immOf s ψ.erase ψ.wit hs) :=
    (ResU.flatAt_iff ⟨e₃, a₃, he₃, ha₃, hc₃⟩ n _).mp
      ((h n hnM s _ _ hs).mp ((ResU.flatAt_iff ⟨e₂, a₂, he₂, ha₂, hc₂⟩ n _).mpr hσ₂))
  exact ResU.ag_eq_flat_at_imm he₃ hc₃ hσ₃ (CellU.kind_immOf _ _ _ _)

/-- `updN_ag_ne_own` at an unmasked location. -/
theorem updNm_ag_ne_own {Φ : LocFam} {k : Nat} {M : Set Loc} {ρ₂ ρ₃ e₂ a₂ σ₂ e₃ a₃ σ₃ : WRes}
    (h : UpdNm Φ k M ρ₂ ρ₃) (hs₂ : MaskShallow M ρ₂) (hs₃ : MaskShallow M ρ₃)
    (he₂ : ExS ρ₂ e₂) (ha₂ : AgW ρ₂ a₂) (hc₂ : ResU.CompS e₂ a₂ σ₂)
    (he₃ : ExS ρ₃ e₃) (ha₃ : AgW ρ₃ a₃) (hc₃ : ResU.CompS e₃ a₃ σ₃)
    {n : Loc} (hnM : n ∉ M) {ψ : CellU Loc Val} (hg : a₂.get n = some ψ)
    (hk : ψ.kind ≠ Kind.own) :
    ∃ ψ', a₃.get n = some ψ' ∧
      (ψ' = ψ ∨ (MutStep Φ k n ψ ψ' ∧ ψ'.erase = ψ.erase ∧ ψ'.wit = ψ.wit)) := by
  by_cases hi : ψ.kind = Kind.imm
  · exact ⟨ψ, updImmM_ag_imm_eq h.1 he₂ ha₂ hc₂ he₃ ha₃ hc₃ hnM hg hi, .inl rfl⟩
  · have hm : ψ.kind = Kind.mut := by
      revert hk hi; cases ψ.kind <;> simp
    have hσ₂ : σ₂.get n = some ψ := ResU.flat_eq_ag_at he₂ hc₂ hg hi
    obtain ⟨ψ', h', hs⟩ :=
      h.2.1 n hnM ψ ((ResU.flatAt_iff ⟨e₂, a₂, he₂, ha₂, hc₂⟩ _ _).mpr hσ₂) hm
    have hσ₃ : σ₃.get n = some ψ' := (ResU.flatAt_iff ⟨e₃, a₃, he₃, ha₃, hc₃⟩ _ _).mp h'
    obtain ⟨ha, he, hw⟩ := agMutCarryM h.1 hs₂ hs₃ he₂ ha₂ hc₂ he₃ ha₃ hc₃ hg hm hσ₃ hs.2.1
    exact ⟨ψ', ha, .inr ⟨hs, he, hw⟩⟩

/-- `updN_ag_own_or_none` at an unmasked location. -/
theorem updNm_ag_own_or_none {Φ : LocFam} {k : Nat} {M : Set Loc}
    {ρ₂ ρ₃ e₂ a₂ σ₂ e₃ a₃ σ₃ : WRes}
    (h : UpdNm Φ k M ρ₂ ρ₃) (hs₂ : MaskShallow M ρ₂) (hs₃ : MaskShallow M ρ₃)
    (he₂ : ExS ρ₂ e₂) (ha₂ : AgW ρ₂ a₂) (hc₂ : ResU.CompS e₂ a₂ σ₂)
    (he₃ : ExS ρ₃ e₃) (ha₃ : AgW ρ₃ a₃) (hc₃ : ResU.CompS e₃ a₃ σ₃)
    {n : Loc} (hnM : n ∉ M) (hg : ∀ ψ, a₂.get n = some ψ → ψ.kind = Kind.own) :
    ∀ φ, a₃.get n = some φ → φ.kind = Kind.own := by
  intro φ hφ
  by_contra hko
  by_cases hi : φ.kind = Kind.imm
  · have := updImmM_ag_imm_eq (updImmM_symm h.1) he₃ ha₃ hc₃ he₂ ha₂ hc₂ hnM hφ hi
    exact hko (by rw [← hg φ this])
  · have hm : φ.kind = Kind.mut := by
      revert hko hi; cases φ.kind <;> simp
    have hσ₃ : σ₃.get n = some φ := ResU.flat_eq_ag_at he₃ hc₃ hφ hi
    obtain ⟨ψ, h', hs⟩ :=
      h.2.2 n hnM φ ((ResU.flatAt_iff ⟨e₃, a₃, he₃, ha₃, hc₃⟩ _ _).mpr hσ₃) hm
    have hσ₂ : σ₂.get n = some ψ := (ResU.flatAt_iff ⟨e₂, a₂, he₂, ha₂, hc₂⟩ _ _).mp h'
    obtain ⟨ha, -, -⟩ :=
      agMutCarryM (updImmM_symm h.1) hs₃ hs₂ he₃ ha₃ hc₃ he₂ ha₂ hc₂ hφ hm hσ₂ hs.1
    have := hg ψ ha
    rw [hs.1] at this
    cases this

/-! ### `[TR]` 6.48 at a mask -/

/-- **`[TR]` Lemma 6.48 at a mask**: if `ρ₁ # ρ₂`, `ρ₁ # ρ₃` and `ρ₂ ↭ₖ ρ₃` outside `M`, then
`ρ₁ ● ρ₂ ↭ₖ ρ₁ ● ρ₃` outside `M`, when `ρ₂` and `ρ₃` carry only empty-witness `imm` cells at `M`.
`updVN_frame`'s proof at every `ℓ ∉ M`: the three cases at `ℓ`; at the aliasable walk the `imm`
ancestor, unmasked by `ancestor_unmasked`, carries the cell (`agMutCarryM`); the `mut ○ mut`
composites are related by `compR_stepN`. -/
theorem updVNm_frame {Φ : LocFam} {k : Nat} {M : Set Loc} {ρ₁ ρ₂ ρ₃ ρ₁₂ ρ₁₃ : WRes}
    (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂)
    (h₁₃ : ResU.CompS ρ₁ ρ₃ ρ₁₃) (hh₂ : ResU.Hash ρ₁ ρ₂) (hh₃ : ResU.Hash ρ₁ ρ₃)
    (hs₂ : MaskShallow M ρ₂) (hs₃ : MaskShallow M ρ₃)
    (h : UpdVNm Φ k M ρ₂ ρ₃) : UpdVNm Φ k M ρ₁₂ ρ₁₃ := by
  classical
  obtain ⟨τ₁₂, hτ₁₂⟩ := hash_valid_comp hh₂ h₁₂
  obtain ⟨τ₁₃, hτ₁₃⟩ := hash_valid_comp hh₃ h₁₃
  obtain ⟨e₁, e₂, e, a₁, a₂, a, he₁, he₂, hec, ha₁, ha₂, hac, hτ⟩ :=
    (ResU.Flat.split h₁₂).mp hτ₁₂
  obtain ⟨e₁', e₃, e', a₁', a₃, a', he₁', he₃, hec', ha₁', ha₃, hac', hτ'⟩ :=
    (ResU.Flat.split h₁₃).mp hτ₁₃
  rw [ExS.functional he₁' he₁] at hec'
  rw [AgW.functional ha₁' ha₁] at hac'
  obtain ⟨σ₂, x₂, y₂, hx₂, hy₂, hc₂⟩ := h.2.1
  rw [ExS.functional hx₂ he₂, AgW.functional hy₂ ha₂] at hc₂
  obtain ⟨σ₃, x₃, y₃, hx₃, hy₃, hc₃⟩ := h.2.2
  rw [ExS.functional hx₃ he₃, AgW.functional hy₃ ha₃] at hc₃
  have hfS : ∀ ψ₁ ψ₂ ψ ψ' : CellU BoCa.Loc BoCa.Val,
      CellU.CompS ψ₁ ψ₂ ψ → CellU.CompS ψ₁ ψ₂ ψ' → ψ = ψ' :=
    fun _ _ _ _ p q => CellU.CompS.functional p q
  have hfR : ∀ ψ₁ ψ₂ ψ ψ' : CellU BoCa.Loc BoCa.Val,
      CellU.CompR ψ₁ ψ₂ ψ → CellU.CompR ψ₁ ψ₂ ψ' → ψ = ψ' :=
    fun _ _ _ _ p q => CellU.CompR.functional p q
  have hdA : ∀ n, e.get n = none ∨ a.get n = none :=
    ResU.CompatS.disjoint_of_immFree
      (ResU.ImmFree.compS hec (ExS.immFree he₁) (ExS.immFree he₂)) hτ.1
  have hdA' : ∀ n, e'.get n = none ∨ a'.get n = none :=
    ResU.CompatS.disjoint_of_immFree
      (ResU.ImmFree.compS hec' (ExS.immFree he₁) (ExS.immFree he₃)) hτ'.1
  have hdE : ∀ n, e₁.get n = none ∨ e₂.get n = none :=
    ResU.CompatS.disjoint_of_immFree (ExS.immFree he₁) hec.1
  have hdE' : ∀ n, e₁.get n = none ∨ e₃.get n = none :=
    ResU.CompatS.disjoint_of_immFree (ExS.immFree he₁) hec'.1
  have hcell : ∀ n, n ∉ M → CellUpdN Φ k n (τ₁₂.get n) (τ₁₃.get n) := by
    intro n hnM
    by_cases hE1 : e₁.get n = none
    · by_cases hA1 : a₁.get n = none
      · -- `ρ₁` is silent in both walks: each composite is the operand's own flattening
        have hEn : e.get n = e₂.get n := by
          rcases ResU.Comp.get hec n with ⟨-, f₂, f⟩ | ⟨ψ, f₁, -, -⟩ | ⟨ψ, -, f₂, f⟩ |
              ⟨ψ₁, ψ₂, ψ, f₁, -, -, -⟩
          · rw [f, f₂]
          · rw [hE1] at f₁; exact absurd f₁ (by simp)
          · rw [f, f₂]
          · rw [hE1] at f₁; exact absurd f₁ (by simp)
        have hAn : a.get n = a₂.get n := by
          rcases ResU.Comp.get hac n with ⟨-, f₂, f⟩ | ⟨ψ, f₁, -, -⟩ | ⟨ψ, -, f₂, f⟩ |
              ⟨ψ₁, ψ₂, ψ, f₁, -, -, -⟩
          · rw [f, f₂]
          · rw [hA1] at f₁; exact absurd f₁ (by simp)
          · rw [f, f₂]
          · rw [hA1] at f₁; exact absurd f₁ (by simp)
        have hEn' : e'.get n = e₃.get n := by
          rcases ResU.Comp.get hec' n with ⟨-, f₂, f⟩ | ⟨ψ, f₁, -, -⟩ | ⟨ψ, -, f₂, f⟩ |
              ⟨ψ₁, ψ₂, ψ, f₁, -, -, -⟩
          · rw [f, f₂]
          · rw [hE1] at f₁; exact absurd f₁ (by simp)
          · rw [f, f₂]
          · rw [hE1] at f₁; exact absurd f₁ (by simp)
        have hAn' : a'.get n = a₃.get n := by
          rcases ResU.Comp.get hac' n with ⟨-, f₂, f⟩ | ⟨ψ, f₁, -, -⟩ | ⟨ψ, -, f₂, f⟩ |
              ⟨ψ₁, ψ₂, ψ, f₁, -, -, -⟩
          · rw [f, f₂]
          · rw [hA1] at f₁; exact absurd f₁ (by simp)
          · rw [f, f₂]
          · rw [hA1] at f₁; exact absurd f₁ (by simp)
        have hL : τ₁₂.get n = σ₂.get n := by
          refine OptComp.functional hfS ?_ (hc₂.2 n)
          rw [← hEn, ← hAn]; exact hτ.2 n
        have hR : τ₁₃.get n = σ₃.get n := by
          refine OptComp.functional hfS ?_ (hc₃.2 n)
          rw [← hEn', ← hAn']; exact hτ'.2 n
        rw [hL, hR]
        exact cellUpdN_of_updNm h.1 ⟨e₂, a₂, he₂, ha₂, hc₂⟩ ⟨e₃, a₃, he₃, ha₃, hc₃⟩ hnM
      · -- `ag(ρ₁)` is occupied: both composites are the aliasable ones
        have hAne : a.get n ≠ none := by
          rcases ResU.Comp.get hac n with ⟨f₁, -, -⟩ | ⟨ψ, -, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
              ⟨ψ₁, ψ₂, ψ, -, -, f, -⟩
          · exact absurd f₁ hA1
          · rw [f]; exact (by simp)
          · exact absurd f₁ hA1
          · rw [f]; exact (by simp)
        have hAne' : a'.get n ≠ none := by
          rcases ResU.Comp.get hac' n with ⟨f₁, -, -⟩ | ⟨ψ, -, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
              ⟨ψ₁, ψ₂, ψ, -, -, f, -⟩
          · exact absurd f₁ hA1
          · rw [f]; exact (by simp)
          · exact absurd f₁ hA1
          · rw [f]; exact (by simp)
        have hEnone : e.get n = none := (hdA n).resolve_right hAne
        have hEnone' : e'.get n = none := (hdA' n).resolve_right hAne'
        have hL : τ₁₂.get n = a.get n := by
          have h0 := hτ.2 n
          rw [hEnone] at h0
          cases hh : a.get n with
          | none => rw [hh] at h0; exact h0
          | some ψ => rw [hh] at h0; exact h0
        have hR : τ₁₃.get n = a'.get n := by
          have h0 := hτ'.2 n
          rw [hEnone'] at h0
          cases hh : a'.get n with
          | none => rw [hh] at h0; exact h0
          | some ψ => rw [hh] at h0; exact h0
        rw [hL, hR]
        by_cases hk : ∀ ψ, a₂.get n = some ψ → ψ.kind = Kind.own
        · have hk' := updNm_ag_own_or_none h.1 hs₂ hs₃ he₂ ha₂ hc₂ he₃ ha₃ hc₃ hnM hk
          obtain ⟨ζ, hζ⟩ : ∃ ζ, a₁.get n = some ζ := by
            cases f : a₁.get n with
            | none => exact absurd f hA1
            | some ζ => exact ⟨ζ, rfl⟩
          have hone : ∀ (b c : ResU BoCa.Loc BoCa.Val),
              ResU.CompR a₁ b c → (∀ ψ, b.get n = some ψ → ψ.kind = Kind.own) →
              c.get n = some ζ := by
            intro b c hcc hb
            rcases ResU.Comp.get hcc n with ⟨f₁, -, -⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
                ⟨ψ₁, ψ₂, ψ, f₁, f₂, f, hC⟩
            · rw [hζ] at f₁; exact absurd f₁ (by simp)
            · rw [f, ← hζ, f₁]
            · rw [hζ] at f₁; exact absurd f₁ (by simp)
            · rw [f, show ψ = ψ₁ from CellU.compR_own_kind_right hC (hb ψ₂ f₂),
                ← hζ, f₁]
          rw [hone a₂ a hac hk, hone a₃ a' hac' hk']
          exact CellUpdN.refl _ _ _ _
        · obtain ⟨ψ, hψ, hψk⟩ : ∃ ψ, a₂.get n = some ψ ∧ ψ.kind ≠ Kind.own := by
            by_contra hcon
            exact hk (fun ψ e => by
              by_contra hko
              exact hcon ⟨ψ, e, hko⟩)
          obtain ⟨ψ', hψ', hrel⟩ :=
            updNm_ag_ne_own h.1 hs₂ hs₃ he₂ ha₂ hc₂ he₃ ha₃ hc₃ hnM hψ hψk
          rcases hrel with rfl | ⟨hst, hse, hsw⟩
          · have heq : a.get n = a'.get n := by
              refine OptComp.functional hfR (hac.2 n) ?_
              rw [hψ, ← hψ']; exact hac'.2 n
            rw [heq]
            exact CellUpdN.refl _ _ _ _
          · obtain ⟨ζ, hζ⟩ : ∃ ζ, a₁.get n = some ζ := by
              cases f : a₁.get n with
              | none => exact absurd f hA1
              | some ζ => exact ⟨ζ, rfl⟩
            have g := hac.2 n
            have g' := hac'.2 n
            rw [hζ, hψ] at g
            rw [hζ, hψ'] at g'
            obtain ⟨c, hcn, hcc⟩ := g
            obtain ⟨c', hcn', hcc'⟩ := g'
            rw [hcn, hcn']
            exact compR_stepN hcc hcc' hst hse hsw
    · -- `ex(ρ₁)` is occupied: both composites are `ex(ρ₁)(n)`
      obtain ⟨ζ, hζ⟩ : ∃ ζ, e₁.get n = some ζ := by
        cases f : e₁.get n with
        | none => exact absurd f hE1
        | some ζ => exact ⟨ζ, rfl⟩
      have hstep : ∀ (x ex ax cx tx : ResU BoCa.Loc BoCa.Val),
          ResU.CompS e₁ x ex → ResU.CompR a₁ ax cx → ResU.CompS ex cx tx →
          (∀ m, ex.get m = none ∨ cx.get m = none) →
          (∀ m, e₁.get m = none ∨ x.get m = none) → tx.get n = some ζ := by
        intro x ex ax cx tx hxe hxa hxt hdd hde
        have hexn : ex.get n = some ζ := by
          rcases ResU.Comp.get hxe n with ⟨f₁, -, -⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
              ⟨ψ₁, ψ₂, ψ, -, f₂, -, -⟩
          · rw [hζ] at f₁; exact absurd f₁ (by simp)
          · rw [f, ← hζ, f₁]
          · rw [hζ] at f₁; exact absurd f₁ (by simp)
          · rcases hde n with c | c
            · rw [hζ] at c; exact absurd c (by simp)
            · rw [c] at f₂; exact absurd f₂ (by simp)
        have hcxn : cx.get n = none := (hdd n).resolve_left (by rw [hexn]; simp)
        rcases ResU.Comp.get hxt n with ⟨f₁, -, -⟩ | ⟨ψ, f₁, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
            ⟨ψ₁, ψ₂, ψ, -, f₂, -, -⟩
        · rw [hexn] at f₁; exact absurd f₁ (by simp)
        · rw [f, ← hexn, f₁]
        · rw [hexn] at f₁; exact absurd f₁ (by simp)
        · rw [hcxn] at f₂; exact absurd f₂ (by simp)
      rw [hstep e₂ e a₂ a τ₁₂ hec hac hτ hdA hdE,
        hstep e₃ e' a₃ a' τ₁₃ hec' hac' hτ' hdA' hdE']
      exact CellUpdN.refl _ _ _ _
  exact ⟨updNm_of_flat hτ₁₂ hτ₁₃ hcell, ⟨τ₁₂, hτ₁₂⟩, ⟨τ₁₃, hτ₁₃⟩⟩

/-- At the empty mask, `updVNm_frame` is `updVN_frame`. -/
theorem updVNm_frame_empty {Φ : LocFam} {k : Nat} {ρ₁ ρ₂ ρ₃ ρ₁₂ ρ₁₃ : WRes}
    (h₁₂ : ResU.CompS ρ₁ ρ₂ ρ₁₂) (h₁₃ : ResU.CompS ρ₁ ρ₃ ρ₁₃) (hh₂ : ResU.Hash ρ₁ ρ₂)
    (hh₃ : ResU.Hash ρ₁ ρ₃) (h : UpdVN Φ k ρ₂ ρ₃) : UpdVN Φ k ρ₁₂ ρ₁₃ :=
  updVNm_empty_iff.mp (updVNm_frame h₁₂ h₁₃ hh₂ hh₃ (maskShallow_empty _) (maskShallow_empty _)
    (updVNm_empty_iff.mpr h))

/-! ### A mask drawn from each run's ends does not compose

The scope's mask for a run from `(ρ, g)` to `(ρ′, g′)` is drawn from `g` and `g′`: the locations
where either holds an `xm`, and the locations of records whose lifetime either wholly holds.
`rwpG_compose`'s `↭` line composes the first run's update with the second's (`UpdVN.trans` after
`updVN_frame`); at the scope's masks that is the law below, with `Xᵢ` the locations the `i`-th
resource's ghost masks. The middle resource's mask is in both runs' masks and in neither end's. -/

/-- **Composition of end-drawn masks.** -/
def EndpointMaskCompose : Prop :=
  ∀ (Φ : LocFam) (n : Nat) (X₀ X₁ X₂ : Set Loc) (ρ₀ ρ₁ ρ₂ : WRes),
    UpdVNm Φ n (X₀ ∪ X₁) ρ₀ ρ₁ → UpdVNm Φ n (X₁ ∪ X₂) ρ₁ ρ₂ → UpdVNm Φ n (X₀ ∪ X₂) ρ₀ ρ₂

/-- `mut(0, v, ∅, ⊤)`. -/
private def topMut (v : Val) : CellU Loc Val :=
  CellU.mutOf (0 : Life) v PMap.empty (ResU.inStratum_empty _) (fun _ _ => True) trivial

private theorem valid_single_topMut (l : Loc) (v : Val) :
    ResU.Valid (ResU.single l (topMut v)) :=
  ResU.valid_single_mut_of_wit (ResU.comp_empty_left _) (ResU.valid_single_own l v)

/-- The flattening of `ℓ ↦ mut(0, v, ∅, ⊤)` holds only `ℓ`. -/
private theorem flat_single_topMut {l : Loc} {v : Val} {τ : WRes}
    (hτ : ResU.Flat (ResU.single l (topMut v)) τ) : ∀ x, x ≠ l → τ.get x = none := by
  obtain ⟨e, a, he, ha, hc⟩ := hτ
  obtain ⟨e₀, he₀, hce⟩ := ExW.single_mut_inv he
  obtain rfl : e₀ = PMap.empty := ExS.functional he₀ exW_empty
  obtain rfl : ResU.single l (topMut v) = e := ResU.eq_of_comp_empty_right hce
  obtain rfl : a = PMap.empty := AgW.functional (AgW.single_mut_inv ha) agW_empty
  obtain rfl : ResU.single l (topMut v) = τ := ResU.eq_of_comp_empty_right hc
  intro x hx
  exact ResU.single_get_ne _ hx

/-- **End-drawn masks do not compose.** `ρ₀ = ∅`; the middle and the end are
`ℓ ↦ mut(0, v, ∅, ⊤)`; only the middle's ghost masks `ℓ` (it holds `xm ℓ`). Each run is unmasked
outside `ℓ` and agrees there; the composite is unmasked at `ℓ`, where the end holds a `mut` cell
and `ρ₀` none. -/
theorem not_endpointMaskCompose : ¬ EndpointMaskCompose := by
  intro H
  let l : Loc := 0
  let S : WRes := ResU.single l (topMut Val.unit)
  have hvS : ResU.Valid S := valid_single_topMut l Val.unit
  have hv0 : ResU.Valid (PMap.empty : WRes) := ⟨_, flat_empty⟩
  have hnone0 : ∀ x ψ, ¬ ResU.FlatAt (PMap.empty : WRes) x ψ := by
    rintro x ψ ⟨σ, hσ, hg⟩
    obtain rfl := ResU.Flat.functional hσ flat_empty
    rw [PMap.empty_get] at hg
    cases hg
  have hnoneS : ∀ x ψ, x ∉ ({l} : Set Loc) → ¬ S.FlatAt x ψ := by
    rintro x ψ hx ⟨σ, hσ, hg⟩
    rw [flat_single_topMut hσ x (by simpa using hx)] at hg
    cases hg
  have h₁ : UpdVNm LocFam.empty 0 (∅ ∪ {l}) PMap.empty S := by
    refine ⟨⟨fun x hx s v χ h => ?_, fun x hx ψ hψ _ => ?_, fun x hx ψ hψ _ => ?_⟩, hv0, hvS⟩
    · rw [Set.empty_union] at hx
      exact ⟨fun h' => absurd h' (hnone0 _ _), fun h' => absurd h' (hnoneS _ _ hx)⟩
    · exact absurd hψ (hnone0 _ _)
    · rw [Set.empty_union] at hx
      exact absurd hψ (hnoneS _ _ hx)
  have h₂ : UpdVNm LocFam.empty 0 ({l} ∪ ∅) S S := UpdVNm.refl _ _ _ hvS
  have h₃ := H LocFam.empty 0 ∅ {l} ∅ PMap.empty S S h₁ h₂
  obtain ⟨σ, hσ⟩ := hvS
  obtain ⟨χ, hχ, hk, -, -⟩ := ResU.Flat.get hσ (show S.get l = some (topMut Val.unit) from
    by simp [S, ResU.single])
  obtain ⟨ψ, hψ, -⟩ := h₃.1.2.2 l (by simp) χ ⟨σ, hσ, hχ⟩
    (by rw [hk]; exact CellU.kind_mutOf _ _ _ _ _ _)
  exact hnone0 _ _ hψ

end BoCa.Fig16.LogRel.Core.Chain.SI

end

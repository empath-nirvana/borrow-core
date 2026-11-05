import Core.Chain.SI.LendAcross
import Core.Chain.SI.HeapN

/-!
# The heap primitives at `erwpX`  `[spec §62]`

`docs/new-core/scope-821-loans.md`, stage 2b. `rwpGX_of_rwp_own` lifts a run of `rwp` from a part
`ρ₀` whose flattening holds only `own` cells into `rwpGX`, beside the rest `ρ_r` of the resource and
the whole ghost `g`, at any mask. `↭` from `ρ₀` keeps every `imm` cell and every `mut` cell, so the
run's end and garbage hold none: the end carries no lifetime, the garbage is empty, and the ghost
is unchanged. This is the lift for a run that touches only owned cells; the general lift
`erwpX_of_erwp_tok`, which would also split the fractions that a released copy takes into the
garbage, is not built.

From it, at `erwpX` around an evaluation context: allocation (`erwpX_alloc`), release
(`erwpX_free`) and load (`erwpX_load`) of an owned cell. These are the continuation cell's
primitives (`HandleX`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont)

/-! ### A run that touches only owned cells -/

/-- `↭` from a resource holding only `own` cells reaches no `imm` cell. -/
theorem not_flatAt_imm_of_updVN_own {Φ : LocFam} {k : Nat} {ρ₀ π : WRes}
    (hown : ∀ l ψ, ρ₀.FlatAt l ψ → ψ.kind = Kind.own) (hU : UpdVN Φ k ρ₀ π) {l : Loc}
    {s : LSet} {w : Val} {χ : WRes} {hh : χ.InStratum s.join} :
    ¬ π.FlatAt l (CellU.immOf s w χ hh) := by
  intro hf
  have := hown l _ ((hU.1.1 l s w χ hh).mpr hf)
  simp at this

/-- …and no `mut` cell. -/
theorem not_flatAt_mut_of_updVN_own {Φ : LocFam} {k : Nat} {ρ₀ π : WRes}
    (hown : ∀ l ψ, ρ₀.FlatAt l ψ → ψ.kind = Kind.own) (hU : UpdVN Φ k ρ₀ π) {l : Loc}
    {ψ : CellU Loc Val} (hψ : π.FlatAt l ψ) : ψ.kind ≠ Kind.mut := by
  intro hk
  obtain ⟨ψ₀, h₀, hs⟩ := hU.1.2.2 l ψ hψ hk
  have := hown l ψ₀ h₀
  rw [hs.1] at this
  cases this

/-- A resource reaching no `imm` cell carries no lifetime. -/
theorem not_carries_of_no_imm {ρ : WRes}
    (h : ∀ l s w χ (hh : χ.InStratum s.join), ¬ ρ.FlatAt l (CellU.immOf s w χ hh)) (α : Life) :
    ¬ Carries ρ α := by
  rintro ⟨l, s, w, χ, hh, hf, -⟩
  exact h l s w χ hh hf

/-- **Garbage with no `own` cell, beside which the composite reaches only `own` cells, is
empty**: its `imm` and `mut` cells would be the composite's. -/
theorem eq_empty_of_noOwn_comp {ρ' ρp π : WRes} (hc : ResU.CompS ρ' ρp π) (hv : π.Valid)
    (hno : NoOwn ρp)
    (himm : ∀ l s w χ (hh : χ.InStratum s.join), ¬ π.FlatAt l (CellU.immOf s w χ hh))
    (hmut : ∀ l ψ, π.FlatAt l ψ → ψ.kind ≠ Kind.mut) : ρp = PMap.empty := by
  obtain ⟨σ, hσ⟩ := hv
  refine PMap.ext fun m => ?_
  cases hg : ρp.get m with
  | none => simp
  | some ψ =>
      exfalso
      have hko : ψ.kind ≠ Kind.own := by
        intro hk
        have hcc : (ρp.restrict Kind.own).get m = some ψ := ResU.restrict_eq_some.mpr ⟨hg, hk⟩
        rw [hno] at hcc
        simp at hcc
      -- the composite's cell at `m`, of `ψ`'s kind or `imm`
      have key : ∃ ζ, π.get m = some ζ ∧ ζ.kind ≠ Kind.own := by
        rcases ResU.Comp.get hc m with ⟨-, f₂, -⟩ | ⟨ζ, -, f₂, -⟩ | ⟨ζ, -, f₂, f⟩ |
            ⟨ζ₁, ζ₂, ζ, -, -, f, hC⟩
        · rw [hg] at f₂; cases f₂
        · rw [hg] at f₂; cases f₂
        · rw [hg] at f₂; cases Option.some.inj f₂; exact ⟨ψ, f, hko⟩
        · exact ⟨ζ, f, by rw [CellU.CompS.kind hC]; simp⟩
      obtain ⟨ζ, hζ, hkζ⟩ := key
      obtain ⟨χ, hχ, hk, -, -⟩ := ResU.Flat.get hσ hζ
      have hfl : π.FlatAt m χ := ⟨σ, hσ, hχ⟩
      cases hkχ : χ.kind with
      | own => exact hkζ (hk ▸ hkχ)
      | «mut» => exact hmut m χ hfl hkχ
      | imm =>
          obtain ⟨t, ht, hχeq⟩ := CellU.imm_eta hkχ
          rw [hχeq] at hfl
          exact himm m t _ _ _ hfl

/-- **A run of `rwp` that touches only owned cells, at `rwpGX`.** `ρ = ρ₀ ● ρ_r` with `ρ₀`'s
flattening holding only `own` cells; the run of `rwp` from `ρ₀` is the run from `ρ` at any mask,
`ρ_r` and the ghost `g` kept beside it, ending at the run's mask. -/
theorem rwpGX_of_rwp_own {Φ : LocFam} {M : Mask} {P : PostN} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ₀ ρr ρ : WRes} {g : GRes} (hown : ∀ l ψ, ρ₀.FlatAt l ψ → ψ.kind = Kind.own)
    (hcρ : ResU.CompS ρ₀ ρr ρ) (hwp : rwp (ℍ := ℍ) Φ P n ls e ρ₀) :
    rwpGX (ℍ := ℍ) Φ M (fun M' _ k ls' t x => M' = M ∧ x.2 = g ∧ ∃ v : Val, t = v.1 ∧
      ∃ ρ'₀, ResU.CompS ρ'₀ ρr x.1 ∧ P k ls' v ρ'₀) n ls e (ρ, g) := by
  intro xf fρ ps μ hf hc hv hwf hwx hsh hau hoff hT htg hl hfd j μ' e' hj hrun
  obtain ⟨y, hy, hy₁⟩ := (hash_shift xf.1 ρr ρ₀).mp ⟨ρ, ResU.CompS.comm hcρ, hf⟩
  obtain ⟨y', hy', hyfρ⟩ := compS_reassoc' (ResU.CompS.comm hcρ) hc
  cases ResU.CompS.functional hy' hy
  have hvρ : ρ.Valid := (hash_valid hf).2
  have hvy : y.Valid := (hash_valid hy₁).1
  obtain ⟨hG, hval, hprog⟩ := hwp y fρ ps μ hy₁ hyfρ hT htg hl hfd j μ' e' hj hrun
  refine ⟨hG.of_compS hy hvy, fun hfin => ?_⟩
  have hve : IsVal e' := by
    by_contra hn
    obtain ⟨_, _, hs⟩ := hprog hn
    exact hfin _ _ hs
  obtain ⟨ρ', ρp, Y', Y'p, π', ps', ls', g₁, g₂, g₃, g₆, g₇, g₉, gA, gB, gT, gtg, gps,
    gls, gC⟩ := hval ⟨e', hve⟩ rfl
  have hvπ' : π'.Valid := gA.2.2
  have himm := fun l s w χ hh => not_flatAt_imm_of_updVN_own (l := l) (s := s) (w := w)
    (χ := χ) (hh := hh) hown gA
  have hmut := fun l ψ hψ => not_flatAt_mut_of_updVN_own (l := l) (ψ := ψ) hown gA hψ
  obtain rfl : ρp = PMap.empty := eq_empty_of_noOwn_comp g₉ hvπ' gB himm hmut
  obtain rfl : ρ' = π' := ResU.eq_of_comp_empty_right g₉
  obtain rfl : Y' = Y'p := ResU.eq_of_comp_empty_right g₆
  -- `ρ_r` beside the end, as `rwp_frame`
  obtain ⟨W, hW, hfW⟩ := compS_reassoc hy g₂
  obtain ⟨W₀, hW₀, hWf₀⟩ := (hash_shift ρ' ρr xf.1).mp ⟨y, ResU.CompS.comm hy, g₁⟩
  have hWf : ResU.Hash W xf.1 := by
    rwa [ResU.CompS.functional (ResU.CompS.comm hW₀) hW] at hWf₀
  obtain ⟨-, hrρ'⟩ := ResU.Hash.split hy (ResU.hash_symm g₁)
  have hvW : W.Valid := (hash_valid hWf).1
  have hU : UpdVN Φ (n - j) ρ W :=
    updVNm_frame_empty (ResU.CompS.comm hcρ) hW
      ⟨(ResU.CompS.comm hcρ).1, ρ, ResU.CompS.comm hcρ, hvρ⟩ hrρ' gA
  have hshr : MaskShallow M.locs ρr := maskShallow_right hcρ hvρ hsh
  have hshW : MaskShallow M.locs W := by
    intro l hl s w χ hh hfW'
    rcases flatAt_comp_imm_split hW hfW' s.join_mem with
      ⟨s₁, h₁, hf₁, -⟩ | ⟨s₂, h₂, hf₂, -⟩
    · exact hshr l hl s₁ w χ h₁ hf₁
    · exact absurd hf₂ (himm l s₂ w χ h₂)
  have hwW : WFC (xf.2 + (g + 0)).counted (W, g) := by
    intro α hα hcW
    rcases carries_comp_split hW hcW with h' | h'
    · simp only [GRes.add_zero] at hα
      exact hwx α hα (carries_comp_right hcρ hvρ h')
    · exact absurd h' (not_carries_of_no_imm himm α)
  refine ⟨M, W, PMap.empty, Y', Y', W, g, 0, ps', ls', hWf, hfW, g₃, g₆, g₇,
    ResU.comp_empty_right _, ?_, gB, gT, gtg, RecAgree.of_iff gps, ListAgree.of_iff gls, ?_,
    ?_, hwW, ?_, maskShallow_fresh hshW (by simpa using flatNone_empty _), ?_, by simpa using hau,
    maskOff_emptyRes _, by simpa using maskShallow_empty _, by simpa using flatNone_empty _,
    rfl, rfl, ⟨e', hve⟩, rfl, ρ', ResU.CompS.comm hW, gC⟩
  · rw [Set.union_self]
    exact (updVNm_empty_iff.mpr hU).mono (Set.empty_subset _)
  · simpa using hv
  · intro α h₁ h₂; simp only [GRes.add_zero] at h₁; exact absurd h₁ h₂
  · intro α _ hc'; exact absurd hc' (not_carries_empty α)
  · rw [Set.union_self]; exact hshW

/-! ### At `erwpX`, around an evaluation context -/

theorem flat_own_only_empty :
    ∀ l (ψ : CellU Loc Val), ResU.FlatAt (PMap.empty : WRes) l ψ → ψ.kind = Kind.own := by
  rintro l ψ ⟨σ, hσ, hg⟩
  obtain rfl := ResU.Flat.functional hσ flat_empty
  rw [PMap.empty_get] at hg; cases hg

theorem flat_own_only_single (l : Loc) (v : Val) :
    ∀ m ψ, (ResU.single l (CellU.ownOf v)).FlatAt m ψ → ψ.kind = Kind.own := by
  rintro m ψ ⟨σ, hσ, hg⟩
  obtain rfl := ResU.Flat.functional hσ (ResU.flat_single_own l v)
  by_cases hm : m = l
  · subst hm; rw [ResU.single_get_self] at hg; cases Option.some.inj hg; simp
  · rw [ResU.single_get_ne _ hm] at hg; cases hg

/-- **An allocation at an evaluation position, in front of an `erwpX`**: `rwp_alloc` (6.141 at the
index) lifted, then bind; the rest of the run at the index the step left. -/
theorem erwpX_alloc {Φ : LocFam} (hΦ : Φ.Down) {M : Mask} {Tb : TableX} (hL : Tb.Local)
    {Q : PostX} (Kc : Kont) (v : Val) {n : Nat} {ls : List SRec} {ρ : WRes} {g : GRes}
    (h : ∀ (ℓ : Loc) (ρ' : WRes), ResU.CompS (ResU.single ℓ (CellU.ownOf v)) ρ ρ' →
      erwpX (ℍ := ℍ) Φ M Tb Q (n - 1) ls (Kc.plug (.val (Val.loc ℓ))) (ρ', g)) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls (Kc.plug (.app (.val (.prim .alloc)) (.val v))) (ρ, g) := by
  rw [erwpX_eq]
  refine rwpGX_bind hΦ Kc ?_
  have ha := rwp_alloc (ℍ := ℍ) (Φ := Φ) ls v
    (fun k ls' w ρ₀ => k = n - 1 ∧ ls' = ls ∧ ∃ ℓ : Loc, w = Val.loc ℓ ∧
      ρ₀ = ResU.single ℓ (CellU.ownOf v)) (n := n) (ρ := PMap.empty)
    (fun ℓ σ₁ σ₂ hp hc => by
      rw [hp] at hc
      exact ⟨rfl, rfl, ℓ, rfl, eq_of_compS_empty_left hc⟩)
  refine rwpGX_mono_le (fun M' C k hk ls' t x hx => ?_)
    (rwpGX_of_rwp_own (M := M) (g := g) flat_own_only_empty (compS_empty_left ρ) ha)
  obtain ⟨rfl, hg, w, rfl, ρ₀, hc₀, rfl, rfl, ℓ, rfl, rfl⟩ := hx
  obtain ⟨x₁, x₂⟩ := x
  simp only at hg hc₀
  subst hg
  exact Or.inl ⟨rfl, (erwpX_unfold_at hL hk (h ℓ x₁ hc₀)).at C⟩

/-- **A release of an owned cell at an evaluation position, in front of an `erwpX`.** -/
theorem erwpX_free {Φ : LocFam} (hΦ : Φ.Down) {M : Mask} {Tb : TableX} (hL : Tb.Local)
    {Q : PostX} (Kc : Kont) (ℓ : Loc) (v : Val) {n : Nat} {ls : List SRec} {ρ ρ₂ : WRes}
    {g : GRes} (hcρ : ResU.CompS (ResU.single ℓ (CellU.ownOf v)) ρ₂ ρ)
    (h : erwpX (ℍ := ℍ) Φ M Tb Q (n - 1) ls (Kc.plug (.val v)) (ρ₂, g)) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls (Kc.plug (BoLo.freeE (.val (Val.loc ℓ)))) (ρ, g) := by
  rw [erwpX_eq]
  refine rwpGX_bind hΦ Kc ?_
  have hf := rwp_free (ℍ := ℍ) (Φ := Φ) ls ℓ v
    (fun k ls' w ρ₀ => k = n - 1 ∧ ls' = ls ∧ w = v ∧ ρ₀ = PMap.empty) (n := n)
    (ρ := ResU.single ℓ (CellU.ownOf v))
    ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, rfl, rfl, rfl, rfl⟩
  refine rwpGX_mono_le (fun M' C k hk ls' t x hx => ?_)
    (rwpGX_of_rwp_own (M := M) (g := g) (flat_own_only_single ℓ v) hcρ hf)
  obtain ⟨rfl, hg, w, rfl, ρ₀, hc₀, rfl, rfl, rfl, rfl⟩ := hx
  obtain ⟨x₁, x₂⟩ := x
  simp only at hg hc₀
  subst hg
  have h₀ := eq_of_compS_empty_left hc₀
  subst h₀
  exact Or.inl ⟨rfl, (erwpX_unfold_at hL hk h).at C⟩

/-- **A load of an owned cell at an evaluation position, in front of an `erwpX`.** -/
theorem erwpX_load {Φ : LocFam} (hΦ : Φ.Down) {M : Mask} {Tb : TableX} (hL : Tb.Local)
    {Q : PostX} (Kc : Kont) (ℓ : Loc) (v : Val) {n : Nat} {ls : List SRec} {ρ ρ₂ : WRes}
    {g : GRes} (hcρ : ResU.CompS (ResU.single ℓ (CellU.ownOf v)) ρ₂ ρ)
    (h : erwpX (ℍ := ℍ) Φ M Tb Q (n - 1) ls (Kc.plug (.val v)) (ρ, g)) :
    erwpX (ℍ := ℍ) Φ M Tb Q n ls (Kc.plug (.app (.val (.prim .load)) (.val (Val.loc ℓ))))
      (ρ, g) := by
  rw [erwpX_eq]
  refine rwpGX_bind hΦ Kc ?_
  have hf := rwp_load (ℍ := ℍ) (Φ := Φ) ls ℓ v
    (fun k ls' w ρ₀ => k = n - 1 ∧ ls' = ls ∧ w = v ∧ ρ₀ = ResU.single ℓ (CellU.ownOf v))
    (n := n) (ρ := ResU.single ℓ (CellU.ownOf v))
    ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, fun σ₁ σ₂ hp hc => by
      rw [hp] at hc
      exact ⟨rfl, rfl, rfl, eq_of_compS_empty_left hc⟩⟩
  refine rwpGX_mono_le (fun M' C k hk ls' t x hx => ?_)
    (rwpGX_of_rwp_own (M := M) (g := g) (flat_own_only_single ℓ v) hcρ hf)
  obtain ⟨rfl, hg, w, rfl, ρ₀, hc₀, rfl, rfl, rfl, rfl⟩ := hx
  obtain ⟨x₁, x₂⟩ := x
  simp only at hg hc₀
  subst hg
  obtain rfl : ρ = x₁ := ResU.CompS.functional hcρ hc₀
  exact Or.inl ⟨rfl, (erwpX_unfold_at hL hk h).at C⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end

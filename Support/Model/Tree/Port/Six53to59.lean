import Support.Model.Tree.Port.Six43to46

/-!
# The printed source over the tree-stratified carrier

`[spec §62]`. `Paper/S6_2_NonStandardLemmas/Lemmas.lean:2694-3598`, read at `CellUT K`, by the printed proofs.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-!
## Lemma 6.53 · `[TR]` p. 18 · `proved*`

> If ρ ∈ reb_β(ρ′) and ρ_f # ℓ ↦ imm(α, ρ′, v) then ρ_f ▸◂ ρ.

**Printed proof, transcribed.** `dom(ρ) ⊆ dom(ρ′)` and `ρ∣own,mut = ∅`.  At `ℓ ∈ dom(ρ_f) ∩ dom(ρ)`, `ρ_f(ℓ)` can fail to compose with `ρ(ℓ)` only by being `own` or `mut`; but `ρ_f # ℓ ↦ imm(α, ρ′, v)`, unfolded with Lemmas 6.18, 6.20 and 6.30, gives `ex(ρ_f)_● ▸◂ ⦇ρ′⦈_○`, so that overlap never happens.

**Lean.** `BoCa.Fig16.Tree.ResUT.six53`, tag `[restricted: to `Tree.EscrowAgree ρ′ ρ (ag ρ_f)`]`.

**Note.** The added hypothesis is *"witnesses and values always stay the same"*, the sentence `[TR]` p. 18 asserts in the proof of 6.55 and `reb_α` does not carry (`docs/adjudications.md` §12.41); `Fig16.escrowAgree_self` inhabits it. At the repaired `wp`: discharged by `Fig16.LogRel.Typed.rebChooseO_top` and `Fig16.LogRel.Typed.rebChooseO_deep_tw` (§12.71).
-/
/-- `[TR]` Lemma 6.53 (p. 18). `[restricted: to `EscrowAgree ρ′ ρ (ag ρ_f)`, §12.41]` -/
theorem ResUT.six53 {β : Life} {ρ' ρ ρf : ResUT Loc Val K} {l₀ : Loc}
    {s : TSet} {v : Val} {hs : ρ'.InStratum s}
    (hreb : ResUT.Reb β ρ' ρ)
    (hag : ∀ a, AgWT ρf a → EscrowAgree ρ' ρ a)
    (hhash : ResUT.Hash ρf (ResUT.single l₀ (CellUT.immOf s v ρ' hs))) :
    ResUT.CompatS ρf ρ := by
  obtain ⟨-, ρc, hcomp, hval⟩ := hhash
  obtain ⟨aF, haF⟩ := ResUT.agW_of_hash_left hcomp hval
  intro l ψf ψ hf hg
  obtain ⟨φ, hφ⟩ := ResUT.reb_dom_subset hreb hg
  obtain ⟨hkf, hef, hwf⟩ := ResUT.frame_cell hcomp hval hf hφ
  by_cases hk : φ.kind = Kind.imm
  · -- the `imm` clause: the image cell is `imm` at the source's value and witness
    obtain ⟨hkψ, heψ, hwψ, -⟩ := ResUT.reb_imm_cell_kw hreb hg hφ hk
    exact CellUT.compatS_of hkf hkψ (hef.trans heψ.symm)
      (hwψ ▸ hwf (by rw [hk]; exact fun hc => Kind.noConfusion hc))
  · obtain ⟨vv, χ, hχs, hψeq, hvv, hor⟩ := ResUT.reb_src hreb hg hφ hk
    have hkψ : ψ.kind = Kind.imm := by rw [hψeq]; exact CellUT.kind_immOf _ _ _ _
    have hwψ : ψ.wit = χ := by rw [hψeq, CellUT.wit_immOf]
    have heψ : ψ.erase = φ.erase := by rw [hψeq, CellUT.erase_immOf, hvv]
    by_cases hown : φ.kind = Kind.own
    · -- the `own` clause: the escrow is fabricated, and `hag` is what pins it
      have hφo : ρ'.get l = some (CellUT.ownOf φ.erase) :=
        hφ.trans (congrArg some (CellUT.eq_ownOf_of_kind hown))
      obtain ⟨χf, hχf, hkχ, -, hwχ⟩ := AgWT.get_imm haF hf hkf
      exact CellUT.compatS_of hkf hkψ (hef.trans heψ.symm)
        (hwχ.symm.trans (hag aF haF l φ.erase ψ χf hφo hg hχf
          (by rw [hkψ]; exact fun c => Kind.noConfusion c)
          (by rw [hkχ]; exact fun c => Kind.noConfusion c)))
    · -- the `mut` clause: the witness is read off the cell
      have hmut : φ.wit = χ := hor.resolve_left hown
      exact CellUT.compatS_of hkf hkψ (hef.trans heψ.symm)
        (by rw [hwψ, ← hmut, hwf hown])

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-!
## Lemma 6.54 · `[TR]` p. 18 · `proved`

> If ρ ∈ reb_β(ρ′) and ✓ℓ ↦ imm(α, ρ′, v) then dom(ag(ρ)) ⊆ dom(⦇ρ′⦈_○)

**Printed proof, transcribed.** Unfolding `ρ ∈ reb_β(ρ′)`: `dom(ρ) ⊆ dom(ρ′)`; `ρ∣dom(ρ′∣imm) = ρ′∣imm∣dom(ρ)`; and for every `ℓ ∈ dom(ρ) ∩ dom(ρ′∣own,mut)` there is `ρ″` with `ρ(ℓ) = imm(_, ρ″, _)` and either `ρ″ ≤ ρ′` or `ρ′(ℓ) = mut(_, ρ″, _, _)`, so `dom(⦇ρ″⦈_○) ⊆ dom(⦇ρ′⦈_○)`.  Collecting these, every immutable borrow in `ρ` is in `⦇ρ′⦈_○`, and every witness is also in `⦇ρ⦈_○`.

**Lean.** `BoCa.Fig16.Tree.ResUT.six54`, tag `[as printed]`.
-/
/-- `[TR]` Lemma 6.54 (p. 18).  `[as printed]` (G4) -/
theorem ResUT.six54 {β : Life} {ρ' ρ A : ResUT Loc Val K} {l₀ : Loc} {s : TSet} {v : Val}
    {hs : ρ'.InStratum s}
    (hreb : ResUT.Reb β ρ' ρ)
    (hval : ResUT.Valid (ResUT.single l₀ (CellUT.immOf s v ρ' hs)))
    (hagρ : AgWT ρ A) :
    ∃ f, ResUT.FlatR ρ' f ∧ ∀ l ψ, A.get l = some ψ → ∃ φ, f.get l = some φ := by
  obtain ⟨f, hf⟩ := ResUT.flatR_of_valid_single_imm hval
  exact ⟨f, hf, fun l ψ hg => ResUT.ag_dom_of_reb hreb hagρ hf hg⟩

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-!
## Lemma 6.55 · `[TR]` p. 18 · `proved*`

> If ρ ∈ reb_β(ρ′) and ρ_f # ℓ ↦ imm(α, ρ′, v) then ρ_f # ρ.  As a corollary, ρ # ℓ ↦ imm(α, ρ′, v), which follows from setting ρ_f = ℓ ↦ imm(α, ρ′, v).

**Printed proof, transcribed.** Let `ρᵢ = imm(α, ρ′, v)`.  By Lemma 6.53, `ρ_f ▸◂ ρ`, so it suffices that `⦇ρ_f ● ρ⦈` is defined.  Unfolding the hypothesis with Lemmas 6.20 and 6.18 and the definitions of `ex` and `ag`, `⦇ρ_f ● ρᵢ⦈ = ex(ρ_f)_● ● ex(ρᵢ)_● ● (ag(ρ_f) ○ ag(ρᵢ)) = ex(ρ_f)_● ● (ag(ρ_f) ○ ρᵢ ○ ⦇ρ′⦈_○)`, all defined, and Lemma 6.30 with 6.36 gives `ex(ρ_f)_● ▸◂ ρᵢ ○ ⦇ρ′⦈_○`, `▸◂ ρᵢ` and `▸◂ ⦇ρ′⦈_○`.  Unfolding the goal the same way, with `dom(ρ∣own,mut) = ∅`, `⦇ρ_f ● ρ⦈ = ex(ρ_f)_● ● (ag(ρ_f) ○ ag(ρ))`; by Lemma 6.37 it suffices that `ag(ρ_f) ▷◁ ag(ρ)` and `ex(ρ_f)_● ▸◂ ag(ρ)`, and by Lemma 6.54 `dom(ag(ρ)) ⊆ dom(⦇ρ′⦈_○)`.  First, at a location of both, `ag(ρ_f) ▷◁ ⦇ρ′⦈_○`, and unfolding `reb`, `ρ` and `ρ′` differ only by potentially changing from `own` or `mut` to `imm`, "but witnesses and values always stay the same".  Second, `ex(ρ_f)_● ▸◂ ⦇ρ′⦈_○` with `ex(ρ_f)_●∣imm = ∅` makes their domains disjoint, and `dom(ag(ρ)) ⊆ dom(⦇ρ′⦈_○)`.

**Lean.** `BoCa.Fig16.Tree.ResUT.six55`, tag `[restricted: to `Tree.EscrowAgree ρ′ ρ (ag ρ_f)` and to `ag(ρ)` being defined]`.

**Note.** `EscrowAgree` as at 6.53 (§12.41); `ag(ρ)` being defined is presupposed by the printed proof's `ag(ρ_f) ▷◁ ag(ρ)` (F1).  The printed corollary is `Tree.ResUT.six55_self`.
-/
/-- `[TR]` Lemma 6.55 (p. 18). `[restricted: to `EscrowAgree ρ′ ρ (ag ρ_f)`, §12.41; to
`ag(ρ)` being defined, F1]` -/
theorem ResUT.six55 {β : Life} {ρ' ρ ρf A : ResUT Loc Val K} {l₀ : Loc}
    {s : TSet} {v : Val} {hs : ρ'.InStratum s}
    (hreb : ResUT.Reb β ρ' ρ)
    (hesc : ∀ a, AgWT ρf a → EscrowAgree ρ' ρ a)
    (hagρ : AgWT ρ A)
    (hhash : ResUT.Hash ρf (ResUT.single l₀ (CellUT.immOf s v ρ' hs))) :
    ResUT.Hash ρf ρ := by
  have hcs : ResUT.CompatS ρf ρ := ResUT.six53 hreb hesc hhash
  obtain ⟨-, ρc, hcomp, hval⟩ := hhash
  obtain ⟨e₁, aF, f, hex, haF, hfl, hEA, hEF, hAF⟩ := ResUT.frame_flat_facts hcomp hval
  have hb1 : ResUT.CompatR aF A :=
    ResUT.frame_compatR_ag hreb hagρ hfl hAF (hesc aF haF)
  have hb2 : ResUT.CompatS e₁ A := ResUT.frame_compatS_ag hreb hex hfl hEF hagρ
  obtain ⟨aa, haa⟩ := (ResUT.compR_defined_iff aF A).mpr hb1
  obtain ⟨σ, hσ⟩ := (ResUT.compS_defined_iff e₁ aa).mpr (ResUT.six37 hEA hb2 haa)
  obtain ⟨w, hw⟩ := (ResUT.compS_defined_iff ρf ρ).mpr hcs
  exact ⟨hcs, w, hw, σ, (ResUT.Flat.split hw).mpr ⟨e₁, PMap.empty, e₁, aF, A, aa,
    hex, ExWT.empty_of_all_imm (fun m ψ h => ResUT.reb_imm_image hreb h),
    ResUT.comp_empty_right e₁, haF, hagρ, haa, hσ⟩⟩

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-! `[about ours]` — for Lemma 6.56. -/
/-- `[TR]` 6.55's corollary (p. 18): *"As a corollary, `ρ # ℓ ↦ imm(α, ρ′, v)`, which
follows from setting `ρ_f = ℓ ↦ imm(α, ρ′, v)`."* `[restricted: as `ResUT.six55`]` -/
theorem ResUT.six55_self {β : Life} {ρ' ρ A : ResUT Loc Val K} {l₀ : Loc}
    {s : TSet} {v : Val} {hs : ρ'.InStratum s}
    (hreb : ResUT.Reb β ρ' ρ)
    (hesc : ∀ a, AgWT (ResUT.single l₀ (CellUT.immOf s v ρ' hs)) a → EscrowAgree ρ' ρ a)
    (hagρ : AgWT ρ A)
    (hhash : ResUT.Hash (ResUT.single l₀ (CellUT.immOf s v ρ' hs))
      (ResUT.single l₀ (CellUT.immOf s v ρ' hs))) :
    ResUT.Hash ρ (ResUT.single l₀ (CellUT.immOf s v ρ' hs)) :=
  ResUT.hash_symm (ResUT.six55 hreb hesc hagρ hhash)

/-- `[about ours: the printed `✓` of 6.55's corollary, in `#` form]` -/
theorem ResUT.hash_self_single_imm {l₀ : Loc} {s : TSet} {v : Val}
    {ρ' : ResUT Loc Val K} {hs : ρ'.InStratum s}
    (hval : ResUT.Valid (ResUT.single l₀ (CellUT.immOf s v ρ' hs))) :
    ResUT.Hash (ResUT.single l₀ (CellUT.immOf s v ρ' hs))
      (ResUT.single l₀ (CellUT.immOf s v ρ' hs)) := by
  have h₃ : ρ'.InStratum (s ∪ s) := ResUT.inStratum_union_iff.mpr ⟨hs, hs⟩
  have e : CellUT.immOf (s ∪ s) v ρ' h₃ = CellUT.immOf s v ρ' hs :=
    CellUT.immOf_congr (TSet.union_self s) rfl rfl h₃ hs
  have hcomp := ResUT.compS_single_imm l₀ s s v ρ' hs hs h₃
  rw [e] at hcomp
  exact ⟨hcomp.1, _, hcomp, hval⟩

/-!
## Lemma 6.56 · `[TR]` p. 19 · `proved*`

> If ρ ∈ reb_β(ρ′) and ✓(ℓ ↦ imm(α, ρ′, v)) then ⟦ρ∣dom(ρ′∣mut,own) ● ℓ ↦ imm(α, ρ′, v)⟧ = ⟦ℓ ↦ imm(α, ρ′, v)⟧

**Printed proof, transcribed.** By Lemma 6.55, `ρ # ℓ ↦ imm(α, ρ′, v)`; by Lemma 6.11, `ρ∣dom(ρ′∣mut,own) # ℓ ↦ imm(α, ρ′, v)`.  Pointwise: unfolding `⟦−⟧`, `⦇−⦈`, `ex` and `ag` and by Lemma 6.20, `⦇ρ∣dom(ρ′∣mut,own) ● ℓ ↦ imm(α, ρ′, v)⦈ = ag(ρ∣dom(ρ′∣mut,own) ● ℓ ↦ imm(α, ρ′, v)) = ag(ρ∣dom(ρ′∣mut,own)) ○ ℓ ↦ imm(α, ρ′, v) ○ ⦇ρ′⦈_○`.  By Lemma 6.54, `dom(⦇ρ∣dom(ρ′∣mut,own)⦈) ⊆ dom(⦇ρ′⦈)`; values and witnesses agree because `ρ∣dom(ρ′∣mut,own) # ℓ ↦ imm(α, ρ′, v)`, so the erasures agree.

**Lean.** `BoCa.Fig16.Tree.ResUT.six56`, tag `[restricted: as 6.55, which it spends]`.
-/
/-- `[TR]` Lemma 6.56 (p. 19). `[restricted: as `ResUT.six55`, which this spends]` -/
theorem ResUT.six56 {β : Life} {ρ' ρ A X : ResUT Loc Val K} {l₀ : Loc} {s : TSet}
    {v : Val} {hs : ρ'.InStratum s} {w : Loc → Option Val}
    (hreb : ResUT.Reb β ρ' ρ)
    (hesc : ∀ a, AgWT (ResUT.single l₀ (CellUT.immOf s v ρ' hs)) a → EscrowAgree ρ' ρ a)
    (hagρ : AgWT ρ A)
    (hval : ResUT.Valid (ResUT.single l₀ (CellUT.immOf s v ρ' hs)))
    (hX : ResUT.CompS (ρ.restrictDom (ρ'.exclPart))
        (ResUT.single l₀ (CellUT.immOf s v ρ' hs)) X) :
    ResUT.Lower X w ↔
      ResUT.Lower (ResUT.single l₀ (CellUT.immOf s v ρ' hs)) w := by
  -- `ρ_i # ρ_i`, from the printed `✓` and 6.43.
  -- 6.55's corollary, then 6.11.
  have hρi := ResUT.six55_self hreb hesc hagρ (ResUT.hash_self_single_imm hval)
  have hspl := ResUT.restrictDom_compS ρ (ρ'.exclPart)
  obtain ⟨-, τX, hτX, hvX⟩ := (ResUT.Hash.split hspl hρi).1
  rw [ResUT.CompS.functional hτX hX] at hvX
  -- `ex(−)●` is `∅` on both sides of the display.
  have himmi : ∀ l ψ, (ResUT.single l₀ (CellUT.immOf s v ρ' hs)).get l = some ψ →
      ψ.kind = Kind.imm := by
    intro l ψ h
    obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some h
    exact CellUT.kind_immOf _ _ _ _
  have hallX : ∀ l ψ, X.get l = some ψ → ψ.kind = Kind.imm := by
    intro l ψ he
    rcases ResUT.Comp.get hX l with ⟨-, -, e⟩ | ⟨ζ, e₁, -, e⟩ | ⟨ζ, -, e₂, e⟩ |
        ⟨ζ₁, ζ₂, ζ, e₁, e₂, e, hC⟩
    · rw [e] at he; exact absurd he (by simp)
    · rw [show ψ = ζ from Option.some.inj (he.symm.trans e)]
      exact ResUT.reb_imm_image hreb (ResUT.restrictDom_get_inv e₁)
    · rw [show ψ = ζ from Option.some.inj (he.symm.trans e)]
      exact himmi l ζ e₂
    · rw [show ψ = ζ from Option.some.inj (he.symm.trans e)]
      exact CellUT.CompS.kind hC
  have hei0 : ExST (ResUT.single l₀ (CellUT.immOf s v ρ' hs)) PMap.empty :=
    ExWT.empty_of_all_imm himmi
  have heX0 : ExST X PMap.empty := ExWT.empty_of_all_imm hallX
  -- `ag(ρ_i) = ρ_i ○ ⦇ρ′⦈_○`, and `ag(X) = ag(ρ|dom(σ)) ○ ag(ρ_i)`.
  obtain ⟨-, -, ai, -, hai, -⟩ := hval
  obtain ⟨-, -, aX, -, haX, -⟩ := hvX
  obtain ⟨ev, av, f, hev, hav, hf, hagi⟩ := AgWT.single_imm_inv hai
  have hflR : ResUT.FlatR ρ' f := ⟨av, ev, hav, hev, ResUT.CompR.comm hf⟩
  obtain ⟨aD, ai', haD, hai', hcD⟩ := (AgWT.split hX).mp haX
  rw [AgWT.functional hai' hai] at hcD
  -- 6.54: the extra factor adds no location.
  have hdomD : ∀ l ζ, aD.get l = some ζ → ∃ φ, ai.get l = some φ := by
    intro l ζ hζ
    obtain ⟨aD₂, aR, haD₂, -, hcA⟩ := (AgWT.split hspl).mp hagρ
    obtain rfl : aD₂ = aD := AgWT.functional haD₂ haD
    obtain ⟨φA, hφA⟩ := ResUT.Comp.dom_left hcA hζ
    obtain ⟨φf, hφf⟩ := ResUT.ag_dom_of_reb hreb hagρ hflR hφA
    exact ResUT.Comp.dom_right hagi hφf
  -- …and changes no erasure.
  have hmaps : ∀ l, (aX.get l).map CellUT.erase = (ai.get l).map CellUT.erase := by
    intro l
    rcases ResUT.Comp.get hcD l with ⟨-, e₂, e⟩ | ⟨ζ, e₁, e₂, -⟩ | ⟨ζ, -, e₂, e⟩ |
        ⟨ζ₁, ζ₂, ζ, -, e₂, e, hC⟩
    · rw [e, e₂]
    · obtain ⟨φ, hφ⟩ := hdomD l ζ e₁
      rw [e₂] at hφ
      exact absurd hφ (by simp)
    · rw [e, e₂]
    · rw [e, e₂]
      show some ζ.erase = some ζ₂.erase
      rw [CellUT.CompR.erase_right hC]
  have hflatX : ResUT.Flat X aX :=
    ⟨PMap.empty, aX, heX0, haX, ResUT.CompS.comm (ResUT.comp_empty_right aX)⟩
  have hflati : ResUT.Flat (ResUT.single l₀ (CellUT.immOf s v ρ' hs)) ai :=
    ⟨PMap.empty, ai, hei0, hai, ResUT.CompS.comm (ResUT.comp_empty_right ai)⟩
  constructor
  · rintro ⟨σ, hσ, hm⟩
    refine ⟨ai, hflati, fun l => ?_⟩
    rw [hm l, ResUT.Flat.functional hσ hflatX]
    exact hmaps l
  · rintro ⟨σ, hσ, hm⟩
    refine ⟨aX, hflatX, fun l => ?_⟩
    rw [hm l, ResUT.Flat.functional hσ hflati]
    exact (hmaps l).symm

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-!
## Lemma 6.57 · `[TR]` p. 19 · `proved*`

> Let ρᵢ = ℓ ↦ imm(α, ρ′ᵢ, v). If ρ ∈ reb_β(ρ′ᵢ), then ⦇ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ⦈ = ⦇ρᵢ⦈

**Printed proof, transcribed.** Unfolding `reb`, `ρ∣dom(ρ′ᵢ∣imm) ≤ ρ′ᵢ∣imm` and `ρ∣dom(ρ′ᵢ∣imm)∣mut,own = ∅`.  Writing `D = dom(ρ′ᵢ∣imm)` and unfolding `⦇−⦈`, `ex`, `ag` with Lemma 6.20: `⦇ρ∣D ● ρᵢ⦈ = ex(ρ∣D ● ρᵢ)_● ● ag(ρ∣D ● ρᵢ) = ag(ρ∣D ● ρᵢ) = ag(ρ∣D) ○ ag(ρᵢ) = ag(ρ∣D) ○ ρᵢ ○ ⦇ρ′ᵢ⦈_○ = ag(ρ∣D) ○ ⦇ρ′ᵢ∣imm⦈_○ ○ ρᵢ ○ ⦇ρ′ᵢ∣mut,own⦈_○ = ⦇ρ′ᵢ∣imm⦈_○ ○ ρᵢ ○ ⦇ρ′ᵢ∣mut,own⦈_○ = ρᵢ ○ ⦇ρ′ᵢ⦈_○ = ag(ρᵢ) = ⦇ρᵢ⦈`.

**Lean.** `BoCa.Fig16.Tree.ResUT.six57`, tag `[restricted: to `ag(ρ)` being defined]`.

**Note.** `ag(ρ)` being defined is presupposed by the printed display's `ag(ρ|dom(ρ′ᵢ|imm))` (F1).
-/
/-- `[TR]` Lemma 6.57 (p. 19). `[restricted: to `ag(ρ)` being defined, F1]` -/
theorem ResUT.six57 {β : Life} {ρ'i ρ A X σ : ResUT Loc Val K} {l₀ : Loc} {s : TSet}
    {v : Val} {hs : ρ'i.InStratum s}
    (hreb : ResUT.Reb β ρ'i ρ)
    (hagρ : AgWT ρ A)
    (hX : ResUT.CompS (ρ.restrictDom (G.restrict CellUT.kind ρ'i Kind.imm))
        (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) X) :
    ResUT.Flat X σ ↔ ResUT.Flat (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) σ := by
  have hR : ∀ ψ₁ ψ₂ ψ : CellUT Loc Val K, CellUT.CompR ψ₁ ψ₂ ψ → CellUT.CompatR ψ₁ ψ₂ :=
    fun _ _ ψ hc => ⟨ψ, hc⟩
  have himmi : ∀ l ψ, (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)).get l = some ψ →
      ψ.kind = Kind.imm := by
    intro l ψ h
    obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some h
    exact CellUT.kind_immOf _ _ _ _
  have hallX : ∀ l ψ, X.get l = some ψ → ψ.kind = Kind.imm := by
    intro l ψ he
    rcases ResUT.Comp.get hX l with ⟨-, -, e⟩ | ⟨ζ, e₁, -, e⟩ | ⟨ζ, -, e₂, e⟩ |
        ⟨ζ₁, ζ₂, ζ, e₁, e₂, e, hC⟩
    · rw [e] at he; exact absurd he (by simp)
    · rw [show ψ = ζ from Option.some.inj (he.symm.trans e)]
      exact ResUT.reb_imm_image hreb (ResUT.restrictDom_get_inv e₁)
    · rw [show ψ = ζ from Option.some.inj (he.symm.trans e)]
      exact himmi l ζ e₂
    · rw [show ψ = ζ from Option.some.inj (he.symm.trans e)]
      exact CellUT.CompS.kind hC
  have hFlat : ∀ Y : ResUT Loc Val K, ExST Y PMap.empty → ∀ τ,
      ResUT.Flat Y τ ↔ AgWT Y τ := by
    intro Y hY τ
    constructor
    · rintro ⟨e, a, he, ha, hcs⟩
      rw [ExST.functional he hY] at hcs
      rw [ResUT.CompS.functional hcs (ResUT.CompS.comm (ResUT.comp_empty_right a))]
      exact ha
    · intro ha
      exact ⟨PMap.empty, τ, hY, ha, ResUT.CompS.comm (ResUT.comp_empty_right τ)⟩
  rw [hFlat X (ExWT.empty_of_all_imm hallX) σ,
    hFlat _ (ExWT.empty_of_all_imm himmi) σ, AgWT.split hX]
  -- `ag(ρ|D)` has a value, by 6.20 at `ρ = ρ|dom(σ) ● ρ/dom(σ)`.
  have hspl := ResUT.restrictDom_compS ρ (G.restrict CellUT.kind ρ'i Kind.imm)
  obtain ⟨aD, aR, haD, -, -⟩ := (AgWT.split hspl).mp hagρ
  -- …and it absorbs `ag(ρᵢ)`.
  have habs : ∀ a₂, AgWT (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) a₂ →
      ResUT.CompR aD a₂ a₂ := fun a₂ ha₂ => ResUT.reb_immPart_ag_absorbs hreb haD ha₂
  constructor
  · rintro ⟨σ₁, σ₂, h₁, h₂, hc⟩
    rw [AgWT.functional h₁ haD] at hc
    rw [ResUT.CompR.functional hc (habs σ₂ h₂)]
    exact h₂
  · intro h₂
    exact ⟨aD, σ, haD, h₂, habs σ h₂⟩

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-!
## Lemma 6.58 · `[TR]` p. 19 · `proved*`

> Let ρᵢ = ℓ ↦ imm(α, ρ′ᵢ, v). If ρ ∈ reb_β(ρ′ᵢ), ρ ● ρ_b ↭ ρ′ ● ρ⁺, @ρ_b ⊐ β, @ρ′ ⊐ β, ρ_b # ρᵢ, and ρ′ ● ρ⁺ # ρᵢ, then ⟦ρ ● ρ_b ● ρᵢ⟧ = ⟦ρ_b ● ρᵢ⟧ and ⟦ρ′ ● ρ⁺ ● ρᵢ⟧ = ⟦ρ′ ● (ρ⁺ ⊟ ρ∣dom(ρ′ᵢ∣mut,own)) ● ρᵢ⟧

**Printed proof, transcribed.** By Lemma 6.56, (H1) `⟦ρ∣dom(ρ′ᵢ∣mut,own) ● ρᵢ⟧ = ⟦ρᵢ⟧`.  `dom(ρ) ⊆ dom(ρ′ᵢ)` by unfolding `reb`, and by Lemma 6.8, rewriting with H1, `⟦ρ ● ρᵢ⟧ = ⟦ρ∣dom(ρ′ᵢ∣imm) ● ρ∣dom(ρ′ᵢ∣mut,own) ● ρᵢ⟧ = ⟦ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ⟧`.  By Lemma 6.57 `⦇ρᵢ⦈ = ⦇ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ⦈`, so `⟦ρᵢ⟧ = ⟦ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ⟧`, which with the equation above gives (H2) `⟦ρ ● ρᵢ⟧ = ⟦ρᵢ⟧`.  The first conclusion is Lemma 6.8 with H2.  By Lemma 6.52, `ρ⁺ = (ρ⁺ ⊟ ρ∣dom(ρ′ᵢ∣mut,own)) ● ρ∣dom(ρ′ᵢ∣mut,own)`; rewriting, `⟦ρ′ ● ρ⁺ ● ρᵢ⟧ = ⟦ρ′ ● (ρ⁺ ⊟ ρ∣dom(ρ′ᵢ∣mut,own)) ● ρ∣dom(ρ′ᵢ∣mut,own) ● ρᵢ⟧`, and by that equation and Lemma 6.8 the second conclusion reduces to H1.

**Lean.** `BoCa.Fig16.Tree.ResUT.six58_left`; `BoCa.Fig16.Tree.ResUT.six58_right`; tag `[restricted: each to one of the two printed conclusions; as 6.55; `six58_right` also to `[TR]` 6.52's equation, as a hypothesis]`.
-/
/-- `[TR]` Lemma 6.58's first conclusion (p. 19). `[restricted: to the first of the two
printed conclusions, and as 6.55; the four printed hypotheses this half does not use
(`ρ ● ρ_b ↭ ρ′ ● ρ⁺`, `@ρ_b ⊐ β`, `@ρ′ ⊐ β`, `ρ′ ● ρ⁺ # ρᵢ`) are dropped, and `ρ # ρ_b`
(`hρb`) is added]` -/
theorem ResUT.six58_left {β : Life} {ρ'i ρ ρb A ρρb X Y : ResUT Loc Val K}
    {l₀ : Loc} {s : TSet} {v : Val} {hs : ρ'i.InStratum s}
    (hreb : ResUT.Reb β ρ'i ρ)
    (hesc : ∀ a, AgWT (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) a →
      EscrowAgree ρ'i ρ a)
    (hagρ : AgWT ρ A)
    (hρb : ResUT.Hash ρ ρb)
    (hbi : ResUT.Hash ρb (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)))
    (hrb : ResUT.CompS ρ ρb ρρb)
    (hX : ResUT.CompS ρρb (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) X)
    (hY : ResUT.CompS ρb (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) Y) :
    ∀ w, ResUT.Lower X w ↔ ResUT.Lower Y w := by
  have hvi : (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)).Valid := by
    obtain ⟨τ, hτ, hv⟩ := hbi.2
    exact (ResUT.Valid.split hτ hv).2
  have hρi := ResUT.six55_self hreb hesc hagρ (ResUT.hash_self_single_imm hvi)
  have hsp := ResUT.restrictDom_split hreb
  obtain ⟨hDiρi, hDmρi⟩ := ResUT.Hash.split hsp hρi
  have hvρ : ρ.Valid := by
    obtain ⟨τ, hτ, hv⟩ := hρi.2
    exact (ResUT.Valid.split hτ hv).1
  have hDiDm : ResUT.Hash (ρ.restrictDom (G.restrict CellUT.kind ρ'i Kind.imm))
      (ρ.restrictDom ρ'i.exclPart) := ⟨hsp.1, ρ, hsp, hvρ⟩
  obtain ⟨Zm, hZm, -⟩ := hDmρi.2
  obtain ⟨Zi, hZi, -⟩ := hDiρi.2
  have H1 : ∀ w, ResUT.Lower Zm w ↔
      ResUT.Lower (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) w :=
    fun w => ResUT.six56 hreb hesc hagρ hvi hZm
  have H57 : ∀ w, ResUT.Lower Zi w ↔
      ResUT.Lower (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) w := by
    refine fun w => ⟨?_, ?_⟩
    · rintro ⟨σ, hσ, hm⟩; exact ⟨σ, (ResUT.six57 hreb hagρ hZi).mp hσ, hm⟩
    · rintro ⟨σ, hσ, hm⟩; exact ⟨σ, (ResUT.six57 hreb hagρ hZi).mpr hσ, hm⟩
  have hDiZm := ResUT.hash_of_pairwise hDiDm hDmρi hDiρi hZm
  obtain ⟨W, hW⟩ :=
    (ResUT.compS_defined_iff (ρ.restrictDom (G.restrict CellUT.kind ρ'i Kind.imm)) Zm).mpr hDiZm.1
  have H8a := ResUT.lower_congr_iff H1 hW hDiZm hZi hDiρi
  obtain ⟨R, hR⟩ :=
    (ResUT.compS_defined_iff ρ (ResUT.single l₀ (CellUT.immOf s v ρ'i hs))).mpr hρi.1
  have hWR : W = R := by
    obtain ⟨y, hy, hyR⟩ :=
      (ResUT.CompS.assoc (ρ.restrictDom (G.restrict CellUT.kind ρ'i Kind.imm))
        (ρ.restrictDom ρ'i.exclPart) (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) W).mp
        ⟨Zm, hZm, hW⟩
    rw [ResUT.CompS.functional hy hsp] at hyR
    exact ResUT.CompS.functional hyR hR
  have H2 : ∀ w, ResUT.Lower R w ↔
      ResUT.Lower (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) w := by
    rw [← hWR]
    exact fun w => (H8a w).trans (H57 w)
  have hbR := ResUT.hash_of_pairwise (ResUT.hash_symm hρb) hρi hbi hR
  obtain ⟨V, hV⟩ := (ResUT.compS_defined_iff ρb R).mpr hbR.1
  have H8b := ResUT.lower_congr_iff H2 hV hbR hY hbi
  have hVX : V = X := by
    obtain ⟨y, hy, hyV⟩ :=
      (ResUT.CompS.assoc ρb ρ (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) V).mp ⟨R, hR, hV⟩
    rw [ResUT.CompS.functional hy (ResUT.CompS.comm hrb)] at hyV
    exact ResUT.CompS.functional hyV hX
  rw [← hVX]
  exact H8b

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-- `[TR]` Lemma 6.58's second conclusion (p. 19). `[restricted: to the second of the
two printed conclusions; to `[TR]` 6.52's equation, taken as a hypothesis at the `χ`
the statement binds; and as 6.55]` -/
theorem ResUT.six58_right {β : Life} {ρ'i ρ ρ'' ρp χ A ρ'p ρ'χ P Q : ResUT Loc Val K}
    {l₀ : Loc} {s : TSet} {v : Val} {hs : ρ'i.InStratum s}
    (hreb : ResUT.Reb β ρ'i ρ)
    (hesc : ∀ a, AgWT (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) a →
      EscrowAgree ρ'i ρ a)
    (hagρ : AgWT ρ A)
    (hpi : ResUT.Hash ρ'p (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)))
    (hcp : ResUT.CompS ρ'' ρp ρ'p)
    (_hsub : ResUT.Sub ρp (ρ.restrictDom ρ'i.exclPart) χ)
    (hsplit : ResUT.CompS χ (ρ.restrictDom ρ'i.exclPart) ρp)
    (hcχ : ResUT.CompS ρ'' χ ρ'χ)
    (hP : ResUT.CompS ρ'p (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) P)
    (hQ : ResUT.CompS ρ'χ (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) Q) :
    ∀ w, ResUT.Lower P w ↔ ResUT.Lower Q w := by
  have hvi : (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)).Valid := by
    obtain ⟨τ, hτ, hv⟩ := hpi.2
    exact (ResUT.Valid.split hτ hv).2
  have hρi := ResUT.six55_self hreb hesc hagρ (ResUT.hash_self_single_imm hvi)
  obtain ⟨-, hDmρi⟩ := ResUT.Hash.split (ResUT.restrictDom_split hreb) hρi
  obtain ⟨Zm, hZm, -⟩ := hDmρi.2
  have H1 : ∀ w, ResUT.Lower Zm w ↔
      ResUT.Lower (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) w :=
    fun w => ResUT.six56 hreb hesc hagρ hvi hZm
  -- `ρ′ ● ρ⁺ = (ρ′ ● χ) ● ρ|dom(ρ′ᵢ|mut,own)`
  have hmid : ResUT.CompS ρ'χ (ρ.restrictDom ρ'i.exclPart) ρ'p := by
    obtain ⟨y, hy, hyp⟩ :=
      (ResUT.CompS.assoc ρ'' χ (ρ.restrictDom ρ'i.exclPart) ρ'p).mp ⟨ρp, hsplit, hcp⟩
    rwa [ResUT.CompS.functional hy hcχ] at hyp
  obtain ⟨hχi, hDmi⟩ := ResUT.Hash.split hmid hpi
  have hvp : ρ'p.Valid := by
    obtain ⟨τ, hτ, hv⟩ := hpi.2
    exact (ResUT.Valid.split hτ hv).1
  have hχDm : ResUT.Hash ρ'χ (ρ.restrictDom ρ'i.exclPart) := ⟨hmid.1, ρ'p, hmid, hvp⟩
  have hχZm := ResUT.hash_of_pairwise hχDm hDmi hχi hZm
  -- `ρ′ ● ρ⁺ ● ρᵢ = (ρ′ ● χ) ● (ρ|dom(ρ′ᵢ|mut,own) ● ρᵢ)`
  have hPZ : ResUT.CompS ρ'χ Zm P := by
    obtain ⟨x, hx, hxP⟩ :=
      (ResUT.CompS.assoc ρ'χ (ρ.restrictDom ρ'i.exclPart)
        (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) P).mpr ⟨ρ'p, hmid, hP⟩
    rwa [ResUT.CompS.functional hx hZm] at hxP
  exact ResUT.lower_congr_iff H1 hPZ hχZm hQ hχi

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
variable {β : Life} {ρ'i ρ L R Lreb Rreb : ResUT BoCa.Loc BoCa.Val K}
  {aL aR areb ai aLr aRr aX aY eLr eRr σL σR : ResUT BoCa.Loc BoCa.Val K}
  {l₀ : BoCa.Loc} {s : TSet} {v : BoCa.Val} {hs : ρ'i.InStratum s}
  {es as pS : ResUT BoCa.Loc BoCa.Val K}

/-! `[about ours]` — for Lemma 6.59. -/
/-- Step 2's first branch, at every ancestor at once: an `imm` cell of `ag(L)` is
absorbed by the goal's other side.  `[about ours: `[TR]` 6.59's closing sentence at
an `imm` cell of `ag(L)`]` -/
theorem ResUT.reb_frame_absImm
    (hreb : ResUT.Reb β ρ'i ρ)
    (hL : L.InStratum (TSet.single β))
    (hupd : ResUT.Upd Lreb Rreb)
    (haL : AgWT L aL)
    (hareb : AgWT (ρ.restrictDom ρ'i.exclPart) areb)
    (hai : AgWT (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) ai)
    (hexS : ExRT ρ'i es) (hagS : AgWT ρ'i as) (hfS : ResUT.CompR es as pS)
    (hcLr : ResUT.CompR aL areb aLr) (hcRr : ResUT.CompR aR areb aRr)
    (hcRi : ResUT.CompR aR ai aY)
    (haLr : AgWT Lreb aLr) (haRr : AgWT Rreb aRr)
    (heLr : ExST Lreb eLr) (heRr : ExST Rreb eRr)
    (hfL : ResUT.CompS eLr aLr σL) (hfR : ResUT.CompS eRr aRr σR) :
    AgWT.AbsImm aL aY := by
  classical
  obtain ⟨bi, hbi, hbile⟩ := ResUT.reb_ag_split hreb hareb hai hexS hagS hfS
  -- `ag(R) ○ bi` is defined, and `ag(R) ○ bi ○ ρ_reb = ag(R ● ρ_reb)`
  obtain ⟨y, hy₁, hy₂⟩ :=
    (ResUT.CompR.assoc aR bi (ρ.restrictDom ρ'i.exclPart) aRr).mp
      ⟨areb, ResUT.CompR.comm hbi, hcRr⟩
  have hyY : ResUT.CompR y aY aY :=
    ResUT.CompR.absorb_comp hy₁ (ResUT.LeR.left hcRi).absorb
      (ResUT.LeR.trans hbile (ResUT.LeR.right hcRi)).absorb
  intro m ψ hgm hk
  have hstr : ψ.InStratum (TSet.single β) := BoLo.AgWT.inStratum haL (TSet.single β) hL m ψ hgm
  obtain ⟨ψt, hψt, hψle⟩ := (ResUT.LeR.left hcLr).get_some hgm
  have hψtk : ψt.kind = Kind.imm := by
    obtain ⟨t, ht, e⟩ := CellUT.imm_eta hk
    obtain ⟨t', h', e'⟩ := CellUT.CompR.imm_left_eq hψle e
    rw [e']; exact CellUT.kind_immOf _ _ _ _
  have hRrm : aRr.get m = some ψt :=
    ResUT.upd_ag_eq_of_ne_own hupd heLr haLr hfL heRr haRr hfR hψt
      (by rw [hψtk]; exact fun c => Kind.noConfusion c)
  -- `ψ` is absorbed by `(ag(R) ○ bi)(m)`, the `{β}` cancelling off
  have habs : ∃ d, y.get m = some d ∧ CellUT.CompR ψ d d := by
    have hdec := hy₂.2 m
    rw [hRrm] at hdec
    cases hr : (ρ.restrictDom ρ'i.exclPart).get m with
    | none =>
        rw [hr] at hdec
        cases hyg : y.get m with
        | none =>
            rw [hyg] at hdec
            exact absurd (show (some ψt : Option (CellUT BoCa.Loc BoCa.Val K)) = none
              from hdec) (by simp)
        | some d =>
            rw [hyg] at hdec
            obtain rfl : ψt = d :=
              Option.some.inj (show (some ψt : Option (CellUT BoCa.Loc BoCa.Val K))
                = some d from hdec)
            exact ⟨_, rfl, hψle⟩
    | some B =>
        rw [hr] at hdec
        obtain ⟨φ', hφ'⟩ := ResUT.restrictDom_dom hr
        obtain ⟨hφ'g, hφ'k⟩ := ResUT.exclPart_eq_some.mp hφ'
        obtain ⟨vm, χm, hχm, hBeq, -, -⟩ :=
          ResUT.reb_src hreb (ResUT.restrictDom_get_inv hr) hφ'g hφ'k
        subst hBeq
        cases hyg : y.get m with
        | none =>
            rw [hyg] at hdec
            obtain rfl : ψt = CellUT.immOf (TSet.single β) vm χm hχm :=
              Option.some.inj hdec
            exact absurd rfl (CellUT.reb_frame_imm_ne_singleton hψle hstr hk)
        | some d =>
            rw [hyg] at hdec
            obtain ⟨e, he, hde⟩ := hdec
            obtain rfl : ψt = e := Option.some.inj he
            exact ⟨d, rfl, CellUT.reb_frame_imm_le hstr hk hde hψle⟩
  obtain ⟨d, hd, hψd⟩ := habs
  obtain ⟨c, hc, hdc⟩ := (ResUT.LeR.left hyY).get_some hd
  exact ⟨c, hc, CellUT.CompR.absorb_transC hψd hdc⟩

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {β : Life} {ρ'i ρ L R Lreb Rreb : ResUT BoCa.Loc BoCa.Val K}
  {aL aR areb ai aLr aRr aX aY eLr eRr σL σR : ResUT BoCa.Loc BoCa.Val K}
  {l₀ : BoCa.Loc} {s : TSet} {v : BoCa.Val} {hs : ρ'i.InStratum s}
  {es as pS : ResUT BoCa.Loc BoCa.Val K}

/-- Steps 3 and 4, at every ancestor at once: the whole `⦇κ⦈_○` under an `imm` cell of
`ag(L)` is a `○`-factor of the goal's other side.  `[about ours: `[TR]` 6.48's
ancestor step run at every ancestor of `ag(L)`]` -/
theorem ResUT.reb_frame_absAnc
    (hreb : ResUT.Reb β ρ'i ρ)
    (hupd : ResUT.Upd Lreb Rreb)
    (haR : AgWT R aR)
    (hareb : AgWT (ρ.restrictDom ρ'i.exclPart) areb)
    (hai : AgWT (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) ai)
    (hexS : ExRT ρ'i es) (hagS : AgWT ρ'i as) (hfS : ResUT.CompR es as pS)
    (hcLr : ResUT.CompR aL areb aLr) (hcRr : ResUT.CompR aR areb aRr)
    (hcRi : ResUT.CompR aR ai aY)
    (haLr : AgWT Lreb aLr) (haRr : AgWT Rreb aRr)
    (heLr : ExST Lreb eLr) (heRr : ExST Rreb eRr)
    (hfL : ResUT.CompS eLr aLr σL) (hfR : ResUT.CompS eRr aRr σR) :
    AgWT.AbsAnc aL aY := by
  intro m t u κ hh hgm ev av p hev hav hp
  obtain ⟨t₁, h₁, hLrm⟩ := ResUT.CompR.imm_left_get hcLr hgm
  have hRrm : aRr.get m = some (CellUT.immOf t₁ u κ h₁) :=
    ResUT.upd_ag_eq_of_ne_own hupd heLr haLr hfL heRr haRr hfR hLrm
      (by rw [CellUT.kind_immOf]; exact fun c => Kind.noConfusion c)
  obtain ⟨ev', av', p', z, hev', hav', hp', hz⟩ :=
    ResUT.reb_attribute hreb haR hareb hai hexS hagS hfS hcRr hcRi hRrm
  cases ExRT.functional hev' hev
  cases AgWT.functional hav' hav
  cases ResUT.CompR.functional hp' hp
  exact (ResUT.LeR.left hz).absorb

/-- `ag(L)` is absorbed by `ag(R) ○ ag(ρᵢ)`.  `[about ours: `[TR]` 6.59's closing
sentence as a `≼` between the two walks]` -/
theorem ResUT.reb_frame_ag_le
    (hreb : ResUT.Reb β ρ'i ρ)
    (hL : L.InStratum (TSet.single β))
    (hupd : ResUT.Upd Lreb Rreb)
    (haL : AgWT L aL) (haR : AgWT R aR)
    (hareb : AgWT (ρ.restrictDom ρ'i.exclPart) areb)
    (hai : AgWT (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) ai)
    (hexS : ExRT ρ'i es) (hagS : AgWT ρ'i as) (hfS : ResUT.CompR es as pS)
    (hcLr : ResUT.CompR aL areb aLr) (hcRr : ResUT.CompR aR areb aRr)
    (hcRi : ResUT.CompR aR ai aY)
    (haLr : AgWT Lreb aLr) (haRr : AgWT Rreb aRr)
    (heLr : ExST Lreb eLr) (heRr : ExST Rreb eRr)
    (hfL : ResUT.CompS eLr aLr σL) (hfR : ResUT.CompS eRr aRr σR) :
    ResUT.CompR aL aY aY :=
  AgWT.absorb_of_ancestors haL aY
    (ResUT.reb_frame_absImm hreb hL hupd haL hareb hai hexS hagS hfS hcLr hcRr
      hcRi haLr haRr heLr heRr hfL hfR)
    (ResUT.reb_frame_absAnc hreb hupd haR hareb hai hexS hagS hfS hcLr hcRr
      hcRi haLr haRr heLr heRr hfL hfR)

/-- `[TR]` 6.59's closing sentence.  `[about ours: `[TR]` 6.59's closing sentence at the
two aliasable walks]` -/
theorem ResUT.reb_frame_ag_eq
    (hreb : ResUT.Reb β ρ'i ρ)
    (hL : L.InStratum (TSet.single β)) (hR : R.InStratum (TSet.single β))
    (hupd : ResUT.Upd Lreb Rreb)
    (haL : AgWT L aL) (haR : AgWT R aR)
    (hareb : AgWT (ρ.restrictDom ρ'i.exclPart) areb)
    (hai : AgWT (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) ai)
    (hexS : ExRT ρ'i es) (hagS : AgWT ρ'i as) (hfS : ResUT.CompR es as pS)
    (hcLr : ResUT.CompR aL areb aLr) (hcRr : ResUT.CompR aR areb aRr)
    (hcLi : ResUT.CompR aL ai aX) (hcRi : ResUT.CompR aR ai aY)
    (haLr : AgWT Lreb aLr) (haRr : AgWT Rreb aRr)
    (heLr : ExST Lreb eLr) (heRr : ExST Rreb eRr)
    (hfL : ResUT.CompS eLr aLr σL) (hfR : ResUT.CompS eRr aRr σR) :
    aX = aY := by
  have h1 : ResUT.CompR aL aY aY :=
    ResUT.reb_frame_ag_le hreb hL hupd haL haR hareb hai hexS hagS hfS
      hcLr hcRr hcRi haLr haRr heLr heRr hfL hfR
  have h2 : ResUT.CompR aR aX aX :=
    ResUT.reb_frame_ag_le hreb hR hupd.symm haR haL hareb hai hexS hagS hfS
      hcRr hcLr hcLi haRr haLr heRr heLr hfR hfL
  have hXY : ResUT.CompR aX aY aY :=
    ResUT.CompR.absorb_comp hcLi h1 (ResUT.LeR.right hcRi).absorb
  have hYX : ResUT.CompR aY aX aX :=
    ResUT.CompR.absorb_comp hcRi h2 (ResUT.LeR.right hcLi).absorb
  exact (ResUT.CompR.functional (ResUT.CompR.comm hXY) hYX).symm

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-- `[TR]` 6.59's two sides have one aliasable walk, and where it is silent so is each
side of the update hypothesis.  `[about ours: `[TR]` 6.59's step 4 at the walks,
before the print's case split]` -/
theorem ResUT.six59_ag_eq
    {β : Life} {ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : ResUT BoCa.Loc BoCa.Val K}
    {l₀ : BoCa.Loc} {s : TSet} {v : BoCa.Val} {hs : ρ'i.InStratum s}
    (hreb : ResUT.Reb β ρ'i ρ)
    (hce : ResUT.CompS ρ ρb ρρb)
    (hcp : ResUT.CompS ρ' ρp ρ'p)
    (hupd : ResUT.UpdV ρρb ρ'p)
    (hsb : ρb.InStratum (TSet.single β))
    (hs' : ρ'.InStratum (TSet.single β))
    (hsplit : ResUT.CompS χ (ρ.restrictDom ρ'i.exclPart) ρp)
    (hχβ : χ.InStratum (TSet.single β))
    (hXc : ResUT.CompS (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) ρb Xi)
    (hYc : ∃ w, ResUT.CompS ρ' χ w ∧
      ResUT.CompS w (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) Y)
    (hfX : ResUT.Flat Xi σX) (hfY : ResUT.Flat Y σY) :
    ∃ a, AgWT Xi a ∧ AgWT Y a ∧
      ∀ aL aR, AgWT ρρb aL → AgWT ρ'p aR →
        ∀ l, a.get l = none → aL.get l = none ∧ aR.get l = none := by
  classical
  obtain ⟨eX, aXi, heX, haXi, hfX'⟩ := hfX
  obtain ⟨ai, ab, hai, hab, hXag⟩ := (AgWT.split hXc).mp haXi
  obtain ⟨eY, aY, heY, haY, hfY'⟩ := hfY
  obtain ⟨R, hRw, hYw⟩ := hYc
  obtain ⟨aR, ai₁, haR, hai₁, hYag⟩ := (AgWT.split hYw).mp haY
  cases AgWT.functional hai₁ hai
  -- the hypothesis's two walks
  obtain ⟨σL, eLr, aLr, heLr, haLr, hfL⟩ := hupd.2.1
  obtain ⟨σR, eRr, aRr, heRr, haRr, hfR⟩ := hupd.2.2
  obtain ⟨aρ, ab₁, haρ, hab₁, hLag⟩ := (AgWT.split hce).mp haLr
  cases AgWT.functional hab₁ hab
  obtain ⟨aρ', aρp, haρ', haρp, hRag⟩ := (AgWT.split hcp).mp haRr
  -- `ρ = ρ|dom(ρ′ᵢ|imm) ● ρ_reb`
  have hDsplit := ResUT.restrictDom_split hreb
  obtain ⟨aD, areb, haD, hareb, hDag⟩ := (AgWT.split hDsplit).mp haρ
  obtain ⟨aχ, areb₁, haχ, hareb₁, hPag⟩ := (AgWT.split hsplit).mp haρp
  cases AgWT.functional hareb₁ hareb
  -- `ag(L) = ag(ρ|dom(ρ′ᵢ|imm)) ○ ag(ρ_b)`, and `ag(L) ○ ag(ρ_reb) = ag(ρ ● ρ_b)`
  obtain ⟨x, hx₁, hx₂⟩ :=
    (ResUT.CompR.assoc aD areb ab aLr).mpr ⟨aρ, hDag, hLag⟩
  obtain ⟨aL, hcDab, hcLareb⟩ :=
    (ResUT.CompR.assoc aD ab areb aLr).mp ⟨x, ResUT.CompR.comm hx₁, hx₂⟩
  -- and `L = ρ|dom(ρ′ᵢ|imm) ● ρ_b` is a resource
  obtain ⟨z, hz₁, hz₂⟩ :=
    (ResUT.CompS.assoc (ρ.restrictDom (G.restrict CellUT.kind ρ'i Kind.imm))
      (ρ.restrictDom ρ'i.exclPart) ρb ρρb).mpr ⟨ρ, hDsplit, hce⟩
  obtain ⟨L, hLc, hLreb⟩ :=
    (ResUT.CompS.assoc (ρ.restrictDom (G.restrict CellUT.kind ρ'i Kind.imm)) ρb
      (ρ.restrictDom ρ'i.exclPart) ρρb).mp ⟨z, ResUT.CompS.comm hz₁, hz₂⟩
  have haLW : AgWT L aL := (AgWT.split hLc).mpr ⟨aD, ab, haD, hab, hcDab⟩
  have hLstr : L.InStratum (TSet.single β) :=
    ResUT.CompS.inStratum hLc (ResUT.reb_immPart_inStratum hreb) hsb
  -- `ag(R) ○ ag(ρ_reb) = ag(ρ′ ● ρ⁺)`
  obtain ⟨aR₀, hcR₀, hcRareb⟩ :=
    (ResUT.CompR.assoc aρ' aχ areb aRr).mp ⟨aρp, hPag, hRag⟩
  obtain ⟨b₁, b₂, hb₁, hb₂, hbc⟩ := (AgWT.split hRw).mp haR
  cases AgWT.functional hb₁ haρ'
  cases AgWT.functional hb₂ haχ
  cases ResUT.CompR.functional hbc hcR₀
  have hRstr : R.InStratum (TSet.single β) := ResUT.CompS.inStratum hRw hs' hχβ
  -- `ρᵢ`'s own walks
  obtain ⟨es, as, pS, hexS, hagS, hfS, hagi⟩ := AgWT.single_imm_inv hai
  -- `ag(L) ○ ag(ρᵢ) = ag(ρᵢ ● ρ_b)`, because `ag(ρ|dom(ρ′ᵢ|imm)) ≼ ag(ρᵢ)`
  have hDai : ResUT.CompR aD ai ai := ResUT.reb_immPart_ag_absorbs hreb haD hai
  have hDaXi : ResUT.CompR aD aXi aXi :=
    (ResUT.LeR.trans ⟨ai, hDai⟩ (ResUT.LeR.left hXag)).absorb
  obtain ⟨y, hy₁, hy₂⟩ :=
    (ResUT.CompR.assoc aD ab ai aXi).mp ⟨aXi, ResUT.CompR.comm hXag, hDaXi⟩
  cases ResUT.CompR.functional hy₁ hcDab
  -- `[TR]` 6.59's closing sentence
  have heq : aXi = aY :=
    ResUT.reb_frame_ag_eq hreb hLstr hRstr hupd.1 haLW haR hareb hai hexS hagS hfS
      hcLareb hcRareb hy₂ hYag haLr haRr heLr heRr hfL hfR
  subst heq
  refine ⟨aXi, haXi, haY, fun aL' aR' haL' haR' l hn => ?_⟩
  cases AgWT.functional haL' haLr
  cases AgWT.functional haR' haRr
  -- where the goal's one walk is silent, so is every factor of it
  obtain ⟨hain, habn⟩ := (ResUT.Comp.eq_none_iff hXag l).mp hn
  obtain ⟨haRn, -⟩ := (ResUT.Comp.eq_none_iff hYag l).mp hn
  obtain ⟨haDn, -⟩ := (ResUT.Comp.eq_none_iff hDai l).mp hain
  -- …and `ρ_reb` cannot stand there, since `ag(ρᵢ)` would
  have hrebn : (ρ.restrictDom ρ'i.exclPart).get l = none := by
    cases hr : (ρ.restrictDom ρ'i.exclPart).get l with
    | none => rfl
    | some ζ =>
        obtain ⟨c, hc⟩ := ResUT.ag_single_imm_some_of_reb hai hr
        rw [hain] at hc; exact absurd hc (by simp)
  have harebn : areb.get l = none := by
    cases hg : areb.get l with
    | none => rfl
    | some ψ =>
        obtain ⟨φ, hφ, -⟩ :=
          ResUT.reb_ag_cell_absorbed_off_dom hreb hareb hai hexS hagS hfS hrebn hg
        rw [hain] at hφ; exact absurd hφ (by simp)
  obtain ⟨haρ'n, haχn⟩ := (ResUT.Comp.eq_none_iff hcR₀ l).mp haRn
  have hnone₂ : ∀ {c₁ c₂ c : ResUT BoCa.Loc BoCa.Val K}, ResUT.CompR c₁ c₂ c →
      c₁.get l = none → c₂.get l = none → c.get l = none := by
    intro c₁ c₂ c hc h₁ h₂
    have := hc.2 l
    rw [h₁, h₂] at this
    exact this
  exact ⟨hnone₂ hLag (hnone₂ hDag haDn harebn) habn,
    hnone₂ hRag haρ'n (hnone₂ hPag haχn harebn)⟩

/-- `[TR]` 6.59's step 6 at a reborrowed `ℓ`. `[restricted: to `[TR]` 6.52's two
conclusions, taken as named hypotheses at the `χ` the statement binds — *"By lemma
6.52, `ρ⁺ = (ρ⁺ ⊟ ρ_reb) ● ρ_reb`, and `@(ρ⁺ ⊟ ρ_reb) ⊐ β`"* (p. 20); `ResUT.six52`
inhabits them]` -/
theorem ResUT.six59_residual_at
    {β : Life} {ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : ResUT BoCa.Loc BoCa.Val K}
    {l₀ : BoCa.Loc} {s : TSet} {v : BoCa.Val} {hs : ρ'i.InStratum s}
    (hreb : ResUT.Reb β ρ'i ρ)
    (hce : ResUT.CompS ρ ρb ρρb)
    (hcp : ResUT.CompS ρ' ρp ρ'p)
    (hupd : ResUT.UpdV ρρb ρ'p)
    (hsb : ρb.InStratum (TSet.single β))
    (hs' : ρ'.InStratum (TSet.single β))
    (hsplit : ResUT.CompS χ (ρ.restrictDom ρ'i.exclPart) ρp)
    (hχβ : χ.InStratum (TSet.single β))
    (_hh1 : ResUT.Hash ρb (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)))
    (_hh2 : ResUT.Hash ρ'p (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)))
    (_hsub : ResUT.Sub ρp (ρ.restrictDom ρ'i.exclPart) χ)
    (hXc : ResUT.CompS (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) ρb Xi)
    (hYc : ∃ w, ResUT.CompS ρ' χ w ∧
      ResUT.CompS w (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) Y)
    (hfX : ResUT.Flat Xi σX) (hfY : ResUT.Flat Y σY)
    (l : BoCa.Loc) (hl : ∃ ζ, (ρ.restrictDom ρ'i.exclPart).get l = some ζ) :
    ResUT.SimFormAt σX σY l := by
  classical
  obtain ⟨a, haXi, haY, -⟩ :=
    ResUT.six59_ag_eq hreb hce hcp hupd hsb hs' hsplit hχβ hXc hYc hfX hfY
  obtain ⟨ai, ab, hai, hab, hXag⟩ := (AgWT.split hXc).mp haXi
  obtain ⟨eX, a₁, heX, ha₁, hfX'⟩ := hfX
  cases AgWT.functional ha₁ haXi
  obtain ⟨eY, a₂, heY, ha₂, hfY'⟩ := hfY
  cases AgWT.functional ha₂ haY
  obtain ⟨ζ, hζ⟩ := hl
  obtain ⟨cA, hcA⟩ := ResUT.ag_single_imm_some_of_reb hai hζ
  have hXin : ∃ c, a.get l = some c := by
    rcases ResUT.Comp.get hXag l with ⟨f₁, -, -⟩ | ⟨ψ, -, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
        ⟨ψ₁, ψ₂, ψ, -, -, f, -⟩
    · rw [hcA] at f₁; exact absurd f₁ (by simp)
    · exact ⟨ψ, f⟩
    · rw [hcA] at f₁; exact absurd f₁ (by simp)
    · exact ⟨ψ, f⟩
  obtain ⟨c, hc⟩ := hXin
  exact ResUT.simFormAt_of_eq
    ((ResUT.flat_eq_ag_of_immFree (ExST.immFree heX) hfX' hc).trans
      (ResUT.flat_eq_ag_of_immFree (ExST.immFree heY) hfY' hc).symm)

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
/-- …and it holds. -/
theorem ResUT.sixFiftyNineResidualKeep {K : WCactus} : ResUT.SixFiftyNineResidualKeep (K := K) := by
  intro β ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY l₀ s v hs D hD hreb hce hcp hupd hsb hs'
    hh1 hh2 hsub hXc hYc hfX hfY l hl
  exact ResUT.six59_residual_at hreb hce hcp hupd hsb hs'
    (ResUT.SubKeep.compS (ResUT.six52_H1 hD hreb hce hcp hupd hsb hs') hsub)
    (ResUT.six52_sub_inStratum hD hreb hce hcp hupd hsb hs' χ hsub.toSub)
    hh1 hh2 hsub.toSub hXc hYc hfX hfY l hl

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-- `[TR]` 6.59's step 6 at `ℓ ∉ dom(ρ_reb)`.  `[restricted: as
`ResUT.six59_residual_at`, to `[TR]` 6.52's two conclusions at the `χ` the statement
binds]` -/
theorem ResUT.six59_offReb_at
    {β : Life} {ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : ResUT BoCa.Loc BoCa.Val K}
    {l₀ : BoCa.Loc} {s : TSet} {v : BoCa.Val} {hs : ρ'i.InStratum s}
    (hreb : ResUT.Reb β ρ'i ρ)
    (hce : ResUT.CompS ρ ρb ρρb)
    (hcp : ResUT.CompS ρ' ρp ρ'p)
    (hupd : ResUT.UpdV ρρb ρ'p)
    (hsb : ρb.InStratum (TSet.single β))
    (hs' : ρ'.InStratum (TSet.single β))
    (hsplit : ResUT.CompS χ (ρ.restrictDom ρ'i.exclPart) ρp)
    (hχβ : χ.InStratum (TSet.single β))
    (hXc : ResUT.CompS (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) ρb Xi)
    (hYc : ∃ w, ResUT.CompS ρ' χ w ∧
      ResUT.CompS w (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) Y)
    (hfX : ResUT.Flat Xi σX) (hfY : ResUT.Flat Y σY)
    (l : BoCa.Loc) (_hl : (ρ.restrictDom ρ'i.exclPart).get l = none) :
    ResUT.SimFormAt σX σY l := by
  classical
  obtain ⟨a, haXi, haY, hsil⟩ :=
    ResUT.six59_ag_eq hreb hce hcp hupd hsb hs' hsplit hχβ hXc hYc hfX hfY
  obtain ⟨eX, a₁, heX, ha₁, hfX'⟩ := hfX
  cases AgWT.functional ha₁ haXi
  obtain ⟨eY, a₂, heY, ha₂, hfY'⟩ := hfY
  cases AgWT.functional ha₂ haY
  cases hg : a.get l with
  | some c =>
      exact ResUT.simFormAt_of_eq
        ((ResUT.flat_eq_ag_of_immFree (ExST.immFree heX) hfX' hg).trans
          (ResUT.flat_eq_ag_of_immFree (ExST.immFree heY) hfY' hg).symm)
  | none =>
      obtain ⟨σL, eLr, aLr, heLr, haLr, hfL⟩ := hupd.2.1
      obtain ⟨σR, eRr, aRr, heRr, haRr, hfR⟩ := hupd.2.2
      obtain ⟨hLn, hRn⟩ := hsil aLr aRr haLr haRr l hg
      -- Step A: the swap does not move the exclusive walk
      have heL : eLr = eX :=
        ResUT.ex_eq_of_swap_immOnly (ResUT.reb_immOnly hreb) ResUT.single_imm_immOnly
          (ResUT.CompS.comm hce) (ResUT.CompS.comm hXc) heLr heX
      obtain ⟨R, hRw, hYw⟩ := hYc
      have hRreb : ResUT.CompS R (ρ.restrictDom ρ'i.exclPart) ρ'p := by
        obtain ⟨y, hy₁, hy₂⟩ :=
          (ResUT.CompS.assoc ρ' χ (ρ.restrictDom ρ'i.exclPart) ρ'p).mp
            ⟨ρp, hsplit, hcp⟩
        rwa [ResUT.CompS.functional hy₁ hRw] at hy₂
      have heR : eRr = eY :=
        ResUT.ex_eq_of_swap_immOnly (ResUT.reb_reb_immOnly hreb)
          ResUT.single_imm_immOnly hRreb hYw heRr heY
      refine ResUT.simFormAt_congr (τ₁ := σL) (τ₂ := σR) ?_ ?_ ?_
      · rw [ResUT.flat_eq_ex_of_ag_none hfX' hg,
          ResUT.flat_eq_ex_of_ag_none hfL hLn, heL]
      · rw [ResUT.flat_eq_ex_of_ag_none hfY' hg,
          ResUT.flat_eq_ex_of_ag_none hfR hRn, heR]
      · exact ResUT.simForm_iff_at.mp
          ((ResUT.upd_iff_sim ⟨eLr, aLr, heLr, haLr, hfL⟩
            ⟨eRr, aRr, heRr, haRr, hfR⟩).mp hupd.1) l

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
/-- …and it holds, on 6.52's two conclusions at that `χ`. -/
theorem ResUT.sixFiftyNineOffRebKeep {K : WCactus} : ResUT.SixFiftyNineOffRebKeep (K := K) := by
  intro β ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY l₀ s v hs D hD hreb hce hcp hupd hsb hs'
    _hh1 _hh2 hsub hXc hYc hfX hfY l hl
  exact ResUT.six59_offReb_at hreb hce hcp hupd hsb hs'
    (ResUT.SubKeep.compS (ResUT.six52_H1 hD hreb hce hcp hupd hsb hs') hsub)
    (ResUT.six52_sub_inStratum hD hreb hce hcp hupd hsb hs' χ hsub.toSub)
    hXc hYc hfX hfY l hl

end BoCa.Fig16.Tree
namespace BoCa.Fig16.Tree
open BoCa.Fig16
variable {Loc Val : Type} {K : WCactus}
/-!
## Lemma 6.59 · `[TR]` p. 20 · `variant`

> Let ρᵢ = ℓ ↦ imm(α, ρ′ᵢ, v). If ρ ∈ reb_β(ρ′ᵢ), ρ ● ρ_b ↭ ρ′ ● ρ⁺, @ρ_b ⊐ β, @ρ′ ⊐ β, ρ_b # ρᵢ, and ρ′ ● ρ⁺ # ρᵢ, then ρᵢ ● ρ_b ↭ ρ′ ● (ρ⁺ ⊟ ρ∣dom(ρ′ᵢ∣mut,own)) ● ρᵢ

**Printed proof, transcribed.** Let `ρ_reb = ρ∣dom(ρ′ᵢ∣mut,own)`.  By Lemma 6.52, `ρ⁺ = (ρ⁺ ⊟ ρ_reb) ● ρ_reb` and `@(ρ⁺ ⊟ ρ_reb) ⊐ β`; unfolding `reb`, `ρ = ρ∣dom(ρ′ᵢ∣imm) ● ρ_reb`.  Rewriting the update hypothesis with both: `ρ∣dom(ρ′ᵢ∣imm) ● ρ_reb ● ρ_b ↭ ρ′ ● (ρ⁺ ⊟ ρ_reb) ● ρ_reb`.  By Lemma 6.57, `⦇ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ⦈ = ⦇ρᵢ⦈`, which also gives `ag(ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ) = ag(ρᵢ)`.  `⦇ρ_b ● ρᵢ⦈` is defined by hypothesis, and unfolding `⦇−⦈` and `ex` with Lemmas 6.18 and 6.20: `⦇ρᵢ ● ρ_b⦈ = ex(ρᵢ)_● ● ex(ρ_b)_● ● ag(ρᵢ) ○ ag(ρ_b) = ex(ρ_b)_● ● ag(ρᵢ) ○ ag(ρ_b) = ex(ρ_b)_● ● ag(ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ) ○ ag(ρ_b) = ex(ρ_b)_● ● ag(ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ ● ρ_b) = ⦇ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ ● ρ_b⦈`.  Rewriting with this, it suffices that `ρ∣dom(ρ′ᵢ∣imm) ● ρᵢ ● ρ_b ↭ ρ′ ● (ρ⁺ ⊟ ρ_reb) ● ρᵢ`: the same `imm`/`mut` domain, and `∼` at every `ℓ` of it.  The rewritten hypothesis gives `⦇ρ∣dom(ρ′ᵢ∣imm) ● ρ_reb ● ρ_b⦈(ℓ) ∼ ⦇ρ′ ● (ρ⁺ ⊟ ρ_reb) ● ρ_reb⦈(ℓ)`.  If `ℓ ∉ dom(ρ_reb)`, the goal is immediate by the hypothesis and unfolding `reb`.  If `ℓ ∈ dom(ρ_reb)`, then since all components of the composition besides `ρ_reb` outlive `β`, neither side has the immutable borrow at `β` from `ρ_reb`, and both get the borrow from `ρᵢ`.

**Lean.** `BoCa.Fig16.Tree.ResUT.six59`, tag `[variant: `↓β` read as the hypothesis `hD : K.DownOf D {β}`; restricted to `ResUT.SubKeep` — Definition 6.3 with its third bullet read through the paragraph printed below it; the ✓ halves of `↭` as hypotheses]` (`docs/adjudications.md` §12.58, §12.64). At the chain `hD` is discharged and the statement is the printed `ResU.six59` (`Tree/Chain59.lean`, `chain_six59`).

**Note.** The conclusion is `ResUT.Upd`, `↭` without its `✓ρ₁ ∧ ✓ρ₂` conjuncts ([CONF] Fig. 18b's form, D3).  Those conjuncts are the hypotheses `hfX : Flat Xi σX` (`⦇ρᵢ ● ρ_b⦈` defined) and `hfY : Flat Y σY` (`⦇ρ′ ● (ρ⁺ ⊟ ρ_reb) ● ρᵢ⦈` defined); with them the conclusion is p. 5's guarded `↭` (`ResUT.UpdV`).  The printed statement does not list them.
-/
/-- `[TR]` Lemma 6.59 (p. 20). `[restricted: to `ResUT.SubKeep` — Definition 6.3 with its
third bullet read through the paragraph printed below it (§12.58); the ✓ halves of `↭` as
hypotheses `hfX`, `hfY`]`. Over the tree-stratified carrier. **Forced change:** 6.52, which
the proof applies, reads `↓β` as a stratum `D` with `K.DownOf D {β}` (`hD`), as 6.27 does. -/
theorem ResUT.six59
    {β : Life} {ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : ResUT BoCa.Loc BoCa.Val K}
    {l₀ : BoCa.Loc} {s : TSet} {v : BoCa.Val} {hs : ρ'i.InStratum s}
    {D : TSet} (hD : K.DownOf D (TSet.single β))
    (hreb : ResUT.Reb β ρ'i ρ)
    (hce : ResUT.CompS ρ ρb ρρb) (hcp : ResUT.CompS ρ' ρp ρ'p)
    (hupd : ResUT.UpdV ρρb ρ'p)
    (hsb : ρb.InStratum (TSet.single β)) (hs' : ρ'.InStratum (TSet.single β))
    (hh1 : ResUT.Hash ρb (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)))
    (hh2 : ResUT.Hash ρ'p (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)))
    (hsub : ResUT.SubKeep ρp (ρ.restrictDom ρ'i.exclPart) χ)
    (hXc : ResUT.CompS (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) ρb Xi)
    (hYc : ∃ w, ResUT.CompS ρ' χ w ∧
      ResUT.CompS w (ResUT.single l₀ (CellUT.immOf s v ρ'i hs)) Y)
    (hfX : ResUT.Flat Xi σX) (hfY : ResUT.Flat Y σY) :
    ResUT.Upd Xi Y := by
  classical
  refine (ResUT.upd_iff_sim hfX hfY).mpr (ResUT.simForm_iff_at.mpr (fun l => ?_))
  cases hl : (ρ.restrictDom ρ'i.exclPart).get l with
  | none =>
      exact ResUT.sixFiftyNineOffRebKeep β ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY
        l₀ s v hs D hD hreb hce hcp hupd hsb hs' hh1 hh2 hsub hXc hYc hfX hfY l hl
  | some ζ =>
      exact ResUT.sixFiftyNineResidualKeep β ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY
        l₀ s v hs D hD hreb hce hcp hupd hsb hs' hh1 hh2 hsub hXc hYc hfX hfY l ⟨ζ, hl⟩

end BoCa.Fig16.Tree

end

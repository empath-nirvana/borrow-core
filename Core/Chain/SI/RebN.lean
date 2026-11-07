import Core.Chain.SI.UpdN

/-!
# `[TR]` 6.50, 6.52 and 6.59 at the step index

## What 6.59's printed proof reads of `↭`

`[TR]` 6.59's closing sentence, at `ℓ ∈ dom(ρ_reb)`: *"neither side has the immutable borrow at
`β` from `ρ_reb`, and both get the borrow from `ρᵢ`"*. Its transcription (`ResU.reb_frame_ag_eq`)
shows the two aliasable walks equal, each absorbing the other through its `imm` cells and their
witnesses (`AgW.absorb_of_ancestors`). The update hypothesis is read there at `imm` cells of the
aliasable walk only: `ResU.reb_frame_absImm` and `ResU.reb_frame_absAnc` each call
`ResU.upd_ag_eq_of_ne_own` at a cell whose kind is `imm`, and that branch of it reads only `↭`'s
`imm` clause. `reb_frame_ag_eq` runs the update in both directions (`hupd.symm`); the `imm` clause
is an `↔`, so it is symmetric (`updImm_symm`).

So the printed proof never compares two `mut` cells across `↭`, and `UpdN`'s `imm` clause is the
printed one: the closing sentence holds at the index with no change. The copies below
(`…I`) are the printed proofs with `ResU.UpdImm` for `ResU.Upd`, `updImm_ag_imm_eq` for the
`imm` branch of `ResU.upd_ag_eq_of_ne_own`, and nothing else changed.

## 6.50 and 6.52 at the index

6.52's proof reads `↭` at `imm` cells (`hupd.1.1`) and through 6.50 (`updV_outlives`). 6.50's
printed sentence, *"all borrows have the same lifetime before and after updating"*, holds at
`UpdN`: `MutStep` keeps `β` (`updVN_outlives`).

## 6.59 at the index

`six59N`: the printed case split on `ℓ ∈ dom(ρ_reb)`. Where `ag` is defined both flattenings are
the one aliasable walk's cell; where it is not, both are the exclusive walks of the hypothesis's
two sides, unmoved by the swap, and the hypothesis's `CellUpdN` at `ℓ` is the goal.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

/-! ### `[TR]` 6.50 at the index -/

/-- Two `mut` cells at one `β` lie in the same strata. -/
theorem CellU.inStratum_of_mutStep {α : Life} {ψ ψ' : CellU Loc Val}
    (hk : ψ.kind = Kind.mut) (hk' : ψ'.kind = Kind.mut) (hat : ψ.at = ψ'.at)
    (h : ψ.InStratum α) : ψ'.InStratum α := by
  cases ψ with
  | own _ => simp [CellU.kind] at hk
  | imm _ => simp [CellU.kind] at hk
  | «mut» m =>
    cases ψ' with
    | own _ => simp [CellU.kind] at hk'
    | imm _ => simp [CellU.kind] at hk'
    | «mut» m' =>
      have e : m.β = m'.β := hat
      show m'.β ⊐ α
      rw [← e]; exact h

/-- **`[TR]` 6.50 at the step index**: the printed proof, *"all borrows have the same lifetime
before and after updating"*; `MutStep` keeps `β`. -/
theorem updVN_outlives {Φ : LocFam} {n : Nat} {ρ ρ' : WRes} {α : Life}
    (h : Fig16.BoLo.Outlives ρ α) (hu : UpdVN Φ n ρ ρ') : Fig16.BoLo.Outlives ρ' α := by
  have hρ : ρ.InStratum α := h
  obtain ⟨σ, hσ⟩ := hu.2.1
  obtain ⟨σ', hσ'⟩ := hu.2.2
  have hsσ : σ.InStratum α := flat_inStratum hσ hρ
  refine flat_inStratum_inv hσ' (fun l χ hl => ?_)
  rcases CellU.rep χ with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b, w, ξ, hξ, P, hP, rfl⟩
  · exact trivial
  · obtain ⟨τ, hτ, hg⟩ := (hu.1.1 l s w ξ hξ).mpr ⟨σ', hσ', hl⟩
    cases ResU.Flat.functional hτ hσ
    exact hsσ l _ hg
  · obtain ⟨ψ, ⟨τ, hτ, hg⟩, hs⟩ := hu.1.2.2 l _ ⟨σ', hσ', hl⟩ rfl
    cases ResU.Flat.functional hτ hσ
    exact CellU.inStratum_of_mutStep hs.1 hs.2.1 hs.2.2.1 (hsσ l _ hg)

/-- `[TR]` 6.50 at one location and the step index (`ResU.updV_outlives_at`). -/
theorem updVN_outlives_at {Φ : LocFam} {n : Nat} {ρ ρ' : WRes} {α : Life}
    (hd : ρ.InStratum (↓α)) (hu : UpdVN Φ n ρ ρ') {l : Loc}
    (hl : ∀ φ, ρ.get l = some φ → φ.InStratum α)
    {ψ : CellU Loc Val} (hg : ρ'.get l = some ψ) : ψ.InStratum α := by
  obtain ⟨σ, hσ⟩ := hu.2.1
  obtain ⟨σ', hσ'⟩ := hu.2.2
  refine ResU.flat_inStratum_inv_at hσ' (fun χ hχ => ?_) hg
  rcases CellU.rep χ with ⟨w, rfl⟩ | ⟨s, w, ξ, hξ, rfl⟩ | ⟨b, w, ξ, hξ, P, hP, rfl⟩
  · exact trivial
  · obtain ⟨τ, hτ, hgg⟩ := (hu.1.1 l s w ξ hξ).mpr ⟨σ', hσ', hχ⟩
    cases ResU.Flat.functional hτ hσ
    exact ResU.flat_inStratum_at hσ hd hl hgg
  · obtain ⟨ψ₀, ⟨τ, hτ, hgg⟩, hs⟩ := hu.1.2.2 l _ ⟨σ', hσ', hχ⟩ rfl
    cases ResU.Flat.functional hτ hσ
    exact CellU.inStratum_of_mutStep hs.1 hs.2.1 hs.2.2.1 (ResU.flat_inStratum_at hσ hd hl hgg)

/-! ### `[TR]` 6.52 at the index -/

/-- `[TR]` 6.52's H1 at the step index: `ResU.six52_H1`'s proof, with `updVN_outlives` for 6.50
and `UpdN`'s `imm` clause where it reads `↭`'s. -/
theorem six52_H1N {Φ : LocFam} {n : Nat} {α : Life}
    {ρ'i ρ ρe ρ'' ρp ρρe ρ'p : WRes}
    (hreb : ResU.Reb α ρ'i ρ)
    (hce : ResU.CompS ρ ρe ρρe)
    (hcp : ResU.CompS ρ'' ρp ρ'p)
    (hupd : UpdVN Φ n ρρe ρ'p)
    (hse : ρe.InStratum α)
    (hs' : ρ''.InStratum α) :
    ∀ (l : Loc) (s' : LSet) (v : Val)
      (χ : WRes) (h' : χ.InStratum s'.join),
      (ρ.restrictDom ρ'i.exclPart).get l = some (CellU.immOf s' v χ h') →
      ∃ (s : LSet) (h : χ.InStratum s.join),
        ρp.get l = some (CellU.immOf s v χ h) ∧ ∀ x, s'.mem x → s.mem x := by
  classical
  have hdle : (↓α) ≤ α := le_of_lt (Life.down_sqsubset α)
  have hρρe : ρρe.InStratum (↓α) :=
    ResU.CompS.inStratum hce (ResU.reb_inStratum_down hreb)
      (ResU.InStratum.mono hdle hse)
  have hpdown : ρp.InStratum (↓α) :=
    ResU.CompS.inStratum_right hcp (updVN_outlives hρρe hupd)
  have hnb : ∀ m φ, ρp.get m = some φ → ¬ (φ.at < α) :=
    fun m φ e => CellU.not_at_lt_of_inStratum_down (hpdown m φ e)
  obtain ⟨σ, hσ⟩ := hupd.2.1
  obtain ⟨σ', hσ'⟩ := hupd.2.2
  obtain ⟨σ'', σp, hσ'', hσp, hcσ⟩ := BoLo.flat_compR hcp hσ'
  have hσ''s : σ''.InStratum α := BoLo.flat_inStratum hσ'' hs'
  intro l s' v χ h' he
  have hρl : ρ.get l = some (CellU.immOf s' v χ h') := ResU.restrictDom_get_inv he
  obtain ⟨φ', hφ'⟩ := ResU.restrictDom_dom he
  obtain ⟨hφ'g, hφ'k⟩ := ResU.exclPart_eq_some.mp hφ'
  obtain ⟨vv, χw, hχs, hψeq, -, -⟩ := ResU.reb_src hreb hρl hφ'g hφ'k
  obtain ⟨hs'eq, -, -⟩ := CellU.immOf_inj hψeq
  have hmem : s'.mem α := by rw [hs'eq]; rfl
  obtain ⟨ζ, hζ, hζk, hζw⟩ := ResU.CompS.get_left hce hρl
  have hζe : ζ.erase = v := by
    rw [ResU.CompS.erase_left hce hρl hζ, CellU.erase_immOf]
  obtain ⟨tζ, htζ, hζeta⟩ := CellU.imm_eta (hζk.trans (CellU.kind_immOf _ _ _ _))
  have hζget : ρρe.get l = some (CellU.immOf tζ ζ.erase ζ.wit htζ) :=
    hζ.trans (congrArg some hζeta)
  have hmemζ : tζ.mem α :=
    ResU.CompR.get_ls_imm (ResU.CompS.toCompR hce) hρl hζget hmem
  obtain ⟨π, hπ, hπk, hπe, hπw⟩ := ResU.Flat.get hσ hζget
  obtain ⟨tπ, htπ, hπeta⟩ := CellU.imm_eta (hπk.trans (CellU.kind_immOf _ _ _ _))
  have hπget : σ.get l = some (CellU.immOf tπ π.erase π.wit htπ) :=
    hπ.trans (congrArg some hπeta)
  have hmemπ : tπ.mem α := ResU.Flat.get_ls_imm hσ hζget hπget hmemζ
  -- across `↭`, at its `imm` clause
  have hπ' : σ'.get l = some (CellU.immOf tπ π.erase π.wit htπ) :=
    (ResU.flatAt_iff hσ' l _).mp
      ((hupd.1.1 l tπ π.erase π.wit htπ).mp ⟨σ, hσ, hπget⟩)
  have hmemp : ∃ ξ t, σp.get l = some ξ ∧ ξ.lsOf = some t ∧ t.mem α := by
    rcases ResU.CompR.lsOf_inv hcσ hπ' rfl hmemπ with ⟨ξ, t, e, ht, hxt⟩ | h
    · exact absurd (t.meet_least α hxt)
        (not_le_of_gt (CellU.sqsupset_of_lsOf ht (hσ''s l ξ e)))
    · exact h
  obtain ⟨ξp, tp, hξp, htp, hxtp⟩ := hmemp
  obtain ⟨ω, tω, hω, htω, hxtω⟩ :=
    ResU.flat_imm_at_top_of_no_shorter hσp hξp htp hxtp hnb
  have hξpe : ξp.erase = π.erase ∧ ξp.wit = π.wit := by
    have hc2 := hcσ.2 l
    rw [hξp, hπ'] at hc2
    cases hσ''l : σ''.get l with
    | none =>
        rw [hσ''l] at hc2
        exact ⟨by rw [← Option.some.inj hc2, CellU.erase_immOf],
          by rw [← Option.some.inj hc2, CellU.wit_immOf]⟩
    | some ξ'' =>
        rw [hσ''l] at hc2
        obtain ⟨ω', hω', hCω⟩ := hc2
        have hω'eq : ω' = CellU.immOf tπ π.erase π.wit htπ := (Option.some.inj hω').symm
        have hkξp : ξp.kind ≠ Kind.own := by
          rw [CellU.kind_of_lsOf htp]; exact fun c => Kind.noConfusion c
        refine ⟨?_, ?_⟩
        · rw [← CellU.CompR.erase_right hCω, hω'eq, CellU.erase_immOf]
        · rw [← (CellU.CompR.nonown_right hCω hkξp).2, hω'eq, CellU.wit_immOf]
  obtain ⟨tω', htω', hωeta⟩ := CellU.imm_eta (CellU.kind_of_lsOf htω)
  obtain ⟨κ, hκ, -, hκe, hκw⟩ := ResU.Flat.get hσp hω
  obtain rfl : κ = ξp := Option.some.inj (hκ.symm.trans hξp)
  have hωe : ω.erase = v := by
    rw [← hκe, hξpe.1, hπe, CellU.erase_immOf, hζe]
  have hωw : ω.wit = χ := by
    rw [← hκw, hξpe.2, hπw, CellU.wit_immOf, hζw, CellU.wit_immOf]
  have htωeq : tω = tω' := by
    have hlsω : CellU.lsOf ω = some tω' := by rw [hωeta]; rfl
    exact Option.some.inj (htω.symm.trans hlsω)
  refine ⟨tω', hωw ▸ htω', ?_, ?_⟩
  · exact hω.trans (congrArg some
      (hωeta.trans (CellU.immOf_congr rfl hωe hωw htω' _)))
  · intro x hx
    rw [hs'eq] at hx
    rw [show x = α from hx, ← htωeq]
    exact hxtω

/-- `[TR]` 6.52's second conclusion at the step index (`ResU.six52_sub_inStratum`'s proof). -/
theorem six52_sub_inStratumN {Φ : LocFam} {n : Nat} {α : Life}
    {ρ'i ρ ρe ρ'' ρp ρρe ρ'p : WRes}
    (hreb : ResU.Reb α ρ'i ρ)
    (hce : ResU.CompS ρ ρe ρρe)
    (hcp : ResU.CompS ρ'' ρp ρ'p)
    (hupd : UpdVN Φ n ρρe ρ'p)
    (hse : ρe.InStratum α)
    (hs' : ρ''.InStratum α) :
    ∀ χ, ResU.Sub ρp (ρ.restrictDom ρ'i.exclPart) χ → χ.InStratum α := by
  classical
  have hdle : (↓α) ≤ α := le_of_lt (Life.down_sqsubset α)
  have hρρe : ρρe.InStratum (↓α) :=
    ResU.CompS.inStratum hce (ResU.reb_inStratum_down hreb)
      (ResU.InStratum.mono hdle hse)
  have hpdown : ρp.InStratum (↓α) :=
    ResU.CompS.inStratum_right hcp (updVN_outlives hρρe hupd)
  have hle := six52_H1N hreb hce hcp hupd hse hs'
  intro ψ hsub
  refine ResU.Sub.inStratum hsub hpdown ?_ ?_
  · intro l φ hnone hφ
    have hρl : ∀ ξ, ρ.get l = some ξ → ξ.InStratum α := by
      intro ξ hξ
      have hexl : ρ'i.exclPart.get l = none := by
        cases f : ρ'i.exclPart.get l with
        | none => rfl
        | some φ' =>
            rw [ResU.restrictDom_get_of_some f, hξ] at hnone
            exact absurd hnone (by simp)
      obtain ⟨φ', hφ'⟩ := ResU.reb_dom_subset hreb hξ
      have hk : φ'.kind = Kind.imm := by
        by_contra hk
        rw [ResU.exclPart_eq_some.mpr ⟨hφ', hk⟩] at hexl
        exact absurd hexl (by simp)
      exact (ResU.reb_imm_cell_kw hreb hξ hφ' hk).2.2.2 _ (hreb.1 l φ' hφ')
    have hρρel : ∀ ξ, ρρe.get l = some ξ → ξ.InStratum α :=
      fun ξ e =>
        ResU.inStratum_comp_at (CellU.compS_hC α) hce hρl (fun ω f => hse l ω f) e
    exact ResU.CompS.inStratum_right_at hcp
      (fun ξ e => updVN_outlives_at hρρe hupd hρρel e) hφ
  · intro l ζ hζ
    have hρl : ρ.get l = some ζ := ResU.restrictDom_get_inv hζ
    obtain ⟨φ', hφ'⟩ := ResU.restrictDom_dom hζ
    obtain ⟨hφ'g, hφ'k⟩ := ResU.exclPart_eq_some.mp hφ'
    obtain ⟨v, w, hw, hζeq, -, -⟩ := ResU.reb_src hreb hρl hφ'g hφ'k
    obtain ⟨s, hs, hpl, -⟩ :=
      hle l (LSet.singleton α) v w hw (by rw [hζ, hζeq])
    exact ⟨s, LSet.singleton α, v, w, hs, hw, hpl, hζeq, rfl⟩

/-! ### `[TR]` 6.59's closing sentence at the `imm` clause -/

/-- `ResU.reb_frame_absImm` at `↭`'s `imm` clause. -/
theorem reb_frame_absImmI {β : Life} {ρ'i ρ L Lreb Rreb : WRes}
    {aL aR areb ai aLr aRr aY eLr eRr σL σR : WRes}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join} {es as pS : WRes}
    (hreb : ResU.Reb β ρ'i ρ)
    (hL : L.InStratum β)
    (hupd : ResU.UpdImm Lreb Rreb)
    (haL : AgW L aL)
    (hareb : AgW (ρ.restrictDom ρ'i.exclPart) areb)
    (hai : AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ai)
    (hexS : ExR ρ'i es) (hagS : AgW ρ'i as) (hfS : ResU.CompR es as pS)
    (hcLr : ResU.CompR aL areb aLr) (hcRr : ResU.CompR aR areb aRr)
    (hcRi : ResU.CompR aR ai aY)
    (haLr : AgW Lreb aLr) (haRr : AgW Rreb aRr)
    (heLr : ExS Lreb eLr) (heRr : ExS Rreb eRr)
    (hfL : ResU.CompS eLr aLr σL) (hfR : ResU.CompS eRr aRr σR) :
    AgW.AbsImm aL aY := by
  classical
  obtain ⟨bi, hbi, hbile⟩ := ResU.reb_ag_split hreb hareb hai hexS hagS hfS
  obtain ⟨y, hy₁, hy₂⟩ :=
    (ResU.CompR.assoc aR bi (ρ.restrictDom ρ'i.exclPart) aRr).mp
      ⟨areb, ResU.CompR.comm hbi, hcRr⟩
  have hyY : ResU.CompR y aY aY :=
    ResU.CompR.absorb_comp hy₁ (ResU.LeR.left hcRi).absorb
      (ResU.LeR.trans hbile (ResU.LeR.right hcRi)).absorb
  intro m ψ hgm hk
  have hstr : ψ.InStratum β := BoLo.AgW.inStratum haL β hL m ψ hgm
  obtain ⟨ψt, hψt, hψle⟩ := (ResU.LeR.left hcLr).get_some hgm
  have hψtk : ψt.kind = Kind.imm := by
    obtain ⟨t, ht, e⟩ := CellU.imm_eta hk
    obtain ⟨t', h', e'⟩ := CellU.CompR.imm_left_eq hψle e
    rw [e']; exact CellU.kind_immOf _ _ _ _
  have hRrm : aRr.get m = some ψt :=
    updImm_ag_imm_eq hupd heLr haLr hfL heRr haRr hfR hψt hψtk
  have habs : ∃ d, y.get m = some d ∧ CellU.CompR ψ d d := by
    have hdec := hy₂.2 m
    rw [hRrm] at hdec
    cases hr : (ρ.restrictDom ρ'i.exclPart).get m with
    | none =>
        rw [hr] at hdec
        cases hyg : y.get m with
        | none =>
            rw [hyg] at hdec
            exact absurd (show (some ψt : Option (CellU Loc Val)) = none
              from hdec) (by simp)
        | some d =>
            rw [hyg] at hdec
            obtain rfl : ψt = d :=
              Option.some.inj (show (some ψt : Option (CellU Loc Val)) = some d from hdec)
            exact ⟨_, rfl, hψle⟩
    | some B =>
        rw [hr] at hdec
        obtain ⟨φ', hφ'⟩ := ResU.restrictDom_dom hr
        obtain ⟨hφ'g, hφ'k⟩ := ResU.exclPart_eq_some.mp hφ'
        obtain ⟨vm, χm, hχm, hBeq, -, -⟩ :=
          ResU.reb_src hreb (ResU.restrictDom_get_inv hr) hφ'g hφ'k
        subst hBeq
        cases hyg : y.get m with
        | none =>
            rw [hyg] at hdec
            obtain rfl : ψt = CellU.immOf (LSet.singleton β) vm χm hχm :=
              Option.some.inj hdec
            exact absurd rfl (CellU.reb_frame_imm_ne_singleton hψle hstr hk)
        | some d =>
            rw [hyg] at hdec
            obtain ⟨e, he, hde⟩ := hdec
            obtain rfl : ψt = e := Option.some.inj he
            exact ⟨d, rfl, CellU.reb_frame_imm_le hstr hk hde hψle⟩
  obtain ⟨d, hd, hψd⟩ := habs
  obtain ⟨c, hc, hdc⟩ := (ResU.LeR.left hyY).get_some hd
  exact ⟨c, hc, CellU.CompR.absorb_transC hψd hdc⟩

/-- `ResU.reb_frame_absAnc` at `↭`'s `imm` clause. -/
theorem reb_frame_absAncI {β : Life} {ρ'i ρ R Lreb Rreb : WRes}
    {aL aR areb ai aLr aRr aY eLr eRr σL σR : WRes}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join} {es as pS : WRes}
    (hreb : ResU.Reb β ρ'i ρ)
    (hupd : ResU.UpdImm Lreb Rreb)
    (haR : AgW R aR)
    (hareb : AgW (ρ.restrictDom ρ'i.exclPart) areb)
    (hai : AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ai)
    (hexS : ExR ρ'i es) (hagS : AgW ρ'i as) (hfS : ResU.CompR es as pS)
    (hcLr : ResU.CompR aL areb aLr) (hcRr : ResU.CompR aR areb aRr)
    (hcRi : ResU.CompR aR ai aY)
    (haLr : AgW Lreb aLr) (haRr : AgW Rreb aRr)
    (heLr : ExS Lreb eLr) (heRr : ExS Rreb eRr)
    (hfL : ResU.CompS eLr aLr σL) (hfR : ResU.CompS eRr aRr σR) :
    AgW.AbsAnc aL aY := by
  intro m t u κ hh hgm ev av p hev hav hp
  obtain ⟨t₁, h₁, hLrm⟩ := ResU.CompR.imm_left_get hcLr hgm
  have hRrm : aRr.get m = some (CellU.immOf t₁ u κ h₁) :=
    updImm_ag_imm_eq hupd heLr haLr hfL heRr haRr hfR hLrm (CellU.kind_immOf _ _ _ _)
  obtain ⟨ev', av', p', z, hev', hav', hp', hz⟩ :=
    ResU.reb_attribute hreb haR hareb hai hexS hagS hfS hcRr hcRi hRrm
  cases ExR.functional hev' hev
  cases AgW.functional hav' hav
  cases ResU.CompR.functional hp' hp
  exact (ResU.LeR.left hz).absorb

/-- `ResU.reb_frame_ag_le` at `↭`'s `imm` clause. -/
theorem reb_frame_ag_leI {β : Life} {ρ'i ρ L R Lreb Rreb : WRes}
    {aL aR areb ai aLr aRr aY eLr eRr σL σR : WRes}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join} {es as pS : WRes}
    (hreb : ResU.Reb β ρ'i ρ)
    (hL : L.InStratum β)
    (hupd : ResU.UpdImm Lreb Rreb)
    (haL : AgW L aL) (haR : AgW R aR)
    (hareb : AgW (ρ.restrictDom ρ'i.exclPart) areb)
    (hai : AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ai)
    (hexS : ExR ρ'i es) (hagS : AgW ρ'i as) (hfS : ResU.CompR es as pS)
    (hcLr : ResU.CompR aL areb aLr) (hcRr : ResU.CompR aR areb aRr)
    (hcRi : ResU.CompR aR ai aY)
    (haLr : AgW Lreb aLr) (haRr : AgW Rreb aRr)
    (heLr : ExS Lreb eLr) (heRr : ExS Rreb eRr)
    (hfL : ResU.CompS eLr aLr σL) (hfR : ResU.CompS eRr aRr σR) :
    ResU.CompR aL aY aY :=
  AgW.absorb_of_ancestors haL aY
    (reb_frame_absImmI hreb hL hupd haL hareb hai hexS hagS hfS hcLr hcRr
      hcRi haLr haRr heLr heRr hfL hfR)
    (reb_frame_absAncI hreb hupd haR hareb hai hexS hagS hfS hcLr hcRr
      hcRi haLr haRr heLr heRr hfL hfR)

/-- `[TR]` 6.59's closing sentence (`ResU.reb_frame_ag_eq`) at `↭`'s `imm` clause; the update is
run in both directions, as printed, through `updImm_symm`. -/
theorem reb_frame_ag_eqI {β : Life} {ρ'i ρ L R Lreb Rreb : WRes}
    {aL aR areb ai aLr aRr aX aY eLr eRr σL σR : WRes}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join} {es as pS : WRes}
    (hreb : ResU.Reb β ρ'i ρ)
    (hL : L.InStratum β) (hR : R.InStratum β)
    (hupd : ResU.UpdImm Lreb Rreb)
    (haL : AgW L aL) (haR : AgW R aR)
    (hareb : AgW (ρ.restrictDom ρ'i.exclPart) areb)
    (hai : AgW (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ai)
    (hexS : ExR ρ'i es) (hagS : AgW ρ'i as) (hfS : ResU.CompR es as pS)
    (hcLr : ResU.CompR aL areb aLr) (hcRr : ResU.CompR aR areb aRr)
    (hcLi : ResU.CompR aL ai aX) (hcRi : ResU.CompR aR ai aY)
    (haLr : AgW Lreb aLr) (haRr : AgW Rreb aRr)
    (heLr : ExS Lreb eLr) (heRr : ExS Rreb eRr)
    (hfL : ResU.CompS eLr aLr σL) (hfR : ResU.CompS eRr aRr σR) :
    aX = aY := by
  have h1 : ResU.CompR aL aY aY :=
    reb_frame_ag_leI hreb hL hupd haL haR hareb hai hexS hagS hfS
      hcLr hcRr hcRi haLr haRr heLr heRr hfL hfR
  have h2 : ResU.CompR aR aX aX :=
    reb_frame_ag_leI hreb hR (updImm_symm hupd) haR haL hareb hai hexS hagS hfS
      hcRr hcLr hcLi haRr haLr heRr heLr hfR hfL
  have hXY : ResU.CompR aX aY aY :=
    ResU.CompR.absorb_comp hcLi h1 (ResU.LeR.right hcRi).absorb
  have hYX : ResU.CompR aY aX aX :=
    ResU.CompR.absorb_comp hcRi h2 (ResU.LeR.right hcLi).absorb
  exact (ResU.CompR.functional (ResU.CompR.comm hXY) hYX).symm

/-! ### 6.59 at the index -/

/-- `ResU.six59_ag_eq` at the step index: the two sides have one aliasable walk, and where it is
silent so is each side of the update hypothesis. The printed proof; `↭` is read at its `imm`
clause (`reb_frame_ag_eqI`) and its two validity conjuncts. -/
theorem six59_ag_eqN {Φ : LocFam} {n : Nat}
    {β : Life} {ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : WRes}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (hce : ResU.CompS ρ ρb ρρb)
    (hcp : ResU.CompS ρ' ρp ρ'p)
    (hupd : UpdVN Φ n ρρb ρ'p)
    (hsb : ρb.InStratum β)
    (hs' : ρ'.InStratum β)
    (hsplit : ResU.CompS χ (ρ.restrictDom ρ'i.exclPart) ρp)
    (hχβ : χ.InStratum β)
    (hXc : ResU.CompS (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ρb Xi)
    (hYc : ∃ w, ResU.CompS ρ' χ w ∧
      ResU.CompS w (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Y)
    (hfX : ResU.Flat Xi σX) (hfY : ResU.Flat Y σY) :
    ∃ a, AgW Xi a ∧ AgW Y a ∧
      ∀ aL aR, AgW ρρb aL → AgW ρ'p aR →
        ∀ l, a.get l = none → aL.get l = none ∧ aR.get l = none := by
  classical
  obtain ⟨eX, aXi, heX, haXi, hfX'⟩ := hfX
  obtain ⟨ai, ab, hai, hab, hXag⟩ := (AgW.split hXc).mp haXi
  obtain ⟨eY, aY, heY, haY, hfY'⟩ := hfY
  obtain ⟨R, hRw, hYw⟩ := hYc
  obtain ⟨aR, ai₁, haR, hai₁, hYag⟩ := (AgW.split hYw).mp haY
  cases AgW.functional hai₁ hai
  obtain ⟨σL, eLr, aLr, heLr, haLr, hfL⟩ := hupd.2.1
  obtain ⟨σR, eRr, aRr, heRr, haRr, hfR⟩ := hupd.2.2
  obtain ⟨aρ, ab₁, haρ, hab₁, hLag⟩ := (AgW.split hce).mp haLr
  cases AgW.functional hab₁ hab
  obtain ⟨aρ', aρp, haρ', haρp, hRag⟩ := (AgW.split hcp).mp haRr
  have hDsplit := ResU.restrictDom_split hreb
  obtain ⟨aD, areb, haD, hareb, hDag⟩ := (AgW.split hDsplit).mp haρ
  obtain ⟨aχ, areb₁, haχ, hareb₁, hPag⟩ := (AgW.split hsplit).mp haρp
  cases AgW.functional hareb₁ hareb
  obtain ⟨x, hx₁, hx₂⟩ :=
    (ResU.CompR.assoc aD areb ab aLr).mpr ⟨aρ, hDag, hLag⟩
  obtain ⟨aL, hcDab, hcLareb⟩ :=
    (ResU.CompR.assoc aD ab areb aLr).mp ⟨x, ResU.CompR.comm hx₁, hx₂⟩
  obtain ⟨z, hz₁, hz₂⟩ :=
    (ResU.CompS.assoc (ρ.restrictDom (ρ'i.restrict Kind.imm))
      (ρ.restrictDom ρ'i.exclPart) ρb ρρb).mpr ⟨ρ, hDsplit, hce⟩
  obtain ⟨L, hLc, hLreb⟩ :=
    (ResU.CompS.assoc (ρ.restrictDom (ρ'i.restrict Kind.imm)) ρb
      (ρ.restrictDom ρ'i.exclPart) ρρb).mp ⟨z, ResU.CompS.comm hz₁, hz₂⟩
  have haLW : AgW L aL := (AgW.split hLc).mpr ⟨aD, ab, haD, hab, hcDab⟩
  have hLstr : L.InStratum β :=
    ResU.CompS.inStratum hLc (ResU.reb_immPart_inStratum hreb) hsb
  obtain ⟨aR₀, hcR₀, hcRareb⟩ :=
    (ResU.CompR.assoc aρ' aχ areb aRr).mp ⟨aρp, hPag, hRag⟩
  obtain ⟨b₁, b₂, hb₁, hb₂, hbc⟩ := (AgW.split hRw).mp haR
  cases AgW.functional hb₁ haρ'
  cases AgW.functional hb₂ haχ
  cases ResU.CompR.functional hbc hcR₀
  have hRstr : R.InStratum β := ResU.CompS.inStratum hRw hs' hχβ
  obtain ⟨es, as, pS, hexS, hagS, hfS, hagi⟩ := AgW.single_imm_inv hai
  have hDai : ResU.CompR aD ai ai := ResU.reb_immPart_ag_absorbs hreb haD hai
  have hDaXi : ResU.CompR aD aXi aXi :=
    (ResU.LeR.trans ⟨ai, hDai⟩ (ResU.LeR.left hXag)).absorb
  obtain ⟨y, hy₁, hy₂⟩ :=
    (ResU.CompR.assoc aD ab ai aXi).mp ⟨aXi, ResU.CompR.comm hXag, hDaXi⟩
  cases ResU.CompR.functional hy₁ hcDab
  have heq : aXi = aY :=
    reb_frame_ag_eqI hreb hLstr hRstr hupd.1.1 haLW haR hareb hai hexS hagS hfS
      hcLareb hcRareb hy₂ hYag haLr haRr heLr heRr hfL hfR
  subst heq
  refine ⟨aXi, haXi, haY, fun aL' aR' haL' haR' l hn => ?_⟩
  cases AgW.functional haL' haLr
  cases AgW.functional haR' haRr
  obtain ⟨hain, habn⟩ := (ResU.Comp.eq_none_iff hXag l).mp hn
  obtain ⟨haRn, -⟩ := (ResU.Comp.eq_none_iff hYag l).mp hn
  obtain ⟨haDn, -⟩ := (ResU.Comp.eq_none_iff hDai l).mp hain
  have hrebn : (ρ.restrictDom ρ'i.exclPart).get l = none := by
    cases hr : (ρ.restrictDom ρ'i.exclPart).get l with
    | none => rfl
    | some ζ =>
        obtain ⟨c, hc⟩ := ResU.ag_single_imm_some_of_reb hai hr
        rw [hain] at hc; exact absurd hc (by simp)
  have harebn : areb.get l = none := by
    cases hg : areb.get l with
    | none => rfl
    | some ψ =>
        obtain ⟨φ, hφ, -⟩ :=
          ResU.reb_ag_cell_absorbed_off_dom hreb hareb hai hexS hagS hfS hrebn hg
        rw [hain] at hφ; exact absurd hφ (by simp)
  obtain ⟨haρ'n, haχn⟩ := (ResU.Comp.eq_none_iff hcR₀ l).mp haRn
  have hnone₂ : ∀ {c₁ c₂ c : WRes}, ResU.CompR c₁ c₂ c →
      c₁.get l = none → c₂.get l = none → c.get l = none := by
    intro c₁ c₂ c hc h₁ h₂
    have := hc.2 l
    rw [h₁, h₂] at this
    exact this
  exact ⟨hnone₂ hLag (hnone₂ hDag haDn harebn) habn,
    hnone₂ hRag haρ'n (hnone₂ hPag haχn harebn)⟩

/-- `[TR]` 6.59's step 6 at a reborrowed `ℓ`, at the step index (`ResU.six59_residual_at`): the
aliasable walk is defined at `ℓ`, so both flattenings are its cell. -/
theorem six59_residual_atN {Φ : LocFam} {n : Nat}
    {β : Life} {ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : WRes}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (hce : ResU.CompS ρ ρb ρρb)
    (hcp : ResU.CompS ρ' ρp ρ'p)
    (hupd : UpdVN Φ n ρρb ρ'p)
    (hsb : ρb.InStratum β)
    (hs' : ρ'.InStratum β)
    (hsplit : ResU.CompS χ (ρ.restrictDom ρ'i.exclPart) ρp)
    (hχβ : χ.InStratum β)
    (hXc : ResU.CompS (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ρb Xi)
    (hYc : ∃ w, ResU.CompS ρ' χ w ∧
      ResU.CompS w (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Y)
    (hfX : ResU.Flat Xi σX) (hfY : ResU.Flat Y σY)
    (l : Loc) (hl : ∃ ζ, (ρ.restrictDom ρ'i.exclPart).get l = some ζ) :
    CellUpdN Φ n l (σX.get l) (σY.get l) := by
  classical
  obtain ⟨a, haXi, haY, -⟩ :=
    six59_ag_eqN hreb hce hcp hupd hsb hs' hsplit hχβ hXc hYc hfX hfY
  obtain ⟨ai, ab, hai, hab, hXag⟩ := (AgW.split hXc).mp haXi
  obtain ⟨eX, a₁, heX, ha₁, hfX'⟩ := hfX
  cases AgW.functional ha₁ haXi
  obtain ⟨eY, a₂, heY, ha₂, hfY'⟩ := hfY
  cases AgW.functional ha₂ haY
  obtain ⟨ζ, hζ⟩ := hl
  obtain ⟨cA, hcA⟩ := ResU.ag_single_imm_some_of_reb hai hζ
  have hXin : ∃ c, a.get l = some c := by
    rcases ResU.Comp.get hXag l with ⟨f₁, -, -⟩ | ⟨ψ, -, -, f⟩ | ⟨ψ, f₁, -, -⟩ |
        ⟨ψ₁, ψ₂, ψ, -, -, f, -⟩
    · rw [hcA] at f₁; exact absurd f₁ (by simp)
    · exact ⟨ψ, f⟩
    · rw [hcA] at f₁; exact absurd f₁ (by simp)
    · exact ⟨ψ, f⟩
  obtain ⟨c, hc⟩ := hXin
  rw [(ResU.flat_eq_ag_of_immFree (ExS.immFree heX) hfX' hc).trans
    (ResU.flat_eq_ag_of_immFree (ExS.immFree heY) hfY' hc).symm]
  exact CellUpdN.refl _ _ _ _

/-- `[TR]` 6.59's step 6 at `ℓ ∉ dom(ρ_reb)`, at the step index (`ResU.six59_offReb_at`): where
the aliasable walk is defined both flattenings are its cell; where it is not, both are the
exclusive walks of the hypothesis's two sides (step A, the swap does not move them), and the
hypothesis's clauses at `ℓ` are the goal. -/
theorem six59_offReb_atN {Φ : LocFam} {n : Nat}
    {β : Life} {ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : WRes}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (hce : ResU.CompS ρ ρb ρρb)
    (hcp : ResU.CompS ρ' ρp ρ'p)
    (hupd : UpdVN Φ n ρρb ρ'p)
    (hsb : ρb.InStratum β)
    (hs' : ρ'.InStratum β)
    (hsplit : ResU.CompS χ (ρ.restrictDom ρ'i.exclPart) ρp)
    (hχβ : χ.InStratum β)
    (hXc : ResU.CompS (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ρb Xi)
    (hYc : ∃ w, ResU.CompS ρ' χ w ∧
      ResU.CompS w (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Y)
    (hfX : ResU.Flat Xi σX) (hfY : ResU.Flat Y σY)
    (l : Loc) (_hl : (ρ.restrictDom ρ'i.exclPart).get l = none) :
    CellUpdN Φ n l (σX.get l) (σY.get l) := by
  classical
  obtain ⟨a, haXi, haY, hsil⟩ :=
    six59_ag_eqN hreb hce hcp hupd hsb hs' hsplit hχβ hXc hYc hfX hfY
  obtain ⟨eX, a₁, heX, ha₁, hfX'⟩ := hfX
  cases AgW.functional ha₁ haXi
  obtain ⟨eY, a₂, heY, ha₂, hfY'⟩ := hfY
  cases AgW.functional ha₂ haY
  cases hg : a.get l with
  | some c =>
      rw [(ResU.flat_eq_ag_of_immFree (ExS.immFree heX) hfX' hg).trans
        (ResU.flat_eq_ag_of_immFree (ExS.immFree heY) hfY' hg).symm]
      exact CellUpdN.refl _ _ _ _
  | none =>
      obtain ⟨σL, eLr, aLr, heLr, haLr, hfL⟩ := hupd.2.1
      obtain ⟨σR, eRr, aRr, heRr, haRr, hfR⟩ := hupd.2.2
      obtain ⟨hLn, hRn⟩ := hsil aLr aRr haLr haRr l hg
      have heL : eLr = eX :=
        ResU.ex_eq_of_swap_immOnly (ResU.reb_immOnly hreb) ResU.single_imm_immOnly
          (ResU.CompS.comm hce) (ResU.CompS.comm hXc) heLr heX
      obtain ⟨R, hRw, hYw⟩ := hYc
      have hRreb : ResU.CompS R (ρ.restrictDom ρ'i.exclPart) ρ'p := by
        obtain ⟨y, hy₁, hy₂⟩ :=
          (ResU.CompS.assoc ρ' χ (ρ.restrictDom ρ'i.exclPart) ρ'p).mp
            ⟨ρp, hsplit, hcp⟩
        rwa [ResU.CompS.functional hy₁ hRw] at hy₂
      have heR : eRr = eY :=
        ResU.ex_eq_of_swap_immOnly (ResU.reb_reb_immOnly hreb)
          ResU.single_imm_immOnly hRreb hYw heRr heY
      rw [ResU.flat_eq_ex_of_ag_none hfX' hg, ResU.flat_eq_ex_of_ag_none hfY' hg,
        ← heL, ← heR, ← ResU.flat_eq_ex_of_ag_none hfL hLn,
        ← ResU.flat_eq_ex_of_ag_none hfR hRn]
      exact cellUpdN_of_updN hupd.1 ⟨eLr, aLr, heLr, haLr, hfL⟩
        ⟨eRr, aRr, heRr, haRr, hfR⟩ l

/-- **`[TR]` Lemma 6.59 at the step index.** Let `ρᵢ = ℓ ↦ imm(α, ρ′ᵢ, v)`. If
`ρ ∈ reb_β(ρ′ᵢ)`, `ρ ● ρ_b ↭ₙ ρ′ ● ρ⁺`, `@ρ_b ⊐ β`, `@ρ′ ⊐ β`, `ρ_b # ρᵢ` and `ρ′ ● ρ⁺ # ρᵢ`,
then `ρᵢ ● ρ_b ↭ₙ ρ′ ● (ρ⁺ ⊟ ρ_reb) ● ρᵢ`. Hypotheses as `ResU.six59` (`ResU.SubKeep`; the ✓
halves `hfX`, `hfY`); the printed case split on `ℓ ∈ dom(ρ_reb)`. -/
theorem six59N {Φ : LocFam} {n : Nat}
    {β : Life} {ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : WRes}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (hce : ResU.CompS ρ ρb ρρb) (hcp : ResU.CompS ρ' ρp ρ'p)
    (hupd : UpdVN Φ n ρρb ρ'p)
    (hsb : ρb.InStratum β) (hs' : ρ'.InStratum β)
    (_hh1 : ResU.Hash ρb (ResU.single l₀ (CellU.immOf s v ρ'i hs)))
    (_hh2 : ResU.Hash ρ'p (ResU.single l₀ (CellU.immOf s v ρ'i hs)))
    (hsub : ResU.SubKeep ρp (ρ.restrictDom ρ'i.exclPart) χ)
    (hXc : ResU.CompS (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ρb Xi)
    (hYc : ∃ w, ResU.CompS ρ' χ w ∧
      ResU.CompS w (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Y)
    (hfX : ResU.Flat Xi σX) (hfY : ResU.Flat Y σY) :
    UpdN Φ n Xi Y := by
  classical
  have hsplit : ResU.CompS χ (ρ.restrictDom ρ'i.exclPart) ρp :=
    ResU.SubKeep.compS (six52_H1N hreb hce hcp hupd hsb hs') hsub
  have hχβ : χ.InStratum β :=
    six52_sub_inStratumN hreb hce hcp hupd hsb hs' χ hsub.toSub
  refine updN_of_flat hfX hfY (fun l => ?_)
  cases hl : (ρ.restrictDom ρ'i.exclPart).get l with
  | none =>
      exact six59_offReb_atN hreb hce hcp hupd hsb hs' hsplit hχβ hXc hYc hfX hfY l hl
  | some ζ =>
      exact six59_residual_atN hreb hce hcp hupd hsb hs' hsplit hχβ hXc hYc hfX hfY l ⟨ζ, hl⟩

/-- `six59N` with the guard: `UpdVN`. -/
theorem six59VN {Φ : LocFam} {n : Nat}
    {β : Life} {ρ'i ρ ρb ρ' ρp χ ρρb ρ'p Xi Y σX σY : WRes}
    {l₀ : Loc} {s : LSet} {v : Val} {hs : ρ'i.InStratum s.join}
    (hreb : ResU.Reb β ρ'i ρ)
    (hce : ResU.CompS ρ ρb ρρb) (hcp : ResU.CompS ρ' ρp ρ'p)
    (hupd : UpdVN Φ n ρρb ρ'p)
    (hsb : ρb.InStratum β) (hs' : ρ'.InStratum β)
    (hh1 : ResU.Hash ρb (ResU.single l₀ (CellU.immOf s v ρ'i hs)))
    (hh2 : ResU.Hash ρ'p (ResU.single l₀ (CellU.immOf s v ρ'i hs)))
    (hsub : ResU.SubKeep ρp (ρ.restrictDom ρ'i.exclPart) χ)
    (hXc : ResU.CompS (ResU.single l₀ (CellU.immOf s v ρ'i hs)) ρb Xi)
    (hYc : ∃ w, ResU.CompS ρ' χ w ∧
      ResU.CompS w (ResU.single l₀ (CellU.immOf s v ρ'i hs)) Y)
    (hfX : ResU.Flat Xi σX) (hfY : ResU.Flat Y σY) :
    UpdVN Φ n Xi Y :=
  ⟨six59N hreb hce hcp hupd hsb hs' hh1 hh2 hsub hXc hYc hfX hfY, ⟨σX, hfX⟩, ⟨σY, hfY⟩⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end

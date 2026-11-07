import Core.Chain.Reborrow791N

/-!
# The suspending field reborrow `withborF`  `[spec §62]`

`withborF d : Mut @a (Ref A) ⊸ (∀'x ⊏ @bnd. Mut 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ(Mut @a (Ref A) ⊗ B)`,
`λr. λf. (f [] (load r)) then b. (r, b) unwind d r`: the callback borrows the boxed field of the
borrowed cell. Core has no rule for it (`Core/TreeGoal791.lean`, §1). The proof is
`withbor3S_compat₀`'s (Core's `withbor3U_compatX`) with the source at `Ref A`, a `load` from the
opened cell, and the Mut Frame at the field's location `ℓ₂` rather than at `ℓ`:

* the anti-frame opens `ℓ ↦ mut(β, loc ℓ₂, σ₀, F_o j)` to `ℓ ↦ own(loc ℓ₂) ● σ₀`,
  `σ₀ = ℓ₂ ↦ own(u) ● σ_u`; the `load` reads `loc ℓ₂` (`rwp_load`, `erwp_bindR`);
* the Mut Frame lends `ℓ₂` at a fresh `α` (`erwp_M_frameCRG`), with `ℓ ↦ own(loc ℓ₂)` framed
  outside it (`erwp_frameGR`, `erwp_frame_cancelRunGR`, `tabG_canF`): the framed cell joins the
  guard at every stop (`ShareG.sep`), the claim at every raise and the claim of every layered
  cancel run;
* the guard and the claim at `ℓ₂`, beside the framed cell, are the guard and the claim at `ℓ`:
  the field's cell with its content is a `Ref A` value, in `F_o k` (`Ref`'s clause, `hunif` at
  `Ref A`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload ubindE)

theorem opTableGR_local (T : OpTabN) (G : ShareG) (R : Nat → WProp) :
    (opTableGR T G R).Local := by
  intro k ls t Ψ Ψ' ρ hΨ h
  rcases h with h | h
  · exact Or.inl (opTableG_local T G k ls t Ψ Ψ' ρ hΨ h)
  · exact Or.inr h

/-! ### The frame at a guarded table with raises -/

/-- **The frame at `erwp` over `opTableGR`** (`erwpG_frame` with raises and cancellable stops):
the framed resource goes into each stop's continuation share beside the guarded part (the guard
`G.sep Fr`) and is taken back at the resume; at a raise it joins the claim (`R k ⋆ Fr`); a
cancellable stop's cancel obligation, at the share with the frame, is the twin's by `hcan`. -/
theorem erwp_frameGR {Φ : LocFam} {T₁ T₂ : OpTabN} (hTT : T₁.Twin T₂)
    (hT : ∀ m i en, T₁ m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF)
    {G : ShareG} {R : Nat → WProp} {Q : PostN} (Fr : WProp)
    (hcan : ∀ m i en en', T₁ m i = some en → T₂ m i = some en' → en.abort = false →
      en.q ≠ .lin → ∀ k ls (K : Kont) (ρk ρ₂ ρk' : WRes), ResU.CompS ρk ρ₂ ρk' → Fr ρ₂ →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρk') :
    ∀ n ls e (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ → Fr ρ₂ →
      erwp (ℍ := ℍ) Φ (opTableGR T₁ G R) Q n ls e ρ₁ →
      erwp (ℍ := ℍ) Φ (opTableGR T₂ (G.sep fun _ => Fr) (fun k => R k ⋆ Fr))
        (fun k ls' v => Q k ls' v ⋆ Fr) n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ₁ ρ₂ ρ hc hR₂ h
  rw [erwp_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ⟨σ₁, σ₂, hσ, ht, hσ₂⟩ => ?_)
    (rwpG_frame (fun _ => Fr) (fun _ _ _ _ h => h) hc h hR₂)
  rcases ht with ⟨v, rfl, hv⟩ | ⟨K, m, i, v, en, hp⟩ | ⟨K, m, i, v, en, hp⟩
  · exact Or.inl ⟨v, rfl, σ₁, σ₂, hσ, hv, hσ₂⟩
  · -- a stop: the frame in the share, beside the guarded part
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hA, hG, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨hqu, hwc⟩ := hT m i en hTe ha
    obtain ⟨en', hTe', hq', hab', hPA', hPB', hwc'⟩ := hTT m i en hTe
    obtain ⟨ρk₂, hk₂, haσ⟩ := (ResU.CompS.assoc ρa ρk σ₂ σ).mpr ⟨σ₁, hcak, hσ⟩
    have hwe : ∀ ls'', en'.wc ls' ls'' ρk₂ → en.wc ls' ls'' ρk := by
      intro ls'' he
      rw [hwc', hwc] at he; rw [hwc]
      exact extF_left _ _ _ _ _ hk₂ he
    refine Or.inr (Or.inl ⟨K, m, i, v, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩
      ⟨ρa, ρk₂, haσ, hPA' ▸ hA, ⟨ρk, σ₂, hk₂, hG, hσ₂⟩,
        fun hu' => absurd (hq'.symm.trans hu') hqu, fun ls'' he =>
          ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hql => ?_⟩⟩⟩)
    · obtain ⟨y, hy, hyτ⟩ := compS_exch hk₂ hcτ
      have hc' := (hcont ls'' (hwe ls'' he)).1 k' hk' w τ₁ y (hPB' ▸ hB) hy
      simp only [erwpC, show k' < n by omega, if_true] at hc' ⊢
      exact ih k' (by omega) ls'' _ y σ₂ τ₂ hyτ hσ₂ hc'
    · have hql' : en.q ≠ .lin := hq' ▸ hql
      exact hcan m i en en' hTe hTe' ha hql' k ls'' K ρk σ₂ ρk₂ hk₂ hσ₂
        ((hcont ls'' (hwe ls'' he)).2 hql')
  · -- a `raise`: the frame beside the claim
    obtain ⟨⟨rfl, hK, hTe, hab⟩, σa, ρR, hcσR, hpa, hR⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hTe', -, hab', hPA', -, -⟩ := hTT m i en hTe
    obtain ⟨y, hy, hσy⟩ := compS_reassoc hcσR hσ
    exact Or.inr (Or.inr ⟨K, m, i, v, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans hab⟩
      ⟨σa, y, hσy, hPA' ▸ hpa, ρR, σ₂, hy, hR, hσ₂⟩⟩)

/-- **The frame over a cancel run at a guarded table** (`erwp_frame_cancelRun` for a cancel run
that stops): the frame joins the claim at the cancel's `raise` and the guard at every stop. -/
theorem erwp_frame_cancelRunGR {Φ : LocFam} {T₁ T₂ : OpTabN} (hTT : T₁.Twin T₂)
    (hT : ∀ m i en, T₁ m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF)
    {G : ShareG} {R : Nat → WProp} (Fr : WProp)
    (hcan : ∀ m i en en', T₁ m i = some en → T₂ m i = some en' → en.abort = false →
      en.q ≠ .lin → ∀ k ls (K : Kont) (ρk ρ₂ ρk' : WRes), ResU.CompS ρk ρ₂ ρk' → Fr ρ₂ →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρk') :
    ∀ n ls e (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ → Fr ρ₂ →
      erwp (ℍ := ℍ) Φ (cancelTabGR T₁ G R) (fun _ _ _ _ => False) n ls e ρ₁ →
      erwp (ℍ := ℍ) Φ (cancelTabGR T₂ (G.sep fun _ => Fr) (fun k => R k ⋆ Fr))
        (fun _ _ _ _ => False) n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ₁ ρ₂ ρ hc hR₂ h
  rw [erwp_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ⟨σ₁, σ₂, hσ, ht, hσ₂⟩ => ?_)
    (rwpG_frame (fun _ => Fr) (fun _ _ _ _ h => h) hc h hR₂)
  rcases ht with ⟨_, _, hf⟩ | ⟨K, err, hp⟩ | ⟨K, m, i, v, en, hp⟩
  · exact hf.elim
  · -- the cancel's `raise`: the frame beside the claim
    obtain ⟨hpur, y1, y2, hy, ⟨τa, τb, hcab, herr, hnb⟩, hR⟩ := pure_sep_iff.mp hp
    obtain ⟨y, hy', hσy⟩ := compS_reassoc hy hσ
    exact Or.inr (Or.inl ⟨K, err, pure_sep_mk hpur ⟨y1, y, hσy,
      ⟨τa, τb, hcab, errOkN_twin hTT herr, hnb⟩, y2, σ₂, hy', hR, hσ₂⟩⟩)
  · -- a stop: the frame in the share, beside the guarded part
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hA, hG, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨hqu, hwc⟩ := hT m i en hTe ha
    obtain ⟨en', hTe', hq', hab', hPA', hPB', hwc'⟩ := hTT m i en hTe
    obtain ⟨ρk₂, hk₂, haσ⟩ := (ResU.CompS.assoc ρa ρk σ₂ σ).mpr ⟨σ₁, hcak, hσ⟩
    have hwe : ∀ ls'', en'.wc ls' ls'' ρk₂ → en.wc ls' ls'' ρk := by
      intro ls'' he
      rw [hwc', hwc] at he; rw [hwc]
      exact extF_left _ _ _ _ _ hk₂ he
    refine Or.inr (Or.inr ⟨K, m, i, v, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩
      ⟨ρa, ρk₂, haσ, hPA' ▸ hA, ⟨ρk, σ₂, hk₂, hG, hσ₂⟩,
        fun hu' => absurd (hq'.symm.trans hu') hqu, fun ls'' he =>
          ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hql => ?_⟩⟩⟩)
    · obtain ⟨y, hy, hyτ⟩ := compS_exch hk₂ hcτ
      have hc' := (hcont ls'' (hwe ls'' he)).1 k' hk' w τ₁ y (hPB' ▸ hB) hy
      simp only [erwpC, show k' < n by omega, if_true] at hc' ⊢
      exact ih k' (by omega) ls'' _ y σ₂ τ₂ hyτ hσ₂ hc'
    · have hql' : en.q ≠ .lin := hq' ▸ hql
      exact hcan m i en en' hTe hTe' ha hql' k ls'' K ρk σ₂ ρk₂ hk₂ hσ₂
        ((hcont ls'' (hwe ls'' he)).2 hql')

/-! ### Exclusive walks and consistency, from a walk -/

/-- **An operand's exclusive walk misses a location the other operand's walk holds a non-`imm`
cell at**, in a composite with a walk (`exS_none_of_part` read off the walk). -/
theorem exS_none_of_walk {ρ₁ ρ₂ ρ ex : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ) (hex : ExS ρ ex)
    {l : Loc} (hl : ∀ e₁, ExS ρ₁ e₁ → ∃ ψ : CellU Loc Val, e₁.get l = some ψ ∧ ψ.kind ≠ Kind.imm) :
    ∀ e, ExS ρ₂ e → e.get l = none := by
  intro e he
  obtain ⟨e₁, e₂, he₁, he₂, hc⟩ := (ExS.split h).mp hex
  obtain rfl := ExS.functional he he₂
  obtain ⟨ψ, h₁, hk⟩ := hl e₁ he₁
  cases f : e.get l with
  | none => rfl
  | some ζ => exact absurd (CellU.CompatS.kinds (hc.1 l _ ζ h₁ f)).1 hk

/-- `consistentX_left` from a walk of the composite. -/
theorem consistentX_leftE {ρ₁ ρ₂ ρ ex : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ) {c : Loc → Option Life}
    (hc : ConsistentX c ρ) (hex : ExS ρ ex) : ConsistentX c ρ₁ := by
  intro e₁ he₁ l ψ hg hk
  obtain ⟨e₁', e₂, he₁', he₂, hc'⟩ := (ExS.split h).mp hex
  obtain rfl := ExS.functional he₁ he₁'
  exact hc ex hex l ψ (compS_get_left_nonimm hc' hg (by rw [hk]; decide)).2 hk

/-- **A `mut` cell's walk holds what its witness's walk holds**, at a non-`imm` cell. -/
theorem exS_mut_wit_get {l : Loc} {b : Life} {w : Val} {χ : WRes} {hχ : χ.InStratum b}
    {P : Val → SPropS Loc Val b} {hw : P w ⟨χ, hχ⟩} {e : WRes}
    (he : ExS (ResU.single l (CellU.mutOf b w χ hχ P hw)) e) :
    ∃ e₀, ExS χ e₀ ∧ ∀ x (ψ : CellU Loc Val), e₀.get x = some ψ → ψ.kind ≠ Kind.imm →
      e.get x = some ψ := by
  obtain ⟨e₀, he₀, hcomp⟩ := ExW.single_mut_inv he
  exact ⟨e₀, he₀, fun x ψ hg hk => (compS_get_left_nonimm (ResU.CompS.comm hcomp) hg hk).2⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 ctx791 vals791 jdgC withborFSTy withborFV withborFE)
open BoCa.BoLo (Heap Kont ubindE Head performE raiseE cancelVal opPayload)

/-! ### The guarded twin with the frame -/

/-! ### The suspending field reborrow -/

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end

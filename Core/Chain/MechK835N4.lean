import Core.Chain.MechK835N
import Core.Chain.Field791N

/-!
# The frame at a guarded table with raises, at `erwpK`  `[spec §19, §27, §62]`

`docs/new-core/scope-835-kripke-stop.md` §2, class M, continued from `MechK835N.lean`. The field
reborrow `withborF` frames the opened cell `ℓ ↦ own(loc ℓ₂)` outside the Mut Frame at the field
(`erwp_frameGR`, `erwp_frame_cancelRunGR`). Restated at `erwpK`: the frame joins the continuation's
share at every stop, so the entry's order at the joint share gives the twin's at the run's own
share (`hwk`); the cancel obligation is carried at the resumption world (`hcan`). Both read the
joint share's validity, which every returned resource has (`rwpG_validK`). Each `erwp` statement is
proved again at one world (`*_of_K`); its text is the original's.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload)

variable {ι : Type}

/-- **A run's returned resource is valid**: `↭` gives it. -/
theorem rwpG_validK {Φ : LocFam} {Q : PostG} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : rwpG (ℍ := ℍ) Φ Q n ls e ρ) :
    rwpG (ℍ := ℍ) Φ (fun k ls t ρ' => Q k ls t ρ' ∧ ResU.Valid ρ') n ls e ρ := by
  intro ρf fρ ps μ hf hcf hT htg hI hl hfd j μ' e' hj hrun hfin
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃⟩ := h ρf fρ ps μ hf hcf hT htg hI hl hfd j μ' e' hj hrun hfin
  exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃, (ResU.Valid.split h₆ h₇.2.2).1⟩

/-- `OpTabN.Twin` at the lifted tables. -/
theorem OpTabN.Twin.liftK {T T' : OpTabN} (h : T.Twin T') : (liftTabK T).Twin (liftTabK T') := by
  intro m i en hT
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
  obtain ⟨en₀', h₀', hq, hab, hPA, hPB, hwc⟩ := h m i en₀ h₀
  refine ⟨liftEntK en₀', liftTabK_of_some h₀', hq, hab, hPA, ?_, hwc⟩
  simp only [liftEntK, hPB]

/-! ### The frame at a guarded table with raises -/

/-- **The frame at `erwpK` over `opTableGRK`** (`erwp_frameGR`). The framed resource goes into
each stop's continuation share beside the guarded part (the guard `G.sep Fr`) and is taken back at
the resume, at the world the stop is resumed at; the twin's order at the joint share gives the
entry's at the run's share (`hwk`); at a raise the frame joins the claim; a cancellable stop's
cancel obligation, at the joint share, is the twin's by `hcan`, read at the resumption world. -/
theorem erwpK_frameGR {V : ι → ι → Prop} {Φ : ι → LocFam} {fl : ι → Life} {T₁ T₂ : ι → OpTabK ι}
    (hTT : ∀ x, (T₁ x).Twin (T₂ x))
    (hT : ∀ x m i en, T₁ x m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF)
    {G : ShareG} {R : Nat → WProp} {Q : ι → PostN} (Fr : WProp)
    (hwk : ∀ x m i en en', T₁ x m i = some en → T₂ x m i = some en' → en.abort = false →
      ∀ f y (ρk ρ₂ ρk' : WRes), ResU.CompS ρk ρ₂ ρk' → ResU.Valid ρk' → Fr ρ₂ →
        en'.wk f y ρk' → en.wk f y ρk)
    (hcan : ∀ x m i en en', T₁ x m i = some en → T₂ x m i = some en' → en.abort = false →
      en.q ≠ .lin → ∀ f y k ls (K : Kont) (ρk ρ₂ ρk' : WRes), ResU.CompS ρk ρ₂ ρk' →
        ResU.Valid ρk' → Fr ρ₂ → en'.wk f y ρk' →
        cancelOKK en y k ls K ρk → cancelOKK en' y k ls K ρk') :
    ∀ n x ls e (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ → Fr ρ₂ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableGRK (fl z) (T₁ z) G R) Q x n ls e ρ₁ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableGRK (fl z) (T₂ z) (G.sep fun _ => Fr)
        (fun k => R k ⋆ Fr)) (fun y k ls' v => Q y k ls' v ⋆ Fr) x n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ₁ ρ₂ ρ hc hR₂ h
  rw [erwpK_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ⟨⟨σ₁, σ₂, hσ, ht, hσ₂⟩, hvσ⟩ => ?_)
    (rwpG_validK (rwpG_frame (fun _ => Fr) (fun _ _ _ _ h => h) hc h hR₂))
  rcases ht with ⟨v, rfl, y, hy, hv⟩ | ⟨K, m, i, v, en, hp⟩ | ⟨K, m, i, v, en, hp⟩
  · exact Or.inl ⟨v, rfl, y, hy, σ₁, σ₂, hσ, hv, hσ₂⟩
  · -- a stop: the frame in the share, beside the guarded part
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hA, hG, -, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨hqu, hwc⟩ := hT x m i en hTe ha
    obtain ⟨en', hTe', hq', hab', hPA', hPB', hwc'⟩ := hTT x m i en hTe
    obtain ⟨ρk₂, hk₂, haσ⟩ := (ResU.CompS.assoc ρa ρk σ₂ σ).mpr ⟨σ₁, hcak, hσ⟩
    have hvk : ResU.Valid ρk₂ := (ResU.Valid.split haσ hvσ).2
    have hwe : ∀ ls'', en'.wc ls' ls'' ρk₂ → en.wc ls' ls'' ρk := by
      intro ls'' he
      rw [hwc', hwc] at he; rw [hwc]
      exact extF_left _ _ _ _ _ hk₂ he
    refine Or.inr (Or.inl ⟨K, m, i, v, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩
      ⟨ρa, ρk₂, haσ, hPA' ▸ hA, ⟨ρk, σ₂, hk₂, hG, hσ₂⟩,
        fun hu' => absurd (hq'.symm.trans hu') hqu, f, hf, fun y hy ls'' he =>
          ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hql => ?_⟩⟩⟩)
    · have hy' := hwk x m i en en' hTe hTe' ha f y ρk σ₂ ρk₂ hk₂ hvk hσ₂ hy
      obtain ⟨z, hz, hzτ⟩ := compS_exch hk₂ hcτ
      have hc' := (hcont y hy' ls'' (hwe ls'' he)).1 k' hk' w τ₁ z (hPB' ▸ hB) hz
      simp only [erwpCK, show k' < n by omega, if_true] at hc' ⊢
      exact ih k' (by omega) y ls'' _ z σ₂ τ₂ hzτ hσ₂ hc'
    · have hql' : en.q ≠ .lin := hq' ▸ hql
      have hy' := hwk x m i en en' hTe hTe' ha f y ρk σ₂ ρk₂ hk₂ hvk hσ₂ hy
      exact hcan x m i en en' hTe hTe' ha hql' f y k ls'' K ρk σ₂ ρk₂ hk₂ hvk hσ₂ hy
        ((hcont y hy' ls'' (hwe ls'' he)).2 hql')
  · -- a `raise`: the frame beside the claim
    obtain ⟨⟨rfl, hK, hTe, hab⟩, σa, ρR, hcσR, hpa, hR⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hTe', -, hab', hPA', -, -⟩ := hTT x m i en hTe
    obtain ⟨y, hy, hσy⟩ := compS_reassoc hcσR hσ
    exact Or.inr (Or.inr ⟨K, m, i, v, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans hab⟩
      ⟨σa, y, hσy, hPA' ▸ hpa, ρR, σ₂, hy, hR, hσ₂⟩⟩)

/-- `erwp_frameGR` from `erwpK_frameGR`. -/
theorem erwp_frameGR_of_K {Φ : LocFam} {T₁ T₂ : OpTabN} (hTT : T₁.Twin T₂)
    (hT : ∀ m i en, T₁ m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF)
    {G : ShareG} {R : Nat → WProp} {Q : PostN} (Fr : WProp)
    (hcan : ∀ m i en en', T₁ m i = some en → T₂ m i = some en' → en.abort = false →
      en.q ≠ .lin → ∀ k ls (K : Kont) (ρk ρ₂ ρk' : WRes), ResU.CompS ρk ρ₂ ρk' → Fr ρ₂ →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρk') :
    ∀ n ls e (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ → Fr ρ₂ →
      erwp (ℍ := ℍ) Φ (opTableGR T₁ G R) Q n ls e ρ₁ →
      erwp (ℍ := ℍ) Φ (opTableGR T₂ (G.sep fun _ => Fr) (fun k => R k ⋆ Fr))
        (fun k ls' v => Q k ls' v ⋆ Fr) n ls e ρ := by
  intro n ls e ρ₁ ρ₂ ρ hc hR₂ h
  rw [erwp_eq_erwpK_of (opTableGRK_lift 0 T₁ G R) Φ Q] at h
  rw [erwp_eq_erwpK_of (opTableGRK_lift 0 T₂ (G.sep fun _ => Fr) (fun k => R k ⋆ Fr)) Φ _]
  refine erwpK_frameGR (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Φ) (fl := fun _ => 0)
    (T₁ := fun _ => liftTabK T₁) (T₂ := fun _ => liftTabK T₂) (Q := fun _ => Q)
    (fun _ => hTT.liftK) ?_ Fr (fun _ m i en _ h₁ _ _ _ _ _ _ _ _ _ _ _ => by
      obtain ⟨en₀, -, rfl⟩ := liftTabK_some h₁
      trivial) ?_
    n () ls e ρ₁ ρ₂ ρ hc hR₂ h
  · intro _ m i en h₁ ha
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hT m i en₀ h₀ ha
  · intro _ m i en en' h₁ h₂ ha hq _ _ k ls K ρk ρ₂' ρk' hc' _ hF _
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    obtain ⟨en₀', h₀', rfl⟩ := liftTabK_some h₂
    exact cancelOKK_lift_conv (hcan m i en₀ en₀' h₀ h₀' ha hq k ls K ρk ρ₂' ρk' hc' hF)

/-- **The frame over a cancel run at a guarded table, at `erwpK`** (`erwp_frame_cancelRunGR`):
the frame joins the claim at the cancel's `raise` and the guard at every stop. -/
theorem erwpK_frame_cancelRunGR {V : ι → ι → Prop} {Φ : ι → LocFam} {fl : ι → Life}
    {T₁ T₂ : ι → OpTabK ι} (hTT : ∀ x, (T₁ x).Twin (T₂ x))
    (hT : ∀ x m i en, T₁ x m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF)
    {G : ShareG} {R : Nat → WProp} (Fr : WProp)
    (hwk : ∀ x m i en en', T₁ x m i = some en → T₂ x m i = some en' → en.abort = false →
      ∀ f y (ρk ρ₂ ρk' : WRes), ResU.CompS ρk ρ₂ ρk' → ResU.Valid ρk' → Fr ρ₂ →
        en'.wk f y ρk' → en.wk f y ρk)
    (hcan : ∀ x m i en en', T₁ x m i = some en → T₂ x m i = some en' → en.abort = false →
      en.q ≠ .lin → ∀ f y k ls (K : Kont) (ρk ρ₂ ρk' : WRes), ResU.CompS ρk ρ₂ ρk' →
        ResU.Valid ρk' → Fr ρ₂ → en'.wk f y ρk' →
        cancelOKK en y k ls K ρk → cancelOKK en' y k ls K ρk') :
    ∀ n x ls e (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ → Fr ρ₂ →
      erwpK (ℍ := ℍ) V Φ (fun z => cancelTabGRK (fl z) (T₁ z) G R) (fun _ _ _ _ _ => False)
        x n ls e ρ₁ →
      erwpK (ℍ := ℍ) V Φ (fun z => cancelTabGRK (fl z) (T₂ z) (G.sep fun _ => Fr)
        (fun k => R k ⋆ Fr)) (fun _ _ _ _ _ => False) x n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ₁ ρ₂ ρ hc hR₂ h
  rw [erwpK_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ⟨⟨σ₁, σ₂, hσ, ht, hσ₂⟩, hvσ⟩ => ?_)
    (rwpG_validK (rwpG_frame (fun _ => Fr) (fun _ _ _ _ h => h) hc h hR₂))
  rcases ht with ⟨_, _, _, _, hf⟩ | ⟨K, m, i, v, en, hp⟩ | ⟨K, err, hp⟩
  · exact hf.elim
  · -- a stop: the frame in the share, beside the guarded part
    obtain ⟨⟨rfl, hK, hTe, ha⟩, ρa, ρk, hcak, hA, hG, -, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨hqu, hwc⟩ := hT x m i en hTe ha
    obtain ⟨en', hTe', hq', hab', hPA', hPB', hwc'⟩ := hTT x m i en hTe
    obtain ⟨ρk₂, hk₂, haσ⟩ := (ResU.CompS.assoc ρa ρk σ₂ σ).mpr ⟨σ₁, hcak, hσ⟩
    have hvk : ResU.Valid ρk₂ := (ResU.Valid.split haσ hvσ).2
    have hwe : ∀ ls'', en'.wc ls' ls'' ρk₂ → en.wc ls' ls'' ρk := by
      intro ls'' he
      rw [hwc', hwc] at he; rw [hwc]
      exact extF_left _ _ _ _ _ hk₂ he
    refine Or.inr (Or.inl ⟨K, m, i, v, en', pure_sep_mk ⟨rfl, hK, hTe', hab'.trans ha⟩
      ⟨ρa, ρk₂, haσ, hPA' ▸ hA, ⟨ρk, σ₂, hk₂, hG, hσ₂⟩,
        fun hu' => absurd (hq'.symm.trans hu') hqu, f, hf, fun y hy ls'' he =>
          ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hql => ?_⟩⟩⟩)
    · have hy' := hwk x m i en en' hTe hTe' ha f y ρk σ₂ ρk₂ hk₂ hvk hσ₂ hy
      obtain ⟨z, hz, hzτ⟩ := compS_exch hk₂ hcτ
      have hc' := (hcont y hy' ls'' (hwe ls'' he)).1 k' hk' w τ₁ z (hPB' ▸ hB) hz
      simp only [erwpCK, show k' < n by omega, if_true] at hc' ⊢
      exact ih k' (by omega) y ls'' _ z σ₂ τ₂ hzτ hσ₂ hc'
    · have hql' : en.q ≠ .lin := hq' ▸ hql
      have hy' := hwk x m i en en' hTe hTe' ha f y ρk σ₂ ρk₂ hk₂ hvk hσ₂ hy
      exact hcan x m i en en' hTe hTe' ha hql' f y k ls'' K ρk σ₂ ρk₂ hk₂ hvk hσ₂ hy
        ((hcont y hy' ls'' (hwe ls'' he)).2 hql')
  · -- the cancel's `raise`: the frame beside the claim
    obtain ⟨hpur, y1, y2, hy, ⟨τa, τb, hcab, herr, hnb⟩, hR⟩ := pure_sep_iff.mp hp
    obtain ⟨y, hy', hσy⟩ := compS_reassoc hy hσ
    exact Or.inr (Or.inr ⟨K, err, pure_sep_mk hpur ⟨y1, y, hσy,
      ⟨τa, τb, hcab, errOkK_twin (hTT x) herr, hnb⟩, y2, σ₂, hy', hR, hσ₂⟩⟩)

/-- `erwp_frame_cancelRunGR` from `erwpK_frame_cancelRunGR`. -/
theorem erwp_frame_cancelRunGR_of_K {Φ : LocFam} {T₁ T₂ : OpTabN} (hTT : T₁.Twin T₂)
    (hT : ∀ m i en, T₁ m i = some en → en.abort = false → en.q ≠ .unr ∧ en.wc = extF)
    {G : ShareG} {R : Nat → WProp} (Fr : WProp)
    (hcan : ∀ m i en en', T₁ m i = some en → T₂ m i = some en' → en.abort = false →
      en.q ≠ .lin → ∀ k ls (K : Kont) (ρk ρ₂ ρk' : WRes), ResU.CompS ρk ρ₂ ρk' → Fr ρ₂ →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρk') :
    ∀ n ls e (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ → Fr ρ₂ →
      erwp (ℍ := ℍ) Φ (cancelTabGR T₁ G R) (fun _ _ _ _ => False) n ls e ρ₁ →
      erwp (ℍ := ℍ) Φ (cancelTabGR T₂ (G.sep fun _ => Fr) (fun k => R k ⋆ Fr))
        (fun _ _ _ _ => False) n ls e ρ := by
  intro n ls e ρ₁ ρ₂ ρ hc hR₂ h
  rw [erwp_eq_erwpK_of (cancelTabGRK_lift 0 T₁ G R) Φ _] at h
  rw [erwp_eq_erwpK_of (cancelTabGRK_lift 0 T₂ (G.sep fun _ => Fr) (fun k => R k ⋆ Fr)) Φ _]
  refine erwpK_frame_cancelRunGR (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Φ)
    (fl := fun _ => 0) (T₁ := fun _ => liftTabK T₁) (T₂ := fun _ => liftTabK T₂)
    (fun _ => hTT.liftK) ?_ Fr (fun _ m i en _ h₁ _ _ _ _ _ _ _ _ _ _ _ => by
      obtain ⟨en₀, -, rfl⟩ := liftTabK_some h₁
      trivial) ?_
    n () ls e ρ₁ ρ₂ ρ hc hR₂ h
  · intro _ m i en h₁ ha
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hT m i en₀ h₀ ha
  · intro _ m i en en' h₁ h₂ ha hq _ _ k ls K ρk ρ₂' ρk' hc' _ hF _
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    obtain ⟨en₀', h₀', rfl⟩ := liftTabK_some h₂
    exact cancelOKK_lift_conv (hcan m i en₀ en₀' h₀ h₀' ha hq k ls K ρk ρ₂' ρk' hc' hF)

end BoCa.Fig16.LogRel.Core.Chain.SI

end

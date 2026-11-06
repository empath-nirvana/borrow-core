import Core.Chain.Reborrow791N

/-!
# The suspending field reborrow `withborF`  `[spec §62]`

`withborF d : Mut @a (Ref A) ⊸ (∀'x ⊏ @bnd. Mut 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ(Mut @a (Ref A) ⊗ B)`,
`λr. λf. (f [] (load r)) then b. (r, b) unwind d r`: the callback borrows the boxed field of the
borrowed cell. Core has no rule for it (`Core/TreeGoal791.lean`, §1). The proof is
`withbor3S_compat`'s (Core's `withbor3U_compatX`) with the source at `Ref A`, a `load` from the
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

/-- **An entry of `tabG` is a layer's, and every `tabG` has the layer's entry at the same key.** -/
theorem tab_lookupGG (R : Nat → WProp) (G : ShareG) : ∀ (F : CTy) {δ : LSub} {Θ : LocTy}
    {c : Loc → Option Life} {m j : UInt32} {en : OpEntN},
    tabG (ℍ := ℍ) R G F δ Θ c m j = some en → ∃ q A B fin, F.LayerOf q A B fin ∧
      en = entN q B (fun k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ)
        (fun k v ρ => vN (ℍ := ℍ) B δ Θ k v ρ) (finG (ℍ := ℍ) R G fin δ Θ c) ∧
      ∀ (R' : Nat → WProp) (G' : ShareG), tabG (ℍ := ℍ) R' G' F δ Θ c m j =
        some (entN q B (fun k v ρ => vN (ℍ := ℍ) A δ Θ k v ρ)
          (fun k v ρ => vN (ℍ := ℍ) B δ Θ k v ρ) (finG (ℍ := ℍ) R' G' fin δ Θ c))
  | .eff m₀ i₀ q A B fin rc C, δ, Θ, c, m, j, en, h => by
      simp only [tabG] at h
      unfold extTabN at h
      split at h
      · rename_i hmj
        cases Option.some.inj h
        exact ⟨q, A, B, fin, .inl ⟨rfl, rfl, rfl, rfl⟩, rfl, fun R' G' => by
          simp only [tabG, extTabN, if_pos hmj]⟩
      · rename_i hmj
        obtain ⟨q', A', B', fin', hL, he, hR⟩ := tab_lookupGG R G C h
        exact ⟨q', A', B', fin', .inr hL, he, fun R' G' => by
          simp only [tabG, extTabN, if_neg hmj]; exact hR R' G'⟩
  | .ret _, _, _, _, _, _, _, h => by simp [tabG, OpTabN.empty] at h
  | .arr _ _, _, _, _, _, _, _, h => by simp [tabG, OpTabN.empty] at h
  | .amp _ _, _, _, _, _, _, _, h => by simp [tabG, OpTabN.empty] at h
  | .top, _, _, _, _, _, _, h => by simp [tabG, OpTabN.empty] at h
  | .all _ _ _, _, _, _, _, _, _, h => by simp [tabG, OpTabN.empty] at h
  | .nu _, _, _, _, _, _, _, h => by simp [tabG, OpTabN.empty] at h

/-- Two guarded twins at the same world and view agree but for the cancel obligations. -/
theorem tabG_tabG_twin (R : Nat → WProp) (G : ShareG) (R' : Nat → WProp) (G' : ShareG) (F : CTy)
    (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) :
    (tabG (ℍ := ℍ) R G F δ Θ c).Twin (tabG (ℍ := ℍ) R' G' F δ Θ c) := by
  intro m i en h
  obtain ⟨q, A, B, fin, -, rfl, hR⟩ := tab_lookupGG R G F h
  exact ⟨_, hR R' G', rfl, rfl, rfl, rfl, rfl⟩

/-- **The guarded twin's cancel obligations with a frame beside the share**, by induction on how
deep cancel rows nest: at a capturable entry the cancel run at its cancel row's guarded table is
framed (`erwp_frame_cancelRunGR`), its own nested cancel obligations by the induction. -/
theorem tabG_canF {x : LifeVar} {δ : LSub} {Θ : LocTy} {c : Loc → Option Life}
    (R : Nat → WProp) (G : ShareG) (Fr : WProp) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → F.SuspendC x →
    ∀ m i en en', tabG (ℍ := ℍ) R G F δ Θ c m i = some en →
      tabG (ℍ := ℍ) (fun k => R k ⋆ Fr) (G.sep fun _ => Fr) F δ Θ c m i = some en' →
      en.abort = false → en.q ≠ .lin →
      ∀ k ls (K : Kont) (ρk ρ₂ ρk' : WRes), ResU.CompS ρk ρ₂ ρk' → Fr ρ₂ →
        cancelOKN en k ls K ρk → cancelOKN en' k ls K ρk' := by
  intro d
  induction d with
  | zero =>
      intro F hd hF m i en en' h
      obtain ⟨q, A, B, fin, hL, -, -⟩ := tab_lookupGG R G F h
      exact absurd (layer_cdepth F hL) (by omega)
  | succ d ih =>
  intro F hd hFs m i en en' h h' ha hql k ls K ρk ρ₂ ρk' hc hFr hcn
  obtain ⟨q, A, B, fin, hL, rfl, hR⟩ := tab_lookupGG R G F h
  rw [hR _ _] at h'
  cases Option.some.inj h'
  have hcap := entN_capB ha hql
  have hfin := (layer_suspend F hFs hL).2.2.2.2.2 hcap
  have hfd : fin.cdepth ≤ d := by have := layer_cdepth F hL; omega
  intro P' hP'
  simp only [entN, hcap, if_true] at hP' hcn
  by_cases htop : fin = .top
  · subst htop; simp [finG] at hP'
  rw [finG_eq _ _ htop] at hP'
  cases Option.some.inj hP'
  have hin := hcn _ (finG_eq R G htop δ Θ c)
  exact erwp_frame_cancelRunGR (Φ := Θ.view c) (tabG_tabG_twin R G _ _ fin δ Θ c)
    (tabG_afok hfin R G δ Θ c) Fr (ih fin hfd hfin) k ls _ ρk ρ₂ ρk' hc hFr hin

/-! ### The suspending field reborrow -/

/-- **`withborF` at a suspending row is a value of `!` its type**: `withborF d` at
`Mut @a (Ref A) ⊸ (∀'x ⊏ @bnd. Mut 'x A ⊸ F_Σ(['x] B)) ⊸ F_Σ(Mut @a (Ref A) ⊗ B)`, `Σ` a
`Row.Suspend x` row. Core has no rule for it. The proof is `withbor3S_compat`'s 13 steps (Core's
`withbor3U_compatX`) at the source `Mut @a (Ref A)`, with three changes, each from the term:

* step 2 reads the source's content as a `Ref A` value: `loc ℓ₂` with
  `σ₀ = ℓ₂ ↦ own(u₀) ● σ_u` and `u₀` in `𝒱⟦A⟧` (`Ref`'s clause);
* between steps 7 and 8, the `load` from the opened cell `ℓ ↦ own(loc ℓ₂)` (`rwp_load`);
* step 8's Mut Frame is at `ℓ₂`, the opened cell `ℓ ↦ own(loc ℓ₂)` framed outside it
  (`erwp_frameGR`, `tabG_canF`); step 6's `hunif` at `A` and step 13's inclusion come from
  `hunif` at `Ref A`: the field's cell with its content is a `Ref A` value, in `Res_β` and in
  `F_o k`.

Premises, and the rule that supplies each: `hbnd`, `hA`, `hB`, `hS`, `hdc` are `Const791.OK`'s for `wF`
(`withbor3U`'s at `Mut @a (Ref A)`, `Row.Suspend` for `Row.Unwind`); `hd` is the fundamental
property at `d`'s derivation, the premise `CDerives Δ Γ d (Mut @a (Ref A) ⊸ 1)` read
semantically. -/
theorem withborFS_compat {a : Lifetime.Life} {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy}
    {S : Row} {d : Expr} (hbnd : LifeCtx.empty.Defines bnd) (hA : ¬ VFree x A) (hB : ¬ VFree x B) (hS : S.Suspend x)
    (hdc : closedAt 0 d = true)
    (hd : SemJN (ℍ := ℍ) LifeCtx.empty [] d (.val (.lolli (.mut a (.ref A)) .unit))) (δ : LSub)
    (Θ₀ : LocTy) (n : Nat) :
    vN (ℍ := ℍ) (.bang (withborFSTy a x bnd A B S)) δ Θ₀ n (withborFV d) PMap.empty := by
  -- step 1
  refine ⟨rfl, fun Θ₁ _ _ c₁ _ ls => ?_⟩
  intro Θ₂ _ _ c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  -- steps 2–4
  intro Θ hE₃ hΘ c k' hk' f ρf ρ'' hc' hf hcon
  set P : CPredL := fun Θ' j u r => vN (ℍ := ℍ) (.ref A) δ Θ' j u r with hP
  obtain ⟨α₀, hα₀, (β : Life), hα₀β, hm, hunif⟩ := vN_le hk' (vN_extR _ δ k u ρu hE₃ hu)
  -- step 5
  obtain ⟨l, w₀, σ₀, hσ₀, j₀, hw₀, hkj, rfl, hl, rfl⟩ := id hm
  -- step 2 at `Ref A`: the source's content is the field `ℓ₂ ↦ own(u₀) ● σ_u`
  obtain ⟨l₂, u₀, σu, rfl, hσ₀s, hu₀⟩ := (vN_above (.ref A) δ Θ hσ₀).mp hw₀
  rw [cN_effOf]
  refine erwp_of_valid fun hv'' => ?_
  have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
  set Fo := CTy.effOf S (.tensor (.mut a (.ref A)) B) with hFo
  set T := tabN (ℍ := ℍ) Fo δ Θ c with hTdef
  have hTd : T.Down := tabN_down _ δ Θ hΘ.1 c
  have hQo : PostN.Down (fun k _ v ρ => vN (ℍ := ℍ) (.tensor (.mut a (.ref A)) B) δ Θ k v ρ) :=
    fun k _ v ρ h => vN_down _ δ Θ k v ρ h
  set Qin : PostN := fun k _ b ρ =>
    vN (ℍ := ℍ) (.tensor (.mut a (.ref A)) B) δ Θ k (Val.pair (Val.loc l) b) ρ with hQin
  refine erwp_det hΦ (opTableN_down hTd) hQo
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl (.appL .hole f)) ?_
  refine erwp_det hΦ (opTableN_down hTd) hQo (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 f (Expr.subst (0 + 1) (Val.shift 1 0 (Val.loc l))
        (thenE ((Expr.var 2).pair (Expr.var 0)) (d.app (Expr.var 2))
          (((Expr.var 0).app (Expr.val Val.unit)).app
            ((Expr.val (Val.prim .load)).app (Expr.var 1)))))) =
      ubindE (.pair (NFv l) (DFv d l)) (.app (.app (.val f) (.val .unit))
        (.app (.val (Val.prim .load)) (.val (Val.loc l)))) := by
    simp [Kont.plug, Expr.subst, Expr.shift, thenE, ubindE, NFv, DFv, Val.shift, Val.pair,
      Val.loc, Val.lam, Expr.val, Val.prim, subst_closedAt d (s := _) hdc (Nat.zero_le _)]
  rw [e₃]
  -- the source's cell
  set cellβ := ResU.single l
    (CellU.mutOf β (Val.loc l₂) σ₀ hσ₀ (famL β P Θ j₀) hw₀) with hcellβ
  have hvu : ResU.Valid cellβ := (ResU.Valid.split hc' hv'').1
  have hkm : (CellU.mutOf β (Val.loc l₂) σ₀ hσ₀ (famL β P Θ j₀) hw₀).kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  have hget : ρ''.get l = some (CellU.mutOf β (Val.loc l₂) σ₀ hσ₀ (famL β P Θ j₀) hw₀) :=
    (ResU.CompS.get_left_of_ne_imm hc' (ResU.single_get_self _ _) hkm).2
  -- step 7: the source's cell is at its view lifetime, and the view types it with `F_o`
  have hcl : c l = some β := by
    have h := consistentX_get hcon hv'' hget (CellU.kind_mutOf _ _ _ _ _ _)
    rwa [CellU.at_mutOf] at h
  obtain ⟨-, -, -, -, -, -, -, hFv, -⟩ :=
    reseal_at_entry (Θ' := Θ) (fun _ _ _ h => h) hcl (vN_fam_down (.ref A) δ β Θ) hm
  -- the parts of the start are consistent with the view
  have hcf : ConsistentX c ρf := consistentX_right hc' hcon hv''
  have hcσ : ConsistentX c σ₀ := consistentX_mut_wit (consistentX_left hc' hcon hv'') hvu
  -- the field's cell
  have hkown : (CellU.ownOf (Loc := Loc) u₀).kind ≠ Kind.imm := by rw [CellU.kind_ownOf]; decide
  have hσ₀l₂ : σ₀.get l₂ = some (CellU.ownOf u₀) :=
    (ResU.CompS.get_left_of_ne_imm hσ₀s (ResU.single_get_self _ _) hkown).2
  have hσu : σu.InStratum β := ResU.CompS.inStratum_right hσ₀s hσ₀
  obtain ⟨-, eβ, -, heβ, -, -⟩ := hvu
  obtain ⟨e₀, he₀, he₀β⟩ := exS_mut_wit_get heβ
  have hcσu : ConsistentX c σu := consistentX_leftE (ResU.CompS.comm hσ₀s) hcσ he₀
  -- step 6 at `A`: every value of `A` is in `Res_β`, as its cell is a `Ref A` value
  have hunifA : ∀ (Θ' : LocTy) (j : Nat) (u : Val) (r : WRes), vN (ℍ := ℍ) A δ Θ' j u r →
      r.InStratum β := by
    intro Θ' j u r h
    obtain ⟨l', hl'⟩ := PMap.exists_fresh loc_infinite r
    obtain ⟨X, hX⟩ := (ResU.compS_defined_iff r (ResU.single l' (CellU.ownOf u))).mpr
      (compatS_single_of_get_none hl')
    exact ResU.CompS.inStratum_left hX
      (hunif Θ' j (Val.loc l') X ⟨l', u, r, rfl, ResU.CompS.comm hX, h⟩)
  -- step 9: the lend's lifetime, fresh, below `β`, the bound and the callback's stratum
  obtain ⟨γ, hγ⟩ := hbnd δ (models_empty_any _)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  obtain ⟨α, hαle, hfr⟩ := LocTy.exists_fresh hΘ.2 (↓(β ⊓ βf ⊓ γ))
  have hαlt : α < β ⊓ βf ⊓ γ := lt_of_le_of_lt hαle (Life.down_sqsubset _)
  have hαβ : α ≤ β := hαlt.le.trans (inf_le_left.trans inf_le_left)
  have houtP : σu.InStratum α := hσu.mono hαβ
  have houtf : ρf.InStratum (↓α) := hβf.mono
    ((Life.down_sqsubset α).le.trans (hαlt.le.trans (inf_le_left.trans inf_le_right)))
  have hLt : LtLife δ bnd α := ⟨γ, hγ, lt_of_lt_of_le hαlt inf_le_right⟩
  -- step 10
  set δ' := δ.extend x α with hδ'
  have hAδ : vN (ℍ := ℍ) A δ' = vN (ℍ := ℍ) A δ := vN_extend_of_not_free hA δ α
  have hBδ : vN (ℍ := ℍ) B δ' = vN (ℍ := ℍ) B δ := vN_extend_of_not_free hB δ α
  set P' : CPredL := fun Θ' j u r => vN (ℍ := ℍ) A δ' Θ' j u r with hP'
  set Fam : Nat → Val → SPropS Loc Val α := famL α P' Θ with hFam
  have hFamD : DownFam α Fam := vN_fam_down A δ' α Θ
  have hwit : Fam j₀ u₀ ⟨σu, houtP⟩ :=
    (vN_above A δ' Θ houtP).mpr (by rw [hAδ]; exact hu₀)
  -- step 13's inclusion: the field's content handed back, with its cell, is in `F_o k`
  have hoi : ∀ k w σ (h : σ.InStratum α) (X : WRes), Fam k w ⟨σ, h⟩ →
      ResU.CompS (ResU.single l₂ (CellU.ownOf w)) σ X →
      ∃ h' : X.InStratum β, famL β P Θ k (Val.loc l₂) ⟨X, h'⟩ := by
    intro k w σ h X hw hX
    have hv : vN (ℍ := ℍ) A δ Θ k w σ := by rw [← hAδ]; exact (vN_above A δ' Θ h).mp hw
    have hr : vN (ℍ := ℍ) (.ref A) δ Θ k (Val.loc l₂) X := ⟨l₂, w, σ, rfl, hX, hv⟩
    exact ⟨hunif Θ k _ X hr, (vN_above (.ref A) δ Θ (hunif Θ k _ X hr)).mpr hr⟩
  -- the opened cell, framed outside the Mut Frame at `ℓ₂`
  set Fr : WProp := fun ρ => ρ = ResU.single l (CellU.ownOf (Val.loc l₂)) with hFr
  set Rc := claimR l₂ α Fam with hRc
  set Gc := CellFold l₂ α Fam with hGc
  set G : ShareG := Gc.sep fun _ => Fr with hGdef
  set Rin : Nat → WProp := fun k => Rc k ⋆ Fr with hRindef
  have hG : ∀ k ls ρ, G k ls ρ → CellFold l β (famL β P Θ) k ls ρ := by
    rintro k ls ρ ⟨ρ₁, ρ₂, h12, ⟨w, χ, h, hw, R, rest, h1, h2⟩, rfl⟩
    obtain ⟨X, hX, hXR⟩ := compS_reassoc' h2 h1
    obtain ⟨h', hw'⟩ := hoi k w χ h X hw hX
    exact ⟨Val.loc l₂, X, h', hw', R, ρ₁, ResU.CompS.comm h12, hXR⟩
  have hRin : ∀ k ρ, Rin k ρ → claimR l β (famL β P Θ) k ρ := by
    rintro k ρ ⟨ρ₁, ρ₂, h12, ⟨w, σ, h, hw, hcl'⟩, rfl⟩
    obtain ⟨h', hw'⟩ := hoi k w σ h ρ₁ hw hcl'
    exact ⟨Val.loc l₂, ρ₁, h', hw', ResU.CompS.comm h12⟩
  set Rout : Nat → WProp := fun k ρ => vN (ℍ := ℍ) (.mut a (.ref A)) δ Θ k (Val.loc l) ρ
    with hRoutd
  have hRout : ∀ k (w : Val) (σ : WRes) (h : σ.InStratum β) (hw : famL β P Θ k w ⟨σ, h⟩),
      Rout k (ResU.single l (CellU.mutOf β w σ h (famL β P Θ k) hw)) :=
    fun k w σ h hw => ⟨α₀, hα₀, β, hα₀β, ⟨l, w, σ, h, k, hw, le_rfl, rfl, hl, rfl⟩, hunif⟩
  -- step 11: the callback's world and view
  set Θ' := Θ.add l₂ α Fam with hΘ'
  set c' := setLife c l₂ α with hc'def
  have hOK' : Θ'.OK := by
    obtain ⟨N, hN⟩ := hΘ.2
    exact ⟨LocTy.down_add hΘ.1 l₂ hFamD, ⟨min N (↓α), LocTy.fresh_add hN (min_le_left _ _)
      (lt_of_le_of_lt (min_le_right _ _) (Life.down_sqsubset α)) l₂ Fam⟩⟩
  have hview : Θ'.view c' = (Θ.view c).set l₂ α Fam := LocTy.view_add Θ c l₂ α Fam
  have hcf' : ConsistentX c' ρf := by
    obtain ⟨-, ex, -, hex, -, -⟩ := hv''
    refine consistentX_setLife hcf (exS_none_of_walk hc' hex fun e₁ he₁ => ?_) α
    obtain ⟨e₀', he₀', hget'⟩ := exS_mut_wit_get he₁
    exact ⟨_, hget' l₂ _ (ExS.get_of_ne_imm he₀' hσ₀l₂ hkown) hkown, hkown⟩
  have hcσu' : ConsistentX c' σu := consistentX_setLife hcσu
    (exS_none_of_walk hσ₀s he₀ fun e₁ he₁ =>
      ⟨_, ExS.get_of_ne_imm he₁ (ResU.single_get_self _ _) hkown, hkown⟩) α
  have hFS : Fo.SuspendC x := suspendC_effOf hS _
  have hbase : tabN (ℍ := ℍ) (CTy.effOf S (.box (.var x) B)) δ' Θ' c' =
      tabN (ℍ := ℍ) Fo δ' Θ' c' := tabN_effOf_base S _ _ δ' Θ' c'
  have hTw : (tabN (ℍ := ℍ) (CTy.effOf S (.box (.var x) B)) δ' Θ' c').Twin
      (tabG (ℍ := ℍ) Rc Gc Fo δ Θ c) := by
    rw [hbase]
    exact tabN_tabG_twin hFS Rc Gc δ Θ' Θ c' c (fun A' hO => vN_add_eq hO δ hfr l₂ Fam)
  have hcanM := tabG_can (ℍ := ℍ) (δ := δ) hfr (c := c) (l := l₂) hFamD Fo.cdepth Fo le_rfl hFS
  rw [← hbase] at hcanM
  have hcanF := tabG_canF (ℍ := ℍ) (x := x) (δ := δ) (Θ := Θ) (c := c) Rc Gc Fr Fo.cdepth Fo
    le_rfl hFS
  have hcanA := tabR_canA (ℍ := ℍ) (x := x) (δ := δ) hΘ.1 hFv hG hRin hRout Fo.cdepth Fo le_rfl
    hFS
  -- step 8: the anti-frame at the source, across stops, raises and layered cancel runs
  have hAF := erwp_M_antiFrameCR (Φ := Θ.view c) hΦ hFv (tabG_tabR_twin Rin G Rout Fo δ Θ c)
    (tabG_afok hFS Rin G δ Θ c) hG hRin hRout hcanA (Q := Qin) k' ls
    (.app (.app (.val f) (.val .unit)) (.app (.val (Val.prim .load)) (.val (Val.loc l))))
    (Val.loc l₂) σ₀ hσ₀ j₀ hw₀ ρf ρ'' hc' (fun W X hW hX => ?_)
  · -- step 13: the claim consistent, the finaliser frame consuming it
    have hM' := erwp_claimX (c := c) hFS k' ls _ ρ'' hcon hAF
    refine erwp_ubindClaimRT hΘ.1 (F := Fo) (δ := δ) (c := c)
      (fun m i en h _ => by obtain ⟨o, ho, rfl, -⟩ := tabN_effOf_some h; exact (hS o ho).2.1)
      (NFv l) (DFv d l) (fun k ls ρ hR => fin_claimM hdc hd hΘ hR.1 hR.2) hQo
      (fun k ls b ρ hq => ?_) k' ls _ ρ'' hM'
    refine erwp_det hΦ (opTableN_down hTd) hQo
      (fun μ => step1Only_plug (Head.beta μ _ b) rfl .hole) ?_
    simp [Kont.plug, Expr.subst, NFv]
    exact erwp_val (v := Val.pair (Val.loc l) b) hq
  -- the `load` from the opened cell `ℓ ↦ own(loc ℓ₂)`
  obtain ⟨X'', hX''1, hX''2⟩ := compS_reassoc' hW hX
  refine erwp_bindR hΦ (opTableGR_local _ _ _) (Kont.appR (.app (.val f) (.val .unit)) .hole) ?_
  refine rwp_load ls l (Val.loc l₂) _
    ⟨_, X'', ResU.CompS.comm hX''2, rfl, fun ρ₁ ρ₂ h1 h2 => ?_⟩
  subst h1
  -- the opened cell framed outside the Mut Frame
  set Q₁ : PostN := fun k ls' v Z => ∀ X₁, ResU.CompS Z (ResU.single l (CellU.ownOf (Val.loc l₂))) X₁ →
    AFPost l β (famL β P Θ) Qin k ls' v X₁ with hQ₁
  refine erwp_mono (fun k ls' b ρ' ⟨ρa, ρb, hab, hq, hρb⟩ => hq _ (by rw [hρb] at hab; exact hab))
    (opTableGR_local _ _ _) _ ls _ ρ₂
    (erwp_frameGR (tabG_tabG_twin Rc Gc Rin G Fo δ Θ c) (tabG_afok hFS Rc Gc δ Θ c) Fr hcanF
      (Q := Q₁) _ ls _ X'' _ ρ₂ h2 rfl ?_)
  -- step 8: the field lent at `α`
  refine erwp_M_frameCRG (Φ := Θ.view c) (l := l₂) (A := α) (F := Fam) hFamD
    (tabN_lendOKCR hS _ δ Θ' c') hTw hcanM (Q := Q₁)
    (k' - 1) j₀ (by omega) ls _ u₀ σu σ₀ ρf X'' houtP houtf (Fam j₀) (fun _ _ h => h) hwit
    hσ₀s (ResU.CompS.comm hX''1) (fun BM hBM => ?_)
  -- step 11: the callback, at the lend's world and view, from the borrow
  rw [← hview]
  have h1 := (hf Θ' ((LocTy.extA_add hfr l₂ Fam).extR ρf) hOK' c' hcf' ls) α hLt
  have hcell : vN (ℍ := ℍ) (.mut (.var x) A) δ' Θ' (k' - 1) (Val.loc l₂)
      (ResU.single l₂ (CellU.mutOf α u₀ σu houtP (Fam j₀) hwit)) :=
    ⟨α, interp_ext_self δ x α, α, le_rfl, lend_mutL Θ l₂ α P' (by omega) houtP hwit,
      fun Θ'' j u r h => (hunifA Θ'' j u r (by rw [← hAδ]; exact h)).mono hαβ⟩
  have hcBM : ConsistentX c' BM := consistentX_compS hBM hcf'
    (consistentX_single_mut hcσu' (by simp [hc'def, setLife]))
  have h2 := h1 Θ' (LocTy.extR_refl _ _) hOK' c' (k' - 1) (by omega) (Val.loc l₂) _ BM hBM
    hcell hcBM
  rw [cN_effOf] at h2
  refine erwp_mono (fun k ls' b ρ' hb => ?_) (opTableN_local _) (k' - 1) ls _ BM h2
  obtain ⟨β', hβ', hbB, hst⟩ := hb
  rw [interp_ext_self] at hβ'
  cases Option.some.inj hβ'
  refine ⟨hst, fun w Y hY σ ⟨hσ, hFσ⟩ Z hZ X₁ hX₁ => ?_⟩
  -- step 12: the result back at `Θ`; step 13: the field's cell with its content in `F_o k`, the
  -- source's cell resealed
  obtain ⟨σ', hσ', hρ'σ'⟩ := compS_reassoc hY hZ
  obtain ⟨h', hw'⟩ := hoi k w σ hσ σ' hFσ hσ'
  have hbB' : vN (ℍ := ℍ) B δ Θ k b ρ' :=
    vN_local B δ Θ l₂ α Fam k b ρ' hst (by rw [← hBδ]; exact hbB)
  exact ⟨Val.loc l₂, σ', h', hw', ρ', Z, ResU.CompS.comm hX₁, ResU.CompS.comm hρ'σ', fun X' hX' =>
    ⟨Val.loc l, b, _, ρ', rfl, ResU.CompS.comm hX', hRout k _ σ' h' hw', hbB'⟩⟩

/-- **`ConstN` for the field reborrow at a suspending row**, from the fundamental property at the
finaliser's derivation. -/
theorem constN_wF (hF : FundamentalN (ℍ := ℍ)) {a : Lifetime.Life} {x : LifeVar}
    {bnd : Lifetime.Life} {A B : VTy} {S : Row} {d : Expr} :
    ConstN (ℍ := ℍ) (.wF a x bnd A B S d) := by
  rintro ⟨hbnd, hA, hB, hS, hdc, hder⟩ δ Θ n _
  exact withborFS_compat hbnd hA hB hS hdc (hF _ _ _ _ hder) δ Θ n

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end

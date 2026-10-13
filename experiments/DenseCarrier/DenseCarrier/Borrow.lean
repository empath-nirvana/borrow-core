import DenseCarrier.FL
import DenseCarrier.Rat
import Core.Compatibility

/-!
# DenseCarrier — a borrow constant over `L`: `withbor` (2)

`Core/Compatibility.lean`'s `withbor2_compatX` (`[TR]` 6.173: `Ref A` lent as `Mut 'x A` to a
callback `∀'x ⊏ ⊓Δ. Mut 'x A ⊸ ['x] B`), re-proved over the relation at every lifetime order `L`
with a slot below every lifetime (`withbor2_compatD`), at payloads of the fragment.

The proof is Core's. Where Core instantiates the callback at the lifetime of the borrow's cell,
the lifetime `α` 6.65's `И` hands over (a slot), it is instantiated here at `ι α`; `И`'s bound is
taken at a slot below `@(⊓Δ)δ` (`fresh_bound`); and the borrow and the result's `[−]` at `ι α` are
the model's at `α` (`ptoMutD_slot`, `boxD_slot`). 6.65 itself is the model's, stated for any
payload predicate (`wpTS_M_frameG`, Core's `wpTS_M_frameX` with `𝒱⟦A⟧δ` abstracted).

Beside it: `[−]` over `L` read on the slots (`outlivesD_iff`), 6.60 non-strict over `L`
(`vD_outlivesLe`), the relation stable along `Ext` (`vD_local`), persistent types at `∅`
(`vD_empty_of_persistent`), and a consumed context at `∅` (`gSepD_deadP`).

`withbor2_compatD` is a statement about `[TR]` 6.173 only when `A` and `B` are in the fragment
(`FragV`): elsewhere `𝒱⟦A⟧` or `𝒱⟦B⟧` is `False` over `L`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace DenseCarrier
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Head Kont)
open BoCa.Lifetime (LifeVar LifeCtx)

variable {L : Type} [LinearOrder L] [OrderTop L]

/-! ### `[−]` over `L`, read on the slots -/

/-- A cell is in the stratum of `γ` over `L` exactly when it is in the stratum of every slot at or
below `γ`. -/
theorem inStratumD_iff (ι : Slots L) (γ : L) (ψ : CellU Loc Val) :
    InStratumD ι γ ψ ↔ ∀ s, ι s ≤ γ → ψ.InStratum s := by
  cases ψ with
  | own v => exact ⟨fun _ _ _ => trivial, fun _ => trivial⟩
  | imm i =>
      show γ < ι i.ls.meet ↔ ∀ s, ι s ≤ γ → s < i.ls.meet
      exact ⟨fun h s hs => ι.lt_iff.mp (lt_of_le_of_lt hs h),
        fun h => not_le.mp fun hle => lt_irrefl _ (h _ hle)⟩
  | «mut» m =>
      show γ < ι m.β ↔ ∀ s, ι s ≤ γ → s < m.β
      exact ⟨fun h s hs => ι.lt_iff.mp (lt_of_le_of_lt hs h),
        fun h => not_le.mp fun hle => lt_irrefl _ (h _ hle)⟩

theorem outlivesD_iff (ι : Slots L) (ρ : WRes) (γ : L) :
    OutlivesD ι ρ γ ↔ ∀ s, ι s ≤ γ → Outlives ρ s := by
  constructor
  · intro h s hs l ψ hl
    exact (inStratumD_iff ι γ ψ).mp (h l ψ hl) s hs
  · intro h l ψ hl
    exact (inStratumD_iff ι γ ψ).mpr fun s hs => h s hs l ψ hl

theorem outlivesD_comp (ι : Slots L) {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (γ : L) :
    OutlivesD ι ρ γ ↔ (OutlivesD ι ρ₁ γ ∧ OutlivesD ι ρ₂ γ) := by
  simp only [outlivesD_iff]
  constructor
  · intro h
    exact ⟨fun s hs => ((outlives_comp hc s).mp (h s hs)).1,
      fun s hs => ((outlives_comp hc s).mp (h s hs)).2⟩
  · rintro ⟨h₁, h₂⟩ s hs
    exact (outlives_comp hc s).mpr ⟨h₁ s hs, h₂ s hs⟩

theorem outlivesD_mono (ι : Slots L) {ρ : WRes} {γ γ' : L} (h : γ' ≤ γ) (ho : OutlivesD ι ρ γ) :
    OutlivesD ι ρ γ' := by
  rw [outlivesD_iff] at ho ⊢
  exact fun s hs => ho s (le_trans hs h)

theorem outlivesD_empty (ι : Slots L) (γ : L) : OutlivesD ι PMap.empty γ :=
  (outlivesD_iff ι _ γ).mpr fun s _ => ResU.inStratum_empty s

theorem outlivesD_single_own (ι : Slots L) (l : Loc) (v : Val) (γ : L) :
    OutlivesD ι (ResU.single l (CellU.ownOf v)) γ :=
  (outlivesD_iff ι _ γ).mpr fun s _ => ResU.inStratum_single_own s l v

/-- `@ρ ⊒ α` over `L`: every stratum strictly below `α` (`OutlivesLe` over `L`). -/
def OutlivesLeD (ι : Slots L) (ρ : WRes) (α : L) : Prop := ∀ γ, γ < α → OutlivesD ι ρ γ

theorem outlivesLeD_comp (ι : Slots L) {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) {α : L}
    (h₁ : OutlivesLeD ι ρ₁ α) (h₂ : OutlivesLeD ι ρ₂ α) : OutlivesLeD ι ρ α :=
  fun γ hγ => (outlivesD_comp ι hc γ).mpr ⟨h₁ γ hγ, h₂ γ hγ⟩

theorem outlivesLeD_of_outlivesD (ι : Slots L) {ρ : WRes} {α : L} (h : OutlivesD ι ρ α) :
    OutlivesLeD ι ρ α :=
  fun _ hγ => outlivesD_mono ι (le_of_lt hγ) h

/-! ### The relation along `Ext` -/

/-- `vD` is stable along `Ext` (`vC_local`). -/
theorem vD_local (ι : Slots L) : ∀ (T : VTy) {ls ls' : List SRec} {δ : LSubD L} {v : Val}
    {ρ : WRes}, Ext ls ls' ρ → vD (ℍ := ℍ) ι T ls δ v ρ → vD (ℍ := ℍ) ι T ls' δ v ρ
  | .unit, _, _, _, _, _, _, h => h
  | .tensor A B, ls, ls', δ, v, ρ, hk, h => by
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      have hk' := hk.right hc
      exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', vD_local ι A (hk'.left hc') h₁,
        vD_local ι B (hk'.right hc') h₂⟩
  | .thunk C, ls, ls', δ, v, ρ, hk, h => fun ls'' hk' => h ls'' (hk.trans hk')
  | .ref A, ls, ls', δ, v, ρ, hk, h => by
      obtain ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho, h₂⟩ := h
      exact ⟨ℓ, v', ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ho,
        vD_local ι A ((hk.right hc).right hc') h₂⟩
  | .box a A, ls, ls', δ, v, ρ, hk, h => by
      obtain ⟨α, hα, hb, ho⟩ := h
      exact ⟨α, hα, vD_local ι A hk hb, ho⟩
  | .mut a A, ls, ls', δ, v, ρ, hk, h => by
      obtain ⟨α, hα, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, hv⟩, b, u, σ, hσ, Q, hw, ls₀, hab, hρ₁, hQ, hls₀,
        hunif⟩ := h
      subst hρ₀
      have hk₁ := hk.right hc
      have hmut : CellIn ρ₁ b :=
        ⟨ℓ, _, by rw [hρ₁]; exact ResU.single_get_self _ _, by simp, le_rfl⟩
      refine ⟨α, hα, ℓ, _, _, hc, ⟨rfl, hv⟩, b, u, σ, hσ, Q, hw, ls₀, hab, hρ₁, hQ, ?_, hunif⟩
      intro x
      rw [hls₀ x]
      exact ⟨fun ⟨hx, hb⟩ => ⟨(hk₁.2 b hmut x hb).mp hx, hb⟩,
             fun ⟨hx, hb⟩ => ⟨(hk₁.2 b hmut x hb).mpr hx, hb⟩⟩
  | .zero, _, _, _, _, _, _, h | .sum _ _, _, _, _, _, _, _, h | .imm _ _, _, _, _, _, _, _, h
  | .bang _, _, _, _, _, _, _, h | .unk, _, _, _, _, _, _, h | .tvar _, _, _, _, _, _, _, h
  | .mu _, _, _, _, _, _, _, h | .int _, _, _, _, _, _, _, h | .fam _, _, _, _, _, _, _, h
  | .opq _, _, _, _, _, _, _, h => h.elim

/-- A frame valid at `vD` is carried to a list with the same members (`vP_same`). -/
theorem vD_same (ι : Slots L) {T : VTy} {ls ls' : List SRec} {δ : LSubD L} {v : Val} {ρ : WRes}
    (h : ∀ x, x ∈ ls' ↔ x ∈ ls) (hv : vD (ℍ := ℍ) ι T ls δ v ρ) : vD (ℍ := ℍ) ι T ls' δ v ρ :=
  vD_local ι T (ext_of_same h ρ) hv

/-! ### Persistent types, and a consumed context -/

/-- At a persistent type the relation holds only at `∅` (`vP_empty_of_persistent`). -/
theorem vD_empty_of_persistent (ι : Slots L) : ∀ (A : VTy), A.Persistent →
    ∀ {ls : List SRec} {δ : LSubD L} {v : Val} {ρ : WRes}, vD (ℍ := ℍ) ι A ls δ v ρ →
      ρ = PMap.empty
  | .unit, _, _, _, _, _, h => h.1
  | .tensor A B, hp, ls, δ, v, ρ, h => by
      simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true] at hp
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hq, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      rw [hq.1] at hc
      rw [vD_empty_of_persistent ι A hp.1 h₁, vD_empty_of_persistent ι B hp.2 h₂] at hc'
      rw [eq_empty_of_compS_empty hc'] at hc
      exact eq_empty_of_compS_empty hc
  | .box _ A, hp, ls, δ, v, ρ, h => by
      obtain ⟨α, -, hb, -⟩ := h
      exact vD_empty_of_persistent ι A hp hb
  | .thunk _, hp, _, _, _, _, _ | .ref _, hp, _, _, _, _, _ | .mut _ _, hp, _, _, _, _, _
  | .imm _ _, hp, _, _, _, _, _ | .fam _, hp, _, _, _, _, _ | .opq _, hp, _, _, _, _, _ =>
      absurd hp (by simp [VTy.Persistent, VTy.persistent])
  | .zero, _, _, _, _, _, h | .sum _ _, _, _, _, _, _, h | .bang _, _, _, _, _, _, h
  | .unk, _, _, _, _, _, h | .tvar _, _, _, _, _, _, h | .mu _, _, _, _, _, _, h
  | .int _, _, _, _, _, _, h => h.elim

/-- A consumed context, up to persistent slots, contributes nothing (`gSepC_deadP`). -/
theorem gSepD_deadP (ι : Slots L) {ls : List SRec} {δ : LSubD L} : ∀ {Γ : Ctx VTy}, Ctx.DeadP Γ →
    ∀ {γ : List Val} {ρ : WRes}, gSepD (ℍ := ℍ) ι ls δ Γ γ ρ → ρ = PMap.empty := by
  intro Γ hd
  induction hd with
  | nil => intro γ ρ h; cases γ <;> exact h.1
  | cons _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact h.1
      | cons v γ' => exact ih (γ := γ') h
  | drop hT _ ih =>
      intro γ ρ h
      cases γ with
      | nil => exact h.1
      | cons v γ' =>
          obtain ⟨ρ₁, ρ₂, hc, hv, hrest⟩ := h
          obtain rfl := vD_empty_of_persistent ι _ hT hv
          rw [eq_of_compS_empty_left hc]
          exact ih hrest

/-! ### `[TR]` 6.65 for any payload predicate -/

/-- `ptoMutX_create` for any payload predicate. -/
theorem ptoMutS_createG {l : Loc} {α b : Life} {ls : List SRec} {P : List SRec → Val → WProp}
    {Q : Val → SPropS Loc Val b} (hab : α ⊑ b) (hQ : ofS Q = fun v => P ls v)
    (hfresh : ∀ x ∈ ls, x.2 ⊐ b) (hunif : ∀ ls' u' σ', P ls' u' σ' → σ'.InStratum b)
    {u : Val} {σ : WRes} (hσ : σ.InStratum b) (hv : P ls u σ) :
    ∃ hw : Q u ⟨σ, hσ⟩, ptoMutS l α ls P (ResU.single l (CellU.mutOf b u σ hσ Q hw)) := by
  have hw : Q u ⟨σ, hσ⟩ := by
    have : ofS Q u σ := by rw [hQ]; exact hv
    exact this.2
  exact ⟨hw, b, u, σ, hσ, Q, hw, ls, hab, rfl, hQ, strat_fresh hfresh, hunif⟩

/-- **`[TR]` Theorem 6.65 (`Mut Frame`) at the tagged `wpTS`, for any payload predicate**:
`wpTS_M_frameX` with `𝒱⟦T⟧δ` abstracted to `P`, its two uses of the relation made hypotheses
(`P ⊨ [β]P` at every list, and `P` the same at lists with the same members). The proof is
`wpTS_M_frameX`'s. -/
theorem wpTS_M_frameG (l : BoCa.Loc) (P : List SRec → Val → WProp) (β : Life)
    (hP : ∀ ls w σ, P ls w σ → σ.InStratum β)
    (hloc : ∀ ls ls' w σ, (∀ x, x ∈ ls' ↔ x ∈ ls) → P ls w σ → P ls' w σ)
    (v : Val) (e : Expr) (ls : List SRec) (Q : List SRec → Val → WProp) :
    Entails
      (ptoOwn l v ⋆ P ls v ⋆
        fresh (fun α => ptoMutS l α ls (fun ls₀ => P ls₀) ─⋆
          wpTS ls e (fun ls'' v' =>
            box α (all fun w => ptoOwn l w ─⋆ (P ls'' w ─⋆ Q ls'' v')))))
      (wpTS ls e Q) := by
  classical
  intro ρ hH2 ρf sρ ps hH3 hsρ hT htg alc kc
  have hvsρ : ResU.Valid sρ := hash_valid_comp hH3 hsρ
  -- 6.112 pulls `ℓ ↦ v ⋆ P̂(v)` inside the `⋔`
  obtain ⟨γ, hγ⟩ := fresh_frame (ptoOwn l v ⋆ P ls v) _ ρ
    (BoLo.sep_assoc' _ _ _ ρ hH2)
  -- H4: a lifetime shorter than `γ`, `β` and every tag
  obtain ⟨b₀, hb₀⟩ := exists_fresh ls
  set A : Life := b₀ ⊓ (↓(γ ⊓ β)) with hAdef
  have hAγ : A ⊏ γ :=
    lt_of_le_of_lt inf_le_right (lt_of_lt_of_le (Life.down_sqsubset _) inf_le_left)
  have hAβ : A ⊏ β :=
    lt_of_le_of_lt inf_le_right (lt_of_lt_of_le (Life.down_sqsubset _) inf_le_right)
  have hAtag : ∀ x ∈ ls, x.2 ⊐ A := fun x hx => lt_of_le_of_lt inf_le_left (hb₀ x hx)
  obtain ⟨hbody, houtρ⟩ := hγ A hAγ
  -- 6.104 splits the box over the `⋆`
  obtain ⟨ρlP, ρb, hcρ, hlP, hwand⟩ := hbody
  obtain ⟨hlPv, houtlP⟩ := hlP
  obtain ⟨ρl, ρP, hclP, hpl, hPv⟩ := hlPv
  subst hpl
  -- H10 and H11
  have houtP : ResU.InStratum A ρP := ResU.CompS.inStratum_right hclP houtlP
  have houtb : ResU.InStratum A ρb := ResU.CompS.inStratum_right hcρ houtρ
  -- `P̂ ⊧ [β] P̂` is what puts `P̂`'s resources in `Res_A`
  have hunif : ∀ ls' w σ, P ls' w σ → ResU.InStratum A σ := fun ls' w σ h m ψ hm =>
    CellU.InStratum.mono (le_of_lt hAβ) (hP ls' w σ h m ψ hm)
  set Qs : Val → SPropS BoCa.Loc BoCa.Val A :=
    (fun (w : Val) (r : ResS BoCa.Loc BoCa.Val A) => P ls w r.1) with hQs
  have hofS : BoLo.ofS Qs = fun w => P ls w := by
    funext w σ
    exact propext ⟨fun h => h.2, fun h => ⟨hunif ls w σ h, h⟩⟩
  -- the "fictional" `ρ_m = ℓ ↦ mut(α, v, ρ_P̂(v), P̂)`, well formed by H4
  obtain ⟨hwit, hcellm⟩ := ptoMutS_createG (l := l) (α := A) (le_refl A) hofS hAtag
    hunif houtP hPv
  set ρm : ResU BoCa.Loc BoCa.Val :=
    ResU.single l (CellU.mutOf A v ρP houtP Qs hwit) with hρm
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  -- H12-H17: the compatibility block
  have hlPcell : ResU.CompS ρP (ResU.single l (CellU.ownOf v)) ρlP :=
    ResU.CompS.comm hclP
  have hH12 : ResU.Hash ρb ρlP :=
    ⟨ResU.CompatS.symm hcρ.1, ρ, ResU.CompS.comm hcρ, hvρ⟩
  have hH13 : ResU.Hash ρb ρm := (ResU.six24 hlPcell).mpr hH12
  obtain ⟨hlPf, hbf⟩ := ResU.Hash.split hcρ (ResU.hash_symm hH3)
  have hH15 : ResU.Hash ρf ρm :=
    (ResU.six24 hlPcell).mpr (ResU.hash_symm hlPf)
  obtain ⟨BM, hBM⟩ := (ResU.compS_defined_iff ρb ρm).mpr hH13.1
  have hH17 : ResU.Hash ρf BM :=
    ResU.hash_of_pairwise (ResU.hash_symm hbf) hH13 hH15 hBM
  obtain ⟨fρ, h4, hvfρ⟩ := hH17.2
  obtain ⟨FB, hFB⟩ := (ResU.compS_defined_iff ρf ρb).mpr (ResU.hash_symm hbf).1
  obtain ⟨FB₁, hFB₁, hFBm⟩ := (ResU.CompS.assoc ρf ρb ρm fρ).mp ⟨BM, hBM, h4⟩
  obtain rfl : FB = FB₁ := ResU.CompS.functional hFB hFB₁
  obtain ⟨FB₂, hFB₂, hFBl⟩ :=
    (ResU.CompS.assoc ρf ρb ρlP sρ).mp ⟨ρ, ResU.CompS.comm hcρ, hsρ⟩
  obtain rfl : FB = FB₂ := ResU.CompS.functional hFB hFB₂
  -- entry: `TW.mutFold`
  have hTin : TW fρ ps (rsOf ls) :=
    TW.mutFold hT hclP (ResU.CompS.comm hFBl) (ResU.CompS.comm hFBm) hvfρ
  have htgin : Tagged fρ ps ls := tagged_of_ag (fun a ha =>
    (mut_fold_ag hclP (ResU.CompS.comm hFBl) (ResU.CompS.comm hFBm) a).mpr ha) htg
  -- H18: the wand, at the fictional borrow
  have hwpBM := hwand ρm BM hcellm hBM
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v', μ, μ', ps'', ls'',
    h1, h2, h3, h5, h6, h7, h8, h9, h10, h11, hT'', htg'', hps'', hls'', h12⟩ :=
    hwpBM ρf fρ ps hH17 h4 hTin htgin alc kc
  -- H24 and H25: unfolding `[α]`
  obtain ⟨hwand', houtρ'⟩ := h12
  -- H26: 6.27 -- the borrow is still at the top level of `ρ′ ● ρ⁺`
  obtain ⟨v'', χ, hχ, hwit'', hsplit''⟩ := ResU.six27 houtb hBM h10
  have hπl : π.get l = some (CellU.mutOf A v'' χ hχ Qs hwit'') := by
    rw [ResU.Comp.get_of_left_none hsplit'' (ResU.del_get_self _ _)]
    exact ResU.single_get_self _ _
  have hkm'' : (CellU.mutOf A v'' χ hχ Qs hwit'').kind ≠ Kind.imm := by
    rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c
  obtain ⟨hρ'ln, hppl⟩ :
      ρ'.get l = none ∧ ρp.get l = some (CellU.mutOf A v'' χ hχ Qs hwit'') := by
    rcases ResU.CompS.get_split_of_ne_imm h9 hπl hkm'' with ⟨hg, -⟩ | ⟨hg, hp⟩
    · exfalso
      have hcon := houtρ' l _ hg
      rw [CellU.inStratum_mutOf] at hcon
      exact absurd hcon (lt_irrefl _)
    · exact ⟨hg, hp⟩
  have hpd : ResU.CompS (ρp.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) ρp := ResU.del_compS hppl
  obtain ⟨RPD, hRPD, hRPDm⟩ :=
    (ResU.CompS.assoc ρ' (ρp.del l)
      (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) π).mp ⟨ρp, hpd, h9⟩
  have hvπ : ResU.Valid π := h10.2.2
  have hvm'' : ResU.Valid (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) :=
    (ResU.Valid.split hRPDm hvπ).2
  obtain ⟨W'', hW''⟩ := ResU.compS_own_of_valid_mut hvm''
  have hRPDmH : ResU.Hash RPD (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) :=
    ⟨hRPDm.1, π, hRPDm, hvπ⟩
  have hH27 : ResU.Hash RPD W'' := (ResU.six24 hW'').mp hRPDmH
  obtain ⟨hfρ', hρ'p⟩ := ResU.Hash.split h2 (ResU.hash_symm h3)
  obtain ⟨hPDf, -⟩ := ResU.Hash.split hpd (ResU.hash_symm hfρ')
  obtain ⟨hρ'PD, -⟩ := ResU.Hash.split hpd (ResU.hash_symm hρ'p)
  obtain ⟨hρ'W'', hPDW''⟩ := ResU.Hash.split hRPD hH27
  have hfm'' : ResU.Hash ρf W'' :=
    (ResU.six24 hW'').mp (ResU.hash_symm (ResU.Hash.split hpd (ResU.hash_symm hfρ')).2)
  obtain ⟨R, hR⟩ := (ResU.compS_defined_iff ρ' W'').mpr hρ'W''.1
  have hfR : ResU.Hash ρf R :=
    ResU.hash_of_pairwise (ResU.hash_symm h1) hρ'W'' hfm'' hR
  obtain ⟨FR, hFR⟩ := (ResU.compS_defined_iff ρf R).mpr hfR.1
  have hPDR : ResU.Hash (ρp.del l) R :=
    ResU.hash_of_pairwise hρ'PD hρ'W'' hPDW'' hR
  have hPDFR : ResU.Hash (ρp.del l) FR :=
    ResU.hash_of_pairwise hPDf hfR hPDR hFR
  obtain ⟨FRP, hFRP⟩ := (ResU.compS_defined_iff FR (ρp.del l)).mpr (ResU.hash_symm hPDFR).1
  obtain ⟨RP, hRP⟩ := (ResU.compS_defined_iff R (ρp.del l)).mpr (ResU.hash_symm hPDR).1
  -- H33: the two memories, by 6.25 under a frame (6.8)
  have hvlP : ResU.Valid ρlP := by
    obtain ⟨-, s, hs, hv⟩ := hH12; exact (ResU.Valid.split hs hv).2
  have hvBM : ResU.Valid BM := by
    obtain ⟨-, s, hs, hv⟩ := hH17; exact (ResU.Valid.split hs hv).2
  have hvmm : ResU.Valid ρm := (ResU.Valid.split hBM hvBM).2
  have hFBmH : ResU.Hash FB ρm :=
    ResU.hash_symm (ResU.hash_of_pairwise (ResU.hash_symm hH15)
      (ResU.hash_symm hbf) (ResU.hash_symm hH13) hFB)
  have hFBlH : ResU.Hash FB ρlP :=
    ResU.hash_symm (ResU.hash_of_pairwise hlPf (ResU.hash_symm hbf) (ResU.hash_symm hH12) hFB)
  have hmem₁ : ResU.Lower sρ μ :=
    (ResU.lower_swap_mut_own hlPcell hvmm hvlP hFBm hFBmH hFBl hFBlH).mp h5
  obtain ⟨FP, hFP, hFPm⟩ := (ResU.CompS.assoc fρ' (ρp.del l)
    (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) fρ'p).mp ⟨ρp, hpd, h6⟩
  obtain ⟨RP₁, hRP₁, hfRP⟩ := (ResU.CompS.assoc ρf R (ρp.del l) FRP).mpr ⟨FR, hFR, hFRP⟩
  obtain rfl : RP = RP₁ := ResU.CompS.functional hRP hRP₁
  obtain ⟨WP, hWP, hρ'WP⟩ := (ResU.CompS.assoc ρ' W'' (ρp.del l) RP).mpr ⟨R, hR, hRP⟩
  obtain ⟨RPD₁, hRPD₁, hRPDW⟩ :=
    (ResU.CompS.assoc ρ' (ρp.del l) W'' RP).mp ⟨WP, ResU.CompS.comm hWP, hρ'WP⟩
  obtain rfl : RPD = RPD₁ := ResU.CompS.functional hRPD hRPD₁
  obtain ⟨FPD, hFPD, hFPDW⟩ :=
    (ResU.CompS.assoc ρf RPD W'' FRP).mp ⟨RP, hRPDW, hfRP⟩
  obtain ⟨FP₁, hFP₁, hFPρ'⟩ := (ResU.CompS.assoc ρf ρ' (ρp.del l) FP).mpr ⟨fρ', h2, hFP⟩
  obtain rfl : RPD = FP₁ := ResU.CompS.functional hRPD hFP₁
  obtain rfl : FP = FPD := ResU.CompS.functional hFPρ' hFPD
  have hvfρ'p : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h7; exact ⟨σ, hσ⟩
  have hvFRP : ResU.Valid FRP := by
    obtain ⟨-, s, hs, hv⟩ := ResU.hash_symm hPDFR
    exact ResU.CompS.functional hs hFRP ▸ hv
  have hvW'' : ResU.Valid W'' := by
    obtain ⟨-, s, hs, hv⟩ := hH27; exact (ResU.Valid.split hs hv).2
  have hFPmH : ResU.Hash FP (ResU.single l (CellU.mutOf A v'' χ hχ Qs hwit'')) :=
    ⟨hFPm.1, fρ'p, hFPm, hvfρ'p⟩
  have hFPWH : ResU.Hash FP W'' := ⟨hFPDW.1, FRP, hFPDW, hvFRP⟩
  have hmem₂ : ResU.Lower FRP μ' :=
    (ResU.lower_swap_mut_own hW'' hvm'' hvW'' hFPm hFPmH hFPDW hFPWH).mp h7
  -- H34: `ρ ↭ ρ′ ● ρ''_v ● ℓ ↦ own(v'') ● ρ⁺/ℓ`, by 6.28
  have hvRP : ResU.Valid RP := by
    obtain ⟨-, s, hs, hv⟩ := hH27
    exact ResU.CompS.functional hs hRPDW ▸ hv
  have hupd : ResU.Upd ρ RP :=
    (ResU.six28 hlPcell hW'' hBM hRPDm (ResU.CompS.comm hcρ) hRPDW
      hvBM hvπ hvρ hvRP).mp h10.1
  have hno : BoLo.NoOwn (ρp.del l) := by
    refine PMap.ext fun x => ?_
    cases hgg : ((ρp.del l).restrict Kind.own).get x with
    | none => simp
    | some ψ =>
        exfalso
        obtain ⟨hdd, hk⟩ := ResU.restrict_eq_some.mp hgg
        by_cases hx : x = l
        · subst hx; rw [ResU.del_get_self] at hdd; simp at hdd
        · rw [ResU.del_get_ne _ hx] at hdd
          have hcc : (ρp.restrict Kind.own).get x = some ψ :=
            ResU.restrict_eq_some.mpr ⟨hdd, hk⟩
          rw [h11] at hcc
          simp at hcc
  -- exit: `TW.mutUnfold`
  have hTout : TW FRP ps'' (rsOf ls'') :=
    TW.mutUnfold hT'' (ResU.CompS.comm hFPm) (ResU.CompS.comm hW'')
      (ResU.CompS.comm hFPDW) hvFRP
  have htgout : Tagged FRP ps'' ls'' := tagged_of_ag (fun a ha =>
    (mut_fold_ag (ResU.CompS.comm hW'') (ResU.CompS.comm hFPDW) (ResU.CompS.comm hFPm) a).mp
      ha) htg''
  -- H35: the callback's wand, at the value the run leaves in the cell, read at the list the
  -- run returns
  have hχv : P ls'' v'' χ := hloc ls ls'' v'' χ hls'' (show P ls v'' χ from hwit'')
  obtain ⟨y, hy₁, hy₂⟩ :=
    (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v'')) χ R).mp
      ⟨W'', ResU.CompS.comm hW'', hR⟩
  have hQ : Q ls'' v' R := (hwand' v'' _ y rfl hy₁) χ R hχv hy₂
  exact ⟨R, ρp.del l, FR, FRP, RP, v', μ, μ', ps'', ls'',
    ResU.hash_symm hfR, hFR, hPDFR, hmem₁, hFRP, hmem₂, h8, hRP,
    ⟨hupd, hvρ, hvRP⟩, hno, hTout, htgout, hps'', hls'', hQ⟩

/-! ### The typing's lifetime premises, read in `L` -/

/-- A reading over `L` re-read in `ℕᵒᵈ` by rank models what it models. -/
theorem rank_models {Δ : LifeCtx} {δ : LSubD L} (hδ : ModelsD Δ δ) :
    Δ.Models (toLSub (δ.map (rankIn (valsD δ)))) := by
  intro x u hu
  obtain ⟨m, n, hm, hn, hlt⟩ := hδ x u hu
  refine ⟨OrderDual.ofDual (rankIn (valsD δ) m), OrderDual.ofDual (rankIn (valsD δ) n), ?_, ?_, ?_⟩
  · rw [toLSub_find?, LSubD.find?_map, hm]; rfl
  · rw [interp_toLSub, interpD_map (rankIn_mono _) (rankIn_top _), hn]; rfl
  · exact rankIn_strict _ (interpD_mem_valsD δ u hn) hlt

/-- **Core's `Δ ⊨ @a` holds over every lifetime order `L`.** -/
theorem definedD_of_defines {Δ : LifeCtx} {a : Lifetime.Life} (h : Δ.Defines a) {δ : LSubD L}
    (hδ : ModelsD Δ δ) : ∃ α, interpD δ a = some α := by
  obtain ⟨n, hn⟩ := h _ (rank_models hδ)
  rw [interp_toLSub, interpD_map (rankIn_mono _) (rankIn_top _)] at hn
  cases hα : interpD δ a with
  | none => rw [hα] at hn; simp at hn
  | some α => exact ⟨α, rfl⟩

/-! ### 6.60 over `L`, non-strict -/

/-- **`[TR]` 6.60 at `Δ ⊢ T ⊒ @a` over `L`** (`vC_outlivesLe`), at the fragment: the resource of
a value of `T` is in every stratum strictly below `@aδ`. -/
theorem vD_outlivesLe (ι : Slots L) {Δ : LifeCtx} {δ : LSubD L} {a : Lifetime.Life} {α : L}
    (hδ : ModelsD Δ δ) (ha : interpD δ a = some α) :
    ∀ {T : VTy}, VOutlivesLe Δ a T → ∀ (ls : List SRec) (v : Val) (ρ : WRes),
      vD (ℍ := ℍ) ι T ls δ v ρ → OutlivesLeD ι ρ α := by
  intro T hT
  induction hT with
  | unit =>
      intro ls v ρ h
      obtain ⟨rfl, -⟩ := h
      exact outlivesLeD_of_outlivesD ι (outlivesD_empty ι α)
  | tensor _ _ ih₁ ih₂ =>
      intro ls v ρ h
      obtain ⟨v₁, v₂, hs⟩ := h
      obtain ⟨-, ρ₁, ρ₂, hc, g₁, g₂⟩ := pure_sep_iff.mp hs
      exact outlivesLeD_comp ι hc (ih₁ ls v₁ ρ₁ g₁) (ih₂ ls v₂ ρ₂ g₂)
  | zero => intro ls v ρ h; exact h.elim
  | sum _ _ => intro ls v ρ h; exact h.elim
  | ref _ ih =>
      intro ls v ρ h
      obtain ⟨ℓ, w, hs⟩ := h
      obtain ⟨-, ρ₁, ρ₂, hc, rfl, g₂⟩ := pure_sep_iff.mp hs
      exact outlivesLeD_comp ι hc
        (outlivesLeD_of_outlivesD ι (outlivesD_single_own ι ℓ w α)) (ih ls w ρ₂ g₂)
  | bang => intro ls v ρ h; exact h.elim
  | box hle =>
      intro ls v ρ h
      obtain ⟨β, hb, -, ho⟩ := h
      obtain ⟨α', β', ha', hb', hle'⟩ := entailsLeD_of_entailsLe (L := L) hle δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hb] at hb'; cases Option.some.inj hb'
      exact fun γ hγ => outlivesD_mono ι (le_of_lt (lt_of_lt_of_le hγ hle')) ho
  | imm _ => intro ls v ρ h; exact h.elim
  | «mut» hle =>
      intro ls v ρ h
      obtain ⟨β, hb, ℓ, ρ₀, ρ₁, hc, ⟨hρ₀, -⟩, b, u, σ, hσ, Q, hw, _ls₀, hβb, hρ₁, -, -, -⟩ := h
      subst hρ₀
      have e := eq_of_compS_empty_left hc
      subst e; subst hρ₁
      obtain ⟨α', β', ha', hb', hle'⟩ := entailsLeD_of_entailsLe (L := L) hle δ hδ
      rw [ha] at ha'; cases Option.some.inj ha'
      rw [hb] at hb'; cases Option.some.inj hb'
      intro γ hγ l ψ hl
      have hψ : ψ = CellU.mutOf b u σ hσ Q hw := by
        by_cases hll : l = ℓ
        · subst hll; rw [ResU.single_get_self] at hl; exact (Option.some.inj hl).symm
        · simp [ResU.single, hll] at hl
      subst hψ
      exact lt_of_lt_of_le hγ (le_trans hle' hβb)
  | tvar => intro ls v ρ h; exact h.elim
  | mu _ _ => intro ls v ρ h; exact h.elim
  | int => intro ls v ρ h; exact h.elim
  | opq => intro ls v ρ h; exact h.elim
  | fam _ _ => intro ls v ρ h; exact h.elim

/-! ### `withbor` (2) over `L` -/

/-- **`[TR]` Lemma 6.173 (`withbor-compat2`) over `L`** (`withbor2_compatX`): `Ref A` lent as
`Mut 'x A` to a callback `∀'x ⊏ ⊓Δ. Mut 'x A ⊸ ['x] B`, with Core's premises, at every lifetime
order with a slot below every lifetime (`hι`). The callback is instantiated at the position
`ι α` of the slot `α` at which 6.65 makes the borrow's cell. -/
theorem withbor2_compatD (ι : Slots L) (hι : ∀ m : L, ∃ s, ι s < m) {Δ : LifeCtx}
    {Γ : Ctx VTy} {A B : VTy} (x : LifeVar) (hΓ : Ctx.DeadP Γ) (_hx : Δ.find? x = none)
    (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
    SemD (ℍ := ℍ) ι Δ Γ withbor (.ret (axWithbor2Ty x Δ.meetOfDom A B)) := by
  intro δ γ ls ρ hδ hg
  have hρ : ρ = PMap.empty := gSepD_deadP ι hΓ ((gDenD_iff ι).mp hg).2
  subst hρ
  show wpTS ls withbor _ _
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ v₁ ρ₁ τ₀ hv₁ hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨ℓ, vℓ, hs₁⟩ := hv₁
  obtain ⟨rfl, ρℓ, ρP, hcℓ, hown, hP⟩ := pure_sep_iff.mp hs₁
  have hβ₁ : Expr.subst 0 (Val.loc ℓ)
        (Expr.val (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))))
      = Expr.val (Val.lam (.pair (.val (.loc ℓ))
          (.app (.app BoCa.v0 unit') (.val (.loc ℓ))))) := by
    simp [Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, unit']
  refine wpTS_lolli _ _ (Val.loc ℓ) _ _ ?_
  rw [hβ₁]
  refine wpTS_val _ _ _ _ ?_
  intro ls₂ hext₂ vf ρ₂ τ hvf hc₂
  have hβ₂ : Expr.subst 0 vf
        (Expr.pair (.val (.loc ℓ)) (.app (.app BoCa.v0 unit') (.val (.loc ℓ))))
      = Expr.pair (.val (.loc ℓ))
          (.app (.app (.val vf) (.val .unit)) (.val (.loc ℓ))) := by
    simp [Expr.subst, BoCa.v0, unit']
  refine wpTS_lolli _ _ vf _ _ ?_
  rw [hβ₂]
  have hP₂ : vD (ℍ := ℍ) ι A ls₂ δ vℓ ρP := vD_local ι A (hext₂.right hcℓ) hP
  -- 6.60 over `L` at the side condition's `@bδ`, read at a slot below it
  obtain ⟨b, hdef, hO⟩ := hside
  obtain ⟨β, hb⟩ := definedD_of_defines hdef hδ
  obtain ⟨s₀, hs₀⟩ := hι β
  have hβ : ∀ ls' w σ', vD (ℍ := ℍ) ι A ls' δ w σ' → σ'.InStratum s₀ :=
    fun ls' w σ' h => (outlivesD_slot ι σ' s₀).mp (vD_outlivesLe ι hδ hb hO ls' w σ' h _ hs₀)
  obtain ⟨σ, hcσ, hcτ⟩ := compS_reassoc hcℓ hc₂
  refine wpTS_M_frameG ℓ (fun ls₀ => vD (ℍ := ℍ) ι A ls₀ δ) s₀ hβ
    (fun _ _ _ _ h hv => vD_same ι h hv) vℓ _ ls₂
    (fun ls' => vD (ℍ := ℍ) ι (.tensor (.ref A) B) ls' δ) τ
    ⟨ρℓ, σ, hcτ, hown, ρP, ρ₂, hcσ, hP₂, ?_⟩
  obtain ⟨a₂, ha₂⟩ := ρ₂.exists_atLife
  have hdefm : Δ.Defines Δ.meetOfDom := fun δ' hδ' =>
    Lifetime.Life.interp_defined_of_wf hδ' (Lifetime.meetOfDomL_wf Δ.entries)
  obtain ⟨m, hm⟩ := definedD_of_defines hdefm hδ
  -- `И`'s bound: a slot below `@ρ₂` every slot below which sits below `@(⊓Δ)δ` in `L`
  obtain ⟨b₀, hb₀a, hb₀m⟩ := fresh_bound ι a₂ (hι m)
  refine ⟨b₀, fun α hα => ⟨?_, outlives_of_atLife ha₂ (lt_of_lt_of_le hα hb₀a)⟩⟩
  -- `─⋆R`: take the borrow `ℓ ↦ M α 𝒱⟦A⟧δ`, the callback's `Mut 'x A` at `ι α`
  intro ρm σ' hm' hcm
  have hmut' : vD (ℍ := ℍ) ι (.mut (.var x) A) ls₂ (δ.extend x (ι α)) (.loc ℓ) ρm := by
    have e : (fun ls₀ => vD (ℍ := ℍ) ι A ls₀ (δ.extend x (ι α))) =
        (fun ls₀ => vD (ℍ := ℍ) ι A ls₀ δ) :=
      funext fun ls₀ => vD_extend_of_not_free ι hfree₁ ls₀ δ (ι α)
    refine ⟨ι α, LSubD.find?_extend_self δ x (ι α), ℓ, pure_sep_mk rfl ?_⟩
    show ptoMutD ι ℓ (ι α) ls₂ (fun ls₀ => vD (ℍ := ℍ) ι A ls₀ (δ.extend x (ι α))) ρm
    rw [e, ptoMutD_slot]
    exact hm'
  refine wpTS_bind (.pairR (.loc ℓ) .hole)
    (.app (.app (.val vf) (.val .unit)) (.val (.loc ℓ))) ls₂ _ σ' ?_
  have hlt : LtLifeD δ Δ.meetOfDom (ι α) := ⟨m, hm, hb₀m α hα⟩
  have hwpf := hvf ls₂ (Ext.refl _ _) (ι α) PMap.empty ρ₂ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ₂)
  refine wpTS_bind_frame (.appL .hole (.loc ℓ)) (.app (.val vf) (.val .unit)) ls₂
    (fun ls'' => vD (ℍ := ℍ) ι (.lolli (.mut (.var x) A) (.box (.var x) B)) ls''
      (δ.extend x (ι α)))
    (fun ls'' => vD (ℍ := ℍ) ι (.mut (.var x) A) ls'' (δ.extend x (ι α)) (.loc ℓ)) _
    (fun ls'' hls ρ h => vD_same ι hls h) ?_ σ' ⟨ρ₂, ρm, hcm, hwpf, hmut'⟩
  rintro ls'' - vg σ'' ⟨σ₁, σ₂, hcσ'', hvg, hmut''⟩
  simp only [Kont.plug]
  refine wpTS_mono (fun ls₃ v'' ρ'' hb => ?_) σ''
    (hvg ls'' (Ext.refl _ _) (.loc ℓ) σ₂ σ'' hmut'' hcσ'')
  -- the callback's `['x] B` at `ι α` is the model's `[α]`
  obtain ⟨α', hα', hB, hout⟩ := hb
  change (δ.extend x (ι α)).find? x = some α' at hα'
  rw [LSubD.find?_extend_self] at hα'
  cases Option.some.inj hα'
  have hB' : vD (ℍ := ℍ) ι B ls₃ δ v'' ρ'' := by
    rw [vD_extend_of_not_free ι hfree₂] at hB; exact hB
  refine wpTS_val ls₃ (.pair (.loc ℓ) v'') _ ρ'' ?_
  refine ⟨fun w c₁ c₂ hc₁ hcc p₁ p₂ hp hcp => ?_, (outlivesD_slot ι ρ'' α).mp hout⟩
  obtain ⟨s, hs, hρs⟩ := compS_reassoc hcc hcp
  exact ⟨.loc ℓ, v'', pure_sep_mk rfl
    ⟨s, ρ'', ResU.CompS.comm hρs, ⟨ℓ, w, pure_sep_mk rfl ⟨c₁, p₁, hs, hc₁, hp⟩⟩, hB'⟩⟩

/-- At `WithTop ℚ` with Core's slots at `-n` (`ratSlots`). -/
theorem withbor2_compatD_rat {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (x : LifeVar)
    (hΓ : Ctx.DeadP Γ) (hx : Δ.find? x = none) (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
    SemD (ℍ := ℍ) ratSlots Δ Γ withbor (.ret (axWithbor2Ty x Δ.meetOfDom A B)) :=
  withbor2_compatD ratSlots ratSlots_unbounded x hΓ hx hside hfree₁ hfree₂

end DenseCarrier

end

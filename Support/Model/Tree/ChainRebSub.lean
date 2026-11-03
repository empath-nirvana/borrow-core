import Support.Model.Tree.Port.SubDef
import Support.Model.Tree.ChainUpd

/-!
# `reb_α` and `⊟` along `chainEquiv`

`[spec §62]`. Row 5.28 (`reb_α`, `Tree/Port/RebDef.lean`) and Definition 6.3 (`⊟`,
`Tree/Port/SubDef.lean`) at the tree-stratified carrier are the printed rows at `WCactus.chain`:
`chain_reb_iff`, `chain_sub_iff`, `chain_subL_iff`, `chain_subKeep_iff`. Both read cells by
lifetime set, value and witness, which `ΦU` keeps; a lifetime `α` is the stratum `{α}`
(`chain_inStratum_iff`), a printed `LSet` the finite set of its members (`TSet.ofLSet`), and
a `mut` cell at `β` the tree's at `{β}` (`ΨU_mutOf`).
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

variable {Loc Val : Type}

/-! ### Cells and strata read through `ΦU` -/

theorem ΦU_immOf_eq {s : TSet} {v : Val} {χ : ResUT Loc Val WCactus.chain} {h : χ.InStratum s}
    {L : LSet} {χ' : ResU Loc Val} {h' : χ'.InStratum L.join} (hL : s.toLSet = L)
    (hχ : χ.map ΦU = χ') : ΦU (CellUT.immOf s v χ h) = CellU.immOf L v χ' h' := by
  rw [ΦU_immOf]; exact CellU.immOf_congr hL rfl hχ _ _

theorem ΦU_ownOf (v : Val) : ΦU (CellUT.ownOf (K := WCactus.chain) (Loc := Loc) v) = CellU.ownOf v :=
  rfl

/-- `Res_S` at the chain is the printed `Res_{⊔S}`. -/
theorem chain_inStratum_jn_iff {S : TSet} {ρ : ResUT Loc Val WCactus.chain} :
    ρ.InStratum S ↔ ResU.InStratum S.jn (ρ.map ΦU) := by
  refine ⟨ΦU_map_inStratum, fun h l ψ e => ?_⟩
  exact ΦU_inStratum_iff.mp (h l _ (map_ΦU_get.mpr e))

theorem inStratum_ofLSet_iff {L : LSet} {ρ : ResUT Loc Val WCactus.chain} :
    ρ.InStratum (TSet.ofLSet L) ↔ ResU.InStratum L.join (ρ.map ΦU) := by
  rw [chain_inStratum_jn_iff, TSet.jn, TSet.toLSet_ofLSet]

theorem chain_restrictDom (ρ σ : ResUT Loc Val WCactus.chain) :
    (ρ.restrictDom σ).map ΦU = ResU.restrictDom (ρ.map ΦU) (σ.map ΦU) := by
  refine PMap.ext fun l => ?_
  show Option.map ΦU (if (σ.get l).isSome then ρ.get l else none) =
    if (Option.map ΦU (σ.get l)).isSome then Option.map ΦU (ρ.get l) else none
  rw [Option.isSome_map]
  split <;> rfl

theorem chain_delDom (ρ σ : ResUT Loc Val WCactus.chain) :
    (ρ.delDom σ).map ΦU = ResU.delDom (ρ.map ΦU) (σ.map ΦU) := by
  refine PMap.ext fun l => ?_
  show Option.map ΦU (if (σ.get l).isSome then none else ρ.get l) =
    if (Option.map ΦU (σ.get l)).isSome then none else Option.map ΦU (ρ.get l)
  rw [Option.isSome_map]
  split <;> rfl

/-! ### `reb_α` -/

theorem chain_rebAt_iff {α : Life} {ρ ρ' p : ResUT Loc Val WCactus.chain} {l : Loc} :
    ResUT.RebAt α ρ ρ' l p ↔ ResU.RebAt α (ρ.map ΦU) (ρ'.map ΦU) l (p.map ΦU) := by
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · exact ⟨fun ⟨ψ, e⟩ => ⟨ΦU ψ, map_ΦU_get.mpr e⟩, fun ⟨c, e⟩ => ⟨ΨU c, map_ΦU_get_some.mp e⟩⟩
  · refine forall_congr' fun v => ?_
    rw [← ΦU_ownOf, map_ΦU_get]
    refine imp_congr_right fun _ => ⟨fun ⟨h, e⟩ => ?_, fun ⟨h, e⟩ => ?_⟩
    · have h' : ResU.InStratum (LSet.singleton α).join (ResU.del (p.map ΦU) l) := by
        rw [← chain_del]; exact chain_inStratum_iff.mp h
      exact ⟨h', by rw [← map_ΦU_get] at e; rwa [ΦU_immOf_eq (TSet.toLSet_single α)
        (chain_del p l)] at e⟩
    · have h' : (p.del l).InStratum (TSet.single α) := by
        rw [chain_inStratum_iff, chain_del]; exact h
      refine ⟨h', map_ΦU_get.mp ?_⟩
      rw [ΦU_immOf_eq (TSet.toLSet_single α) (chain_del p l)]
      exact e
  · constructor
    · intro H b v χ hb P hw e
      rw [map_ΦU_get_some, ΨU_mutOf] at e
      obtain ⟨⟨h, e'⟩, hd⟩ := H _ v _ _ _ _ e
      refine ⟨⟨?_, ?_⟩, chain_dom_iff.mp hd⟩
      · have := chain_inStratum_iff.mp h; rwa [map_ΦU_ΨU] at this
      · rw [← map_ΦU_get] at e'
        rwa [ΦU_immOf_eq (TSet.toLSet_single α) (map_ΦU_ΨU χ)] at e'
    · intro H b _ v χ hb P hw e
      rw [← map_ΦU_get, ΦU_mutOf] at e
      obtain ⟨⟨h, e'⟩, hd⟩ := H _ v _ _ _ _ e
      refine ⟨⟨chain_inStratum_iff.mpr h, map_ΦU_get.mp ?_⟩, chain_dom_iff.mpr hd⟩
      rw [ΦU_immOf_eq (TSet.toLSet_single α) rfl]
      exact e'
  · constructor
    · intro H s v χ h e
      rw [map_ΦU_get_some, ΨU_immOf] at e
      obtain ⟨⟨t, ht, hsub, e'⟩, hd⟩ := H _ v _ _ e
      refine ⟨⟨t.toLSet, ?_, fun x hx => TSet.mem_ofLSet.mp (hsub hx), ?_⟩,
        chain_dom_iff.mp hd⟩
      · have := ΦU_map_inStratum ht; rwa [map_ΦU_ΨU] at this
      · rw [← map_ΦU_get] at e'
        rwa [ΦU_immOf_eq rfl (map_ΦU_ΨU χ)] at e'
    · intro H s v χ h e
      rw [← map_ΦU_get, ΦU_immOf] at e
      obtain ⟨⟨t, ht, hsub, e'⟩, hd⟩ := H _ v _ _ e
      refine ⟨⟨TSet.ofLSet t, inStratum_ofLSet_iff.mpr ht,
        fun x hx => hsub x (TSet.mem_ofLSet.mp hx), map_ΦU_get.mp ?_⟩, chain_dom_iff.mpr hd⟩
      rw [ΦU_immOf_eq (TSet.toLSet_ofLSet t) rfl]
      exact e'

/-- **`reb_α` at the chain is the printed `reb_α`** (row 5.28). -/
theorem chain_reb_iff {α : Life} {ρ ρ' : ResUT Loc Val WCactus.chain} :
    ResUT.Reb α ρ ρ' ↔ ResU.Reb α (ρ.map ΦU) (ρ'.map ΦU) := by
  refine and_congr chain_inStratum_iff ⟨?_, ?_⟩
  · rintro ⟨π, b, hd, hbc, hle, hall⟩
    refine ⟨π.map pmapP, b.map ΦU, ?_, ?_, chain_le_iff.mp hle, ?_⟩
    · rw [pmapP_fst]; exact chain_dom_iff.mp hd
    · rw [pmapP_snd]; exact (chain_bigComp_iff cellCompatS_iff cellCompS_iff).mp hbc
    · intro l p hp
      obtain ⟨q, hq, e⟩ := List.mem_map.mp hp
      cases e
      exact chain_rebAt_iff.mp (hall q.1 q.2 hq)
  · rintro ⟨π, b, hd, hbc, hle, hall⟩
    refine ⟨π.map pmapQ, b.map ΨU, ?_, ?_, ?_, ?_⟩
    · rw [pmapQ_fst]; exact chain_dom_iff.mpr hd
    · refine (chain_bigComp_iff cellCompatS_iff cellCompS_iff).mpr ?_
      rw [pmapQ_snd, List.map_map, map_ΦU_ΨU,
        show PMap.map ΦU ∘ PMap.map ΨU = (id : ResU Loc Val → _) from funext map_ΦU_ΨU,
        List.map_id]
      exact hbc
    · rw [chain_le_iff, map_ΦU_ΨU]; exact hle
    · intro l p hp
      obtain ⟨q, hq, e⟩ := List.mem_map.mp hp
      cases e
      refine chain_rebAt_iff.mpr ?_
      show ResU.RebAt α (ρ.map ΦU) (ρ'.map ΦU) q.1 ((q.2.map ΨU).map ΦU)
      rw [map_ΦU_ΨU]
      exact hall q.1 q.2 hq

/-! ### `⊟` -/

theorem lset_diffEmpty_iff {s t : LSet} :
    LSet.DiffEmpty s t ↔ TSet.DiffEmpty (TSet.ofLSet s) (TSet.ofLSet t) := by
  simp only [LSet.DiffEmpty, TSet.DiffEmpty, TSet.mem_ofLSet]

theorem lset_diff_iff {s t u : LSet} :
    LSet.Diff s t u ↔ TSet.Diff (TSet.ofLSet s) (TSet.ofLSet t) (TSet.ofLSet u) := by
  simp only [LSet.Diff, TSet.Diff, TSet.mem_ofLSet]

theorem tset_diffEmpty_iff {s t : TSet} :
    TSet.DiffEmpty s t ↔ LSet.DiffEmpty s.toLSet t.toLSet := Iff.rfl

theorem tset_diff_iff {s t u : TSet} :
    TSet.Diff s t u ↔ LSet.Diff s.toLSet t.toLSet u.toLSet := Iff.rfl

/-- The two readings of Definition 6.3's fourth bullet differ only in which resource the last
sub-case constrains; both are read at the chain by the same steps. -/
theorem chain_subClauseAt_iff {ρ ρ' : ResUT Loc Val WCactus.chain}
    (Q₁ Q₂ : ResUT Loc Val WCactus.chain) {l : Loc} :
    (∀ (s s' : TSet) (v : Val) (ρi : ResUT Loc Val WCactus.chain)
        (h : ρi.InStratum s) (h' : ρi.InStratum s'),
        ρ.get l = some (CellUT.immOf s v ρi h) →
        ρ'.get l = some (CellUT.immOf s' v ρi h') →
        (TSet.DiffEmpty s s' → Q₁.get l = none) ∧
        (∀ u : TSet, TSet.Diff s s' u → ¬ TSet.DiffEmpty s s' →
            ∃ hu : ρi.InStratum u, Q₂.get l = some (CellUT.immOf u v ρi hu))) ↔
    (∀ (s s' : LSet) (v : Val) (ρi : ResU Loc Val)
        (h : ρi.InStratum s.join) (h' : ρi.InStratum s'.join),
        (ρ.map ΦU).get l = some (CellU.immOf s v ρi h) →
        (ρ'.map ΦU).get l = some (CellU.immOf s' v ρi h') →
        (LSet.DiffEmpty s s' → (Q₁.map ΦU).get l = none) ∧
        (∀ u : LSet, LSet.Diff s s' u → ¬ LSet.DiffEmpty s s' →
            ∃ hu : ρi.InStratum u.join, (Q₂.map ΦU).get l = some (CellU.immOf u v ρi hu))) := by
  constructor
  · intro H s s' v ρi h h' e e'
    rw [map_ΦU_get_some, ΨU_immOf] at e e'
    obtain ⟨H1, H2⟩ := H _ _ v _ _ _ e e'
    refine ⟨fun hd => map_ΦU_get_none.mpr (H1 (lset_diffEmpty_iff.mp hd)), fun u hu hne => ?_⟩
    obtain ⟨hu', e''⟩ := H2 _ (lset_diff_iff.mp hu) (fun k => hne (lset_diffEmpty_iff.mpr k))
    refine ⟨?_, ?_⟩
    · have := inStratum_ofLSet_iff.mp hu'; rwa [map_ΦU_ΨU] at this
    · rw [← map_ΦU_get] at e''
      rwa [ΦU_immOf_eq (TSet.toLSet_ofLSet u) (map_ΦU_ΨU ρi)] at e''
  · intro H s s' v ρi h h' e e'
    rw [← map_ΦU_get, ΦU_immOf] at e e'
    obtain ⟨H1, H2⟩ := H _ _ v _ _ _ e e'
    refine ⟨fun hd => map_ΦU_get_none.mp (H1 (tset_diffEmpty_iff.mp hd)), fun u hu hne => ?_⟩
    obtain ⟨hu', e''⟩ := H2 _ (tset_diff_iff.mp hu) (fun k => hne (tset_diffEmpty_iff.mpr k))
    refine ⟨chain_inStratum_jn_iff.mpr hu', map_ΦU_get.mp ?_⟩
    rw [ΦU_immOf_eq rfl rfl]
    exact e''

theorem chain_subClause_iff {ρ ρ' ρ'' : ResUT Loc Val WCactus.chain} :
    ResUT.SubClause ρ ρ' ρ'' ↔ ResU.SubClause (ρ.map ΦU) (ρ'.map ΦU) (ρ''.map ΦU) :=
  forall_congr' fun _ => chain_subClauseAt_iff ρ'' ρ''

theorem chain_subClauseL_iff {ρ ρ' ρ'' : ResUT Loc Val WCactus.chain} :
    ResUT.SubClauseL ρ ρ' ρ'' ↔ ResU.SubClauseL (ρ.map ΦU) (ρ'.map ΦU) (ρ''.map ΦU) :=
  forall_congr' fun _ => chain_subClauseAt_iff ρ'' ρ'

theorem exclPart_empty_iff {ρ : ResUT Loc Val WCactus.chain} :
    ρ.exclPart = PMap.empty ↔ ResU.exclPart (ρ.map ΦU) = PMap.empty := by
  rw [← chain_exclPart, ← chain_empty]
  exact ⟨fun h => h ▸ rfl, fun h => ΦU_map_injective h⟩

theorem restrict_get_iff {ρ ρ'' : ResUT Loc Val WCactus.chain} {l : Loc} :
    ρ''.get l = (ρ.restrict Kind.imm).get l ↔
      (ρ''.map ΦU).get l = (ResU.restrict (ρ.map ΦU) Kind.imm).get l := by
  rw [← chain_restrict, PMap.map_get, PMap.map_get]
  exact ⟨fun h => h ▸ rfl, fun h => Option.map_injective ΦU_injective h⟩

theorem restrict_ne_none_iff {ρ : ResUT Loc Val WCactus.chain} {l : Loc} :
    (ρ.restrict Kind.imm).get l ≠ none ↔ (ResU.restrict (ρ.map ΦU) Kind.imm).get l ≠ none := by
  rw [← chain_restrict]
  exact not_congr map_ΦU_get_none.symm

/-- The common shape of the three readings of Definition 6.3, at the chain. -/
theorem chain_subShape_iff {ρ ρ' χ : ResUT Loc Val WCactus.chain}
    (A : ResUT Loc Val WCactus.chain → Prop) (A' : ResU Loc Val → Prop)
    (hA : ∀ ρ'', A ρ'' ↔ A' (ρ''.map ΦU)) :
    (∃ ρ'' : ResUT Loc Val WCactus.chain, ρ'.exclPart = PMap.empty ∧
        ResUT.Le ρ'' (ρ.restrict Kind.imm) ∧ A ρ'' ∧ ResUT.CompS ρ.exclPart ρ'' χ) ↔
    (∃ ρ'' : ResU Loc Val, ResU.exclPart (ρ'.map ΦU) = PMap.empty ∧
        ResU.Le ρ'' (ResU.restrict (ρ.map ΦU) Kind.imm) ∧ A' ρ'' ∧
        ResU.CompS (ResU.exclPart (ρ.map ΦU)) ρ'' (χ.map ΦU)) := by
  constructor
  · rintro ⟨ρ'', h1, h2, h3, h4⟩
    refine ⟨ρ''.map ΦU, exclPart_empty_iff.mp h1, ?_, (hA ρ'').mp h3, ?_⟩
    · rw [← chain_restrict]; exact chain_le_iff.mp h2
    · rw [← chain_exclPart]; exact chain_resCompS_iff.mp h4
  · rintro ⟨ρ'', h1, h2, h3, h4⟩
    refine ⟨ρ''.map ΨU, exclPart_empty_iff.mpr h1, ?_, (hA _).mpr (by rwa [map_ΦU_ΨU]), ?_⟩
    · rw [chain_le_iff, map_ΦU_ΨU, chain_restrict]; exact h2
    · rw [chain_resCompS_iff, map_ΦU_ΨU, chain_exclPart]; exact h4

/-- **`⊟` at the chain is the printed `⊟`** (Definition 6.3, its bullets). -/
theorem chain_sub_iff {ρ ρ' χ : ResUT Loc Val WCactus.chain} :
    ResUT.Sub ρ ρ' χ ↔ ResU.Sub (ρ.map ΦU) (ρ'.map ΦU) (χ.map ΦU) := by
  have := chain_subShape_iff (ρ := ρ) (ρ' := ρ') (χ := χ)
    (fun ρ'' => (∀ l, (ρ.restrict Kind.imm).get l ≠ none → ρ'.get l = none →
      ρ''.get l ≠ none) ∧ ResUT.SubClause ρ ρ' ρ'')
    (fun ρ'' => (∀ l, (ResU.restrict (ρ.map ΦU) Kind.imm).get l ≠ none →
      (ρ'.map ΦU).get l = none → ρ''.get l ≠ none) ∧
      ResU.SubClause (ρ.map ΦU) (ρ'.map ΦU) ρ'')
    (fun ρ'' => and_congr (forall_congr' fun _ => imp_congr restrict_ne_none_iff
      (imp_congr map_ΦU_get_none.symm (not_congr map_ΦU_get_none.symm)))
      chain_subClause_iff)
  simp only [ResUT.Sub, ResU.Sub, and_assoc] at this ⊢
  exact this

/-- **`⊟` at the chain is the printed `⊟`** (Definition 6.3, the last sub-case literal). -/
theorem chain_subL_iff {ρ ρ' χ : ResUT Loc Val WCactus.chain} :
    ResUT.SubL ρ ρ' χ ↔ ResU.SubL (ρ.map ΦU) (ρ'.map ΦU) (χ.map ΦU) := by
  have := chain_subShape_iff (ρ := ρ) (ρ' := ρ') (χ := χ)
    (fun ρ'' => (∀ l, (ρ.restrict Kind.imm).get l ≠ none → ρ'.get l = none →
      ρ''.get l ≠ none) ∧ ResUT.SubClauseL ρ ρ' ρ'')
    (fun ρ'' => (∀ l, (ResU.restrict (ρ.map ΦU) Kind.imm).get l ≠ none →
      (ρ'.map ΦU).get l = none → ρ''.get l ≠ none) ∧
      ResU.SubClauseL (ρ.map ΦU) (ρ'.map ΦU) ρ'')
    (fun ρ'' => and_congr (forall_congr' fun _ => imp_congr restrict_ne_none_iff
      (imp_congr map_ΦU_get_none.symm (not_congr map_ΦU_get_none.symm)))
      chain_subClauseL_iff)
  simp only [ResUT.SubL, ResU.SubL, and_assoc] at this ⊢
  exact this

/-- **`⊟` at the chain is the printed `⊟`** (Definition 6.3, the third bullet read through the
paragraph below it). -/
theorem chain_subKeep_iff {ρ ρ' χ : ResUT Loc Val WCactus.chain} :
    ResUT.SubKeep ρ ρ' χ ↔ ResU.SubKeep (ρ.map ΦU) (ρ'.map ΦU) (χ.map ΦU) := by
  have := chain_subShape_iff (ρ := ρ) (ρ' := ρ') (χ := χ)
    (fun ρ'' => (∀ l, (ρ.restrict Kind.imm).get l ≠ none → ρ'.get l = none →
      ρ''.get l = (ρ.restrict Kind.imm).get l) ∧ ResUT.SubClause ρ ρ' ρ'')
    (fun ρ'' => (∀ l, (ResU.restrict (ρ.map ΦU) Kind.imm).get l ≠ none →
      (ρ'.map ΦU).get l = none → ρ''.get l = (ResU.restrict (ρ.map ΦU) Kind.imm).get l) ∧
      ResU.SubClause (ρ.map ΦU) (ρ'.map ΦU) ρ'')
    (fun ρ'' => and_congr (forall_congr' fun _ => imp_congr restrict_ne_none_iff
      (imp_congr map_ΦU_get_none.symm restrict_get_iff))
      chain_subClause_iff)
  simp only [ResUT.SubKeep, ResU.SubKeep, and_assoc] at this ⊢
  exact this

end BoCa.Fig16.Tree

end

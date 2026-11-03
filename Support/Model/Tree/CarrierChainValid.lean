import Support.Model.Tree.CarrierChainOps

/-!
# At the WCactus.chain, `✓` and `#` are the printed ones

`[spec §62]`. `chainEquiv` (`Tree/CarrierChain.lean`) identifies the cells of the tree-stratified carrier at
`WCactus.chain` with the printed cells, keeping tags, values and witnesses, `▶◀`, `●`, `⋈` and
`○` (`Tree/CarrierChainOps.lean`). The walks, `⦇−⦈`, `✓` and `#` are built from those alone, so
they agree along it:

* `chain_valid_iff`: `✓ρ` at the WCactus.chain iff the printed `✓(ΦU ρ)`;
* `chain_hash_iff`: `ρ₁ # ρ₂` at the WCactus.chain iff the printed `ΦU ρ₁ # ΦU ρ₂`;
* `chain_flat_iff`: `⦇ρ⦈ = σ` at the WCactus.chain iff the printed `⦇ΦU ρ⦈ = ΦU σ`.

Each walk is carried in both directions, along `ΦU` (`t_…`) and along `ΨU` (`p_…`), by
induction on the walk; `ΦU ∘ ΨU = id` closes the converse.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

variable {Loc Val : Type}

/-! ### `ΨU` keeps what `ΦU` keeps -/

theorem ΨU_kind (c : CellU Loc Val) : (ΨU c).kind = c.kind := by
  rw [← ΦU_kind, ΦU_ΨU]

theorem ΨU_wit (c : CellU Loc Val) : (ΨU c).wit = c.wit.map ΨU := by
  have h := ΦU_wit (ΨU c)
  rw [ΦU_ΨU] at h
  rw [h, PMap.map_map]
  exact ((PMap.map_congr _ fun _ ψ _ => ΨU_ΦU ψ).trans (PMap.map_id' _)).symm

theorem map_ΦU_ΨU (ρ : ResU Loc Val) : (ρ.map ΨU).map ΦU = ρ := by
  rw [PMap.map_map]
  exact (PMap.map_congr _ fun _ c _ => ΦU_ΨU c).trans (PMap.map_id' _)

theorem map_ΨU_ΦU (ρ : ResUT Loc Val WCactus.chain) : (ρ.map ΦU).map ΨU = ρ := by
  rw [PMap.map_map]
  exact (PMap.map_congr _ fun _ c _ => ΨU_ΦU c).trans (PMap.map_id' _)

theorem ΨU_compatS {a b : CellU Loc Val} (h : CellU.CompatS a b) :
    CellUT.CompatS (ΨU a) (ΨU b) :=
  chain_compatS_iff.mp (by rw [ΦU_ΨU, ΦU_ΨU]; exact h)

theorem ΨU_compS {a b c : CellU Loc Val} (h : CellU.CompS a b c) :
    CellUT.CompS (ΨU a) (ΨU b) (ΨU c) :=
  chain_compS_iff.mp (by rw [ΦU_ΨU, ΦU_ΨU, ΦU_ΨU]; exact h)

theorem ΨU_compatR {a b : CellU Loc Val} (h : CellU.CompatR a b) :
    CellUT.CompatR (ΨU a) (ΨU b) :=
  chain_compatR_iff.mp (by rw [ΦU_ΨU, ΦU_ΨU]; exact h)

theorem ΨU_compR {a b c : CellU Loc Val} (h : CellU.CompR a b c) :
    CellUT.CompR (ΨU a) (ΨU b) (ΨU c) :=
  chain_compR_iff.mp (by rw [ΦU_ΨU, ΦU_ΨU, ΦU_ΨU]; exact h)

/-! ### Along `ΦU`: the schema at the WCactus.chain to the printed rows -/

section T
variable {R : CellUT Loc Val WCactus.chain → CellUT Loc Val WCactus.chain → Prop}
  {C : CellUT Loc Val WCactus.chain → CellUT Loc Val WCactus.chain → CellUT Loc Val WCactus.chain → Prop}
  {R' : CellU Loc Val → CellU Loc Val → Prop}
  {C' : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}

theorem t_comp (hR : ∀ a b, R a b → R' (ΦU a) (ΦU b))
    (hC : ∀ a b c, C a b c → C' (ΦU a) (ΦU b) (ΦU c)) {ρ₁ ρ₂ ρ : ResUT Loc Val WCactus.chain}
    (h : G.Comp R C ρ₁ ρ₂ ρ) : ResU.Comp R' C' (ρ₁.map ΦU) (ρ₂.map ΦU) (ρ.map ΦU) := by
  refine ⟨fun l a b e₁ e₂ => ?_, fun l => ?_⟩
  · simp only [PMap.map_get] at e₁ e₂
    cases f₁ : ρ₁.get l <;> rw [f₁] at e₁ <;> cases e₁
    cases f₂ : ρ₂.get l <;> rw [f₂] at e₂ <;> cases e₂
    exact hR _ _ (h.1 l _ _ f₁ f₂)
  · have hl := h.2 l
    simp only [PMap.map_get]
    revert hl
    cases ρ₁.get l <;> cases ρ₂.get l <;> intro hl
    · show Option.map ΦU (ρ.get l) = none; rw [show ρ.get l = none from hl]; rfl
    · show Option.map ΦU (ρ.get l) = some _; rw [show ρ.get l = some _ from hl]; rfl
    · show Option.map ΦU (ρ.get l) = some _; rw [show ρ.get l = some _ from hl]; rfl
    · obtain ⟨ψ, e, hc⟩ := hl
      exact ⟨ΦU ψ, by rw [e]; rfl, hC _ _ _ hc⟩

theorem t_restrict (ρ : ResUT Loc Val WCactus.chain) (k : Kind) :
    (G.restrict CellUT.kind ρ k).map ΦU = ResU.restrict (ρ.map ΦU) k := by
  refine PMap.ext fun l => ?_
  show Option.map ΦU ((ρ.get l).bind _) = (Option.map ΦU (ρ.get l)).bind _
  cases ρ.get l with
  | none => rfl
  | some ψ =>
      simp only [Option.bind_some, Option.map_some, ΦU_kind]
      split <;> rfl

theorem t_sites {ρ : ResUT Loc Val WCactus.chain} {k : Kind} {d : List Loc}
    (h : G.Sites CellUT.kind ρ k d) : ResU.Sites (ρ.map ΦU) k d := by
  refine ⟨h.1, fun l => (h.2 l).trans ?_⟩
  simp only [PMap.map_get]
  constructor
  · rintro ⟨ψ, e, hk⟩; exact ⟨ΦU ψ, by rw [e]; rfl, by rw [ΦU_kind]; exact hk⟩
  · rintro ⟨c, e, hk⟩
    cases f : ρ.get l with
    | none => rw [f] at e; cases e
    | some ψ =>
        rw [f] at e; cases Option.some.inj e
        exact ⟨ψ, rfl, by rw [← ΦU_kind]; exact hk⟩

theorem t_bigComp (hR : ∀ a b, R a b → R' (ΦU a) (ΦU b))
    (hC : ∀ a b c, C a b c → C' (ΦU a) (ΦU b) (ΦU c)) :
    ∀ {L : List (ResUT Loc Val WCactus.chain)} {b : ResUT Loc Val WCactus.chain}, G.BigComp R C L b →
      BigComp R' C' (L.map (PMap.map ΦU)) (b.map ΦU) := by
  intro L b h
  induction h with
  | nil => exact BigComp.nil
  | cons _ hc ih => exact BigComp.cons ih (t_comp hR hC hc)

/-- The tag of a pair is kept by mapping the resource. -/
def pmapP (p : Loc × ResUT Loc Val WCactus.chain) : Loc × ResU Loc Val := (p.1, p.2.map ΦU)

theorem pmapP_fst (w : List (Loc × ResUT Loc Val WCactus.chain)) :
    (w.map pmapP).map Prod.fst = w.map Prod.fst := by
  rw [List.map_map]; rfl

theorem pmapP_snd (w : List (Loc × ResUT Loc Val WCactus.chain)) :
    (w.map pmapP).map Prod.snd = (w.map Prod.snd).map (PMap.map ΦU) := by
  rw [List.map_map, List.map_map]; rfl

theorem t_exW (hR : ∀ a b, R a b → R' (ΦU a) (ΦU b))
    (hC : ∀ a b c, C a b c → C' (ΦU a) (ΦU b) (ΦU c)) {ρ σ : ResUT Loc Val WCactus.chain}
    (h : G.ExW CellUT.kind CellUT.wit R C ρ σ) : ExW R' C' (ρ.map ΦU) (σ.map ΦU) := by
  refine G.ExW.rec (motive_1 := fun ρ σ _ => ExW R' C' (ρ.map ΦU) (σ.map ΦU))
    (motive_2 := fun ρ w _ => ExWits R' C' (ρ.map ΦU) (w.map pmapP)) ?mk ?nil ?cons h
  case mk =>
    intro ρ₀ σ₀ nm b w hs _ hb hnm hσ ih
    refine ExW.mk (w := w.map pmapP) (by rw [pmapP_fst]; exact t_sites hs) ih
      (by rw [pmapP_snd]; exact t_bigComp hR hC hb) ?_ (t_comp hR hC hσ)
    rw [← t_restrict, ← t_restrict]
    exact t_comp hR hC hnm
  case nil => intro ρ₀; exact ExWits.nil
  case cons =>
    intro ρ₀ e l w ψ hψ hk _ _ ihe ihw
    refine ExWits.cons (ΦU ψ) (by rw [PMap.map_get, hψ]; rfl) (by rw [ΦU_kind]; exact hk)
      (by rw [ΦU_wit]; exact ihe) ihw

theorem t_agW {ρ σ : ResUT Loc Val WCactus.chain} (h : AgWT ρ σ) : AgW (ρ.map ΦU) (σ.map ΦU) := by
  have hR : ∀ a b : CellUT Loc Val WCactus.chain, CellUT.CompatR a b → CellU.CompatR (ΦU a) (ΦU b) :=
    fun _ _ k => chain_compatR_iff.mpr k
  have hC : ∀ a b c : CellUT Loc Val WCactus.chain, CellUT.CompR a b c →
      CellU.CompR (ΦU a) (ΦU b) (ΦU c) := fun _ _ _ k => chain_compR_iff.mpr k
  refine G.AgW.rec (motive_1 := fun ρ σ _ => AgW (ρ.map ΦU) (σ.map ΦU))
    (motive_2 := fun ρ w _ => AgWitsM (ρ.map ΦU) (w.map pmapP))
    (motive_3 := fun ρ w _ => AgWitsI (ρ.map ΦU) (w.map pmapP))
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ₀ σ₀ a bm bi wm wi hsm hsi _ _ hbm hbi ha hσ ihm ihi
    refine AgW.mk (wm := wm.map pmapP) (wi := wi.map pmapP)
      (by rw [pmapP_fst]; exact t_sites hsm) (by rw [pmapP_fst]; exact t_sites hsi) ihm ihi
      (by rw [pmapP_snd]; exact t_bigComp hR hC hbm)
      (by rw [pmapP_snd]; exact t_bigComp hR hC hbi) ?_ (t_comp hR hC hσ)
    rw [← t_restrict]
    exact t_comp hR hC ha
  case nilM => intro ρ₀; exact AgWitsM.nil
  case consM =>
    intro ρ₀ e l w ψ hψ hk _ _ ihe ihw
    exact AgWitsM.cons (ΦU ψ) (by rw [PMap.map_get, hψ]; rfl) (by rw [ΦU_kind]; exact hk)
      (by rw [ΦU_wit]; exact ihe) ihw
  case nilI => intro ρ₀; exact AgWitsI.nil
  case consI =>
    intro ρ₀ p l w ψ hψ hk e a hex _ hp _ iha ihw
    exact AgWitsI.cons (ΦU ψ) (by rw [PMap.map_get, hψ]; rfl) (by rw [ΦU_kind]; exact hk)
      (e.map ΦU) (a.map ΦU) (by rw [ΦU_wit]; exact t_exW hR hC hex)
      (by rw [ΦU_wit]; exact iha) (t_comp hR hC hp) ihw

theorem t_flat {ρ σ : ResUT Loc Val WCactus.chain} (h : ResUT.Flat ρ σ) :
    ResU.Flat (ρ.map ΦU) (σ.map ΦU) := by
  have hRS : ∀ a b : CellUT Loc Val WCactus.chain, CellUT.CompatS a b → CellU.CompatS (ΦU a) (ΦU b) :=
    fun _ _ k => chain_compatS_iff.mpr k
  have hCS : ∀ a b c : CellUT Loc Val WCactus.chain, CellUT.CompS a b c →
      CellU.CompS (ΦU a) (ΦU b) (ΦU c) := fun _ _ _ k => chain_compS_iff.mpr k
  obtain ⟨e, a, he, ha, hc⟩ := h
  exact ⟨e.map ΦU, a.map ΦU, t_exW hRS hCS he, t_agW ha, t_comp hRS hCS hc⟩

end T

/-! ### Along `ΨU`: the printed rows to the schema at the WCactus.chain -/

section P
variable {R : CellU Loc Val → CellU Loc Val → Prop}
  {C : CellU Loc Val → CellU Loc Val → CellU Loc Val → Prop}
  {R' : CellUT Loc Val WCactus.chain → CellUT Loc Val WCactus.chain → Prop}
  {C' : CellUT Loc Val WCactus.chain → CellUT Loc Val WCactus.chain → CellUT Loc Val WCactus.chain → Prop}

theorem p_comp (hR : ∀ a b, R a b → R' (ΨU a) (ΨU b))
    (hC : ∀ a b c, C a b c → C' (ΨU a) (ΨU b) (ΨU c)) {ρ₁ ρ₂ ρ : ResU Loc Val}
    (h : ResU.Comp R C ρ₁ ρ₂ ρ) : G.Comp R' C' (ρ₁.map ΨU) (ρ₂.map ΨU) (ρ.map ΨU) := by
  refine ⟨fun l a b e₁ e₂ => ?_, fun l => ?_⟩
  · simp only [PMap.map_get] at e₁ e₂
    cases f₁ : ρ₁.get l <;> rw [f₁] at e₁ <;> cases e₁
    cases f₂ : ρ₂.get l <;> rw [f₂] at e₂ <;> cases e₂
    exact hR _ _ (h.1 l _ _ f₁ f₂)
  · have hl := h.2 l
    simp only [PMap.map_get]
    revert hl
    cases ρ₁.get l <;> cases ρ₂.get l <;> intro hl
    · show Option.map ΨU (ρ.get l) = none; rw [show ρ.get l = none from hl]; rfl
    · show Option.map ΨU (ρ.get l) = some _; rw [show ρ.get l = some _ from hl]; rfl
    · show Option.map ΨU (ρ.get l) = some _; rw [show ρ.get l = some _ from hl]; rfl
    · obtain ⟨ψ, e, hc⟩ := hl
      exact ⟨ΨU ψ, by rw [e]; rfl, hC _ _ _ hc⟩

theorem p_restrict (ρ : ResU Loc Val) (k : Kind) :
    (ResU.restrict ρ k).map ΨU = G.restrict CellUT.kind (ρ.map ΨU) k := by
  refine PMap.ext fun l => ?_
  show Option.map ΨU ((ρ.get l).bind _) = (Option.map ΨU (ρ.get l)).bind _
  cases ρ.get l with
  | none => rfl
  | some ψ =>
      simp only [Option.bind_some, Option.map_some, ΨU_kind]
      split <;> rfl

theorem p_sites {ρ : ResU Loc Val} {k : Kind} {d : List Loc}
    (h : ResU.Sites ρ k d) : G.Sites CellUT.kind (ρ.map ΨU) k d := by
  refine ⟨h.1, fun l => (h.2 l).trans ?_⟩
  simp only [PMap.map_get]
  constructor
  · rintro ⟨ψ, e, hk⟩; exact ⟨ΨU ψ, by rw [e]; rfl, by rw [ΨU_kind]; exact hk⟩
  · rintro ⟨c, e, hk⟩
    cases f : ρ.get l with
    | none => rw [f] at e; cases e
    | some ψ =>
        rw [f] at e; cases Option.some.inj e
        exact ⟨ψ, rfl, by rw [← ΨU_kind]; exact hk⟩

theorem p_bigComp (hR : ∀ a b, R a b → R' (ΨU a) (ΨU b))
    (hC : ∀ a b c, C a b c → C' (ΨU a) (ΨU b) (ΨU c)) :
    ∀ {L : List (ResU Loc Val)} {b : ResU Loc Val}, BigComp R C L b →
      G.BigComp R' C' (L.map (PMap.map ΨU)) (b.map ΨU) := by
  intro L b h
  induction h with
  | nil => exact G.BigComp.nil
  | cons _ hc ih => exact G.BigComp.cons ih (p_comp hR hC hc)

/-- The tag of a pair is kept by mapping the resource. -/
def pmapQ (p : Loc × ResU Loc Val) : Loc × ResUT Loc Val WCactus.chain := (p.1, p.2.map ΨU)

theorem pmapQ_fst (w : List (Loc × ResU Loc Val)) :
    (w.map pmapQ).map Prod.fst = w.map Prod.fst := by
  rw [List.map_map]; rfl

theorem pmapQ_snd (w : List (Loc × ResU Loc Val)) :
    (w.map pmapQ).map Prod.snd = (w.map Prod.snd).map (PMap.map ΨU) := by
  rw [List.map_map, List.map_map]; rfl

theorem p_exW (hR : ∀ a b, R a b → R' (ΨU a) (ΨU b))
    (hC : ∀ a b c, C a b c → C' (ΨU a) (ΨU b) (ΨU c)) {ρ σ : ResU Loc Val}
    (h : ExW R C ρ σ) : G.ExW CellUT.kind CellUT.wit R' C' (ρ.map ΨU) (σ.map ΨU) := by
  refine ExW.rec (motive_1 := fun ρ σ _ => G.ExW CellUT.kind CellUT.wit R' C' (ρ.map ΨU) (σ.map ΨU))
    (motive_2 := fun ρ w _ => G.ExWits CellUT.kind CellUT.wit R' C' (ρ.map ΨU) (w.map pmapQ))
    ?mk ?nil ?cons h
  case mk =>
    intro ρ₀ σ₀ nm b w hs _ hb hnm hσ ih
    refine G.ExW.mk (w := w.map pmapQ) (by rw [pmapQ_fst]; exact p_sites hs) ih
      (by rw [pmapQ_snd]; exact p_bigComp hR hC hb) ?_ (p_comp hR hC hσ)
    rw [← p_restrict, ← p_restrict]
    exact p_comp hR hC hnm
  case nil => intro ρ₀; exact G.ExWits.nil
  case cons =>
    intro ρ₀ e l w ψ hψ hk _ _ ihe ihw
    refine G.ExWits.cons (ΨU ψ) (by rw [PMap.map_get, hψ]; rfl) (by rw [ΨU_kind]; exact hk)
      (by rw [ΨU_wit]; exact ihe) ihw

theorem p_agW {ρ σ : ResU Loc Val} (h : AgW ρ σ) : AgWT (ρ.map ΨU) (σ.map ΨU) := by
  have hR : ∀ a b : CellU Loc Val, CellU.CompatR a b → CellUT.CompatR (ΨU a) (ΨU b) :=
    fun _ _ k => ΨU_compatR k
  have hC : ∀ a b c : CellU Loc Val, CellU.CompR a b c → CellUT.CompR (ΨU a) (ΨU b) (ΨU c) :=
    fun _ _ _ k => ΨU_compR k
  refine AgW.rec (motive_1 := fun ρ σ _ => AgWT (ρ.map ΨU) (σ.map ΨU))
    (motive_2 := fun ρ w _ => G.AgWitsM CellUT.kind CellUT.wit CellUT.CompatR CellUT.CompR
      (ρ.map ΨU) (w.map pmapQ))
    (motive_3 := fun ρ w _ => G.AgWitsI CellUT.kind CellUT.wit CellUT.CompatR CellUT.CompR
      (ρ.map ΨU) (w.map pmapQ))
    ?mk ?nilM ?consM ?nilI ?consI h
  case mk =>
    intro ρ₀ σ₀ a bm bi wm wi hsm hsi _ _ hbm hbi ha hσ ihm ihi
    refine G.AgW.mk (wm := wm.map pmapQ) (wi := wi.map pmapQ)
      (by rw [pmapQ_fst]; exact p_sites hsm) (by rw [pmapQ_fst]; exact p_sites hsi) ihm ihi
      (by rw [pmapQ_snd]; exact p_bigComp hR hC hbm)
      (by rw [pmapQ_snd]; exact p_bigComp hR hC hbi) ?_ (p_comp hR hC hσ)
    rw [← p_restrict]
    exact p_comp hR hC ha
  case nilM => intro ρ₀; exact G.AgWitsM.nil
  case consM =>
    intro ρ₀ e l w ψ hψ hk _ _ ihe ihw
    exact G.AgWitsM.cons (ΨU ψ) (by rw [PMap.map_get, hψ]; rfl) (by rw [ΨU_kind]; exact hk)
      (by rw [ΨU_wit]; exact ihe) ihw
  case nilI => intro ρ₀; exact G.AgWitsI.nil
  case consI =>
    intro ρ₀ p l w ψ hψ hk e a hex _ hp _ iha ihw
    exact G.AgWitsI.cons (ΨU ψ) (by rw [PMap.map_get, hψ]; rfl) (by rw [ΨU_kind]; exact hk)
      (e.map ΨU) (a.map ΨU) (by rw [ΨU_wit]; exact p_exW hR hC hex)
      (by rw [ΨU_wit]; exact iha) (p_comp hR hC hp) ihw

theorem p_flat {ρ σ : ResU Loc Val} (h : ResU.Flat ρ σ) :
    ResUT.Flat (ρ.map ΨU) (σ.map ΨU) := by
  have hRS : ∀ a b : CellU Loc Val, CellU.CompatS a b → CellUT.CompatS (ΨU a) (ΨU b) :=
    fun _ _ k => ΨU_compatS k
  have hCS : ∀ a b c : CellU Loc Val, CellU.CompS a b c → CellUT.CompS (ΨU a) (ΨU b) (ΨU c) :=
    fun _ _ _ k => ΨU_compS k
  obtain ⟨e, a, he, ha, hc⟩ := h
  exact ⟨e.map ΨU, a.map ΨU, p_exW hRS hCS he, p_agW ha, p_comp hRS hCS hc⟩

end P

/-! ### The agreement -/

/-- **`⦇−⦈` at the WCactus.chain is the printed `⦇−⦈`.** -/
theorem chain_flat_iff {ρ σ : ResUT Loc Val WCactus.chain} :
    ResUT.Flat ρ σ ↔ ResU.Flat (ρ.map ΦU) (σ.map ΦU) := by
  refine ⟨t_flat, fun h => ?_⟩
  have := p_flat h
  rwa [map_ΨU_ΦU, map_ΨU_ΦU] at this

/-- **`✓` at the WCactus.chain is the printed `✓`.** -/
theorem chain_valid_iff {ρ : ResUT Loc Val WCactus.chain} :
    ResUT.Valid ρ ↔ ResU.Valid (ρ.map ΦU) := by
  constructor
  · rintro ⟨σ, h⟩; exact ⟨σ.map ΦU, t_flat h⟩
  · rintro ⟨σ, h⟩
    refine ⟨σ.map ΨU, ?_⟩
    have := p_flat h
    rwa [map_ΨU_ΦU] at this

/-- **`#` at the WCactus.chain is the printed `#`.** -/
theorem chain_hash_iff {ρ₁ ρ₂ : ResUT Loc Val WCactus.chain} :
    ResUT.Hash ρ₁ ρ₂ ↔ ResU.Hash (ρ₁.map ΦU) (ρ₂.map ΦU) := by
  have hRS : ∀ a b : CellUT Loc Val WCactus.chain, CellUT.CompatS a b → CellU.CompatS (ΦU a) (ΦU b) :=
    fun _ _ k => chain_compatS_iff.mpr k
  have hCS : ∀ a b c : CellUT Loc Val WCactus.chain, CellUT.CompS a b c →
      CellU.CompS (ΦU a) (ΦU b) (ΦU c) := fun _ _ _ k => chain_compS_iff.mpr k
  have hRS' : ∀ a b : CellU Loc Val, CellU.CompatS a b → CellUT.CompatS (ΨU a) (ΨU b) :=
    fun _ _ k => ΨU_compatS k
  have hCS' : ∀ a b c : CellU Loc Val, CellU.CompS a b c → CellUT.CompS (ΨU a) (ΨU b) (ΨU c) :=
    fun _ _ _ k => ΨU_compS k
  constructor
  · rintro ⟨hc, ρ, hcomp, hv⟩
    exact ⟨(t_comp hRS hCS ⟨hc, fun l => hcomp.2 l⟩).1, ρ.map ΦU, t_comp hRS hCS hcomp,
      chain_valid_iff.mp hv⟩
  · rintro ⟨hc, ρ, hcomp, hv⟩
    have hcomp' := p_comp hRS' hCS' hcomp
    rw [map_ΨU_ΦU, map_ΨU_ΦU] at hcomp'
    refine ⟨hcomp'.1, ρ.map ΨU, hcomp', chain_valid_iff.mpr ?_⟩
    rwa [map_ΦU_ΨU]

end BoCa.Fig16.Tree

end

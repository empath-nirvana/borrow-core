import Support.Model.Tree.CarrierGraft

/-!
# A handler's lend and a task resumed inside it, in the tree-stratified carrier

`[spec §62]`. `K₀ = WCactus.ofParent beforeP`: the task's lend `α = 1` and the handler's later lend `β = 2`,
siblings under `⊤`. `K₁ = WCactus.ofParent graftP`: after the handler resumes the task inside
`β`, `α` is a child of `β` (`graftEx_lt`). No lifetime is renamed: `α` stays `1`, `β` stays `2`.

* `graftExt`: `K₁` keeps every nesting of `K₀`, so `ResUT.Valid.graft` carries any valid world
  of `K₀` into `K₁` (`graftWorld_valid_after`, at the world before the graft).
* `graftCell_refused_before`: in `K₀` a witness holding the handler's borrow at `β` is in no
  stratum of `α` (they are siblings), so no `mut` cell at `α` stores it.
* `graftCell_admitted`: in `K₁` the `mut` cell at `α` whose witness holds the borrow at `β` is a
  cell (`CellUT.mutOf` at `{α}`), and the world holding it beside the handler's own view of the
  same borrow is valid. This is the cell `graftEx_carrier_refuses` exhibits: refused by the
  printed carrier, stratified by the chain, and admitted by the carrier stratified by the tree.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

variable {Loc Val : Type}

/-! ### Small resources -/

open Classical in
/-- `ℓ ↦ x`. -/
def PMap.sng {X : Type} (l : Loc) (x : X) : PMap Loc X where
  get l' := if l' = l then some x else none
  finite := by
    refine ⟨[l], fun l' h => ?_⟩
    by_cases e : l' = l
    · exact e ▸ List.mem_singleton.mpr rfl
    · exact absurd (if_neg e) h

open Classical in
/-- `ℓ₁ ↦ x₁, ℓ₂ ↦ x₂`. -/
def PMap.pair {X : Type} (l₁ : Loc) (x₁ : X) (l₂ : Loc) (x₂ : X) : PMap Loc X where
  get l' := if l' = l₁ then some x₁ else if l' = l₂ then some x₂ else none
  finite := by
    refine ⟨[l₁, l₂], fun l' h => ?_⟩
    by_cases e₁ : l' = l₁
    · exact e₁ ▸ List.mem_cons_self
    · by_cases e₂ : l' = l₂
      · exact e₂ ▸ List.mem_cons_of_mem _ List.mem_cons_self
      · exact absurd (by simp [e₁, e₂]) h

open Classical in
theorem PMap.sng_get {X : Type} (l : Loc) (x : X) (l' : Loc) :
    (PMap.sng l x).get l' = if l' = l then some x else none := rfl

open Classical in
theorem PMap.pair_get {X : Type} (l₁ : Loc) (x₁ : X) (l₂ : Loc) (x₂ : X) (l' : Loc) :
    (PMap.pair l₁ x₁ l₂ x₂).get l' =
      if l' = l₁ then some x₁ else if l' = l₂ then some x₂ else none := rfl

section
variable {X : Type} {R : X → X → Prop} {C : X → X → X → Prop}

theorem G.comp_empty_left (ρ : PMap Loc X) : G.Comp R C PMap.empty ρ ρ := by
  refine ⟨G.Compat.of_disjoint (fun _ => Or.inl rfl), fun l => ?_⟩
  show G.OptComp C none (ρ.get l) (ρ.get l)
  cases ρ.get l <;> rfl

open Classical in
theorem G.comp_sng_sng {l₁ l₂ : Loc} (hl : l₁ ≠ l₂) (x₁ x₂ : X) :
    G.Comp R C (PMap.sng l₁ x₁) (PMap.sng l₂ x₂) (PMap.pair l₁ x₁ l₂ x₂) := by
  refine ⟨G.Compat.of_disjoint fun l => ?_, fun l => ?_⟩
  · by_cases e : l = l₁
    · subst e; exact Or.inr (by simp [PMap.sng_get, hl])
    · exact Or.inl (by simp [PMap.sng_get, e])
  · simp only [PMap.sng_get, PMap.pair_get]
    by_cases e₁ : l = l₁
    · subst e₁; simp [hl]; rfl
    · by_cases e₂ : l = l₂
      · subst e₂; simp [e₁]; rfl
      · simp [e₁, e₂]; rfl

open Classical in
theorem G.restrict_sng (kd : X → Kind) (l : Loc) (x : X) (k : Kind) :
    G.restrict kd (PMap.sng l x) k = if kd x = k then PMap.sng l x else PMap.empty := by
  refine PMap.ext fun l' => ?_
  show ((PMap.sng l x).get l').bind _ = _
  rw [PMap.sng_get]
  by_cases e : l' = l <;> by_cases hk : kd x = k <;> simp [e, hk, PMap.sng_get]

open Classical in
theorem G.restrict_pair (kd : X → Kind) {l₁ l₂ : Loc} (hl : l₁ ≠ l₂) (x₁ x₂ : X) (k : Kind)
    (h₁ : kd x₁ = k) (h₂ : kd x₂ ≠ k) :
    G.restrict kd (PMap.pair l₁ x₁ l₂ x₂) k = PMap.sng l₁ x₁ := by
  refine PMap.ext fun l' => ?_
  show ((PMap.pair l₁ x₁ l₂ x₂).get l').bind _ = _
  rw [PMap.pair_get, PMap.sng_get]
  by_cases e₁ : l' = l₁
  · simp [e₁, h₁]
  · by_cases e₂ : l' = l₂
    · subst e₂; simp [e₁, h₂]
    · simp [e₁, e₂]

open Classical in
theorem G.restrict_pair_none (kd : X → Kind) (l₁ l₂ : Loc) (x₁ x₂ : X) (k : Kind)
    (h₁ : kd x₁ ≠ k) (h₂ : kd x₂ ≠ k) :
    G.restrict kd (PMap.pair l₁ x₁ l₂ x₂) k = PMap.empty := by
  refine PMap.ext fun l' => ?_
  show ((PMap.pair l₁ x₁ l₂ x₂).get l').bind _ = _
  rw [PMap.pair_get]
  by_cases e₁ : l' = l₁
  · simp [e₁, h₁]
  · by_cases e₂ : l' = l₂
    · subst e₂; simp [e₁, h₂]
    · simp [e₁, e₂]

theorem G.restrict_empty (kd : X → Kind) (k : Kind) :
    G.restrict kd (PMap.empty : PMap Loc X) k = PMap.empty :=
  PMap.ext fun _ => rfl

open Classical in
theorem G.sites_sng (kd : X → Kind) (l : Loc) (x : X) (k : Kind) (h : kd x = k) :
    G.Sites kd (PMap.sng l x) k [l] := by
  refine ⟨List.nodup_singleton l, fun l' => ?_⟩
  simp only [List.mem_singleton, PMap.sng_get]
  constructor
  · rintro rfl; exact ⟨x, by simp, h⟩
  · rintro ⟨ψ, e, -⟩
    by_contra hne
    simp [hne] at e

open Classical in
theorem G.sites_sng_none (kd : X → Kind) (l : Loc) (x : X) (k : Kind) (h : kd x ≠ k) :
    G.Sites kd (PMap.sng l x) k [] := by
  refine ⟨List.nodup_nil, fun l' => ?_⟩
  simp only [List.not_mem_nil, false_iff, PMap.sng_get]
  rintro ⟨ψ, e, hk⟩
  by_cases e' : l' = l
  · simp [e'] at e; subst e; exact h hk
  · simp [e'] at e

theorem G.sites_empty (kd : X → Kind) (k : Kind) :
    G.Sites kd (PMap.empty : PMap Loc X) k [] :=
  ⟨List.nodup_nil, fun _ => by simp⟩

open Classical in
theorem G.sites_pair (kd : X → Kind) {l₁ l₂ : Loc} (hl : l₁ ≠ l₂) (x₁ x₂ : X) (k : Kind)
    (h₁ : kd x₁ = k) (h₂ : kd x₂ ≠ k) : G.Sites kd (PMap.pair l₁ x₁ l₂ x₂) k [l₁] := by
  refine ⟨List.nodup_singleton l₁, fun l' => ?_⟩
  simp only [List.mem_singleton, PMap.pair_get]
  constructor
  · rintro rfl; exact ⟨x₁, by simp, h₁⟩
  · rintro ⟨ψ, e, hk⟩
    by_contra hne
    by_cases e₂ : l' = l₂
    · subst e₂; simp [hne] at e; subst e; exact h₂ hk
    · simp [hne, e₂] at e

open Classical in
theorem G.sites_pair' (kd : X → Kind) {l₁ l₂ : Loc} (hl : l₁ ≠ l₂) (x₁ x₂ : X) (k : Kind)
    (h₁ : kd x₁ ≠ k) (h₂ : kd x₂ = k) : G.Sites kd (PMap.pair l₁ x₁ l₂ x₂) k [l₂] := by
  refine ⟨List.nodup_singleton l₂, fun l' => ?_⟩
  simp only [List.mem_singleton, PMap.pair_get]
  constructor
  · rintro rfl; exact ⟨x₂, by simp [Ne.symm hl], h₂⟩
  · rintro ⟨ψ, e, hk⟩
    by_cases e₁ : l' = l₁
    · simp [e₁] at e; subst e; exact absurd hk h₁
    · by_contra hne
      simp [e₁, hne] at e

end

/-! ### Walks of the small worlds, at any cactus -/

variable {K : WCactus}

theorem exW_empty {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop} :
    G.ExW CellUT.kind CellUT.wit R C PMap.empty PMap.empty :=
  G.ExW.mk (w := []) (G.sites_empty _ _) G.ExWits.nil G.BigComp.nil
    (by rw [G.restrict_empty, G.restrict_empty]; exact G.comp_empty_right _)
    (G.comp_empty_right _)

theorem agW_empty : AgWT (PMap.empty : ResUT Loc Val K) PMap.empty :=
  G.AgW.mk (wm := []) (wi := []) (G.sites_empty _ _) (G.sites_empty _ _) G.AgWitsM.nil
    G.AgWitsI.nil G.BigComp.nil G.BigComp.nil
    (by rw [G.restrict_empty]; exact G.comp_empty_right _) (G.comp_empty_right _)

/-- An `imm` cell with an empty witness. -/
def leafImm (t : TSet) (u : Val) : CellUT Loc Val K :=
  CellUT.immOf t u PMap.empty (fun _ _ e => by simp at e)

theorem leafImm_kind (t : TSet) (u : Val) : (leafImm (K := K) (Loc := Loc) t u).kind = .imm :=
  rfl

theorem leafImm_wit (t : TSet) (u : Val) : (leafImm (K := K) (Loc := Loc) t u).wit = PMap.empty :=
  CellUT.wit_immOf _ _ _ _

theorem exW_sng_imm {R : CellUT Loc Val K → CellUT Loc Val K → Prop}
    {C : CellUT Loc Val K → CellUT Loc Val K → CellUT Loc Val K → Prop} (l : Loc) (t : TSet)
    (u : Val) :
    G.ExW CellUT.kind CellUT.wit R C (PMap.sng l (leafImm t u)) PMap.empty :=
  G.ExW.mk (w := []) (G.sites_sng_none _ _ _ _ (by rw [leafImm_kind]; try decide)) G.ExWits.nil G.BigComp.nil
    (by
      rw [G.restrict_sng, G.restrict_sng, if_neg (by rw [leafImm_kind]; try decide),
        if_neg (by rw [leafImm_kind]; try decide)]
      exact G.comp_empty_right _)
    (G.comp_empty_right _)

theorem agW_sng_imm (l : Loc) (t : TSet) (u : Val) :
    AgWT (PMap.sng l (leafImm (K := K) (Loc := Loc) t u)) (PMap.sng l (leafImm t u)) := by
  refine G.AgW.mk (wm := []) (wi := [(l, PMap.empty)])
    (G.sites_sng_none _ _ _ _ (by rw [leafImm_kind]; try decide)) (G.sites_sng _ _ _ _ (by rw [leafImm_kind]; try decide))
    G.AgWitsM.nil ?_ G.BigComp.nil
    (G.BigComp.cons G.BigComp.nil (G.comp_empty_right _)) ?_ (G.comp_empty_right _)
  · refine G.AgWitsI.cons (leafImm t u) (by simp [PMap.sng_get]) (by rw [leafImm_kind]; try decide)
      PMap.empty PMap.empty ?_ ?_ (G.comp_empty_right _) G.AgWitsI.nil
    · rw [leafImm_wit]; exact exW_empty
    · rw [leafImm_wit]; exact agW_empty
  · rw [G.restrict_sng, if_pos (by rw [leafImm_kind]; try decide)]
    exact G.comp_empty_right _

/-- `ℓ₁ ↦ mut(β̄, v, π, P̂), ℓ₂ ↦ imm(γ̄, u, ∅)` is valid when `π` is `∅` or the same `imm` view
at `ℓ₂`: `⦇−⦈` is the world itself. -/
theorem valid_pair {l₁ l₂ : Loc} (hl : l₁ ≠ l₂) (M : CellUT Loc Val K) (hM : M.kind = .mut)
    (t : TSet) (u : Val)
    (hπ : M.wit = PMap.empty ∨ M.wit = PMap.sng l₂ (leafImm t u)) :
    ResUT.Valid (PMap.pair l₁ M l₂ (leafImm t u)) := by
  have hI : (leafImm (K := K) (Loc := Loc) t u).kind = .imm := leafImm_kind t u
  have hex : G.ExW CellUT.kind CellUT.wit CellUT.CompatS CellUT.CompS M.wit PMap.empty := by
    rcases hπ with e | e <;> rw [e]
    · exact exW_empty
    · exact exW_sng_imm _ _ _
  obtain ⟨a, hag, ha⟩ : ∃ a, AgWT M.wit a ∧
      ResUT.CompR (PMap.sng l₂ (leafImm t u)) a (PMap.sng l₂ (leafImm t u)) := by
    rcases hπ with e | e <;> rw [e]
    · exact ⟨_, agW_empty, G.comp_empty_right _⟩
    · exact ⟨_, agW_sng_imm _ _ _, ResUT.compR_self _⟩
  have hEx : ExST (PMap.pair l₁ M l₂ (leafImm t u)) (PMap.sng l₁ M) := by
    refine G.ExW.mk (w := [(l₁, PMap.empty)]) (G.sites_pair _ hl _ _ _ hM (by rw [hI]; simp))
      (G.ExWits.cons M (by simp [PMap.pair_get]) hM hex G.ExWits.nil)
      (G.BigComp.cons G.BigComp.nil (G.comp_empty_right _)) ?_ (G.comp_empty_right _)
    rw [G.restrict_pair_none _ _ _ _ _ _ (by rw [hM]; simp) (by rw [hI]; simp),
      G.restrict_pair _ hl _ _ _ hM (by rw [hI]; simp)]
    exact G.comp_empty_left _
  have hAg : AgWT (PMap.pair l₁ M l₂ (leafImm t u)) (PMap.sng l₂ (leafImm t u)) := by
    refine G.AgW.mk (wm := [(l₁, a)]) (wi := [(l₂, PMap.empty)])
      (G.sites_pair _ hl _ _ _ hM (by rw [hI]; simp))
      (G.sites_pair' _ hl _ _ _ (by rw [hM]; simp) hI)
      (G.AgWitsM.cons M (by simp [PMap.pair_get]) hM hag G.AgWitsM.nil) ?_
      (G.BigComp.cons G.BigComp.nil (G.comp_empty_right _))
      (G.BigComp.cons G.BigComp.nil (G.comp_empty_right _)) ?_ (G.comp_empty_right _)
    · refine G.AgWitsI.cons (leafImm t u) (by simp [PMap.pair_get, Ne.symm hl]) hI
        PMap.empty PMap.empty ?_ ?_ (G.comp_empty_right _) G.AgWitsI.nil
      · rw [leafImm_wit]; exact exW_empty
      · rw [leafImm_wit]; exact agW_empty
    · have e : G.restrict CellUT.kind (PMap.pair l₁ M l₂ (leafImm t u)) Kind.imm =
          PMap.sng l₂ (leafImm t u) := by
        refine PMap.ext fun l' => ?_
        show ((PMap.pair l₁ M l₂ (leafImm t u)).get l').bind _ = _
        rw [PMap.pair_get, PMap.sng_get]
        by_cases e₁ : l' = l₁
        · subst e₁; simp [hM, hl]
        · by_cases e₂ : l' = l₂
          · subst e₂; simp [e₁, hI]
          · simp [e₁, e₂]
      rw [e]
      exact ha
  exact ⟨_, _, _, hEx, hAg, G.comp_sng_sng hl _ _⟩

/-! ### The configuration -/

/-- The cactus before the graft. -/
abbrev K₀ : WCactus := WCactus.ofParent beforeP
/-- The cactus after the graft. -/
abbrev K₁ : WCactus := WCactus.ofParent graftP

/-- `α`, the task's lend. -/
abbrev αL : Life := OrderDual.toDual 1
/-- `β`, the handler's later lend. -/
abbrev βL : Life := OrderDual.toDual 2

/-- The graft keeps every nesting. -/
theorem graftExt : K₀.Ext K₁ := fun {_ _} h =>
  ⟨graftEx_mono h.1, h.2⟩

theorem K₁_lt : K₁.lt αL βL := graftEx_lt

theorem K₀_not_lt : ¬ K₀.lt αL βL := fun h => beforeEx_siblings.2 h.1

theorem anti_single (K : WCactus) (a : Life) : K.Anti (TSet.single a) := by
  intro x hx y hy hxy
  simp only [TSet.single_set, Finset.mem_singleton] at hx hy
  subst hx; subst hy
  exact Cactus.lt_irrefl _ _ hxy

/-- The handler's borrow at `β`, as the task would store it. -/
def borrowAt (K : WCactus) (l₂ : Loc) (u : Val) : ResUT Loc Val K :=
  PMap.sng l₂ (leafImm (TSet.single βL) u)

theorem borrowAt_inStratum_iff (K : WCactus) (l₂ : Loc) (u : Val) :
    ResUT.InStratum (TSet.single αL) (borrowAt (Loc := Loc) K l₂ u) ↔ K.lt αL βL := by
  classical
  constructor
  · intro h
    have := h l₂ (leafImm (TSet.single βL) u) (by simp [borrowAt, PMap.sng_get])
    exact this αL (by simp) βL (by simp)
  · intro h l ψ e
    simp only [borrowAt, PMap.sng_get] at e
    split at e
    · cases e
      intro x hx y hy
      simp only [TSet.single_set, Finset.mem_singleton] at hx hy
      subst hx; subst hy; exact h
    · cases e

/-- **Before the graft the carrier refuses the cell**: the witness holding the borrow at `β` is in
no stratum of `α`, so no `mut` cell at `{α}` stores it. -/
theorem graftCell_refused_before (l₂ : Loc) (u : Val) :
    ¬ ResUT.InStratum (TSet.single αL) (borrowAt (Loc := Loc) (Val := Val) K₀ l₂ u) ∧
    ∀ m : MutT Loc Val K₀, m.ls = TSet.single αL → m.res ≠ borrowAt K₀ l₂ u := by
  refine ⟨fun h => K₀_not_lt ((borrowAt_inStratum_iff K₀ l₂ u).mp h), fun m hm e => ?_⟩
  have := CellUT.wit_inStratum_mut (m := m)
  rw [hm, e] at this
  exact K₀_not_lt ((borrowAt_inStratum_iff K₀ l₂ u).mp this)

/-- **After the graft the carrier admits it**: a `mut` cell at `{α}` whose witness holds the
handler's borrow at `β`, and the world holding it beside the handler's own view is valid. No
lifetime is renamed. -/
theorem graftCell_admitted {l₁ l₂ : Loc} (hl : l₁ ≠ l₂) (v u : Val)
    (P : Val → SPropST Loc Val K₁ (TSet.single αL))
    (hw : P v ⟨borrowAt K₁ l₂ u, (borrowAt_inStratum_iff K₁ l₂ u).mpr K₁_lt⟩) :
    let M := CellUT.mutOf (TSet.single αL) v (borrowAt K₁ l₂ u)
      ((borrowAt_inStratum_iff K₁ l₂ u).mpr K₁_lt) P hw
    ResUT.InStratum (TSet.single αL) (borrowAt (Loc := Loc) (Val := Val) K₁ l₂ u) ∧
      M.lsOf = some (TSet.single αL) ∧ M.wit = borrowAt K₁ l₂ u ∧
      ResUT.Valid (PMap.pair l₁ M l₂ (leafImm (TSet.single βL) u)) := by
  intro M
  exact ⟨(borrowAt_inStratum_iff K₁ l₂ u).mpr K₁_lt, rfl, CellUT.wit_mutOf _ _ _ _ _ _,
    valid_pair hl M rfl _ u (Or.inr (CellUT.wit_mutOf _ _ _ _ _ _))⟩

/-- The world before the graft: the task's `mut` cell at `α` with an empty witness, beside the
handler's view at `β`. Valid in `K₀`. -/
theorem graftWorld_valid_before {l₁ l₂ : Loc} (hl : l₁ ≠ l₂) (v u : Val)
    (P : Val → SPropST Loc Val K₀ (TSet.single αL))
    (hw : P v ⟨PMap.empty, fun _ _ e => by simp at e⟩) :
    ResUT.Valid (PMap.pair l₁ (CellUT.mutOf (TSet.single αL) v PMap.empty
      (fun _ _ e => by simp at e) P hw) l₂ (leafImm (TSet.single βL) u)) :=
  valid_pair hl _ rfl _ u (Or.inl (CellUT.wit_mutOf _ _ _ _ _ _))

/-- **The world before the graft, carried to the tree after it, is valid**; every name kept. -/
theorem graftWorld_valid_after {l₁ l₂ : Loc} (hl : l₁ ≠ l₂) (v u : Val)
    (P : Val → SPropST Loc Val K₀ (TSet.single αL))
    (hw : P v ⟨PMap.empty, fun _ _ e => by simp at e⟩) :
    ResUT.Valid ((PMap.pair l₁ (CellUT.mutOf (TSet.single αL) v PMap.empty
      (fun _ _ e => by simp at e) P hw) l₂ (leafImm (TSet.single βL) u)).map
        (trU graftExt)) :=
  ResUT.Valid.graft graftExt (graftWorld_valid_before hl v u P hw)

/-- **A predicate carried across the graft does not see the new borrow.** No resource of `α`'s
stratum before the graft carries to the witness holding the borrow at `β`. The predicate of a
`mut` cell created before the graft is carried as an image (`trU`, row 5.57's extension by
falsity), so it is false at that witness: storing the handler's borrow into such a cell needs
its invariant re-read at `K₁`, which `trU` does not do. -/
theorem graft_carried_refuses (l₂ : Loc) (u : Val) (r₀ : ResUT Loc Val K₀)
    (h : r₀.InStratum (TSet.single αL)) : r₀.map (trU graftExt) ≠ borrowAt K₁ l₂ u := by
  classical
  intro e
  have hg := congrArg (fun r : ResUT Loc Val K₁ => r.get l₂) e
  simp only [PMap.map_get, borrowAt, PMap.sng_get] at hg
  rw [if_pos trivial] at hg
  cases hc : r₀.get l₂ with
  | none => rw [hc] at hg; cases hg
  | some c =>
      rw [hc] at hg
      simp only [Option.map_some] at hg
      replace hg := Option.some.inj hg
      have hs := h l₂ c hc
      cases c with
      | own v => cases hg
      | «mut» m => cases hg
      | imm i =>
          have hls : i.ls = TSet.single βL := by
            have := congrArg CellUT.lsOf hg
            simpa [trU, leafImm] using this
          have hab : K₀.Above (TSet.single αL) i.ls := hs
          rw [hls] at hab
          exact K₀_not_lt (hab αL (by simp) βL (by simp))

end BoCa.Fig16.Tree

end

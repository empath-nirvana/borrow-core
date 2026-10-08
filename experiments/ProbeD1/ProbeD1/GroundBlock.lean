import ProbeD1.GroundRegress
import ProbeD1.Block

/-!
# ProbeD1 — the block's gate (`GROUND.md` §4.4)

The facts the block push (`Block.lean`) needs before it enters the relation, and the block gates at
the suite's payloads.

* **The stack's shape** is in `R1Block.lean` (`stackOKB_of_ok`, `instStackOKB`, `stackJBaseIff`,
  `guardInstB`), where the re-proved rows read it.
* **The reach**: a single leaf fits no block of two (`blockFitsLeafLe`), and the reborrowed blocks
  of the pair and of an array fit (`blockFitsReb`).
* **The guard at a block push**: the start of a block lend keeps the guard's views (`pvlStartB`),
  and a block of views composed with the callback's resource meets the table and the views at the
  pushed stack (`pairGuardHoldsB`).
* **The block gate** (`LoadGateNilB`): `withload`'s draft step at the empty stack, at a payload
  whose reborrow puts several cells at `β`, by a single push or a block push.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty)

/-! ### The reach -/

/-- **A single leaf fits no block of two**: a callback at `Mut 'x T` or `Imm 'x T` (every
`withbor`'s, and an unwinding form's at a `Ref` or `Mut` payload) has no block push, so D12 does not
reach it. -/
def BlockFitsLeafLe : Prop :=
  ∀ (x : LifeVar) (τ : LStack) (S : VTy),
    (BlockFits x τ (.mut (.var x) S) → τ.length ≤ 1) ∧
    (BlockFits x τ (.imm (.var x) S) → τ.length ≤ 1)

theorem blockFitsLeafLe : BlockFitsLeafLe := by
  intro x τ S
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases h <;> simp
  · cases h <;> simp

/-- **The reborrowed blocks fit**: two `imm` entries at `1` fit the pair's reborrow
`Imm 'x 1 ⊗ Imm 'x 1`, and any number of `imm` entries at `I32` fit an array's, `[Imm 'x I32]`. -/
def BlockFitsReb : Prop :=
  (∀ (x : LifeVar) (e₁ e₂ : LEnt), (∃ u, e₁.k = .imm u) → (∃ u, e₂.k = .imm u) →
      e₁.T = .unit → e₂.T = .unit → BlockFits x [e₁, e₂] (pairTy.immReborrow (.var x))) ∧
  ∀ (x : LifeVar) (τ : LStack), (∀ e ∈ τ, (∃ u, e.k = .imm u) ∧ e.T = .int .w32) →
    BlockFits x τ ((VTy.array (.int .w32)).immReborrow (.var x))

/-- Every list of `imm` entries at `S` fits the family `[Imm 'x S]`. -/
theorem blockFits_fam_imm (x : LifeVar) (S : VTy) :
    ∀ τ : LStack, (∀ e ∈ τ, (∃ u, e.k = .imm u) ∧ e.T = S) → BlockFits x τ (.fam (.imm (.var x) S))
  | [], _ => .nil _
  | e :: τ, h =>
      .fam (τ₁ := [e]) (τ₂ := τ) (.imm (h e (List.mem_cons_self ..)).1 (h e (List.mem_cons_self ..)).2)
        (blockFits_fam_imm x S τ fun e' he' => h e' (List.mem_cons_of_mem _ he'))
        (List.Perm.refl _)

theorem blockFitsReb : BlockFitsReb := by
  refine ⟨fun x e₁ e₂ h₁ h₂ hT₁ hT₂ => ?_, fun x τ h => blockFits_fam_imm x _ τ h⟩
  exact .tensor (τ₁ := [e₁]) (τ₂ := [e₂]) (.imm h₁ hT₁) (.imm h₂ hT₂) (List.Perm.refl _)

/-! ### The guard at a block push -/

/-- **The start of a block lend keeps the guard's views**: the callback's resource, holding at a
block place only `own` cells frozen under an `imm` ancestor, joined to the block's views, has the
guard's views at the pushed stack. `pvlStart` with the block's relaxed `placeFree`. -/
def PVLStartB : Prop :=
  ∀ (s s' : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (τ : LStack) (α : Life)
    (ρ a R : WRes), StackOKB σ αs → List.IsChain (· < ·) (α :: αs) →
    (τ.map LEnt.l).Nodup → (∀ e ∈ τ, e.l ∉ σ.map LEnt.l) →
    (∀ e' ∈ σ, ∀ y, VFree y e'.T → s'.find? y = s.find? y) →
    PlaceViewsL s σ αs ls ρ →
    (∀ e ∈ τ, ∀ ψ, DeepAt ρ e.l ψ → ψ.kind = Kind.own ∧ ¬ ExAt ρ e.l ψ) →
    vwSW s' [] τ (τ.map fun _ => true) (blockL τ α) ls a →
    PlaceViewsL s' (τ ++ σ) (blockL τ α ++ αs) ls a →
    ResU.CompS ρ a R → PlaceViewsL s' (τ ++ σ) (blockL τ α ++ αs) ls R

/-- Pushing a block whose places hold only frozen `own` cells of the resource keeps its guard's
views, read at a reading that agrees with the old one at the old entries' payload types. -/
theorem placeViewsL_pushB {s s' : LSub} {σ : LStack} {αs : List Life} {ls : List SRec}
    {τ : LStack} {α : Life} (hs : ∀ e' ∈ σ, ∀ y, VFree y e'.T → s'.find? y = s.find? y)
    {ρ : WRes} (h : PlaceViewsL s σ αs ls ρ)
    (hfree : ∀ e ∈ τ, ∀ ψ, DeepAt ρ e.l ψ → ψ.kind = Kind.own ∧ ¬ ExAt ρ e.l ψ) :
    PlaceViewsL s' (τ ++ σ) (blockL τ α ++ αs) ls ρ := by
  have hlen : (blockL τ α).length = τ.length := by simp [blockL]
  refine ⟨fun l ψ hx ho e' α' hi => ?_, fun l ψ hd ho hl => ?_⟩
  · by_cases hlτ : l ∈ τ.map LEnt.l
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hlτ
      exact absurd hx (hfree e he ψ hx.toDeepAt).2
    · rw [innerAt_append_right hlen hlτ] at hi
      have he' : e' ∈ σ := (List.of_mem_zip (innerAt_mem hi).1).1
      exact (vwEW_congr (hs e' he')).mpr (h.1 l ψ hx ho e' α' hi)
  · have hl' : l ∈ σ.map LEnt.l := by
      rw [List.map_append, List.mem_append] at hl
      rcases hl with hl | hl
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hl
        exact absurd (hfree e he ψ hd).1 ho
      · exact hl
    obtain ⟨e', α', hm, hel, hv⟩ := h.2 l ψ hd ho hl'
    refine ⟨e', α', ?_, hel, (vwEW_congr (hs e' (List.of_mem_zip hm).1)).mpr hv⟩
    rw [List.zip_append hlen.symm]
    exact List.mem_append_right _ hm

theorem pvlStartB : PVLStartB := by
  intro s s' σ αs ls τ α ρ a R _ _ _ _ hs h hfree _ ha hc
  exact placeViewsL_join hc (placeViewsL_pushB hs h hfree) ha

/-! ### Cells at a block push -/

/-- A cell whose lifetime is strictly above `α` lies in `α`'s stratum. -/
theorem cell_inStratum_of_lt_at {ψ : CellU BoCa.Loc Val} {α : Life} (h : α < ψ.at) :
    ψ.InStratum α := by
  cases ψ with
  | own v => trivial
  | imm i => exact h
  | «mut» m => exact h

/-- A cell exactly at `α` lies in the stratum of `↓α`. -/
theorem AtExactly.inStratum_down {ψ : CellU BoCa.Loc Val} {α : Life} (h : AtExactly α ψ) :
    ψ.InStratum (Life.down α) :=
  cell_inStratum_of_lt_at (h.1 ▸ GhostEnd.down_lt α)

/-- A cell in `α`'s stratum lies in the stratum of `↓α`. -/
theorem cell_inStratum_down {ψ : CellU BoCa.Loc Val} {α : Life} (h : ψ.InStratum α) :
    ψ.InStratum (Life.down α) :=
  h.mono (le_of_lt (GhostEnd.down_lt α))

/-- An `imm` cell over the singleton `{β}` is exactly at `β`. -/
theorem atExactly_singleton (β : Life) (v : Val) (χ : WRes)
    (h : χ.InStratum (LSet.singleton β).join) :
    AtExactly β (CellU.immOf (LSet.singleton β) v χ h) :=
  ⟨rfl, fun t ht y hy => by
    simp only [CellU.lsOf_immOf, Option.some.injEq] at ht
    subst ht; exact hy⟩

/-- **A reborrowed cell is exactly at `β` or above it** ([TR] p. 5's `reb_β`): over an `own` or
`mut` cell it is `imm({β}, …)`; over an `imm` cell of the source, which lies above `β`, it keeps a
subset of that cell's lifetimes. -/
theorem reb_exact_or_above {β : Life} {R cb : WRes} (hr : ResU.Reb β R cb) {l : BoCa.Loc}
    {ψ : CellU BoCa.Loc Val} (e : cb.get l = some ψ) : AtExactly β ψ ∨ ψ.InStratum β := by
  have hk : ψ.kind = Kind.imm := (reb_cell hr e).1
  rcases reb_cell_ls hr e with ⟨-, hls⟩ | ⟨ζ, hζ, hζk, -, -, hsub⟩
  · left
    rcases CellU.rep ψ with ⟨v, rfl⟩ | ⟨s, v, χ, h, rfl⟩ | ⟨b, v, χ, h, P, hw, rfl⟩
    · exact absurd hk (by simp [CellU.kind, CellU.ownOf])
    · simp only [CellU.lsOf_immOf, Option.some.injEq] at hls
      subst hls
      exact atExactly_singleton β v χ h
    · exact absurd hk (by simp)
  · right
    rcases CellU.rep ζ with ⟨v, rfl⟩ | ⟨s, v, χ, h, rfl⟩ | ⟨b, v, χ, h, P, hw, rfl⟩
    · exact absurd hζk (by simp [CellU.kind, CellU.ownOf])
    · rcases CellU.rep ψ with ⟨v', rfl⟩ | ⟨t, v', χ', h', rfl⟩ | ⟨b', v', χ', h', P', hw', rfl⟩
      · exact absurd hk (by simp [CellU.kind, CellU.ownOf])
      · have hζs : β < s.meet := hr.1 l _ hζ
        have hts : ∀ y, t.mem y → s.mem y := hsub s t (by simp) (by simp)
        show β < t.meet
        exact lt_of_lt_of_le hζs (s.meet_least _ (hts _ t.meet_mem))
      · exact absurd hk (by simp)
    · exact absurd hζk (by simp)

/-- **The callback's part holds nothing at the composite's block places.** A composite
`ρc ● cb` whose left part holds no cell, at any depth, at the places `cb` holds a cell. -/
theorem get_of_free {ρc cb ρ : WRes} (hc : ResU.CompS ρc cb ρ)
    (hfree : ∀ (l : BoCa.Loc) (ψ φ : CellU BoCa.Loc Val), cb.get l = some ψ → ¬ DeepAt ρc l φ)
    (l : BoCa.Loc) :
    (∃ ψ, cb.get l = some ψ ∧ ρc.get l = none ∧ ρ.get l = some ψ) ∨
      (cb.get l = none ∧ ρ.get l = ρc.get l) := by
  rcases ResU.Comp.get hc l with ⟨h₁, h₂, h⟩ | ⟨ψ, h₁, h₂, h⟩ | ⟨ψ, h₁, h₂, h⟩ |
      ⟨ψ₁, ψ₂, ψ, h₁, h₂, h, -⟩
  · exact Or.inr ⟨h₂, by rw [h, h₁]⟩
  · exact Or.inr ⟨h₂, by rw [h, h₁]⟩
  · exact Or.inl ⟨ψ, h₂, h₁, h⟩
  · exact absurd (DeepAt.top h₁) (hfree l ψ₂ ψ₁ h₂)

/-- **The table and the guard's views at a pushed stack with no outer entry**: every cell is at or
above the block's lifetime, every cell at an unlent place above it, and every borrow cell at any
depth at a block place is the top-level view of its entry. -/
theorem guard_nil_of {s : LSub} {ls : List SRec} {τ : LStack} {β : Life} {ρ : WRes}
    (hne : τ ≠ []) (hhead : ρ.InStratum (Life.down β))
    (hout : ∀ k ψ, k ∉ τ.map LEnt.l → ρ.get k = some ψ → ψ.InStratum β)
    (hview : ∀ e ∈ τ, ∀ ψ, DeepAt ρ e.l ψ → ψ.kind ≠ Kind.own →
      vwEW s e true β ls (ResU.single e.l ψ)) :
    TabAtS τ (blockL τ β) ρ ∧ PlaceViewsL s τ (blockL τ β) ls ρ := by
  obtain ⟨e₀, τ', rfl⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨⟨fun a ha => ?_, fun a ha k ψ hk hg => ?_⟩, fun l ψ hx ho e α hi => ?_,
    fun l ψ hd ho hl => ?_⟩
  · simp only [blockL, List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at ha
    subst ha; exact hhead
  · have : a = β := by
      have hmem := List.mem_of_getLast? ha
      simp only [blockL, List.mem_map] at hmem
      obtain ⟨_, _, rfl⟩ := hmem; rfl
    subst this
    exact hout k ψ hk hg
  · obtain ⟨hm, hel⟩ := innerAt_mem hi
    have hα : α = β := snd_of_mem_zip_blockL hm
    subst hα; subst hel
    exact hview e (List.of_mem_zip hm).1 ψ hx.toDeepAt ho
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hl
    exact ⟨e, β, mem_zip_blockL he β, rfl, hview e he ψ hd ho⟩

/-! ### The guard at a block push, at every stack -/

/-- **A block of views meets the guard at the pushed stack** (`GROUND.md` §4.4). At a stack in
shape, a block's own lend whose places hold only frozen `own` cells of the callback's resource
`ρc`, and a part `cb` holding exactly the block's places, each its entry's view at the block's
lifetime: the composite meets the table and the views at the pushed stack. Two hypotheses are added
to the design's statement, both `PVLStart`'s: the pushed reading agrees with the old one at the old
entries' payload types, and the views' nested cells at the stack's places are views (at a data
payload a view's witness is empty, so its only cell is its own). -/
def PairGuardHoldsB : Prop :=
  ∀ (δ : LSub) (σ : LStack) (αs : List Life) (ls : List SRec) (x : LifeVar) (β : Life)
    (τ : LStack) (cb ρc ρ : WRes),
    StackOKB σ αs → OwnOKB δ σ αs x τ β ρc → TabAtS σ αs ρc →
    PlaceViewsL (extS δ σ αs) σ αs ls ρc →
    (∀ e ∈ τ, ∃ ψ : CellU BoCa.Loc Val, cb.get e.l = some ψ ∧
      vwEW (extS (δ.extend x β) (τ ++ σ) (blockL τ β ++ αs)) e true β ls (ResU.single e.l ψ)) →
    (∀ l ψ, cb.get l = some ψ → l ∈ τ.map LEnt.l) → ResU.CompS ρc cb ρ →
    (∀ e' ∈ σ, ∀ y, VFree y e'.T →
      (extS (δ.extend x β) (τ ++ σ) (blockL τ β ++ αs)).find? y = (extS δ σ αs).find? y) →
    PlaceViewsL (extS (δ.extend x β) (τ ++ σ) (blockL τ β ++ αs)) (τ ++ σ) (blockL τ β ++ αs)
      ls cb →
    TabAtS (τ ++ σ) (blockL τ β ++ αs) ρ ∧
      PlaceViewsL (extS (δ.extend x β) (τ ++ σ) (blockL τ β ++ αs)) (τ ++ σ)
        (blockL τ β ++ αs) ls ρ

theorem pairGuardHoldsB : PairGuardHoldsB := by
  intro δ σ αs ls x β τ cb ρc ρ hokB hown ht hpv hviews hdom hc hs hcbpv
  refine ⟨⟨fun a ha => ?_, fun a ha k ψ hk hg => ?_⟩,
    placeViewsL_join hc (placeViewsL_pushB hs hpv hown.placeFree) hcbpv⟩
  · obtain ⟨e₀, τ', rfl⟩ := List.exists_cons_of_ne_nil hown.ne
    simp only [blockL, List.map_cons, List.cons_append, List.head?_cons, Option.mem_def,
      Option.some.injEq] at ha
    subst ha
    intro l ψ hg
    rcases top_split hc hg with h₁ | h₂ | ⟨ψ₁, ψ₂, h₁, h₂, -⟩
    · exact cell_inStratum_down (hown.below l ψ h₁)
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp (hdom l ψ h₂)
      obtain ⟨ψ', hψ', hv⟩ := hviews e he
      rw [hψ'] at h₂; cases h₂
      exact (vwEW_atExactly rfl hv).inStratum_down
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp (hdom _ ψ₂ h₂)
      exact absurd (ExAt.top h₁) (hown.placeFree e he ψ₁ (DeepAt.top h₁)).2
  · have hkτ : k ∉ τ.map LEnt.l := fun h => hk (by
      rw [List.map_append]; exact List.mem_append_left _ h)
    have hkσ : k ∉ σ.map LEnt.l := fun h => hk (by
      rw [List.map_append]; exact List.mem_append_right _ h)
    have hcbk : cb.get k = none := by
      cases h : cb.get k with
      | none => rfl
      | some ψ' => exact absurd (hdom k ψ' h) hkτ
    have hρc : ρc.get k = some ψ := by
      rcases top_split hc hg with h₁ | h₂ | ⟨ψ₁, ψ₂, h₁, h₂, -⟩
      · exact h₁
      · rw [hcbk] at h₂; cases h₂
      · rw [hcbk] at h₂; cases h₂
    cases hαs : αs.getLast? with
    | none =>
        have hnil : αs = [] := List.getLast?_eq_none_iff.mp hαs
        subst hnil
        rw [List.append_nil] at ha
        have hmem : a ∈ blockL τ β := List.mem_of_getLast? ha
        obtain ⟨_, _, rfl⟩ := List.mem_map.mp hmem
        exact hown.below k ψ hρc
    | some o =>
        have hao : o = a := by
          rw [List.getLast?_append, hαs] at ha
          simpa using ha
        subst hao
        exact ht.2 o hαs k ψ hkσ hρc

/-! ### The block gate at the empty stack: the guard -/

/-- **The view of an exact cell at a data payload**: an `imm` cell exactly at `β` over a value its
payload type relates at the empty witness is its `imm` entry's view. -/
theorem vwEW_of_exact {s : LSub} {e : LEnt} {u₀ : Val} (hk : e.k = .imm u₀) {β : Life}
    {ls : List SRec} {S : LSet} {v : Val} {h : ResU.InStratum S.join (PMap.empty : WRes)}
    (hS : ∀ y, S.mem y → y = β)
    (hv : ∀ ls₀ : List SRec, vC true e.T ls₀ s v PMap.empty) :
    vwEW s e true β ls (ResU.single e.l (CellU.immOf S v PMap.empty h)) :=
  (vwEW_imm_iff hk).mpr ⟨rfl, S, v, PMap.empty, h, rfl, hS,
    ls.filter (fun x => decide (β < x.2)), hv _, fun x => by simp [Life.Sqsupset]⟩

/-- **The table and the guard's views at the gate**, read off the reborrowed cells: the callback's
part `ρc` above `β` and holding nothing at `cb`'s places; `cb`'s cells exactly at `β` or above it,
with empty witnesses; every place holding an exact cell lent by an entry, and every entry's place
either holding an exact cell, which is the entry's view, or holding no cell of the composite. -/
theorem gate_guard {s : LSub} {ls : List SRec} {τ : LStack} {β : Life} {ρc cb ρ : WRes}
    (hne : τ ≠ []) (hst : ρc.InStratum β)
    (hfree : ∀ (l : BoCa.Loc) (ψ φ : CellU BoCa.Loc Val), cb.get l = some ψ → ¬ DeepAt ρc l φ)
    (hc : ResU.CompS ρc cb ρ)
    (hcells : ∀ l ψ, cb.get l = some ψ → AtExactly β ψ ∨ ψ.InStratum β)
    (hwit : ∀ l ψ, cb.get l = some ψ → ψ.wit = PMap.empty)
    (hlent : ∀ l ψ, cb.get l = some ψ → AtExactly β ψ → l ∈ τ.map LEnt.l)
    (hent : ∀ e ∈ τ, (∃ ψ, cb.get e.l = some ψ ∧ vwEW s e true β ls (ResU.single e.l ψ)) ∨
      ∀ ψ, ¬ DeepAt ρ e.l ψ) :
    TabAtS τ (blockL τ β) ρ ∧ PlaceViewsL s τ (blockL τ β) ls ρ := by
  refine guard_nil_of hne (fun l ψ hg => ?_) (fun k ψ hk hg => ?_) (fun e he ψ hd ho => ?_)
  · rcases get_of_free hc hfree l with ⟨ψ', h₁, -, h⟩ | ⟨-, h⟩
    · rw [hg] at h; cases h
      rcases hcells l ψ h₁ with hx | hx
      · exact hx.inStratum_down
      · exact cell_inStratum_down hx
    · rw [hg] at h
      exact cell_inStratum_down (hst l ψ h.symm)
  · rcases get_of_free hc hfree k with ⟨ψ', h₁, -, h⟩ | ⟨-, h⟩
    · rw [hg] at h; cases h
      rcases hcells k ψ h₁ with hx | hx
      · exact absurd (hlent k ψ h₁ hx) hk
      · exact hx
    · rw [hg] at h
      exact hst k ψ h.symm
  · rcases hent e he with ⟨ψ', hψ', hv⟩ | hno
    · cases hd with
      | top hg =>
          rcases get_of_free hc hfree e.l with ⟨ψ'', h₁, -, h⟩ | ⟨h₁, -⟩
          · rw [hg] at h; cases h
            rw [hψ'] at h₁; cases h₁
            exact hv
          · rw [hψ'] at h₁; cases h₁
      | @wit _ m _ φ _ em hw =>
          rcases get_of_free hc hfree m with ⟨φ', h₁, -, h⟩ | ⟨-, h⟩
          · rw [em] at h; cases h
            rw [hwit m φ h₁] at hw
            cases hw with
            | top e' => exact absurd e' (by simp)
            | wit e' => exact absurd e' (by simp)
          · rw [em] at h
            exact absurd (DeepAt.wit h.symm hw) (hfree e.l ψ' ψ hψ')
    · exact absurd hd (hno ψ)

/-! ### The block gate -/

/-- **The block gate at the empty stack** (`GROUND.md` §4.4): at a view `CohE` admits, whichever of
its two cases, [TR] 6.175's argument, the payload reborrowed at a fresh `β`, is admitted by a single
own push or a block push of the callback, related at the pushed index, with the composite meeting
the guard there. `x ∉ CTy.binders (C' x)` is added, as in `LoadGateNil`. -/
def LoadGateNilB (A : VTy) (C' : LifeVar → CTy) : Prop :=
  ∀ (δ : LSub) (ls : List SRec) (W : WRes) (ℓ : BoCa.Loc) (u : Val) (R : WRes) (x : LifeVar)
    (c : Lifetime.Life) (β : Life) (cb ρc ρ : WRes),
    CohE (rsOf ls) ℓ A δ → LoadPay W (rsOf ls) ℓ u R → ¬ VFree x A → δ.find? x = none →
    x ∉ CTy.binders (C' x) →
    (∀ y, VFree y A → δ.find? y ≠ none) → ResU.Reb β R cb →
    vC true (A.immReborrow (.var x)) ls (δ.extend x β) u cb →
    ρc.InStratum β → β < ⊤ → LtLife δ c β → RecsOutside [β] ls → SubFresh δ β →
    (∀ (l : BoCa.Loc) (ψ φ : CellU BoCa.Loc Val), cb.get l = some ψ → ¬ DeepAt ρc l φ) →
    ResU.CompS ρc cb ρ →
    ∃ τ : LStack, ((∃ en, τ = [en] ∧ OwnPushM δ (.all x c (C' x)) ρc ([], []) en β) ∨
        OwnPushB δ (.all x c (C' x)) ρc ([], []) τ β) ∧
      vRLM (ℍ := ℍ) .binder0 none τ (δ.extend x β) (A.immReborrow (.var x)) (blockL τ β) ls u cb ∧
      TabAtS τ (blockL τ β) ρ ∧ PlaceViewsL (extS (δ.extend x β) τ (blockL τ β)) τ (blockL τ β) ls ρ

/-- The reading `δ, 'x ↦ β` finds `x` at `β`. -/
theorem find_extend_self (δ : LSub) (x : LifeVar) (β : Life) : (δ.extend x β).find? x = some β := by
  simp [LSub.find?, LSub.extend, Lifetime.assocFind]; rfl

/-- A block of entries named `x` at `a`, read over a reading sending `x` to `a`, reads every
variable as that reading does. -/
theorem extS_block_find {δ : LSub} {x : LifeVar} {a : Life} :
    ∀ (τ : LStack), (∀ e ∈ τ, e.x = x) → ∀ y,
      (extS (δ.extend x a) τ (blockL τ a)).find? y = (δ.extend x a).find? y
  | [], _, _ => rfl
  | e :: τ, h, y => by
      have he : e.x = x := h e (List.mem_cons_self ..)
      have ih := extS_block_find (δ := δ) (x := x) (a := a) τ
        (fun e' he' => h e' (List.mem_cons_of_mem _ he')) y
      show ((extS (δ.extend x a) τ (blockL τ a)).extend e.x a).find? y = _
      rw [he]
      by_cases hy : y = x
      · subst hy; simp [LSub.find?, LSub.extend, Lifetime.assocFind]
      · have : ((extS (δ.extend x a) τ (blockL τ a)).extend x a).find? y =
            (extS (δ.extend x a) τ (blockL τ a)).find? y := by
          simp [LSub.find?, LSub.extend, Lifetime.assocFind, Ne.symm hy]
        rw [this, ih]

/-- **Core's `Imm` leaf at `1`, at a reading sending `x` to `β`**: one `imm` cell at the leaf's
place, over `()` and the empty witness, at lifetimes `⊒ β`. -/
theorem vC_imm_unit_leaf {δx : LSub} {x : LifeVar} {β : Life} (hx : δx.find? x = some β)
    {ls : List SRec} {v : Val} {ρ : WRes} (h : vC true (.imm (.var x) .unit) ls δx v ρ) :
    ∃ (l : BoCa.Loc) (s : LSet) (hs : ResU.InStratum s.join (PMap.empty : WRes)),
      v = .loc l ∧ ρ = ResU.single l (CellU.immOf s .unit PMap.empty hs) ∧ β ≤ s.meet := by
  obtain ⟨α, hα, l, hsep⟩ := h
  rw [Lifetime.Life.interp_var, hx] at hα
  have hαβ : (α : Life) = β := (Option.some.inj hα).symm
  obtain ⟨⟨rfl, -⟩, s, u, χ, hχ, ls₀, hρ, hP, hle, -⟩ := pure_sep_iff.mp hsep
  rw [hαβ] at hle
  obtain ⟨rfl, rfl⟩ := hP
  exact ⟨l, s, hχ, rfl, hρ, hle⟩

/-- **A leaf at the pushed stack**: Core's `Imm` leaf at `1`, its cell exactly at `β` when an entry
lends its place, is `vRLM`'s at a stack of `imm` entries at `1` named `x`, all at `β`. -/
theorem vRLM_imm_unit_at {τ : LStack} {δ : LSub} {x : LifeVar} {β : Life} {ls : List SRec}
    {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val}
    (hxτ : ∀ e ∈ τ, e.x = x) (hTτ : ∀ e ∈ τ, e.T = .unit ∧ ∃ u, e.k = .imm u)
    (hv : vC true (.imm (.var x) .unit) ls (δ.extend x β) (.loc l) (ResU.single l ψ))
    (hex : l ∈ τ.map LEnt.l → AtExactly β ψ) :
    vRLM (ℍ := ℍ) .binder0 none τ (δ.extend x β) (.imm (.var x) .unit) (blockL τ β) ls (.loc l)
      (ResU.single l ψ) := by
  rw [vRLM]
  refine ⟨?_, fun l' e α hl' hi => ?_, fun l' _ _ y hy => absurd hy (by simp [wClose, VFree])⟩
  · show vC true (.imm (.var x) .unit) ls (extS (δ.extend x β) τ (blockL τ β)) (.loc l)
      (ResU.single l ψ)
    rw [vC_congr _ (fun y _ => extS_block_find τ hxτ y)]
    exact hv
  · cases hl'
    obtain ⟨hm, hel⟩ := innerAt_mem hi
    have hα : α = β := snd_of_mem_zip_blockL hm
    have he : e ∈ τ := (List.of_mem_zip hm).1
    obtain ⟨hT, u, hk⟩ := hTτ e he
    refine ⟨by unfold CohKind; rw [hk]; exact ⟨trivial, by rw [hT]; exact TyEq.refl _ _⟩,
      fun ψ' hψ' => ?_⟩
    rw [hel.symm, ResU.single_get_self] at hψ'
    cases hψ'
    rw [hα]
    exact (hex (List.mem_map.mpr ⟨e, he, hel⟩)).1

/-- The entry lending `l` at `'x`: kind `imm`, payload `1`. -/
def unitEnt (l : BoCa.Loc) (x : LifeVar) : LEnt := ⟨l, x, .unit, .imm .unit, fun _ => true⟩

/-- A cell of a composite of two single cells is at one of their places. -/
theorem get_two_singles {l₁ l₂ : BoCa.Loc} {ψ₁ ψ₂ : CellU BoCa.Loc Val} {cb : WRes}
    (hc : ResU.CompS (ResU.single l₁ ψ₁) (ResU.single l₂ ψ₂) cb) {l : BoCa.Loc}
    {ψ : CellU BoCa.Loc Val} (h : cb.get l = some ψ) : l = l₁ ∨ l = l₂ := by
  by_contra hn
  simp only [not_or] at hn
  rcases ResU.Comp.get hc l with ⟨-, -, h'⟩ | ⟨_, h₁, -, -⟩ | ⟨_, -, h₂, -⟩ | ⟨_, _, _, h₁, -, -, -⟩
  · rw [h] at h'; cases h'
  · rw [ResU.single_get_ne _ hn.1] at h₁; cases h₁
  · rw [ResU.single_get_ne _ hn.2] at h₂; cases h₂
  · rw [ResU.single_get_ne _ hn.1] at h₁; cases h₁

/-- A cell above an `imm` cell over `()` and the empty witness is an `imm` cell over them. -/
theorem immSub_unit_form {s : LSet} {hs : ResU.InStratum s.join (PMap.empty : WRes)}
    {φ : CellU BoCa.Loc Val} (h : ImmSub (CellU.immOf s .unit PMap.empty hs) φ) :
    ∃ (S : LSet) (hS : ResU.InStratum S.join (PMap.empty : WRes)),
      φ = CellU.immOf S .unit PMap.empty hS := by
  rcases h with rfl | ⟨S, S', v, χ, h₀, h', e₀, rfl, -⟩
  · exact ⟨s, hs, rfl⟩
  · obtain ⟨-, rfl, rfl⟩ := CellU.immOf_inj e₀
    exact ⟨S', h', rfl⟩

/-- **The block gate at the pair** (`GROUND.md` §4.4): `LoadGateNilB` at `Ref 1 ⊗ Ref 1`, at a
callback-shaped type whose argument is the pair's reborrow. The entries lend the places where the
reborrow leaves a cell exactly at `β`: two make a block push, one a single push, none a single push
at a free place (`FreePlaceExists`). A cell above `β` (over an `imm` cell of the source) is left
unlent, inside the table's stratum. -/
theorem loadGateNilB_pair_of (hfp : FreePlaceExists) (C' : LifeVar → CTy)
    (hcb : ∀ x, CbArg (C' x) (pairTy.immReborrow (.var x)))
    (harr : ∀ x A D, C' x = .arr A D → A = pairTy.immReborrow (.var x)) :
    LoadGateNilB (ℍ := ℍ) pairTy C' := by
  intro δ ls W ℓ u R x c β cb ρc ρ _ _ _ _ hbind _ hreb hv hst _ hlt _ _ hfree hc
  have hxβ := find_extend_self δ x β
  obtain ⟨v₁, v₂, hsep⟩ := hv
  obtain ⟨rfl, c₁, c₂, hc12, h₁, h₂⟩ := pure_sep_iff.mp hsep
  obtain ⟨l₁, s₁, hs₁, rfl, rfl, -⟩ := vC_imm_unit_leaf hxβ h₁
  obtain ⟨l₂, s₂, hs₂, rfl, rfl, -⟩ := vC_imm_unit_leaf hxβ h₂
  obtain ⟨φ₁, hφ₁, hsub₁⟩ := top_of_compS_left hc12 (ResU.single_get_self l₁ _)
  obtain ⟨φ₂, hφ₂, hsub₂⟩ := top_of_compS_left (ResU.CompS.comm hc12) (ResU.single_get_self l₂ _)
  have hdom : ∀ l ψ, cb.get l = some ψ → l = l₁ ∨ l = l₂ := fun l ψ h => get_two_singles hc12 h
  have hcellOf : ∀ l ψ, cb.get l = some ψ → ψ = φ₁ ∨ ψ = φ₂ := by
    intro l ψ h
    rcases hdom l ψ h with rfl | rfl
    · rw [hφ₁] at h; exact Or.inl (Option.some.inj h).symm
    · rw [hφ₂] at h; exact Or.inr (Option.some.inj h).symm
  have hform : ∀ l ψ, cb.get l = some ψ → ∃ (S : LSet) (hS : ResU.InStratum S.join (PMap.empty : WRes)),
      ψ = CellU.immOf S .unit PMap.empty hS := by
    intro l ψ h
    rcases hcellOf l ψ h with rfl | rfl
    · exact immSub_unit_form hsub₁
    · exact immSub_unit_form hsub₂
  have hwit : ∀ l ψ, cb.get l = some ψ → ψ.wit = PMap.empty := by
    intro l ψ h
    obtain ⟨S, hS, rfl⟩ := hform l ψ h
    exact CellU.wit_immOf _ _ _ _
  have hcells : ∀ l ψ, cb.get l = some ψ → AtExactly β ψ ∨ ψ.InStratum β :=
    fun l ψ h => reb_exact_or_above hreb h
  have hρ₁ : ρ.get l₁ = some φ₁ := by
    rcases get_of_free hc hfree l₁ with ⟨ψ, h, -, hr⟩ | ⟨h, -⟩
    · rw [hφ₁] at h; cases h; exact hr
    · rw [hφ₁] at h; cases h
  have hρ₂ : ρ.get l₂ = some φ₂ := by
    rcases get_of_free hc hfree l₂ with ⟨ψ, h, -, hr⟩ | ⟨h, -⟩
    · rw [hφ₂] at h; cases h; exact hr
    · rw [hφ₂] at h; cases h
  -- the relation at a stack of `imm` entries at `1` named `x`
  have hrel : ∀ τ : LStack, (∀ e ∈ τ, e.x = x) → (∀ e ∈ τ, e.T = .unit ∧ ∃ u, e.k = .imm u) →
      (l₁ ∈ τ.map LEnt.l → AtExactly β φ₁) → (l₂ ∈ τ.map LEnt.l → AtExactly β φ₂) →
      vRLM (ℍ := ℍ) .binder0 none τ (δ.extend x β) (pairTy.immReborrow (.var x)) (blockL τ β) ls
        (.pair (.loc l₁) (.loc l₂)) cb := by
    intro τ hx hT hx₁ hx₂
    show vRLM (ℍ := ℍ) .binder0 none τ (δ.extend x β)
      (.tensor (.imm (.var x) .unit) (.imm (.var x) .unit)) (blockL τ β) ls _ cb
    rw [vRLM]
    exact ⟨.loc l₁, .loc l₂, pure_sep_mk rfl ⟨_, _, hc12,
      vRLM_imm_unit_at hx hT h₁ fun hm => (hx₁ hm).of_immSub hsub₁,
      vRLM_imm_unit_at hx hT h₂ fun hm => (hx₂ hm).of_immSub hsub₂⟩⟩
  -- the guard at such a stack
  have hguard : ∀ τ : LStack, τ ≠ [] → (∀ e ∈ τ, e.T = .unit ∧ ∃ u, e.k = .imm u) →
      (∀ l ψ, cb.get l = some ψ → AtExactly β ψ → l ∈ τ.map LEnt.l) →
      (∀ e ∈ τ, (∃ ψ, cb.get e.l = some ψ ∧ AtExactly β ψ) ∨ ∀ ψ, ¬ DeepAt ρ e.l ψ) →
      TabAtS τ (blockL τ β) ρ ∧
        PlaceViewsL (extS (δ.extend x β) τ (blockL τ β)) τ (blockL τ β) ls ρ := by
    intro τ hne hT hlent hent
    refine gate_guard hne hst hfree hc hcells hwit hlent (fun e he => ?_)
    rcases hent e he with ⟨ψ, hψ, hex⟩ | hno
    · refine Or.inl ⟨ψ, hψ, ?_⟩
      obtain ⟨S, hS, rfl⟩ := hform e.l ψ hψ
      obtain ⟨hTe, u₀, hk⟩ := hT e he
      exact vwEW_of_exact hk (fun y hy => hex.2 S rfl y hy)
        (fun _ => by rw [hTe]; exact ⟨rfl, rfl⟩)
    · exact Or.inr hno
  -- the single push at a place the callback's part does not reach
  have hsingle : ∀ l₀ : BoCa.Loc, (∀ ψ, ¬ DeepAt ρc l₀ ψ) →
      OwnPushM δ (.all x c (C' x)) ρc ([], []) (unitEnt l₀ x) β := by
    intro l₀ hl₀
    refine ⟨⟨x, c, C' x, rfl, rfl, hbind, ⟨⟨List.isChain_singleton β, hst, List.not_mem_nil,
      List.not_mem_nil, fun y hy => absurd hy (by simp [unitEnt, VFree])⟩, hl₀⟩, hlt,
      fun A D hCD => ?_⟩, fun y hy => absurd hy (by simp [unitEnt, VFree]), fun h => h⟩
    rw [harr x A D hCD]; trivial
  have hTone : ∀ l₀, ∀ e ∈ [unitEnt l₀ x], e.T = .unit ∧ ∃ u, e.k = .imm u := by
    intro l₀ e he; rw [List.mem_singleton.mp he]; exact ⟨rfl, _, rfl⟩
  have hxone : ∀ l₀, ∀ e ∈ [unitEnt l₀ x], e.x = x := by
    intro l₀ e he; rw [List.mem_singleton.mp he]; rfl
  by_cases hE₁ : AtExactly β φ₁ <;> by_cases hE₂ : AtExactly β φ₂
  · by_cases hl : l₁ = l₂
    · -- one place, exactly at `β`: the single push
      subst hl
      refine ⟨[unitEnt l₁ x], Or.inl ⟨_, rfl, hsingle l₁ fun ψ => hfree l₁ φ₁ ψ hφ₁⟩,
        hrel _ (hxone l₁) (hTone l₁) (fun _ => hE₁) (fun _ => hE₂), hguard _ (by simp) (hTone l₁)
          (fun l ψ h _ => ?_) (fun e he => ?_)⟩
      · rcases hdom l ψ h with rfl | rfl <;> simp [unitEnt]
      · rw [List.mem_singleton.mp he]; exact Or.inl ⟨φ₁, hφ₁, hE₁⟩
    · -- two places, both exactly at `β`: the block push
      have hτT : ∀ e ∈ [unitEnt l₁ x, unitEnt l₂ x], e.T = .unit ∧ ∃ u, e.k = .imm u := by
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨rfl, _, rfl⟩
        · rw [List.mem_singleton.mp he]; exact ⟨rfl, _, rfl⟩
      have hτx : ∀ e ∈ [unitEnt l₁ x, unitEnt l₂ x], e.x = x := by
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · rfl
        · rw [List.mem_singleton.mp he]; rfl
      have hτl : ∀ e ∈ [unitEnt l₁ x, unitEnt l₂ x], e.l = l₁ ∨ e.l = l₂ := by
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact Or.inl rfl
        · rw [List.mem_singleton.mp he]; exact Or.inr rfl
      have hpush : OwnPushB δ (.all x c (C' x)) ρc ([], []) [unitEnt l₁ x, unitEnt l₂ x] β := by
        refine ⟨x, c, C' x, _, rfl, hcb x, hbind, le_refl _, ⟨by simp, hτx, ?_,
          List.isChain_singleton β, hst, List.not_mem_nil, by simp [unitEnt, hl], fun _ _ => List.not_mem_nil,
          fun e he ψ hd => ?_, fun e he y hy => ?_, fun e he hy => ?_⟩, hlt, fun e he y hy => ?_,
          blockFitsReb.1 x _ _ ⟨_, rfl⟩ ⟨_, rfl⟩ rfl rfl⟩
        · intro e he e' he'
          rcases List.mem_cons.mp he with rfl | he <;> rcases List.mem_cons.mp he' with rfl | he' <;>
            simp_all [unitEnt]
        · rcases hτl e he with h | h
          · exact absurd hd (hfree _ φ₁ ψ (h ▸ hφ₁))
          · exact absurd hd (hfree _ φ₂ ψ (h ▸ hφ₂))
        · rw [(hτT e he).1] at hy; exact absurd hy (by simp [VFree])
        · rw [(hτT e he).1] at hy; exact absurd hy (by simp [VFree])
        · rw [(hτT e he).1] at hy; exact absurd hy (by simp [VFree])
      refine ⟨[unitEnt l₁ x, unitEnt l₂ x], Or.inr hpush,
        hrel _ hτx hτT (fun _ => hE₁) (fun _ => hE₂), hguard _ (by simp) hτT
          (fun l ψ h _ => ?_) (fun e he => ?_)⟩
      · rcases hdom l ψ h with rfl | rfl <;> simp [unitEnt]
      · rcases hτl e he with h | h
        · exact Or.inl ⟨φ₁, h ▸ hφ₁, hE₁⟩
        · exact Or.inl ⟨φ₂, h ▸ hφ₂, hE₂⟩
  · -- only the first place exactly at `β`
    have hl : l₁ ≠ l₂ := by
      rintro rfl; rw [hφ₁] at hφ₂; cases hφ₂; exact hE₂ hE₁
    refine ⟨[unitEnt l₁ x], Or.inl ⟨_, rfl, hsingle l₁ fun ψ => hfree l₁ φ₁ ψ hφ₁⟩,
      hrel _ (hxone l₁) (hTone l₁) (fun _ => hE₁) (fun hm => ?_), hguard _ (by simp) (hTone l₁)
        (fun l ψ h hx => ?_) (fun e he => ?_)⟩
    · simp [unitEnt] at hm; exact absurd hm.symm hl
    · rcases hdom l ψ h with rfl | rfl
      · simp [unitEnt]
      · rw [hφ₂] at h; cases h; exact absurd hx hE₂
    · rw [List.mem_singleton.mp he]; exact Or.inl ⟨φ₁, hφ₁, hE₁⟩
  · -- only the second place exactly at `β`
    have hl : l₁ ≠ l₂ := by
      rintro rfl; rw [hφ₁] at hφ₂; cases hφ₂; exact hE₁ hE₂
    refine ⟨[unitEnt l₂ x], Or.inl ⟨_, rfl, hsingle l₂ fun ψ => hfree l₂ φ₂ ψ hφ₂⟩,
      hrel _ (hxone l₂) (hTone l₂) (fun hm => ?_) (fun _ => hE₂), hguard _ (by simp) (hTone l₂)
        (fun l ψ h hx => ?_) (fun e he => ?_)⟩
    · simp [unitEnt] at hm; exact absurd hm hl
    · rcases hdom l ψ h with rfl | rfl
      · rw [hφ₁] at h; cases h; exact absurd hx hE₁
      · simp [unitEnt]
    · rw [List.mem_singleton.mp he]; exact Or.inl ⟨φ₂, hφ₂, hE₂⟩
  · -- no place exactly at `β`: the single push at a free place
    obtain ⟨l₀, hl₀⟩ := hfp ρ
    have hne₁ : l₀ ≠ l₁ := by rintro rfl; exact hl₀ φ₁ (DeepAt.top hρ₁)
    have hne₂ : l₀ ≠ l₂ := by rintro rfl; exact hl₀ φ₂ (DeepAt.top hρ₂)
    refine ⟨[unitEnt l₀ x], Or.inl ⟨_, rfl, hsingle l₀ fun ψ hd => ?_⟩,
      hrel _ (hxone l₀) (hTone l₀) (fun hm => ?_) (fun hm => ?_), hguard _ (by simp) (hTone l₀)
        (fun l ψ h hx => ?_) (fun e he => ?_)⟩
    · obtain ⟨ψ', hd', -⟩ := DeepAt.of_compS_left hc hd
      exact hl₀ ψ' hd'
    · simp [unitEnt] at hm; exact absurd hm.symm hne₁
    · simp [unitEnt] at hm; exact absurd hm.symm hne₂
    · rcases hcellOf l ψ h with rfl | rfl
      · exact absurd hx hE₁
      · exact absurd hx hE₂
    · rw [List.mem_singleton.mp he]; exact Or.inr hl₀

/-- **The block gate at the pair, at both callback shapes**: `withload`'s (thunked) and
`withloadU`'s at the empty row (`.arr`). -/
theorem loadGateNilB_pair (hfp : FreePlaceExists) (B : VTy) :
    LoadGateNilB (ℍ := ℍ) pairTy (loadCbF pairTy B) ∧ LoadGateNilB (ℍ := ℍ) pairTy (loadCbU pairTy B) :=
  ⟨loadGateNilB_pair_of hfp _ (fun _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ h => by cases h),
    loadGateNilB_pair_of hfp _ (fun _ => Or.inl ⟨_, rfl⟩) (fun _ _ _ h => by cases h; rfl)⟩

/-! ### The block gate at an array of `I32` -/

/-- **Core's `Imm` leaf at `I32`, at a reading sending `x` to `β`**: one `imm` cell at the leaf's
place, over an integer and the empty witness, at lifetimes `⊒ β`. -/
theorem vC_imm_i32_leaf {δx : LSub} {x : LifeVar} {β : Life} (hx : δx.find? x = some β)
    {ls : List SRec} {v : Val} {ρ : WRes} (h : vC true (.imm (.var x) (.int .w32)) ls δx v ρ) :
    ∃ (l : BoCa.Loc) (s : LSet) (w : Val) (hs : ResU.InStratum s.join (PMap.empty : WRes)),
      v = .loc l ∧ ρ = ResU.single l (CellU.immOf s w PMap.empty hs) ∧ β ≤ s.meet ∧
        w.IsInt .w32 := by
  obtain ⟨α, hα, l, hsep⟩ := h
  rw [Lifetime.Life.interp_var, hx] at hα
  have hαβ : (α : Life) = β := (Option.some.inj hα).symm
  obtain ⟨⟨rfl, -⟩, s, u, χ, hχ, ls₀, hρ, hP, hle, -⟩ := pure_sep_iff.mp hsep
  rw [hαβ] at hle
  obtain ⟨rfl, hu⟩ := hP
  exact ⟨l, s, u, hχ, rfl, hρ, hle, hu⟩

/-- **A leaf at the pushed stack, at a closed payload**: Core's `Imm` leaf at `S`, its cell exactly
at `β` when an entry lends its place, is `vRLM`'s at a stack of `imm` entries at `S` named `x`,
all at `β`. -/
theorem vRLM_imm_closed_at {τ : LStack} {δ : LSub} {x : LifeVar} {β : Life} {ls : List SRec}
    {S : VTy} (hS : ∀ y, ¬ VFree y S) {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val}
    (hxτ : ∀ e ∈ τ, e.x = x) (hTτ : ∀ e ∈ τ, e.T = S ∧ ∃ u, e.k = .imm u)
    (hv : vC true (.imm (.var x) S) ls (δ.extend x β) (.loc l) (ResU.single l ψ))
    (hex : l ∈ τ.map LEnt.l → AtExactly β ψ) :
    vRLM (ℍ := ℍ) .binder0 none τ (δ.extend x β) (.imm (.var x) S) (blockL τ β) ls (.loc l)
      (ResU.single l ψ) := by
  rw [vRLM]
  refine ⟨?_, fun l' e α hl' hi => ?_, fun l' _ _ y hy => absurd hy (hS y)⟩
  · show vC true (.imm (.var x) S) ls (extS (δ.extend x β) τ (blockL τ β)) (.loc l)
      (ResU.single l ψ)
    rw [vC_congr _ (fun y _ => extS_block_find τ hxτ y)]
    exact hv
  · cases hl'
    obtain ⟨hm, hel⟩ := innerAt_mem hi
    have hα : α = β := snd_of_mem_zip_blockL hm
    have he : e ∈ τ := (List.of_mem_zip hm).1
    obtain ⟨hT, u, hk⟩ := hTτ e he
    refine ⟨by unfold CohKind; rw [hk]; exact ⟨trivial, by rw [hT]; exact TyEq.refl _ _⟩,
      fun ψ' hψ' => ?_⟩
    rw [hel.symm, ResU.single_get_self] at hψ'
    cases hψ'
    rw [hα]
    exact (hex (List.mem_map.mpr ⟨e, he, hel⟩)).1

/-- The entry lending `m` at `'x`: kind `imm`, payload `I32`. -/
def i32Ent (m : BoCa.Loc) (x : LifeVar) : LEnt := ⟨m, x, .int .w32, .imm .unit, fun _ => true⟩

/-- A cell above an `imm` cell over the empty witness is an `imm` cell over it, at the same value. -/
theorem immSub_empty_form {s : LSet} {w : Val} {hs : ResU.InStratum s.join (PMap.empty : WRes)}
    {φ : CellU BoCa.Loc Val} (h : ImmSub (CellU.immOf s w PMap.empty hs) φ) :
    ∃ (S : LSet) (hS : ResU.InStratum S.join (PMap.empty : WRes)),
      φ = CellU.immOf S w PMap.empty hS := by
  rcases h with rfl | ⟨S, S', v, χ, h₀, h', e₀, rfl, -⟩
  · exact ⟨s, hs, rfl⟩
  · obtain ⟨-, rfl, rfl⟩ := CellU.immOf_inj e₀
    exact ⟨S', h', rfl⟩

/-- **The block gate at an array of `I32`** (`GROUND.md` §4.4): `LoadGateNilB` at `array i32`, at a
callback-shaped type whose argument is the array's reborrow `[Imm 'x I32]`, at every length. The
entries lend the places of the range where the reborrow leaves a cell exactly at `β`: two or more
make a block push, one a single push, none a single push at a free place (`FreePlaceExists`). -/
theorem loadGateNilB_array_of (hfp : FreePlaceExists) (C' : LifeVar → CTy)
    (hcb : ∀ x, CbArg (C' x) ((VTy.array (.int .w32)).immReborrow (.var x)))
    (harr : ∀ x A D, C' x = .arr A D → A = (VTy.array (.int .w32)).immReborrow (.var x)) :
    LoadGateNilB (ℍ := ℍ) (VTy.array (.int .w32)) C' := by
  intro δ ls W ℓ₀ u R x c β cb ρc ρ _ _ _ _ hbind _ hreb hv hst _ hlt _ _ hfree hc
  have hxβ := find_extend_self δ x β
  obtain ⟨ℓ, k, hsep⟩ := hv
  obtain ⟨⟨rfl, hk⟩, hrange⟩ := pure_sep_iff.mp hsep
  -- every cell of `cb` is a leaf's: at a place of the range, `imm` over an integer and `∅`
  have hsrc : ∀ m ψ, cb.get m = some ψ → (∃ i, i < k.toNat ∧ m = ℓ + i) ∧
      ∃ (S : LSet) (w : Val) (hS : ResU.InStratum S.join (PMap.empty : WRes)),
        ψ = CellU.immOf S w PMap.empty hS ∧ w.IsInt .w32 := by
    intro m ψ hg
    obtain ⟨i, hi, ρi, ψi, hP, hgi, t, ht⟩ := sepRange_get hrange hg
    obtain ⟨l', s', w', hs', hl', rfl, -, hw'⟩ := vC_imm_i32_leaf hxβ hP
    cases hl'
    have hm : m = ℓ + i := by
      by_contra hne
      rw [ResU.single_get_ne _ hne] at hgi; cases hgi
    subst hm
    rw [ResU.single_get_self] at hgi; cases hgi
    obtain ⟨ψ', hψ', hsub⟩ := top_of_compS_left ht (ResU.single_get_self _ _)
    rw [hg] at hψ'; cases hψ'
    obtain ⟨S, hS, rfl⟩ := immSub_empty_form hsub
    exact ⟨⟨i, hi, rfl⟩, S, w', hS, rfl, hw'⟩
  have hwit : ∀ m ψ, cb.get m = some ψ → ψ.wit = PMap.empty := by
    intro m ψ hg
    obtain ⟨-, S, w, hS, rfl, -⟩ := hsrc m ψ hg
    exact CellU.wit_immOf _ _ _ _
  have hcells : ∀ l ψ, cb.get l = some ψ → AtExactly β ψ ∨ ψ.InStratum β :=
    fun l ψ h => reb_exact_or_above hreb h
  -- every place of the range holds a cell of `cb`, and of the composite
  have hhas : ∀ i, i < k.toNat → ∃ ψ, cb.get (ℓ + i) = some ψ := by
    intro i hi
    obtain ⟨ρi, hP, t, ht⟩ := sepRange_le hi hrange
    obtain ⟨l', s', w', hs', hl', rfl, -, -⟩ := vC_imm_i32_leaf hxβ hP
    cases hl'
    obtain ⟨ψ', hψ', -⟩ := top_of_compS_left ht (ResU.single_get_self _ _)
    exact ⟨ψ', hψ'⟩
  have hρhas : ∀ m ψ, cb.get m = some ψ → ρ.get m = some ψ := by
    intro m ψ hg
    rcases get_of_free hc hfree m with ⟨ψ', h, -, hr⟩ | ⟨h, -⟩
    · rw [hg] at h; cases h; exact hr
    · rw [hg] at h; cases h
  let E : BoCa.Loc → Prop := fun m => ∃ ψ, cb.get m = some ψ ∧ AtExactly β ψ
  -- the relation at a stack of `imm` entries at `I32` named `x`, its places exact or unreached
  have hrel : ∀ τ : LStack, (∀ e ∈ τ, e.x = x) →
      (∀ e ∈ τ, e.T = .int .w32 ∧ ∃ u, e.k = .imm u) →
      (∀ m ∈ τ.map LEnt.l, E m ∨ ∀ ψ, ¬ DeepAt ρ m ψ) →
      vRLM (ℍ := ℍ) .binder0 none τ (δ.extend x β)
        ((VTy.array (.int .w32)).immReborrow (.var x)) (blockL τ β) ls (Val.arr ℓ k) cb := by
    intro τ hx hT hτm
    show vRLM (ℍ := ℍ) .binder0 none τ (δ.extend x β) (.fam (.imm (.var x) (.int .w32)))
      (blockL τ β) ls _ cb
    rw [vRLM]
    refine ⟨ℓ, k, pure_sep_mk ⟨rfl, hk⟩ ?_⟩
    refine sepRange_mono_down (R := fun a => ResU.Le a cb)
      (fun a₁ a₂ a hc' ha => ⟨ResU.Le.trans ⟨a₂, hc'⟩ ha,
        ResU.Le.trans ⟨a₁, ResU.CompS.comm hc'⟩ ha⟩)
      (fun m σ hle hP => ?_) (ResU.Le.refl cb) hrange
    obtain ⟨l', s', w', hs', hl', rfl, -, -⟩ := vC_imm_i32_leaf hxβ hP
    cases hl'
    refine vRLM_imm_closed_at (fun y => by simp [VFree]) hx hT hP (fun hm => ?_)
    obtain ⟨t, ht⟩ := hle
    obtain ⟨ψ', hψ', hsub⟩ := top_of_compS_left ht (ResU.single_get_self _ _)
    rcases hτm m hm with ⟨ψ, hψ, hex⟩ | hno
    · rw [hψ] at hψ'; cases hψ'
      exact hex.of_immSub hsub
    · exact absurd (DeepAt.top (hρhas m ψ' hψ')) (hno ψ')
  -- the guard at such a stack
  have hguard : ∀ τ : LStack, τ ≠ [] → (∀ e ∈ τ, e.T = .int .w32 ∧ ∃ u, e.k = .imm u) →
      (∀ l ψ, cb.get l = some ψ → AtExactly β ψ → l ∈ τ.map LEnt.l) →
      (∀ e ∈ τ, E e.l ∨ ∀ ψ, ¬ DeepAt ρ e.l ψ) →
      TabAtS τ (blockL τ β) ρ ∧
        PlaceViewsL (extS (δ.extend x β) τ (blockL τ β)) τ (blockL τ β) ls ρ := by
    intro τ hne hT hlent hent
    refine gate_guard hne hst hfree hc hcells hwit hlent (fun e he => ?_)
    rcases hent e he with ⟨ψ, hψ, hex⟩ | hno
    · refine Or.inl ⟨ψ, hψ, ?_⟩
      obtain ⟨-, S, w, hS, rfl, hw⟩ := hsrc e.l ψ hψ
      obtain ⟨hTe, u₀, hk'⟩ := hT e he
      exact vwEW_of_exact hk' (fun y hy => hex.2 S rfl y hy)
        (fun _ => by rw [hTe]; exact ⟨rfl, hw⟩)
    · exact Or.inr hno
  have hsingle : ∀ e : LEnt, e.x = x → e.T = .int .w32 → (∀ ψ, ¬ DeepAt ρc e.l ψ) →
      OwnPushM δ (.all x c (C' x)) ρc ([], []) e β := by
    intro e hex hT hl₀
    refine ⟨⟨x, c, C' x, rfl, hex, hbind, ⟨⟨List.isChain_singleton β, hst, List.not_mem_nil,
      List.not_mem_nil, fun y hy => absurd hy (by rw [hT]; simp [VFree])⟩, hl₀⟩, hlt,
      fun A D hCD => ?_⟩, fun y hy => absurd hy (by rw [hT]; simp [VFree]),
      by rw [hT]; simp [VFree]⟩
    rw [harr x A D hCD]; trivial
  -- the exact places of the range, in order
  let places : List BoCa.Loc := ((List.range k.toNat).map fun i => ℓ + i).filter
    fun m => @decide (E m) (Classical.propDecidable _)
  have hplaces : ∀ m, m ∈ places ↔ (∃ i, i < k.toNat ∧ m = ℓ + i) ∧ E m := by
    intro m
    simp only [places, List.mem_filter, List.mem_map, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨i, hi, rfl⟩, hE⟩; exact ⟨⟨i, hi, rfl⟩, hE⟩
    · rintro ⟨⟨i, hi, rfl⟩, hE⟩; exact ⟨⟨i, hi, rfl⟩, hE⟩
  have hnodup : places.Nodup := by
    refine List.Nodup.filter _ ((List.nodup_range).map ?_)
    intro i j h; exact Nat.add_left_cancel h
  have hmapl : ∀ ps : List BoCa.Loc, (ps.map fun m => i32Ent m x).map LEnt.l = ps := by
    intro ps
    induction ps with
    | nil => rfl
    | cons a t ih => simp only [List.map_cons, ih]; rfl
  have hτl : (places.map fun m => i32Ent m x).map LEnt.l = places := hmapl places
  have hτx : ∀ e ∈ places.map (fun m => i32Ent m x), e.x = x := by
    intro e he; obtain ⟨m, -, rfl⟩ := List.mem_map.mp he; rfl
  have hτT : ∀ e ∈ places.map (fun m => i32Ent m x), e.T = .int .w32 ∧ ∃ u, e.k = .imm u := by
    intro e he; obtain ⟨m, -, rfl⟩ := List.mem_map.mp he; exact ⟨rfl, _, rfl⟩
  have hτE : ∀ e ∈ places.map (fun m => i32Ent m x), E e.l := by
    intro e he; obtain ⟨m, hm, rfl⟩ := List.mem_map.mp he; exact ((hplaces m).mp hm).2
  have hlent : ∀ l ψ, cb.get l = some ψ → AtExactly β ψ →
      l ∈ (places.map fun m => i32Ent m x).map LEnt.l := by
    intro l ψ h hx
    rw [hτl, hplaces]
    exact ⟨(hsrc l ψ h).1, ψ, h, hx⟩
  have hrelτ := hrel (places.map fun m => i32Ent m x) hτx hτT (fun m hm => by
    rw [hτl] at hm; exact Or.inl ((hplaces m).mp hm).2)
  have hnodupτ : ((places.map fun m => i32Ent m x).map LEnt.l).Nodup := by rw [hτl]; exact hnodup
  have hτc : ∀ e ∈ places.map (fun m => i32Ent m x), e.cross = fun _ => true := by
    intro e he; obtain ⟨m, -, rfl⟩ := List.mem_map.mp he; rfl
  generalize (places.map fun m => i32Ent m x) = τ at hτl hτx hτT hτE hlent hrelτ hnodupτ hτc
  rcases τ with _ | ⟨e₁, _ | ⟨e₂, rest⟩⟩
  · -- no place exactly at `β`: the single push at a free place
    obtain ⟨l₀, hl₀⟩ := hfp ρ
    have hnot : ∀ ψ, ¬ DeepAt ρc l₀ ψ := fun ψ hd => by
      obtain ⟨ψ', hd', -⟩ := DeepAt.of_compS_left hc hd
      exact hl₀ ψ' hd'
    have hx₀ : ∀ e ∈ [i32Ent l₀ x], e.x = x := fun e he => by
      rw [List.mem_singleton.mp he]; rfl
    have hT₀ : ∀ e ∈ [i32Ent l₀ x], e.T = .int .w32 ∧ ∃ u, e.k = .imm u := fun e he => by
      rw [List.mem_singleton.mp he]; exact ⟨rfl, _, rfl⟩
    have hm₀ : ∀ m ∈ [i32Ent l₀ x].map LEnt.l, E m ∨ ∀ ψ, ¬ DeepAt ρ m ψ := fun m hm => by
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hm
      subst hm; exact Or.inr hl₀
    have hlent₀ : ∀ l ψ, cb.get l = some ψ → AtExactly β ψ → l ∈ [i32Ent l₀ x].map LEnt.l :=
      fun l ψ h hx => absurd (hlent l ψ h hx) List.not_mem_nil
    have hent₀ : ∀ e ∈ [i32Ent l₀ x], E e.l ∨ ∀ ψ, ¬ DeepAt ρ e.l ψ := fun e he => by
      rw [List.mem_singleton.mp he]; exact Or.inr hl₀
    exact ⟨[i32Ent l₀ x], Or.inl ⟨_, rfl, hsingle _ rfl rfl hnot⟩, hrel _ hx₀ hT₀ hm₀,
      hguard _ (List.cons_ne_nil _ _) hT₀ hlent₀ hent₀⟩
  · -- one place exactly at `β`: the single push
    have he₁ : e₁ ∈ [e₁] := List.mem_singleton_self e₁
    obtain ⟨ψ, hψ, -⟩ := hτE e₁ he₁
    exact ⟨[e₁], Or.inl ⟨e₁, rfl, hsingle e₁ (hτx e₁ he₁) (hτT e₁ he₁).1
      (fun ψ' => hfree e₁.l ψ ψ' hψ)⟩, hrelτ,
      hguard _ (List.cons_ne_nil _ _) hτT hlent (fun e he => Or.inl (hτE e he))⟩
  · -- two or more places exactly at `β`: the block push
    have hpush : OwnPushB δ (.all x c (C' x)) ρc ([], []) (e₁ :: e₂ :: rest) β := by
      refine ⟨x, c, C' x, _, rfl, hcb x, hbind, by simp, ⟨List.cons_ne_nil _ _, hτx,
        fun e he e' he' => ?_, List.isChain_singleton β, hst, List.not_mem_nil, hnodupτ,
        fun _ _ => List.not_mem_nil, fun e he ψ hd => ?_, fun e he y hy => ?_,
        fun e he hy => ?_⟩, hlt, fun e he y hy => ?_,
        blockFitsReb.2 x _ fun e he => ⟨(hτT e he).2, (hτT e he).1⟩⟩
      · rw [hτc e he, hτc e' he']
      · exact absurd hd (hfree _ (hτE e he).choose ψ (hτE e he).choose_spec.1)
      · rw [(hτT e he).1] at hy; exact absurd hy (by simp [VFree])
      · rw [(hτT e he).1] at hy; exact absurd hy (by simp [VFree])
      · rw [(hτT e he).1] at hy; exact absurd hy (by simp [VFree])
    exact ⟨_, Or.inr hpush, hrelτ, hguard _ (List.cons_ne_nil _ _) hτT hlent
      (fun e he => Or.inl (hτE e he))⟩

/-- **The block gate at an array of `I32`, at both callback shapes.** -/
theorem loadGateNilB_array (hfp : FreePlaceExists) (B : VTy) :
    LoadGateNilB (ℍ := ℍ) (VTy.array (.int .w32)) (loadCbF (VTy.array (.int .w32)) B) ∧
      LoadGateNilB (ℍ := ℍ) (VTy.array (.int .w32)) (loadCbU (VTy.array (.int .w32)) B) :=
  ⟨loadGateNilB_array_of hfp _ (fun _ => Or.inr ⟨_, rfl⟩) (fun _ _ _ h => by cases h),
    loadGateNilB_array_of hfp _ (fun _ => Or.inl ⟨_, rfl⟩) (fun _ _ _ h => by cases h; rfl)⟩

/-! ### A free place at every depth

`Res` is finite at every depth (`PMap.finite`, the stratification of `Cell`). A witness of a cell
in `Res_α` is in a stratum strictly inside `α` (`Res.toU_inStratum`), so the places a resource
holds at every depth lie in one list, and a place outside it is free (`loc_infinite`). -/

/-- The places a resource holds at every depth lie in one list. -/
def DeepFin (ρ : WRes) : Prop := ∃ d : List BoCa.Loc, ∀ l ψ, DeepAt ρ l ψ → l ∈ d

theorem deepFin_empty : DeepFin (PMap.empty : WRes) :=
  ⟨[], fun l ψ h => absurd h (empty_not_deepAt l ψ)⟩

/-- **A resource whose cells' witnesses are `DeepFin` is `DeepFin`**: its own places are finite
(`PMap.finite`), and each of them adds its witness's list. -/
theorem deepFin_of_wits (ρ : WRes) (hw : ∀ m φ, ρ.get m = some φ → DeepFin φ.wit) :
    DeepFin ρ := by
  obtain ⟨d₀, hd₀⟩ := ρ.finite
  have key : ∀ L : List BoCa.Loc, ∃ d : List BoCa.Loc, ∀ m ∈ L, ∀ φ, ρ.get m = some φ →
      ∀ l ψ, DeepAt φ.wit l ψ → l ∈ d := by
    intro L
    induction L with
    | nil => exact ⟨[], fun m hm => absurd hm List.not_mem_nil⟩
    | cons m L ih =>
        obtain ⟨d, hd⟩ := ih
        cases hm : ρ.get m with
        | none =>
            refine ⟨d, fun m' hm' φ hφ l ψ h => ?_⟩
            rcases List.mem_cons.mp hm' with rfl | hm'
            · rw [hm] at hφ; cases hφ
            · exact hd m' hm' φ hφ l ψ h
        | some φ₀ =>
            obtain ⟨d', hd'⟩ := hw m φ₀ hm
            refine ⟨d' ++ d, fun m' hm' φ hφ l ψ h => ?_⟩
            rcases List.mem_cons.mp hm' with rfl | hm'
            · rw [hm] at hφ
              cases hφ
              exact List.mem_append_left _ (hd' l ψ h)
            · exact List.mem_append_right _ (hd m' hm' φ hφ l ψ h)
  obtain ⟨d, hd⟩ := key d₀
  refine ⟨d₀ ++ d, fun l ψ h => ?_⟩
  cases h with
  | top e => exact List.mem_append_left _ (hd₀ l (by rw [e]; simp))
  | wit e hdeep => exact List.mem_append_right _ (hd _ (hd₀ _ (by rw [e]; simp)) _ e l ψ hdeep)

/-- **A resource in a stratum is `DeepFin`**, by induction on the stratum: a witness of one of its
cells is in a stratum strictly inside it. -/
theorem deepFin_of_inStratum : ∀ (n : ℕ) (ρ : WRes), ρ.InStratum (OrderDual.toDual n) →
    DeepFin ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro ρ hρ
      refine deepFin_of_wits ρ fun m φ hφ => ?_
      have hs := hρ m φ hφ
      cases φ with
      | own v => exact deepFin_empty
      | imm i =>
          have hlt : OrderDual.ofDual i.ls.join < n := by
            have h₁ : OrderDual.toDual n < i.ls.join := lt_of_lt_of_le hs i.ls.meet_le_join
            exact OrderDual.toDual_lt.mp h₁
          exact ih _ hlt i.res (Res.toU_inStratum i.ρ)
      | «mut» mm =>
          have hlt : OrderDual.ofDual mm.β < n := OrderDual.toDual_lt.mp hs
          exact ih _ hlt mm.res (Res.toU_inStratum mm.ρ)

/-- **Every resource is `DeepFin`**: each cell's witness is in the cell's own stratum. -/
theorem deepFin (ρ : WRes) : DeepFin ρ := by
  refine deepFin_of_wits ρ fun m φ _ => ?_
  cases φ with
  | own v => exact deepFin_empty
  | imm i => exact deepFin_of_inStratum _ i.res (Res.toU_inStratum i.ρ)
  | «mut» mm => exact deepFin_of_inStratum _ mm.res (Res.toU_inStratum mm.ρ)

/-- **`FreePlaceExists`**: a place outside the resource's list at every depth. -/
theorem freePlaceExists : FreePlaceExists := by
  intro ρ
  obtain ⟨d, hd⟩ := deepFin ρ
  obtain ⟨l, hl⟩ := loc_infinite d
  exact ⟨l, fun ψ h => hl (hd l ψ h)⟩

/-- **The block gate at the pair**, both callback shapes. -/
theorem loadGateNilB_pairTy (B : VTy) :
    LoadGateNilB (ℍ := ℍ) pairTy (loadCbF pairTy B) ∧
      LoadGateNilB (ℍ := ℍ) pairTy (loadCbU pairTy B) :=
  loadGateNilB_pair freePlaceExists B

/-- **The block gate at an array of `I32`**, both callback shapes, every length. -/
theorem loadGateNilB_arrayI32 (B : VTy) :
    LoadGateNilB (ℍ := ℍ) (VTy.array (.int .w32)) (loadCbF (VTy.array (.int .w32)) B) ∧
      LoadGateNilB (ℍ := ℍ) (VTy.array (.int .w32)) (loadCbU (VTy.array (.int .w32)) B) :=
  loadGateNilB_array freePlaceExists B

end ProbeD1

end

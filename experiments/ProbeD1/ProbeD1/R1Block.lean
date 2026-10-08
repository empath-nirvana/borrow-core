import ProbeD1.R1

/-!
# ProbeD1 — the block push's facts the relation's rows read (`GROUND.md` §4.4, §4.5)

* **The stack's shape**: `StackOK` is `StackOKB` with no block (`stackOKB_of_ok`); an
  instantiation keeps `StackOKB` (`instStackOKB`); at distinct variables `StackJBase` and `StackJB`
  are `StackJ` and `StackJM` (`stackJBaseIff`), and the old forms give the new
  (`stackJBase_of_stackJ`, `stackJB_of_stackJM`).
* **`StackJBase` and `StackJB` along the rows**: an instantiation keeps `StackJBase`
  (`stackJBaseInst`); at a type that is no lifetime `∀` its entries are of the first two kinds,
  and `StackJB` follows (`stackJB_of_notAll`, `stackJB_of_kinds`, `stackJBase_body`).
* **`GuardInstB`**: the table and the guard's views at an instantiated stack, blocks admitted. The
  table is read directly at the instantiated lifetimes, not through `ReLend`'s strict chain,
  which an instantiation of a block does not keep (`guardInst`'s route, `instReLend`, reads it).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS jdgCty)

/-! ### The stack's shape -/

/-- Two members of a zip whose first components' images are distinct are equal when their images
agree. -/
theorem zip_eq_of_fst {σ : LStack} {αs : List Life} (hl : αs.length = σ.length)
    (hn : (σ.map LEnt.x).Nodup) {p q : LEnt × Life} (hp : p ∈ σ.zip αs) (hq : q ∈ σ.zip αs)
    (h : p.1.x = q.1.x) : p = q := by
  have hm : (σ.zip αs).map (fun p => p.1.x) = σ.map LEnt.x := by
    rw [show (fun p : LEnt × Life => p.1.x) = LEnt.x ∘ Prod.fst from rfl, ← List.map_map,
      List.map_fst_zip (le_of_eq hl.symm)]
  exact List.inj_on_of_nodup_map (f := fun p : LEnt × Life => p.1.x) (by rw [hm]; exact hn) hp hq h

/-- Two members of a zip whose second components are distinct are equal when those agree. -/
theorem zip_eq_of_snd {σ : LStack} {αs : List Life} (hl : αs.length = σ.length)
    (hn : αs.Nodup) {p q : LEnt × Life} (hp : p ∈ σ.zip αs) (hq : q ∈ σ.zip αs)
    (h : p.2 = q.2) : p = q := by
  have hm : (σ.zip αs).map Prod.snd = αs := List.map_snd_zip (le_of_eq hl)
  exact List.inj_on_of_nodup_map (f := Prod.snd) (by rw [hm]; exact hn) hp hq h

/-- A strict chain has no repeated lifetime. -/
theorem nodup_of_chain_lt {αs : List Life} (h : List.IsChain (· < ·) αs) : αs.Nodup :=
  (List.IsChain.pairwise h).imp fun hab => ne_of_lt hab

/-- **`StackOK` is `StackOKB` with no block.** -/
def StackOKBOfOK : Prop := ∀ (σ : LStack) (αs : List Life), StackOK σ αs → StackOKB σ αs

theorem stackOKB_of_ok : StackOKBOfOK := by
  intro σ αs ⟨hl, hc, hn⟩
  have hna : αs.Nodup := nodup_of_chain_lt hc
  refine ⟨hl, hc.imp fun _ _ h => le_of_lt h, fun p hp q hq => ⟨fun h => ?_, fun h => ?_⟩,
    fun p hp q hq h => ?_⟩
  · rw [zip_eq_of_fst hl hn hp hq h]
  · rw [zip_eq_of_snd hl hna hp hq h]
  · rw [zip_eq_of_snd hl hna hp hq h]

/-- **An instantiation keeps `StackOKB`**: it maps the lifetimes by a strictly monotone map. -/
def InstStackOKB : Prop :=
  ∀ (σ : LStack) (αs : List Life) (ι : Inst), InstAt αs ι → StackOKB σ αs → StackOKB σ (ι.life αs)

theorem instStackOKB : InstStackOKB := by
  intro σ αs ι _ ⟨hl, hc, hx, hr⟩
  have hm := ι.life1_strictMono
  refine ⟨by simp [Inst.life, hl], ?_, fun p hp q hq => ?_, fun p hp q hq h => ?_⟩
  · exact (List.isChain_map ι.life1).mpr (hc.imp fun _ _ h => hm.monotone h)
  · rw [Inst.life, List.zip_map_right, List.mem_map] at hp hq
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    simp only [Prod.map_fst, Prod.map_snd, id]
    rw [hx p₀ hp₀ q₀ hq₀]
    exact ⟨fun h => h ▸ rfl, fun h => hm.injective h⟩
  · rw [Inst.life, List.zip_map_right, List.mem_map] at hp hq
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    exact hr p₀ hp₀ q₀ hq₀ (hm.injective h)

/-- **At distinct variables the block forms are the old ones.** -/
def StackJBaseIff : Prop :=
  ∀ (σ : LStack) (αs : List Life) (δ : LSub) (Δ : LifeCtx) (Γ : Ctx VTy) (C : CTy),
    (σ.map LEnt.x).Nodup →
      ((StackJBase σ αs δ Δ Γ C ↔ StackJ σ αs δ Δ Γ C) ∧
        (StackJB σ αs δ Δ Γ C ↔ StackJM σ αs δ Δ Γ C))

/-- At distinct variables the head names a member exactly when it is that member. -/
theorem head_map_x_iff {σ : LStack} (hn : (σ.map LEnt.x).Nodup) {e : LEnt} (he : e ∈ σ) :
    σ.head?.map LEnt.x = some e.x ↔ σ.head? = some e := by
  constructor
  · intro h
    obtain ⟨h₀, hh, hx⟩ := Option.map_eq_some_iff.mp h
    have hm : h₀ ∈ σ := List.mem_of_mem_head? hh
    rw [List.inj_on_of_nodup_map hn hm he hx] at hh
    exact hh
  · intro h; rw [h]; rfl

theorem stackJBaseIff : StackJBaseIff := by
  intro σ αs δ Δ Γ C hn
  have hbase : StackJBase σ αs δ Δ Γ C ↔ StackJ σ αs δ Δ Γ C := by
    constructor
    · rintro ⟨hp, hk⟩
      refine ⟨hn, hp, fun e he => ?_⟩
      rcases hk e he with h | h | ⟨h₁, h₂, h₃⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h₁, (head_map_x_iff hn he).mp h₂, h₃⟩)
    · rintro ⟨-, hp, hk⟩
      refine ⟨hp, fun e he => ?_⟩
      rcases hk e he with h | h | ⟨h₁, h₂, h₃⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h₁, (head_map_x_iff hn he).mpr h₂, h₃⟩)
  refine ⟨hbase, ?_⟩
  constructor
  · rintro ⟨hb, hx⟩
    exact ⟨hbase.mp hb, fun e he h₁ h₂ h₃ => hx e he h₁ ((head_map_x_iff hn he).mpr h₂) h₃⟩
  · rintro ⟨hj, hx⟩
    exact ⟨hbase.mpr hj, fun e he h₁ h₂ h₃ => hx e he h₁ ((head_map_x_iff hn he).mp h₂) h₃⟩


/-- The old form gives the block form. -/
theorem stackJBase_of_stackJ {σ : LStack} {αs : List Life} {δ : LSub} {Δ : LifeCtx}
    {Γ : Ctx VTy} {C : CTy} (h : StackJ σ αs δ Δ Γ C) : StackJBase σ αs δ Δ Γ C :=
  ((stackJBaseIff σ αs δ Δ Γ C h.1).1).mpr h

theorem stackJB_of_stackJM {σ : LStack} {αs : List Life} {δ : LSub} {Δ : LifeCtx}
    {Γ : Ctx VTy} {C : CTy} (h : StackJM σ αs δ Δ Γ C) : StackJB σ αs δ Δ Γ C :=
  ((stackJBaseIff σ αs δ Δ Γ C h.1.1).2).mpr h

/-- `(e, α)` is a member of a block's zip with its lifetimes. -/
theorem mem_zip_blockL {τ : LStack} {e : LEnt} (he : e ∈ τ) (α : Life) :
    (e, α) ∈ τ.zip (blockL τ α) := by
  induction τ with
  | nil => exact absurd he List.not_mem_nil
  | cons e₀ τ ih =>
      rcases List.mem_cons.mp he with rfl | he
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih he)

/-- A member of a block's zip is at the block's lifetime. -/
theorem snd_of_mem_zip_blockL {τ : LStack} {α : Life} {p : LEnt × Life}
    (h : p ∈ τ.zip (blockL τ α)) : p.2 = α := by
  induction τ with
  | nil => exact absurd h List.not_mem_nil
  | cons e₀ τ ih =>
      rcases List.mem_cons.mp h with rfl | h
      · rfl
      · exact ih h

/-! ### `StackJBase` and `StackJB` along the rows -/

/-- **An instantiation keeps `StackJBase`**: `stackJInst`'s proof. -/
theorem stackJBaseInst {σ : LStack} {αs : List Life} {δ : LSub} {Δ : LifeCtx} {Γ : Ctx VTy}
    {C : CTy} (ι : Inst) (h : StackJBase σ αs δ Δ Γ C) :
    StackJBase σ (ι.life αs) (ι.sub δ) Δ Γ C := by
  obtain ⟨hp, hk⟩ := h
  refine ⟨hp, fun e he => ?_⟩
  rcases hk e he with h₁ | h₂ | ⟨h₃, hhd, hfr, c, C', hC, hb, hlt⟩
  · exact Or.inl h₁
  · exact Or.inr (Or.inl h₂)
  · refine Or.inr (Or.inr ⟨h₃, hhd, hfr, c, C', hC, hb, fun a' ha' => ?_⟩)
    rw [Inst.life_head?] at ha'
    obtain ⟨a, ha, rfl⟩ := Option.mem_map.mp ha'
    rw [extS_inst]
    exact (ι.ltLife_sub_iff _ c a).mpr (hlt a ha)

/-- **`StackJB` at a type that is no lifetime `∀`**: its added conjunct reads an outermost `∀`. -/
theorem stackJB_of_notAll {σ : LStack} {αs : List Life} {δ : LSub} {Δ : LifeCtx} {Γ : Ctx VTy}
    {C : CTy} (hJ : StackJBase σ αs δ Δ Γ C) (hC : ∀ x c D, C ≠ .all x c D) :
    StackJB σ αs δ Δ Γ C :=
  ⟨hJ, fun _ _ _ _ ⟨_, _, h⟩ => absurd h (hC _ _ _)⟩

/-- **`StackJB` where every entry is of the first two kinds**: an entry of the second kind is a
name no program binds, so under `BindersLow` no `∀` of the type binds it. -/
theorem stackJB_of_kinds {σ : LStack} {αs : List Life} {δ : LSub} {Δ : LifeCtx} {Γ : Ctx VTy}
    {C : CTy} (hJ : StackJBase σ αs δ Δ Γ C) (hBL : BindersLow Γ C)
    (hk : ∀ e ∈ σ, (∃ u, Δ.find? e.x = some u) ∨ NsVar e.x) : StackJB σ αs δ Δ Γ C := by
  refine ⟨hJ, fun e he hΔ _ ⟨c, C', hC⟩ => ?_⟩
  exfalso
  rcases hk e he with ⟨u, hu⟩ | hns
  · rw [hΔ] at hu; cases hu
  · exact hBL.1 e.x (by rw [hC]; exact List.mem_cons_self ..) hns

/-- At a type that is no lifetime `∀`, every entry `StackJBase` admits is of the first two kinds. -/
theorem stackJBase_kinds_of_notAll {σ : LStack} {αs : List Life} {δ : LSub} {Δ : LifeCtx}
    {Γ : Ctx VTy} {C : CTy} (hJ : StackJBase σ αs δ Δ Γ C) (hC : ∀ x c D, C ≠ .all x c D) :
    ∀ e ∈ σ, (∃ u, Δ.find? e.x = some u) ∨ NsVar e.x := by
  intro e he
  rcases hJ.2 e he with h | ⟨hns, -⟩ | ⟨-, -, -, c, D, hall, -⟩
  · exact Or.inl h
  · exact Or.inr hns
  · exact absurd hall (hC _ _ _)

/-- **`StackJBase` at a body**: `stackJ_body`'s proof. -/
theorem stackJBase_body {σ : LStack} {αs αs' : List Life} {δ : LSub} {Δ : LifeCtx}
    {Γ Γ' : Ctx VTy} {C C' : CTy} (h : StackJBase σ αs δ Δ Γ C) (hC : ∀ x c D, C ≠ .all x c D)
    (hfree : ∀ x, ¬ CFree x C → ¬ CFree x C') (hΓ : ∀ x, CtxAvoids x Γ → CtxAvoids x Γ') :
    StackJBase σ αs' δ Δ Γ' C' := by
  obtain ⟨hp, hk⟩ := h
  refine ⟨hp, fun e he => ?_⟩
  rcases hk e he with h₁ | ⟨hns, hΔ, hCe, hctx⟩ | ⟨-, -, -, c, D, hall, -⟩
  · exact Or.inl h₁
  · exact Or.inr (Or.inl ⟨hns, hΔ, hfree _ hCe, hΓ _ hctx⟩)
  · exact absurd hall (hC _ _ _)

/-! ### The table and the guard's views at an instantiation, blocks admitted -/

/-- In a non-decreasing chain the head is below every member. -/
theorem head_le_of_chain_le {αs : List Life} (hc : List.IsChain (· ≤ ·) αs) {a b : Life}
    (ha : a ∈ αs.head?) (hb : b ∈ αs) : a ≤ b := by
  cases αs with
  | nil => exact absurd ha (by simp)
  | cons a₀ αs₀ =>
      have ha' : a = a₀ := by simpa using ha.symm
      subst ha'
      rcases List.mem_cons.mp hb with rfl | hb
      · exact le_rfl
      · exact (List.rel_of_pairwise_cons (List.IsChain.pairwise hc) hb)

/-- In a non-decreasing chain every member is below the last. -/
theorem le_last_of_chain_le {αs : List Life} (hc : List.IsChain (· ≤ ·) αs) {a o : Life}
    (ha : a ∈ αs) (ho : αs.getLast? = some o) : a ≤ o := by
  have hp := List.IsChain.pairwise hc
  have hmo : o ∈ αs := List.mem_of_getLast? ho
  obtain ⟨l, hl⟩ : ∃ l, αs = l ++ [o] := by
    obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.mp ho
    exact ⟨l, hl⟩
  rw [hl] at ha hp
  rcases List.mem_append.mp ha with ha | ha
  · exact (List.pairwise_append.mp hp).2.2 a ha o (List.mem_singleton_self o)
  · rw [List.mem_singleton.mp ha]

/-- **A part above the outermost lend holds no borrow cell at a bound place**, blocks admitted:
`no_bound_of_stratS` at a non-decreasing chain. -/
theorem no_bound_of_stratS_le {s : LSub} {σ : LStack} {αs : List Life} {ls : List SRec}
    (hc : List.IsChain (· ≤ ·) αs) {ρz ρn ρ : WRes} (hcomp : ResU.CompS ρz ρn ρ)
    (hz : stratS αs ρz) (h : PlaceViewsL s σ αs ls ρ) {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val}
    (hd : DeepAt ρz l ψ) (ho : ψ.kind ≠ Kind.own) (hl : l ∈ σ.map LEnt.l) : False := by
  obtain ⟨ψ', hd', hs⟩ := DeepAt.of_compS_left hcomp hd
  obtain ⟨e, α, hm, hel, hv⟩ := h.2 l ψ' hd' (hs.kind ▸ ho) hl
  have hex : AtExactly α ψ := (vwEW_atExactly hel hv).of_immSub hs
  have hα : α ∈ αs := (List.of_mem_zip hm).2
  cases ho' : αs.getLast? with
  | none => rw [List.getLast?_eq_none_iff] at ho'; subst ho'; exact absurd hα List.not_mem_nil
  | some o =>
      have hαo : α ≤ o := le_last_of_chain_le hc hα ho'
      have hin : ψ.InStratum o := DeepAt.inStratum (hz o ho') hd
      have hat : o < ψ.at := by
        cases ψ with
        | own v => exact absurd rfl ho
        | imm i => exact hin
        | «mut» m => exact hin
      rw [hex.1] at hat
      exact absurd (lt_of_lt_of_le hat hαo) (lt_irrefl _)

/-- **The table and the guard's views at an instantiation, blocks admitted** (`GuardInst` at
`StackOKB`). The table is read at the instantiated lifetimes directly: the share lies above the
outermost lend, which is at or above every lend and is moved no longer; the views lie at the
stack's places, each at an instantiated lend lifetime, at or above the instantiated innermost
one. -/
def GuardInstB : Prop :=
  ∀ (δ : LSub) (σ : LStack) (ds : List Bool) (αs : List Life) (ls ls' : List SRec)
    (ρz ρn ρ ρv R : WRes) (ι : Inst),
    StackOKB σ αs → InstAt αs ι → stratS αs ρz → vwSL (extS δ σ αs) σ ds αs ls ρn →
    ResU.CompS ρz ρn ρ → PlaceViewsL (extS δ σ αs) σ αs ls ρ →
    vwSL (extS (ι.sub δ) σ (ι.life αs)) σ ds (ι.life αs) ls' ρv → ResU.CompS ρz ρv R →
    TabAtS σ (ι.life αs) R ∧ PlaceViewsL (extS (ι.sub δ) σ (ι.life αs)) σ (ι.life αs) ls' R

theorem guardInstB : GuardInstB := by
  intro δ σ ds αs ls ls' ρz ρn ρ ρv R ι hok _ hz _ hcomp h hv hcv
  refine ⟨⟨fun a ha => ?_, fun a ha k ψ hk e => ?_⟩,
    placeViewsL_join hcv
      (placeViewsL_of_noBound fun l ψ hd ho hl => no_bound_of_stratS_le hok.2.1 hcomp hz h hd ho hl)
      hv.2⟩
  · rw [Inst.life_head?] at ha
    obtain ⟨a₀, ha₀, rfl⟩ := Option.mem_map.mp ha
    refine (outlives_comp hcv (Life.down (ι.life1 a₀))).mpr ⟨?_, ?_⟩
    · cases ho : αs.getLast? with
      | none =>
          rw [List.getLast?_eq_none_iff] at ho; subst ho; exact absurd ha₀ (by simp)
      | some o =>
          have hlast : a₀ ≤ o :=
            head_le_of_chain_le hok.2.1 ha₀ (List.mem_of_getLast? ho)
          exact (hz o ho).mono (le_of_lt (lt_of_lt_of_le (GhostEnd.down_lt _)
            (le_trans (ι.life1_le a₀) hlast)))
    · refine GhostEnd.vwS_inStratum (vwSW_vwS hv.1) _ fun α hα => ?_
      obtain ⟨α₀, hα₀, rfl⟩ := List.mem_map.mp hα
      exact lt_of_lt_of_le (GhostEnd.down_lt _)
        (ι.life1_strictMono.monotone (head_le_of_chain_le hok.2.1 ha₀ hα₀))
  · refine ResU.inStratum_comp_at (CellU.compS_hC a) hcv (fun φ f => ?_) (fun φ f => ?_) e
    · rw [Inst.life_getLast?] at ha
      obtain ⟨o, ho, rfl⟩ := Option.mem_map.mp ha
      exact ((hz o ho) k φ f).mono (ι.life1_le o)
    · exact absurd (vwS_places (vwSW_vwS hv.1) k φ f) hk

/-- **An instantiation keeps `StackOKB`**, at every instantiation. -/
theorem StackOKB.inst {σ : LStack} {αs : List Life} (h : StackOKB σ αs) (ι : Inst) :
    StackOKB σ (ι.life αs) := by
  obtain ⟨hl, hc, hx, hr⟩ := h
  have hm := ι.life1_strictMono
  refine ⟨by simp [Inst.life, hl], ?_, fun p hp q hq => ?_, fun p hp q hq h => ?_⟩
  · exact (List.isChain_map ι.life1).mpr (hc.imp fun _ _ h => hm.monotone h)
  · rw [Inst.life, List.zip_map_right, List.mem_map] at hp hq
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    simp only [Prod.map_fst, Prod.map_snd, id]
    rw [hx p₀ hp₀ q₀ hq₀]
    exact ⟨fun h => h ▸ rfl, fun h => hm.injective h⟩
  · rw [Inst.life, List.zip_map_right, List.mem_map] at hp hq
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    exact hr p₀ hp₀ q₀ hq₀ (hm.injective h)

/-- **A single push keeps `StackOKB`**: an entry new to the stack's variables, strictly below the
stack. -/
theorem stackOKB_push {σ : LStack} {αs : List Life} {e : LEnt} {a : Life} (h : StackOKB σ αs)
    (hch : List.IsChain (· < ·) (a :: αs)) (hx : e.x ∉ σ.map LEnt.x) :
    StackOKB (e :: σ) (a :: αs) := by
  obtain ⟨hl, hc, hxs, hr⟩ := h
  have hlt : ∀ b ∈ αs, a < b := fun b hb =>
    List.rel_of_pairwise_cons (List.IsChain.pairwise hch) hb
  have hne : ∀ q ∈ σ.zip αs, e.x ≠ q.1.x ∧ a ≠ q.2 := fun q hq =>
    ⟨fun h => hx (h ▸ List.mem_map_of_mem (List.of_mem_zip hq).1),
      ne_of_lt (hlt q.2 (List.of_mem_zip hq).2)⟩
  refine ⟨by simp [hl], hch.imp fun _ _ h => le_of_lt h, fun p hp q hq => ?_,
    fun p hp q hq hpq => ?_⟩
  · rw [List.zip_cons_cons] at hp hq
    rcases List.mem_cons.mp hp with rfl | hp <;> rcases List.mem_cons.mp hq with rfl | hq
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · exact ⟨fun h => absurd h (hne q hq).1, fun h => absurd h (hne q hq).2⟩
    · exact ⟨fun h => absurd h.symm (hne p hp).1, fun h => absurd h.symm (hne p hp).2⟩
    · exact hxs p hp q hq
  · rw [List.zip_cons_cons] at hp hq
    rcases List.mem_cons.mp hp with rfl | hp <;> rcases List.mem_cons.mp hq with rfl | hq
    · rfl
    · exact absurd hpq (hne q hq).2
    · exact absurd hpq.symm (hne p hp).2
    · exact hr p hp q hq hpq

end ProbeD1

end

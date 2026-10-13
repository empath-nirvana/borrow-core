import ProbeD1.BinderW

/-!
# ProbeD1 — the lifetime binder: the instantiation's bookkeeping (`BINDER.md` §3, item 2)

The relation-independent facts about an instantiation `ι : Inst` (the identity, or a
re-stratification `Restrat.Emb c` at the stack's cut).

* **The models** (`instModels`, `reLendModelsI_of`, `q2Inst`): `extS` commutes with `θ ∘ -`
  (`extS_inst`), and `⟦Δ⟧` is invariant under a re-stratification (`Restrat.Emb.models_mapN_iff`).
  No condition on `Δ`'s bounds. So `ReLendModels` at the instantiations follows from the index's
  models, and `q2_reached`'s configuration is kept by every instantiation.
* **The stack**: an instantiation is a re-lend (`instReLend`); the own lend's bound is read at the
  instantiated reading (`stackJInst`); an own lend is below `⊤` (`ownPushBelowTop`).
* **Composition**: a re-stratification at a lower cut is one at a higher cut (`embLift`), and an
  instantiation of an instantiated stack is an instantiation of the stack (`instComp`), the
  records included.
* **The records**: an instantiation keeps `RecsOutside` (`recsOutsideInst`); the share's
  instantiation at the ended part's cut is one of the whole stack (`shareReLendInst`); the views'
  records are kept along a composite (`keepsSComp`).
* **The readings**: `SubOutside` is kept by an instantiation (`subOutsideInst`), opened by the own
  lend (`subOutsidePush`) and kept by a binding new to the stack (`subOutsideExtend`). An internal
  variable was bound inside the outermost lend (`internalBoundInside`), and the share's
  instantiation fixes every variable bound before the part it moves (`sharedReadFixed`).
* **The two descriptions of "internal"**: a variable whose bound reaches below a stack variable is
  internal (`internalOfBound`).
* **Freshness**: fresh instantiations exist (`instFreshExists`), by arithmetic.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS)

/-! ### The action on one lifetime -/

namespace Inst

theorem life1_none (a : Life) : life1 none a = a := rfl

theorem life1_some {c : Life} (θ : Restrat.Emb c) (a : Life) : life1 (some ⟨c, θ⟩) a = θ a := rfl

theorem life1_le (ι : Inst) (a : Life) : ι.life1 a ≤ a := by
  rcases ι with _ | ⟨c, θ⟩
  · exact le_rfl
  · exact θ.le_self a

theorem life1_lt_iff (ι : Inst) {a b : Life} : ι.life1 a < ι.life1 b ↔ a < b := by
  rcases ι with _ | ⟨c, θ⟩
  · exact Iff.rfl
  · exact θ.lt_iff

theorem life1_le_iff (ι : Inst) {a b : Life} : ι.life1 a ≤ ι.life1 b ↔ a ≤ b := by
  rcases ι with _ | ⟨c, θ⟩
  · exact Iff.rfl
  · exact θ.le_iff

theorem life1_strictMono (ι : Inst) : StrictMono ι.life1 := fun _ _ h => ι.life1_lt_iff.mpr h

theorem life_length (ι : Inst) (αs : List Life) : (ι.life αs).length = αs.length :=
  List.length_map _

theorem mem_life {ι : Inst} {αs : List Life} {a' : Life} :
    a' ∈ ι.life αs ↔ ∃ a ∈ αs, ι.life1 a = a' := List.mem_map

theorem life_getLast? (ι : Inst) (αs : List Life) :
    (ι.life αs).getLast? = αs.getLast?.map ι.life1 := List.getLast?_map

theorem life_head? (ι : Inst) (αs : List Life) :
    (ι.life αs).head? = αs.head?.map ι.life1 := List.head?_map

/-- The action on one record: moved when its frame lifetime is below the cut. -/
def rec1 : Inst → SRec → SRec
  | none, x => x
  | some ⟨c, θ⟩, x =>
      if x.2 < c then (⟨x.1.le, x.1.v, x.1.R, x.1.T, Restrat.LSub.mapN θ.toNat x.1.δ⟩, θ x.2)
      else x

theorem recs_eq_map (ι : Inst) (ls : List SRec) : ι.recs ls = ls.map ι.rec1 := by
  rcases ι with _ | ⟨c, θ⟩
  · exact (List.map_id' ls).symm
  · rfl

theorem mem_recs {ι : Inst} {ls : List SRec} {x : SRec} :
    x ∈ ι.recs ls ↔ ∃ y ∈ ls, ι.rec1 y = x := by
  rw [recs_eq_map]; exact List.mem_map

theorem rec1_le (ι : Inst) (x : SRec) : (ι.rec1 x).1.le = x.1.le := by
  rcases ι with _ | ⟨c, θ⟩
  · rfl
  · simp only [rec1]; split <;> rfl

theorem rec1_v (ι : Inst) (x : SRec) : (ι.rec1 x).1.v = x.1.v := by
  rcases ι with _ | ⟨c, θ⟩
  · rfl
  · simp only [rec1]; split <;> rfl

theorem rec1_R (ι : Inst) (x : SRec) : (ι.rec1 x).1.R = x.1.R := by
  rcases ι with _ | ⟨c, θ⟩
  · rfl
  · simp only [rec1]; split <;> rfl

theorem rec1_T (ι : Inst) (x : SRec) : (ι.rec1 x).1.T = x.1.T := by
  rcases ι with _ | ⟨c, θ⟩
  · rfl
  · simp only [rec1]; split <;> rfl

theorem rec1_fixed {c : Life} (θ : Restrat.Emb c) {x : SRec} (h : c ≤ x.2) :
    rec1 (some ⟨c, θ⟩) x = x := by
  simp only [rec1, if_neg (not_lt.mpr h)]

theorem rec1_moved {c : Life} (θ : Restrat.Emb c) {x : SRec} (h : x.2 < c) :
    rec1 (some ⟨c, θ⟩) x =
      (⟨x.1.le, x.1.v, x.1.R, x.1.T, Restrat.LSub.mapN θ.toNat x.1.δ⟩, θ x.2) := by
  simp only [rec1, if_pos h]

end Inst

/-! ### The cut -/

theorem cutOf_eq {αs : List Life} {c : Life} :
    cutOf αs = some c ↔ ∃ o ∈ αs.getLast?, c = OrderDual.toDual (OrderDual.ofDual o - 1) := by
  unfold cutOf
  cases αs.getLast? with
  | none => simp
  | some o => simp [eq_comm]

/-- Below `⊤`, the cut is the lifetime just above the outermost lend: `x ⊏ c ↔ x ⊑ o`. -/
theorem lt_cut_iff {o x : Life} (ho : o < ⊤) :
    x < OrderDual.toDual (OrderDual.ofDual o - 1) ↔ x ≤ o := by
  have h0 : 0 < OrderDual.ofDual o := by
    have : OrderDual.ofDual (⊤ : Life) < OrderDual.ofDual o := ho
    exact lt_of_le_of_lt (Nat.zero_le _) this
  show OrderDual.ofDual o - 1 < OrderDual.ofDual x ↔ OrderDual.ofDual o ≤ OrderDual.ofDual x
  omega

/-- The outermost lend is strictly below the cut (below `⊤`). -/
theorem lt_cut_self {o : Life} (ho : o < ⊤) : o < OrderDual.toDual (OrderDual.ofDual o - 1) :=
  (lt_cut_iff ho).mpr le_rfl

/-- At `⊤`, the cut is `⊤`. -/
theorem cut_top : OrderDual.toDual (OrderDual.ofDual (⊤ : Life) - 1) = (⊤ : Life) := rfl

/-- Anything strictly above a lend `o` is at or above its cut. -/
theorem cut_le_of_lt {o x : Life} (h : o < x) : OrderDual.toDual (OrderDual.ofDual o - 1) ≤ x := by
  show OrderDual.ofDual x ≤ OrderDual.ofDual o - 1
  have : OrderDual.ofDual x < OrderDual.ofDual o := h
  omega

/-- At or above the cut is strictly above the lend, below `⊤`. -/
theorem lt_of_cut_le {o x : Life} (ho : o < ⊤) (h : OrderDual.toDual (OrderDual.ofDual o - 1) ≤ x) :
    o < x := by
  by_contra hn
  exact absurd ((lt_cut_iff ho).mpr (not_lt.mp hn)) (not_lt.mpr h)

/-- Every lend of a stack in nesting order is at or below the outermost. -/
theorem le_last_of_mem {αs : List Life} (hc : List.IsChain (· < ·) αs) {a o : Life} (ha : a ∈ αs)
    (ho : αs.getLast? = some o) : a ≤ o :=
  mem_le_last hc a ha o ho

/-- **A cut is below the cut of an instantiation of its stack**: an instantiation lowers the
outermost lend. -/
theorem cutOf_inst_le {αs : List Life} {c c₂ : Life} {ι : Inst} (h₁ : cutOf αs = some c)
    (h₂ : cutOf (ι.life αs) = some c₂) : c₂ ≤ c := by
  obtain ⟨o, ho, rfl⟩ := cutOf_eq.mp h₁
  obtain ⟨o₂, ho₂, rfl⟩ := cutOf_eq.mp h₂
  rw [Inst.life_getLast?, ho] at ho₂
  obtain rfl : o₂ = ι.life1 o := by simpa using ho₂.symm
  show OrderDual.ofDual o - 1 ≤ OrderDual.ofDual (ι.life1 o) - 1
  have : OrderDual.ofDual o ≤ OrderDual.ofDual (ι.life1 o) := ι.life1_le o
  omega

/-- **Below one cut, an instantiation lands below the instantiated stack's cut.** -/
theorem lt_cutOf_inst {αs : List Life} {c c₂ : Life} {ι : Inst} (h₁ : cutOf αs = some c)
    (h₂ : cutOf (ι.life αs) = some c₂) {x : Life} (hx : x < c) : ι.life1 x < c₂ := by
  obtain ⟨o, ho, rfl⟩ := cutOf_eq.mp h₁
  obtain ⟨o₂, ho₂, rfl⟩ := cutOf_eq.mp h₂
  rw [Inst.life_getLast?, ho] at ho₂
  obtain rfl : o₂ = ι.life1 o := by simpa using ho₂.symm
  by_cases htop : o < ⊤
  · have hxo : x ≤ o := (lt_cut_iff htop).mp hx
    have htop₂ : ι.life1 o < ⊤ := lt_of_le_of_lt (ι.life1_le o) htop
    exact (lt_cut_iff htop₂).mpr (ι.life1_le_iff.mpr hxo)
  · have hot : o = ⊤ := le_antisymm le_top (not_lt.mp htop)
    subst hot
    have h1 : ι.life1 (⊤ : Life) = ⊤ := by
      rcases ι with _ | ⟨c', θ⟩
      · rfl
      · exact θ.map_top
    rw [h1, cut_top]
    rw [cut_top] at hx
    exact lt_of_le_of_lt (ι.life1_le x) hx

/-! ### The reading substitution -/

theorem Inst.sub_none (δ : LSub) : Inst.sub none δ = δ := rfl

theorem Inst.find?_sub (ι : Inst) (δ : LSub) (y : LifeVar) :
    (ι.sub δ).find? y = (δ.find? y).map (fun m => OrderDual.ofDual (ι.life1 (OrderDual.toDual m))) := by
  rcases ι with _ | ⟨c, θ⟩
  · show δ.find? y = Option.map (fun m => m) (δ.find? y)
    cases δ.find? y <;> rfl
  · exact Restrat.LSub.find?_mapN _ δ y

theorem Inst.sub_extend (ι : Inst) (δ : LSub) (x : LifeVar) (a : Life) :
    ι.sub (δ.extend x a) = (ι.sub δ).extend x (ι.life1 a) := by
  rcases ι with _ | ⟨c, θ⟩
  · rfl
  · rfl

/-- **The stack's reading commutes with an instantiation.** -/
theorem extS_inst (δ : LSub) (ι : Inst) : ∀ (σ : LStack) (αs : List Life),
    extS (ι.sub δ) σ (ι.life αs) = ι.sub (extS δ σ αs)
  | [], αs => by cases αs <;> rfl
  | _ :: _, [] => rfl
  | e :: σ, α :: αs => by
      show (extS (ι.sub δ) σ (ι.life αs)).extend e.x (ι.life1 α) =
        ι.sub ((extS δ σ αs).extend e.x α)
      rw [extS_inst δ ι σ αs, Inst.sub_extend]

theorem extSInst : ExtSInst := fun δ σ αs ι _ => extS_inst δ ι σ αs

theorem Inst.interp_sub (ι : Inst) (δ : LSub) (a : Lifetime.Life) :
    a.interp (ι.sub δ) = (a.interp δ).map (fun m => OrderDual.ofDual (ι.life1 (OrderDual.toDual m))) := by
  rcases ι with _ | ⟨c, θ⟩
  · show a.interp δ = Option.map (fun m => m) (a.interp δ)
    cases a.interp δ <;> rfl
  · exact θ.interp_mapN δ a

theorem Inst.models_sub_iff (ι : Inst) (Δ : LifeCtx) (δ : LSub) :
    Δ.Models (ι.sub δ) ↔ Δ.Models δ := by
  rcases ι with _ | ⟨c, θ⟩
  · exact Iff.rfl
  · exact θ.models_mapN_iff Δ δ

theorem Inst.ltLife_sub_iff (ι : Inst) (δ : LSub) (b : Lifetime.Life) (a : Life) :
    LtLife (ι.sub δ) b (ι.life1 a) ↔ LtLife δ b a := by
  rcases ι with _ | ⟨c, θ⟩
  · exact Iff.rfl
  · exact θ.ltLife_mapN_iff δ b a

/-! ### The models at an instantiation -/

/-- **An instantiation keeps every lifetime context's models.** -/
theorem instModels : InstModels := by
  intro Δ δ σ αs ι h
  rw [extS_inst]
  exact (ι.models_sub_iff Δ _).mpr h

/-- **`ReLendModels` at the instantiations follows from the index's models**, at every `Δ`. It
replaces `BoundsStackFree`. -/
theorem reLendModelsI_of {Δ : LifeCtx} {δ : LSub} {σ : LStack} {αs : List Life}
    (h : Δ.Models (extS δ σ αs)) : ReLendModelsI Δ δ σ αs :=
  fun ι _ => instModels Δ δ σ αs ι h

/-- **`q2_reached`'s configuration is kept by every instantiation.** -/
theorem q2Inst : Q2Inst :=
  reLendModelsI_of q2_reached.2.2.2.2.1

/-! ### The stack at an instantiation -/

/-- **An instantiation of a stack in shape is a re-lend of it.** -/
theorem instReLend : InstReLend := by
  intro σ αs ι hok _
  refine ⟨?_, ?_⟩
  · show List.Forall₂ (· ≤ ·) (αs.map ι.life1) αs
    rw [List.forall₂_map_left_iff]
    exact List.forall₂_same.mpr fun a _ => ι.life1_le a
  · exact List.isChain_map_of_isChain _ (fun a b h => ι.life1_lt_iff.mpr h) hok.2.1

theorem StackOK.inst {σ : LStack} {αs : List Life} (hok : StackOK σ αs) (ι : Inst) :
    StackOK σ (ι.life αs) :=
  ⟨(ι.life_length αs).trans hok.1,
    List.isChain_map_of_isChain _ (fun _ _ h => ι.life1_lt_iff.mpr h) hok.2.1, hok.2.2⟩

/-- **The stack's entries in a judgement are entries of it at an instantiation.** -/
theorem stackJInst : StackJInst := by
  intro σ αs δ Δ Γ C ι _ h
  obtain ⟨hn, hp, hk⟩ := h
  refine ⟨hn, hp, fun e he => ?_⟩
  rcases hk e he with h₁ | h₂ | ⟨h₃, hhd, hfr, c, C', hC, hb, hlt⟩
  · exact Or.inl h₁
  · exact Or.inr (Or.inl h₂)
  · refine Or.inr (Or.inr ⟨h₃, hhd, hfr, c, C', hC, hb, fun a' ha' => ?_⟩)
    rw [Inst.life_head?] at ha'
    obtain ⟨a, ha, rfl⟩ := Option.mem_map.mp ha'
    rw [extS_inst]
    exact (ι.ltLife_sub_iff _ c a).mpr (hlt a ha)

/-- **An own lend is below `⊤`.** -/
theorem ownPushBelowTop : OwnPushBelowTop := by
  intro δ C ρ s e a h
  obtain ⟨x, c, C', -, -, -, -, ⟨β, -, hlt⟩, -⟩ := h
  exact lt_of_lt_of_le hlt le_top

/-! ### Composition -/

/-- **A re-stratification at a lower cut is one at a higher cut.** -/
theorem embLift : EmbLift := by
  intro c c' θ h
  exact ⟨⟨θ.f, θ.strictMono, fun x hx => θ.fix x (le_trans h hx)⟩, fun _ => rfl⟩

/-- The lift itself. -/
def Restrat.Emb.lift {c c' : Life} (θ : Restrat.Emb c') (h : c' ≤ c) : Restrat.Emb c :=
  ⟨θ.f, θ.strictMono, fun x hx => θ.fix x (le_trans h hx)⟩

theorem mapN_comp {c : Life} (θ₂ θ₁ : Restrat.Emb c) (δ : LSub) :
    Restrat.LSub.mapN (Restrat.Emb.comp θ₂ θ₁).toNat δ =
      Restrat.LSub.mapN θ₂.toNat (Restrat.LSub.mapN θ₁.toNat δ) := by
  cases δ with
  | mk entries =>
      simp only [Restrat.LSub.mapN, List.map_map]
      rfl

/-- **Instantiations compose**, the records included. -/
theorem instComp : InstComp := by
  intro αs ι₁ ι₂ h₁ h₂
  rcases ι₁ with _ | ⟨c₁, θ₁⟩
  · have e : Inst.life none αs = αs := List.map_id' αs
    rw [e] at h₂
    exact ⟨ι₂, h₂, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  · rcases ι₂ with _ | ⟨c₂, θ₂⟩
    · exact ⟨some ⟨c₁, θ₁⟩, h₁, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
    · have hc₁ : cutOf αs = some c₁ := h₁ c₁ θ₁ rfl
      have hc₂ : cutOf (Inst.life (some ⟨c₁, θ₁⟩) αs) = some c₂ := h₂ c₂ θ₂ rfl
      have hle : c₂ ≤ c₁ := cutOf_inst_le hc₁ hc₂
      refine ⟨some ⟨c₁, Restrat.Emb.comp (Restrat.Emb.lift θ₂ hle) θ₁⟩,
        fun c θ h => by cases h; exact hc₁, fun δ => mapN_comp _ _ δ, fun _ => rfl,
        fun ls => ?_⟩
      rw [Inst.recs_eq_map, Inst.recs_eq_map, Inst.recs_eq_map, List.map_map]
      refine List.map_congr_left fun x _ => ?_
      by_cases hx : x.2 < c₁
      · have hx₂ : θ₁ x.2 < c₂ := lt_cutOf_inst (ι := some ⟨c₁, θ₁⟩) hc₁ hc₂ hx
        show Inst.rec1 _ x = Inst.rec1 (some ⟨c₂, θ₂⟩) (Inst.rec1 (some ⟨c₁, θ₁⟩) x)
        rw [Inst.rec1_moved _ hx, Inst.rec1_moved _ hx, Inst.rec1_moved _ hx₂]
        simp only [mapN_comp]
        rfl
      · have hx' : c₁ ≤ x.2 := not_lt.mp hx
        show Inst.rec1 _ x = Inst.rec1 (some ⟨c₂, θ₂⟩) (Inst.rec1 (some ⟨c₁, θ₁⟩) x)
        rw [Inst.rec1_fixed _ hx', Inst.rec1_fixed _ hx', Inst.rec1_fixed _ (le_trans hle hx')]

/-! ### The records -/

/-- **An instantiation keeps `RecsOutside`.** -/
theorem recsOutsideInst : RecsOutsideInst := by
  intro αs ls ι hat h a' ha' x' hx' hlt p' hp'
  obtain ⟨a, ha, rfl⟩ := Inst.mem_life.mp ha'
  obtain ⟨x, hx, rfl⟩ := Inst.mem_recs.mp hx'
  rcases ι with _ | ⟨c, θ⟩
  · exact h a ha x hx hlt p' hp'
  · by_cases hxc : x.2 < c
    · rw [Inst.rec1_moved _ hxc] at hlt hp'
      have hax : a < x.2 := θ.lt_iff.mp hlt
      simp only [Restrat.LSub.mapN, List.mem_map] at hp'
      obtain ⟨p, hp, rfl⟩ := hp'
      exact θ.lt_iff.mpr (h a ha x hx hax p hp)
    · have hcx : c ≤ x.2 := not_lt.mp hxc
      rw [Inst.rec1_fixed _ hcx] at hlt hp'
      by_cases hac : c ≤ a
      · rw [show Inst.life1 (some ⟨c, θ⟩) a = a from θ.fix a hac] at hlt ⊢
        exact h a ha x hx hlt p' hp'
      · have hax : a < x.2 := lt_of_lt_of_le (not_le.mp hac) hcx
        exact lt_of_le_of_lt (θ.le_self a) (h a ha x hx hax p' hp')

/-- In nesting order, everything in the outer part is strictly above the inner part's
outermost lend. -/
theorem lt_outer {αi αo : List Life} (hc : List.IsChain (· < ·) (αi ++ αo)) {oi : Life}
    (hoi : αi.getLast? = some oi) {a : Life} (ha : a ∈ αo) : oi < a := by
  obtain ⟨-, hco, hrel⟩ := List.isChain_append.mp hc
  cases αo with
  | nil => exact absurd ha List.not_mem_nil
  | cons h t =>
      have hlt : oi < h := hrel oi hoi h rfl
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hlt
      · exact lt_trans hlt (GhostEnd.head_lt_mem hco a ha)

/-- …hence at or above its cut. -/
theorem cut_le_outer {αi αo : List Life} (hc : List.IsChain (· < ·) (αi ++ αo)) {oi : Life}
    (hoi : αi.getLast? = some oi) {a : Life} (ha : a ∈ αo) :
    OrderDual.toDual (OrderDual.ofDual oi - 1) ≤ a :=
  cut_le_of_lt (lt_outer hc hoi ha)

/-- A substitution whose every value a map fixes is fixed by it. -/
theorem mapN_eq_self {g : ℕ → ℕ} {δ : LSub} (h : ∀ p ∈ δ.entries, g p.2 = p.2) :
    Restrat.LSub.mapN g δ = δ := by
  cases δ with
  | mk entries =>
      show (⟨entries.map fun p => (p.1, g p.2)⟩ : LSub) = ⟨entries⟩
      congr 1
      conv_rhs => rw [← List.map_id' entries]
      exact List.map_congr_left fun p hp => Prod.ext rfl (h p hp)

/-- **The share's instantiation is one of the whole stack**: at the cut of the ended part, it
fixes the kept part, reads the same substitution, and (under `RecsOutside`) moves the same
records. -/
theorem shareReLendInst : ShareReLendInst := by
  intro αi αo ls ci θ hci hc hro
  obtain ⟨oi, hoi, rfl⟩ := cutOf_eq.mp hci
  cases hαo : αo.getLast? with
  | none =>
      have : αo = [] := List.getLast?_eq_none_iff.mp hαo
      subst this
      refine ⟨Inst.ofEmb θ, fun c θ' h => ?_, by simp [Inst.life], fun _ => rfl, rfl⟩
      cases h
      rw [List.append_nil]
      exact hci
  | some oo =>
      have hoo : oo ∈ αo := List.mem_of_getLast? hαo
      have hlt : oi < oo := lt_outer hc hoi hoo
      have hle : OrderDual.toDual (OrderDual.ofDual oi - 1) ≤
          OrderDual.toDual (OrderDual.ofDual oo - 1) := by
        show OrderDual.ofDual oo - 1 ≤ OrderDual.ofDual oi - 1
        have : OrderDual.ofDual oo < OrderDual.ofDual oi := hlt
        omega
      have hcut : cutOf (αi ++ αo) = some (OrderDual.toDual (OrderDual.ofDual oo - 1)) := by
        unfold cutOf
        rw [List.getLast?_append, hαo]
        rfl
      have htop : oi < ⊤ := lt_of_lt_of_le hlt le_top
      refine ⟨some ⟨_, Restrat.Emb.lift θ hle⟩, fun c θ' h => by cases h; exact hcut, ?_,
        fun _ => rfl, ?_⟩
      · show (αi ++ αo).map θ = αi.map θ ++ αo
        rw [List.map_append]
        congr 1
        conv_rhs => rw [← List.map_id' αo]
        refine List.map_congr_left fun a ha => θ.fix a (cut_le_outer hc hoi ha)
      · rw [Inst.recs_eq_map, Inst.recs_eq_map]
        refine List.map_congr_left fun x hx => ?_
        show Inst.rec1 (some ⟨_, Restrat.Emb.lift θ hle⟩) x = Inst.rec1 (some ⟨_, θ⟩) x
        by_cases h₁ : x.2 < OrderDual.toDual (OrderDual.ofDual oi - 1)
        · rw [Inst.rec1_moved _ h₁, Inst.rec1_moved _ (lt_of_lt_of_le h₁ hle)]
          rfl
        · have hc₁ : OrderDual.toDual (OrderDual.ofDual oi - 1) ≤ x.2 := not_lt.mp h₁
          rw [Inst.rec1_fixed _ hc₁]
          by_cases h₂ : x.2 < OrderDual.toDual (OrderDual.ofDual oo - 1)
          · rw [Inst.rec1_moved _ h₂]
            have hox : oi < x.2 := lt_of_cut_le htop hc₁
            have hδ : Restrat.LSub.mapN (Restrat.Emb.lift θ hle).toNat x.1.δ = x.1.δ := by
              refine mapN_eq_self fun p hp => ?_
              have hop : oi < OrderDual.toDual p.2 :=
                hro oi (List.mem_append_left _ (List.mem_of_getLast? hoi)) x hx hox p hp
              exact congrArg OrderDual.ofDual (θ.fix _ (cut_le_of_lt hop))
            rw [hδ, show (Restrat.Emb.lift θ hle) x.2 = x.2 from θ.fix x.2 hc₁]
          · rw [Inst.rec1_fixed _ (not_lt.mp h₂)]

/-! ### The views' records along a composite -/

theorem rel_rec1 (ι : Inst) (x : SRec) (ρ : WRes) : Core.Rel (ι.rec1 x).1 ρ ↔ Core.Rel x.1 ρ := by
  unfold Core.Rel
  rw [ι.rec1_le, ι.rec1_v, ι.rec1_R, ι.rec1_T]

/-- A chain reads only the witness's `own` cells. -/
theorem Chain.of_own_iff {R R' : WRes} (hR : ∀ l u, R'.get l = some (CellU.ownOf u) ↔
    R.get l = some (CellU.ownOf u)) {T : VTy} {v : Val} {p : Option BoCa.Loc} {m : BoCa.Loc}
    {S : VTy} {u : Val} (h : Chain R T v p m S u) : Chain R' T v p m S u := by
  induction h with
  | one hr hg => exact Chain.one hr ((hR _ _).mpr hg)
  | step hr hg _ ih => exact Chain.step hr ((hR _ _).mpr hg) ih

theorem RecUpTo.refl (x : SRec) : RecUpTo x x :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => Iff.rfl⟩

theorem RecUpTo.trans {x y z : SRec} (h₁ : RecUpTo x y) (h₂ : RecUpTo y z) : RecUpTo x z := by
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂⟩ := h₂
  exact ⟨a₂.trans a₁, b₂.trans b₁, c₂.trans c₁, d₂.trans d₁, e₂.trans e₁,
    fun l u => (f₂ l u).trans (f₁ l u)⟩

/-- `Rel` reads a record up to `RecUpTo`. -/
theorem RecUpTo.rel_iff {x x' : SRec} (h : RecUpTo x x') (ρ : WRes) : Core.Rel x'.1 ρ ↔ Core.Rel x.1 ρ := by
  obtain ⟨hl, hv, hT, -, -, hR⟩ := h
  unfold Core.Rel
  rw [hl, hv, hT]
  constructor
  · rintro ⟨m, ψ, hg, hk, hm⟩
    refine ⟨m, ψ, hg, hk, hm.imp id fun ⟨p, S, u, hc⟩ =>
      ⟨p, S, u, Chain.of_own_iff (fun l u => (hR l u).symm) hc⟩⟩
  · rintro ⟨m, ψ, hg, hk, hm⟩
    refine ⟨m, ψ, hg, hk, hm.imp id fun ⟨p, S, u, hc⟩ => ⟨p, S, u, Chain.of_own_iff hR hc⟩⟩

/-- An instantiation acts on records `RecUpTo` one another alike. -/
theorem RecUpTo.rec1 {x x' : SRec} (h : RecUpTo x x') (ι : Inst) : RecUpTo (ι.rec1 x) (ι.rec1 x') := by
  obtain ⟨hl, hv, hT, hd, he, hR⟩ := h
  rcases ι with _ | ⟨c, θ⟩
  · exact ⟨hl, hv, hT, hd, he, hR⟩
  · by_cases hx : x.2 < c
    · have hx' : x'.2 < c := he ▸ hx
      rw [Inst.rec1_moved _ hx, Inst.rec1_moved _ hx']
      exact ⟨hl, hv, hT, by simp only [hd], by simp only [he], hR⟩
    · have hx' : ¬ x'.2 < c := he ▸ hx
      rw [Inst.rec1_fixed _ (not_lt.mp hx), Inst.rec1_fixed _ (not_lt.mp hx')]
      exact ⟨hl, hv, hT, hd, he, hR⟩

/-- An `imm` cell at `m`. -/
def ImmAt (ρ : WRes) (m : BoCa.Loc) : Prop := ∃ ψ, ρ.get m = some ψ ∧ ψ.kind = Kind.imm

/-- The places a stack's views put an `imm` cell at, as the drop flags and the shadowing decide. -/
def VisImm : List BoCa.Loc → LStack → List Bool → BoCa.Loc → Prop
  | seen, e :: σ, d :: ds, m =>
      (vis seen e d = true ∧ e.l = m ∧ (match e.k with | .mut => False | .imm _ => True)) ∨
        VisImm (e.l :: seen) σ ds m
  | _, _, _, _ => False

theorem immAt_compS {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (m : BoCa.Loc) :
    ImmAt ρ m ↔ ImmAt ρ₁ m ∨ ImmAt ρ₂ m := by
  rcases ResU.Comp.get hc m with ⟨e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ | ⟨ψ, e₁, e₂, e⟩ |
      ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hC⟩
  · simp [ImmAt, e₁, e₂, e]
  · simp [ImmAt, e₁, e₂, e]
  · simp [ImmAt, e₁, e₂, e]
  · obtain ⟨s₁, s₂, v, χ, k₁, k₂, k₃, f₁, f₂, f₃⟩ := hC
    subst f₁ f₂ f₃
    simp [ImmAt, e₁, e₂, e]

theorem immAt_vwEW {s : LSub} {e : LEnt} {d : Bool} {α : Life} {ls : List SRec} {ρ : WRes}
    (h : vwEW s e d α ls ρ) (m : BoCa.Loc) :
    ImmAt ρ m ↔ (d = true ∧ e.l = m ∧ (match e.k with | .mut => False | .imm _ => True)) := by
  obtain ⟨hv, -⟩ := h
  cases d with
  | false =>
      obtain ⟨rfl, -⟩ := hv
      simp [ImmAt]
  | true =>
      obtain ⟨l, x, T, k, cr⟩ := e
      cases k with
      | «mut» =>
          obtain ⟨b, u, χ, hχ, Q, hw, ls₀, -, rfl, -⟩ := hv
          simp only [ImmAt, and_false, iff_false, not_exists, not_and]
          intro ψ hψ
          rcases ResU.single_get_eq_some hψ with ⟨-, rfl⟩
          simp
      | imm v =>
          obtain ⟨s', u, χ, hχ, ls₀, rfl, -⟩ := hv
          simp only [ImmAt, true_and, and_true]
          constructor
          · rintro ⟨ψ, hψ, -⟩
            exact (ResU.single_get_eq_some hψ).1.symm
          · rintro rfl
            exact ⟨_, ResU.single_get_self _ _, rfl⟩

/-- **A stack's views put their `imm` cells where the flags and the shadowing say**, whatever the
reading, the lifetimes and the list. -/
theorem immAt_vwSW {s : LSub} : ∀ {seen : List BoCa.Loc} {σ : LStack} {ds : List Bool}
    {αs : List Life} {ls : List SRec} {ρ : WRes}, vwSW s seen σ ds αs ls ρ →
    ∀ m, ImmAt ρ m ↔ VisImm seen σ ds m
  | _, [], [], [], _, _, h, m => by
      obtain ⟨rfl, -⟩ := h
      simp [ImmAt, VisImm]
  | seen, e :: σ, d :: ds, α :: αs, ls, ρ, ⟨a, r, hc, ha, hr⟩, m => by
      rw [immAt_compS hc, immAt_vwEW ha, immAt_vwSW hr m]
      rfl
  | _, [], [], _ :: _, _, _, h, _ => h.elim
  | _, [], _ :: _, [], _, _, h, _ => h.elim
  | _, [], _ :: _, _ :: _, _, _, h, _ => h.elim
  | _, _ :: _, [], [], _, _, h, _ => h.elim
  | _, _ :: _, [], _ :: _, _, _, h, _ => h.elim
  | _, _ :: _, _ :: _, [], _, _, h, _ => h.elim

theorem rel_iff_of_immAt {ρ ρ' : WRes} (h : ∀ m, ImmAt ρ m ↔ ImmAt ρ' m) (r : FrameRec) :
    Core.Rel r ρ ↔ Core.Rel r ρ' := by
  unfold Core.Rel
  constructor
  · rintro ⟨m, ψ, hg, hk, hm⟩
    obtain ⟨ψ', hg', hk'⟩ := (h m).mp ⟨ψ, hg, hk⟩
    exact ⟨m, ψ', hg', hk', hm⟩
  · rintro ⟨m, ψ, hg, hk, hm⟩
    obtain ⟨ψ', hg', hk'⟩ := (h m).mpr ⟨ψ, hg, hk⟩
    exact ⟨m, ψ', hg', hk', hm⟩

/-- **The views' records are kept along a composite instantiation.** -/
theorem keepsSComp : KeepsSComp := by
  intro s s' σ ds αs αs' ls lsv ls₁ ls₂ ρn ρv ι₁ ι₂ hn hv hk₁ hk₂ x hx hrel
  obtain ⟨y, hy, rfl⟩ := Inst.mem_recs.mp hx
  have hrely : Core.Rel y.1 ρn := (rel_rec1 ι₂ y ρn).mp hrel
  obtain ⟨x₁, hx₁, hux₁⟩ := hk₁ y hy hrely
  have hrel₁ : Core.Rel x₁.1 ρn := (hux₁.rel_iff ρn).mpr hrely
  have himm : ∀ m, ImmAt ρn m ↔ ImmAt ρv m := fun m =>
    (immAt_vwSW hn.1 m).trans (immAt_vwSW hv.1 m).symm
  have hrel₁v : Core.Rel x₁.1 ρv := (rel_iff_of_immAt himm x₁.1).mp hrel₁
  obtain ⟨x₂, hx₂, hux₂⟩ := hk₂ (ι₂.rec1 x₁) (Inst.mem_recs.mpr ⟨x₁, hx₁, rfl⟩)
    ((rel_rec1 ι₂ x₁ ρv).mpr hrel₁v)
  exact ⟨x₂, hx₂, (hux₁.rec1 ι₂).trans hux₂⟩

/-! ### The readings -/

theorem boundBefore_sub (ι : Inst) (x : LifeVar) (δ : LSub) :
    boundBefore x (ι.sub δ) =
      (boundBefore x δ).map (fun p => (p.1, OrderDual.ofDual (ι.life1 (OrderDual.toDual p.2)))) := by
  rcases ι with _ | ⟨c, θ⟩
  · show boundBefore x δ = (boundBefore x δ).map (fun p => (p.1, p.2))
    exact (List.map_id' _).symm
  · unfold boundBefore
    show ((δ.entries.map fun p => (p.1, θ.toNat p.2)).dropWhile fun p => p.1 != x).drop 1 = _
    rw [List.dropWhile_map, List.map_drop]
    rfl

theorem boundBefore_extend_self (x : LifeVar) (a : Life) (δ : LSub) :
    boundBefore x (δ.extend x a) = δ.entries := by
  unfold boundBefore
  show (((x, OrderDual.ofDual a) :: δ.entries).dropWhile fun p => p.1 != x).drop 1 = δ.entries
  rw [List.dropWhile_cons_of_neg (by simp)]
  rfl

theorem boundBefore_extend_ne {x y : LifeVar} (h : x ≠ y) (a : Life) (δ : LSub) :
    boundBefore y (δ.extend x a) = boundBefore y δ := by
  unfold boundBefore
  show (((x, OrderDual.ofDual a) :: δ.entries).dropWhile fun p => p.1 != y).drop 1 = _
  rw [List.dropWhile_cons_of_pos (by simpa using h)]

theorem mem_zip_life {σ : LStack} {αs : List Life} {ι : Inst} {e : LEnt} {a' : Life}
    (h : (e, a') ∈ σ.zip (ι.life αs)) : ∃ a, (e, a) ∈ σ.zip αs ∧ ι.life1 a = a' := by
  unfold Inst.life at h
  rw [List.zip_map_right, List.mem_map] at h
  obtain ⟨⟨e₀, a⟩, hm, he⟩ := h
  simp only [Prod.map, Prod.mk.injEq, id] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨a, hm, rfl⟩

/-- **An instantiation keeps `SubOutside`.** -/
theorem subOutsideInst : SubOutsideInst := by
  intro σ αs δ ι h e a' hm p' hp'
  obtain ⟨a, ha, rfl⟩ := mem_zip_life hm
  rw [boundBefore_sub, List.mem_map] at hp'
  obtain ⟨p, hp, rfl⟩ := hp'
  exact ι.life1_lt_iff.mpr (h e a ha p hp)

/-- **The own lend opens `SubOutside`.** -/
theorem subOutsidePush : SubOutsidePush := by
  intro σ αs δ e α hx h hf e' a' hm p hp
  rcases List.mem_cons.mp hm with he | hm
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    rw [boundBefore_extend_self] at hp
    exact hf p hp
  · have hne : e.x ≠ e'.x := fun hxe => hx (hxe ▸ List.mem_map_of_mem (List.of_mem_zip hm).1)
    rw [boundBefore_extend_ne hne] at hp
    exact h e' a' hm p hp

/-- **A binding new to the stack keeps `SubOutside`.** -/
theorem subOutsideExtend : SubOutsideExtend := by
  intro σ αs δ x α hx h e' a' hm p hp
  have hne : x ≠ e'.x := fun hxe => hx (hxe ▸ List.mem_map_of_mem (List.of_mem_zip hm).1)
  rw [boundBefore_extend_ne hne] at hp
  exact h e' a' hm p hp

/-- The outermost entry and the outermost lend are paired by the zip. -/
theorem getLast?_mem_zip : ∀ {σ : LStack} {αs : List Life}, σ.length = αs.length →
    ∀ {e : LEnt} {o : Life}, σ.getLast? = some e → αs.getLast? = some o → (e, o) ∈ σ.zip αs
  | [], _, _, _, _, he, _ => by simp at he
  | [_], [_], _, _, _, he, ho => by
      simp only [List.getLast?_singleton, Option.some.injEq] at he ho
      subst he ho
      exact List.mem_singleton_self _
  | _ :: e₂ :: σ, _ :: o₂ :: αs, hl, _, _, he, ho => by
      rw [List.getLast?_cons_cons] at he ho
      rw [List.zip_cons_cons]
      exact List.mem_cons_of_mem _ (getLast?_mem_zip (σ := e₂ :: σ) (αs := o₂ :: αs)
        (by simpa using hl) he ho)
  | [_], [], hl, _, _, _, _ => by simp at hl
  | [_], _ :: _ :: _, hl, _, _, _, _ => by simp at hl
  | _ :: _ :: _, [], hl, _, _, _, _ => by simp at hl
  | _ :: _ :: _, [_], hl, _, _, _, _ => by simp at hl

theorem assocFind_mem {β : Type} {y : LifeVar} {m : β} :
    ∀ {L : List (LifeVar × β)}, BoCa.Lifetime.assocFind y L = some m → (y, m) ∈ L
  | [], h => by simp [BoCa.Lifetime.assocFind] at h
  | (z, v) :: L, h => by
      simp only [BoCa.Lifetime.assocFind] at h
      split at h
      · subst_vars; cases h; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (assocFind_mem h)

/-- A variable whose newest binding comes after `x`'s newest binding is bound before `x`. -/
theorem mem_boundBefore_of {x y : LifeVar} {m : ℕ} (hxy : y ≠ x) :
    ∀ {L : List (LifeVar × ℕ)}, BoCa.Lifetime.assocFind y L = some m →
      y ∉ (L.takeWhile fun p => p.1 != x).map Prod.fst →
      (y, m) ∈ (L.dropWhile fun p => p.1 != x).drop 1
  | [], h, _ => by simp [BoCa.Lifetime.assocFind] at h
  | (z, v) :: L, h, hn => by
      by_cases hz : z = x
      · subst hz
        have : (z, v) :: L = ((z, v) :: L) := rfl
        rw [List.dropWhile_cons_of_neg (by simp)]
        simp only [BoCa.Lifetime.assocFind, if_neg (Ne.symm hxy)] at h
        exact assocFind_mem h
      · rw [List.takeWhile_cons_of_pos (by simpa using hz)] at hn
        rw [List.dropWhile_cons_of_pos (by simpa using hz)]
        simp only [List.map_cons, List.mem_cons, not_or] at hn
        simp only [BoCa.Lifetime.assocFind, if_neg (Ne.symm hn.1)] at h
        exact mem_boundBefore_of hxy h hn.2

/-- **At an index keeping `SubOutside`, an internal variable was bound inside the outermost
lend.** -/
theorem internalBoundInside : InternalBoundInside := by
  intro δ σ αs y hok hso hiv
  by_cases hy : y ∈ σ.map LEnt.x
  · exact Or.inl hy
  · right
    intro eo heo
    obtain ⟨m, hm, c, hc, hlt⟩ := hiv
    rw [extS_find_not_mem δ σ αs y hy] at hm
    obtain ⟨o, ho, rfl⟩ := cutOf_eq.mp hc
    have hmem : (eo, o) ∈ σ.zip αs := getLast?_mem_zip hok.1.symm heo ho
    have hyx : y ≠ eo.x := fun h => hy (h ▸ List.mem_map_of_mem (List.mem_of_getLast? heo))
    by_contra hnot
    have hbb : (y, m) ∈ boundBefore eo.x δ := mem_boundBefore_of hyx hm hnot
    have h₁ : o < OrderDual.toDual m := hso eo o hmem (y, m) hbb
    have h₁' : m < OrderDual.ofDual o := h₁
    have h₂ : OrderDual.ofDual o - 1 < m := hlt
    omega

/-- **The share's instantiation fixes every variable bound before the part it moves.** -/
theorem sharedReadFixed : SharedReadFixed := by
  intro σi σo αi αo δ ci θ eo hlen hci heo hso p hp
  obtain ⟨oi, hoi, rfl⟩ := cutOf_eq.mp hci
  have hmem : (eo, oi) ∈ (σi ++ σo).zip (αi ++ αo) := by
    rw [List.zip_append hlen.symm]
    exact List.mem_append_left _ (getLast?_mem_zip hlen.symm heo hoi)
  exact θ.fix _ (cut_le_of_lt (hso eo oi hmem p hp))

/-! ### The two descriptions of "internal" -/

/-- The lifetime the stack reads a stack variable at is one of its lends. -/
theorem extS_find_mem_stack (δ : LSub) : ∀ (σ : LStack) (αs : List Life), αs.length = σ.length →
    ∀ y ∈ σ.map LEnt.x, ∃ a ∈ αs, (extS δ σ αs).find? y = some a
  | [], _, _, y, hy => by simp at hy
  | _ :: _, [], hl, _, _ => by simp at hl
  | e :: σ, α :: αs, hl, y, hy => by
      simp only [extS]
      by_cases hxy : e.x = y
      · subst hxy
        exact ⟨α, List.mem_cons_self, find?_extend_self _ _ _⟩
      · rw [find?_extend_ne _ _ hxy]
        have hy' : y ∈ σ.map LEnt.x := by
          simp only [List.map_cons, List.mem_cons] at hy
          exact hy.resolve_left (Ne.symm hxy)
        obtain ⟨a, ha, he⟩ := extS_find_mem_stack δ σ αs (by simpa using hl) y hy'
        exact ⟨a, List.mem_cons_of_mem _ ha, he⟩

section internal
variable {Δ : LifeCtx} {δ : LSub} {σ : LStack} {αs : List Life}

/-- Both halves of `InternalOfBound`, by the mutual recursor. -/
theorem internal_of_boundBelow (hok : StackOK σ αs) (hob : OuterBelowTop αs)
    (hM : Δ.Models (extS δ σ αs)) :
    ∀ y, BoundBelowV Δ σ y → ∀ m, (extS δ σ αs).find? y = some m →
      Internal αs (OrderDual.toDual m) := by
  obtain ⟨o, ho⟩ : ∃ o, αs.getLast? = some o ∨ αs = [] := by
    cases h : αs.getLast? with
    | none => exact ⟨⊤, Or.inr (List.getLast?_eq_none_iff.mp h)⟩
    | some o => exact ⟨o, Or.inl rfl⟩
  have key : ∀ a ∈ αs, Internal αs a := by
    intro a ha
    rcases ho with ho | rfl
    · have hto : o < ⊤ := hob o ho
      exact ⟨_, by unfold cutOf; rw [ho]; rfl,
        lt_of_le_of_lt (le_last_of_mem hok.2.1 ha ho) (lt_cut_self hto)⟩
    · exact absurd ha List.not_mem_nil
  have mono : ∀ a b, Internal αs b → a ≤ b → Internal αs a := by
    intro a b h hab
    obtain ⟨c, hc, hb⟩ := h
    exact ⟨c, hc, lt_of_le_of_lt hab hb⟩
  have hmin : ∀ na nb : ℕ, Internal αs (OrderDual.toDual na) → Internal αs (OrderDual.toDual nb) →
      Internal αs (OrderDual.toDual (min na nb)) := by
    intro na nb h₁ h₂
    obtain ⟨c, hc, ha⟩ := h₁
    obtain ⟨c', hc', hb⟩ := h₂
    obtain rfl : c = c' := Option.some.inj (hc.symm.trans hc')
    refine ⟨c, hc, ?_⟩
    have ha' : OrderDual.ofDual c < na := ha
    have hb' : OrderDual.ofDual c < nb := hb
    show OrderDual.ofDual c < min na nb
    omega
  refine fun y h => @BoundBelowV.rec Δ σ
    (fun y _ => ∀ m, (extS δ σ αs).find? y = some m → Internal αs (OrderDual.toDual m))
    (fun u _ => ∀ n, u.interp (extS δ σ αs) = some n → Internal αs (OrderDual.toDual n))
    ?stack ?bound ?var ?meetL ?meetR ?join y h
  case stack =>
    intro y hy m hm
    obtain ⟨a, ha, he⟩ := extS_find_mem_stack δ σ αs hok.1 y hy
    rw [he] at hm
    rw [← Option.some.inj hm]
    exact key a ha
  case bound =>
    intro y u _ hu _ ih m hm
    obtain ⟨m', n, hm', hn, hlt⟩ := hM y u hu
    rw [hm] at hm'
    rw [Option.some.inj hm']
    exact mono _ _ (ih n hn) (le_of_lt hlt)
  case var =>
    intro z _ ih n hn
    exact ih n hn
  case meetL =>
    intro a b _ ih n hn
    simp only [Lifetime.Life.interp] at hn
    cases ha : a.interp (extS δ σ αs) with
    | none => rw [ha] at hn; simp at hn
    | some na =>
        cases hb : b.interp (extS δ σ αs) with
        | none => rw [ha, hb] at hn; simp at hn
        | some nb =>
            rw [ha, hb] at hn
            simp only [Option.bind_some, Option.some.injEq, Lifetime.SLife.meet] at hn
            subst hn
            exact mono _ _ (ih na ha) (show na ≤ max na nb from le_max_left _ _)
  case meetR =>
    intro a b _ ih n hn
    simp only [Lifetime.Life.interp] at hn
    cases ha : a.interp (extS δ σ αs) with
    | none => rw [ha] at hn; simp at hn
    | some na =>
        cases hb : b.interp (extS δ σ αs) with
        | none => rw [ha, hb] at hn; simp at hn
        | some nb =>
            rw [ha, hb] at hn
            simp only [Option.bind_some, Option.some.injEq, Lifetime.SLife.meet] at hn
            subst hn
            exact mono _ _ (ih nb hb) (show nb ≤ max na nb from le_max_right _ _)
  case join =>
    intro a b _ _ iha ihb n hn
    simp only [Lifetime.Life.interp] at hn
    cases ha : a.interp (extS δ σ αs) with
    | none => rw [ha] at hn; simp at hn
    | some na =>
        cases hb : b.interp (extS δ σ αs) with
        | none => rw [ha, hb] at hn; simp at hn
        | some nb =>
            rw [ha, hb] at hn
            simp only [Option.bind_some, Option.some.injEq, Lifetime.SLife.join] at hn
            subst hn
            exact hmin na nb (iha na ha) (ihb nb hb)

end internal

/-- **A variable whose bound reaches below a stack variable is internal**, at a model of `Δ` and
a stack whose outermost lend is below `⊤`. -/
theorem internalOfBound : InternalOfBound := by
  intro Δ δ σ αs y hok hob hM hb
  have hdef : ∃ m, (extS δ σ αs).find? y = some m := by
    cases hb with
    | stack hy =>
        obtain ⟨a, -, he⟩ := extS_find_mem_stack δ σ αs hok.1 y hy
        exact ⟨a, he⟩
    | bound _ hu _ =>
        obtain ⟨m, -, hm, -, -⟩ := hM _ _ hu
        exact ⟨m, hm⟩
  obtain ⟨m, hm⟩ := hdef
  exact ⟨m, hm, internal_of_boundBelow hok hob hM y hb m hm⟩

/-! ### Freshness -/

theorem nat_le_sum_of_mem {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons b l ih =>
      rcases List.mem_cons.mp h with rfl | h
      · simp
      · have := ih h; simp only [List.sum_cons]; omega

theorem CellU.inStratum_of_lt_at {ψ : CellU BoCa.Loc Val} {a : Life} (h : a < ψ.at) :
    ψ.InStratum a := by
  cases ψ with
  | own v => trivial
  | imm i => exact h
  | «mut» m => exact h

/-- **Fresh instantiations exist**, below every resumer's resource and every lifetime its index
reads: a shift past the finite set's largest value. -/
theorem instFreshExists : InstFreshExists := by
  intro αs R δ αsR lsR c _
  obtain ⟨d, hd⟩ := R.finite
  let atN : BoCa.Loc → ℕ := fun l => match R.get l with
    | some ψ => OrderDual.ofDual ψ.at
    | none => 0
  let N : ℕ := (d.map atN).sum + (αsR.map OrderDual.ofDual).sum + (δ.entries.map Prod.snd).sum +
    (lsR.map fun x => OrderDual.ofDual x.2 + (x.1.δ.entries.map Prod.snd).sum).sum
  have hshift : ∀ a, a < c → N < OrderDual.ofDual (Restrat.Emb.shift c (N + 1) a) := by
    intro a ha
    rw [Restrat.Emb.shift_apply_lt ha]
    omega
  refine ⟨Restrat.Emb.shift c (N + 1), fun a ha => ⟨?_, fun b hb => ?_⟩⟩
  · intro l ψ hψ
    apply CellU.inStratum_of_lt_at
    have hl : l ∈ d := hd l (by rw [hψ]; simp)
    have h₁ : atN l ≤ (d.map atN).sum := nat_le_sum_of_mem (List.mem_map_of_mem hl)
    have h₂ : atN l = OrderDual.ofDual ψ.at := by simp only [atN, hψ]
    have h₃ := hshift a ha
    show OrderDual.ofDual ψ.at < OrderDual.ofDual (Restrat.Emb.shift c (N + 1) a)
    omega
  · have h₃ := hshift a ha
    have hb' : OrderDual.ofDual b ≤ N := by
      rcases hb with hb | ⟨p, hp, rfl⟩ | ⟨x, hx, rfl | ⟨p, hp, rfl⟩⟩
      · have := nat_le_sum_of_mem (List.mem_map_of_mem (f := OrderDual.ofDual) hb)
        omega
      · have := nat_le_sum_of_mem (List.mem_map_of_mem (f := Prod.snd) hp)
        show p.2 ≤ N
        omega
      · have := nat_le_sum_of_mem (List.mem_map_of_mem
          (f := fun x : SRec => OrderDual.ofDual x.2 + (x.1.δ.entries.map Prod.snd).sum) hx)
        omega
      · have h₁ := nat_le_sum_of_mem (List.mem_map_of_mem (f := Prod.snd) hp)
        have h₂ := nat_le_sum_of_mem (List.mem_map_of_mem
          (f := fun x : SRec => OrderDual.ofDual x.2 + (x.1.δ.entries.map Prod.snd).sum) hx)
        show p.2 ≤ N
        omega
    show OrderDual.ofDual b < OrderDual.ofDual (Restrat.Emb.shift c (N + 1) a)
    omega

end ProbeD1

end

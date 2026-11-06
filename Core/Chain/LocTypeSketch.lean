import Core.Chain.Shape791N

/-!
# Location typing per lend: a sketch for #791's step 7  `[spec §62]`

Standalone definitions; nothing here changes a definition the relation reads. The design is
`docs/new-core/scope-791-loctype.md`.

## The world

`LocTy` keys a family by the location *and the lifetime of the lend*: `Θ ℓ b` is the payload family
of the `mut` cell lent at `ℓ` at `b`. A reborrow of `ℓ` at a fresh `α` adds the key `(ℓ, α)` and
leaves `(ℓ, β)`, the source's, alone (`LocTy.add`, `add_keep`). Core's records are one per lend in
the same way (`Core/Relation.lean`, `ls`).

A family stored at `(ℓ, a)` reads the world only above `a` (`famL`, Core's `ls₀`, the records
strictly longer-lived than the cell): the lifetime stratification, not the step index, is what
makes the stored family a fixed function. Lends add keys at a lifetime strictly shorter than every
key present (`LocTy.Fresh`); then the part of the world above every existing key never changes
(`above_add`), so a family stored at a lend stays the payload's family read at the current world
(`fam_add_self`), and a value typed before the lend stays typed (`mutL_add`).

## Its view at a run

The relation's `LocFam` is per location. At a run, each location's live `mut` cell is at one
lifetime (`c : Loc → Option Life`), and the per-location typing the run uses is the view
`Θ.view c`. A lend at `α` is, viewed, `Φ.set ℓ α F`: `view_add`. So the relation's
`rwp_M_frame` at `Φ.set` is already the per-lend lend seen at its run. `UpdN` keeps the lifetimes
of the cells it relates, so a view consistent with a resource is consistent with every resource
`↭` reaches (`consistent_of_updN`).

## What is proved

* **L1** (`reseal_at_entry`, `erwp_antiFrame_view`): a `Mut @β` value of Core's shape at `Θ`, at a
  view whose lifetime at `ℓ` is `β`, gives the existing anti-frame its `hF : Φ ℓ = (β, F)` with
  `F` the payload's family, at `Θ` and at every extension of `Θ` (the reborrow's world); the
  reseal of the content handed back at any lower index is a `MutStep` there, and the resealed cell
  is the same `Mut @β` value at that index. `erwp_antiFrame_view` is `erwp_M_antiFrame` itself,
  applied at the view.
* **L2** (`ext_add`, `add_keep`, `mutL_add`, `coreShapeL_reborrow`): a lend at a fresh lifetime is
  an extension, keeps the source's entry, and keeps every `Mut` value of Core's shape typed;
  `coreShapeL_reborrow` is `coreShape_not_reborrow`'s configuration, which fails per location
  (`Shape791N`), holding per lend.
* **The Kripke order** (`LocTy.ExtA`: entries only added, nothing added above a key present):
  `extA_add`, `extA_trans`, and `Mut` values stable along it (`mutL_extA`).
* **L3, the pieces the port reads besides**: `mutL_of_add` (locality: a value in the lend's
  stratum is typed at the world without the lend, Core's `vC_local`), `fam_add_self` and
  `lend_mutL` (the lend's borrow is a value at the extended world), `view_add`, `view_down`,
  `consistent_of_updN`, `exists_fresh` and `fresh_add` (fresh lifetimes exist at a bounded world,
  which stays bounded).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.LocTypeSketch
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI

/-! ### The world -/

/-- **Location typing per lend**: the family of the cell lent at `ℓ` at `b`. -/
abbrev LocTy : Type := Loc → (b : Life) → Option (Nat → Val → SPropS Loc Val b)

/-- Every family `Θ` assigns is downward closed. -/
def LocTy.Down (Θ : LocTy) : Prop := ∀ l b F, Θ l b = some F → DownFam b F

/-- The Kripke order: entries are only added. -/
def LocTy.Ext (Θ Θ' : LocTy) : Prop := ∀ l b F, Θ l b = some F → Θ' l b = some F

/-- `α` is strictly shorter-lived than every key of `Θ`. -/
def LocTy.Fresh (Θ : LocTy) (α : Life) : Prop := ∀ l b, Θ l b ≠ none → α < b

/-- The entry `(ℓ, α) ↦ F` added; every other key unchanged. -/
def LocTy.add (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) : LocTy :=
  fun x b => if hb : b = α then (if x = l then some (hb ▸ F) else Θ x b) else Θ x b

/-- The entries strictly longer-lived than `a` (Core's `ls₀`). -/
def LocTy.above (Θ : LocTy) (a : Life) : LocTy := fun x b => if a < b then Θ x b else none

theorem add_self (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) :
    Θ.add l α F l α = some F := by
  simp [LocTy.add]

/-- **A lend keeps every other key**, the source's `(ℓ, β)` among them. -/
theorem add_keep (Θ : LocTy) (l : Loc) {α : Life} (F : Nat → Val → SPropS Loc Val α) (x : Loc)
    {b : Life} (hb : b ≠ α) : Θ.add l α F x b = Θ x b := by
  simp [LocTy.add, hb]

theorem add_other (Θ : LocTy) {l x : Loc} (hx : x ≠ l) {α : Life}
    (F : Nat → Val → SPropS Loc Val α) (b : Life) : Θ.add l α F x b = Θ x b := by
  unfold LocTy.add
  split <;> simp_all

/-- **L2 (a): a lend at a fresh lifetime is an extension.** -/
theorem ext_add {Θ : LocTy} {α : Life} (hf : Θ.Fresh α) (l : Loc)
    (F : Nat → Val → SPropS Loc Val α) : Θ.Ext (Θ.add l α F) := by
  intro x b G hG
  have hb : b ≠ α := fun e => by
    have := hf x b (by rw [hG]; simp)
    rw [e] at this
    exact lt_irrefl _ this
  rw [add_keep Θ l F x hb]
  exact hG

/-- The part of the world above `a` is unchanged by a lend at a lifetime not above `a`. -/
theorem above_add (Θ : LocTy) (l : Loc) {α a : Life} (h : ¬ a < α)
    (F : Nat → Val → SPropS Loc Val α) : (Θ.add l α F).above a = Θ.above a := by
  funext x b
  simp only [LocTy.above]
  by_cases hab : a < b
  · have hb : b ≠ α := fun e => h (e ▸ hab)
    simp [hab, add_keep Θ l F x hb]
  · simp [hab]

theorem down_add {Θ : LocTy} (hΘ : Θ.Down) (l : Loc) {α : Life}
    {F : Nat → Val → SPropS Loc Val α} (hF : DownFam α F) : (Θ.add l α F).Down := by
  intro x b G hG
  by_cases hb : b = α
  · subst hb
    by_cases hx : x = l
    · subst hx
      rw [add_self] at hG
      cases hG
      exact hF
    · rw [add_other Θ hx F] at hG
      exact hΘ x _ G hG
  · rw [add_keep Θ l F x hb] at hG
    exact hΘ x b G hG

/-! ### Fresh lifetimes -/

/-- A bounded world: some lifetime is fresh for it. -/
def LocTy.Bounded (Θ : LocTy) : Prop := ∃ N, Θ.Fresh N

theorem fresh_le {Θ : LocTy} {N α : Life} (hN : Θ.Fresh N) (h : α ≤ N) : Θ.Fresh α :=
  fun l b hb => lt_of_le_of_lt h (hN l b hb)

/-- **Fresh lifetimes exist below any bound** at a bounded world. -/
theorem exists_fresh {Θ : LocTy} (hB : Θ.Bounded) (a : Life) : ∃ α, α ≤ a ∧ Θ.Fresh α := by
  obtain ⟨N, hN⟩ := hB
  exact ⟨min N a, min_le_right _ _, fresh_le hN (min_le_left _ _)⟩

/-- **A lend keeps the world bounded.** -/
theorem fresh_add {Θ : LocTy} {N α : Life} (hN : Θ.Fresh N) {N' : Life} (h₁ : N' ≤ N)
    (h₂ : N' < α) (l : Loc) (F : Nat → Val → SPropS Loc Val α) : (Θ.add l α F).Fresh N' := by
  intro x b hb
  by_cases e : b = α
  · exact e ▸ h₂
  · rw [add_keep Θ l F x e] at hb
    exact lt_of_le_of_lt h₁ (hN x b hb)

/-! ### Core's `Mut` over the per-lend world -/

/-- A content predicate read at a world. -/
abbrev CPredL := LocTy → Nat → Val → WRes → Prop

/-- The family stored at a cell at `a`: the payload read at the world above `a`. -/
def famL (a : Life) (P : CPredL) (Θ : LocTy) : Nat → Val → SPropS Loc Val a :=
  fun j u r => P (Θ.above a) j u r.1

/-- **Core's `Mut` clause over the per-lend world**: a location whose cell at `a` holds the member
`j ≥ n` of `famL a P Θ`, the family `Θ` stores at the lend's key `(ℓ, a)`. -/
def mutL (a : Life) (P : CPredL) : CPredL := fun Θ n v ρ =>
  ∃ (l : Loc) (w : Val) (χ : WRes) (hχ : χ.InStratum a) (j : Nat) (hw : famL a P Θ j w ⟨χ, hχ⟩),
    n ≤ j ∧ v = Val.loc l ∧ Θ l a = some (famL a P Θ) ∧
      ρ = ResU.single l (CellU.mutOf a w χ hχ (famL a P Θ j) hw)

/-- `mutL` at `a` reads the world only at the keys at `a` and above `a`. -/
theorem mutL_congr {Θ Θ' : LocTy} {a : Life} (P : CPredL) (h₁ : ∀ x, Θ' x a = Θ x a)
    (h₂ : Θ'.above a = Θ.above a) (n : Nat) (v : Val) (ρ : WRes) :
    mutL a P Θ' n v ρ ↔ mutL a P Θ n v ρ := by
  have hfam : famL a P Θ' = famL a P Θ := by
    funext j u r
    simp only [famL, h₂]
  unfold mutL
  rw [hfam]
  simp only [h₁]

/-- **L2 (b): a `Mut` value of Core's shape stays typed across a lend at a fresh lifetime**, for
every payload. The key it reads is not the lend's (`α` is shorter-lived than it), and nothing is
added above it. -/
theorem mutL_add {Θ : LocTy} {α : Life} (hf : Θ.Fresh α) (l₀ : Loc)
    (F : Nat → Val → SPropS Loc Val α) {a : Life} {P : CPredL} {n : Nat} {v : Val} {ρ : WRes}
    (hm : mutL a P Θ n v ρ) : mutL a P (Θ.add l₀ α F) n v ρ := by
  obtain ⟨l, -, -, -, -, -, -, -, hl, -⟩ := id hm
  have hαa : α < a := hf l a (by rw [hl]; simp)
  refine (mutL_congr P (fun x => add_keep Θ l₀ F x (ne_of_gt hαa))
    (above_add Θ l₀ (not_lt_of_gt hαa) F) n v ρ).mpr hm

/-- **The Kripke order of the interpretation**: entries only added, and nothing added above any
key present. A lend at a fresh lifetime is one step of it (`extA_add`). -/
def LocTy.ExtA (Θ Θ' : LocTy) : Prop :=
  Θ.Ext Θ' ∧ ∀ l a, Θ l a ≠ none → Θ'.above a = Θ.above a

theorem extA_add {Θ : LocTy} {α : Life} (hf : Θ.Fresh α) (l : Loc)
    (F : Nat → Val → SPropS Loc Val α) : Θ.ExtA (Θ.add l α F) :=
  ⟨ext_add hf l F, fun x a ha => above_add Θ l (not_lt_of_gt (hf x a ha)) F⟩

theorem extA_refl (Θ : LocTy) : Θ.ExtA Θ := ⟨fun _ _ _ h => h, fun _ _ _ => rfl⟩

theorem extA_trans {Θ Θ' Θ'' : LocTy} (h₁ : Θ.ExtA Θ') (h₂ : Θ'.ExtA Θ'') : Θ.ExtA Θ'' := by
  refine ⟨fun l b F h => h₂.1 l b F (h₁.1 l b F h), fun l a ha => ?_⟩
  obtain ⟨G, hG⟩ := Option.ne_none_iff_exists'.mp ha
  rw [h₂.2 l a (by rw [h₁.1 l a G hG]; simp), h₁.2 l a ha]

/-- **`Mut` values of Core's shape are stable along the Kripke order.** -/
theorem mutL_extA {Θ Θ' : LocTy} (hE : Θ.ExtA Θ') {a : Life} {P : CPredL} {n : Nat} {v : Val}
    {ρ : WRes} (hm : mutL a P Θ n v ρ) : mutL a P Θ' n v ρ := by
  obtain ⟨l, w, χ, hχ, j, hw, hnj, hv, hl, hρ⟩ := hm
  have hfam : famL a P Θ' = famL a P Θ := by
    funext j u r
    simp only [famL, hE.2 l a (by rw [hl]; simp)]
  unfold mutL
  rw [hfam]
  exact ⟨l, w, χ, hχ, j, hw, hnj, hv, hE.1 l a _ hl, hρ⟩

/-- **L3 (locality)**: a `Mut` value of Core's shape at the world with the lend, whose cell is
longer-lived than the lend, is one at the world without it (Core's `vC_local`; what the lender
reads of a result in the lend's stratum). -/
theorem mutL_of_add {Θ : LocTy} {α a : Life} (hα : α < a) (l₀ : Loc)
    (F : Nat → Val → SPropS Loc Val α) {P : CPredL} {n : Nat} {v : Val} {ρ : WRes}
    (hm : mutL a P (Θ.add l₀ α F) n v ρ) : mutL a P Θ n v ρ :=
  (mutL_congr P (fun x => add_keep Θ l₀ F x (ne_of_gt hα))
    (above_add Θ l₀ (not_lt_of_gt hα) F) n v ρ).mp hm

/-- **The family a lend stores is the payload's family at the extended world**: nothing is above
the fresh `α` but what was there. -/
theorem fam_add_self (Θ : LocTy) (l : Loc) (α : Life) (P : CPredL)
    (F : Nat → Val → SPropS Loc Val α) : famL α P (Θ.add l α F) = famL α P Θ := by
  funext j u r
  simp only [famL, above_add Θ l (lt_irrefl α) F]

/-- **The lend's borrow is a `Mut @α` value at the extended world** (the Mut Frame's `lend_vMut`
in Core's shape). -/
theorem lend_mutL (Θ : LocTy) (l : Loc) (α : Life) (P : CPredL) {n j : Nat} (hnj : n ≤ j)
    {w : Val} {χ : WRes} (hχ : χ.InStratum α) (hw : famL α P Θ j w ⟨χ, hχ⟩) :
    mutL α P (Θ.add l α (famL α P Θ)) n (Val.loc l)
      (ResU.single l (CellU.mutOf α w χ hχ (famL α P Θ j) hw)) := by
  unfold mutL
  rw [fam_add_self]
  exact ⟨l, w, χ, hχ, j, hw, hnj, rfl, add_self Θ l α _, rfl⟩

/-! ### The view at a run -/

/-- **The per-location typing a run uses**: at each location, the entry of the lifetime its live
cell is at. -/
def LocTy.view (Θ : LocTy) (c : Loc → Option Life) : LocFam := fun x =>
  match c x with
  | some b => (Θ x b).map (fun F => ⟨b, F⟩)
  | none => none

theorem view_down {Θ : LocTy} (hΘ : Θ.Down) (c : Loc → Option Life) : (Θ.view c).Down := by
  intro x b G h
  simp only [LocTy.view] at h
  cases hc : c x with
  | none => rw [hc] at h; cases h
  | some b' =>
      rw [hc] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨F, hF, he⟩ := h
      cases he
      exact hΘ _ _ _ hF

/-- The live lifetime of `ℓ` set to `α`. -/
def setLife (c : Loc → Option Life) (l : Loc) (α : Life) : Loc → Option Life :=
  fun x => if x = l then some α else c x

theorem view_some {Θ : LocTy} {c : Loc → Option Life} {l : Loc} {b : Life} (hc : c l = some b)
    {F : Nat → Val → SPropS Loc Val b} (hF : Θ l b = some F) : Θ.view c l = some ⟨b, F⟩ := by
  simp [LocTy.view, hc, hF]

/-- **L3: the relation's `Φ.set` at a lend is the view of the per-lend lend.** -/
theorem view_add (Θ : LocTy) (c : Loc → Option Life) (l : Loc) (α : Life)
    (F : Nat → Val → SPropS Loc Val α) :
    (Θ.add l α F).view (setLife c l α) = (Θ.view c).set l α F := by
  funext x
  by_cases hx : x = l
  · subst hx
    simp [LocTy.view, setLife, LocFam.set, add_self]
  · simp only [LocTy.view, setLife, LocFam.set, if_neg hx]
    cases c x with
    | none => rfl
    | some b => simp [add_other Θ hx F b]

/-- A view is consistent with a resource when it gives each `mut` cell of the flattening its own
lifetime. -/
def Consistent (c : Loc → Option Life) (ρ : WRes) : Prop :=
  ∀ l ψ, ρ.FlatAt l ψ → ψ.kind = Kind.mut → c l = some ψ.at

/-- **L3: `↭` keeps a view consistent**: `UpdMutN`'s second clause gives every `mut` cell after
the step a `mut` cell before it at the same lifetime. -/
theorem consistent_of_updN {Φ : LocFam} {n : Nat} {ρ₁ ρ₂ : WRes} (h : UpdN Φ n ρ₁ ρ₂)
    {c : Loc → Option Life} (hc : Consistent c ρ₁) : Consistent c ρ₂ := by
  intro l ψ' hg hk
  obtain ⟨ψ, hg₁, hs⟩ := h.2.2 l ψ' hg hk
  rw [← hs.2.2.1]
  exact hc l ψ hg₁ hs.1

/-- `MutStep` reads its location typing only at its location. -/
theorem mutStep_congr {Φ Φ' : LocFam} {n : Nat} {l : Loc} (h : Φ' l = Φ l)
    {ψ ψ' : CellU Loc Val} (hs : MutStep Φ n l ψ ψ') : MutStep Φ' n l ψ ψ' :=
  ⟨hs.1, hs.2.1, hs.2.2.1, fun hn => hs.2.2.2.1 (h ▸ hn),
    fun b F hF => hs.2.2.2.2 b F (h ▸ hF)⟩

/-! ### L1: the reseal at the original entry -/

/-- **L1: the reseal at the original entry.** A `Mut @β` value of Core's shape at `Θ`, at a view
whose lifetime at `ℓ` is `β`, at any extension `Θ′` of `Θ` (the reborrow's world among them):
the view types `ℓ` with the payload's family (the anti-frame's `hF`); resealing the content
handed back at any `k`, read at any `m ≤ k`, is a `MutStep` there; and the resealed cell is the
same `Mut @β` value at `k`. Contrast `Shape791N.reseal_untyped`, where `Φ ℓ = none` forces the
stored predicate unchanged. -/
theorem reseal_at_entry {Θ Θ' : LocTy} (hE : Θ.Ext Θ') {c : Loc → Option Life} {l : Loc}
    {β : Life} (hc : c l = some β) {P : CPredL} (hd : DownFam β (famL β P Θ)) {n : Nat}
    {ρ : WRes} (hm : mutL β P Θ n (Val.loc l) ρ) :
    ∃ (w : Val) (χ : WRes) (hχ : χ.InStratum β) (j : Nat) (hw : famL β P Θ j w ⟨χ, hχ⟩),
      n ≤ j ∧ ρ = ResU.single l (CellU.mutOf β w χ hχ (famL β P Θ j) hw) ∧
      Θ'.view c l = some ⟨β, famL β P Θ⟩ ∧
      ∀ k m, m ≤ k → ∀ (w' : Val) (σ' : WRes) (hσ' : σ'.InStratum β)
        (hw' : famL β P Θ k w' ⟨σ', hσ'⟩),
        MutStep (Θ'.view c) m l (CellU.mutOf β w χ hχ (famL β P Θ j) hw)
          (CellU.mutOf β w' σ' hσ' (famL β P Θ k) hw') ∧
        mutL β P Θ k (Val.loc l) (ResU.single l (CellU.mutOf β w' σ' hσ' (famL β P Θ k) hw')) := by
  obtain ⟨l', w, χ, hχ, j, hw, hnj, hv, hl, rfl⟩ := hm
  obtain rfl : l = l' := by
    have := congrArg Subtype.val hv
    simpa [Val.loc] using this
  have hview : Θ'.view c l = some ⟨β, famL β P Θ⟩ := view_some hc (hE l β _ hl)
  refine ⟨w, χ, hχ, j, hw, hnj, rfl, hview, fun k m hmk w' σ' hσ' hw' => ⟨?_, ?_⟩⟩
  · -- `mutStep_write` at the one-entry typing `ℓ ↦ (β, F)`, read at the view
    let Φ₀ : LocFam := LocFam.set (fun _ => none) l β (famL β P Θ)
    have hΦ₀ : Φ₀.Down := LocFam.set_down (fun _ _ _ h => by cases h) hd
    have hF₀ : Φ₀ l = some ⟨β, famL β P Θ⟩ := by simp [Φ₀, LocFam.set]
    exact mutStep_congr (hview.trans hF₀.symm) (mutStep_write hΦ₀ hF₀ hmk)
  · exact ⟨l, w', σ', hσ', k, hw', le_rfl, rfl, hl, rfl⟩

/-- **L1 at the relation: `erwp_M_antiFrame` itself, at the view.** A `Mut @β` value of Core's
shape at `Θ` is opened by the existing anti-frame at `Θ.view c` when `c ℓ = β`: the per-lend
world supplies `hF`, which neither `vN` nor Core's interpretation supplies per location
(`scope-791-rule.md` §7.2). -/
theorem erwp_antiFrame_view {Θ : LocTy} {c : Loc → Option Life} (hΦ : (Θ.view c).Down)
    {l : Loc} {β : Life} (hc : c l = some β) {P : CPredL} {T : OpTabN} (hT : T.AFOK)
    {Q : PostN} {n : Nat} {ls : List SRec} {e : Expr} {ρm ρa ρ : WRes}
    (hm : mutL β P Θ n (Val.loc l) ρm) (hsplit : ResU.CompS ρm ρa ρ)
    (hA : ∀ (w : Val) (χ : WRes), (∃ (hχ : χ.InStratum β) (j : Nat), n ≤ j ∧
        famL β P Θ j w ⟨χ, hχ⟩) → ∀ W X,
      ResU.CompS χ (ResU.single l (CellU.ownOf w)) W → ResU.CompS ρa W X →
      erwp (ℍ := ℍ) (Θ.view c) (opTableG T (CellFold l β (famL β P Θ)))
        (AFPost l β (famL β P Θ) Q) n ls e X) :
    erwp (ℍ := ℍ) (Θ.view c) (opTableN T) Q n ls e ρ := by
  obtain ⟨l', w, χ, hχ, j, hw, hnj, hv, hl, rfl⟩ := hm
  obtain rfl : l = l' := by
    have := congrArg Subtype.val hv
    simpa [Val.loc] using this
  exact erwp_M_antiFrame hΦ (view_some hc hl) hT n ls e w χ hχ j hw ρa ρ hsplit
    (fun W X hW hX => hA w χ ⟨hχ, j, hnj, hw⟩ W X hW hX)

/-- **The reborrow's world keeps the source's entry** and its view is the relation's
`Φ.set ℓ α Fi`, the location typing `erwp_withbor3` runs its callback at. -/
theorem reborrow_view {Θ : LocTy} {α β : Life} (hf : Θ.Fresh α) {l : Loc}
    {Fo : Nat → Val → SPropS Loc Val β} (hl : Θ l β = some Fo) (c : Loc → Option Life)
    (Fi : Nat → Val → SPropS Loc Val α) :
    Θ.Ext (Θ.add l α Fi) ∧ Θ.add l α Fi l β = some Fo ∧
      (Θ.add l α Fi).view (setLife c l α) = (Θ.view c).set l α Fi :=
  ⟨ext_add hf l Fi, ext_add hf l Fi l β Fo hl, view_add Θ c l α Fi⟩

/-! ### L2 (c): `coreShape_not_reborrow`'s configuration, per lend -/

/-- `𝒱⟦1⟧`. -/
def unitL : CPredL := fun _ _ v ρ => v = Val.unit ∧ ρ = PMap.empty

theorem famL_unit (b : Life) (Θ : LocTy) : famL b unitL Θ = Shape791N.famUnit b := rfl

/-- `ℓ` and `ℓ₂` lent at `β` with `𝒱⟦1⟧`'s family. -/
def W₁ (l l₂ : Loc) (β : Life) : LocTy := fun x b =>
  if (x = l ∨ x = l₂) ∧ b = β then some (Shape791N.famUnit b) else none

/-- …and `ℓ_b` lent at `b` with `𝒱⟦Mut @β 1⟧`'s, read above `b`. -/
def Wc (l l₂ lb : Loc) (b β : Life) : LocTy := fun x a =>
  if x = lb ∧ a = b then some (famL a (mutL β unitL) (W₁ l l₂ β)) else W₁ l l₂ β x a

theorem Wc_above (l l₂ lb : Loc) (hl : lb ≠ l) (hl₂ : lb ≠ l₂) (b β : Life) :
    (Wc l l₂ lb b β).above b = (W₁ l l₂ β).above b := by
  funext x a
  simp only [LocTy.above, Wc]
  by_cases h : x = lb ∧ a = b
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp [h]

theorem Wc_fresh (l l₂ lb : Loc) {α b β : Life} (hαb : α < b) (hbβ : b < β) :
    (Wc l l₂ lb b β).Fresh α := by
  intro x a ha
  simp only [Wc, W₁] at ha
  by_cases h : x = lb ∧ a = b
  · rw [h.2]; exact hαb
  · rw [if_neg h] at ha
    by_cases h' : (x = l ∨ x = l₂) ∧ a = β
    · rw [h'.2]; exact lt_trans hαb hbβ
    · exact absurd (if_neg h') ha

/-- **`coreShape_not_reborrow`'s configuration holds per lend.** The same value (a `Mut @b
(Mut @β 1)` at `ℓ_b`, its content a `Mut @β 1` at `ℓ₂`, holding nothing at `ℓ`) is one of Core's
shape at `Wc` and at `Wc` with `ℓ` lent at any `α < b < β` with any family: the per-location
typing loses `ℓ` above `b` (`Shape791N.coreShape_not_reborrow`), the per-lend typing keeps it. -/
theorem coreShapeL_reborrow (l l₂ lb : Loc) (hl : lb ≠ l) (hl₂ : lb ≠ l₂) {α b β : Life}
    (hαb : α < b) (hbβ : b < β) (F : Nat → Val → SPropS Loc Val α) :
    ∃ (v : Val) (ρ : WRes),
      (∀ x ψ, ρ.get x = some ψ → x ≠ l) ∧
      mutL b (mutL β unitL) (Wc l l₂ lb b β) 0 v ρ ∧
      mutL b (mutL β unitL) ((Wc l l₂ lb b β).add l α F) 0 v ρ := by
  have hfam : famL b (mutL β unitL) (Wc l l₂ lb b β) = famL b (mutL β unitL) (W₁ l l₂ β) := by
    funext j u r
    simp only [famL, Wc_above l l₂ lb hl hl₂ b β]
  -- the content: `ℓ₂ ↦ mut(β, (), ∅, 𝒱⟦1⟧)`, typed at `W₁` above `b`
  have hin : mutL β unitL ((W₁ l l₂ β).above b) 0 (Val.loc l₂) (Shape791N.innerCell l₂ β) := by
    refine ⟨l₂, Val.unit, PMap.empty, ResU.inStratum_empty β, 0, ⟨rfl, rfl⟩, le_rfl, rfl, ?_, rfl⟩
    simp [LocTy.above, W₁, hbβ, famL_unit]
  have hw : famL b (mutL β unitL) (Wc l l₂ lb b β) 0 (Val.loc l₂)
      ⟨Shape791N.innerCell l₂ β, Shape791N.innerCell_inStratum l₂ hbβ⟩ := by
    rw [hfam]; exact hin
  have hv : mutL b (mutL β unitL) (Wc l l₂ lb b β) 0 (Val.loc lb)
      (ResU.single lb (CellU.mutOf b (Val.loc l₂) (Shape791N.innerCell l₂ β)
        (Shape791N.innerCell_inStratum l₂ hbβ) _ hw)) := by
    refine ⟨lb, _, _, _, 0, hw, le_rfl, rfl, ?_, rfl⟩
    simp only [Wc, and_self, if_true, hfam]
  refine ⟨_, _, fun x ψ hx => ?_, hv, mutL_add (Wc_fresh l l₂ lb hαb hbβ) l F hv⟩
  by_cases h : x = lb
  · rw [h]; exact hl
  · rw [ResU.single_get_ne _ h] at hx; exact absurd hx (by simp)

end BoCa.Fig16.LogRel.Core.Chain.SI.LocTypeSketch

end

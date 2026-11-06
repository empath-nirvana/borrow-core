import Core.Chain.SI.AntiStopN
import Core.Chain.SI.MutSemN

/-!
# Location typing per lend: the world the #791 interpretation reads  `[spec §62]`

The design is `docs/new-core/scope-791-loctype.md`.

## The world

`LocTy` keys a family by the location *and the lifetime of the lend*: `Θ ℓ b` is the payload family
of the `mut` cell lent at `ℓ` at `b`. A reborrow of `ℓ` at a fresh `α` adds the key `(ℓ, α)` and
leaves `(ℓ, β)`, the source's, alone (`LocTy.add`, `LocTy.add_keep`). Core's records are one per
lend in the same way (`Core/FrameRecords.lean`, `SRec`).

A family stored at `(ℓ, a)` reads the world only above `a` (`famL`, Core's `ls₀` in `ptoMutS`):
the lifetime stratification, not the step index, makes the stored family a fixed function. Lends
add keys at a lifetime strictly shorter than every key present (`LocTy.Fresh`); then the part of
the world above every existing key never changes (`LocTy.above_add`), so a family stored at a
lend stays the payload's family read at the current world (`fam_add_self`), and a value typed
before the lend stays typed (`mutL_add`). The Kripke order is `LocTy.ExtA`: entries only added,
nothing added above a key present.

## Its view at a run

The relation's `LocFam` is per location. At a run, each location's live `mut` cell is at one
lifetime (`c : Loc → Option Life`), and the per-location typing the run uses is the view
`Θ.view c`. A lend at `α` is, viewed, `Φ.set ℓ α F` (`LocTy.view_add`), so the relation's lend
frames stated at `Φ.set` are the per-lend lend seen at its run; nothing in the relation changes.

## Consistency

`ConsistentX c ρ`: every `mut` cell of `ρ`'s exclusive walk `ex(ρ)` is at `c ℓ`. A `Mut` argument
is a top-level `mut` cell, so it is in the exclusive walk; cells beneath an `imm` cell are in the
aliasable walk and are read-only. `ConsistentX` is kept by a run: the resource a run returns is
consistent when the one it started from is (`erwp_consistent`). The proof follows a returned
exclusive `mut` cell into the post-configuration's flattening, back across `↭` (`UpdMutN`'s second
clause), and, where `↭` finds it in the aliasable walk, to its `imm` ancestor
(`AgW.nonimm_beneath_imm`), which `↭` keeps (`upd_ag_imm_wit_factorI`); the ancestor puts the
location in the post-configuration's aliasable walk, where the exclusive cell cannot be.

`Consistent` (every `mut` cell of the whole flattening) is the design's first reading; it is kept
by `↭` on the whole resource (`consistent_of_updN`) but not by taking a part of it: a `mut` cell
beneath an `imm` ancestor is hidden in the flattening by an `imm` cell at its location held
elsewhere (`CellU.CompR.mutImm`), and appears when the part is taken alone
(`Core/Chain/ConsistentFlat791.lean`).

## What the interpretation reads besides

* **L1** (`reseal_at_entry`, `erwp_antiFrame_view`): a `Mut @β` value of Core's shape at `Θ`, at a
  view whose lifetime at `ℓ` is `β`, gives the existing anti-frame its `hF : Φ ℓ = (β, F)`.
* **L2** (`LocTy.ext_add`, `LocTy.add_keep`, `mutL_add`, `mutL_extA`): a lend at a fresh
  lifetime is an extension, keeps the source's entry, and keeps every `Mut` value of Core's shape
  typed.
* `mutL_of_add` (locality of `Mut` in the lend's stratum), `fam_add_self`, `lend_mutL`,
  `LocTy.exists_fresh`, `LocTy.fresh_add`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core

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

theorem LocTy.add_self (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) :
    Θ.add l α F l α = some F := by
  simp [LocTy.add]

/-- **A lend keeps every other key**, the source's `(ℓ, β)` among them. -/
theorem LocTy.add_keep (Θ : LocTy) (l : Loc) {α : Life} (F : Nat → Val → SPropS Loc Val α) (x : Loc)
    {b : Life} (hb : b ≠ α) : Θ.add l α F x b = Θ x b := by
  simp [LocTy.add, hb]

theorem LocTy.add_other (Θ : LocTy) {l x : Loc} (hx : x ≠ l) {α : Life}
    (F : Nat → Val → SPropS Loc Val α) (b : Life) : Θ.add l α F x b = Θ x b := by
  unfold LocTy.add
  split <;> simp_all

/-- **L2 (a): a lend at a fresh lifetime is an extension.** -/
theorem LocTy.ext_add {Θ : LocTy} {α : Life} (hf : Θ.Fresh α) (l : Loc)
    (F : Nat → Val → SPropS Loc Val α) : Θ.Ext (Θ.add l α F) := by
  intro x b G hG
  have hb : b ≠ α := fun e => by
    have := hf x b (by rw [hG]; simp)
    rw [e] at this
    exact lt_irrefl _ this
  rw [LocTy.add_keep Θ l F x hb]
  exact hG

/-- The part of the world above `a` is unchanged by a lend at a lifetime not above `a`. -/
theorem LocTy.above_add (Θ : LocTy) (l : Loc) {α a : Life} (h : ¬ a < α)
    (F : Nat → Val → SPropS Loc Val α) : (Θ.add l α F).above a = Θ.above a := by
  funext x b
  simp only [LocTy.above]
  by_cases hab : a < b
  · have hb : b ≠ α := fun e => h (e ▸ hab)
    simp [hab, LocTy.add_keep Θ l F x hb]
  · simp [hab]

theorem LocTy.down_add {Θ : LocTy} (hΘ : Θ.Down) (l : Loc) {α : Life}
    {F : Nat → Val → SPropS Loc Val α} (hF : DownFam α F) : (Θ.add l α F).Down := by
  intro x b G hG
  by_cases hb : b = α
  · subst hb
    by_cases hx : x = l
    · subst hx
      rw [LocTy.add_self] at hG
      cases hG
      exact hF
    · rw [LocTy.add_other Θ hx F] at hG
      exact hΘ x _ G hG
  · rw [LocTy.add_keep Θ l F x hb] at hG
    exact hΘ x b G hG

/-! ### Fresh lifetimes -/

/-- A bounded world: some lifetime is fresh for it. -/
def LocTy.Bounded (Θ : LocTy) : Prop := ∃ N, Θ.Fresh N

theorem LocTy.fresh_le {Θ : LocTy} {N α : Life} (hN : Θ.Fresh N) (h : α ≤ N) : Θ.Fresh α :=
  fun l b hb => lt_of_le_of_lt h (hN l b hb)

/-- **Fresh lifetimes exist below any bound** at a bounded world. -/
theorem LocTy.exists_fresh {Θ : LocTy} (hB : Θ.Bounded) (a : Life) : ∃ α, α ≤ a ∧ Θ.Fresh α := by
  obtain ⟨N, hN⟩ := hB
  exact ⟨min N a, min_le_right _ _, LocTy.fresh_le hN (min_le_left _ _)⟩

/-- **A lend keeps the world bounded.** -/
theorem LocTy.fresh_add {Θ : LocTy} {N α : Life} (hN : Θ.Fresh N) {N' : Life} (h₁ : N' ≤ N)
    (h₂ : N' < α) (l : Loc) (F : Nat → Val → SPropS Loc Val α) : (Θ.add l α F).Fresh N' := by
  intro x b hb
  by_cases e : b = α
  · exact e ▸ h₂
  · rw [LocTy.add_keep Θ l F x e] at hb
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
  refine (mutL_congr P (fun x => LocTy.add_keep Θ l₀ F x (ne_of_gt hαa))
    (LocTy.above_add Θ l₀ (not_lt_of_gt hαa) F) n v ρ).mpr hm

/-- **The Kripke order of the interpretation**: entries only added, and nothing added above any
key present. A lend at a fresh lifetime is one step of it (`LocTy.extA_add`). -/
def LocTy.ExtA (Θ Θ' : LocTy) : Prop :=
  Θ.Ext Θ' ∧ ∀ l a, Θ l a ≠ none → Θ'.above a = Θ.above a

theorem LocTy.extA_add {Θ : LocTy} {α : Life} (hf : Θ.Fresh α) (l : Loc)
    (F : Nat → Val → SPropS Loc Val α) : Θ.ExtA (Θ.add l α F) :=
  ⟨LocTy.ext_add hf l F, fun x a ha => LocTy.above_add Θ l (not_lt_of_gt (hf x a ha)) F⟩

theorem LocTy.extA_refl (Θ : LocTy) : Θ.ExtA Θ := ⟨fun _ _ _ h => h, fun _ _ _ => rfl⟩

theorem LocTy.extA_trans {Θ Θ' Θ'' : LocTy} (h₁ : Θ.ExtA Θ') (h₂ : Θ'.ExtA Θ'') : Θ.ExtA Θ'' := by
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
  (mutL_congr P (fun x => LocTy.add_keep Θ l₀ F x (ne_of_gt hα))
    (LocTy.above_add Θ l₀ (not_lt_of_gt hα) F) n v ρ).mp hm

/-- **The family a lend stores is the payload's family at the extended world**: nothing is above
the fresh `α` but what was there. -/
theorem fam_add_self (Θ : LocTy) (l : Loc) (α : Life) (P : CPredL)
    (F : Nat → Val → SPropS Loc Val α) : famL α P (Θ.add l α F) = famL α P Θ := by
  funext j u r
  simp only [famL, LocTy.above_add Θ l (lt_irrefl α) F]

/-- **The lend's borrow is a `Mut @α` value at the extended world** (the Mut Frame's `lend_vMut`
in Core's shape). -/
theorem lend_mutL (Θ : LocTy) (l : Loc) (α : Life) (P : CPredL) {n j : Nat} (hnj : n ≤ j)
    {w : Val} {χ : WRes} (hχ : χ.InStratum α) (hw : famL α P Θ j w ⟨χ, hχ⟩) :
    mutL α P (Θ.add l α (famL α P Θ)) n (Val.loc l)
      (ResU.single l (CellU.mutOf α w χ hχ (famL α P Θ j) hw)) := by
  unfold mutL
  rw [fam_add_self]
  exact ⟨l, w, χ, hχ, j, hw, hnj, rfl, LocTy.add_self Θ l α _, rfl⟩

/-! ### The view at a run -/

/-- **The per-location typing a run uses**: at each location, the entry of the lifetime its live
cell is at. -/
def LocTy.view (Θ : LocTy) (c : Loc → Option Life) : LocFam := fun x =>
  match c x with
  | some b => (Θ x b).map (fun F => ⟨b, F⟩)
  | none => none

theorem LocTy.view_down {Θ : LocTy} (hΘ : Θ.Down) (c : Loc → Option Life) : (Θ.view c).Down := by
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

theorem LocTy.view_some {Θ : LocTy} {c : Loc → Option Life} {l : Loc} {b : Life} (hc : c l = some b)
    {F : Nat → Val → SPropS Loc Val b} (hF : Θ l b = some F) : Θ.view c l = some ⟨b, F⟩ := by
  simp [LocTy.view, hc, hF]

/-- **L3: the relation's `Φ.set` at a lend is the view of the per-lend lend.** -/
theorem LocTy.view_add (Θ : LocTy) (c : Loc → Option Life) (l : Loc) (α : Life)
    (F : Nat → Val → SPropS Loc Val α) :
    (Θ.add l α F).view (setLife c l α) = (Θ.view c).set l α F := by
  funext x
  by_cases hx : x = l
  · subst hx
    simp [LocTy.view, setLife, LocFam.set, LocTy.add_self]
  · simp only [LocTy.view, setLife, LocFam.set, if_neg hx]
    cases c x with
    | none => rfl
    | some b => simp [LocTy.add_other Θ hx F b]

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
  have hview : Θ'.view c l = some ⟨β, famL β P Θ⟩ := LocTy.view_some hc (hE l β _ hl)
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
  exact erwp_M_antiFrame hΦ (LocTy.view_some hc hl) hT n ls e w χ hχ j hw ρa ρ hsplit
    (fun W X hW hX => hA w χ ⟨hχ, j, hnj, hw⟩ W X hW hX)

/-- **The reborrow's world keeps the source's entry** and its view is the relation's
`Φ.set ℓ α Fi`, the location typing `erwp_withbor3` runs its callback at. -/
theorem reborrow_view {Θ : LocTy} {α β : Life} (hf : Θ.Fresh α) {l : Loc}
    {Fo : Nat → Val → SPropS Loc Val β} (hl : Θ l β = some Fo) (c : Loc → Option Life)
    (Fi : Nat → Val → SPropS Loc Val α) :
    Θ.Ext (Θ.add l α Fi) ∧ Θ.add l α Fi l β = some Fo ∧
      (Θ.add l α Fi).view (setLife c l α) = (Θ.view c).set l α Fi :=
  ⟨LocTy.ext_add hf l Fi, LocTy.ext_add hf l Fi l β Fo hl, LocTy.view_add Θ c l α Fi⟩


/-! ### The empty world, and the view along the Kripke order -/

/-- The world with no entries. -/
def LocTy.empty : LocTy := fun _ _ => none

theorem LocTy.empty_down : LocTy.empty.Down := fun _ _ _ h => by cases h

theorem LocTy.empty_bounded : LocTy.empty.Bounded := ⟨0, fun _ _ h => absurd rfl h⟩

/-- A world an interpretation runs at: its families downward closed, and a lifetime fresh for
it (`LocTy.exists_fresh`). -/
def LocTy.OK (Θ : LocTy) : Prop := Θ.Down ∧ Θ.Bounded

theorem LocTy.empty_ok : LocTy.empty.OK := ⟨LocTy.empty_down, LocTy.empty_bounded⟩

/-- The view of the empty world types nothing. -/
theorem LocTy.view_empty (c : Loc → Option Life) : LocTy.empty.view c = fun _ => none := by
  funext x
  simp only [LocTy.view, LocTy.empty]
  cases c x <;> rfl

theorem LocTy.ext_of_extA {Θ Θ' : LocTy} (h : Θ.ExtA Θ') : Θ.Ext Θ' := h.1

/-- **The view grows along the Kripke order**: `LocFam.Ext`, the order `erwp_extΦ` reads. -/
theorem LocTy.view_ext {Θ Θ' : LocTy} (h : Θ.Ext Θ') (c : Loc → Option Life) :
    LocFam.Ext (Θ.view c) (Θ'.view c) := by
  intro x y hx
  simp only [LocTy.view] at hx ⊢
  cases hc : c x with
  | none => rw [hc] at hx; cases hx
  | some b =>
      rw [hc] at hx
      simp only at hx ⊢
      obtain ⟨F, hF, rfl⟩ := Option.map_eq_some_iff.mp hx
      rw [h x b F hF]
      rfl

/-! ### Consistency on the exclusive walk -/

/-- **A view is consistent with a resource** when it gives each `mut` cell of the resource's
exclusive walk its own lifetime. -/
def ConsistentX (c : Loc → Option Life) (ρ : WRes) : Prop :=
  ∀ e, ExS ρ e → ∀ l ψ, e.get l = some ψ → ψ.kind = Kind.mut → c l = some ψ.at

/-- A cell of a strict composite that is not `imm`, held by the left operand, is the
composite's, and the right operand holds nothing there. -/
theorem compS_get_left_nonimm {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ) {l : Loc}
    {ψ : CellU Loc Val} (e : ρ₁.get l = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    ρ₂.get l = none ∧ ρ.get l = some ψ := by
  rcases ResU.Comp.get h l with ⟨f₁, -, -⟩ | ⟨ζ, f₁, f₂, f⟩ | ⟨ζ, f₁, -, -⟩ |
      ⟨ζ₁, ζ₂, ζ, f₁, f₂, -, -⟩
  · rw [e] at f₁; cases f₁
  · rw [e] at f₁; cases Option.some.inj f₁; exact ⟨f₂, f⟩
  · rw [e] at f₁; cases f₁
  · rw [e] at f₁; cases Option.some.inj f₁
    exact absurd (CellU.CompatS.kinds (h.1 l _ ζ₂ e f₂)).1 hk

theorem consistentX_empty (c : Loc → Option Life) : ConsistentX c PMap.empty := by
  intro e he l ψ hg _
  obtain rfl : e = PMap.empty := ExS.functional he exW_empty
  cases hg

/-- **Consistency of a composite from its operands'.** -/
theorem consistentX_compS {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ) {c : Loc → Option Life}
    (h₁ : ConsistentX c ρ₁) (h₂ : ConsistentX c ρ₂) : ConsistentX c ρ := by
  intro e he l ψ hg hk
  obtain ⟨e₁, e₂, he₁, he₂, hc⟩ := (ExS.split h).mp he
  rcases ResU.Comp.get hc l with ⟨-, -, f⟩ | ⟨ζ, f₁, -, f⟩ | ⟨ζ, -, f₂, f⟩ |
      ⟨ζ₁, ζ₂, ζ, f₁, f₂, -, -⟩
  · rw [hg] at f; cases f
  · rw [hg] at f; cases Option.some.inj f; exact h₁ e₁ he₁ l _ f₁ hk
  · rw [hg] at f; cases Option.some.inj f; exact h₂ e₂ he₂ l _ f₂ hk
  · exact absurd (CellU.CompatS.kinds (hc.1 l ζ₁ ζ₂ f₁ f₂)).1 (ExS.immFree he₁ l ζ₁ f₁)

/-- **Consistency of an operand from the composite's.** -/
theorem consistentX_left {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ) {c : Loc → Option Life}
    (hc : ConsistentX c ρ) (hv : ResU.Valid ρ) : ConsistentX c ρ₁ := by
  intro e₁ he₁ l ψ hg hk
  obtain ⟨σ, e, a, he, -, -⟩ := hv
  obtain ⟨e₁', e₂, he₁', he₂, hc'⟩ := (ExS.split h).mp he
  obtain rfl := ExS.functional he₁ he₁'
  exact hc e he l ψ (compS_get_left_nonimm hc' hg (by rw [hk]; decide)).2 hk

theorem consistentX_right {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ) {c : Loc → Option Life}
    (hc : ConsistentX c ρ) (hv : ResU.Valid ρ) : ConsistentX c ρ₂ :=
  consistentX_left (ResU.CompS.comm h) hc hv

/-- **A consistent view gives a held `mut` cell its lifetime**: a top-level `mut` cell of a valid
resource is in its exclusive walk, so a consistent view is at the cell's lifetime there (the
anti-frame's `c ℓ = β`, `erwp_antiFrame_view`). -/
theorem consistentX_get {ρ : WRes} {c : Loc → Option Life} (hc : ConsistentX c ρ)
    (hv : ResU.Valid ρ) {l : Loc} {ψ : CellU Loc Val} (e : ρ.get l = some ψ)
    (hk : ψ.kind = Kind.mut) : c l = some ψ.at := by
  obtain ⟨σ, ex, a, hex, -, -⟩ := hv
  exact hc ex hex l ψ (ExS.get_of_ne_imm hex e (by rw [hk]; decide)) hk

/-- The ancestor transfer (`ResU.upd_ag_imm_wit_factor`) from `↭`'s `imm` clause alone, the
only clause its proof reads. -/
theorem upd_ag_imm_wit_factorI {ρ₂ ρ₃ e₂ a₂ σ₂ e₃ a₃ σ₃ : WRes}
    (h : ResU.UpdImm ρ₂ ρ₃)
    (he₂ : ExS ρ₂ e₂) (ha₂ : AgW ρ₂ a₂) (hc₂ : ResU.CompS e₂ a₂ σ₂)
    (he₃ : ExS ρ₃ e₃) (ha₃ : AgW ρ₃ a₃) (hc₃ : ResU.CompS e₃ a₃ σ₃)
    {m : Loc} {s : LSet} {u : Val} {χ : WRes} {hh : χ.InStratum s.join}
    (hg : a₂.get m = some (CellU.immOf s u χ hh)) :
    ∃ ev av p z, ExR χ ev ∧ AgW χ av ∧ ResU.CompR ev av p ∧ ResU.CompR p z a₃ := by
  have hex : e₂.get m = none := by
    cases f : e₂.get m with
    | none => rfl
    | some ξ =>
        exact absurd (CellU.CompatS.kinds (hc₂.1 m ξ _ f hg)).1 (ExS.immFree he₂ m ξ f)
  have hσ₂ : σ₂.get m = some (CellU.immOf s u χ hh) := by
    rw [ResU.Comp.get_of_left_none hc₂ hex, hg]
  have hσ₃ : σ₃.get m = some (CellU.immOf s u χ hh) :=
    (ResU.flatAt_iff ⟨e₃, a₃, he₃, ha₃, hc₃⟩ m _).mp
      ((h m s u χ hh).mp ((ResU.flatAt_iff ⟨e₂, a₂, he₂, ha₂, hc₂⟩ m _).mpr hσ₂))
  exact ResU.flat_imm_wit_factor he₃ ha₃ hc₃ hσ₃

/-- **`↭` keeps consistency on the part of the post-configuration that is returned.** A `mut`
cell of the returned part's exclusive walk is in the post-configuration's flattening; `↭`'s
second `mut` clause finds a `mut` cell at the same lifetime in the flattening of the resource
the step started from. That cell is in the start's exclusive walk, where consistency gives its
lifetime; or in its aliasable walk, beneath an `imm` ancestor that `↭` keeps, and then the
post-configuration's aliasable walk holds the location, which its exclusive walk does. -/
theorem consistentX_of_updN {Φ : LocFam} {n : Nat} {ρ π ρ' ρp : WRes} (hu : UpdN Φ n ρ π)
    (hvπ : ResU.Valid π) (hs : ResU.CompS ρ' ρp π) {c : Loc → Option Life}
    (hc : ConsistentX c ρ) : ConsistentX c ρ' := by
  intro e' he' l ψ hg hk
  have hkn : ψ.kind ≠ Kind.imm := by rw [hk]; decide
  obtain ⟨σπ, eπ, aπ, heπ, haπ, hcπ⟩ := hvπ
  obtain ⟨e₁, e₂, he₁, he₂, hc12⟩ := (ExS.split hs).mp heπ
  obtain rfl := ExS.functional he' he₁
  obtain ⟨-, heπl⟩ := compS_get_left_nonimm hc12 hg hkn
  obtain ⟨haπl, hσl⟩ := compS_get_left_nonimm hcπ heπl hkn
  obtain ⟨ψ₀, hρ₀, hst⟩ := hu.2.2 l ψ ⟨σπ, ⟨eπ, aπ, heπ, haπ, hcπ⟩, hσl⟩ hk
  obtain ⟨hk₀, -, hat, -⟩ := hst
  rw [← hat]
  obtain ⟨σρ, ⟨eρ, aρ, heρ, haρ, hcρ⟩, hσρ⟩ := hρ₀
  rcases ResU.Comp.get hcρ l with ⟨-, -, f⟩ | ⟨ζ, f₁, -, f⟩ | ⟨ζ, -, f₂, f⟩ |
      ⟨ζ₁, ζ₂, ζ, f₁, f₂, -, -⟩
  · rw [hσρ] at f; cases f
  · rw [hσρ] at f; cases Option.some.inj f
    exact hc eρ heρ l _ f₁ hk₀
  · rw [hσρ] at f; cases Option.some.inj f
    obtain ⟨m, s, u, χ, hh, ev, av, p, ξ, hm, hev, hav, hp, hpl, -, -, -⟩ :=
      AgW.nonimm_beneath_imm haρ l _ f₂ (by rw [hk₀]; decide)
    obtain ⟨ev', av', p', z, hev', hav', hp', hz⟩ :=
      upd_ag_imm_wit_factorI hu.1 heρ haρ hcρ heπ haπ hcπ hm
    rw [ExR.functional hev' hev, AgW.functional hav' hav] at hp'
    rw [ResU.CompR.functional hp' hp] at hz
    have := ((ResU.Comp.eq_none_iff hz l).mp haπl).1
    rw [hpl] at this; cases this
  · exact absurd (CellU.CompatS.kinds (hcρ.1 l ζ₁ ζ₂ f₁ f₂)).1 (ExS.immFree heρ l ζ₁ f₁)

/-- **A run keeps the view consistent**: every run segment of `rwpG` from a resource consistent
with `c` ends at a returned resource consistent with `c`. -/
theorem rwpG_consistentX {Φ : LocFam} {Q : PostG} {n : Nat} {ls : List SRec} {e : Expr}
    {ρ : WRes} (h : rwpG (ℍ := ℍ) Φ Q n ls e ρ) {c : Loc → Option Life}
    (hc : ConsistentX c ρ) :
    rwpG (ℍ := ℍ) Φ (fun k ls t ρ' => Q k ls t ρ' ∧ ConsistentX c ρ') n ls e ρ := by
  intro ρf fρ ps μ hf hcf hT htg hl hfd j μ' e' hj hrun hfin
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃⟩ := h ρf fρ ps μ hf hcf hT htg hl hfd j μ' e' hj hrun hfin
  exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃, consistentX_of_updN h₇.1 h₇.2.2 h₆ hc⟩

/-- `rwpG_consistentX` with the returned resource's validity, which `↭` gives. -/
theorem rwpG_consistentXV {Φ : LocFam} {Q : PostG} {n : Nat} {ls : List SRec} {e : Expr}
    {ρ : WRes} (h : rwpG (ℍ := ℍ) Φ Q n ls e ρ) {c : Loc → Option Life}
    (hc : ConsistentX c ρ) :
    rwpG (ℍ := ℍ) Φ (fun k ls t ρ' => Q k ls t ρ' ∧ ConsistentX c ρ' ∧ ResU.Valid ρ') n ls e ρ := by
  intro ρf fρ ps μ hf hcf hT htg hl hfd j μ' e' hj hrun hfin
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃⟩ := h ρf fρ ps μ hf hcf hT htg hl hfd j μ' e' hj hrun hfin
  exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃, consistentX_of_updN h₇.1 h₇.2.2 h₆ hc, (ResU.Valid.split h₆ h₇.2.2).1⟩

/-- **A run to a value keeps the view consistent**, at `rwp`. -/
theorem rwp_consistentXV {Φ : LocFam} {Q : PostN} {n : Nat} {ls : List SRec} {e : Expr}
    {ρ : WRes} (h : rwp (ℍ := ℍ) Φ Q n ls e ρ) {c : Loc → Option Life}
    (hc : ConsistentX c ρ) :
    rwp (ℍ := ℍ) Φ (fun k ls v ρ' => Q k ls v ρ' ∧ ConsistentX c ρ' ∧ ResU.Valid ρ') n ls e ρ := by
  refine rwp_iff_rwpG.mpr (rwpG_mono (fun k ls t ρ' ht => ?_)
    (rwpG_consistentXV (rwp_iff_rwpG.mp h) hc))
  obtain ⟨⟨v, hv, hq⟩, hc', hv'⟩ := ht
  exact ⟨v, hv, hq, hc', hv'⟩

/-- **`erwp_consistent`: a run's returned resource stays consistent with the view.** A run at any
location typing (the view `Θ.view c` among them) from a resource consistent with `c` returns, at
every value or stop it reaches, a resource consistent with `c`. -/
theorem erwp_consistent {Φ : LocFam} {Tb : TableN} {Q : PostN} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes} (h : erwp (ℍ := ℍ) Φ Tb Q n ls e ρ) {c : Loc → Option Life}
    (hc : ConsistentX c ρ) :
    rwpG (ℍ := ℍ) Φ (fun k ls t ρ' => erwpPost Tb Q (erwpC (ℍ := ℍ) Φ Tb Q n) k ls t ρ' ∧
      ConsistentX c ρ') n ls e ρ := by
  rw [erwp_eq] at h
  exact rwpG_consistentX h hc

end BoCa.Fig16.LogRel.Core.Chain.SI

end

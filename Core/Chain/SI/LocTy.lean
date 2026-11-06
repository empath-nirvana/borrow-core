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
before the lend stays typed (`mutL_add`). Lends extend the world along `LocTy.ExtA`: entries only
added, nothing added above a key present. `U` and `⊸` are Kripke along the resource-relative
order `LocTy.ExtR`, which departs from Core's `Ext` (`scope-791-loctype.md` §10,
`Core/Chain/ExtRLit791.lean`); `ExtA` is `ExtR` at every resource.

The world also holds its `imm` records, each with the lifetime it was lent at (`LocTy.imm`,
Core's record list moved into the world); `vN`'s `Imm` clause reads its witnesses there. A lend of
a `mut` cell leaves them alone, `LocTy.above` keeps them whole, and the Kripke orders keep every
one (`LocTy.ImmLe`).

## Its view at a run

The relation's `LocFam` is per location. At a run, each location's live `mut` cell is at one
lifetime (`c : Loc → Option Life`), and the per-location typing the run uses is the view
`Θ.view c`, which carries the world's `imm` records to the relation's entry tie (`ImmTieL`). A
lend at `α` is, viewed, `Φ.set ℓ α F` (`LocTy.view_add`), so the relation's lend frames stated at
`Φ.set` are the per-lend lend seen at its run.

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

/-- **Location typing per lend**: the family of the cell lent at `ℓ` at `b` (`fam`, applied as
`Θ ℓ b`), and the `imm` records of the world, each with the lifetime it was lent at (`imm`, Core's
record list moved into the world; `vN`'s `Imm` clause reads its witnesses there). -/
structure LocTy where
  fam : Loc → (b : Life) → Option (Nat → Val → SPropS Loc Val b)
  imm : List SRec := []

instance : CoeFun LocTy (fun _ => (l : Loc) → (b : Life) → Option (Nat → Val → SPropS Loc Val b)) :=
  ⟨LocTy.fam⟩

@[simp] theorem LocTy.mk_apply (f : Loc → (b : Life) → Option (Nat → Val → SPropS Loc Val b))
    (I : List SRec) (l : Loc) (b : Life) : (LocTy.mk f I) l b = f l b := rfl

theorem LocTy.ext' {Θ Θ' : LocTy} (h : ∀ l b, Θ l b = Θ' l b) (hI : Θ.imm = Θ'.imm) : Θ = Θ' := by
  cases Θ; cases Θ'
  simp only at hI
  subst hI
  congr
  funext l b
  exact h l b

/-- The `imm` records of `Θ` are among `Θ′`'s. -/
def LocTy.ImmLe (Θ Θ' : LocTy) : Prop := ∀ x ∈ Θ.imm, x ∈ Θ'.imm

/-- Every family `Θ` assigns is downward closed. -/
def LocTy.Down (Θ : LocTy) : Prop := ∀ l b F, Θ l b = some F → DownFam b F

/-- The Kripke order: entries are only added. -/
def LocTy.Ext (Θ Θ' : LocTy) : Prop := ∀ l b F, Θ l b = some F → Θ' l b = some F

/-- `α` is strictly shorter-lived than every key of `Θ`. -/
def LocTy.Fresh (Θ : LocTy) (α : Life) : Prop := ∀ l b, Θ l b ≠ none → α < b

/-- The entry `(ℓ, α) ↦ F` added; every other key unchanged. -/
def LocTy.add (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) : LocTy :=
  ⟨fun x b => if hb : b = α then (if x = l then some (hb ▸ F) else Θ x b) else Θ x b, Θ.imm⟩

@[simp] theorem LocTy.add_imm (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) :
    (Θ.add l α F).imm = Θ.imm := rfl

/-- **The part of the world above `a`, Core's `ls₀`**: the entries strictly longer-lived than `a`,
and the `imm` records lent strictly above `a` (`ptoMutS`'s `x ∈ ls₀ ↔ x ∈ ls ∧ x.2 ⊐ b`). -/
def LocTy.above (Θ : LocTy) (a : Life) : LocTy :=
  ⟨fun x b => if a < b then Θ x b else none, Θ.imm.filter (fun x => decide (a < x.2))⟩

@[simp] theorem LocTy.above_apply (Θ : LocTy) (a : Life) (x : Loc) (b : Life) :
    Θ.above a x b = if a < b then Θ x b else none := rfl

@[simp] theorem LocTy.above_imm (Θ : LocTy) (a : Life) :
    (Θ.above a).imm = Θ.imm.filter (fun x => decide (a < x.2)) := rfl

theorem LocTy.mem_above_imm {Θ : LocTy} {a : Life} {x : SRec} :
    x ∈ (Θ.above a).imm ↔ x ∈ Θ.imm ∧ a < x.2 := by
  simp [LocTy.above]

theorem LocTy.add_self (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) :
    Θ.add l α F l α = some F := by
  simp [LocTy.add]

/-- **A lend keeps every other key**, the source's `(ℓ, β)` among them. -/
theorem LocTy.add_keep (Θ : LocTy) (l : Loc) {α : Life} (F : Nat → Val → SPropS Loc Val α) (x : Loc)
    {b : Life} (hb : b ≠ α) : Θ.add l α F x b = Θ x b := by
  simp [LocTy.add, hb]

theorem LocTy.add_other (Θ : LocTy) {l x : Loc} (hx : x ≠ l) {α : Life}
    (F : Nat → Val → SPropS Loc Val α) (b : Life) : Θ.add l α F x b = Θ x b := by
  show (if hb : b = α then (if x = l then some (hb ▸ F) else Θ x b) else Θ x b) = Θ x b
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
  refine LocTy.ext' (fun x b => ?_) rfl
  simp only [LocTy.above_apply]
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

/-- **The Kripke order of the interpretation**: entries and `imm` records only added, and nothing
added above any key present (an `imm` record among them, since `LocTy.above` keeps them). A lend
at a fresh lifetime is one step of it (`LocTy.extA_add`). -/
def LocTy.ExtA (Θ Θ' : LocTy) : Prop :=
  Θ.Ext Θ' ∧ (∀ l a, Θ l a ≠ none → Θ'.above a = Θ.above a) ∧ Θ.ImmLe Θ'

theorem LocTy.extA_add {Θ : LocTy} {α : Life} (hf : Θ.Fresh α) (l : Loc)
    (F : Nat → Val → SPropS Loc Val α) : Θ.ExtA (Θ.add l α F) :=
  ⟨LocTy.ext_add hf l F, fun x a ha => LocTy.above_add Θ l (not_lt_of_gt (hf x a ha)) F,
    fun _ h => h⟩

theorem LocTy.extA_refl (Θ : LocTy) : Θ.ExtA Θ :=
  ⟨fun _ _ _ h => h, fun _ _ _ => rfl, fun _ h => h⟩

theorem LocTy.extA_trans {Θ Θ' Θ'' : LocTy} (h₁ : Θ.ExtA Θ') (h₂ : Θ'.ExtA Θ'') : Θ.ExtA Θ'' := by
  refine ⟨fun l b F h => h₂.1 l b F (h₁.1 l b F h), fun l a ha => ?_,
    fun x hx => h₂.2.2 x (h₁.2.2 x hx)⟩
  obtain ⟨G, hG⟩ := Option.ne_none_iff_exists'.mp ha
  rw [h₂.2.1 l a (by rw [h₁.1 l a G hG]; simp), h₁.2.1 l a ha]

/-- **`Mut` values of Core's shape are stable along the Kripke order.** -/
theorem mutL_extA {Θ Θ' : LocTy} (hE : Θ.ExtA Θ') {a : Life} {P : CPredL} {n : Nat} {v : Val}
    {ρ : WRes} (hm : mutL a P Θ n v ρ) : mutL a P Θ' n v ρ := by
  obtain ⟨l, w, χ, hχ, j, hw, hnj, hv, hl, hρ⟩ := hm
  have hfam : famL a P Θ' = famL a P Θ := by
    funext j u r
    simp only [famL, hE.2.1 l a (by rw [hl]; simp)]
  unfold mutL
  rw [hfam]
  exact ⟨l, w, χ, hχ, j, hw, hnj, hv, hE.1 l a _ hl, hρ⟩

/-! ### The resource-relative Kripke order -/

/-- **Core's `Keeps` at the per-lend world**: `Θ′` keeps every `imm` record of `Θ` relevant to `ρ`,
a record being relevant when `ρ` holds a borrow cell no longer-lived than the lifetime the record
was lent at (`CellIn ρ x.2`). An `Imm` value's witness is relevant to its cell, since a record
witnesses only cells no longer-lived than it (`Goal791N.ImmWitW`); a record lent at `α` is relevant
to no resource in `Res_α`. Core's `Keeps` reads relevance off the record's location
(`Rel`, `Core/FrameRecords.lean`) and supplies the lifetime from the run's tags (`FrameLife`,
`not_rel_lineage`); here the world carries the lifetime, and relevance reads it. -/
def LocTy.Keeps (Θ Θ' : LocTy) (ρ : WRes) : Prop := ∀ x ∈ Θ.imm, CellIn ρ x.2 → x ∈ Θ'.imm

theorem LocTy.Keeps.of_immLe {Θ Θ' : LocTy} (h : Θ.ImmLe Θ') (ρ : WRes) : Θ.Keeps Θ' ρ :=
  fun x hx _ => h x hx

/-- **The resource-relative order on the per-lend world**, the order `U` and `⊸` are Kripke
along: at the resource `ρ`, every key at a lifetime `a` with a borrow cell of `ρ` no longer-lived
than `a` (`CellIn ρ a`, Core's) is kept, and nothing is added above it, `imm` records included
(`LocTy.above` is Core's `ls₀`); the `imm` records relevant to `ρ` are kept (`LocTy.Keeps`, Core's
`Keeps`). A stored family here reads the world above its key (`famL`), so the keys at and above
such an `a`, and what lies above them, are what a value with resource `ρ` reads. It departs from
Core's literal `Ext ls ls′ ρ`, which asks agreement above every `b` with `CellIn ρ b`, not only
above the keys present (`scope-791-loctype.md` §10); read literally, `U` is not Kripke along
`ExtA` at a type through `ν`, which the interpretation reads as empty
(`Core/Chain/ExtRLit791.lean`). -/
def LocTy.ExtR (Θ Θ' : LocTy) (ρ : WRes) : Prop :=
  (∀ l a F, Θ l a = some F → CellIn ρ a → Θ' l a = some F ∧ Θ'.above a = Θ.above a) ∧
    Θ.Keeps Θ' ρ

theorem LocTy.extR_refl (Θ : LocTy) (ρ : WRes) : Θ.ExtR Θ ρ :=
  ⟨fun _ _ _ h _ => ⟨h, rfl⟩, fun _ h _ => h⟩

theorem LocTy.ExtR.trans {Θ Θ' Θ'' : LocTy} {ρ : WRes} (h₁ : Θ.ExtR Θ' ρ) (h₂ : Θ'.ExtR Θ'' ρ) :
    Θ.ExtR Θ'' ρ := by
  refine ⟨fun l a F hF hc => ?_, fun x hx hc => h₂.2 x (h₁.2 x hx hc) hc⟩
  obtain ⟨e₁, a₁⟩ := h₁.1 l a F hF hc
  obtain ⟨e₂, a₂⟩ := h₂.1 l a F e₁ hc
  exact ⟨e₂, a₂.trans a₁⟩

/-- The world-relative order is the resource-relative one at every resource. -/
theorem LocTy.ExtA.extR {Θ Θ' : LocTy} (h : Θ.ExtA Θ') (ρ : WRes) : Θ.ExtR Θ' ρ :=
  ⟨fun l a F hF _ => ⟨h.1 l a F hF, h.2.1 l a (by rw [hF]; simp)⟩, LocTy.Keeps.of_immLe h.2.2 ρ⟩

theorem LocTy.ExtR.mono {Θ Θ' : LocTy} {ρ σ : WRes} (h : Θ.ExtR Θ' ρ)
    (hs : ∀ a, CellIn σ a → CellIn ρ a) : Θ.ExtR Θ' σ :=
  ⟨fun l a F hF hc => h.1 l a F hF (hs a hc), fun x hx hc => h.2 x hx (hs _ hc)⟩

theorem LocTy.ExtR.left {Θ Θ' : LocTy} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : Θ.ExtR Θ' ρ) : Θ.ExtR Θ' ρ₁ := h.mono fun _ hi => hi.of_left hc

theorem LocTy.ExtR.right {Θ Θ' : LocTy} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : Θ.ExtR Θ' ρ) : Θ.ExtR Θ' ρ₂ := h.mono fun _ hi => hi.of_right hc

/-- **A lend at `α` and the world without it are extensions of each other at a resource in
`Res_α`**: such a resource's borrow cells are longer-lived than `α`, so the lend's key is never
one it reads. -/
theorem LocTy.extR_of_add (Θ : LocTy) (l₀ : Loc) {α : Life} (F : Nat → Val → SPropS Loc Val α)
    {ρ : WRes} (hρ : ρ.InStratum α) : (Θ.add l₀ α F).ExtR Θ ρ := by
  refine ⟨fun l a G hG hc => ?_, fun x hx _ => hx⟩
  have hαa : α < a := hc.of_stratum hρ
  rw [LocTy.add_keep Θ l₀ F l (ne_of_gt hαa)] at hG
  exact ⟨hG, (LocTy.above_add Θ l₀ (not_lt_of_gt hαa) F).symm⟩

/-- **`Mut` values of Core's shape are stable along the resource-relative order**: the cell's
own key and what lies above it are the ones its resource reads. -/
theorem mutL_extR {Θ Θ' : LocTy} {a : Life} {P : CPredL} {n : Nat} {v : Val} {ρ : WRes}
    (hE : Θ.ExtR Θ' ρ) (hm : mutL a P Θ n v ρ) : mutL a P Θ' n v ρ := by
  obtain ⟨l, w, χ, hχ, j, hw, hnj, hv, hl, rfl⟩ := hm
  have hin : CellIn (ResU.single l (CellU.mutOf a w χ hχ (famL a P Θ j) hw)) a :=
    CellIn.single (ψ := CellU.mutOf a w χ hχ (famL a P Θ j) hw)
      (by rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c)
  obtain ⟨hl', ha⟩ := hE.1 l a _ hl hin
  have hfam : famL a P Θ' = famL a P Θ := by
    funext j u r
    simp only [famL, ha]
  unfold mutL
  rw [hfam]
  exact ⟨l, w, χ, hχ, j, hw, hnj, hv, hl', rfl⟩

/-- **The part of the world above `a` and the whole are extensions of each other at a resource
in `Res_a`**: such a resource reads only keys above `a`, and every record relevant to it is lent
above `a`. -/
theorem LocTy.extR_above (Θ : LocTy) {a : Life} {ρ : WRes} (hρ : ρ.InStratum a) :
    (Θ.above a).ExtR Θ ρ ∧ Θ.ExtR (Θ.above a) ρ := by
  have habove : ∀ b, a < b → (Θ.above a).above b = Θ.above b := by
    intro b hab
    refine LocTy.ext' (fun x y => ?_) ?_
    · simp only [LocTy.above_apply]
      by_cases hby : b < y
      · simp [hby, lt_trans hab hby]
      · simp [hby]
    · simp only [LocTy.above_imm, List.filter_filter]
      congr 1
      funext x
      by_cases hbx : b < x.2
      · simp [hbx, lt_trans hab hbx]
      · simp [hbx]
  refine ⟨⟨fun l b F hF hc => ?_, fun x hx _ => (LocTy.mem_above_imm.mp hx).1⟩,
    ⟨fun l b F hF hc => ?_, fun x hx hc => LocTy.mem_above_imm.mpr ⟨hx, hc.of_stratum hρ⟩⟩⟩
  · have hab : a < b := hc.of_stratum hρ
    simp only [LocTy.above_apply, if_pos hab] at hF
    exact ⟨hF, (habove b hab).symm⟩
  · have hab : a < b := hc.of_stratum hρ
    exact ⟨by simp only [LocTy.above_apply, if_pos hab]; exact hF, habove b hab⟩

/-! ### An `imm` lend's record -/

/-- An `imm` lend's record added to the world; the keys unchanged. -/
def LocTy.addImm (Θ : LocTy) (x : SRec) : LocTy := ⟨Θ.fam, x :: Θ.imm⟩

@[simp] theorem LocTy.addImm_apply (Θ : LocTy) (x : SRec) (l : Loc) (b : Life) :
    Θ.addImm x l b = Θ l b := rfl

@[simp] theorem LocTy.addImm_imm (Θ : LocTy) (x : SRec) : (Θ.addImm x).imm = x :: Θ.imm := rfl

/-- Above a lifetime longer than the record's, the record is not seen. -/
theorem LocTy.above_addImm (Θ : LocTy) {x : SRec} {a : Life} (h : ¬ a < x.2) :
    (Θ.addImm x).above a = Θ.above a := by
  refine LocTy.ext' (fun _ _ => rfl) ?_
  simp only [LocTy.above_imm, LocTy.addImm_imm]
  rw [List.filter_cons_of_neg (by simpa using h)]

/-- **Core's `ext_add` at the per-lend world**: a record lent at `α` is not compared at a resource
in `Res_α`, whose borrow cells are all longer-lived than `α`. -/
theorem LocTy.extR_addImm (Θ : LocTy) (r : FrameRec) {α : Life} {ρ : WRes}
    (hρ : ρ.InStratum α) : Θ.ExtR (Θ.addImm (r, α)) ρ :=
  ⟨fun _ a _ hF hc => ⟨hF, LocTy.above_addImm Θ (not_lt_of_gt (hc.of_stratum hρ))⟩,
    fun _ hy _ => List.mem_cons_of_mem _ hy⟩

/-- **Core's `ext_drop` at the per-lend world**: the record lent at `α` is relevant to no resource
in `Res_α`, so the world without it is an extension there. -/
theorem LocTy.extR_of_addImm (Θ : LocTy) (r : FrameRec) {α : Life} {ρ : WRes}
    (hρ : ρ.InStratum α) : (Θ.addImm (r, α)).ExtR Θ ρ := by
  refine ⟨fun _ a _ hF hc => ⟨hF, (LocTy.above_addImm Θ
    (not_lt_of_gt (hc.of_stratum hρ))).symm⟩, fun y hy hc => ?_⟩
  rcases List.mem_cons.mp hy with rfl | hy
  · exact absurd (hc.of_stratum hρ) (lt_irrefl _)
  · exact hy

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
def LocTy.view (Θ : LocTy) (c : Loc → Option Life) : LocFam :=
  ⟨fun x => match c x with
    | some b => (Θ x b).map (fun F => ⟨b, F⟩)
    | none => none, Θ.imm⟩

@[simp] theorem LocTy.view_imm (Θ : LocTy) (c : Loc → Option Life) : (Θ.view c).imm = Θ.imm := rfl

theorem LocTy.view_apply (Θ : LocTy) (c : Loc → Option Life) (x : Loc) :
    Θ.view c x = match c x with
      | some b => (Θ x b).map (fun F => ⟨b, F⟩)
      | none => none := rfl

theorem LocTy.view_down {Θ : LocTy} (hΘ : Θ.Down) (c : Loc → Option Life) : (Θ.view c).Down := by
  intro x b G h
  rw [LocTy.view_apply] at h
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
  simp [LocTy.view_apply, hc, hF]

/-- **L3: the relation's `Φ.set` at a lend is the view of the per-lend lend.** -/
theorem LocTy.view_add (Θ : LocTy) (c : Loc → Option Life) (l : Loc) (α : Life)
    (F : Nat → Val → SPropS Loc Val α) :
    (Θ.add l α F).view (setLife c l α) = (Θ.view c).set l α F := by
  refine LocFam.ext' (fun x => ?_) rfl
  by_cases hx : x = l
  · subst hx
    simp [LocTy.view_apply, setLife, LocFam.set, LocTy.add_self]
  · simp only [LocTy.view_apply, setLife, LocFam.set, if_neg hx, LocFam.mk_apply]
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
    let Φ₀ : LocFam := LocFam.set LocFam.empty l β (famL β P Θ)
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
def LocTy.empty : LocTy := ⟨fun _ _ => none, []⟩

@[simp] theorem LocTy.empty_apply (l : Loc) (b : Life) : LocTy.empty l b = none := rfl

@[simp] theorem LocTy.empty_imm : LocTy.empty.imm = [] := rfl

theorem LocTy.empty_down : LocTy.empty.Down := fun _ _ _ h => by simp at h

theorem LocTy.empty_bounded : LocTy.empty.Bounded := ⟨0, fun _ _ h => by simp at h⟩

/-- A world an interpretation runs at: its families downward closed, and a lifetime fresh for
it (`LocTy.exists_fresh`). -/
def LocTy.OK (Θ : LocTy) : Prop := Θ.Down ∧ Θ.Bounded

theorem LocTy.empty_ok : LocTy.empty.OK := ⟨LocTy.empty_down, LocTy.empty_bounded⟩

/-- The view of the empty world types nothing. -/
theorem LocTy.view_empty (c : Loc → Option Life) : LocTy.empty.view c = LocFam.empty := by
  refine LocFam.ext' (fun x => ?_) rfl
  rw [LocTy.view_apply]
  cases c x <;> rfl

theorem LocTy.ext_of_extA {Θ Θ' : LocTy} (h : Θ.ExtA Θ') : Θ.Ext Θ' := h.1

/-- **The view grows along the Kripke order**: `LocFam.Ext`, the order `erwp_extΦ` reads. -/
theorem LocTy.view_ext {Θ Θ' : LocTy} (h : Θ.Ext Θ') (c : Loc → Option Life) :
    LocFam.Ext (Θ.view c) (Θ'.view c) := by
  intro x y hx
  rw [LocTy.view_apply] at hx ⊢
  cases hc : c x with
  | none => rw [hc] at hx; cases hx
  | some b =>
      rw [hc] at hx
      simp only at hx ⊢
      obtain ⟨F, hF, rfl⟩ := Option.map_eq_some_iff.mp hx
      rw [h x b F hF]
      rfl

/-- The view's `imm` records grow along the order that keeps them. -/
theorem LocTy.view_immLe {Θ Θ' : LocTy} (h : Θ.ImmLe Θ') (c : Loc → Option Life) :
    (Θ.view c).ImmLe (Θ'.view c) := h

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

/-- A view moved at a location the resource's exclusive walk does not hold stays consistent. -/
theorem consistentX_setLife {c : Loc → Option Life} {ρ : WRes} (hc : ConsistentX c ρ) {l : Loc}
    (hl : ∀ e, ExS ρ e → e.get l = none) (α : Life) : ConsistentX (setLife c l α) ρ := by
  intro e he x ψ hg hk
  have hx : x ≠ l := fun h => by subst h; rw [hl e he] at hg; cases hg
  simp only [setLife, if_neg hx]
  exact hc e he x ψ hg hk

/-- **An operand's exclusive walk misses a location the other operand holds a non-`imm` cell at**,
in a valid composite. -/
theorem exS_none_of_part {ρ₁ ρ₂ ρ : WRes} (h : ResU.CompS ρ₁ ρ₂ ρ) (hv : ResU.Valid ρ) {l : Loc}
    {ψ : CellU Loc Val} (hg : ρ₁.get l = some ψ) (hk : ψ.kind ≠ Kind.imm) :
    ∀ e, ExS ρ₂ e → e.get l = none := by
  intro e he
  obtain ⟨σ, ex, a, hex, -, -⟩ := hv
  obtain ⟨e₁, e₂, he₁, he₂, hc⟩ := (ExS.split h).mp hex
  obtain rfl := ExS.functional he he₂
  have h₁ := ExS.get_of_ne_imm he₁ hg hk
  cases f : e.get l with
  | none => rfl
  | some ζ => exact absurd (CellU.CompatS.kinds (hc.1 l _ ζ h₁ f)).1 hk

/-- **A `mut` cell at its view lifetime, its content consistent, is consistent.** -/
theorem consistentX_single_mut {c : Loc → Option Life} {l : Loc} {b : Life} {w : Val}
    {σ : WRes} {hσ : σ.InStratum b} {P : Val → SPropS Loc Val b} {hw : P w ⟨σ, hσ⟩}
    (hc : ConsistentX c σ) (hl : c l = some b) :
    ConsistentX c (ResU.single l (CellU.mutOf b w σ hσ P hw)) := by
  intro e he x ψ hg hk
  obtain ⟨e₀, he₀, hcomp⟩ := ExW.single_mut_inv he
  rcases ResU.Comp.get hcomp x with ⟨-, -, f⟩ | ⟨ζ, f₁, -, f⟩ | ⟨ζ, -, f₂, f⟩ |
      ⟨ζ₁, ζ₂, ζ, f₁, f₂, -, -⟩
  · rw [hg] at f; cases f
  · rw [hg] at f; cases Option.some.inj f
    obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some f₁
    rw [hl, CellU.at_mutOf]
  · rw [hg] at f; cases Option.some.inj f
    exact hc e₀ he₀ x _ f₂ hk
  · obtain ⟨-, rfl⟩ := ResU.single_get_eq_some f₁
    exact absurd (CellU.CompatS.kinds (hcomp.1 x _ ζ₂ f₁ f₂)).1
      (by rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c)

/-- **A resource in the top stratum is consistent with every view**: it holds no borrow cell, and
neither does its exclusive walk. -/
theorem consistentX_of_top {σ : WRes} (h : σ.InStratum (OrderDual.toDual 0))
    (c : Loc → Option Life) : ConsistentX c σ := by
  intro e he x ψ hg hk
  have hin := ExW.inStratum BoLo.compS_hC he _ h x ψ hg
  rcases ψ with _ | _ | m
  · cases hk
  · cases hk
  · exact absurd hin (fun h' => Nat.not_lt_zero _ h')

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
  intro ρf fρ ps μ hf hcf hT htg hI hl hfd j μ' e' hj hrun hfin
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃⟩ := h ρf fρ ps μ hf hcf hT htg hI hl hfd j μ' e' hj hrun hfin
  exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃, consistentX_of_updN h₇.1 h₇.2.2 h₆ hc⟩

/-- `rwpG_consistentX` with the returned resource's validity, which `↭` gives. -/
theorem rwpG_consistentXV {Φ : LocFam} {Q : PostG} {n : Nat} {ls : List SRec} {e : Expr}
    {ρ : WRes} (h : rwpG (ℍ := ℍ) Φ Q n ls e ρ) {c : Loc → Option Life}
    (hc : ConsistentX c ρ) :
    rwpG (ℍ := ℍ) Φ (fun k ls t ρ' => Q k ls t ρ' ∧ ConsistentX c ρ' ∧ ResU.Valid ρ') n ls e ρ := by
  intro ρf fρ ps μ hf hcf hT htg hI hl hfd j μ' e' hj hrun hfin
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    h₁₃⟩ := h ρf fρ ps μ hf hcf hT htg hI hl hfd j μ' e' hj hrun hfin
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

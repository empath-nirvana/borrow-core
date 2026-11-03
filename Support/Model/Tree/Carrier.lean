import Support.Model.Tree.Parent

/-!
# The carrier stratified by the lifetime tree

`[spec §62]`. Rows 5.1–5.8 and 5.58 with `⊐` read in a cactus `K` (`Tree/Order.lean`) instead
of the printed chain (row 5.9). At the chain it is the printed carrier (`chainEquiv`), and the
printed statements of `[TR]` §6 are its chain instances (`Tree/Chain*.lean`). The tree files read
only the printed definitions (`Paper/S5_Model/Definitions.lean`,
`Paper/S6_2_NonStandardLemmas/Definitions.lean`) and the cell facts below them
(`Support/Model/Cells.lean`, `Composition.lean`, `CellFacts.lean`, `Lifetimes.lean`,
`Prelude.lean`), never a printed lemma. Core's relation and typed worlds still read the printed
carrier (`ResU`); they move to this one in the later PRs of #771.

    Cell_S ≜ own(Val) + imm(Imm_S) + mut(Mut_S)
    Imm_S  ≜ {(ᾱ : ℘⁺_fin(Life), v, ρ : Res_ᾱ) ∣ ∀ x ∈ S, y ∈ ᾱ. x ⊏ y}
    Mut_S  ≜ {(β̄ an antichain, v, ρ : Res_β̄, P̂ : Val → SProp_β̄) ∣ ∀ x ∈ S, y ∈ β̄. x ⊏ y, P̂(v)(ρ)}

Strata are indexed by a nonempty finite set of lifetimes `S` (`TSet`): `Res_S` holds the cells
every lifetime of which is strictly above every member of `S`. A single lifetime `α` is the
stratum `{α}`.

**Forced changes, each named with its printed row:**

* **Row 5.4, `ρ : Res_{⊔ᾱ}`.** `⊔ᾱ` of siblings is their nearest common ancestor, and a cell
  strictly above both need not be strictly above it (`Cactus.star_sup_lt_fails`). The payload
  stratum is `Res_ᾱ`, the intersection of the members' strata. At the chain `Res_ᾱ = Res_{⊔ᾱ}`
  (`Tree/CarrierChain.lean`).
* **Row 5.4, `⊓ᾱ ⊐ α`.** Read at every member (`LSet.le_meet_iff`'s right-hand side).
* **Row 5.5 and row 5.16 clause 3, `mut(α ⊓ β, v, ρ, P̂ ∧ Q̂)`.** `α ⊓ β` exists only for
  comparable lifetimes (`Cactus.comparable_of_lower`), and no stratum holds the strata of two
  cousins (`cousins_no_common_stratum`). A `mut` cell carries a set `β̄` of lifetimes, as an `imm`
  cell does: an antichain (no member strictly below another). Clause 3 composes `mut(β̄₁)` and
  `mut(β̄₂)` to `mut(min(β̄₁ ∪ β̄₂))`, the members of the union with no member strictly below
  them (`WCactus.minS`). For comparable `α`, `β` that is `{α ⊓ β}`; at the chain every antichain
  is a singleton, so the printed `mut(β)` is `mut({β})`. Wherever the printed model reads `β` of a
  `mut` cell it reads every member: `@ψ ⊐ α` is `x ⊐ α` at every member (`CellUT.InStratum`),
  and the witness lies in `Res_β̄`.
* **Row 5.58, the recursion.** Well-founded recursion on "strictly above every member" in `K`
  (`WCactus.above_wf`); `K` has no infinite ascending chain (`WCactus.wf`). The printed measure
  (the chain) is the instance `WCactus.chain`.
* **`℘⁺(Life)` is finite** (`TSet`). The printed `LSet`s are exactly the finite nonempty sets
  (their members lie between `⊔ᾱ` and `⊓ᾱ` in `ℕ`); `Tree/CarrierChain.lean` gives the
  bijection.

Each change is proved equal to the printed row at the chain: strata, `▶◀`, `●`, `⋈`, `○`
(`Tree/CarrierChainOps.lean`: `ΦU_inStratum_iff`, `chain_compR_iff`, …), and `✓`, `#` and
`⦇−⦈` (`Tree/CarrierChainValid.lean`: `chain_valid_iff`, `chain_hash_iff`, `chain_flat_iff`).

**Forced changes in the ported lemmas** (`Tree/Port/`), each an added hypothesis or a reading
named in the lemma's docstring:
* **6.27, 6.52, 6.59: `↓α` (row 5.12, `α + 1`).** The proofs read of `↓α` that it lies strictly
  below `α` and that whatever lies strictly above it is at or above `α`. In a tree `α` need
  not have a child, so that stratum is a hypothesis `hD : K.DownOf D {α}`
  (`Tree/Port/Down.lean`). A covering child gives one (`WCactus.downOf_covers`), and at the
  chain the printed `↓α` does (`WCactus.chain_downOf`). A stratum below an antichain exists only
  when the antichain is one lifetime (`WCactus.downOf_anti_singleton`), so 6.27 is stated for a
  `mut` cell at `{a}`; for a `mut` cell at two or more siblings it is open
  (`Tree/Port/Six27.lean`).
* **`@χ ⊑ @ψ` inside `Support/Model/Outlives.lean`'s walk strata** is read as what the proofs
  use of it, that every stratum holding `χ` holds `ψ` (`StratumLE`, `Tree/Port/Strata.lean`), and
  "a borrow shorter than `x`" as `CellUT.Shorter` (`Tree/Port/OutlivesB.lean`). Neither appears
  in a printed statement.
* **A `mut` cell's `β`** is its antichain `β̄` with its antichain fact (`[Fact (K.Anti β̄)]`), per
  row 5.16 above; at the chain `β̄ = {β}`.
Not ported: 6.40 (untranscribed on the printed carrier too) and 6.45, which reads `@ρ` (the
meet of a resource's lifetimes) as one lifetime; its stratum reading is
`ResUT.CompS.inStratum`, `ResUT.CompS.inStratum_left` and `ResUT.CompS.inStratum_right`.

**Records.** In `Tree/Port/` a record's tag `[as printed]` means the printed statement read at
`CellUT K` through the readings above (a lifetime as the stratum `{α}`, a lifetime set as a
`TSet`, a `mut` cell's lifetime as its antichain); a further change is `[variant: …]` or
`[restricted: …]`, as in `Paper/INDEX.md`.

**Files** (`Support/Model/Tree/`):
* `Order`, `Parent`, `Graft`: the lifetime order as a cactus, built from a parent function, and
  grafting a subtree under a newer lifetime.
* `Carrier`, `CarrierOps`, `CarrierRes`: this carrier, its cell operations, resources, walks,
  `✓`, `#`, and Lemmas 6.1–6.6 and 6.9.
* `CarrierChain`, `CarrierChainOps`, `CarrierChainValid`: the chain instance and `chainEquiv`.
* `ChainRes`, `ChainUpd`, `ChainRebSub`: the printed resource vocabulary, `↭`, `reb_α` and `⊟`
  along `chainEquiv`; `Chain59` and `ChainSix*`: the printed statements of `[TR]` §6 as chain
  instances.
* `CarrierGraft`, `CarrierGraftEx`, `CarrierSim`: worlds carried along a graft, and a handler's
  lend with a task resumed inside it.
* `Port/`: the printed lemmas of `[TR]` §6 (6.1–6.59 but 6.40 and 6.45) and the `Support/Model`
  results they rest on, over `CellUT K`, by the printed proofs.
* `Comparability`: the classification of every place the printed model compares two lifetimes.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

/-! ### Finite nonempty lifetime sets -/

/-- `ᾱ ∈ ℘⁺(Life)`, finite. -/
@[ext] structure TSet where
  /-- The members. -/
  set : Finset Life
  /-- `ᾱ ≠ ∅`. -/
  ne : set.Nonempty

namespace TSet

/-- `{a}`. -/
def single (a : Life) : TSet := ⟨{a}, Finset.singleton_nonempty a⟩

/-- `ᾱ₁ ∪ ᾱ₂`. -/
def union (s t : TSet) : TSet := ⟨s.set ∪ t.set, s.ne.mono Finset.subset_union_left⟩

instance : Union TSet := ⟨union⟩

@[simp] theorem union_set (s t : TSet) : (s ∪ t).set = s.set ∪ t.set := rfl

@[simp] theorem single_set (a : Life) : (single a).set = {a} := rfl

theorem union_comm (s t : TSet) : s ∪ t = t ∪ s := TSet.ext (Finset.union_comm _ _)

theorem union_assoc (s t u : TSet) : s ∪ t ∪ u = s ∪ (t ∪ u) :=
  TSet.ext (Finset.union_assoc _ _ _)

theorem union_self (s : TSet) : s ∪ s = s := TSet.ext (Finset.union_self _)

end TSet

/-! ### A cactus with no infinite ascending chain -/

/-- A `Cactus` in which no lifetime has infinitely many strict ancestors: row 5.58's measure. -/
structure WCactus extends Cactus where
  /-- No infinite ascending chain `a₀ ⊏ a₁ ⊏ ⋯`. -/
  wf : WellFounded (fun b a => toCactus.lt a b)

namespace WCactus

variable (K : WCactus)

/-- Every member of `T` is strictly above every member of `S`: `T` may sit in `Cell_S`. -/
def Above (S T : TSet) : Prop := ∀ x ∈ S.set, ∀ y ∈ T.set, K.lt x y

/-- Row 5.58's measure in the tree. -/
theorem above_wf : WellFounded (fun T S => K.Above S T) := by
  let pick : TSet → Life := fun S => S.ne.choose
  have h : Subrelation (fun T S => K.Above S T) (InvImage (fun b a => K.lt a b) pick) :=
    fun {T S} hTS => hTS _ S.ne.choose_spec _ T.ne.choose_spec
  exact h.wf (InvImage.wf pick K.wf)

theorem lt_trans {a b c : Life} (h₁ : K.lt a b) (h₂ : K.lt b c) : K.lt a c :=
  Cactus.lt_of_lt_of_le h₁ h₂.le

/-- No member strictly below another. -/
def Anti (s : TSet) : Prop := ∀ x ∈ s.set, ∀ y ∈ s.set, ¬ K.lt x y

/-- A finite nonempty set has a member with no member strictly below it. -/
theorem exists_minimal (s : Finset Life) (hs : s.Nonempty) :
    ∃ x ∈ s, ∀ y ∈ s, ¬ K.lt y x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hs (by simp)
  | @insert a s _ ih =>
      rcases s.eq_empty_or_nonempty with rfl | hne
      · refine ⟨a, by simp, fun y hy => ?_⟩
        simp only [insert_empty_eq, Finset.mem_singleton] at hy
        subst hy; exact Cactus.lt_irrefl _ _
      · obtain ⟨m, hm, hmin⟩ := ih hne
        by_cases ham : K.lt a m
        · refine ⟨a, by simp, fun y hy => ?_⟩
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact Cactus.lt_irrefl _ _
          · exact fun hya => hmin y hy (K.lt_trans hya ham)
        · refine ⟨m, Finset.mem_insert_of_mem hm, fun y hy => ?_⟩
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact ham
          · exact hmin y hy

open scoped Classical in
/-- `min(ᾱ)`: the members with no member strictly below them. -/
def minS (s : TSet) : TSet :=
  ⟨s.set.filter (fun x => ∀ y ∈ s.set, ¬ K.lt y x), by
    obtain ⟨x, hx, hmin⟩ := K.exists_minimal s.set s.ne
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hmin⟩⟩⟩

theorem mem_minS {s : TSet} {x : Life} :
    x ∈ (K.minS s).set ↔ x ∈ s.set ∧ ∀ y ∈ s.set, ¬ K.lt y x := by
  classical
  unfold minS
  simp only [Finset.mem_filter]

theorem minS_sub {s : TSet} {x : Life} (h : x ∈ (K.minS s).set) : x ∈ s.set :=
  ((K.mem_minS).mp h).1

theorem minS_anti (s : TSet) : K.Anti (K.minS s) :=
  fun x hx _ hy hxy => ((K.mem_minS).mp hy).2 x ((K.mem_minS).mp hx).1 hxy

/-- Every member is above some member of `min(ᾱ)`. -/
theorem exists_minS_le {s : TSet} {y : Life} (hy : y ∈ s.set) :
    ∃ x ∈ (K.minS s).set, K.le x y := by
  classical
  obtain ⟨m, hm, hmin⟩ := K.exists_minimal (s.set.filter (fun x => K.le x y))
    ⟨y, Finset.mem_filter.mpr ⟨hy, K.refl y⟩⟩
  obtain ⟨hms, hmy⟩ := Finset.mem_filter.mp hm
  refine ⟨m, (K.mem_minS).mpr ⟨hms, fun z hz hzm => ?_⟩, hmy⟩
  exact hmin z (Finset.mem_filter.mpr ⟨hz, K.trans hzm.le hmy⟩) hzm

/-- An antichain is its own `min`. -/
theorem minS_of_anti {s : TSet} (h : K.Anti s) : K.minS s = s := by
  refine TSet.ext (Finset.ext fun x => ?_)
  rw [K.mem_minS]
  exact ⟨fun k => k.1, fun hx => ⟨hx, fun y hy => h y hy x hx⟩⟩

/-- `min(min(ᾱ) ∪ β̄) = min(ᾱ ∪ β̄)`. -/
theorem minS_union_minS_left (s t : TSet) : K.minS (K.minS s ∪ t) = K.minS (s ∪ t) := by
  refine TSet.ext (Finset.ext fun x => ?_)
  rw [K.mem_minS (s := K.minS s ∪ t), K.mem_minS (s := s ∪ t)]
  simp only [TSet.union_set, Finset.mem_union]
  constructor
  · rintro ⟨hx, hmin⟩
    refine ⟨hx.imp (K.minS_sub) id, fun y hy hyx => ?_⟩
    rcases hy with hy | hy
    · obtain ⟨z, hz, hzy⟩ := K.exists_minS_le hy
      exact hmin z (Or.inl hz) (Cactus.lt_of_le_of_lt hzy hyx)
    · exact hmin y (Or.inr hy) hyx
  · rintro ⟨hx, hmin⟩
    refine ⟨?_, fun y hy => hmin y (hy.imp (K.minS_sub) id)⟩
    rcases hx with hx | hx
    · exact Or.inl ((K.mem_minS).mpr ⟨hx, fun y hy => hmin y (Or.inl hy)⟩)
    · exact Or.inr hx

theorem minS_union_comm (s t : TSet) : K.minS (s ∪ t) = K.minS (t ∪ s) := by
  rw [TSet.union_comm]

/-- `min(min(ᾱ ∪ β̄) ∪ γ̄) = min(ᾱ ∪ min(β̄ ∪ γ̄))`: the associativity clause 3 rests on, where
the printed proof cites the associativity of `⊓`. -/
theorem minS_assoc (s t u : TSet) :
    K.minS (K.minS (s ∪ t) ∪ u) = K.minS (s ∪ K.minS (t ∪ u)) := by
  rw [K.minS_union_minS_left, TSet.union_comm s (K.minS _), K.minS_union_minS_left]
  congr 1
  ext x
  simp only [TSet.union_set, Finset.mem_union]
  tauto

theorem minS_self {s : TSet} (h : K.Anti s) : K.minS (s ∪ s) = s := by
  rw [TSet.union_self, K.minS_of_anti h]

/-- `Above S` reads only the members of `min`. -/
theorem above_minS_iff {S s : TSet} : K.Above S (K.minS s) ↔ K.Above S s := by
  constructor
  · intro h x hx y hy
    obtain ⟨z, hz, hzy⟩ := K.exists_minS_le hy
    exact Cactus.lt_of_lt_of_le (h x hx z hz) hzy
  · intro h x hx y hy
    exact h x hx y (K.minS_sub hy)

theorem above_union_iff {S s t : TSet} : K.Above S (s ∪ t) ↔ K.Above S s ∧ K.Above S t := by
  constructor
  · intro h
    exact ⟨fun x hx y hy => h x hx y (Finset.mem_union_left _ hy),
      fun x hx y hy => h x hx y (Finset.mem_union_right _ hy)⟩
  · rintro ⟨h₁, h₂⟩ x hx y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact h₁ x hx y hy
    · exact h₂ x hx y hy

/-- A stratum below a union is below each part. -/
theorem above_of_union_left {S s t : TSet} (h : K.Above (s ∪ t) S) : K.Above s S :=
  fun x hx y hy => h x (Finset.mem_union_left _ hx) y hy

theorem above_of_union_right {S s t : TSet} (h : K.Above (s ∪ t) S) : K.Above t S :=
  fun x hx y hy => h x (Finset.mem_union_right _ hx) y hy

theorem above_union_of {S s t : TSet} (h₁ : K.Above s S) (h₂ : K.Above t S) :
    K.Above (s ∪ t) S := by
  intro x hx y hy
  rcases Finset.mem_union.mp hx with hx | hx
  · exact h₁ x hx y hy
  · exact h₂ x hx y hy

theorem above_minS_of {S s : TSet} (h : K.Above s S) : K.Above (K.minS s) S :=
  fun x hx y hy => h x (K.minS_sub hx) y hy

/-! #### Instances -/

/-- The printed chain (row 5.9) with its measure (row 5.58). -/
def chain : WCactus where
  toCactus := Cactus.chainC
  wf := by
    have h : Subrelation (fun b a => Cactus.chainC.lt a b)
        (InvImage (· < ·) (fun a : Life => OrderDual.ofDual a)) := by
      intro b a hab
      exact (Cactus.chainC_lt a b).mp hab
    exact h.wf (InvImage.wf _ Nat.lt_wfRel.wf)

@[simp] theorem chain_le (a b : Life) : chain.le a b ↔ a ≤ b := Iff.rfl

theorem chain_lt (a b : Life) : chain.lt a b ↔ a < b := Cactus.chainC_lt a b

/-- The cactus of a parent function: ancestors are finitely many (`rank` decreases). -/
def ofParent (P : ParentFn) : WCactus where
  toCactus := Cactus.ofParent P
  wf := by
    have h : Subrelation (fun b a => (Cactus.ofParent P).lt a b)
        (InvImage (· < ·) (fun a : Life => P.rank (OrderDual.ofDual a))) := by
      intro b a hab
      rcases ParentFn.Anc.eq_or_rank_lt hab.1 with e | e
      · exact absurd (OrderDual.ofDual.injective e).symm hab.2
      · exact e
    exact h.wf (InvImage.wf _ Nat.lt_wfRel.wf)

end WCactus

/-! ### The stratified construction (rows 5.1–5.5, 5.58) -/

variable (Loc Val : Type)

/-- `Cell_S`, one layer. `below T _` is `Cell_T`, for `T` strictly above every member of
`S`. -/
inductive CellTF (K : WCactus) (S : TSet) (below : ∀ T, K.Above S T → Type) : Type where
  /-- `own(Val)`. -/
  | own (v : Val)
  /-- `imm(ᾱ, v, ρ : Res_ᾱ)`, every member of `ᾱ` strictly above `S`. -/
  | imm (s : TSet) (hs : K.Above S s) (v : Val) (ρ : PMap Loc (below s hs))
  /-- `mut(β̄, v, ρ : Res_β̄, P̂)` with `P̂(v)(ρ)`, `β̄` an antichain strictly above `S`. -/
  | mut (s : TSet) (hs : K.Above S s) (anti : K.Anti s) (v : Val) (ρ : PMap Loc (below s hs))
      (P : Val → PMap Loc (below s hs) → Prop) (hw : P v ρ)

/-- `Cell_S`, by well-founded recursion on `K`. -/
def CellT (K : WCactus) : TSet → Type :=
  WellFounded.fix K.above_wf (CellTF Loc Val K)

/-- `Res_S`. -/
abbrev ResT (K : WCactus) (S : TSet) : Type := PMap Loc (CellT Loc Val K S)

/-- Row 5.3 in the tree, as an equation. -/
theorem CellT_eq (K : WCactus) (S : TSet) :
    CellT Loc Val K S = CellTF Loc Val K S (fun T _ => CellT Loc Val K T) :=
  WellFounded.fix_eq K.above_wf (CellTF Loc Val K) S

/-- The `imm` payload of the union. -/
structure ImmT (K : WCactus) : Type where
  ls : TSet
  v : Val
  ρ : ResT Loc Val K ls

/-- The `mut` payload of the union. -/
structure MutT (K : WCactus) : Type where
  ls : TSet
  anti : K.Anti ls
  v : Val
  ρ : ResT Loc Val K ls
  P : Val → ResT Loc Val K ls → Prop
  hw : P v ρ

/-- `ψ ∈ Cell ≜ ⋃_S Cell_S` (row 5.8). -/
inductive CellUT (K : WCactus) : Type where
  | own (v : Val)
  | imm (i : ImmT Loc Val K)
  | mut (m : MutT Loc Val K)

/-- `Res` (row 5.7). -/
abbrev ResUT (K : WCactus) : Type := PMap Loc (CellUT Loc Val K)

variable {Loc Val : Type} {K : WCactus}

/-- One layer, forgetting the side condition. -/
def CellTF.toU {S : TSet} : CellTF Loc Val K S (fun T _ => CellT Loc Val K T) → CellUT Loc Val K
  | .own v => .own v
  | .imm s _ v ρ => .imm ⟨s, v, ρ⟩
  | .mut s _ a v ρ P hw => .mut ⟨s, a, v, ρ, P, hw⟩

/-- The lifetime set of a borrow cell; `none` for `own`. -/
def CellUT.lsOf : CellUT Loc Val K → Option TSet
  | .own _ => none
  | .imm i => some i.ls
  | .mut m => some m.ls

/-- `ψ ∈ Cell_S`: every lifetime of the cell strictly above every member of `S`. -/
def CellUT.InStratum (S : TSet) : CellUT Loc Val K → Prop
  | .own _ => True
  | .imm i => K.Above S i.ls
  | .mut m => K.Above S m.ls

/-- `ρ ∈ Res_S`. -/
def ResUT.InStratum (S : TSet) (ρ : ResUT Loc Val K) : Prop :=
  ∀ l ψ, ρ.get l = some ψ → ψ.InStratum S

def CellUT.toLayer (S : TSet) :
    (ψ : CellUT Loc Val K) → ψ.InStratum S → CellTF Loc Val K S (fun T _ => CellT Loc Val K T)
  | .own v, _ => .own v
  | .imm i, h => .imm i.ls h i.v i.ρ
  | .mut m, h => .mut m.ls h m.anti m.v m.ρ m.P m.hw

theorem CellTF.toU_inStratum {S : TSet}
    (x : CellTF Loc Val K S (fun T _ => CellT Loc Val K T)) : (CellTF.toU x).InStratum S := by
  cases x with
  | own v => exact trivial
  | imm s hs v ρ => exact hs
  | «mut» s hs a v ρ P hw => exact hs

theorem CellUT.toU_toLayer {S : TSet} (ψ : CellUT Loc Val K) (h : ψ.InStratum S) :
    CellTF.toU (ψ.toLayer S h) = ψ := by cases ψ <;> rfl

theorem CellTF.toLayer_toU {S : TSet} (x : CellTF Loc Val K S (fun T _ => CellT Loc Val K T))
    (h : (CellTF.toU x).InStratum S) : (CellTF.toU x).toLayer S h = x := by
  cases x <;> rfl

@[simp] theorem CellUT.inStratum_own (S : TSet) (v : Val) :
    (CellUT.own (K := K) (Loc := Loc) v).InStratum S := trivial

theorem CellUT.InStratum.mono {S S' : TSet} (h : ∀ x ∈ S'.set, ∃ y ∈ S.set, K.le x y)
    {ψ : CellUT Loc Val K} (hψ : ψ.InStratum S) : ψ.InStratum S' := by
  have key : ∀ t : TSet, K.Above S t → K.Above S' t := by
    intro t ht x hx z hz
    obtain ⟨y, hy, hxy⟩ := h x hx
    exact Cactus.lt_of_le_of_lt hxy (ht y hy z hz)
  cases ψ with
  | own v => exact trivial
  | imm i => exact key _ hψ
  | «mut» m => exact key _ hψ

theorem ResUT.InStratum.mono {S S' : TSet} (h : ∀ x ∈ S'.set, ∃ y ∈ S.set, K.le x y)
    {ρ : ResUT Loc Val K} (hρ : ρ.InStratum S) : ρ.InStratum S' :=
  fun l ψ e => (hρ l ψ e).mono h

/-- `Res_ᾱ ∩ Res_β̄ = Res_{ᾱ ∪ β̄}`. -/
theorem CellUT.inStratum_union_iff {s t : TSet} {ψ : CellUT Loc Val K} :
    ψ.InStratum (s ∪ t) ↔ ψ.InStratum s ∧ ψ.InStratum t := by
  cases ψ with
  | own v => exact ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩
  | imm i =>
      exact ⟨fun h => ⟨K.above_of_union_left h, K.above_of_union_right h⟩,
        fun h => K.above_union_of h.1 h.2⟩
  | «mut» m =>
      exact ⟨fun h => ⟨K.above_of_union_left h, K.above_of_union_right h⟩,
        fun h => K.above_union_of h.1 h.2⟩

theorem ResUT.inStratum_union_iff {s t : TSet} {ρ : ResUT Loc Val K} :
    ρ.InStratum (s ∪ t) ↔ ρ.InStratum s ∧ ρ.InStratum t :=
  ⟨fun h => ⟨fun l ψ e => (CellUT.inStratum_union_iff.mp (h l ψ e)).1,
      fun l ψ e => (CellUT.inStratum_union_iff.mp (h l ψ e)).2⟩,
    fun h l ψ e => CellUT.inStratum_union_iff.mpr ⟨h.1 l ψ e, h.2 l ψ e⟩⟩

/-- `Res_ᾱ ⊆ Res_{min ᾱ}`. -/
theorem CellUT.InStratum.minS {s : TSet} {ψ : CellUT Loc Val K} (h : ψ.InStratum s) :
    ψ.InStratum (K.minS s) := by
  cases ψ with
  | own v => exact trivial
  | imm i => exact K.above_minS_of h
  | «mut» m => exact K.above_minS_of h

theorem ResUT.InStratum.minS {s : TSet} {ρ : ResUT Loc Val K} (h : ρ.InStratum s) :
    ρ.InStratum (K.minS s) := fun l ψ e => (h l ψ e).minS

/-- The payload of the clause-3 composite: in `Res_{min(β̄₁ ∪ β̄₂)}`. -/
theorem ResUT.InStratum.minUnion {s t : TSet} {ρ : ResUT Loc Val K} (hs : ρ.InStratum s)
    (ht : ρ.InStratum t) : ρ.InStratum (K.minS (s ∪ t)) :=
  (ResUT.inStratum_union_iff.mpr ⟨hs, ht⟩).minS

/-! ### `Cell_S ≃ {ψ ∈ Cell ∣ ψ ∈ Cell_S}` -/

def CellT.toF {S : TSet} (ψ : CellT Loc Val K S) :
    CellTF Loc Val K S (fun T _ => CellT Loc Val K T) :=
  cast (CellT_eq Loc Val K S) ψ

def CellT.ofF {S : TSet} (x : CellTF Loc Val K S (fun T _ => CellT Loc Val K T)) :
    CellT Loc Val K S :=
  cast (CellT_eq Loc Val K S).symm x

@[simp] theorem CellT.toF_ofF {S : TSet} (x : CellTF Loc Val K S (fun T _ => CellT Loc Val K T)) :
    (CellT.ofF x).toF = x := cast_cast _ _ x

@[simp] theorem CellT.ofF_toF {S : TSet} (ψ : CellT Loc Val K S) : CellT.ofF ψ.toF = ψ :=
  cast_cast _ _ ψ

/-- `Cell_S ↪ Cell`. -/
def CellT.toU {S : TSet} (ψ : CellT Loc Val K S) : CellUT Loc Val K := CellTF.toU ψ.toF

theorem CellT.toU_inStratum {S : TSet} (ψ : CellT Loc Val K S) : ψ.toU.InStratum S :=
  CellTF.toU_inStratum ψ.toF

/-- `Res_S ↪ Res`. -/
def ResT.toU {S : TSet} (ρ : ResT Loc Val K S) : ResUT Loc Val K := ρ.map CellT.toU

theorem ResT.toU_inStratum {S : TSet} (ρ : ResT Loc Val K S) : ρ.toU.InStratum S := by
  intro l ψ e
  have he : Option.map CellT.toU (ρ.get l) = some ψ := e
  cases f : ρ.get l with
  | none => rw [f] at he; exact absurd he (by simp)
  | some ψ' =>
      rw [f] at he
      simp only [Option.map_some, Option.some.injEq] at he
      exact he ▸ ψ'.toU_inStratum

def CellUT.toStratum (S : TSet) (ψ : CellUT Loc Val K) (h : ψ.InStratum S) :
    CellT Loc Val K S :=
  CellT.ofF (ψ.toLayer S h)

def optToStratumT (S : TSet) : (o : Option (CellUT Loc Val K)) →
    (∀ ψ, o = some ψ → ψ.InStratum S) → Option (CellT Loc Val K S)
  | none, _ => none
  | some ψ, h => some (ψ.toStratum S (h ψ rfl))

theorem optToStratumT_eq_none {S : TSet} {o : Option (CellUT Loc Val K)}
    (k : ∀ ψ, o = some ψ → ψ.InStratum S) (e : o = none) : optToStratumT S o k = none := by
  subst e; rfl

def ResUT.toStratum {S : TSet} (ρ : ResUT Loc Val K) (h : ρ.InStratum S) : ResT Loc Val K S where
  get := fun l => optToStratumT S (ρ.get l) (fun ψ e => h l ψ e)
  finite := by
    obtain ⟨d, hd⟩ := ρ.finite
    refine ⟨d, fun l hl => hd l (fun e => ?_)⟩
    exact hl (optToStratumT_eq_none _ e)

theorem CellUT.toU_toStratum {S : TSet} (ψ : CellUT Loc Val K) (h : ψ.InStratum S) :
    (ψ.toStratum S h).toU = ψ := by
  unfold CellT.toU CellUT.toStratum
  rw [CellT.toF_ofF, CellUT.toU_toLayer]

theorem optToStratumT_toU {S : TSet} (o : Option (CellUT Loc Val K))
    (k : ∀ ψ, o = some ψ → ψ.InStratum S) :
    Option.map CellT.toU (optToStratumT S o k) = o := by
  cases o with
  | none => rfl
  | some ψ => exact congrArg some (CellUT.toU_toStratum ψ _)

theorem ResUT.toU_toStratum {S : TSet} (ρ : ResUT Loc Val K) (h : ρ.InStratum S) :
    (ρ.toStratum h).toU = ρ :=
  PMap.ext fun l => optToStratumT_toU (ρ.get l) _

theorem CellT.toStratum_toU {S : TSet} (ψ : CellT Loc Val K S) (h : ψ.toU.InStratum S) :
    ψ.toU.toStratum S h = ψ := by
  unfold CellUT.toStratum
  rw [show ψ.toU.toLayer S h = ψ.toF from CellTF.toLayer_toU ψ.toF h, CellT.ofF_toF]

theorem optToStratumT_map {S : TSet} (o : Option (CellT Loc Val K S))
    (k : ∀ ψ, Option.map CellT.toU o = some ψ → ψ.InStratum S) :
    optToStratumT S (Option.map CellT.toU o) k = o := by
  cases o with
  | none => rfl
  | some ψ => exact congrArg some (CellT.toStratum_toU ψ _)

theorem ResT.toStratum_toU {S : TSet} (ρ : ResT Loc Val K S) (h : ρ.toU.InStratum S) :
    ρ.toU.toStratum h = ρ :=
  PMap.ext fun l => optToStratumT_map (ρ.get l) _

theorem CellT.toU_injective {S : TSet} {ψ ψ' : CellT Loc Val K S} (h : ψ.toU = ψ'.toU) :
    ψ = ψ' := by
  rw [← CellT.toStratum_toU ψ ψ.toU_inStratum, ← CellT.toStratum_toU ψ' ψ'.toU_inStratum]
  congr 1

theorem ResT.toU_injective {S : TSet} {ρ ρ' : ResT Loc Val K S} (h : ρ.toU = ρ'.toU) :
    ρ = ρ' := by
  rw [← ResT.toStratum_toU ρ ρ.toU_inStratum, ← ResT.toStratum_toU ρ' ρ'.toU_inStratum]
  congr 1

variable (Loc Val K) in
/-- `Res_S` as a subset of `Res`. -/
abbrev ResST (S : TSet) : Type := { ρ : ResUT Loc Val K // ρ.InStratum S }

variable (Loc Val K) in
/-- `SProp_S ≜ Res_S → ℙ`, read on the union. -/
abbrev SPropST (S : TSet) : Type := ResST Loc Val K S → Prop

def ResT.toS {S : TSet} (ρ : ResT Loc Val K S) : ResST Loc Val K S := ⟨ρ.toU, ρ.toU_inStratum⟩

def ResST.toRes {S : TSet} (r : ResST Loc Val K S) : ResT Loc Val K S :=
  r.val.toStratum r.property

@[simp] theorem ResST.toS_toRes {S : TSet} (r : ResST Loc Val K S) : r.toRes.toS = r :=
  Subtype.ext (ResUT.toU_toStratum r.val r.property)

@[simp] theorem ResT.toRes_toS {S : TSet} (ρ : ResT Loc Val K S) : ρ.toS.toRes = ρ :=
  ResT.toStratum_toU ρ _

@[simp] theorem ResST.toU_toRes {S : TSet} (r : ResST Loc Val K S) : r.toRes.toU = r.val :=
  ResUT.toU_toStratum r.val r.property

/-! ### Cells -/

/-- The witness of an `imm` cell, in `Res`. -/
def ImmT.res (i : ImmT Loc Val K) : ResUT Loc Val K := i.ρ.toU

/-- The witness of a `mut` cell, in `Res`. -/
def MutT.res (m : MutT Loc Val K) : ResUT Loc Val K := m.ρ.toU

/-- The witness of a cell (`∅` for `own`). -/
def CellUT.wit : CellUT Loc Val K → ResUT Loc Val K
  | .own _ => PMap.empty
  | .imm i => i.res
  | .mut m => m.res

/-- The tag of a cell. -/
def CellUT.kind : CellUT Loc Val K → Kind
  | .own _ => .own
  | .imm _ => .imm
  | .mut _ => .mut

/-- `⟦ψ⟧` (row 5.24). -/
def CellUT.erase : CellUT Loc Val K → Val
  | .own v => v
  | .imm i => i.v
  | .mut m => m.v

/-- `own(v)`. -/
def CellUT.ownOf (v : Val) : CellUT Loc Val K := .own v

/-- `imm(ᾱ, v, ρ)`, with `h` the row's `ρ : Res_ᾱ`. -/
def CellUT.immOf (s : TSet) (v : Val) (ρ : ResUT Loc Val K) (h : ρ.InStratum s) :
    CellUT Loc Val K :=
  .imm ⟨s, v, ResST.toRes ⟨ρ, h⟩⟩

instance WCactus.anti_single_fact (K : WCactus) (a : Life) : Fact (K.Anti (TSet.single a)) :=
  ⟨fun x hx y hy hxy => by
    simp only [TSet.single_set, Finset.mem_singleton] at hx hy
    subst hx; subst hy
    exact Cactus.lt_irrefl _ _ hxy⟩

instance WCactus.minS_anti_fact (K : WCactus) (s : TSet) : Fact (K.Anti (K.minS s)) :=
  ⟨K.minS_anti s⟩

/-- `mut(β̄, v, ρ, P̂)`, with `h` the row's `ρ : Res_β̄` and `hw` the refinement; `β̄`'s
antichain fact is found by instance, so the constructor has the printed shape. -/
def CellUT.mutOf (s : TSet) [a : Fact (K.Anti s)] (v : Val) (ρ : ResUT Loc Val K) (h : ρ.InStratum s)
    (P : Val → SPropST Loc Val K s) (hw : P v ⟨ρ, h⟩) : CellUT Loc Val K :=
  .mut ⟨s, a.out, v, ResST.toRes ⟨ρ, h⟩, fun v r => P v r.toS, by
    show P v (ResST.toRes ⟨ρ, h⟩).toS
    rw [ResST.toS_toRes]
    exact hw⟩

@[simp] theorem CellUT.kind_ownOf (v : Val) : (CellUT.ownOf (K := K) (Loc := Loc) v).kind = .own :=
  rfl
@[simp] theorem CellUT.kind_immOf (s : TSet) (v : Val) (ρ : ResUT Loc Val K) (h : ρ.InStratum s) :
    (CellUT.immOf s v ρ h).kind = .imm := rfl
@[simp] theorem CellUT.kind_mutOf (s : TSet) [Fact (K.Anti s)] (v : Val) (ρ : ResUT Loc Val K)
    (h : ρ.InStratum s) (P : Val → SPropST Loc Val K s) (hw : P v ⟨ρ, h⟩) :
    (CellUT.mutOf s v ρ h P hw).kind = .mut := rfl

@[simp] theorem CellUT.erase_ownOf (v : Val) : (CellUT.ownOf (K := K) (Loc := Loc) v).erase = v :=
  rfl
@[simp] theorem CellUT.erase_immOf (s : TSet) (v : Val) (ρ : ResUT Loc Val K) (h : ρ.InStratum s) :
    (CellUT.immOf s v ρ h).erase = v := rfl
@[simp] theorem CellUT.erase_mutOf (s : TSet) [Fact (K.Anti s)] (v : Val) (ρ : ResUT Loc Val K)
    (h : ρ.InStratum s) (P : Val → SPropST Loc Val K s) (hw : P v ⟨ρ, h⟩) :
    (CellUT.mutOf s v ρ h P hw).erase = v := rfl

@[simp] theorem CellUT.wit_ownOf (v : Val) :
    (CellUT.ownOf (K := K) (Loc := Loc) v).wit = PMap.empty := rfl
@[simp] theorem CellUT.wit_immOf (s : TSet) (v : Val) (ρ : ResUT Loc Val K) (h : ρ.InStratum s) :
    (CellUT.immOf s v ρ h).wit = ρ := ResST.toU_toRes ⟨ρ, h⟩
@[simp] theorem CellUT.wit_mutOf (s : TSet) [Fact (K.Anti s)] (v : Val) (ρ : ResUT Loc Val K)
    (h : ρ.InStratum s) (P : Val → SPropST Loc Val K s) (hw : P v ⟨ρ, h⟩) :
    (CellUT.mutOf s v ρ h P hw).wit = ρ := ResST.toU_toRes ⟨ρ, h⟩

@[simp] theorem CellUT.lsOf_immOf (s : TSet) (v : Val) (ρ : ResUT Loc Val K) (h : ρ.InStratum s) :
    (CellUT.immOf s v ρ h).lsOf = some s := rfl
@[simp] theorem CellUT.lsOf_mutOf (s : TSet) [Fact (K.Anti s)] (v : Val) (ρ : ResUT Loc Val K)
    (h : ρ.InStratum s) (P : Val → SPropST Loc Val K s) (hw : P v ⟨ρ, h⟩) :
    (CellUT.mutOf s v ρ h P hw).lsOf = some s := rfl

@[simp] theorem CellUT.inStratum_immOf (S s : TSet) (v : Val) (ρ : ResUT Loc Val K)
    (h : ρ.InStratum s) : (CellUT.immOf s v ρ h).InStratum S ↔ K.Above S s := Iff.rfl
@[simp] theorem CellUT.inStratum_mutOf (S s : TSet) [Fact (K.Anti s)] (v : Val)
    (ρ : ResUT Loc Val K) (h : ρ.InStratum s) (P : Val → SPropST Loc Val K s)
    (hw : P v ⟨ρ, h⟩) : (CellUT.mutOf s v ρ h P hw).InStratum S ↔ K.Above S s := Iff.rfl

theorem ImmT.ext' {i j : ImmT Loc Val K} (hs : i.ls = j.ls) (hv : i.v = j.v)
    (hρ : i.ρ ≍ j.ρ) : i = j := by
  obtain ⟨s₁, v₁, ρ₁⟩ := i
  obtain ⟨s₂, v₂, ρ₂⟩ := j
  simp only at hs hv hρ
  subst hs; subst hv
  simp only [heq_eq_eq] at hρ
  subst hρ; rfl

theorem MutT.ext' {m n : MutT Loc Val K} (hs : m.ls = n.ls) (hv : m.v = n.v)
    (hρ : m.ρ ≍ n.ρ) (hP : m.P ≍ n.P) : m = n := by
  obtain ⟨s₁, a₁, v₁, ρ₁, P₁, w₁⟩ := m
  obtain ⟨s₂, a₂, v₂, ρ₂, P₂, w₂⟩ := n
  simp only at hs hv hρ hP
  subst hs; subst hv
  simp only [heq_eq_eq] at hρ hP
  subst hρ; subst hP; rfl

theorem CellUT.immOf_inj {s₁ s₂ : TSet} {v₁ v₂ : Val} {ρ₁ ρ₂ : ResUT Loc Val K}
    {h₁ : ρ₁.InStratum s₁} {h₂ : ρ₂.InStratum s₂}
    (e : CellUT.immOf s₁ v₁ ρ₁ h₁ = CellUT.immOf s₂ v₂ ρ₂ h₂) :
    s₁ = s₂ ∧ v₁ = v₂ ∧ ρ₁ = ρ₂ := by
  simp only [CellUT.immOf] at e
  injection e with e'
  refine ⟨congrArg ImmT.ls e', congrArg ImmT.v e', ?_⟩
  have := congrArg ImmT.res e'
  simpa [ImmT.res] using this

theorem CellUT.immOf_congr {s s' : TSet} {v v' : Val} {ρ ρ' : ResUT Loc Val K}
    (hs : s = s') (hv : v = v') (hρ : ρ = ρ') (h : ρ.InStratum s) (h' : ρ'.InStratum s') :
    CellUT.immOf s v ρ h = CellUT.immOf s' v' ρ' h' := by
  subst hs; subst hv; subst hρ; rfl

theorem CellUT.mutOf_congr {s s' : TSet} (e : s = s') [Fact (K.Anti s)] [Fact (K.Anti s')] (v : Val)
    (ρ : ResUT Loc Val K) (h : ρ.InStratum s) (h' : ρ.InStratum s')
    (P : Val → SPropST Loc Val K s) (P' : Val → SPropST Loc Val K s')
    (hP : P v ⟨ρ, h⟩) (hP' : P' v ⟨ρ, h'⟩)
    (eP : ∀ (r : ResUT Loc Val K) (hr : r.InStratum s) (hr' : r.InStratum s') (w : Val),
        P w ⟨r, hr⟩ ↔ P' w ⟨r, hr'⟩) :
    CellUT.mutOf s v ρ h P hP = CellUT.mutOf s' v ρ h' P' hP' := by
  subst e
  have hPP : P = P' := by
    funext w r
    exact propext (eP r.val r.property r.property w)
  subst hPP
  rfl

theorem CellUT.mutOf_injSet {s₁ s₂ : TSet} [Fact (K.Anti s₁)] [Fact (K.Anti s₂)] {v₁ v₂ : Val}
    {ρ₁ ρ₂ : ResUT Loc Val K} {h₁ : ρ₁.InStratum s₁} {h₂ : ρ₂.InStratum s₂}
    {P₁ : Val → SPropST Loc Val K s₁} {P₂ : Val → SPropST Loc Val K s₂}
    {w₁ : P₁ v₁ ⟨ρ₁, h₁⟩} {w₂ : P₂ v₂ ⟨ρ₂, h₂⟩}
    (e : CellUT.mutOf s₁ v₁ ρ₁ h₁ P₁ w₁ = CellUT.mutOf s₂ v₂ ρ₂ h₂ P₂ w₂) :
    s₁ = s₂ ∧ v₁ = v₂ ∧ ρ₁ = ρ₂ ∧
      ∀ (r : ResUT Loc Val K) (hr₁ : r.InStratum s₁) (hr₂ : r.InStratum s₂) (w : Val),
        P₁ w ⟨r, hr₁⟩ ↔ P₂ w ⟨r, hr₂⟩ := by
  simp only [CellUT.mutOf] at e
  injection e with e'
  injection e' with hs hv hρ hP
  subst hs
  simp only [heq_eq_eq] at hρ hP
  refine ⟨rfl, hv, ?_, ?_⟩
  · have := congrArg ResT.toU hρ
    simpa using this
  · intro r hr₁ hr₂ w
    have := congrFun (congrFun hP w) (ResST.toRes ⟨r, hr₁⟩)
    simp only [ResST.toS_toRes] at this
    exact Iff.of_eq this

/-- Every cell is an `own`, an `imm` or a `mut`. -/
theorem CellUT.rep (ψ : CellUT Loc Val K) :
    (∃ v : Val, ψ = CellUT.ownOf v) ∨
    (∃ (s : TSet) (v : Val) (ρ : ResUT Loc Val K) (h : ρ.InStratum s),
        ψ = CellUT.immOf s v ρ h) ∨
    (∃ (s : TSet) (_ : Fact (K.Anti s)) (v : Val) (ρ : ResUT Loc Val K) (h : ρ.InStratum s)
        (P : Val → SPropST Loc Val K s) (hw : P v ⟨ρ, h⟩), ψ = CellUT.mutOf s v ρ h P hw) := by
  cases ψ with
  | own v => exact Or.inl ⟨v, rfl⟩
  | imm i =>
      refine Or.inr (Or.inl ⟨i.ls, i.v, i.ρ.toU, i.ρ.toU_inStratum, ?_⟩)
      show CellUT.imm i = CellUT.imm _
      exact congrArg CellUT.imm (ImmT.ext' rfl rfl (by
        simp only [heq_eq_eq]
        exact (ResT.toRes_toS i.ρ).symm))
  | «mut» m =>
      refine Or.inr (Or.inr ⟨m.ls, ⟨m.anti⟩, m.v, m.ρ.toU, m.ρ.toU_inStratum,
        fun v r => m.P v r.toRes, ?_, ?_⟩)
      · show m.P m.v (ResST.toRes ⟨m.ρ.toU, m.ρ.toU_inStratum⟩)
        rw [show ResST.toRes ⟨m.ρ.toU, m.ρ.toU_inStratum⟩ = m.ρ from ResT.toRes_toS m.ρ]
        exact m.hw
      · show CellUT.mut m = CellUT.mut _
        refine congrArg CellUT.mut (MutT.ext' rfl rfl ?_ ?_)
        · simp only [heq_eq_eq]; exact (ResT.toRes_toS m.ρ).symm
        · simp only [heq_eq_eq]
          funext v r
          show m.P v r = m.P v r.toS.toRes
          rw [ResT.toRes_toS]

theorem CellUT.wit_inStratum_imm {i : ImmT Loc Val K} : i.res.InStratum i.ls :=
  i.ρ.toU_inStratum

theorem CellUT.wit_inStratum_mut {m : MutT Loc Val K} : m.res.InStratum m.ls :=
  m.ρ.toU_inStratum

end BoCa.Fig16.Tree

end

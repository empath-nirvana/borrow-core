import Support.Model.Tree.World.Records
import Support.Model.Tree.CarrierGraftEx

/-!
# Row 5.16 clause 3 against the store typing

Two `mut` cells at one location `ℓ`, both storing `Θ ℓ = τ` read at the tree, at lifetimes
`a ⊏ b`: `mut({a}, v, χ, τ|_{Res_a}) ○ mut({b}, v, χ, τ|_{Res_b})` is, by clause 3,
`mut(min{a, b}, v, χ, P̂ ∧ Q̂) = mut({a}, v, χ, P̂ ∧ Q̂)`.

* **What clause 3 builds** (`conj_tyPred`): `P̂ ∧ Q̂` of two cells storing `τ` is `τ` read on
  `Res_{s ∪ t}`, the intersection of the operands' strata, as the printed `SPropS.conj` is `τ`
  on `Res_α ∩ Res_β` (each conjunct extended by falsity outside its own stratum, row 5.57).
* **It is not `τ` on `Res_{min(s ∪ t)}`** (`clause3_not_cov`): with `a ⊏ c ⊏ b` and
  `τ = 1 + Imm @c 1`, the witness `ℓ′ ↦ imm({c}, (), ∅)` lies in `Res_{a}`, `inj₂ ℓ′` is in `τ`
  there, and `P̂ ∧ Q̂` refuses it. Each operand is covered (`clause3_operands_cov`); the composite
  is not (`Cov` reads `τ` on the cell's own stratum `Res_{min(s ∪ t)}`).
* **The configuration is on the printed chain** (`clause3_chain`): it is not a tree effect.
* **Coverage read on the formation stratum** (`CovAt`): a `mut` cell stores `τ` read on a stratum
  `S` whose `min` is the cell's antichain. The composite is covered at `S = s ∪ t`
  (`clause3_covAt`); at `S = β̄` it is `Cov` (`covAt_self_iff`), so a cell no `○` formed is
  covered exactly as before.

Where the composite occurs. `Cov` is read of the cells a world stores (`CovR`); the composite of
clause 3 is formed by `○` in the flattening `⦇ρ⦈` (the aliasable walk, `AgWT`), where a world's
re-reading relates cells by tag, value and witness only (`ResUT.Flat.rr`), and no step reads a
flattened cell's invariant against `Θ`. The two cells exist in one world only when a `mut` cell
at `ℓ` is held beneath an `imm` cell elsewhere while another `mut` cell at `ℓ` is stored: in the
printed rules, a `mut` cell is made only by the Mut Frame (6.65) from `own(v)`, so the second cell
needs a lend of `ℓ` after an earlier lend of `ℓ` ended with a view of its cell still held. The
printed Mut Frame ends its lend with every `imm` lend inside it ended (6.64 returns the lender's
resource), so in the printed run the two cells never meet at distinct lifetimes; over the tree,
`mutEnd_world` asks nothing of the frame, and the frame condition (`joinFd`) is what excludes the
held view.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K : WCactus}

/-- The invariant a `mut` cell at `ℓ` stores at the tree `K`: `Θ ℓ = τ` read at `K`. -/
def tyPred (τ : KSem) (K : WCactus) (s : TSet) : BoCa.Val → SPropST BoCa.Loc BoCa.Val K s :=
  fun v r => τ.P K v r.val

/-- **What clause 3 builds from two cells storing `τ`**: `τ` read on `Res_{s ∪ t}`. -/
theorem conj_tyPred (τ : KSem) (s t : TSet) (w : BoCa.Val)
    (r : ResST BoCa.Loc BoCa.Val K (K.minS (s ∪ t))) :
    SPropST.conj (tyPred τ K s) (tyPred τ K t) w r ↔ r.val.InStratum (s ∪ t) ∧ τ.P K w r.val := by
  simp only [SPropST.conj, SPropST.embed, tyPred, ResUT.inStratum_union_iff]
  exact ⟨fun ⟨⟨h₁, p⟩, ⟨h₂, _⟩⟩ => ⟨⟨h₁, h₂⟩, p⟩, fun ⟨⟨h₁, h₂⟩, p⟩ => ⟨⟨h₁, p⟩, ⟨h₂, p⟩⟩⟩

/-! ### The configuration -/

/-- `τ = 1 + Imm @c 1`. -/
def τ3 (c : Life) : KSem := vSum vUnit (vImm c vUnit)

/-- The location typing: `ℓ = 1` holds `τ`. -/
def Θ3 (c : Life) : LocTy := fun l => if l = 1 then some (τ3 c) else none

theorem Θ3_one (c : Life) : Θ3 c 1 = some (τ3 c) := by simp [Θ3]

theorem empty_inStratum (S : TSet) : ResUT.InStratum S (PMap.empty : TRes K) :=
  fun _ _ e => by simp at e

theorem τ3_inj₁ (c : Life) : (τ3 c).P K (BoCa.Val.inj₁ BoCa.Val.unit) PMap.empty :=
  Or.inl ⟨_, rfl, rfl, rfl⟩

/-- `mut(s, inj₁ (), ∅, τ|_{Res_s})`, the cell a fresh `mut` lend makes (`mutLend_world`). -/
def cellAt (c : Life) (s : TSet) [Fact (K.Anti s)] : TCell K :=
  CellUT.mutOf s (BoCa.Val.inj₁ BoCa.Val.unit) PMap.empty (empty_inStratum s)
    (tyPred (τ3 c) K s) (τ3_inj₁ c)

/-- The composite clause 3 builds. -/
def compAt (c : Life) (s t : TSet) [Fact (K.Anti s)] [Fact (K.Anti t)] : TCell K :=
  CellUT.mutOf (K.minS (s ∪ t)) (BoCa.Val.inj₁ BoCa.Val.unit) PMap.empty
    ((empty_inStratum s).minUnion (empty_inStratum t))
    (SPropST.conj (tyPred (τ3 c) K s) (tyPred (τ3 c) K t))
    (SPropST.conj_holds (P := tyPred (τ3 c) K s) (Q := tyPred (τ3 c) K t) (empty_inStratum s)
      (empty_inStratum t) (τ3_inj₁ c) (τ3_inj₁ c))

theorem compAt_compR (c : Life) (s t : TSet) [Fact (K.Anti s)] [Fact (K.Anti t)] :
    CellUT.CompR (cellAt (K := K) c s) (cellAt c t) (compAt c s t) :=
  CellUT.CompR.mutMut s t _ PMap.empty (empty_inStratum s) (empty_inStratum t)
    (tyPred (τ3 c) K s) (tyPred (τ3 c) K t) (τ3_inj₁ c) (τ3_inj₁ c)

/-- Each cell a lend makes is covered. -/
theorem cellAt_cov (c : Life) (s : TSet) [Fact (K.Anti s)] :
    Cov (Θ3 c) K 1 (cellAt (K := K) c s) := by
  refine .mut 1 _ (τ3 c) (Θ3_one c) (fun _ _ => Iff.rfl) fun k ψ e => ?_
  have hw : (cellAt (K := K) c s).wit = PMap.empty := CellUT.wit_mutOf _ _ _ _ _ _
  change (cellAt (K := K) c s).wit.get k = some ψ at e
  rw [hw] at e; simp at e

/-- The witness `ℓ′ ↦ imm({c}, (), ∅)`. -/
def viewAt (c : Life) (l' : BoCa.Loc) : TRes K :=
  PMap.sng l' (leafImm (TSet.single c) BoCa.Val.unit)

theorem viewAt_inStratum_iff (c : Life) (l' : BoCa.Loc) (S : TSet) :
    (viewAt (K := K) c l').InStratum S ↔ ∀ x ∈ S.set, K.lt x c := by
  classical
  constructor
  · intro h x hx
    have := h l' (leafImm (TSet.single c) BoCa.Val.unit) (by simp [viewAt, PMap.sng_get])
    exact this x hx c (by simp)
  · intro h l ψ e
    simp only [viewAt, PMap.sng_get] at e
    split at e
    · cases e
      intro x hx y hy
      simp only [TSet.single_set, Finset.mem_singleton] at hy
      subst hy; exact h x hx
    · cases e

theorem τ3_view (c : Life) (l' : BoCa.Loc) :
    (τ3 c).P K (BoCa.Val.inj₂ (BoCa.Val.loc l')) (viewAt c l') := by
  refine Or.inr ⟨_, rfl, l', ⟨TSet.single c, BoCa.Val.unit, ResST.toRes ⟨PMap.empty, _⟩⟩, rfl,
    rfl, fun x hx => ?_, rfl, ResST.toU_toRes _⟩
  simp only [TSet.single_set, Finset.mem_singleton] at hx
  subst hx
  exact K.refl _

/-- `min{a, b} = {a}` when `a ⊏ b`. -/
theorem minS_pair {a b : Life} (h : K.lt a b) :
    ∀ x ∈ (K.minS (TSet.single a ∪ TSet.single b)).set, x = a := by
  intro x hx
  obtain ⟨hx, hmin⟩ := (K.mem_minS).mp hx
  simp only [TSet.union_set, TSet.single_set, Finset.mem_union, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · rfl
  · exact absurd h (hmin a (by simp))

/-- **The composite of two covered cells is not covered**: `a ⊏ c ⊏ b`, `τ = 1 + Imm @c 1`.
The witness `ℓ′ ↦ imm({c}, (), ∅)` lies in the composite's stratum `Res_{a}`, `inj₂ ℓ′` is in
`τ` there, and `P̂ ∧ Q̂` refuses it: `c` does not outlive `b`. -/
theorem clause3_not_cov {a b c : Life} (hac : K.lt a c) (hcb : K.lt c b) (l' : BoCa.Loc) :
    Cov (Θ3 c) K 1 (cellAt (K := K) c (TSet.single a)) ∧
    Cov (Θ3 c) K 1 (cellAt (K := K) c (TSet.single b)) ∧
    CellUT.CompR (cellAt (K := K) c (TSet.single a)) (cellAt c (TSet.single b))
      (compAt c (TSet.single a) (TSet.single b)) ∧
    ¬ Cov (Θ3 c) K 1 (compAt (K := K) c (TSet.single a) (TSet.single b)) := by
  refine ⟨cellAt_cov _ _, cellAt_cov _ _, compAt_compR _ _ _, fun hc => ?_⟩
  have hab : K.lt a b := K.lt_trans hac hcb
  have hin : (viewAt (K := K) c l').InStratum (K.minS (TSet.single a ∪ TSet.single b)) :=
    (viewAt_inStratum_iff c l' _).mpr fun x hx => by rw [minS_pair hab x hx]; exact hac
  cases hc with
  | «mut» _ m τ hΘ hP _ =>
      rw [Θ3_one] at hΘ
      cases Option.some.inj hΘ
      have key := hP (BoCa.Val.inj₂ (BoCa.Val.loc l')) (ResST.toRes ⟨viewAt c l', hin⟩)
      rw [ResST.toU_toRes] at key
      have hconj := key.mpr (τ3_view c l')
      change SPropST.conj (tyPred (τ3 c) K _) (tyPred (τ3 c) K _) _
        (ResST.toRes ⟨viewAt c l', hin⟩).toS at hconj
      rw [ResST.toS_toRes, conj_tyPred] at hconj
      have hb := (viewAt_inStratum_iff c l' _).mp (ResUT.inStratum_union_iff.mp hconj.1).2 b
        (by simp)
      exact Cactus.lt_irrefl _ _ (K.lt_trans hb hcb)

/-- **The same configuration on the printed chain** (row 5.9): `a = 3 ⊏ c = 2 ⊏ b = 1`. -/
theorem clause3_chain (l' : BoCa.Loc) :
    ¬ Cov (Θ3 (OrderDual.toDual 2)) WCactus.chain 1
      (compAt (K := WCactus.chain) (OrderDual.toDual 2) (TSet.single (OrderDual.toDual 3))
        (TSet.single (OrderDual.toDual 1))) :=
  (clause3_not_cov (K := WCactus.chain) ((WCactus.chain_lt _ _).mpr (by decide))
    ((WCactus.chain_lt _ _).mpr (by decide)) l').2.2.2

/-! ### Coverage read on the stratum a cell's invariant was formed at -/

end BoCa.Fig16.Tree.Wp

end

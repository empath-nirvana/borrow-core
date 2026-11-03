import Support.Model.Tree.Carrier

/-!
# Where the printed model compares two lifetimes, read in a tree

`[spec §62]`. Row 5.9 orders `Life` as a single chain (`ℕᵒᵈ`). The tree-stratified carrier
(`Tree/Carrier.lean`) reads `⊐` in a cactus instead. A scan of the elaborated terms (the #770
spike's `Tree/ChainUses.lean`, recorded in `docs/new-core/evidence.md`; it reads that
experiment's typed worlds, so it is not in the library) lists every declaration in the closure
of the printed lemmas #770 asks about, of `TW`'s and `TWNC`'s invariants and of the relation's
resource clauses, whose term reads `Life` as a single chain. They fall into five classes. This
file gives each its Lean evidence: a tree statement proved, or a tree configuration where the
chain's fact fails.

**1. The carrier: strata and the cell operations.** `CellU.CompR.mutMut` and the declarations
that mention it (`○` clause 3, `mut(α ⊓ β, v, ρ, P̂ ∧ Q̂)`, row 5.16; `SPropS.conj*`,
`InStratum.inf_left`, `compR_assoc_forward`, `compR_mutMut_*`, `compatR_iff`, `CompR.*`,
`lift_view`, `compR_mut_src`, `CompR.back_view`, `CompR.lift_full`); `LSet.union` (`●` of two
`imm` cells, row 5.15, recomputing `⊔` and `⊓` by `Nat.le_total`); `compS._proof_1`,
`compS_assoc`, `InStratum.sup` (the composite's witness in `Res_{⊔(ᾱ₁ ∪ ᾱ₂)}`);
`CellU.CompS.at`, `atOn*`, `cellCompR_*`, `cellCompS_inStratum`, `CompS.inStratum` (`@` of a
composite as a `⊓`); `Life.meet_*`.
  * `○` clause 3 needs a stratum holding both cells' strata. In a tree it exists for siblings
    (`siblings_common_stratum`) and not for cousins (`cousins_no_common_stratum`). The tree
    carrier restates the clause: a `mut` cell carries an antichain `β̄`, and
    `mut(β̄₁) ○ mut(β̄₂) = mut(min(β̄₁ ∪ β̄₂))` (`Tree/CarrierOps.lean`). At the chain every
    antichain is a singleton and the clause is the printed one (`chain_compR_iff`).
  * `Res_{⊔ᾱ}` fails in a tree (`Cactus.star_sup_lt_fails`) and is restated as `⋂_{x ∈ ᾱ} Res_x`
    (`Res_ᾱ` in the tree carrier, equal to the printed at the chain, `ΦU_inStratum_iff`);
    `⊓ᾱ` is read universally
    (`LSet.le_meet_iff`, `LSet.meet_lt_iff`).

**2. A fresh lifetime: `↓α` (row 5.12).** `Life.down_sqsubset`, `Life.not_lt_of_down_lt`,
`Life.le_of_down_lt`, `six27`, `six52_H1`, `six52_sub_inStratum`, `reb_inStratum_down`,
`updV_outlives_at`, `flat_inStratum_at`, `AgW.inStratum_at`, `ExW.inStratum_at`,
`not_at_lt_of_inStratum_down`, `wit_inStratum_of_down`, `Sub.inStratum`. What is read of `↓α`
is that nothing lies strictly between it and `α`; every covering child has that
(`Cactus.Covers.le_of_lt`). Restatement: `↓α` is a covering child, of which a tree has many
(`Cactus.star_covers_top`). The ported lemmas read it as a stratum below `α`
(`WCactus.DownOf`, `Tree/Port/Down.lean`).

**3. Two bounds below which a lifetime is chosen** (И combined with И or with a resource):
`fresh_frame` (6.112, `@ρ_P ⊓ β`), `wp_M_frame` (6.65 H4, `↓(γ ⊓ β)`), `exists_shorter`
(6.150 H11, `↓(γᵢ ⊓ γ_b)`), `wp_I_frame` (6.64 H4, through 6.112). Needs a common lower bound,
which in a tree exists only for comparable lifetimes (`Cactus.comparable_of_lower`,
`Cactus.star_no_lower`). Holds for lifetimes on one branch: `exists_below_two` (6.150 H11 and
6.65 H4). 6.112 and 6.64 are entailments and a `wp` rule, read over the relation; they move to
the tree order with it (#771, tree lifetimes in the semantics).

**4. A lifetime below the whole world.** `TW.reb`'s `StratumLe W β`, `TW.rebDeep`'s
`W.InStratum β`, `TW.rebEnd`'s `W′.InStratum β`, and `frameLife_reb_like` (`le_of_not_gt` on
`StratumLe`). A world holding two siblings lies in no stratum
(`no_stratum_below_siblings`). These premises need every lifetime of the world to be
comparable. The spike's `TWN`/`TWNC` replace them by premises read at one record
(`RebRecLe`, `RebEndRec`, `RebCellLe`), which compare only lifetimes of one lineage; they move
into the library with the typed world (#774).

**5. `⊓ᾱ ∈ ᾱ` used to get a member.** `LSet.ext`, `LSet.meet_mono_of_subset`,
`LSet.notMem_of_meet_sqsupset`, `ti_endReb`, `ti_rebDeep`, `ti_endRebN`, and (outside the scan's
closure) the spike's `TWN`, `LinDisj` and `Uncapture`. Each picks `⊓ᾱ` as a member, then reads a
clause stated at every member (`FrameLife`'s first clause, `RebEndRec`, `hβs`). Any member serves,
and `ᾱ ≠ ∅` (`join_mem`). Read, not rebuilt.

`ptoImmS`, `ptoMutS`, `Ext`, `box`, `LtLife` belong to the relation, which stays on the printed
carrier until the later PRs of #771; the spike restates them, equal to the printed at the chain.
The scan finds no comparability inside them.

Not in the scan's closure, and not restated: the interpretation of lifetime terms (row 2.54,
`@b₁ ⊓ @b₂` and `@b₁ ⊔ @b₂` as `max`/`min` on `ℕ`) and `LifeCtx.Models` (row 2.52, `SLife.Lt`).
A type's lifetimes are those in scope where it is written, on one branch; `⊓` of two of them is
class 3.

No lemma ported to the tree carrier (`Tree/Port/`, Lemmas 6.1–6.59 but 6.40 and 6.45) needs two
lifetimes to be comparable.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

/-- `1` and `2` children of `⊤`, `3` a child of `1`, `4` a child of `2`, every other a child
of `⊤`: `3` and `4` are cousins. -/
def cousinsP : ParentFn where
  par n := if n = 3 then 1 else if n = 4 then 2 else 0
  rank n := n
  par_zero := by simp
  rank_lt n hn := by
    show (if n = 3 then 1 else if n = 4 then 2 else 0) < n
    split_ifs <;> omega

theorem cousinsP_inAlloc : cousinsP.InAlloc := cousinsP.rank_lt

/-- The cousins cactus. -/
abbrev cousins : Cactus := Cactus.ofParent cousinsP

theorem cousins_lt_3_1 : cousins.lt (OrderDual.toDual 3) (OrderDual.toDual 1) :=
  ⟨.up (by show cousinsP.Anc (cousinsP.par 3) 1; simp [cousinsP]; exact .refl 1),
    fun h => by have := congrArg OrderDual.ofDual h; simp at this⟩

theorem cousins_lt_4_2 : cousins.lt (OrderDual.toDual 4) (OrderDual.toDual 2) :=
  ⟨.up (by show cousinsP.Anc (cousinsP.par 4) 2; simp [cousinsP]; exact .refl 2),
    fun h => by have := congrArg OrderDual.ofDual h; simp at this⟩

theorem cousins_not_le_1_2 : ¬ cousins.le (OrderDual.toDual 1) (OrderDual.toDual 2) := by
  intro h
  change cousinsP.Anc 1 2 at h
  cases h with
  | up h' =>
      have : cousinsP.par 1 = 0 := by simp [cousinsP]
      rw [this] at h'
      exact absurd (h'.le cousinsP_inAlloc) (by omega)

theorem cousins_not_le_2_1 : ¬ cousins.le (OrderDual.toDual 2) (OrderDual.toDual 1) := by
  intro h
  change cousinsP.Anc 2 1 at h
  cases h with
  | up h' =>
      have : cousinsP.par 2 = 0 := by simp [cousinsP]
      rw [this] at h'
      exact absurd (h'.le cousinsP_inAlloc) (by omega)

/-! ### Class 1: `○` clause 3 in a tree-stratified carrier -/

/-- **No stratum holds the strata of two cousins.** A stratum `γ` holding `Res_α` and `Res_β`
(every lifetime strictly above `α` or `β` is strictly above `γ`) is what `○` clause 3 needs for
two `mut` cells at `α` and `β`. At `α = 3`, `β = 4` it would lie below `1` and `2`. -/
theorem cousins_no_common_stratum :
    ¬ ∃ γ, (∀ x, cousins.lt (OrderDual.toDual 3) x → cousins.lt γ x) ∧
      (∀ x, cousins.lt (OrderDual.toDual 4) x → cousins.lt γ x) := by
  rintro ⟨γ, h₃, h₄⟩
  rcases Cactus.comparable_of_lower cousins (h₃ _ cousins_lt_3_1).le
      (h₄ _ cousins_lt_4_2).le with h | h
  · exact cousins_not_le_1_2 h
  · exact cousins_not_le_2_1 h

/-- Siblings have one: each other's stratum. Strata in a tree are the strict ancestors, and
siblings share them. -/
theorem siblings_common_stratum (K : Cactus) {α β p : Life} (hα : K.Covers α p)
    (hβ : K.Covers β p) : ∀ x, K.lt β x → K.lt α x := by
  intro x hx
  exact Cactus.lt_of_lt_of_le hα.1 (hβ.le_of_lt hx)

/-! ### Class 3: two bounds on one branch -/

/-- **6.150 H11 and 6.65 H4 in the tree order.** Two bounds on `n`'s branch, and `n` has a
child: a lifetime strictly below both. The printed `↓(γ ⊓ β)` is that child. -/
theorem exists_below_two (K : Cactus) {n g₁ g₂ : Life} (h₁ : K.le n g₁) (h₂ : K.le n g₂)
    (hchild : ∃ c, K.lt c n) : ∃ b, K.lt b g₁ ∧ K.lt b g₂ := by
  obtain ⟨c, hc⟩ := hchild
  exact ⟨c, Cactus.lt_of_lt_of_le hc h₁, Cactus.lt_of_lt_of_le hc h₂⟩

/-- Off one branch there is none: `1` and `2` in `star`. -/
theorem star_none_below_two :
    ¬ ∃ b, Cactus.star.lt b (OrderDual.toDual 1) ∧ Cactus.star.lt b (OrderDual.toDual 2) :=
  fun ⟨b, h₁, h₂⟩ => Cactus.star_no_lower (m := 1) (n := 2) (by decide) (by decide)
    (by decide) ⟨b, h₁.le, h₂.le⟩

/-! ### Class 4: a lifetime below the whole world -/

variable {Loc Val : Type}

/-- **A world holding cells at two incomparable lifetimes lies in no stratum**: `StratumLe W β`
and `W.InStratum β`, read in a tree, are false. A member `z` of the stratum would lie strictly
below both lifetimes, which makes them comparable. -/
theorem no_stratum_below_siblings {K : WCactus} {W : ResUT Loc Val K} {l₁ l₂ : Loc}
    {ψ₁ ψ₂ : CellUT Loc Val K} {s₁ s₂ : TSet} {x y : Life} (e₁ : W.get l₁ = some ψ₁)
    (e₂ : W.get l₂ = some ψ₂) (h₁ : ψ₁.lsOf = some s₁) (h₂ : ψ₂.lsOf = some s₂)
    (hx : x ∈ s₁.set) (hy : y ∈ s₂.set) (hxy : ¬ K.le x y ∧ ¬ K.le y x) :
    ¬ ∃ S, W.InStratum S := by
  rintro ⟨S, hS⟩
  obtain ⟨z, hz⟩ := S.ne
  have below : ∀ {l : Loc} {ψ : CellUT Loc Val K} {s : TSet} {w : Life}, W.get l = some ψ →
      ψ.lsOf = some s → w ∈ s.set → K.lt z w := by
    intro l ψ s w e h hw
    have hψ := hS l ψ e
    cases ψ with
    | own _ => cases h
    | imm i => cases h; exact hψ z hz w hw
    | «mut» m => cases h; exact hψ z hz w hw
  rcases Cactus.comparable_of_lower K.toCactus (below e₁ h₁ hx).le (below e₂ h₂ hy).le with
    h | h
  · exact hxy.1 h
  · exact hxy.2 h

/-- The instance: two `imm` views at the siblings `1` and `2` of the cousins cactus. -/
theorem cousins_world_no_stratum {W : ResUT Loc Val (WCactus.ofParent cousinsP)} {l₁ l₂ : Loc}
    {v₁ v₂ : Val} {σ₁ σ₂ : ResUT Loc Val (WCactus.ofParent cousinsP)}
    {h₁ : σ₁.InStratum (TSet.single (OrderDual.toDual 1))}
    {h₂ : σ₂.InStratum (TSet.single (OrderDual.toDual 2))}
    (e₁ : W.get l₁ = some (CellUT.immOf (TSet.single (OrderDual.toDual 1)) v₁ σ₁ h₁))
    (e₂ : W.get l₂ = some (CellUT.immOf (TSet.single (OrderDual.toDual 2)) v₂ σ₂ h₂)) :
    ¬ ∃ S, W.InStratum S :=
  no_stratum_below_siblings e₁ e₂ rfl rfl (Finset.mem_singleton_self _)
    (Finset.mem_singleton_self _) ⟨cousins_not_le_1_2, cousins_not_le_2_1⟩

end BoCa.Fig16.Tree

end

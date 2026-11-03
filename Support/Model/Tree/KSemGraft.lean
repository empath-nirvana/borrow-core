import Support.Model.Tree.KSem

/-!
# Round 7 with cell invariants read at the tree  `[spec §62]`

`Tree/CarrierGraftEx.lean`'s configuration: before the graft (`K₀`) the task's lend `α = 1` and
the handler's later lend `β = 2` are siblings under `⊤`; the handler resumes the task inside `β`,
and after the graft (`K₁`) `α` is a child of `β`. No lifetime is renamed.

Before the graft the task created a `mut` cell at `ℓ₁ = 1` at `{α}`. Its contents have type
`1 + Imm @α 1` (`τc`); the location typing `Θ₇` gives `ℓ₁` that type. It holds `inj₁ ()`. The
handler holds its view of `ℓ₂ = 2` at `{β}`.

* `round7_refused_before`: at `K₀` the handler's borrow is not a value of `τc`: `β` does not
  outlive `α`.
* `round7_write`: the world, re-read at `K₁` (`reread`), is valid and covered; the task's cell
  there stores `τc` read at `K₁`; the task writes `inj₂ ℓ₂`, holding a copy of the handler's view
  at `β`, into that cell, keeping its lifetime set `{α}` and its invariant. The world after the
  write is valid, covered at `K₁`, and the cell's witness lies in `Res_{α}` read in `K₁`. A
  stored task whose continuation is a thunk over the cell at `K₀` is a thunk over the re-read
  cell at `K₁` (`kmono_thunk`).
* `trU_not_kmono`: carried by `trU` instead, the task's cell is no longer a value of `Mut @α τc`
  at `K₁`.
-/

noncomputable section

namespace BoCa.Fig16.Tree
open BoCa.Fig16

/-- The contents' type: `1 + Imm @α 1`. -/
def τc : KSem := vSum vUnit (vImm αL vUnit)

open Classical in
/-- The location typing: `ℓ₁ = 1` holds `τc`. -/
def Θ₇ : LocTy := fun l => if l = 1 then some τc else none

theorem monoΘ₇ : MonoΘ Θ₇ := by
  intro l τ h
  simp only [Θ₇] at h
  split at h
  · cases Option.some.inj h
    exact kmono_sum kmono_unit (kmono_imm kmono_unit)
  · cases h

theorem Θ₇_one : Θ₇ 1 = some τc := by simp [Θ₇]

/-- `inj₁ () ∈ τc` with the empty resource, at any tree. -/
theorem τc_inj₁ (K : WCactus) : τc.P K (BoCa.Val.inj₁ BoCa.Val.unit) PMap.empty :=
  Or.inl ⟨_, rfl, rfl, rfl⟩

/-- The task's cell before the graft: `mut({α}, inj₁ (), ∅, τc read at K₀)`. -/
def cell₀ : TCell K₀ :=
  CellUT.mutOf (TSet.single αL) (BoCa.Val.inj₁ BoCa.Val.unit) PMap.empty
    (fun _ _ e => by simp at e) (fun w r => τc.P K₀ w r.val) (τc_inj₁ K₀)

/-- The handler's view at `β`. -/
abbrev hand (K : WCactus) : TCell K := leafImm (TSet.single βL) BoCa.Val.unit

/-- The world before the graft. -/
def W₀ : TRes K₀ := PMap.pair 1 cell₀ 2 (hand K₀)

theorem cov_leaf {K : WCactus} (l : BoCa.Loc) (t : TSet) (u : BoCa.Val) :
    Cov Θ₇ K l (leafImm t u) := by
  refine Cov.imm l _ fun k ψ e => ?_
  have hw : (leafImm (K := K) (Loc := BoCa.Loc) t u).wit = PMap.empty := leafImm_wit t u
  change (CellUT.imm _).wit.get k = some ψ at e
  rw [show (CellUT.imm _ : TCell K) = leafImm t u from rfl, hw] at e
  simp at e

theorem cov_pair {K : WCactus} {a b : TCell K} (ha : Cov Θ₇ K 1 a) (hb : Cov Θ₇ K 2 b) :
    CovR Θ₇ K (PMap.pair 1 a 2 b) := by
  intro l ψ e
  rw [PMap.pair_get] at e
  split at e
  · subst l; cases Option.some.inj e; exact ha
  · split at e
    · subst l; cases Option.some.inj e; exact hb
    · cases e

theorem cov_W₀ : CovR Θ₇ K₀ W₀ := by
  refine cov_pair ?_ (cov_leaf _ _ _)
  refine Cov.mut 1 _ τc Θ₇_one (fun _ _ => Iff.rfl) fun k ψ e => ?_
  have hw : cell₀.wit = PMap.empty := CellUT.wit_mutOf _ _ _ _ _ _
  change cell₀.wit.get k = some ψ at e
  rw [hw] at e; simp at e

theorem valid_W₀ : ResUT.Valid W₀ :=
  valid_pair (by decide) cell₀ rfl _ _ (Or.inl (CellUT.wit_mutOf _ _ _ _ _ _))

theorem Val.inj₁_ne_inj₂ (v w : BoCa.Val) : BoCa.Val.inj₁ v ≠ BoCa.Val.inj₂ w := by
  intro h
  have := congrArg Subtype.val h
  simp at this

theorem Val.inj₂_inj {v w : BoCa.Val} (h : BoCa.Val.inj₂ v = BoCa.Val.inj₂ w) : v = w := by
  have := congrArg Subtype.val h
  simp only [BoCa.Val.val_inj₂, Expr.inj₂.injEq] at this
  exact Subtype.ext this

/-- **Before the graft the handler's borrow is not a value of the cell's type**: a view at `β` is
`Imm @α` only where `β` outlives `α`, and at `K₀` they are siblings. -/
theorem round7_refused_before :
    ¬ τc.P K₀ (BoCa.Val.inj₂ (BoCa.Val.loc 2)) (borrowAt K₀ 2 BoCa.Val.unit) := by
  classical
  rintro (⟨v₁, h, -⟩ | ⟨v₂, h₂, l, i, hl, hρ, hle, -⟩)
  · exact Val.inj₁_ne_inj₂ _ _ h.symm
  · have hv := Val.inj₂_inj h₂
    subst hv
    have hl' : l = 2 := (BoCa.Val.loc_inj.mp hl).symm
    subst hl'
    have hg := congrArg (fun r : TRes K₀ => r.get 2) hρ
    simp only [borrowAt, PMap.sng_get, if_pos] at hg
    have hls : i.ls = TSet.single βL := by
      have h1 : (leafImm (K := K₀) (Loc := BoCa.Loc) (TSet.single βL) BoCa.Val.unit).lsOf =
          some (TSet.single βL) := CellUT.lsOf_immOf _ _ _ _
      have h2 : (CellUT.imm i).lsOf = some i.ls := rfl
      rw [← Option.some.inj hg] at h2
      exact Option.some.inj (h2.symm.trans h1)
    have hab := hle βL (by rw [hls]; simp)
    exact K₀_not_lt ⟨hab, by decide⟩

/-- The handler's borrow is a value of `τc` at `K₁`. -/
theorem round7_admitted_after :
    τc.P K₁ (BoCa.Val.inj₂ (BoCa.Val.loc 2)) (borrowAt K₁ 2 BoCa.Val.unit) := by
  refine Or.inr ⟨_, rfl, 2, ⟨TSet.single βL, BoCa.Val.unit, ResST.toRes ⟨PMap.empty, _⟩⟩, rfl,
    rfl, fun x hx => ?_, rfl, ResST.toU_toRes _⟩
  simp only [TSet.single_set, Finset.mem_singleton] at hx
  subst hx
  exact K₁_lt.le

/-- **Round 7, decided.** Re-read at `K₁`, the world is valid and covered, and the task's
pre-graft cell stores `τc` read at `K₁`. The task writes the handler's borrow at `β` into it,
keeping the cell's lifetime set `{α}` and its invariant. The world after the write is valid, is
covered at `K₁`, and the cell's witness lies in `Res_{α}` read in `K₁`. The task's
continuation, a thunk over the cell at `K₀`, is a thunk over the re-read cell at `K₁`. -/
theorem round7_write :
    ∃ (W₁ W₂ : TRes K₁) (m₁ m₂ : TMut K₁),
      RR Θ₇ W₀ W₁ ∧ ResUT.Valid W₁ ∧ CovR Θ₇ K₁ W₁ ∧
      RC Θ₇ 1 cell₀ (.mut m₁) ∧ W₁ = PMap.pair 1 (.mut m₁) 2 (hand K₁) ∧
      (∀ w r, m₁.P w r ↔ τc.P K₁ w r.toU) ∧
      W₂ = PMap.pair 1 (.mut m₂) 2 (hand K₁) ∧
      m₂.ls = m₁.ls ∧ m₂.ls = TSet.single αL ∧ m₂.P ≍ m₁.P ∧
      m₂.v = BoCa.Val.inj₂ (BoCa.Val.loc 2) ∧ m₂.res = borrowAt K₁ 2 BoCa.Val.unit ∧
      ResUT.Valid W₂ ∧ CovR Θ₇ K₁ W₂ ∧ m₂.res.InStratum (TSet.single αL) ∧
      ∀ (C : (K : WCactus) → BoCa.Val → TRes K → Prop) (v : BoCa.Val),
        (vThunk Θ₇ C).P K₀ v (PMap.sng 1 cell₀) →
        (vThunk Θ₇ C).P K₁ v (PMap.sng 1 (.mut m₁)) := by
  classical
  obtain ⟨W₁, hRR, hcov, hval, -⟩ := reread graftExt monoΘ₇ cov_W₀ valid_W₀
  -- the task's cell, re-read
  obtain ⟨ψ₁, e₁, hrc₁⟩ := hRR.get_some (m := 1) (ψ := cell₀) (by simp [W₀, PMap.pair_get])
  obtain ⟨m₀, em₀⟩ : ∃ m₀, cell₀ = CellUT.mut m₀ := ⟨_, rfl⟩
  have hrc₁' := hrc₁
  rw [em₀] at hrc₁
  cases hrc₁ with
  | «mut» _ _ m₁ τ hΘ hs _ _ _ hP₁ =>
  rw [Θ₇_one] at hΘ
  cases Option.some.inj hΘ
  have hls₀ : m₀.ls = TSet.single αL := by
    have h1 : cell₀.lsOf = some (TSet.single αL) := CellUT.lsOf_mutOf _ _ _ _ _ _
    have h2 : (CellUT.mut m₀).lsOf = some m₀.ls := rfl
    rw [← em₀] at h2
    exact Option.some.inj (h2.symm.trans h1)
  have hls : m₁.ls = TSet.single αL := by
    rw [hs, hls₀]; exact K₁.minS_of_anti (anti_single K₁ αL)
  -- the handler's view, re-read
  obtain ⟨ψ₂, e₂, hrc₂⟩ := hRR.get_some (m := 2) (ψ := hand K₀) (by simp [W₀, PMap.pair_get])
  have hψ₂ : ψ₂ = hand K₁ := by
    have hwit := hrc₂.wit
    rw [show (hand K₀).wit = PMap.empty from leafImm_wit _ _] at hwit
    have hψw := RR.of_empty hwit
    cases hrc₂ with
    | imm _ _ i' hs' hv' _ _ =>
        exact congrArg CellUT.imm (ImmT.eq_of hs' hv' (hψw.trans
          (leafImm_wit (K := K₁) (Loc := BoCa.Loc) _ _).symm))
  subst hψ₂
  have hW₁ : W₁ = PMap.pair 1 (.mut m₁) 2 (hand K₁) := by
    refine PMap.ext fun l => ?_
    rw [PMap.pair_get]
    by_cases a : l = 1
    · subst a; rw [if_pos rfl, e₁]
    · by_cases b : l = 2
      · subst b; rw [if_neg a, if_pos rfl, e₂]
      · rw [if_neg a, if_neg b]
        exact (hRR.1 l).mp (by simp [W₀, PMap.pair_get, a, b])
  -- the write
  have hS : (borrowAt K₁ 2 BoCa.Val.unit).InStratum m₁.ls := by
    rw [hls]; exact (borrowAt_inStratum_iff K₁ 2 BoCa.Val.unit).mpr K₁_lt
  let m₂ : TMut K₁ := ⟨m₁.ls, m₁.anti, BoCa.Val.inj₂ (BoCa.Val.loc 2),
    ResST.toRes ⟨borrowAt K₁ 2 BoCa.Val.unit, hS⟩, m₁.P, by
      refine (hP₁ _ _).mpr ?_
      rw [ResST.toU_toRes]; exact round7_admitted_after⟩
  have hres₂ : m₂.res = borrowAt K₁ 2 BoCa.Val.unit := ResST.toU_toRes _
  refine ⟨W₁, PMap.pair 1 (.mut m₂) 2 (hand K₁), m₁, m₂, hRR, hval, hcov, hrc₁', hW₁, hP₁, rfl,
    rfl, hls, HEq.rfl, rfl, hres₂, ?_, ?_, hres₂ ▸ hls ▸ hS, ?_⟩
  · exact valid_pair (by decide) (.mut m₂) rfl _ _ (Or.inr hres₂)
  · refine cov_pair (Cov.mut 1 m₂ τc Θ₇_one hP₁ fun k ψ e => ?_) (cov_leaf _ _ _)
    change m₂.res.get k = some ψ at e
    rw [hres₂, borrowAt, PMap.sng_get] at e
    split at e
    · subst k; cases Option.some.inj e; exact cov_leaf _ _ _
    · cases e
  · intro C v h
    exact kmono_thunk K₀ K₁ graftExt v _ _
      (fun l ψ e => by
        rw [PMap.sng_get] at e
        split at e
        · subst l; cases Option.some.inj e; exact cov_W₀ 1 cell₀ (by simp [W₀, PMap.pair_get])
        · cases e)
      (RR.sng hrc₁') h

/-- **Rules out a `Mut` whose invariant is carried, not re-read.** This is the shape of a type
whose meaning is not monotone along tree extension: a value stored before a graft stops meeting
its type after it. The former it rules out is `Mut @a A` with the cell's invariant kept as the
predicate it was stored with (row 5.57's `SProp_α ⊆ SProp_α'`, extension by falsity, which `trU`
implements), in place of the store type re-read at the grown tree (`RC`, `kmono_mut`).

**Monotonicity carried by `trU` fails at `Mut`.** The task's cell at `K₀` is a value of
`Mut @α τc`; carried to `K₁` by `trU` it is not, because `trU` keeps the stored predicate as the
image of the old one (row 5.57's extension by falsity), which refuses the handler's borrow that
`τc` read at `K₁` admits. This is why the transport of `Tree/KSem.lean` re-reads invariants. -/
theorem trU_not_kmono :
    (vMut Θ₇ αL τc).P K₀ (BoCa.Val.loc 1) (PMap.sng 1 cell₀) ∧
    ¬ (vMut Θ₇ αL τc).P K₁ (BoCa.Val.loc 1) ((PMap.sng 1 cell₀).map (trU graftExt)) := by
  classical
  obtain ⟨m₀, em₀⟩ : ∃ m₀, cell₀ = CellUT.mut m₀ := ⟨_, rfl⟩
  have hls₀ : m₀.ls = TSet.single αL := by
    have h1 : cell₀.lsOf = some (TSet.single αL) := CellUT.lsOf_mutOf _ _ _ _ _ _
    have h2 : (CellUT.mut m₀).lsOf = some m₀.ls := rfl
    rw [← em₀] at h2
    exact Option.some.inj (h2.symm.trans h1)
  have hP₀ : ∀ w r, m₀.P w r ↔ τc.P K₀ w r.toU := by
    have := cov_W₀ 1 cell₀ (by simp [W₀, PMap.pair_get])
    rw [em₀] at this
    cases this with
    | «mut» _ _ τ hΘ hP _ =>
        rw [Θ₇_one] at hΘ; cases Option.some.inj hΘ; exact hP
  constructor
  · rw [em₀]
    refine ⟨1, m₀, rfl, rfl, Θ₇_one, fun x hx => ?_, hP₀⟩
    rw [hls₀] at hx
    simp only [TSet.single_set, Finset.mem_singleton] at hx
    subst hx; exact K₀.refl _
  · rintro ⟨l, m, hl, hρ, -, -, hP⟩
    have hl' : l = 1 := (BoCa.Val.loc_inj.mp hl).symm
    subst hl'
    have h1 := congrArg (fun ρ : TRes K₁ => ρ.get 1) hρ
    simp only [PMap.map_get, PMap.sng_get, if_pos, Option.map_some] at h1
    replace h1 := Option.some.inj h1
    rw [em₀] at h1
    simp only [trU, CellUT.mutOf] at h1
    injection h1 with h2
    subst h2
    have hS : (borrowAt K₁ 2 BoCa.Val.unit).InStratum (K₁.minS m₀.ls) := by
      rw [hls₀, K₁.minS_of_anti (anti_single K₁ αL)]
      exact (borrowAt_inStratum_iff K₁ 2 BoCa.Val.unit).mpr K₁_lt
    have := (hP (BoCa.Val.inj₂ (BoCa.Val.loc 2)) (ResST.toRes ⟨_, hS⟩)).mpr
      (by rw [ResST.toU_toRes]; exact round7_admitted_after)
    obtain ⟨r₀, hr₀, -⟩ := this
    rw [ResST.toS_toRes, Tr_map] at hr₀
    exact graft_carried_refuses 2 BoCa.Val.unit r₀.toU (hls₀ ▸ r₀.toU_inStratum) hr₀

end BoCa.Fig16.Tree

end

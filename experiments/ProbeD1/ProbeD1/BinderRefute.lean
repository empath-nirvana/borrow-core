import ProbeD1.BinderPVRun

/-!
# ProbeD1 — four of the design's statements, refuted at configurations the index admits

Each refutation is a fact about one of `BINDER.md`'s statements, at a configuration that meets
every hypothesis the statement takes. None is shown to arise (DESIGN §11), so none is an
obstruction; each names a step of the design's plan that the build then revises (`BINDER.md`
§11).

* **`not_extInst`**: an extension of the list is not always one of the instantiated lists. `Ext`
  keeps a record relevant to the resource as a `FrameRec`, forgetting its tag, so the extension
  can hold the record at a tag the instantiation leaves alone while the original holds it at a
  tag it moves. The design's composite (`ThawInst`, the thaw of a `U` slot) rests on this step.
* **`not_cohEInst`**: at an outermost lend at `⊤` the cut is `⊤` itself, a record at `⊤` is left
  alone, and `RecsOutside` says nothing of it; its reading of a variable below `⊤` moves in the
  slot's reading and not in the record's.
* **`not_mutPayloadInst`, `not_instEquivLeaf`, `not_ctxRelendsThawFree`**: the support conjunct of
  a retained `mut` cell's payload is not kept by an instantiation. The payload
  `1 ⊕ Imm 'x (Imm 'x (Imm 'x 1))` at `'x ↦ 1` has no resource in its second branch: three
  nested `imm` cells need three distinct lifetimes at or above `1`, and only `1` and `⊤ = 0` are.
  The shift `n ↦ n + 1` reads `'x` at `2`, and its gap at `1` makes the room: cells at `2`, `1`,
  `0`. So a payload supported in `Res_⊤` at the reading is not at the instantiated one, at a list
  holding the three coherence records. This is `mut_not_natural`'s mechanism (a cell at a lifetime
  in the instantiation's gap) at the retained part of an order-preserving instantiation, through
  the support conjunct the design's §3.6 named. At `binder0`, a context holding such a cell at `⊤`
  in a slot `m : Mut '0 (1 ⊕ Imm '0 (Imm '0 (Imm '0 1)))`, at the stack `[qEnt]` at `1`, meets
  every hypothesis of `CtxRelendableAtI` and is `CtxThawFree`, and the thaw fails: the partial
  target `Statement0UThawFree binder0` is false as stated.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack LKind extS vwE vwS vis stratS ReLend TabAtS)

/-! ### Small lists of records -/

/-- The members of `ls` strictly longer-lived than `b`. -/
def lsAbove (ls : List SRec) (b : Life) : List SRec := ls.filter fun x => decide (b < x.2)

theorem mem_lsAbove {ls : List SRec} {b : Life} {x : SRec} :
    x ∈ lsAbove ls b ↔ x ∈ ls ∧ x.2 ⊐ b := by
  unfold lsAbove
  rw [List.mem_filter, decide_eq_true_iff]

/-! ### `ExtInst` -/

/-- The record `ExtInst`'s refutation moves: at the place `0`, reading `'0 ↦ 7`. -/
abbrev eiRec : FrameRec := ⟨0, Val.unit, PMap.empty, .unit, ⟨[(0, 7)]⟩⟩

/-- An `imm` cell at `1`, at the place `0`. -/
abbrev eiCell : CellU BoCa.Loc Val :=
  CellU.immOf (LSet.singleton (lifeN 1)) Val.unit PMap.empty (ResU.inStratum_empty _)

abbrev eiρ : WRes := ResU.single 0 eiCell

theorem eiRel : Core.Rel eiRec eiρ :=
  ⟨0, eiCell, ResU.single_get_self _ _, rfl, Or.inl rfl⟩

theorem cellIn_eiρ {b : Life} (h : CellIn eiρ b) : lifeN 1 ≤ b := by
  obtain ⟨m, ψ, hg, -, hle⟩ := h
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hg
  exact hle

/-- **`ExtInst` is false as stated.** The original list holds the record at `5`, below the cut
`2` of the stack `[3]`, and the extension holds it at `1`, above: `Ext` keeps relevant records
untagged. The instantiation moves the first and not the second, and the moved record's reading is
not the kept one's. -/
theorem not_extInst : ¬ ExtInst := by
  intro h
  have hat : InstAt [lifeN 3] (Inst.ofEmb (Restrat.Emb.shift (lifeN 2) 1)) := by
    intro c θ hc
    cases hc
    rfl
  have hz : stratS [lifeN 3] eiρ := by
    intro a ha
    obtain rfl : a = lifeN 3 := (Option.some.inj ha).symm
    exact ResU.inStratum_single _ (show lifeN 3 < lifeN 1 from by decide)
  have hext : Ext [(eiRec, lifeN 5)] [(eiRec, lifeN 1)] eiρ := by
    refine ⟨fun r hr _ => ?_, fun b hb x hx => ?_⟩
    · simp only [rsOf, List.map_cons, List.map_nil, List.mem_singleton] at hr ⊢
      exact hr
    · have h1 := cellIn_eiρ hb
      constructor
      · intro hm
        rw [List.mem_singleton] at hm
        subst hm
        exact absurd (lt_of_le_of_lt h1 hx) (by decide)
      · intro hm
        rw [List.mem_singleton] at hm
        subst hm
        exact absurd (lt_of_le_of_lt h1 hx) (by decide)
  have := (h _ _ eiρ [lifeN 3] _ hat hz hext).1
  have hmem : (Inst.rec1 (Inst.ofEmb (Restrat.Emb.shift (lifeN 2) 1)) (eiRec, lifeN 5)).1 ∈
      rsOf (Inst.recs (Inst.ofEmb (Restrat.Emb.shift (lifeN 2) 1)) [(eiRec, lifeN 5)]) := by
    rw [Inst.recs_eq_map]
    exact List.mem_map_of_mem (List.mem_map_of_mem List.mem_cons_self)
  have hrel : Core.Rel (Inst.rec1 (Inst.ofEmb (Restrat.Emb.shift (lifeN 2) 1))
      (eiRec, lifeN 5)).1 eiρ := (rel_rec1 _ _ _).mpr eiRel
  have hk := this _ hmem hrel
  rw [Inst.recs_eq_map] at hk
  simp only [List.map_cons, List.map_nil, rsOf, List.mem_singleton] at hk
  have hfix : Inst.rec1 (Inst.ofEmb (Restrat.Emb.shift (lifeN 2) 1)) (eiRec, lifeN 1) =
      (eiRec, lifeN 1) := Inst.rec1_fixed _ (show lifeN 2 ≤ lifeN 1 from by decide)
  rw [hfix, Inst.ofEmb, Inst.rec1_moved _ (show lifeN 5 < lifeN 2 from by decide)] at hk
  have hδ := congrArg FrameRec.δ hk
  simp only [Restrat.LSub.mapN, List.map_cons, List.map_nil] at hδ
  have h8 : (Restrat.Emb.shift (lifeN 2) 1).toNat 7 = 8 := rfl
  rw [h8] at hδ
  exact absurd hδ (by decide)

/-! ### `CohEInst` at an outermost lend at `⊤` -/

/-- A record at `⊤` reading `'0 ↦ 1`, its payload type `[@'0] 1`. -/
abbrev ctRec : FrameRec := ⟨0, Val.unit, PMap.empty, .box (.var 0) .unit, ⟨[(0, 1)]⟩⟩

theorem not_chain_empty {T : VTy} {v : Val} {p : Option BoCa.Loc} {m : BoCa.Loc} {S : VTy}
    {u : Val} (h : Chain (PMap.empty : WRes) T v p m S u) : False := by
  cases h with
  | one _ hg => exact absurd hg (by simp)
  | step _ hg _ => exact absurd hg (by simp)

/-- **`CohEInst` is false at an outermost lend at `⊤`.** The cut is `⊤`, the record at `⊤` is
left alone, `RecsOutside [⊤]` is vacuous, and the record reads `'0` at `1`, which the slot's
instantiated reading moves to `2`. -/
theorem not_cohEInst : ¬ CohEInst := by
  intro h
  have hcut : cutOf [(⊤ : Life)] = some ⊤ := rfl
  have hro : RecsOutside [(⊤ : Life)] [(ctRec, ⊤)] := by
    intro a ha x _ hlt
    rw [List.mem_singleton] at ha
    subst ha
    exact absurd hlt (not_lt.mpr le_top)
  have hcoh : CohE (rsOf [(ctRec, ⊤)]) 0 (.box (.var 0) .unit) ⟨[(0, 1)]⟩ :=
    ⟨_, _, TyEq.refl _ _, Or.inl ⟨ctRec, List.mem_singleton_self _, rfl, rfl, fun _ _ => rfl⟩⟩
  obtain ⟨S₀, δ₀, hty, hc⟩ := h [⊤] [(ctRec, ⊤)] 0 _ _ ⊤ (Restrat.Emb.shift ⊤ 1) hcut hro hcoh
  have hrecs : rsOf (Inst.recs (Inst.ofEmb (Restrat.Emb.shift ⊤ 1)) [(ctRec, ⊤)]) = [ctRec] := by
    rw [Inst.recs_eq_map]
    simp only [List.map_cons, List.map_nil, rsOf]
    rw [show Inst.rec1 (Inst.ofEmb (Restrat.Emb.shift ⊤ 1)) (ctRec, ⊤) = (ctRec, ⊤) from
      Inst.rec1_fixed _ le_rfl]
  rw [hrecs] at hc
  rcases hc with ⟨r, hr, -, hS, hag⟩ | ⟨r, hr, p, u, hch, -⟩
  · rw [List.mem_singleton] at hr
    subst hr
    subst hS
    have h0 : δ₀.find? 0 = some 1 := hag 0 (by simp [VFree, BoCa.Lifetime.Life.mentions])
    have hsub : Inst.sub (Inst.ofEmb (Restrat.Emb.shift ⊤ 1)) (⟨[(0, 1)]⟩ : LSub) = ⟨[(0, 2)]⟩ :=
      rfl
    rw [hsub] at hty
    obtain ⟨hi, -⟩ := hty
    simp only [BoCa.Lifetime.Life.interp] at hi
    rw [h0] at hi
    exact absurd hi (by decide)
  · rw [List.mem_singleton] at hr
    subst hr
    exact not_chain_empty hch

/-! ### The support conjunct at a retained `mut` cell -/

/-- `Imm 'x (Imm 'x (Imm 'x 1))`, `'x = '0`. -/
abbrev gB : VTy := .imm (.var 0) (.imm (.var 0) (.imm (.var 0) .unit))

/-- `1 ⊕ Imm 'x (Imm 'x (Imm 'x 1))`. -/
abbrev gT : VTy := .sum .unit gB

abbrev gs₁ : LSub := ⟨[(0, 1)]⟩

abbrev gs₂ : LSub := ⟨[(0, 2)]⟩

abbrev gθ : Restrat.Emb (⊤ : Life) := Restrat.Emb.shift ⊤ 1

theorem gθ_sub : Inst.sub (Inst.ofEmb gθ) gs₁ = gs₂ := rfl

theorem gT_coreStable : CoreStable gT := ⟨trivial, trivial⟩

/-- **The nested branch has no resource at `'x ↦ 1`**: three nested `imm` cells, the outer at or
above `1`, each witness strictly above its cell, need three lifetimes in `{1, 0}`. -/
theorem gB_unsat (ls : List SRec) (u : Val) (σ' : WRes) : ¬ vC true gB ls gs₁ u σ' := by
  rintro ⟨α, hα, ℓ₁, hk₁⟩
  have hα' : α = lifeN 1 := (Option.some.inj hα).symm
  subst hα'
  obtain ⟨-, S₁, u₁, σ₁, h₁, ls₁, -, hP₁, hle₁, -⟩ := pure_sep_iff.mp hk₁
  obtain ⟨α₂, hα₂, ℓ₂, hk₂⟩ := hP₁
  have hα₂' : α₂ = lifeN 1 := (Option.some.inj hα₂).symm
  subst hα₂'
  obtain ⟨-, S₂, u₂, σ₂, h₂, ls₂, hσ₁, hP₂, -, -⟩ := pure_sep_iff.mp hk₂
  obtain ⟨α₃, -, ℓ₃, hk₃⟩ := hP₂
  obtain ⟨-, S₃, u₃, σ₃, h₃, ls₃, hσ₂, -, -, -⟩ := pure_sep_iff.mp hk₃
  -- the strata
  have k₁ : S₁.join < S₂.meet := by
    have := h₁ ℓ₂ _ (by rw [hσ₁]; exact ResU.single_get_self _ _)
    exact this
  have k₂ : S₂.join < S₃.meet := by
    have := h₂ ℓ₃ _ (by rw [hσ₂]; exact ResU.single_get_self _ _)
    exact this
  have m₁ := S₁.meet_le_join
  have m₂ := S₂.meet_le_join
  have n₁ : OrderDual.ofDual S₁.meet ≤ 1 := hle₁
  have n₂ : OrderDual.ofDual S₁.join ≤ OrderDual.ofDual S₁.meet := m₁
  have n₃ : OrderDual.ofDual S₂.meet < OrderDual.ofDual S₁.join := k₁
  have n₄ : OrderDual.ofDual S₂.join ≤ OrderDual.ofDual S₂.meet := m₂
  have n₅ : OrderDual.ofDual S₃.meet < OrderDual.ofDual S₂.join := k₂
  omega

/-- **At `'x ↦ 1` the payload is supported in `Res_⊤`**: its only resource is the empty one. -/
theorem gT_support : ∀ ls u σ', vC true gT ls gs₁ u σ' → σ'.InStratum ⊤ := by
  intro ls u σ' h
  rcases h with ⟨v₁, hs⟩ | ⟨v₂, hs⟩
  · obtain ⟨-, hu⟩ := pure_sep_iff.mp hs
    obtain ⟨rfl, -⟩ := hu
    exact ResU.inStratum_empty _
  · obtain ⟨-, hB⟩ := pure_sep_iff.mp hs
    exact absurd hB (gB_unsat ls v₂ σ')

/-- The cells of the witness at `'x ↦ 2`: `0 ↦ imm({2}, 1, 1 ↦ imm({1}, 2, 2 ↦ imm({0}, (), ∅)))`. -/
abbrev gw₃ : WRes :=
  ResU.single 2 (CellU.immOf (LSet.singleton (lifeN 0)) Val.unit PMap.empty (ResU.inStratum_empty _))

theorem gw₃_in : gw₃.InStratum (LSet.singleton (lifeN 1)).join :=
  ResU.inStratum_single _ (show lifeN 1 < lifeN 0 from by decide)

abbrev gw₂ : WRes :=
  ResU.single 1 (CellU.immOf (LSet.singleton (lifeN 1)) (Val.loc 2) gw₃ gw₃_in)

theorem gw₂_in : gw₂.InStratum (LSet.singleton (lifeN 2)).join :=
  ResU.inStratum_single _ (show lifeN 2 < lifeN 1 from by decide)

abbrev gw₁ : WRes :=
  ResU.single 0 (CellU.immOf (LSet.singleton (lifeN 2)) (Val.loc 1) gw₂ gw₂_in)

/-- The coherence records, each at the reading `'x ↦ 2`. -/
abbrev gr₁ : FrameRec := ⟨0, Val.loc 1, gw₂, .imm (.var 0) (.imm (.var 0) .unit), gs₂⟩
abbrev gr₂ : FrameRec := ⟨1, Val.loc 2, gw₃, .imm (.var 0) .unit, gs₂⟩
abbrev gr₃ : FrameRec := ⟨2, Val.unit, PMap.empty, .unit, gs₂⟩

abbrev gls : List SRec := [(gr₁, lifeN 5), (gr₂, lifeN 1), (gr₃, lifeN 0)]

theorem coh_mem {L : List SRec} {r : FrameRec} {t : Life} (h : (r, t) ∈ L) :
    CohE (rsOf L) r.le r.T r.δ ∧ True := by
  refine ⟨⟨r.T, r.δ, TyEq.refl _ _, Or.inl ⟨r, ?_, rfl, rfl, fun _ _ => rfl⟩⟩, trivial⟩
  exact List.mem_map_of_mem (f := Prod.fst) h

/-- **At `'x ↦ 2` the nested branch has a resource at `2`**, at the list holding its three
coherence records: the instantiation's gap at `1` is the room. -/
theorem gT_violator : vC true gT gls gs₂ (.inj₂ (.loc 0)) gw₁ := by
  refine Or.inr ⟨.loc 0, pure_sep_mk rfl ⟨lifeN 2, rfl, 0, pure_sep_mk ⟨rfl, ?c₁⟩ ?p₁⟩⟩
  case c₁ => exact (coh_mem (r := gr₁) (t := lifeN 5) (by simp)).1
  case p₁ =>
    refine ⟨LSet.singleton (lifeN 2), Val.loc 1, gw₂, gw₂_in, lsAbove gls (lifeN 2), rfl, ?_,
      le_rfl, fun x => mem_lsAbove⟩
    refine ⟨lifeN 2, rfl, 1, pure_sep_mk ⟨rfl, ?c₂⟩ ?p₂⟩
    case c₂ =>
      exact (coh_mem (L := lsAbove gls (lifeN 2)) (r := gr₂) (t := lifeN 1)
        (mem_lsAbove.mpr ⟨by simp, by decide⟩)).1
    case p₂ =>
      refine ⟨LSet.singleton (lifeN 1), Val.loc 2, gw₃, gw₃_in,
        lsAbove (lsAbove gls (lifeN 2)) (lifeN 1), rfl, ?_,
        show lifeN 2 ≤ lifeN 1 from by decide, fun x => mem_lsAbove⟩
      refine ⟨lifeN 2, rfl, 2, pure_sep_mk ⟨rfl, ?c₃⟩ ?p₃⟩
      case c₃ =>
        exact (coh_mem (L := lsAbove (lsAbove gls (lifeN 2)) (lifeN 1)) (r := gr₃) (t := lifeN 0)
          (mem_lsAbove.mpr ⟨mem_lsAbove.mpr ⟨by simp, by decide⟩, by decide⟩)).1
      case p₃ =>
        exact ⟨LSet.singleton (lifeN 0), Val.unit, PMap.empty, ResU.inStratum_empty _,
          lsAbove (lsAbove (lsAbove gls (lifeN 2)) (lifeN 1)) (lifeN 0), rfl, ⟨rfl, rfl⟩,
          show lifeN 2 ≤ lifeN 0 from by decide, fun x => mem_lsAbove⟩

theorem gw₁_not_top : ¬ gw₁.InStratum ⊤ := by
  intro h
  have h2 : (⊤ : Life) < lifeN 2 := h 0 _ (ResU.single_get_self _ _)
  exact absurd h2 (not_lt.mpr le_top)

/-- **`MutPayloadInst` is false**: its support conjunct fails at `1 ⊕ Imm 'x (Imm 'x (Imm 'x 1))`,
the cell above the cut at `⊤`, the shift `n ↦ n + 1` below `⊤`. -/
theorem not_mutPayloadInst : ¬ MutPayloadInst := by
  intro h
  have := (h gT [] gs₁ ⊤ ⊤ gθ gT_coreStable le_rfl (fun _ hx => absurd hx List.not_mem_nil)
    gT_support).2 gls (.inj₂ (.loc 0)) gw₁
  rw [gθ_sub] at this
  exact gw₁_not_top (this gT_violator)

/-! ### At a retained cell -/

/-- The predicate the retained cell stores: `𝒱⟦1 ⊕ Imm 'x (Imm 'x (Imm 'x 1))⟧` at `'x ↦ 1`, in
`Res_⊤`. -/
def gQ : Val → SPropS BoCa.Loc Val ⊤ := fun v => SPropU.toS ⊤ (vC true gT [] gs₁ v)

theorem ofS_gQ : ofS gQ = vC true gT [] gs₁ := by
  funext v r
  apply propext
  constructor
  · rintro ⟨_, hS⟩; exact hS
  · intro hS; exact ⟨gT_support [] v r hS, hS⟩

theorem gQ_holds : gQ (.inj₁ .unit) ⟨PMap.empty, ResU.inStratum_empty ⊤⟩ :=
  Or.inl ⟨.unit, pure_sep_mk rfl ⟨rfl, rfl⟩⟩

/-- The retained cell: a `mut` cell at `⊤` holding `inj₁ ()`, storing `gQ`. -/
abbrev gCell : CellU BoCa.Loc Val :=
  CellU.mutOf ⊤ (.inj₁ .unit) PMap.empty (ResU.inStratum_empty ⊤) gQ gQ_holds

abbrev gρ : WRes := ResU.single 5 gCell

/-- The slot type: `Mut 'x (1 ⊕ Imm 'x (Imm 'x (Imm 'x 1)))`. -/
abbrev gA : VTy := .mut (.var 0) gT

/-- The retained cell is a value of the slot type at `'x ↦ 1`. -/
theorem gA_holds : vC true gA [] gs₁ (.loc 5) gρ := by
  refine ⟨lifeN 1, rfl, 5, pure_sep_mk rfl ?_⟩
  refine ⟨⊤, .inj₁ .unit, PMap.empty, ResU.inStratum_empty ⊤, gQ, gQ_holds, [], le_top, rfl,
    ofS_gQ, fun x => ?_, gT_support⟩
  simp

/-- At `'x ↦ 2` the same cell is not: its stored predicate's support fails. -/
theorem gA_fails (ls : List SRec) : ¬ vC true gA ls gs₂ (.loc 5) gρ := by
  rintro ⟨α, -, ℓ, hk⟩
  obtain ⟨-, b, u, χ, hχ, Q, hw, ls₀, -, hρ, -, -, hsupp⟩ := pure_sep_iff.mp hk
  have hg := congrArg (fun r => PMap.get r 5) hρ
  simp only [ResU.single_get_self] at hg
  have hℓ : ℓ = 5 := by
    by_contra hne
    rw [ResU.single_get_ne _ (Ne.symm hne)] at hg
    exact absurd hg (by simp)
  subst hℓ
  rw [ResU.single_get_self] at hg
  have hb : (⊤ : Life) = b := CellU.mutOf_at (Option.some.inj hg)
  subst hb
  exact gw₁_not_top (hsupp gls _ gw₁ gT_violator)

/-- **`InstEquivLeaf` is false**: at the retained cell above, at the stack `[1]` (cut `⊤`). -/
theorem not_instEquivLeaf : ¬ InstEquivLeaf := by
  intro h
  have := h gA true [lifeN 1] [] gs₁ (.loc 5) gρ ⊤ gθ rfl
    (fun _ _ x hx => absurd hx List.not_mem_nil) gT_coreStable
    (fun β' hβ' l ψ hψ => by
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hψ
      exact hβ') gA_holds
  rw [gθ_sub] at this
  exact gA_fails _ this

/-! ### The thaw at `binder0`, as designed -/

/-- The context: `m : Mut '0 (1 ⊕ Imm '0 (Imm '0 (Imm '0 1)))`, `'0` the stack's variable. -/
abbrev gΓ : Ctx VTy := [⟨gA, true⟩]

abbrev gγ : List Val := [.loc 5]

theorem gΓ_thawFree : CtxThawFree gΓ := by
  intro s hs _
  rw [List.mem_singleton] at hs
  subst hs
  exact gT_coreStable

theorem gρ_deepAt {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val} (h : DeepAt gρ l ψ) : l = 5 := by
  cases h with
  | top e => exact (ResU.single_get_eq_some e).1
  | @wit _ m _ φ _ em hw =>
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some em
      rw [CellU.wit_mutOf] at hw
      cases hw with
      | top e => exact absurd e (by simp)
      | wit e _ => exact absurd e (by simp)

theorem vRLI_mut_eq (p : Placement) (σ : LStack) (δ : LSub) (a : Lifetime.Life) (T : VTy)
    (αs : List Life) (ls : List SRec) (v : Val) :
    vRLI p σ δ (.mut a T) αs ls v =
      fun ρ => vC true (.mut a T) ls (extS δ σ αs) v ρ ∧
        CohS σ αs (extS δ σ αs) (.mut a T) v ρ := by
  rw [vRLI]

theorem vwEW_off (s : LSub) (e : LEnt) (α : Life) (ls : List SRec) :
    vwEW s e false α ls PMap.empty :=
  ⟨⟨rfl, trivial⟩, fun _ hψ => absurd hψ (by simp)⟩

theorem vwEW_off_eq {s : LSub} {e : LEnt} {α : Life} {ls : List SRec} {ρ : WRes}
    (h : vwEW s e false α ls ρ) : ρ = PMap.empty := h.1.1

/-- The views of a stack with every flag off hold at `∅`, and only there. -/
theorem vwSW_off (s : LSub) (ls : List SRec) : ∀ (seen : List BoCa.Loc) (σ : LStack)
    (αs : List Life), αs.length = σ.length →
    vwSW s seen σ (σ.map fun _ => false) αs ls PMap.empty
  | _, [], [], _ => ⟨rfl, trivial⟩
  | seen, e :: σ, _ :: αs, h => by
      refine ⟨PMap.empty, PMap.empty, ResU.comp_empty_left _, ?_,
        vwSW_off s ls (e.l :: seen) σ αs (by simpa using h)⟩
      show vwEW s e (vis seen e false) _ ls PMap.empty
      rw [show vis seen e false = false from rfl]
      exact vwEW_off s e _ ls
  | _, [], _ :: _, h => absurd h (by simp)
  | _, _ :: _, [], h => absurd h (by simp)

/-- **The thaw as designed fails at a context the partial result admits**, at `binder0`'s stack
`[qEnt]` at `1`, whose cut is `⊤`: the retained cell's payload support fails at every
instantiation that moves `'0`. -/
theorem not_ctxRelendableAtI_g : ¬ CtxRelendableAtI (ℍ := ℍ) .binder0 kΔ gΓ := by
  intro h
  have hok : StackOK [qEnt] [kα] := ⟨rfl, List.isChain_singleton _, List.nodup_singleton _⟩
  have hext : extS kδ [qEnt] [kα] = gs₁ := rfl
  have hM : kΔ.Models (extS kδ [qEnt] [kα]) := kΔ_models kδ
  have hro : RecsOutside [kα] [] := fun _ _ x hx => absurd hx List.not_mem_nil
  have hso : SubOutside [qEnt] [kα] kδ := by
    intro e a hm p hp
    simp [boundBefore] at hp
  have htab : TabAtS [qEnt] [kα] gρ := by
    refine ⟨fun a ha => ?_, fun a ha k ψ hk e => ?_⟩
    · obtain rfl : a = kα := (Option.some.inj ha).symm
      exact ResU.inStratum_single _ (show (↓kα) < ⊤ from by decide)
    · obtain rfl : a = kα := (Option.some.inj ha).symm
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
      exact show kα < ⊤ from by decide
  have hpv : PlaceViewsL (extS kδ [qEnt] [kα]) [qEnt] [kα] [] gρ := by
    refine placeViewsL_of_noBound fun l ψ hd _ hl => ?_
    rw [gρ_deepAt hd] at hl
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hl
    exact absurd hl (by decide)
  have hg : gRLI (ℍ := ℍ) .binder0 [qEnt] kδ [kα] [] gΓ gγ gρ := by
    refine pure_sep_mk trivial ⟨gρ, PMap.empty, ResU.comp_empty_right _, ?_, rfl, trivial⟩
    show vRLI (ℍ := ℍ) .binder0 [qEnt] kδ gA [kα] [] (.loc 5) gρ
    rw [vRLI_mut_eq]
    refine ⟨by rw [hext]; exact gA_holds, fun l e α hv hi => ?_⟩
    cases hv
    exact absurd hi (by simp [innerAt])
  obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ :=
    h kδ [qEnt] [kα] [] gγ gρ hok (fun y hy => absurd rfl hy) hM hro hso htab hpv hg
  -- the views are empty: the stack's place holds no cell of the context
  have hρn : ρn = PMap.empty ∧ ds = [false] := by
    obtain ⟨hw, -⟩ := hn
    match ds, hw with
    | [], hw => exact hw.elim
    | _ :: _ :: _, hw => exact absurd hw (by rintro ⟨_, _, _, _, h⟩; exact h.elim)
    | [false], hw =>
        obtain ⟨a, r, hc', ha, hr⟩ := hw
        rw [show vis [] qEnt false = false from rfl] at ha
        obtain rfl := vwEW_off_eq ha
        obtain rfl : r = PMap.empty := hr.1
        exact ⟨eq_empty_of_compS_empty hc', rfl⟩
    | [true], hw =>
        exfalso
        obtain ⟨a, r, hc', ha, -⟩ := hw
        obtain ⟨⟨b, u, χ, hχ, Q, hwQ, -, -, hρa, -⟩, -⟩ := ha
        have ha0 : a.get 0 = some (CellU.mutOf b u χ hχ Q hwQ) := by
          rw [hρa]; exact ResU.single_get_self _ _
        obtain ⟨ψ₁, h₁, -⟩ := top_of_compS_left hc' ha0
        obtain ⟨ψ₂, h₂, -⟩ := top_of_compS_left (ResU.CompS.comm hc) h₁
        rw [ResU.single_get_ne _ (show (0 : BoCa.Loc) ≠ 5 from by decide)] at h₂
        exact absurd h₂ (by simp)
  obtain ⟨rfl, rfl⟩ := hρn
  have hρz : ρz = gρ := ResU.CompS.functional hc (ResU.comp_empty_right _) |>.symm
  subst hρz
  have hat : InstAt [kα] (Inst.ofEmb gθ) := fun c θ hcθ => by cases hcθ; rfl
  have hnil : Inst.recs (Inst.ofEmb gθ) ([] : List SRec) = [] := rfl
  have hvw : vwSL (extS (Inst.sub (Inst.ofEmb gθ) kδ) [qEnt] (Inst.life (Inst.ofEmb gθ) [kα]))
      [qEnt] [false] (Inst.life (Inst.ofEmb gθ) [kα]) [] PMap.empty :=
    ⟨vwSW_off _ [] [] [qEnt] _ rfl,
      placeViewsL_of_noBound fun l ψ hd _ _ => by
        cases hd with
        | top e => exact absurd e (by simp)
        | wit e _ => exact absurd e (by simp)⟩
  have hfin := H (Inst.ofEmb gθ) hat [] (by rw [hnil]; exact Ext.refl _ _)
    (fun x hx => absurd hx (by rw [hnil]; exact List.not_mem_nil))
    (fun _ _ x hx => absurd hx List.not_mem_nil) PMap.empty gρ hvw (ResU.comp_empty_right _)
  obtain ⟨-, hgs⟩ := pure_sep_iff.mp hfin
  obtain ⟨ρ₁, ρ₂, hc₁, hv₁, hρ₂, -⟩ := hgs
  obtain rfl : ρ₂ = PMap.empty := hρ₂
  have hρ₁ : ρ₁ = gρ := (ResU.CompS.functional hc₁ (ResU.comp_empty_right _)).symm
  subst hρ₁
  have hv₁' : vRLI (ℍ := ℍ) .binder0 [qEnt] (Inst.sub (Inst.ofEmb gθ) kδ) gA
      (Inst.life (Inst.ofEmb gθ) [kα]) [] (.loc 5) gρ := hv₁
  rw [vRLI_mut_eq] at hv₁'
  have hext₂ : extS (Inst.sub (Inst.ofEmb gθ) kδ) [qEnt] (Inst.life (Inst.ofEmb gθ) [kα]) = gs₂ :=
    rfl
  rw [hext₂] at hv₁'
  exact gA_fails [] hv₁'.1

/-- **The partial target's thaw is false as designed**, at a `CtxThawFree` context. -/
theorem not_ctxRelendsThawFree : ¬ CtxRelendsThawFree (ℍ := ℍ) .binder0 :=
  fun h => not_ctxRelendableAtI_g (h kΔ gΓ gΓ_thawFree)

/-- **So the item-4 targets are false as designed**: the partial one, and the full one with it. -/
theorem not_statement0UThawFree : ¬ Statement0UThawFree (ℍ := ℍ) .binder0 :=
  fun h => not_ctxRelendsThawFree h.2.1

theorem not_statement0UFull : ¬ Statement0UFull (ℍ := ℍ) .binder0 :=
  fun h => not_ctxRelendableAtI_g (h.2.1 kΔ gΓ)

end ProbeD1

end

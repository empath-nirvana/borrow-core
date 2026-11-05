import Core.Chain.SI.RebStopD
import Core.Chain.SI.RebProg

/-!
# The test: a reborrow of an item reached through a borrowed box, live across a `yield`

    progDeep = hnd_Div rtH (hnd_Y yStore (
                 (λe. (λd. (λc. iterate (fD, c)) (alloc d)) (alloc e)) (alloc ())))

    fD = λs. λb. case b { next → (λx. (λy. y (); (λz. ()) (!y)) (!x)) (!s); inr s | close → () }

`s = c ↦ own(d) ● d ↦ own(e) ● e ↦ own(())`: a value (`c`) holding a box of items (`d`) holding an
item (`e`), the shape of `for item in &self.items { item.process().await }`. Each turn lends `c`
`imm` (`erwp_I_frame`), loads `d` through the lend and reborrows the field (`erwp_reborrow`, the
image at the root `d`), loads `e` through that image and reborrows the item at the chain view
`d` (`erwp_reborrowDeep`, the image at `e`, a chain position below `d`): the item's reborrow is
live across `y`, whose `κ` the scheduler stores and resumes; after the resume it reads `e`, and
every borrow ends. The two reborrows are nested and both live across the stop, at the canonical
images `canon r β₁` and `canonD r S₂ (loc e) (e ↦ own(())) β₂`.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI.DeepRebProg
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.LendProg
open BoCa.Fig16.LogRel.Core.Chain.SI.ILendProg
open BoCa.Fig16.LogRel.Core.Chain.SI.RebProg
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  clauseAt capTag)
open BoCa.Lifetime (LSub LifeVar)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-! ### The record and its images -/

/-- The item's type: a box of `()`. -/
def S₂ : VTy := .ref .unit

/-- The record's type: a box of items. -/
def rT2 : VTy := .ref S₂

theorem S₂_free (x : LifeVar) : ¬ VFree x S₂ := by simp [S₂, VFree]

/-- The record of the turn's lend: `c ↦ own(d)`, escrow `d ↦ own(e) ● e ↦ own(())`. -/
def recD (c d : Loc) (R₀ : WRes) : FrameRec := recRS S₂ c d R₀

/-- `ag` of a cell whose witness is one `own` cell elsewhere. -/
theorem agW_single_imm_own {d e : Loc} (hed : e ≠ d) (s : LSet) (v u : Val)
    (h : ResU.InStratum s.join (ResU.single e (CellU.ownOf u))) :
    ∃ A, AgW (ResU.single d (CellU.immOf s v (ResU.single e (CellU.ownOf u)) h)) A := by
  have hc : ResU.CompatS (ResU.single d (CellU.immOf s v (ResU.single e (CellU.ownOf u)) h))
      (ResU.single e (CellU.ownOf u)) := compatS_single_of_get_none (ResU.single_get_ne _ hed)
  obtain ⟨σ, hσ⟩ := (ResU.compS_defined_iff _ _).mpr hc
  have hfl : ResU.FlatR (ResU.single e (CellU.ownOf u)) (ResU.single e (CellU.ownOf u)) :=
    ⟨PMap.empty, _, AgW.single_own e u, ExW.single_own e u,
      (ResU.compR_iff_compS (compS_empty_left _).1 _).mpr (compS_empty_left _)⟩
  exact ⟨σ, AgW.single_imm hfl ((ResU.compR_iff_compS hc σ).mpr hσ)⟩

theorem inStratum_single_own (β : Life) (e : Loc) (u : Val) :
    ResU.InStratum β (ResU.single e (CellU.ownOf u)) :=
  ResU.inStratum_single e (by simp)

/-- The shape of the field's image at `β`: one cell at `d`, its witness the item's cell. -/
theorem shape_root (δ : LSub) (x : LifeVar) (β : Life) (d e : Loc)
    (h : ResU.InStratum (LSet.singleton β).join (ResU.single e (CellU.ownOf Val.unit))) :
    vShape (rT2.immReborrow (.var x)) (δ.extend x β) (.loc d)
      (ResU.single d (CellU.immOf (LSet.singleton β) (.loc e)
        (ResU.single e (CellU.ownOf Val.unit)) h)) := by
  refine ⟨β, ?_, d, pure_sep_mk rfl ⟨LSet.singleton β, .loc e, _, h, rfl,
    ⟨e, Val.unit, pure_sep_mk rfl ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, rfl, rfl⟩⟩,
    le_refl _⟩⟩
  simp [BoCa.Lifetime.Life.interp, find?_extend_self]
  rfl

/-- The shape of the item's image at `β`: one cell at `e`, witness `∅`. -/
theorem shape_item (δ : LSub) (x : LifeVar) (β : Life) (e : Loc)
    (h : ResU.InStratum (LSet.singleton β).join (PMap.empty : WRes)) :
    vShape (S₂.immReborrow (.var x)) (δ.extend x β) (.loc e)
      (ResU.single e (CellU.immOf (LSet.singleton β) Val.unit PMap.empty h)) := by
  refine ⟨β, ?_, e, pure_sep_mk rfl ⟨LSet.singleton β, Val.unit, _, h, rfl, ⟨rfl, rfl⟩,
    le_refl _⟩⟩
  simp [BoCa.Lifetime.Life.interp, find?_extend_self]
  rfl

/-- An image at `β` of an escrow with an `own` cell at `ℓ`, taking the piece `p` at `ℓ`
(`reb_pair_at` for any escrow in `Res_β`). -/
theorem reb_one_at {l : Loc} {v : Val} {R p w : WRes} {β : Life} (hRs : R.InStratum β)
    (hRl : R.get l = some (CellU.ownOf v)) (hpl : p.get l = some (CellU.ownOf v))
    (hpR : ResU.Le p R) (hpw : p.del l = w) (h : w.InStratum (LSet.singleton β).join) :
    ResU.Reb β R (ResU.single l (CellU.immOf (LSet.singleton β) v w h)) := by
  subst hpw
  refine ⟨hRs, [(l, p)], p, ⟨by simp, fun k => ?_⟩,
    BigComp.cons BigComp.nil (ResU.comp_empty_right p), hpR, fun k q hkq => ?_⟩
  · constructor
    · intro hk; simp only [List.map_cons, List.map_nil, List.mem_singleton] at hk
      subst hk; exact ⟨_, ResU.single_get_self _ _⟩
    · rintro ⟨ψ, e⟩
      by_cases hk : k = l
      · simp [hk]
      · rw [ResU.single_get_ne _ hk] at e; cases e
  · simp only [List.mem_singleton, Prod.mk.injEq] at hkq
    obtain ⟨rfl, rfl⟩ := hkq
    refine ⟨⟨_, hpl⟩, fun v' e => ?_, fun b v' χ hb P hw e => ?_, fun s v' χ h' e => ?_⟩
    · rw [hRl] at e; cases Option.some.inj e
      exact ⟨h, ResU.single_get_self _ _⟩
    · rw [hRl] at e; cases e
    · rw [hRl] at e; cases e

/-- The shape of `ref ()`: one `own` cell holding `()`. -/
theorem shape_S₂_inv {δ : LSub} {v : Val} {w : WRes} (h : vShape S₂ δ v w) :
    ∃ ℓ, v = Val.loc ℓ ∧ w = ResU.single ℓ (CellU.ownOf Val.unit) := by
  obtain ⟨ℓ, v', hk⟩ := h
  obtain ⟨hv, ρ₁, ρ₂, hc, rfl, hρ₂⟩ := pure_sep_iff.mp hk
  obtain ⟨rfl, rfl⟩ := hρ₂
  exact ⟨ℓ, hv, ResU.CompS.functional hc (ResU.comp_empty_right _)⟩

/-- The shape of `()`: nothing. -/
theorem shape_unit_inv {δ : LSub} {v : Val} {w : WRes} (h : vShape VTy.unit δ v w) :
    v = Val.unit ∧ w = PMap.empty := ⟨h.2, h.1⟩

/-- The record's template exists: the image at `⊤` whose witness is the item's cell. -/
theorem recD_tmpl {c d e : Loc} (hed : e ≠ d) {R₀ : WRes}
    (hR₀ : ResU.CompS (ResU.single d (CellU.ownOf (.loc e)))
      (ResU.single e (CellU.ownOf Val.unit)) R₀) :
    TmplSpec (recD c d R₀) (tmpl (recD c d R₀)) := by
  have h : ResU.InStratum (LSet.singleton (⊤ : Life)).join
      (ResU.single e (CellU.ownOf Val.unit)) := inStratum_single_own _ e _
  exact tmpl_spec ⟨_, ⊤, 0, by simp [recD, recRS, S₂, VFree],
    reb_pair_at hR₀ (pair_get_left hR₀) ⟨PMap.empty, ResU.comp_empty_right _⟩
      (pair_del_left hed hR₀) h,
    shape_root δ₀ 0 ⊤ d e h, agW_single_imm_own hed _ _ _ h⟩

/-- **The field's canonical image**: one cell at `d` at `{β}`, holding `e`, its witness the
item's cell. -/
theorem canon_recD {c d e : Loc} (hed : e ≠ d) {R₀ : WRes}
    (hR₀ : ResU.CompS (ResU.single d (CellU.ownOf (.loc e)))
      (ResU.single e (CellU.ownOf Val.unit)) R₀) (β : Life) :
    ∃ h, canon (recD c d R₀) β = ResU.single d (CellU.immOf (LSet.singleton β) (.loc e)
      (ResU.single e (CellU.ownOf Val.unit)) h) := by
  obtain ⟨β₀, x₀, -, hreb₀, hden₀, -⟩ := recD_tmpl (c := c) hed hR₀
  obtain ⟨α, -, ℓ, hk⟩ := hden₀
  obtain ⟨hvℓ, s, u, w, h, htm, hSw, -⟩ := pure_sep_iff.mp hk
  have hℓ : ℓ = d := (BoCa.Val.loc_inj.mp hvℓ).symm
  subst hℓ
  have hRd := pair_get_left hR₀
  have e0 : (tmpl (recD c ℓ R₀)).get ℓ = some (CellU.immOf s u w h) := by
    rw [htm]; exact ResU.single_get_self _ _
  have hu : u = .loc e := by
    obtain ⟨-, hcase⟩ := reb_cell hreb₀ e0
    rcases hcase with ⟨u', q, h', hown, hψ, -, -⟩ | ⟨ζ, eζ, kζ, -⟩ | ⟨ζ, eζ, kζ, -⟩
    · change R₀.get ℓ = _ at hown
      rw [hRd] at hown; cases Option.some.inj hown
      have := congrArg CellU.erase hψ
      simpa using this
    · change R₀.get ℓ = _ at eζ
      rw [hRd] at eζ; cases Option.some.inj eζ; simp at kζ
    · change R₀.get ℓ = _ at eζ
      rw [hRd] at eζ; cases Option.some.inj eζ; simp at kζ
  subst hu
  obtain ⟨ℓ', hℓ', rfl⟩ := shape_S₂_inv hSw
  cases BoCa.Val.loc_inj.mp hℓ'
  have hwβ : ResU.InStratum (LSet.singleton β).join (ResU.single e (CellU.ownOf Val.unit)) :=
    inStratum_single_own _ e _
  refine ⟨hwβ, ?_⟩
  rw [canon, htm, relRes_single]
  congr 1
  unfold relCell
  rw [dif_pos ⟨CellU.kind_immOf _ _ _ _, ⟨_, hRd, by simp⟩, by rw [CellU.wit_immOf]; exact hwβ⟩]
  exact CellU.immOf_congr rfl (by simp) (by simp) _ _

/-- The item's template exists: the image at `⊤` with witness `∅`. -/
theorem item_tmpl (r : FrameRec) (e : Loc) :
    TmplSpecD r S₂ (.loc e) (ResU.single e (CellU.ownOf Val.unit))
      (tmplD r S₂ (.loc e) (ResU.single e (CellU.ownOf Val.unit))) := by
  have h : ResU.InStratum (LSet.singleton (⊤ : Life)).join (PMap.empty : WRes) :=
    inStratum_empty _
  exact tmplD_spec ⟨_, ⊤, 0, S₂_free 0,
    reb_one_at (inStratum_single_own _ e _) (ResU.single_get_self _ _)
      (ResU.single_get_self _ _) ⟨PMap.empty, ResU.comp_empty_right _⟩ (single_del_self _ _) h,
    shape_item r.δ 0 ⊤ e h, _, agW_single_imm_empty e _ Val.unit h⟩

/-- **The item's canonical image**: one cell at `e` at `{β}`, holding `()`, witness `∅`. -/
theorem canonD_item (r : FrameRec) (e : Loc) (β : Life) :
    ∃ h, canonD r S₂ (.loc e) (ResU.single e (CellU.ownOf Val.unit)) β =
      ResU.single e (CellU.immOf (LSet.singleton β) Val.unit PMap.empty h) := by
  obtain ⟨β₀, x₀, -, hreb₀, hden₀, -⟩ := item_tmpl r e
  obtain ⟨α, -, ℓ, hk⟩ := hden₀
  obtain ⟨hvℓ, s, u, w, h, htm, hSw, -⟩ := pure_sep_iff.mp hk
  have hℓ : ℓ = e := (BoCa.Val.loc_inj.mp hvℓ).symm
  subst hℓ
  obtain ⟨rfl, rfl⟩ := shape_unit_inv hSw
  have hwβ : ResU.InStratum (LSet.singleton β).join (PMap.empty : WRes) := inStratum_empty _
  refine ⟨hwβ, ?_⟩
  rw [canonD, htm, relRes_single]
  congr 1
  unfold relCell
  rw [dif_pos ⟨CellU.kind_immOf _ _ _ _, ⟨_, ResU.single_get_self _ _, by simp⟩,
    by rw [CellU.wit_immOf]; exact hwβ⟩]
  exact CellU.immOf_congr rfl (by simp) (by simp) _ _

/-! ### The item's reborrow, the field's, the lend -/

/-- **The item's reborrowed computation**: `y ()` stops with the item's image in the
continuation's share; after the resume the image reads `e` and is released. -/
theorem itemBody_ok {Φ : LocFam} (hΦ : Φ.Down) (e : Loc) (β : Life) {Q : PostN}
    (hQ : ∀ k ls, Q k ls Val.unit PMap.empty) (k : Nat) (ls : List SRec) (Bχ : WRes)
    (P : Val → WProp) (hpto : ptoImm e β P Bχ) :
    erwp (ℍ := ℍ) Φ (opTableN T2) (RebPost β Q) k ls (.seq FileProg.yE (useR e)) Bχ := by
  refine erwp_perform (T := T2) (en := yEnt) (K := .seq .hole (useR e)) (by simp [Kont.HasHnd])
    (by simp [T2]) rfl rfl (compS_empty_left _) ⟨rfl, rfl⟩
    (fun ls' _ k' hk' w σB XB hB hXB => ?_)
  obtain ⟨rfl, rfl⟩ := hB
  obtain rfl := ResU.CompS.functional hXB (ResU.comp_empty_right _)
  cases k' with
  | zero => exact erwp_zero
  | succ k₀ =>
  refine erwp_step (opTableN_local T2) (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  have hplug : useR e = (Kont.appR (.val discardV) .hole).plug (ldR e) := rfl
  rw [hplug]
  refine erwp_bindR hΦ (opTableN_local T2) (Kont.appR (.val discardV) .hole) (rwp_load_I ls' e β P _
    ⟨_, PMap.empty, ResU.comp_empty_right _, hpto, fun v ρc X hc hX => ?_⟩)
  obtain rfl := eq_of_compS_empty_left hX
  obtain ⟨s, u', σ, hs, rfl, -, -⟩ := hc
  generalize k₀ - 1 = k₁
  cases k₁ with
  | zero => exact erwp_zero
  | succ k₂ =>
  refine erwp_step (opTableN_local T2) (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 v (.val Val.unit)) = (Val.unit).1 := by
    simp [Expr.subst, Kont.plug, Val.unit, Expr.val]
  rw [e₁]
  exact erwp_garbage (compS_empty_left _) (noOwn_single_imm e _ _ _ _)
    (erwp_val ⟨hQ _ _, inStratum_empty β⟩)

/-- The escrow lies above every lifetime. -/
theorem R₀_inStratumD {d e : Loc} {R₀ : WRes} (β : Life)
    (hR₀ : ResU.CompS (ResU.single d (CellU.ownOf (.loc e)))
      (ResU.single e (CellU.ownOf Val.unit)) R₀) : R₀.InStratum β :=
  ResU.CompS.inStratum hR₀ (ResU.inStratum_single d (by simp)) (ResU.inStratum_single e (by simp))

/-- The lend's post, the turn's resource handed back. -/
abbrev QL (c d : Loc) (R₀ : WRes) (A : Life) : PostN := IFPost c (.loc d) (PR d R₀) A (Qt c d R₀)

theorem QL_unit (c d : Loc) (R₀ : WRes) (A β : Life) :
    ∀ k ls, RebPost β (QL c d R₀ A) k ls Val.unit PMap.empty := by
  intro k ls
  refine ⟨⟨fun ρl Y hl hY ρv Z hv hZ => ?_, inStratum_empty A⟩, inStratum_empty β⟩
  obtain ⟨-, rfl⟩ := hv
  subst hl
  obtain rfl := eq_of_compS_empty_left hY
  exact ⟨rfl, hZ⟩

/-- **The field's reborrowed computation**: loads `e` through the field's image (6.143), then
reborrows the item at the chain view `d` at `↓β`, across `y` (`erwp_reborrowDeep`). -/
theorem fieldBody_ok {Φ : LocFam} (hΦ : Φ.Down) (c d e : Loc) (hed : e ≠ d) (R₀ : WRes)
    (hR₀ : ResU.CompS (ResU.single d (CellU.ownOf (.loc e)))
      (ResU.single e (CellU.ownOf Val.unit)) R₀)
    (A β : Life) (k : Nat) (ls : List SRec) (hr : recD c d R₀ ∈ rsOf ls)
    (Bχ : WRes)
    (hBχ : ResU.CompS PMap.empty (canon (recD c d R₀) β) Bχ) :
    erwp (ℍ := ℍ) Φ (opTableN T2) (RebPost β (QL c d R₀ A)) k ls (lendRE d) Bχ := by
  obtain rfl := eq_of_compS_empty_left hBχ
  obtain ⟨h₁, hcanon⟩ := canon_recD (c := c) hed hR₀ β
  rw [hcanon]
  have hplug : lendRE d = (Kont.appR (.val lamX) .hole).plug (ldR d) := rfl
  rw [hplug]
  refine erwp_bindR hΦ (opTableN_local T2) _ (rwp_load_I ls d β
    (fun v σ => v = .loc e ∧ σ = ResU.single e (CellU.ownOf Val.unit)) _
    ⟨_, PMap.empty, ResU.comp_empty_right _,
      ⟨LSet.singleton β, .loc e, _, h₁, rfl, ⟨rfl, rfl⟩, le_refl _⟩,
      fun v ρc X hc hX => ?_⟩)
  obtain rfl := eq_of_compS_empty_left hX
  obtain ⟨s, v', σ, hs, rfl, hsep, hβs⟩ := hc
  obtain ⟨rfl, ⟨rfl, rfl⟩⟩ := pure_sep_iff.mp hsep
  generalize k - 1 = k'
  cases k' with
  | zero => exact erwp_zero
  | succ k₀ =>
  refine erwp_step (opTableN_local T2)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc e)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.loc e)
      (.seq FileProg.yE (.app (.val discardV) (.app (.val (.prim .load)) (.var 0))))) =
      .seq FileProg.yE (useR e) := by
    simp [Expr.subst, Kont.plug, FileProg.yE, useR, discardV, ldR, performE, opPayload, Val.pair,
      Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [e₁]
  -- the item's reborrow at the chain view `d`, at `↓β`
  have hch₀ : Chain R₀ rT2 (.loc d) none d S₂ (.loc e) :=
    Chain.one (RefPos.ref S₂ d) (pair_get_left hR₀)
  have hβ₂ : (↓β) ⊏ s.meet := lt_of_lt_of_le (Life.down_sqsubset β) hβs
  obtain ⟨h₂, hcanonD⟩ := canonD_item (recD c d R₀) e (↓β)
  have hshape : vShape (S₂.immReborrow (.var 0)) ((recD c d R₀).δ.extend 0 (↓β)) (.loc e)
      (canonD (recD c d R₀) S₂ (.loc e) (ResU.single e (CellU.ownOf Val.unit)) (↓β)) := by
    rw [hcanonD]; exact shape_item _ 0 _ e h₂
  refine erwp_reborrowDeep (recD c d R₀) hch₀ 0 (S₂_free 0) (item_tmpl _ e)
    (inStratum_single_own _ e _)
    ((CellU.inStratum_immOf _ _ _ _ _).mpr hβ₂) hshape (T2_rebOK (↓β)) k₀ ls _
    PMap.empty _ (ResU.comp_empty_right _) (inStratum_empty _) hr (fun Bχ hBχ => ?_)
  obtain rfl := eq_of_compS_empty_left hBχ
  rw [hcanonD]
  exact itemBody_ok hΦ e (↓β) (QL_unit c d R₀ A β) k₀ ls _
    (fun v σ => v = Val.unit ∧ σ = PMap.empty)
    ⟨LSet.singleton (↓β), Val.unit, PMap.empty, h₂, rfl, ⟨rfl, rfl⟩, le_refl _⟩

/-- `λx. (λy. y (); (λz. ()) (!y)) (!x)`. -/
def lamXD : Val := Val.lam (.app (.val lamX) (.app (.val (.prim .load)) (.var 0)))

/-- The lent computation: `lamXD (!c)`. -/
def lendDE (c : Loc) : Expr := .app (.val lamXD) (ldR c)

/-- **The lent computation**: loads `d` through the `imm` lend, then reborrows the field at
`↓A` (`erwp_reborrow`, at the canonical image), inside which the item is reborrowed. -/
theorem lendD_ok {Φ : LocFam} (hΦ : Φ.Down) (c d e : Loc) (hed : e ≠ d) (R₀ : WRes)
    (hR₀ : ResU.CompS (ResU.single d (CellU.ownOf (.loc e)))
      (ResU.single e (CellU.ownOf Val.unit)) R₀)
    (A : Life) (houtP : R₀.InStratum A) (k : Nat) (ls : List SRec)
    (ds : List FrameRec) (BI : WRes)
    (hBI : ResU.CompS PMap.empty
      (ResU.single c (CellU.immOf (LSet.singleton A) (.loc d) R₀ houtP)) BI) :
    erwp (ℍ := ℍ) Φ (opTableN T2) (QL c d R₀ A) k (frameList (recD c d R₀) ds A ls)
      (lendDE c) BI := by
  obtain rfl := eq_of_compS_empty_left hBI
  set lsF := frameList (recD c d R₀) ds A ls with hlsF
  have hplug : lendDE c = (Kont.appR (.val lamXD) .hole).plug (ldR c) := rfl
  rw [hplug]
  refine erwp_bindR hΦ (opTableN_local T2) _ (rwp_load_I lsF c A
    (fun v σ => v = .loc d ∧ σ = R₀) _ ⟨_, PMap.empty, ResU.comp_empty_right _,
      ⟨LSet.singleton A, .loc d, R₀, houtP, rfl, ⟨rfl, rfl⟩, le_refl _⟩,
      fun v ρc X hc hX => ?_⟩)
  obtain rfl := eq_of_compS_empty_left hX
  obtain ⟨s, v', σ, hs, rfl, hsep, hAs⟩ := hc
  obtain ⟨rfl, ⟨rfl, hσ⟩⟩ := pure_sep_iff.mp hsep
  subst σ
  generalize k - 1 = k'
  cases k' with
  | zero => exact erwp_zero
  | succ k₀ =>
  refine erwp_step (opTableN_local T2)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc d)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.loc d)
      (.app (.val lamX) (.app (.val (.prim .load)) (.var 0)))) = lendRE d := by
    simp [Expr.subst, Kont.plug, lamX, discardV, lendRE, ldR, FileProg.yE, performE, opPayload,
      Val.pair, Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [e₁]
  -- the field's reborrow, at `↓A`
  have hS := recD_tmpl (c := c) hed hR₀
  have hRβ : R₀.InStratum (↓A) := R₀_inStratumD _ hR₀
  have hshape := canon_ref (r := recD c d R₀) (S := S₂) rfl (x := 0) (S₂_free 0) hS hRβ
    (fun ℓ h => ⟨.loc e, by
      rw [show ℓ = d from (BoCa.Val.loc_inj.mp h).symm]
      exact pair_get_left hR₀⟩)
  have hr : recD c d R₀ ∈ rsOf lsF := by rw [hlsF, rsOf_frameList]; exact List.mem_cons_self
  exact erwp_reborrow (recD c d R₀) 0 (by simp [recD, recRS, S₂, VFree]) hS hRβ hshape
    (down_le_of_meet hAs) (T2_rebOK (↓A)) k₀ lsF _ PMap.empty _ (ResU.comp_empty_right _)
    (inStratum_empty _) hr
    (fun Bχ hBχ => fieldBody_ok hΦ c d e hed R₀ hR₀ A (↓A) k₀ lsF hr
      Bχ hBχ)

/-- The loop's invariant: `c ↦ own(d) ● d ↦ own(e) ● e ↦ own(())`. -/
def IRD : Val → WProp := fun s ρ => ∃ (c d e : Loc) (R₀ : WRes), s = Val.loc c ∧
  ResU.CompS (ResU.single d (CellU.ownOf (.loc e))) (ResU.single e (CellU.ownOf Val.unit)) R₀ ∧
  ResU.CompS (ResU.single c (CellU.ownOf (.loc d))) R₀ ρ

theorem IRD_closed : ∀ s ρ, IRD s ρ → closedAt 0 s.1 = true := by
  rintro s ρ ⟨c, -, -, -, rfl, -⟩
  rfl

theorem ne_of_pair {d e : Loc} {v u : Val} {R : WRes}
    (h : ResU.CompS (ResU.single d (CellU.ownOf v)) (ResU.single e (CellU.ownOf u)) R) :
    e ≠ d := by
  rintro rfl
  have := ResU.compatS_single_own h.1
  rw [ResU.single_get_self] at this
  cases this

/-- `λs. λb. case b {next → lamXD (!s); inr s | close → ()}`. -/
def fD : Val :=
  Val.lam (.lam (.case (.var 0) (.seq (.app (.val lamXD) (.app (.val (.prim .load)) (.var 2)))
    (.inj₂ (.var 2))) (.val .unit)))

/-- **A turn**: three steps to `lamXD (!c); inr c`, the lend of `c` by `erwp_I_frame` at a
lifetime below the list's records, inside it the field's and the item's reborrows, then
`inr c`. -/
theorem turnD_ok {Φ : LocFam} (hΦ : Φ.Down) (k : Nat) (s : Val) (ls : List SRec)
    (ρ : WRes) (hI : IRD s ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T2) (turnPostN IRD QZ) k ls
      (.app (.app (.val fD) (.val s)) (.val nextV)) ρ := by
  obtain ⟨c, d, e, R₀, rfl, hR₀, hρ⟩ := hI
  have hed := ne_of_pair hR₀
  have hD := opTableN_down T2_down
  have hTP : (turnPostN IRD QZ).Down := fun _ _ _ _ h => by
    rcases h with ⟨x, hx, hq⟩ | h
    · exact .inl ⟨x, hx, hq⟩
    · exact .inr h
  refine erwp_det hΦ hD hTP
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc c)) rfl (.appL .hole nextV)) ?_
  have e₁ : (Kont.appL .hole nextV).plug (Expr.subst 0 (Val.loc c)
      (.lam (.case (.var 0) (.seq (.app (.val lamXD) (.app (.val (.prim .load)) (.var 2)))
        (.inj₂ (.var 2))) (.val .unit)))) =
      Kont.hole.plug (.app (.val (Val.lam (.case (.var 0)
        (.seq (lendDE c) (.inj₂ (.val (Val.loc c)))) (.val .unit)))) (.val nextV)) := by
    simp [Expr.subst, Expr.shift, Kont.plug, lamXD, lamX, discardV, lendDE, ldR, FileProg.yE,
      performE, opPayload, Val.pair, Val.i32, Val.unit, Val.lam, Val.loc, Expr.val, Val.prim,
      Val.shift]
  rw [e₁]
  refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.beta μ _ nextV) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 nextV (.case (.var 0)
        (.seq (lendDE c) (.inj₂ (.val (Val.loc c)))) (.val .unit))) =
      Kont.hole.plug (.case (.val (Val.inj₁ Val.unit))
        (.seq (lendDE c) (.inj₂ (.val (Val.loc c)))) (.val .unit)) := by
    simp [Expr.subst, Kont.plug, lamXD, lamX, discardV, lendDE, ldR, FileProg.yE, performE,
      opPayload, Val.pair, Val.i32, Val.unit, nextV, Val.inj₁, Val.loc, Expr.val, Val.prim,
      Val.lam]
  rw [e₂]
  refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl .hole) ?_
  have e₃ : Kont.hole.plug (Expr.subst 0 Val.unit
        (.seq (lendDE c) (.inj₂ (.val (Val.loc c))))) =
      (Kont.seq .hole (.inj₂ (.val (Val.loc c)))).plug (lendDE c) := by
    simp [Expr.subst, Kont.plug, lamXD, lamX, discardV, lendDE, ldR, FileProg.yE, performE,
      opPayload, Val.pair, Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [e₃]
  refine erwp_bind_le (Q' := Qt c d R₀) hΦ _ (fun m => by simp [Kont.HasHnd])
    (fun m => by simp [Kont.Catches]) (OpTabN.ctxClosed_of_fin T2_fin _) k ?_ k le_rfl ls _ _ ?_
  · rintro k' ls' v σ - ⟨hv, hσ⟩
    obtain rfl : v = Val.unit := hv
    refine erwp_det hΦ hD hTP (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    exact erwp_val (v := Val.inj₂ (Val.loc c)) (.inr ⟨Val.loc c, rfl, c, d, e, R₀, rfl, hR₀, hσ⟩)
  · obtain ⟨A, -⟩ := exists_fresh ls
    have hshape : vShape rT2 δ₀ (.loc d) R₀ :=
      ⟨d, .loc e, pure_sep_mk rfl ⟨_, _, hR₀, rfl,
        ⟨e, Val.unit, pure_sep_mk rfl ⟨_, PMap.empty, ResU.comp_empty_right _, rfl, rfl, rfl⟩⟩⟩⟩
    have hadm : AdmWf rT2 δ₀ := fun y hy => by simp [rT2, S₂, VFree] at hy
    have hex : ExS R₀ R₀ := (ExS.split hR₀).mpr ⟨_, _, ExW.single_own d (Val.loc e),
      ExW.single_own e Val.unit, hR₀⟩
    obtain ⟨ds, hds⟩ := lineage_list (r := recD c d R₀) hshape hadm hex
    have houtP : R₀.InStratum A := R₀_inStratumD A hR₀
    exact erwp_I_frame c rT2 δ₀ hadm (.loc d) (PR d R₀)
      (fun _ ρ' h => by obtain ⟨-, rfl⟩ := h; exact hshape)
      (fun _ _ _ _ h => h) (T2_ilendOK A) (fun _ _ _ _ _ _ h => h) k ls (lendDE c)
      R₀ _ PMap.empty ρ houtP (inStratum_empty A) ⟨rfl, rfl⟩ hρ
      (ResU.comp_empty_right _) ds hds
      (lendD_ok hΦ c d e hed R₀ hR₀ A houtP k ls ds)

/-- `(λc. iterate (fD, c))`. -/
def lamCD : Val := Val.lam (.app (.val (.prim .iterate)) (.pair (.val fD) (.var 0)))

/-- `(λd. lamCD (alloc d))`. -/
def lamDD : Val := Val.lam (.app (.val lamCD) (.app (.val (.prim .alloc)) (.var 0)))

/-- `(λe. lamDD (alloc e))`. -/
def lamED : Val := Val.lam (.app (.val lamDD) (.app (.val (.prim .alloc)) (.var 0)))

/-- `lamED (alloc ())`. -/
def bodyD : Expr := .app (.val lamED) (.app (.val (.prim .alloc)) (.val Val.unit))

/-- `hnd_Div rtH (hnd_Y yStore bodyD)`. -/
def progDeep : Expr := hndE DivRuntime.rtH (hndE yH bodyD)

theorem bodyD_ok (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN T2) QZ n [] bodyD (PMap.empty : WRes) := by
  have hD := opTableN_down T2_down
  have hL := opTableN_local T2
  refine erwp_alloc Φ₀_down hL (.appR (.val lamED) .hole) Val.unit (fun e σ₁ σ₂ hcell hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have h₁ : Kont.hole.plug (Expr.subst 0 (Val.loc e)
      (.app (.val lamDD) (.app (.val (.prim .alloc)) (.var 0)))) =
      (Kont.appR (.val lamDD) .hole).plug (.app (.val (.prim .alloc)) (.val (Val.loc e))) := by
    simp [Expr.subst, Kont.plug, lamDD, lamCD, fD, lamXD, lamX, discardV, FileProg.yE,
      performE, opPayload, Val.pair, Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [h₁]
  refine erwp_alloc Φ₀_down hL (.appR (.val lamDD) .hole) (Val.loc e)
    (fun d τ₁ τ₂ hcd hcd' => ?_)
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have h₂ : Kont.hole.plug (Expr.subst 0 (Val.loc d)
      (.app (.val lamCD) (.app (.val (.prim .alloc)) (.var 0)))) =
      (Kont.appR (.val lamCD) .hole).plug (.app (.val (.prim .alloc)) (.val (Val.loc d))) := by
    simp [Expr.subst, Kont.plug, lamCD, fD, lamXD, lamX, discardV, FileProg.yE, performE, opPayload,
      Val.pair, Val.i32, Val.unit, Val.loc, Expr.val, Val.prim, Val.lam]
  rw [h₂]
  refine erwp_alloc Φ₀_down hL (.appR (.val lamCD) .hole) (Val.loc d)
    (fun c υ₁ υ₂ hcc hcc' => ?_)
  refine erwp_det Φ₀_down hD QZ_down (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  have h₃ : Kont.hole.plug (Expr.subst 0 (Val.loc c)
      (.app (.val (.prim .iterate)) (.pair (.val fD) (.var 0)))) = iterateE fD (Val.loc c) := by
    simp [Expr.subst, Kont.plug, iterateE, Val.pair, Val.loc, Expr.val, Val.prim,
      subst_closedAt _ _ (show closedAt 0 fD.1 = true from rfl) (Nat.zero_le _)]
  rw [h₃]
  subst hcell hcd hcc
  exact erwp_iterate Φ₀_down T2_down (OpTabN.ctxClosed_of_fin T2_fin _) QZ_down rfl (I := IRD)
    (en := tickEnt) (by simp [T2, T1, FileProg.divEff_ne6]) rfl rfl
    (fun _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ h => h) IRD_closed
    (fun k s ls ρ hI => turnD_ok Φ₀_down k s ls ρ hI) _ _ _ _
    ⟨c, d, e, _, rfl, ResU.CompS.comm hcd', ResU.CompS.comm hcc'⟩

theorem progDeep_ok (n : Nat) :
    erwp (ℍ := ℍ) Φ₀ (opTableN OpTabN.empty) QZ n [] progDeep (PMap.empty : WRes) :=
  erwp_rtH Φ₀_down n [] _ _ (erwp_yH Φ₀_down n [] _ _ (bodyD_ok n))

/-- **The deep reborrow test.** On every turn of a loop with no bound, a value is lent `imm`, its
boxed field is reborrowed, and an item inside the field (a chain position below the field) is
reborrowed at a shorter lifetime, live across `y`, under a scheduler that stores the
continuation in a cell and resumes it, under the runtime's `Div` handler: every configuration a
run reaches is a value or steps, a value only at the empty memory, and every `free` finds its
cell. No fuel. -/
theorem progDeep_orDiverges : OrDiverges (ℍ := ℍ) progDeep :=
  erwp_adequacy (Φ := Φ₀) (fun _ _ _ _ h => h) progDeep_ok

end BoCa.Fig16.LogRel.Core.Chain.SI.DeepRebProg

end

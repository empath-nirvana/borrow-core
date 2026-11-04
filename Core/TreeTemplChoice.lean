import Core.TreeBorrowEdges

/-!
# Two templates of one escrow whose canonical images differ  `[spec §62]`

`docs/new-core/scope-791.md` O1. The escrow of a record at `ref (imm 'a 1)`: `k ↦ own(loc j)` beside
`j ↦ imm({a₁, a₂}, (), ∅)`. `●` composes `imm` cells by the union of their lifetime sets
(`ResUT.compS_single_imm`), so the escrow lies above `k ↦ own(loc j) ● j ↦ imm({aᵢ}, (), ∅)` for
each `i`, and each gives a typed image `k ↦ imm({β}, loc j, j ↦ imm({aᵢ}, (), ∅))` meeting
`TmplSpecT` (`tmplSpecT_two_wit`). `relRes` re-takes an image's top cell and keeps its witness
(`relCellT_props`), and a re-reading keeps the lifetime sets in a witness (`RC.imm`), so at every
`β′` the two canonical images have no common re-reading (`canon_two_wit`). The template is not
fixed by its specification up to canonical images, and `tmplT`'s `Classical` pick at a grown tree
is unrelated to its pick before: the reason the record stores its template (option (a)).
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

abbrev K₀ : WCactus := wE.K

/-- `j = 1 ↦ imm(S, (), ∅)`. -/
def vw (S : TSet) : TRes K₀ :=
  ResUT.single 1 (CellUT.immOf S BoCa.Val.unit PMap.empty (emptyT_inStratum _))

/-- `k = 2 ↦ own(loc 1)`. -/
def okj : TRes K₀ := ResUT.single 2 (CellUT.ownOf (BoCa.Val.loc 1))

theorem lt31 : K₀.lt (lfE 3) (lfE 1) := ⟨chain_le (by omega), by decide⟩
theorem lt32 : K₀.lt (lfE 3) (lfE 2) := ⟨chain_le (by omega), by decide⟩

/-- `{a₁, a₂} = {1, 2}`. -/
abbrev S12 : TSet := TSet.single (lfE 1) ∪ TSet.single (lfE 2)

theorem vw_inStratum {a : Nat} (h : K₀.lt (lfE 3) (lfE a)) :
    (vw (TSet.single (lfE a))).InStratum (TSet.single (lfE 3)) :=
  ResUT.inStratum_single 1 ((CellUT.inStratum_immOf _ _ _ _ _).mpr fun x hx y hy => by
    simp only [TSet.single_set, Finset.mem_singleton] at hx hy
    subst hx; subst hy; exact h)

theorem okj_vw_compS (S : TSet) : ∃ p, ResUT.CompS okj (vw S) p :=
  single_compS (by decide) _ _

/-- The escrow `k ↦ own(loc j) ● j ↦ imm({a₁, a₂}, (), ∅)`. -/
def Rj : TRes K₀ := (okj_vw_compS S12).choose
theorem Rj_spec : ResUT.CompS okj (vw S12) Rj := (okj_vw_compS S12).choose_spec

/-- The part `k ↦ own(loc j) ● j ↦ imm({aᵢ}, (), ∅)`. -/
def pj (a : Nat) : TRes K₀ := (okj_vw_compS (TSet.single (lfE a))).choose
theorem pj_spec (a : Nat) : ResUT.CompS okj (vw (TSet.single (lfE a))) (pj a) :=
  (okj_vw_compS _).choose_spec

/-- The image `k ↦ imm({β}, loc j, j ↦ imm({aᵢ}, (), ∅))`, `β = 3`. -/
def cjCell (a : Nat) (h : K₀.lt (lfE 3) (lfE a)) : TCell K₀ :=
  CellUT.immOf (TSet.single (lfE 3)) (BoCa.Val.loc 1) (vw (TSet.single (lfE a))) (vw_inStratum h)

def cj (a : Nat) (h : K₀.lt (lfE 3) (lfE a)) : TRes K₀ := ResUT.single 2 (cjCell a h)

theorem vw_valid (a : Nat) : ResUT.Valid (vw (TSet.single (lfE a))) := valid_view _ _

theorem own_ne_imm (v : BoCa.Val) : (CellUT.ownOf v : TCell K₀).kind ≠ Kind.imm := by
  simp [CellUT.kind, CellUT.ownOf]

theorem okj_get_comp {S : TSet} {p : TRes K₀} (h : ResUT.CompS okj (vw S) p) :
    p.get 2 = some (CellUT.ownOf (BoCa.Val.loc 1)) :=
  (ResUT.CompS.get_left_of_ne_imm h (ResUT.single_get_self _ _) (own_ne_imm _)).2

theorem pj_del (a : Nat) : (pj a).del 2 = vw (TSet.single (lfE a)) := by
  refine PMap.ext fun x => ?_
  by_cases hx : x = 2
  · subst hx; rw [ResUT.del_get_self]; exact (ResUT.single_get_ne _ (by decide)).symm
  · rw [ResUT.del_get_ne _ hx]
    exact ResUT.Comp.get_of_left_none (pj_spec a) (ResUT.single_get_ne _ hx)

theorem vw_comp12 : ResUT.CompS (vw (TSet.single (lfE 1))) (vw (TSet.single (lfE 2))) (vw S12) :=
  ResUT.compS_single_imm 1 _ _ _ _ _ _ _

theorem pj_le (a : Nat) (ha : a = 1 ∨ a = 2) : ResUT.Le (pj a) Rj := by
  rcases ha with rfl | rfl
  · obtain ⟨y, hy, hyR⟩ := (ResUT.CompS.assoc okj _ _ Rj).mp ⟨_, vw_comp12, Rj_spec⟩
    obtain rfl := ResUT.CompS.functional hy (pj_spec 1)
    exact ⟨_, hyR⟩
  · obtain ⟨y, hy, hyR⟩ :=
      (ResUT.CompS.assoc okj _ _ Rj).mp ⟨_, ResUT.CompS.comm vw_comp12, Rj_spec⟩
    obtain rfl := ResUT.CompS.functional hy (pj_spec 2)
    exact ⟨_, hyR⟩

theorem Rj_inStratum : Rj.InStratum (TSet.single (lfE 3)) :=
  BoLo.inStratum_comp (BoLo.compS_hC _) Rj_spec (ResUT.inStratum_single_own _ _ _)
    (ResUT.inStratum_single 1 ((CellUT.inStratum_immOf _ _ _ _ _).mpr fun x hx y hy => by
      simp only [TSet.single_set, Finset.mem_singleton] at hx
      subst hx
      rcases Finset.mem_union.mp hy with hy | hy <;>
        simp only [TSet.single_set, Finset.mem_singleton] at hy <;> subst hy
      · exact lt31
      · exact lt32))

theorem cj_reb {a : Nat} (ha : a = 1 ∨ a = 2) (h : K₀.lt (lfE 3) (lfE a)) :
    ResUT.Reb (lfE 3) Rj (cj a h) := by
  have hR2 := okj_get_comp Rj_spec
  refine ⟨Rj_inStratum, [(2, pj a)], pj a, ⟨List.nodup_singleton 2, fun x => ?_⟩,
    (BigCompT.singleton_iff ResUT.compLawsS).mpr rfl, pj_le a ha, ?_⟩
  · simp only [List.map, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨_, ResUT.single_get_self _ _⟩
    · rintro ⟨ψ, e⟩; exact (ResUT.single_get_eq_some e).1
  · intro x p hx
    simp only [List.mem_singleton, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    refine ⟨⟨_, okj_get_comp (pj_spec a)⟩, fun v e => ?_, fun b _ v χ hb P hw e => ?_,
      fun s v χ hs e => ?_⟩
    · rw [hR2] at e
      cases e
      refine ⟨by rw [pj_del]; exact vw_inStratum h, ?_⟩
      rw [cj, ResUT.single_get_self, cjCell]
      exact congrArg some (CellUT.immOf_congr rfl rfl (pj_del a).symm _ _)
    · rw [hR2] at e; exact absurd (Option.some.inj e) CellUT.ownOf_ne_mutOf
    · rw [hR2] at e; exact absurd (Option.some.inj e) CellUT.ownOf_ne_immOf

theorem cj_typed (Θ : CodeTy) {a : Nat} (h : K₀.lt (lfE 3) (lfE a)) :
    (((KTy.ref (KTy.imm (lfE 3) KTy.unit)).immReborrow (lfE 3)).interp Θ).P K₀
      (BoCa.Val.loc 2) (cj a h) :=
  ⟨2, ⟨TSet.single (lfE 3), BoCa.Val.loc 1, ResST.toRes ⟨_, vw_inStratum h⟩⟩, rfl, rfl,
    fun x hx => by
      simp only [TSet.single_set, Finset.mem_singleton] at hx
      subst hx; exact K₀.refl _,
    1, ⟨TSet.single (lfE a), BoCa.Val.unit, ResST.toRes ⟨PMap.empty, emptyT_inStratum _⟩⟩, rfl,
    ResST.toU_toRes _, fun x hx => by
      simp only [TSet.single_set, Finset.mem_singleton] at hx
      subst hx; exact h.1,
    rfl, ResST.toU_toRes _⟩

theorem cj_valid {a : Nat} (h : K₀.lt (lfE 3) (lfE a)) : ResUT.Valid (cj a h) := by
  obtain ⟨σ, hσ⟩ := vw_valid a
  obtain rfl := flat_view hσ
  have hlo : ResUT.Lower (vw (TSet.single (lfE a))) fun l => ((vw (TSet.single (lfE a))).get l).map
      CellUT.erase := ⟨_, hσ, fun _ => rfl⟩
  obtain ⟨τ, hτ, -⟩ := lower_compS_ownT (ResUT.CompS.comm (pj_spec a)) hlo
    (by simp [ResUT.single_get_ne _ (show (2 : BoCa.Loc) ≠ 1 by decide), vw])
  exact valid_single_imm (vw_inStratum h) (ResUT.CompS.comm (pj_spec a)) ⟨τ, hτ⟩

theorem cj_cov (Θ : CodeTy) {a : Nat} (h : K₀.lt (lfE 3) (lfE a)) :
    CovR (sem Θ) K₀ (cj a h) := by
  intro x ψ e
  obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some e
  refine .imm _ _ fun k χ ek => ?_
  change (cjCell a h).wit.get k = some χ at ek
  rw [cjCell, CellUT.wit_immOf] at ek
  obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some ek
  refine .imm _ _ fun k' χ' ek' => ?_
  change (CellUT.immOf (TSet.single (lfE a)) BoCa.Val.unit (PMap.empty : TRes K₀)
    (emptyT_inStratum _)).wit.get k' = some χ' at ek'
  rw [CellUT.wit_immOf] at ek'
  simp at ek'

/-- **Two templates of one escrow**, each meeting `TmplSpecT` at `ref (imm '3 1)`. -/
theorem tmplSpecT_two_wit (Θ : CodeTy) :
    TmplSpecT K₀ Θ Rj (KTy.ref (KTy.imm (lfE 3) KTy.unit)) (BoCa.Val.loc 2) (cj 1 lt31) ∧
    TmplSpecT K₀ Θ Rj (KTy.ref (KTy.imm (lfE 3) KTy.unit)) (BoCa.Val.loc 2) (cj 2 lt32) :=
  ⟨⟨lfE 3, cj_reb (Or.inl rfl) lt31, cj_typed Θ lt31, ⟨_, (agW_of_valid (cj_valid lt31)).choose_spec⟩,
      cj_cov Θ lt31⟩,
    ⟨lfE 3, cj_reb (Or.inr rfl) lt32, cj_typed Θ lt32, ⟨_, (agW_of_valid (cj_valid lt32)).choose_spec⟩,
      cj_cov Θ lt32⟩⟩

/-- A re-reading keeps the lifetime set of an `imm` cell in a witness. -/
theorem rc_wit_imm {Θ : LocTy} {K K' : WCactus} {l m : BoCa.Loc} {ψ : TCell K} {φ : TCell K'}
    {i₀ : TImm K} (h : RC Θ l ψ φ) (e : ψ.wit.get m = some (.imm i₀)) :
    ∃ i', φ.wit.get m = some (.imm i') ∧ i'.ls = i₀.ls := by
  cases h with
  | own => simp [CellUT.wit] at e
  | imm _ i i' _ _ hdom hw =>
      change i.res.get m = some _ at e
      obtain ⟨ψ', e'⟩ : ∃ ψ', i'.res.get m = some ψ' := by
        cases g : i'.res.get m with
        | none => rw [← hdom] at g; rw [e] at g; cases g
        | some ψ' => exact ⟨ψ', rfl⟩
      cases hw m _ _ e e' with
      | imm _ _ j hs _ _ _ => exact ⟨j, e', hs⟩
  | «mut» _ n n' _ _ _ _ hdom hw _ =>
      change n.res.get m = some _ at e
      obtain ⟨ψ', e'⟩ : ∃ ψ', n'.res.get m = some ψ' := by
        cases g : n'.res.get m with
        | none => rw [← hdom] at g; rw [e] at g; cases g
        | some ψ' => exact ⟨ψ', rfl⟩
      cases hw m _ _ e e' with
      | imm _ _ j hs _ _ _ => exact ⟨j, e', hs⟩

/-- **The two templates' canonical images have no common re-reading**, at every lifetime they are
re-taken at, at every tree and location typing. -/
theorem canon_two_wit (β : Life) (Θ' : LocTy) {K' : WCactus} (x : TRes K') :
    ¬ (RR Θ' (relResT Rj β (cj 1 lt31)) x ∧ RR Θ' (relResT Rj β (cj 2 lt32)) x) := by
  rintro ⟨h₁, h₂⟩
  have g₁ : (relResT Rj β (cj 1 lt31)).get 2 = some (relCellT Rj β 2 (cjCell 1 lt31)) := by rw [relResT_get, cj, ResUT.single_get_self]; rfl
  have g₂ : (relResT Rj β (cj 2 lt32)).get 2 = some (relCellT Rj β 2 (cjCell 2 lt32)) := by rw [relResT_get, cj, ResUT.single_get_self]; rfl
  obtain ⟨φ, eφ, r₁⟩ := h₁.get_some g₁
  have r₂ := h₂.2 2 _ φ g₂ eφ
  have w₁ : (relCellT Rj β 2 (cjCell 1 lt31)).wit.get 1 =
      some (.imm ⟨TSet.single (lfE 1), BoCa.Val.unit, ResST.toRes ⟨PMap.empty, emptyT_inStratum _⟩⟩) := by
    rw [(relCellT_props _ _ _ _).2.1, cjCell, CellUT.wit_immOf, vw, ResUT.single_get_self]; rfl
  have w₂ : (relCellT Rj β 2 (cjCell 2 lt32)).wit.get 1 =
      some (.imm ⟨TSet.single (lfE 2), BoCa.Val.unit, ResST.toRes ⟨PMap.empty, emptyT_inStratum _⟩⟩) := by
    rw [(relCellT_props _ _ _ _).2.1, cjCell, CellUT.wit_immOf, vw, ResUT.single_get_self]; rfl
  obtain ⟨i₁, e₁, s₁⟩ := rc_wit_imm r₁ w₁
  obtain ⟨i₂, e₂, s₂⟩ := rc_wit_imm r₂ w₂
  rw [e₁] at e₂
  cases Option.some.inj e₂
  have := congrArg TSet.set (s₁.symm.trans s₂)
  simp only [TSet.single_set, Finset.singleton_inj] at this
  exact absurd this (by decide)

end BoCa.Fig16.Tree.Wp

end

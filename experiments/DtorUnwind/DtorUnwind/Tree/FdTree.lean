import DtorUnwind.SI.FdTypes
import DtorUnwind.Tree.Rel

/-!
# The join's frame condition from the resumer's types, in the tree order

`SI/FdTypes.lean` refutes `FdFromLifetimeTypes`: a resumer's value of type `Imm 'r 1` at
`δ('r) = β` can be a second copy of the stored task's view of its lent location `ℓ` at `α`,
because in the chain `β ⊑ α` once `β` was opened after `α`. `ptoImmS` asks only `δ('r) ⊑ ⊓β̄`.

`FdFromLifetimeTypesT K` is the same statement with the order read in a `Cactus` `K`: the
scope `a` and the two lends in it (`α ⊏ a`, `β ⊏ a` in `K`), the resumer's value typed by
`vCT K`, and one hypothesis the chain cannot state: the resumer's lend is not nested inside the
task's (`¬ β ⊑ α` in `K`). That holds when the two are siblings (`not_le_of_siblings`), and also
after the task is grafted under the resumer, when `α` lies inside `β`
(`not_le_of_lt_flip`).

`fdFromLifetimeTypesT` proves it for every `K`. A view of `ℓ` anywhere in the world carries the
task's lifetime and nothing else (`FrameLife`, clause 1); `ptoImmT` asks `δ('r) ⊑ x` at every
member `x`; so a copy at `ℓ` would put `β` inside `α`.

`old_config_not_vCT`: the copy `not_fdFromLifetimeTypes` builds is refused by `vCT star` (in
`star`, `β = 2` and `α = 1` are siblings), while `old_config_vCE` restates that the printed
relation admits it. `fdFromLifetimeTypesT_nonvacuous`: every hypothesis is met at that world
with the resumer holding its own view of its own lend instead.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Tree
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.DtorUnwind.SI
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LSub LifeVar)

/-- **What a resume reads of the resumer's other resources, from their types in `K`.**
`FdFromLifetimeTypes` with `⊏` read in `K`, the resumer's value typed by `vCT K`, and the
resumer's lend not nested inside the task's (`¬ K.le β α`). -/
def FdFromLifetimeTypesT (K : Cactus) : Prop :=
  ∀ (W ρf ρS ρk ρrest : WRes) (ps : List FrameRec) (ls : List SRec) (μ : Heap)
    (p q : FrameRec) (α β a : Life) (δ : LSub) (r : LifeVar) (v : Val),
    TWNC W ps (rsOf ls) → Tagged W ps ls → ResU.Lower W μ →
    ResU.CompS ρf ρS W → ResU.CompS ρk ρrest ρS →
    p ∈ ps → FrameLife W p α → (∃ ψ, ρk.get p.le = some ψ) → K.lt α a →
    q ∈ ps → q ≠ p → FrameLife W q β → (BoCa.Lifetime.Life.var r).interp δ = some β → K.lt β a →
    ¬ K.le β α →
    vCT (ℍ := ℍ) K none true (.imm (.var r) .unit) ls δ v ρrest →
    joinFd (Val.loc p.le) ρrest

/-- Siblings: neither is nested inside the other. -/
theorem not_le_of_siblings {K : Cactus} {α β : Life} (h : ¬ K.le β α ∧ ¬ K.le α β) :
    ¬ K.le β α := h.1

/-- After a graft that puts `α` strictly inside `β`, `β` is not inside `α`. -/
theorem not_le_of_lt_flip {K : Cactus} {α β : Life} (h : K.lt α β) : ¬ K.le β α :=
  fun h' => h.2 (K.antisymm h.1 h')

/-- An `imm` cell of the right operand of a `○` sits, with its lifetimes, inside the
composite's `imm` cell at the same location. -/
theorem compR_imm_right_ls {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompR ρ₁ ρ₂ ρ) {l : Loc} {s : LSet}
    {v : Val} {χ : WRes} {h : χ.InStratum s.join}
    (e : ρ₂.get l = some (CellU.immOf s v χ h)) :
    ∃ (s' : LSet) (v' : Val) (χ' : WRes) (h' : χ'.InStratum s'.join),
      ρ.get l = some (CellU.immOf s' v' χ' h') ∧ ∀ x, s.mem x → s'.mem x := by
  obtain ⟨ζ, hζ, hk, -, -⟩ := ResU.CompR.get_imm_right hc e (CellU.kind_immOf _ _ _ _)
  obtain ⟨s', hs', hη⟩ := CellU.imm_eta hk
  rw [hη] at hζ
  exact ⟨s', _, _, hs', hζ, fun x hx => ResU.CompR.get_ls_imm hc.comm e hζ hx⟩

/-- The same through `ag`. -/
theorem agW_imm_ls {ρ a : WRes} (hag : AgW ρ a) {l : Loc} {s : LSet} {v : Val} {χ : WRes}
    {h : χ.InStratum s.join} (e : ρ.get l = some (CellU.immOf s v χ h)) :
    ∃ (ζ : CellU Loc Val) (t : LSet), a.get l = some ζ ∧ ζ.lsOf = some t ∧
      ∀ x, s.mem x → t.mem x := by
  obtain ⟨ζ, hζ, hk, -, -⟩ := AgW.get_imm hag e (CellU.kind_immOf _ _ _ _)
  obtain ⟨t, ht, hη⟩ := CellU.imm_eta hk
  refine ⟨ζ, t, hζ, by rw [hη]; rfl, fun x hx => ?_⟩
  rw [hη] at hζ
  exact AgW.get_ls_imm hag e hζ hx

/-- **The join's frame condition follows from the resumer's types in the tree order.** -/
theorem fdFromLifetimeTypesT (K : Cactus) : FdFromLifetimeTypesT (ℍ := ℍ) K := by
  intro W ρf ρS ρk ρrest ps ls μ p q α β a δ r v hT _ _ hW hS _ hFLp _ _ _ _ _ hδ _ hnest hv
  obtain ⟨β', hβ', ℓ, ρ₁, ρ₂, hc, ⟨rfl, -, -⟩, s, u, σ, hσ, ls₀, rfl, hpay, hle, -⟩ := hv
  have eβ : β' = β := Option.some.inj (hβ'.symm.trans hδ)
  subst eβ
  obtain ⟨rfl, -⟩ : σ = PMap.empty ∧ u = Val.unit := hpay
  obtain rfl := eq_of_compS_empty_left hc
  refine ⟨p.le, rfl, fun τ hτ => ?_⟩
  by_cases hℓ : p.le = ℓ
  · exfalso
    subst hℓ
    obtain ⟨s₁, _, _, _, e₁, hs₁⟩ :=
      compR_imm_right_ls hS.toCompR (ResU.single_get_self _ _)
    obtain ⟨s₂, _, _, _, e₂, hs₂⟩ := compR_imm_right_ls hW.toCompR e₁
    obtain ⟨τW, eW, ag, -, hag, -⟩ := hT.valid
    obtain ⟨ζ, t, hζ, ht, hst⟩ := agW_imm_ls hag e₂
    have hj : s.join = α := hFLp.1 ag hag ζ t hζ ht _ (hst _ (hs₂ _ (hs₁ _ s.join_mem)))
    exact hnest (hj ▸ hle _ s.join_mem)
  · exact flat_single_imm_empty hτ _ hℓ

/-! ### The configuration of `not_fdFromLifetimeTypes`, in `star` -/

/-- The task's lend `α = 1`, the resumer's `β = 2`, the scope `a = ⊤`: in `star`, siblings
inside `a`. -/
theorem star_config :
    Cactus.star.lt (OrderDual.toDual 1) ⊤ ∧ Cactus.star.lt (OrderDual.toDual 2) ⊤ ∧
      ¬ Cactus.star.le (OrderDual.toDual 2) (OrderDual.toDual 1) ∧
      ¬ Cactus.star.le (OrderDual.toDual 1) (OrderDual.toDual 2) :=
  ⟨Cactus.star_lt_top (by decide), Cactus.star_lt_top (by decide),
    Cactus.star_not_le (by decide) (by decide), Cactus.star_not_le (by decide) (by decide)⟩

/-- The copy of the task's view of `0` at `α = 1` is not a value of `Imm 'r 1` at
`δ('r) = 2` in `star`: whatever records the list holds. -/
theorem old_config_not_vCT (ls : List SRec) :
    ¬ vCT (ℍ := ℍ) Cactus.star none true (.imm (.var 0) .unit) ls ⟨[(0, 2)]⟩ (Val.loc 0)
      (viewA 0 Val.unit (OrderDual.toDual 1)) := by
  rintro ⟨β', hβ', ℓ, ρ₁, ρ₂, hc, ⟨rfl, hl, -⟩, s, u, σ, hσ, ls₀, e, -, hle, -⟩
  have eβ : β' = OrderDual.toDual 2 := Option.some.inj hβ'.symm
  subst eβ
  obtain rfl := eq_of_compS_empty_left hc
  cases hl
  have hget := congrArg (fun ρ : WRes => ρ.get 0) e
  simp only [viewA, ResU.single_get_self] at hget
  obtain ⟨hs, -, -⟩ := CellU.immOf_inj (Option.some.inj hget)
  subst hs
  exact Cactus.star_not_le (m := 2) (n := 1) (by decide) (by decide)
    (hle _ (LSet.singleton _).join_mem)

/-! ### The world of `not_fdFromLifetimeTypes` -/

/-- `δ('r) = 2` at `'r = 0`. -/
def δ₀ : LSub := ⟨[(0, 2)]⟩

/-- The task's lend's record (`0`) and the resumer's (`1`). -/
abbrev pT : FrameRec := cexRecF 0 δ₀
abbrev qR : FrameRec := cexRecF 1 δ₀

/-- The world's list: the resumer's lend at `β = 2` over the task's at `α = 1`. -/
abbrev lsW : List SRec :=
  frameList qR [] (OrderDual.toDual 2) (frameList pT [] (OrderDual.toDual 1) [])

/-- **The world `not_fdFromLifetimeTypes` builds**: the task's view of `0` at `α = 1` beside the
resumer's view of `1` at `β = 2`, both lends recorded and tagged, lowered to a heap. -/
theorem fdWorld : ∃ (W : WRes) (μ : Heap),
    TWNC W [qR, pT] (rsOf lsW) ∧ Tagged W [qR, pT] lsW ∧ ResU.Lower W μ ∧
    ResU.CompS (viewA 0 Val.unit (OrderDual.toDual 1)) (viewA 1 Val.unit (OrderDual.toDual 2)) W ∧
    FrameLife W pT (OrderDual.toDual 1) ∧ FrameLife W qR (OrderDual.toDual 2) := by
  let α : Life := OrderDual.toDual 1
  let β : Life := OrderDual.toDual 2
  let r : LifeVar := 0
  let δ : LSub := ⟨[(r, 2)]⟩
  let p := cexRecF 0 δ
  let q := cexRecF 1 δ
  let v₀ : WRes := viewA 0 Val.unit α
  let v₁ : WRes := viewA 1 Val.unit β
  -- the task's lend: `0 ↦ own(())`, lent at `α`
  let W₁ : WRes := ResU.single 0 (CellU.ownOf Val.unit)
  have hv₁ : ResU.Valid W₁ := ResU.valid_single_own 0 Val.unit
  have hT₁ : TWNC W₁ [] (rsOf []) :=
    TWNC.alloc TWNC.empty lower_empty rfl (compS_empty_left _) hv₁
  have hl₁ : ResU.Lower W₁ (BoCa.BoLo.Heap.upd (fun _ => none) 0 Val.unit) :=
    lower_compS_own (compS_empty_left _) lower_empty rfl
  have hS₀ : Split [] [] [] := ⟨fun x => by simp, fun x hx => by simp at hx⟩
  have htg₀ : Tagged W₁ [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨BI, fρ, hBI, -, hfρ, -, hT₂, htg₂, hl₂⟩ :=
    capture_world (ρb := PMap.empty) (A := α) 0 .unit δ (fun x hx => by cases hx) Val.unit
      (inStratumE α) (ResU.comp_empty_right _) (ResU.comp_empty_right _)
      ⟨rfl, rfl⟩ (ds := []) (fun d => ⟨fun h => by simp at h, fun h => absurd h
        (not_desc_cexRecF 0 δ d)⟩)
      (ρf := PMap.empty) (ResU.hash_symm (ResU.hash_empty_right hv₁)) (compS_empty_left _) hS₀
      hT₁ htg₀ hl₁
  have e₁ : fρ = BI := eq_of_compS_empty_left hfρ
  subst e₁
  have e₂ : fρ = v₀ := eq_of_compS_empty_left hBI
  subst e₂
  -- the resumer's lend: `1 ↦ own(())`, allocated beside, lent at `β`
  have hvv₀ : ResU.Valid v₀ := hT₂.valid
  have hh : ResU.Hash v₀ (ResU.single 1 (CellU.ownOf Val.unit)) :=
    hash_own_of_flatFree hvv₀ (fun τ hτ => flat_single_imm_empty hτ 1 (by decide)) Val.unit
  obtain ⟨W₂, hW₂, hvW₂⟩ := hh.2
  have hμ1 : BoCa.BoLo.Heap.upd (fun _ => none) 0 Val.unit 1 = none := by
    simp [BoCa.BoLo.Heap.upd]
  obtain ⟨σ', hσ', -, hl₃⟩ := hash_compS_own (compS_empty_left v₀) hl₂ hμ1 hW₂
  have e₃ : σ' = W₂ := eq_of_compS_empty_left hσ'
  subst e₃
  have hT₃ : TWNC σ' [p] (rsOf (frameList p [] α [])) :=
    TWNC.alloc hT₂ hl₂ hμ1 hW₂ hvW₂
  have htg₃ : Tagged σ' [p] (frameList p [] α []) :=
    tagged_of_ag (fun a ha => alloc_ag hW₂ ha) htg₂
  have hS₁ : Split [p] [] [p] := ⟨fun x => by simp, fun x hx => by simp at hx⟩
  obtain ⟨BI', fρ', hBI', -, hfρ', -, hT, htg, hlow⟩ :=
    capture_world (ρb := PMap.empty) (A := β) 1 .unit δ (fun x hx => by cases hx) Val.unit
      (inStratumE β) (ResU.comp_empty_right _) (ResU.comp_empty_right _)
      ⟨rfl, rfl⟩ (ds := []) (fun d => ⟨fun h => by simp at h, fun h => absurd h
        (not_desc_cexRecF 1 δ d)⟩)
      (ρf := v₀) (hh) hW₂ hS₁ hT₃ htg₃ hl₃
  have e₄ : BI' = v₁ := eq_of_compS_empty_left hBI'
  subst e₄
  -- the tags
  have hpq : q ≠ p := by simp [p, q, cexRecF]
  have hFLp : FrameLife fρ' p α := by
    obtain ⟨x, hx, hd, hfx⟩ := htg (p, α) (by simp [frameList])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact absurd (descR_cexRecF hd) (Ne.symm hpq)
    · exact hfx
  have hFLq : FrameLife fρ' q β := by
    obtain ⟨x, hx, hd, hfx⟩ := htg (q, β) (by simp only [frameList]; exact List.mem_cons_self)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hfx
    · exact absurd (descR_cexRecF hd) hpq
  exact ⟨fρ', _, hT, htg, hlow, hfρ', hFLp, hFLq⟩
/-- The printed relation admits the copy: `δ('r) = 2 ⊑ 1` in the chain. -/
theorem old_config_vCE : vCE (ℍ := ℍ) none true (.imm (.var 0) .unit) lsW δ₀ (Val.loc 0)
    (viewA 0 Val.unit (OrderDual.toDual 1)) := by
  refine ⟨OrderDual.toDual 2, rfl, 0, PMap.empty, _, compS_empty_left _, ⟨rfl, ⟨rfl, ?_⟩⟩, ?_⟩
  · refine ⟨.unit, δ₀, TyEq.refl _ _, Or.inl ⟨pT, by simp [rsOf, frameList], rfl, rfl, ?_⟩⟩
    intro y hy; cases hy
  · refine ⟨LSet.singleton _, Val.unit, PMap.empty, inStratumE _, [], rfl, ⟨rfl, rfl⟩, ?_, ?_⟩
    · show OrderDual.toDual 2 ≤ OrderDual.toDual 1
      exact OrderDual.toDual_le_toDual.mpr (by omega)
    · intro x
      simp only [List.not_mem_nil, false_iff, not_and]
      intro hx
      simp only [frameList, List.map_nil, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | rfl
      · show ¬ (OrderDual.toDual 2 : Life) ⊐ OrderDual.toDual 1
        exact not_lt.mpr (OrderDual.toDual_le_toDual.mpr (by omega))
      · exact lt_irrefl _

/-- The resumer's own view of its own lend is a value of `Imm 'r 1` at `δ('r) = 2` in `star`. -/
theorem resumer_view_vCT : vCT (ℍ := ℍ) Cactus.star none true (.imm (.var 0) .unit) lsW δ₀
    (Val.loc 1) (viewA 1 Val.unit (OrderDual.toDual 2)) := by
  refine ⟨OrderDual.toDual 2, rfl, 1, PMap.empty, _, compS_empty_left _, ⟨rfl, ⟨rfl, ?_⟩⟩, ?_⟩
  · refine ⟨.unit, δ₀, TyEq.refl _ _, Or.inl ⟨qR, by simp [rsOf, frameList], rfl, rfl, ?_⟩⟩
    intro y hy; cases hy
  · refine ⟨LSet.singleton _, Val.unit, PMap.empty, inStratumE _, [], rfl, ⟨rfl, rfl⟩, ?_, ?_⟩
    · intro x hx
      cases hx
      exact Cactus.star.refl _
    · intro x
      simp only [List.not_mem_nil, false_iff, not_and]
      intro hx ⟨y, hy, hlt⟩
      cases hy
      simp only [frameList, List.map_nil, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | rfl
      · exact hlt.2 rfl
      · exact Cactus.star_not_le (m := 2) (n := 1) (by decide) (by decide) hlt.1

/-- **Every hypothesis of `FdFromLifetimeTypesT star` is met** at the world of
`not_fdFromLifetimeTypes`, with the resumer holding its own view (`ρrest`) beside the task's
share (`ρk`), the scope at `⊤`. -/
theorem fdFromLifetimeTypesT_nonvacuous : ∃ (W : WRes) (μ : Heap),
    TWNC W [qR, pT] (rsOf lsW) ∧ Tagged W [qR, pT] lsW ∧ ResU.Lower W μ ∧
    ResU.CompS PMap.empty W W ∧
    ResU.CompS (viewA 0 Val.unit (OrderDual.toDual 1)) (viewA 1 Val.unit (OrderDual.toDual 2)) W ∧
    pT ∈ [qR, pT] ∧ FrameLife W pT (OrderDual.toDual 1) ∧
    (∃ ψ, (viewA 0 Val.unit (OrderDual.toDual 1)).get pT.le = some ψ) ∧
    Cactus.star.lt (OrderDual.toDual 1) ⊤ ∧
    qR ∈ [qR, pT] ∧ qR ≠ pT ∧ FrameLife W qR (OrderDual.toDual 2) ∧
    (BoCa.Lifetime.Life.var 0).interp δ₀ = some (OrderDual.toDual 2) ∧
    Cactus.star.lt (OrderDual.toDual 2) ⊤ ∧
    ¬ Cactus.star.le (OrderDual.toDual 2) (OrderDual.toDual 1) ∧
    vCT (ℍ := ℍ) Cactus.star none true (.imm (.var 0) .unit) lsW δ₀ (Val.loc 1)
      (viewA 1 Val.unit (OrderDual.toDual 2)) := by
  obtain ⟨W, μ, hT, htg, hlow, hc, hFLp, hFLq⟩ := fdWorld
  obtain ⟨h1, h2, h3, -⟩ := star_config
  exact ⟨W, μ, hT, htg, hlow, compS_empty_left _, hc, by simp, hFLp,
    ⟨_, ResU.single_get_self _ _⟩, h1, by simp, by simp [pT, qR, cexRecF], hFLq, rfl, h2, h3,
    resumer_view_vCT⟩


end BoCa.Fig16.LogRel.Core.Tree

end

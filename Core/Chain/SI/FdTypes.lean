import Core.Chain.SI.CactusInv

/-!
# Is the join's frame condition supplied by lifetimes on continuation types?

A lend left open across a stop is ended in a later segment, under a frame its resumer chose
(`uncapture_world`). Ending it asks that the frame hold nothing at the lent location: `joinFd`
in the join's table entry (`SI/CaptureScope.lean`), `JoinReady` at the scheduler
(`SI/CactusInv.lean`). For a lend opened inside a task, the generic form is `FrameOK O`: the frame
holds nothing at the location of any record the resumed computation owns. `frameOK_joinFd`: it
gives `joinFd` at every owned record.

The hypothesis under test (`770-structure.md` §5): a continuation type `κ@a` carrying the lifetime
of the borrows it holds makes this local. A resumer that holds `κ@a` beside other values knows,
of those values, their types at its own lifetimes (`vCE … δ`), and of `κ`'s records that they
are strictly shorter than `a` (a lend opened inside the handled computation is fresh there).

`not_fdFromLifetimeTypes` refutes the claim that this suffices. The configuration: one lend, of
`ℓ = 0` at `α`, its record proper and its cell held by the share; beside it, a value of type
`Imm 'r 1` at `δ('r) = β ⊏ α` (a lend the resumer opened after `α`), whose resource is a second
copy of the share's `imm` cell (`[TR]` 6.116). Every hypothesis is discharged on a `TWNC` world
built by `TWNC.alloc` and `capture_world`. `𝒱⟦Imm 'r 1⟧` admits the copy because `ptoImmS`
asks only `δ('r) ⊑ ⊓β̄` and `Coh`, both of which a view of `ℓ` at `α` meets once `β ⊑ α`.

The reason is the order on `Life`: it is total (`ℕᵒᵈ`, row 5.9), so a lifetime opened later on
the resumer's side is comparable with, and shorter than, a lifetime opened earlier inside a
stored task, and the stratum `⊒ δ('r)` contains `α`. Nesting of lends across stored tasks is a
tree; the resumer's stratum cannot tell its own branch from the stored task's.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap)
open BoCa.Lifetime (LSub LifeVar)

/-- **The frame holds nothing at the location of any record the computation owns.** -/
def FrameOK (O : List FrameRec) (ρ : WRes) : Prop :=
  ∀ p ∈ O, ∀ τ, ResU.Flat ρ τ → τ.get p.le = none

/-- `FrameOK` gives the join's frame condition at every owned record. -/
theorem frameOK_joinFd {O : List FrameRec} {ρ : WRes} (h : FrameOK O ρ) {p : FrameRec}
    (hp : p ∈ O) : joinFd (Val.loc p.le) ρ :=
  ⟨p.le, rfl, h p hp⟩

/-- **What a resume could read of the resumer's other resources, if `fd` came from the types.**
The world: a tagged `TWNC` world at the list, lowered, the resumer's frame `ρ_f` beside its
resource `ρ_S`. The resumer's resource is the stored continuation's share `ρ_k` beside the rest
`ρ_rest`. `κ@a`: the share holds the cell of its record `p`, a record proper whose lifetime `α` is
strictly shorter than `a`. The resumer's scope: a lend of its own, the record proper `q ≠ p` at
`β ⊏ a`, named by the lifetime variable `'r`. The rest: a value of type `Imm 'r 1` at `δ`. The
conclusion: the rest holds nothing at `p`'s location, at any depth (`joinFd`). -/
def FdFromLifetimeTypes : Prop :=
  ∀ (W ρf ρS ρk ρrest : WRes) (ps : List FrameRec) (ls : List SRec) (μ : Heap)
    (p q : FrameRec) (α β a : Life) (δ : LSub) (r : LifeVar) (v : Val),
    TWNC W ps (rsOf ls) → Tagged W ps ls → ResU.Lower W μ →
    ResU.CompS ρf ρS W → ResU.CompS ρk ρrest ρS →
    p ∈ ps → FrameLife W p α → (∃ ψ, ρk.get p.le = some ψ) → α ⊏ a →
    q ∈ ps → q ≠ p → FrameLife W q β → (BoCa.Lifetime.Life.var r).interp δ = some β → β ⊏ a →
    vCE (ℍ := ℍ) none true (.imm (.var r) .unit) ls δ v ρrest →
    joinFd (Val.loc p.le) ρrest

/-! ### The configuration -/

/-- The flattening of one `imm` cell with an empty witness is that cell. -/
theorem flat_single_imm_empty_eq {m : Loc} {s : LSet} {u : Val}
    {h : ResU.InStratum s.join (PMap.empty : WRes)} {τ : WRes}
    (hτ : ResU.Flat (ResU.single m (CellU.immOf s u PMap.empty h)) τ) :
    τ = ResU.single m (CellU.immOf s u PMap.empty h) := by
  obtain ⟨e, a, he, ha, hc⟩ := hτ
  have he0 : e = PMap.empty := ExS.functional he (ExW.empty_of_all_imm (fun x ψ hx => by
    obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hx; exact CellU.kind_immOf _ _ _ _))
  obtain ⟨ev, av, p, hev, hav, hp, hpa⟩ := AgW.single_imm_inv ha
  obtain rfl : ev = PMap.empty := ExR.functional hev exW_empty
  obtain rfl : av = PMap.empty := AgW.functional hav agW_empty
  obtain rfl : p = PMap.empty := ResU.CompR.functional hp (ResU.comp_empty_right _)
  obtain rfl : a = ResU.single m (CellU.immOf s u PMap.empty h) :=
    ResU.CompR.functional hpa (ResU.comp_empty_right _)
  subst he0
  exact eq_of_compS_empty_left hc

/-- A lend's record at `ℓ` holding `()`, empty payload, type `1`. -/
def cexRecF (l : Loc) (δ : LSub) : FrameRec := ⟨l, Val.unit, PMap.empty, .unit, δ⟩

theorem not_desc_cexRecF (l : Loc) (δ : LSub) (d : FrameRec) : ¬ Desc (cexRecF l δ) d := by
  rintro ⟨path, hne, hp⟩
  cases hp with
  | nil => exact hne rfl
  | cons hsub _ =>
      obtain ⟨-, -, ζ, eζ, -⟩ := hsub
      simp [cexRecF, PMap.empty_get] at eζ

theorem descR_cexRecF {l : Loc} {δ : LSub} {d : FrameRec} (h : DescR (cexRecF l δ) d) :
    d = cexRecF l δ :=
  descR_empty rfl h

/-- **Lifetimes on continuation types do not supply the join's frame condition.** The stored
task lent `ℓ = 0` at `α = 1` inside its scope `a = 0`; the resumer lent `ℓ = 1` at `β = 2`
afterwards; the resumer's value of type `Imm 'r 1` at `δ('r) = β` is a copy of the task's view of
`0`. -/
theorem not_fdFromLifetimeTypes : ¬ FdFromLifetimeTypes (ℍ := ℍ) := by
  intro H
  let a : Life := OrderDual.toDual 0
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
  have hdup : ResU.CompS v₀ v₀ v₀ := compS_imm_dup 0 _ Val.unit _ _
  have hv : vCE (ℍ := ℍ) none true (.imm (.var r) .unit) (frameList q [] β (frameList p [] α []))
      δ (Val.loc 0) v₀ := by
    refine ⟨β, rfl, 0, PMap.empty, v₀, compS_empty_left _, ⟨rfl, ⟨rfl, ?_⟩⟩, ?_⟩
    · refine ⟨.unit, δ, TyEq.refl _ _, Or.inl ⟨p, by simp [rsOf, frameList], rfl, rfl, ?_⟩⟩
      intro y hy; cases hy
    · refine ⟨LSet.singleton α, Val.unit, PMap.empty, inStratumE _, [], rfl, ⟨rfl, rfl⟩, ?_, ?_⟩
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
  have hj := H fρ' v₁ v₀ v₀ v₀ [q, p] (frameList q [] β (frameList p [] α [])) _ p q α β a δ r
    (Val.loc 0) hT htg hlow (ResU.CompS.comm hfρ') hdup (by simp) hFLp
    ⟨_, ResU.single_get_self _ _⟩ (OrderDual.toDual_lt_toDual.mpr (by omega)) (by simp) hpq hFLq
    rfl (OrderDual.toDual_lt_toDual.mpr (by omega)) hv
  obtain ⟨m, hm, hfree⟩ := hj
  cases hm
  obtain ⟨σ, hσ⟩ := hvv₀
  have e := flat_single_imm_empty_eq hσ
  have := hfree σ hσ
  rw [e] at this
  simp [p, cexRecF, ResU.single_get_self] at this

end BoCa.Fig16.LogRel.Core.Chain.SI

end

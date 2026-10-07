import ProbeD1.GapPos

/-!
# ProbeD1 — W's `U` clause reads the room Core's `∀` skips (`GAP.md` §3.4)

`GapWitness.lean` shows Core's `ℕ`-`∀` reading adjacency: at `∀'0 ⊏ ⊤. F (Mut '0 1)` the closure
`Λ. return ℓ₀` is related over a `mut` cell at `1`, adjacent to `⊤`, and not over a `mut` cell at
`2`. `GAP.md` §3.4 says W's `U` clause already reads every position an admissible embedding can
open, since it asks the closure's body at every instantiation of the stack, and that the closure,
transplanted into a W `U` slot over the view of an entry adjacent to `⊤`, is therefore not a W `U`
value. This file checks that claim.

* **W's `U` clause is reading (B)** (`wU_allPosJ`): a W `U` value at a `∀` type is `AllPosJ` of its
  body, so with `instRealisesCut_at` it reads every cut below the stack's cut.
* **The configuration** (`adjIndex`): one 6.65 entry `muEnt` lending the place `0` at `1`, so its
  cut is `⊤`; the resource the entry's view `0 ↦ mut(1, (), ∅, 𝒱⟦1⟧)`; the table and the guard's
  views hold there.
* **Core's `U` clause admits the closure** (`adj_core_U`): its body is Core's `∀`, which holds by
  adjacency (`adj_holds_ls`).
* **W's does not** (`adj_not_wU`): every split of the resource puts the cell among the views
  (`not_relendJ_adj`), and at the instantiation `shift ⊤ 1`, which opens the cut between `⊤` and the
  view, the view is handed back at `2`, where the body's `∀` at `α = 1` meets the cell's lifetime
  (`adj_run_fails`, the run of `adj_fails`).

So at this configuration W's `U` clause is the position-`∀` at work: it reads the cut that Core's
`ℕ`-`∀` skips. The closure is not claimed derivable (`GAP.md` §3c), and nothing here refutes a
statement of the probe: both results are about the relations' clauses at one configuration.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace ProbeD1
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open GhostEnd (LEnt LStack extS stratS TabAtS innerView unitQ unitQ_holds innerView_ptoMutS)

/-! ### W's `U` clause is reading (B) -/

/-- **A W `U` value at a `∀` type reads the position-`∀`**: under its guard, a value of
`U (∀'x ⊏ c. C)` at `binder0` is `AllPosJ` of its body, the clause's records moved exactly. Its
`U` clause asks the body at every instantiation of the stack, the views handed back, and the `∀`
clause then asks every lifetime below the bound at the instantiated reading; by `instRealisesCut_at`
that reaches every cut of the lifetimes in play below the stack's cut. -/
theorem wU_allPosJ {σ : LStack} {δ : LSub} {x : LifeVar} {c : Lifetime.Life} {C : CTy}
    {αs : List Life} {ls : List SRec} {f : Val} {ρ : WRes}
    (h : vRLJ (ℍ := ℍ) .binder0 σ δ (.thunk (.all x c C)) αs ls f ρ) (ht : TabAtS σ αs ρ)
    (hpv : PlaceViewsL (extS δ σ αs) σ αs ls ρ) :
    AllPosJ δ σ c (fun δ' αs' ls' α => guardPV (extS (δ'.extend x α) σ αs') σ αs' ls'
      (cRLJ (ℍ := ℍ) .binder0 σ (δ'.extend x α) C αs' ls'
        (.app (forceE (.all x c C) (.val f)) (.val .unit)))) αs ls ρ := by
  rw [vRLJ_thunk0] at h
  obtain ⟨ds, ρz, ρn, hc, hn, hz, H⟩ := h ht hpv
  refine ⟨ds, ρz, ρn, hc, hn, hz, fun ι hat hro ρv τ hv hcv => ?_⟩
  have hb := H ι hat (ι.recs ls) (Ext.refl _ _) (fun _ hx _ => hx)
    (fun y hy _ => ⟨y, hy, RecUpTo.refl y⟩) hro ρv τ hv hcv
  exact (hb (ι.recs ls) σ (ι.life αs) rfl rfl
    (fun e he hx => absurd (List.mem_map_of_mem (f := LEnt.x) he) hx)).1

/-! ### The configuration -/

/-- The instantiation `shift ⊤ 1`, which opens the cut between `⊤` and `1`. -/
abbrev adjι : Inst := Inst.ofEmb adjθ

theorem adj_stackOK : StackOK [muEnt] [lifeN 1] :=
  ⟨rfl, List.isChain_singleton _, List.nodup_singleton _⟩

theorem adj_cutOf : cutOf [lifeN 1] = some ⊤ := rfl

theorem adj_instAt : InstAt [lifeN 1] adjι := fun c θ h => by cases h; exact adj_cutOf

theorem adjι_life : adjι.life [lifeN 1] = [lifeN 2] := rfl

/-- The view's cell. -/
abbrev viewCell (α : Life) : CellU BoCa.Loc Val :=
  CellU.mutOf α Val.unit PMap.empty (ResU.inStratum_empty α) (unitQ α) (unitQ_holds α)

theorem innerView_get (α : Life) : (innerView 0 α).get 0 = some (viewCell α) :=
  ResU.single_get_self _ _

/-- A cell of the view at any depth is its one cell. -/
theorem deepAt_innerView {α : Life} {l : BoCa.Loc} {ψ : CellU BoCa.Loc Val}
    (h : DeepAt (innerView 0 α) l ψ) : l = 0 ∧ ψ = viewCell α := by
  cases h with
  | top e => exact ResU.single_get_eq_some e
  | wit e d =>
      obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
      rw [CellU.wit_mutOf] at d
      exact absurd d not_deepAt_empty

/-- **The entry's view at `α`**, at every reading: a `mut` cell exactly at `α` storing `𝒱⟦1⟧`. -/
theorem vwEW_innerView (s : LSub) (α : Life) (ls : List SRec) :
    vwEW s muEnt true α ls (innerView 0 α) := by
  refine ⟨innerView_ptoMutS 0 α ls s, fun ψ hψ => ?_⟩
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some hψ
  exact ⟨rfl, fun t ht => by simp [CellU.lsOf, CellU.mutOf] at ht⟩

/-- **The guard's views at the view.** -/
theorem pvl_innerView (s : LSub) (α : Life) (ls : List SRec) :
    PlaceViewsL s [muEnt] [α] ls (innerView 0 α) := by
  refine ⟨fun l ψ hx _ e α' hi => ?_, fun l ψ hd _ _ => ?_⟩
  · obtain ⟨rfl, rfl⟩ := deepAt_innerView hx.toDeepAt
    have hi' : innerAt [muEnt] [α] 0 = some (muEnt, α) := by simp [innerAt]
    rw [hi'] at hi
    obtain ⟨rfl, rfl⟩ : muEnt = e ∧ α = α' := by simpa using hi
    exact vwEW_innerView s α ls
  · obtain ⟨rfl, rfl⟩ := deepAt_innerView hd
    exact ⟨muEnt, α, List.mem_singleton_self _, rfl, vwEW_innerView s α ls⟩

/-- **W's views of the stack at the view.** -/
theorem vwSL_innerView (s : LSub) (α : Life) (ls : List SRec) :
    vwSL s [muEnt] [true] [α] ls (innerView 0 α) :=
  ⟨⟨innerView 0 α, PMap.empty, ResU.comp_empty_right _, by
      have : GhostEnd.vis [] muEnt true = true := rfl
      rw [this]; exact vwEW_innerView s α ls, ⟨rfl, trivial⟩⟩, pvl_innerView s α ls⟩

/-- **The table at the view**: its cell is at the entry's own place, at `α`. -/
theorem tab_innerView (α : Life) : TabAtS [muEnt] [α] (innerView 0 α) := by
  refine ⟨fun a ha => ?_, fun a _ k ψ hk e => ?_⟩
  · obtain rfl : a = α := (Option.some.inj ha).symm
    intro l ψ e
    obtain ⟨rfl, rfl⟩ := ResU.single_get_eq_some e
    exact GhostEnd.down_lt a
  · exact absurd (ResU.single_get_eq_some e).1 (fun h => hk (by simp [h]))

/-- **The configuration meets the index hypotheses `SemSJ` and `CtxRelendableAtJ` put on it**, at
`Δ = ∅` and the empty reading. -/
theorem adjIndex :
    StackOK [muEnt] [lifeN 1] ∧ OuterBelowTop [lifeN 1] ∧ SubDom adjδ LifeCtx.empty ∧
      LifeCtx.empty.Models (extS adjδ [muEnt] [lifeN 1]) ∧ RecsOutside [lifeN 1] [] ∧
      SubOutside [muEnt] [lifeN 1] adjδ ∧ TabAtS [muEnt] [lifeN 1] (innerView 0 (lifeN 1)) ∧
      PlaceViewsL (extS adjδ [muEnt] [lifeN 1]) [muEnt] [lifeN 1] [] (innerView 0 (lifeN 1)) := by
  refine ⟨adj_stackOK, fun o ho => ?_, fun y hy => absurd rfl hy, fun x u hx => ?_,
    fun a _ x hx => absurd hx List.not_mem_nil, fun e a _ p hp => ?_, tab_innerView _,
    pvl_innerView _ _ _⟩
  · obtain rfl : o = lifeN 1 := (Option.some.inj ho).symm
    show (0 : ℕ) < 1
    decide
  · exact absurd hx (by simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind])
  · simp [boundBefore] at hp

/-! ### Every split puts the cell among the views -/

/-- **At the configuration, the `U` clause's body is asked at `shift ⊤ 1` over the view handed
back at `2`**: a part strictly above the outermost lend holds no cell at `1`, so the view is
dropped, and it is handed back at the instantiated lifetime. -/
theorem not_relendJ_adj {δ : LSub} {P : LSub → List Life → List SRec → WProp}
    (hP : ¬ P (adjι.sub δ) [lifeN 2] [] (innerView 0 (lifeN 2))) :
    ¬ RelendJ δ [muEnt] P [lifeN 1] [] (innerView 0 (lifeN 1)) := by
  rintro ⟨ds, ρz, ρn, hc, ⟨hn, -⟩, hz, H⟩
  match ds, hn with
  | [], hn => exact hn.elim
  | _ :: _ :: _, hn =>
      obtain ⟨_, _, _, _, h⟩ := hn
      exact h.elim
  | [false], hn =>
      obtain ⟨a, r, hc', ha, ⟨rfl, -⟩⟩ := hn
      have ha' : a = PMap.empty := ha.1.1
      subst ha'
      obtain rfl := eq_empty_of_compS_empty hc'
      obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right ρz)
      exact lt_irrefl (lifeN 1) (hz (lifeN 1) rfl 0 (viewCell (lifeN 1)) (innerView_get _))
  | [true], hn =>
      obtain ⟨a, r, hc', ha, ⟨rfl, -⟩⟩ := hn
      obtain rfl := ResU.CompS.functional hc' (ResU.comp_empty_right a)
      obtain ⟨⟨b, u, χ, hχ, Q, hw, ls₀, -, hρn, -⟩, -⟩ := ha
      have hz0 : ρz = PMap.empty := by
        refine PMap.ext fun l => ?_
        rw [PMap.empty_get]
        cases e : ρz.get l with
        | none => rfl
        | some φ =>
            obtain ⟨φ', e', -⟩ := ResU.CompS.get_left hc e
            obtain ⟨rfl, -⟩ := ResU.single_get_eq_some e'
            have hg : ρn.get 0 = some (CellU.mutOf b u χ hχ Q hw) := by rw [hρn]; simp
            have := (ResU.CompS.get_right_of_ne_imm hc hg (by simp)).1
            rw [e] at this
            exact absurd this (by simp)
      subst hz0
      refine hP (H adjι adj_instAt [] (Ext.refl _ _) (fun _ hx _ => hx) (fun _ hx _ => ?_)
        (fun _ _ x hx => absurd hx List.not_mem_nil) (innerView 0 (lifeN 2)) _
        (vwSL_innerView _ (lifeN 2) []) (compS_empty_left _))
      exact absurd hx List.not_mem_nil

/-! ### The body at the view handed back at `2` -/

/-- **`adj_fails`'s run**: at a single `mut` cell at `2` with an empty witness, the body of
`∀'0 ⊏ ⊤. F (Mut '0 1)` at `α = 1` fails: the answer's cell, brought back to the start's
flattening by `↭`, is at `2`, and `Mut '0` at `1` asks `1 ⊑ 2`. -/
theorem adj_run_fails {h : ResU.InStratum (lifeN 2) (PMap.empty : WRes)}
    {Q : Val → SPropS BoCa.Loc Val (lifeN 2)} (hw : Q Val.unit ⟨PMap.empty, h⟩) :
    ¬ wpTS (ℍ := ℍ) [] (.app adjE (.val .unit))
      (fun ls'' => vC true (.mut (.var 0) .unit) ls'' (adjδ.extend 0 (lifeN 1)))
      (ResU.single 0 (CellU.mutOf (lifeN 2) Val.unit PMap.empty h Q hw)) := by
  intro hwp
  have hflat := flat_single_mut_empty (k := 0) (u := Val.unit) (hw := hw)
  have hval : ResU.Valid (ResU.single 0 (CellU.mutOf (lifeN 2) Val.unit PMap.empty h Q hw)) :=
    ⟨_, hflat⟩
  obtain ⟨ρ', ρp, -, -, π, v, -, -, -, ls', -, -, -, -, -, -, -, hπ, hU, -, -, -, -, -, hQ⟩ :=
    hwp PMap.empty _ [] ⟨(compS_empty_left _).1, _, compS_empty_left _, hval⟩
      (compS_empty_left _) (tw_single_mut_empty hw) (fun _ hx => absurd hx List.not_mem_nil)
      BoCa.BoLo.Alloc.leastFree 0
  obtain ⟨α, hα, ℓ, hsep⟩ := hQ
  obtain rfl : α = lifeN 1 := (Option.some.inj hα).symm
  obtain ⟨-, b, u, χ, hχ, Q', hw', -, hαb, hρ', -, -, -⟩ := pure_sep_iff.mp hsep
  have hg : ρ'.get ℓ = some (CellU.mutOf b u χ hχ Q' hw') := by rw [hρ']; simp
  have hf : π.FlatAt ℓ (CellU.mutOf b u χ hχ Q' hw') :=
    pvLocal π ρp ρ' hU.2.2 (ResU.CompS.comm hπ) ℓ _ hg (CellU.kind_mutOf _ _ _ _ _ _)
  obtain ⟨v₀, χ₀, h₀, hw₀, σ₀, hσ₀, hg₀⟩ := (hU.1.2 ℓ b Q').mpr ⟨u, χ, hχ, hw', hf⟩
  rw [ResU.Flat.functional hσ₀ hflat] at hg₀
  obtain ⟨-, he⟩ := ResU.single_get_eq_some hg₀
  have hb : b = lifeN 2 := CellU.mutOf_at he
  rw [hb] at hαb
  exact absurd hαb (by decide)

/-- `adjC` has no free lifetime variable: every reading gives it one relation. -/
theorem adjC_cTyEq (δ δ' : LSub) : CTyEq adjC δ adjC δ' :=
  CTyEq.of_agree adjC fun y hy => by
    simp [CFree, VFree, Lifetime.Life.mentions] at hy

/-- **`Λ. return ℓ₀` is no W `∀`-computation over the view handed back at `2`.** -/
theorem adj_not_cRLJ (δ : LSub) :
    ¬ cRLJ (ℍ := ℍ) .binder0 [muEnt] δ adjC [lifeN 2] [] adjE (innerView 0 (lifeN 2)) := by
  intro h
  have hall := (h [] [muEnt] [lifeN 2] rfl rfl (fun e he hx => absurd
    (List.mem_map_of_mem (f := LEnt.x) he) hx)).1 (lifeN 1)
  have hlt : LtLife (extS δ [muEnt] [lifeN 2]) .top (lifeN 1) :=
    ⟨Lifetime.SLife.top, rfl, show OrderDual.toDual (1 : ℕ) < OrderDual.toDual 0 from by decide⟩
  have hg := hall PMap.empty _ ⟨rfl, hlt⟩ (ResU.comp_empty_right _) (tab_innerView _)
    (pvl_innerView _ _ _)
  refine adj_run_fails (unitQ_holds (lifeN 2)) (wpTS_mono (fun ls'' v ρ' hv => ?_) _ hg)
  have h₁ := hv.1
  rwa [vC_congr _ (δ₂ := adjδ.extend 0 (lifeN 1)) (fun y hy => by
    simp only [VFree, Lifetime.Life.mentions, beq_iff_eq] at hy
    rcases hy with rfl | hy
    · rfl
    · exact hy.elim)] at h₁

/-! ### Core admits the closure, W does not -/

/-- `adj_holds` at every list: the clause holds at the cell adjacent to `⊤`. -/
theorem adj_holds_ls (ls : List SRec) :
    cC (ℍ := ℍ) adjC ls adjδ adjE (innerView 0 (lifeN 1)) := by
  intro α ρ₁ ρ₂ hp hc
  obtain ⟨rfl, β, hβ, hlt⟩ := hp
  obtain rfl : β = Lifetime.SLife.top := Option.some.inj hβ.symm
  have hρ₂ : ρ₂ = innerView 0 (lifeN 1) := ResU.CompS.functional hc (ResU.comp_empty_right _)
  subst hρ₂
  refine wpTS_lolli ls (.val (Val.loc 0)) Val.unit _ _ ?_
  rw [adj_subst]
  refine wpTS_val ls (Val.loc 0) _ _ ?_
  exact ⟨α, rfl, 0, pure_sep_mk rfl (ptoMutS_innerView_le (le_one_of_lt_top hlt) ls _)⟩

/-- **Core's `U` clause admits the closure** over the view at `1`, at the stack's reading: its body
is Core's `∀`, which holds by adjacency. -/
theorem adj_core_U :
    vC true (.thunk adjC) [] (extS adjδ [muEnt] [lifeN 1]) (Val.lam (.val (Val.loc 0)))
      (innerView 0 (lifeN 1)) := by
  intro ls' _
  rw [forceE_of_not_ret rfl, cC_tyEq (adjC_cTyEq _ adjδ)]
  exact adj_holds_ls ls'

/-- **W's `U` clause does not**: at the instantiation that opens the cut between `⊤` and the view,
the body meets the view handed back at `2`. -/
theorem adj_not_wU :
    ¬ vRLJ (ℍ := ℍ) .binder0 [muEnt] adjδ (.thunk adjC) [lifeN 1] []
      (Val.lam (.val (Val.loc 0))) (innerView 0 (lifeN 1)) := by
  intro h
  rw [vRLJ_thunk0] at h
  have hR := h (tab_innerView _) (pvl_innerView _ _ _)
  refine not_relendJ_adj (fun hP => ?_) hR
  rw [forceE_of_not_ret rfl] at hP
  exact adj_not_cRLJ _ hP

end ProbeD1

end

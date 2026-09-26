import FrameTheorems.EveryRun
import Optics.Shape

/-!
# FrameTheorems — the frame of a semantically typed callback

A callback `g` at `∀'x ⊏ @b. F('x) ⊸ ['x] T` (`cbTy`), applied to a borrow `v` of `F('x)` at a
lifetime `α ⊏ @b`, runs as `g () v`.  Its `wpTS` at the callback's resource `ρg` composed with
the borrow's `ρv` is built from the relation's clauses alone (`call_wp`), so `Footprint` applies:
on the run the relation exhibits, and on every run that does not allocate, an existing location
changes only where `⦇ρg ● ρv⦈` holds it exclusively.

* `closed_vP`: a closed well-typed value is in the relation at `∅`, at every record list.
* `call_frame`: the footprint of `g () v` for a callback in the relation.
* `imm_call_keeps`: an `Imm` callback leaves the lent cell as it was.
* `mut_call_frame`: a closed well-typed `Mut` callback at a payload type that holds no resource
  (`A.Persistent`) leaves every existing location other than the lent cell as it was, and the
  lent cell allocated.  This is `ElemFrame`'s heap clause, at the heaps of typed worlds.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.FrameTheorems
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Closed values -/

/-- `Ext [] ls ∅`: the empty resource has no record to keep and no borrow cell. -/
theorem ext_empty (ls ls' : List SRec) : Ext ls ls' (PMap.empty : WRes) :=
  ⟨fun _ _ ⟨m, _, e, _⟩ => (by rw [PMap.empty_get] at e; cases e),
    fun _ ⟨m, _, e, _⟩ => (by rw [PMap.empty_get] at e; cases e)⟩

/-- A resource that is a factor of a world lowering to the empty heap is empty. -/
theorem eq_empty_of_lower_none {X Y Z : WRes} (h : ResU.CompS X Y Z)
    (hμ : ResU.Lower Z (fun _ => none)) : X = PMap.empty := by
  refine PMap.ext fun l => ?_
  rw [PMap.empty_get]
  cases e : X.get l with
  | none => rfl
  | some ψ =>
      obtain ⟨χ, eχ, -, -, -⟩ := compS_get_left' h e
      have := lower_get hμ eχ
      simp at this

/-- **A closed well-typed value is in the relation at `∅`**, at every record list. -/
theorem closed_vP {Δ : LifeCtx} {f : Val} {A : VTy} (h : SemV Δ [] (.val f) A) {δ : LSub}
    (hδ : Δ.Models δ) (ls : List SRec) : vP A ls δ f PMap.empty := by
  have hw := h δ [] [] PMap.empty hδ (gDenC_nil _ _)
  have he : substAll [] (Expr.val f) = .val f := Adequacy.psub_nil 0 _
  rw [he] at hw
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', -, h₂, -, h₅, h₆, h₇, h₈, -, -, -, -, -,
    -, hls, hC⟩ := hw PMap.empty PMap.empty [] Fig16.LogRel.hash_empty
      (ResU.comp_empty_right _) TW.empty htg
  obtain ⟨hμμ, rfl⟩ := steps_from_val (v := f) h₈
  rw [hμμ, ResU.Lower.functional h₅ Fig16.BoLo.lower_empty] at h₇
  obtain rfl : ρ' = fρ' := ResU.eq_of_comp_empty_left h₂
  obtain rfl := eq_empty_of_lower_none h₆ h₇
  have hls' : ls' = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
    simpa using (hls x).mp hx
  subst hls'
  exact vC_local true A (ext_empty [] ls) hC

/-! ### Application in the relation -/

/-- `f v` for `f` at `A ⊸ B` and `v` at `A`. -/
theorem app_wp {A B : VTy} {ls : List SRec} {δ : LSub} {f v : Val} {ρf ρv ρ : WRes}
    (hf : vP (.lolli A B) ls δ f ρf) (hv : vP A ls δ v ρv) (hc : ResU.CompS ρf ρv ρ) :
    wpTS ls (.app (.val f) (.val v)) (fun ls' => vP B ls' δ) ρ :=
  hf ls (Ext.refl _ _) v ρv ρ hv hc

/-- `f a b` for `f` at `A ⊸ B ⊸ C` in the empty resource. -/
theorem app2_wp {A B C : VTy} {ls : List SRec} {δ : LSub} {f a b : Val} {ρa ρb ρ : WRes}
    (hf : vP (.lolli A (.lolli B C)) ls δ f PMap.empty) (ha : vP A ls δ a ρa)
    (hb : vP B ls δ b ρb) (hc : ResU.CompS ρa ρb ρ) :
    wpTS ls (BoCa.Programs.app2 (.val f) (.val a) (.val b)) (fun ls' => vP C ls' δ) ρ := by
  refine wpTS_bind_frame (.appL .hole b) (.app (.val f) (.val a)) ls
    (fun ls' => vP (.lolli B C) ls' δ) (fun ls' => vP B ls' δ b) (fun ls' => vP C ls' δ)
    (fun ls' hls ρ h => vP_same hls h) ?_ ρ ⟨ρa, ρb, hc, ?_, hb⟩
  · rintro ls' - h σ ⟨σ₁, σ₂, hcσ, hh, hb'⟩
    exact app_wp hh hb' hcσ
  · exact app_wp hf ha (ResU.comp_empty_left _)

/-- **The call of a callback.**  `g () v`, for `g` at `∀'x ⊏ @b. F('x) ⊸ ['x] T` and `v` at
`F('x)` with `'x ↦ α ⊏ @b`, is in the relation at `['x] T`. -/
theorem call_wp {F : Lifetime.Life → VTy} {x : LifeVar} {b : Lifetime.Life} {T : VTy}
    {ls : List SRec} {δ : LSub} {α : Life} {g v : Val} {ρg ρv ρ : WRes}
    (hg : vP (Optics.cbTy F x b T) ls δ g ρg) (hlt : LtLife δ b α)
    (hv : vP (F (.var x)) ls (δ.extend x α) v ρv) (hc : ResU.CompS ρg ρv ρ) :
    wpTS ls (BoCa.Programs.app2 (.val g) unit' (.val v))
      (fun ls' => vP (.box (.var x) T) ls' (δ.extend x α)) ρ := by
  have h₁ : wpTS ls (.app (.val g) (.val .unit))
      (fun ls' => vP (.lolli (F (.var x)) (.box (.var x) T)) ls' (δ.extend x α)) ρg :=
    hg ls (Ext.refl _ _) α PMap.empty ρg ⟨rfl, hlt⟩ (ResU.comp_empty_right ρg)
  refine wpTS_bind_frame (.appL .hole v) (.app (.val g) (.val .unit)) ls
    (fun ls' => vP (.lolli (F (.var x)) (.box (.var x) T)) ls' (δ.extend x α))
    (fun ls' => vP (F (.var x)) ls' (δ.extend x α) v)
    (fun ls' => vP (.box (.var x) T) ls' (δ.extend x α))
    (fun ls' hls ρ h => vP_same hls h) ?_ ρ ⟨ρg, ρv, hc, h₁, hv⟩
  rintro ls' - h σ ⟨σ₁, σ₂, hcσ, hh, hv'⟩
  exact app_wp hh hv' hcσ

/-! ### The frame of a call -/

/-- The configuration a computation at `ρ` runs in: a frame `ρf` completing it to a tagged
typed world `ρf ● ρ`, and that world's heap. -/
def World (ls : List SRec) (ρ ρf : WRes) (μ : Heap) : Prop :=
  ResU.Hash ρf ρ ∧ ∃ (fρ : WRes) (ps : List FrameRec), ResU.CompS ρf ρ fρ ∧
    TW fρ ps (rsOf ls) ∧ Tagged fρ ps ls ∧ ResU.Lower fρ μ

/-- The footprint on the exhibited run and on every run that does not allocate. -/
theorem world_footprint {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp}
    {ρ ρf : WRes} {μ : Heap} (hw : wpTS ls e Q ρ) (hW : World ls ρ ρf μ) :
    (∃ (μ' : Heap) (v : Val), Steps μ e μ' (.val v) ∧ (∃ ls' ρ', Q ls' v ρ') ∧
      Footprint ρf ρ μ μ') ∧
    ∀ {μR : Heap} {w : Val}, StepsNA μ e μR (.val w) →
      (∃ ls' ρ', Q ls' w ρ') ∧ Footprint ρf ρ μ μR := by
  obtain ⟨hf, fρ, ps, hc, hT, htg, hμ⟩ := hW
  exact ⟨wpTS_footprint hw hf hc hT htg hμ,
    fun hR => wpTS_footprint_every hw hf hc hT htg hμ hR⟩

/-- **The frame of a semantically typed callback.**  From any tagged typed world holding the
callback's resource `ρg` and the lent borrow's `ρv`, the call `g () v` has a run to a value in
`['x] T` with `Footprint ρf (ρg ● ρv)`, and every run of the call that does not allocate is
that run. -/
theorem call_frame {F : Lifetime.Life → VTy} {x : LifeVar} {b : Lifetime.Life} {T : VTy}
    {ls : List SRec} {δ : LSub} {α : Life} {g v : Val} {ρg ρv ρ ρf : WRes} {μ : Heap}
    (hg : vP (Optics.cbTy F x b T) ls δ g ρg) (hlt : LtLife δ b α)
    (hv : vP (F (.var x)) ls (δ.extend x α) v ρv) (hc : ResU.CompS ρg ρv ρ)
    (hW : World ls ρ ρf μ) :
    (∃ (μ' : Heap) (w : Val), Steps μ (BoCa.Programs.app2 (.val g) unit' (.val v)) μ' (.val w) ∧
      (∃ ls' ρ', vP (.box (.var x) T) ls' (δ.extend x α) w ρ') ∧ Footprint ρf ρ μ μ') ∧
    ∀ {μR : Heap} {w : Val}, StepsNA μ (BoCa.Programs.app2 (.val g) unit' (.val v)) μR (.val w) →
      (∃ ls' ρ', vP (.box (.var x) T) ls' (δ.extend x α) w ρ') ∧ Footprint ρf ρ μ μR :=
  world_footprint (call_wp hg hlt hv hc) hW

/-! ### `Imm` callbacks keep the lent cell -/

/-- A borrow at `Imm 'x A` is one `imm` cell at its location. -/
theorem imm_cell {A : VTy} {ls : List SRec} {δ : LSub} {x : LifeVar} {a : Loc} {ρv : WRes}
    (hv : vP (.imm (.var x) A) ls δ (.loc a) ρv) :
    ∃ ψ : CellU Loc Val, ρv.get a = some ψ ∧ ψ.kind = Kind.imm := by
  obtain ⟨α, -, ℓ, hsep⟩ := hv
  obtain ⟨⟨hℓ, -⟩, hpto⟩ := pure_sep_iff.mp hsep
  obtain ⟨s, u, σ, hs, ls₀, rfl, -, -, -⟩ := hpto
  obtain rfl : a = ℓ := by simpa using hℓ
  exact ⟨_, ResU.single_get_self _ _, by simp⟩

/-- **An `Imm` callback keeps the lent cell.**  On the exhibited run and on every run that does
not allocate, the cell lent immutably holds what it held. -/
theorem imm_call_keeps {A : VTy} {x : LifeVar} {b : Lifetime.Life} {T : VTy}
    {ls : List SRec} {δ : LSub} {α : Life} {g : Val} {a : Loc} {ρg ρv ρ ρf : WRes} {μ : Heap}
    (hg : vP (Optics.cbTy (fun c => .imm c A) x b T) ls δ g ρg) (hlt : LtLife δ b α)
    (hv : vP (.imm (.var x) A) ls (δ.extend x α) (.loc a) ρv) (hc : ResU.CompS ρg ρv ρ)
    (hW : World ls ρ ρf μ) :
    (∃ (μ' : Heap) (w : Val),
      Steps μ (BoCa.Programs.app2 (.val g) unit' (.val (.loc a))) μ' (.val w) ∧ μ' a = μ a) ∧
    ∀ {μR : Heap} {w : Val},
      StepsNA μ (BoCa.Programs.app2 (.val g) unit' (.val (.loc a))) μR (.val w) → μR a = μ a := by
  obtain ⟨ψ, eψ, kψ⟩ := imm_cell hv
  obtain ⟨χ, eχ, kχ, -, -⟩ := compS_get_right' hc eψ
  have himm : ImmOnly ρ a := immOnly_of_get eχ (kχ.trans kψ)
  have hdom : μ a ≠ none := by
    obtain ⟨-, fρ, ps, hcW, -, -, hμ⟩ := hW
    obtain ⟨χ', eχ', -, -, -⟩ := compS_get_right' hcW eχ
    rw [lower_get hμ eχ']
    simp
  obtain ⟨⟨μ', w, hrun, -, -, hfoot, -⟩, hevery⟩ :=
    call_frame (F := fun c => .imm c A) hg hlt hv hc hW
  exact ⟨⟨μ', w, hrun, hfoot a hdom himm⟩, fun hR => (hevery hR).2.2.1 a hdom himm⟩

/-! ### `Mut` callbacks at a payload that holds no resource -/

/-- `⦇ℓ ↦ mut(b, u, ∅, Q)⦈ = ℓ ↦ mut(b, u, ∅, Q)`. -/
theorem flat_single_mut_empty (l : Loc) (b : Life) (u : Val)
    (h : ResU.InStratum b (PMap.empty : WRes)) (Q : Val → SPropS Loc Val b)
    (hw : Q u ⟨PMap.empty, h⟩) :
    ResU.Flat (ResU.single l (CellU.mutOf b u PMap.empty h Q hw))
      (ResU.single l (CellU.mutOf b u PMap.empty h Q hw)) := by
  have hk : (CellU.mutOf b u (PMap.empty : WRes) h Q hw).kind = Kind.mut := by simp
  have hb : BigComp CellU.CompatS CellU.CompS [(PMap.empty : WRes)] PMap.empty :=
    .cons .nil (ResU.comp_empty_right _)
  have hbR : BigComp CellU.CompatR CellU.CompR [(PMap.empty : WRes)] PMap.empty :=
    .cons .nil (ResU.comp_empty_right _)
  refine ⟨ResU.single l (CellU.mutOf b u PMap.empty h Q hw), PMap.empty, ?_, ?_,
    ResU.comp_empty_right _⟩
  · refine ExW.mk (w := [(l, PMap.empty)]) (b := PMap.empty)
      (nm := ResU.single l (CellU.mutOf b u PMap.empty h Q hw))
      (ResU.sites_single_self hk)
      (.cons _ (ResU.single_get_self _ _) hk (by simpa using Fig16.BoLo.exW_empty) .nil)
      hb ?_ (ResU.comp_empty_right _)
    rw [ResU.restrict_single_other (k := Kind.own) (by simp),
      ResU.restrict_single_self (k := Kind.mut) hk]
    exact ResU.comp_empty_left _
  · refine AgW.mk (wm := [(l, PMap.empty)]) (wi := []) (a := PMap.empty) (bm := PMap.empty)
      (bi := PMap.empty) (ResU.sites_single_self hk) (ResU.sites_single_other (by simp))
      (.cons _ (ResU.single_get_self _ _) hk (by simpa using Fig16.BoLo.agW_empty) .nil)
      .nil hbR .nil ?_ (ResU.comp_empty_right _)
    rw [ResU.restrict_single_other (k := Kind.imm) (by simp)]
    exact ResU.comp_empty_right _

/-- A borrow at `Mut 'x A`, `A` persistent, is one `mut` cell with an empty witness, and that
cell is its whole flattening. -/
theorem mut_cell_persistent {A : VTy} (hA : A.Persistent) {ls : List SRec} {δ : LSub}
    {x : LifeVar} {a : Loc} {ρv : WRes} (hv : vP (.mut (.var x) A) ls δ (.loc a) ρv) :
    ResU.Flat ρv ρv ∧ ∃ ψ : CellU Loc Val, ρv = ResU.single a ψ ∧ ψ.kind = Kind.mut := by
  obtain ⟨α, -, ℓ, hsep⟩ := hv
  obtain ⟨hℓ, hpto⟩ := pure_sep_iff.mp hsep
  obtain ⟨b, u, σ, hσ, Q, hw, ls₀, -, rfl, hQ, -, -⟩ := hpto
  obtain rfl : a = ℓ := by simpa using hℓ
  have hP : vP A ls₀ δ u σ := by
    have : ofS Q u σ := ⟨hσ, hw⟩
    rw [hQ] at this
    exact this
  obtain rfl := vP_empty_of_persistent hA hP
  exact ⟨flat_single_mut_empty a b u hσ Q hw, _, rfl, by simp⟩

/-- A heap relation: every existing location other than `a` keeps its value, and `a` stays
allocated.  `ElemFrame`'s heap clauses. -/
def KeepsAllBut (a : Loc) (μ μ' : Heap) : Prop :=
  (μ' a ≠ none) ∧ ∀ k, k ≠ a → μ k ≠ none → μ' k = μ k

/-- **The frame of a closed well-typed `Mut` callback at a payload that holds no resource.**
From any tagged typed world in which the borrow `a` is lent at `Mut 'x A`, `A` persistent,
the call `g () a` of a closed well-typed callback `g : ∀'x ⊏ @b. Mut 'x A ⊸ ['x] T` has a run
to a value that changes no existing location other than `a` and leaves `a` allocated; every run
that does not allocate is that run. -/
theorem mut_call_frame {Δ : LifeCtx} {A : VTy} (hA : A.Persistent) {x : LifeVar}
    {b : Lifetime.Life} {T : VTy} {g : Val}
    (hg : CDerives Δ [] (.val g) (.val (Optics.cbTy (fun c => .mut c A) x b T)))
    {δ : LSub} (hδ : Δ.Models δ) {ls : List SRec} {α : Life} (hlt : LtLife δ b α)
    {a : Loc} {ρv ρf : WRes} {μ : Heap}
    (hv : vP (.mut (.var x) A) ls (δ.extend x α) (.loc a) ρv) (hW : World ls ρv ρf μ) :
    (∃ (μ' : Heap) (w : Val),
      Steps μ (BoCa.Programs.app2 (.val g) unit' (.val (.loc a))) μ' (.val w) ∧
        KeepsAllBut a μ μ') ∧
    ∀ {μR : Heap} {w : Val},
      StepsNA μ (BoCa.Programs.app2 (.val g) unit' (.val (.loc a))) μR (.val w) →
        KeepsAllBut a μ μR := by
  have hg' := closed_vP (fundamentalC hg) hδ ls
  obtain ⟨hflat, ψ, rfl, hk⟩ := mut_cell_persistent hA hv
  have hkeep : ∀ {μ' : Heap}, Footprint ρf (ResU.single a ψ) μ μ' → KeepsAllBut a μ μ' := by
    rintro μ' ⟨-, hfoot, hmut⟩
    refine ⟨hmut a ψ ⟨_, hflat, ResU.single_get_self _ _⟩ hk, fun k hk' hdom => hfoot k hdom ?_⟩
    refine immOnly_of_not_mem fun χ ⟨σ, hσ, eσ⟩ => ?_
    rw [ResU.Flat.functional hσ hflat, ResU.single_get_ne _ hk'] at eσ
    cases eσ
  obtain ⟨⟨μ', w, hrun, -, hfp⟩, hevery⟩ := call_frame (F := fun c => .mut c A) hg' hlt hv
    (ResU.comp_empty_left _) hW
  exact ⟨⟨μ', w, hrun, hkeep hfp⟩, fun hR => hkeep (hevery hR).2⟩

/-! ### The world hypotheses are met -/

/-- The invariant `𝒱⟦1⟧` at a stratum. -/
def unitInv (b : Life) : Val → SPropS Loc Val b := fun u r => r.val = PMap.empty ∧ u = .unit

/-- The cell `a ↦ mut(b, (), ∅, 𝒱⟦1⟧)`. -/
def unitMutCell (b : Life) : CellU Loc Val :=
  CellU.mutOf b .unit PMap.empty (ResU.inStratum_empty b) (unitInv b) ⟨rfl, rfl⟩

/-- **The hypotheses of `mut_call_frame` are met.**  The one-cell world `a ↦ mut(α, (), ∅, 𝒱⟦1⟧)`,
reached from `∅` by `alloc` and `mutFold`, lends `a` at `Mut 'x 1` with `'x ↦ α`, with the empty
frame. -/
theorem lent_unit_world (δ : LSub) (x : LifeVar) (α : Life) (a : Loc) :
    vP (.mut (.var x) .unit) [] (δ.extend x α) (.loc a) (ResU.single a (unitMutCell α)) ∧
      World [] (ResU.single a (unitMutCell α)) PMap.empty
        (BoLo.Heap.upd (fun _ => none) a .unit) := by
  have hflat := flat_single_mut_empty a α .unit (ResU.inStratum_empty α) (unitInv α) ⟨rfl, rfl⟩
  have hvalid : ResU.Valid (ResU.single a (unitMutCell α)) := ⟨_, hflat⟩
  refine ⟨⟨α, by simp only [Lifetime.Life.interp, find?_extend_self]; rfl, a, pure_sep_iff.mpr ⟨rfl, ?_⟩⟩,
    ⟨⟨(ResU.comp_empty_left (C := CellU.CompS) _).1, _, ResU.comp_empty_left _, hvalid⟩, _, [],
      ResU.comp_empty_left _, ?_, fun x hx => absurd hx (by simp), ?_⟩⟩
  · refine ⟨α, .unit, PMap.empty, ResU.inStratum_empty α, unitInv α, ⟨rfl, rfl⟩, [], le_rfl, rfl,
      ?_, fun x => by simp, fun _ _ σ' h => ?_⟩
    · funext u σ
      apply propext
      show (∃ _ : ResU.InStratum α σ, σ = PMap.empty ∧ u = .unit) ↔ (σ = PMap.empty ∧ u = .unit)
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨h.1 ▸ ResU.inStratum_empty α, h⟩⟩
    · obtain ⟨rfl, -⟩ := h
      exact ResU.inStratum_empty α
  · have h₀ : TW (ResU.single a (CellU.ownOf Val.unit)) [] [] :=
      .alloc .empty Fig16.BoLo.lower_empty rfl (ResU.comp_empty_left _)
        (ResU.valid_single_own a Val.unit)
    exact .mutFold (ρ := PMap.empty) (hw := ⟨rfl, rfl⟩) h₀ (ResU.comp_empty_right _)
      (ResU.comp_empty_right _) (ResU.comp_empty_right _) hvalid
  · refine ⟨_, hflat, fun k => ?_⟩
    by_cases hk : k = a
    · subst hk; simp [BoLo.Heap.upd]; rfl
    · simp [BoLo.Heap.upd, hk, ResU.single_get_ne _ hk]

end BoCa.Fig16.LogRel.Core.FrameTheorems

end

import TwoRun.Refute

/-!
# TwoRun — the read footprint does not follow from `wpTS`

A head step *touches* the location it loads, stores to or frees (`Touch`).  `RunIn P` is a run
all of whose steps touch only locations in `P`.  The read footprint of a computation at `ρ` is
the statement that the run the relation exhibits from `ρf ● ρ` touches only locations `⦇ρ⦈`
holds or that the initial heap lacks (`ReadFootprint`).  `Footprint` bounds what a run
*changes*; this bounds what it *inspects*.

`ReadFootprint` does not hold for every `wpTS` term (`not_readFootprint`).  `peekE k` allocates
a cell, loads `k`, and returns the new cell.  It satisfies `wpTS` at `∅`: in a world whose heap
lacks `k`, the exhibited run allocates `k` itself, and in a world whose heap holds `k`, it
allocates elsewhere and loads the frame's cell.  In the world whose frame owns `k`, every run to
a value loads `k`, which `⦇∅⦈` does not hold.

Two features of `wpTS` meet here:

* a load leaves no trace in the post-world, so `↭` constrains what a run changes and never what
  it reads;
* allocation is angelic: `wpTS` exhibits a run, and its `alloc↦` step may pick a location that
  depends on the frame.

`peekE` mentions a location literal and is not typed by `CDerives`.  The statement for typed
programs is `ReadFootprintTyped`.  I have not derived it and have not verified that any
obstruction to it is real.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.TwoRun
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx)
open BoCa.Fig16.LogRel.Core.FrameTheorems (allocRedex head_det)

/-! ### Touching a location -/

/-- The redex `a` touches `ℓ`: it loads, stores to or frees `ℓ`. -/
inductive Touch : Expr → Loc → Prop where
  | load (ℓ : Loc) : Touch (.app (.val (.prim .load)) (.val (.loc ℓ))) ℓ
  | free (ℓ : Loc) : Touch (.app (.val (.prim .free)) (.val (.loc ℓ))) ℓ
  | store (ℓ : Loc) (v : Val) :
      Touch (.app (.app (.val (.prim .store)) (.val (.loc ℓ))) (.val v)) ℓ

/-- A run each of whose steps touches only locations in `P`. -/
inductive RunIn (P : Loc → Prop) : Heap → Expr → Heap → Expr → Prop where
  | refl (μ : Heap) (e : Expr) : RunIn P μ e μ e
  | more {μ μ₁ μ' : Heap} {e e₁ e' : Expr} (K : Kont) (a a' : Expr) (he : e = K.plug a)
      (he₁ : e₁ = K.plug a') (hh : Head μ a μ₁ a') (ht : ∀ ℓ, Touch a ℓ → P ℓ)
      (t : RunIn P μ₁ e₁ μ' e') : RunIn P μ e μ' e'

theorem RunIn.toSteps {P : Loc → Prop} {μ μ' : Heap} {e e' : Expr} (h : RunIn P μ e μ' e') :
    Steps μ e μ' e' := by
  induction h with
  | refl => exact .refl _ _
  | more K a a' he he₁ hh _ _ ih => exact .more ⟨K, a, a', he, he₁, hh⟩ ih

/-- The locations a computation at `ρ` may touch from the heap `μ`: those `⦇ρ⦈` holds, and
those `μ` lacks. -/
def Own (ρ : WRes) (μ : Heap) (ℓ : Loc) : Prop := (∃ ψ, ρ.FlatAt ℓ ψ) ∨ μ ℓ = none

/-- **The read footprint**, for every `wpTS` term: from every tagged typed world `ρf ● ρ`, some
run to a value whose result satisfies the post-condition touches only locations `⦇ρ⦈` holds or
that the initial heap lacks. -/
def ReadFootprint : Prop :=
  ∀ (ls : List SRec) (e : Expr) (Q : List SRec → Val → WProp) (ρ ρf fρ : WRes)
    (ps : List FrameRec) (μ : Heap),
    wpTS ls e Q ρ → ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → TW fρ ps (rsOf ls) →
    Tagged fρ ps ls → ResU.Lower fρ μ →
    ∃ (μ' : Heap) (v : Val), RunIn (Own ρ μ) μ e μ' (.val v) ∧ ∃ ls' ρ', Q ls' v ρ'

/-- **The read footprint of a well-typed computation**: `ReadFootprint` at the instances
`fundamentalC` gives, a computation at `F A` typed by `CDerives` under the substitution of a
context's values.  Not derived. -/
def ReadFootprintTyped : Prop :=
  ∀ (Δ : LifeCtx) (Γ : Ctx VTy) (e : Expr) (A : VTy), CDerives Δ Γ e (.comp (.ret A)) →
    ∀ (δ : LSub) (γ : List Val) (ls : List SRec) (ρ ρf fρ : WRes) (ps : List FrameRec)
      (μ : Heap), Δ.Models δ → gDenC ls δ Γ γ ρ → ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ →
    TW fρ ps (rsOf ls) → Tagged fρ ps ls → ResU.Lower fρ μ →
    ∃ (μ' : Heap) (v : Val), RunIn (Own ρ μ) μ (substAll γ e) μ' (.val v) ∧
      ∃ ls' ρ', vP A ls' δ v ρ'

/-! ### `wpTS` of an allocation whose location depends on the heap -/

/-- A term that runs from every heap of a world completing `ρ` to that heap with one new cell
`l ↦ v`, returning `l`, satisfies `wpTS` at every post-condition that holds of `ρ` with the cell
added.  The location may depend on the heap. -/
theorem wpTS_alloc_at {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp} {ρ : WRes}
    {v : Val}
    (hrun : ∀ fρ μ, ResU.Lower fρ μ →
      ∃ l, μ l = none ∧ Steps μ e (BoLo.Heap.upd μ l v) (.val (.loc l)))
    (hQ : ∀ l x, ResU.CompS ρ (ResU.single l (CellU.ownOf v)) x → Q ls (.loc l) x) :
    wpTS ls e Q ρ := by
  intro ρf σ ps hf hσ hT htg
  obtain ⟨μ, hμ⟩ := lower_of_hash hf hσ
  obtain ⟨τ, hτ, hval⟩ := id hμ
  obtain ⟨l, hμl, hsteps⟩ := hrun σ μ hμ
  have hl : τ.get l = none := (lower_eq_none_iff hval).mp hμl
  have hρl : ρ.get l = none :=
    ((ResU.Comp.eq_none_iff hσ l).mp (get_eq_none_of_flat hτ hl)).2
  obtain ⟨x, hx⟩ := (ResU.compS_defined_iff ρ (ResU.single l (CellU.ownOf v))).mpr
    (compatS_single_of_get_none hρl)
  obtain ⟨σ', hσ'x, hfx, hlow'⟩ := hash_compS_own hσ hμ hμl hx
  obtain ⟨y, hy, hyσ'⟩ := (ResU.CompS.assoc ρf ρ (ResU.single l (CellU.ownOf v)) σ').mp
    ⟨x, hx, hσ'x⟩
  cases ResU.CompS.functional hy hσ
  have hT' : TW σ' ps (rsOf ls) := TW.alloc hT hμ hμl hyσ' (hash_valid_comp hfx hσ'x)
  exact ⟨x, PMap.empty, σ', σ', x, .loc l, μ, BoCa.BoLo.Heap.upd μ l v, ps, ls,
    ResU.hash_symm hfx, hσ'x,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hfx hσ'x)),
    hμ, ResU.comp_empty_right σ', hlow', hsteps, ResU.comp_empty_right x,
    updV_compS_own hx (hash_valid hf).2 (hash_valid hfx).2,
    noOwn_empty, hT', tagged_of_ag (fun a ha => alloc_ag hyσ' ha) htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, hQ l x hx⟩

/-! ### A computation that reads its frame -/

/-- `let x = alloc () in let _ = load k in x`. -/
def peekE (k : Loc) : Expr := elet (allocE unit') (elet (loadE (.val (.loc k))) (.var 1))

theorem peekE_runs {μ : Heap} {k l : Loc} (hl : μ l = none) {w : Val}
    (hk : BoLo.Heap.upd μ l .unit k = some w) :
    Steps μ (peekE k) (BoLo.Heap.upd μ l .unit) (.val (.loc l)) :=
  steps_elet (steps_head (.alloc _ .unit l hl))
    (steps_elet (steps_head (.load _ k w hk)) (.refl _ _))

/-- `peekE k` satisfies `wpTS` at `∅`: where the heap lacks `k` the run allocates `k`, and where
it holds `k` the run allocates elsewhere and loads it. -/
theorem peekE_wp (k : Loc) (ls : List SRec) :
    wpTS ls (peekE k) (fun _ v _ => ∃ l, v = .loc l) PMap.empty := by
  refine wpTS_alloc_at (v := .unit) (fun fρ μ hμ => ?_) (fun l _ _ => ⟨l, rfl⟩)
  by_cases hk : μ k = none
  · exact ⟨k, hk, peekE_runs hk (w := .unit) (BoLo.Heap.upd_same _ _ _)⟩
  · obtain ⟨d, hd⟩ := lower_finite hμ
    obtain ⟨l, hl⟩ := loc_infinite d
    have hμl : μ l = none := by by_contra h; exact hl (hd l h)
    have hne : k ≠ l := fun e => hk (e ▸ hμl)
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hk
    exact ⟨l, hμl, peekE_runs hμl (w := w) (by rw [BoLo.Heap.upd_other hne, hw])⟩

/-! ### Every run touches the frame -/

/-- A run to a value from `K[a]`, where `a` is a redex, first takes a head step of `a`. -/
theorem runIn_head_inv {P : Loc → Prop} {μ μ' : Heap} {K : Kont} {a e' : Expr}
    {μ₀ μ₀' : Heap} {a₀' : Expr} (h₀ : Head μ₀ a μ₀' a₀') (h : RunIn P μ (K.plug a) μ' e')
    (hv : IsVal e') :
    ∃ μ₁ a₁, Head μ a μ₁ a₁ ∧ (∀ ℓ, Touch a ℓ → P ℓ) ∧ RunIn P μ₁ (K.plug a₁) μ' e' := by
  cases h with
  | refl => exact absurd (K.isVal_of_plug hv) h₀.not_isVal
  | more K' b b' he he₁ hh ht t =>
      obtain ⟨K'', hb, rfl⟩ := Fig16.LogRel.Core.plug_decomp hh K K' h₀.not_isVal he
      obtain rfl : K'' = .hole := Fig16.LogRel.Core.head_plug h₀ K'' hh.not_isVal hb
      simp only [Kont.plug] at hb
      subst hb
      subst he₁
      rw [BoLo.Kont.plug_comp] at t
      exact ⟨_, _, hh, ht, t⟩

/-- The world whose frame owns `k`, holding `()`, and whose computation's resource is `∅`. -/
theorem frame_world (k : Loc) :
    ResU.Hash (ResU.single k (CellU.ownOf Val.unit)) (PMap.empty : WRes) ∧
      ResU.CompS (ResU.single k (CellU.ownOf Val.unit)) PMap.empty
        (ResU.single k (CellU.ownOf Val.unit)) ∧
      TW (ResU.single k (CellU.ownOf Val.unit)) [] (rsOf []) ∧
      Tagged (ResU.single k (CellU.ownOf Val.unit)) [] [] ∧
      ResU.Lower (ResU.single k (CellU.ownOf Val.unit)) (BoLo.Heap.upd (fun _ => none) k Val.unit) := by
  have hv := ResU.valid_single_own k Val.unit
  have hc : ResU.CompS PMap.empty (ResU.single k (CellU.ownOf Val.unit))
      (ResU.single k (CellU.ownOf Val.unit)) := ResU.comp_empty_left _
  obtain ⟨σ', hσ', -, hlow⟩ := hash_compS_own (ResU.comp_empty_left PMap.empty)
    Fig16.BoLo.lower_empty rfl hc
  cases ResU.CompS.functional hσ' (ResU.comp_empty_left _)
  exact ⟨ResU.hash_empty_right hv, ResU.comp_empty_right _,
    .alloc .empty Fig16.BoLo.lower_empty rfl (ResU.comp_empty_left _) hv,
    fun x hx => absurd hx (by simp), hlow⟩

/-- **`ReadFootprint` does not hold**, at a term outside the calculus: from the world whose
frame owns `k`, every run of `peekE k` to a value loads `k`. -/
theorem not_readFootprint : ¬ ReadFootprint := by
  intro h
  obtain ⟨hf, hc, hT, htg, hμ⟩ := frame_world 0
  obtain ⟨μ', v, hrun, -⟩ := h [] (peekE 0) _ _ _ _ _ _ (peekE_wp 0 []) hf hc hT htg hμ
  -- the allocation
  obtain ⟨μ₁, a₁, hh₁, -, t₁⟩ := runIn_head_inv (K := .appR (.val (.lam _)) .hole)
    (a := allocE unit') (Head.alloc (fun _ => none) .unit 0 rfl) hrun v.2
  obtain ⟨l, -, rfl, rfl⟩ := head_alloc_inv hh₁ (v := .unit) rfl
  -- the application of the continuation
  obtain ⟨μ₂, a₂, hh₂, -, t₂⟩ := runIn_head_inv (K := .hole)
    (Head.beta (fun _ => none) _ (.loc l)) t₁ v.2
  obtain ⟨rfl, rfl⟩ := head_det (Head.beta _ _ (.loc l)) hh₂
    (by intro w e; simp [allocRedex, Expr.val, Val.lam] at e)
  -- the load of the frame's cell
  obtain ⟨-, -, -, ht, -⟩ := runIn_head_inv (K := .appR (.val (.lam (.val (.loc l)))) .hole)
    (a := loadE (.val (.loc 0)))
    (Head.load (BoLo.Heap.upd (fun _ => none) 0 .unit) 0 .unit (BoLo.Heap.upd_same _ _ _))
    t₂ v.2
  rcases ht 0 (.load 0) with ⟨ψ, σ, hσ, e⟩ | h0
  · rw [ResU.Flat.functional hσ Fig16.BoLo.flat_empty, PMap.empty_get] at e
    cases e
  · simp [BoLo.Heap.upd] at h0

end BoCa.Fig16.LogRel.Core.TwoRun

end

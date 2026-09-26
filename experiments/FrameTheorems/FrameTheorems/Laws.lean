import FrameTheorems.Callback

/-!
# FrameTheorems — the Optics laws' frame hypotheses at typed worlds

The Optics laws (`experiments/Optics`) are statements about every run of the bare machine from
every closed heap.  The frame facts they assume are hypotheses there: `ElemFrame` for the shape
law, distinct source and focus cells and `PureFn` for fusion.  This file derives what the
logical relation gives of each, at the heaps of tagged typed worlds.

* `optic_frame`: every optic of `experiments/Optics`, run on a source and a callback in the
  relation, changes an existing location only where the source's or the callback's resource
  holds it exclusively.  Proved once for the interface, from `Optic.sem`.
* `over_frame`, `iterMut_frame`: the same for the accessor `over` and for IterMut.
* `elemFrameNA_of_typed`: `ElemFrame`'s heap clauses, for a closed well-typed callback at a
  payload that holds no resource, at every heap of a typed world lending the cell, on every run
  that does not allocate.
* `pure_heap_of_typed`: `PureFn`'s heap clause, for a closed well-typed function at a payload
  that holds no resource, at typed worlds, on every run that does not allocate.
* `mut_ref_distinct`: at a typed world lending `ℓ` at `Mut @a (Ref V)`, the source cell `ℓ`
  and the focus cell it holds are distinct.  `over_fuse_typed` is `over_fuse` with that
  hypothesis discharged.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.FrameTheorems
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Programs (app2)

/-! ### Every optic, once -/

/-- **The frame of every optic.**  For an optic `L` of `experiments/Optics`, a source `s` in the
relation at `ρs` and a callback `g` at `ρg`, from any tagged typed world holding `ρs ● ρg`, the
run `L.run s g` has a run to a value in the relation with `Footprint ρf (ρs ● ρg)`, and every
run that does not allocate is that run. -/
theorem optic_frame {S F : Lifetime.Life → VTy} {W : VTy → VTy} {O : VTy → VTy → VTy}
    (L : Optics.Optic S F W O) {Δ : LifeCtx} {a : Lifetime.Life} {x : LifeVar} {T : VTy}
    (hadm : L.Adm Δ a x) (hT : plainV T = true) {δ : LSub} (hδ : Δ.Models δ)
    {ls : List SRec} {s g : Val} {ρs ρg ρ ρf : WRes} {μ : Heap}
    (hs : vP (S a) ls δ s ρs) (hg : vP (W (Optics.cbTy F x Δ.meetOfDom T)) ls δ g ρg)
    (hc : ResU.CompS ρs ρg ρ) (hW : World ls ρ ρf μ) :
    (∃ (μ' : Heap) (w : Val), Steps μ (app2 (.val L.run) (.val s) (.val g)) μ' (.val w) ∧
      (∃ ls' ρ', vP (.tensor (S a) (O T (Optics.cbTy F x Δ.meetOfDom T))) ls' δ w ρ') ∧
      Footprint ρf ρ μ μ') ∧
    ∀ {μR : Heap} {w : Val}, StepsNA μ (app2 (.val L.run) (.val s) (.val g)) μR (.val w) →
      (∃ ls' ρ', vP (.tensor (S a) (O T (Optics.cbTy F x Δ.meetOfDom T))) ls' δ w ρ') ∧
      Footprint ρf ρ μ μR :=
  world_footprint (app2_wp (closed_vP (L.sem hadm hT) hδ ls) hs hg hc) hW

/-- **The frame of `over`.**  `over ℓ f`, for `ℓ` lent at `Mut @a S` and `f : V ⊸ V ⊗ T` in the
relation, changes an existing location only where the source's or `f`'s resource holds it
exclusively. -/
theorem over_frame {S V : VTy} (hV : plainV V = true)
    (L : Optics.Lens (fun _ => S) (fun c => .mut c V)) {Δ : LifeCtx} {a : Lifetime.Life}
    {x : LifeVar} {T : VTy} (hadm : L.Adm Δ a x) (hΔ : Δ.Ok) (hx : Δ.find? x = none)
    (hT : plainV T = true) {δ : LSub} (hδ : Δ.Models δ) {ls : List SRec} {m f : Val}
    {ρs ρg ρ ρf : WRes} {μ : Heap} (hs : vP (.mut a S) ls δ m ρs)
    (hf : vP (.lolli V (.tensor V T)) ls δ f ρg) (hc : ResU.CompS ρs ρg ρ)
    (hW : World ls ρ ρf μ) :
    (∃ (μ' : Heap) (w : Val),
      Steps μ (app2 (.val (Optics.overV L.run)) (.val m) (.val f)) μ' (.val w) ∧
      Footprint ρf ρ μ μ') ∧
    ∀ {μR : Heap} {w : Val},
      StepsNA μ (app2 (.val (Optics.overV L.run)) (.val m) (.val f)) μR (.val w) →
      Footprint ρf ρ μ μR := by
  have hsem : SemV Δ [] (.val (Optics.overV L.run)) (Optics.overTy S V a T) :=
    fundamentalC (Optics.d_over hV L hadm hΔ hx hT .nil)
  obtain ⟨⟨μ', w, hrun, -, hfp⟩, hevery⟩ :=
    world_footprint (app2_wp (closed_vP hsem hδ ls) hs hf hc) hW
  exact ⟨⟨μ', w, hrun, hfp⟩, fun hR => (hevery hR).2⟩

/-- **The frame of IterMut.**  `iterMut v g`, for a list `v` in the relation at `ρL` and a
callback `g : !(∀'x ⊏ ⊓Δ. Mut 'x E ⊸ ['x] 1)` at `ρg`, returns a list and changes an existing
location only where the list's or the callback's resource holds it exclusively. -/
theorem iterMut_frame {Δ : LifeCtx} {x : LifeVar} {E : VTy} (hE : plainV E = true)
    (hEc : E.Cl 0) (hx : Δ.find? x = none) {δ : LSub} (hδ : Δ.Models δ) {ls : List SRec}
    {v g : Val} {ρL ρg ρ ρf : WRes} {μ : Heap}
    (hv : vP (clistLE E) ls δ v ρL) (hg : vP (.bang (Optics.elemCb E x Δ.meetOfDom)) ls δ g ρg)
    (hc : ResU.CompS ρL ρg ρ) (hW : World ls ρ ρf μ) :
    (∃ (μ' : Heap) (w : Val),
      Steps μ (app2 (.val (Optics.iterMutV E)) (.val v) (.val g)) μ' (.val w) ∧
      (∃ ls' ρ', vP (.tensor (clistLE E) .unit) ls' δ w ρ') ∧ Footprint ρf ρ μ μ') ∧
    ∀ {μR : Heap} {w : Val},
      StepsNA μ (app2 (.val (Optics.iterMutV E)) (.val v) (.val g)) μR (.val w) →
      (∃ ls' ρ', vP (.tensor (clistLE E) .unit) ls' δ w ρ') ∧ Footprint ρf ρ μ μR := by
  have hsem : SemV Δ [] (.val (Optics.iterMutV E))
      (.lolli (clistLE E) (.lolli (.bang (Optics.elemCb E x Δ.meetOfDom))
        (.tensor (clistLE E) .unit))) :=
    fundamentalC (Optics.d_iterMut hE hEc hx .nil)
  exact world_footprint (app2_wp (closed_vP hsem hδ ls) hv hg hc) hW

/-! ### `ElemFrame` at typed worlds -/

/-- `ElemFrame`'s heap clauses at one heap and one lent cell, on the runs that do not allocate:
the lent cell stays allocated, and every other existing location keeps its value. -/
def ElemFrameNA (g : Val) (μ : Heap) (a : Loc) : Prop :=
  ∀ {μ' : Heap} {t : Val}, StepsNA μ (app2 g.1 unit' (Val.loc a).1) μ' t.1 → KeepsAllBut a μ μ'

/-- **`ElemFrame` at typed worlds.**  A closed well-typed callback
`g : ∀'x ⊏ @b. Mut 'x A ⊸ ['x] T`, `A` persistent, satisfies `ElemFrame`'s heap clauses at
every heap of a tagged typed world lending the cell at `Mut 'x A`, on every run that does not
allocate; and it has a run to a value there. -/
theorem elemFrameNA_of_typed {Δ : LifeCtx} {A : VTy} (hA : A.Persistent) {x : LifeVar}
    {b : Lifetime.Life} {T : VTy} {g : Val}
    (hg : CDerives Δ [] (.val g) (.val (Optics.cbTy (fun c => .mut c A) x b T)))
    {δ : LSub} (hδ : Δ.Models δ) {ls : List SRec} {α : Life} (hlt : LtLife δ b α)
    {a : Loc} {ρv ρf : WRes} {μ : Heap}
    (hv : vP (.mut (.var x) A) ls (δ.extend x α) (.loc a) ρv) (hW : World ls ρv ρf μ) :
    ElemFrameNA g μ a ∧ ∃ (μ' : Heap) (t : Val), Steps μ (app2 g.1 unit' (Val.loc a).1) μ' t.1 := by
  obtain ⟨⟨μ', t, hrun, -⟩, hevery⟩ := mut_call_frame hA hg hδ hlt hv hW
  exact ⟨fun hR => hevery hR, μ', t, hrun⟩

/-! ### `PureFn`'s heap clause -/

/-- **A closed well-typed function at a payload that holds no resource changes no existing
location.**  `f : V ⊸ V ⊗ T`, closed and well typed, `V` persistent: from any heap of a tagged
typed world, `f v` has a run to a value that leaves every existing location as it was, and every
run that does not allocate is that run.  This is `PureFn`'s heap clause at typed worlds; its
value clause, that the result is a function of `v` alone, is not derived here. -/
theorem pure_heap_of_typed {Δ : LifeCtx} {V T : VTy} (hV : V.Persistent) {f : Val}
    (hf : CDerives Δ [] (.val f) (.val (.lolli V (.tensor V T)))) {δ : LSub}
    (hδ : Δ.Models δ) {ls : List SRec} {v : Val} {ρv ρf : WRes} {μ : Heap}
    (hv : vP V ls δ v ρv) (hW : World ls ρv ρf μ) :
    (∃ (μ' : Heap) (w : Val), Steps μ (.app (.val f) (.val v)) μ' (.val w) ∧
      ∀ l, μ l ≠ none → μ' l = μ l) ∧
    ∀ {μR : Heap} {w : Val}, StepsNA μ (.app (.val f) (.val v)) μR (.val w) →
      ∀ l, μ l ≠ none → μR l = μ l := by
  obtain rfl := vP_empty_of_persistent hV hv
  have hnone : ∀ l, ImmOnly (PMap.empty : WRes) l := fun l =>
    immOnly_of_not_mem fun ψ ⟨σ, hσ, e⟩ => by
      rw [ResU.Flat.functional hσ Fig16.BoLo.flat_empty, PMap.empty_get] at e
      cases e
  obtain ⟨⟨μ', w, hrun, -, -, hfoot, -⟩, hevery⟩ := world_footprint
    (app_wp (closed_vP (fundamentalC hf) hδ ls) hv (ResU.comp_empty_left _)) hW
  exact ⟨⟨μ', w, hrun, fun l hl => hfoot l hl (hnone l)⟩,
    fun hR l hl => (hevery hR).2.2.1 l hl (hnone l)⟩

/-! ### Distinct cells -/

/-- **The source cell and the focus cell are distinct.**  In any typed world in which `ℓ` is
lent at `Mut @a (Ref V)`, `ℓ` holds a location `ℓ′ ≠ ℓ`, and `ℓ′` is allocated. -/
theorem mut_ref_distinct {V : VTy} {ls : List SRec} {δ : LSub} {c : Lifetime.Life} {ℓ : Loc}
    {ρv Y Z : WRes} {μ : Heap} (hv : vP (.mut c (.ref V)) ls δ (.loc ℓ) ρv)
    (hc : ResU.CompS ρv Y Z) (hμ : ResU.Lower Z μ) :
    ∃ ℓ' : Loc, μ ℓ = some (.loc ℓ') ∧ ℓ ≠ ℓ' ∧ μ ℓ' ≠ none := by
  obtain ⟨α, -, ℓ₀, hsep⟩ := hv
  obtain ⟨hℓ, hpto⟩ := pure_sep_iff.mp hsep
  obtain rfl : ℓ = ℓ₀ := by simpa using hℓ
  obtain ⟨b, u, σ, hσ, Q, hw, ls₀, -, rfl, hQ, -, -⟩ := hpto
  have hP : vP (.ref V) ls₀ δ u σ := by
    have : ofS Q u σ := ⟨hσ, hw⟩
    rw [hQ] at this
    exact this
  obtain ⟨ℓ', v', hsep'⟩ := hP
  obtain ⟨rfl, σ₁, σ₂, hcσ, rfl, -⟩ := pure_sep_iff.mp hsep'
  -- the witness owns `ℓ′`
  obtain ⟨ψ', eψ', kψ', -, -⟩ := compS_get_left' hcσ (ResU.single_get_self ℓ' (CellU.ownOf v'))
  -- the heap reads the `mut` cell's value at `ℓ`
  obtain ⟨χ, eχ, -, -, xχ⟩ := compS_get_left' hc (ResU.single_get_self ℓ _)
  have hμℓ : μ ℓ = some (.loc ℓ') := by rw [lower_get hμ eχ, xχ]; simp
  -- the flattening of `ρv` exists, and its exclusive walk puts `ℓ′`'s `own` cell beside `ℓ`
  obtain ⟨σZ, hσZ, hvalZ⟩ := hμ
  obtain ⟨σv, -, hσv, -, hinv, -, -⟩ := flat_factor hc hσZ
  obtain ⟨ex, ag, hex, -, hexag⟩ := hσv
  obtain ⟨e', he', hce'⟩ := ExW.single_mut_inv hex
  have he'ℓ' : e'.get ℓ' = some ψ' := ExS.get_of_ne_imm he' eψ' (by rw [kψ']; simp)
  refine ⟨ℓ', hμℓ, fun hEq => ?_, ?_⟩
  · subst hEq
    have := CellU.CompatS.kinds (hce'.1 ℓ _ _ (ResU.single_get_self ℓ _) he'ℓ')
    simp at this
  · obtain ⟨ζ, eζ⟩ : ∃ ζ, ex.get ℓ' = some ζ := by
      obtain ⟨ζ, eζ, -⟩ := comp_get_right_erase compS_erase hce' he'ℓ'
      exact ⟨ζ, eζ⟩
    obtain ⟨ζ', eζ', -⟩ := comp_get_left_erase compS_erase hexag eζ
    obtain ⟨ζ'', eζ'', -⟩ := hinv ℓ' ζ' eζ'
    rw [hvalZ ℓ', eζ'']
    simp

/-- **Fusion at typed worlds.**  `over_fuse` at the identity lens, with the distinct-cells
hypothesis discharged: in any typed world lending `ℓ` at `Mut @a (Ref V)`, two `over`s at pure
`f` and `g` in sequence run exactly as one `over` of the sequenced function. -/
theorem over_fuse_typed {V : VTy} (hV : plainV V = true) {ls : List SRec} {δ : LSub}
    {c : Lifetime.Life} {ℓ : Loc} {ρv Y Z : WRes} {μ : Heap}
    (hv : vP (.mut c (.ref V)) ls δ (.loc ℓ) ρv) (hc : ResU.CompS ρv Y Z)
    (hμ : ResU.Lower Z μ) (hμc : Optics.HeapClosed μ)
    {f g : Val} {φ₁ φ₂ ψ₁ ψ₂ : Val → Val} (hf : closedAt 0 f.1 = true)
    (hg : closedAt 0 g.1 = true) (hpf : Optics.PureFn f φ₁ φ₂) (hpg : Optics.PureFn g ψ₁ ψ₂)
    (hφ₁ : ∀ v, closedAt 0 (φ₁ v).1 = true) (hφ₂ : ∀ v, closedAt 0 (φ₂ v).1 = true)
    {μ' : Heap} {w : Val} :
    Steps μ (Optics.twiceE (Optics.idLens V hV).run ℓ f g) μ' w.1 ↔
      Steps μ (app2 (.val (Optics.overV (Optics.idLens V hV).run)) (Val.loc ℓ).1
        (Optics.seqF f g).1) μ' w.1 := by
  obtain ⟨ℓ', hs, hne, hdom⟩ := mut_ref_distinct hv hc hμ
  obtain ⟨v, hv'⟩ := Option.ne_none_iff_exists'.mp hdom
  exact Optics.over_fuse (Optics.idLens V hV) (fun _ => True) id rfl (fun _ h _ => h) hf hg
    hpf hpg hφ₁ hφ₂ hμc hs trivial rfl hv' hne

end BoCa.Fig16.LogRel.Core.FrameTheorems

end

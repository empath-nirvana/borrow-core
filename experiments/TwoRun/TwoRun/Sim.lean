import TwoRun.Fresh

/-!
# TwoRun — every fresh run follows every run

A fresh run `B` and an arbitrary run `A` from one configuration, both to values, are related
at every step by a function `g : Loc → Loc` (`HeapRel`, `step_sim`, `run_sim`):

* `A`'s term is `B`'s term renamed by `g`;
* `g` is injective on `B`'s allocated locations, maps them onto `A`'s, and each of `B`'s cells
  renamed by `g` is `A`'s cell at the image.

`g` need not be injective off `B`'s heap.  `A` may reuse a location its configuration still
names (a dangling pointer after `free`), and then `g` sends a name `B` holds only as a dangling
pointer to the location `A` reused.  `B` never reads through such a name: `B` is fresh, so the
name stays unallocated in `B`, and `B` would be stuck.  So `A` takes the steps `B` takes, at the
image under `g`.

At the end `A`'s heap is `B`'s heap pushed forward along `g` (`Heap.push`), and `A`'s value is
`B`'s renamed.  Applied to the run `wpTS` exhibits, this is the footprint of every fresh run
(`wpTS_footprint_fresh`): an injective renaming of its final heap satisfies `Footprint`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.TwoRun
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Fig16.LogRel.Core.FrameTheorems (allocRedex head_det Footprint)

/-! ### The relation between the two runs' heaps -/

/-- `g` maps `μB`'s allocated locations injectively onto `μA`'s, and each cell of `μB`, renamed
by `g`, is `μA`'s cell at the image. -/
def HeapRel (g : Loc → Loc) (μB μA : Heap) : Prop :=
  (∀ x, μB x ≠ none → μA (g x) = (μB x).map (Val.rename g)) ∧
  (∀ x y, μB x ≠ none → μB y ≠ none → g x = g y → x = y) ∧
  (∀ k, μA k ≠ none → ∃ x, μB x ≠ none ∧ g x = k)

theorem heapRel_id (μ : Heap) : HeapRel id μ μ := by
  refine ⟨fun x _ => ?_, fun _ _ _ _ h => h, fun k hk => ⟨k, hk, rfl⟩⟩
  show μ x = (μ x).map (Val.rename id)
  cases μ x with
  | none => rfl
  | some v => exact congrArg some (Val.rename_id v).symm

/-- `μ` pushed forward along `g`: the cell at `x` moves to `g x`, its value renamed. -/
def Heap.push (g : Loc → Loc) (μ : Heap) : Heap := fun k =>
  open Classical in
  if h : ∃ x, μ x ≠ none ∧ g x = k then (μ h.choose).map (Val.rename g) else none

/-- A heap `HeapRel` relates to `μB` along `g` is `μB` pushed forward. -/
theorem HeapRel.eq_push {g : Loc → Loc} {μB μA : Heap} (h : HeapRel g μB μA) :
    μA = Heap.push g μB := by
  funext k
  unfold Heap.push
  split
  · rename_i hk
    obtain ⟨hx, e⟩ := hk.choose_spec
    have := h.1 _ hx
    rwa [e] at this
  · rename_i hk
    by_contra hne
    exact hk (h.2.2 k hne)

theorem HeapRel.injOn {g : Loc → Loc} {μB μA : Heap} (h : HeapRel g μB μA) :
    Set.InjOn g {x | μB x ≠ none} := fun x hx y hy e => h.2.1 x y hx hy e

/-! ### One head step -/

/-- **A head step that is not an allocation, followed.**  If `B` takes it, `A` takes it at the
image under `g`, and the heaps stay related. -/
theorem head_sim {g : Loc → Loc} {μB μB' μA : Heap} {b b' : Expr} (hB : Head μB b μB' b')
    (hR : HeapRel g μB μA) (hna : ∀ v : Val, b ≠ allocRedex v) :
    ∃ μA', Head μA (b.rename g) μA' (b'.rename g) ∧ HeapRel g μB' μA' := by
  obtain ⟨h₁, h₂, h₃⟩ := hR
  cases hB with
  | alloc v _ _ => exact absurd rfl (hna v)
  | beta b v =>
      rw [Expr.rename_subst]
      exact ⟨μA, .beta _ (b.rename g) (v.rename g), h₁, h₂, h₃⟩
  | seq => exact ⟨μA, .seq _ _, h₁, h₂, h₃⟩
  | letpair v₁ v₂ e =>
      rw [Expr.rename_subst, Expr.rename_subst, Val.rename_shift]
      exact ⟨μA, .letpair _ (v₁.rename g) (v₂.rename g) (e.rename g), h₁, h₂, h₃⟩
  | case₁ v e₁ e₂ =>
      rw [Expr.rename_subst]
      exact ⟨μA, .case₁ _ (v.rename g) (e₁.rename g) (e₂.rename g), h₁, h₂, h₃⟩
  | case₂ v e₁ e₂ =>
      rw [Expr.rename_subst]
      exact ⟨μA, .case₂ _ (v.rename g) (e₁.rename g) (e₂.rename g), h₁, h₂, h₃⟩
  | host op v r h =>
      obtain ⟨e₁, e₂⟩ := host_call_rename ℍ op g v
      have hr : (Expr.val r).rename g = Expr.val r := by rw [← Val.rename_val, e₂ r h]
      rw [hr]
      exact ⟨μA, .host _ op (v.rename g) r (e₁.trans h), h₁, h₂, h₃⟩
  | load ℓ v h =>
      have hA : μA (g ℓ) = some (v.rename g) := by rw [h₁ ℓ (by simp [h]), h]; rfl
      exact ⟨μA, .load _ (g ℓ) (v.rename g) hA, h₁, h₂, h₃⟩
  | store ℓ v w h =>
      have hℓ : μB ℓ ≠ none := by simp [h]
      have hA : μA (g ℓ) = some (w.rename g) := by rw [h₁ ℓ hℓ, h]; rfl
      have dom : ∀ x, (μB.upd ℓ v) x ≠ none ↔ μB x ≠ none := fun x => by
        by_cases e : x = ℓ
        · subst e; simp [h]
        · rw [Heap.upd_other e]
      refine ⟨μA.upd (g ℓ) (v.rename g), .store _ (g ℓ) (v.rename g) (w.rename g) hA, fun x hx => ?_,
        fun x y hx hy => h₂ x y ((dom x).mp hx) ((dom y).mp hy), fun k hk => ?_⟩
      · by_cases e : x = ℓ
        · subst e; simp
        · have hx' := (dom x).mp hx
          rw [Heap.upd_other e, Heap.upd_other fun e' => e (h₂ x ℓ hx' hℓ e')]
          exact h₁ x hx'
      · by_cases e : k = g ℓ
        · exact ⟨ℓ, (dom ℓ).mpr hℓ, e.symm⟩
        · rw [Heap.upd_other e] at hk
          obtain ⟨x, hx, rfl⟩ := h₃ k hk
          exact ⟨x, (dom x).mpr hx, rfl⟩
  | free ℓ v h =>
      have hℓ : μB ℓ ≠ none := by simp [h]
      have hA : μA (g ℓ) = some (v.rename g) := by rw [h₁ ℓ hℓ, h]; rfl
      have dom : ∀ x, (μB.del ℓ) x ≠ none ↔ μB x ≠ none ∧ x ≠ ℓ := fun x => by
        by_cases e : x = ℓ
        · subst e; simp
        · rw [Heap.del_other e]; exact ⟨fun h => ⟨h, e⟩, fun h => h.1⟩
      refine ⟨μA.del (g ℓ), .free _ (g ℓ) (v.rename g) hA, fun x hx => ?_,
        fun x y hx hy => h₂ x y ((dom x).mp hx).1 ((dom y).mp hy).1, fun k hk => ?_⟩
      · obtain ⟨hx', e⟩ := (dom x).mp hx
        rw [Heap.del_other e, Heap.del_other fun e' => e (h₂ x ℓ hx' hℓ e')]
        exact h₁ x hx'
      · by_cases e : k = g ℓ
        · subst e; simp at hk
        · rw [Heap.del_other e] at hk
          obtain ⟨x, hx, rfl⟩ := h₃ k hk
          exact ⟨x, (dom x).mpr ⟨hx, fun e' => e (e' ▸ rfl)⟩, rfl⟩

/-! ### One step -/

theorem rename_update_eq {g : Loc → Loc} {ℓ ℓ' : Loc} {e : Expr} (h : ¬ e.Occ ℓ) :
    e.rename (Function.update g ℓ ℓ') = e.rename g :=
  Expr.rename_congr e fun k o => Function.update_of_ne (fun (e' : k = ℓ) => h (e' ▸ o)) _ _

theorem Kont.rename_congr {σ τ : Loc → Loc} :
    ∀ (K : Kont) (e : Expr), (∀ ℓ, (K.plug e).Occ ℓ → σ ℓ = τ ℓ) → K.rename σ = K.rename τ
  | .hole, _, _ => rfl
  | .pairL K e₂, e, h | .letpair K e₂, e, h | .seq K e₂, e, h => by
      simp only [BoLo.Kont.rename, Kont.rename_congr K e (fun ℓ o => h ℓ (Or.inl o)),
        Expr.rename_congr e₂ (fun ℓ o => h ℓ (Or.inr o))]
  | .pairR v K, e, h => by
      simp only [BoLo.Kont.rename, Kont.rename_congr K e (fun ℓ o => h ℓ (Or.inr o))]
      exact congrArg₂ _ (Subtype.ext (Expr.rename_congr _ (fun ℓ o => h ℓ (Or.inl o)))) rfl
  | .appR f K, e, h => by
      simp only [BoLo.Kont.rename, Kont.rename_congr K e (fun ℓ o => h ℓ (Or.inr o)),
        Expr.rename_congr f (fun ℓ o => h ℓ (Or.inl o))]
  | .appL K v, e, h => by
      simp only [BoLo.Kont.rename, Kont.rename_congr K e (fun ℓ o => h ℓ (Or.inl o))]
      exact congrArg₂ _ rfl (Subtype.ext (Expr.rename_congr _ (fun ℓ o => h ℓ (Or.inr o))))
  | .case K e₁ e₂, e, h => by
      simp only [BoLo.Kont.rename, Kont.rename_congr K e (fun ℓ o => h ℓ (Or.inl o)),
        Expr.rename_congr e₁ (fun ℓ o => h ℓ (Or.inr (Or.inl o))),
        Expr.rename_congr e₂ (fun ℓ o => h ℓ (Or.inr (Or.inr o)))]
  | .inj₁ K, e, h | .inj₂ K, e, h => by
      simp only [BoLo.Kont.rename, Kont.rename_congr K e h]

/-- **One step of a fresh run, followed.**  If `B` takes a fresh step from `(μB, eB)` and `A`
takes any step from `(μA, g eB)` with the heaps related along `g`, then `A`'s step is `B`'s at
the image, and the resulting configurations are related along an update of `g`. -/
theorem step_sim {g : Loc → Loc} {μB μB' μA μA' : Heap} {eB eB' eA' : Expr}
    (hB : Step1F μB eB μB' eB') (hR : HeapRel g μB μA) (hA : Step1 μA (eB.rename g) μA' eA') :
    ∃ g', eA' = eB'.rename g' ∧ HeapRel g' μB' μA' := by
  obtain ⟨⟨K, b, b', rfl, rfl, hhB⟩, hfB⟩ := hB
  obtain ⟨K', a, a', hE, rfl, hhA⟩ := hA
  rw [BoLo.Kont.rename_plug] at hE
  have hnv : ¬ IsVal (b.rename g) := fun h => hhB.not_isVal (isVal_of_rename g h)
  obtain ⟨K'', hb, rfl⟩ := Fig16.LogRel.Core.plug_decomp hhA (K.rename g) K' hnv hE
  rw [BoLo.Kont.plug_comp]
  by_cases hal : ∃ v, b = allocRedex v
  · obtain ⟨v, rfl⟩ := hal
    -- the allocation redex has a head step at the empty heap
    have hh₀ : Head (fun _ => none) ((allocRedex v).rename g)
        (BoLo.Heap.upd (fun _ => none) 0 (v.rename g)) (.val (.loc 0)) := by
      simp only [allocRedex, Expr.rename]; exact .alloc _ (v.rename g) 0 rfl
    obtain rfl : K'' = .hole := Fig16.LogRel.Core.head_plug hh₀ K'' hhA.not_isVal hb
    simp only [Kont.plug] at hb
    subst hb
    obtain ⟨ℓB, hℓB, rfl, rfl⟩ := head_alloc_inv hhB rfl
    obtain ⟨ℓA, hℓA, rfl, rfl⟩ := head_alloc_inv hhA (v := v.rename g) rfl
    have nB := hfB ℓB (by simp) hℓB
    have oK : ∀ k, (K.plug (allocRedex v)).Occ k → k ≠ ℓB := fun k o e => nB (.inr (.inl (e ▸ o)))
    have hv : v.rename (Function.update g ℓB ℓA) = v.rename g :=
      Subtype.ext (rename_update_eq fun o =>
        oK ℓB (Kont.occ_plug K (show (Expr.app _ _).Occ ℓB from Or.inr o)) rfl)
    refine ⟨Function.update g ℓB ℓA, ?_, ?_⟩
    · rw [BoLo.Kont.rename_plug, Kont.rename_congr (σ := Function.update g ℓB ℓA) (τ := g) K
        (allocRedex v) (fun k o => Function.update_of_ne (oK k o) _ _)]
      simp only [Kont.plug, Expr.rename, Expr.val, Val.loc, Function.update_self]
    · obtain ⟨h₁, h₂, h₃⟩ := hR
      have ne : ∀ x, μB x ≠ none → x ≠ ℓB := fun x hx e => hx (e ▸ hℓB)
      have neA : ∀ x, μB x ≠ none → g x ≠ ℓA := fun x hx e => by
        have := h₁ x hx; rw [e, hℓA] at this
        cases h : μB x with
        | none => exact hx h
        | some w => rw [h] at this; cases this
      refine ⟨fun x hx => ?_, fun x y hx hy e => ?_, fun k hk => ?_⟩
      · by_cases ex : x = ℓB
        · rw [ex, Function.update_self, Heap.upd_same, Heap.upd_same, Option.map_some, hv]
        · have hx' : μB x ≠ none := by rwa [Heap.upd_other ex] at hx
          rw [Function.update_of_ne ex, Heap.upd_other (neA x hx'), Heap.upd_other ex, h₁ x hx']
          cases hμ : μB x with
          | none => exact absurd hμ hx'
          | some w =>
              refine congrArg some (Subtype.ext (rename_update_eq fun o => nB ?_).symm)
              exact .inr (.inr ⟨x, w, hμ, o⟩)
      · by_cases ex : x = ℓB <;> by_cases ey : y = ℓB
        · exact ex.trans ey.symm
        · have hy' : μB y ≠ none := by rwa [Heap.upd_other ey] at hy
          rw [ex, Function.update_self, Function.update_of_ne ey] at e
          exact absurd e.symm (neA y hy')
        · have hx' : μB x ≠ none := by rwa [Heap.upd_other ex] at hx
          rw [ey, Function.update_self, Function.update_of_ne ex] at e
          exact absurd e (neA x hx')
        · have hx' : μB x ≠ none := by rwa [Heap.upd_other ex] at hx
          have hy' : μB y ≠ none := by rwa [Heap.upd_other ey] at hy
          rw [Function.update_of_ne ex, Function.update_of_ne ey] at e
          exact h₂ x y hx' hy' e
      · by_cases ek : k = ℓA
        · exact ⟨ℓB, by simp, by rw [ek, Function.update_self]⟩
        · rw [Heap.upd_other ek] at hk
          obtain ⟨x, hx, rfl⟩ := h₃ k hk
          exact ⟨x, by rwa [Heap.upd_other (ne x hx)], Function.update_of_ne (ne x hx) _ _⟩
  · push Not at hal
    obtain ⟨μA'', hA'', hR''⟩ := head_sim hhB hR hal
    obtain rfl : K'' = .hole := Fig16.LogRel.Core.head_plug hA'' K'' hhA.not_isVal hb
    simp only [Kont.plug] at hb
    subst hb
    obtain ⟨rfl, rfl⟩ := head_det hA'' hhA (not_allocRedex_rename g hal)
    exact ⟨g, (BoLo.Kont.rename_plug g K b').symm, hR''⟩

/-! ### Runs -/

/-- **A fresh run, followed by every run.**  From configurations related along `g`, if `B`
takes a fresh run to a value and `A` takes any run to a value, then `A`'s value is `B`'s
renamed and the final heaps are related, along one function. -/
theorem run_sim {μB μB' : Heap} {eB eB' : Expr} (hB : FreshRun μB eB μB' eB') :
    IsVal eB' → ∀ {g : Loc → Loc} {μA μA' : Heap} {eA' : Expr}, HeapRel g μB μA →
      Steps μA (eB.rename g) μA' eA' → IsVal eA' →
      ∃ g', eA' = eB'.rename g' ∧ HeapRel g' μB' μA' := by
  induction hB with
  | refl μ e =>
      intro hv g μA μA' eA' hR hA _
      cases hA with
      | refl => exact ⟨g, rfl, hR⟩
      | more h _ => exact absurd h (not_step1_of_isVal (hv.rename g))
  | more hs _ ih =>
      intro hv g μA μA' eA' hR hA hvA
      cases hA with
      | refl => exact absurd hs.1 (not_step1_of_isVal (isVal_of_rename g hvA))
      | more h t =>
          obtain ⟨g₁, rfl, hR₁⟩ := step_sim hs hR h
          exact ih hv hR₁ t hvA

/-- **Every run is a fresh run's image.**  If a fresh run and any run from one configuration
reach values, the second's heap is the first's pushed forward along a function injective on the
first's heap, and its value is the first's renamed. -/
theorem fresh_run_image {μ μB μA : Heap} {e : Expr} {vB vA : Val}
    (hB : FreshRun μ e μB vB.1) (hA : Steps μ e μA vA.1) :
    ∃ g : Loc → Loc, Set.InjOn g {x | μB x ≠ none} ∧ μA = Heap.push g μB ∧ vA = vB.rename g := by
  obtain ⟨g, hv, hR⟩ := run_sim hB vB.2 (g := id) (heapRel_id μ) (by rwa [Expr.rename_id]) vA.2
  exact ⟨g, hR.injOn, hR.eq_push, Subtype.ext hv⟩

/-! ### The footprint of every fresh run -/

/-- **The footprint of every fresh run.**  From the tagged typed world `ρf ● ρ`, every fresh
run of `e` to a value has, along a function `g` injective on its final heap, the exhibited run's
footprint: the final heap pushed forward along `g` satisfies `Footprint ρf ρ`, and the value
renamed by `g` satisfies the post-condition. -/
theorem wpTS_footprint_fresh {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp}
    {ρ : WRes} (hw : wpTS ls e Q ρ) {ρf fρ : WRes} {ps : List FrameRec}
    (hf : ResU.Hash ρf ρ) (hc : ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls))
    (htg : Tagged fρ ps ls) {μ μR : Heap} {w : Val} (hμ : ResU.Lower fρ μ)
    (hR : FreshRun μ e μR w.1) :
    ∃ g : Loc → Loc, Set.InjOn g {x | μR x ≠ none} ∧
      (∃ ls' ρ', Q ls' (w.rename g) ρ') ∧ Footprint ρf ρ μ (Heap.push g μR) := by
  obtain ⟨μ', v, hrun, hQ, hfp⟩ := FrameTheorems.wpTS_footprint hw hf hc hT htg hμ
  obtain ⟨g, hinj, rfl, rfl⟩ := fresh_run_image hR hrun
  exact ⟨g, hinj, hQ, hfp⟩

/-- The footprint on every fresh run, up to an injective renaming of its final heap. -/
def EveryFreshRunFootprint : Prop :=
  ∀ (ls : List SRec) (e : Expr) (Q : List SRec → Val → WProp) (ρ ρf fρ : WRes)
    (ps : List FrameRec) (μ μR : Heap) (w : Val),
    wpTS ls e Q ρ → ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ → TW fρ ps (rsOf ls) →
    Tagged fρ ps ls → ResU.Lower fρ μ → FreshRun μ e μR w.1 →
    ∃ g : Loc → Loc, Set.InjOn g {x | μR x ≠ none} ∧ Footprint ρf ρ μ (Heap.push g μR)

theorem everyFreshRunFootprint : EveryFreshRunFootprint := by
  intro ls e Q ρ ρf fρ ps μ μR w hw hf hc hT htg hμ hR
  obtain ⟨g, hinj, -, hfp⟩ := wpTS_footprint_fresh hw hf hc hT htg hμ hR
  exact ⟨g, hinj, hfp⟩

end BoCa.Fig16.LogRel.Core.TwoRun

end

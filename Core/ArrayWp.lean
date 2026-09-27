import Core.Integers

/-!
# Core — the array steps at the typed world  `[spec §9]`

`tab` places `n` cells holding `()` at fresh consecutive locations and continues as `tabFill`.
In the typed world that is `n` of `TW.alloc`, at the allocator's block `ℓ, …, ℓ + n − 1`, free in
the configuration's memory (`Alloc.fresh`): `alloc_block` builds the world after them,
and `wpTS_tab` puts the step in front of the run of `tabFill`. `idx` and `drop` change no memory:
`wpTS_idx` and `wpTS_dropStep` are `wpTS_head`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore Alloc ARun Step1N)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `omega` at locations: `Loc` is `ℕ`. -/
macro "lomega" : tactic => `(tactic| ((try unfold BoCa.Loc at *) <;> omega))

/-- One cell placed at a location the heap does not hold: the world after `TW.alloc`, with the
frame kept.  `[spec §9]` -/
theorem alloc_world {ρf ρ σ : WRes} {ps rs : List FrameRec} {μ : Heap} {l : Loc} (v : Val)
    (hf : ResU.Hash ρf ρ) (hσ : ResU.CompS ρf ρ σ) (hT : TW σ ps rs) (hμ : ResU.Lower σ μ)
    (hμl : μ l = none) :
    ∃ x σ', ResU.CompS ρ (ResU.single l (CellU.ownOf v)) x ∧ ResU.Hash ρf x ∧
      ResU.CompS ρf x σ' ∧ TW σ' ps rs ∧ ResU.Lower σ' (μ.upd l v) ∧ ResU.UpdV ρ x ∧
      (∀ a, AgW σ' a → AgW σ a) := by
  obtain ⟨τ, hτ, hval⟩ := id hμ
  have hρl : ρ.get l = none :=
    ((ResU.Comp.eq_none_iff hσ l).mp (get_eq_none_of_flat hτ ((lower_eq_none_iff hval).mp hμl))).2
  obtain ⟨x, hx⟩ := (ResU.compS_defined_iff ρ (ResU.single l (CellU.ownOf v))).mpr
    (compatS_single_of_get_none hρl)
  obtain ⟨σ', hσ'x, hfx, hlow'⟩ := hash_compS_own hσ hμ hμl hx
  obtain ⟨y, hy, hyσ'⟩ := (ResU.CompS.assoc ρf ρ (ResU.single l (CellU.ownOf v)) σ').mp
    ⟨x, hx, hσ'x⟩
  cases ResU.CompS.functional hy hσ
  exact ⟨x, σ', hx, hfx, hσ'x, TW.alloc hT hμ hμl hyσ' (hash_valid_comp hfx hσ'x), hlow',
    updV_compS_own hx (hash_valid hf).2 (hash_valid hfx).2, fun a ha => alloc_ag hyσ' ha⟩

theorem fill_zero (μ : Heap) (ℓ : Loc) (v : Val) : μ.fill ℓ 0 v = μ := by
  funext k; simp only [BoCa.BoLo.Heap.fill]; split
  · lomega
  · rfl

theorem fill_succ (μ : Heap) (ℓ : Loc) (n : Nat) (v : Val) :
    (μ.upd ℓ v).fill (ℓ + 1) n v = μ.fill ℓ (n + 1) v := by
  funext k
  simp only [BoCa.BoLo.Heap.fill, BoCa.BoLo.Heap.upd]
  by_cases h₁ : ℓ + 1 ≤ k ∧ k < ℓ + 1 + n
  · rw [if_pos h₁, if_pos (by lomega)]
  · rw [if_neg h₁]
    by_cases h₂ : k = ℓ
    · rw [if_pos h₂, if_pos (by lomega)]
    · rw [if_neg h₂, if_neg (by lomega)]

/-- `n` cells holding `v` placed at `ℓ + k, …, ℓ + k + n − 1`, locations the heap does not hold:
`n` of `alloc_world`.  `[spec §9]` -/
theorem alloc_block {ρf : WRes} {ps rs : List FrameRec} (v : Val) (ℓ : Nat) :
    ∀ (n k : Nat) {ρ σ : WRes} {μ : Heap}, ResU.Hash ρf ρ → ResU.CompS ρf ρ σ → TW σ ps rs →
      ResU.Lower σ μ → (∀ j, j < n → μ (ℓ + k + j) = none) →
      ∃ x σ' cells, sepRange (fun m => ptoOwn m v) (ℓ + k) n cells ∧ ResU.CompS ρ cells x ∧
        ResU.Hash ρf x ∧ ResU.CompS ρf x σ' ∧ TW σ' ps rs ∧ ResU.Lower σ' (μ.fill (ℓ + k) n v) ∧
        ResU.UpdV ρ x ∧ (∀ a, AgW σ' a → AgW σ a)
  | 0, k, ρ, σ, μ, hf, hσ, hT, hμ, _ => by
      refine ⟨ρ, σ, PMap.empty, ⟨rfl, trivial⟩, ResU.comp_empty_right ρ, hf, hσ, hT, ?_,
        (ResU.updV_self_iff ρ).mpr (hash_valid hf).2, fun _ h => h⟩
      rw [fill_zero]; exact hμ
  | n + 1, k, ρ, σ, μ, hf, hσ, hT, hμ, hfr => by
      obtain ⟨x₁, σ₁, hx₁, hf₁, hσ₁, hT₁, hμ₁, hu₁, hag₁⟩ :=
        alloc_world v hf hσ hT hμ (by simpa using hfr 0 (Nat.succ_pos n))
      obtain ⟨x, σ', cells, hcells, hx, hf', hσ', hT', hμ', hu, hag⟩ :=
        alloc_block v ℓ n (k + 1) hf₁ hσ₁ hT₁ hμ₁ (fun j hj => by
          rw [BoCa.BoLo.Heap.upd_other (by lomega)]
          have := hfr (j + 1) (by lomega)
          rwa [show ℓ + k + (j + 1) = ℓ + (k + 1) + j by lomega] at this)
      obtain ⟨bc, hbc, hρx⟩ := compS_reassoc hx₁ hx
      refine ⟨x, σ', bc, ⟨_, cells, hbc, rfl, ?_⟩, hρx, hf', hσ', hT', ?_, hu₁.trans hu,
        fun a ha => hag₁ a (hag a ha)⟩
      · rwa [show ℓ + k + 1 = ℓ + (k + 1) by omega]
      · rw [← fill_succ]; rwa [show ℓ + k + 1 = ℓ + (k + 1) by omega]

/-- **The `tab` step.**  At the allocator's block `ℓ, …`, the placeholders `ℓ + i ↦ ()` are
handed to the run of `tabFill`.  `[spec §9]` -/
theorem wpTS_tab (ls : List SRec) (c : UInt32) (f : Val) (Q : List SRec → Val → WProp) :
    Entails (all fun ℓ : Loc => wand (sepRange (fun m => ptoOwn m .unit) ℓ (arrLen c).toNat)
        (wpTS ls (tabFill f ℓ (arrLen c) 0 (arrLen c).toNat) Q))
      (wpTS ls (.app (.val (.prim .tab)) (.val (Val.pair (Val.i32 c) f))) Q) := by
  intro ρ h ρf σ ps hf hσ hT htg A k
  obtain ⟨μ, hμ⟩ := lower_of_hash hf hσ
  set ℓ := A.pick k μ (arrLen c).toNat
  have hfree : ∀ j, j < (arrLen c).toNat → μ (ℓ + j) = none :=
    A.fresh k μ _ (lower_finDom hμ)
  obtain ⟨x, σ', cells, hcells, hx, hf', hσ', hT', hμ', hu, hag⟩ :=
    alloc_block .unit ℓ (arrLen c).toNat 0 hf hσ hT hμ (fun j hj => by simpa using hfree j hj)
  simp only [Nat.add_zero] at hcells hμ'
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ₁, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, ⟨j, h₈⟩, h₉, hA, hB,
    hT'', htg', hps, hls, hC⟩ :=
    h ℓ cells x hcells hx ρf σ' ps hf' hσ' hT' (tagged_of_ag hag htg) A (k + 1)
  cases ResU.Lower.functional h₅ hμ'
  exact ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', h₁, h₂, h₃, hμ, h₆, h₇,
    ⟨j, .more ⟨.hole, _, _, rfl, rfl, BoCa.BoLo.AHead.tab k μ c f hfree⟩ h₈⟩, h₉, hu.trans hA,
    hB, hT'', htg', hps, hls, hC⟩

/-- The `idx` step.  `[spec §9]` -/
theorem wpTS_idx (ls : List SRec) (ℓ : Loc) (n i : UInt32) (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (.val (idxAns ℓ n i)) Q)
      (wpTS ls (.app (.val (.prim .idx)) (.val (Val.pair (Val.arr ℓ n) (Val.i32 i)))) Q) :=
  wpTS_head (fun μ => Head.idx μ ℓ n i) rfl ls Q

/-- The `drop` step.  `[spec §9]` -/
theorem wpTS_dropStep (ls : List SRec) (f : Val) (ℓ : Loc) (n : UInt32)
    (Q : List SRec → Val → WProp) :
    Entails (wpTS ls (dropFill f ℓ 0 n.toNat) Q)
      (wpTS ls (.app (.val (.prim .drop)) (.val (Val.pair f (Val.arr ℓ n)))) Q) :=
  wpTS_head (fun μ => Head.drop μ f ℓ n) rfl ls Q

end BoCa.Fig16.LogRel.Core

end

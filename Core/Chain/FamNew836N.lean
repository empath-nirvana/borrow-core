import Core.Chain.FamSwap836N
import Core.EffCancelRuns

/-!
# `array_new`'s `tab` step on the chain  `[spec §9]`

Core's `arrNew_compatX` (`Core/Arrays.lean`) is the `tab` step (`wpTS_tab`, `Core/ArrayWp.lean`)
then the fill (`tabFill_wp`). On the chain:

* `alloc_worldN`/`alloc_blockN` are Core's `alloc_world`/`alloc_block` at the chain's typed world
  `TWNC` (`TWNC.alloc` for `TW.alloc`): `n` cells at a block the memory does not hold.
* `rwpG_tab` is `wpTS_tab` at the step index: the `tab` step is one allocating head step to a
  term that is not a value, so the run after it is the continuation's run from the world
  `alloc_blockN` builds, the index paying for the step; `erwp_tab` is the same at `erwp`.
* `consistentX_sepRange_own`: the allocated block is consistent with every view.

`FamOpsKW835N` reads the fill at `SemJN` (`tabFill_wpN`, Core's `tabFill_wp`) and the constant
(`arrNew_compatN`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont hndE ubindE ccatchE cfinE)

/-- **One cell placed at a location the memory does not hold** (Core's `alloc_world`), at the
chain's typed world. -/
theorem alloc_worldN {ρf ρ σ : WRes} {ps : List FrameRec} {rs : List FrameRec} {μ : Heap} {l : Loc}
    (v : Val) (hf : ResU.Hash ρf ρ) (hσ : ResU.CompS ρf ρ σ) (hT : TWNC σ ps rs)
    (hμ : ResU.Lower σ μ) (hμl : μ l = none) :
    ∃ x σ', ResU.CompS ρ (ResU.single l (CellU.ownOf v)) x ∧ ResU.Hash ρf x ∧
      ResU.CompS ρf x σ' ∧ TWNC σ' ps rs ∧ ResU.Lower σ' (μ.upd l v) ∧ ResU.UpdV ρ x ∧
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
  exact ⟨x, σ', hx, hfx, hσ'x, TWNC.alloc hT hμ hμl hyσ' (hash_valid_comp hfx hσ'x), hlow',
    updV_compS_own hx (hash_valid hf).2 (hash_valid hfx).2, fun a ha => alloc_ag hyσ' ha⟩

/-- **`n` cells holding `v` at `ℓ + k, …, ℓ + k + n − 1`**, locations the memory does not hold
(Core's `alloc_block`): `n` of `alloc_worldN`. -/
theorem alloc_blockN {ρf : WRes} {ps : List FrameRec} {rs : List FrameRec} (v : Val) (ℓ : Nat) :
    ∀ (n k : Nat) {ρ σ : WRes} {μ : Heap}, ResU.Hash ρf ρ → ResU.CompS ρf ρ σ → TWNC σ ps rs →
      ResU.Lower σ μ → (∀ j, j < n → μ (ℓ + k + j) = none) →
      ∃ x σ' cells, sepRange (fun m => ptoOwn m v) (ℓ + k) n cells ∧ ResU.CompS ρ cells x ∧
        ResU.Hash ρf x ∧ ResU.CompS ρf x σ' ∧ TWNC σ' ps rs ∧
        ResU.Lower σ' (μ.fill (ℓ + k) n v) ∧ ResU.UpdV ρ x ∧ (∀ a, AgW σ' a → AgW σ a)
  | 0, k, ρ, σ, μ, hf, hσ, hT, hμ, _ => by
      refine ⟨ρ, σ, PMap.empty, ⟨rfl, trivial⟩, ResU.comp_empty_right ρ, hf, hσ, hT, ?_,
        (ResU.updV_self_iff ρ).mpr (hash_valid hf).2, fun _ h => h⟩
      rw [fill_zero]; exact hμ
  | n + 1, k, ρ, σ, μ, hf, hσ, hT, hμ, hfr => by
      obtain ⟨x₁, σ₁, hx₁, hf₁, hσ₁, hT₁, hμ₁, hu₁, hag₁⟩ :=
        alloc_worldN v hf hσ hT hμ (by simpa using hfr 0 (Nat.succ_pos n))
      obtain ⟨x, σ', cells, hcells, hx, hf', hσ', hT', hμ', hu, hag⟩ :=
        alloc_blockN v ℓ n (k + 1) hf₁ hσ₁ hT₁ hμ₁ (fun j hj => by
          rw [BoCa.BoLo.Heap.upd_other (by lomega)]
          have := hfr (j + 1) (by lomega)
          rwa [show ℓ + k + (j + 1) = ℓ + (k + 1) + j by lomega] at this)
      obtain ⟨bc, hbc, hρx⟩ := compS_reassoc hx₁ hx
      refine ⟨x, σ', bc, ⟨_, cells, hbc, rfl, ?_⟩, hρx, hf', hσ', hT', ?_, hu₁.trans hu,
        fun a ha => hag₁ a (hag a ha)⟩
      · rwa [show ℓ + k + 1 = ℓ + (k + 1) by omega]
      · rw [← fill_succ]; rwa [show ℓ + k + 1 = ℓ + (k + 1) by omega]

/-- `tab`'s head steps: the block at a location the memory does not hold, then `tabFill`. -/
theorem head_tab_inv {μ μ' : Heap} {c : UInt32} {f : Val} {a' : Expr}
    (h : Head (ℍ := ℍ) μ (.app (.val (.prim .tab)) (.val (Val.pair (Val.i32 c) f))) μ' a') :
    ∃ ℓ, (∀ i, i < (arrLen c).toNat → μ (ℓ + i) = none) ∧
      μ' = μ.fill ℓ (arrLen c).toNat .unit ∧ a' = tabFill f ℓ (arrLen c) 0 (arrLen c).toNat := by
  generalize hb : Expr.app (.val (.prim .tab)) (.val (Val.pair (Val.i32 c) f)) = b at h
  cases h with
  | tab c' f' ℓ hℓ =>
      simp only [Expr.app.injEq, true_and] at hb
      obtain ⟨h₁, rfl⟩ := Val.pair_inj' (Subtype.ext hb)
      obtain rfl : c = c' := by
        have := congrArg Subtype.val h₁
        simpa [Val.i32, Val.prim, Expr.val] using this
      exact ⟨ℓ, hℓ, rfl, rfl⟩
  | _ => simp_all [hndE, ubindE, ccatchE, cfinE, Expr.val, Val.prim]

/-- **The `tab` step at the step index** (Core's `wpTS_tab`): one allocating head step to `tabFill`,
at a block the memory does not hold; the run after it is the continuation's, from the world after
the block (`alloc_blockN`), at the index the step leaves. -/
theorem rwpG_tab {Φ : LocFam} (hΦ : Φ.Down) {Q : PostG} {n : Nat} {ls : List SRec} {c : UInt32}
    {f : Val} {ρ : WRes}
    (h : ∀ (ℓ : Loc) (cells x : WRes),
      sepRange (fun m => ptoOwn m .unit) ℓ (arrLen c).toNat cells → ResU.CompS ρ cells x →
      rwpG (ℍ := ℍ) Φ Q n ls (tabFill f ℓ (arrLen c) 0 (arrLen c).toNat) x) :
    rwpG (ℍ := ℍ) Φ Q (n + 1) ls (.app (.val (.prim .tab)) (.val (Val.pair (Val.i32 c) f))) ρ := by
  intro ρf fρ ps μ hf hc hT htg hI hl hfd j μ' E hj hrun hfin
  have hred : Head (ℍ := ℍ) (fun _ => none)
      (.app (.val (.prim .tab)) (.val (Val.pair (Val.i32 c) f))) _ _ :=
    Head.tab (fun _ => none) c f 0 (fun _ _ => rfl)
  cases hrun with
  | refl =>
      obtain ⟨ℓ₀, hℓ₀⟩ := BoLo.finDom_block hfd
      exact (hfin _ _ ⟨Kont.hole, _, _, rfl, rfl, Head.tab μ c f ℓ₀ (fun i _ => hℓ₀ i)⟩).elim
  | @more j' _ μ₁ _ _ e₁ _ hs t =>
      obtain ⟨ℓ, hfree, rfl, rfl⟩ := head_tab_inv (step1_head hred hs)
      obtain ⟨x, σ', cells, hcells, hx, hf', hσ', hT', hμ', hu, hag⟩ :=
        alloc_blockN .unit ℓ (arrLen c).toNat 0 hf hc hT hl (fun j hj => by simpa using hfree j hj)
      simp only [Nat.add_zero] at hcells hμ'
      obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
        h₁₃⟩ := h ℓ cells x hcells hx ρf σ' ps _ hf' hσ' hT' (tagged_of_ag hag htg) hI hμ'
          (finDom_fill hfd _ _ _) j' μ' E (by omega) t hfin
      rw [show n + 1 - (j' + 1) = n - j' by omega]
      exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆,
        UpdVN.trans hΦ le_rfl (updVN_of_updV Φ _ hu) h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃⟩

/-- **The `tab` step at `erwp`**: `rwpG_tab` at `erwp`'s postcondition. -/
theorem erwp_tab {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hL : Tb.Local) {Q : PostN} {n : Nat}
    {ls : List SRec} {c : UInt32} {f : Val} {ρ : WRes}
    (h : ∀ (ℓ : Loc) (cells x : WRes),
      sepRange (fun m => ptoOwn m .unit) ℓ (arrLen c).toNat cells → ResU.CompS ρ cells x →
      erwp (ℍ := ℍ) Φ Tb Q n ls (tabFill f ℓ (arrLen c) 0 (arrLen c).toNat) x) :
    erwp (ℍ := ℍ) Φ Tb Q (n + 1) ls (.app (.val (.prim .tab)) (.val (Val.pair (Val.i32 c) f))) ρ :=
  erwp_fold_at hL le_rfl (rwpG_tab hΦ fun ℓ cells x hcells hx =>
    erwp_unfold_at hL (Nat.le_succ n) (h ℓ cells x hcells hx))

/-- A block of `own` cells is consistent with every view. -/
theorem consistentX_sepRange_own (c : Loc → Option Life) (v : Val) :
    ∀ (n : Nat) (ℓ : Loc) {ρ : WRes}, sepRange (fun m => ptoOwn m v) ℓ n ρ → ConsistentX c ρ
  | 0, _, _, ⟨rfl, _⟩ => consistentX_empty c
  | n + 1, ℓ, _, ⟨_, _, hc, rfl, hr⟩ =>
      consistentX_compS hc (Goal791N.consistentX_single_own c ℓ v)
        (consistentX_sepRange_own c v n (ℓ + 1) hr)

namespace Goal791N
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

end Goal791N

end BoCa.Fig16.LogRel.Core.Chain.SI

end

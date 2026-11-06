import Core.Chain.FamSwap836N
import Core.EffCancelRuns

/-!
# `array_new` at `SemJN`  `[spec §9]`

Core's `arrNew_compatX` (`Core/Arrays.lean`) is the `tab` step (`wpTS_tab`, `Core/ArrayWp.lean`)
then the fill (`tabFill_wp`). On the chain:

* `alloc_worldN`/`alloc_blockN` are Core's `alloc_world`/`alloc_block` at the chain's typed world
  `TWNC` (`TWNC.alloc` for `TW.alloc`): `n` cells at a block the memory does not hold.
* `rwpG_tab` is `wpTS_tab` at the step index: the `tab` step is one allocating head step to a
  term that is not a value, so the run after it is the continuation's run from the world
  `alloc_blockN` builds, the index paying for the step; `erwp_tab` is the same at `erwp`.
* `tabFill_wpN` is `tabFill_wp`, by Core's induction: `bang_app` for the call of the
  `!`-function, `erwp_bind_frame` for Core's `wpTS_bind_frame`, `rwp_store`, and the `1↦` step.
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

/-- **The fill** (Core's `tabFill_wp`): with the cells `ℓ, …, ℓ + i − 1` filled and
`ℓ + i, …, ℓ + i + k − 1` holding `()`, the rest of `tabFill` runs to the array, at every index
below the `!`-function's; by induction on `k`. -/
theorem tabFill_wpN {A : VTy} {δ : LSub} {Θ : LocTy} (hΘ : Θ.OK) {M : Nat} (f : Val) (l : Loc)
    (N : UInt32) (hN31 : N.toNat < 2 ^ 31)
    (hf : vN (ℍ := ℍ) (.bang (.lolli (.int .w32) A)) δ Θ M f PMap.empty) :
    ∀ (k i m : Nat) (ls : List SRec) (ρd ρt ρ : WRes) (c : Loc → Option Life), m ≤ M →
      ConsistentX c ρ → i + k = N.toNat →
      sepRange (fun x => vN (ℍ := ℍ) (.ref A) δ Θ m (Val.loc x)) l i ρd →
      sepRange (fun m => ptoOwn m .unit) (l + i) k ρt → ResU.CompS ρd ρt ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty)
        (fun k _ v ρ => vN (ℍ := ℍ) (.array A) δ Θ k v ρ) m ls (tabFill f l N i k) ρ
  | 0, i, m, ls, ρd, ρt, ρ, c, _, _, hN, hd, ht, hc => by
      obtain ⟨rfl, -⟩ := ht
      rw [ResU.CompS.functional hc (ResU.comp_empty_right ρd)]
      refine erwp_val (v := Val.arr l N) (vN_fam_mk hN31 ?_)
      rw [← hN]; exact hd
  | k + 1, i, m, ls, ρd, ρt, ρ, c, hm, hcon, hN, hd, ⟨cl, ρt', hct, hcl, ht'⟩, hc => by
      have hΦ := LocTy.view_down hΘ.1 c
      show erwp (ℍ := ℍ) _ _ _ m ls
        ((Kont.seq (.appR (.app (.val (.prim .store)) (.val (.loc (l + i)))) .hole)
          (tabFill f l N (i + 1) k)).plug (.app (.val f) (.val (Val.i32 (UInt32.ofNat i))))) ρ
      -- `ρ = cell ● (ρd ● ρt')`
      obtain ⟨R, hR, hρ⟩ := compS_lcomm hct hc
      refine erwp_bind_frame hΦ (opTableN_local _) _
        (fun σ => ∃ σc σr, ResU.CompS σc σr σ ∧ ptoOwn (l + i) .unit σc ∧ ∃ σd σt,
          ResU.CompS σd σt σr ∧
          sepRange (fun x => vN (ℍ := ℍ) (.ref A) δ Θ m (Val.loc x)) l i σd ∧
          sepRange (fun m => ptoOwn m .unit) (l + i + 1) k σt)
        (compS_empty_left ρ) hcon
        (bang_app hΘ hm hf (consistentX_empty c) (k := m) ⟨⟨_, rfl⟩, rfl⟩ ls)
        ⟨cl, R, hρ, hcl, ρd, ρt', hR, hd, ht'⟩ ?_
      intro k' hk' ls' w σw σr σ hσ hw ⟨c', R', hR', hc', σd, σt, hdt, hd', ht''⟩ hcσ hvσ
      obtain rfl := hc'
      simp only [Kont.plug]
      -- `σ = cell ● (σw ● R')`
      obtain ⟨G, hG, hσG⟩ := compS_lcomm hR' hσ
      refine erwp_bindR hΦ (opTableN_local _) (.seq .hole (tabFill f l N (i + 1) k)) ?_
      refine rwp_store ls' (l + i) .unit w _ ⟨_, G, hσG, rfl, fun c₃ σ₃ hc₃ hcomp₃ => ?_⟩
      obtain rfl := hc₃
      simp only [Kont.plug]
      refine erwp_det hΦ (opTableN_down OpTabN.empty_down)
        (fun k _ v ρ h => vN_down _ δ Θ k v ρ h)
        (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
      -- the new leaf `σw ● cell`, beside the filled cells and the rest of the placeholders
      obtain ⟨L, hL, hσ₃⟩ := compS_exch hG hcomp₃
      obtain ⟨Md, hMd, hσ₃'⟩ := compS_lcomm hdt hσ₃
      obtain ⟨D, hD, hσ₃''⟩ := compS_reassoc' hMd hσ₃'
      have hvG : ResU.Valid G := (ResU.Valid.split hσG hvσ).2
      have hcG : ConsistentX c G := consistentX_right hσG hcσ hvσ
      have hvR' : ResU.Valid R' := (ResU.Valid.split hG hvG).2
      have hcR' : ConsistentX c R' := consistentX_right hG hcG hvG
      have hcw : ConsistentX c σw := consistentX_left hG hcG hvG
      have hcL : ConsistentX c L :=
        consistentX_compS (ResU.CompS.comm hL) (consistentX_single_own c (l + i) w) hcw
      have hc₃ : ConsistentX c σ₃ := consistentX_compS hσ₃ hcL hcR'
      have hleaf : vN (ℍ := ℍ) (.ref A) δ Θ (k' - 1) (Val.loc (l + i)) L :=
        ⟨l + i, w, σw, rfl, ResU.CompS.comm hL, vN_le (by omega) hw⟩
      refine tabFill_wpN hΘ f l N hN31 hf k (i + 1) (k' - 1) ls' D σt σ₃ c (by omega) hc₃
        (by rw [← hN]; ring) (sepRange_append hD
          (sepRange_mono' (fun _ _ h => vN_le (by omega) h) hd')
          ⟨L, PMap.empty, ResU.comp_empty_right L, hleaf, ⟨rfl, trivial⟩⟩) ?_ hσ₃''
      rwa [show l + i + 1 = l + (i + 1) by ring] at ht''

/-- **`array_new` at `SemJN`** (Core's `arrNew_compatX`): the `tab` step (`erwp_tab`), then the
fill from no filled cell (`tabFill_wpN`). -/
theorem arrNew_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.prim .tab)) (.val (arrNewTy A)) := by
  refine sem_constN hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp] at hcon ⊢
  obtain ⟨v₁, f, σ₁, σ₂, rfl, hc, ⟨⟨cn, rfl⟩, rfl⟩, hf⟩ := hv
  obtain rfl : σ₂ = PMap.empty := hf.1
  cases eq_empty_of_compS_empty hc
  have hΦ := LocTy.view_down hΘ'.1 c''
  rcases k with _ | k
  · exact erwp_zero
  refine erwp_tab hΦ (opTableN_local _) fun ℓ cells x hcells hx => ?_
  rw [eq_of_compS_empty_left hx]
  exact tabFill_wpN hΘ' f ℓ (arrLen cn) (arrLen_bound cn) hf (arrLen cn).toNat 0 k ls'
    PMap.empty cells cells c'' (Nat.le_succ k)
    (consistentX_sepRange_own c'' .unit _ ℓ hcells) (by simp) ⟨rfl, trivial⟩
    (by simpa using hcells) (compS_empty_left cells)

end Goal791N

end BoCa.Fig16.LogRel.Core.Chain.SI

end

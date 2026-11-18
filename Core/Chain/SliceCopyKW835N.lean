import Core.Chain.FamOpsKW835N
import Core.Chain.SI.HandleN
import Core.Demonic

/-!
# `slice_copy_mut` at the typed world  `[spec §74]`

Core's `sliceCopyM_compatX` (`Core/SliceCopy.lean`) at `SemJN`, step for step:

* the destination's leaves `[di, di + len)` are opened one by one by Mut Anti-Frame at the step
  index (`rwp_M_antiFrameRange`, `len` of `rwp_M_antiFrame`), each leaf's lifetime read off the
  consistent view, each payload at `∅` (`vN_empty_of_persistent`);
* the source's leaves are `imm` cells whose values the memory holds; at a persistent `A` the
  observable payload is the relation's at `∅` (`vO_vN_of_persistent`);
* the step writes each opened cell (`rwp_copy`, `store_block` at `TWNC`), and the sealed cell
  holds the source's value at `∅`, at the index the step leaves;
* out of range the memory is unchanged (`rwp_copy_out`).

The source family holds no `own` cell and is given up after the step (`rwp_garbage`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont Head copyHeap)

/-! ### The observable payload at a persistent type -/

/-- At a persistent type the observable view is the relation (Core's `vC_true_of_persistent`).
`[spec §74]` -/
theorem vO_vN_of_persistent {A : VTy} (hA : A.Persistent) {δ : LSub} {Θ : LocTy} {n : Nat}
    {v : Val} {ρ : WRes} (h : vBN (ℍ := ℍ) none false A δ Θ n v ρ) :
    vN (ℍ := ℍ) A δ Θ n v ρ := by
  refine vN_ind δ (fun _ T Θ n v ρ => T.Persistent → vBN (ℍ := ℍ) none true T δ Θ n v ρ) ?_
    false A Θ n v ρ h hA
  intro b T Θ n v ρ h hp
  refine (vFN_vN δ true T Θ n v ρ).mpr ?_
  cases T with
  | unit => exact h
  | int _ => exact h
  | zero => exact h.elim
  | unk => exact h
  | tvar _ => exact h.elim
  | bang _ => exact ⟨h.1, h.2.1⟩
  | tensor T₁ T₂ =>
      simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true] at hp
      obtain ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, h₃, h₄⟩ := h
      exact ⟨v₁, v₂, ρ₁, ρ₂, h₁, h₂, h₃.2 hp.1, h₄.2 hp.2⟩
  | sum T₁ T₂ =>
      simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true] at hp
      rcases h with ⟨v₁, h₁, h₂⟩ | ⟨v₂, h₁, h₂⟩
      · exact .inl ⟨v₁, h₁, h₂.2 hp.1⟩
      · exact .inr ⟨v₂, h₁, h₂.2 hp.2⟩
  | box _ T =>
      obtain ⟨α, hα, hb, hs⟩ := h
      exact ⟨α, hα, hb.2 hp, hs⟩
  | mu T =>
      exact ⟨h.1, h.2.1, h.2.2.2 (by
        show (VTy.inst (.mu T) T).persistent = true
        rw [persistent_inst_mu]; exact hp)⟩
  | opq _ => simp [VTy.Persistent, VTy.persistent] at hp
  | thunk _ => simp [VTy.Persistent, VTy.persistent] at hp
  | code _ _ _ => simp [VTy.Persistent, VTy.persistent] at hp
  | ref _ => simp [VTy.Persistent, VTy.persistent] at hp
  | imm _ _ => simp [VTy.Persistent, VTy.persistent] at hp
  | «mut» _ _ => simp [VTy.Persistent, VTy.persistent] at hp
  | fam _ => simp [VTy.Persistent, VTy.persistent] at hp

/-- A leaf of `[Imm @b A]` at a persistent `A`: one `imm` cell, its value in the relation at `∅`.
`[spec §74]` -/
theorem vN_imm_leaf_val {b : Lifetime.Life} {A : VTy} (hA : A.Persistent) {δ : LSub}
    {Θ : LocTy} {n : Nat} {m : Loc} {ρ : WRes}
    (h : vN (ℍ := ℍ) (.imm b A) δ Θ n (Val.loc m) ρ) :
    (∃ ψ, ρ.get m = some ψ ∧ vN (ℍ := ℍ) A δ Θ n ψ.erase PMap.empty) ∧ NoOwn ρ := by
  obtain ⟨α, -, ⟨l, s, u, σ, hs, hl, rfl, -, hP⟩, -⟩ := h
  obtain rfl : m = l := loc_inj hl
  have hv : vN (ℍ := ℍ) A δ Θ n u σ := vO_vN_of_persistent hA hP
  have h0 : σ = PMap.empty := vN_empty_of_persistent A hA hv
  subst h0
  exact ⟨⟨_, ResU.single_get_self _ _, hv⟩, ResU.restrict_single_other (by simp)⟩

/-- The values of `n` leaves of `[Imm @b A]` from `ℓ`, at a persistent `A` (Core's
`immRange_vals`).  `[spec §74]` -/
theorem immRange_valsN {b : Lifetime.Life} {A : VTy} (hA : A.Persistent) {δ : LSub}
    {Θ : LocTy} {k : Nat} {ℓ : Loc} {n : Nat} {ρ : WRes}
    (h : sepRange (fun m => vN (ℍ := ℍ) (.imm b A) δ Θ k (Val.loc m)) ℓ n ρ) :
    ∃ u : Nat → Val, ∀ j, j < n →
      (∃ ψ, ρ.get (ℓ + j) = some ψ ∧ ψ.erase = u j) ∧ vN (ℍ := ℍ) A δ Θ k (u j) PMap.empty := by
  have hx : ∀ j, ∃ u : Val, j < n →
      (∃ ψ, ρ.get (ℓ + j) = some ψ ∧ ψ.erase = u) ∧ vN (ℍ := ℍ) A δ Θ k u PMap.empty := by
    intro j
    by_cases hj : j < n
    · obtain ⟨ρj, ρr, hc, hPj, -⟩ := sepRange_pick hj h
      obtain ⟨⟨ψ, hψ, hv⟩, -⟩ := vN_imm_leaf_val hA hPj
      obtain ⟨ψ', hψ', he⟩ := compS_get_erase hc hψ
      exact ⟨ψ.erase, fun _ => ⟨⟨ψ', hψ', he⟩, hv⟩⟩
    · exact ⟨.unit, fun hj' => absurd hj' hj⟩
  choose u hu using hx
  exact ⟨u, hu⟩

/-! ### The copy step at the step index -/

/-- A part of the postcondition with no `own` cell may be given up. -/
theorem rwp_garbage {Φ : LocFam} {Q : PostN} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : rwp (ℍ := ℍ) Φ (fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧ NoOwn ρ₂ ∧
      Q k ls' v ρ₁) n ls e ρ) :
    rwp (ℍ := ℍ) Φ Q n ls e ρ := by
  rw [rwp_iff_rwpG] at h ⊢
  exact rwpG_garbage (rwpG_mono (fun _ _ _ _ ⟨v, hv, ρ₁, ρ₂, hc, hno, hq⟩ =>
    ⟨ρ₁, ρ₂, hc, hno, v, hv, hq⟩) h)

/-- The copy step at a memory holding every cell. -/
theorem head_copy_any (ℓd : Loc) (nd di : UInt32) (ℓs : Loc) (ns si len : UInt32) :
    Head (ℍ := ℍ) (fun _ => some Val.unit)
      (.app (.val (.prim .sliceCopy)) (.val (copyArg ℓd nd di ℓs ns si len)))
      (copyHeap (fun _ => some Val.unit) ℓd nd di ℓs ns si len)
      (.val (copyAns ℓd nd di ns si len)) :=
  Head.sliceCopy _ ℓd nd di ℓs ns si len fun _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩

/-- **The `sliceCopy` step in range, at the step index** (Core's `wpTS_copy`).  `[spec §74]` -/
theorem rwp_copy {Φ : LocFam} {ls : List SRec} {ℓd : Loc} {nd di : UInt32} {ℓs : Loc}
    {ns si len : UInt32} (hok : copyOk nd di ns si len = true) (u : Nat → Val)
    {ρd ρs R X ρ : WRes}
    (hd : sepRange (fun l => ex fun v => ptoOwn l v) (ℓd + di.toNat) len.toNat ρd)
    (hs : ∀ j, j < len.toNat → ∃ ψ, ρs.get (ℓs + si.toNat + j) = some ψ ∧ ψ.erase = u j)
    (hX : ResU.CompS ρs R X) (hρ : ResU.CompS ρd X ρ) (Q : PostN) {n : Nat}
    (hQ : ∀ ρd' x, sepRange (fun l => ptoOwn l (u (l - (ℓd + di.toNat)))) (ℓd + di.toNat)
        len.toNat ρd' → ResU.CompS ρd' X x → Q (n - 1) ls (copyAns ℓd nd di ns si len) x) :
    rwp (ℍ := ℍ) Φ Q n ls
      (.app (.val (.prim .sliceCopy)) (.val (copyArg ℓd nd di ℓs ns si len))) ρ := by
  refine rwp_head1 (head_copy_any ℓd nd di ℓs ns si len)
    (fun ρf fρ ps μ hf hc hT htg hμ _ => ?_)
  have hsrc : ∀ j, j < len.toNat → μ (ℓs + si.toNat + j) = some (u j) := by
    intro j hj
    obtain ⟨ψ, hψ, he⟩ := hs j hj
    obtain ⟨ψ₁, hψ₁, he₁⟩ := compS_get_erase hX hψ
    obtain ⟨ψ₂, hψ₂, he₂⟩ := compS_get_erase (ResU.CompS.comm hρ) hψ₁
    obtain ⟨ψ₃, hψ₃, he₃⟩ := compS_get_erase (ResU.CompS.comm hc) hψ₂
    rw [lower_get hμ hψ₃, he₃, he₂, he₁, he]
  obtain ⟨ρd', x, σ', hd', hx, hf', hσ', hT', hμ', hu, hag, hrange⟩ :=
    store_block (Tw := fun W => TWNC W ps (rsOf ls)) (fun hT h₁ h₂ hv => TWNC.store hT h₁ h₂ hv)
      (fun l => u (l - (ℓd + di.toNat))) len.toNat (ℓd + di.toNat) hd hρ hf hc hT hμ
  have hheap : copyHeap μ ℓd nd di ℓs ns si len =
      writeRange μ (ℓd + di.toNat) len.toNat (fun l => u (l - (ℓd + di.toNat))) := by
    unfold copyHeap
    rw [if_pos hok]
    funext k
    simp only [BoCa.BoLo.Heap.copy, writeRange]
    split
    · rename_i hk
      exact hsrc _ (by lomega)
    · rfl
  have hstep : Head (ℍ := ℍ) μ
      (.app (.val (.prim .sliceCopy)) (.val (copyArg ℓd nd di ℓs ns si len)))
      (copyHeap μ ℓd nd di ℓs ns si len) (.val (copyAns ℓd nd di ns si len)) :=
    Head.sliceCopy μ ℓd nd di ℓs ns si len fun _ =>
      ⟨hrange, fun j hj => by rw [hsrc j hj]; simp⟩
  refine ⟨⟨_, _, hstep⟩, fun μ₁ e₁ hh => ?_⟩
  obtain ⟨rfl, rfl⟩ := head_det hstep rfl hh rfl
  refine ⟨copyAns ℓd nd di ns si len, rfl, x, PMap.empty, σ', σ', x, ps, ls,
    ResU.hash_symm hf', hσ', ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hf' hσ')),
    ResU.comp_empty_right σ', ?_, ResU.comp_empty_right x, updVN_of_updV Φ _ hu, noOwn_empty,
    hT', tagged_of_ag hag htg, fun _ => Iff.rfl, fun _ => Iff.rfl, hQ ρd' x hd' hx⟩
  rw [hheap]; exact hμ'

/-- **The `sliceCopy` step out of range, at the step index**: nothing is written.  `[spec §74]` -/
theorem rwp_copy_out {Φ : LocFam} {ls : List SRec} {ℓd : Loc} {nd di : UInt32} {ℓs : Loc}
    {ns si len : UInt32} (hok : copyOk nd di ns si len = false) (Q : PostN) {n : Nat} {ρ : WRes}
    (hQ : Q (n - 1) ls (copyAns ℓd nd di ns si len) ρ) :
    rwp (ℍ := ℍ) Φ Q n ls
      (.app (.val (.prim .sliceCopy)) (.val (copyArg ℓd nd di ℓs ns si len))) ρ := by
  refine rwp_head1 (head_copy_any ℓd nd di ℓs ns si len)
    (fun ρf σ ps μ hf hσ hT htg hμ _ => ?_)
  have hstep : Head (ℍ := ℍ) μ
      (.app (.val (.prim .sliceCopy)) (.val (copyArg ℓd nd di ℓs ns si len)))
      (copyHeap μ ℓd nd di ℓs ns si len) (.val (copyAns ℓd nd di ns si len)) :=
    Head.sliceCopy μ ℓd nd di ℓs ns si len fun h => absurd h (by simp [hok])
  have hheap : copyHeap μ ℓd nd di ℓs ns si len = μ := by simp [copyHeap, hok]
  refine ⟨⟨_, _, hstep⟩, fun μ₁ e₁ hh => ?_⟩
  obtain ⟨rfl, rfl⟩ := head_det hstep rfl hh rfl
  rw [hheap]
  exact ⟨copyAns ℓd nd di ns si len, rfl, ρ, PMap.empty, σ, σ, ρ, ps, ls,
    ResU.hash_symm hf, hσ,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hf hσ)),
    ResU.comp_empty_right σ, hμ, ResU.comp_empty_right ρ,
    UpdVN.refl Φ _ (hash_valid hf).2, noOwn_empty, hT, htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, hQ⟩

/-! ### Mut Anti-Frame over a range of leaves, at the step index -/

/-- After a run with `len` leaves from `m` opened (Core's `openPost`): each cell holds a value in
the relation at `∅`, and the leaves given back at the index left yield `Q`. -/
def openPostN (A : VTy) (δ : LSub) (Θ : LocTy) (a : Lifetime.Life) (m : Loc) (len : Nat)
    (Q : PostN) : PostN :=
  fun k ls v ρ => ∃ ρo W, ResU.CompS ρo W ρ ∧
    sepRange (fun l r => ∃ w, r = ResU.single l (CellU.ownOf w) ∧
      vN (ℍ := ℍ) A δ Θ k w PMap.empty) m len ρo ∧
    ∀ M Z, sepRange (fun l => vN (ℍ := ℍ) (.mut a A) δ Θ k (Val.loc l)) m len M →
      ResU.CompS W M Z → Q k ls v Z

/-- **Mut Anti-Frame at `len` leaves of `[Mut @a A]`**, `A` persistent, at the step index (Core's
`wpTS_M_antiFrameRange`): `len` of `rwp_M_antiFrame`, each leaf's lifetime read off the view.
`[spec §74]` -/
theorem rwp_M_antiFrameRange {a : Lifetime.Life} {A : VTy} {δ : LSub} (hA : A.Persistent)
    {Θ : LocTy} {c : Loc → Option Life} (hΦ : (Θ.view c).Down) (e : Expr) (ls : List SRec)
    (n : Nat) :
    ∀ (len : Nat) (m : Loc) (Q : PostN) {ρm ρr ρ : WRes},
      sepRange (fun l => vN (ℍ := ℍ) (.mut a A) δ Θ n (Val.loc l)) m len ρm →
      (∀ l ψ, ρm.get l = some ψ → ψ.kind = Kind.mut → c l = some ψ.at) →
      ResU.CompS ρm ρr ρ →
      (∀ ρo X, sepRange (fun l => ex fun w => ptoOwn l w) m len ρo → ResU.CompS ρo ρr X →
        rwp (ℍ := ℍ) (Θ.view c) (openPostN (ℍ := ℍ) A δ Θ a m len Q) n ls e X) →
      rwp (ℍ := ℍ) (Θ.view c) Q n ls e ρ
  | 0, m, Q, ρm, ρr, ρ, hm, _, hρ, H => by
      obtain ⟨rfl, -⟩ := hm
      rw [eq_of_compS_empty_left hρ]
      refine rwp_mono (fun k ls' v R hR => ?_)
        (H PMap.empty ρr ⟨rfl, trivial⟩ (compS_empty_left ρr))
      obtain ⟨O, W, hOW, ⟨rfl, -⟩, hW⟩ := hR
      rw [eq_of_compS_empty_left hOW]
      exact hW PMap.empty W ⟨rfl, trivial⟩ (ResU.comp_empty_right W)
  | len + 1, m, Q, ρm, ρr, ρ, ⟨ρ1, ρm2, h12, hleaf, hrest⟩, hview, hρ, H => by
      obtain ⟨F, hF, hρ1F⟩ := compS_reassoc h12 hρ
      obtain ⟨α₀, hα₀, b, hα₀b, hm₁, hunif⟩ := hleaf
      obtain ⟨l', w₀, σ₀, hσ₀, j₀, hw₀, -, hl', hlΘ, rfl⟩ := hm₁
      obtain rfl : m = l' := loc_inj hl'
      have hcb : c m = some b := by
        have h := hview m _ (ResU.CompS.get_left_of_ne_imm h12 (ResU.single_get_self _ _)
          (by rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c)).2
          (CellU.kind_mutOf _ _ _ _ _ _)
        rwa [CellU.at_mutOf] at h
      have hσ0 : σ₀ = PMap.empty := vN_empty_of_persistent A hA hw₀
      subst hσ0
      refine rwp_M_antiFrame hΦ (LocTy.view_some hcb hlΘ) hρ1F (fun W X hW hX => ?_)
      have hW0 := eq_of_compS_empty_left hW
      subst hW0
      obtain ⟨bc, hbc, hX'⟩ := compS_reassoc hF hX
      refine rwp_M_antiFrameRange hA hΦ e ls n len (m + 1) _ hrest
        (fun l ψ hg hk => hview l ψ (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm h12) hg
          (by rw [hk]; exact fun c => Kind.noConfusion c)).2 hk) hX' fun ρo X' hρo hX'' => ?_
      obtain ⟨ab, hab, habX⟩ := compS_reassoc' (ResU.CompS.comm hbc) hX''
      refine rwp_mono (fun k ls' v R hR => ?_)
        (H ab X' ⟨_, ρo, ResU.CompS.comm hab, ⟨w₀, rfl⟩, hρo⟩ habX)
      obtain ⟨O, W2, hOW, ⟨O1, O2, hO12, ⟨w, rfl, hvw⟩, hO2⟩, hW2⟩ := hR
      obtain ⟨W', hW', hR'⟩ := compS_exch hO12 hOW
      refine ⟨O2, W', ResU.CompS.comm hR', hO2, fun M Z hM hZ => ?_⟩
      obtain ⟨WM, hWM, hZ'⟩ := compS_reassoc hW' hZ
      have hs0 := stratum_empty b
      have hw' : famL b (fun Θ₀ j u r => vN (ℍ := ℍ) A δ Θ₀ j u r) Θ k w ⟨PMap.empty, hs0⟩ :=
        (vN_above A δ Θ hs0).mpr hvw
      refine ⟨w, PMap.empty, hs0, hw', WM, WM, hZ', compS_empty_left WM, fun X₀ hX₀ => ?_⟩
      obtain ⟨bc', hbc', hX₀'⟩ := compS_reassoc hWM hX₀
      have hleaf' : vN (ℍ := ℍ) (.mut a A) δ Θ k (Val.loc m)
          (ResU.single m (CellU.mutOf b w PMap.empty hs0
            (famL b (fun Θ₀ j u r => vN (ℍ := ℍ) A δ Θ₀ j u r) Θ k) hw')) :=
        ⟨α₀, hα₀, b, hα₀b, ⟨m, w, PMap.empty, hs0, k, hw', le_rfl, rfl, hlΘ, rfl⟩, hunif⟩
      exact hW2 bc' X₀ ⟨_, M, ResU.CompS.comm hbc', hleaf', hM⟩ hX₀'

/-! ### `slice_copy_mut` -/

/-- **`slice_copy_mut` at `SemJN`** (Core's `sliceCopyM_compatX`).  `[spec §74]` -/
theorem sliceCopyM_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a b : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) (hA : A.Persistent) :
    SemJN (ℍ := ℍ) Δ Γ (.val sliceCopyV) (.val (sliceCopyMTy a b A)) := by
  refine sem_constN hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp] at hcon ⊢
  obtain ⟨v₁, v₂, σ₁, σ₂, rfl, hc, ⟨ℓd, nd, rfl, hnd, hsd⟩, w₁, x, ρ₀, σx, rfl, hc₂,
    ⟨⟨di, rfl⟩, rfl⟩, hx⟩ := hv
  rw [eq_of_compS_empty_left hc₂] at hc
  obtain ⟨x₁, x₂, σs, σ₃, rfl, hc₃, ⟨ℓs, ns, rfl, -, hss⟩, y₁, y₂, ρ₁, ρ₂, rfl, hc₄,
    ⟨⟨si, rfl⟩, rfl⟩, ⟨⟨len, rfl⟩, rfl⟩⟩ := hx
  rw [eq_of_compS_empty_left hc₄] at hc₃
  rw [ResU.CompS.functional hc₃ (ResU.comp_empty_right σs)] at hc
  have hΦ := LocTy.view_down hΘ'.1 c''
  have hσs : NoOwn σs := sepRange_closed noOwn_empty
    (fun _ _ _ hc h₁ h₂ => noOwn_compS hc h₁ h₂) (fun _ _ h => (vN_imm_leaf_val hA h).2) hss
  have hle : ∀ {T : VTy} {m : Loc} {ρ : WRes}, vN (ℍ := ℍ) T δ Θ' k (Val.loc m) ρ →
      vN (ℍ := ℍ) T δ Θ' (k - 1) (Val.loc m) ρ := fun h => vN_le (Nat.sub_le k 1) h
  refine cN_ret_of ?_
  refine erwp_of_valid fun hvσ => ?_
  refine erwp_of_rwp ?_
  change rwp (ℍ := ℍ) (Θ'.view c'') _ k ls'
    (.app (.val (.prim .sliceCopy)) (.val (copyArg ℓd nd di ℓs ns si len))) σ
  refine rwp_garbage ?_
  by_cases hok : copyOk nd di ns si len = true
  swap
  · -- out of range: nothing is written, and the family is handed back
    have hok' : copyOk nd di ns si len = false := by simpa using hok
    refine rwp_copy_out hok' _ ⟨σ₁, σs, hc, hσs, ?_⟩
    rw [show copyAns ℓd nd di ns si len = Val.pair (Val.arr ℓd nd) (Val.inj₁ Val.unit) by
      simp [copyAns, hok']]
    exact ⟨_, _, σ₁, PMap.empty, rfl, ResU.comp_empty_right σ₁,
      vN_fam_mk hnd (sepRange_mono' (fun _ _ h => hle h) hsd), .inl ⟨Val.unit, rfl, rfl, rfl⟩⟩
  -- in range
  obtain ⟨hdl, hsl⟩ := copyOk_bounds hok
  have hnd' : nd.toNat = di.toNat + (len.toNat + (nd.toNat - di.toNat - len.toNat)) := by omega
  rw [hnd'] at hsd
  obtain ⟨D1, D23, hD, hD1, hD23⟩ := sepRange_split hsd
  obtain ⟨Dm, D3, hDm3, hDm, hD3⟩ := sepRange_split hD23
  have hns' : ns.toNat = si.toNat + (len.toNat + (ns.toNat - si.toNat - len.toNat)) := by omega
  rw [hns'] at hss
  obtain ⟨S1, S23, hS, -, hS23⟩ := sepRange_split hss
  obtain ⟨Sm, S3, hSm3, hSm, -⟩ := sepRange_split hS23
  obtain ⟨u, hu⟩ := immRange_valsN hA hSm
  have hreads : ∀ j, j < len.toNat →
      ∃ ψ, σs.get (ℓs + si.toNat + j) = some ψ ∧ ψ.erase = u j := by
    intro j hj
    obtain ⟨⟨ψ, hψ, he⟩, -⟩ := hu j hj
    obtain ⟨ψ₁, hψ₁, he₁⟩ := compS_get_erase hSm3 hψ
    obtain ⟨ψ₂, hψ₂, he₂⟩ := compS_get_erase (ResU.CompS.comm hS) hψ₁
    exact ⟨ψ₂, hψ₂, he₂.trans (he₁.trans he)⟩
  -- each destination leaf's lifetime, read off the consistent view
  have hview : ∀ l ψ, Dm.get l = some ψ → ψ.kind = Kind.mut → c'' l = some ψ.at := by
    intro l ψ hg hk
    have hni : ψ.kind ≠ Kind.imm := by rw [hk]; exact fun c => Kind.noConfusion c
    have g₁ := (ResU.CompS.get_left_of_ne_imm hDm3 hg hni).2
    have g₂ := (ResU.CompS.get_left_of_ne_imm (ResU.CompS.comm hD) g₁ hni).2
    have g₃ := (ResU.CompS.get_left_of_ne_imm hc g₂ hni).2
    exact consistentX_get hcon hvσ g₃ hk
  -- `σ = Dm ● ((D1 ● D3) ● σs)`
  obtain ⟨D13, hD13, hDmσ₁⟩ := compS_lcomm hDm3 hD
  obtain ⟨Rr, hRr, hDmR⟩ := compS_reassoc hDmσ₁ hc
  refine rwp_M_antiFrameRange hA hΦ _ ls' k len.toNat (ℓd + di.toNat) _ hDm hview hDmR
    fun ρo X hρo hX => ?_
  refine rwp_copy hok u hρo hreads (ResU.CompS.comm hRr) hX _ fun ρd' y hd' hy => ?_
  rw [show copyAns ℓd nd di ns si len = Val.pair (Val.arr ℓd nd) (Val.inj₂ Val.unit) by
    simp [copyAns, hok]]
  refine ⟨ρd', Rr, hy, ?_, fun M Z hM hZ => ?_⟩
  · refine sepRange_mono (fun m hm hm' ρ hρ => ?_) ρd' hd'
    exact ⟨_, hρ, vN_le (Nat.sub_le k 1) (hu _ (by lomega)).2⟩
  · obtain ⟨ac, hac, hZ'⟩ := compS_exch hRr hZ
    refine ⟨ac, σs, hZ', hσs, ?_⟩
    obtain ⟨bc, hbc, hacD⟩ := compS_reassoc hD13 hac
    have h23 := sepRange_append (ResU.CompS.comm hbc) hM (sepRange_mono' (fun _ _ h => hle h) hD3)
    have hall := sepRange_append hacD (sepRange_mono' (fun _ _ h => hle h) hD1) h23
    rw [← hnd'] at hall
    exact ⟨_, _, ac, PMap.empty, rfl, ResU.comp_empty_right ac, vN_fam_mk hnd hall,
      .inr ⟨Val.unit, rfl, rfl, rfl⟩⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end

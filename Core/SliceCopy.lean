import Core.SliceOps
import Core.Persistent

/-!
# Core — `slice_copy_mut`  `[spec §74]`

    sliceCopyM : !(ArrayMut @a A ⊗ (I32 ⊗ (ArrayImm @b A ⊗ (I32 ⊗ I32))) ⇒ ArrayMut @a A ⊗ (1 ⊕ 1))

at a persistent `A`. The term is the machine's `sliceCopy` (`Head.sliceCopy`): one step that
checks the bounds and, in range, writes `dst[di + k] := src[si + k]` for every `k < len`,
answering `(dst, inj₂ ())`; out of range it writes nothing and answers `(dst, inj₁ ())`.

The compatibility lemma is `sliceReplaceM_compatX`'s argument over a range:

* the destination's leaves `[di, di + len)` are opened by Mut Anti-Frame one by one
  (`wpTS_M_antiFrameRange`), the rest of the family framed;
* the source's leaves `[si, si + len)` are `imm` cells, read in place: their values are what the
  memory holds there (`immRange_vals`), and at a persistent `A` the observable payload is the
  program's at `∅` (`vC_true_of_persistent`);
* the step writes each opened cell (`wpTS_copy`, `n` of `TW.store`, `store_block`); a persistent
  value owns no resource, so the payload handed back to each leaf is the source's value at `∅`.

The two ranges are disjoint because the destination's opened cells are `own` and the source's
are `imm` in one composite: an `own` cell excludes every other cell at its location.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Head Kont Step1N ARun copyHeap)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The observable payload at a persistent type -/

/-- At a persistent type the observable view is the program's relation.  `[spec §74, §10]` -/
theorem vC_true_of_persistent {A : VTy} (hA : A.Persistent) {ls : List SRec} {δ : LSub}
    {v : Val} {ρ : WRes} (h : vC false A ls δ v ρ) : vC true A ls δ v ρ := by
  refine vC_ind δ (fun _ T ls v ρ => T.Persistent → vC true T ls δ v ρ) ?_ false A ls v ρ h hA
  intro b T ls v ρ h hp
  cases T with
  | unit => exact h
  | int w => exact h
  | opq k => simp [VTy.Persistent, VTy.persistent] at hp
  | tensor T₁ T₂ =>
      simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true] at hp
      obtain ⟨v₁, v₂, ρ₀, ρ₃, hc, hq, ρ₁, ρ₂, hc', h₁, h₂⟩ := h
      exact ⟨v₁, v₂, ρ₀, ρ₃, hc, hq, ρ₁, ρ₂, hc', h₁.2 hp.1, h₂.2 hp.2⟩
  | sum T₁ T₂ =>
      simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true] at hp
      rcases h with ⟨v₁, ρ₀, ρ₁, hc, hq, h₁⟩ | ⟨v₂, ρ₀, ρ₂, hc, hq, h₂⟩
      · exact Or.inl ⟨v₁, ρ₀, ρ₁, hc, hq, h₁.2 hp.1⟩
      · exact Or.inr ⟨v₂, ρ₀, ρ₂, hc, hq, h₂.2 hp.2⟩
  | zero => exact h
  | thunk _ => simp [VTy.Persistent, VTy.persistent] at hp
  | code _ _ _ => simp [VTy.Persistent, VTy.persistent] at hp
  | bang T => exact ⟨h.1, h.2.1⟩
  | box a T =>
      obtain ⟨α, hα, hb, ho⟩ := h
      exact ⟨α, hα, hb.2 hp, ho⟩
  | ref T => simp [VTy.Persistent, VTy.persistent] at hp
  | imm a T => simp [VTy.Persistent, VTy.persistent] at hp
  | «mut» a T => simp [VTy.Persistent, VTy.persistent] at hp
  | unk => exact h
  | tvar _ => exact h.elim
  | mu A =>
      exact vC_roll h.1 h.2.1 (h.2.2.2 (by
        show (VTy.inst (.mu A) A).persistent = true
        rw [persistent_inst_mu]; exact hp))
  | fam L => simp [VTy.Persistent, VTy.persistent] at hp

/-- A leaf of `[Imm @b A]` at a persistent `A`: one `imm` cell whose value is in the program's
relation at `∅`, at every list.  `[spec §74]` -/
theorem vP_imm_leaf_val {b : Lifetime.Life} {A : VTy} (hA : A.Persistent) {ls : List SRec}
    {δ : LSub} {m : Loc} {ρ : WRes} (h : vP (.imm b A) ls δ (.loc m) ρ) :
    ∃ ψ, ρ.get m = some ψ ∧ ∀ ls', vC true A ls' δ ψ.erase PMap.empty := by
  obtain ⟨α, -, ℓ', hs⟩ := h
  obtain ⟨⟨hl, -⟩, s, u, σ, hσ, ls₀, rfl, hP, -, -⟩ := pure_sep_iff.mp hs
  have hℓ : ℓ' = m := by
    have := congrArg Subtype.val hl; simpa using this.symm
  subst hℓ
  have h0 : σ = PMap.empty :=
    vCE_empty_of_persistent A (η := none) (fun _ _ _ _ _ h => h.elim) hA hP
  subst h0
  have hext : ∀ ls', Ext ls₀ ls' PMap.empty := fun _ =>
    ⟨fun _ _ hr => by obtain ⟨m, ψ, e, -⟩ := hr; simp at e,
     fun _ hb => by obtain ⟨m, ψ, e, -⟩ := hb; simp at e⟩
  exact ⟨_, ResU.single_get_self _ _, fun ls' =>
    vC_local true A (hext ls') (vC_true_of_persistent hA hP)⟩

/-- The values of `n` leaves of `[Imm @b A]` from `ℓ`, at a persistent `A`: the cell at `ℓ + j`
holds `u j`, which is in the program's relation at `∅`.  `[spec §74]` -/
theorem immRange_vals {b : Lifetime.Life} {A : VTy} (hA : A.Persistent) {ls : List SRec}
    {δ : LSub} {ℓ : Loc} {n : Nat} {ρ : WRes}
    (h : sepRange (fun m => vP (.imm b A) ls δ (.loc m)) ℓ n ρ) :
    ∃ u : Nat → Val, ∀ j, j < n →
      (∃ ψ, ρ.get (ℓ + j) = some ψ ∧ ψ.erase = u j) ∧ ∀ ls', vC true A ls' δ (u j) PMap.empty := by
  have hx : ∀ j, ∃ u : Val, j < n →
      (∃ ψ, ρ.get (ℓ + j) = some ψ ∧ ψ.erase = u) ∧ ∀ ls', vC true A ls' δ u PMap.empty := by
    intro j
    by_cases hj : j < n
    · obtain ⟨ρj, ρr, hc, hPj, -⟩ := sepRange_pick hj h
      obtain ⟨ψ, hψ, hv⟩ := vP_imm_leaf_val hA hPj
      obtain ⟨ψ', hψ', he⟩ := compS_get_erase hc hψ
      exact ⟨ψ.erase, fun _ => ⟨⟨ψ', hψ', he⟩, hv⟩⟩
    · exact ⟨.unit, fun hj' => absurd hj' hj⟩
  choose u hu using hx
  exact ⟨u, hu⟩

/-! ### The write: `n` of `TW.store` -/

/-- `μ[k ↦ w k | d ≤ k < d + n]`.  `[spec §74]` -/
def writeRange (μ : Heap) (d n : Nat) (w : Loc → Val) : Heap :=
  fun k => if d ≤ k ∧ k < d + n then some (w k) else μ k

theorem writeRange_zero (μ : Heap) (d : Nat) (w : Loc → Val) : writeRange μ d 0 w = μ := by
  funext k; simp only [writeRange]; split
  · lomega
  · rfl

theorem writeRange_succ (μ : Heap) (d n : Nat) (w : Loc → Val) :
    writeRange (μ.upd d (w d)) (d + 1) n w = writeRange μ d (n + 1) w := by
  funext k
  simp only [writeRange, BoCa.BoLo.Heap.upd]
  by_cases h₁ : d + 1 ≤ k ∧ k < d + 1 + n
  · rw [if_pos h₁, if_pos (by lomega)]
  · rw [if_neg h₁]
    by_cases h₂ : k = d
    · subst h₂; rw [if_pos rfl, if_pos (by lomega)]
    · rw [if_neg h₂, if_neg (by lomega)]

/-- One owned cell rewritten: the world after `TW.store`, with the frame kept.  `[spec §74]` -/
theorem store_world {ρf ρ σ R : WRes} {ps rs : List FrameRec} {μ : Heap} {l : Loc} {v₁ v₂ : Val}
    (hcρ : ResU.CompS (ResU.single l (CellU.ownOf v₁)) R ρ)
    (hf : ResU.Hash ρf ρ) (hσ : ResU.CompS ρf ρ σ) (hT : TW σ ps rs) (hμ : ResU.Lower σ μ) :
    ∃ x σ', ResU.CompS R (ResU.single l (CellU.ownOf v₂)) x ∧ ResU.Hash ρf x ∧
      ResU.CompS ρf x σ' ∧ TW σ' ps rs ∧ ResU.Lower σ' (μ.upd l v₂) ∧ ResU.UpdV ρ x ∧
      (∀ a, AgW σ' a → AgW σ a) ∧ μ l = some v₁ := by
  have h₂ : ResU.Hash ρf R :=
    ResU.hash_symm (ResU.Hash.split hcρ (ResU.hash_symm hf)).2
  obtain ⟨σ₂, hσ₂, hσ₂σ⟩ :=
    (ResU.CompS.assoc ρf R (ResU.single l (CellU.ownOf v₁)) σ).mp
      ⟨ρ, ResU.CompS.comm hcρ, hσ⟩
  obtain ⟨hlv, μ₂, hlow₂, hupd, hnone⟩ := lower_compS_own_inv hσ₂σ hμ
  obtain ⟨x, hx⟩ := (ResU.compS_defined_iff R (ResU.single l (CellU.ownOf v₂))).mpr
    (compatS_single_of_get_none (ResU.compatS_single_own hcρ.1))
  obtain ⟨σ', hσ'x, hfx, hlow'⟩ := hash_compS_own hσ₂ hlow₂ hnone hx
  have hstep : BoCa.BoLo.Heap.upd μ l v₂ = BoCa.BoLo.Heap.upd μ₂ l v₂ := by
    funext k
    by_cases e : k = l
    · subst e; rw [BoCa.BoLo.Heap.upd_same, BoCa.BoLo.Heap.upd_same]
    · rw [BoCa.BoLo.Heap.upd_other e, BoCa.BoLo.Heap.upd_other e, hupd,
        BoCa.BoLo.Heap.upd_other e]
  obtain ⟨y, hy, hyσ'⟩ := (ResU.CompS.assoc ρf R (ResU.single l (CellU.ownOf v₂)) σ').mp
    ⟨x, hx, hσ'x⟩
  cases ResU.CompS.functional hy hσ₂
  refine ⟨x, σ', hx, hfx, hσ'x,
    TW.store hT (ResU.CompS.comm hσ₂σ) (ResU.CompS.comm hyσ') (hash_valid_comp hfx hσ'x),
    hstep ▸ hlow', ?_, fun a ha => (own_cell_ag (ResU.CompS.comm hσ₂σ) a).mpr
      ((own_cell_ag (ResU.CompS.comm hyσ') a).mp ha), hlv⟩
  exact ResU.UpdV.trans
    (updV_compS_own (ResU.CompS.comm hcρ) (hash_valid h₂).2 (hash_valid hf).2).symm
    (updV_compS_own hx (hash_valid h₂).2 (hash_valid hfx).2)

/-- `n` owned cells from `d` rewritten to `w`: `n` of `store_world`.  `[spec §74]` -/
theorem store_block {ρf : WRes} {ps rs : List FrameRec} (w : Loc → Val) :
    ∀ (n : Nat) (d : Loc) {ρ σ ρd R : WRes} {μ : Heap},
      sepRange (fun l => ex fun v => ptoOwn l v) d n ρd → ResU.CompS ρd R ρ →
      ResU.Hash ρf ρ → ResU.CompS ρf ρ σ → TW σ ps rs → ResU.Lower σ μ →
      ∃ ρd' x σ', sepRange (fun l => ptoOwn l (w l)) d n ρd' ∧ ResU.CompS ρd' R x ∧
        ResU.Hash ρf x ∧ ResU.CompS ρf x σ' ∧ TW σ' ps rs ∧
        ResU.Lower σ' (writeRange μ d n w) ∧ ResU.UpdV ρ x ∧ (∀ a, AgW σ' a → AgW σ a) ∧
        μ.HasRange d n
  | 0, d, ρ, σ, ρd, R, μ, hd, hρ, hf, hσ, hT, hμ => by
      obtain ⟨rfl, -⟩ := hd
      rw [eq_of_compS_empty_left hρ]
      refine ⟨PMap.empty, R, σ, ⟨rfl, trivial⟩, compS_empty_left R,
        by rwa [eq_of_compS_empty_left hρ] at hf, by rwa [eq_of_compS_empty_left hρ] at hσ, hT,
        by rw [writeRange_zero]; exact hμ, ?_, fun _ h => h, fun i hi => absurd hi (by omega)⟩
      exact (ResU.updV_self_iff R).mpr (hash_valid (by rwa [eq_of_compS_empty_left hρ] at hf)).2
  | n + 1, d, ρ, σ, ρd, R, μ, ⟨c₁, ρd₂, h12, ⟨v, hv⟩, hd₂⟩, hρ, hf, hσ, hT, hμ => by
      subst hv
      obtain ⟨Y, hY, hρY⟩ := compS_reassoc h12 hρ
      obtain ⟨x₁, σ₁, hx₁, hf₁, hσ₁, hT₁, hμ₁, hu₁, hag₁, hdv⟩ :=
        store_world (v₂ := w d) hρY hf hσ hT hμ
      obtain ⟨bc, hbc, hx₁'⟩ := compS_reassoc hY hx₁
      obtain ⟨ρd₂', x, σ', hd₂', hx, hf', hσ', hT', hμ', hu, hag, hrange⟩ :=
        store_block w n (d + 1) hd₂ hx₁' hf₁ hσ₁ hT₁ hμ₁
      obtain ⟨ab, hab, habx⟩ := compS_reassoc' (ResU.CompS.comm hbc) hx
      refine ⟨ab, x, σ', ⟨_, ρd₂', ResU.CompS.comm hab, rfl, hd₂'⟩, habx, hf', hσ', hT', ?_,
        hu₁.trans hu, fun a ha => hag₁ a (hag a ha), fun i hi => ?_⟩
      · rw [← writeRange_succ]; exact hμ'
      · rcases i with _ | j
        · simp [hdv]
        · have := hrange j (Nat.lt_of_succ_lt_succ hi)
          have hne : d + 1 + j ≠ d := by lomega
          have heq : d + 1 + j = d + (j + 1) := by lomega
          rwa [BoCa.BoLo.Heap.upd_other hne, heq] at this

/-! ### The copy step at the typed world -/

/-- **The `sliceCopy` step in range.**  The destination's `len` cells from `ℓd + di` are owned;
the source's `len` cells from `ℓs + si` are cells of `ρs` holding `u`. The step writes `u` into
the destination and keeps the rest.  `[spec §74]` -/
theorem wpTS_copy {ls : List SRec} {ℓd : Loc} {nd di : UInt32} {ℓs : Loc} {ns si len : UInt32}
    (hok : copyOk nd di ns si len = true) (u : Nat → Val) {ρd ρs R X ρ : WRes}
    (hd : sepRange (fun l => ex fun v => ptoOwn l v) (ℓd + di.toNat) len.toNat ρd)
    (hs : ∀ j, j < len.toNat → ∃ ψ, ρs.get (ℓs + si.toNat + j) = some ψ ∧ ψ.erase = u j)
    (hX : ResU.CompS ρs R X) (hρ : ResU.CompS ρd X ρ) (Q : List SRec → Val → WProp)
    (hQ : ∀ ρd' x, sepRange (fun l => ptoOwn l (u (l - (ℓd + di.toNat)))) (ℓd + di.toNat)
        len.toNat ρd' → ResU.CompS ρd' X x → Q ls (copyAns ℓd nd di ns si len) x) :
    wpTS ls (.app (.val (.prim .sliceCopy)) (.val (copyArg ℓd nd di ℓs ns si len))) Q ρ := by
  intro ρf fρ ps hf hc hT htg A k
  obtain ⟨μ, hμ⟩ := lower_of_hash hf hc
  -- the source's cells, read in the memory before the step
  have hsrc : ∀ j, j < len.toNat → μ (ℓs + si.toNat + j) = some (u j) := by
    intro j hj
    obtain ⟨ψ, hψ, he⟩ := hs j hj
    obtain ⟨ψ₁, hψ₁, he₁⟩ := compS_get_erase hX hψ
    obtain ⟨ψ₂, hψ₂, he₂⟩ := compS_get_erase (ResU.CompS.comm hρ) hψ₁
    obtain ⟨ψ₃, hψ₃, he₃⟩ := compS_get_erase (ResU.CompS.comm hc) hψ₂
    rw [lower_get hμ hψ₃, he₃, he₂, he₁, he]
  obtain ⟨ρd', x, σ', hd', hx, hf', hσ', hT', hμ', hu, hag, hrange⟩ :=
    store_block (fun l => u (l - (ℓd + di.toNat))) len.toNat (ℓd + di.toNat) hd hρ hf hc hT hμ
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
  have hstep : Head (ℍ := ℍ) μ (.app (.val (.prim .sliceCopy)) (.val (copyArg ℓd nd di ℓs ns si len)))
      (copyHeap μ ℓd nd di ℓs ns si len) (.val (copyAns ℓd nd di ns si len)) :=
    Head.sliceCopy μ ℓd nd di ℓs ns si len fun _ =>
      ⟨hrange, fun j hj => by rw [hsrc j hj]; simp⟩
  rw [hheap] at hstep
  exact ⟨x, PMap.empty, σ', σ', x, copyAns ℓd nd di ns si len, μ, _, ps, ls,
    ResU.hash_symm hf', hσ', ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hf' hσ')),
    hμ, ResU.comp_empty_right σ', hμ', ⟨k, ARun.one (Step1N.head hstep rfl)⟩,
    ResU.comp_empty_right x, hu, noOwn_empty, hT', tagged_of_ag hag htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, hQ ρd' x hd' hx⟩

/-! ### Mut Anti-Frame over a range of leaves -/

/-- After a run with `n` leaves from `m` opened: each cell holds a value in the relation, and the
leaves given back yield `Q`. -/
def openPost (a : Lifetime.Life) (A : VTy) (δ : LSub) (m : Loc) (n : Nat)
    (Q : List SRec → Val → WProp) : List SRec → Val → WProp :=
  fun ls v => sep (sepRange (fun l => ex fun w => sep (ptoOwn l w) (vC true A ls δ w)) m n)
    (wand (sepRange (fun l => vP (.mut a A) ls δ (.loc l)) m n) (Q ls v))

/-- **Mut Anti-Frame at `n` leaves of `[Mut @a A]`**, `A` persistent: `n` of
`wpTS_M_antiFrameX`, each payload at `∅`.  `[spec §74]` -/
theorem wpTS_M_antiFrameRange {a : Lifetime.Life} {A : VTy} {δ : LSub} (hA : A.Persistent)
    (e : Expr) (ls : List SRec) :
    ∀ (n : Nat) (m : Loc) (Q : List SRec → Val → WProp) {ρm ρr ρ : WRes},
      sepRange (fun l => vP (.mut a A) ls δ (.loc l)) m n ρm → ResU.CompS ρm ρr ρ →
      (∀ ρo X, sepRange (fun l => ex fun w => ptoOwn l w) m n ρo → ResU.CompS ρo ρr X →
        wpTS ls e (openPost a A δ m n Q) X) →
      wpTS ls e Q ρ
  | 0, m, Q, ρm, ρr, ρ, hm, hρ, H => by
      obtain ⟨rfl, -⟩ := hm
      rw [eq_of_compS_empty_left hρ]
      refine wpTS_mono (fun ls' v R hR => ?_) ρr (H PMap.empty ρr ⟨rfl, trivial⟩ (compS_empty_left ρr))
      obtain ⟨O, W, hOW, ⟨rfl, -⟩, hW⟩ := hR
      rw [eq_of_compS_empty_left hOW]
      exact hW PMap.empty W ⟨rfl, trivial⟩ (ResU.comp_empty_right W)
  | n + 1, m, Q, ρm, ρr, ρ, ⟨ρ1, ρm2, h12, hleaf, hrest⟩, hρ, H => by
      obtain ⟨F, hF, hρ1F⟩ := compS_reassoc h12 hρ
      obtain ⟨α, ha, hmut⟩ := vP_mut_leaf hleaf
      refine wpTS_M_antiFrameX m α A δ e ls Q ρ ⟨ρ1, F, hρ1F, hmut, ?_⟩
      intro old c₁ c₂ hc₁ hcc p₁ p₂ hp₁ hcp
      have hp0 : p₁ = PMap.empty := vP_empty_of_persistent hA hp₁
      subst hp0
      cases ResU.CompS.functional hcp (ResU.comp_empty_right c₂)
      obtain ⟨bc, hbc, hc₂⟩ := compS_reassoc hF hcc
      refine wpTS_M_antiFrameRange hA e ls n (m + 1) _ hrest hc₂ fun ρo X hρo hX => ?_
      obtain ⟨ab, hab, habX⟩ := compS_reassoc' (ResU.CompS.comm hbc) hX
      refine wpTS_mono (fun ls' v R hR => ?_) X
        (H ab X ⟨c₁, ρo, ResU.CompS.comm hab, ⟨old, hc₁⟩, hρo⟩ habX)
      obtain ⟨O, W, hOW, ⟨O1, O2, hO12, ⟨w, o, pv, hop, ho, hv⟩, hO2⟩, hW⟩ := hR
      have hpv : pv = PMap.empty := vP_empty_of_persistent hA hv
      subst hpv
      cases ResU.CompS.functional hop (ResU.comp_empty_right o)
      obtain ⟨W', hW', hR'⟩ := compS_exch hO12 hOW
      refine ⟨O2, W', ResU.CompS.comm hR', hO2, ?_⟩
      intro M2 Z hM2 hZ
      obtain ⟨WM, hWM, hZ'⟩ := compS_reassoc hW' hZ
      refine ⟨w, O1, WM, hZ', ho, PMap.empty, WM, compS_empty_left WM, hv, ?_⟩
      intro Mm Z' hMm hZ''
      obtain ⟨M, hM, hWMZ⟩ := compS_reassoc hWM hZ''
      exact hW M Z' ⟨Mm, M2, ResU.CompS.comm hM, vP_mut_leaf_mk ha hMm, hM2⟩ hWMZ

/-! ### `slice_copy_mut` -/

/-- `slice_copy_mut : !([Mut @a A] ⊗ (I32 ⊗ ([Imm @b A] ⊗ (I32 ⊗ I32))) ⇒ [Mut @a A] ⊗ (1 ⊕ 1))`.
`[spec §74]` -/
abbrev sliceCopyMTy (a b : Lifetime.Life) (A : VTy) : VTy :=
  .bang (.lolli
    (.tensor (.sliceMut a A) (.tensor (.int .w32)
      (.tensor (.arrayImm b A) (.tensor (.int .w32) (.int .w32)))))
    (.tensor (.sliceMut a A) (.sum .unit .unit)))

/-- The machine's `sliceCopy`.  `[spec §74]` -/
def sliceCopyV : Val := .prim .sliceCopy

/-- The bounds `copyOk` checks, as naturals. -/
theorem copyOk_bounds {nd di ns si len : UInt32} (h : copyOk nd di ns si len = true) :
    di.toNat + len.toNat ≤ nd.toNat ∧ si.toNat + len.toNat ≤ ns.toNat := by
  simp only [copyOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2⟩

/-- **`slice_copy_mut`.**  `[spec §74]` -/
theorem sliceCopyM_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a b : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) (hA : A.Persistent) :
    SemV Δ Γ (.val sliceCopyV) (sliceCopyMTy a b A) := by
  refine sem_const hΓ rfl fun δ ls _ => ⟨rfl, ?_⟩
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  -- the argument `(dst, (di, (src, (si, len))))`
  obtain ⟨v₁, v₂, hk⟩ := hv
  obtain ⟨rfl, σ₁, σ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hk
  obtain ⟨ℓd, nd, rfl, hnd, hsd⟩ := vP_fam_iff.mp h₁
  obtain ⟨w₁, x, hk₂⟩ := h₂
  obtain ⟨rfl, ρ₀, σx, hc₂, ⟨e₀, di, rfl⟩, hx⟩ := pure_sep_iff.mp hk₂
  subst e₀
  rw [eq_of_compS_empty_left hc₂] at hc
  obtain ⟨x₁, x₂, hk₃⟩ := hx
  obtain ⟨rfl, σs, σ₃, hc₃, h₃, h₄⟩ := pure_sep_iff.mp hk₃
  obtain ⟨ℓs, ns, rfl, -, hss⟩ := vP_fam_iff.mp h₃
  obtain ⟨y₁, y₂, hk₄⟩ := h₄
  obtain ⟨rfl, ρ₁, ρ₂, hc₄, ⟨e₁, si, rfl⟩, ⟨e₂, len, rfl⟩⟩ := pure_sep_iff.mp hk₄
  subst e₁ e₂
  rw [eq_of_compS_empty_left hc₄] at hc₃
  rw [ResU.CompS.functional hc₃ (ResU.comp_empty_right σs)] at hc
  have hσs : NoOwn σs := sepRange_closed noOwn_empty
    (fun _ _ _ hc h₁ h₂ => noOwn_compS hc h₁ h₂) (fun _ _ h => noOwn_imm h) hss
  change wpTS ls' (.app (.val (.prim .sliceCopy)) (.val (copyArg ℓd nd di ℓs ns si len))) _ σ
  by_cases hok : copyOk nd di ns si len = true
  swap
  · -- out of range: nothing is written, and the family is handed back
    have hok' : copyOk nd di ns si len = false := by simpa using hok
    refine wpTS_drop hσs (ResU.CompS.comm hc) ?_
    refine wpTS_head (e' := .val (copyAns ℓd nd di ns si len)) (fun μ => ?_) rfl ls' _ σ₁ ?_
    · have h := Head.sliceCopy (ℍ := ℍ) μ ℓd nd di ℓs ns si len (fun h => absurd h hok)
      rwa [show copyHeap μ ℓd nd di ℓs ns si len = μ by simp [copyHeap, hok']] at h
    · rw [show copyAns ℓd nd di ns si len = Val.pair (Val.arr ℓd nd) (Val.inj₁ Val.unit) by
        simp [copyAns, hok']]
      exact wpTS_val ls' _ _ σ₁ ⟨_, _, pure_sep_mk rfl ⟨σ₁, PMap.empty,
        ResU.comp_empty_right σ₁, vP_fam_mk hnd hsd, Or.inl ⟨.unit, pure_sep_mk rfl ⟨rfl, rfl⟩⟩⟩⟩
  -- in range
  obtain ⟨hdl, hsl⟩ := copyOk_bounds hok
  -- the destination: `[0, di)`, `[di, di + len)`, the rest
  have hnd' : nd.toNat = di.toNat + (len.toNat + (nd.toNat - di.toNat - len.toNat)) := by omega
  rw [hnd'] at hsd
  obtain ⟨D1, D23, hD, hD1, hD23⟩ := sepRange_split hsd
  obtain ⟨Dm, D3, hDm3, hDm, hD3⟩ := sepRange_split hD23
  -- the source: its range `[si, si + len)`
  have hns' : ns.toNat = si.toNat + (len.toNat + (ns.toNat - si.toNat - len.toNat)) := by omega
  rw [hns'] at hss
  obtain ⟨S1, S23, hS, -, hS23⟩ := sepRange_split hss
  obtain ⟨Sm, S3, hSm3, hSm, -⟩ := sepRange_split hS23
  obtain ⟨u, hu⟩ := immRange_vals hA hSm
  have hreads : ∀ j, j < len.toNat →
      ∃ ψ, σs.get (ℓs + si.toNat + j) = some ψ ∧ ψ.erase = u j := by
    intro j hj
    obtain ⟨⟨ψ, hψ, he⟩, -⟩ := hu j hj
    obtain ⟨ψ₁, hψ₁, he₁⟩ := compS_get_erase hSm3 hψ
    obtain ⟨ψ₂, hψ₂, he₂⟩ := compS_get_erase (ResU.CompS.comm hS) hψ₁
    exact ⟨ψ₂, hψ₂, he₂.trans (he₁.trans he)⟩
  -- `σ = Dm ● ((D1 ● D3) ● σs)`
  obtain ⟨D13, hD13, hDmσ₁⟩ := compS_lcomm hDm3 hD
  obtain ⟨Rr, hRr, hDmR⟩ := compS_reassoc hDmσ₁ hc
  refine wpTS_M_antiFrameRange hA _ ls' len.toNat (ℓd + di.toNat) _ hDm hDmR fun ρo X hρo hX => ?_
  refine wpTS_bind .hole _ ls' _ X ?_
  refine wpTS_copy hok u hρo hreads (ResU.CompS.comm hRr) hX _ fun ρd' y hd' hy => ?_
  rw [show copyAns ℓd nd di ns si len = Val.pair (Val.arr ℓd nd) (Val.inj₂ Val.unit) by
    simp [copyAns, hok]]
  simp only [Kont.plug]
  obtain ⟨ab, hab, haby⟩ := compS_reassoc' hRr hy
  refine wpTS_drop hσs (ResU.CompS.comm haby) ?_
  refine wpTS_val ls' _ _ ab ⟨ρd', D13, hab, ?_, ?_⟩
  · refine sepRange_mono (fun m hm hm' ρ hρ => ?_) ρd' hd'
    exact ⟨_, ρ, PMap.empty, ResU.comp_empty_right ρ, hρ, (hu _ (by lomega)).2 ls'⟩
  · intro M ZZ hM hZZ
    obtain ⟨bc, hbc, hZ⟩ := compS_reassoc hD13 hZZ
    have h23 := sepRange_append (ResU.CompS.comm hbc) hM hD3
    have hall := sepRange_append hZ hD1 h23
    rw [← hnd'] at hall
    exact ⟨_, _, pure_sep_mk rfl ⟨ZZ, PMap.empty, ResU.comp_empty_right ZZ,
      vP_fam_mk hnd hall, Or.inr ⟨.unit, pure_sep_mk rfl ⟨rfl, rfl⟩⟩⟩⟩

end BoCa.Fig16.LogRel.Core

end

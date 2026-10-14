import Law2.Rules

/-!
# Law2 — the family operations at the re-lendable reading

A family `[L]` is read leaf by leaf (`RSlot` at `.fam`, as the kernel's clause at `[L]`), each leaf
re-lendable with its own share. The operations on a family are then the kernel's proofs with the
leaf predicate `RSlot L`:

* `idx` (`array_get`, `slice_get_mut`): the leaf at the index, re-lendable as it was in the family,
  the rest dropped (its leaves hold no `own` cell at the current lifetimes) — `pv_famGet`;
* `split` (`slice_split_imm`, `slice_split_mut`): the range split at the index, each part its leaves
  as they were — `pv_famSplit`;
* `array_replace`: the old element out of its owned cell, the new one in, the cell frozen beside it
  — `pv_arrReplace`;
* `array_new`, `array_free`: the function held at `!` called once per element at the current
  lifetimes (`bang_app_rs`), by induction on the cells left (`tabFill_rs`, `dropFill_rs`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Law2
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Head Step1N performE opPayload eLoad eStore)
open BoCa.Lifetime (LifeVar LifeCtx LSub)
open GhostEnd

section families
variable {δ : LSub} {σ : LStack} {S₀ : Row}

/-- The argument of an operation on a family and an index: the family's leaves, the index
frozen. -/
theorem rslot_fam_idx {L : VTy} {αs : List Life} {ls : List SRec} {v : Val} {ρ : WRes}
    (hch : List.IsChain (· < ·) αs)
    (h : RSlot (ℍ := ℍ) δ σ S₀ (.tensor (.fam L) (.int .w32)) αs ls v ρ) :
    ∃ ℓ n i, v = Val.pair (Val.arr ℓ n) (Val.i32 i) ∧ n.toNat < 2 ^ 31 ∧
      sepRange (fun m => RSlot (ℍ := ℍ) δ σ S₀ L αs ls (.loc m)) ℓ n.toNat ρ := by
  obtain ⟨v₁, v₂, hk⟩ := h
  obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hk
  obtain ⟨ℓ, n, hq⟩ := h₁
  obtain ⟨⟨rfl, hn⟩, hs⟩ := pure_sep_iff.mp hq
  obtain ⟨rfl, i, rfl⟩ := relendableS_now hch h₂
  rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)]
  exact ⟨ℓ, n, i, rfl, hn, hs⟩

/-- **`idx` on a family whose leaves hold no `own` cell** (`array_get`, `slice_get_mut`): the leaf
at the index, re-lendable as it was in the family; the rest dropped. -/
theorem pv_famGet {Δ : LifeCtx} {Γ : Ctx VTy} {L : VTy} (hΓ : Ctx.DeadP Γ)
    (hL : ∀ αs ls m ρ, List.IsChain (· < ·) αs →
      RSlot (ℍ := ℍ) δ σ S₀ L αs ls (.loc m) ρ → NoOwn ρ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .idx))
      (.bang (.lolli (.tensor (.fam L) (.int .w32)) (.sum L .unit))) := by
  refine pv_const (c := Val.prim .idx) hΓ (fun k γ => rfl) fun αs ls hlen _ => ⟨rfl, ?_⟩
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr _ _) αs' ls' (.val (Val.prim .idx)) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  have hlen' : αs'.length = σ.length := (List.Forall₂.length_eq hr.1).trans hlen
  obtain ⟨ℓ, n, i, rfl, -, hs⟩ := rslot_fam_idx hr.2 hv
  refine rc_ret_of_wpTS (wpTS_head (fun μ => Head.idx μ ℓ n i) rfl ls' _ ρ₁ ?_)
  have hσ : NoOwn ρ₁ := sepRange_closed noOwn_empty
    (fun _ _ _ hc h₁ h₂ => noOwn_compS hc h₁ h₂) (fun m τ h => hL αs' ls' m τ hr.2 h) hs
  rcases idxAns_cases ℓ n i with ⟨hi, he⟩ | he
  · rw [he]
    obtain ⟨ρi, ρr, hci, hPi, -⟩ := sepRange_pick hi hs
    refine wpTS_drop (noOwn_right hci hσ) (ResU.CompS.comm hci) ?_
    exact wpTS_val ls' _ _ _ (Or.inl ⟨_, pure_sep_mk rfl hPi⟩)
  · rw [he]
    refine wpTS_drop hσ (ResU.comp_empty_right ρ₁) ?_
    exact wpTS_val ls' _ _ _ (Or.inr ⟨.unit, pure_sep_mk rfl (rslot_unit hlen' ls')⟩)

/-- **`array_get`**: `idx` on a family of `imm` leaves. -/
theorem pv_arrGet {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy) (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .idx)) (arrGetTy a A) :=
  pv_famGet hΓ fun _ _ _ _ hch h => by
    rw [rslot_leaf (A := .imm a A) leafR] at h
    exact noOwn_imm (relendableS_now hch h)

/-- **`slice_get_mut`**: `idx` on a family of `mut` leaves. -/
theorem pv_sliceGetM {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy)
    (hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .idx)) (sliceGetMTy a A) :=
  pv_famGet hΓ fun _ _ _ _ hch h => by
    rw [rslot_leaf (A := .mut a A) leafR] at h
    exact noOwn_mut (relendableS_now hch h)

/-- **`split` on a family at any leaf**: the range split at the index, each part its leaves as
they were; out of range, the family back. -/
theorem pv_famSplit {Δ : LifeCtx} {Γ : Ctx VTy} {L : VTy} (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .split)) (famSplitTy L) := by
  refine pv_const (c := Val.prim .split) hΓ (fun k γ => rfl) fun αs ls hlen _ => ⟨rfl, ?_⟩
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr _ _) αs' ls' (.val (Val.prim .split)) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  obtain ⟨ℓ, n, i, rfl, hn, hs⟩ := rslot_fam_idx hr.2 hv
  refine rc_ret_of_wpTS (wpTS_head (fun μ => Head.split μ ℓ n i) rfl ls' _ ρ₁ ?_)
  rcases splitAns_cases ℓ n i with ⟨hi, he⟩ | he
  · rw [he]
    have hin : i.toNat ≤ n.toNat := UInt32.le_iff_toNat_le.mp hi
    rw [show n.toNat = i.toNat + (n.toNat - i.toNat) by omega] at hs
    obtain ⟨τ₁, τ₂, hcτ, h₁, h₂⟩ := sepRange_split hs
    have h₂' : sepRange (fun m => RSlot (ℍ := ℍ) δ σ S₀ L αs' ls' (.loc m)) (ℓ + i.toNat)
        (n - i).toNat τ₂ := by
      rwa [uint32_sub_toNat hi]
    exact wpTS_val ls' _ _ _ (Or.inl ⟨_, pure_sep_mk rfl ⟨_, _, pure_sep_mk rfl ⟨τ₁, τ₂, hcτ,
      ⟨ℓ, i, pure_sep_mk ⟨rfl, by omega⟩ h₁⟩,
      ⟨ℓ + i.toNat, n - i, pure_sep_mk ⟨rfl, by rw [uint32_sub_toNat hi]; omega⟩ h₂'⟩⟩⟩⟩)
  · rw [he]
    exact wpTS_val ls' _ _ _ (Or.inr ⟨_, pure_sep_mk rfl ⟨ℓ, n, pure_sep_mk ⟨rfl, hn⟩ hs⟩⟩)

theorem pv_sliceSplitI {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy)
    (hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .split)) (sliceSplitITy a A) :=
  pv_famSplit hΓ

theorem pv_sliceSplitM {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (A : VTy)
    (hΓ : Ctx.DeadP Γ) : PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .split)) (sliceSplitMTy a A) :=
  pv_famSplit hΓ

/-- **`array_replace`**: in range, the old element out of its owned cell, re-lendable as it was,
and the new one in, the cell frozen beside it; out of range, the family and the element back. -/
theorem pv_arrReplace {Δ : LifeCtx} {Γ : Ctx VTy} (A : VTy) (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val replaceV) (arrReplaceTy A) := by
  refine pv_const hΓ (fun k γ => psub_closedAt _ γ rfl (Nat.zero_le k))
    fun αs ls hlen _ => ⟨rfl, ?_⟩
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr _ _) αs' ls' (.val replaceV) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc₀
  rw [eq_of_compS_empty_left hc₀]
  refine rc_ret_of_wpTS ?_
  obtain ⟨v₁, v₂, hk⟩ := hv
  obtain ⟨rfl, σ₁, σ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hk
  obtain ⟨ℓ, n, hq⟩ := h₁
  obtain ⟨⟨rfl, hn⟩, hs⟩ := pure_sep_iff.mp hq
  obtain ⟨w₁, x, hk₂⟩ := h₂
  obtain ⟨rfl, ρ₀, σx, hc₂, hi32, hx⟩ := pure_sep_iff.mp hk₂
  obtain ⟨rfl, i, rfl⟩ := relendableS_now hr.2 hi32
  rw [eq_of_compS_empty_left hc₂] at hc
  refine wpTS_lolli ls' _ _ _ _ ?_
  rw [replace_body₁]
  refine wpTS_tensor ls' (Val.arr ℓ n) (Val.pair (Val.i32 i) x) _ _ _ ?_
  rw [replace_body₂]
  refine wpTS_tensor ls' (Val.i32 i) x _ _ _ ?_
  rw [replace_body₃]
  refine wpTS_bind (.case .hole _ _) _ ls' _ ρ₁ ?_
  refine wpTS_head (fun μ => Head.idx μ ℓ n i) rfl ls' _ ρ₁ ?_
  refine wpTS_val ls' (idxAns ℓ n i) _ ρ₁ ?_
  simp only [Kont.plug]
  rcases idxAns_cases ℓ n i with ⟨hi, he⟩ | he
  · rw [he]
    refine wpTS_sum₁ ls' _ _ _ _ ρ₁ ?_
    rw [replace_in]
    obtain ⟨ρi, ρr, hci, hPi, hback⟩ := sepRange_pick hi hs
    obtain ⟨ℓ', old, hs'⟩ := hPi
    obtain ⟨hl, c, ρold, hcw, hcell, hold⟩ := pure_sep_iff.mp hs'
    have hℓ : ℓ' = ℓ + i.toNat := by
      have := congrArg Subtype.val hl; simpa using this.symm
    subst hℓ
    -- `ρ₁ = c ● G`, `G = ρold ● (ρr ● σx)`
    obtain ⟨F, hF, hiF⟩ := compS_reassoc hci hc
    obtain ⟨G, hG, hσ⟩ := compS_reassoc hcw hiF
    refine wpTS_bind (.pairR (Val.arr ℓ n) (.inj₁ .hole)) _ ls' _ ρ₁ ?_
    refine wpTS_bind (.appR (.val (.lam _)) .hole) (eLoad (ℓ + i.toNat)) ls' _ ρ₁ ?_
    refine wpTS_load ls' _ old _ ρ₁ ⟨c, G, hσ, hcell, ?_⟩
    intro c₁ p₁ hc₁ hp₁
    rw [hc₁, ← hcell] at hp₁
    simp only [Kont.plug]
    refine wpTS_lolli ls' _ old _ p₁ ?_
    rw [replace_store]
    refine wpTS_bind (.seq .hole (.val old)) (eStore (ℓ + i.toNat) x) ls' _ p₁ ?_
    refine wpTS_store ls' _ old x _ p₁ ⟨c, G, ResU.CompS.comm hp₁, hcell, ?_⟩
    intro c₃ p₃ hc₃ hp₃
    simp only [Kont.plug]
    refine wpTS_1 ls' _ _ p₃ ?_
    refine wpTS_val ls' old _ p₃ ?_
    refine wpTS_val ls' (Val.pair (Val.arr ℓ n) (Val.inj₁ old)) _ p₃ ?_
    -- `p₃ = G ● c₃`: the new leaf `c₃ ● σx` beside the rest of the family, and `old`'s payload
    obtain ⟨X, hX, hp₃'⟩ := compS_exch (ResU.CompS.comm hG) hp₃
    obtain ⟨M, hM, hXM⟩ := compS_reassoc hF hX
    exact ⟨_, _, pure_sep_mk rfl ⟨X, ρold, hp₃',
      ⟨ℓ, n, pure_sep_mk ⟨rfl, hn⟩ (hback M X (ResU.CompS.comm hXM)
        ⟨_, x, pure_sep_mk rfl ⟨c₃, σx, ResU.CompS.comm hM, hc₃, hx⟩⟩)⟩,
      Or.inl ⟨old, pure_sep_mk rfl hold⟩⟩⟩
  · rw [he]
    refine wpTS_sum₂ ls' _ _ _ _ ρ₁ ?_
    rw [replace_out]
    exact wpTS_val ls' _ _ ρ₁ ⟨_, _, pure_sep_mk rfl
      ⟨σ₁, σx, hc, ⟨ℓ, n, pure_sep_mk ⟨rfl, hn⟩ hs⟩, Or.inr ⟨x, pure_sep_mk rfl hx⟩⟩⟩

/-- **The fill at the re-lendable reading.** With the cells `ℓ, …, ℓ + i − 1` filled, each a
re-lendable leaf, and `ℓ + i, …, ℓ + i + k − 1` holding `()`, the rest of `tabFill` runs to the
array, each element the answer of the function held at `!`. -/
theorem tabFill_rs {A : VTy} {αs : List Life} (hch : List.IsChain (· < ·) αs)
    (hlen : αs.length = σ.length) {ls₀ : List SRec} (f : Val) (ℓ : Loc) (N : UInt32)
    (hN31 : N.toNat < 2 ^ 31)
    (hf : RSlot (ℍ := ℍ) δ σ S₀ (.bang (.lolli (.int .w32) A)) αs ls₀ f PMap.empty) :
    ∀ (k i : Nat) (ls : List SRec) (ρd ρt ρ : WRes), (∀ x, x ∈ ls ↔ x ∈ ls₀) →
      i + k = N.toNat →
      sepRange (fun m => RSlot (ℍ := ℍ) δ σ S₀ (.ref A) αs ls (.loc m)) ℓ i ρd →
      sepRange todoP (ℓ + i) k ρt → ResU.CompS ρd ρt ρ →
      wpTS ls (tabFill f ℓ N i k) (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ (.array A) αs ls' v) ρ
  | 0, i, ls, ρd, ρt, ρ, _, hN, hd, ht, hc => by
      obtain ⟨rfl, -⟩ := ht
      rw [ResU.CompS.functional hc (ResU.comp_empty_right ρd)]
      refine wpTS_val ls (Val.arr ℓ N) _ ρd ⟨ℓ, N, pure_sep_mk ⟨rfl, hN31⟩ ?_⟩
      rw [← hN]; exact hd
  | k + 1, i, ls, ρd, ρt, ρ, hls, hN, hd, ⟨c, ρt', hct, hcell, ht'⟩, hc => by
      show wpTS ls (.seq (.app (.app (.val (.prim .store)) (.val (.loc (ℓ + i))))
        (.app (.val f) (.val (Val.i32 (UInt32.ofNat i))))) (tabFill f ℓ N (i + 1) k)) _ ρ
      refine wpTS_bind (.seq .hole (tabFill f ℓ N (i + 1) k)) _ ls _ ρ ?_
      -- `ρ = c ● (ρd ● ρt')`
      obtain ⟨R, hR, hρ⟩ := compS_lcomm hct hc
      refine wpTS_bind_frame (.appR (.app (.val (.prim .store)) (.val (.loc (ℓ + i)))) .hole)
        (.app (.val f) (.val (Val.i32 (UInt32.ofNat i)))) ls
        (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ A αs ls' v)
        (fun ls' => ptoOwn (ℓ + i) .unit ⋆
          (sepRange (fun m => RSlot (ℍ := ℍ) δ σ S₀ (.ref A) αs ls' (.loc m)) ℓ i ⋆
            sepRange todoP (ℓ + i + 1) k))
        _ ?_ ?_ ρ ⟨PMap.empty, ρ, compS_empty_left ρ,
          bang_app_rs hch hls hf (rslot_i32 hlen ls _), c, R, hρ, hcell, ρd, ρt', hR, hd, ht'⟩
      · intro ls' hls' τ ⟨τ₁, τ₂, hτ, h₁, τ₃, τ₄, hτ', h₃, h₄⟩
        exact ⟨τ₁, τ₂, hτ, h₁, τ₃, τ₄, hτ',
          sepRange_mono' (fun m υ h => rslot_local (.ref A) (ext_of_same hls' υ) h) h₃, h₄⟩
      · intro ls' hls' w τ ⟨τw, τr, hτ, hw, c', R', hR', hc', τd, τt, hdt, hd', ht''⟩
        simp only [Kont.plug]
        -- `τ = c' ● (τw ● R')`
        obtain ⟨G, hG, hτG⟩ := compS_lcomm hR' hτ
        refine wpTS_store ls' (ℓ + i) .unit w _ τ ⟨c', G, hτG, hc', ?_⟩
        intro c₃ τ₃ hc₃ hcomp₃
        refine wpTS_1 ls' _ _ τ₃ ?_
        -- the new leaf `τw ● c₃`, beside the filled cells and the rest of the placeholders
        obtain ⟨M, hM, hτ₃⟩ := compS_exch hG hcomp₃
        obtain ⟨M', hM', hτ₃'⟩ := compS_lcomm hdt hτ₃
        obtain ⟨D, hD, hτ₃''⟩ := compS_reassoc' hM' hτ₃'
        have hleaf : RSlot (ℍ := ℍ) δ σ S₀ (.ref A) αs ls' (.loc (ℓ + i)) M :=
          ⟨ℓ + i, w, pure_sep_mk rfl ⟨c₃, τw, ResU.CompS.comm hM, hc₃, hw⟩⟩
        refine tabFill_rs hch hlen f ℓ N hN31 hf k (i + 1) ls' D τt τ₃
          (fun x => (hls' x).trans (hls x)) (by rw [← hN]; ring)
          (sepRange_append hD hd' ⟨M, PMap.empty, ResU.comp_empty_right M, hleaf, ⟨rfl, trivial⟩⟩)
          ?_ hτ₃''
        rwa [show ℓ + i + 1 = ℓ + (i + 1) by ring] at ht''

/-- **`array_new`**: the function, held at `!`, called once per element at the current lifetimes;
each element stored in its cell, owned and frozen beside it. -/
theorem pv_arrNew {Δ : LifeCtx} {Γ : Ctx VTy} (A : VTy) (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .tab)) (arrNewTy A) := by
  refine pv_const (c := Val.prim .tab) hΓ (fun k γ => rfl) fun αs ls hlen _ => ⟨rfl, ?_⟩
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr _ _) αs' ls' (.val (Val.prim .tab)) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  have hlen' : αs'.length = σ.length := (List.Forall₂.length_eq hr.1).trans hlen
  obtain ⟨v₁, f, hk⟩ := hv
  obtain ⟨rfl, σ₁, σ₂, hc', hint, hf⟩ := pure_sep_iff.mp hk
  obtain ⟨rfl, c, rfl⟩ := relendableS_now hr.2 hint
  have e₂ : σ₂ = PMap.empty := hf.1
  subst e₂
  cases eq_empty_of_compS_empty hc'
  refine rc_ret_of_wpTS (wpTS_tab ls' c f _ PMap.empty ?_)
  intro ℓ cells x hcells hx
  rw [eq_of_compS_empty_left hx]
  exact tabFill_rs hr.2 hlen' f ℓ (arrLen c) (arrLen_bound c) hf (arrLen c).toNat 0 ls'
    PMap.empty cells cells (fun _ => Iff.rfl) (by simp) ⟨rfl, trivial⟩ (by simpa using hcells)
    (compS_empty_left cells)

/-- **The drain at the re-lendable reading.** The cells `ℓ + i, …, ℓ + i + k − 1` freed in order,
each element handed to the consumer held at `!`. -/
theorem dropFill_rs {A : VTy} {αs : List Life} (hch : List.IsChain (· < ·) αs)
    (hlen : αs.length = σ.length) {ls₀ : List SRec} (f : Val) (ℓ : Loc)
    (hf : RSlot (ℍ := ℍ) δ σ S₀ (.bang (.lolli A .unit)) αs ls₀ f PMap.empty) :
    ∀ (k i : Nat) (ls : List SRec) (ρ : WRes), (∀ x, x ∈ ls ↔ x ∈ ls₀) →
      sepRange (fun m => RSlot (ℍ := ℍ) δ σ S₀ (.ref A) αs ls (.loc m)) (ℓ + i) k ρ →
      wpTS ls (dropFill f ℓ i k) (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ .unit αs ls' v) ρ
  | 0, i, ls, ρ, _, hs => by
      obtain ⟨rfl, -⟩ := hs
      exact wpTS_val ls .unit _ _ (rslot_unit hlen ls)
  | k + 1, i, ls, ρ, hls, ⟨ρl, ρr, hc, hleaf, hrest⟩ => by
      show wpTS ls (.seq (.app (.val f) (.app (.val (.prim .free)) (.val (.loc (ℓ + i)))))
        (dropFill f ℓ (i + 1) k)) _ ρ
      refine wpTS_bind (.seq .hole (dropFill f ℓ (i + 1) k)) _ ls _ ρ ?_
      refine wpTS_bind (.appR (.val f) .hole) (.app (.val (.prim .free)) (.val (.loc (ℓ + i))))
        ls _ ρ ?_
      obtain ⟨ℓ', w, hk⟩ := hleaf
      obtain ⟨hl, c, ρw, hcw, hcell, hw⟩ := pure_sep_iff.mp hk
      have hℓ : ℓ' = ℓ + i := by
        have := congrArg Subtype.val hl; simpa using this.symm
      subst hℓ
      obtain ⟨R, hR, hρ⟩ := compS_reassoc hcw hc
      refine wpTS_free ls _ w _ ρ ⟨c, R, hρ, hcell, ?_⟩
      simp only [Kont.plug]
      refine wpTS_bind_frame .hole (.app (.val f) (.val w)) ls
        (fun ls' v => RSlot (ℍ := ℍ) δ σ S₀ .unit αs ls' v)
        (fun ls' => sepRange (fun m => RSlot (ℍ := ℍ) δ σ S₀ (.ref A) αs ls' (.loc m))
          (ℓ + i + 1) k)
        _ ?_ ?_ R ⟨ρw, ρr, hR, bang_app_rs hch hls hf hw, hrest⟩
      · intro ls' hls' τ h
        exact sepRange_mono' (fun m υ h => rslot_local (.ref A) (ext_of_same hls' υ) h) h
      · rintro ls' hls' u τ ⟨τu, τr, hτ, hu, hr⟩
        obtain ⟨rfl, rfl⟩ := relendableS_now hch hu
        rw [eq_of_compS_empty_left hτ]
        simp only [Kont.plug]
        refine wpTS_val ls' .unit _ τr ?_
        refine wpTS_1 ls' _ _ τr ?_
        refine dropFill_rs hch hlen f ℓ hf k (i + 1) ls' τr (fun x => (hls' x).trans (hls x)) ?_
        rwa [show ℓ + i + 1 = ℓ + (i + 1) by ring] at hr

/-- **`array_free`**: each cell freed, its element handed to the consumer held at `!`. -/
theorem pv_arrFree {Δ : LifeCtx} {Γ : Ctx VTy} (A : VTy) (hΓ : Ctx.DeadP Γ) :
    PV (ℍ := ℍ) δ σ S₀ Δ Γ (.val (.prim .drop)) (arrFreeTy A) := by
  refine pv_const (c := Val.prim .drop) hΓ (fun k γ => rfl) fun αs ls hlen _ => ⟨rfl, ?_⟩
  refine rslot_const hlen ls fun αs' ls' hr => ?_
  show RC δ σ S₀ (.arr _ _) αs' ls' (.val (Val.prim .drop)) PMap.empty
  rw [rc_arr_eq]
  intro v ρ₁ ρ₂ hv hc
  rw [eq_of_compS_empty_left hc]
  have hlen' : αs'.length = σ.length := (List.Forall₂.length_eq hr.1).trans hlen
  obtain ⟨f, v₂, hk⟩ := hv
  obtain ⟨rfl, σ₁, σ₂, hc', hf, h₂⟩ := pure_sep_iff.mp hk
  have e₁ : σ₁ = PMap.empty := hf.1
  subst e₁
  rw [eq_of_compS_empty_left hc']
  obtain ⟨ℓ, n, hq⟩ := h₂
  obtain ⟨⟨rfl, hn⟩, hs⟩ := pure_sep_iff.mp hq
  refine rc_ret_of_wpTS (wpTS_dropStep ls' f ℓ n _ σ₂ ?_)
  exact dropFill_rs hr.2 hlen' f ℓ hf n.toNat 0 ls' σ₂ (fun _ => Iff.rfl) (by simpa using hs)

end families

end Law2

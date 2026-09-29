import PositiveArrays.FrameFam

/-!
# PositiveArrays — the owned eliminator: each element consumed once by an indexed body

The positive array eliminator binds one variable per index, and a variable of the pattern may
be used only under an index scope (`[CC-arrays]` §3.1, Elim; §4.2's scope contexts
`C[for i:n. ·]`). Read linearly, at run-time `n`: every element of an owned `Array A` is
consumed exactly once, by a body that is run once per index and so is persistent,
`!(I32 ⊗ A ⇒ B)`, and the result is again indexed, `Array B`:

    elim : !(I32 ⊗ A ⇒ B) ⊗ Array A ⇒ Array B

The term is one `tab` whose tabulator takes the `i`-th element out of the source by `idx`
and `free`:

    mapE f (ℓ, n) = tab (n, λi. case idx((ℓ, n), i) { inl c → f (i, free c) | inr _ → () })

`wpTS_arrayMap`: from the source's `n` owned leaves, `mapE` runs to an `Array B` and leaves no
source cell. `array_free` (SPEC §9) is the instance at `B = 1` with the index dropped and no
result array.

**The length.** `tab (c, g)` places `arrLen c` cells (`c` when `c < 2³¹`, else `0`), while
`𝒱⟦[L]⟧` places `c.toNat` leaves for every `c`. `wpTS_arrayMap` carries `arrLen n = n`.
`arrMap_compatX`, the constant's compatibility lemma, takes `FamLenBound`: every family in the
relation has `tab`'s length. That is stated, not derived. Every family a program builds
satisfies it, since `tab` builds them, and it would hold by definition if the relation's clause
at `[L]` carried `⌜c < 2³¹⌝`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.PositiveArrays
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The relation's families have `tab`'s lengths. Stated, not derived. -/
def FamLenBound : Prop :=
  ∀ (L : VTy) (ls : List SRec) (δ : LSub) (ℓ : Loc) (n : UInt32) (ρ : WRes),
    vP (.fam L) ls δ (Val.arr ℓ n) ρ → arrLen n = n

/-- The tabulator, closed over `f` and the source `(ℓ, n)`. -/
def mapTab (f : Val) (ℓ : Loc) (n : UInt32) : Val :=
  .lam (.case (.app (.prim .idx) (.pair (Val.arr ℓ n).1 (.var 0)))
    (.app (f.1.shift 2 0) (.pair (.var 1) (.app (.prim .free) (.var 0))))
    .unit)

/-- `tab (n, mapTab f ℓ n)`. -/
def mapE (f : Val) (ℓ : Loc) (n : UInt32) : Expr :=
  .app (.val (.prim .tab)) (.val (Val.pair (Val.i32 n) (mapTab f ℓ n)))

theorem mapTab_beta (f : Val) (ℓ : Loc) (n j : UInt32) :
    Expr.subst 0 (Val.i32 j) (.case (.app (.prim .idx) (.pair (Val.arr ℓ n).1 (.var 0)))
      (.app (f.1.shift 2 0) (.pair (.var 1) (.app (.prim .free) (.var 0)))) .unit) =
    .case (.app (.val (.prim .idx)) (.val (Val.pair (Val.arr ℓ n) (Val.i32 j))))
      (.app (f.1.shift 1 0) (.pair (Val.i32 j).1 (.app (.prim .free) (.var 0)))) .unit := by
  simp [Expr.subst, Val.shift, arr_subst_shift_succ, subst_arr, shift_i32, Val.pair]

theorem mapTab_in (f : Val) (j : UInt32) (c : Loc) :
    Expr.subst 0 (Val.loc c)
      (.app (f.1.shift 1 0) (.pair (Val.i32 j).1 (.app (.prim .free) (.var 0)))) =
    .app (.val f) (.pair (.val (Val.i32 j)) (.app (.val (.prim .free)) (.val (.loc c)))) := by
  simp [Expr.subst, arr_subst_shift_succ, Expr.shift_zero]
  rfl

/-- One index of the tabulator: the source leaf at `ℓ + j` is consumed, and `f` runs. -/
theorem mapTab_wp {A B : VTy} {δ : LSub} {ls₀ ls : List SRec} (f : Val) (ℓ : Loc)
    (n j : UInt32) (hf : vP (.bang (.lolli (.tensor (.int .w32) A) B)) ls₀ δ f PMap.empty)
    (hls : ∀ x, x ∈ ls ↔ x ∈ ls₀) (hj : j < n) {ρ : WRes}
    (hleaf : ownLeaf A ls δ (ℓ + j.toNat) ρ) :
    wpTS ls (.app (.val (mapTab f ℓ n)) (.val (Val.i32 j))) (fun ls' => vP B ls' δ) ρ := by
  refine wpTS_lolli ls _ (Val.i32 j) _ ρ ?_
  rw [mapTab_beta]
  refine wpTS_bind (.case .hole _ _) _ ls _ ρ ?_
  refine wpTS_head (fun μ => Head.idx μ ℓ n j) rfl ls _ ρ ?_
  refine wpTS_val ls (idxAns ℓ n j) _ ρ ?_
  simp only [BoCa.BoLo.Kont.plug]
  have he : idxAns ℓ n j = .inj₁ (.loc (ℓ + j.toNat)) := by unfold idxAns; exact if_pos hj
  rw [he]
  refine wpTS_sum₁ ls _ _ _ _ ρ ?_
  rw [mapTab_in]
  obtain ⟨ℓ', w, hk⟩ := hleaf
  obtain ⟨hl, c, p, hcp, hcell, hw⟩ := pure_sep_iff.mp hk
  have hℓ : ℓ' = ℓ + j.toNat := by
    have := congrArg Subtype.val hl; simpa using this.symm
  subst hℓ
  refine wpTS_bind (.appR (.val f) (.pairR (Val.i32 j) .hole)) _ ls _ ρ ?_
  refine wpTS_free ls _ w _ ρ ⟨c, p, hcp, hcell, ?_⟩
  simp only [BoCa.BoLo.Kont.plug]
  exact bang_app hf hls ⟨Val.i32 j, w, pure_sep_mk rfl
    ⟨PMap.empty, p, compS_empty_left p, vP_i32 j, hw⟩⟩

/-- **The fill.** With the cells `ℓ, …, ℓ + i − 1` holding results, `ℓ + i, …` holding `()`, and
the source leaves `ℓs + i, …` not yet consumed, the rest of the fill runs to an `Array B`. -/
theorem mapFill_wp {A B : VTy} {δ : LSub} {ls₀ : List SRec} (f : Val) (ℓs ℓ : Loc)
    (n : UInt32) (hf : vP (.bang (.lolli (.tensor (.int .w32) A) B)) ls₀ δ f PMap.empty) :
    ∀ (k i : Nat) (ls : List SRec) (ρd ρt ρs ρ₀ ρ : WRes), (∀ x, x ∈ ls ↔ x ∈ ls₀) →
      i + k = n.toNat → sepRange (doneP B ls δ) ℓ i ρd → sepRange todoP (ℓ + i) k ρt →
      sepRange (ownLeaf A ls δ) (ℓs + i) k ρs → ResU.CompS ρd ρt ρ₀ → ResU.CompS ρ₀ ρs ρ →
      wpTS ls (tabFill (mapTab f ℓs n) ℓ n i k) (fun ls' => vP (.array B) ls' δ) ρ
  | 0, i, ls, ρd, ρt, ρs, ρ₀, ρ, _, hN, hd, ht, hs, hc₀, hc => by
      obtain ⟨rfl, -⟩ := ht
      obtain ⟨rfl, -⟩ := hs
      rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ₀),
        ResU.CompS.functional hc₀ (ResU.comp_empty_right ρd)]
      refine wpTS_val ls (Val.arr ℓ n) _ ρd (vP_fam_mk ?_)
      rw [← hN]; exact hd
  | k + 1, i, ls, ρd, ρt, ρs, ρ₀, ρ, hls, hN, hd, ⟨c, ρt', hct, hcell, ht'⟩,
      ⟨ρl, ρs', hcs, hleaf, hs'⟩, hc₀, hc => by
      have hi : i < n.toNat := by omega
      have hsz : i < UInt32.size := by
        have := n.toNat_lt; simp only [UInt32.size]; omega
      have hjn : (UInt32.ofNat i).toNat = i := UInt32.toNat_ofNat_of_lt' hsz
      have hj : UInt32.ofNat i < n := by rw [UInt32.lt_iff_toNat_lt, hjn]; exact hi
      show wpTS ls (.seq (.app (.app (.val (.prim .store)) (.val (.loc (ℓ + i))))
        (.app (.val (mapTab f ℓs n)) (.val (Val.i32 (UInt32.ofNat i)))))
        (tabFill (mapTab f ℓs n) ℓ n (i + 1) k)) _ ρ
      refine wpTS_bind (.seq .hole (tabFill (mapTab f ℓs n) ℓ n (i + 1) k)) _ ls _ ρ ?_
      -- `ρ = ρl ● (c ● (ρd ● ρt′) ● ρs′)`
      obtain ⟨R₀, hR₀, hρ₀⟩ := compS_lcomm hct hc₀
      obtain ⟨S, hS, hρS⟩ := compS_reassoc hρ₀ hc
      obtain ⟨Rs, hRs, hS'⟩ := compS_lcomm hcs hS
      obtain ⟨X, hX, hρX⟩ := compS_lcomm hS' hρS
      refine wpTS_bind_frame (.appR (.app (.val (.prim .store)) (.val (.loc (ℓ + i)))) .hole)
        (.app (.val (mapTab f ℓs n)) (.val (Val.i32 (UInt32.ofNat i)))) ls
        (fun ls' => vP B ls' δ)
        (fun ls' => ptoOwn (ℓ + i) .unit ⋆ ((sepRange (doneP B ls' δ) ℓ i ⋆
          sepRange todoP (ℓ + i + 1) k) ⋆ sepRange (ownLeaf A ls' δ) (ℓs + i + 1) k))
        _ ?_ ?_ ρ ⟨ρl, X, hρX, mapTab_wp f ℓs n _ hf hls hj (by rwa [hjn]),
          c, Rs, hX, hcell, R₀, ρs', hRs, ⟨ρd, ρt', hR₀, hd, ht'⟩, hs'⟩
      · intro ls' hls' σ ⟨σ₁, σ₂, hσ, h₁, σ₃, σ₄, hσ', ⟨σ₅, σ₆, hσ'', h₅, h₆⟩, h₄⟩
        exact ⟨σ₁, σ₂, hσ, h₁, σ₃, σ₄, hσ', ⟨σ₅, σ₆, hσ'', doneP_same hls' h₅, h₆⟩,
          sepRange_mono' (fun _ _ h => vP_same hls' h) h₄⟩
      · intro ls' hls' w σ ⟨σw, σr, hσ, hw, c', R', hR', hc', D, σs, hDs, ⟨σd, σt, hdt, hd', ht''⟩,
          hs''⟩
        simp only [BoCa.BoLo.Kont.plug]
        obtain ⟨G, hG, hσG⟩ := compS_lcomm hR' hσ
        refine wpTS_store ls' (ℓ + i) .unit w _ σ ⟨c', G, hσG, hc', ?_⟩
        intro c₃ σ₃ hc₃ hcomp₃
        refine wpTS_1 ls' _ _ σ₃ ?_
        -- `σ₃ = ((σd ● (σw ● c₃)) ● σt) ● σs`: the new leaf joins the results
        obtain ⟨L, hL, hσ₃⟩ := compS_exch hG hcomp₃
        obtain ⟨LD, hLD, hσ₃'⟩ := compS_reassoc' hDs hσ₃
        obtain ⟨Y, hY, hLD'⟩ := compS_reassoc' hdt hLD
        have hleaf' : doneP B ls' δ (ℓ + i) L :=
          ⟨ℓ + i, w, pure_sep_mk rfl ⟨c₃, σw, ResU.CompS.comm hL, hc₃, hw⟩⟩
        refine mapFill_wp f ℓs ℓ n hf k (i + 1) ls' Y σt σs LD σ₃
          (fun x => (hls' x).trans (hls x)) (by omega)
          (sepRange_append (ResU.CompS.comm hY) hd' ⟨L, PMap.empty, ResU.comp_empty_right L,
            hleaf', ⟨rfl, trivial⟩⟩) ?_ ?_ hLD' hσ₃'
        · rwa [show ℓ + i + 1 = ℓ + (i + 1) by ring] at ht''
        · rwa [show ℓs + i + 1 = ℓs + (i + 1) by ring] at hs''

/-- **The owned eliminator.** Every element of the source is consumed exactly once, by the
persistent body at its index, and the results form an `Array B`; no source cell is left. -/
theorem wpTS_arrayMap {A B : VTy} {δ : LSub} {ls₀ ls : List SRec} (f : Val)
    (hf : vP (.bang (.lolli (.tensor (.int .w32) A) B)) ls₀ δ f PMap.empty)
    (hls : ∀ x, x ∈ ls ↔ x ∈ ls₀) (ℓs : Loc) (n : UInt32) (hn : arrLen n = n) {ρ : WRes}
    (hs : sepRange (ownLeaf A ls δ) ℓs n.toNat ρ) :
    wpTS ls (mapE f ℓs n) (fun ls' => vP (.array B) ls' δ) ρ := by
  refine wpTS_tab ls n (mapTab f ℓs n) _ ρ ?_
  intro ℓ cells x hcells hx
  rw [hn] at hcells ⊢
  exact mapFill_wp f ℓs ℓ n hf n.toNat 0 ls PMap.empty cells ρ cells x hls (by simp)
    ⟨rfl, trivial⟩ (by simpa using hcells) (by simpa using hs) (compS_empty_left cells)
    (ResU.CompS.comm hx)

/-! ### As a constant, given the length bound -/

/-- `array_map : !(!(I32 ⊗ A ⇒ B) ⊗ Array A ⇒ Array B)`. -/
abbrev arrMapTy (A B : VTy) : VTy :=
  .bang (.lolli (.tensor (.bang (.lolli (.tensor (.int .w32) A) B)) (.array A)) (.array B))

/-- The body under `λp`, `let (f, a) = p` and `let (ℓ, n) = a`; inside the tabulator `a` is
`3` and `f` is `4`. -/
def mapBody : Expr :=
  .app (.prim .tab) (.pair (.var 0)
    (.lam (.case (.app (.prim .idx) (.pair (.var 3) (.var 0)))
      (.app (.var 5) (.pair (.var 1) (.app (.prim .free) (.var 0))))
      .unit)))

/-- `λp. let (f, a) = p in let (ℓ, n) = a in tab (n, λi. case idx(a, i) {…})`. -/
def mapV : Val := .lam (.letpair (.var 0) (.letpair (.var 0) mapBody))

theorem mapV_beta₁ (v : Val) :
    Expr.subst 0 v (.letpair (.var 0) (.letpair (.var 0) mapBody)) =
      .letpair (.val v) (.letpair (.var 0) mapBody) := by
  simp [Expr.subst, mapBody]

theorem mapV_steps (f : Val) (ℓ : Loc) (n : UInt32) :
    ((((Expr.letpair (.var 0) mapBody).subst 0 ((Val.arr ℓ n).shift 1 0)).subst 0 f)) =
      .letpair (.val (Val.arr ℓ n))
        (((mapBody.subst 2 ((Val.arr ℓ n).shift 3 0)).subst 2 (f.shift 2 0))) := by
  simp [Expr.subst, Val.shift, shift_arr, subst_arr]

theorem mapV_steps₂ (f : Val) (ℓ : Loc) (n : UInt32) :
    (((((mapBody.subst 2 ((Val.arr ℓ n).shift 3 0)).subst 2 (f.shift 2 0))).subst 0
      ((Val.i32 n).shift 1 0)).subst 0 (Val.loc ℓ)) = mapE f ℓ n := by
  have h₃ : ∀ (s : Val) (e : Expr), Expr.subst 2 s (Expr.shift 4 0 e) = Expr.shift 3 0 e :=
    fun s e => Expr.subst_shift 3 0 2 s e (by omega) (by omega)
  have h₂ : ∀ (s : Val) (e : Expr), Expr.subst 2 s (Expr.shift 3 0 e) = Expr.shift 2 0 e :=
    fun s e => Expr.subst_shift 2 0 2 s e (by omega) (by omega)
  simp [Expr.subst, mapBody, mapE, mapTab, Val.shift, Expr.shift_shift, shift_arr, subst_arr,
    Val.pair, Val.lam, Val.i32, h₂, h₃]

/-- **The owned eliminator as a constant**, given `FamLenBound`. -/
theorem arrMap_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (hbound : FamLenBound)
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ (.val mapV) (arrMapTy A B) := by
  refine sem_const hΓ rfl fun δ ls _ => ⟨rfl, ?_⟩
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨f, v₂, hk⟩ := hv
  obtain ⟨rfl, σ₁, σ₂, hc, hf, h₂⟩ := pure_sep_iff.mp hk
  have e₁ : σ₁ = PMap.empty := hf.1
  subst e₁
  rw [eq_of_compS_empty_left hc]
  obtain ⟨ℓ, n, rfl, hs⟩ := vP_fam_iff.mp h₂
  have hn := hbound _ _ _ _ _ _ h₂
  refine wpTS_lolli ls' _ _ _ _ ?_
  rw [mapV_beta₁]
  refine wpTS_tensor ls' f (Val.arr ℓ n) _ _ _ ?_
  rw [mapV_steps]
  refine wpTS_tensor ls' (Val.loc ℓ) (Val.i32 n) _ _ _ ?_
  rw [mapV_steps₂]
  exact wpTS_arrayMap f hf (fun _ => Iff.rfl) ℓ n hn hs

end BoCa.Fig16.LogRel.Core.PositiveArrays

end

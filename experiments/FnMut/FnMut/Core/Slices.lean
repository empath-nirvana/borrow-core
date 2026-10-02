import FnMut.Core.SliceFrames

/-!
# Core — slice borrows  `[spec §9]`

An owned array lent as a family of leaf borrows at one lifetime, with no cell (K2 of
`docs/strings-slices-design.md`):

    slice_borrow_mut : Array A ⊸ (∀'x ⊏ ⊓Δ. [Mut 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B
    slice_borrow_imm : Array A ⊸ (∀'x ⊏ ⊓Δ. [Imm 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B

The term is `withbor`'s own, `λa. λg. (a, g () a)`: the handle `(ℓ, n)` goes to the callback
and comes back. Nothing new runs; the `n` frames are proof only.

- `sliceBorrowM_compatX` is `withbor2_compatX` (`[TR]` 6.173) with `wpTS_M_frameFam` in place of
  one `wpTS_M_frameX`, and the family relation in place of `𝒱⟦Mut⟧` at one location.
- `sliceBorrowI_compatX` is `withbor1_compatX` (`[TR]` 6.172) with `wpTS_I_frameFam`.

Side conditions, at both modes: `A` and `B` each outlive a lifetime of `Δ`. With more than one
frame the callback runs below every frame but the innermost, and what it returns (and, at `Imm`,
the payloads handed back) is reboxed at each outer frame's lifetime by 6.60 (`vC_outlives`).
They hold for `i32`, `u8`, and every result that holds no borrow. At `Imm`, `A` is also scoped
in `Δ` (`withbor1`'s condition).

The element operations on a `mut` family (K4), with the terms of their `imm` counterparts:

| constant | type | term |
|---|---|---|
| `slice_get_mut` | `!([Mut @a A] ⊗ I32 ⇒ Mut @a A ⊕ 1)` | `idx` |
| `slice_len_mut` | `!([Mut @a A] ⇒ [Mut @a A] ⊗ I32)` | `array_size`'s |

`slice_get_mut` consumes the family and hands out one leaf: the others are forgotten, since a
`mut` leaf holds no `own` cell (`noOwn_mut`). A `mut` family is not duplicable, so its length is
read by handing the family back.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Head)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### K2 at `Mut` -/

/-- `[Mut 'c A]`. -/
abbrev VTy.sliceMut (a : Lifetime.Life) (A : VTy) : VTy := .fam (.mut a A)

/-- `slice_borrow : Array A ⊸ (∀'x ⊏ @bnd. [Mut 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B`. -/
def sliceBorrowMTy (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) : VTy :=
  .lolli (.array A)
    (.lolli (.all x bnd (.lolli (VTy.sliceMut (.var x) A) (.box (.var x) B)))
      (.tensor (.array A) B))

/-- **K2 at `Mut`.** -/
theorem sliceBorrowM_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (x : LifeVar)
    (hΓ : Ctx.DeadP Γ) (hsideA : ∃ b, Δ.Defines b ∧ VOutlives Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlives Δ b B)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
    SemV Δ Γ withbor (sliceBorrowMTy x Δ.meetOfDom A B) := by
  intro δ γ ls ρ hδ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  show wpTS ls withbor _ _
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ v₁ ρ₁ τ₀ hv₁ hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨ℓ, n, rfl, -, -⟩ := vP_fam_iff.mp hv₁
  have hβ₁ : Expr.subst 0 (Val.arr ℓ n)
        (Expr.val (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))))
      = Expr.val (Val.lam (.pair (.val (Val.arr ℓ n))
          (.app (.app BoCa.v0 unit') (.val (Val.arr ℓ n))))) := by
    simp [Expr.subst, BoCa.v0, BoCa.v1, unit', shift_arr]
  refine wpTS_lolli _ _ (Val.arr ℓ n) _ _ ?_
  rw [hβ₁]
  refine wpTS_val _ _ _ _ ?_
  intro ls₂ hext₂ vf ρ₂ τ hvf hc₂
  have hβ₂ : Expr.subst 0 vf
        (Expr.pair (.val (Val.arr ℓ n)) (.app (.app BoCa.v0 unit') (.val (Val.arr ℓ n))))
      = Expr.pair (.val (Val.arr ℓ n))
          (.app (.app (.val vf) (.val .unit)) (.val (Val.arr ℓ n))) := by
    simp [Expr.subst, BoCa.v0, unit', subst_arr]
  refine wpTS_lolli _ _ vf _ _ ?_
  rw [hβ₂]
  -- the owned family at the callback's list
  obtain ⟨ℓ', n', he, hn, hs⟩ := vP_fam_iff.mp (vC_local true (.array A) hext₂ hv₁)
  obtain ⟨rfl, rfl⟩ := Val.arr_inj he
  -- `MutFrame`'s premise from `A`'s side condition, and the rebox bound from `B`'s (6.60)
  obtain ⟨a, hdefa, hOa⟩ := hsideA
  obtain ⟨βA, hβA⟩ := hdefa δ hδ
  have hA := vC_outlives hδ hβA hOa true
  obtain ⟨b, hdefb, hOb⟩ := hsideB
  obtain ⟨βB, hβB⟩ := hdefb δ hδ
  have hB := vC_outlives hδ hβB hOb true
  -- the frames' postcondition: the handle beside a result of `B`
  let Φ : List SRec → Val → WProp := fun ls' v =>
    ex fun v'' => ⌜v = Val.pair (Val.arr ℓ n) v''⌝ ⋆ vP B ls' δ v''
  have hΦ : ∀ ls' v σ, Φ ls' v σ → BoLo.Outlives σ βB := by
    rintro ls' v σ ⟨v'', hk⟩
    exact hB ls' v'' σ (pure_sep_iff.mp hk).2
  refine wpTS_M_frameFam A δ βA (fun ls' w σ h => hA ls' w σ h) _ ls₂ Φ βB hΦ n.toNat ℓ
    (fun ls' => vP (.tensor (.array A) B) ls' δ) ?_ τ ⟨ρ₁, ρ₂, hc₂, hs, ?_⟩
  · -- the handle and the returned leaves are `Array A`
    rintro ls' v σ ⟨σo, σB, hσ, ho, v'', hk⟩
    obtain ⟨rfl, hv''⟩ := pure_sep_iff.mp hk
    exact ⟨Val.arr ℓ n, v'', pure_sep_mk rfl ⟨σo, σB, hσ, vP_fam_mk hn ho, hv''⟩⟩
  -- `⋔α` at `@ρ₂ ⊓ ⊓Δδ`
  obtain ⟨a₂, ha₂⟩ := ρ₂.exists_atLife
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  refine ⟨a₂ ⊓ m, fun α hα => ⟨?_, outlives_of_atLife ha₂ (lt_of_lt_of_le hα inf_le_left)⟩⟩
  intro ρm σ' hm' hcm
  -- the `mut` leaves at `α` are the family `[Mut 'x A]` at `δ['x ↦ α]`
  have e : (fun ls₀ => vC true A ls₀ (δ.extend x α)) = (fun ls₀ => vC true A ls₀ δ) :=
    funext fun ls₀ => vC_extend_of_not_free hfree₁ true ls₀ δ α
  have hmut' : vP (VTy.sliceMut (.var x) A) ls₂ (δ.extend x α) (Val.arr ℓ n) ρm := by
    refine vP_fam_mk hn (sepRange_mono' (fun k σ h => ?_) hm')
    refine ⟨α, interp_ext_self δ x α, k, pure_sep_mk rfl ?_⟩
    show ptoMutS k α ls₂ (fun ls₀ => vC true A ls₀ (δ.extend x α)) σ
    rw [e]; exact h
  refine wpTS_bind (.pairR (Val.arr ℓ n) .hole)
    (.app (.app (.val vf) (.val .unit)) (.val (Val.arr ℓ n))) ls₂ _ σ' ?_
  have hlt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_right⟩
  have hwpf := hvf ls₂ (Ext.refl _ _) α PMap.empty ρ₂ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ₂)
  refine wpTS_bind_frame (.appL .hole (Val.arr ℓ n)) (.app (.val vf) (.val .unit)) ls₂
    (fun ls'' => vP (.lolli (VTy.sliceMut (.var x) A) (.box (.var x) B)) ls'' (δ.extend x α))
    (fun ls'' => vP (VTy.sliceMut (.var x) A) ls'' (δ.extend x α) (Val.arr ℓ n)) _
    (fun ls'' hls ρ h => vP_same hls h) ?_ σ' ⟨ρ₂, ρm, hcm, hwpf, hmut'⟩
  rintro ls'' - vg σ'' ⟨σ₁, σ₂, hcσ'', hvg, hmut''⟩
  simp only [BoCa.BoLo.Kont.plug]
  refine wpTS_mono (fun ls''' v'' ρ'' hb => ?_) σ''
    (hvg ls'' (Ext.refl _ _) (Val.arr ℓ n) σ₂ σ'' hmut'' hcσ'')
  -- the callback's result, `[α] 𝒱⟦B⟧δ(v″)`; `Φ` keeps `𝒱⟦B⟧` only
  obtain ⟨α', hα', hBδ', -⟩ := hb
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  have hB' : vP B ls''' δ v'' ρ'' := by
    rw [vC_extend_of_not_free hfree₂] at hBδ'; exact hBδ'
  exact wpTS_val ls''' (.pair (Val.arr ℓ n) v'') _ ρ'' ⟨v'', pure_sep_mk rfl hB'⟩

/-! ### K2 at `Imm` -/

/-- `slice_borrow : Array A ⊸ (∀'x ⊏ @bnd. [Imm 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B`. -/
def sliceBorrowITy (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) : VTy :=
  .lolli (.array A)
    (.lolli (.all x bnd (.lolli (.arrayImm (.var x) A) (.box (.var x) B)))
      (.tensor (.array A) B))

/-- A leaf of the frames is a leaf of `[Imm 'x A]` at `δ['x ↦ α]`: `withbor1_compatX`'s step
from the frame's record and cell to `𝒱⟦Imm 'x A⟧`. -/
theorem immLeaf_to_vP {A : VTy} {x : LifeVar} (hfree : ¬ VFree x A) {ls : List SRec}
    {δ : LSub} {α : Life} {m : Loc} {ρ : WRes} (h : immLeaf A ls δ α m ρ) :
    vP (.imm (.var x) A) ls (δ.extend x α) (.loc m) ρ := by
  obtain ⟨⟨r, hr, hle, hT, hδr⟩, hm⟩ := h
  refine ⟨α, interp_ext_self δ x α, m, pure_sep_mk ⟨rfl, cohE_of_coh
    (Or.inl ⟨r, hr, hle.symm, hT.symm, fun y hy => ?_⟩)⟩ ?_⟩
  · rw [hδr]
    rw [hT] at hy
    exact find?_extend_ne δ α (fun e => by subst e; exact hfree hy)
  · exact ptoImmS_mono (fun ls₀ u σ h => by
      rw [vC_extend_of_not_free hfree]; exact vO_obs A h) hm

/-- **K2 at `Imm`.** -/
theorem sliceBorrowI_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (x : LifeVar)
    (hΓ : Ctx.DeadP Γ) (hsc : VScoped Δ A) (hsideA : ∃ b, Δ.Defines b ∧ VOutlives Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlives Δ b B)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) :
    SemV Δ Γ withbor (sliceBorrowITy x Δ.meetOfDom A B) := by
  intro δ γ ls ρ hδ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  show wpTS ls withbor _ _
  refine wpTS_val _ _ _ _ ?_
  intro ls₁ _ v₁ ρ₁ τ₀ hv₁ hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨ℓ, n, rfl, -, -⟩ := vP_fam_iff.mp hv₁
  have hβ₁ : Expr.subst 0 (Val.arr ℓ n)
        (Expr.val (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))))
      = Expr.val (Val.lam (.pair (.val (Val.arr ℓ n))
          (.app (.app BoCa.v0 unit') (.val (Val.arr ℓ n))))) := by
    simp [Expr.subst, BoCa.v0, BoCa.v1, unit', shift_arr]
  refine wpTS_lolli _ _ (Val.arr ℓ n) _ _ ?_
  rw [hβ₁]
  refine wpTS_val _ _ _ _ ?_
  intro ls₂ hext₂ vf ρ₂ τ hvf hc₂
  have hβ₂ : Expr.subst 0 vf
        (Expr.pair (.val (Val.arr ℓ n)) (.app (.app BoCa.v0 unit') (.val (Val.arr ℓ n))))
      = Expr.pair (.val (Val.arr ℓ n))
          (.app (.app (.val vf) (.val .unit)) (.val (Val.arr ℓ n))) := by
    simp [Expr.subst, BoCa.v0, unit', subst_arr]
  refine wpTS_lolli _ _ vf _ _ ?_
  rw [hβ₂]
  obtain ⟨ℓ', n', he, hn, hs⟩ := vP_fam_iff.mp (vC_local true (.array A) hext₂ hv₁)
  obtain ⟨rfl, rfl⟩ := Val.arr_inj he
  obtain ⟨a, hdefa, hOa⟩ := hsideA
  obtain ⟨βA, hβA⟩ := hdefa δ hδ
  have hA := vC_outlives hδ hβA hOa true
  obtain ⟨b, hdefb, hOb⟩ := hsideB
  obtain ⟨βB, hβB⟩ := hdefb δ hδ
  have hB := vC_outlives hδ hβB hOb true
  let Φ : List SRec → Val → WProp := fun ls' v =>
    ex fun v'' => ⌜v = Val.pair (Val.arr ℓ n) v''⌝ ⋆ vP B ls' δ v''
  have hΦ : ∀ ls' v σ, Φ ls' v σ → BoLo.Outlives σ βB := by
    rintro ls' v σ ⟨v'', hk⟩
    exact hB ls' v'' σ (pure_sep_iff.mp hk).2
  have hΦext : ∀ ls₁ ls₂ w σ, Ext ls₁ ls₂ σ → Φ ls₁ w σ → Φ ls₂ w σ := by
    rintro ls₁ ls₂ w σ hk ⟨v'', hk'⟩
    obtain ⟨hw, hv''⟩ := pure_sep_iff.mp hk'
    exact ⟨v'', pure_sep_mk hw (vC_local true B hk hv'')⟩
  refine wpTS_mono (P := fun ls' v => sepRange (ownLeaf A ls' δ) ℓ n.toNat ⋆ Φ ls' v) ?_ τ
    (wpTS_I_frameFam A δ βA (fun ls' w σ h => hA ls' w σ h) (admWf_of_vScoped hsc hδ) _ Φ βB
      hΦ hΦext n.toNat ℓ ls₂ τ ⟨ρ₁, ρ₂, hc₂, hs, ?_⟩)
  · rintro ls' v σ ⟨σo, σB, hσ, ho, v'', hk⟩
    obtain ⟨rfl, hv''⟩ := pure_sep_iff.mp hk
    exact ⟨Val.arr ℓ n, v'', pure_sep_mk rfl ⟨σo, σB, hσ, vP_fam_mk hn ho, hv''⟩⟩
  obtain ⟨a₂, ha₂⟩ := ρ₂.exists_atLife
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  refine ⟨a₂ ⊓ m, fun α hα => ⟨?_, outlives_of_atLife ha₂ (lt_of_lt_of_le hα inf_le_left)⟩⟩
  -- the callback's list `ls′` is `Ext`-above `ls₂` at its resource `ρ₂`
  intro ls' hext ρm σ' hm' hcm
  have himm' : vP (.arrayImm (.var x) A) ls' (δ.extend x α) (Val.arr ℓ n) ρm :=
    vP_fam_mk hn (sepRange_mono' (fun k σ h => immLeaf_to_vP hfree₁ h) hm')
  refine wpTS_bind (.pairR (Val.arr ℓ n) .hole)
    (.app (.app (.val vf) (.val .unit)) (.val (Val.arr ℓ n))) ls' _ σ' ?_
  have hlt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_right⟩
  have hwpf := hvf ls' hext α PMap.empty ρ₂ ⟨rfl, hlt⟩ (ResU.comp_empty_right ρ₂)
  refine wpTS_bind_frame (.appL .hole (Val.arr ℓ n)) (.app (.val vf) (.val .unit)) ls'
    (fun ls'' => vP (.lolli (.arrayImm (.var x) A) (.box (.var x) B)) ls'' (δ.extend x α))
    (fun ls'' => vP (.arrayImm (.var x) A) ls'' (δ.extend x α) (Val.arr ℓ n)) _
    (fun ls'' hls ρ h => vP_same hls h) ?_ σ' ⟨ρ₂, ρm, hcm, hwpf, himm'⟩
  rintro ls'' - vg σ'' ⟨σ₁, σ₂, hcσ'', hvg, himm''⟩
  simp only [BoCa.BoLo.Kont.plug]
  refine wpTS_mono (fun ls''' v'' ρ'' hb => ?_) σ''
    (hvg ls'' (Ext.refl _ _) (Val.arr ℓ n) σ₂ σ'' himm'' hcσ'')
  obtain ⟨α', hα', hBδ', -⟩ := hb
  rw [interp_ext_self] at hα'
  cases Option.some.inj hα'
  have hB' : vP B ls''' δ v'' ρ'' := by
    rw [vC_extend_of_not_free hfree₂] at hBδ'; exact hBδ'
  exact wpTS_val ls''' (.pair (Val.arr ℓ n) v'') _ ρ'' ⟨v'', pure_sep_mk rfl hB'⟩

/-! ### K4: the element operations on a family of leaves -/

/-- A `mut` leaf borrow holds no `own` cell. -/
theorem noOwn_mut {a : Lifetime.Life} {A : VTy} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : vP (.mut a A) ls δ v ρ) : NoOwn ρ := by
  obtain ⟨α, -, ℓ, hs⟩ := h
  obtain ⟨-, b, u, σ, hσ, Q, hw, ls₀, -, rfl, -⟩ := pure_sep_iff.mp hs
  exact ResU.restrict_single_other (by simp)

/-- `idx` on a family whose leaves hold no `own` cell: the leaf at the index, the rest
forgotten.  `[spec §9]` -/
theorem famGet_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {L : VTy} (hΓ : Ctx.DeadP Γ)
    (hL : ∀ ls δ m ρ, vP L ls δ (.loc m) ρ → NoOwn ρ) :
    SemV Δ Γ (.val (.prim .idx)) (.bang (.lolli (.tensor (.fam L) (.int .w32)) (.sum L .unit))) := by
  refine sem_const hΓ rfl fun δ ls _ => ⟨rfl, ?_⟩
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨ℓ, n, i, rfl, -, hs⟩ := vP_fam_idx hv
  refine wpTS_head (fun μ => Head.idx μ ℓ n i) rfl ls' _ σ ?_
  have hσ : NoOwn σ := sepRange_closed noOwn_empty
    (fun _ _ _ hc h₁ h₂ => noOwn_compS hc h₁ h₂) (hL ls' δ) hs
  rcases idxAns_cases ℓ n i with ⟨hi, he⟩ | he
  · rw [he]
    obtain ⟨ρi, ρr, hc, hPi, -⟩ := sepRange_pick hi hs
    refine wpTS_drop (noOwn_right hc hσ) (ResU.CompS.comm hc) ?_
    exact wpTS_val ls' _ _ _ (Or.inl ⟨_, pure_sep_mk rfl hPi⟩)
  · rw [he]
    refine wpTS_drop hσ (ResU.comp_empty_right σ) ?_
    exact wpTS_val ls' _ _ _ (Or.inr ⟨.unit, pure_sep_mk rfl ⟨rfl, rfl⟩⟩)

/-- `array_size`'s term on any family: the family handed back beside its length.  `[spec §9]` -/
theorem famSize_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {L : VTy} (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val sizeV) (.bang (.lolli (.fam L) (.tensor (.fam L) (.int .w32)))) := by
  refine sem_const hΓ rfl fun δ ls _ => ⟨rfl, ?_⟩
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨ℓ, n, rfl, hn, hs⟩ := vP_fam_iff.mp hv
  refine wpTS_lolli ls' _ _ _ _ ?_
  show wpTS ls' (.letpair (.val (Val.arr ℓ n)) (.pair (.pair (.var 1) (.var 0)) (.var 0))) _ _
  refine wpTS_tensor ls' (Val.loc ℓ) (Val.i32 n) _ _ _ ?_
  refine wpTS_val ls' (Val.pair (Val.arr ℓ n) (Val.i32 n)) _ _ ?_
  exact ⟨_, _, pure_sep_mk rfl ⟨σ, PMap.empty, ResU.comp_empty_right σ, vP_fam_mk hn hs,
    vP_i32 n⟩⟩

/-- `slice_get_mut : !([Mut @a A] ⊗ I32 ⇒ Mut @a A ⊕ 1)`.  `[spec §9]` -/
abbrev sliceGetMTy (a : Lifetime.Life) (A : VTy) : VTy :=
  .bang (.lolli (.tensor (.sliceMut a A) (.int .w32)) (.sum (.mut a A) .unit))

/-- `slice_len_mut : !([Mut @a A] ⇒ [Mut @a A] ⊗ I32)`.  `[spec §9]` -/
abbrev sliceLenMTy (a : Lifetime.Life) (A : VTy) : VTy :=
  .bang (.lolli (.sliceMut a A) (.tensor (.sliceMut a A) (.int .w32)))

theorem sliceGetM_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ (.val (.prim .idx)) (sliceGetMTy a A) :=
  famGet_compatX hΓ fun _ _ _ _ h => noOwn_mut h

theorem sliceLenM_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ (.val sizeV) (sliceLenMTy a A) :=
  famSize_compatX hΓ

end BoCa.Fig16.LogRel.Core

end

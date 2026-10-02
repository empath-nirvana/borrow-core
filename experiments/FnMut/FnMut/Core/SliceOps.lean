import FnMut.Core.Slices

/-!
# Core — splits and writes on a borrowed family  `[spec §9]`

K3 and K5 of `docs/strings-slices-design.md`, on the families `[Imm @a A]` and `[Mut @a A]` that
`slice_borrow` lends:

| constant | type | term |
|---|---|---|
| `slice_split_imm`, `slice_split_mut` | `!([L] ⊗ I32 ⇒ ([L] ⊗ [L]) ⊕ [L])` | `split` |
| `slice_empty_imm`, `slice_empty_mut` | `[L]` | `(0, 0)` |
| `slice_replace_mut` | `!([Mut @a A] ⊗ (I32 ⊗ A) ⇒ [Mut @a A] ⊗ (A ⊕ A))` | `array_replace`'s |
| `slice_swap_mut` | `!([Mut @a A] ⊗ (I32 ⊗ I32) ⇒ [Mut @a A])` | `swapV` |

**Split.** `split ((ℓ, n), i)` at `i ≤ n` answers `(ℓ, i)` and `(ℓ + i, n − i)`, and otherwise
hands the family back. It is a machine step (`Head.split`), not a term over the host's `le_u`
and `sub`: a split that subtracted with the host would be sound only at hosts whose subtraction
subtracts, and every theorem holds at every host (as `count`, SPEC §16). The relation half is
`vP_fam_split`: a family is a separating conjunction of its leaves, so the two parts are
disjoint and at the same leaf predicate, hence at the same lifetime. `famSplit_compatX` holds at
every leaf; the constants are its instances at `imm` and `mut` leaves. An owned family is not
split: it is sound in the model, but a block is freed once (design §5.4).

**Writes.** A `mut` leaf is opened by Mut Anti-Frame (`[TR]` 6.66, `wpTS_M_antiFrameX`), as
`withswap` opens its cell (`withswap_compatX`): the family is the leaf beside the rest
(`sepRange_pick`, or `sepRange_pick2R` for two leaves), the leaf's cell is read and written,
and the leaf goes back into the family with its new payload. `slice_swap_mut` at `i = j` opens
the one leaf and writes it twice.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### K3: the split and the empty family -/

/-- `!([L] ⊗ I32 ⇒ ([L] ⊗ [L]) ⊕ [L])`.  `[spec §9]` -/
abbrev famSplitTy (L : VTy) : VTy :=
  .bang (.lolli (.tensor (.fam L) (.int .w32)) (.sum (.tensor (.fam L) (.fam L)) (.fam L)))

/-- The answer `split` gives: the two parts in range, the family back otherwise. -/
theorem splitAns_cases (ℓ : Loc) (n i : UInt32) :
    (i ≤ n ∧ splitAns ℓ n i = .inj₁ (.pair (Val.arr ℓ i) (Val.arr (ℓ + i.toNat) (n - i)))) ∨
      splitAns ℓ n i = .inj₂ (Val.arr ℓ n) := by
  unfold splitAns
  by_cases h : i ≤ n
  · exact Or.inl ⟨h, if_pos h⟩
  · exact Or.inr (if_neg h)

/-- **K3**: `split` on a family at any leaf.  `[spec §9]` -/
theorem famSplit_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {L : VTy} (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val (.prim .split)) (famSplitTy L) := by
  refine sem_const hΓ rfl fun δ ls _ => ⟨rfl, ?_⟩
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨ℓ, n, i, rfl, hn, hs⟩ := vP_fam_idx hv
  refine wpTS_head (fun μ => Head.split μ ℓ n i) rfl ls' _ σ ?_
  have hfam : vP (.fam L) ls' δ (Val.arr ℓ n) σ := vP_fam_mk hn hs
  rcases splitAns_cases ℓ n i with ⟨hi, he⟩ | he
  · rw [he]
    obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := vP_fam_split hfam hi
    exact wpTS_val ls' _ _ _
      (Or.inl ⟨_, pure_sep_mk rfl ⟨_, _, pure_sep_mk rfl ⟨ρ₁, ρ₂, hc, h₁, h₂⟩⟩⟩)
  · rw [he]
    exact wpTS_val ls' _ _ _ (Or.inr ⟨_, pure_sep_mk rfl hfam⟩)

/-- `slice_split_imm : !([Imm @a A] ⊗ I32 ⇒ ([Imm @a A] ⊗ [Imm @a A]) ⊕ [Imm @a A])`.
`[spec §9]` -/
abbrev sliceSplitITy (a : Lifetime.Life) (A : VTy) : VTy := famSplitTy (.imm a A)

/-- `slice_split_mut : !([Mut @a A] ⊗ I32 ⇒ ([Mut @a A] ⊗ [Mut @a A]) ⊕ [Mut @a A])`.
`[spec §9]` -/
abbrev sliceSplitMTy (a : Lifetime.Life) (A : VTy) : VTy := famSplitTy (.mut a A)

theorem sliceSplitI_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ (.val (.prim .split)) (sliceSplitITy a A) :=
  famSplit_compatX hΓ

theorem sliceSplitM_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ (.val (.prim .split)) (sliceSplitMTy a A) :=
  famSplit_compatX hΓ

/-- The empty family `(0, 0)`.  `[spec §9]` -/
def emptyFamV : Val := Val.arr 0 0

/-- **K3**: the empty family, at any leaf: no leaves, so no resource.  `[spec §9]` -/
theorem famEmpty_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {L : VTy} (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val emptyFamV) (.fam L) :=
  sem_const hΓ rfl fun _ _ _ => vP_fam_mk (by decide) ⟨rfl, trivial⟩

theorem sliceEmptyI_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ (.val emptyFamV) (.arrayImm a A) :=
  famEmpty_compatX hΓ

theorem sliceEmptyM_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ (.val emptyFamV) (.sliceMut a A) :=
  famEmpty_compatX hΓ

/-! ### K5: `slice_replace_mut` -/

/-- `slice_replace_mut : !([Mut @a A] ⊗ (I32 ⊗ A) ⇒ [Mut @a A] ⊗ (A ⊕ A))`.  `[spec §9]` -/
abbrev sliceReplaceMTy (a : Lifetime.Life) (A : VTy) : VTy :=
  .bang (.lolli (.tensor (.sliceMut a A) (.tensor (.int .w32) A))
    (.tensor (.sliceMut a A) (.sum A A)))

/-- A leaf of `[Mut @a A]`: its lifetime and its `mut` cell. -/
theorem vP_mut_leaf {a : Lifetime.Life} {A : VTy} {ls : List SRec} {δ : LSub} {m : Loc}
    {ρ : WRes} (h : vP (.mut a A) ls δ (.loc m) ρ) :
    ∃ α, a.interp δ = some α ∧ ptoMutS m α ls (fun ls₀ => vC true A ls₀ δ) ρ := by
  obtain ⟨α, ha, ℓ', hs⟩ := h
  obtain ⟨hl, hmut⟩ := pure_sep_iff.mp hs
  have hℓ : ℓ' = m := by
    have := congrArg Subtype.val hl; simpa using this.symm
  subst hℓ
  exact ⟨α, ha, hmut⟩

theorem vP_mut_leaf_mk {a : Lifetime.Life} {A : VTy} {ls : List SRec} {δ : LSub} {m : Loc}
    {α : Life} {ρ : WRes} (ha : a.interp δ = some α)
    (h : ptoMutS m α ls (fun ls₀ => vC true A ls₀ δ) ρ) : vP (.mut a A) ls δ (.loc m) ρ :=
  ⟨α, ha, m, pure_sep_mk rfl h⟩

/-- **K5**: `array_replace`'s term on a `mut` family.  `[spec §9]` -/
theorem sliceReplaceM_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ (.val replaceV) (sliceReplaceMTy a A) := by
  refine sem_const hΓ rfl fun δ ls _ => ⟨rfl, ?_⟩
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨v₁, v₂, hk⟩ := hv
  obtain ⟨rfl, σ₁, σ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hk
  obtain ⟨ℓ, n, rfl, hn, hs⟩ := vP_fam_iff.mp h₁
  obtain ⟨w₁, x, hk₂⟩ := h₂
  obtain ⟨rfl, ρ₀, σx, hc₂, ⟨e₀, i, rfl⟩, hx⟩ := pure_sep_iff.mp hk₂
  subst e₀
  rw [eq_of_compS_empty_left hc₂] at hc
  refine wpTS_lolli ls' _ _ _ _ ?_
  rw [replace_body₁]
  refine wpTS_tensor ls' (Val.arr ℓ n) (Val.pair (Val.i32 i) x) _ _ _ ?_
  rw [replace_body₂]
  refine wpTS_tensor ls' (Val.i32 i) x _ _ _ ?_
  rw [replace_body₃]
  refine wpTS_bind (.case .hole _ _) _ ls' _ σ ?_
  refine wpTS_head (fun μ => Head.idx μ ℓ n i) rfl ls' _ σ ?_
  refine wpTS_val ls' (idxAns ℓ n i) _ σ ?_
  simp only [Kont.plug]
  rcases idxAns_cases ℓ n i with ⟨hi, he⟩ | he
  · rw [he]
    refine wpTS_sum₁ ls' _ _ _ _ σ ?_
    rw [replace_in]
    obtain ⟨ρi, ρr, hci, hPi, hback⟩ := sepRange_pick hi hs
    obtain ⟨α, ha, hmut⟩ := vP_mut_leaf hPi
    -- `σ = ρi ● F`, `F = ρr ● σx`
    obtain ⟨F, hF, hσ⟩ := compS_reassoc hci hc
    -- Mut Anti-Frame at the leaf; `old` is the payload it hands over
    refine wpTS_M_antiFrameX _ α A δ _ ls' _ σ ⟨ρi, F, hσ, hmut, ?_⟩
    intro old c₁ c₂ hc₁ hcc p₁ p₂ hp₁ hcp
    obtain ⟨s, hs', hsp⟩ := compS_exch hcc hcp
    refine wpTS_bind (.pairR (Val.arr ℓ n) (.inj₁ .hole)) _ ls' _ p₂ ?_
    refine wpTS_bind (.appR (.val (.lam _)) .hole) (eLoad (ℓ + i.toNat)) ls' _ p₂ ?_
    refine wpTS_load ls' _ old _ p₂ ⟨c₁, s, ResU.CompS.comm hsp, hc₁, ?_⟩
    intro c₃ p₃ hc₃ hp₃
    rw [hc₃, ← hc₁] at hp₃
    simp only [Kont.plug]
    refine wpTS_lolli ls' _ old _ p₃ ?_
    rw [replace_store]
    refine wpTS_bind (.seq .hole (.val old)) (eStore (ℓ + i.toNat) x) ls' _ p₃ ?_
    refine wpTS_store ls' _ old x _ p₃ ⟨c₁, s, ResU.CompS.comm hp₃, hc₁, ?_⟩
    intro c₄ p₄ hc₄ hp₄
    simp only [Kont.plug]
    refine wpTS_1 ls' _ _ p₄ ?_
    refine wpTS_val ls' old _ p₄ ?_
    refine wpTS_val ls' (Val.pair (Val.arr ℓ n) (Val.inj₁ old)) _ p₄ ?_
    -- `s = F ● p₁ = σx ● W`, `W = ρr ● p₁`
    obtain ⟨W, hW, hsW⟩ := compS_reassoc (ResU.CompS.comm hF) hs'
    -- the new value `x` in the cell, and the leaf back in the family beside `old`
    refine ⟨x, c₄, s, ResU.CompS.comm hp₄, hc₄, σx, W, hsW, hx, ?_⟩
    intro m₁ R hm₁ hR
    obtain ⟨X, hX, hRX⟩ := compS_reassoc' hW (ResU.CompS.comm hR)
    exact ⟨_, _, pure_sep_mk rfl ⟨X, p₁, hRX,
      vP_fam_mk hn (hback m₁ X hX (vP_mut_leaf_mk ha hm₁)),
      Or.inl ⟨old, pure_sep_mk rfl hp₁⟩⟩⟩
  · rw [he]
    refine wpTS_sum₂ ls' _ _ _ _ σ ?_
    rw [replace_out]
    exact wpTS_val ls' _ _ σ ⟨_, _, pure_sep_mk rfl
      ⟨σ₁, σx, hc, vP_fam_mk hn hs, Or.inr ⟨x, pure_sep_mk rfl hx⟩⟩⟩

/-! ### K5: `slice_swap_mut` -/

/-- Two distinct leaves of a range, with the rest framed, and the range rebuilt from any two
leaves in their places. -/
theorem sepRange_pick2R {P : Loc → WProp} {ℓ : Loc} {n i j : Nat} (hij : i < j) (hj : j < n)
    {ρ : WRes} (h : sepRange P ℓ n ρ) :
    ∃ ρi ρj ρr ρ₁, ResU.CompS ρj ρr ρ₁ ∧ ResU.CompS ρi ρ₁ ρ ∧ P (ℓ + i) ρi ∧ P (ℓ + j) ρj ∧
      ∀ σi σj σ₁ ρ', ResU.CompS σj ρr σ₁ → ResU.CompS σi σ₁ ρ' → P (ℓ + i) σi →
        P (ℓ + j) σj → sepRange P ℓ n ρ' := by
  obtain ⟨m, rfl⟩ : ∃ m, n = j + (m + 1) := ⟨n - j - 1, by omega⟩
  obtain ⟨A, B, hAB, hA, ρj, C, hjC, hPj, hC⟩ := sepRange_split h
  obtain ⟨ρi, Ar, hiA, hPi, hbackA⟩ := sepRange_pick hij hA
  -- `ρ = (ρi ● Ar) ● (ρj ● C) = ρi ● (ρj ● (Ar ● C))`
  obtain ⟨X, hX, hρ⟩ := compS_reassoc hiA hAB
  obtain ⟨Y, hY, hX'⟩ := compS_lcomm hjC hX
  refine ⟨ρi, ρj, Y, X, hX', hρ, hPi, hPj, fun σi σj σ₁ ρ' h₁ h₂ hPi' hPj' => ?_⟩
  obtain ⟨B', hB', hσ₁⟩ := compS_lcomm hY h₁
  obtain ⟨A', hA', hρ'⟩ := compS_reassoc' hσ₁ h₂
  exact sepRange_append hρ' (hbackA σi A' hA' hPi') ⟨σj, C, hB', hPj', hC⟩

/-- `sepRange_pick2R` at two distinct leaves in either order. -/
theorem sepRange_pick2N {P : Loc → WProp} {ℓ : Loc} {n i j : Nat} (hij : i ≠ j) (hi : i < n)
    (hj : j < n) {ρ : WRes} (h : sepRange P ℓ n ρ) :
    ∃ ρi ρj ρr ρ₁, ResU.CompS ρj ρr ρ₁ ∧ ResU.CompS ρi ρ₁ ρ ∧ P (ℓ + i) ρi ∧ P (ℓ + j) ρj ∧
      ∀ σi σj σ₁ ρ', ResU.CompS σj ρr σ₁ → ResU.CompS σi σ₁ ρ' → P (ℓ + i) σi →
        P (ℓ + j) σj → sepRange P ℓ n ρ' := by
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · exact sepRange_pick2R hlt hj h
  · obtain ⟨ρj, ρi, ρr, ρ₁, h₁, h₂, hPj, hPi, hback⟩ := sepRange_pick2R hgt hi h
    obtain ⟨ρ₁', h₁', h₂'⟩ := compS_lcomm h₁ h₂
    refine ⟨ρi, ρj, ρr, ρ₁', h₁', h₂', hPi, hPj, fun σi σj σ₁ ρ' k₁ k₂ kPi kPj => ?_⟩
    obtain ⟨σ₁', k₁', k₂'⟩ := compS_lcomm k₁ k₂
    exact hback σj σi σ₁' ρ' k₁' k₂' kPj kPi

/-- `slice_swap_mut : !([Mut @a A] ⊗ (I32 ⊗ I32) ⇒ [Mut @a A])`.  `[spec §9]` -/
abbrev sliceSwapMTy (a : Lifetime.Life) (A : VTy) : VTy :=
  .bang (.lolli (.tensor (.sliceMut a A) (.tensor (.int .w32) (.int .w32))) (.sliceMut a A))

/-- Under `d` (`0`), `c` (`1`) and the family `f` (`5`):
`(λx. (λy. store c y; store d x; f) (load d)) (load c)`. -/
def slSwapCellsE : Expr :=
  .app (.val (.lam (.app (.val (.lam
      (.seq (.app (.app (.val (.prim .store)) (.var 3)) (.var 0))
        (.seq (.app (.app (.val (.prim .store)) (.var 2)) (.var 1)) (.var 7)))))
    (.app (.val (.prim .load)) (.var 1)))))
    (.app (.val (.prim .load)) (.var 1))

/-- `λp. let (f, r) = p in let (i, j) = r in
case idx (f, i) {inj₁ c. case idx (f, j) {inj₁ d. slSwapCellsE | inj₂ _. f} | inj₂ _. f}`.
`[spec §9]` -/
def swapV : Val :=
  .lam (.letpair (.var 0) (.letpair (.var 0)
    (.case (.app (.val (.prim .idx)) (.pair (.var 3) (.var 1)))
      (.case (.app (.val (.prim .idx)) (.pair (.var 4) (.var 1))) slSwapCellsE (.var 5))
      (.var 4))))

/-- `slSwapCellsE` at the family `(ℓ, n)`. -/
def slSwapIn (ℓ : Loc) (n : UInt32) : Expr :=
  .app (.val (.lam (.app (.val (.lam
      (.seq (.app (.app (.val (.prim .store)) (.var 3)) (.var 0))
        (.seq (.app (.app (.val (.prim .store)) (.var 2)) (.var 1)) (.val (Val.arr ℓ n))))))
    (.app (.val (.prim .load)) (.var 1)))))
    (.app (.val (.prim .load)) (.var 1))

/-- `swapV`'s body at the family `(ℓ, n)` and the indices `i`, `j`. -/
def slSwapBody (ℓ : Loc) (n i j : UInt32) : Expr :=
  .case (.app (.val (.prim .idx)) (.val (Val.pair (Val.arr ℓ n) (Val.i32 i))))
    (.case (.app (.val (.prim .idx)) (.val (Val.pair (Val.arr ℓ n) (Val.i32 j))))
      (slSwapIn ℓ n) (.val (Val.arr ℓ n)))
    (.val (Val.arr ℓ n))

/-- `slSwapIn` at the leaves `c` and `d`. -/
def slSwapCells (ℓ : Loc) (n : UInt32) (c d : Loc) : Expr :=
  .app (.val (.lam (.app (.val (.lam
      (.seq (.app (.app (.val (.prim .store)) (.val (.loc c))) (.var 0))
        (.seq (.app (.app (.val (.prim .store)) (.val (.loc d))) (.var 1)) (.val (Val.arr ℓ n))))))
    (eLoad d))))
    (eLoad c)

theorem slSwap_x (ℓ : Loc) (n : UInt32) (c d : Loc) (x : Val) :
    Expr.subst 0 x (.app (.val (.lam
      (.seq (.app (.app (.val (.prim .store)) (.val (.loc c))) (.var 0))
        (.seq (.app (.app (.val (.prim .store)) (.val (.loc d))) (.var 1)) (.val (Val.arr ℓ n))))))
      (eLoad d)) =
    .app (.val (.lam
      (.seq (.app (.app (.val (.prim .store)) (.val (.loc c))) (.var 0))
        (.seq (.app (.app (.val (.prim .store)) (.val (.loc d))) (x.1.shift 1 0))
          (.val (Val.arr ℓ n))))))
      (eLoad d) := by
  simp [Expr.subst, eLoad, subst_arr, Val.shift]

theorem slSwap_y (ℓ : Loc) (n : UInt32) (c d : Loc) (x y : Val) :
    Expr.subst 0 y
      (.seq (.app (.app (.val (.prim .store)) (.val (.loc c))) (.var 0))
        (.seq (.app (.app (.val (.prim .store)) (.val (.loc d))) (x.1.shift 1 0))
          (.val (Val.arr ℓ n)))) =
      .seq (eStore c y) (.seq (eStore d x) (.val (Val.arr ℓ n))) := by
  simp [Expr.subst, eStore, subst_arr, arr_subst_shift_succ, Expr.shift_zero]

theorem sliceSwapM_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ (.val swapV) (sliceSwapMTy a A) := by
  refine sem_const hΓ rfl fun δ ls _ => ⟨rfl, ?_⟩
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨v₁, v₂, hk⟩ := hv
  obtain ⟨rfl, σ₁, σ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hk
  obtain ⟨ℓ, n, rfl, hn, hs⟩ := vP_fam_iff.mp h₁
  obtain ⟨w₁, w₂, hk₂⟩ := h₂
  obtain ⟨rfl, ρ₀, ρ₀', hc₂, ⟨e₀, i, rfl⟩, ⟨e₁, j, rfl⟩⟩ := pure_sep_iff.mp hk₂
  subst e₀ e₁
  rw [eq_of_compS_empty_left hc₂] at hc
  rw [ResU.CompS.functional hc (ResU.comp_empty_right σ₁)] at *
  refine wpTS_lolli ls' _ _ _ _ ?_
  refine wpTS_tensor ls' (Val.arr ℓ n) (Val.pair (Val.i32 i) (Val.i32 j)) _ _ _ ?_
  refine wpTS_tensor ls' (Val.i32 i) (Val.i32 j) _ _ _ ?_
  change wpTS ls' (slSwapBody ℓ n i j) _ σ₁
  have hfam : vP (.sliceMut a A) ls' δ (Val.arr ℓ n) σ₁ := vP_fam_mk hn hs
  refine wpTS_bind (.case .hole _ _) _ ls' _ σ₁ ?_
  refine wpTS_head (fun μ => Head.idx μ ℓ n i) rfl ls' _ σ₁ ?_
  refine wpTS_val ls' (idxAns ℓ n i) _ σ₁ ?_
  simp only [Kont.plug]
  rcases idxAns_cases ℓ n i with ⟨hi, he⟩ | he
  swap
  · rw [he]
    exact wpTS_sum₂ ls' _ _ _ _ σ₁ (wpTS_val ls' (Val.arr ℓ n) _ σ₁ hfam)
  rw [he]
  refine wpTS_sum₁ ls' _ _ _ _ σ₁ ?_
  change wpTS ls' (.case (.app (.val (.prim .idx)) (.val (Val.pair (Val.arr ℓ n) (Val.i32 j))))
    (.app (.val (.lam (.app (.val (.lam
      (.seq (.app (.app (.val (.prim .store)) (.val (.loc (ℓ + i.toNat)))) (.var 0))
        (.seq (.app (.app (.val (.prim .store)) (.var 2)) (.var 1)) (.val (Val.arr ℓ n))))))
      (.app (.val (.prim .load)) (.var 1)))))
      (eLoad (ℓ + i.toNat)))
    (.val (Val.arr ℓ n))) _ σ₁
  refine wpTS_bind (.case .hole _ _) _ ls' _ σ₁ ?_
  refine wpTS_head (fun μ => Head.idx μ ℓ n j) rfl ls' _ σ₁ ?_
  refine wpTS_val ls' (idxAns ℓ n j) _ σ₁ ?_
  simp only [Kont.plug]
  rcases idxAns_cases ℓ n j with ⟨hj, he'⟩ | he'
  swap
  · rw [he']
    exact wpTS_sum₂ ls' _ _ _ _ σ₁ (wpTS_val ls' (Val.arr ℓ n) _ σ₁ hfam)
  rw [he']
  refine wpTS_sum₁ ls' _ _ _ _ σ₁ ?_
  change wpTS ls' (slSwapCells ℓ n (ℓ + i.toNat) (ℓ + j.toNat)) _ σ₁
  by_cases hij : i = j
  · -- one leaf, read twice and written twice
    subst hij
    obtain ⟨ρi, ρr, hci, hPi, hback⟩ := sepRange_pick hi hs
    obtain ⟨α, ha, hmut⟩ := vP_mut_leaf hPi
    refine wpTS_M_antiFrameX _ α A δ _ ls' _ σ₁ ⟨ρi, ρr, hci, hmut, ?_⟩
    intro old c₁ c₂ hc₁ hcc p₁ p₂ hp₁ hcp
    obtain ⟨s, hs', hsp⟩ := compS_exch hcc hcp
    refine wpTS_bind (.appR (.val (.lam _)) .hole) (eLoad _) ls' _ p₂ ?_
    refine wpTS_load ls' _ old _ p₂ ⟨c₁, s, ResU.CompS.comm hsp, hc₁, ?_⟩
    intro c₃ p₃ hc₃ hp₃
    rw [hc₃, ← hc₁] at hp₃
    simp only [Kont.plug]
    refine wpTS_lolli ls' _ old _ p₃ ?_
    rw [slSwap_x]
    refine wpTS_bind (.appR (.val (.lam _)) .hole) (eLoad _) ls' _ p₃ ?_
    refine wpTS_load ls' _ old _ p₃ ⟨c₁, s, ResU.CompS.comm hp₃, hc₁, ?_⟩
    intro c₄ p₄ hc₄ hp₄
    rw [hc₄, ← hc₁] at hp₄
    simp only [Kont.plug]
    refine wpTS_lolli ls' _ old _ p₄ ?_
    rw [slSwap_y]
    refine wpTS_bind (.seq .hole _) (eStore _ old) ls' _ p₄ ?_
    refine wpTS_store ls' _ old old _ p₄ ⟨c₁, s, ResU.CompS.comm hp₄, hc₁, ?_⟩
    intro c₅ p₅ hc₅ hp₅
    simp only [Kont.plug]
    refine wpTS_1 ls' _ _ p₅ ?_
    refine wpTS_bind (.seq .hole _) (eStore _ old) ls' _ p₅ ?_
    refine wpTS_store ls' _ old old _ p₅ ⟨c₅, s, ResU.CompS.comm hp₅, hc₅, ?_⟩
    intro c₆ p₆ hc₆ hp₆
    simp only [Kont.plug]
    refine wpTS_1 ls' _ _ p₆ ?_
    refine wpTS_val ls' (Val.arr ℓ n) _ p₆ ?_
    refine ⟨old, c₆, s, ResU.CompS.comm hp₆, hc₆, p₁, ρr, ResU.CompS.comm hs', hp₁, ?_⟩
    intro m₁ R hm₁ hR
    exact vP_fam_mk hn (hback m₁ R (ResU.CompS.comm hR) (vP_mut_leaf_mk ha hm₁))
  · -- two leaves, each opened by its own Anti-Frame
    have hij' : i.toNat ≠ j.toNat := fun h => hij (UInt32.toNat_inj.mp h)
    obtain ⟨ρi, ρj, ρr, ρ₁, h₁r, hi₁, hPi, hPj, hback⟩ := sepRange_pick2N hij' hi hj hs
    obtain ⟨αi, hai, hmi⟩ := vP_mut_leaf hPi
    obtain ⟨αj, haj, hmj⟩ := vP_mut_leaf hPj
    refine wpTS_M_antiFrameX _ αi A δ _ ls' _ σ₁ ⟨ρi, ρ₁, hi₁, hmi, ?_⟩
    intro xi c₁ c₂ hc₁ hcc p₁ p₂ hp₁ hcp
    obtain ⟨s, hs', hsp⟩ := compS_exch hcc hcp
    obtain ⟨H, hH, hsH⟩ := compS_reassoc h₁r hs'
    obtain ⟨G, hG, hp₂G⟩ := compS_reassoc hsH hsp
    refine wpTS_M_antiFrameX _ αj A δ _ ls' _ p₂ ⟨ρj, G, hp₂G, hmj, ?_⟩
    intro xj e₁ e₂ he₁ hee q₁ q₂ hq₁ hqe
    obtain ⟨t, ht', htq⟩ := compS_exch hee hqe
    -- `q₂ = c₁ ● K`, `K = (H ● q₁) ● e₁`
    obtain ⟨Hq, hHq, ht⟩ := compS_reassoc (ResU.CompS.comm hG) ht'
    obtain ⟨K, hK, hq₂⟩ := compS_reassoc ht htq
    refine wpTS_bind (.appR (.val (.lam _)) .hole) (eLoad _) ls' _ q₂ ?_
    refine wpTS_load ls' _ xi _ q₂ ⟨c₁, K, hq₂, hc₁, ?_⟩
    intro c₃ p₃ hc₃ hp₃
    rw [hc₃, ← hc₁] at hp₃
    simp only [Kont.plug]
    refine wpTS_lolli ls' _ xi _ p₃ ?_
    rw [slSwap_x]
    -- `p₃ = e₁ ● L`, `L = Hq ● c₁`
    obtain ⟨L, hL, hp₃L⟩ := compS_reassoc (ResU.CompS.comm hK) hp₃
    refine wpTS_bind (.appR (.val (.lam _)) .hole) (eLoad _) ls' _ p₃ ?_
    refine wpTS_load ls' _ xj _ p₃ ⟨e₁, L, hp₃L, he₁, ?_⟩
    intro c₄ p₄ hc₄ hp₄
    rw [hc₄, ← he₁] at hp₄
    simp only [Kont.plug]
    refine wpTS_lolli ls' _ xj _ p₄ ?_
    rw [slSwap_y]
    -- `p₄ = c₁ ● M`, `M = Hq ● e₁`
    obtain ⟨M, hM, hp₄M⟩ := compS_reassoc (ResU.CompS.comm hL) hp₄
    refine wpTS_bind (.seq .hole _) (eStore _ xj) ls' _ p₄ ?_
    refine wpTS_store ls' _ xi xj _ p₄ ⟨c₁, M, hp₄M, hc₁, ?_⟩
    intro c₅ p₅ hc₅ hp₅
    simp only [Kont.plug]
    refine wpTS_1 ls' _ _ p₅ ?_
    -- `p₅ = e₁ ● N`, `N = Hq ● c₅`
    obtain ⟨N, hN, hp₅N⟩ := compS_reassoc (ResU.CompS.comm hM) hp₅
    refine wpTS_bind (.seq .hole _) (eStore _ xi) ls' _ p₅ ?_
    refine wpTS_store ls' _ xj xi _ p₅ ⟨e₁, N, hp₅N, he₁, ?_⟩
    intro e₆ p₆ he₆ hp₆
    simp only [Kont.plug]
    refine wpTS_1 ls' _ _ p₆ ?_
    refine wpTS_val ls' (Val.arr ℓ n) _ p₆ ?_
    -- `N = p₁ ● V`, `V = (ρr ● q₁) ● c₅`
    obtain ⟨U, hU, hHqU⟩ := compS_exch hH hHq
    obtain ⟨V, hV, hNV⟩ := compS_exch hHqU hN
    refine ⟨xi, e₆, N, ResU.CompS.comm hp₆, he₆, p₁, V, ResU.CompS.comm hNV, hp₁, ?_⟩
    intro md R hmd hR
    obtain ⟨W, hW, hRW⟩ := compS_reassoc (ResU.CompS.comm hV) hR
    obtain ⟨Fc, hFc, hWF⟩ := compS_reassoc (ResU.CompS.comm hU) hW
    refine ⟨xj, c₅, W, hRW, hc₅, q₁, Fc, hWF, hq₁, ?_⟩
    intro mc R' hmc hR'
    exact vP_fam_mk hn (hback mc md Fc R' (ResU.CompS.comm hFc) (ResU.CompS.comm hR')
      (vP_mut_leaf_mk hai hmc) (vP_mut_leaf_mk haj hmd))

end BoCa.Fig16.LogRel.Core

end

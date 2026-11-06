import Core.Chain.Borrow834N
import Core.Chain.Count834N
import Core.Tok
import Core.SliceOps

/-!
# The opaque token and the families at `SemJN`  `[spec §9, §11, §42]`

`docs/new-core/scope-831-interface.md` §9. Each rule's chain proof is Core's compatibility lemma
(`Core/Tok.lean`, `Core/Arrays.lean`, `Core/Slices.lean`, `Core/SliceOps.lean`), line by line,
against `vN`'s `opq` and family clauses:
* `Tok`: `tokMint_compatN`, `tokBurn_compatN`, the cell by `erwp_alloc`/`erwp_free`;
* a family whose leaves own nothing: `arrLen_compatN`, `arrGet_compatN`, `arrCopy_compatN`,
  `arrRelease_compatN`, `sliceGetM_compatN`, the leaves released by `erwp_garbage`;
* every family: `famSize_compatN` (`arrSize`, `sliceLenM`), `famEmpty_compatN` (`arrEmpty`,
  `sliceEmptyI`, `sliceEmptyM`), `famSplit_compatN` (`sliceSplitI`, `sliceSplitM`).
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
open BoCa.BoLo (Heap Kont Head)

/-! ### The relation at a family -/

theorem vN_fam_iff {L : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val} {ρ : WRes} :
    vN (ℍ := ℍ) (.fam L) δ Θ n v ρ ↔
      ∃ l c, v = Val.arr l c ∧ c.toNat < 2 ^ 31 ∧
        sepRange (fun m => vN (ℍ := ℍ) L δ Θ n (Val.loc m)) l c.toNat ρ := Iff.rfl

theorem vN_fam_mk {L : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {l : Loc} {c : UInt32} {ρ : WRes}
    (hc : c.toNat < 2 ^ 31) (hs : sepRange (fun m => vN (ℍ := ℍ) L δ Θ n (Val.loc m)) l c.toNat ρ) :
    vN (ℍ := ℍ) (.fam L) δ Θ n (Val.arr l c) ρ :=
  ⟨l, c, rfl, hc, hs⟩

/-- The argument of an operation on a family and an index (Core's `vP_fam_idx`). -/
theorem vN_fam_idx {L : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val} {ρ : WRes}
    (h : vN (ℍ := ℍ) (.tensor (.fam L) (.int .w32)) δ Θ n v ρ) :
    ∃ l c i, v = Val.pair (Val.arr l c) (Val.i32 i) ∧ c.toNat < 2 ^ 31 ∧
      sepRange (fun m => vN (ℍ := ℍ) L δ Θ n (Val.loc m)) l c.toNat ρ := by
  obtain ⟨v₁, v₂, ρ₁, ρ₂, rfl, hc, ⟨l, c, rfl, hn, hs⟩, ⟨⟨i, rfl⟩, rfl⟩⟩ := h
  rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)]
  exact ⟨l, c, i, rfl, hn, hs⟩

/-- An `imm` leaf holds no `own` cell (Core's `noOwn_imm`). -/
theorem noOwn_immN {a : Lifetime.Life} {A : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val}
    {ρ : WRes} (h : vN (ℍ := ℍ) (.imm a A) δ Θ n v ρ) : NoOwn ρ := by
  obtain ⟨α, -, ⟨l, s, u, σ, hs, -, rfl, -, -⟩, -⟩ := h
  exact ResU.restrict_single_other (by simp)

/-- A `mut` leaf holds no `own` cell (Core's `noOwn_mut`). -/
theorem noOwn_mutN {a : Lifetime.Life} {A : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val}
    {ρ : WRes} (h : vN (ℍ := ℍ) (.mut a A) δ Θ n v ρ) : NoOwn ρ := by
  obtain ⟨α, -, b, -, ⟨l, w, χ, hχ, j, hw, -, -, -, rfl⟩, -⟩ := h
  exact ResU.restrict_single_other (by simp)

/-- A family of leaves that hold no `own` cell holds none (Core's `noOwn_fam`). -/
theorem noOwn_famN {L : VTy} {δ : LSub} {Θ : LocTy} {n : Nat}
    (hL : ∀ m ρ, vN (ℍ := ℍ) L δ Θ n (Val.loc m) ρ → NoOwn ρ) {v : Val} {ρ : WRes}
    (h : vN (ℍ := ℍ) (.fam L) δ Θ n v ρ) : NoOwn ρ := by
  obtain ⟨l, c, -, -, hs⟩ := h
  exact sepRange_closed noOwn_empty (fun _ _ _ hc h₁ h₂ => noOwn_compS hc h₁ h₂) hL hs

/-! ### The constants at a dead context -/

/-- **A closed value at a dead context** (Core's `sem_const`): its resource is `∅`. -/
theorem sem_constN {Δ : LifeCtx} {Γ : Ctx VTy} {v : Val} {A : VTy} (hΓ : Ctx.DeadP Γ)
    (hcl : closedAt 0 v.1 = true)
    (h : ∀ (δ : LSub) (Θ : LocTy) (n : Nat), Δ.Models δ → Θ.OK →
      vN (ℍ := ℍ) A δ Θ n v PMap.empty) :
    SemJN (ℍ := ℍ) Δ Γ (.val v) (.val A) := by
  intro δ γ Θ c n ls ρ hδ hΘ _ _ hg
  obtain rfl := gN_deadP hΓ hg
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ (.val v)) _
  rw [substAll_closed hcl]
  exact erwp_val (h δ Θ n hδ hΘ)

/-! ### `Tok`: `mint` and `burn` -/

/-- `mint`'s value. -/
def mintV : Val := ⟨mintE, .lam⟩

/-- `burn`'s value. -/
def burnV : Val := ⟨burnE, .lam⟩

/-- **`mint` at `SemJN`** (Core's `tokMint_compatX`, `[TR]` 6.141 at the cell): `1 ⊸ Tok`. -/
theorem tokMint_compatN {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ mintE (.val mintTy) := by
  refine sem_constN (v := mintV) hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨rfl, rfl⟩ := hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  rw [show Kont.hole.plug (Expr.subst 0 Val.unit (.app (.val (.prim .alloc)) (.var 0))) =
    Kont.hole.plug (.app (.val (.prim .alloc)) (.val Val.unit)) by
      simp [Kont.plug, Expr.subst]]
  refine erwp_alloc hΦ (opTableN_local _) .hole Val.unit fun l σ₁ σ₂ hcell hc => ?_
  have hσ : σ₁ = ResU.single l (CellU.ownOf Val.unit) := hcell
  subst hσ
  obtain rfl := eq_of_compS_empty_left hc
  exact erwp_val (v := Val.loc l) (Opaque.rel_tok_intro l)

/-- **`burn` at `SemJN`** (Core's `tokBurn_compatX`, `[TR]` 6.142 at the cell): `Tok ⊸ 1`. -/
theorem tokBurn_compatN {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ burnE (.val burnTy) := by
  refine sem_constN (v := burnV) hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  rcases Opaque.rel_cases hv with ⟨hk, -, -⟩ | ⟨-, l, rfl, rfl⟩
  · exact absurd hk Opaque.tok_not_host
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  rw [show Kont.hole.plug (Expr.subst 0 (Val.loc l) (.app (.val (.prim .free)) (.var 0))) =
    Kont.hole.plug (BoLo.freeE (.val (Val.loc l))) by
      simp [Kont.plug, Expr.subst, BoLo.freeE]]
  refine erwp_free hΦ (opTableN_local _) .hole l Val.unit ?_
  exact ⟨_, _, ResU.comp_empty_right _, rfl, erwp_val (v := Val.unit) ⟨rfl, rfl⟩⟩

/-! ### Families whose leaves own nothing -/

/-- An `imm` leaf is duplicable (Core's `vP_imm_dup`): the cell composes with itself
(`compS_imm_dup`) and its witness is the cell's. -/
theorem vN_imm_dupN {a : Lifetime.Life} {A : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val}
    {ρ : WRes} (h : vN (ℍ := ℍ) (.imm a A) δ Θ n v ρ) :
    ∃ τ₁ τ₂, ResU.CompS τ₁ τ₂ ρ ∧ vN (ℍ := ℍ) (.imm a A) δ Θ n v τ₁ ∧
      vN (ℍ := ℍ) (.imm a A) δ Θ n v τ₂ := by
  obtain ⟨α, -, ⟨l, s, u, σ, hs, -, rfl, -, -⟩, -⟩ := id h
  exact ⟨_, _, compS_imm_dup l s u σ hs, h, h⟩

/-- **`array_len` at `SemJN`** (Core's `arrLen_compatX`). -/
theorem arrLen_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN (ℍ := ℍ) Δ Γ (.val arrLenV) (.val (arrLenTy a A)) := by
  refine sem_constN hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨l, c, rfl, -, -⟩ := id hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_garbage (compS_empty_left σ) (noOwn_famN (fun _ _ h => noOwn_immN h) hv) ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.arr l c)) rfl .hole) ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.letpair μ (Val.loc l) (Val.i32 c) (.var 0)) rfl .hole) ?_
  exact erwp_val (v := Val.i32 c) ⟨⟨c, rfl⟩, rfl⟩

/-- **`array_get` and `slice_get_mut`'s term on a family whose leaves own nothing** (Core's
`famGet_compatX`): the leaf at the index, the rest released. -/
theorem famGet_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {L : VTy} (hΓ : Ctx.DeadP Γ)
    (hL : ∀ δ Θ n m ρ, vN (ℍ := ℍ) L δ Θ n (Val.loc m) ρ → NoOwn ρ) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.prim .idx))
      (.val (.bang (.lolli (.tensor (.fam L) (.int .w32)) (.sum L .unit)))) := by
  refine sem_constN hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨l, c, i, rfl, -, hs⟩ := vN_fam_idx hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.idx μ l c i) rfl .hole) ?_
  have hσ : NoOwn σ := sepRange_closed noOwn_empty
    (fun _ _ _ hc h₁ h₂ => noOwn_compS hc h₁ h₂) (hL δ Θ' k) hs
  rcases idxAns_cases l c i with ⟨hi, he⟩ | he
  · rw [he]
    obtain ⟨ρi, ρr, hc, hPi, -⟩ := sepRange_pick hi hs
    refine erwp_garbage hc (noOwn_right hc hσ) ?_
    exact erwp_val (v := Val.inj₁ (Val.loc (l + i.toNat))) (.inl ⟨_, rfl, hPi⟩)
  · rw [he]
    refine erwp_garbage (compS_empty_left σ) hσ ?_
    exact erwp_val (v := Val.inj₂ Val.unit) (.inr ⟨_, rfl, rfl, rfl⟩)

theorem arrGet_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN (ℍ := ℍ) Δ Γ (.val (.prim .idx)) (.val (arrGetTy a A)) :=
  famGet_compatN hΓ fun _ _ _ _ _ h => noOwn_immN h

theorem sliceGetM_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN (ℍ := ℍ) Δ Γ (.val (.prim .idx)) (.val (sliceGetMTy a A)) :=
  famGet_compatN hΓ fun _ _ _ _ _ h => noOwn_mutN h

/-- **`array_copy` at `SemJN`** (Core's `arrCopy_compatX`): every leaf duplicated. -/
theorem arrCopy_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN (ℍ := ℍ) Δ Γ (.val copyV) (.val (arrCopyTy a A)) := by
  refine sem_constN hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨l, c, rfl, hn, hs⟩ := hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.arr l c)) rfl .hole) ?_
  obtain ⟨τ₁, τ₂, hc, h₁, h₂⟩ := sepRange_dup (fun _ _ h => vN_imm_dupN h) hs
  exact erwp_val (v := Val.pair (Val.arr l c) (Val.arr l c))
    ⟨_, _, τ₁, τ₂, rfl, hc, vN_fam_mk hn h₁, vN_fam_mk hn h₂⟩

/-- **A family whose leaves hold no `own` cell is released by `λp. ()`** (Core's
`release_fam_compatX`). -/
theorem release_fam_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {L : VTy} (hΓ : Ctx.DeadP Γ)
    (hL : ∀ δ Θ n m ρ, vN (ℍ := ℍ) L δ Θ n (Val.loc m) ρ → NoOwn ρ) :
    SemJN (ℍ := ℍ) Δ Γ (.val releaseV) (.val (.bang (.lolli (.fam L) .unit))) := by
  refine sem_constN hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp]
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_garbage (compS_empty_left σ) (noOwn_famN (hL δ Θ' k) hv) ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  exact erwp_val (v := Val.unit) ⟨rfl, rfl⟩

theorem arrRelease_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN (ℍ := ℍ) Δ Γ (.val releaseV) (.val (arrReleaseTy a A)) :=
  release_fam_compatN hΓ fun _ _ _ _ _ h => noOwn_immN h

/-! ### Every family -/

/-- **`array_size`'s term on any family** (Core's `famSize_compatX`, `arrSize_compatX`): the
family handed back beside its length. -/
theorem famSize_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {L : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val sizeV) (.val (.bang (.lolli (.fam L) (.tensor (.fam L) (.int .w32))))) := by
  refine sem_constN hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨l, c, rfl, hn, hs⟩ := hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.arr l c)) rfl .hole) ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.letpair μ (Val.loc l) (Val.i32 c) _) rfl .hole) ?_
  exact erwp_val (v := Val.pair (Val.arr l c) (Val.i32 c))
    ⟨_, _, σ, PMap.empty, rfl, ResU.comp_empty_right σ, vN_fam_mk hn hs, ⟨⟨c, rfl⟩, rfl⟩⟩

theorem arrSize_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val sizeV) (.val (arrSizeTy A)) :=
  famSize_compatN hΓ

theorem sliceLenM_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN (ℍ := ℍ) Δ Γ (.val sizeV) (.val (sliceLenMTy a A)) :=
  famSize_compatN hΓ

/-- **The empty family at any leaf** (Core's `famEmpty_compatX`): no leaves, no resource. -/
theorem famEmpty_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {L : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val emptyFamV) (.val (.fam L)) :=
  sem_constN hΓ rfl fun _ _ _ _ _ => vN_fam_mk (by decide) ⟨rfl, trivial⟩

theorem sliceEmptyI_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN (ℍ := ℍ) Δ Γ (.val emptyFamV) (.val (.arrayImm a A)) :=
  famEmpty_compatN hΓ

theorem sliceEmptyM_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN (ℍ := ℍ) Δ Γ (.val emptyFamV) (.val (.sliceMut a A)) :=
  famEmpty_compatN hΓ

theorem arrEmpty_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN (ℍ := ℍ) Δ Γ (.val emptyFamV) (.val (.array A)) :=
  famEmpty_compatN hΓ

/-- **A family splits at a run-time index `i ≤ n`, at every leaf** (Core's `vP_fam_split`). -/
theorem vN_fam_split {L : VTy} {δ : LSub} {Θ : LocTy} {k : Nat} {l : Loc} {n i : UInt32}
    {ρ : WRes} (hv : vN (ℍ := ℍ) (.fam L) δ Θ k (Val.arr l n) ρ) (hi : i ≤ n) :
    ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ vN (ℍ := ℍ) (.fam L) δ Θ k (Val.arr l i) ρ₁ ∧
      vN (ℍ := ℍ) (.fam L) δ Θ k (Val.arr (l + i.toNat) (n - i)) ρ₂ := by
  obtain ⟨l', n', he, hn, hs⟩ := hv
  obtain ⟨rfl, rfl⟩ := Val.arr_inj he
  have hin : i.toNat ≤ n.toNat := UInt32.le_iff_toNat_le.mp hi
  rw [show n.toNat = i.toNat + (n.toNat - i.toNat) by omega] at hs
  obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := sepRange_split hs
  refine ⟨ρ₁, ρ₂, hc, vN_fam_mk (by omega) h₁, vN_fam_mk (by rw [uint32_sub_toNat hi]; omega) ?_⟩
  rwa [uint32_sub_toNat hi]

/-- **`split` on a family at any leaf** (Core's `famSplit_compatX`). -/
theorem famSplit_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {L : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN (ℍ := ℍ) Δ Γ (.val (.prim .split)) (.val (famSplitTy L)) := by
  refine sem_constN hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨l, c, i, rfl, hn, hs⟩ := vN_fam_idx hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.split μ l c i) rfl .hole) ?_
  have hfam : vN (ℍ := ℍ) (.fam L) δ Θ' k (Val.arr l c) σ := vN_fam_mk hn hs
  rcases splitAns_cases l c i with ⟨hi, he⟩ | he
  · rw [he]
    obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := vN_fam_split hfam hi
    exact erwp_val (v := Val.inj₁ (Val.pair (Val.arr l i) (Val.arr (l + i.toNat) (c - i))))
      (.inl ⟨_, rfl, _, _, ρ₁, ρ₂, rfl, hc, h₁, h₂⟩)
  · rw [he]
    exact erwp_val (v := Val.inj₂ (Val.arr l c)) (.inr ⟨_, rfl, hfam⟩)

theorem sliceSplitI_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN (ℍ := ℍ) Δ Γ (.val (.prim .split)) (.val (sliceSplitITy a A)) :=
  famSplit_compatN hΓ

theorem sliceSplitM_compatN {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN (ℍ := ℍ) Δ Γ (.val (.prim .split)) (.val (sliceSplitMTy a A)) :=
  famSplit_compatN hΓ

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end

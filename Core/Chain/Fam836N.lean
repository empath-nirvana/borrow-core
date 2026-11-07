import Core.Chain.Borrow834N
import Core.Chain.Count834N
import Core.Tok
import Core.SliceOps

/-!
# The opaque token and the families at `SemJN₀`  `[spec §9, §11, §42]`

`docs/new-core/scope-831-interface.md` §11. Each rule's chain proof is Core's compatibility lemma
(`Core/Tok.lean`, `Core/Arrays.lean`, `Core/Slices.lean`, `Core/SliceOps.lean`), line by line,
against `vN₀`'s `opq` and family clauses:
* `Tok`: `tokMint_compatN₀`, `tokBurn_compatN₀`, the cell by `erwp_alloc`/`erwp_free`;
* a family whose leaves own nothing: `arrLen_compatN₀`, `arrGet_compatN₀`, `arrCopy_compatN₀`,
  `arrRelease_compatN₀`, `sliceGetM_compatN₀`, the leaves released by `erwp_garbage`;
* every family: `famSize_compatN₀` (`arrSize`, `sliceLenM`), `famEmpty_compatN₀` (`arrEmpty`,
  `sliceEmptyI`, `sliceEmptyM`), `famSplit_compatN₀` (`sliceSplitI`, `sliceSplitM`).
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
open BoCa.BoLo (Heap Kont Head eLoad eStore)

/-! ### The relation at a family -/

theorem vN_fam_iff₀ {L : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val} {ρ : WRes} :
    vN₀ (ℍ := ℍ) (.fam L) δ Θ n v ρ ↔
      ∃ l c, v = Val.arr l c ∧ c.toNat < 2 ^ 31 ∧
        sepRange (fun m => vN₀ (ℍ := ℍ) L δ Θ n (Val.loc m)) l c.toNat ρ := Iff.rfl

theorem vN_fam_mk₀ {L : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {l : Loc} {c : UInt32} {ρ : WRes}
    (hc : c.toNat < 2 ^ 31) (hs : sepRange (fun m => vN₀ (ℍ := ℍ) L δ Θ n (Val.loc m)) l c.toNat ρ) :
    vN₀ (ℍ := ℍ) (.fam L) δ Θ n (Val.arr l c) ρ :=
  ⟨l, c, rfl, hc, hs⟩

/-- The argument of an operation on a family and an index (Core's `vP_fam_idx`). -/
theorem vN_fam_idx₀ {L : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val} {ρ : WRes}
    (h : vN₀ (ℍ := ℍ) (.tensor (.fam L) (.int .w32)) δ Θ n v ρ) :
    ∃ l c i, v = Val.pair (Val.arr l c) (Val.i32 i) ∧ c.toNat < 2 ^ 31 ∧
      sepRange (fun m => vN₀ (ℍ := ℍ) L δ Θ n (Val.loc m)) l c.toNat ρ := by
  obtain ⟨v₁, v₂, ρ₁, ρ₂, rfl, hc, ⟨l, c, rfl, hn, hs⟩, ⟨⟨i, rfl⟩, rfl⟩⟩ := h
  rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)]
  exact ⟨l, c, i, rfl, hn, hs⟩

/-- An `imm` leaf holds no `own` cell (Core's `noOwn_imm`). -/
theorem noOwn_immN₀ {a : Lifetime.Life} {A : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val}
    {ρ : WRes} (h : vN₀ (ℍ := ℍ) (.imm a A) δ Θ n v ρ) : NoOwn ρ := by
  obtain ⟨α, -, ⟨l, s, u, σ, hs, -, rfl, -, -⟩, -⟩ := h
  exact ResU.restrict_single_other (by simp)

/-- A `mut` leaf holds no `own` cell (Core's `noOwn_mut`). -/
theorem noOwn_mutN₀ {a : Lifetime.Life} {A : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val}
    {ρ : WRes} (h : vN₀ (ℍ := ℍ) (.mut a A) δ Θ n v ρ) : NoOwn ρ := by
  obtain ⟨α, -, b, -, ⟨l, w, χ, hχ, j, hw, -, -, -, rfl⟩, -⟩ := h
  exact ResU.restrict_single_other (by simp)

/-- A family of leaves that hold no `own` cell holds none (Core's `noOwn_fam`). -/
theorem noOwn_famN₀ {L : VTy} {δ : LSub} {Θ : LocTy} {n : Nat}
    (hL : ∀ m ρ, vN₀ (ℍ := ℍ) L δ Θ n (Val.loc m) ρ → NoOwn ρ) {v : Val} {ρ : WRes}
    (h : vN₀ (ℍ := ℍ) (.fam L) δ Θ n v ρ) : NoOwn ρ := by
  obtain ⟨l, c, -, -, hs⟩ := h
  exact sepRange_closed noOwn_empty (fun _ _ _ hc h₁ h₂ => noOwn_compS hc h₁ h₂) hL hs

/-! ### The constants at a dead context -/

/-- **A closed value at a dead context** (Core's `sem_const`): its resource is `∅`. -/
theorem sem_constN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {v : Val} {A : VTy} (hΓ : Ctx.DeadP Γ)
    (hcl : closedAt 0 v.1 = true)
    (h : ∀ (δ : LSub) (Θ : LocTy) (n : Nat), Δ.Models δ → Θ.OK →
      vN₀ (ℍ := ℍ) A δ Θ n v PMap.empty) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val v) (.val A) := by
  intro δ γ Θ c n ls ρ hδ hΘ _ _ hg
  obtain rfl := gN_deadP₀ hΓ hg
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ (.val v)) _
  rw [substAll_closed hcl]
  exact erwp_val (h δ Θ n hδ hΘ)

/-! ### `Tok`: `mint` and `burn` -/

/-- `mint`'s value. -/
def mintV : Val := ⟨mintE, .lam⟩

/-- `burn`'s value. -/
def burnV : Val := ⟨burnE, .lam⟩

/-- **`mint` at `SemJN₀`** (Core's `tokMint_compatX`, `[TR]` 6.141 at the cell): `1 ⊸ Tok`. -/
theorem tokMint_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN₀ (ℍ := ℍ) Δ Γ mintE (.val mintTy) := by
  refine sem_constN₀ (v := mintV) hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  obtain ⟨rfl, rfl⟩ := hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  rw [show Kont.hole.plug (Expr.subst 0 Val.unit (.app (.val (.prim .alloc)) (.var 0))) =
    Kont.hole.plug (.app (.val (.prim .alloc)) (.val Val.unit)) by
      simp [Kont.plug, Expr.subst]]
  refine erwp_alloc hΦ (opTableN_local _) .hole Val.unit fun l σ₁ σ₂ hcell hc => ?_
  have hσ : σ₁ = ResU.single l (CellU.ownOf Val.unit) := hcell
  subst hσ
  obtain rfl := eq_of_compS_empty_left hc
  exact erwp_val (v := Val.loc l) (Opaque.rel_tok_intro l)

/-- **`burn` at `SemJN₀`** (Core's `tokBurn_compatX`, `[TR]` 6.142 at the cell): `Tok ⊸ 1`. -/
theorem tokBurn_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN₀ (ℍ := ℍ) Δ Γ burnE (.val burnTy) := by
  refine sem_constN₀ (v := burnV) hΓ rfl fun δ Θ n _ _ => ?_
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  obtain rfl := eq_of_compS_empty_left hcomp
  rcases Opaque.rel_cases hv with ⟨hk, -, -⟩ | ⟨-, l, rfl, rfl⟩
  · exact absurd hk Opaque.tok_not_host
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl .hole) ?_
  rw [show Kont.hole.plug (Expr.subst 0 (Val.loc l) (.app (.val (.prim .free)) (.var 0))) =
    Kont.hole.plug (BoLo.freeE (.val (Val.loc l))) by
      simp [Kont.plug, Expr.subst, BoLo.freeE]]
  refine erwp_free hΦ (opTableN_local _) .hole l Val.unit ?_
  exact ⟨_, _, ResU.comp_empty_right _, rfl, erwp_val (v := Val.unit) ⟨rfl, rfl⟩⟩

/-! ### Families whose leaves own nothing -/

/-- An `imm` leaf is duplicable (Core's `vP_imm_dup`): the cell composes with itself
(`compS_imm_dup`) and its witness is the cell's. -/
theorem vN_imm_dupN₀ {a : Lifetime.Life} {A : VTy} {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val}
    {ρ : WRes} (h : vN₀ (ℍ := ℍ) (.imm a A) δ Θ n v ρ) :
    ∃ τ₁ τ₂, ResU.CompS τ₁ τ₂ ρ ∧ vN₀ (ℍ := ℍ) (.imm a A) δ Θ n v τ₁ ∧
      vN₀ (ℍ := ℍ) (.imm a A) δ Θ n v τ₂ := by
  obtain ⟨α, -, ⟨l, s, u, σ, hs, -, rfl, -, -⟩, -⟩ := id h
  exact ⟨_, _, compS_imm_dup l s u σ hs, h, h⟩

/-- **`array_len` at `SemJN₀`** (Core's `arrLen_compatX`). -/
theorem arrLen_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN₀ (ℍ := ℍ) Δ Γ (.val arrLenV) (.val (arrLenTy a A)) := by
  refine sem_constN₀ hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨l, c, rfl, -, -⟩ := id hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_garbage (compS_empty_left σ) (noOwn_famN₀ (fun _ _ h => noOwn_immN₀ h) hv) ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.arr l c)) rfl .hole) ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.letpair μ (Val.loc l) (Val.i32 c) (.var 0)) rfl .hole) ?_
  exact erwp_val (v := Val.i32 c) ⟨⟨c, rfl⟩, rfl⟩

/-- **`array_get` and `slice_get_mut`'s term on a family whose leaves own nothing** (Core's
`famGet_compatX`): the leaf at the index, the rest released. -/
theorem famGet_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {L : VTy} (hΓ : Ctx.DeadP Γ)
    (hL : ∀ δ Θ n m ρ, vN₀ (ℍ := ℍ) L δ Θ n (Val.loc m) ρ → NoOwn ρ) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val (.prim .idx))
      (.val (.bang (.lolli (.tensor (.fam L) (.int .w32)) (.sum L .unit)))) := by
  refine sem_constN₀ hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨l, c, i, rfl, -, hs⟩ := vN_fam_idx₀ hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h)
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

theorem arrGet_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN₀ (ℍ := ℍ) Δ Γ (.val (.prim .idx)) (.val (arrGetTy a A)) :=
  famGet_compatN₀ hΓ fun _ _ _ _ _ h => noOwn_immN₀ h

theorem sliceGetM_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN₀ (ℍ := ℍ) Δ Γ (.val (.prim .idx)) (.val (sliceGetMTy a A)) :=
  famGet_compatN₀ hΓ fun _ _ _ _ _ h => noOwn_mutN₀ h

/-- **`array_copy` at `SemJN₀`** (Core's `arrCopy_compatX`): every leaf duplicated. -/
theorem arrCopy_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN₀ (ℍ := ℍ) Δ Γ (.val copyV) (.val (arrCopyTy a A)) := by
  refine sem_constN₀ hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨l, c, rfl, hn, hs⟩ := hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.arr l c)) rfl .hole) ?_
  obtain ⟨τ₁, τ₂, hc, h₁, h₂⟩ := sepRange_dup (fun _ _ h => vN_imm_dupN₀ h) hs
  exact erwp_val (v := Val.pair (Val.arr l c) (Val.arr l c))
    ⟨_, _, τ₁, τ₂, rfl, hc, vN_fam_mk₀ hn h₁, vN_fam_mk₀ hn h₂⟩

/-- **A family whose leaves hold no `own` cell is released by `λp. ()`** (Core's
`release_fam_compatX`). -/
theorem release_fam_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {L : VTy} (hΓ : Ctx.DeadP Γ)
    (hL : ∀ δ Θ n m ρ, vN₀ (ℍ := ℍ) L δ Θ n (Val.loc m) ρ → NoOwn ρ) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val releaseV) (.val (.bang (.lolli (.fam L) .unit))) := by
  refine sem_constN₀ hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp]
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_garbage (compS_empty_left σ) (noOwn_famN₀ (hL δ Θ' k) hv) ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  exact erwp_val (v := Val.unit) ⟨rfl, rfl⟩

theorem arrRelease_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN₀ (ℍ := ℍ) Δ Γ (.val releaseV) (.val (arrReleaseTy a A)) :=
  release_fam_compatN₀ hΓ fun _ _ _ _ _ h => noOwn_immN₀ h

/-! ### Every family -/

/-- **`array_size`'s term on any family** (Core's `famSize_compatX`, `arrSize_compatX`): the
family handed back beside its length. -/
theorem famSize_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {L : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val sizeV) (.val (.bang (.lolli (.fam L) (.tensor (.fam L) (.int .w32))))) := by
  refine sem_constN₀ hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨l, c, rfl, hn, hs⟩ := hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.arr l c)) rfl .hole) ?_
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.letpair μ (Val.loc l) (Val.i32 c) _) rfl .hole) ?_
  exact erwp_val (v := Val.pair (Val.arr l c) (Val.i32 c))
    ⟨_, _, σ, PMap.empty, rfl, ResU.comp_empty_right σ, vN_fam_mk₀ hn hs, ⟨⟨c, rfl⟩, rfl⟩⟩

theorem arrSize_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val sizeV) (.val (arrSizeTy A)) :=
  famSize_compatN₀ hΓ

theorem sliceLenM_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN₀ (ℍ := ℍ) Δ Γ (.val sizeV) (.val (sliceLenMTy a A)) :=
  famSize_compatN₀ hΓ

/-- **The empty family at any leaf** (Core's `famEmpty_compatX`): no leaves, no resource. -/
theorem famEmpty_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {L : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val emptyFamV) (.val (.fam L)) :=
  sem_constN₀ hΓ rfl fun _ _ _ _ _ => vN_fam_mk₀ (by decide) ⟨rfl, trivial⟩

theorem sliceEmptyI_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN₀ (ℍ := ℍ) Δ Γ (.val emptyFamV) (.val (.arrayImm a A)) :=
  famEmpty_compatN₀ hΓ

theorem sliceEmptyM_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN₀ (ℍ := ℍ) Δ Γ (.val emptyFamV) (.val (.sliceMut a A)) :=
  famEmpty_compatN₀ hΓ

theorem arrEmpty_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN₀ (ℍ := ℍ) Δ Γ (.val emptyFamV) (.val (.array A)) :=
  famEmpty_compatN₀ hΓ

/-- **A family splits at a run-time index `i ≤ n`, at every leaf** (Core's `vP_fam_split`). -/
theorem vN_fam_split₀ {L : VTy} {δ : LSub} {Θ : LocTy} {k : Nat} {l : Loc} {n i : UInt32}
    {ρ : WRes} (hv : vN₀ (ℍ := ℍ) (.fam L) δ Θ k (Val.arr l n) ρ) (hi : i ≤ n) :
    ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ vN₀ (ℍ := ℍ) (.fam L) δ Θ k (Val.arr l i) ρ₁ ∧
      vN₀ (ℍ := ℍ) (.fam L) δ Θ k (Val.arr (l + i.toNat) (n - i)) ρ₂ := by
  obtain ⟨l', n', he, hn, hs⟩ := hv
  obtain ⟨rfl, rfl⟩ := Val.arr_inj he
  have hin : i.toNat ≤ n.toNat := UInt32.le_iff_toNat_le.mp hi
  rw [show n.toNat = i.toNat + (n.toNat - i.toNat) by omega] at hs
  obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := sepRange_split hs
  refine ⟨ρ₁, ρ₂, hc, vN_fam_mk₀ (by omega) h₁, vN_fam_mk₀ (by rw [uint32_sub_toNat hi]; omega) ?_⟩
  rwa [uint32_sub_toNat hi]

/-- **`split` on a family at any leaf** (Core's `famSplit_compatX`). -/
theorem famSplit_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {L : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val (.prim .split)) (.val (famSplitTy L)) := by
  refine sem_constN₀ hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨l, c, i, rfl, hn, hs⟩ := vN_fam_idx₀ hv
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.split μ l c i) rfl .hole) ?_
  have hfam : vN₀ (ℍ := ℍ) (.fam L) δ Θ' k (Val.arr l c) σ := vN_fam_mk₀ hn hs
  rcases splitAns_cases l c i with ⟨hi, he⟩ | he
  · rw [he]
    obtain ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ := vN_fam_split₀ hfam hi
    exact erwp_val (v := Val.inj₁ (Val.pair (Val.arr l i) (Val.arr (l + i.toNat) (c - i))))
      (.inl ⟨_, rfl, _, _, ρ₁, ρ₂, rfl, hc, h₁, h₂⟩)
  · rw [he]
    exact erwp_val (v := Val.inj₂ (Val.arr l c)) (.inr ⟨_, rfl, hfam⟩)

theorem sliceSplitI_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN₀ (ℍ := ℍ) Δ Γ (.val (.prim .split)) (.val (sliceSplitITy a A)) :=
  famSplit_compatN₀ hΓ

theorem sliceSplitM_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemJN₀ (ℍ := ℍ) Δ Γ (.val (.prim .split)) (.val (sliceSplitMTy a A)) :=
  famSplit_compatN₀ hΓ

/-! ### `array_free` -/

/-- **The drain** (Core's `dropFill_wp`): the cells `ℓ + i, …, ℓ + i + k − 1` are freed in order,
each value handed to the consumer, at every index below the consumer's; by induction on `k`. -/
theorem dropFill_wpN₀ {A : VTy} {δ : LSub} {Θ : LocTy} (hΘ : Θ.OK) {N : Nat} (f : Val) (l : Loc)
    (hf : vN₀ (ℍ := ℍ) (.bang (.lolli A .unit)) δ Θ N f PMap.empty) :
    ∀ (k i m : Nat) (ls : List SRec) (ρ : WRes) (c : Loc → Option Life), m ≤ N →
      ConsistentX c ρ → sepRange (fun x => vN₀ (ℍ := ℍ) (.ref A) δ Θ m (Val.loc x)) (l + i) k ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) (fun k _ v ρ => vN₀ (ℍ := ℍ) .unit δ Θ k v ρ)
        m ls (dropFill f l i k) ρ
  | 0, i, m, ls, ρ, c, _, _, hs => by
      obtain ⟨rfl, -⟩ := hs
      exact erwp_val (v := Val.unit) ⟨rfl, rfl⟩
  | k + 1, i, m, ls, ρ, c, hm, hc, ⟨ρl, ρr, hcl, hleaf, hrest⟩ => by
      have hΦ := LocTy.view_down hΘ.1 c
      refine erwp_of_valid fun hv => ?_
      obtain ⟨l', w, ρw, hl', hcw, hw⟩ := hleaf
      obtain rfl : l + i = l' := loc_inj hl'
      -- `ρ = cell ● (ρw ● ρr)`
      obtain ⟨R, hR, hρ⟩ := compS_reassoc hcw hcl
      show erwp (ℍ := ℍ) _ _ _ m ls ((Kont.seq (.appR (.val f) .hole) (dropFill f l (i + 1) k)).plug
        (BoLo.freeE (.val (Val.loc (l + i))))) ρ
      refine erwp_free hΦ (opTableN_local _) _ (l + i) w ⟨_, R, hρ, rfl, ?_⟩
      have hvR : ResU.Valid R := (ResU.Valid.split hρ hv).2
      have hcR : ConsistentX c R := consistentX_right hρ hc hv
      have hcw' : ConsistentX c ρw := consistentX_left hR hcR hvR
      show erwp (ℍ := ℍ) _ _ _ (m - 1) ls ((Kont.seq .hole (dropFill f l (i + 1) k)).plug
        (.app (.val f) (.val w))) R
      refine erwp_bind_frame hΦ (opTableN_local _) _
        (sepRange (fun x => vN₀ (ℍ := ℍ) (.ref A) δ Θ (m - 1) (Val.loc x)) (l + i + 1) k) hR hcR
        (bang_app₀ hΘ ((Nat.sub_le m 1).trans hm) hf hcw' (vN_le₀ (Nat.sub_le m 1) hw) ls)
        (sepRange_mono' (fun x τ h => vN_le₀ (Nat.sub_le m 1) h) hrest) ?_
      intro k' hk' ls' u σ₁ σ₂ σ hcσ hu hr hcσ' _
      obtain ⟨rfl, rfl⟩ := hu
      rw [eq_of_compS_empty_left hcσ] at hcσ' ⊢
      refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ k v ρ h)
        (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
      refine dropFill_wpN₀ hΘ f l hf k (i + 1) k' ls' σ₂ c (hk'.trans ((Nat.sub_le m 1).trans hm)) hcσ' ?_
      rw [← Nat.add_assoc]
      exact sepRange_mono' (fun x τ h => vN_le₀ hk' h) hr

/-- **`array_free` at `SemJN₀`** (Core's `arrFree_compatX`). -/
theorem arrFree_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val (.prim .drop)) (.val (arrFreeTy A)) := by
  refine sem_constN₀ hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp] at hcon ⊢
  obtain ⟨f, v₂, σ₁, σ₂, rfl, hc, hf, l, cn, rfl, hn, hs⟩ := hv
  obtain rfl : σ₁ = PMap.empty := hf.1
  rw [eq_of_compS_empty_left hc] at hcon ⊢
  have hΦ := LocTy.view_down hΘ'.1 c''
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.drop μ f l cn) rfl .hole) ?_
  exact dropFill_wpN₀ hΘ' f l hf cn.toNat 0 k ls' σ₂ c'' le_rfl hcon (by simpa using hs)

/-! ### `array_replace` -/

theorem eStore_storeV (c : Loc) (x : Val) :
    eStore c x = .app (.val (Val.storeV (Val.loc c))) (.val x) := rfl

/-- **`array_replace` at `SemJN₀`** (Core's `arrReplace_compatX`): in range, the leaf's cell is
read (`rwp_load`) and written (`rwp_store`), and the leaf goes back into the family with the new
payload beside the old one; out of range, the element is handed back. -/
theorem arrReplace_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    SemJN₀ (ℍ := ℍ) Δ Γ (.val replaceV) (.val (arrReplaceTy A)) := by
  refine sem_constN₀ hΓ rfl fun δ Θ n _ _ => ⟨rfl, ?_⟩
  intro Θ' _ hΘ' _ _ ls' c'' k _ v σ τ hcomp hv hcon
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨v₁, v₂, σ₁, σ₂, rfl, hc, ⟨ℓ, cn, rfl, hn, hs⟩, w₁, x, ρ₀, σx, rfl, hc₂,
    ⟨⟨i, rfl⟩, rfl⟩, hx⟩ := hv
  rw [eq_of_compS_empty_left hc₂] at hc
  have hΦ := LocTy.view_down hΘ'.1 c''
  have hQd : PostN.Down (fun k _ v ρ => vN₀ (ℍ := ℍ) (.tensor (.array A) (.sum A A)) δ Θ' k v ρ) :=
    fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h
  have hTd := opTableN_down OpTabN.empty_down
  refine erwp_det hΦ hTd hQd (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  simp only [Kont.plug]
  rw [replace_body₁]
  refine erwp_det hΦ hTd hQd
    (fun μ => step1Only_plug (Head.letpair μ (Val.arr ℓ cn) (Val.pair (Val.i32 i) x) _) rfl .hole) ?_
  simp only [Kont.plug]
  rw [replace_body₂]
  refine erwp_det hΦ hTd hQd
    (fun μ => step1Only_plug (Head.letpair μ (Val.i32 i) x _) rfl .hole) ?_
  simp only [Kont.plug]
  rw [replace_body₃]
  refine erwp_det hΦ hTd hQd
    (fun μ => step1Only_plug (Head.idx μ ℓ cn i) rfl (.case .hole _ _)) ?_
  simp only [Kont.plug]
  rcases idxAns_cases ℓ cn i with ⟨hi, he⟩ | he
  · rw [he]
    refine erwp_det hΦ hTd hQd
      (fun μ => step1Only_plug (Head.case₁ μ (Val.loc (ℓ + i.toNat)) _ _) rfl .hole) ?_
    simp only [Kont.plug]
    rw [replace_in]
    obtain ⟨ρi, ρr, hci, hPi, hback⟩ := sepRange_pick hi hs
    obtain ⟨ℓ', old, ρold, hl, hcw, hold⟩ := hPi
    obtain rfl : ℓ + i.toNat = ℓ' := loc_inj hl
    -- `σ = cell ● G`, `G = ρold ● F`, `F = ρr ● σx`
    obtain ⟨F, hF, hiF⟩ := compS_reassoc hci hc
    obtain ⟨G, hG, hσ⟩ := compS_reassoc hcw hiF
    refine erwp_bindR hΦ (opTableN_local _)
      (.pairR (Val.arr ℓ cn) (.inj₁ (.appR (.val (.lam _)) .hole))) ?_
    refine rwp_load ls' _ old _ ⟨_, G, hσ, rfl, fun c₁ p₁ hc₁ hp₁ => ?_⟩
    obtain rfl := hc₁
    simp only [Kont.plug]
    refine erwp_det hΦ hTd hQd
      (fun μ => step1Only_plug (Head.beta μ _ old) rfl (.pairR (Val.arr ℓ cn) (.inj₁ .hole))) ?_
    simp only [Kont.plug]
    rw [replace_store, eStore_storeV]
    refine erwp_bindR hΦ (opTableN_local _)
      (.pairR (Val.arr ℓ cn) (.inj₁ (.seq .hole (.val old)))) ?_
    refine rwp_store ls' _ old x _ ⟨_, G, ResU.CompS.comm hp₁, rfl, fun c₃ p₃ hc₃ hp₃ => ?_⟩
    obtain rfl := hc₃
    simp only [Kont.plug]
    refine erwp_det hΦ hTd hQd
      (fun μ => step1Only_plug (Head.seq μ _) rfl (.pairR (Val.arr ℓ cn) (.inj₁ .hole))) ?_
    simp only [Kont.plug]
    -- `p₃ = X ● ρold`, `X = ρr ● L`, `L` the new leaf `c₃ ● σx`
    obtain ⟨X, hX, hp₃'⟩ := compS_exch (ResU.CompS.comm hG) hp₃
    obtain ⟨L, hL, hXL⟩ := compS_reassoc hF hX
    have hfam : vN₀ (ℍ := ℍ) (.array A) δ Θ' k (Val.arr ℓ cn) X :=
      vN_fam_mk₀ hn (hback L X (ResU.CompS.comm hXL)
        ⟨ℓ + i.toNat, x, σx, rfl, ResU.CompS.comm hL, hx⟩)
    exact erwp_val (v := Val.pair (Val.arr ℓ cn) (Val.inj₁ old))
      (vN_le₀ (by omega) ⟨_, _, X, ρold, rfl, hp₃', hfam, .inl ⟨old, rfl, hold⟩⟩)
  · rw [he]
    refine erwp_det hΦ hTd hQd
      (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
    simp only [Kont.plug]
    rw [replace_out]
    exact erwp_val (v := Val.pair (Val.arr ℓ cn) (Val.inj₂ x))
      ⟨_, _, σ₁, σx, rfl, hc, vN_fam_mk₀ hn hs, .inr ⟨x, rfl, hx⟩⟩

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end

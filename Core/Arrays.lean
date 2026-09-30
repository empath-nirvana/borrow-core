import Core.Integers
import Core.Fix
import Core.ArrayWp
import Support.Dynamics.Completeness

/-!
# Core — Arrays  `[spec §9]`

`[L]` (`VTy.fam L`) is the run-time family `⊛_{i<n} L` of leaf places: a value `(ℓ, n)` whose
`i`-th leaf is the location `ℓ + i`. `Array A = [Ref A]` owns its `n` cells; `ArrayImm @a A` is
the family of leaf views that `withload` gives at `Imm @a (Array A)` (`Imm̲ 'x [Ref A] =
[Imm 'x A]`).

This file gives the constants of `SPEC.md` §9, each a closed value typed at a dead context, and
proves each sound at every host:

| constant | type | term |
|---|---|---|
| `array_new` | `!(I32 ⊗ !(I32 ⇒ A) ⇒ Array A)` | `tab` |
| `array_free` | `!(!(A ⇒ 1) ⊗ Array A ⇒ 1)` | `drop` |
| `array_size` | `!(Array A ⇒ Array A ⊗ I32)` | `λp. let (b, n) = p in ((b, n), n)` |
| `array_replace` | `!(Array A ⊗ (I32 ⊗ A) ⇒ Array A ⊗ (A ⊕ A))` | `replaceV` |
| `array_len` | `!(ArrayImm @a A ⇒ I32)` | `λp. let (b, n) = p in n` |
| `array_get` | `!(ArrayImm @a A ⊗ I32 ⇒ Imm @a A ⊕ 1)` | `idx` |
| `array_copy` | `!(ArrayImm @a A ⇒ ArrayImm @a A ⊗ ArrayImm @a A)` | `λp. (p, p)` |
| `array_forget` | `!(ArrayImm @a A ⇒ 1)` | `λp. ()` |

**Why a leaf view is sound.** A family of leaf views holds each leaf's `imm` cell at the top level
of its resource (`sepRange`); no cell of it owns another. `array_get` hands out one leaf's cell, by
`idx` (a pure step), and forgets the others, which hold no `own` cell (`noOwn_fam`). No run
returns a view below a parent cell, so the update relation is never asked to accept one: that is
the view `experiments/FrameEnd` excludes (`imm_view_rejected`), which a leaf view taken at `@a`
from `Imm @a (Array A)` would be.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The types -/

/-- `Array A = [Ref A]`.  `[spec §9]` -/
abbrev VTy.array (A : VTy) : VTy := .fam (.ref A)

/-- `ArrayImm @a A = [Imm @a A]`.  `[spec §9]` -/
abbrev VTy.arrayImm (a : Lifetime.Life) (A : VTy) : VTy := .fam (.imm a A)

/-! ### The relation at a family -/

theorem vP_fam_iff {L : VTy} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes} :
    vP (.fam L) ls δ v ρ ↔
      ∃ ℓ n, v = Val.arr ℓ n ∧ n.toNat < 2 ^ 31 ∧
        sepRange (fun m => vP L ls δ (.loc m)) ℓ n.toNat ρ := by
  constructor
  · rintro ⟨ℓ, n, hs⟩
    obtain ⟨⟨he, hn⟩, hs⟩ := pure_sep_iff.mp hs
    exact ⟨ℓ, n, he, hn, hs⟩
  · rintro ⟨ℓ, n, he, hn, hs⟩
    exact ⟨ℓ, n, pure_sep_mk ⟨he, hn⟩ hs⟩

theorem vP_fam_mk {L : VTy} {ls : List SRec} {δ : LSub} {ℓ : Loc} {n : UInt32} {ρ : WRes}
    (hn : n.toNat < 2 ^ 31) (hs : sepRange (fun m => vP L ls δ (.loc m)) ℓ n.toNat ρ) :
    vP (.fam L) ls δ (Val.arr ℓ n) ρ :=
  vP_fam_iff.mpr ⟨ℓ, n, rfl, hn, hs⟩

/-- A family in the relation has `tab`'s length: `arrLen n = n`.  `[spec §9]` -/
theorem arrLen_of_bound {n : UInt32} (hn : n.toNat < 2 ^ 31) : arrLen n = n := arrLen_eq_of_lt hn

/-- `tab`'s length is below `2³¹`. -/
theorem arrLen_bound (c : UInt32) : (arrLen c).toNat < 2 ^ 31 := by
  unfold arrLen
  split
  · rename_i h; have := UInt32.lt_iff_toNat_lt.mp h; simpa using this
  · simp

/-- A leaf borrow holds no `own` cell. -/
theorem noOwn_imm {a : Lifetime.Life} {A : VTy} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : vP (.imm a A) ls δ v ρ) : NoOwn ρ := by
  obtain ⟨α, -, ℓ, hs⟩ := h
  obtain ⟨-, s, u, σ, hσ, ls₀, rfl, -⟩ := pure_sep_iff.mp hs
  exact ResU.restrict_single_other (by simp)

/-- A family of leaves that hold no `own` cell holds none. -/
theorem noOwn_fam {L : VTy} {ls : List SRec} {δ : LSub}
    (hL : ∀ m ρ, vP L ls δ (.loc m) ρ → NoOwn ρ) {v : Val} {ρ : WRes}
    (h : vP (.fam L) ls δ v ρ) : NoOwn ρ := by
  obtain ⟨ℓ, n, -, -, hs⟩ := vP_fam_iff.mp h
  exact sepRange_closed noOwn_empty (fun _ _ _ hc h₁ h₂ => noOwn_compS hc h₁ h₂) hL hs

theorem noOwn_arrayImm {a : Lifetime.Life} {A : VTy} {ls : List SRec} {δ : LSub} {v : Val}
    {ρ : WRes} (h : vP (.arrayImm a A) ls δ v ρ) : NoOwn ρ :=
  noOwn_fam (fun _ _ h => noOwn_imm h) h

/-- A part of a resource with no `own` cell has none. -/
theorem noOwn_right {a b c : WRes} (hc : ResU.CompS a b c) (h : NoOwn c) : NoOwn b :=
  noOwn_iff.mpr fun l ψ hl => by
    obtain ⟨ψ', e', k', -, -⟩ := compS_get_right' hc hl
    rw [← k']; exact noOwn_iff.mp h l ψ' e'

/-- A resource with no `own` cell may be dropped in front of a run. -/
theorem wpTS_drop {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp} {σ τ ρ : WRes}
    (hσ : NoOwn σ) (hc : ResU.CompS σ τ ρ) (h : wpTS ls e Q τ) : wpTS ls e Q ρ :=
  wpTS_frame_noOwn (R := fun ρ' => ρ' = σ) (fun _ e => e ▸ hσ) ls e Q ρ ⟨σ, τ, hc, rfl, h⟩

/-- The constant at a dead context: its resource is `∅`. -/
theorem sem_const {Δ : LifeCtx} {Γ : Ctx VTy} {v : Val} {A : VTy} (hΓ : Ctx.DeadP Γ)
    (hcl : closedAt 0 v.1 = true)
    (h : ∀ (δ : LSub) (ls : List SRec), Δ.Models δ → vP A ls δ v PMap.empty) :
    SemV Δ Γ (.val v) A := by
  intro δ γ ls ρ hδ hg
  have hρ : ρ = PMap.empty := gSepC_deadP hΓ (gDenC_iff.mp hg).2
  subst hρ
  show wpTS ls (substAll γ (.val v)) _ _
  rw [substAll_closed hcl]
  exact wpTS_val ls v _ _ (h δ ls hδ)

/-! ### `array_len` -/

/-- `λp. let (b, n) = p in n`.  `[spec §9]` -/
def arrLenV : Val := .lam (.letpair (.var 0) (.var 0))

/-- `array_len : !(ArrayImm @a A ⇒ I32)`.  `[spec §9]` -/
abbrev arrLenTy (a : Lifetime.Life) (A : VTy) : VTy := .bang (.lolli (.arrayImm a A) (.int .w32))

theorem arrLen_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ (.val arrLenV) (arrLenTy a A) := by
  refine sem_const hΓ rfl fun δ ls _ => ⟨rfl, ?_⟩
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨ℓ, n, rfl, -, -⟩ := vP_fam_iff.mp hv
  refine wpTS_drop (noOwn_arrayImm hv) (ResU.comp_empty_right σ) ?_
  refine wpTS_lolli ls' _ _ _ _ ?_
  show wpTS ls' (.letpair (.val (Val.arr ℓ n)) (.var 0)) _ _
  refine wpTS_tensor ls' (Val.loc ℓ) (Val.i32 n) (.var 0) _ _ ?_
  exact wpTS_val ls' (Val.i32 n) _ _ (vP_i32 n)

/-! ### `array_get` -/

/-- `array_get : !(ArrayImm @a A ⊗ I32 ⇒ Imm @a A ⊕ 1)`.  `[spec §9]` -/
abbrev arrGetTy (a : Lifetime.Life) (A : VTy) : VTy :=
  .bang (.lolli (.tensor (.arrayImm a A) (.int .w32)) (.sum (.imm a A) .unit))

/-- The argument of an operation on a family and an index. -/
theorem vP_fam_idx {L : VTy} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : vP (.tensor (.fam L) (.int .w32)) ls δ v ρ) :
    ∃ ℓ n i, v = Val.pair (Val.arr ℓ n) (Val.i32 i) ∧ n.toNat < 2 ^ 31 ∧
      sepRange (fun m => vP L ls δ (.loc m)) ℓ n.toNat ρ := by
  obtain ⟨v₁, v₂, hk⟩ := h
  obtain ⟨rfl, ρ₁, ρ₂, hc, h₁, ⟨e₂, i, rfl⟩⟩ := pure_sep_iff.mp hk
  subst e₂
  obtain ⟨ℓ, n, rfl, hn, hs⟩ := vP_fam_iff.mp h₁
  rw [ResU.CompS.functional hc (ResU.comp_empty_right ρ₁)]
  exact ⟨ℓ, n, i, rfl, hn, hs⟩

/-- The leaf `idx` answers: in range, the leaf at `ℓ + i` beside the rest of the family;
otherwise nothing. -/
theorem idxAns_cases (ℓ : Loc) (n i : UInt32) :
    (i.toNat < n.toNat ∧ idxAns ℓ n i = .inj₁ (.loc (ℓ + i.toNat))) ∨ idxAns ℓ n i = .inj₂ .unit := by
  unfold idxAns
  by_cases h : i < n
  · exact Or.inl ⟨UInt32.lt_iff_toNat_lt.mp h, if_pos h⟩
  · exact Or.inr (if_neg h)

theorem arrGet_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ (.val (.prim .idx)) (arrGetTy a A) := by
  refine sem_const hΓ rfl fun δ ls _ => ⟨rfl, ?_⟩
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨ℓ, n, i, rfl, -, hs⟩ := vP_fam_idx hv
  refine wpTS_head (fun μ => Head.idx μ ℓ n i) rfl ls' _ σ ?_
  rcases idxAns_cases ℓ n i with ⟨hi, he⟩ | he
  · rw [he]
    obtain ⟨ρi, ρr, hc, hPi, -⟩ := sepRange_pick hi hs
    have hσ : NoOwn σ := sepRange_closed noOwn_empty
      (fun _ _ _ hc h₁ h₂ => noOwn_compS hc h₁ h₂) (fun _ _ h => noOwn_imm h) hs
    refine wpTS_drop (noOwn_right hc hσ) (ResU.CompS.comm hc) ?_
    exact wpTS_val ls' _ _ _ (Or.inl ⟨_, pure_sep_mk rfl hPi⟩)
  · rw [he]
    have hσ : NoOwn σ := sepRange_closed noOwn_empty
      (fun _ _ _ hc h₁ h₂ => noOwn_compS hc h₁ h₂) (fun _ _ h => noOwn_imm h) hs
    refine wpTS_drop hσ (ResU.comp_empty_right σ) ?_
    exact wpTS_val ls' _ _ _ (Or.inr ⟨.unit, pure_sep_mk rfl ⟨rfl, rfl⟩⟩)

/-! ### `array_copy` and the forgets -/

/-- A duplicable leaf predicate gives a duplicable range. -/
theorem sepRange_dup {P : Loc → WProp}
    (hP : ∀ m ρ, P m ρ → ∃ τ₁ τ₂, ResU.CompS τ₁ τ₂ ρ ∧ P m τ₁ ∧ P m τ₂) :
    ∀ {ℓ : Loc} {n : Nat} {ρ : WRes}, sepRange P ℓ n ρ →
      ∃ τ₁ τ₂, ResU.CompS τ₁ τ₂ ρ ∧ sepRange P ℓ n τ₁ ∧ sepRange P ℓ n τ₂
  | _, 0, ρ, h => by
      obtain ⟨rfl, -⟩ := h
      exact ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, trivial⟩, ⟨rfl, trivial⟩⟩
  | _, _ + 1, _, ⟨ρ₁, ρ₂, hc, h₁, h₂⟩ => by
      obtain ⟨τ₁, τ₂, hτ, g₁, g₂⟩ := hP _ _ h₁
      obtain ⟨σ₁, σ₂, hσ, k₁, k₂⟩ := sepRange_dup hP h₂
      obtain ⟨bc, hbc, hρ⟩ := compS_reassoc hτ hc
      obtain ⟨ac, hac, hbc'⟩ := compS_lcomm hσ hbc
      obtain ⟨X, hX, hρ'⟩ := compS_reassoc' hbc' hρ
      exact ⟨X, ac, hρ', ⟨τ₁, σ₁, hX, g₁, k₁⟩, ⟨τ₂, σ₂, hac, g₂, k₂⟩⟩

theorem vP_imm_dup {a : Lifetime.Life} {A : VTy} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes}
    (h : vP (.imm a A) ls δ v ρ) :
    ∃ τ₁ τ₂, ResU.CompS τ₁ τ₂ ρ ∧ vP (.imm a A) ls δ v τ₁ ∧ vP (.imm a A) ls δ v τ₂ := by
  obtain ⟨α, ha, ℓ, hs⟩ := h
  obtain ⟨hvl, himm⟩ := pure_sep_iff.mp hs
  obtain ⟨τ₁, τ₂, hc, h₁, h₂⟩ := ptoImmS_dup himm
  exact ⟨τ₁, τ₂, hc, ⟨α, ha, ℓ, pure_sep_mk hvl h₁⟩, ⟨α, ha, ℓ, pure_sep_mk hvl h₂⟩⟩

/-- `array_copy : !(ArrayImm @a A ⇒ ArrayImm @a A ⊗ ArrayImm @a A)`.  `[spec §9]` -/
abbrev arrCopyTy (a : Lifetime.Life) (A : VTy) : VTy :=
  .bang (.lolli (.arrayImm a A) (.tensor (.arrayImm a A) (.arrayImm a A)))

/-- `λp. (p, p)`. -/
def copyV : Val := .lam (.pair (.var 0) (.var 0))

theorem arrCopy_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ (.val copyV) (arrCopyTy a A) := by
  refine sem_const hΓ rfl fun δ ls _ => ⟨rfl, ?_⟩
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨ℓ, n, rfl, hn, hs⟩ := vP_fam_iff.mp hv
  refine wpTS_lolli ls' _ _ _ _ ?_
  show wpTS ls' (.pair (.val (Val.arr ℓ n)) (.val (Val.arr ℓ n))) _ _
  refine wpTS_val ls' (Val.pair (Val.arr ℓ n) (Val.arr ℓ n)) _ _ ?_
  obtain ⟨τ₁, τ₂, hc, h₁, h₂⟩ := sepRange_dup (fun _ _ h => vP_imm_dup h) hs
  exact ⟨_, _, pure_sep_mk rfl ⟨τ₁, τ₂, hc, vP_fam_mk hn h₁, vP_fam_mk hn h₂⟩⟩

/-- `array_forget : !(ArrayImm @a A ⇒ 1)`.  `[spec §9]` -/
abbrev arrForgetTy (a : Lifetime.Life) (A : VTy) : VTy := .bang (.lolli (.arrayImm a A) .unit)

/-- `λp. ()`. -/
def forgetV : Val := .lam (.val .unit)

/-- A family whose leaves hold no `own` cell is forgotten by `λp. ()`. -/
theorem forget_fam_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {L : VTy} (hΓ : Ctx.DeadP Γ)
    (hL : ∀ ls δ m ρ, vP L ls δ (.loc m) ρ → NoOwn ρ) :
    SemV Δ Γ (.val forgetV) (.bang (.lolli (.fam L) .unit)) := by
  refine sem_const hΓ rfl fun δ ls _ => ⟨rfl, ?_⟩
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  refine wpTS_drop (noOwn_fam (hL ls' δ) hv) (ResU.comp_empty_right σ) ?_
  refine wpTS_lolli ls' _ _ _ _ ?_
  exact wpTS_val ls' .unit _ _ ⟨rfl, rfl⟩

theorem arrForget_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ (.val forgetV) (arrForgetTy a A) :=
  forget_fam_compatX hΓ fun _ _ _ _ h => noOwn_imm h

/-! ### `array_size` -/

/-- `array_size : !(Array A ⇒ Array A ⊗ I32)`.  `[spec §9]` -/
abbrev arrSizeTy (A : VTy) : VTy := .bang (.lolli (.array A) (.tensor (.array A) (.int .w32)))

/-- `λp. let (b, n) = p in ((b, n), n)`.  `[spec §9]` -/
def sizeV : Val := .lam (.letpair (.var 0) (.pair (.pair (.var 1) (.var 0)) (.var 0)))

theorem arrSize_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val sizeV) (arrSizeTy A) := by
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

/-! ### `array_replace` -/

/-- `array_replace : !(Array A ⊗ (I32 ⊗ A) ⇒ Array A ⊗ (A ⊕ A))`.  `[spec §9]` -/
abbrev arrReplaceTy (A : VTy) : VTy :=
  .bang (.lolli (.tensor (.array A) (.tensor (.int .w32) A)) (.tensor (.array A) (.sum A A)))

/-- The in-range branch, under `c` (`0`) and `x` (`1`):
`(λold. store c x; old) (load c)`. -/
def swapCellE : Expr :=
  .app (.val (.lam (.seq (.app (.app (.val (.prim .store)) (.var 1)) (.var 2)) (.var 0))))
    (.app (.val (.prim .load)) (.var 0))

/-- `λp. let (f, r) = p in let (i, x) = r in
case idx (f, i) {inj₁ c. (f, inj₁ ((λold. store c x; old) (load c))) | inj₂ _. (f, inj₂ x)}`.
`[spec §9]` -/
def replaceV : Val :=
  .lam (.letpair (.var 0) (.letpair (.var 0)
    (.case (.app (.val (.prim .idx)) (.pair (.var 3) (.var 1)))
      (.pair (.var 4) (.inj₁ swapCellE))
      (.pair (.var 4) (.inj₂ (.var 1))))))

/-- The in-range branch at the element `x`. -/
def replaceIn (ℓ : Loc) (n : UInt32) (x : Val) : Expr :=
  .pair (.val (Val.arr ℓ n)) (.inj₁ (.app (.val (.lam (.seq
    (.app (.app (.val (.prim .store)) (.var 1)) (x.1.shift 2 0)) (.var 0))))
    (.app (.val (.prim .load)) (.var 0))))

/-- The out-of-range branch at the element `x`. -/
def replaceOut (ℓ : Loc) (n : UInt32) (x : Val) : Expr :=
  .pair (.val (Val.arr ℓ n)) (.inj₂ (x.1.shift 1 0))

theorem arr_subst_shift_succ (j : Nat) (s : Val) (e : Expr) :
    Expr.subst j s (Expr.shift (j + 1) 0 e) = Expr.shift j 0 e :=
  Expr.subst_shift j 0 j s e (Nat.zero_le j) (by omega)

theorem shift_arr (d c : Nat) (ℓ : Loc) (n : UInt32) :
    Expr.shift d c (Val.arr ℓ n).1 = (Val.arr ℓ n).1 := rfl

theorem subst_arr (j : Nat) (s : Val) (ℓ : Loc) (n : UInt32) :
    Expr.subst j s (Val.arr ℓ n).1 = (Val.arr ℓ n).1 := rfl

theorem shift_i32 (d c : Nat) (i : UInt32) : Expr.shift d c (Val.i32 i).1 = (Val.i32 i).1 :=
  rfl

theorem replace_body₁ (v : Val) :
    Expr.subst 0 v (.letpair (.var 0) (.letpair (.var 0)
      (.case (.app (.val (.prim .idx)) (.pair (.var 3) (.var 1)))
        (.pair (.var 4) (.inj₁ swapCellE)) (.pair (.var 4) (.inj₂ (.var 1)))))) =
      .letpair (.val v) (.letpair (.var 0)
        (.case (.app (.val (.prim .idx)) (.pair (.var 3) (.var 1)))
          (.pair (.var 4) (.inj₁ swapCellE)) (.pair (.var 4) (.inj₂ (.var 1))))) := by
  simp [Expr.subst, swapCellE]

theorem replace_body₂ (ℓ : Loc) (n : UInt32) (w : Val) :
    ((Expr.letpair (.var 0)
        (.case (.app (.val (.prim .idx)) (.pair (.var 3) (.var 1)))
          (.pair (.var 4) (.inj₁ swapCellE)) (.pair (.var 4) (.inj₂ (.var 1))))).subst 0
        (w.shift 1 0)).subst 0 (Val.arr ℓ n) =
      .letpair (.val w)
        (.case (.app (.val (.prim .idx)) (.pair (.val (Val.arr ℓ n)) (.var 1)))
          (.pair (.val (Val.arr ℓ n)) (.inj₁ swapCellE))
          (.pair (.val (Val.arr ℓ n)) (.inj₂ (.var 1)))) := by
  simp [Expr.subst, swapCellE, Val.shift, Expr.shift_zero, arr_subst_shift_succ, shift_arr]

theorem replace_body₃ (ℓ : Loc) (n i : UInt32) (x : Val) :
    ((Expr.case (.app (.val (.prim .idx)) (.pair (.val (Val.arr ℓ n)) (.var 1)))
          (.pair (.val (Val.arr ℓ n)) (.inj₁ swapCellE))
          (.pair (.val (Val.arr ℓ n)) (.inj₂ (.var 1)))).subst 0 (x.shift 1 0)).subst 0
        (Val.i32 i) =
      .case (.app (.val (.prim .idx)) (.val (Val.pair (Val.arr ℓ n) (Val.i32 i))))
        (replaceIn ℓ n x) (replaceOut ℓ n x) := by
  simp [Expr.subst, swapCellE, replaceIn, replaceOut, Val.shift, Expr.shift_shift,
    arr_subst_shift_succ, subst_arr, shift_i32]

theorem replace_in (ℓ : Loc) (n : UInt32) (x : Val) (c : Loc) :
    (replaceIn ℓ n x).subst 0 (Val.loc c) =
      .pair (.val (Val.arr ℓ n)) (.inj₁ (.app (.val (.lam (.seq
        (.app (.app (.val (.prim .store)) (.val (.loc c))) (x.1.shift 1 0)) (.var 0))))
        (eLoad c))) := by
  simp [replaceIn, eLoad, Expr.subst, Val.shift, Expr.shift, arr_subst_shift_succ, subst_arr]

theorem replace_out (ℓ : Loc) (n : UInt32) (x : Val) :
    (replaceOut ℓ n x).subst 0 Val.unit = (Val.pair (Val.arr ℓ n) (Val.inj₂ x)).1 := by
  simp [replaceOut, Expr.subst, Val.pair, Val.inj₂, Expr.shift_zero, arr_subst_shift_succ,
    subst_arr]

theorem replace_store (c : Loc) (x old : Val) :
    Expr.subst 0 old (.seq (.app (.app (.val (.prim .store)) (.val (.loc c))) (x.1.shift 1 0))
      (.var 0)) = .seq (eStore c x) (.val old) := by
  simp [eStore, Expr.subst, Expr.shift_zero, arr_subst_shift_succ]

theorem arrReplace_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy}
    (hΓ : Ctx.DeadP Γ) : SemV Δ Γ (.val replaceV) (arrReplaceTy A) := by
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
    obtain ⟨ℓ', old, hs'⟩ := hPi
    obtain ⟨hl, c, ρold, hcw, hcell, hold⟩ := pure_sep_iff.mp hs'
    have hℓ : ℓ' = ℓ + i.toNat := by
      have := congrArg Subtype.val hl; simpa using this.symm
    subst hℓ
    -- `σ = c ● G`, `G = ρold ● (ρr ● σx)`
    obtain ⟨F, hF, hiF⟩ := compS_reassoc hci hc
    obtain ⟨G, hG, hσ⟩ := compS_reassoc hcw hiF
    refine wpTS_bind (.pairR (Val.arr ℓ n) (.inj₁ .hole)) _ ls' _ σ ?_
    refine wpTS_bind (.appR (.val (.lam _)) .hole) (eLoad (ℓ + i.toNat)) ls' _ σ ?_
    refine wpTS_load ls' _ old _ σ ⟨c, G, hσ, hcell, ?_⟩
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
    obtain ⟨L, hL, hXL⟩ := compS_reassoc hF hX
    exact ⟨_, _, pure_sep_mk rfl ⟨X, ρold, hp₃',
      vP_fam_mk hn (hback L X (ResU.CompS.comm hXL)
        ⟨_, x, pure_sep_mk rfl ⟨c₃, σx, ResU.CompS.comm hL, hc₃, hx⟩⟩),
      Or.inl ⟨old, pure_sep_mk rfl hold⟩⟩⟩
  · rw [he]
    refine wpTS_sum₂ ls' _ _ _ _ σ ?_
    rw [replace_out]
    exact wpTS_val ls' _ _ σ ⟨_, _, pure_sep_mk rfl
      ⟨σ₁, σx, hc, vP_fam_mk hn hs, Or.inr ⟨x, pure_sep_mk rfl hx⟩⟩⟩

/-! ### `array_new` -/

/-- `array_new : !(I32 ⊗ !(I32 ⇒ A) ⇒ Array A)`.  `[spec §9]` -/
abbrev arrNewTy (A : VTy) : VTy :=
  .bang (.lolli (.tensor (.int .w32) (.bang (.lolli (.int .w32) A))) (.array A))

/-- A `!`-function is valid at every list with the same members, and applies. -/
theorem bang_app {A B : VTy} {ls ls' : List SRec} {δ : LSub} {f v : Val} {ρv : WRes}
    (hf : vP (.bang (.lolli A B)) ls δ f PMap.empty) (hls : ∀ x, x ∈ ls' ↔ x ∈ ls)
    (hv : vP A ls' δ v ρv) :
    wpTS ls' (.app (.val f) (.val v)) (fun ls'' => vP B ls'' δ) ρv :=
  hf.2 ls' (ext_of_same hls _) v ρv ρv hv (compS_empty_left ρv)

/-- The filled cells, as leaves of `Array A`. -/
abbrev doneP (A : VTy) (ls : List SRec) (δ : LSub) : Loc → WProp :=
  fun m => vP (.ref A) ls δ (.loc m)

/-- The placeholders. -/
abbrev todoP : Loc → WProp := fun m => ptoOwn m .unit

theorem doneP_same {A : VTy} {ls ls' : List SRec} {δ : LSub} (hls : ∀ x, x ∈ ls' ↔ x ∈ ls)
    {ℓ : Loc} {n : Nat} {ρ : WRes} (h : sepRange (doneP A ls δ) ℓ n ρ) :
    sepRange (doneP A ls' δ) ℓ n ρ :=
  sepRange_mono' (fun _ _ h => vP_same hls h) h

/-- **The fill.**  With the cells `ℓ, …, ℓ + i − 1` filled and `ℓ + i, …, ℓ + i + k − 1` holding
`()`, the rest of `tabFill` runs to the array.  `[spec §9]` -/
theorem tabFill_wp {A : VTy} {δ : LSub} {ls₀ : List SRec} (f : Val) (ℓ : Loc) (N : UInt32)
    (hN31 : N.toNat < 2 ^ 31) (hf : vP (.bang (.lolli (.int .w32) A)) ls₀ δ f PMap.empty) :
    ∀ (k i : Nat) (ls : List SRec) (ρd ρt ρ : WRes), (∀ x, x ∈ ls ↔ x ∈ ls₀) →
      i + k = N.toNat → sepRange (doneP A ls δ) ℓ i ρd → sepRange todoP (ℓ + i) k ρt →
      ResU.CompS ρd ρt ρ → wpTS ls (tabFill f ℓ N i k) (fun ls' => vP (.array A) ls' δ) ρ
  | 0, i, ls, ρd, ρt, ρ, _, hN, hd, ht, hc => by
      obtain ⟨rfl, -⟩ := ht
      rw [ResU.CompS.functional hc (ResU.comp_empty_right ρd)]
      refine wpTS_val ls (Val.arr ℓ N) _ ρd (vP_fam_mk hN31 ?_)
      rw [← hN]; exact hd
  | k + 1, i, ls, ρd, ρt, ρ, hls, hN, hd, ⟨c, ρt', hct, hcell, ht'⟩, hc => by
      show wpTS ls (.seq (.app (.app (.val (.prim .store)) (.val (.loc (ℓ + i))))
        (.app (.val f) (.val (Val.i32 (UInt32.ofNat i))))) (tabFill f ℓ N (i + 1) k)) _ ρ
      refine wpTS_bind (.seq .hole (tabFill f ℓ N (i + 1) k)) _ ls _ ρ ?_
      -- `ρ = c ● (ρd ● ρt')`
      obtain ⟨R, hR, hρ⟩ := compS_lcomm hct hc
      refine wpTS_bind_frame (.appR (.app (.val (.prim .store)) (.val (.loc (ℓ + i)))) .hole)
        (.app (.val f) (.val (Val.i32 (UInt32.ofNat i)))) ls (fun ls' => vP A ls' δ)
        (fun ls' => ptoOwn (ℓ + i) .unit ⋆ (sepRange (doneP A ls' δ) ℓ i ⋆ sepRange todoP (ℓ + i + 1) k))
        _ ?_ ?_ ρ ⟨PMap.empty, ρ, compS_empty_left ρ,
          bang_app (ls' := ls) hf hls (vP_i32 _), c, R, hρ, hcell, ρd, ρt', hR, hd, ht'⟩
      · intro ls' hls' σ ⟨σ₁, σ₂, hσ, h₁, σ₃, σ₄, hσ', h₃, h₄⟩
        exact ⟨σ₁, σ₂, hσ, h₁, σ₃, σ₄, hσ', doneP_same hls' h₃, h₄⟩
      · intro ls' hls' w σ ⟨σw, σr, hσ, hw, c', R', hR', hc', σd, σt, hdt, hd', ht''⟩
        simp only [Kont.plug]
        -- `σ = c' ● (σw ● R')`
        obtain ⟨G, hG, hσG⟩ := compS_lcomm hR' hσ
        refine wpTS_store ls' (ℓ + i) .unit w _ σ ⟨c', G, hσG, hc', ?_⟩
        intro c₃ σ₃ hc₃ hcomp₃
        refine wpTS_1 ls' _ _ σ₃ ?_
        -- the new leaf `σw ● c₃`, beside the filled cells and the rest of the placeholders
        obtain ⟨L, hL, hσ₃⟩ := compS_exch hG hcomp₃
        obtain ⟨M, hM, hσ₃'⟩ := compS_lcomm hdt hσ₃
        obtain ⟨D, hD, hσ₃''⟩ := compS_reassoc' hM hσ₃'
        have hleaf : doneP A ls' δ (ℓ + i) L :=
          ⟨ℓ + i, w, pure_sep_mk rfl ⟨c₃, σw, ResU.CompS.comm hL, hc₃, hw⟩⟩
        refine tabFill_wp f ℓ N hN31 hf k (i + 1) ls' D σt σ₃ (fun x => (hls' x).trans (hls x))
          (by rw [← hN]; ring) (sepRange_append hD hd' ⟨L, PMap.empty, ResU.comp_empty_right L,
            hleaf, ⟨rfl, trivial⟩⟩) ?_ hσ₃''
        rwa [show ℓ + i + 1 = ℓ + (i + 1) by ring] at ht''

theorem arrNew_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val (.prim .tab)) (arrNewTy A) := by
  refine sem_const hΓ rfl fun δ ls _ => ⟨rfl, ?_⟩
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨v₁, f, hk⟩ := hv
  obtain ⟨rfl, σ₁, σ₂, hc, ⟨e₁, c, rfl⟩, hf⟩ := pure_sep_iff.mp hk
  have e₂ : σ₂ = PMap.empty := hf.1
  subst e₁; subst e₂
  cases eq_empty_of_compS_empty hc
  refine wpTS_tab ls' c f _ PMap.empty ?_
  intro ℓ cells x hcells hx
  rw [eq_of_compS_empty_left hx]
  exact tabFill_wp f ℓ (arrLen c) (arrLen_bound c) hf (arrLen c).toNat 0 ls' PMap.empty cells cells
    (fun _ => Iff.rfl) (by simp) ⟨rfl, trivial⟩ (by simpa using hcells) (compS_empty_left cells)

/-! ### `array_free` -/

/-- `array_free : !(!(A ⇒ 1) ⊗ Array A ⇒ 1)`.  `[spec §9]` -/
abbrev arrFreeTy (A : VTy) : VTy :=
  .bang (.lolli (.tensor (.bang (.lolli A .unit)) (.array A)) .unit)

/-- **The drain.**  The cells `ℓ + i, …, ℓ + i + k − 1` are freed in order, each value handed
to the consumer.  `[spec §9]` -/
theorem dropFill_wp {A : VTy} {δ : LSub} {ls₀ : List SRec} (f : Val) (ℓ : Loc)
    (hf : vP (.bang (.lolli A .unit)) ls₀ δ f PMap.empty) :
    ∀ (k i : Nat) (ls : List SRec) (ρ : WRes), (∀ x, x ∈ ls ↔ x ∈ ls₀) →
      sepRange (doneP A ls δ) (ℓ + i) k ρ →
      wpTS ls (dropFill f ℓ i k) (fun ls' => vP .unit ls' δ) ρ
  | 0, i, ls, ρ, _, hs => by
      obtain ⟨rfl, -⟩ := hs
      exact wpTS_val ls .unit _ _ ⟨rfl, rfl⟩
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
      refine wpTS_bind_frame .hole (.app (.val f) (.val w)) ls (fun ls' => vP .unit ls' δ)
        (fun ls' => sepRange (doneP A ls' δ) (ℓ + i + 1) k) _ ?_ ?_ R
        ⟨ρw, ρr, hR, bang_app hf hls hw, hrest⟩
      · intro ls' hls' σ h
        exact doneP_same hls' h
      · rintro ls' hls' u σ ⟨σu, σr, hσ, ⟨e, rfl⟩, hr⟩
        subst e
        rw [eq_of_compS_empty_left hσ]
        simp only [Kont.plug]
        refine wpTS_val ls' .unit _ σr ?_
        refine wpTS_1 ls' _ _ σr ?_
        refine dropFill_wp f ℓ hf k (i + 1) ls' σr (fun x => (hls' x).trans (hls x)) ?_
        rwa [show ℓ + i + 1 = ℓ + (i + 1) by ring] at hr

theorem arrFree_compatX {Δ : LifeCtx} {Γ : Ctx VTy} {A : VTy} (hΓ : Ctx.DeadP Γ) :
    SemV Δ Γ (.val (.prim .drop)) (arrFreeTy A) := by
  refine sem_const hΓ rfl fun δ ls _ => ⟨rfl, ?_⟩
  intro ls' _ v σ τ hv hcomp
  rw [eq_of_compS_empty_left hcomp]
  obtain ⟨f, v₂, hk⟩ := hv
  obtain ⟨rfl, σ₁, σ₂, hc, hf, h₂⟩ := pure_sep_iff.mp hk
  have e₁ : σ₁ = PMap.empty := hf.1
  subst e₁
  rw [eq_of_compS_empty_left hc]
  obtain ⟨ℓ, n, rfl, hn, hs⟩ := vP_fam_iff.mp h₂
  refine wpTS_dropStep ls' f ℓ n _ σ₂ ?_
  exact dropFill_wp f ℓ hf n.toNat 0 ls' σ₂ (fun _ => Iff.rfl) (by simpa using hs)

end BoCa.Fig16.LogRel.Core

end

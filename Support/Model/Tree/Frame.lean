import Paper.S6_3_FrameAndAntiFrame.Lemmas
import Support.Model.Tree.Order

/-!
# 6.112 and 6.64 in the tree order

The printed proofs, step by step, with the order read in a `Cactus` `K`. What changes:

* `[α]` (row 5.32) is `boxK`: every borrow cell strictly above `α` in `K`.
* `ℓ ↦ Imm α P̂` (row 5.30) is `ptoImmK`: `α ⊑ x` at every member, the witness in the tree
  stratum of every member.
* `И` (row 5.46) is `freshN K n`: `И` at a **branch point** `n`, the innermost lifetime of the
  running computation. The bound `β` lies on `n`'s branch (`n ⊑ β`), and every `α ⊏ β` works.

The one step that needs two lifetimes to be comparable is 6.112's bound `@ρ_P ⊓ β_Q` (the
printed proof takes the shortest lifetime of the framed resource and the shortest of the
bound). In a tree it exists only when the framed resource's lifetimes and `β_Q` have a common
lower bound (`Cactus.comparable_of_lower`). Here that lower bound is the branch point: the
framed resource lies on `n`'s branch (`OnBranchRes K n ρ`), and `n ⊑ β_Q` is `freshN`'s. So
`fresh_frameT` carries `OnBranchRes` as a hypothesis, the fact the cactus supplies: a
computation's borrows are at lifetimes on its branch.

6.64's H4, *"such an `α` always exists because for any lifetime, the set of lifetimes shorter
than it is infinite"*, is `hchild`: the branch point has a child.

Every other step is the printed one: 6.104, 6.10, 6.11, 6.15, 6.34, 6.29, 6.38, 6.26, 6.8,
6.39 are applied unchanged. They read only the carrier's strata, which a tree stratum implies
when the tree sits inside the chain (`ResU.InStratumT.toChain`, `Cactus.InChain`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree
open BoCa.Fig16
open BoCa.Fig16.BoLo

variable {Loc Val : Type}

/-- A cell is on `n`'s branch: every lifetime of it is `n` or above. -/
def CellAbove (K : Cactus) (n : Life) : CellU Loc Val → Prop
  | .own _ => True
  | .imm i => ∀ x, i.ls.mem x → K.le n x
  | .mut m => K.le n m.β

/-- `ρ`'s borrow cells are all on `n`'s branch. -/
def OnBranchRes (K : Cactus) (n : Life) (ρ : ResU Loc Val) : Prop :=
  ∀ l ψ, ρ.get l = some ψ → CellAbove K n ψ

/-- `[α] P` in `K`. -/
def boxK (K : Cactus) (α : Life) (P : SPropU Loc Val) : SPropU Loc Val :=
  fun ρ => P ρ ∧ ResU.InStratumT K α ρ

/-- `И` at the branch point `n`, in `K`. -/
def freshN (K : Cactus) (n : Life) (P : Life → SPropU Loc Val) : SPropU Loc Val :=
  fun ρ => ∃ β, K.le n β ∧ ∀ α, K.lt α β → boxK K α (P α) ρ

/-- `ℓ ↦ Imm α P̂` in `K`. -/
def ptoImmK (K : Cactus) (l : Loc) (α : Life) (P : Val → SPropU Loc Val) : SPropU Loc Val :=
  fun ρ => ∃ (s : LSet) (v : Val) (σ : ResU Loc Val) (h : σ.InStratum s.join),
    ρ = ResU.single l (CellU.immOf s v σ h) ∧ ResU.InStratumAll K s σ ∧ P v σ ∧
      ∀ x, s.mem x → K.le α x

/-- A composite is in a tree stratum iff both parts are: `outlives_comp` in `K`. -/
theorem inStratumT_comp {K : Cactus} {α : Life} {ρ₁ ρ₂ ρ : ResU Loc Val}
    (h : ResU.CompS ρ₁ ρ₂ ρ) :
    ResU.InStratumT K α ρ ↔ (ResU.InStratumT K α ρ₁ ∧ ResU.InStratumT K α ρ₂) := by
  constructor
  · intro hρ
    constructor
    · intro l ψ₁ e₁
      rcases h.get l with ⟨f₁, -, -⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, f₁, -, -⟩ |
          ⟨χ₁, χ₂, χ, f₁, -, f, hC⟩
      · rw [e₁] at f₁; exact absurd f₁ (by simp)
      · rw [e₁] at f₁; cases Option.some.inj f₁; exact hρ l _ f
      · rw [e₁] at f₁; exact absurd f₁ (by simp)
      · rw [e₁] at f₁; cases Option.some.inj f₁
        obtain ⟨s₁, s₂, w, τ, k₁, k₂, k₃, rfl, rfl, rfl⟩ := hC
        exact fun x hx => hρ l _ f x (Or.inl hx)
    · intro l ψ₂ e₂
      rcases h.get l with ⟨-, f₂, -⟩ | ⟨χ, -, f₂, -⟩ | ⟨χ, -, f₂, f⟩ |
          ⟨χ₁, χ₂, χ, -, f₂, f, hC⟩
      · rw [e₂] at f₂; exact absurd f₂ (by simp)
      · rw [e₂] at f₂; exact absurd f₂ (by simp)
      · rw [e₂] at f₂; cases Option.some.inj f₂; exact hρ l _ f
      · rw [e₂] at f₂; cases Option.some.inj f₂
        obtain ⟨s₁, s₂, w, τ, k₁, k₂, k₃, rfl, rfl, rfl⟩ := hC
        exact fun x hx => hρ l _ f x (Or.inr hx)
  · rintro ⟨h₁, h₂⟩ l ψ e
    rcases h.get l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
        ⟨χ₁, χ₂, χ, f₁, f₂, f, hC⟩
    · rw [e] at f; exact absurd f (by simp)
    · rw [e] at f; cases Option.some.inj f; exact h₁ l _ f₁
    · rw [e] at f; cases Option.some.inj f; exact h₂ l _ f₂
    · rw [e] at f; cases Option.some.inj f
      obtain ⟨s₁, s₂, w, τ, k₁, k₂, k₃, rfl, rfl, rfl⟩ := hC
      rintro x (hx | hx)
      · exact h₁ l _ f₁ x hx
      · exact h₂ l _ f₂ x hx

/-- A composite of two resources on `n`'s branch is on it. -/
theorem onBranchRes_comp {K : Cactus} {n : Life} {ρ₁ ρ₂ ρ : ResU Loc Val}
    (h : ResU.CompS ρ₁ ρ₂ ρ) (h₁ : OnBranchRes K n ρ₁) (h₂ : OnBranchRes K n ρ₂) :
    OnBranchRes K n ρ := by
  intro l ψ e
  rcases h.get l with ⟨-, -, f⟩ | ⟨χ, f₁, -, f⟩ | ⟨χ, -, f₂, f⟩ |
      ⟨χ₁, χ₂, χ, f₁, f₂, f, hC⟩
  · rw [e] at f; exact absurd f (by simp)
  · rw [e] at f; cases Option.some.inj f; exact h₁ l _ f₁
  · rw [e] at f; cases Option.some.inj f; exact h₂ l _ f₂
  · rw [e] at f; cases Option.some.inj f
    obtain ⟨s₁, s₂, w, τ, k₁, k₂, k₃, rfl, rfl, rfl⟩ := hC
    rintro x (hx | hx)
    · exact h₁ l _ f₁ x hx
    · exact h₂ l _ f₂ x hx

/-- An `own` cell is on every branch. -/
theorem onBranchRes_own (K : Cactus) (n : Life) (l : Loc) (v : Val) :
    OnBranchRes K n (ResU.single l (CellU.ownOf (Loc := Loc) v)) := by
  intro x ψ e
  obtain ⟨-, rfl⟩ := ResU.single_get_eq_some e
  trivial

/-- A resource on `n`'s branch is in the tree stratum of every `α ⊏ n`. -/
theorem OnBranchRes.inStratumT {K : Cactus} {n α : Life} {ρ : ResU Loc Val}
    (h : OnBranchRes K n ρ) (hα : K.lt α n) : ResU.InStratumT K α ρ := by
  intro l ψ e
  have := h l ψ e
  cases ψ with
  | own _ => trivial
  | imm i => exact fun x hx => Cactus.lt_of_lt_of_le hα (this x hx)
  | «mut» m => exact Cactus.lt_of_lt_of_le hα this

/-- **`[TR]` Lemma 6.112 (`Иf`) in the tree order.** The printed bound is `@ρ_P ⊓ β_Q`; here it
is the branch point `n`, a lower bound of `β_Q` (`freshN`) and of every lifetime of the framed
resource (`hP`). -/
theorem fresh_frameT (K : Cactus) (n : Life) (P : SPropU Loc Val) (Q : Life → SPropU Loc Val)
    (hP : ∀ ρ, P ρ → OnBranchRes K n ρ) :
    (P ⋆ freshN K n Q) ⊨ freshN K n (fun α => boxK K α P ⋆ Q α) := by
  rintro ρ ⟨ρ₁, ρ₂, hc, hP₁, ⟨β, hnβ, hβ⟩⟩
  refine ⟨n, K.refl n, fun α hα => ?_⟩
  have k₁ : ResU.InStratumT K α ρ₁ := (hP ρ₁ hP₁).inStratumT hα
  obtain ⟨hQ, o₂⟩ := hβ α (Cactus.lt_of_lt_of_le hα hnβ)
  exact ⟨⟨ρ₁, ρ₂, hc, ⟨hP₁, k₁⟩, hQ⟩, (inStratumT_comp hc).mpr ⟨k₁, o₂⟩⟩

end BoCa.Fig16.Tree

namespace BoCa.Fig16.LogRel.Tree
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore)

/-- **`[TR]` Theorem 6.64 (`Imm Frame`) in the tree order**, by the printed proof. Added
hypotheses: `hchild`, H4's *"such an `α` always exists"* at the branch point; `hbr`, the lent
payload lies on the branch (what 6.112's `⊓` reads). The order sits inside the chain (`hK`),
so the carrier's strata hold the tree's. -/
theorem wp_I_frameT (K : Cactus) (hK : K.InChain) (n : Life) (hchild : ∃ c, K.lt c n)
    (l : BoCa.Loc)
    (P : Val → WProp) (v : Val) (e : Expr) (Q : Val → WProp)
    (hbr : ∀ ρ, P v ρ → OnBranchRes K n ρ) :
    Entails
      (ptoOwn l v ⋆ P v ⋆
        freshN K n (fun α => ptoImmK K l α P ─⋆
          wp e (fun v' => boxK K α (ptoOwn l v ─⋆ (P v ─⋆ Q v')))))
      (wp e Q) := by
  have hbrlP : ∀ ρ, (ptoOwn l v ⋆ P v) ρ → OnBranchRes K n ρ := by
    rintro ρ ⟨ρ₁, ρ₂, hc, rfl, h₂⟩
    exact onBranchRes_comp hc (onBranchRes_own K n l v) (hbr ρ₂ h₂)
  classical
  intro ρ hH2 ρf hH3
  -- 6.112 pulls `ℓ ↦ v ⋆ P̂(v)` inside the `⋔`, at the branch point
  obtain ⟨γ, hnγ, hγ⟩ := fresh_frameT K n (ptoOwn l v ⋆ P v) _ hbrlP ρ
    (BoLo.sep_assoc' _ _ _ ρ hH2)
  -- H4: a lifetime strictly below the bound, a child of the branch point
  obtain ⟨A, hAn⟩ := hchild
  have hAγ : K.lt A γ := Cactus.lt_of_lt_of_le hAn hnγ
  obtain ⟨hbody, houtρ⟩ := hγ A hAγ
  -- 6.104 splits the box over the `⋆`
  obtain ⟨ρlP, ρb, hcρ, hlP, hwand⟩ := hbody
  obtain ⟨hlPv, houtlP⟩ := hlP
  obtain ⟨ρl, ρP, hclP, hpl, hPv⟩ := hlPv
  subst hpl
  -- H10 and H11, in `K`, and in the carrier's stratum
  have houtPT : ResU.InStratumT K A ρP := ((inStratumT_comp hclP).mp houtlP).2
  have houtbT : ResU.InStratumT K A ρb := ((inStratumT_comp hcρ).mp houtρ).2
  have houtP : ResU.InStratum A ρP := houtPT.toChain hK
  have houtb : ResU.InStratum A ρb := houtbT.toChain hK
  -- the "fictional" `ρᵢ = ℓ ↦ imm({α}, v, ρ_P̂(v))`, well formed by H10
  set ρi : ResU BoCa.Loc BoCa.Val :=
    ResU.single l (CellU.immOf (LSet.singleton A) v ρP houtP) with hρidef
  -- ✓ρ, by 6.10 with ✓(ρ_f ● ρ) from H3
  obtain ⟨-, sρ, hsρ, hvsρ⟩ := id hH3
  have hvρ : ResU.Valid ρ := (ResU.Valid.split hsρ hvsρ).2
  have hlPcell : ResU.CompS ρP (ResU.single l (CellU.ownOf v)) ρlP :=
    ResU.CompS.comm hclP
  -- H12-H17: the compatibility block
  have hH12 : ResU.Hash ρb ρlP :=
    ⟨ResU.CompatS.symm hcρ.1, ρ, ResU.CompS.comm hcρ, hvρ⟩
  have hH13 : ResU.Hash ρb ρi := ResU.six34 hlPcell hH12
  obtain ⟨hlPf, hbf⟩ := ResU.Hash.split hcρ (ResU.hash_symm hH3)
  have hH15 : ResU.Hash ρf ρi := ResU.six34 hlPcell (ResU.hash_symm hlPf)
  obtain ⟨BI, hBI⟩ := (ResU.compS_defined_iff ρb ρi).mpr hH13.1
  have hH17 : ResU.Hash ρf BI :=
    ResU.hash_of_pairwise (ResU.hash_symm hbf) hH13 hH15 hBI
  -- H18: the wand, at the fictional borrow
  have hwpBI := hwand ρi BI
    ⟨LSet.singleton A, v, ρP, houtP, rfl, fun x hx => hx ▸ houtPT, hPv,
      fun x hx => hx ▸ K.refl A⟩ hBI
  obtain ⟨ρ', ρp, fρ, fρ', fρ'p, π, v', μ, μ',
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwpBI ρf hH17
  -- H24 and H25
  obtain ⟨hwand', houtρ'T⟩ := h12
  have houtρ' : ResU.InStratum A ρ' := houtρ'T.toChain hK
  -- H27
  obtain ⟨hfρp, hρ'p⟩ := ResU.Hash.split h2 (ResU.hash_symm h3)
  -- H26: 6.29 with H11 and H12 and H21, then "by H24, `ℓ ∉ dom(ρ′)`"
  obtain ⟨hGsplit, hGiH, hGc⟩ :=
    ResU.six38_steps_one_two hlPcell hH12 hρ'p houtb houtρ' hBI h9 h10
  -- H28: 6.38 with H12 and H27 and H11 and H24 and H22 and H21
  obtain ⟨G₀, hG₀, hH28⟩ :=
    ResU.six38 hlPcell hH12 hρ'p houtb houtρ' h11 hBI h9 h10
  obtain rfl : π.del l = G₀ := ResU.CompS.functional hGsplit hG₀
  -- `ρ⁺ = ρ⁺/ℓ ● ρᵢ`
  have hπl : π.get l = some (CellU.immOf (LSet.singleton A) v ρP houtP) :=
    ResU.compS_single_get_self (ResU.CompS.comm hGc) (ResU.del_get_self _ _)
  have hρ'l : ρ'.get l = none := ResU.six38_no_borrow_in_frame houtρ' h9 hπl
  have hppl : ρp.get l = some (CellU.immOf (LSet.singleton A) v ρP houtP) :=
    (ResU.Comp.get_of_left_none h9 hρ'l).symm.trans hπl
  have hpd : ResU.CompS (ρp.del l) ρi ρp := ResU.del_compS hppl
  -- H29-H33: the second compatibility block
  obtain ⟨hPDf, -⟩ := ResU.Hash.split hpd (ResU.hash_symm hfρp)
  obtain ⟨hPDρ', -⟩ := ResU.Hash.split hpd (ResU.hash_symm hρ'p)
  obtain ⟨hρ'lPh, hPDlP⟩ := ResU.Hash.split hGsplit hH28
  have hflP : ResU.Hash ρf ρlP := ResU.hash_symm hlPf
  obtain ⟨R, hR⟩ := (ResU.compS_defined_iff ρ' ρlP).mpr hρ'lPh.1
  have hfR : ResU.Hash ρf R :=
    ResU.hash_of_pairwise (ResU.hash_symm h1) hρ'lPh hflP hR
  obtain ⟨FR, hFR⟩ := (ResU.compS_defined_iff ρf R).mpr hfR.1
  have hPDR : ResU.Hash (ρp.del l) R :=
    ResU.hash_of_pairwise hPDρ' hρ'lPh hPDlP hR
  have hPDFR : ResU.Hash (ρp.del l) FR :=
    ResU.hash_of_pairwise hPDf hfR hPDR hFR
  obtain ⟨FRP, hFRP⟩ :=
    (ResU.compS_defined_iff FR (ρp.del l)).mpr (ResU.hash_symm hPDFR).1
  obtain ⟨RP, hRP⟩ :=
    (ResU.compS_defined_iff R (ρp.del l)).mpr (ResU.hash_symm hPDR).1
  -- H34: the two memories, by 6.26 under a frame (6.8)
  obtain ⟨FB, hFB⟩ := (ResU.compS_defined_iff ρf ρb).mpr (ResU.hash_symm hbf).1
  obtain ⟨FB₁, hFB₁, hFBi⟩ := (ResU.CompS.assoc ρf ρb ρi fρ).mp ⟨BI, hBI, h4⟩
  obtain rfl : FB = FB₁ := ResU.CompS.functional hFB hFB₁
  obtain ⟨FB₂, hFB₂, hFBl⟩ :=
    (ResU.CompS.assoc ρf ρb ρlP sρ).mp ⟨ρ, ResU.CompS.comm hcρ, hsρ⟩
  obtain rfl : FB = FB₂ := ResU.CompS.functional hFB hFB₂
  have hvlP : ResU.Valid ρlP := by
    obtain ⟨-, s, hs, hv⟩ := hH12; exact (ResU.Valid.split hs hv).2
  have hvBI : ResU.Valid BI := by
    obtain ⟨-, s, hs, hv⟩ := hH17; exact (ResU.Valid.split hs hv).2
  have hvi : ResU.Valid ρi := (ResU.Valid.split hBI hvBI).2
  have hFBiH : ResU.Hash FB ρi :=
    ResU.hash_symm (ResU.hash_of_pairwise (ResU.hash_symm hH15)
      (ResU.hash_symm hbf) (ResU.hash_symm hH13) hFB)
  have hFBlH : ResU.Hash FB ρlP :=
    ResU.hash_symm
      (ResU.hash_of_pairwise hlPf (ResU.hash_symm hbf) (ResU.hash_symm hH12) hFB)
  have hmem₁ : ResU.Lower sρ μ :=
    (ResU.lower_swap_imm_own hlPcell hvi hvlP hFBi hFBiH hFBl hFBlH).mp h5
  -- and at the other end of the run
  obtain ⟨FP, hFP, hFPi⟩ :=
    (ResU.CompS.assoc fρ' (ρp.del l) ρi fρ'p).mp ⟨ρp, hpd, h6⟩
  obtain ⟨RP₁, hRP₁, hfRP⟩ := (ResU.CompS.assoc ρf R (ρp.del l) FRP).mpr ⟨FR, hFR, hFRP⟩
  obtain rfl : RP = RP₁ := ResU.CompS.functional hRP hRP₁
  obtain ⟨WP, hWP, hρ'WP⟩ := (ResU.CompS.assoc ρ' ρlP (ρp.del l) RP).mpr ⟨R, hR, hRP⟩
  obtain ⟨D₁, hD₁, hDlP⟩ :=
    (ResU.CompS.assoc ρ' (ρp.del l) ρlP RP).mp ⟨WP, ResU.CompS.comm hWP, hρ'WP⟩
  obtain rfl : π.del l = D₁ := ResU.CompS.functional hGsplit hD₁
  obtain ⟨FPD, hFPD, hFPDlP⟩ :=
    (ResU.CompS.assoc ρf (π.del l) ρlP FRP).mp ⟨RP, hDlP, hfRP⟩
  obtain ⟨FP₁, hFP₁, hFPρ'⟩ := (ResU.CompS.assoc ρf ρ' (ρp.del l) FP).mpr ⟨fρ', h2, hFP⟩
  obtain rfl : π.del l = FP₁ := ResU.CompS.functional hGsplit hFP₁
  obtain rfl : FP = FPD := ResU.CompS.functional hFPρ' hFPD
  have hvfρ'p : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := h7; exact ⟨σ, hσ⟩
  have hvFRP : ResU.Valid FRP := by
    obtain ⟨-, s, hs, hv⟩ := ResU.hash_symm hPDFR
    exact ResU.CompS.functional hs hFRP ▸ hv
  have hFPiH : ResU.Hash FP ρi := ⟨hFPi.1, fρ'p, hFPi, hvfρ'p⟩
  have hFPlH : ResU.Hash FP ρlP := ⟨hFPDlP.1, FRP, hFPDlP, hvFRP⟩
  have hmem₂ : ResU.Lower FRP μ' :=
    (ResU.lower_swap_imm_own hlPcell hvi hvlP hFPi hFPiH hFPDlP hFPlH).mp h7
  -- H35: `ρ ↭ ρ′ ● ρ⁺/ℓ ● ρ_ℓ ● ρ_P̂(v)`, by 6.39 with H12 and H28 and H21
  obtain ⟨w₁, w₂, hw₁, hw₂, hupdw⟩ := ResU.six39 hclP hH12 hH28 hBI hGc h10
  obtain rfl : ρ = w₁ := ResU.CompS.functional (ResU.CompS.comm hcρ) hw₁
  obtain rfl : RP = w₂ := ResU.CompS.functional hDlP hw₂
  -- G6: `ρ⁺/ℓ` is still own-free
  have hno : BoLo.NoOwn (ρp.del l) := by
    refine PMap.ext fun x => ?_
    cases hgg : ((ρp.del l).restrict Kind.own).get x with
    | none => simp
    | some ψ =>
        exfalso
        obtain ⟨hdd, hk⟩ := ResU.restrict_eq_some.mp hgg
        by_cases hx : x = l
        · subst hx; rw [ResU.del_get_self] at hdd; simp at hdd
        · rw [ResU.del_get_ne _ hx] at hdd
          have hcc : (ρp.restrict Kind.own).get x = some ψ :=
            ResU.restrict_eq_some.mpr ⟨hdd, hk⟩
          rw [h11] at hcc
          simp at hcc
  -- H36: the callback's wand, at the cell and the payload it gets back
  obtain ⟨X, hX, hXR⟩ :=
    (ResU.CompS.assoc ρ' (ResU.single l (CellU.ownOf v)) ρP R).mp ⟨ρlP, hclP, hR⟩
  have hQ : Q v' R := (hwand' _ X rfl hX) ρP R hPv hXR
  exact ⟨R, ρp.del l, sρ, FR, FRP, RP, v', μ, μ',
    ResU.hash_symm hfR, hFR, hPDFR, hsρ, hmem₁, hFRP, hmem₂, h8, hRP,
    hupdw, hno, hQ⟩
/-- The added hypotheses are met: in `star` at the branch point `⊤`, with a payload that holds
no borrow. -/
theorem wp_I_frameT_hyps (v : Val) : Cactus.star.InChain ∧
    (∃ c, Cactus.star.lt c ⊤) ∧
      ∀ ρ, (fun _ : Val => (emp : WProp)) v ρ → OnBranchRes Cactus.star ⊤ ρ := by
  refine ⟨Cactus.star_inChain, ⟨_, Cactus.star_lt_top (n := 1) (by decide)⟩, ?_⟩
  rintro ρ ⟨rfl, -⟩ l ψ e
  simp at e

end BoCa.Fig16.LogRel.Tree

end

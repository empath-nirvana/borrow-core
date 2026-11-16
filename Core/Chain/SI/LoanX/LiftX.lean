import Core.Chain.SI.LoanX.ErwpKX
import Core.Chain.SI.LoanX.Erasure

/-!
# A main run is an X run, its ghost framed out  `[spec §62]`

`rwpGX_of_rwpG`: a main `rwpG` run from `ρ` is an `rwpGX` run from `(ρ, g)` at a mask `M` that
lends nothing across stops (`M.lendLocs = ∅`, as a mask of `mloan` entries), when `ρ` carries no
lifetime `g` holds a token of. The run's `ImmTieL` is asked at its entry list, as main asks it.
The ghost `g` and the mask come back unchanged at the end; the update `↭` is main's, unmasked.

`erwpKX_of_erwpK` lifts a main `erwpK` at the typed world, its stops at `opTableK`, to `erwpKX`
at a loan world, its stops at the lifted table (`liftTabX`): every payload at zero ghost, the whole
ghost `g` with the continuation, every reply at zero ghost carrying no lifetime and with the
resumption list's `ImmTieL` at the resumption world. A loan world `LoanKW.Owed` admits is one main
`KW.Owed` admits (its first conjunct), so a main continuation covers it. `erwpKX_of_cN_ret` and
`erwpKX_of_cN_eff` read it at `cN`'s `F A` and `F_Σ R`.

`rwpG_of_rwpGX_mloan` is the converse at a `mut` loan's mask `{(ℓ, mloan κ)}`: an X run entered
with `[κ]_1`, for a `κ` the main frame carries nowhere (`exists_not_carried`), that ends with no
borrow at `ℓ`, is a main run.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa.Lifetime (LSub)
open BoCa.BoLo (Kont performE raiseE opPayload)

/-! ### `↭`'s `imm` clause keeps what is carried and shallowness -/

theorem carries_of_updImm {ρ π : WRes} (hu : ResU.UpdImm ρ π) {α : Life} (h : Carries π α) :
    Carries ρ α := by
  obtain ⟨l, s, v, χ, hh, hf, hm⟩ := h
  exact ⟨l, s, v, χ, hh, (hu l s v χ hh).mpr hf, hm⟩

/-- Main `↭` from a resource with no borrow at `L` reaches one with none there. -/
theorem noBorrowAt_of_updN {Φ : LocFam} {n : Nat} {L : Set Loc} {ρ π : WRes}
    (hu : UpdN Φ n ρ π) (h : NoBorrowAt L ρ) : NoBorrowAt L π := by
  intro l hl ψ hψ
  cases hk : ψ.kind with
  | own => rfl
  | imm =>
      obtain ⟨t, ht, hψeq⟩ := CellU.imm_eta hk
      rw [hψeq] at hψ
      have h' := h l hl _ ((hu.1 l t _ _ ht).mpr hψ)
      rw [CellU.kind_immOf] at h'; cases h'
  | «mut» =>
      obtain ⟨ψ₀, h₀, hs⟩ := hu.2.2 l ψ hψ hk
      have h' := h l hl ψ₀ h₀
      rw [hs.1] at h'; cases h'

theorem not_carries_of_noBorrowAt {ρ : WRes} (h : NoBorrowAt Set.univ ρ) (α : Life) :
    ¬ Carries ρ α := by
  rintro ⟨l, s, v, χ, hh, hf, -⟩
  have h' := h l (Set.mem_univ l) _ hf
  rw [CellU.kind_immOf] at h'; cases h'

theorem maskShallow_of_updImm {L : Set Loc} {ρ π : WRes} (hu : ResU.UpdImm ρ π)
    (h : MaskShallow L ρ) : MaskShallow L π :=
  fun l hl s v χ hh hf => h l hl s v χ hh ((hu l s v χ hh).mpr hf)

/-! ### One segment -/

/-- A main post read at the X relation: at the run's mask, the ghost `g` unchanged, the end valid,
carrying no lifetime `g` holds a token of and holding no borrow where `M` lends `mut`. -/
def liftPostGX (M : Mask) (g : GRes) (Q : PostG) : PostGX :=
  fun M' _ k ls t x => M' = M ∧ x.2 = g ∧ x.1.Valid ∧ (∀ α, 0 < g.tok α → ¬ Carries x.1 α) ∧
    NoBorrowAt M.mloanLocs x.1 ∧ Q k ls t x.1

/-- **A main run is an X run**, the ghost `g` framed out, at a mask lending nothing across stops. -/
theorem rwpGX_of_rwpG {Φ : LocFam} {M : Mask} {Q : PostG} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes} {g : GRes} (hlend : M.lendLocs = ∅) (himm : ImmTieL Φ.imm ls)
    (hnc : ∀ α, 0 < g.tok α → ¬ Carries ρ α) (hnb : NoBorrowAt M.mloanLocs ρ)
    (h : rwpG (ℍ := ℍ) Φ Q n ls e ρ) :
    rwpGX (ℍ := ℍ) Φ M (liftPostGX M g Q) n ls e (ρ, g) := by
  intro xf fρ ps μ hf hc hv _hwf hwx hsh hau _hoff hT htg hl hfd j μ' e' hj hrun hfin
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂,
    hQ⟩ := h xf.1 fρ ps μ hf hc hT htg himm hl hfd j μ' e' hj hrun hfin
  have hvπ : π.Valid := h₇.2.2
  have hu : ResU.UpdImm ρ π := h₇.1.1
  have hρ : ∀ α, α ∈ (xf.2 + g).counted → ¬ Carries ρ α := fun α hα hcα =>
    hnc α (hwx α hα hcα) hcα
  have hshπ : MaskShallow M.locs π := maskShallow_of_updImm hu hsh
  have hg0 : xf.2 + (g + 0) = xf.2 + g := by rw [GRes.add_zero]
  have hπnb : NoBorrowAt M.mloanLocs π := noBorrowAt_of_updN h₇.1 hnb
  refine ⟨M, ρ', ρp, fρ', fρ'p, π, g, 0, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, ?_, h₈, h₉, h₁₀,
    RecAgree.of_iff h₁₁, ListAgree.of_iff h₁₂, ?_, ?_, ?_, ?_, maskShallow_left h₆ hvπ hshπ, ?_,
    hau, ?_, ?_, ?_, NoBorrowAt.right h₆ hvπ hπnb, rfl, rfl, (hash_valid h₁).1,
    fun α hα hcα => ?_, NoBorrowAt.left h₆ hvπ hπnb, hQ⟩
  · rw [Set.union_self]
    exact (updVNm_empty_iff.mpr h₇).mono (Set.empty_subset _)
  · rw [hg0]; exact hv
  · intro α hα hα₀; rw [hg0] at hα; exact absurd hα hα₀
  · rw [hg0]
    exact fun α hα hcα => absurd (carries_of_updImm hu (carries_comp_left h₆ hvπ hcα)) (hρ α hα)
  · rw [hg0]
    exact fun α hα hcα => absurd (carries_of_updImm hu (carries_comp_right h₆ hvπ hcα)) (hρ α hα)
  · rw [Set.union_self]; exact hshπ
  · intro l hl; rw [hlend] at hl; exact absurd hl (Set.notMem_empty l)
  · rw [Set.sdiff_self]; exact maskShallow_empty _
  · rw [Mask.fresh_self]; exact flatNone_empty _
  · exact hnc α hα (carries_of_updImm hu (carries_comp_left h₆ hvπ hcα))

/-! ### The lifted table -/

/-- A main entry at a loan world: the payload at zero ghost; the reply at zero ghost, holding no
borrow, with the resumption list's `ImmTieL` at the resumption world's family. -/
def liftEntX (Φ : KW → LocFam) (en : OpEntK KW) : LoanOpEntX where
  q := en.q
  remask := false
  PA := fun k ls v r => r.2 = 0 ∧ en.PA k ls v r.1
  PB := fun y k ls v r => r.2 = 0 ∧ NoBorrowAt Set.univ r.1 ∧ ImmTieL (Φ y.typed).imm ls ∧
    en.PB y.typed k ls v r.1
  wc := fun ls ls' r => en.wc ls ls' r.1

/-- A main table at a loan world. -/
def liftTabX (Φ : KW → LocFam) (T : OpTabK KW) : LoanOpTabX := fun n i => (T n i).map (liftEntX Φ)

/-- `loanPerformTableX` at a table read at the stop's world. -/
def loanPerformTableXW (T : LoanKW → LoanOpTabX) : LoanTableX :=
  fun x => loanPerformTableX (T x) x

theorem loanPerformTableXW_local (T : LoanKW → LoanOpTabX) : (loanPerformTableXW T).Local :=
  fun x => loanPerformTableX_local (T x) x

/-- A main value post at a loan world, the ghost `g`. -/
def liftQX (g : GRes) (Q : KW → PostN) : LoanKW → PostX :=
  fun y _ k ls v r => r.2 = g ∧ Q y.typed k ls v r.1

/-! ### The recursive lift -/

/-- **A main `erwpK` at the typed world is an `erwpKX` at a loan world**, the ghost `g` framed out
and carried to every continuation, at a mask lending nothing across stops. The table's entries
resume (`abort = false`) and owe their continuations at least at every world `KW.Owed` admits. -/
theorem erwpKX_of_erwpK (Φ : KW → LocFam) (T : KW → OpTabK KW) (Q : KW → PostN) {M : Mask}
    {g : GRes} (hlend : M.lendLocs = ∅)
    (hab : ∀ z m i en, T z m i = some en → en.abort = false)
    (hwk : ∀ z m i en, T z m i = some en → ∀ f y ρ, z.Owed f y ρ → en.wk f y ρ) :
    ∀ n (x : LoanKW) ls e ρ, ImmTieL (Φ x.typed).imm ls → (∀ α, 0 < g.tok α → ¬ Carries ρ α) →
      NoBorrowAt M.mloanLocs ρ →
      erwpK (ℍ := ℍ) KW.PostK Φ (fun z => opTableK z.lo (T z)) Q x.typed n ls e ρ →
      erwpKX (ℍ := ℍ) (fun x y => y = x) (fun y => Φ y.typed)
        (loanPerformTableXW (fun y => liftTabX Φ (T y.typed))) (liftQX g Q) x M n ls e (ρ, g) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ himm hnc hnb h
  rw [erwpK_eq] at h
  rw [erwpKX_eq]
  refine rwpGX_mono_le (fun M' C k hk ls' t r ht => ?_) (rwpGX_of_rwpG hlend himm hnc hnb h)
  obtain ⟨ρ', g'⟩ := r
  obtain ⟨hM, hg, hvr, hncr, hnbr, hpost⟩ := ht
  simp only at hg hvr hncr hnbr hpost
  subst M'
  subst g'
  rcases hpost with ⟨v, rfl, y, hy, hq⟩ | hstop
  · -- a value: the post's world is the run's
    cases hy
    exact Or.inl ⟨rfl, v, rfl, x, rfl, rfl, hq⟩
  rcases hstop with ⟨K, m, i, v, en, hst⟩ | ⟨K, m, i, v, en, hst⟩
  swap
  · -- an abortive stop: no entry is abortive
    obtain ⟨⟨-, -, hen, hab'⟩, -⟩ := pure_sep_iff.mp hst
    rw [hab _ _ _ _ hen] at hab'
    cases hab'
  obtain ⟨⟨ht, hK, hen, -⟩, ρa, ρk, hcρ, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hst
  refine Or.inr ⟨K, m, i, v, liftEntX Φ en, ht, hK, by simp [liftTabX, hen], Or.inr rfl,
    ρa, ρk, 0, g, hcρ, by simp, ⟨rfl, hA⟩, fun hq => hu hq, f, hf, ?_⟩
  intro y hyo ls'' hwc k' hk' w z r hz hcomp
  obtain ⟨hz0, hznb, hzimm, hzB⟩ := hz
  obtain ⟨hcr, hr2⟩ := hcomp
  have hΨ := (hcont y.typed (hwk _ _ _ _ hen f y.typed ρk hyo.1) ls'' hwc).1 k' hk' w z.1 r.1
    hzB hcr
  have hk'n : k' < n := by omega
  simp only [erwpCK, hk'n, if_true] at hΨ
  simp only [erwpKXC, hk'n, if_true]
  obtain ⟨r₁, r₂⟩ := r
  have hr₂ : r₂ = g := by simpa [hz0] using hr2
  subst hr₂
  refine ih k' hk'n y ls'' _ r₁ hzimm (fun α hα hcα => ?_)
    (noBorrowAt_comp hcr (NoBorrowAt.right hcρ hvr hnbr) (hznb.mono (Set.subset_univ _))) hΨ
  rcases carries_comp_split hcr hcα with hc₁ | hc₂
  · exact hncr α hα (carries_comp_right hcρ hvr hc₁)
  · exact not_carries_of_noBorrowAt hznb α hc₂

/-! ### At `cN` -/

/-- **`cN`'s `F A` lifted**: a loan-free computation at `F A`, run at the loan world's typed world,
is an `erwpKX` there, the ghost framed out. -/
theorem erwpKX_of_cN_ret {A : VTy} {δ : LSub} {M : Mask} {g : GRes} (hlend : M.lendLocs = ∅)
    {n : Nat} (x : LoanKW) {ls : List SRec} {e : Expr} {ρ : WRes}
    (himm : ImmTieL (x.typed.Θ.view x.typed.c).imm ls) (hnc : ∀ α, 0 < g.tok α → ¬ Carries ρ α)
    (hnb : NoBorrowAt M.mloanLocs ρ)
    (h : cN (ℍ := ℍ) (.ret A) δ x.typed.Θ x.typed.c n ls e ρ) :
    erwpKX (ℍ := ℍ) (fun x y => y = x) (fun y => y.typed.Θ.view y.typed.c)
      (loanPerformTableXW (fun _ => liftTabX (fun z => z.Θ.view z.c) OpTabK.empty))
      (liftQX g (fun z k _ v ρ => vNE none A δ z.Θ k v ρ)) x M n ls e (ρ, g) := by
  rw [cN] at h
  exact erwpKX_of_erwpK (fun z => z.Θ.view z.c) (fun _ => OpTabK.empty) _ hlend
    (fun _ _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h) n x ls e ρ himm hnc
    hnb (h x.typed.lo)

/-- Every entry of a row's table at the typed world owes its continuation at every world
`KW.Owed` admits. -/
theorem tabN_wk : ∀ (C : CTy) (δ : LSub) (z : KW) (m i : UInt32) (en : OpEntK KW),
    tabN (ℍ := ℍ) C δ z m i = some en → ∀ f y ρ, z.Owed f y ρ → en.wk f y ρ
  | .eff m₀ i₀ q A B fin _ C, δ, z, m, i, en, h => by
      rw [tabN] at h
      rcases extTabK_some h with ⟨-, -, rfl⟩ | h
      · exact fun _ _ _ hy => hy
      · exact tabN_wk C δ z m i en h
  | .ret _, _, _, _, _, _, h => by simp [tabN, OpTabK.empty] at h
  | .arr _ _, _, _, _, _, _, h => by simp [tabN, OpTabK.empty] at h
  | .amp _ _, _, _, _, _, _, h => by simp [tabN, OpTabK.empty] at h
  | .top, _, _, _, _, _, h => by simp [tabN, OpTabK.empty] at h
  | .all _ _ _, _, _, _, _, _, h => by simp [tabN, OpTabK.empty] at h
  | .nuSys _ _ _, _, _, _, _, _, h => by simp [tabN, OpTabK.empty] at h

/-- **`cN`'s `F_Σ R` lifted**: a loan-free computation at `F_Σ R` whose row resumes at every
operation is an `erwpKX` at the loan world, the ghost framed out and carried to every
continuation. -/
theorem erwpKX_of_cN_eff {m i : UInt32} {q : Qual} {A B : VTy} {fin : CTy} {b : Bool} {C : CTy}
    {δ : LSub} {M : Mask} {g : GRes} (hlend : M.lendLocs = ∅)
    (hab : ∀ z m' i' en, extTabK m i (entNK q B (fun k v ρ => vNE none A δ z.Θ k v ρ)
        (fun y k v ρ => vNE none B δ y.Θ k v ρ ∧ ConsistentX y.c ρ)
        (finN (ℍ := ℍ) fin δ) (fun f y ρ => z.Owed f y ρ)) (tabN (ℍ := ℍ) C δ z) m' i' = some en →
      en.abort = false)
    {n : Nat} (x : LoanKW) {ls : List SRec} {e : Expr} {ρ : WRes}
    (himm : ImmTieL (x.typed.Θ.view x.typed.c).imm ls) (hnc : ∀ α, 0 < g.tok α → ¬ Carries ρ α)
    (hnb : NoBorrowAt M.mloanLocs ρ)
    (h : cN (ℍ := ℍ) (.eff m i q A B fin b C) δ x.typed.Θ x.typed.c n ls e ρ) :
    erwpKX (ℍ := ℍ) (fun x y => y = x) (fun y => y.typed.Θ.view y.typed.c)
      (loanPerformTableXW (fun y => liftTabX (fun z => z.Θ.view z.c)
        (extTabK m i (entNK q B (fun k v ρ => vNE none A δ y.typed.Θ k v ρ)
          (fun y' k v ρ => vNE none B δ y'.Θ k v ρ ∧ ConsistentX y'.c ρ)
          (finN (ℍ := ℍ) fin δ) (fun f y' ρ => y.typed.Owed f y' ρ)) (tabN (ℍ := ℍ) C δ y.typed))))
      (liftQX g (fun z k _ v ρ => retN (ℍ := ℍ) C δ z.Θ k v ρ)) x M n ls e (ρ, g) := by
  rw [cN] at h
  refine erwpKX_of_erwpK (fun z => z.Θ.view z.c) _ _ hlend hab (fun z m' i' en hen => ?_) n x ls
    e ρ himm hnc hnb (h x.typed.lo)
  rcases extTabK_some hen with ⟨-, -, rfl⟩ | hen
  · exact fun _ _ _ hy => hy
  · exact tabN_wk C δ z m' i' en hen

/-! ### Erasure at a `mut` loan's mask

An X run at the mask `{(ℓ, mloan κ)}`, entered with `[κ]_1` for a `κ` the main frame carries
nowhere, and ending with no borrow at `ℓ` in its end, is a main run. The garbage holds no borrow
at `ℓ` (`EndOKX`'s `NoBorrowAt`), so the end's composite holds none, and `↭` at `ℓ`, between two
resources with no borrow there, holds unmasked. -/

/-- **A lifetime a lowered resource carries nowhere**: its flattening's `imm` cells are finitely
many, each lifetime set bounded by its meet. -/
theorem exists_not_carried {ρ : WRes} {μ : BoCa.BoLo.Heap} (hl : ResU.Lower ρ μ)
    (hfd : FinDom μ) : ∃ κ : Life, ¬ Carries ρ κ := by
  classical
  obtain ⟨τ, hτ, hval⟩ := hl
  obtain ⟨d, hd⟩ := hfd
  let b : Loc → ℕ := fun l => match τ.get l with
    | some (.imm i) => OrderDual.ofDual i.ls.meet
    | _ => 0
  refine ⟨OrderDual.toDual ((d.map b).sum + 1), ?_⟩
  rintro ⟨l, s, v, χ, hh, ⟨σ, hσ, hg⟩, hm⟩
  obtain rfl := ResU.Flat.functional hσ hτ
  have hld : l ∈ d := hd l (by rw [hval l, hg]; simp)
  have hbl : b l = OrderDual.ofDual s.meet := by simp [b, hg, CellU.immOf]
  have h₁ : b l ≤ (d.map b).sum := List.le_sum_of_mem (List.mem_map_of_mem hld)
  have h₂ := s.meet_least _ hm
  change OrderDual.ofDual (OrderDual.toDual ((d.map b).sum + 1)) ≤ OrderDual.ofDual s.meet at h₂
  simp only [OrderDual.ofDual_toDual] at h₂
  omega

theorem Mask.locs_mloan (l : Loc) (κ : Life) : ({(l, Auth.mloan κ)} : Mask).locs = {l} := by
  ext m; simp [Mask.locs]

theorem Mask.lendLocs_mloan (l : Loc) (κ : Life) :
    ({(l, Auth.mloan κ)} : Mask).lendLocs = ∅ := by
  ext m; simp [Mask.lendLocs]

theorem Mask.mloanLocs_mloan (l : Loc) (κ : Life) :
    ({(l, Auth.mloan κ)} : Mask).mloanLocs = {l} := by
  ext m; simp [Mask.mloanLocs]

/-- What a `mut` loan's run owes at its exit: its mask, no borrow at `ℓ`, and the main post. -/
def exitPostX (M : Mask) (l : Loc) (Q : PostG) : PostGX :=
  fun M' _ k ls t x => M' = M ∧ NoBorrowAt {l} x.1 ∧ Q k ls t x.1

/-- **Erasure at a `mut` loan's mask**: an X run at `{(ℓ, mloan κ)}` from `(ρ, [κ]_1)`, for every
`κ`, that ends at its mask with no borrow at `ℓ`, is a main run from `ρ`, when `ρ` holds no borrow
at `ℓ`. -/
theorem rwpG_of_rwpGX_mloan {Φ : LocFam} {l : Loc} {Q : PostG} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes} (hρ : NoBorrowAt {l} ρ)
    (h : ∀ κ, rwpGX (ℍ := ℍ) Φ {(l, Auth.mloan κ)} (exitPostX {(l, Auth.mloan κ)} l Q) n ls e
      (ρ, GRes.life κ)) :
    rwpG (ℍ := ℍ) Φ Q n ls e ρ := by
  intro ρf fρ ps μ hf hc hT htg _himm hl hfd j μ' e' hj hrun hfin
  obtain ⟨κ, hκ⟩ := exists_not_carried hl hfd
  have hκf : ¬ Carries ρf κ := fun h' => hκ (carries_comp_left hc (hash_valid_comp hf hc) h')
  have hv0 : ((0 : GRes) + GRes.life κ).Valid := by
    rw [GRes.zero_add]; simpa using GRes.valid_add_life GRes.valid_zero (α := κ) rfl
  have hwf : WFC ((0 : GRes) + GRes.life κ).counted (ρf, 0) := by
    intro α hα hcα
    have hακ : α = κ := by
      by_contra hne
      simp [GRes.counted, hne] at hα
    exact absurd (hακ ▸ hcα) hκf
  have hwx : WFC ((0 : GRes) + GRes.life κ).counted (ρ, GRes.life κ) := by
    intro α hα _
    simpa [GRes.counted] using hα
  have hsh : MaskShallow ({(l, Auth.mloan κ)} : Mask).locs ρ := by
    rw [Mask.locs_mloan]
    intro m hm s v χ hh hf'
    have h' := hρ m hm _ hf'
    rw [CellU.kind_immOf] at h'; cases h'
  have hau : MaskAuth {(l, Auth.mloan κ)} (GRes.life κ) := by
    intro m a ha
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.mp ha)
    show (GRes.life κ).tok κ = 1
    simp
  have hoff : MaskOff {(l, Auth.mloan κ)} ρf := by
    intro m hm; rw [Mask.lendLocs_mloan] at hm; exact absurd hm (Set.notMem_empty m)
  obtain ⟨M', ρ', ρp, fρ', fρ'p, π, g', gp, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, hU, hNo, hT', htg',
    hps, hls, -, -, -, -, -, -, -, -, -, -, hNB, hM', hnb', hQ⟩ :=
    h κ (ρf, 0) fρ ps μ hf hc hv0 hwf hwx hsh hau hoff hT htg hl hfd j μ' e' hj hrun hfin
  subst M'
  rw [Mask.mloanLocs_mloan] at hNB
  have hπ : NoBorrowAt {l} π := noBorrowAt_comp h₆ hnb' hNB
  have hUl : ∀ m, m ≠ l → m ∉ (({(l, Auth.mloan κ)} : Mask) ∪ {(l, Auth.mloan κ)}).locs := by
    intro m hm; rw [Set.union_self, Mask.locs_mloan]; exact hm
  have hnl : ∀ p : Loc, p ∉ (({(l, Auth.mloan κ)} : Mask) ∪ {(l, Auth.mloan κ)}).lendLocs := by
    intro p; rw [Set.union_self, Mask.lendLocs_mloan]; exact Set.notMem_empty p
  refine ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₄, h₅, h₆,
    ⟨⟨fun m s v χ hh => ?_, fun m ψ hψ hk => ?_, fun m ψ' hψ hk => ?_⟩, hU.2⟩, hNo, hT', htg',
    fun p => hps p (hnl _), fun y => hls y (hnl _), hQ⟩
  · by_cases hm : m = l
    · subst hm
      constructor <;> intro hf'
      · have h' := hρ m rfl _ hf'; rw [CellU.kind_immOf] at h'; cases h'
      · have h' := hπ m rfl _ hf'; rw [CellU.kind_immOf] at h'; cases h'
    · exact hU.1.1 m (hUl m hm) s v χ hh
  · by_cases hm : m = l
    · subst hm; have h' := hρ m rfl ψ hψ; rw [hk] at h'; cases h'
    · exact hU.1.2.1 m (hUl m hm) ψ hψ hk
  · by_cases hm : m = l
    · subst hm; have h' := hπ m rfl ψ' hψ; rw [hk] at h'; cases h'
    · exact hU.1.2.2 m (hUl m hm) ψ' hψ hk

#print axioms exists_not_carried
#print axioms rwpG_of_rwpGX_mloan

#print axioms rwpGX_of_rwpG
#print axioms erwpKX_of_erwpK
#print axioms erwpKX_of_cN_ret
#print axioms erwpKX_of_cN_eff

end BoCa.Fig16.LogRel.Core.Chain.SI

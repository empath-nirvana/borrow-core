import Nominal.Records
import Nominal.Facts

/-!
# Nominal — Core's clauses with records, `wp` a parameter

`Core/Relation.lean`'s `vCE none` and `cC` at the fragment, with Core's record layer
(`Records.lean`): the Kripke quantifier over `Ext` at `U`, the list `ls₀` of the records strictly
longer-lived than a lent cell at `Mut` and `Imm`, coherence `CohE` at `Imm`. The `wp` at `F` is a
parameter `W : WpOpN L`, as Core's `WpOp`; the printed `wp` threading the list unchanged is one
(`wpLift`). Core's own, `wpTS` over the typed world, is not ported.

Changes from Core's clauses beyond `Relation.lean`'s: `ls₀ = {x ∈ ls ∣ x.2 ⊐ b}` at a `mut` cell
at `b`, as Core; at an `imm` cell `ls₀ = {x ∈ ls ∣ x.2 ⊐ ⊓β̄}` is read "`x.2` strictly outlives some
member of `β̄`" (on a chain `x.2 ⊐ min β̄`).

**`vR_map`, `cR_map`: for every order automorphism `π` under which `W` is carried (`WpEquiv`),
`𝒱⟦A⟧(π·ls)(π·δ)(v)(π·ρ) ↔ 𝒱⟦A⟧(ls)δ(v)(ρ)`**, by one induction on types; the record layer moves
with `π` (`extN_act_iff`, `cohEN_act_iff`). `wpLift_equiv`: the printed `wp` is carried by every
`π`. `reopenR`: the corollary of `Package.lean` at these clauses.
-/

noncomputable section
open Classical

namespace Nominal
open BoCa
open BoCa.Fig16 (PMap Kind)
open BoCa.Fig16.LogRel.Core (VTy CTy forceE)
open BoCa.Lifetime (LifeVar LifeCtx)

set_option linter.unusedSectionVars false

variable {L : Type} [PartialOrder L] [OrderTop L] [WellFoundedGT L]

/-- A `wp` over tagged record lists (Core's `WpOp`). -/
abbrev WpOpN (L : Type) [PartialOrder L] [WellFoundedGT L] : Type :=
  List (SRecN L) → Expr → (List (SRecN L) → Val → WPropN L) → WPropN L

/-- `ℓ ↦ M_α 𝒱⟦S⟧(ls|⊐b)δ` (Core's `ptoMutS`). -/
def ptoMutR (l : Loc) (α : L) (ls : List (SRecN L)) (P : List (SRecN L) → Val → WPropN L) :
    WPropN L := fun ρ =>
  ∃ (b : L) (u : Val) (σ : ResU L) (h : σ.InStratum {b}) (ls₀ : List (SRecN L))
    (hw : P ls₀ u σ),
    α ≤ b ∧ (∀ x, x ∈ ls₀ ↔ (x ∈ ls ∧ b < x.2)) ∧
    (∀ ls' u' σ', P ls' u' σ' → σ'.InStratum {b}) ∧
    ρ = ResU.single l (CellU.mutOf b u σ h (P ls₀) hw)

/-- `ℓ ↦ I_α 𝒱⟦S⟧(ls|⊐⊓β̄)δ` (Core's `ptoImmS`). -/
def ptoImmR (l : Loc) (α : L) (ls : List (SRecN L)) (P : List (SRecN L) → Val → WPropN L) :
    WPropN L := fun ρ =>
  ∃ (s : Finset L) (hs : s.Nonempty) (u : Val) (σ : ResU L) (h : σ.InStratum s)
    (ls₀ : List (SRecN L)),
    ρ = ResU.single l (CellU.immOf s hs u σ h) ∧ P ls₀ u σ ∧ (∀ m ∈ s, α ≤ m) ∧
    ∀ x, x ∈ ls₀ ↔ (x ∈ ls ∧ ∃ m ∈ s, m < x.2)

mutual
/-- `𝒱⟦A⟧(ls)δ(v)`, Core's clauses at the fragment; `b = false` is the observable view. -/
def vR (W : WpOpN L) : Bool → VTy → List (SRecN L) → LSubN L → Val → WPropN L
  | _, .unit, _, _, v => pureN (v = .unit)
  | b, .tensor A B, ls, δ, v =>
      exN fun v₁ => exN fun v₂ => sepN (pureN (v = .pair v₁ v₂))
        (sepN (vR W b A ls δ v₁) (vR W b B ls δ v₂))
  | true, .thunk C, ls, δ, v => fun ρ =>
      ∀ ls', ExtN ls ls' ρ → cR W C ls' δ (forceE C (.val v)) ρ
  | false, .thunk _, _, _, _ => fun _ => True
  | b, .ref A, ls, δ, v =>
      exN fun ℓ => exN fun v' =>
        sepN (pureN (v = .loc ℓ)) (sepN (ptoOwnN ℓ v') (vR W b A ls δ v'))
  | b, .box a A, ls, δ, v => atLifeN δ a fun α => boxE α (vR W b A ls δ v)
  | _, .imm a A, ls, δ, v =>
      atLifeN δ a fun α => exN fun ℓ =>
        sepN (pureN (v = .loc ℓ ∧ CohEN (rsOfN ls) ℓ A δ))
          (ptoImmR ℓ α ls (fun ls₀ => vR W false A ls₀ δ))
  | _, .mut a A, ls, δ, v =>
      atLifeN δ a fun α => exN fun ℓ =>
        sepN (pureN (v = .loc ℓ)) (ptoMutR ℓ α ls (fun ls₀ => vR W true A ls₀ δ))
  | _, .zero, _, _, _ | _, .sum _ _, _, _, _ | _, .bang _, _, _, _ | _, .unk, _, _, _
  | _, .tvar _, _, _, _ | _, .mu _, _, _, _ | _, .int _, _, _, _ | _, .fam _, _, _, _
  | _, .opq _, _, _, _ => fun _ => False

/-- `𝒞⟦C⟧(ls)δ(e)`. -/
def cR (W : WpOpN L) : CTy → List (SRecN L) → LSubN L → Expr → WPropN L
  | .ret A, ls, δ, e => W ls e (fun ls'' => vR W true A ls'' δ)
  | .arr A C, ls, δ, e => fun ρ =>
      ∀ v, wandN (vR W true A ls δ v) (cR W C ls δ (.app e (.val v))) ρ
  | .top, _, _, _ => fun _ => True
  | .all x c C, ls, δ, e => fun ρ =>
      ∀ α : L, wandN (pureN (LtLifeN δ c α)) (cR W C ls (δ.extend x α) (.app e (.val .unit))) ρ
  | .amp _ _, _, _, _ | .nu _, _, _, _ | .eff _ _ _ _ _ _ _, _, _, _ => fun _ => False
end

/-! ### Equivariance -/

/-- `W` is carried by `π`: if `Q′` at `π·ls`, `π·σ` is `Q` at `ls`, `σ`, then `W` at `π·ls`, `π·ρ`
with `Q′` is `W` at `ls`, `ρ` with `Q`. -/
def WpEquiv (π : L ≃o L) (W : WpOpN L) : Prop :=
  ∀ (ls : List (SRecN L)) (e : Expr) (Q Q' : List (SRecN L) → Val → WPropN L),
    (∀ ls'' v σ, Q' (actL π ls'') v (relRU π σ) ↔ Q ls'' v σ) →
    ∀ ρ, W (actL π ls) e Q' (relRU π ρ) ↔ W ls e Q ρ

theorem CellU.mutOf_congr {b : L} {u : Val} {σ : ResU L} {h : σ.InStratum {b}}
    {P P' : Val → ResU L → Prop} (e : P = P') (hw : P u σ) (hw' : P' u σ) :
    CellU.mutOf b u σ h P hw = CellU.mutOf b u σ h P' hw' := by
  subst e; rfl

/-- The `Mut` clause moves with `π`. -/
theorem ptoMutR_act (π : L ≃o L) (l : Loc) (α : L) {ls : List (SRecN L)}
    {P P' : List (SRecN L) → Val → WPropN L}
    (hP : ∀ ls'' u σ, P' (actL π ls'') u (relRU π σ) ↔ P ls'' u σ) {ρ : ResU L}
    (h : ptoMutR l α ls P ρ) : ptoMutR l (π α) (actL π ls) P' (relRU π ρ) := by
  obtain ⟨b, u, σ, hσ, ls₀, hw, hαb, hls₀, hstr, rfl⟩ := h
  have himg : img π (P ls₀) = P' (actL π ls₀) := img_eq_of π fun u σ => hP ls₀ u σ
  refine ⟨π b, u, relRU π σ, (inStratum_relRU_singleton π b σ).mpr hσ, actL π ls₀,
    (hP ls₀ u σ).mpr hw, π.le_iff_le.mpr hαb, ?_, ?_, ?_⟩
  · intro x'
    obtain ⟨x, rfl⟩ := SRecN.act_surjective π x'
    rw [mem_actL, mem_actL, hls₀]
    exact and_congr_right fun _ => π.lt_iff_lt.symm
  · intro ls' u' σ' h'
    obtain ⟨ls'', rfl⟩ := actL_surjective π ls'
    obtain ⟨σ'', rfl⟩ := relRU_surjective π σ'
    exact (inStratum_relRU_singleton π b σ'').mpr (hstr ls'' u' σ'' ((hP ls'' u' σ'').mp h'))
  · rw [relRU_single, relU_mutOf]
    congr 1
    exact CellU.mutOf_congr himg _ _

theorem ptoMutR_act_iff (π : L ≃o L) (l : Loc) (α : L) {ls : List (SRecN L)}
    {P P' : List (SRecN L) → Val → WPropN L}
    (hP : ∀ ls'' u σ, P' (actL π ls'') u (relRU π σ) ↔ P ls'' u σ) (ρ : ResU L) :
    ptoMutR l (π α) (actL π ls) P' (relRU π ρ) ↔ ptoMutR l α ls P ρ := by
  refine ⟨fun h => ?_, ptoMutR_act π l α hP⟩
  have hP' : ∀ ls'' u σ, P (actL π.symm ls'') u (relRU π.symm σ) ↔ P' ls'' u σ := by
    intro ls'' u σ
    rw [← hP, actL_actL_symm, relRU_relRU_symm]
  have := ptoMutR_act π.symm l (π α) hP' h
  rwa [OrderIso.symm_apply_apply, actL_symm_actL, relRU_symm_relRU] at this

/-- The `Imm` clause moves with `π`. -/
theorem ptoImmR_act (π : L ≃o L) (l : Loc) (α : L) {ls : List (SRecN L)}
    {P P' : List (SRecN L) → Val → WPropN L}
    (hP : ∀ ls'' u σ, P' (actL π ls'') u (relRU π σ) ↔ P ls'' u σ) {ρ : ResU L}
    (h : ptoImmR l α ls P ρ) : ptoImmR l (π α) (actL π ls) P' (relRU π ρ) := by
  obtain ⟨s, hs, u, σ, hσ, ls₀, rfl, hpay, hα, hls₀⟩ := h
  refine ⟨mapS π s, mapS_nonempty.mpr hs, u, relRU π σ, (inStratum_relRU π s σ).mpr hσ,
    actL π ls₀, by rw [relRU_single, relU_immOf], (hP ls₀ u σ).mpr hpay, ?_, ?_⟩
  · intro m' hm'
    obtain ⟨m, hm, rfl⟩ := mem_mapS.mp hm'
    exact π.le_iff_le.mpr (hα m hm)
  · intro x'
    obtain ⟨x, rfl⟩ := SRecN.act_surjective π x'
    rw [mem_actL, mem_actL, hls₀]
    refine and_congr_right fun _ => ?_
    constructor
    · rintro ⟨m, hm, hlt⟩
      exact ⟨π m, mem_mapS_apply.mpr hm, π.lt_iff_lt.mpr hlt⟩
    · rintro ⟨m', hm', hlt⟩
      obtain ⟨m, hm, rfl⟩ := mem_mapS.mp hm'
      exact ⟨m, hm, π.lt_iff_lt.mp hlt⟩

theorem ptoImmR_act_iff (π : L ≃o L) (l : Loc) (α : L) {ls : List (SRecN L)}
    {P P' : List (SRecN L) → Val → WPropN L}
    (hP : ∀ ls'' u σ, P' (actL π ls'') u (relRU π σ) ↔ P ls'' u σ) (ρ : ResU L) :
    ptoImmR l (π α) (actL π ls) P' (relRU π ρ) ↔ ptoImmR l α ls P ρ := by
  refine ⟨fun h => ?_, ptoImmR_act π l α hP⟩
  have hP' : ∀ ls'' u σ, P (actL π.symm ls'') u (relRU π.symm σ) ↔ P' ls'' u σ := by
    intro ls'' u σ
    rw [← hP, actL_actL_symm, relRU_relRU_symm]
  have := ptoImmR_act π.symm l (π α) hP' h
  rwa [OrderIso.symm_apply_apply, actL_symm_actL, relRU_symm_relRU] at this

theorem rsOfN_actL_eq (π : L ≃o L) (ls : List (SRecN L)) :
    rsOfN (actL π ls) = (rsOfN ls).map (FrameRecN.act π) := rsOfN_actL π ls

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

mutual
/-- **Core's value relation, with records, is equivariant under every order automorphism that
carries its `wp`.** -/
theorem vR_map (π : L ≃o L) (W : WpOpN L) (hW : WpEquiv π W) :
    ∀ (b : Bool) (A : VTy) (ls : List (SRecN L)) (δ : LSubN L) (v : Val) (ρ : ResU L),
      vR W b A (actL π ls) (δ.map π) v (relRU π ρ) ↔ vR W b A ls δ v ρ
  | _, .unit, _, _, v, ρ => pureN_relRU_iff π (v = .unit) ρ
  | b, .tensor A B, ls, δ, _, ρ =>
      exN_relRU_iff π (fun v₁ σ => exN_relRU_iff π (fun v₂ σ' =>
        sepN_relRU_iff π (pureN_relRU_iff π _)
          (sepN_relRU_iff π (vR_map π W hW b A ls δ v₁) (vR_map π W hW b B ls δ v₂)) σ') σ) ρ
  | true, .thunk C, ls, δ, v, ρ => by
      show (∀ ls', ExtN (actL π ls) ls' (relRU π ρ) →
          cR W C ls' (δ.map π) (forceE C (.val v)) (relRU π ρ)) ↔
        (∀ ls', ExtN ls ls' ρ → cR W C ls' δ (forceE C (.val v)) ρ)
      rw [(actL_surjective π).forall]
      refine forall_congr' fun ls' => ?_
      rw [extN_act_iff, cR_map π W hW C ls' δ _ ρ]
  | false, .thunk _, _, _, _, _ => Iff.rfl
  | b, .ref A, ls, δ, _, ρ =>
      exN_relRU_iff π (fun ℓ σ => exN_relRU_iff π (fun v' σ' =>
        sepN_relRU_iff π (pureN_relRU_iff π _)
          (sepN_relRU_iff π (ptoOwnN_relRU_iff π ℓ v') (vR_map π W hW b A ls δ v')) σ') σ) ρ
  | b, .box a A, ls, δ, v, ρ =>
      atLifeN_map π δ a (fun α σ => boxE_relRU_iff π α (vR_map π W hW b A ls δ v) σ) ρ
  | _, .imm a A, ls, δ, v, ρ =>
      atLifeN_map π δ a (fun α σ => exN_relRU_iff π (fun ℓ σ' =>
        sepN_relRU_iff π (fun τ => by
            rw [pureN_relRU_iff, rsOfN_actL_eq]
            show (τ = PMap.empty ∧ v = .loc ℓ ∧ CohEN _ ℓ A (δ.map π)) ↔
              (τ = PMap.empty ∧ v = .loc ℓ ∧ CohEN _ ℓ A δ)
            rw [cohEN_act_iff])
          (ptoImmR_act_iff π ℓ α (fun ls'' u σ'' => vR_map π W hW false A ls'' δ u σ'')) σ')
        σ) ρ
  | _, .mut a A, ls, δ, v, ρ =>
      atLifeN_map π δ a (fun α σ => exN_relRU_iff π (fun ℓ σ' =>
        sepN_relRU_iff π (pureN_relRU_iff π _)
          (ptoMutR_act_iff π ℓ α (fun ls'' u σ'' => vR_map π W hW true A ls'' δ u σ'')) σ')
        σ) ρ
  | _, .zero, _, _, _, _ | _, .sum _ _, _, _, _, _ | _, .bang _, _, _, _, _
  | _, .unk, _, _, _, _ | _, .tvar _, _, _, _, _ | _, .mu _, _, _, _, _
  | _, .int _, _, _, _, _ | _, .fam _, _, _, _, _ | _, .opq _, _, _, _, _ => Iff.rfl

/-- **Core's computation relation, with records, is equivariant** under every order automorphism
that carries its `wp`. -/
theorem cR_map (π : L ≃o L) (W : WpOpN L) (hW : WpEquiv π W) :
    ∀ (C : CTy) (ls : List (SRecN L)) (δ : LSubN L) (e : Expr) (ρ : ResU L),
      cR W C (actL π ls) (δ.map π) e (relRU π ρ) ↔ cR W C ls δ e ρ
  | .ret A, ls, δ, e, ρ => hW ls e _ _ (fun ls'' v σ => vR_map π W hW true A ls'' δ v σ) ρ
  | .arr A C, ls, δ, e, ρ =>
      forall_congr' fun v =>
        wandN_relRU_iff π (vR_map π W hW true A ls δ v) (cR_map π W hW C ls δ _) ρ
  | .top, _, _, _, _ => Iff.rfl
  | .all x c C, ls, δ, e, ρ => by
      show (∀ α' : L, wandN (pureN (LtLifeN (δ.map π) c α'))
          (cR W C (actL π ls) ((δ.map π).extend x α') (.app e (.val .unit))) (relRU π ρ)) ↔
        (∀ α : L, wandN (pureN (LtLifeN δ c α))
          (cR W C ls (δ.extend x α) (.app e (.val .unit))) ρ)
      rw [π.surjective.forall]
      refine forall_congr' fun α => ?_
      rw [← LSubN.map_extend]
      exact wandN_relRU_iff π (fun σ => by rw [pureN_relRU_iff, ltLifeN_map])
        (cR_map π W hW C ls (δ.extend x α) _) ρ
  | .amp _ _, _, _, _, _ | .nu _, _, _, _, _ | .eff _ _ _ _ _ _ _, _, _, _, _ => Iff.rfl
end

/-! ### The printed `wp` as Core's `WpOp` -/

/-- The printed `wp`, threading the record list unchanged. -/
def wpLift : WpOpN L := fun ls e Q => wpN (ℍ := ℍ) e (Q ls)

/-- **The printed `wp` is carried by every order automorphism.** -/
theorem wpLift_equiv (π : L ≃o L) : WpEquiv π (wpLift (L := L) (ℍ := ℍ)) := by
  intro ls e Q Q' hQ ρ
  exact wpN_relRU_iff π e (fun v σ => hQ ls v σ) ρ

/-- The equivariance at the printed `wp`, every hypothesis discharged. -/
theorem vR_map_wpLift (π : L ≃o L) (b : Bool) (A : VTy) (ls : List (SRecN L)) (δ : LSubN L)
    (v : Val) (ρ : ResU L) :
    vR (wpLift (ℍ := ℍ)) b A (actL π ls) (δ.map π) v (relRU π ρ) ↔
      vR (wpLift (ℍ := ℍ)) b A ls δ v ρ :=
  vR_map π _ (wpLift_equiv π) b A ls δ v ρ

end Nominal

end

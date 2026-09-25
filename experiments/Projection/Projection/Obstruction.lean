import Support.TypedWorld.FrameRules
import Support.TypedWorld.Compatibility

/-!
# Projection — Obstruction

A same-lifetime projection `Imm @a (Ref A ⊗ Ref B) ⊸ Imm @a A` at the typed world
(`ProjSpec`), and its refutation (`no_projection`) at `A = B = 1`: in the callback of `[TR]`
6.64, the projected view is an `imm` cell at the frame's own lifetime on an `own` cell of the
frame record's escrow, and `Tagged` (through `FrameLife`) requires every such view to be
strictly shorter than the frame.
-/

noncomputable section

namespace Projection
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel
open BoCa.Fig16.LogRel.MutImmCell
open BoCa.Fig16.LogRel.Typed
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- A tagged world holds no `imm` view at lifetime `α` of an `own` cell of the escrow of a
record tagged `α`. -/
theorem no_view_at_tag {W : WRes} {ps : List FrameRec} {ls : List SRec}
    (htg : Tagged W ps ls) {r : FrameRec} {α : Life} (hr : (r, α) ∈ ls)
    {m : Loc} {u : Val} (hm : r.R.get m = some (CellU.ownOf u))
    {aW : WRes} (haW : AgW W aW) {ρ : WRes} (hicp : ICpAt aW ρ m)
    {ls₀ : List SRec} {P : List SRec → Val → WProp} (h : ptoImmS m α ls₀ P ρ) : False := by
  obtain ⟨q, -, hqr, hFL⟩ := htg (r, α) hr
  have hLin : LinLoc q m := ⟨r, hqr, CellU.ownOf u, hm, by simp⟩
  obtain ⟨s, u', σ, hσ, ls₁, rfl, -, hαs, -⟩ := h
  obtain ⟨ζ, t, eζ, ht, hmem⟩ :=
    (hicp _ (ResU.single_get_self _ _)).ls (CellU.lsOf_immOf _ _ _ _) s.meet_mem
  have hlt : s.meet ⊏ α := hFL.2 aW haW m hLin ζ t eζ ht s.meet hmem
  exact lt_irrefl _ (lt_of_le_of_lt hαs hlt)

/-- The pair type whose first component is projected: `Ref 1 ⊗ Ref 1`. -/
abbrev T0 : Ty := .tensor (.ref .unit) (.ref .unit)

/-- `u`'s first component is the location `m`. -/
def FstLoc (u : Val) (m : Loc) : Prop := ∃ v₂, u = Val.pair (Val.loc m) v₂

/-- A same-lifetime projection `proj : Imm @a (Ref A ⊗ Ref B) ⊸ Imm @a A` at the typed world:
from a view `ℓ` of the pair, `proj ℓ` returns a view of the first component's contents at the
same lifetime `@aδ`, and the location it returns is the first component of the pair `ℓ`
holds. -/
def ProjSpec (proj : Loc → Expr) (a : Lifetime.Life) (A B : Ty) : Prop :=
  ∀ (ls : List SRec) (δ : LSub) (ℓ : Loc) (ρ : WRes),
    vP (.imm a (.tensor (.ref A) (.ref B))) ls δ (Val.loc ℓ) ρ →
    wpTS ls (proj ℓ) (fun ls' w ρ' => vP (.imm a A) ls' δ w ρ' ∧
      ∃ m, w = Val.loc m ∧ ∀ ψ : CellU Loc Val, ρ.get ℓ = some ψ → FstLoc ψ.erase m) ρ

/-- The payload `Ref 1 ⊗ Ref 1` at either mode: the value is a pair of locations and the
witness owns the first. -/
theorem t0_payload {b : Bool} {ls : List SRec} {δ : LSub} {u : Val} {σ : WRes}
    (h : vX wpTS b T0 ls δ u σ) :
    ∃ m₁ v₂, u = Val.pair (Val.loc m₁) v₂ ∧ σ.get m₁ = some (CellU.ownOf Val.unit) := by
  obtain ⟨v₁, v₂, ρa, ρb, hab, ⟨rfl, huv⟩, ρ₁, ρ₂, h12, h₁, h₂⟩ := h
  subst huv
  cases eq_of_compS_empty_left hab
  obtain ⟨m₁, u₁, ρc, ρd, hcd, ⟨rfl, hv₁⟩, ρe, ρf, hef, rfl, rfl, hu₁⟩ := h₁
  subst hv₁
  cases eq_of_compS_empty_left hcd
  subst hu₁
  refine ⟨m₁, v₂, rfl, ?_⟩
  have e₁ : ρ₁.get m₁ = some (CellU.ownOf Val.unit) :=
    (ResU.CompS.get_left_of_ne_imm hef (ResU.single_get_self _ _) (by simp)).2
  exact (ResU.CompS.get_left_of_ne_imm h12 e₁ (by simp)).2

/-- `𝒱X⟦Ref 1 ⊗ Ref 1⟧` does not depend on the mode or on `δ`. -/
theorem t0_mode {b b' : Bool} {ls : List SRec} {δ δ' : LSub} {u : Val} {σ : WRes}
    (h : vX wpTS b T0 ls δ u σ) : vX wpTS b' T0 ls δ' u σ := h

/-- Inside the callback of `[TR]` 6.64 (`wpTS_I_frameX`) entered from the empty list, a
same-lifetime projection of the borrow the frame hands over has no `wpTS`: its post-world
would hold a view at the frame's own lifetime of a chain position of the frame's record. -/
theorem callback_blocked (proj : Loc → Expr) (x : LifeVar)
    (hspec : ProjSpec proj (.var x) .unit .unit) {δ₀ : LSub} {ℓ : Loc} {α : Life}
    {ls' : List SRec} {ρi : WRes} (hadd : AddAt [] ls' α)
    (hrec : ∃ r ∈ rsOf ls', r.le = ℓ ∧ r.T = T0 ∧ r.δ = δ₀)
    (hcell : ptoImmS ℓ α ls' (fun ls₀ => vX wpTS true T0 ls₀ δ₀) ρi)
    (Q : List SRec → Val → WProp) : wpTS ls' (proj ℓ) Q ρi := by
  intro ρf fρ ps hf hc hT htg
  set δ' : LSub := δ₀.extend x α with hδ'
  obtain ⟨r, hr, hrl, hrT, -⟩ := hrec
  have hcoh : CohE (rsOf ls') ℓ T0 δ' :=
    ⟨T0, δ', ⟨trivial, trivial⟩, Or.inl ⟨r, hr, hrl.symm, hrT.symm, fun y hy => by
      rw [hrT] at hy; simp [LFree] at hy⟩⟩
  have hv : vP (.imm (.var x) T0) ls' δ' (Val.loc ℓ) ρi := by
    refine ⟨α, find?_extend_self δ₀ x α, ℓ, PMap.empty, ρi, compS_empty_left ρi,
      ⟨rfl, rfl, hcoh⟩, ?_⟩
    obtain ⟨s, u, σ, hσ, ls₀, e, hP, hαs, hls₀⟩ := hcell
    exact ⟨s, u, σ, hσ, ls₀, e, t0_mode hP, hαs, hls₀⟩
  obtain ⟨ρ', ρp, fρ', fρ'p, π, w, μ, μ', ps', ls'', h1, h2, h3, h5, h6, h7, h8, h9, hA, hB,
    hT', htg', hps', hls', hvw, m, rfl, hfst⟩ := hspec ls' δ' ℓ ρi hv ρf fρ ps hf hc hT htg
  exfalso
  obtain ⟨s, u, σ, hσ, ls₀, rfl, hP, -, -⟩ := hcell
  obtain ⟨m₁, v₂, rfl, hm₁⟩ := t0_payload hP
  obtain ⟨v₂', hfst'⟩ := hfst _ (ResU.single_get_self _ _)
  have hmm : m = m₁ := by
    rw [CellU.erase_immOf] at hfst'
    have := congrArg Subtype.val hfst'
    simp [Val.pair, Val.loc] at this
    exact this.1.symm
  subst hmm
  -- the record at `ℓ` has the view's witness as its escrow
  obtain ⟨aW, haW⟩ := agW_of_valid (hash_valid_comp hf hc)
  obtain ⟨ψ, eψ, -, -, wψ⟩ := hT.inv.leInvW r hr aW haW
  have hicpℓ : ICpAt aW (ResU.single ℓ (CellU.immOf s (Val.pair (Val.loc m) v₂) σ hσ)) ℓ :=
    icpAt_trans (icpAt_right (ResU.CompS.toCompR hc) ℓ) (icpAt_agW haW ℓ)
  obtain ⟨ζ, eζ, -, -, wζ, -⟩ := hicpℓ _ (ResU.single_get_self _ _) (CellU.kind_immOf _ _ _ _)
  rw [hrl, eζ] at eψ
  cases Option.some.inj eψ
  have hrR : r.R = σ := wψ.symm.trans (wζ.trans (CellU.wit_immOf _ _ _ _))
  -- the record is tagged at the frame's lifetime
  obtain ⟨t, ht⟩ := mem_rsOf.mp hr
  have htα : t = α := hadd.2 _ ht (by simp)
  subst htα
  have hr'' : (r, t) ∈ ls'' := (hls' _).mpr ht
  -- the post-world
  have hvF : ResU.Valid fρ'p := by obtain ⟨σ₁, hσ₁, -⟩ := h7; exact ⟨σ₁, hσ₁⟩
  obtain ⟨aF, haF⟩ := agW_of_valid hvF
  have hicp : ICpAt aF ρ' m :=
    icpAt_trans (icpAt_right (ResU.CompS.toCompR h2) m)
      (icpAt_trans (icpAt_left (ResU.CompS.toCompR h6) m) (icpAt_agW haF m))
  obtain ⟨α', hα', ℓ', ρ₁, ρ₂, h12, ⟨rfl, hwl, -⟩, hpto⟩ := hvw
  cases eq_of_compS_empty_left h12
  rw [Lifetime.Life.interp_var, hδ', find?_extend_self] at hα'
  cases Option.some.inj hα'
  cases (Val.loc_inj.mp hwl)
  exact no_view_at_tag htg' hr'' (hrR ▸ hm₁) haF hicp hpto

/-- A `wpTS` run from a tagged typed world ends in one, the frame absorbing `ρ⁺`. -/
theorem run {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp} {ρ ρf fρ : WRes}
    {ps : List FrameRec} (hw : wpTS ls e Q ρ) (hf : ResU.Hash ρf ρ) (hc : ResU.CompS ρf ρ fρ)
    (hT : TW fρ ps (rsOf ls)) (htg : Tagged fρ ps ls) :
    ∃ (ρ' ρf' fρ' : WRes) (ps' : List FrameRec) (ls' : List SRec) (v : Val),
      Q ls' v ρ' ∧ ResU.Hash ρf' ρ' ∧ ResU.CompS ρf' ρ' fρ' ∧ TW fρ' ps' (rsOf ls') ∧
      Tagged fρ' ps' ls' := by
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', ls', -, h2, -, -, h6, h7, -, -, -, -,
    hT', htg', -, -, hQ⟩ := hw ρf fρ ps hf hc hT htg
  obtain ⟨z, -, hz⟩ := compS_exch h2 h6
  have hv : ResU.Valid fρ'p := by obtain ⟨σ₁, hσ₁, -⟩ := h7; exact ⟨σ₁, hσ₁⟩
  exact ⟨ρ', z, fρ'p, ps', ls', v, hQ, ⟨hz.1, fρ'p, hz, hv⟩, hz, hT', htg'⟩

/-- The post-condition of one allocation at the empty list. -/
def AllocQ (ρ₀ : WRes) (v : Val) : List SRec → Val → WProp := fun ls w ρ =>
  ls = [] ∧ ∃ l, w = Val.loc l ∧ ResU.CompS ρ₀ (ResU.single l (CellU.ownOf v)) ρ

theorem alloc_run (ρ₀ : WRes) (v : Val) :
    wpTS [] (.app (.val (.prim .alloc)) (.val v)) (AllocQ ρ₀ v) ρ₀ :=
  wpTS_alloc [] v _ ρ₀ (fun l ρ₁ ρ₂ h₁ h₂ => by
    subst h₁; exact ⟨rfl, l, rfl, h₂⟩)

theorem vX_ref_unit {b : Bool} {ls : List SRec} {δ : LSub} (l : Loc) :
    vX wpTS b (.ref .unit) ls δ (Val.loc l) (ResU.single l (CellU.ownOf Val.unit)) :=
  ⟨l, Val.unit, PMap.empty, _, compS_empty_left _, ⟨rfl, rfl⟩, _, PMap.empty,
    ResU.comp_empty_right _, rfl, ⟨rfl, rfl⟩⟩

/-- **No same-lifetime projection.**  No expression `proj` meets `ProjSpec` at
`Imm 'x (Ref 1 ⊗ Ref 1) ⊸ Imm 'x 1`.  The configuration is built by the library: three
allocations from the empty typed world, then `[TR]` 6.64 (`wpTS_I_frameX`) borrowing the pair
cell, whose callback runs `proj` on the borrow it is handed. -/
theorem no_projection (proj : Loc → Expr) (x : LifeVar) :
    ¬ ProjSpec proj (.var x) .unit .unit := by
  intro hspec
  obtain ⟨ρ1, f1, W1, ps1, ls1, -, ⟨rfl, l2, -, hc1⟩, hf1, hW1, hT1, htg1⟩ :=
    run (alloc_run PMap.empty Val.unit) hash_empty (ResU.comp_empty_right _) TW.empty
      (fun x hx => by simp at hx)
  cases eq_of_compS_empty_left hc1
  obtain ⟨ρ2, f2, W2, ps2, ls2, -, ⟨rfl, l1, -, hc2⟩, hf2, hW2, hT2, htg2⟩ :=
    run (alloc_run _ Val.unit) hf1 hW1 hT1 htg1
  set v : Val := Val.pair (Val.loc l1) (Val.loc l2) with hvdef
  obtain ⟨ρ3, f3, W3, ps3, ls3, -, ⟨rfl, ℓ, -, hc3⟩, hf3, hW3, hT3, htg3⟩ :=
    run (alloc_run ρ2 v) hf2 hW2 hT2 htg2
  have hadm : AdmWf T0 LSub.empty := fun y hy => by simp [LFree] at hy
  have hvX : vX wpTS true T0 [] LSub.empty v ρ2 :=
    ⟨Val.loc l1, Val.loc l2, PMap.empty, ρ2, compS_empty_left ρ2, ⟨rfl, rfl⟩, _, _,
      ResU.CompS.comm hc2, vX_ref_unit l1, vX_ref_unit l2⟩
  have hpre := wpTS_I_frameX ℓ T0 LSub.empty hadm v (proj ℓ) []
    (fun _ _ _ => False) (fun _ _ _ _ _ h => h) ρ3
    ⟨_, ρ2, ResU.CompS.comm hc3, rfl, ρ2, PMap.empty, ResU.comp_empty_right ρ2, hvX,
      ⊤, fun α _ => ⟨fun ls' hadd hrec ρi BI hcell hBI => by
        cases eq_of_compS_empty_left hBI
        exact callback_blocked proj x hspec hadd hrec hcell _, empty_inStratum α⟩⟩
  obtain ⟨-, -, -, -, -, -, hfalse, -⟩ := run hpre hf3 hW3 hT3 htg3
  exact hfalse

end Projection

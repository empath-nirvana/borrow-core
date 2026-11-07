import Core.Chain.Fam836N
import Core.Slices

/-!
# The `n`-cell Mut Frame and `slice_borrow_mut` at `SemJN₀`  `[spec §9, §23]`

Core's `wpTS_M_frameList` (`Core/SliceFrames.lean`) is one Mut Frame per place of a finite list,
around one expression, by induction on the list; `wpTS_M_frameFam` is its instance at an array's
range. `rwp_M_frameListN₀` is that induction at the chain, over the one-cell frame `rwp_M_frame`:
* frame `j` lends its leaf at a lifetime `αⱼ` fresh for the world the frames before it reached, at
  the key `(ℓⱼ, αⱼ)` (`LocTy.add`), the view moved to `αⱼ` at `ℓⱼ` (`LocTy.view_add`); one key per
  cell;
* `αⱼ` lies below the frame's rest, the payloads' stratum `β` and the result's stratum `β′`, as
  Core's `aF ⊓ β′ ⊓ β`; the frames after it are chosen below it (Core's `aR ⊓ α₁ ⊓ γH`);
* the callback receives every leaf at the innermost lifetime: a leaf lent at `αⱼ` is a value of
  `Mut 'x A` at every `α ⊑ αⱼ` through `Mut`'s slack `@aδ ⊑ b` (`mutLeafN₀`), where Core uses
  `ptoMutS_antitone`;
* a frame's postcondition returns its leaf and moves what the inner frames returned to the world
  without the frame's key (`vN_local₀`), the leaves and the result being in the frame's stratum.

`sliceBorrowM_compatN₀` is Core's `sliceBorrowM_compatX` against it, with `withbor2_compatN₀`'s
steps around the callback.
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

/-- **A `mut` leaf at `α`** at the world `Θ`: `Mut`'s clause read at `α` (Core's `mutLeaf`), the
cell at some `b ⊒ α` holding a member of the payload stored at the world's key `(ℓ, b)`. -/
def mutLeafN₀ (A : VTy) (δ : LSub) (α : Life) (Θ : LocTy) (n : Nat) (m : Loc) : WProp := fun ρ =>
  ∃ b : Life, α ≤ b ∧ mutL b (fun Θ' j u r => vN₀ (ℍ := ℍ) A δ Θ' j u r) Θ n (Val.loc m) ρ ∧
    ∀ (Θ' : LocTy) (j : Nat) (u : Val) (r : WRes), vN₀ (ℍ := ℍ) A δ Θ' j u r → r.InStratum b

/-- A `mut` leaf at `α` is a value of `Mut 'x A` at `δ['x ↦ α]`. -/
theorem vN_mutLeaf₀ {x : LifeVar} {A : VTy} (hx : ¬ VFree x A) {δ : LSub} {α : Life} {Θ : LocTy}
    {n : Nat} {m : Loc} {ρ : WRes} (h : mutLeafN₀ (ℍ := ℍ) A δ α Θ n m ρ) :
    vN₀ (ℍ := ℍ) (.mut (.var x) A) (δ.extend x α) Θ n (Val.loc m) ρ := by
  obtain ⟨b, hab, hm, hu⟩ := h
  have hAδ : vN₀ (ℍ := ℍ) A (δ.extend x α) = vN₀ (ℍ := ℍ) A δ := vN_extend_of_not_free₀ hx δ α
  refine ⟨α, interp_ext_self δ x α, b, hab, ?_, fun Θ' j u r h => hu Θ' j u r (hAδ ▸ h)⟩
  rw [hAδ]; exact hm

/-- An owned leaf lies in every stratum below its payload's. -/
theorem ownLeafN_inStratum₀ {A : VTy} {δ : LSub} {β α : Life} (hαβ : α ≤ β)
    (hunif : ∀ Θ j u r, vN₀ (ℍ := ℍ) A δ Θ j u r → r.InStratum β) {Θ : LocTy} {n : Nat}
    {m : Loc} {ρ : WRes} (h : vN₀ (ℍ := ℍ) (.ref A) δ Θ n (Val.loc m) ρ) : ρ.InStratum α := by
  obtain ⟨l, u, σ, -, hc, hu⟩ := h
  exact inStratum_compS hc (ResU.inStratum_single_own α l u) ((hunif _ _ _ _ hu).mono hαβ)

/-- **One Mut Frame per place, around one expression** (Core's `wpTS_M_frameList`), at the chain:
the list induction over `rwp_M_frame`, each frame its own key in the world. `Ψ` is the
callback's postcondition at the world it ends at: in the stratum `β′`, and stable from a world
with one more key to the world without it at a resource in the key's stratum (`vN_local₀`). -/
theorem rwp_M_frameListN₀ {A : VTy} {δ : LSub} {β β' : Life}
    (hunif : ∀ Θ j u r, vN₀ (ℍ := ℍ) A δ Θ j u r → r.InStratum β)
    (Ψ : LocTy → PostN) (hΨs : ∀ Θ k ls v ρ, Ψ Θ k ls v ρ → ρ.InStratum β')
    (hΨl : ∀ (Θ : LocTy) (l : Loc) (α : Life) (F : Nat → Val → SPropS Loc Val α) k ls v ρ,
      ρ.InStratum α → Ψ (Θ.add l α F) k ls v ρ → Ψ Θ k ls v ρ)
    (e : Expr) (ls : List SRec) :
    ∀ (I : List Loc) (Θ : LocTy) (c : Loc → Option Life) (n : Nat) (ρo ρH ρ : WRes) (γ : Life),
      Θ.OK → ConsistentX c ρ → ResU.CompS ρo ρH ρ →
      sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ n (Val.loc m)) I ρo →
      (∀ α, α < γ → ρH.InStratum α ∧ ∀ (Θ' : LocTy) (c' : Loc → Option Life), Θ.ExtA Θ' →
        Θ'.OK → ∀ ρm ρ', sepList (mutLeafN₀ (ℍ := ℍ) A δ α Θ' n) I ρm → ResU.CompS ρH ρm ρ' →
          ConsistentX c' ρ' → rwp (ℍ := ℍ) (Θ'.view c') (Ψ Θ') n ls e ρ') →
      rwp (ℍ := ℍ) (Θ.view c) (fun k ls' v ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧
        sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ ∧ Ψ Θ k ls' v ρ₂)
        n ls e ρ
  | [], Θ, c, n, ρo, ρH, ρ, γ, hΘ, hc, hcρ, ho, hH => by
      obtain ⟨rfl, -⟩ := ho
      rw [eq_of_compS_empty_left hcρ] at hc ⊢
      have h := (hH (↓γ) (Life.down_sqsubset γ)).2 Θ c (LocTy.extA_refl Θ) hΘ PMap.empty ρH
        ⟨rfl, trivial⟩ (ResU.comp_empty_right ρH) hc
      exact rwp_mono (fun k ls' v σ h' =>
        ⟨PMap.empty, σ, compS_empty_left σ, ⟨rfl, trivial⟩, h'⟩) h
  | ℓ :: I, Θ, c, n, ρo, ρH, ρ, γ, hΘ, hc, hcρ, ho, hH => by
      obtain ⟨ρ0, ρr, hc0, hleaf, hrest⟩ := ho
      obtain ⟨l, u, σ, hl, hcl, hu⟩ := hleaf
      obtain rfl : ℓ = l := loc_inj hl
      -- `ρ = ρ0 ● F`, `F = ρr ● ρH`
      obtain ⟨F, hF, hρ⟩ := compS_reassoc hc0 hcρ
      refine rwp_of_erwp_empty (erwp_of_valid fun hv => erwp_of_rwp ?_)
      have hvρ0 : ResU.Valid ρ0 := (ResU.Valid.split hρ hv).1
      have hko : (CellU.ownOf (Loc := Loc) u).kind ≠ Kind.imm := by simp
      have hown : ρ0.get ℓ = some (CellU.ownOf u) :=
        (ResU.CompS.get_left_of_ne_imm hcl (ResU.single_get_self _ _) hko).2
      have hcF : ConsistentX c F := consistentX_right hρ hc hv
      have hcσ : ConsistentX c σ := consistentX_right hcl (consistentX_left hρ hc hv) hvρ0
      -- the outer frame's lifetime: fresh, below the frame's rest, `β` and `β′`
      obtain ⟨βF, hβF⟩ := ResU.exists_stratum F
      obtain ⟨α₁, hα₁le, hfr⟩ := LocTy.exists_fresh hΘ.2 (βF ⊓ β ⊓ β')
      have hα₁F : α₁ ≤ βF := hα₁le.trans (inf_le_left.trans inf_le_left)
      have hα₁β : α₁ ≤ β := hα₁le.trans (inf_le_left.trans inf_le_right)
      have hα₁β' : α₁ ≤ β' := hα₁le.trans inf_le_right
      set P : CPredL := fun Θ' j w r => vN₀ (ℍ := ℍ) A δ Θ' j w r with hP
      set Fm : Nat → Val → SPropS Loc Val α₁ := famL α₁ P Θ with hFm
      have hFmD : DownFam α₁ Fm := vN_fam_down₀ A δ α₁ Θ
      have houtP : σ.InStratum α₁ := (hunif Θ n u σ hu).mono hα₁β
      have hwit : Fm n u ⟨σ, houtP⟩ := (vN_above₀ A δ Θ houtP).mpr hu
      set Θ₁ := Θ.add ℓ α₁ Fm with hΘ₁
      set c₁ := setLife c ℓ α₁ with hc₁
      have hOK₁ : Θ₁.OK := by
        obtain ⟨N, hN⟩ := hΘ.2
        exact ⟨LocTy.down_add hΘ.1 ℓ hFmD, ⟨min N (↓α₁), LocTy.fresh_add hN (min_le_left _ _)
          (lt_of_le_of_lt (min_le_right _ _) (Life.down_sqsubset α₁)) ℓ Fm⟩⟩
      have hE₁ : Θ.ExtA Θ₁ := LocTy.extA_add hfr ℓ Fm
      have hview : Θ₁.view c₁ = (Θ.view c).set ℓ α₁ Fm := LocTy.view_add Θ c ℓ α₁ Fm
      have hcF₁ : ConsistentX c₁ F := consistentX_setLife hcF (exS_none_of_part hρ hv hown hko) α₁
      have hcσ₁ : ConsistentX c₁ σ :=
        consistentX_setLife hcσ (exS_none_of_part hcl hvρ0 (ResU.single_get_self _ _) hko) α₁
      have hΦ : (Θ.view c).Down := LocTy.view_down hΘ.1 c
      refine rwp_M_frame hΦ hFmD le_rfl houtP (hβF.mono hα₁F) hwit hcl hρ (fun BM hBM => ?_)
      rw [← hview]
      -- `BM = ρr ● R`, `R = ρH ● cell`
      obtain ⟨R, hR, hBMR⟩ := compS_reassoc hF hBM
      have hcBM : ConsistentX c₁ BM := consistentX_compS hBM hcF₁
        (consistentX_single_mut hcσ₁ (by simp [hc₁, setLife]))
      obtain ⟨βR, hβR⟩ := ResU.exists_stratum R
      have hrest₁ : sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ₁ n (Val.loc m)) I ρr :=
        sepList_mono' (fun m τ h => vN_extA₀ (.ref A) δ hE₁ n _ τ h) hrest
      refine rwp_mono (fun k ls' v ρ' h => ?_)
        (rwp_M_frameListN₀ hunif Ψ hΨs hΨl e ls I Θ₁ c₁ n ρr R BM (βR ⊓ α₁ ⊓ γ) hOK₁ hcBM hBMR
          hrest₁ (fun α₂ hα₂ => ⟨hβR.mono (le_of_lt (lt_of_lt_of_le hα₂
            (inf_le_left.trans inf_le_left))), ?_⟩))
      · -- the outer frame's postcondition from the inner ones'
        obtain ⟨ρ₁, ρ₂, hc12, ho1, hψ⟩ := h
        have hs1 : ρ₁.InStratum α₁ := sepList_closed (ResU.inStratum_empty α₁)
          (fun _ _ _ hc a b => inStratum_compS hc a b)
          (fun m τ hm => ownLeafN_inStratum₀ hα₁β hunif hm) ho1
        have hs2 : ρ₂.InStratum α₁ := (hΨs _ _ _ _ _ hψ).mono hα₁β'
        refine ⟨inStratum_compS hc12 hs1 hs2, fun w Y hY σ' ⟨hσ', hFσ⟩ Z hZ => ?_⟩
        have ho1' : sepList (fun m => vN₀ (ℍ := ℍ) (.ref A) δ Θ k (Val.loc m)) I ρ₁ :=
          sepList_mono_down (R := fun τ => τ.InStratum α₁)
            (fun _ _ _ hc h => ⟨ResU.CompS.inStratum_left hc h,
              ResU.CompS.inStratum_left (ResU.CompS.comm hc) h⟩)
            (fun m τ hτ hm => vN_local₀ (.ref A) δ Θ ℓ α₁ Fm k _ τ hτ hm) hs1 ho1
        have hψ' := hΨl Θ ℓ α₁ Fm k ls' v ρ₂ hs2 hψ
        have hwA : vN₀ (ℍ := ℍ) A δ Θ k w σ' := (vN_above₀ A δ Θ hσ').mp hFσ
        obtain ⟨cp, hcp, hZ'⟩ := compS_reassoc hY hZ
        obtain ⟨oc, hoc, hZ''⟩ := compS_exch hc12 hZ'
        exact ⟨oc, ρ₂, hZ'', ⟨cp, ρ₁, ResU.CompS.comm hoc, ⟨ℓ, w, σ', rfl, hcp, hwA⟩, ho1'⟩, hψ'⟩
      · -- the inner frames' callback: the outer leaf, at `α₂ ⊑ α₁`, heads the family
        intro Θ' c' hE hOK' ρm₂ ρ' hm₂ hcomp hc'
        have hα₂γ : α₂ < γ := lt_of_lt_of_le hα₂ inf_le_right
        have hα₂α₁ : α₂ ≤ α₁ := le_of_lt (lt_of_lt_of_le hα₂ (inf_le_left.trans inf_le_right))
        obtain ⟨X, hX, hρ'X⟩ := compS_reassoc hR hcomp
        have hlead : mutLeafN₀ (ℍ := ℍ) A δ α₂ Θ' n ℓ
            (ResU.single ℓ (CellU.mutOf α₁ u σ houtP (Fm n) hwit)) :=
          ⟨α₁, hα₂α₁, mutL_extR (hE.extR _) (lend_mutL Θ ℓ α₁ P le_rfl houtP hwit),
            fun Θ'' j w r h => (hunif Θ'' j w r h).mono hα₁β⟩
        exact (hH α₂ hα₂γ).2 Θ' c' (LocTy.extA_trans hE₁ hE) hOK' X ρ' ⟨_, ρm₂, hX, hlead, hm₂⟩
          hρ'X hc'

/-! ### `slice_borrow_mut` at the pure row -/

/-- The body of `withbor` at the source `a`, after the first β step. -/
def withborAtV (a : Val) : Val :=
  Val.lam (.pair (.val a) (.app (.app BoCa.v0 unit') (.val a)))

/-- **`slice_borrow_mut` is a value of its type** (Core's `sliceBorrowM_compatX`):
`withbor` at `Array A ⊸ (∀'x ⊏ @Δ. [Mut 'x A] ⊸ ['x] B) ⊸ Array A ⊗ B`. The source family at
the callback's world (`vN_extR₀`); the `n` Mut Frames around the callback (`rwp_M_frameListN₀` at
the family's range, `sepRange_eq_sepList`), the payloads' stratum and the result's from the side
conditions by 6.60 at `↓@bδ` (`vN_outlivesLe₀`), the callback's lifetimes below the bound and the
callback's stratum; inside, `withbor2_compatN₀`'s steps: `f ()` framed beside the leaves, the
result applied to the family `[Mut 'x A]` (`vN_mutLeaf₀` at each leaf), the result `['x] B` read at
`δ`. -/
theorem sliceBorrowM_sem₀ {Δ : LifeCtx} {x : LifeVar} {A B : VTy} {δ : LSub} (hδ : Δ.Models δ)
    (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (hA : ¬ VFree x A) (hB : ¬ VFree x B)
    (Θ₀ : LocTy) (n : Nat) :
    vN₀ (ℍ := ℍ) (sliceBorrowMTy x Δ.meetOfDom A B) δ Θ₀ n withborVal PMap.empty := by
  intro Θ₂ _ hΘ₂ c₁ _ ls c₂ k hk u ρv ρu hc hu _
  obtain rfl := eq_of_compS_empty_left hc
  obtain ⟨l, cn, rfl, hn, hs⟩ := hu
  have hΦ₂ : (Θ₂.view c₂).Down := LocTy.view_down hΘ₂.1 c₂
  refine erwp_det hΦ₂ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ₂ k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ (Val.arr l cn)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.arr l cn)
      (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))).1) =
      (withborAtV (Val.arr l cn)).1 := by
    simp [Kont.plug, Expr.subst, withborAtV, BoCa.v0, BoCa.v1, unit', Val.lam,
      Expr.val, Val.unit, shift_arr]
  rw [e₁]
  refine erwp_val (v := withborAtV (Val.arr l cn)) ?_
  intro Θ' hE₃ hΘ' c _ ls' c' k' hk' f ρf ρ'' hc' hf hcon
  obtain ⟨l₁, cn₁, he, hn', hs'⟩ := vN_le₀ hk'
    (vN_extR₀ (.array A) δ k _ ρu hE₃ ⟨l, cn, rfl, hn, hs⟩)
  obtain ⟨rfl, rfl⟩ := Val.arr_inj he
  have hΦ : (Θ'.view c').Down := LocTy.view_down hΘ'.1 c'
  refine erwp_det hΦ (opTableN_down OpTabN.empty_down) (fun k _ v ρ h => vN_down₀ _ δ Θ' k v ρ h)
    (fun μ => step1Only_plug (Head.beta μ _ f) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 f
      (.pair (.val (Val.arr l cn)) (.app (.app BoCa.v0 unit') (.val (Val.arr l cn))))) =
      (Kont.pairR (Val.arr l cn) (Kont.appL Kont.hole (Val.arr l cn))).plug
        (.app (.val f) (.val Val.unit)) := by
    simp [Kont.plug, Expr.subst, BoCa.v0, unit', Expr.val, Val.unit, subst_arr]
  rw [e₂]
  refine erwp_of_valid fun hv'' => ?_
  -- the side conditions: the payloads' and the result's strata (6.60 at `↓@bδ`)
  obtain ⟨a, hdefa, hOa⟩ := hsideA
  obtain ⟨βP, hβP⟩ := hdefa δ hδ
  have hunif : ∀ Θ j w r, vN₀ (ℍ := ℍ) A δ Θ j w r → r.InStratum (↓βP) :=
    vN_outlivesLe₀ hδ hβP (Life.down_sqsubset βP) hOa
  obtain ⟨b, hdefb, hOb⟩ := hsideB
  obtain ⟨βB, hβB⟩ := hdefb δ hδ
  have hBs : ∀ Θ j w r, vN₀ (ℍ := ℍ) B δ Θ j w r → r.InStratum (↓βB) :=
    vN_outlivesLe₀ hδ hβB (Life.down_sqsubset βB) hOb
  obtain ⟨m, hm⟩ : ∃ m, Δ.meetOfDom.interp δ = some m :=
    Lifetime.Life.interp_defined_of_wf hδ (Lifetime.meetOfDomL_wf Δ.entries)
  obtain ⟨βf, hβf⟩ := ResU.exists_stratum ρf
  have hAδ : ∀ α, vN₀ (ℍ := ℍ) A (δ.extend x α) = vN₀ (ℍ := ℍ) A δ :=
    fun α => vN_extend_of_not_free₀ hA δ α
  have hBδ : ∀ α, vN₀ (ℍ := ℍ) B (δ.extend x α) = vN₀ (ℍ := ℍ) B δ :=
    fun α => vN_extend_of_not_free₀ hB δ α
  -- the frames' postcondition: the handle beside a result of `B`
  let Ψ : LocTy → PostN := fun Θ k _ v ρ => ∃ w, v = Val.pair (Val.arr l cn) w ∧
    vN₀ (ℍ := ℍ) B δ Θ k w ρ
  refine erwp_of_rwp (rwp_mono (fun k ls₁ v ρ' h => ?_)
    (rwp_M_frameListN₀ hunif Ψ (fun Θ k _ v ρ ⟨w, _, hw⟩ => hBs Θ k w ρ hw)
      (fun Θ l₀ α F k _ v ρ hρ ⟨w, hvw, hw⟩ => ⟨w, hvw, vN_local₀ B δ Θ l₀ α F k w ρ hρ hw⟩)
      _ ls' (rangeLocs l cn.toNat) Θ' c' k' ρu ρf ρ'' (m ⊓ βf) hΘ' hcon hc'
      (by rw [← sepRange_eq_sepList]; exact hs') (fun α hα => ⟨hβf.mono (le_of_lt
        (lt_of_lt_of_le hα inf_le_right)), ?_⟩)))
  · -- the returned leaves are the array again, beside the callback's result
    obtain ⟨ρ₁, ρ₂, hc12, ho, w, rfl, hw⟩ := h
    exact ⟨Val.arr l cn, w, ρ₁, ρ₂, rfl, hc12,
      ⟨l, cn, rfl, hn', by rw [sepRange_eq_sepList]; exact ho⟩, hw⟩
  -- the callback, at the frames' world and view, from the leaves at `α`
  intro Θ'' c'' hE hOK'' ρm ρ₃ hml hcomp hc''
  refine rwp_of_erwp_empty (erwp_of_valid fun hv₃ => erwp_of_rwp ?_)
  have hLt : LtLife δ Δ.meetOfDom α := ⟨m, hm, lt_of_lt_of_le hα inf_le_left⟩
  have hΦi : (Θ''.view c'').Down := LocTy.view_down hOK''.1 c''
  have hcf : ConsistentX c'' ρf := consistentX_left hcomp hc'' hv₃
  have hcm : ConsistentX c'' ρm := consistentX_right hcomp hc'' hv₃
  have hfam : vN₀ (ℍ := ℍ) (.sliceMut (.var x) A) (δ.extend x α) Θ'' k' (Val.arr l cn) ρm :=
    ⟨l, cn, rfl, hn', by rw [sepRange_eq_sepList]; exact sepList_mono' (fun _ _ h => vN_mutLeaf₀ hA h) hml⟩
  refine rwp_bind hΦi _ ?_
  have hcb := (hf Θ'' (hE.extR ρf) hOK'' c'' hcf ls') α hLt
  have hfr' := rwp_frame (fun _ τ => τ = ρm) (fun _ _ _ _ h => h) hcomp (rwp_of_erwp_empty hcb) rfl
  refine rwp_mono_le (fun j hj ls₂ g τ hg => ?_) (rwp_consistentXV hfr' hc'')
  obtain ⟨⟨τg, τm, hcτ, hgv, rfl⟩, hcτ', hvτ⟩ := hg
  have happ := hgv Θ'' (LocTy.extR_refl _ _) hOK'' c'' (consistentX_left hcτ hcτ' hvτ) ls₂
    c'' j le_rfl (Val.arr l cn) _ τ hcτ (vN_le₀ hj hfam) hcτ'
  show rwp (ℍ := ℍ) _ _ j ls₂ ((Kont.pairR (Val.arr l cn) Kont.hole).plug
    (.app (.val g) (.val (Val.arr l cn)))) τ
  refine rwp_bind hΦi _ ?_
  refine rwp_mono_le (fun j' hj' ls₃ w ρw hw => ?_) (rwp_of_erwp_empty happ)
  refine rwp_val (v := Val.pair (Val.arr l cn) w) ?_
  obtain ⟨β, hβ, hwB, -⟩ := hw
  exact ⟨w, rfl, by rw [← hBδ α]; exact hwB⟩

/-- **`slice_borrow_mut` at `SemJN₀`** (Core's `sliceBorrowM_compatX`). -/
theorem sliceBorrowM_compatN₀ {Δ : LifeCtx} {Γ : Ctx VTy} {A B : VTy} (x : LifeVar)
    (hΓ : Ctx.DeadP Γ) (hsideA : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hsideB : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b B) (hfree₁ : ¬ VFree x A)
    (hfree₂ : ¬ VFree x B) :
    SemJN₀ (ℍ := ℍ) Δ Γ withbor (.val (sliceBorrowMTy x Δ.meetOfDom A B)) := by
  intro δ γ Θ c n ls ρ hδ hΘ hc hlw hg
  obtain rfl := gN_deadP₀ hΓ hg
  show erwp (ℍ := ℍ) (Θ.view c) (opTableN OpTabN.empty) _ n ls (substAll γ withbor) _
  rw [show substAll γ withbor = withbor from psub_closedAt _ γ (by decide) (Nat.zero_le 0)]
  exact erwp_val (v := withborVal) (sliceBorrowM_sem₀ hδ hsideA hsideB hfree₁ hfree₂ Θ n)

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end

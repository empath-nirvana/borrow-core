import Core.Chain.SI.RebAcrossN
import Paper.LiteralReadings.S6_7_WeakestPreconditionRules

/-!
# The re-entry's agreement fails at a resume world `TWN` reaches

`RebReentryAgreeN` (`SI/RebAcrossN.lean`) is what re-entering a folded reborrow with the image
chosen at its first entry needs of the resume world. `not_rebReentryAgreeN` refutes it at a
configuration built from `TWN`'s constructors, every hypothesis discharged:

* `W₀`: three allocations, then `TWN.immFrame` of the cell `2 ↦ own(loc 0)` over the escrow
  `ρ″ = 0 ↦ own(v) ● 1 ↦ own(u)` at the type `ref (thunk ⊤)` (`DeepReborrow.rho2`, `cellB`). This
  is the first entry's world. The continuation's image is `rebA`, `0 ↦ imm({β}, v, 1 ↦ own(u))`;
  it agrees with `ag(W₀)`, where `0` is `own`.
* `W = W₀ ● 0 ↦ imm({β}, v, ∅)`: `TWN.reb` of the same record with the other choice of witness
  (`DeepReborrow.comp`), at the same records and tags. A handler holding an alias of the
  record's cell does this while the continuation is stored, its image folded.
* At `W` the view at `0` has witness `∅` and `rebA`'s has `1 ↦ own(u)`: `EscrowAgree` fails, and
  `W ● rebA` is not defined (`DeepReborrow.noCompat`).

So the route "fold the image at the stop, re-enter the same image at the resume" does not go
through at every frame `rwpG` quantifies over. The literal reading
`deepReborrow_not_rebEscrow` is the same pair of images, against 6.150's `EscrowAgree` input.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.DeepReborrow
open BoCa.Lifetime (LifeVar LSub)

/-- One allocation at a `TWN` world: `resume_frame_short`'s first step. -/
theorem twn_alloc {W : WRes} {ps rs : List FrameRec} {μ : BoCa.BoLo.Heap} {l : Loc}
    (hT : TWN W ps rs) (hL : ResU.Lower W μ) (hμ : μ l = none) (v : Val) :
    ∃ W1, ResU.CompS W (ResU.single l (CellU.ownOf v)) W1 ∧ TWN W1 ps rs ∧
      ResU.Lower W1 (BoCa.BoLo.Heap.upd μ l v) := by
  obtain ⟨τ, hτ, hval⟩ := id hL
  have hWl : W.get l = none := get_eq_none_of_flat hτ ((lower_eq_none_iff hval).mp hμ)
  obtain ⟨W1, hc⟩ := (ResU.compS_defined_iff W (ResU.single l (CellU.ownOf v))).mpr
    (compatS_single_of_get_none hWl)
  obtain ⟨σ', hσ', hH, hLσ'⟩ := hash_compS_own (ρf := PMap.empty) (ResU.comp_empty_left W) hL hμ hc
  obtain rfl : W1 = σ' := ResU.CompS.functional (ResU.comp_empty_left W1) hσ'
  exact ⟨W1, hc, TWN.alloc hT hL hμ hc (hash_valid_comp hH hσ'), hLσ'⟩

/-- `tagged_reb` at `TWN`: `FrameLife` kept by `frameLife_reb_rec` at `RebRecLe`. -/
theorem tagged_rebN {W W' c : WRes} {ps rs : List FrameRec} {ls : List SRec} {r : FrameRec}
    {le : Loc} {s : LSet} {β : Life} {hs : r.R.InStratum s.join}
    (hW₀ : TWN W ps rs) (hr : r ∈ rs) (hle : W.get le = some (CellU.immOf s r.v r.R hs))
    (hreb : ResU.Reb β r.R c) (hβ : RebRecLe W ps r.R β) (hW : ResU.CompS W c W')
    (htag : Tagged W ps ls) : Tagged W' ps ls := by
  have hTI := hW₀.inv
  intro y hy
  obtain ⟨p, hp, hd, hα⟩ := htag y hy
  have hpR : p ∈ rs := (hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hp, DescR.refl p⟩
  refine ⟨p, hp, hd, frameLife_reb_rec hW₀.valid hle hreb hW (fun ζ e => ?_)
    (hβ p hp y.2 hα) hα⟩
  rcases CellU.rep ζ with ⟨u, rfl⟩ | ⟨s₁, v₁, χ₁, h₁, rfl⟩ | ⟨b₁, v₁, χ₁, h₁, P, hw, rfl⟩
  · exact (hTI.2.2.2.1 p hpR r hr u e).elim
  · exact CellU.kind_immOf _ _ _ _
  · exact (hTI.2.2.2.2.2.1.1 p hp (mutAt_of_cell hle (MutAt.top e (by simp)))).elim

/-- The record's type. -/
def cexT : VTy := .ref (.thunk .top)

theorem cex_rho2 (v u : Val) :
    ResU.CompS (ResU.single 0 (CellU.ownOf v)) (ResU.single 1 (CellU.ownOf u)) (rho2 v u) := by
  refine ⟨compatS_single_of_get_none (ResU.single_get_ne _ (by decide)), fun l => ?_⟩
  by_cases e0 : l = 0
  · subst e0
    rw [ResU.single_get_self, ResU.single_get_ne _ (by decide : (0:Nat) ≠ 1), rho2_0]
    exact rfl
  · by_cases e1 : l = 1
    · subst e1
      rw [ResU.single_get_ne _ (by decide : (1:Nat) ≠ 0), ResU.single_get_self, rho2_1]
      exact rfl
    · rw [ResU.single_get_ne _ e0, ResU.single_get_ne _ e1, rho2_ne v u e0 e1]
      exact rfl

theorem cex_shape (δ : LSub) (v u : Val) : vShape cexT δ (.loc 0) (rho2 v u) :=
  ⟨0, v, pure_sep_mk rfl ⟨_, _, cex_rho2 v u, rfl, trivial⟩⟩

theorem cex_imageShape (δ : LSub) (x : LifeVar) (β : Life) (v : Val) (w : WRes)
    (h : w.InStratum (LSet.singleton β).join) :
    vShape (cexT.immReborrow (.var x)) (δ.extend x β) (.loc 0)
      (ResU.single 0 (CellU.immOf (LSet.singleton β) v w h)) := by
  refine ⟨β, ?_, 0, pure_sep_mk rfl ⟨LSet.singleton β, v, w, h, rfl, trivial, le_refl _⟩⟩
  simp [BoCa.Lifetime.Life.interp, find?_extend_self]
  rfl

/-- `ag(2 ↦ imm({α}, w, ρ″))` holds `own(v)` at `0`. -/
theorem cex_ag0 {α : Life} {v u w : Val} {a : WRes} (ha : AgW (ResU.single 2 (cellB α v u w)) a) :
    a.get 0 = some (CellU.ownOf v) := by
  obtain ⟨e, a', p, he, ha', hp, hσ⟩ := AgW.single_imm_inv ha
  obtain rfl : e = rho2 v u := ExR.functional he (exR_rho2 v u)
  obtain rfl : a' = PMap.empty := AgW.functional ha' (agW_rho2 v u)
  have hp0 : p.get 0 = some (CellU.ownOf v) :=
    (ResU.Comp.get_of_right_none hp (PMap.empty_get 0)).trans (rho2_0 v u)
  exact (ResU.Comp.get_of_left_none hσ (ResU.single_get_ne _ (by decide : (0:Nat) ≠ 2))).trans hp0

/-- **The re-entry's agreement is refuted** at a configuration `TWN` reaches. -/
theorem not_rebReentryAgreeN : ¬ RebReentryAgreeN := by
  intro hAgree
  -- values, lifetimes, the record
  set v : Val := 𝓋
  set u : Val := 𝓋
  set w : Val := .loc 0
  set α : Life := ⊤
  set β : Life := ↓α
  have hβα : β ⊏ α := Life.down_sqsubset α
  let δ : LSub := ⟨[]⟩
  let x : LifeVar := 0
  have hR := cex_rho2 v u
  -- three allocations
  obtain ⟨W1, hc1, hT1, hL1⟩ := twn_alloc TWN.empty lower_empty (μ := fun _ => none) (l := 2)
    rfl w
  obtain rfl : W1 = ResU.single 2 (CellU.ownOf w) :=
    ResU.CompS.functional hc1 (ResU.comp_empty_left _)
  obtain ⟨W2, hc2, hT2, hL2⟩ := twn_alloc hT1 hL1 (l := 0) (by simp [BoCa.BoLo.Heap.upd]) v
  obtain ⟨W3, hc3, hT3, -⟩ := twn_alloc hT2 hL2 (l := 1) (by simp [BoCa.BoLo.Heap.upd]) u
  obtain ⟨Y, hY, hX⟩ := (ResU.CompS.assoc _ _ _ W3).mpr ⟨W2, hc2, hc3⟩
  obtain rfl : Y = rho2 v u := ResU.CompS.functional hY hR
  -- the Imm Frame: the record `r`
  set r : FrameRec := ⟨2, w, rho2 v u, cexT, δ⟩ with hrdef
  have hadm : AdmWf cexT δ := fun y hy => by simp [cexT, VFree, CFree] at hy
  have hvW3 := hT3.valid
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hvW3
  obtain ⟨eR, heR, -, -⟩ := frame_ex hX (ResU.comp_empty_right W3) heW
  obtain ⟨ds, hds⟩ := lineage_list (r := r) (cex_shape δ v u) hadm heR
  have hvW₀ : ResU.Valid (ResU.single 2 (cellB α v u w)) :=
    (ResU.Valid.split (bcell_frame_comp α β v u w) (Valid_composite α β v u w)).1
  have hT₀' : TWN (ResU.single 2 (cellB α v u w)) [r] (r :: (ds ++ [])) :=
    TWN.immFrame cexT δ (rho2_stratum v u _) hT3 hadm hX (ResU.comp_empty_right W3)
      (cex_shape δ v u) (ResU.comp_empty_right _) hvW₀ hds
  set ls : List SRec := frameList r ds α [] with hlsdef
  have hT₀ : TWN (ResU.single 2 (cellB α v u w)) [r] (rsOf ls) := by
    rw [hlsdef, rsOf_frameList]; exact hT₀'
  obtain ⟨hFL, -⟩ := frameLife_frame cexT δ hvW3 hX (ResU.comp_empty_right W3)
    (ResU.comp_empty_right _) hT3.inv
  have htg₀ : Tagged (ResU.single 2 (cellB α v u w)) [r] ls := by
    intro y hy
    simp only [hlsdef, frameList, List.mem_cons, List.mem_append, List.mem_map,
      List.not_mem_nil, or_false] at hy
    rcases hy with rfl | ⟨d, hd, rfl⟩
    · exact ⟨r, List.mem_singleton_self _, DescR.refl r, hFL⟩
    · obtain ⟨q, hq, hqd⟩ := (hds d).mp hd
      exact ⟨r, List.mem_singleton_self _, ⟨q, hqd⟩, hFL⟩
  have htags : ∀ y ∈ ls, y.2 ⊐ β := by
    intro y hy
    simp only [hlsdef, frameList, List.mem_cons, List.mem_append, List.mem_map,
      List.not_mem_nil, or_false] at hy
    rcases hy with rfl | ⟨d, -, rfl⟩ <;> exact hβα
  have hr : r ∈ rsOf ls := by rw [hlsdef, rsOf_frameList]; exact List.mem_cons_self
  have hle₀ : (ResU.single 2 (cellB α v u w)).get r.le =
      some (CellU.immOf (LSet.singleton α) r.v r.R (rho2_stratum v u _)) :=
    ResU.single_get_self _ _
  -- the handler's reborrow: the other witness, at the same records and tags
  have hrebF : ResU.Reb β (rho2 v u) (ResU.single 0 (cellF β v)) :=
    reb_pair_at hR (ResU.single_get_self _ _) ⟨_, hR⟩ (single_del_self _ _) _
  have hrebLe := rebRecLe_of_tags hT₀ htg₀ htags (rho2 v u)
  have hT : TWN (comp α β v u w) [r] (rsOf ls) :=
    TWN.reb r x hT₀ hr hle₀ (by simp [hrdef, cexT, VFree, CFree]) hrebF
      (cex_imageShape δ x β v _ _) hrebLe (bcell_frame_comp α β v u w)
      (Valid_composite α β v u w)
  have htg : Tagged (comp α β v u w) [r] ls :=
    tagged_rebN hT₀ hr hle₀ hrebF hrebLe (bcell_frame_comp α β v u w) htg₀
  have hle : (comp α β v u w).get r.le =
      some (CellU.immOf (LSet.singleton α) r.v r.R (rho2_stratum v u _)) := comp_2 α β v u w
  -- the continuation's image, chosen at `W₀`, where it agrees
  have hrebA : ResU.Reb β (rho2 v u) (rebA β v u) :=
    reb_pair_at hR (rho2_0 v u) ⟨_, ResU.comp_empty_right _⟩ (rho2_del_0 v u) _
  have hagree₀ : ∀ a, AgW (ResU.single 2 (cellB α v u w)) a → EscrowAgree (rho2 v u) (rebA β v u) a :=
    fun a ha l v' ψ ψf _ hψ hψf _ hkf => by
      by_cases e0 : l = 0
      · subst e0; rw [cex_ag0 ha] at hψf; cases hψf; exact absurd rfl hkf
      · rw [show (rebA β v u).get l = none from ResU.single_get_ne _ e0] at hψ
        cases hψ
  have hstr₀ : (ResU.single 2 (cellB α v u w)).InStratum β :=
    ResU.inStratum_single 2 hβα
  have h := hAgree _ _ [r] [r] ls ls r (LSet.singleton α) (rho2_stratum v u _) (rebA β v u) β x
    hT₀ htg₀ hstr₀ hr hle₀ hrebA (cex_imageShape δ x β v _ _) hagree₀ hT htg (fun _ => Iff.rfl)
    hle _ (agW_comp α β v u w)
  -- at `W`, the view at `0` has witness `∅`
  have hwit := h 0 v _ _ (rho2_0 v u) (rebA_0 β v u) (sigma_0 α β v u w)
    (by rw [CellU.kind_immOf]; exact fun c => Kind.noConfusion c)
    (by rw [cellF_kind]; exact fun c => Kind.noConfusion c)
  rw [cellF_wit, CellU.wit_immOf] at hwit
  have hg : (PMap.empty : WRes).get 1 = (witU u).get 1 := by rw [hwit]
  rw [PMap.empty_get, show (witU u).get 1 = some (CellU.ownOf u) from
    ResU.single_get_self _ _] at hg
  exact absurd hg (by simp)

end BoCa.Fig16.LogRel.Core.Chain.SI

end

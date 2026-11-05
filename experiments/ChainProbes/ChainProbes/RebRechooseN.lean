import Core.Chain.SI.RebAgreeCex

/-!
# 6.150 across a stop: re-choosing the image at the resume

At a resume the continuation of a reborrow body is re-entered with an image `χ′` of the record's
escrow that agrees with the resume world (`EscrowAgree`, `[TR]` 6.55's input), in place of the
image `χ` chosen at the first entry. The continuation was proved good at `χ`; it is owed at `χ′`.

## The relabelling `relabel_obs` uses keeps witnesses

`relabel_obs` types `relRes R β c` at the reborrow type, and `relCell` changes only a cell's
lifetime set (`relCell_props`: value, witness and kind kept). So every `relRes`-relabelling of `χ`
carries `χ`'s witnesses, and `EscrowAgree` reads only witnesses and kinds
(`escrowAgree_relRes`). The resume world of `not_rebReentryAgreeN` refutes agreement for every one of them:
`not_rebRelabelAgreeN`, from `not_rebReentryAgreeN`.

## The image that agrees changes witnesses

At that resume world an image that agrees exists, of the same escrow at the same `β` and of
the reborrow's shape: the handler's own image, witness `∅` (`cex_rechoose`). It differs from `χ`
in the witness at the root, so it is related to `χ` by `obs_transfer`'s move (both are pieces of the
escrow), not by `relRes`. The continuation's obligation then moves along a change of witness.

## Moving `erwp` along a change of witness

`erwp` at `ρ ● χ′` quantifies over frames compatible with `χ′`; the handler's image is one, and it
is not compatible with `χ` (`DeepReborrow.noCompat`), so the hypothesis at `ρ ● χ` says nothing at
those frames. Moving the obligation needs every typed world at `χ′` carried to a typed world at `χ`
with the witnesses swapped, and back at the end of every run. `TWN` is a reachability inductive; a
transport by induction on its derivations meets `TWN.immFrame`, whose premise
`vShape T δ v R` is read at the record's own type `T`, unrelated to the reborrowed record's type.
`not_immFrameWitSwapN`: at a world `TWN` reaches, a record proper whose escrow is the handler's
image of the reborrowed escrow, typed `imm 'x 1`, has no shape at the other image, whose root
witness is not empty. The per-step transport fails there.

That refutes a proof route, not the invariance: whether the swapped world is reached by another
derivation is not derived, and no obstruction to the invariance itself is verified.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.DeepReborrow
open BoCa.Lifetime (LifeVar LSub)

/-! ### `relRes` keeps witnesses -/

/-- `EscrowAgree` reads an image's cells only through their kind and witness, which `relRes`
keeps. -/
theorem escrowAgree_relRes {R R' χ a : WRes} {β : Life} :
    EscrowAgree R (relRes R' β χ) a ↔ EscrowAgree R χ a := by
  constructor
  · intro h l v ψ ψf hown hψ hψf hk hkf
    have e : (relRes R' β χ).get l = some (relCell R' β l ψ) := by rw [relRes_get, hψ]; rfl
    have := h l v _ ψf hown e hψf (by rw [(relCell_props R' β l ψ).2.2]; exact hk) hkf
    rwa [(relCell_props R' β l ψ).2.1] at this
  · intro h l v ψ' ψf hown hψ' hψf hk hkf
    rw [relRes_get] at hψ'
    obtain ⟨ψ, e, rfl⟩ := Option.map_eq_some_iff.mp hψ'
    rw [(relCell_props R' β l ψ).2.1]
    exact h l v ψ ψf hown e hψf (by rwa [(relCell_props R' β l ψ).2.2] at hk) hkf

/-- **Re-choosing by `relabel_obs`'s relabelling.** At every later typed, tagged world at the same
records that holds the record's cell, some relabelling `relRes R′ β′ χ` of the first entry's image
agrees with the world. -/
def RebRelabelAgreeN : Prop :=
  ∀ (W₀ W : WRes) (ps₀ ps : List FrameRec) (ls ls' : List SRec) (r : FrameRec) (s : LSet)
    (hs : r.R.InStratum s.join) (χ : WRes) (β : Life) (x : LifeVar),
    TWN W₀ ps₀ (rsOf ls) → Tagged W₀ ps₀ ls → W₀.InStratum β → r ∈ rsOf ls →
    W₀.get r.le = some (CellU.immOf s r.v r.R hs) →
    ResU.Reb β r.R χ → vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v χ →
    (∀ a, AgW W₀ a → EscrowAgree r.R χ a) →
    TWN W ps (rsOf ls') → Tagged W ps ls' → (∀ y, y ∈ ls' ↔ y ∈ ls) →
    W.get r.le = some (CellU.immOf s r.v r.R hs) →
    ∃ (R' : WRes) (β' : Life), ∀ a, AgW W a → EscrowAgree r.R (relRes R' β' χ) a

theorem rebReentryAgreeN_of_relabel (h : RebRelabelAgreeN) : RebReentryAgreeN := by
  intro W₀ W ps₀ ps ls ls' r s hs χ β x hT₀ htg₀ hβ hr hle₀ hreb hden hag₀ hT htg hls hle a ha
  obtain ⟨R', β', h'⟩ := h W₀ W ps₀ ps ls ls' r s hs χ β x hT₀ htg₀ hβ hr hle₀ hreb hden hag₀ hT
    htg hls hle
  exact escrowAgree_relRes.mp (h' a ha)

/-- **No `relRes`-relabelling of the first entry's image agrees at `not_rebReentryAgreeN`'s resume
world.** -/
theorem not_rebRelabelAgreeN : ¬ RebRelabelAgreeN :=
  fun h => not_rebReentryAgreeN (rebReentryAgreeN_of_relabel h)

/-! ### The resume world of `not_rebReentryAgreeN` -/

/-- The record of `not_rebReentryAgreeN`'s configuration: the cell `2 ↦ own(loc 0)` over `0 ↦ own(𝓋) ● 1 ↦ own(𝓋)`
at `ref (thunk ⊤)`. -/
def cexRec : FrameRec := ⟨2, .loc 0, rho2 𝓋 𝓋, cexT, ⟨[]⟩⟩

/-- The first entry's lifetime and the reborrow's. -/
abbrev cxα : Life := ⊤
abbrev cxβ : Life := ↓cxα

/-- The resume world `0 ↦ imm({β}, 𝓋, ∅) ● 2 ↦ imm({α}, loc 0, ρ″)`. -/
abbrev cxW : WRes := comp cxα cxβ 𝓋 𝓋 (.loc 0)

/-- `not_rebReentryAgreeN`'s resume world is typed at the record, with `TWN.reb` of the handler's image. -/
theorem cex_resumeWorld :
    ∃ ls : List SRec, TWN cxW [cexRec] (rsOf ls) ∧ Tagged cxW [cexRec] ls ∧
      cexRec ∈ rsOf ls := by
  set v : Val := 𝓋
  set u : Val := 𝓋
  set w : Val := .loc 0
  set α : Life := cxα
  set β : Life := cxβ
  have hβα : β ⊏ α := Life.down_sqsubset α
  let δ : LSub := ⟨[]⟩
  let x : LifeVar := 0
  have hR := cex_rho2 v u
  obtain ⟨W1, hc1, hT1, hL1⟩ := twn_alloc TWN.empty lower_empty (μ := fun _ => none) (l := 2)
    rfl w
  obtain rfl : W1 = ResU.single 2 (CellU.ownOf w) :=
    ResU.CompS.functional hc1 (ResU.comp_empty_left _)
  obtain ⟨W2, hc2, hT2, hL2⟩ := twn_alloc hT1 hL1 (l := 0) (by simp [BoCa.BoLo.Heap.upd]) v
  obtain ⟨W3, hc3, hT3, -⟩ := twn_alloc hT2 hL2 (l := 1) (by simp [BoCa.BoLo.Heap.upd]) u
  obtain ⟨Y, hY, hX⟩ := (ResU.CompS.assoc _ _ _ W3).mpr ⟨W2, hc2, hc3⟩
  obtain rfl : Y = rho2 v u := ResU.CompS.functional hY hR
  have hadm : AdmWf cexT δ := fun y hy => by simp [cexT, VFree, CFree] at hy
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hT3.valid
  obtain ⟨eR, heR, -, -⟩ := frame_ex hX (ResU.comp_empty_right W3) heW
  obtain ⟨ds, hds⟩ := lineage_list (r := cexRec) (cex_shape δ v u) hadm heR
  have hvW₀ : ResU.Valid (ResU.single 2 (cellB α v u w)) :=
    (ResU.Valid.split (bcell_frame_comp α β v u w) (Valid_composite α β v u w)).1
  have hT₀' : TWN (ResU.single 2 (cellB α v u w)) [cexRec] (cexRec :: (ds ++ [])) :=
    TWN.immFrame cexT δ (rho2_stratum v u _) hT3 hadm hX (ResU.comp_empty_right W3)
      (cex_shape δ v u) (ResU.comp_empty_right _) hvW₀ hds
  set ls : List SRec := frameList cexRec ds α [] with hlsdef
  have hT₀ : TWN (ResU.single 2 (cellB α v u w)) [cexRec] (rsOf ls) := by
    rw [hlsdef, rsOf_frameList]; exact hT₀'
  obtain ⟨hFL, -⟩ := frameLife_frame cexT δ hT3.valid hX (ResU.comp_empty_right W3)
    (ResU.comp_empty_right _) hT3.inv
  have htg₀ : Tagged (ResU.single 2 (cellB α v u w)) [cexRec] ls := by
    intro y hy
    simp only [hlsdef, frameList, List.mem_cons, List.mem_append, List.mem_map,
      List.not_mem_nil, or_false] at hy
    rcases hy with rfl | ⟨d, hd, rfl⟩
    · exact ⟨cexRec, List.mem_singleton_self _, DescR.refl cexRec, hFL⟩
    · obtain ⟨q, hq, hqd⟩ := (hds d).mp hd
      exact ⟨cexRec, List.mem_singleton_self _, ⟨q, hqd⟩, hFL⟩
  have htags : ∀ y ∈ ls, y.2 ⊐ β := by
    intro y hy
    simp only [hlsdef, frameList, List.mem_cons, List.mem_append, List.mem_map,
      List.not_mem_nil, or_false] at hy
    rcases hy with rfl | ⟨d, -, rfl⟩ <;> exact hβα
  have hr : cexRec ∈ rsOf ls := by rw [hlsdef, rsOf_frameList]; exact List.mem_cons_self
  have hle₀ : (ResU.single 2 (cellB α v u w)).get cexRec.le =
      some (CellU.immOf (LSet.singleton α) cexRec.v cexRec.R (rho2_stratum v u _)) :=
    ResU.single_get_self _ _
  have hrebF : ResU.Reb β (rho2 v u) (ResU.single 0 (cellF β v)) :=
    reb_pair_at hR (ResU.single_get_self _ _) ⟨_, hR⟩ (single_del_self _ _) _
  have hrebLe := rebRecLe_of_tags hT₀ htg₀ htags (rho2 v u)
  have hT : TWN (comp α β v u w) [cexRec] (rsOf ls) :=
    TWN.reb cexRec x hT₀ hr hle₀ (by simp [cexRec, cexT, VFree, CFree]) hrebF
      (cex_imageShape δ x β v _ _) hrebLe (bcell_frame_comp α β v u w)
      (Valid_composite α β v u w)
  exact ⟨ls, hT, tagged_rebN hT₀ hr hle₀ hrebF hrebLe (bcell_frame_comp α β v u w) htg₀, hr⟩

/-- **An image that agrees exists at `not_rebReentryAgreeN`'s resume world**: the handler's own, witness `∅`. It
is an image of the same escrow at the same `β`, of the reborrow's shape, and it differs from the
first entry's image `rebA` at the root's witness. -/
theorem cex_rechoose (x : LifeVar) :
    ResU.Reb cxβ (rho2 𝓋 𝓋) (ResU.single 0 (cellF cxβ 𝓋)) ∧
      vShape (cexT.immReborrow (.var x)) ((⟨[]⟩ : LSub).extend x cxβ) (.loc 0)
        (ResU.single 0 (cellF cxβ 𝓋)) ∧
      (∀ a, AgW cxW a → EscrowAgree (rho2 𝓋 𝓋) (ResU.single 0 (cellF cxβ 𝓋)) a) ∧
      ResU.Reb cxβ (rho2 𝓋 𝓋) (rebA cxβ 𝓋 𝓋) ∧
      ¬ ResU.CompatS (ResU.single 0 (cellF cxβ 𝓋)) (rebA cxβ 𝓋 𝓋) := by
  have hR := cex_rho2 𝓋 𝓋
  refine ⟨reb_pair_at hR (ResU.single_get_self _ _) ⟨_, hR⟩ (single_del_self _ _) _,
    cex_imageShape _ x cxβ 𝓋 _ _, fun a ha => ?_,
    reb_pair_at hR (rho2_0 𝓋 𝓋) ⟨_, ResU.comp_empty_right _⟩ (rho2_del_0 𝓋 𝓋) _, ?_⟩
  · obtain rfl : a = sigma cxα cxβ 𝓋 𝓋 (.loc 0) := AgW.functional ha (agW_comp _ _ _ _ _)
    intro l v' ψ ψf hown hψ hψf _ _
    by_cases e0 : l = 0
    · subst e0
      rw [ResU.single_get_self] at hψ; cases hψ
      rw [sigma_0] at hψf; cases hψf
      rfl
    · rw [ResU.single_get_ne _ e0] at hψ; cases hψ
  · intro hc
    obtain ⟨s₁, s₂, v', ρ, h₁, h₂, e₁, e₂⟩ :=
      hc 0 _ _ (ResU.single_get_self _ _) (rebA_0 cxβ 𝓋 𝓋)
    have w₁ := (CellU.immOf_inj e₁).2.2
    have w₂ := (CellU.immOf_inj e₂).2.2
    have hm := congrArg (fun ρ : WRes => ρ.get 1) (w₁.trans w₂.symm)
    simp only [PMap.empty_get] at hm
    rw [show (witU 𝓋).get 1 = some (CellU.ownOf 𝓋) from ResU.single_get_self _ _] at hm
    cases hm

/-! ### The per-step transport of `TWN` along a change of witness -/

/-- **The shape premise of `TWN.immFrame` moves along a change of witness.** A record proper whose
escrow is an image of another record's escrow at `β`, of that record's reborrow shape, keeps the
shape premise of its frame when its escrow is replaced by any other such image. The step a
transport of `TWN` derivations along a swap of witnesses takes at `TWN.immFrame`. -/
def ImmFrameWitSwapN : Prop :=
  ∀ (W : WRes) (ps rs : List FrameRec) (p r : FrameRec) (c : WRes) (β : Life) (x : LifeVar),
    TWN W (p :: ps) rs → r ∈ rs →
    ResU.Reb β r.R p.R → vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v p.R →
    ResU.Reb β r.R c → vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v c →
    vShape p.T p.δ p.v c

/-- The memory of `not_rebReentryAgreeN`'s resume world. -/
def cxμ : BoCa.BoLo.Heap := fun l => ((sigma cxα cxβ 𝓋 𝓋 (.loc 0)).get l).map CellU.erase

theorem cx_lower : ResU.Lower cxW cxμ := ⟨_, flat_composite _ _ _ _ _, fun _ => rfl⟩

/-- The transient record's type `imm 'x 1` and lifetimes. -/
def cxT₃ : VTy := .imm (.var 0) .unit
def cxδ₃ : LSub := (⟨[]⟩ : LSub).extend 0 cxβ

/-- The handler's image typed at `imm 'x 1`: its root witness is empty. -/
theorem cx_shape₃ : vShape cxT₃ cxδ₃ (.loc 0) (ResU.single 0 (cellF cxβ 𝓋)) := by
  refine ⟨cxβ, ?_, 0, pure_sep_mk rfl ⟨LSet.singleton cxβ, 𝓋, PMap.empty,
    (fun _ _ e => by cases e), rfl, ⟨rfl, rfl⟩, le_refl _⟩⟩
  simp [cxδ₃, BoCa.Lifetime.Life.interp, find?_extend_self]
  rfl

/-- …and the first entry's image has no shape there: its root witness holds `1 ↦ own(𝓋)`. -/
theorem cx_not_shape₃ : ¬ vShape cxT₃ cxδ₃ (.loc 0) (rebA cxβ 𝓋 𝓋) := by
  rintro ⟨α', -, ℓ, hk⟩
  obtain ⟨hl, s, v', σ, hσ, heq, ⟨hσe, -⟩, -⟩ := pure_sep_iff.mp hk
  have hl' : ℓ = 0 := by
    have := congrArg Subtype.val hl; simpa using this.symm
  subst hl'
  have e := congrArg (fun ρ : WRes => ρ.get 0) heq
  simp only [rebA_0, ResU.single_get_self] at e
  have hw := (CellU.immOf_inj (Option.some.inj e)).2.2
  rw [hσe] at hw
  have hm := congrArg (fun ρ : WRes => ρ.get 1) hw
  simp only [PMap.empty_get] at hm
  rw [show (witU 𝓋).get 1 = some (CellU.ownOf 𝓋) from ResU.single_get_self _ _] at hm
  cases hm

/-- **The per-step transport fails at a world `TWN` reaches.** From `not_rebReentryAgreeN`'s resume world: the
handler allocates `5 ↦ own(loc 0)` and takes an Imm Frame of it at `imm 'x 1`, its escrow the
handler's image of the reborrowed escrow (`TWN.alloc`, `TWN.immFrame`). Its shape premise does not
hold at the first entry's image. -/
theorem not_immFrameWitSwapN : ¬ ImmFrameWitSwapN := by
  intro hswap
  obtain ⟨ls, hT, -, hr⟩ := cex_resumeWorld
  -- 6.141: `5 ↦ own(loc 0)`
  obtain ⟨W1, hc1, hT1, -⟩ := twn_alloc hT cx_lower (l := 5)
    (by simp [cxμ, sigma_ne cxα cxβ 𝓋 𝓋 (.loc 0) (l := 5) (by decide) (by decide) (by decide)])
    (.loc 0)
  -- the thread's part `5 ↦ own(loc 0) ● 0 ↦ imm({β}, 𝓋, ∅)`, the frame `2 ↦ imm({α}, …)`
  obtain ⟨X, hX0, hXW⟩ := (ResU.CompS.assoc _ _ _ W1).mpr
    ⟨cxW, bcell_frame_comp cxα cxβ 𝓋 𝓋 (.loc 0), hc1⟩
  have hvW1 := hT1.valid
  have hhash : ResU.Hash (ResU.single 2 (cellB cxα 𝓋 𝓋 (.loc 0))) X :=
    ⟨hXW.1, W1, hXW, hvW1⟩
  set A : Life := ↓cxβ
  have hA : (ResU.single 0 (cellF cxβ 𝓋) : WRes).InStratum (LSet.singleton A).join :=
    ResU.inStratum_single 0 (Life.down_sqsubset cxβ)
  have hH := ResU.six34 (hs := hA) hX0 hhash
  obtain ⟨W', hW', hvW'⟩ := hH.2
  -- the record and its lineage
  set p : FrameRec := ⟨5, .loc 0, ResU.single 0 (cellF cxβ 𝓋), cxT₃, cxδ₃⟩ with hpdef
  have hadm : AdmWf cxT₃ cxδ₃ := by
    intro y hy
    simp [cxT₃, VFree, Lifetime.Life.mentions] at hy
    subst hy
    exact ⟨cxβ, find?_extend_self _ _ _⟩
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hvW1
  obtain ⟨eR, heR, -, -⟩ := frame_ex (ResU.CompS.comm hX0) (ResU.CompS.comm hXW) heW
  obtain ⟨ds, hds⟩ := lineage_list (r := p) cx_shape₃ hadm heR
  have hT' : TWN W' (p :: [cexRec]) (p :: (ds ++ rsOf ls)) :=
    TWN.immFrame cxT₃ cxδ₃ hA hT1 hadm (ResU.CompS.comm hX0) (ResU.CompS.comm hXW) cx_shape₃
      (ResU.CompS.comm hW') hvW' hds
  have hR := cex_rho2 𝓋 𝓋
  obtain ⟨hrebF, hdenF, -, hrebA, -⟩ := cex_rechoose 0
  have := hswap W' [cexRec] _ p cexRec (rebA cxβ 𝓋 𝓋) cxβ 0 hT'
    (List.mem_cons_of_mem _ (List.mem_append_right _ hr)) hrebF hdenF hrebA
    (cex_imageShape _ 0 cxβ 𝓋 _ _)
  exact cx_not_shape₃ this

end BoCa.Fig16.LogRel.Core.Chain.SI

end

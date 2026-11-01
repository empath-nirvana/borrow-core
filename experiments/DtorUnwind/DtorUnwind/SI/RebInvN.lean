import DtorUnwind.SI.RebRechooseN

/-!
# 6.150 across a stop, route B: typed worlds by their invariants

`IW W ps ls` is a typed world given by the invariants the development reads of one: `✓`, `TI`,
`LinLife`, `ProperRoot` and `Tagged`. Every `TWN` world with a tagged list is one (`iw_of_twn`).

At a resume the continuation of a reborrow body was proved good at the image `χ` chosen at its
first entry, and is re-entered at an image `χ′` that agrees with the resume world. Route B moves
the continuation's obligation from `χ′` to `χ` by a map on worlds: from the resume world, at which
`χ′` agrees, to a world holding `χ`, at the same records (`WitSwapIWN`). The frame's records are
kept, up to their escrows, because the frame is the one the obligation at `χ′` is owed against
and the run hands it back.

## The swap does not preserve `TI`

`not_witSwapIWN` refutes `WitSwapIWN` at round 9's world (`not_immFrameWitSwapN`'s world, built
by `TWN` and so an `IW` world): the handler holds a record `p` at `5`, typed `imm 'x 1`, whose
escrow is the handler's image `0 ↦ imm({β}, 𝓋, ∅)` of the reborrowed escrow.

* `TI`'s `ChainInv` holds `vShape p.T p.δ p.v p.R` at every record; at `imm 'x 1` that forces the
  view at `0` in `p.R` to have the empty witness (`shape₃_wit`).
* `TI`'s `LeInv` puts `p`'s cell in `ag(W)` with witness `p.R`, and `ag` carries the views nested
  in it (`ag_nested`): `ag(W)` at `0` has the empty witness.
* A world holding `χ = rebA` has, in `ag`, the view at `0` with witness `1 ↦ own(𝓋)`.

`ag(W)` is a function, so no world satisfying `TI` holds both. The argument is global: it reads
`TI` of the whole world (`LeInv` at one record, `ChainInv` at the same record, the aliasable walk
of the whole world), not a derivation step, so it applies to every map, relation or re-derivation
that keeps the frame's records.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.DtorUnwind.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.DeepReborrow
open BoCa.Lifetime (LifeVar LSub)

/-- **The invariant world.** A world, its records proper and its tagged list satisfying the
invariants the development reads of a typed world. -/
def IW (W : WRes) (ps : List FrameRec) (ls : List SRec) : Prop :=
  ResU.Valid W ∧ TI W ps (rsOf ls) ∧ LinLife W ps ∧ ProperRoot ps ∧ Tagged W ps ls

/-- Every tagged `TWN` world is an invariant world. -/
theorem iw_of_twn {W : WRes} {ps : List FrameRec} {ls : List SRec}
    (hT : TWN W ps (rsOf ls)) (htg : Tagged W ps ls) : IW W ps ls :=
  ⟨hT.valid, hT.inv, hT.linLife, hT.properRoot, htg⟩

/-- A record without its escrow: what a change of witnesses leaves of it. -/
def recKey (p : FrameRec) : Loc × Val × VTy × LSub := (p.le, p.v, p.T, p.δ)

/-- **Route B's key step: the witness swap.** At an invariant world at which an image `χ′` of a
record's escrow at `β` agrees, and for any other image `χ` of the same escrow at the same `β` of
the reborrow's shape, there is an invariant world holding `χ`, at records that differ from the
first world's only in their escrows. -/
def WitSwapIWN : Prop :=
  ∀ (W : WRes) (ps : List FrameRec) (ls : List SRec) (r : FrameRec) (β : Life) (x : LifeVar)
    (χ' χ : WRes),
    IW W ps ls → r ∈ rsOf ls →
    ResU.Reb β r.R χ' → vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v χ' →
    (∀ a, AgW W a → EscrowAgree r.R χ' a) →
    ResU.Reb β r.R χ → vShape (r.T.immReborrow (.var x)) (r.δ.extend x β) r.v χ →
    ∃ (Wo W' : WRes) (ps' : List FrameRec) (ls' : List SRec),
      ResU.CompS Wo χ W' ∧ IW W' ps' ls' ∧ ps'.map recKey = ps.map recKey

/-! ### The aliasable walk carries nested views -/

/-- A view nested in the witness of a view of `ag(W)` is a view of `ag(W)`, over the same
witness. -/
theorem ag_nested {W a : WRes} (ha : AgW W a) {le : Loc} {ψ : CellU Loc Val}
    (e : a.get le = some ψ) (hk : ψ.kind = Kind.imm) {l : Loc} {ζ : CellU Loc Val}
    (hR : ψ.wit.get l = some ζ) (hkζ : ζ.kind = Kind.imm) :
    ∃ ψ', a.get l = some ψ' ∧ ψ'.wit = ζ.wit := by
  obtain ⟨s, hs, hψ⟩ := CellU.imm_eta hk
  rw [hψ] at e
  obtain ⟨ev, av, p, z, -, hav, hp, hpz⟩ := AgW.flat_imm_wit_le ha le s _ _ hs e
  obtain ⟨ζ₁, e₁, k₁, -, w₁⟩ := AgW.get_imm hav hR hkζ
  obtain ⟨ζ₂, e₂, k₂, -, w₂⟩ := imm_fwd_full_r hp e₁ k₁
  obtain ⟨ζ₃, e₃, -, -, w₃⟩ := imm_fwd_full_l hpz e₂ k₂
  exact ⟨ζ₃, e₃, w₃.trans (w₂.trans w₁)⟩

/-- A record proper's escrow's `imm` views are views of `ag(W)`, at every `TI` world. -/
theorem ag_of_record {W a : WRes} {ps rs : List FrameRec} (hTI : TI W ps rs) (ha : AgW W a)
    {p : FrameRec} (hp : p ∈ ps) {l : Loc} {ζ : CellU Loc Val} (hR : p.R.get l = some ζ)
    (hkζ : ζ.kind = Kind.imm) : ∃ ψ', a.get l = some ψ' ∧ ψ'.wit = ζ.wit := by
  obtain ⟨ψ, e, k, -, w⟩ := hTI.2.1 p hp a ha
  exact ag_nested ha e k (by rw [w]; exact hR) hkζ

/-! ### The shape `imm 'x 1` fixes the witness -/

/-- At `imm 'x 1` over `loc 0`, the escrow is one view at `0`, with the empty witness. -/
theorem shape₃_wit {R : WRes} (h : vShape cxT₃ cxδ₃ (.loc 0) R) :
    ∃ ζ : CellU Loc Val, R.get 0 = some ζ ∧ ζ.kind = Kind.imm ∧ ζ.wit = PMap.empty := by
  obtain ⟨α', -, ℓ, hk⟩ := h
  obtain ⟨hl, s, v', σ, hσ, heq, ⟨hσe, -⟩, -⟩ := pure_sep_iff.mp hk
  have hl' : ℓ = 0 := by
    have := congrArg Subtype.val hl; simpa using this.symm
  subst hl'
  refine ⟨CellU.immOf s v' σ hσ, ?_, CellU.kind_immOf _ _ _ _, by rw [CellU.wit_immOf, hσe]⟩
  rw [heq]; exact ResU.single_get_self _ _

/-! ### Round 9's world as an invariant world -/

/-- The handler's record: `5 ↦ loc 0` at `imm 'x 1`, its escrow the handler's image. -/
def cxP : FrameRec := ⟨5, .loc 0, ResU.single 0 (cellF cxβ 𝓋), cxT₃, cxδ₃⟩

/-- **Round 9's world is a tagged `TWN` world at the handler's record and the reborrowed one.**
`not_immFrameWitSwapN`'s construction, with the tags. -/
theorem cex_frameWorld :
    ∃ (W' : WRes) (ls' : List SRec), TWN W' [cxP, cexRec] (rsOf ls') ∧
      Tagged W' [cxP, cexRec] ls' ∧ cexRec ∈ rsOf ls' := by
  obtain ⟨ls, hT, htg, hr⟩ := cex_resumeWorld
  obtain ⟨W1, hc1, hT1, -⟩ := twn_alloc hT cx_lower (l := 5)
    (by simp [cxμ, sigma_ne cxα cxβ 𝓋 𝓋 (.loc 0) (l := 5) (by decide) (by decide) (by decide)])
    (.loc 0)
  have htg1 : Tagged W1 [cexRec] ls := tagged_of_ag (fun a ha => alloc_ag hc1 ha) htg
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
  have hadm : AdmWf cxT₃ cxδ₃ := by
    intro y hy
    simp [cxT₃, VFree, Lifetime.Life.mentions] at hy
    subst hy
    exact ⟨cxβ, find?_extend_self _ _ _⟩
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hvW1
  obtain ⟨eR, heR, -, -⟩ := frame_ex (ResU.CompS.comm hX0) (ResU.CompS.comm hXW) heW
  obtain ⟨ds, hds⟩ := lineage_list (r := cxP) cx_shape₃ hadm heR
  set ls' : List SRec := frameList cxP ds A ls with hls'def
  have hT' : TWN W' [cxP, cexRec] (rsOf ls') := by
    rw [hls'def, rsOf_frameList]
    exact TWN.immFrame cxT₃ cxδ₃ hA hT1 hadm (ResU.CompS.comm hX0) (ResU.CompS.comm hXW)
      cx_shape₃ (ResU.CompS.comm hW') hvW' hds
  obtain ⟨hFLnew, hFLold⟩ := frameLife_frame (α := A) cxT₃ cxδ₃ hvW1 (ResU.CompS.comm hX0)
    (ResU.CompS.comm hXW) (ResU.CompS.comm hW') hT1.inv
  have htg' : Tagged W' [cxP, cexRec] ls' := by
    intro y hy
    simp only [hls'def, frameList, List.mem_cons, List.mem_append, List.mem_map] at hy
    rcases hy with rfl | ⟨d, hd, rfl⟩ | hy
    · exact ⟨cxP, List.mem_cons_self, DescR.refl cxP, hFLnew⟩
    · obtain ⟨q, hq, hqd⟩ := (hds d).mp hd
      exact ⟨cxP, List.mem_cons_self, ⟨q, hqd⟩, hFLnew⟩
    · obtain ⟨q, hq, hqd, hfq⟩ := htg1 y hy
      exact ⟨q, List.mem_cons_of_mem _ hq, hqd, hFLold q hq y.2 hfq⟩
  refine ⟨W', ls', hT', htg', ?_⟩
  rw [hls'def, rsOf_frameList]
  exact List.mem_cons_of_mem _ (List.mem_append_right _ hr)

/-- At every `TI` world holding the handler's record, the view of `ag` at `0` has the empty
witness. -/
theorem cx_ag0_empty {W a : WRes} {ps rs : List FrameRec} (hTI : TI W ps rs) (ha : AgW W a)
    {p : FrameRec} (hp : p ∈ ps) (hkey : recKey p = recKey cxP) :
    ∃ ψ, a.get 0 = some ψ ∧ ψ.wit = PMap.empty := by
  have hpR : p ∈ rs := (hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hp, DescR.refl p⟩
  have hsh := (hTI.1.2.2.2.1 p hpR).1
  simp only [recKey, cxP, Prod.mk.injEq] at hkey
  obtain ⟨-, hv, hT, hδ⟩ := hkey
  rw [hv, hT, hδ] at hsh
  obtain ⟨ζ, eζ, kζ, wζ⟩ := shape₃_wit hsh
  obtain ⟨ψ, e, w⟩ := ag_of_record hTI ha hp eζ kζ
  exact ⟨ψ, e, w.trans wζ⟩

/-! ### The refutation -/

/-- **Route B's key step is refuted** at round 9's world: no invariant world holds the first
entry's image `rebA` beside the handler's record. Of the swapped world's invariants the proof
reads `✓` (for `ag`), `TI`'s `LeInv`, its membership clause and `ChainInv`'s shape clause, each at
the handler's record only. -/
theorem not_witSwapIWN : ¬ WitSwapIWN := by
  intro hswap
  obtain ⟨W, ls, hT, htg, hr⟩ := cex_frameWorld
  have hIW := iw_of_twn hT htg
  obtain ⟨hrebF, hdenF, -, hrebA, -⟩ := cex_rechoose 0
  -- the handler's image agrees with `ag(W)`: the view at `0` has the empty witness
  have hagree : ∀ a, AgW W a → EscrowAgree cexRec.R (ResU.single 0 (cellF cxβ 𝓋)) a := by
    intro a ha l v' ψ ψf _ hψ hψf _ _
    by_cases e0 : l = 0
    · subst e0
      rw [ResU.single_get_self] at hψ; cases hψ
      obtain ⟨ψ₀, e₀, w₀⟩ := cx_ag0_empty hIW.2.1 ha (p := cxP) List.mem_cons_self rfl
      rw [hψf] at e₀; cases e₀
      rw [w₀, cellF_wit]
    · rw [ResU.single_get_ne _ e0] at hψ; cases hψ
  obtain ⟨Wo, W', ps', ls', hc, hIW', hkeys⟩ := hswap W [cxP, cexRec] ls cexRec cxβ 0
    (ResU.single 0 (cellF cxβ 𝓋)) (rebA cxβ 𝓋 𝓋) hIW hr hrebF hdenF hagree hrebA
    (cex_imageShape _ 0 cxβ 𝓋 _ _)
  -- the handler's record survives, up to its escrow
  obtain ⟨p', hp', hkey⟩ : ∃ p' ∈ ps', recKey p' = recKey cxP := by
    have : recKey cxP ∈ ps'.map recKey := by rw [hkeys]; exact List.mem_cons_self
    obtain ⟨p', hp', e⟩ := List.mem_map.mp this
    exact ⟨p', hp', e⟩
  obtain ⟨a, ha⟩ := agW_of_valid hIW'.1
  obtain ⟨ψ₀, e₀, w₀⟩ := cx_ag0_empty hIW'.2.1 ha hp' hkey
  -- `rebA` puts the view at `0` with witness `1 ↦ own(𝓋)` into `ag(W′)`
  obtain ⟨ao, ac, -, hac, hcomp⟩ := (AgW.split hc).mp ha
  obtain ⟨ζ₁, e₁, k₁, -, w₁⟩ := AgW.get_imm hac (rebA_0 cxβ 𝓋 𝓋) (CellU.kind_immOf _ _ _ _)
  obtain ⟨ζ₂, e₂, -, -, w₂⟩ := imm_fwd_full_r hcomp e₁ k₁
  rw [e₀] at e₂; cases e₂
  rw [w₀] at w₂
  rw [CellU.wit_immOf] at w₁
  have hm := congrArg (fun ρ : WRes => ρ.get 1) (w₂.trans w₁)
  simp only [PMap.empty_get] at hm
  rw [show (witU 𝓋).get 1 = some (CellU.ownOf 𝓋) from ResU.single_get_self _ _] at hm
  cases hm

end BoCa.Fig16.LogRel.Core.DtorUnwind.SI

end

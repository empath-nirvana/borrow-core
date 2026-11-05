import Core.Chain.SI.RebRechooseN

/-!
# Round 8's world at canonical images

`cex_canon`: the record of round 8's counterexample (`SI/RebAgreeCex.lean`) has a template, and at
every `TWNC` world holding it the canonical image agrees with the world. The handler's image at
round 8's resume world enters by `TWNC.reb` only as `canon cexRec β`, the image the continuation
holds.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.DeepReborrow
open BoCa.Lifetime (LifeVar)

/-! ### Round 8's world -/

/-- **Round 8's configuration at canonical images.** The record `cexRec` has a typed image (the
handler's, witness `∅`), so its template exists (existence). Round 8's resume world adds the
handler's image by `TWN.reb`; at `TWNC` that step needs the image to be `canon cexRec β`, the same
image the continuation holds, and then the agreement holds at every typed world holding the
record (`canon_escrowAgree`). -/
theorem cex_canon (β : Life) :
    (∃ c, TmplSpec cexRec c) ∧
      ∀ (W : WRes) (ps rs : List FrameRec), TWNC W ps rs → cexRec ∈ rs →
        ∀ a, AgW W a → EscrowAgree cexRec.R (canon cexRec β) a := by
  have hR := cex_rho2 𝓋 𝓋
  have hex : ∃ c, TmplSpec cexRec c := by
    obtain ⟨-, a₂, -, h₂, -⟩ := (AgW.split (bcell_frame_comp cxα cxβ 𝓋 𝓋 (.loc 0))).mp
      (agW_comp cxα cxβ 𝓋 𝓋 (.loc 0))
    exact ⟨_, cxβ, 0, by simp [cexRec, cexT, VFree, CFree],
      reb_pair_at hR (ResU.single_get_self _ _) ⟨_, hR⟩ (single_del_self _ _) _,
      cex_imageShape _ 0 cxβ 𝓋 _ _, a₂, h₂⟩
  exact ⟨hex, fun W ps rs hT hr => canon_escrowAgree hT hr (tmpl_spec hex) β⟩

end BoCa.Fig16.LogRel.Core.Chain.SI

end

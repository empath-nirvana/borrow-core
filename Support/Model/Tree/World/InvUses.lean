import Support.Model.Tree.World.TInvHolds

/-!
# The results that read `TIT`

`[spec §62]`. `TWNT.noOwnUnder` (`World/NoOwnUnder.lean`'s vocabulary) and `TWNT.used_cellAt`,
`TWNT.tcCoherent`, `TWNT.tcCarried_exists` (`World/Coherent.lean`'s), each reading `TIT` at a
`TWNT` world through `TWNT.inv`.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa.Fig16.Tree
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo

variable {K : WCactus}

/-- `LeInv` gives `own_not_at_view`'s hypothesis at every record proper. -/
theorem leInv_view {Θ : CodeTy} {tc : TChoice K} {W : TRes K} {ps rs : List (FrameRecT K)}
    (hT : TWNT K Θ tc W ps rs) {q : FrameRecT K} (hq : q ∈ ps) :
    ∀ a, AgWT W a → ∃ ψ : TCell K, a.get q.le = some ψ := fun a ha => by
  obtain ⟨ψ, hψ, -, -, -⟩ := hT.inv.2.1 q hq a ha
  exact ⟨ψ, hψ⟩

/-- **No `own` cell of a record's location beneath a borrow of the world.** -/
def NoOwnUnderT (W : TRes K) (ps : List (FrameRecT K)) : Prop :=
  ∀ p ∈ ps, ¬ OwnUnder W p.le

/-- **`NoOwnUnder` is an invariant of `TWNT`.** It reads `TIT` at `immFrame` and `mutFold`
(`leInv_view`); at `reread` a re-reading keeps every cell's
kind and the witnesses' cells (`OwnAt.rr_back`), and every record's location (`RecRR`). -/
theorem TWNT.noOwnUnder {Θ : CodeTy} {tc : TChoice K} {W : TRes K}
    {ps rs : List (FrameRecT K)} (h : TWNT K Θ tc W ps rs) : NoOwnUnderT W ps := by
  induction h with
  | empty => intro p hp; simp at hp
  | alloc _ _ _ hW _ ih =>
      intro p hp ho
      rcases OwnUnder.split hW ho with h | h
      · exact ih p hp h
      · exact not_ownUnder_single_own _ _ _ h
  | @immFrame K Θ tc W X Z R W' ps rs ds l v α T hα hT hX hW hden hW' hv hds ih =>
      intro p hp ho
      rcases step_frame hX hW (CellUT.wit_immOf _ _ _ _) hW' ho with h | ⟨χ, e, hk⟩
      · rcases List.mem_cons.mp hp with rfl | hp
        · -- the new record: `W(ℓ) = own(v)`
          have hl : W.get l = some (CellUT.ownOf v) :=
            (ResUT.CompS.get_left_of_ne_imm hW
              (ResUT.CompS.get_left_of_ne_imm hX (ResUT.single_get_self _ _) (by simp)).2
              (by simp)).2
          exact not_ownUnder_top_own hT.valid hl h
        · exact ih p hp h
      · rcases List.mem_cons.mp hp with rfl | hp
        · -- `ρ` misses `ℓ`: `ℓ ↦ own(v) ● ρ` is defined
          have := hX.1 l _ χ (ResUT.single_get_self _ _) e
          exact absurd (CellUT.CompatS.kind_left this) (by simp)
        · obtain ⟨ζ, eζ, kζ⟩ := top_of_frame hX hW e
          exact own_not_at_view hT.valid (leInv_view hT hp) eζ (kζ.trans hk)
  | reb r hT hr hle hreb hden hβ hc hW hv ih =>
      intro p hp ho
      rcases OwnUnder.split hW ho with h | h
      · exact ih p hp h
      · exact ih p hp (OwnUnder.of_cell hle (by simp)
          (by rw [CellUT.wit_immOf]; exact ownAt_image hreb h))
  | rebDeep r hT hr hch hcell hreb hden hβc hrec hc hW hv ih =>
      intro p hp ho
      rcases OwnUnder.split hW ho with h | h
      · exact ih p hp h
      · exact ih p hp (OwnUnder.of_cell hcell (by simp)
          (by rw [CellUT.wit_immOf]; exact ownAt_image hreb h))
  | mutFold hT hX hW hW' hv ih =>
      intro p hp ho
      rcases step_frame hX hW (CellUT.wit_mutOf _ _ _ _ _ _) hW' ho with h | ⟨χ, e, hk⟩
      · exact ih p hp h
      · obtain ⟨ζ, eζ, kζ⟩ := top_of_frame hX hW e
        exact own_not_at_view hT.valid (leInv_view hT hp) eζ (kζ.trans hk)
  | mutUnfold hT hW hX hW' hv ih =>
      intro p hp ho
      rcases OwnUnder.split hW' ho with h | h
      · rcases OwnUnder.split hX h with h | ⟨m, ζ, e, hk, hw⟩
        · exact not_ownUnder_single_own _ _ _ h
        · obtain ⟨ψ, eψ, kψ, wψ, -⟩ :=
            compS_get_left' hW (ResUT.single_get_self _ _)
          refine ih p hp (OwnUnder.of_cell eψ (by rw [kψ]; simp) ?_)
          rw [wψ, CellUT.wit_mutOf]
          exact OwnAt.nest e hk hw
      · exact ih p hp (OwnUnder.of_compS_right hW h)
  | free hT hW hv ih =>
      intro p hp ho
      exact ih p hp (OwnUnder.of_compS_right hW ho)
  | store hT hW hW' hv ih =>
      intro p hp ho
      rcases OwnUnder.split hW' ho with h | h
      · exact not_ownUnder_single_own _ _ _ h
      · exact ih p hp (OwnUnder.of_compS_right hW h)
  | immEnd r hT hr hc hX' hW' hv hps hrs ih =>
      intro p hp ho
      have hp' : p ∈ _ := ((hps p).mp hp).1
      rcases OwnUnder.split hW' ho with h | h
      · rcases OwnUnder.split hX' h with h | ⟨m, ζ, e, hk, hw⟩
        · exact not_ownUnder_single_own _ _ _ h
        · obtain ⟨ψ, eψ, kψ, wψ, -⟩ :=
            compS_get_left' hc (ResUT.single_get_self _ _)
          refine ih p hp' (OwnUnder.of_cell eψ (by rw [kψ]; simp) ?_)
          rw [wψ, CellUT.wit_immOf]
          exact OwnAt.nest e hk hw
      · exact ih p hp' (OwnUnder.of_compS_right hc h)
  | rebEnd r hT hr hle hreb hW hβ ih =>
      intro p hp ho
      exact ih p hp (OwnUnder.of_compS_left hW ho)
  | rebEndDeep r hT hr hch hle hreb hW hβ ih =>
      intro p hp ho
      exact ih p hp (OwnUnder.of_compS_left hW ho)
  | reread hT hE hag hr hps hrs _ ih =>
      intro p' hp' ho
      obtain ⟨p, hp, hpp⟩ := forall₂_mem_right hps hp'
      rw [hpp.1] at ho
      exact ih p hp (ho.rr_back hr)

/-- **Every used argument's cells sit at depth of the world.** A record's escrow is the witness of
the record cell's view (`LeInv`) or of a `mut` cell of its parent's escrow; a chain view's
witness is the witness of a view of `ag(W)`. -/
theorem TWNT.used_cellAt {Θ : CodeTy} {tc : TChoice K} {W : TRes K}
    {ps rs : List (FrameRecT K)} (hT : TWNT K Θ tc W ps rs) {R : TRes K} {T : KTy}
    {v : BoCa.Val} (hu : UsedT W rs R T v) : ∀ y ψ, R.get y = some ψ → CellAt W y ψ := by
  have hTI := hT.inv
  obtain ⟨aW, haW⟩ := agW_of_valid hT.valid
  rcases hu with ⟨r, hr, rfl, -, -⟩ | ⟨r, -, p₀, l₀, -, a, ha, ψ₀, e₀, k₀, rfl⟩
  · obtain ⟨p, hp, q, hq⟩ := (hTI.2.2.2.2.2.2.1 r).mp hr
    obtain ⟨ψ, eψ, kψ, -, wψ⟩ := hTI.2.1 p hp aW haW
    obtain ⟨ψ', cψ', wψ'⟩ := agW_cellAt haW _ ψ eψ (by rw [kψ]; simp)
    refine hq.cellAt fun y φ e => cψ'.wit_trans ?_
    rw [wψ', wψ]; exact e
  · obtain ⟨ψ', cψ', wψ'⟩ := agW_cellAt ha _ ψ₀ e₀ k₀
    exact fun y φ e => cψ'.wit_trans (by rw [wψ']; exact e)

/-- **Template coherence across a re-reading**: two used arguments whose escrows re-read to one
escrow are one argument, so their templates re-read to one template. -/
theorem TWNT.tcCoherent {K' : WCactus} {Θ Θ' : CodeTy} {tc : TChoice K}
    {W : TRes K} {ps rs : List (FrameRecT K)} (hT : TWNT K Θ tc W ps rs) :
    TcCoherent (K' := K') Θ' W rs tc :=
  tcCoherent_of_inj fun _ _ _ _ h₁ h₂ _ e₁ e₂ =>
    RR.inj_of hT.mutOne e₁ e₂ (hT.used_cellAt h₁) (hT.used_cellAt h₂)

/-- **A carried choice exists at every re-reading** whose used templates have re-readings:
`tcCarried_exists` at `TWNT.tcCoherent`. -/
theorem TWNT.tcCarried_exists {K' : WCactus} {Θ Θ' Θ'' : CodeTy}
    {tc : TChoice K} {W : TRes K} {ps rs : List (FrameRecT K)} (hT : TWNT K Θ tc W ps rs)
    (hex : ∀ R T v, UsedT W rs R T v → ∃ c : TRes K', RR (sem Θ') (tc R T v) c) :
    ∃ tc' : TChoice K', TcCarried Θ' W rs tc tc' :=
  BoCa.Fig16.Tree.Wp.tcCarried_exists (Θ' := Θ') (Θ'' := Θ'') hex (hT.tcCoherent (K' := K') (Θ' := Θ'))

end BoCa.Fig16.Tree.Wp

end

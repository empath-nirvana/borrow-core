import Support.Model.Tree.World.TInvReb

/-!
# `TIT` across `immFrame`

`[spec §62]`. `Core/Invariant.lean`'s `ti_frame` over `TWNT` (`tit_frame`): a view of `ag(W)`
reaches `ag(W′)` over the same witness (`frame_fwd`).
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

variable {K : WCactus} {Θ : CodeTy}

/-- Under `immFrame`, a view of `ag(W)` reaches `ag(W′)` over the same witness. -/
theorem frame_fwd {W X Z R W' a' : TRes K} {l : BoCa.Loc} {v : BoCa.Val} {α : Life}
    {h : R.InStratum (TSet.single α)}
    (hX : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) R X) (hW : ResUT.CompS X Z W)
    (hW' : ResUT.CompS (ResUT.single l (CellUT.immOf (TSet.single α) v R h)) Z W')
    (hv : ResUT.Valid W) (ha' : AgWT W' a') {aW : TRes K} (haW : AgWT W aW) {m : BoCa.Loc}
    {ψ₀ : TCell K} (e₀ : aW.get m = some ψ₀) (k₀ : ψ₀.kind ≠ Kind.own) :
    ∃ ψ, a'.get m = some ψ ∧ ψ.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit := by
  obtain ⟨eW, aW', r, z, eR, σc, pc, -, haW', -, hrz, -, -, -, hpc, hcp, hcz⟩ :=
    frame_walks hX hW hW' hv ha'
  rw [AgWT.functional haW' haW] at hrz
  rcases back_view hrz e₀ k₀ with ⟨ψ₁, e₁, k₁, w₁⟩ | ⟨ψ₁, e₁, k₁, w₁⟩
  · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := lift_view_r hpc e₁ k₁
    obtain ⟨ψ₃, e₃, k₃, w₃⟩ := lift_view_r hcp e₂ k₂
    obtain ⟨ψ₄, e₄, k₄, w₄⟩ := lift_view hcz e₃ k₃
    exact ⟨ψ₄, e₄, k₄, w₄.trans (w₃.trans (w₂.trans w₁.symm))⟩
  · obtain ⟨ψ₄, e₄, k₄, w₄⟩ := lift_view_r hcz e₁ k₁
    exact ⟨ψ₄, e₄, k₄, w₄.trans w₁.symm⟩
/-- `immFrame` keeps `TI`. -/
theorem tit_frame {W X Z R W' : TRes K} {ps rs ds : List (FrameRecT K)} {l : BoCa.Loc} {v : BoCa.Val}
    {α : Life} {T : KTy} {hα : R.InStratum (TSet.single α)}
    (hvW : ResUT.Valid W)
    (hX : ResUT.CompS (ResUT.single l (CellUT.ownOf v)) R X) (hW : ResUT.CompS X Z W)
    (hden : (T.interp Θ).P K v R)
    (hW' : ResUT.CompS (ResUT.single l (CellUT.immOf (TSet.single α) v R hα)) Z W')
    (hv : ResUT.Valid W') (hds : ∀ d, d ∈ ds ↔ DescT ⟨l, v, R, T⟩ d) (h : TIT K Θ W ps rs) :
    TIT K Θ W' (⟨l, v, R, T⟩ :: ps) (⟨l, v, R, T⟩ :: (ds ++ rs)) := by
  have hlw : LeInvW W rs := TI.leInvW h
  obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, hle, hid, hio, hN, hM, hmem, hC⟩ := h
  obtain ⟨σ₀, eW, aW, heW, haW, -⟩ := id hvW
  obtain ⟨a', ha'⟩ := agW_of_valid hv
  obtain ⟨eR, heR, hRW, hRl⟩ := frame_ex hX hW heW
  -- the new lineage lives in `ex(W)_●`
  have newEx : ∀ d, DescRT ⟨l, v, R, T⟩ d → ∀ x (ζ : TCell K), d.R.get x = some ζ →
      ζ.kind ≠ Kind.imm → eR.get x = some ζ := by
    rintro d ⟨p, hp⟩ x ζ e k
    exact xpath_ex heR hp.xpath e k
  have newNotAg : ∀ d, DescRT ⟨l, v, R, T⟩ d → ∀ x (ζ : TCell K), d.R.get x = some ζ →
      ζ.kind ≠ Kind.imm → aW.get x = none := by
    intro d hd x ζ e k
    cases ea : aW.get x with
    | none => rfl
    | some ξ => exact (ex_ag_disjoint hvW heW haW (hRW x ζ (newEx d hd x ζ e k) k) ea).elim
  have newUnique : ∀ d₁ d₂, DescRT ⟨l, v, R, T⟩ d₁ → DescRT ⟨l, v, R, T⟩ d₂ →
      ∀ x (ζ₁ ζ₂ : TCell K), d₁.R.get x = some ζ₁ → ζ₁.kind ≠ Kind.imm →
      d₂.R.get x = some ζ₂ → ζ₂.kind ≠ Kind.imm → d₁ = d₂ := by
    rintro d₁ d₂ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ x ζ₁ ζ₂ e₁ k₁ e₂ k₂
    have hpp := xpath_unique heR hp₁.xpath hp₂.xpath e₁ k₁ e₂ k₂
    subst hpp
    exact hp₁.functional hden hp₂
  have newNotL : ∀ d, DescRT ⟨l, v, R, T⟩ d → ∀ ζ : TCell K, d.R.get l = some ζ →
      ζ.kind ≠ Kind.imm → False := by
    intro d hd ζ e k
    rw [newEx d hd l ζ e k] at hRl; cases hRl
  have newRoot : ∀ d, DescRT ⟨l, v, R, T⟩ d → ∀ m u, d.R.get m = some (CellUT.ownOf u) →
      ∀ a, AgWT W' a → (∃ ζ, a.get m = some ζ) ∧
        (∀ ψ : TCell K, a.get m = some ψ → ψ.kind ≠ Kind.own → False) := by
    intro d hd m u hm a ha
    have := frame_new_root' hX hW hW' hvW
      (fun eR' heR' => by rw [ExST.functional heR' heR]; exact newEx d hd m _ hm (by simp))
      (fun hml => newNotL d hd (CellUT.ownOf u) (by rw [← hml]; exact hm) (by simp)) ha
    exact ⟨this.1, this.2.1⟩
  have newTyped : ∀ d, DescRT ⟨l, v, R, T⟩ d → (d.T.interp Θ).P K d.v d.R :=
    fun d ⟨p, hp⟩ => hp.typed hden
  have mem' : ∀ x, x ∈ (⟨l, v, R, T⟩ :: (ds ++ rs) : List (FrameRecT K)) →
      DescRT ⟨l, v, R, T⟩ x ∨ x ∈ rs := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Or.inl (DescRT.refl _)
    · rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨p, -, hp⟩ := (hds x).mp hx; exact Or.inl ⟨p, hp⟩
      · exact Or.inr hx
  -- a new record's location is not in `ag(W)`
  have newLeNone : ∀ d, DescRT ⟨l, v, R, T⟩ d → aW.get d.le = none := by
    intro d hd
    rcases hd.cases with rfl | ⟨p, hp, hpp⟩
    · cases e : aW.get l with
      | none => rfl
      | some ζ =>
          have Wl : W.get l = some (CellUT.ownOf v) :=
            (ResUT.CompS.get_left_of_ne_imm hW (ResUT.CompS.get_left_of_ne_imm hX
              (ResUT.single_get_self _ _) (by simp)).2 (by simp)).2
          exact (ex_ag_disjoint hvW heW haW (ExST.get_of_ne_imm heW Wl (by simp)) e).elim
    · obtain ⟨d', hd', -, ζ, eζ, kζ, -⟩ := hpp.last hp
      exact newNotAg d' hd' _ ζ eζ (by rw [kζ]; simp)
  -- the transfer for the old records
  have back : ∀ r ∈ rs, ∀ m u, r.R.get m = some (CellUT.ownOf u) → ∀ a, AgWT W' a →
      ∀ ψ : TCell K, a.get m = some ψ → ψ.kind ≠ Kind.own →
      ∃ ψ₀ : TCell K, aW.get m = some ψ₀ ∧ ψ₀.kind ≠ Kind.own ∧ ψ.wit = ψ₀.wit := by
    intro r hr m u hm a ha ψ e hk
    obtain ⟨aW₁, haW₁, ψ₀, e₀, k₀, w₀⟩ := frame_transfer hX hW hW' hvW (h2 r hr m u hm) ha e hk
    rw [AgWT.functional haW₁ haW] at e₀
    exact ⟨ψ₀, e₀, k₀, w₀⟩
  -- the `ICp` maps across the frame
  obtain ⟨eW', aW', rw₀, z, eR', σc, pc, heW', haW', hr', hrz, heR', -, hl, hpc, hcp, hcz⟩ :=
    frame_walks hX hW hW' hvW ha'
  rw [AgWT.functional haW' haW] at hrz
  have lNone : aW.get l = none := newLeNone _ (DescRT.refl _)
  have backI : ∀ m, m ≠ l → ICpAt aW a' m := by
    intro m hm
    exact icpAt_comp hcz (icpAt_comp hcp (icpAt_none (single_ne _ hm))
      (icpAt_comp hpc (icpAt_of_immFree (ExST.immFree heR') m) (icpAt_left hrz m)))
      (icpAt_right hrz m)
  have fwdI : ∀ m, ICpAt a' aW m := by
    intro m
    exact icpAt_comp hrz (icpAt_trans (icpAt_right hpc m)
      (icpAt_trans (icpAt_right hcp m) (icpAt_left hcz m))) (icpAt_right hcz m)
  have tm : ∀ x, MutAtT W' x → MutAtT W x := by
    intro x hm
    rcases MutAtT.split hW' hm with h₁ | h₂
    · cases h₁ with
      | top e hk => obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e; exact absurd hk (by simp)
      | nest e hk hw =>
          obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e
          rw [CellUT.wit_immOf] at hw
          exact MutAtT.of_compS_left hW (MutAtT.of_compS_right hX hw)
    · exact MutAtT.of_compS_right hW h₂
  have Wl : W.get l = some (CellUT.ownOf v) :=
    (ResUT.CompS.get_left_of_ne_imm hW
      (ResUT.CompS.get_left_of_ne_imm hX (ResUT.single_get_self _ _) (by simp)).2 (by simp)).2
  refine ⟨⟨fun x hx => ?_, fun x hx m u hm a ha => ?_, fun x₁ hx₁ x₂ hx₂ m u₁ u₂ hm₁ hm₂ => ?_,
    fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩, fun x hx a ha => ?_,
    fun x₁ hx₁ x₂ hx₂ e => ?_, fun x₁ hx₁ x₂ hx₂ u hu => ?_, fun x hx => ?_, ⟨fun x hx => ?_,
    fun x hx m u hm hmm => ?_⟩, fun x => ?_, ?_⟩
  -- DeepInv
  · rcases mem' x hx with hd | hx
    · intro p m S u hc a ha ψ e hk
      exact ((newRoot x hd m u hc.own a ha).2 ψ e hk).elim
    · intro p m S u hc a ha ψ e hk
      obtain ⟨ψ₀, e₀, k₀, w₀⟩ := back x hx m u hc.own a ha ψ e hk
      obtain ⟨kk, d, o, b₁, b₂⟩ := h1 x hx p m S u hc aW haW ψ₀ e₀ k₀
      obtain ⟨ψ', e', k'⟩ := frame_imm hX hW hW' hvW ha haW e₀ kk
      rw [e] at e'; cases Option.some.inj e'
      refine ⟨k', w₀ ▸ d, w₀ ▸ o, fun hp => w₀ ▸ b₁ hp, fun l₀ hp => ?_⟩
      obtain ⟨ψ₁, e₁, k₁, q, hq, hql, hw⟩ := b₂ l₀ hp
      obtain ⟨ψ₂, e₂, k₂, w₂⟩ := frame_fwd hX hW hW' hvW ha haW e₁ k₁
      exact ⟨ψ₂, e₂, k₂, q, w₂ ▸ hq, hql, w₀.trans hw⟩
  -- support
  · rcases mem' x hx with hd | hx
    · exact (newRoot x hd m u hm a ha).1
    · exact frame_support hX hW hW' hvW (h2 x hx m u hm) ha
  -- escrows own disjoint locations
  · rcases mem' x₁ hx₁ with hd₁ | hx₁ <;> rcases mem' x₂ hx₂ with hd₂ | hx₂
    · exact newUnique x₁ x₂ hd₁ hd₂ m _ _ hm₁ (by simp) hm₂ (by simp)
    · obtain ⟨ζ, hζ⟩ := h2 x₂ hx₂ m u₂ hm₂ aW haW
      rw [newNotAg x₁ hd₁ m _ hm₁ (by simp)] at hζ; cases hζ
    · obtain ⟨ζ, hζ⟩ := h2 x₁ hx₁ m u₁ hm₁ aW haW
      rw [newNotAg x₂ hd₂ m _ hm₂ (by simp)] at hζ; cases hζ
    · exact h3 x₁ hx₁ x₂ hx₂ m u₁ u₂ hm₁ hm₂
  -- typed
  · rcases mem' x hx with hd | hx
    · exact newTyped x hd
    · exact h4 x hx
  -- JointAt
  · rcases mem' x hx with hd | hx
    · rintro ⟨S, m, u, hR, a, ha, ψ, e, hk⟩
      exact ((newRoot x hd m u hR.2 a ha).2 ψ e hk).elim
    · rintro ⟨S, m, u, hR, a, ha, ψ, e, hk⟩
      obtain ⟨ψ₀, e₀, k₀, -⟩ := back x hx m u hR.2 a ha ψ e hk
      obtain ⟨β₀, c₀, q2, q3, q4, q5⟩ := h5 x hx ⟨S, m, u, hR, aW, haW, ψ₀, e₀, k₀⟩
      refine ⟨β₀, c₀, q2, q3, q4, fun S' m' u' hR' a₁ ha₁ ψ₁ e₁ hk₁ => ?_⟩
      obtain ⟨ψ₂, e₂, k₂, w₂⟩ := back x hx m' u' hR'.2 a₁ ha₁ ψ₁ e₁ hk₁
      obtain ⟨ζ, eζ, wζ⟩ := q5 S' m' u' hR' aW haW ψ₂ e₂ k₂
      exact ⟨ζ, eζ, w₂.trans wζ⟩
  -- JointDeep
  · rcases mem' x hx with hd | hx
    · rintro p₀ l₀ S₀ u₀ - ⟨m, S, u, hc, a, ha, ψ, e, hk⟩
      exact ((newRoot x hd m u hc.own a ha).2 ψ e hk).elim
    · rintro p₀ l₀ S₀ u₀ hc₀ ⟨m, S, u, hc, a, ha, ψ, e, hk⟩
      obtain ⟨ψ₀, e₀, k₀, -⟩ := back x hx m u hc.own a ha ψ e hk
      obtain ⟨w₀, hw₀, β₀, c₀, q2, q3, q4, q5⟩ :=
        h6 x hx p₀ l₀ S₀ u₀ hc₀ ⟨m, S, u, hc, aW, haW, ψ₀, e₀, k₀⟩
      refine ⟨w₀, fun a₁ ha₁ => ?_, β₀, c₀, q2, q3, q4,
        fun m' S' u' hc' a₁ ha₁ ψ₁ e₁ hk₁ => ?_⟩
      · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := hw₀ aW haW
        obtain ⟨ψ₃, e₃, k₃, w₃⟩ := frame_fwd hX hW hW' hvW ha₁ haW e₂ k₂
        exact ⟨ψ₃, e₃, k₃, w₃.trans w₂⟩
      · obtain ⟨ψ₂, e₂, k₂, w₂⟩ := back x hx m' u' hc'.own a₁ ha₁ ψ₁ e₁ hk₁
        obtain ⟨ζ, eζ, wζ⟩ := q5 m' S' u' hc' aW haW ψ₂ e₂ k₂
        exact ⟨ζ, eζ, w₂.trans wζ⟩
  -- LeInvT at the records proper
  · rcases List.mem_cons.mp hx with rfl | hx
    · obtain ⟨ψ, e, k, w, r'⟩ := compS_get_left' hW' (ResUT.single_get_self _ _)
      obtain ⟨χ, eχ, kχ, rχ, wχ⟩ := AgWT.get_imm ha e (k.trans (CellUT.kind_immOf _ _ _ _))
      exact ⟨χ, eχ, kχ, by rw [rχ, r']; rfl, by rw [wχ, w]; simp⟩
    · obtain ⟨ψ₀, e₀, k₀, r₀, w₀⟩ := hle x hx aW haW
      obtain ⟨ψ, e, k, r', w⟩ := frame_fwd_imm hX hW hW' hvW ha haW e₀ k₀
      exact ⟨ψ, e, k, r'.trans r₀, w.trans w₀⟩
  -- records proper sit at distinct cells
  · rcases List.mem_cons.mp hx₁ with rfl | hx₁ <;> rcases List.mem_cons.mp hx₂ with rfl | hx₂
    · rfl
    · obtain ⟨ψ, e', -⟩ := hle x₂ hx₂ aW haW
      simp only at e
      rw [← e, lNone] at e'; cases e'
    · obtain ⟨ψ, e', -⟩ := hle x₁ hx₁ aW haW
      simp only at e
      rw [e, lNone] at e'; cases e'
    · exact hid x₁ hx₁ x₂ hx₂ e
  -- no escrow owns a record's location
  · rcases mem' x₁ hx₁ with hd₁ | hx₁ <;> rcases mem' x₂ hx₂ with hd₂ | hx₂
    · rcases hd₁.cases with rfl | ⟨p, hp, hpp⟩
      · exact newNotL x₂ hd₂ _ hu (by simp)
      · obtain ⟨d', hd', -, ζ, eζ, kζ, -⟩ := hpp.last hp
        have := newUnique d' x₂ hd' hd₂ _ ζ _ eζ (by rw [kζ]; simp) hu (by simp)
        subst this
        rw [hu] at eζ; cases Option.some.inj eζ; exact absurd kζ (by simp)
    · obtain ⟨ζ, hζ⟩ := h2 x₂ hx₂ _ u hu aW haW
      rw [newLeNone x₁ hd₁] at hζ; cases hζ
    · obtain ⟨ψ, e, -⟩ := hlw x₁ hx₁ aW haW
      rw [newNotAg x₂ hd₂ _ _ hu (by simp)] at e; cases e
    · exact hio x₁ hx₁ x₂ hx₂ u hu
  -- NestLife
  · rcases mem' x hx with hd | hx
    · intro l₀ m S u hc a ha ψ s e hs y hy
      exact ((newRoot x hd m u hc.own a ha).2 ψ e
        (by rw [CellUT.kind_of_lsOf hs]; simp)).elim
    · refine nestLife_of_icp (hN x hx) haW (fun a₁ ha₁ l₀ m S u hc => ?_)
        (fun a₁ ha₁ l₀ m S u hc => by rw [AgWT.functional ha₁ ha']; exact fwdI l₀)
      rw [AgWT.functional ha₁ ha']
      refine backI m (fun hml => ?_)
      obtain ⟨ζ, hζ⟩ := h2 x hx m u hc.own aW haW
      rw [hml, lNone] at hζ; cases hζ
  -- NoMutT at the records proper
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact fun hm => not_mutAt_top_own hvW Wl (tm _ hm)
    · exact fun hm => hM.1 x hx (tm _ hm)
  -- NoMutT at every escrow's `own` cells
  · rcases mem' x hx with hd | hx
    · exact not_mutAt_ex_own hvW heW (hRW m _ (newEx x hd m _ hm (by simp)) (by simp)) (tm _ hmm)
    · exact hM.2 x hx m u hm (tm _ hmm)
  -- membership
  · constructor
    · intro hx
      rcases mem' x hx with hd | hx
      · exact ⟨_, List.mem_cons_self, hd⟩
      · obtain ⟨p, hp, hpx⟩ := (hmem x).mp hx
        exact ⟨p, List.mem_cons_of_mem _ hp, hpx⟩
    · rintro ⟨p, hp, hpx⟩
      rcases List.mem_cons.mp hp with rfl | hp
      · rcases hpx.cases with rfl | hd
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ ((hds x).mpr hd))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ ((hmem x).mpr ⟨p, hp, hpx⟩))
  -- coverage
  · intro a₁ ha₁ m ψ e hk
    rw [AgWT.functional ha₁ ha'] at e
    by_cases hml : m = l
    · subst hml
      obtain ⟨ψ₁, e₁, k₁, w₁, r₁⟩ := compS_get_left' hW' (ResUT.single_get_self _ _)
      obtain ⟨χ, eχ, kχ, rχ, wχ⟩ := AgWT.get_imm ha' e₁ (k₁.trans (CellUT.kind_immOf _ _ _ _))
      rw [e] at eχ; cases Option.some.inj eχ
      exact Or.inl ⟨_, List.mem_cons_self, rfl, by rw [rχ, r₁]; rfl, by rw [wχ, w₁]; simp⟩
    · obtain ⟨ζ, eζ, kζ, rζ, wζ, -⟩ := backI m hml ψ e hk
      rcases hC aW haW m ζ eζ kζ with ⟨r, hr, h₁, h₂, h₃⟩ | ⟨r, hr, p, S, u, hch⟩
      · exact Or.inl ⟨r, List.mem_cons_of_mem _ (List.mem_append_right _ hr), h₁,
          rζ.symm.trans h₂, wζ.symm.trans h₃⟩
      · exact Or.inr ⟨r, List.mem_cons_of_mem _ (List.mem_append_right _ hr), p, S, u, hch⟩

end BoCa.Fig16.Tree.Wp

end

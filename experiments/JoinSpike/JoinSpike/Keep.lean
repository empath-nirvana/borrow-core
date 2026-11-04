import Core.TreePool

/-!
# Join spike: a run beside a frame that may hold views of the run's lenders

`twp_frame_keep_sh` is `twp_frame_keep` (`Core/TreePool.lean`) with one direction of the
separation relaxed. The run may hold anything at the masks of framed records lent at a location
in `S` (the shared lends: their views are spread across tasks); for every other framed record it
holds nothing at the record's masks at the start, and still holds nothing there at the end (R1,
read per record). The framed part still holds nothing at the masks of the run's records. The
proof is `twp_frame_keep`'s with the R1 conclusion read one record at a time; `hesc₂` was used
nowhere else.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont)

/-- **A resource framed beside a run keeps the records it reads; R1 per unshared record.** -/
theorem twp_frame_keep_sh {S : BoCa.Loc → Prop} {F F₁ : TFrame} {P : TPost} {R : TRProp} (hR : R.Mono) {n : Nat}
    {w : TWd} {ls : List (SRecT w.K)} {O₁ O₂ : List (FrameRecT w.K)}
    (hO : ∀ p ∈ O₁, ∀ q ∈ O₂, p.le ≠ q.le) {e : Expr} {ρ₁ ρ₂ ρ : TRes w.K}
    (hcρ : ResUT.CompS ρ₁ ρ₂ ρ) (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ)
    (hesc₁ : NoneAt (recMask O₁) ρ₂) (hesc₂ : ∀ q ∈ O₂, ¬ S q.le → NoneAt (recMask [q]) ρ₁)
    (hF : ∀ (w₀ : TWd) (ρf ρ₁₀ ρ₂₀ y fρ : TRes w₀.K) (O₁₀ O₂₀ ps psF : List (FrameRecT w₀.K))
      (ls₀ : List (SRecT w₀.K)) (μ : Heap), w.Ext w₀ ρ₂ → RRw (w := w) (w' := w₀) ρ₂ ρ₂₀ →
      RecsRR w₀.Θ O₁ O₁₀ → RecsRR w₀.Θ O₂ O₂₀ → F w₀ ρf → ResUT.CompS ρf ρ₂₀ y →
      ResUT.CompS y ρ₁₀ fρ → SplitT ps (O₁₀ ++ O₂₀) psF →
      (∀ p ∈ O₁₀, ∀ q ∈ O₂₀, p.le ≠ q.le) → RecInv w₀ fρ ps ls₀ → WInv w₀ fρ μ → F₁ w₀ y)
    (hwp : twp (ℍ := ℍ) F₁ P n w ls O₁ e ρ₁) (hR₂ : R w O₂ ρ₂) :
    twp (ℍ := ℍ) F (fun k w' ls' O' t ρ' => ∃ (O₁' O₂' : List (FrameRecT w'.K)) (a b : TRes w'.K),
      O' = O₁' ++ O₂' ∧ ResUT.CompS a b ρ' ∧ P k w' ls' O₁' t a ∧ R w' O₂' b ∧
        KeepRel w'.Θ ls ls' ρ₂ ∧ NoneAt (recMask O₁') b ∧
          (∀ q ∈ O₂', ¬ S q.le → NoneAt (recMask [q]) a) ∧
        (∀ p ∈ O₁', ∀ q ∈ O₂', p.le ≠ q.le) ∧ (∀ q ∈ O₂', ¬ recMask O₁' q.le) ∧
        ∀ p ∈ O₁', ¬ recMask O₂' p.le)
      n w ls (O₁ ++ O₂) e ρ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hOr hFρ hf hc hS hRi hI hfd j μ' e' hj hrun hfin
  obtain ⟨O₁₀, O₂₀, rfl, hO₁, hO₂⟩ := forall₂_append_left hOr
  have hO₀ : ∀ p ∈ O₁₀, ∀ q ∈ O₂₀, p.le ≠ q.le := by
    intro p hp q hq
    obtain ⟨p₁, hp₁, r₁⟩ := forall₂_mem_right hO₁ hp
    obtain ⟨q₂, hq₂, r₂⟩ := forall₂_mem_right hO₂ hq
    rw [r₁.1, r₂.1]
    exact hO p₁ hp₁ q₂ hq₂
  obtain ⟨ρ₁₀, ρ₂₀, h₁₀, h₂₀, hc₀⟩ := RR.split_retype hE.1 hcρ hcov hE.2 hr
  have hE₁ := hE.of_compS_left hcρ
  have hE₂ := hE.of_compS_right hcρ
  obtain ⟨y, hy, hyf⟩ := reassoc_out hc hc₀
  have hS₁ : SplitT ps O₁₀ (O₂₀ ++ psF) := by
    refine ⟨fun p => ?_, fun p hp q hq => ?_⟩
    · rw [hS.1 p, List.mem_append, List.mem_append]; tauto
    · rcases List.mem_append.mp hq with h | h
      · exact hO₀ p hp q h
      · exact hS.2 p (List.mem_append_left _ hp) q h
  obtain ⟨w', y', ρ₁', fρ', psF'', ps', O₁', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
      g₁₁⟩ :=
    hwp w₀ ρ₁₀ y fρ ls₀ O₁₀ ps (O₂₀ ++ psF) μ hE₁ h₁₀ hl hO₁
      (hF w₀ ρf ρ₁₀ ρ₂₀ y fρ O₁₀ O₂₀ ps psF ls₀ μ hE₂ h₂₀ hO₁ hO₂ hFρ hy hyf hS hO₀ hRi hI)
      (hash_of_inv hyf hI) hyf hS₁ hRi hI hfd j μ' e' hj hrun hfin
  obtain ⟨O₂', psF', rfl, hO₂', hpsF'⟩ := forall₂_append_left g₂
  obtain ⟨ρf', ρ₂', hf', h₂', hy'⟩ :=
    RR.split_retype g₀.1 hy (covf_of_comp hyf hI) g₀.2 g₁
  obtain ⟨ρ', hρ', hfρ'⟩ := reassoc_in hy' g₄
  have hR₂₀ : R w₀ O₂₀ ρ₂₀ := hR _ _ _ _ _ _ hE₂ h₂₀ hO₂ hR₂
  have hvy' : ResUT.Valid y' := (ResUT.Valid.split g₄ g₇.valid).1
  have hu : UpdX (sem w'.Θ) (recMask O₁₀) (recMask O₁') ρ₀ ρ' :=
    UpdX.frame g₀.1 g₉ h₂' hc₀ hρ' (cov_valid hc hI) (cov_valid hfρ' g₇)
      (g₁₀.of_compS_right hy' hvy')
  have hmask : ∀ x, MaskDiff (recMask (O₁₀ ++ O₂₀)) (recMask (O₁' ++ O₂')) x →
      MaskDiff (recMask O₁₀) (recMask O₁') x := fun x hx => by
    unfold MaskDiff at hx ⊢
    rw [recMask_append, recMask_append, ← recMask_rr hO₂' x] at hx
    tauto
  -- validity of the parts, at `w` and at `w₀`
  have hv₁ : ResUT.Valid ρ₁ := (ResUT.Valid.split hcρ hv).1
  have hv₂ : ResUT.Valid ρ₂ := (ResUT.Valid.split hcρ hv).2
  have hvy : ResUT.Valid y := (ResUT.Valid.split hyf hI.valid).1
  have hv₂₀ : ResUT.Valid ρ₂₀ := (ResUT.Valid.split hy hvy).2
  have hv₁₀ : ResUT.Valid ρ₁₀ := (ResUT.Valid.split hyf hI.valid).2
  have hvesc : ∀ p ∈ ps, ResUT.Valid p.R := TWNT.esc_valid hRi.1
  -- the separation at `w₀`
  have hesc₁₀ : NoneAt (recMask O₁₀) ρ₂₀ :=
    (hesc₁.rr hE.1 hv₂ h₂₀).mono fun x hx => (recMask_rr hO₁ x).mpr hx
  -- **the records the framed part reads are kept**
  have hkeep : KeepRel w'.Θ ls ls' ρ₂ := by
    intro r hr₀ hrel
    obtain ⟨r₀, hr₀', e₀⟩ := hl.mem_fwd hr₀
    have hrel₀ : RelFT r₀ ρ₂₀ := (RelFT.rr_iff e₀ h₂₀).mp hrel
    obtain ⟨p₁, hp₁, hd⟩ := (hRi.1.inv.2.2.2.2.2.2.1 r₀).mp hr₀'
    rcases (hS₁.1 p₁).mp hp₁ with hp₁O | hp₁F
    · exact (relFT_not_fdEsc hd hrel₀ hv₂₀ (hvesc p₁ hp₁)
        (fdEsc_of_noneAt hRi.1 hp₁O hp₁ hesc₁₀)).elim
    · obtain ⟨r', hr', e'⟩ := keep_frameRooted g₂ g₅ g₆.1 ⟨p₁, hp₁F, hd⟩
      exact ⟨r', hr', RecRR.trans g₀.1 e₀ e'⟩
  -- **the framed part avoids the masks of the records the run ends with**
  have hb : NoneAt (recMask O₁') ρ₂' := by
    intro τ hτ x hx
    by_cases hx₀ : recMask O₁₀ x
    · exact (hesc₁₀.rr g₀.1 hv₂₀ h₂') τ hτ x hx₀
    · exact (g₁₀.of_compS_right hy' hvy') τ hτ x (Or.inr ⟨hx, hx₀⟩)
  -- **the run's end avoids the masks of the framed records** (R1)
  have ha : ∀ q' ∈ O₂', ¬ S q'.le → NoneAt (recMask [q']) ρ₁' := by
    intro q' hq' hS'
    refine noneAt_recMask (fun q hq => by
      rcases List.mem_singleton.mp hq with rfl
      exact TWNT.esc_valid g₆.1 q (g₅.right q (List.mem_append_left _ hq'))) fun q₁ hq₁ => ?_
    rcases List.mem_singleton.mp hq₁ with rfl
    obtain ⟨q, hq, hqq⟩ := forall₂_mem_right hO₂' hq'
    obtain ⟨q₂, hq₂, hqq₂⟩ := forall₂_mem_right hO₂ hq
    have hq₀ : q ∈ ps := (hS.1 q).mpr (Or.inl (List.mem_append_right _ hq))
    have hn₂ : ¬ S q₂.le := by rw [← hqq₂.1, ← hqq.1]; exact hS'
    have hn : NoneAt (recMask [q]) ρ₁₀ :=
      ((hesc₂ q₂ hq₂ hn₂).rr hE.1 hv₁ h₁₀).mono fun x hx =>
        (recMask_rr (List.Forall₂.cons hqq₂ .nil) x).mpr hx
    exact fdEsc_of_updX g₀.1 (hvesc q hq₀) (fdEsc_of_noneAt hRi.1 (List.mem_singleton_self q) hq₀ hn)
      g₆.1 g₄ g₅ (List.mem_append_left _ hq') hqq g₉
  -- **the framed records' lent locations are outside the run's masks**
  have hout : ∀ q ∈ O₂', ¬ recMask O₁' q.le := by
    rintro q hq ⟨p, hp, hx⟩
    have hTI := g₆.1.inv
    have hpps : p ∈ ps' := (g₅.1 p).mpr (Or.inl hp)
    have hqps : q ∈ ps' := (g₅.1 q).mpr (Or.inr (List.mem_append_left _ hq))
    rcases hx with hx | hx
    · exact g₅.2 p hp q (List.mem_append_left _ hq) hx.symm
    · have hprs : p ∈ rsOfT ls' := (hTI.2.2.2.2.2.2.1 p).mpr ⟨p, hpps, [], .nil p⟩
      exact le_not_linLoc g₆.1 hpps hqps (ExDom.linLoc w'.Θ hx p rfl (hTI.1.2.2.2.1 p hprs))
  have hout' : ∀ p ∈ O₁', ¬ recMask O₂' p.le := by
    rintro p hp ⟨q, hq, hx⟩
    have hTI := g₆.1.inv
    have hpps : p ∈ ps' := (g₅.1 p).mpr (Or.inl hp)
    have hqps : q ∈ ps' := (g₅.1 q).mpr (Or.inr (List.mem_append_left _ hq))
    rcases hx with hx | hx
    · exact g₅.2 p hp q (List.mem_append_left _ hq) hx
    · have hqrs : q ∈ rsOfT ls' := (hTI.2.2.2.2.2.2.1 q).mpr ⟨q, hqps, [], .nil q⟩
      exact le_not_linLoc g₆.1 hqps hpps (ExDom.linLoc w'.Θ hx q rfl (hTI.1.2.2.2.1 q hqrs))
  refine ⟨w', ρf', ρ', fρ', psF', ps', O₁' ++ O₂', ls', g₀.of_compS_left hy, hf', hpsF',
    ResUT.hash_symm (hash_of_inv hfρ' g₇), hfρ', ⟨fun p => ?_, fun p hp q hq => ?_⟩, g₆, g₇,
    ⟨O₁', O₂', ρ₁', ρ₂', rfl, hρ', g₈, hR _ _ _ _ _ _ (g₀.of_compS_right hy) h₂' hO₂' hR₂₀,
      hkeep, hb, ha, fun p hp q hq => g₅.2 p hp q (List.mem_append_left _ hq), hout, hout'⟩,
    (hu.widen (recMask O₂₀)).congr (fun l => recMask_append l)
      (fun l => by rw [recMask_append, recMask_rr hO₂' l]),
    (g₁₀.of_compS_left hy' hvy').mono hmask,
    (g₁₁.mono fun l h => (recMask_append l).mpr (Or.inl h)).frame hc₀ (TWNT.mutOne hRi.1)
      (fun _ _ h k => (h.of_compS_right hc₀ (kind_mut_ne_imm k)).of_compS_right hc
        (kind_mut_ne_imm k))
      (AgreeOn.of_compS_right hy g₀.2)⟩
  · rw [g₅.1 p, List.mem_append, List.mem_append]; tauto
  · rcases List.mem_append.mp hp with h | h
    · exact g₅.2 p h q (List.mem_append_right _ hq)
    · obtain ⟨p₀, hp₀, r₀⟩ := forall₂_mem_right hO₂' h
      obtain ⟨q₀, hq₀, s₀⟩ := forall₂_mem_right hpsF' hq
      rw [r₀.1, s₀.1]
      exact hS.2 p₀ (List.mem_append_right _ hp₀) q₀ hq₀


end BoCa.Fig16.Tree.Wp

end

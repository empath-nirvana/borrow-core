import Core.Chain.SI.LoanX.HandleX

/-! Positive ghost ownership at a real linear capture. Generic derived rule; no machine
or erwpX definition changes. Unlike KapRelX alone, the stop carries J positively. -/
noncomputable section
variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]
namespace BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont Head performE opPayload hndE hndVal kappaC kappaAt capTag clauseAt)

def claimTable (T : OpTabX) (name : UInt32) (J : UInt32 → GRes → Prop) : TableX :=
  fun M M' _ k ls t Ψ x =>
    ∃ (K : Kont) (m i : UInt32) (v : Val) (en : OpEntX),
      t = K.plug (performE (.val (opPayload m i v))) ∧ K.HasHnd m = false ∧ T m i = some en ∧
      (en.remask = true ∨ M' = M) ∧
      sepX (en.PA k ls v) (fun y => (m = name → J i y.2) ∧ contShareX en k ls K Ψ y) x

theorem claimTable_local (T : OpTabX) (name : UInt32) (J : UInt32 → GRes → Prop) :
    (claimTable T name J).Local := by
  rintro M M' C k ls t Ψ Ψ' x hΨ ⟨K,m,i,v,en,ht,hK,hT,hrm,ρa,ρk,ga,gk,hc,hg,hA,hJ,hu,hcont⟩
  refine ⟨K,m,i,v,en,ht,hK,hT,hrm,ρa,ρk,ga,gk,hc,hg,hA,hJ,hu,?_⟩
  intro ls' he
  exact ⟨fun k' hk w y z hB hcz => hΨ k' hk _ _ _ ((hcont ls' he).1 k' hk w y z hB hcz),
    (hcont ls' he).2⟩

/-- The real linear handler passes J on the captured κ share to its clause. Capture-cell
allocation preserves its ghost, so this requires no bespoke allocation invariant. -/
theorem handle_claim_le {Φ : LocFam} (hΦ : Φ.Down) (N : Nat) (Tin Tout : OpTabX)
    (hTinD : Tin.Down) (hTout : Tout.Down) (name : UInt32) (J : UInt32 → GRes → Prop)
    (hTin : ∀ m i, m ≠ name → Tin m i = Tout m i) (qs hr hs : Val) (Qin Qout : PostX)
    (hQout : Qout.Down)
    (hlin : ∀ i en, Tin name i = some en → en.q = .lin ∧ en.remask = false)
    (hq : ∀ i en, Tin name i = some en → capTag qs.1 i.toNat = en.q.tag)
    (hret : ∀ M C k, k ≤ N → ∀ ls v x, Qin C k ls v x →
      erwpX (ℍ := ℍ) Φ M (opTableX Tout) Qout k ls (.app (.val hr) (.val v)) x)
    (hop : ∀ i en, Tin name i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      ∀ M k, k ≤ N → ∀ ls v (κ : Val) x,
        sepX (en.PA k ls v) (fun y => J i y.2 ∧
          KapRelX (ℍ := ℍ) Φ M (opTableX Tout) Qout en k ls κ y) x →
        erwpX (ℍ := ℍ) Φ M (opTableX Tout) Qout k ls (.app (.val c) (.pair (.val v) κ.1)) x) :
    ∀ n, n ≤ N → ∀ M ls e x,
      erwpX (ℍ := ℍ) Φ M (claimTable Tin name J) Qin n ls e x →
      erwpX (ℍ := ℍ) Φ M (opTableX Tout) Qout n ls (hndE (hndVal name qs hr hs) e) x := by
  have hLin := claimTable_local Tin name J
  have hLout := opTableX_local Tout
  have hDout := opTableX_down hTout
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN M ls e x h
  have hPD := erwpXPost_down (M := M) hDout hQout (erwpXC (ℍ := ℍ) Φ (opTableX Tout) Qout n)
  set H := hndVal name qs hr hs with hH
  rw [erwpX_eq]
  show rwpGX (ℍ := ℍ) Φ M _ n ls ((hndK H).plug e) x
  refine rwpGX_bind hΦ (hndK H) ?_
  refine rwpGX_mono_le (fun M' C k hk ls' t y ht => ?_) (erwpX_unfold_at hLin le_rfl h)
  have hcontIH : ∀ M'' k', k' < k → ∀ ls'' e'' τ,
      erwpXC (ℍ := ℍ) Φ (claimTable Tin name J) Qin n M'' k' ls'' e'' τ →
      erwpXC (ℍ := ℍ) Φ (opTableX Tout) Qout n M'' k' ls'' (hndE H e'') τ := by
    intro M'' k' hk' ls'' e'' τ hc
    simp only [erwpXC, show k' < n by omega, if_true] at hc ⊢
    exact ih k' (by omega) (by omega) M'' ls'' e'' τ hc
  rcases ht with ⟨hM',v,rfl,hv⟩ | ht
  · subst M'
    exact Or.inl ⟨rfl,(rwpGX_det hΦ hPD
      (fun μ => step1Only_plug (Head.hret μ name qs hr hs v) rfl .hole)
      (erwpX_unfold_at hLout hk (hret M C k (by omega) ls' v y hv))).at C⟩
  obtain ⟨K₁,m,i,v,en,rfl,hK₁,hT,hrm,ρa,ρk,ga,gk,hcak,hg,hA,hJ,hu,hcont⟩ := ht
  by_cases hm : m = name
  · subst hm
    obtain ⟨hql,hrf⟩ := hlin i en hT
    have hMM : M' = M := by rw [hrf] at hrm; simpa using hrm
    subst M'
    obtain ⟨c,hc,hna⟩ := hop i en hT
    refine Or.inl ⟨rfl,(rwpGX_det hΦ hPD
      (fun μ => step1Only_plug (Head.hop μ m i qs hr hs c v K₁ hc hK₁) rfl .hole) ?_).at C⟩
    rw [hq i en hT,kappaAt_tag,hql]
    obtain ⟨y₁,y₂⟩ := y
    simp only at hcak hg
    subst hg
    refine erwpX_unfold_at hLout hk (erwpX_kappaCell hΦ hLout hDout hQout false H K₁
      (.appR (.val c) (.pairR v .hole)) (fun ℓ σ₂ hc₂ => ?_))
    obtain ⟨z,hz₁,hz₂⟩ := compS_reassoc hcak (ResU.CompS.comm hc₂)
    have hA' : en.PA (k - 1) ls' v (ρa,ga) := by
      cases k with
      | zero => exact hA
      | succ k₀ => exact hTinD.pa _ _ _ hT _ _ _ _ hA
    refine hna M (k - 1) (by omega) ls' v ⟨_,isVal_kappaC _ ℓ H K₁⟩ (σ₂,ga + gk)
      ⟨ρa,z,ga,gk,hz₂,rfl,hA',hJ rfl,?_⟩
    intro ls'' he k' hk' w y z' hB hcz
    have hzk : CompX (ρk,gk) (ResU.single ℓ (CellU.ownOf Val.unit),0) (z,gk) := ⟨hz₁,by simp⟩
    have he' := hTinD.wcl _ _ _ hT _ _ _ _ _ hzk he
    obtain ⟨hcz₁,hcz₂⟩ := hcz
    simp only at hcz₁ hcz₂
    obtain ⟨u,hu₁,hu₂⟩ := compS_exch hz₁ hcz₁
    have h₁ := hcontIH M k' (by omega) _ _ _
      ((hcont ls'' he').1 k' (by omega) w y (u,gk + y.2) hB ⟨hu₁,rfl⟩)
    simp only [erwpXC,show k' < n by omega,if_true] at h₁
    obtain ⟨z'₁,z'₂⟩ := z'
    simp only at hcz₂ hu₂ ⊢
    subst hcz₂
    exact erwpX_kappaC_resume hΦ hLout hDout hQout _ ℓ H K₁ w (ResU.CompS.comm hu₂)
      (erwpX_le hΦ hLout hDout hQout (Nat.sub_le k' 1) h₁)
  · have hKo : ((hndK H).comp K₁).HasHnd m = false := by
      rw [hasHnd_comp,hndK_hasHnd,hK₁]; simpa using Ne.symm hm
    have ht' : (hndK H).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((hndK H).comp K₁).plug (performE (.val (opPayload m i v))) := by rw [Kont.plug_comp]
    refine Or.inr ⟨by rw [ht']; exact final_opPlug (r := false) (payloadName_opPayload m i v) hKo,
      Or.inr ?_⟩
    rw [ht']
    refine ⟨(hndK H).comp K₁,m,i,v,en,rfl,hKo,(hTin m i hm) ▸ hT,hrm,ρa,ρk,ga,gk,
      hcak,hg,hA,hu,fun ls'' he => ⟨fun k' hk' w y₁ z hB hcz => ?_,fun hq' => ?_⟩⟩
    · rw [Kont.plug_comp]
      exact hcontIH M' k' hk' _ _ _ ((hcont ls'' he).1 k' hk' w y₁ z hB hcz)
    · intro P hP
      show P k ls'' (((hndK H).comp K₁).dead.plug _) (ρk,gk)
      rw [dead_comp,dead_hndK]
      exact (hcont ls'' he).2 hq' P hP

#print axioms claimTable_local
#print axioms handle_claim_le
end BoCa.Fig16.LogRel.Core.Chain.SI.TypedCase

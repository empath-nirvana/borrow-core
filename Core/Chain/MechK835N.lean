import Core.Chain.SI.MFrameK
import Core.Chain.SI.LoopN
import Core.Chain.SI.UbindN
import Core.Chain.SI.UbindGN
import Core.Chain.SI.FinCancelN
import Core.Chain.SI.FinPerformN

/-!
# The mechanical stop producers at `erwpK`  `[spec §19, §27, §62]`

`docs/new-core/scope-835-kripke-stop.md` §2, class M. Each producer is restated at `erwpK` over
any world index: the existing proof, the continuation premise read at every world the stop allows,
the continuation re-entered at the resumption world. Each `erwp` statement is proved again from its
`erwpK` form at one world (`*_of_K`); its text is the original's.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload ubindE cfinE)

variable {ι : Type}

/-! ### Tables -/

theorem cancelTabK_local (lo : Life) (T : OpTabK ι) : (cancelTabK lo T).Local := by
  intro k ls t Ψ Ψ' ρ hΨ h
  rcases h with ⟨K, n, i, v, en, h⟩ | h
  · obtain ⟨hp, ρa, ρk, hc, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp h
    exact Or.inl ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, hu, f, hf, fun y hy ls' he =>
      ⟨fun k' hk w σ₁ σ₂ hB hcσ => hΨ y k' hk _ _ _ ((hcont y hy ls' he).1 k' hk w σ₁ σ₂ hB hcσ),
        (hcont y hy ls' he).2⟩⟩⟩
  · exact Or.inr h

theorem cancelTabRK_local (lo : Life) (T : OpTabK ι) (R : Nat → WProp) :
    (cancelTabRK lo T R).Local := by
  intro k ls t Ψ Ψ' ρ hΨ h
  rcases h with ⟨K, n, i, v, en, h⟩ | h
  · obtain ⟨hp, ρa, ρk, hc, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp h
    exact Or.inl ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, hu, f, hf, fun y hy ls' he =>
      ⟨fun k' hk w σ₁ σ₂ hB hcσ => hΨ y k' hk _ _ _ ((hcont y hy ls' he).1 k' hk w σ₁ σ₂ hB hcσ),
        (hcont y hy ls' he).2⟩⟩⟩
  · exact Or.inr h

theorem performStopK_localK (lo : Life) (T : OpTabK ι) : (performStopK lo T).Local := by
  intro k ls t Ψ Ψ' ρ hΨ h
  obtain ⟨K, n, i, v, en, h⟩ := h
  obtain ⟨hp, ρa, ρk, hc, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp h
  exact ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, hu, f, hf, fun y hy ls' he =>
    ⟨fun k' hk w σ₁ σ₂ hB hcσ => hΨ y k' hk _ _ _ ((hcont y hy ls' he).1 k' hk w σ₁ σ₂ hB hcσ),
      (hcont y hy ls' he).2⟩⟩⟩

theorem opTableRK_local (lo : Life) (T : OpTabK ι) (R : Nat → WProp) :
    (opTableRK lo T R).Local := by
  intro k ls t Ψ Ψ' ρ hΨ h
  rcases h with h | h
  · exact Or.inl (performStopK_localK lo T k ls t Ψ Ψ' ρ hΨ h)
  · exact Or.inr h

/-- `cancelTabN_down` over a world index. -/
theorem cancelTabK_down {lo : Life} {T : OpTabK ι} (hT : T.Down) : (cancelTabK lo T).Down := by
  intro k ls t Ψ ρ h
  rcases h with ⟨K, n, i, v, en, h⟩ | ⟨K, err, hp⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp h
    refine Or.inl ⟨K, n, i, v, en, pure_sep_mk ⟨h₁, h₂, h₃, h₄⟩ ⟨ρa, ρk, hc,
      hT.pa _ _ _ h₃ _ _ _ _ hA, hu, f, hf, fun y hy ls' he =>
      ⟨fun k' hk => (hcont y hy ls' he).1 k' (by omega), fun hq P hP =>
        hT.fin _ _ _ _ h₃ hP _ _ _ _ _ ((hcont y hy ls' he).2 hq P hP)⟩⟩⟩
  · obtain ⟨hc, τa, τb, hcab, he, hnb⟩ := pure_sep_iff.mp hp
    refine Or.inr ⟨K, err, pure_sep_mk hc ⟨τa, τb, hcab, ?_, hnb⟩⟩
    cases err with
    | none => exact he
    | some E =>
        obtain ⟨m, j, w, en, he⟩ := he
        obtain ⟨hh, hPA, hn⟩ := pure_sep_iff.mp he
        exact ⟨m, j, w, en, pure_sep_mk hh ⟨hT.pa _ _ _ hh.2.1 _ _ _ _ hPA, hn⟩⟩

/-- `OpTabN.Down` at the lifted table. -/
theorem OpTabN.Down.liftK {T : OpTabN} (h : T.Down) : (liftTabK T).Down where
  pa n i en hT k ls v ρ hA := by
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
    exact h.pa n i en₀ h₀ k ls v ρ hA
  fin n i en P hT hP y k ls e ρ hP' := by
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some hT
    simp only [liftEntK, Option.map_eq_some_iff] at hP
    obtain ⟨P₀, hP₀, rfl⟩ := hP
    exact h.fin n i en₀ P₀ h₀ hP₀ k ls e ρ hP'

/-! ### Bind up to an index -/

/-- **Bind at `erwpK` with the continuation known only up to the index `N`** (`erwp_bind_le`). -/
theorem erwpK_bind_le {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down) (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life}
    {T : ι → OpTabK ι} (hTV : ∀ x y, V x y → (opTableK (fl y) (T y)).Le (opTableK (fl x) (T x)))
    {Q Q' : ι → PostN} (K : Kont) (hH : ∀ m, K.HasHnd m = false)
    (hC : ∀ m, K.Catches m = false) (hK : ∀ x, (T x).CtxClosed K) (N : Nat)
    (hcont : ∀ y k ls (v : Val) ρ, k ≤ N → Q' y k ls v ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q y k ls (K.plug v.1) ρ) :
    ∀ n, n ≤ N → ∀ x ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q' x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q x n ls (K.plug e) ρ := by
  have hL : ∀ z, (opTableK (fl z) (T z)).Local := fun z => opTableK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN x ls e ρ h
  rw [erwpK_eq]
  refine rwpG_bind (hΦ x) K ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwpK_unfold_at hL le_rfl h)
  rcases ht with ⟨v, rfl, y, hy, hv⟩ | ht | ht
  · exact erwpK_shift hVt hΦV hTV hL hy hk (hcont y k ls' v σ (by omega) hv)
  · obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont'⟩ := pure_sep_iff.mp hp
    have hKo : (K.comp K₁).HasHnd m = false := by simp [hasHnd_comp, hH, hK₁]
    have ht' : K.plug (K₁.plug (performE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
        ⟨ρa, ρk, hcak, hA, hu, f, hf, fun y hy ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
          fun hq' P hP => ?_⟩⟩⟩))
    · rw [Kont.plug_comp]
      have hc := (hcont' y hy ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpCK, show k' < n by omega, if_true] at hc ⊢
      exact ih k' (by omega) (by omega) y _ _ _ hc
    · exact hK x m i en P hT hP y _ _ _ _ _ ((hcont' y hy ls'' he).2 hq' P hP)
  · obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, hrest⟩ := pure_sep_iff.mp hp
    have hKo : (K.comp K₁).Catches m = false := by simp [catches_comp, hC, hK₁]
    have ht' : K.plug (K₁.plug (raiseE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE true (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    exact rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩ hrest⟩))

/-- `erwp_bind_le` from `erwpK_bind_le`. -/
theorem erwp_bind_le_of_K {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} {Q Q' : PostN} (K : Kont)
    (hH : ∀ m, K.HasHnd m = false) (hC : ∀ m, K.Catches m = false) (hK : T.CtxClosed K)
    (N : Nat) (hcont : ∀ k ls (v : Val) ρ, k ≤ N → Q' k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Q k ls (K.plug v.1) ρ) :
    ∀ n, n ≤ N → ∀ ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T) Q' n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Q n ls (K.plug e) ρ := by
  intro n hn ls e ρ h
  rw [erwp_opTableN_eq_erwpK 0] at h ⊢
  refine erwpK_bind_le (ℍ := ℍ) (V := fun _ _ => True) (fun _ _ _ _ _ => trivial)
    (Φ := fun _ => Φ) (fun _ => hΦ) (fun _ _ _ => rfl) (fl := fun _ => 0)
    (T := fun _ => liftTabK T) (fun _ _ _ _ _ _ _ _ h => h) K hH hC (fun _ => liftTabK_ctxClosed hK)
    N ?_ n hn () ls e ρ h
  intro y k ls' v ρ' hk hv
  rw [← erwp_opTableN_eq_erwpK 0]
  exact hcont k ls' v ρ' hk hv

/-! ### The finaliser frame -/

/-- **A cancel run carrying `R`, under a frame whose finaliser consumes `R`, at `erwpK`**
(`erwp_ubind_cancelRun`). -/
theorem erwpK_ubind_cancelRun {V : ι → ι → Prop} {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down)
    {fl : ι → Life} {T₁ : ι → OpTabK ι} (hT₁ : ∀ x, (T₁ x).Down)
    (hT₁e : ∀ x m i en, T₁ x m i = some en → en.abort = false ∧ en.q = .lin) {R : Nat → WProp}
    (N D : Val)
    (hD : ∀ x k ls ρ, R k ρ →
      rwp (ℍ := ℍ) (Φ x) (fun _ _ _ ρ' => ρ' = PMap.empty) k ls (.app (.val D) (.val .unit)) ρ) :
    ∀ n x ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => cancelTabRK (fl z) (T₁ z) R)
        (fun _ _ _ _ _ => False) x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T₁ z)) (fun _ _ _ _ _ => False) x n ls
        ((ubK N D).plug e) ρ := by
  have hL : ∀ z, (cancelTabRK (fl z) (T₁ z) R).Local := fun z => cancelTabRK_local _ _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ h
  have hPD := erwpPostK_down (V := V x) (cancelTabK_down (lo := fl x) (hT₁ x))
    (Q := fun _ _ _ _ _ => False) (fun _ => falsePost_down)
  rw [erwpK_eq]
  refine rwpG_bind (hΦ x) (ubK N D) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwpK_unfold_at hL le_rfl h)
  rcases ht with ⟨_, _, _, _, hf⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K', err, hp⟩
  · exact hf.elim
  · -- a finaliser's stop passes the frame
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    have hKo : ((ubK N D).comp K₁).HasHnd m = false := by simp [hasHnd_comp, hK₁]
    have ht' : (ubK N D).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubK N D).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨(ubK N D).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
        ⟨ρa, ρk, hcak, hA, hu, f, hf, fun y hy ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
          fun hq' => absurd (hT₁e x _ _ en hT).2 hq'⟩⟩⟩))
    rw [Kont.plug_comp]
    have hc := (hcont y hy ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
    simp only [erwpCK, show k' < n by omega, if_true] at hc ⊢
    exact ih k' (by omega) y _ _ _ hc
  · -- the cancel's `raise`: `[finalise-cancel]`, `D` consumes the claim, `[cfin-ret]`
    obtain ⟨⟨rfl, hK'⟩, y1, y2, hy, ⟨τa, τb, hcab, herr, hnb⟩, hR⟩ := pure_sep_iff.mp hp
    cases err with
    | some E =>
        obtain ⟨m, j, w, en, he⟩ := herr
        obtain ⟨⟨-, hTe, ha⟩, -⟩ := pure_sep_iff.mp he
        exact absurd ha (by rw [(hT₁e x _ _ en hTe).1]; simp)
    | none =>
    obtain rfl : τa = PMap.empty := herr.1
    obtain rfl := eq_of_compS_empty_left hcab
    refine rwpG_det (hΦ x) (hPD _)
      (fun μ => step1Only_plug (Head.ufinC μ N D none K' hK') rfl .hole) ?_
    rw [Kont.plug_hole, ← cfK_plug]
    refine rwpG_bind (hΦ x) (cfK _) ?_
    have hDr := rwpG_frame (fun _ τ => NoOwn τ) (fun _ _ _ _ h => h) (ResU.CompS.comm hy)
      (rwp_iff_rwpG.mp (hD x k ls' y2 hR)) hnb
    refine rwpG_mono_le (fun k₂ hk₂ ls₂ t₂ σ₂ ht₂ => ?_) hDr
    obtain ⟨σa, σb, hcσ, ⟨w, rfl, rfl⟩, hnσb⟩ := ht₂
    obtain rfl := eq_of_compS_empty_left hcσ
    refine rwpG_det (hΦ x) (hPD _) (fun μ => step1Only_plug (Head.cfret μ none w) rfl .hole) ?_
    have hfin : ∀ μ, Final (ℍ := ℍ) μ (Kont.hole.plug (opE true (cancelVal none))) :=
      final_opPlug (payloadName_cancelVal none) (by simp [OpFree, Kont.Catches])
    exact rwpG_here hfin (Or.inr (Or.inr ⟨.hole, none, pure_sep_mk ⟨rfl, rfl⟩
      ⟨PMap.empty, σ₂, compS_empty_left _, emp_empty, hnσb⟩⟩))

/-- `erwp_ubind_cancelRun` from `erwpK_ubind_cancelRun`. -/
theorem erwp_ubind_cancelRun_of_K {Φ : LocFam} (hΦ : Φ.Down) {T₁ : OpTabN} (hT₁ : T₁.Down)
    (hT₁e : ∀ m i en, T₁ m i = some en → en.abort = false ∧ en.q = .lin) {R : Nat → WProp}
    (N D : Val)
    (hD : ∀ k ls ρ, R k ρ →
      rwp (ℍ := ℍ) Φ (fun _ _ _ ρ' => ρ' = PMap.empty) k ls (.app (.val D) (.val .unit)) ρ) :
    ∀ n ls x ρ, erwp (ℍ := ℍ) Φ (cancelTabR T₁ R) (fun _ _ _ _ => False) n ls x ρ →
      erwp (ℍ := ℍ) Φ (cancelTabN T₁) (fun _ _ _ _ => False) n ls ((ubK N D).plug x) ρ := by
  intro n ls x ρ h
  rw [erwp_eq_erwpK_of (cancelTabRK_lift 0 T₁ R) Φ _] at h
  rw [erwp_eq_erwpK_of (cancelTabK_lift 0 T₁) Φ _]
  exact erwpK_ubind_cancelRun (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Φ) (fun _ => hΦ)
    (fl := fun _ => 0) (T₁ := fun _ => liftTabK T₁) (fun _ => hT₁.liftK)
    (fun _ m i en h => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h
      exact hT₁e m i en₀ h₀) N D (fun _ => hD) n () ls x ρ h

/-- **The finaliser frame around a body at `erwpK`** (`erwp_ubindClaim`). The body's table `Ti`
is the outer `To` but for the cancel obligations; a cancellable stop's, the body's, is the outer
one's around the frame (`hcan`), read at the resumption world. -/
theorem erwpK_ubindClaim {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down) (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life}
    {Ti To : ι → OpTabK ι} (hTD : ∀ x, (To x).Down)
    (hTV : ∀ x y, V x y → (opTableK (fl y) (To y)).Le (opTableK (fl x) (To x)))
    (hTw : ∀ x m i en, Ti x m i = some en → ∃ en', To x m i = some en' ∧ en'.q = en.q ∧
      en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧ en'.wk = en.wk)
    (hab : ∀ x m i en, Ti x m i = some en → en.abort = false)
    (N D : Val)
    (hcan : ∀ x m i en en', Ti x m i = some en → To x m i = some en' → en.q ≠ .lin →
      ∀ y k ls (K₁ : Kont) ρ, cancelOKK en y k ls K₁ ρ →
        cancelOKK en' y k ls ((ubK N D).comp K₁) ρ)
    {Qin Qout : ι → PostN} (hQout : ∀ y, (Qout y).Down)
    (hN : ∀ y k ls (v : Val) ρ, Qin y k ls v ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (To z)) Qout y k ls
        (.app (.val N) (.val v)) ρ) :
    ∀ n x ls M ρ, erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Ti z)) Qin x n ls M ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (To z)) Qout x n ls
        (ubindE (.pair N D) M) ρ := by
  have hL : ∀ z, (opTableK (fl z) (Ti z)).Local := fun z => opTableK_local _ _
  have hLo : ∀ z, (opTableK (fl z) (To z)).Local := fun z => opTableK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls M ρ h
  have hPD := erwpPostK_down (V := V x) (opTableK_down (lo := fl x) (hTD x)) hQout
  rw [← ubK_plug, erwpK_eq]
  refine rwpG_bind (hΦ x) (ubK N D) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwpK_unfold_at hL le_rfl h)
  rcases ht with ⟨v, rfl, y, hy, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · -- `[then]`, at the world the body's value was posted at
    have hstep := fun μ => then_ret (ℍ := ℍ) μ N D v .hole
    simp only [Kont.plug_hole] at hstep
    exact rwpG_det (hΦ x) (hPD _) hstep
      (erwpK_shift hVt hΦV hTV hLo hy hk (hN y k ls' v σ hv))
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hT', hq, hab', hPA, hPB, hwc, hwk⟩ := hTw x m i en hT
    have hKo : ((ubK N D).comp K₁).HasHnd m = false := by simp [hasHnd_comp, hK₁]
    have ht' : (ubK N D).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubK N D).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨(ubK N D).comp K₁, m, i, v, en', pure_sep_mk ⟨rfl, hKo, hT', hab'.trans ha⟩
        ⟨ρa, ρk, hcak, hPA ▸ hA, fun hu' => hu (hq ▸ hu'), f, hf, fun y hy ls'' he =>
          ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hql => ?_⟩⟩⟩))
    · rw [Kont.plug_comp]
      rw [hwk] at hy; rw [hwc] at he; rw [hPB] at hB
      have hc := (hcont y hy ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpCK, show k' < n by omega, if_true] at hc ⊢
      exact ih k' (by omega) y _ _ _ hc
    · rw [hwk] at hy; rw [hwc] at he
      have hql' : en.q ≠ .lin := hq ▸ hql
      exact hcan x m i en en' hT hT' hql' y k ls'' K₁ ρk ((hcont y hy ls'' he).2 hql')
  · obtain ⟨⟨-, -, hT, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd ha (by rw [hab x m i en hT]; simp)

/-- At one world, the cancel obligations of `claimT` pass to the outer table's around the
finaliser frame, given the cancel run's transfer `hrun`. -/
theorem claimT_canK {Φ : LocFam} {T T₁ : OpTabN}
    (hTe : ∀ m i en, T m i = some en → en.abort = false ∧ en.q ≠ .unr)
    (hfin : ∀ m i en, T m i = some en → en.q = .cancel →
      en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁))
    {R : Nat → WProp} {N D : Val}
    (hrun : ∀ n ls x ρ, erwp (ℍ := ℍ) Φ (cancelTabR T₁ R) (fun _ _ _ _ => False) n ls x ρ →
      erwp (ℍ := ℍ) Φ (cancelTabN T₁) (fun _ _ _ _ => False) n ls ((ubK N D).plug x) ρ) :
    ∀ (_ : Unit) m i en en', liftTabK (@OpTabN.claimT ℍ _ T Φ T₁ R) m i = some en →
      liftTabK T m i = some en' → en.q ≠ .lin → ∀ y k ls (K₁ : Kont) ρ,
        cancelOKK en y k ls K₁ ρ → cancelOKK en' y k ls ((ubK N D).comp K₁) ρ := by
  intro _ m i en en' h' h'' hql y k ls' K₁ ρ' hc
  obtain ⟨en₁, h₁, rfl⟩ := liftTabK_some h'
  obtain ⟨en₀, h₀, rfl⟩ := claimT_some h₁
  obtain ⟨en₀', h₀', rfl⟩ := liftTabK_some h''
  rw [h₀] at h₀'
  cases Option.some.inj h₀'
  by_cases hqc : en₀.q = .cancel
  · rw [if_pos hqc] at hc
    refine (cancelOKK_liftEntK en₀ k ls' ((ubK N D).comp K₁) ρ').mpr fun P hP => ?_
    rw [hfin m i en₀ h₀ hqc] at hP
    cases hP
    have hin := (cancelOKK_liftEntK _ k ls' K₁ ρ').mp hc _ rfl
    show erwp (ℍ := ℍ) Φ (cancelTabN T₁) (fun _ _ _ _ => False) k ls'
      (((ubK N D).comp K₁).dead.plug _) ρ'
    rw [dead_comp, ubK_dead, Kont.plug_comp]
    exact hrun k ls' _ ρ' hin
  · rw [if_neg hqc] at hql
    exfalso
    have := (hTe m i en₀ h₀).2
    simp only [liftEntK] at hql
    cases h : en₀.q <;> simp_all

/-- `erwp_ubindClaim` from `erwpK_ubindClaim`. -/
theorem erwp_ubindClaim_of_K {Φ : LocFam} (hΦ : Φ.Down) {T T₁ : OpTabN} (hTD : T.Down)
    (hT₁ : T₁.Down) (hT₁e : ∀ m i en, T₁ m i = some en → en.abort = false ∧ en.q = .lin)
    (hTe : ∀ m i en, T m i = some en → en.abort = false ∧ en.q ≠ .unr)
    (hfin : ∀ m i en, T m i = some en → en.q = .cancel →
      en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁))
    {R : Nat → WProp} (N D : Val)
    (hD : ∀ k ls ρ, R k ρ →
      rwp (ℍ := ℍ) Φ (fun _ _ _ ρ' => ρ' = PMap.empty) k ls (.app (.val D) (.val .unit)) ρ)
    {Qin Qout : PostN} (hQout : Qout.Down)
    (hN : ∀ k ls (v : Val) ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Qout k ls (.app (.val N) (.val v)) ρ) :
    ∀ n ls M ρ, erwp (ℍ := ℍ) Φ (opTableN (@OpTabN.claimT ℍ _ T Φ T₁ R)) Qin n ls M ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Qout n ls (ubindE (.pair N D) M) ρ := by
  intro n ls M ρ h
  rw [erwp_opTableN_eq_erwpK 0] at h ⊢
  refine erwpK_ubindClaim (ℍ := ℍ) (V := fun _ _ => True) (fun _ _ _ _ _ => trivial)
    (Φ := fun _ => Φ) (fun _ => hΦ) (fun _ _ _ => rfl) (fl := fun _ => 0)
    (Ti := fun _ => liftTabK (@OpTabN.claimT ℍ _ T Φ T₁ R)) (To := fun _ => liftTabK T)
    (fun _ => hTD.liftK) (fun _ _ _ _ _ _ _ _ h => h) ?_ ?_ N D ?_ (fun _ => hQout) ?_ n () ls M ρ h
  · intro _ m i en h'
    obtain ⟨en₁, h₁, rfl⟩ := liftTabK_some h'
    obtain ⟨en₀, h₀, rfl⟩ := claimT_some h₁
    refine ⟨liftEntK en₀, liftTabK_of_some h₀, ?_⟩
    by_cases hqc : en₀.q = .cancel <;> simp [hqc, liftEntK]
  · intro _ m i en h'
    obtain ⟨en₁, h₁, rfl⟩ := liftTabK_some h'
    obtain ⟨en₀, h₀, rfl⟩ := claimT_some h₁
    have := (hTe m i en₀ h₀).1
    by_cases hqc : en₀.q = .cancel <;> simp [hqc, liftEntK, this]
  · exact claimT_canK hTe hfin (erwp_ubind_cancelRun_of_K hΦ hT₁ hT₁e N D hD)
  · intro y k ls' v ρ' hv
    rw [← erwp_opTableN_eq_erwpK 0]
    exact hN k ls' v ρ' hv

theorem OpTabK.Down.pa_leK {T : OpTabK ι} (hT : T.Down) {n i : UInt32} {en : OpEntK ι}
    (h : T n i = some en) {m k : Nat} (hmk : m ≤ k) {ls : List SRec} {v : Val} {ρ : WRes}
    (hk : en.PA k ls v ρ) : en.PA m ls v ρ := by
  induction hmk with
  | refl => exact hk
  | step _ ih => exact ih (hT.pa _ _ _ h _ _ _ _ hk)

/-- **The finaliser frame around a body whose raises carry `R`, at `erwpK`** (`erwp_ubindRaise`). -/
theorem erwpK_ubindRaise {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down) (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life}
    {T : ι → OpTabK ι} (hTD : ∀ x, (T x).Down)
    (hTV : ∀ x y, V x y → (opTableK (fl y) (T y)).Le (opTableK (fl x) (T x)))
    (hTe : ∀ x m i en, T x m i = some en → en.abort = false → en.q = .lin)
    (hTr : ∀ x m i en, T x m i = some en → en.abort = true → m ≠ 0)
    (hPAls : ∀ x m i en, T x m i = some en → ∀ k ls ls' v ρ, (∀ a, a ∈ ls' ↔ a ∈ ls) →
      en.PA k ls v ρ → en.PA k ls' v ρ)
    {R : Nat → WProp} (N D : Val)
    (hD : ∀ x k ls ρ, R k ρ → rwp (ℍ := ℍ) (Φ x) (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty)
      k ls (.app (.val D) (.val .unit)) ρ)
    {Qin Qout : ι → PostN} (hQout : ∀ y, (Qout y).Down)
    (hN : ∀ y k ls (v : Val) ρ, Qin y k ls v ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Qout y k ls
        (.app (.val N) (.val v)) ρ) :
    ∀ n x ls M ρ, erwpK (ℍ := ℍ) V Φ (fun z => opTableRK (fl z) (T z) R) Qin x n ls M ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Qout x n ls
        (ubindE (.pair N D) M) ρ := by
  have hL : ∀ z, (opTableRK (fl z) (T z) R).Local := fun z => opTableRK_local _ _ _
  have hLo : ∀ z, (opTableK (fl z) (T z)).Local := fun z => opTableK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls M ρ h
  have hPD := erwpPostK_down (V := V x) (opTableK_down (lo := fl x) (hTD x)) hQout
  rw [← ubK_plug, erwpK_eq]
  refine rwpG_bind (hΦ x) (ubK N D) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwpK_unfold_at hL le_rfl h)
  rcases ht with ⟨v, rfl, y, hy, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · -- `[then]`, at the world the body's value was posted at
    have hstep := fun μ => then_ret (ℍ := ℍ) μ N D v .hole
    simp only [Kont.plug_hole] at hstep
    exact rwpG_det (hΦ x) (hPD _) hstep
      (erwpK_shift hVt hΦV hTV hLo hy hk (hN y k ls' v σ hv))
  · -- a stop passes the frame
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    have hKo : ((ubK N D).comp K₁).HasHnd m = false := by simp [hasHnd_comp, hK₁]
    have ht' : (ubK N D).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubK N D).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨(ubK N D).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
        ⟨ρa, ρk, hcak, hA, hu, f, hf, fun y hy ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
          fun hql => absurd (hTe x m i en hT ha) hql⟩⟩⟩))
    rw [Kont.plug_comp]
    have hc := (hcont y hy ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
    simp only [erwpCK, show k' < n by omega, if_true] at hc ⊢
    exact ih k' (by omega) y _ _ _ hc
  · -- `[finalise]`: `D (); raise p`, `D` consuming the claim
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, σ₁, ρR, hcσ, ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩, hR⟩ :=
      pure_sep_iff.mp hp
    have hm0 := hTr x m i en hT ha
    refine rwpG_det (hΦ x) (hPD _)
      (fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm0 hK₁ .hole).1) ?_
    rw [Kont.plug_hole]
    refine rwpG_bind (hΦ x) _ ?_
    have hDr := rwpG_frame
      (fun ls₀ τ => (∀ a, a ∈ ls₀ ↔ a ∈ ls') ∧
        ((fun ρ => en.PA k ls' v ρ ∧ NoOwn ρ) ⋆ (fun ρ => NoOwn ρ)) τ)
      (fun _ _ hs _ ⟨h₁, h₂⟩ => ⟨fun a => (hs a).trans (h₁ a), h₂⟩) (ResU.CompS.comm hcσ)
      (rwp_iff_rwpG.mp (hD x k ls' ρR hR)) ⟨fun _ => Iff.rfl, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩
    refine rwpG_mono_le (fun k₂ hk₂ ls₂ t₂ σ₂ ht₂ => ?_) hDr
    obtain ⟨σa, σb, hcσ', ⟨w, rfl, rfl, rfl⟩, hls₂, ⟨τa, τn, hcτ, ⟨hPAτ, hnτ⟩, hnn'⟩⟩ := ht₂
    obtain rfl := eq_of_compS_empty_left hcσ'
    refine rwpG_det (hΦ x) (hPD _)
      (fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm0 hK₁ .hole).2.2) ?_
    exact rwpG_here (final_opPlug (K := .hole) (r := true) (payloadName_opPayload m i v)
      (by simp [OpFree, Kont.Catches])) (Or.inr (Or.inr ⟨.hole, m, i, v, en,
        pure_sep_mk ⟨rfl, rfl, hT, ha⟩ ⟨τa, τn, hcτ, ⟨(hTD x).pa_leK hT hk₂
          (hPAls x _ _ _ hT _ _ _ _ _ hls₂ hPAτ), hnτ⟩, hnn'⟩⟩))

/-- `erwp_ubindRaise` from `erwpK_ubindRaise`. -/
theorem erwp_ubindRaise_of_K {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (hTD : T.Down)
    (hTe : ∀ m i en, T m i = some en → en.abort = false → en.q = .lin)
    (hTr : ∀ m i en, T m i = some en → en.abort = true → m ≠ 0)
    (hPAls : ∀ m i en, T m i = some en → ∀ k ls ls' v ρ, (∀ x, x ∈ ls' ↔ x ∈ ls) →
      en.PA k ls v ρ → en.PA k ls' v ρ)
    {R : Nat → WProp} (N D : Val)
    (hD : ∀ k ls ρ, R k ρ → rwp (ℍ := ℍ) Φ (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
      (.app (.val D) (.val .unit)) ρ)
    {Qin Qout : PostN} (hQout : Qout.Down)
    (hN : ∀ k ls (v : Val) ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Qout k ls (.app (.val N) (.val v)) ρ) :
    ∀ n ls M ρ, erwp (ℍ := ℍ) Φ (opTableR T R) Qin n ls M ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Qout n ls (ubindE (.pair N D) M) ρ := by
  intro n ls M ρ h
  rw [erwp_eq_erwpK_of (opTableRK_lift 0 T R) Φ _] at h
  rw [erwp_opTableN_eq_erwpK 0]
  refine erwpK_ubindRaise (ℍ := ℍ) (V := fun _ _ => True) (fun _ _ _ _ _ => trivial)
    (Φ := fun _ => Φ) (fun _ => hΦ) (fun _ _ _ => rfl) (fl := fun _ => 0)
    (T := fun _ => liftTabK T) (fun _ => hTD.liftK) (fun _ _ _ _ _ _ _ _ h => h) ?_ ?_ ?_ N D
    (fun _ => hD) (fun _ => hQout) ?_ n () ls M ρ h
  · intro _ m i en h'
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h'
    exact hTe m i en₀ h₀
  · intro _ m i en h'
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h'
    exact hTr m i en₀ h₀
  · intro _ m i en h'
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h'
    exact hPAls m i en₀ h₀
  · intro y k ls' v ρ' hv
    rw [← erwp_opTableN_eq_erwpK 0]
    exact hN k ls' v ρ' hv

/-- **A cancel run under a finaliser frame owning `ρ_D`, at `erwpK`** (`cancelOblN_ubind`): still a
cancel run. The frame joins the continuation's share at a stop, so the entries' list order and
world order pass to a part of the share (`hwcl`, `hwk`). -/
theorem cancelOblNK_ubind {V : ι → ι → Prop} {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down)
    {fl : ι → Life} {T₁ : ι → OpTabK ι} (hT₁ : ∀ x, (T₁ x).Down)
    (hwcl : ∀ x m i en, T₁ x m i = some en → ∀ ls ls' (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
      en.wc ls ls' ρ → en.wc ls ls' ρ₁)
    (hwk : ∀ x m i en, T₁ x m i = some en → ∀ f y (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
      ResU.Valid ρ → en.wk f y ρ → en.wk f y ρ₁)
    (hT₁e : ∀ x m i en, T₁ x m i = some en → en.abort = false ∧ en.q = .lin) (N D : Val)
    {ρD : WRes} (hD : ∀ x, FinOK (ℍ := ℍ) (Φ x) D ρD) :
    ∀ n x ls e ρ X, ResU.CompS ρ ρD X →
      erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T₁ z)) (fun _ _ _ _ _ => False) x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T₁ z)) (fun _ _ _ _ _ => False) x n ls
        ((ubK N D).plug e) X := by
  have hL : ∀ z, (cancelTabK (fl z) (T₁ z)).Local := fun z => cancelTabK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ X hX h
  have hPD := erwpPostK_down (V := V x) (cancelTabK_down (lo := fl x) (hT₁ x))
    (Q := fun _ _ _ _ _ => False) (fun _ => falsePost_down)
  rw [erwpK_eq]
  refine rwpG_bind (hΦ x) (ubK N D) ?_
  have hfr := rwpG_frame (fun _ τ => τ = ρD) (fun _ _ _ _ h => h) hX
    (erwpK_unfold_at hL le_rfl h) rfl
  refine rwpG_mono_le (fun k hk ls' t σ ⟨⟨σ₁, σ₂, hσ, ht, hσ₂⟩, hvσ⟩ => ?_)
    (rwpG_validK hfr)
  rw [hσ₂] at hσ
  rcases ht with ⟨_, _, _, _, hf⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K', err, hp⟩
  · exact hf.elim
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    have hq := (hT₁e x _ _ en hT).2
    obtain ⟨ρkD, hkD, haX⟩ := (ResU.CompS.assoc ρa ρk ρD σ).mpr ⟨σ₁, hcak, hσ⟩
    have hKo : ((ubK N D).comp K₁).HasHnd m = false := by simp [hasHnd_comp, hK₁]
    have ht' : (ubK N D).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubK N D).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨(ubK N D).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
        ⟨ρa, ρkD, haX, hA, fun hu' => absurd (hq.symm.trans hu') (by simp), f, hf,
          fun y hy ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
            fun hq' => absurd hq hq'⟩⟩⟩))
    have he' : en.wc ls' ls'' ρk := hwcl x _ _ _ hT _ _ _ _ _ hkD he
    have hy' : en.wk f y ρk := hwk x _ _ _ hT _ _ _ _ _ hkD (ResU.Valid.split haX hvσ).2 hy
    obtain ⟨z, hz, hzτ⟩ := compS_exch hkD hcτ
    have hc := (hcont y hy' ls'' he').1 k' hk' w τ₁ z hB hz
    simp only [erwpCK, show k' < n by omega, if_true] at hc ⊢
    rw [Kont.plug_comp]
    exact ih k' (by omega) y _ _ _ _ hzτ hc
  · obtain ⟨⟨rfl, hK'⟩, τa, τb, hcab, herr, hnb⟩ := pure_sep_iff.mp hp
    cases err with
    | some E =>
        obtain ⟨m, j, w, en, he⟩ := herr
        obtain ⟨⟨-, hTe, ha⟩, -⟩ := pure_sep_iff.mp he
        exact absurd ha (by rw [(hT₁e x _ _ en hTe).1]; simp)
    | none =>
    obtain rfl : τa = PMap.empty := herr.1
    obtain rfl := eq_of_compS_empty_left hcab
    refine rwpG_det (hΦ x) (hPD _)
      (fun μ => step1Only_plug (Head.ufinC μ N D none K' hK') rfl .hole) ?_
    rw [Kont.plug_hole, ← cfK_plug]
    refine rwpG_bind (hΦ x) (cfK _) ?_
    have hDr := rwpG_frame (fun _ τ => NoOwn τ) (fun _ _ _ _ h => h) (ResU.CompS.comm hσ)
      (rwp_iff_rwpG.mp (hD x k ls')) hnb
    refine rwpG_mono_le (fun k₂ hk₂ ls₂ t₂ σ₂ ht₂ => ?_) hDr
    obtain ⟨σa, σb, hcσ, ⟨w, rfl, -, rfl⟩, hnσb⟩ := ht₂
    obtain rfl := eq_of_compS_empty_left hcσ
    refine rwpG_det (hΦ x) (hPD _) (fun μ => step1Only_plug (Head.cfret μ none w) rfl .hole) ?_
    have hfin : ∀ μ, Final (ℍ := ℍ) μ (Kont.hole.plug (opE true (cancelVal none))) :=
      final_opPlug (payloadName_cancelVal none) (by simp [OpFree, Kont.Catches])
    exact rwpG_here hfin (Or.inr (Or.inr ⟨.hole, none, pure_sep_mk ⟨rfl, rfl⟩
      ⟨PMap.empty, σ₂, compS_empty_left _, emp_empty, hnσb⟩⟩))

/-- `cancelOblN_ubind` from `cancelOblNK_ubind`. -/
theorem cancelOblN_ubind_of_K {Φ : LocFam} (hΦ : Φ.Down) {T₁ : OpTabN} (hT₁ : T₁.Down)
    (hT₁e : ∀ m i en, T₁ m i = some en → en.abort = false ∧ en.q = .lin) (N D : Val) {ρD : WRes}
    (hD : FinOK (ℍ := ℍ) Φ D ρD) :
    ∀ n ls x ρ X, ResU.CompS ρ ρD X → cancelOblN (ℍ := ℍ) Φ T₁ n ls x ρ →
      cancelOblN (ℍ := ℍ) Φ T₁ n ls ((ubK N D).plug x) X := by
  intro n ls x ρ X hX h
  show erwp (ℍ := ℍ) Φ _ _ _ _ _ _
  have h' : erwp (ℍ := ℍ) Φ (cancelTabN T₁) (fun _ _ _ _ => False) n ls x ρ := h
  rw [erwp_eq_erwpK_of (cancelTabK_lift 0 T₁) Φ _] at h' ⊢
  exact cancelOblNK_ubind (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Φ) (fun _ => hΦ)
    (fl := fun _ => 0) (T₁ := fun _ => liftTabK T₁) (fun _ => hT₁.liftK)
    (fun _ m i en h₁ => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
      exact hT₁.wcl m i en₀ h₀)
    (fun _ m i en h₁ _ _ _ _ _ _ _ _ => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
      trivial)
    (fun _ m i en h₁ => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
      exact hT₁e m i en₀ h₀) N D (fun _ => hD) n () ls x ρ X hX h'

/-- **The finaliser frame at `erwpK`** (`erwp_ubind`). At a stop the frame's `ρ_D` joins the
continuation's share; the outer entry owes, at a world, at that share, what the body's owes at its
own part (`hperf`), and its cancel obligation is the body's around the frame. -/
theorem erwpK_ubind {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down) (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life}
    {Tin Tout : ι → OpTabK ι} (hToutD : ∀ x, (Tout x).Down)
    (hTV : ∀ x y, V x y → (opTableK (fl y) (Tout y)).Le (opTableK (fl x) (Tout x)))
    (hwcl : ∀ x m i en, Tin x m i = some en → ∀ ls ls' (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
      en.wc ls ls' ρ → en.wc ls ls' ρ₁)
    {Qin Qout : ι → PostN} (hQout : ∀ y, (Qout y).Down) (N D : Val) {ρD : WRes}
    (hD : ∀ x, FinOK (ℍ := ℍ) (Φ x) D ρD)
    (hN : ∀ y k ls (v : Val) ρ X, ResU.CompS ρ ρD X → Qin y k ls v ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout y k ls
        (.app (.val N) (.val v)) X)
    (hperf : ∀ x m i en, Tin x m i = some en → en.abort = false → ∃ en', Tout x m i = some en' ∧
      en'.q = en.q ∧ en'.abort = false ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
      (∀ f y ρk X, ResU.CompS ρk ρD X → en'.wk f y X → en.wk f y ρk) ∧
      ∀ y k ls K ρk X, ResU.CompS ρk ρD X → cancelOKK en y k ls K ρk →
        cancelOKK en' y k ls ((ubK N D).comp K) X)
    (hunr : ∀ x m i en, Tin x m i = some en → en.q ≠ .unr)
    (hrais : ∀ x m i en, Tin x m i = some en → en.abort = true → m ≠ 0 ∧ ∃ en',
      Tout x m i = some en' ∧ en'.abort = true ∧ (∀ k ls v ρ, en.PA k ls v ρ → en'.PA k ls v ρ) ∧
      ∀ k ls ls' v ρ, (∀ a, a ∈ ls' ↔ a ∈ ls) → en'.PA k ls v ρ → en'.PA k ls' v ρ) :
    ∀ n x ls M ρ X, ResU.CompS ρ ρD X →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tin z)) Qin x n ls M ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (Tout z)) Qout x n ls
        (ubindE (.pair N D) M) X := by
  have hL : ∀ z, (opTableK (fl z) (Tin z)).Local := fun z => opTableK_local _ _
  have hLo : ∀ z, (opTableK (fl z) (Tout z)).Local := fun z => opTableK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls M ρ X hX h
  have hPD := erwpPostK_down (V := V x) (opTableK_down (lo := fl x) (hToutD x)) hQout
  rw [← ubK_plug, erwpK_eq]
  refine rwpG_bind (hΦ x) (ubK N D) ?_
  have hfr := rwpG_frame (fun _ τ => τ = ρD) (fun _ _ _ _ h => h) hX
    (erwpK_unfold_at hL le_rfl h) rfl
  refine rwpG_mono_le (fun k hk ls' t σ ⟨σ₁, σ₂, hσ, ht, hσ₂⟩ => ?_) hfr
  rw [hσ₂] at hσ
  rcases ht with ⟨v, rfl, y, hy, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · -- `[then]`, at the world the body's value was posted at
    have hstep := fun μ => then_ret (ℍ := ℍ) μ N D v .hole
    simp only [Kont.plug_hole] at hstep
    exact rwpG_det (hΦ x) (hPD _) hstep
      (erwpK_shift hVt hΦV hTV hLo hy hk (hN y k ls' v σ₁ σ hσ hv))
  · -- a stop passes the frame
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hT', hq', ha', hPA', hPB', hwc', hwk', hcan⟩ := hperf x m i en hT ha
    obtain ⟨ρkD, hkD, haX⟩ := (ResU.CompS.assoc ρa ρk ρD σ).mpr ⟨σ₁, hcak, hσ⟩
    have hKo : ((ubK N D).comp K₁).HasHnd m = false := by simp [hasHnd_comp, hK₁]
    have ht' : (ubK N D).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubK N D).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨(ubK N D).comp K₁, m, i, v, en', pure_sep_mk ⟨rfl, hKo, hT', ha'⟩
        ⟨ρa, ρkD, haX, hPA' ▸ hA,
          fun hu' => absurd (hq'.symm.trans hu') (hunr x m i en hT), f, hf,
          fun y hy ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hq'' => ?_⟩⟩⟩))
    · have he' : en.wc ls' ls'' ρk := by
        rw [hwc'] at he; exact hwcl x _ _ _ hT _ _ _ _ _ hkD he
      rw [hPB'] at hB
      obtain ⟨z, hz, hzτ⟩ := compS_exch hkD hcτ
      have hc := (hcont y (hwk' f y ρk ρkD hkD hy) ls'' he').1 k' hk' w τ₁ z hB hz
      simp only [erwpCK, show k' < n by omega, if_true] at hc ⊢
      rw [Kont.plug_comp]
      exact ih k' (by omega) y _ _ _ _ hzτ hc
    · have he' : en.wc ls' ls'' ρk := by
        rw [hwc'] at he; exact hwcl x _ _ _ hT _ _ _ _ _ hkD he
      exact hcan y k ls'' K₁ ρk ρkD hkD
        ((hcont y (hwk' f y ρk ρkD hkD hy) ls'' he').2 (hq' ▸ hq''))
  · -- `[finalise]`: `D (); raise p`
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    obtain ⟨hm0, en', hT', ha', hPA', hPAls⟩ := hrais x m i en hT ha
    refine rwpG_det (hΦ x) (hPD _)
      (fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm0 hK₁ .hole).1) ?_
    rw [Kont.plug_hole]
    refine rwpG_bind (hΦ x) _ ?_
    have hDr := rwpG_frame
      (fun ls₀ τ => (∀ a, a ∈ ls₀ ↔ a ∈ ls') ∧
        ((fun ρ => en.PA k ls' v ρ ∧ NoOwn ρ) ⋆ (fun ρ => NoOwn ρ)) τ)
      (fun _ _ hs _ ⟨h₁, h₂⟩ => ⟨fun a => (hs a).trans (h₁ a), h₂⟩) (ResU.CompS.comm hσ)
      (rwp_iff_rwpG.mp (hD x k ls')) ⟨fun _ => Iff.rfl, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩
    refine rwpG_mono_le (fun k₂ hk₂ ls₂ t₂ σ₂ ht₂ => ?_) hDr
    obtain ⟨σa, σb, hcσ, ⟨w, rfl, rfl, rfl⟩, hls₂, ⟨τa, τn, hcτ, ⟨hPAτ, hnτ⟩, hnn'⟩⟩ := ht₂
    obtain rfl := eq_of_compS_empty_left hcσ
    refine rwpG_det (hΦ x) (hPD _)
      (fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm0 hK₁ .hole).2.2) ?_
    exact rwpG_here (final_opPlug (K := .hole) (r := true) (payloadName_opPayload m i v)
      (by simp [OpFree, Kont.Catches])) (Or.inr (Or.inr ⟨.hole, m, i, v, en',
        pure_sep_mk ⟨rfl, rfl, hT', ha'⟩ ⟨τa, τn, hcτ, ⟨(hToutD x).pa_leK hT' hk₂
          (hPAls _ _ _ _ _ hls₂ (hPA' _ _ _ _ hPAτ)), hnτ⟩, hnn'⟩⟩))

/-- `erwp_ubind` from `erwpK_ubind`. -/
theorem erwp_ubind_of_K {Φ : LocFam} (hΦ : Φ.Down) {Tin Tout : OpTabN} (hToutD : Tout.Down)
    (hTinD : Tin.Down) {Qin Qout : PostN} (hQout : Qout.Down) (N D : Val) {ρD : WRes}
    (hD : FinOK (ℍ := ℍ) Φ D ρD)
    (hN : ∀ k ls (v : Val) ρ X, ResU.CompS ρ ρD X → Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val N) (.val v)) X)
    (hperf : ∀ m i en, Tin m i = some en → en.abort = false → ∃ en', Tout m i = some en' ∧
      en'.q = en.q ∧ en'.abort = false ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
      ∀ k ls K ρk X, ResU.CompS ρk ρD X → cancelOKN en k ls K ρk →
        cancelOKN en' k ls ((ubK N D).comp K) X)
    (hunr : ∀ m i en, Tin m i = some en → en.q ≠ .unr)
    (hrais : ∀ m i en, Tin m i = some en → en.abort = true → m ≠ 0 ∧ ∃ en', Tout m i = some en' ∧
      en'.abort = true ∧ (∀ k ls v ρ, en.PA k ls v ρ → en'.PA k ls v ρ) ∧
      ∀ k ls ls' v ρ, (∀ x, x ∈ ls' ↔ x ∈ ls) → en'.PA k ls v ρ → en'.PA k ls' v ρ) :
    ∀ n ls M ρ X, ResU.CompS ρ ρD X → erwp (ℍ := ℍ) Φ (opTableN Tin) Qin n ls M ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout n ls (ubindE (.pair N D) M) X := by
  intro n ls M ρ X hX h
  rw [erwp_opTableN_eq_erwpK 0] at h ⊢
  refine erwpK_ubind (ℍ := ℍ) (V := fun _ _ => True) (fun _ _ _ _ _ => trivial)
    (Φ := fun _ => Φ) (fun _ => hΦ) (fun _ _ _ => rfl) (fl := fun _ => 0)
    (Tin := fun _ => liftTabK Tin) (Tout := fun _ => liftTabK Tout) (fun _ => hToutD.liftK)
    (fun _ _ _ _ _ _ _ _ h => h) ?_ (fun _ => hQout) N D (fun _ => hD) ?_ ?_ ?_ ?_ n () ls M ρ X
    hX h
  · intro _ m i en h₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hTinD.wcl m i en₀ h₀
  · intro y k ls' v ρ' X' hX' hv
    rw [← erwp_opTableN_eq_erwpK 0]
    exact hN k ls' v ρ' X' hX' hv
  · intro _ m i en h₁ ha
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    obtain ⟨en', hT', hq, ha', hPA, hPB, hwc, hcan⟩ := hperf m i en₀ h₀ ha
    refine ⟨liftEntK en', liftTabK_of_some hT', hq, ha', hPA, ?_, hwc,
      fun _ _ _ _ _ _ => trivial, fun _ k ls' K ρk X' hX' hc => ?_⟩
    · show (fun _ => en'.PB) = fun _ => en₀.PB
      rw [hPB]
    · exact (cancelOKK_liftEntK en' k ls' _ X').mpr
        (hcan k ls' K ρk X' hX' ((cancelOKK_liftEntK en₀ k ls' K ρk).mp hc))
  · intro _ m i en h₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hunr m i en₀ h₀
  · intro _ m i en h₁ ha
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    obtain ⟨hm0, en', hT', ha', hPA, hPAls⟩ := hrais m i en₀ h₀ ha
    exact ⟨hm0, liftEntK en', liftTabK_of_some hT', ha', hPA, hPAls⟩

/-! ### A finaliser that performs, on the cancel path -/

/-- **`cfin cancel (D ())` as a cancel run at `erwpK`** (`erwp_cfin_run`). The part `g` beside
`D ()`'s run rides into each of its stops' continuation shares, so the entries' list order and
world order pass to a part of the share (`hwcl`, `hwk`). -/
theorem erwpK_cfin_run {V : ι → ι → Prop} {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down)
    {fl : ι → Life} {T₁ : ι → OpTabK ι} (hT₁ : ∀ x, (T₁ x).Down)
    (hwcl : ∀ x m i en, T₁ x m i = some en → ∀ ls ls' (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
      en.wc ls ls' ρ → en.wc ls ls' ρ₁)
    (hwk : ∀ x m i en, T₁ x m i = some en → ∀ f y (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
      ResU.Valid ρ → en.wk f y ρ → en.wk f y ρ₁)
    (hT₁e : ∀ x m i en, T₁ x m i = some en → en.abort = false ∧ en.q = .lin) :
    ∀ n x ls e (ρ g σ : WRes), ResU.CompS ρ g σ → NoOwn g →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T₁ z))
        (fun _ _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T₁ z)) (fun _ _ _ _ _ => False) x n ls
        ((cfK (cancelVal none)).plug e) σ := by
  have hL : ∀ z, (opTableK (fl z) (T₁ z)).Local := fun z => opTableK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ g σ hc hg h
  have hPD := erwpPostK_down (V := V x) (cancelTabK_down (lo := fl x) (hT₁ x))
    (Q := fun _ _ _ _ _ => False) (fun _ => falsePost_down)
  rw [erwpK_eq] at h ⊢
  refine rwpG_bind (hΦ x) (cfK _) ?_
  refine rwpG_mono_le (fun k hk ls' t τ ⟨⟨τ₁, τ₂, hτ, ht, hτ₂⟩, hvτ⟩ => ?_)
    (rwpG_validK (rwpG_frame (fun _ τ => NoOwn τ) (fun _ _ _ _ h => h) hc h hg))
  rcases ht with ⟨w, rfl, -, -, rfl, rfl⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · -- `D ()` answered: `[cfin-ret]`
    obtain rfl := eq_of_compS_empty_left hτ
    refine rwpG_det (hΦ x) (hPD _)
      (fun μ => step1Only_plug (Head.cfret μ none Val.unit) rfl .hole) ?_
    have hfin : ∀ μ, Final (ℍ := ℍ) μ (Kont.hole.plug (opE true (cancelVal none))) :=
      final_opPlug (payloadName_cancelVal none) (by simp [OpFree, Kont.Catches])
    exact rwpG_here hfin (Or.inr (Or.inr ⟨.hole, none, pure_sep_mk ⟨rfl, rfl⟩
      ⟨PMap.empty, _, compS_empty_left _, emp_empty, hτ₂⟩⟩))
  · -- a stop of `D ()`: a stop of the cancel run, the part riding in its share
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    have hql := (hT₁e x m i en hT).2
    have hKo : ((cfK (cancelVal none)).comp K₁).HasHnd m = false := by
      simp [hasHnd_comp, hK₁, cfK, Kont.HasHnd]
    have ht' : (cfK (cancelVal none)).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((cfK (cancelVal none)).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    obtain ⟨ρk₂, hk₂, haσ⟩ := (ResU.CompS.assoc ρa ρk τ₂ τ).mpr ⟨τ₁, hcak, hτ⟩
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨(cfK (cancelVal none)).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
        ⟨ρa, ρk₂, haσ, hA, fun hu' => absurd (hql.symm.trans hu') (by simp), f, hf,
          fun y hy ls'' he => ⟨fun k' hk' w σ₁ σ₂ hB hcσ => ?_, fun hq' => absurd hql hq'⟩⟩⟩))
    have he' : en.wc ls' ls'' ρk := hwcl x _ _ _ hT _ _ _ _ _ hk₂ he
    have hy' : en.wk f y ρk := hwk x _ _ _ hT _ _ _ _ _ hk₂ (ResU.Valid.split haσ hvτ).2 hy
    obtain ⟨z, hz, hzσ⟩ := compS_exch hk₂ hcσ
    have hc' := (hcont y hy' ls'' he').1 k' hk' w σ₁ z hB hz
    rw [Kont.plug_comp]
    simp only [erwpCK, show k' < n by omega, if_true] at hc' ⊢
    exact ih k' (by omega) y ls'' _ z τ₂ σ₂ hzσ hτ₂ hc'
  · obtain ⟨⟨-, -, hT, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd ha (by rw [(hT₁e x m i en hT).1]; simp)

/-- `erwp_cfin_run` from `erwpK_cfin_run`. -/
theorem erwp_cfin_run_of_K {Φ : LocFam} (hΦ : Φ.Down) {T₁ : OpTabN} (hT₁ : T₁.Down)
    (hT₁e : ∀ m i en, T₁ m i = some en → en.abort = false ∧ en.q = .lin) :
    ∀ n ls x (ρ g σ : WRes), ResU.CompS ρ g σ → NoOwn g →
      erwp (ℍ := ℍ) Φ (opTableN T₁) (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) n ls x ρ →
      erwp (ℍ := ℍ) Φ (cancelTabN T₁) (fun _ _ _ _ => False) n ls
        ((cfK (cancelVal none)).plug x) σ := by
  intro n ls x ρ g σ hc hg h
  rw [erwp_opTableN_eq_erwpK 0] at h
  rw [erwp_eq_erwpK_of (cancelTabK_lift 0 T₁) Φ _]
  exact erwpK_cfin_run (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Φ) (fun _ => hΦ)
    (fl := fun _ => 0) (T₁ := fun _ => liftTabK T₁) (fun _ => hT₁.liftK)
    (fun _ m i en h₁ => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
      exact hT₁.wcl m i en₀ h₀)
    (fun _ m i en h₁ _ _ _ _ _ _ _ _ => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
      trivial)
    (fun _ m i en h₁ => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
      exact hT₁e m i en₀ h₀) n () ls x ρ g σ hc hg h

/-- **`erwpK_ubind_cancelRun` with a finaliser that performs** (`erwp_ubind_cancelRunF`): `D ()`
at `erwpK` at the cancel run's table, at every world the cancel run reaches. -/
theorem erwpK_ubind_cancelRunF {V : ι → ι → Prop} {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down)
    {fl : ι → Life} {T₁ : ι → OpTabK ι} (hT₁ : ∀ x, (T₁ x).Down)
    (hwcl : ∀ x m i en, T₁ x m i = some en → ∀ ls ls' (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
      en.wc ls ls' ρ → en.wc ls ls' ρ₁)
    (hwk : ∀ x m i en, T₁ x m i = some en → ∀ f y (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
      ResU.Valid ρ → en.wk f y ρ → en.wk f y ρ₁)
    (hT₁e : ∀ x m i en, T₁ x m i = some en → en.abort = false ∧ en.q = .lin) {R : Nat → WProp}
    (N D : Val)
    (hD : ∀ x k ls ρ, R k ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T₁ z))
        (fun _ _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) x k ls (.app (.val D) (.val .unit)) ρ) :
    ∀ n x ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => cancelTabRK (fl z) (T₁ z) R)
        (fun _ _ _ _ _ => False) x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T₁ z)) (fun _ _ _ _ _ => False) x n ls
        ((ubK N D).plug e) ρ := by
  have hL : ∀ z, (cancelTabRK (fl z) (T₁ z) R).Local := fun z => cancelTabRK_local _ _ _
  have hLc : ∀ z, (cancelTabK (fl z) (T₁ z)).Local := fun z => cancelTabK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ h
  have hPD := erwpPostK_down (V := V x) (cancelTabK_down (lo := fl x) (hT₁ x))
    (Q := fun _ _ _ _ _ => False) (fun _ => falsePost_down)
  rw [erwpK_eq]
  refine rwpG_bind (hΦ x) (ubK N D) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwpK_unfold_at hL le_rfl h)
  rcases ht with ⟨_, _, _, _, hf⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K', err, hp⟩
  · exact hf.elim
  · -- a finaliser's stop passes the frame
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    have hKo : ((ubK N D).comp K₁).HasHnd m = false := by simp [hasHnd_comp, hK₁]
    have ht' : (ubK N D).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubK N D).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨(ubK N D).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
        ⟨ρa, ρk, hcak, hA, hu, f, hf, fun y hy ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
          fun hq' => absurd (hT₁e x _ _ en hT).2 hq'⟩⟩⟩))
    rw [Kont.plug_comp]
    have hc := (hcont y hy ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
    simp only [erwpCK, show k' < n by omega, if_true] at hc ⊢
    exact ih k' (by omega) y _ _ _ hc
  · -- the cancel's `raise`: `[finalise-cancel]`, `D` consumes the claim, `[cfin-ret]`
    obtain ⟨⟨rfl, hK'⟩, y1, y2, hy, ⟨τa, τb, hcab, herr, hnb⟩, hR⟩ := pure_sep_iff.mp hp
    cases err with
    | some E =>
        obtain ⟨m, j, w, en, he⟩ := herr
        obtain ⟨⟨-, hTe, ha⟩, -⟩ := pure_sep_iff.mp he
        exact absurd ha (by rw [(hT₁e x _ _ en hTe).1]; simp)
    | none =>
    obtain rfl : τa = PMap.empty := herr.1
    obtain rfl := eq_of_compS_empty_left hcab
    refine rwpG_det (hΦ x) (hPD _)
      (fun μ => step1Only_plug (Head.ufinC μ N D none K' hK') rfl .hole) ?_
    rw [Kont.plug_hole, ← cfK_plug]
    exact erwpK_unfold_at hLc hk
      (erwpK_cfin_run hΦ hT₁ hwcl hwk hT₁e k x ls' _ y2 y1 σ (ResU.CompS.comm hy) hnb
        (hD x k ls' y2 hR))

/-- `erwp_ubind_cancelRunF` from `erwpK_ubind_cancelRunF`. -/
theorem erwp_ubind_cancelRunF_of_K {Φ : LocFam} (hΦ : Φ.Down) {T₁ : OpTabN} (hT₁ : T₁.Down)
    (hT₁e : ∀ m i en, T₁ m i = some en → en.abort = false ∧ en.q = .lin) {R : Nat → WProp}
    (N D : Val)
    (hD : ∀ k ls ρ, R k ρ →
      erwp (ℍ := ℍ) Φ (opTableN T₁) (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
        (.app (.val D) (.val .unit)) ρ) :
    ∀ n ls x ρ, erwp (ℍ := ℍ) Φ (cancelTabR T₁ R) (fun _ _ _ _ => False) n ls x ρ →
      erwp (ℍ := ℍ) Φ (cancelTabN T₁) (fun _ _ _ _ => False) n ls ((ubK N D).plug x) ρ := by
  intro n ls x ρ h
  rw [erwp_eq_erwpK_of (cancelTabRK_lift 0 T₁ R) Φ _] at h
  rw [erwp_eq_erwpK_of (cancelTabK_lift 0 T₁) Φ _]
  refine erwpK_ubind_cancelRunF (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Φ) (fun _ => hΦ)
    (fl := fun _ => 0) (T₁ := fun _ => liftTabK T₁) (fun _ => hT₁.liftK)
    (fun _ m i en h₁ => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
      exact hT₁.wcl m i en₀ h₀)
    (fun _ m i en h₁ _ _ _ _ _ _ _ _ => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
      trivial)
    (fun _ m i en h₁ => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
      exact hT₁e m i en₀ h₀) N D (fun _ k ls' ρ' hR => ?_) n () ls x ρ h
  have h' := hD k ls' ρ' hR
  rw [erwp_opTableN_eq_erwpK 0] at h'
  exact h'

/-- `erwp_ubindClaimF` from `erwpK_ubindClaim`: the cancel path's transfer is
`erwp_ubind_cancelRunF`'s. -/
theorem erwp_ubindClaimF_of_K {Φ : LocFam} (hΦ : Φ.Down) {T T₁ : OpTabN} (hTD : T.Down)
    (hT₁ : T₁.Down) (hT₁e : ∀ m i en, T₁ m i = some en → en.abort = false ∧ en.q = .lin)
    (hTe : ∀ m i en, T m i = some en → en.abort = false ∧ en.q ≠ .unr)
    (hfin : ∀ m i en, T m i = some en → en.q = .cancel →
      en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁))
    {R : Nat → WProp} (N D : Val)
    (hD : ∀ k ls ρ, R k ρ →
      erwp (ℍ := ℍ) Φ (opTableN T₁) (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls
        (.app (.val D) (.val .unit)) ρ)
    {Qin Qout : PostN} (hQout : Qout.Down)
    (hN : ∀ k ls (v : Val) ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Qout k ls (.app (.val N) (.val v)) ρ) :
    ∀ n ls M ρ, erwp (ℍ := ℍ) Φ (opTableN (@OpTabN.claimT ℍ _ T Φ T₁ R)) Qin n ls M ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Qout n ls (ubindE (.pair N D) M) ρ := by
  intro n ls M ρ h
  rw [erwp_opTableN_eq_erwpK 0] at h ⊢
  refine erwpK_ubindClaim (ℍ := ℍ) (V := fun _ _ => True) (fun _ _ _ _ _ => trivial)
    (Φ := fun _ => Φ) (fun _ => hΦ) (fun _ _ _ => rfl) (fl := fun _ => 0)
    (Ti := fun _ => liftTabK (@OpTabN.claimT ℍ _ T Φ T₁ R)) (To := fun _ => liftTabK T)
    (fun _ => hTD.liftK) (fun _ _ _ _ _ _ _ _ h => h) ?_ ?_ N D
    (claimT_canK hTe hfin (erwp_ubind_cancelRunF_of_K hΦ hT₁ hT₁e N D hD)) (fun _ => hQout) ?_
    n () ls M ρ h
  · intro _ m i en h'
    obtain ⟨en₁, h₁, rfl⟩ := liftTabK_some h'
    obtain ⟨en₀, h₀, rfl⟩ := claimT_some h₁
    refine ⟨liftEntK en₀, liftTabK_of_some h₀, ?_⟩
    by_cases hqc : en₀.q = .cancel <;> simp [hqc, liftEntK]
  · intro _ m i en h'
    obtain ⟨en₁, h₁, rfl⟩ := liftTabK_some h'
    obtain ⟨en₀, h₀, rfl⟩ := claimT_some h₁
    have := (hTe m i en₀ h₀).1
    by_cases hqc : en₀.q = .cancel <;> simp [hqc, liftEntK, this]
  · intro y k ls' v ρ' hv
    rw [← erwp_opTableN_eq_erwpK 0]
    exact hN k ls' v ρ' hv

/-! ### A finaliser that performs, on the raise path -/

/-- **The frame at `erwpK`, across must-resume stops** (`erwp_frameL`). The frame `R`, read at a
world, owns nothing; at a stop it joins the continuation's share, so the entries' list order and
world order pass to a part of the share (`hwcl`, `hwk`), and it is read again at the resumption
world (`hRk`, the order read at the joint share); a value is posted with it at the world the
run chose (`hRV`). -/
theorem erwpK_frameL {V : ι → ι → Prop} {Φ : ι → LocFam} {fl : ι → Life} {T : ι → OpTabK ι}
    (hwcl : ∀ x m i en, T x m i = some en → ∀ ls ls' (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
      en.wc ls ls' ρ → en.wc ls ls' ρ₁)
    (hwk : ∀ x m i en, T x m i = some en → ∀ f y (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
      ResU.Valid ρ → en.wk f y ρ → en.wk f y ρ₁)
    (hq : ∀ x m i en, T x m i = some en → en.abort = false → en.q = .lin)
    {Q : ι → PostN} (R : ι → List SRec → WProp)
    (hR : ∀ x ls ls', (∀ a, a ∈ ls' ↔ a ∈ ls) → ∀ ρ, R x ls ρ → R x ls' ρ)
    (hRwc : ∀ x m i en, T x m i = some en → en.abort = false → ∀ ls ls' (ρk ρ₂ ρ : WRes),
      ResU.CompS ρk ρ₂ ρ → en.wc ls ls' ρ → R x ls ρ₂ → R x ls' ρ₂)
    (hRk : ∀ x m i en, T x m i = some en → en.abort = false → ∀ f y ls (ρk ρ₂ ρ : WRes),
      ResU.CompS ρk ρ₂ ρ → en.wk f y ρ → R x ls ρ₂ → R y ls ρ₂)
    (hRV : ∀ x y, V x y → ∀ ls ρ, R x ls ρ → R y ls ρ)
    (hRno : ∀ x ls ρ, R x ls ρ → NoOwn ρ) :
    ∀ n x ls e (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ → R x ls ρ₂ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q x n ls e ρ₁ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z))
        (fun y k ls' v => Q y k ls' v ⋆ R y ls') x n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ₁ ρ₂ ρ hc hR₂ h
  rw [erwpK_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ⟨⟨σ₁, σ₂, hσ, ht, hσ₂⟩, hvσ⟩ => ?_)
    (rwpG_validK (rwpG_frame (R x) (hR x) hc h hR₂))
  rcases ht with ⟨v, rfl, y, hy, hv⟩ | ⟨K, m, i, v, en, hp⟩ | ⟨K, m, i, v, en, hp⟩
  · exact Or.inl ⟨v, rfl, y, hy, σ₁, σ₂, hσ, hv, hRV x y hy ls' σ₂ hσ₂⟩
  · obtain ⟨⟨rfl, hK, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    have hql := hq x m i en hT ha
    obtain ⟨ρk₂, hk₂, haσ⟩ := (ResU.CompS.assoc ρa ρk σ₂ σ).mpr ⟨σ₁, hcak, hσ⟩
    refine Or.inr (Or.inl ⟨K, m, i, v, en, pure_sep_mk ⟨rfl, hK, hT, ha⟩ ⟨ρa, ρk₂, haσ, hA,
      fun hu' => absurd (hql.symm.trans hu') (by simp), f, hf, fun y hy ls'' he =>
        ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hq' => absurd hql hq'⟩⟩⟩)
    have he' : en.wc ls' ls'' ρk := hwcl x _ _ _ hT _ _ _ _ _ hk₂ he
    have hy' : en.wk f y ρk := hwk x _ _ _ hT _ _ _ _ _ hk₂ (ResU.Valid.split haσ hvσ).2 hy
    obtain ⟨z, hz, hzτ⟩ := compS_exch hk₂ hcτ
    have hc' := (hcont y hy' ls'' he').1 k' hk' w τ₁ z hB hz
    simp only [erwpCK, show k' < n by omega, if_true] at hc' ⊢
    exact ih k' (by omega) y ls'' _ z σ₂ τ₂ hzτ
      (hRk x m i en hT ha f y ls'' ρk σ₂ ρk₂ hk₂ hy
        (hRwc x m i en hT ha ls' ls'' ρk σ₂ ρk₂ hk₂ he hσ₂)) hc'
  · obtain ⟨hpur, τa, τn, hcan, hPA, hnn⟩ := pure_sep_iff.mp hp
    obtain ⟨τn₂, hn₂, haσ⟩ := (ResU.CompS.assoc τa τn σ₂ σ).mpr ⟨σ₁, hcan, hσ⟩
    exact Or.inr (Or.inr ⟨K, m, i, v, en, pure_sep_mk hpur
      ⟨τa, τn₂, haσ, hPA, noOwn_compS hn₂ hnn (hRno _ _ _ hσ₂)⟩⟩)

/-- `erwp_frameL` from `erwpK_frameL`. -/
theorem erwp_frameL_of_K {Φ : LocFam} {T : OpTabN} (hTD : T.Down)
    (hq : ∀ m i en, T m i = some en → en.abort = false → en.q = .lin)
    {Q : PostN} (R : List SRec → WProp)
    (hR : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ ρ, R ls ρ → R ls' ρ)
    (hRwc : ∀ m i en, T m i = some en → en.abort = false → ∀ ls ls' (ρk ρ₂ ρ : WRes),
      ResU.CompS ρk ρ₂ ρ → en.wc ls ls' ρ → R ls ρ₂ → R ls' ρ₂)
    (hRno : ∀ ls ρ, R ls ρ → NoOwn ρ) :
    ∀ n ls e (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ → R ls ρ₂ →
      erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ₁ →
      erwp (ℍ := ℍ) Φ (opTableN T) (fun k ls' v => Q k ls' v ⋆ R ls') n ls e ρ := by
  intro n ls e ρ₁ ρ₂ ρ hc hR₂ h
  rw [erwp_opTableN_eq_erwpK 0] at h ⊢
  exact erwpK_frameL (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Φ) (fl := fun _ => 0)
    (T := fun _ => liftTabK T) (Q := fun _ => Q)
    (fun _ m i en h₁ => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
      exact hTD.wcl m i en₀ h₀)
    (fun _ m i en h₁ _ _ _ _ _ _ _ _ => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
      trivial)
    (fun _ m i en h₁ => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
      exact hq m i en₀ h₀) (fun _ => R) (fun _ => hR)
    (fun _ m i en h₁ => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
      exact hRwc m i en₀ h₀) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    (fun _ => hRno) n () ls e ρ₁ ρ₂ ρ hc hR₂ h

/-- **The finaliser frame around a body whose raises carry `R`, the finaliser performing, at
`erwpK`** (`erwp_ubindRaiseF`). At `[finalise]` `D ()` runs from the world of the `raise`; the
`raise` goes on at the world `D ()`'s value is posted at. So the abortive entry, with its payload,
is read again at each world `D ()` reaches: across its stops (`hTk`) and at its post (`hTVr`). -/
theorem erwpK_ubindRaiseF {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down) (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life}
    {T : ι → OpTabK ι} (hTD : ∀ x, (T x).Down)
    (hTV : ∀ x y, V x y → (opTableK (fl y) (T y)).Le (opTableK (fl x) (T x)))
    (hwcl : ∀ x m i en, T x m i = some en → ∀ ls ls' (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
      en.wc ls ls' ρ → en.wc ls ls' ρ₁)
    (hwk : ∀ x m i en, T x m i = some en → ∀ f y (ρ₁ ρ₂ ρ : WRes), ResU.CompS ρ₁ ρ₂ ρ →
      ResU.Valid ρ → en.wk f y ρ → en.wk f y ρ₁)
    (hTe : ∀ x m i en, T x m i = some en → en.abort = false → en.q = .lin ∧ en.wc = extF)
    (hfinN : ∀ x m i en, T x m i = some en → en.fin = none)
    (hTr : ∀ x m i en, T x m i = some en → en.abort = true → m ≠ 0)
    (hPAls : ∀ x m i en, T x m i = some en → ∀ k ls ls' v ρ, extF ls ls' ρ →
      en.PA k ls v ρ → en.PA k ls' v ρ)
    (hTk : ∀ x m' i' en', T x m' i' = some en' → en'.abort = false → ∀ f y (ρa ρb ρ : WRes),
      ResU.CompS ρa ρb ρ → en'.wk f y ρ → ∀ m i en, T x m i = some en → en.abort = true →
        ∃ en'', T y m i = some en'' ∧ en''.abort = true ∧
          ∀ k ls v, en.PA k ls v ρa → en''.PA k ls v ρa)
    (hTVr : ∀ x y, V x y → ∀ m i en, T x m i = some en → en.abort = true → ∃ en'',
      T y m i = some en'' ∧ en''.abort = true ∧ ∀ k ls v ρ, en.PA k ls v ρ → en''.PA k ls v ρ)
    {R : Nat → WProp} (N D : Val)
    (hD : ∀ x k ls ρ, R k ρ → erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z))
      (fun _ _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) x k ls (.app (.val D) (.val .unit)) ρ)
    {Qin Qout : ι → PostN} (hQout : ∀ y, (Qout y).Down)
    (hN : ∀ y k ls (v : Val) ρ, Qin y k ls v ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Qout y k ls
        (.app (.val N) (.val v)) ρ) :
    ∀ n x ls M ρ, erwpK (ℍ := ℍ) V Φ (fun z => opTableRK (fl z) (T z) R) Qin x n ls M ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Qout x n ls
        (ubindE (.pair N D) M) ρ := by
  have hL : ∀ z, (opTableRK (fl z) (T z) R).Local := fun z => opTableRK_local _ _ _
  have hLo : ∀ z, (opTableK (fl z) (T z)).Local := fun z => opTableK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls M ρ h
  have hPD := erwpPostK_down (V := V x) (opTableK_down (lo := fl x) (hTD x)) hQout
  rw [← ubK_plug, erwpK_eq]
  refine rwpG_bind (hΦ x) (ubK N D) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwpK_unfold_at hL le_rfl h)
  rcases ht with ⟨v, rfl, y, hy, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · -- `[then]`, at the world the body's value was posted at
    have hstep := fun μ => then_ret (ℍ := ℍ) μ N D v .hole
    simp only [Kont.plug_hole] at hstep
    exact rwpG_det (hΦ x) (hPD _) hstep
      (erwpK_shift hVt hΦV hTV hLo hy hk (hN y k ls' v σ hv))
  · -- a stop passes the frame
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    have hKo : ((ubK N D).comp K₁).HasHnd m = false := by simp [hasHnd_comp, hK₁]
    have ht' : (ubK N D).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubK N D).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨(ubK N D).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
        ⟨ρa, ρk, hcak, hA, hu, f, hf, fun y hy ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
          fun hql => absurd (hTe x m i en hT ha).1 hql⟩⟩⟩))
    rw [Kont.plug_comp]
    have hc := (hcont y hy ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
    simp only [erwpCK, show k' < n by omega, if_true] at hc ⊢
    exact ih k' (by omega) y _ _ _ hc
  · -- `[finalise]`: `D (); raise p`, `D` consuming the claim, its stops passing the `raise`
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, σ₁, ρR, hcσ, ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩, hR⟩ :=
      pure_sep_iff.mp hp
    have hm0 := hTr x m i en hT ha
    refine rwpG_det (hΦ x) (hPD _)
      (fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm0 hK₁ .hole).1) ?_
    rw [Kont.plug_hole]
    refine erwpK_unfold_at hLo hk ?_
    -- the `raise`'s entry, read at a world, beside its payload
    set Fr : ι → List SRec → WProp := fun z ls₀ τ => ∃ en₀, T z m i = some en₀ ∧
      en₀.abort = true ∧ ((fun ρ => en₀.PA k ls₀ v ρ ∧ NoOwn ρ) ⋆ (fun ρ => NoOwn ρ)) τ with hFr
    have hFrT : ∀ z, (∃ en₀, T z m i = some en₀ ∧ en₀.abort = true ∧
        ∀ k ls v ρ, en.PA k ls v ρ → en₀.PA k ls v ρ) → ∀ ls₀ τ,
        ((fun ρ => en.PA k ls₀ v ρ ∧ NoOwn ρ) ⋆ (fun ρ => NoOwn ρ)) τ → Fr z ls₀ τ := by
      rintro z ⟨en₀, h₀, ha₀, hP₀⟩ ls₀ τ ⟨τa, τn, hcτ, ⟨hPAτ, hn⟩, hnn⟩
      exact ⟨en₀, h₀, ha₀, τa, τn, hcτ, ⟨hP₀ _ _ _ _ hPAτ, hn⟩, hnn⟩
    have hDr := erwpK_frameL hwcl hwk (fun x m i en h ha => (hTe x m i en h ha).1) Fr
      (fun z _ _ hs _ ⟨en₀, h₀, ha₀, τa, τn, hcτ, ⟨hPAτ, hn⟩, hnn⟩ =>
        ⟨en₀, h₀, ha₀, τa, τn, hcτ, ⟨hPAls z _ _ _ h₀ _ _ _ _ _ (extF_of_same hs τa) hPAτ, hn⟩,
          hnn⟩)
      (fun x' m' i' en' h ha' ls₁ ls₂ ρk ρ₂ ρ₃ hc₃ he
          ⟨en₀, h₀, ha₀, τa, τn, hcτ, ⟨hPAτ, hn⟩, hnn⟩ => by
        rw [(hTe x' m' i' en' h ha').2] at he
        exact ⟨en₀, h₀, ha₀, τa, τn, hcτ, ⟨hPAls x' _ _ _ h₀ _ _ _ _ _
          (extF_left _ _ _ _ _ hcτ (extF_right hc₃ he)) hPAτ, hn⟩, hnn⟩)
      (fun x' m' i' en' h ha' f y ls₀ ρk ρ₂ ρ₃ hc₃ hy ⟨en₀, h₀, ha₀, hrest⟩ => by
        obtain ⟨τa, τn, hcτ, ⟨hPAτ, hn⟩, hnn⟩ := hrest
        obtain ⟨X, -, hX⟩ := compS_reassoc hcτ (ResU.CompS.comm hc₃)
        obtain ⟨en'', h'', ha'', hP''⟩ := hTk x' m' i' en' h ha' f y τa X ρ₃ hX hy m i en₀ h₀ ha₀
        exact ⟨en'', h'', ha'', τa, τn, hcτ, ⟨hP'' _ _ _ hPAτ, hn⟩, hnn⟩)
      (fun x' y hxy ls₀ τ ⟨en₀, h₀, ha₀, hrest⟩ => by
        obtain ⟨en'', h'', ha'', hP''⟩ := hTVr x' y hxy m i en₀ h₀ ha₀
        obtain ⟨τa, τn, hcτ, ⟨hPAτ, hn⟩, hnn⟩ := hrest
        exact ⟨en'', h'', ha'', τa, τn, hcτ, ⟨hP'' _ _ _ _ hPAτ, hn⟩, hnn⟩)
      (fun _ _ _ ⟨_, _, _, τa, τn, hcτ, ⟨_, hnA'⟩, hnn'⟩ => noOwn_compS hcτ hnA' hnn')
      k x ls' _ ρR σ₁ σ (ResU.CompS.comm hcσ)
      (hFrT x ⟨en, hT, ha, fun _ _ _ _ h => h⟩ ls' σ₁ ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩)
      (hD x k ls' ρR hR)
    refine erwpK_bind_le hVt hΦ hΦV hTV _ (fun m => by simp [Kont.HasHnd])
      (then_fin (ℍ := ℍ) (μ := fun _ => none) (i := i) N D v hm0 hK₁ .hole).2.1
      (fun x' m' i' en' P h hP => by rw [hfinN x' m' i' en' h] at hP; cases hP) k ?_ k le_rfl
      x ls' _ σ hDr
    rintro y k₂ ls₂ w σ₂ hk₂
      ⟨σa, σb, hcσ', ⟨rfl, rfl⟩, en₀, h₀, ha₀, τa, τn, hcτ, ⟨hPAτ, hnτ⟩, hnn'⟩
    obtain rfl := eq_of_compS_empty_left hcσ'
    refine erwpK_det (hΦ y) (opTableK_down (hTD y)) hQout
      (fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm0 hK₁ .hole).2.2) ?_
    rw [Kont.plug_hole, erwpK_eq]
    exact rwpG_here (final_opPlug (K := .hole) (r := true) (payloadName_opPayload m i v)
      (by simp [OpFree, Kont.Catches])) (Or.inr (Or.inr ⟨.hole, m, i, v, en₀,
        pure_sep_mk ⟨rfl, rfl, h₀, ha₀⟩ ⟨τa, τn, hcτ, ⟨(hTD y).pa_leK h₀ hk₂
          hPAτ, hnτ⟩, hnn'⟩⟩))

/-- `erwp_ubindRaiseF` from `erwpK_ubindRaiseF`. -/
theorem erwp_ubindRaiseF_of_K {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (hTD : T.Down)
    (hTe : ∀ m i en, T m i = some en → en.abort = false → en.q = .lin ∧ en.wc = extF)
    (hfinN : ∀ m i en, T m i = some en → en.fin = none)
    (hTr : ∀ m i en, T m i = some en → en.abort = true → m ≠ 0)
    (hPAls : ∀ m i en, T m i = some en → ∀ k ls ls' v ρ, extF ls ls' ρ →
      en.PA k ls v ρ → en.PA k ls' v ρ)
    {R : Nat → WProp} (N D : Val)
    (hD : ∀ k ls ρ, R k ρ → erwp (ℍ := ℍ) Φ (opTableN T)
      (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls (.app (.val D) (.val .unit)) ρ)
    {Qin Qout : PostN} (hQout : Qout.Down)
    (hN : ∀ k ls (v : Val) ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Qout k ls (.app (.val N) (.val v)) ρ) :
    ∀ n ls M ρ, erwp (ℍ := ℍ) Φ (opTableR T R) Qin n ls M ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Qout n ls (ubindE (.pair N D) M) ρ := by
  intro n ls M ρ h
  rw [erwp_eq_erwpK_of (opTableRK_lift 0 T R) Φ _] at h
  rw [erwp_opTableN_eq_erwpK 0]
  refine erwpK_ubindRaiseF (ℍ := ℍ) (V := fun _ _ => True) (fun _ _ _ _ _ => trivial)
    (Φ := fun _ => Φ) (fun _ => hΦ) (fun _ _ _ => rfl) (fl := fun _ => 0)
    (T := fun _ => liftTabK T) (fun _ => hTD.liftK) (fun _ _ _ _ _ _ _ _ h => h) ?_ ?_ ?_ ?_ ?_ ?_
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ en h ha => ⟨en, h, ha, fun _ _ _ h => h⟩)
    (fun _ _ _ _ _ en h ha => ⟨en, h, ha, fun _ _ _ _ h => h⟩) N D ?_ (fun _ => hQout) ?_
    n () ls M ρ h
  · intro _ m i en h₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hTD.wcl m i en₀ h₀
  · intro _ m i en h₁ _ _ _ _ _ _ _ _
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    trivial
  · intro _ m i en h₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hTe m i en₀ h₀
  · intro _ m i en h₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    simp [liftEntK, hfinN m i en₀ h₀]
  · intro _ m i en h₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hTr m i en₀ h₀
  · intro _ m i en h₁
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hPAls m i en₀ h₀
  · intro _ k ls' ρ' hR'
    have h' := hD k ls' ρ' hR'
    rw [erwp_opTableN_eq_erwpK 0] at h'
    exact h'
  · intro y k ls' v ρ' hv
    rw [← erwp_opTableN_eq_erwpK 0]
    exact hN k ls' v ρ' hv

/-! ### The finaliser frame over cancel runs that stop -/

/-- An abortive entry's payload read lower and at another list: the cancel's error payload
outlasts `D ()`'s run. -/
theorem errOkK_le {T : OpTabK ι}
    (hPAle : ∀ m i en, T m i = some en → en.abort = true → ∀ k k' ls ls' v ρ, k' ≤ k →
      en.PA k ls v ρ → en.PA k' ls' v ρ) {k k' : Nat} (hk : k' ≤ k) {ls ls' : List SRec} :
    ∀ {err : Option Val} {ρ : WRes}, errOkK T k ls err ρ → errOkK T k' ls' err ρ
  | none, _, h => h
  | some _, _, h => by
      obtain ⟨m, j, w, en, he⟩ := h
      obtain ⟨⟨hE, hTe, ha⟩, hPA, hn⟩ := pure_sep_iff.mp he
      exact ⟨m, j, w, en, pure_sep_mk ⟨hE, hTe, ha⟩ ⟨hPAle m j en hTe ha _ _ _ _ _ _ hk hPA, hn⟩⟩

/-- **The finaliser frame over a cancel run that stops, at `erwpK`** (`erwp_ubind_cancelRunCR`).
The cancel run's table `Ti` is the outer `To` but for the cancel obligations; at the cancel's
`raise`, `D` consumes `R` beside the error payload and `[cfin-ret]` re-raises; a cancellable stop's
cancel run passes the frame by `hcan`, read at the resumption world. -/
theorem erwpK_ubind_cancelRunCR {V : ι → ι → Prop} {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down)
    {fl : ι → Life} {Ti To : ι → OpTabK ι} (hToD : ∀ x, (To x).Down)
    (hTw : ∀ x m i en, Ti x m i = some en → ∃ en', To x m i = some en' ∧ en'.q = en.q ∧
      en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧ en'.wk = en.wk)
    (hPAle : ∀ x m i en, To x m i = some en → en.abort = true → ∀ k k' ls ls' v ρ, k' ≤ k →
      en.PA k ls v ρ → en.PA k' ls' v ρ)
    {R : Nat → WProp} (N D : Val)
    (hcan : ∀ x m i en en', Ti x m i = some en → To x m i = some en' → en.q ≠ .lin →
      ∀ y k ls (K₁ : Kont) ρ, cancelOKK en y k ls K₁ ρ →
        cancelOKK en' y k ls ((ubK N D).comp K₁) ρ)
    (hD : ∀ x k ls ρ, R k ρ →
      rwp (ℍ := ℍ) (Φ x) (fun _ _ _ ρ' => ρ' = PMap.empty) k ls (.app (.val D) (.val .unit)) ρ) :
    ∀ n x ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => cancelTabRK (fl z) (Ti z) R)
        (fun _ _ _ _ _ => False) x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (To z)) (fun _ _ _ _ _ => False) x n ls
        ((ubK N D).plug e) ρ := by
  have hL : ∀ z, (cancelTabRK (fl z) (Ti z) R).Local := fun z => cancelTabRK_local _ _ _
  have hTT : ∀ x, (Ti x).Twin (To x) := fun x m i en h => by
    obtain ⟨en', h', h₁, h₂, h₃, h₄, h₅, -⟩ := hTw x m i en h
    exact ⟨en', h', h₁, h₂, h₃, h₄, h₅⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ h
  have hPD := erwpPostK_down (V := V x) (cancelTabK_down (lo := fl x) (hToD x))
    (Q := fun _ _ _ _ _ => False) (fun _ => falsePost_down)
  rw [erwpK_eq]
  refine rwpG_bind (hΦ x) (ubK N D) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwpK_unfold_at hL le_rfl h)
  rcases ht with ⟨_, _, _, _, hf⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K', err, hp⟩
  · exact hf.elim
  · -- a stop passes the frame; a cancellable one's cancel run through the frame
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hT', hq, hab', hPA, hPB, hwc, hwk⟩ := hTw x m i en hT
    have hKo : ((ubK N D).comp K₁).HasHnd m = false := by simp [hasHnd_comp, hK₁]
    have ht' : (ubK N D).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubK N D).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨(ubK N D).comp K₁, m, i, v, en', pure_sep_mk ⟨rfl, hKo, hT', hab'.trans ha⟩
        ⟨ρa, ρk, hcak, hPA ▸ hA, fun hu' => hu (hq ▸ hu'), f, hf, fun y hy ls'' he =>
          ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hql => ?_⟩⟩⟩))
    · rw [Kont.plug_comp]
      rw [hwk] at hy; rw [hwc] at he; rw [hPB] at hB
      have hc := (hcont y hy ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpCK, show k' < n by omega, if_true] at hc ⊢
      exact ih k' (by omega) y _ _ _ hc
    · rw [hwk] at hy; rw [hwc] at he
      have hql' : en.q ≠ .lin := hq ▸ hql
      exact hcan x m i en en' hT hT' hql' y k ls'' K₁ ρk ((hcont y hy ls'' he).2 hql')
  · -- the cancel's `raise`: `[finalise-cancel]`, `D` consumes the claim, `[cfin-ret]`
    obtain ⟨⟨rfl, hK'⟩, y1, y2, hy, hy1, hR⟩ := pure_sep_iff.mp hp
    have hy1' : (errOkK (To x) k ls' err ⋆ fun ρ => NoOwn ρ) y1 := by
      obtain ⟨τa, τb, hcab, herr, hnb⟩ := hy1
      exact ⟨τa, τb, hcab, errOkK_twin (hTT x) herr, hnb⟩
    refine rwpG_det (hΦ x) (hPD _)
      (fun μ => step1Only_plug (Head.ufinC μ N D err K' hK') rfl .hole) ?_
    rw [Kont.plug_hole, ← cfK_plug]
    refine rwpG_bind (hΦ x) (cfK _) ?_
    have hDr := rwpG_frame (fun _ τ => (errOkK (To x) k ls' err ⋆ fun ρ => NoOwn ρ) τ)
      (fun _ _ _ _ h => h) (ResU.CompS.comm hy) (rwp_iff_rwpG.mp (hD x k ls' y2 hR)) hy1'
    refine rwpG_mono_le (fun k₂ hk₂ ls₂ t₂ σ₂ ht₂ => ?_) hDr
    obtain ⟨σa, σb, hcσ, ⟨w, rfl, rfl⟩, hσb⟩ := ht₂
    obtain rfl := eq_of_compS_empty_left hcσ
    refine rwpG_det (hΦ x) (hPD _) (fun μ => step1Only_plug (Head.cfret μ err w) rfl .hole) ?_
    have hfin : ∀ μ, Final (ℍ := ℍ) μ (Kont.hole.plug (opE true (cancelVal err))) :=
      final_opPlug (payloadName_cancelVal err) (by simp [OpFree, Kont.Catches])
    obtain ⟨τa, τb, hcab, herr, hnb⟩ := hσb
    exact rwpG_here hfin (Or.inr (Or.inr ⟨.hole, err, pure_sep_mk ⟨rfl, rfl⟩
      ⟨τa, τb, hcab, errOkK_le (hPAle x) hk₂ herr, hnb⟩⟩))

/-- **The finaliser frame around a body whose table is the outer one but for the cancel
obligations, its raises carrying `R`, at `erwpK`** (`erwp_ubindClaimRT`): `[then]` at a return; at
a stop the frame passes outward, a cancellable stop's cancel obligation by `hcan`; at a `raise`,
`[finalise]` runs `D ()`, which consumes the claim, and the `raise` goes on at the outer table. -/
theorem erwpK_ubindClaimRT {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down) (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life}
    {Ti To : ι → OpTabK ι} (hToD : ∀ x, (To x).Down)
    (hTV : ∀ x y, V x y → (opTableK (fl y) (To y)).Le (opTableK (fl x) (To x)))
    (hTw : ∀ x m i en, Ti x m i = some en → ∃ en', To x m i = some en' ∧ en'.q = en.q ∧
      en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧ en'.wk = en.wk)
    (hPAle : ∀ x m i en, To x m i = some en → en.abort = true → ∀ k k' ls ls' v ρ, k' ≤ k →
      en.PA k ls v ρ → en.PA k' ls' v ρ)
    (hTr : ∀ x m i en, To x m i = some en → en.abort = true → m ≠ 0)
    {R : Nat → WProp} (N D : Val)
    (hcan : ∀ x m i en en', Ti x m i = some en → To x m i = some en' → en.q ≠ .lin →
      ∀ y k ls (K₁ : Kont) ρ, cancelOKK en y k ls K₁ ρ →
        cancelOKK en' y k ls ((ubK N D).comp K₁) ρ)
    (hD : ∀ x k ls ρ, R k ρ → rwp (ℍ := ℍ) (Φ x)
      (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls (.app (.val D) (.val .unit)) ρ)
    {Qin Qout : ι → PostN} (hQout : ∀ y, (Qout y).Down)
    (hN : ∀ y k ls (v : Val) ρ, Qin y k ls v ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (To z)) Qout y k ls
        (.app (.val N) (.val v)) ρ) :
    ∀ n x ls M ρ, erwpK (ℍ := ℍ) V Φ (fun z => opTableRK (fl z) (Ti z) R) Qin x n ls M ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (To z)) Qout x n ls
        (ubindE (.pair N D) M) ρ := by
  have hL : ∀ z, (opTableRK (fl z) (Ti z) R).Local := fun z => opTableRK_local _ _ _
  have hLo : ∀ z, (opTableK (fl z) (To z)).Local := fun z => opTableK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls M ρ h
  have hPD := erwpPostK_down (V := V x) (opTableK_down (lo := fl x) (hToD x)) hQout
  rw [← ubK_plug, erwpK_eq]
  refine rwpG_bind (hΦ x) (ubK N D) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwpK_unfold_at hL le_rfl h)
  rcases ht with ⟨v, rfl, y, hy, hv⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · -- `[then]`, at the world the body's value was posted at
    have hstep := fun μ => then_ret (ℍ := ℍ) μ N D v .hole
    simp only [Kont.plug_hole] at hstep
    exact rwpG_det (hΦ x) (hPD _) hstep
      (erwpK_shift hVt hΦV hTV hLo hy hk (hN y k ls' v σ hv))
  · -- a stop passes the frame; a cancellable one's cancel obligation through the frame
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hT', hq, hab', hPA, hPB, hwc, hwk⟩ := hTw x m i en hT
    have hKo : ((ubK N D).comp K₁).HasHnd m = false := by simp [hasHnd_comp, hK₁]
    have ht' : (ubK N D).plug (K₁.plug (performE (.val (opPayload m i v)))) =
        ((ubK N D).comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨(ubK N D).comp K₁, m, i, v, en', pure_sep_mk ⟨rfl, hKo, hT', hab'.trans ha⟩
        ⟨ρa, ρk, hcak, hPA ▸ hA, fun hu' => hu (hq ▸ hu'), f, hf, fun y hy ls'' he =>
          ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hql => ?_⟩⟩⟩))
    · rw [Kont.plug_comp]
      rw [hwk] at hy; rw [hwc] at he; rw [hPB] at hB
      have hc := (hcont y hy ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpCK, show k' < n by omega, if_true] at hc ⊢
      exact ih k' (by omega) y _ _ _ hc
    · rw [hwk] at hy; rw [hwc] at he
      have hql' : en.q ≠ .lin := hq ▸ hql
      exact hcan x m i en en' hT hT' hql' y k ls'' K₁ ρk ((hcont y hy ls'' he).2 hql')
  · -- `[finalise]`: `D (); raise p`, `D` consuming the claim
    obtain ⟨⟨rfl, hK₁, hT, hab⟩, σ₁, ρR, hcσ, ⟨ρa, ρn, hcan', ⟨hPA, hnA⟩, hnn⟩, hR⟩ :=
      pure_sep_iff.mp hp
    obtain ⟨en', hT', -, hab', hPA', -, -, -⟩ := hTw x m i en hT
    have hab'' : en'.abort = true := hab'.trans hab
    have hm0 := hTr x m i en' hT' hab''
    refine rwpG_det (hΦ x) (hPD _)
      (fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm0 hK₁ .hole).1) ?_
    rw [Kont.plug_hole]
    refine rwpG_bind (hΦ x) _ ?_
    have hDr := rwpG_frame
      (fun _ τ => ((fun ρ => en'.PA k ls' v ρ ∧ NoOwn ρ) ⋆ (fun ρ => NoOwn ρ)) τ)
      (fun _ _ _ _ h => h) (ResU.CompS.comm hcσ)
      (rwp_iff_rwpG.mp (hD x k ls' ρR hR)) ⟨ρa, ρn, hcan', ⟨hPA' ▸ hPA, hnA⟩, hnn⟩
    refine rwpG_mono_le (fun k₂ hk₂ ls₂ t₂ σ₂ ht₂ => ?_) hDr
    obtain ⟨σa, σb, hcσ', ⟨w, rfl, rfl, rfl⟩, ⟨τa, τn, hcτ, ⟨hPAτ, hnτ⟩, hnn'⟩⟩ := ht₂
    obtain rfl := eq_of_compS_empty_left hcσ'
    refine rwpG_det (hΦ x) (hPD _)
      (fun μ => (then_fin (ℍ := ℍ) (μ := μ) (i := i) N D v hm0 hK₁ .hole).2.2) ?_
    exact rwpG_here (final_opPlug (K := .hole) (r := true) (payloadName_opPayload m i v)
      (by simp [OpFree, Kont.Catches])) (Or.inr (Or.inr ⟨.hole, m, i, v, en',
        pure_sep_mk ⟨rfl, rfl, hT', hab''⟩ ⟨τa, τn, hcτ,
          ⟨hPAle x m i en' hT' hab'' _ _ _ _ _ _ hk₂ hPAτ, hnτ⟩, hnn'⟩⟩))

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Kont ubindE Head performE raiseE cancelVal opPayload)

/-- The lifted lender's twin and the lifted row table agree but for the cancel obligations. -/
theorem tabR_tabN_twinLiftK (R : Nat → WProp) (F : CTy) (δ : LSub) (Θ : LocTy)
    (c : Loc → Option Life) :
    ∀ (_ : Unit) m i en, liftTabK (tabR (ℍ := ℍ) R F δ Θ c) m i = some en →
      ∃ en', liftTabK (tabN (ℍ := ℍ) F δ Θ c) m i = some en' ∧ en'.q = en.q ∧
        en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
        en'.wk = en.wk := by
  intro _ m i en h
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h
  obtain ⟨q, A, B, fin, -, rfl, hN, -⟩ := tab_lookupR R F h₀
  exact ⟨_, liftTabK_of_some (hN δ Θ c), rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The lifted row table's abortive payloads are read lower and at every list. -/
theorem tabN_paLeLiftK (F : CTy) (δ : LSub) (Θ : LocTy) (c : Loc → Option Life) :
    ∀ (_ : Unit) m i en, liftTabK (tabN (ℍ := ℍ) F δ Θ c) m i = some en → en.abort = true →
      ∀ k k' ls ls' v ρ, k' ≤ k → en.PA k ls v ρ → en.PA k' ls' v ρ := by
  intro _ m i en h _ k k' ls ls' v ρ hk hPA
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h
  obtain ⟨q, A, B, fin, -, rfl, -⟩ := tab_lookupN F h₀
  exact vN_le hk hPA

/-- At one world, a cancellable stop's cancel run at its cancel row's `tabR` passes the frame to
one at its `tabN`, given that transfer at the cancel row (`hrun`). -/
theorem tabR_ubindCanLiftK {R : Nat → WProp} {F : CTy} {δ : LSub} {Θ : LocTy}
    {c : Loc → Option Life} {N D : Val}
    (hrun : ∀ fin : CTy, fin.cdepth < F.cdepth → ∀ n ls x ρ,
      erwp (ℍ := ℍ) (Θ.view c) (cancelTabR (tabR (ℍ := ℍ) R fin δ Θ c) R) (fun _ _ _ _ => False)
        n ls x ρ →
      erwp (ℍ := ℍ) (Θ.view c) (cancelTabN (tabN (ℍ := ℍ) fin δ Θ c)) (fun _ _ _ _ => False) n
        ls ((ubK N D).plug x) ρ) :
    ∀ (_ : Unit) m i en en', liftTabK (tabR (ℍ := ℍ) R F δ Θ c) m i = some en →
      liftTabK (tabN (ℍ := ℍ) F δ Θ c) m i = some en' → en.q ≠ .lin → ∀ y k ls (K₁ : Kont) ρ,
        cancelOKK en y k ls K₁ ρ → cancelOKK en' y k ls ((ubK N D).comp K₁) ρ := by
  intro _ m i en en' h h' hql y k ls'' K₁ ρk hc
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h
  obtain ⟨en₀', h₀', rfl⟩ := liftTabK_some h'
  obtain ⟨q, A, B, fin, hLy, rfl, hN, -⟩ := tab_lookupR R F h₀
  rw [hN δ Θ c] at h₀'
  cases Option.some.inj h₀'
  refine (cancelOKK_liftEntK _ k ls'' ((ubK N D).comp K₁) ρk).mpr fun P hP => ?_
  have hc' := (cancelOKK_liftEntK _ k ls'' K₁ ρk).mp hc
  have hq' : q ≠ .lin := hql
  by_cases hcap : capB q B = true
  · simp only [entN, hcap, if_true] at hP hc'
    by_cases htop : fin = .top
    · subst htop; simp [finN] at hP
    rw [finN_eq htop] at hP
    cases Option.some.inj hP
    have hin := hc' _ (finR_eq R htop δ Θ c)
    show erwp (ℍ := ℍ) (Θ.view c) (cancelTabN (tabN (ℍ := ℍ) fin δ Θ c)) (fun _ _ _ _ => False)
      k ls'' (((ubK N D).comp K₁).dead.plug _) ρk
    rw [dead_comp, ubK_dead, Kont.plug_comp]
    exact hrun fin (layer_cdepth F hLy) k ls'' _ ρk hin
  · simp [entN, hcap] at hP

/-- `erwp_ubind_cancelRunCR` from `erwpK_ubind_cancelRunCR`, by induction on how deep cancel rows
nest. -/
theorem erwp_ubind_cancelRunCR_of_K {Θ : LocTy} (hΘ : Θ.Down) {c : Loc → Option Life}
    {R : Nat → WProp} (N D : Val)
    (hD : ∀ k ls ρ, R k ρ →
      rwp (ℍ := ℍ) (Θ.view c) (fun _ _ _ ρ' => ρ' = PMap.empty) k ls
        (.app (.val D) (.val .unit)) ρ)
    (δ : LSub) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → ∀ n ls x ρ,
      erwp (ℍ := ℍ) (Θ.view c) (cancelTabR (tabR (ℍ := ℍ) R F δ Θ c) R) (fun _ _ _ _ => False)
        n ls x ρ →
      erwp (ℍ := ℍ) (Θ.view c) (cancelTabN (tabN (ℍ := ℍ) F δ Θ c)) (fun _ _ _ _ => False) n ls
        ((ubK N D).plug x) ρ := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro F hFd n ls x ρ h
  rw [erwp_eq_erwpK_of (cancelTabRK_lift 0 _ R) _ _] at h
  rw [erwp_eq_erwpK_of (cancelTabK_lift 0 _) _ _]
  exact erwpK_ubind_cancelRunCR (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Θ.view c)
    (fun _ => LocTy.view_down hΘ c) (fl := fun _ => 0)
    (Ti := fun _ => liftTabK (tabR (ℍ := ℍ) R F δ Θ c))
    (To := fun _ => liftTabK (tabN (ℍ := ℍ) F δ Θ c))
    (fun _ => (tabN_down F δ Θ hΘ c).liftK) (tabR_tabN_twinLiftK R F δ Θ c) (tabN_paLeLiftK F δ Θ c) N D
    (tabR_ubindCanLiftK fun fin hfin => ihd fin.cdepth (by omega) fin le_rfl) (fun _ => hD)
    n () ls x ρ h

/-- `erwp_ubindClaimRT` from `erwpK_ubindClaimRT`. -/
theorem erwp_ubindClaimRT_of_K {Θ : LocTy} (hΘ : Θ.Down) {c : Loc → Option Life} {F : CTy}
    {δ : LSub}
    (hTr : ∀ m i en, tabN (ℍ := ℍ) F δ Θ c m i = some en → en.abort = true → m ≠ 0)
    {R : Nat → WProp} (N D : Val)
    (hD : ∀ k ls ρ, R k ρ → rwp (ℍ := ℍ) (Θ.view c)
      (fun _ _ v ρ' => v = Val.unit ∧ ρ' = PMap.empty) k ls (.app (.val D) (.val .unit)) ρ)
    {Qin Qout : PostN} (hQout : Qout.Down)
    (hN : ∀ k ls (v : Val) ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN (ℍ := ℍ) F δ Θ c)) Qout k ls
        (.app (.val N) (.val v)) ρ) :
    ∀ n ls M ρ, erwp (ℍ := ℍ) (Θ.view c) (opTableR (tabR (ℍ := ℍ) R F δ Θ c) R) Qin n ls M ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableN (tabN (ℍ := ℍ) F δ Θ c)) Qout n ls
        (ubindE (.pair N D) M) ρ := by
  have hD' : ∀ k ls ρ, R k ρ →
      rwp (ℍ := ℍ) (Θ.view c) (fun _ _ _ ρ' => ρ' = PMap.empty) k ls
        (.app (.val D) (.val .unit)) ρ :=
    fun k ls ρ h => rwp_mono (fun _ _ _ _ h => h.2) (hD k ls ρ h)
  intro n ls M ρ h
  rw [erwp_eq_erwpK_of (opTableRK_lift 0 _ R) _ _] at h
  rw [erwp_opTableN_eq_erwpK 0]
  refine erwpK_ubindClaimRT (ℍ := ℍ) (V := fun _ _ => True) (fun _ _ _ _ _ => trivial)
    (Φ := fun _ => Θ.view c) (fun _ => LocTy.view_down hΘ c) (fun _ _ _ => rfl) (fl := fun _ => 0)
    (Ti := fun _ => liftTabK (tabR (ℍ := ℍ) R F δ Θ c))
    (To := fun _ => liftTabK (tabN (ℍ := ℍ) F δ Θ c))
    (fun _ => (tabN_down F δ Θ hΘ c).liftK) (fun _ _ _ _ _ _ _ _ h => h)
    (tabR_tabN_twinLiftK R F δ Θ c) (tabN_paLeLiftK F δ Θ c) ?_ N D
    (tabR_ubindCanLiftK fun fin _ => erwp_ubind_cancelRunCR_of_K hΘ N D hD' δ fin.cdepth fin le_rfl)
    (fun _ => hD) (fun _ => hQout) ?_ n () ls M ρ h
  · intro _ m i en h₁ ha
    obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
    exact hTr m i en₀ h₀ ha
  · intro y k ls' v ρ' hv
    rw [← erwp_opTableN_eq_erwpK 0]
    exact hN k ls' v ρ' hv

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end

import Core.Chain.MechK835N
import Core.Chain.Eff835N
import Core.Chain.Hardest791N
import Core.Chain.FamImm836N

/-!
# The mechanical stop producers at `erwpK`: `perform` and cancel runs in a context
  `[spec §19, §27, §62]`

`docs/new-core/scope-835-kripke-stop.md` §2, class M, continued from `MechK835N.lean`. A
`perform` at `erwpK` chooses its floor and owes its continuation at every world its entry allows
there; a cancel run passes a context with no handler and no catcher at every world it reaches.
Each `erwp` statement is proved again at one world (`*_of_K`); its text is the original's.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)

variable {ι : Type}

/-- **A `perform` stops at once, at `erwpK`** (`erwp_perform_here`): it chooses the floor `f`, its
continuation, the hole, answers `Q` at every world the entry allows there, and its cancel run, of
the empty region, holds at the entry's cancel obligation at each. -/
theorem erwpK_perform_here {V : ι → ι → Prop} (hV : ∀ y, V y y) {Φ : ι → LocFam}
    {fl : ι → Life} {T : ι → OpTabK ι} {x : ι} {n i : UInt32} {en : OpEntK ι}
    (hT : T x n i = some en) (ha : en.abort = false) (f : Life) (hf : f ≤ fl x)
    (hfin : ∀ y, en.wk f y PMap.empty → ∀ k ls, cancelOKK en y k ls .hole PMap.empty)
    {Q : ι → PostN}
    (hQ : ∀ y, en.wk f y PMap.empty → ∀ k ls' w ρ, en.PB y k ls' w ρ → Q y k ls' w ρ) {k : Nat}
    {ls : List SRec} {v : Val} {ρ : WRes} (h : en.PA k ls v ρ) :
    erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q x k ls
      (performE (.val (opPayload n i v))) ρ := by
  rw [erwpK_eq]
  refine rwpG_here (final_opPlug (K := .hole) (r := false) (payloadName_opPayload n i v)
    (by simp [OpFree, Kont.HasHnd])) (Or.inr (Or.inl
      ⟨.hole, n, i, v, en, pure_sep_mk ⟨rfl, rfl, hT, ha⟩
        ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, h, fun _ => rfl, f, hf, fun y hy ls' _ =>
          ⟨fun k' hk' w σ₁ σ₂ hB hc => ?_, fun _ => hfin y hy k ls'⟩⟩⟩))
  rw [eq_of_compS_empty_left hc]
  simp only [erwpCK, hk', if_true]
  exact erwpK_val (hV y) (hQ y hy _ _ _ _ hB)

/-- `erwp_perform_here` from `erwpK_perform_here`. -/
theorem erwp_perform_here_of_K {Φ : LocFam} {T : OpTabN} {n i : UInt32} {en : OpEntN}
    (hT : T n i = some en) (ha : en.abort = false)
    (hfin : ∀ k ls, cancelOKN en k ls .hole PMap.empty) {Q : PostN}
    (hQ : ∀ k ls' w ρ, en.PB k ls' w ρ → Q k ls' w ρ) {k : Nat} {ls : List SRec} {v : Val}
    {ρ : WRes} (h : en.PA k ls v ρ) :
    erwp (ℍ := ℍ) Φ (opTableN T) Q k ls (performE (.val (opPayload n i v))) ρ := by
  rw [erwp_opTableN_eq_erwpK 0]
  exact erwpK_perform_here (ℍ := ℍ) (V := fun _ _ => True) (fun _ => trivial) (Φ := fun _ => Φ)
    (fl := fun _ => 0) (T := fun _ => liftTabK T) (Q := fun _ => Q) (x := ())
    (liftTabK_of_some hT) ha 0 le_rfl
    (fun _ _ k ls => (cancelOKK_liftEntK en k ls .hole PMap.empty).mpr (hfin k ls))
    (fun _ _ k ls' w ρ hB => hQ k ls' w ρ hB) h

/-- **A Kripke stop at a non-abortive operation of any qualifier** (`erwp_performG`): the
continuation's share and the floor given, the continuation and the cancel run owed at every world
the entry allows there. -/
theorem erwpK_performG {V : ι → ι → Prop} {Φ : ι → LocFam} {fl : ι → Life} {T : ι → OpTabK ι}
    {Q : ι → PostN} {x : ι} (K : Kont) {m i : UInt32} {v : Val} {en : OpEntK ι}
    (hK : K.HasHnd m = false) (hT : T x m i = some en) (ha : en.abort = false)
    {n : Nat} {ls : List SRec} {ρa ρk ρ : WRes} (hc : ResU.CompS ρa ρk ρ)
    (hA : en.PA n ls v ρa) (hu : en.q = .unr → ρk = PMap.empty) (f : Life) (hf : f ≤ fl x)
    (hk : ∀ y, en.wk f y ρk → ∀ ls', en.wc ls ls' ρk → ∀ k', k' < n → ∀ w : Val,
      (en.PB y k' ls' w ─⋆
        erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q y k' ls' (K.plug (.val w))) ρk)
    (hcan : ∀ y, en.wk f y ρk → ∀ ls', en.wc ls ls' ρk → en.q ≠ .lin → cancelOKK en y n ls' K ρk) :
    erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q x n ls
      (K.plug (performE (.val (opPayload m i v)))) ρ := by
  rw [erwpK_eq]
  refine rwpG_here (final_opPlug (r := false) (payloadName_opPayload m i v) hK) (Or.inr (Or.inl
    ⟨K, m, i, v, en, pure_sep_mk ⟨rfl, hK, hT, ha⟩ ⟨ρa, ρk, hc, hA, hu, f, hf,
      fun y hy ls' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, hcan y hy ls' he⟩⟩⟩))
  simp only [erwpCK, hk', if_true]
  exact hk y hy ls' he k' hk' w τ₁ τ₂ hB hcτ

/-- **A cancel run carrying `R` passes a context with no handler and no catcher, at `erwpK`**
(`erwp_cancelTabR_ctx`). -/
theorem erwpK_cancelTabR_ctx {V : ι → ι → Prop} {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down)
    {fl : ι → Life} {T : ι → OpTabK ι} {R : Nat → WProp} (K : Kont)
    (hH : ∀ m, K.HasHnd m = false) (hC : ∀ m, K.Catches m = false)
    (hK : ∀ x, (T x).CtxClosed K) :
    ∀ n x ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => cancelTabRK (fl z) (T z) R)
        (fun _ _ _ _ _ => False) x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => cancelTabRK (fl z) (T z) R) (fun _ _ _ _ _ => False) x n ls
        (K.plug e) ρ := by
  have hL : ∀ z, (cancelTabRK (fl z) (T z) R).Local := fun z => cancelTabRK_local _ _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ h
  rw [erwpK_eq]
  refine rwpG_bind (hΦ x) K ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwpK_unfold_at hL le_rfl h)
  rcases ht with ⟨_, _, _, _, hf⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K', err, hp⟩
  · exact hf.elim
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont'⟩ := pure_sep_iff.mp hp
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
      exact ih k' (by omega) y _ _ _ hc
    · exact hK x m i en P hT hP y _ _ _ _ _ ((hcont' y hy ls'' he).2 hq' P hP)
  · obtain ⟨⟨rfl, hK'⟩, hrest⟩ := pure_sep_iff.mp hp
    have hKo : (K.comp K').Catches 0 = false := by simp [catches_comp, hC, hK']
    have ht' : K.plug (K'.plug (raiseE (.val (cancelVal err)))) =
        (K.comp K').plug (opE true (cancelVal err)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    exact rwpG_here (final_opPlug (payloadName_cancelVal err) hKo) (Or.inr (Or.inr
      ⟨K.comp K', err, pure_sep_mk ⟨rfl, hKo⟩ hrest⟩))

/-- **A cancel run passes a context with no handler and no catcher, at `erwpK`**
(`erwp_cancelTabN_ctx`). -/
theorem erwpK_cancelTabN_ctx {V : ι → ι → Prop} {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down)
    {fl : ι → Life} {T : ι → OpTabK ι} (K : Kont)
    (hH : ∀ m, K.HasHnd m = false) (hC : ∀ m, K.Catches m = false)
    (hK : ∀ x, (T x).CtxClosed K) :
    ∀ n x ls e ρ, erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T z))
        (fun _ _ _ _ _ => False) x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => cancelTabK (fl z) (T z)) (fun _ _ _ _ _ => False) x n ls
        (K.plug e) ρ := by
  have hL : ∀ z, (cancelTabK (fl z) (T z)).Local := fun z => cancelTabK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ h
  rw [erwpK_eq]
  refine rwpG_bind (hΦ x) K ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwpK_unfold_at hL le_rfl h)
  rcases ht with ⟨_, _, _, _, hf⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K', err, hp⟩
  · exact hf.elim
  · obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont'⟩ := pure_sep_iff.mp hp
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
      exact ih k' (by omega) y _ _ _ hc
    · exact hK x m i en P hT hP y _ _ _ _ _ ((hcont' y hy ls'' he).2 hq' P hP)
  · obtain ⟨⟨rfl, hK'⟩, hrest⟩ := pure_sep_iff.mp hp
    have hKo : (K.comp K').Catches 0 = false := by simp [catches_comp, hC, hK']
    have ht' : K.plug (K'.plug (raiseE (.val (cancelVal err)))) =
        (K.comp K').plug (opE true (cancelVal err)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    exact rwpG_here (final_opPlug (payloadName_cancelVal err) hKo) (Or.inr (Or.inr
      ⟨K.comp K', err, pure_sep_mk ⟨rfl, hKo⟩ hrest⟩))

/-! ### The claim with the view's consistency -/

/-- **A body carries the view's consistency to its claim, at `erwpK`** (`erwp_claimX`). The body's
table `Ti` and the outer `To` agree but for the cancel obligations; a stop's share is consistent,
and so is every answer (`hPBc`); a cancellable stop's cancel obligation passes by `hcan`, read at
the resumption world; a `raise`'s claim is part of a consistent resource. -/
theorem erwpK_claimX {V : ι → ι → Prop} {Φ : ι → LocFam} {fl : ι → Life}
    {Ti To : ι → OpTabK ι}
    (hTw : ∀ x m i en, Ti x m i = some en → ∃ en', To x m i = some en' ∧ en'.q = en.q ∧
      en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧ en'.wk = en.wk)
    {c : Loc → Option Life} {R : Nat → WProp} {Q : ι → PostN}
    (hPBc : ∀ x m i en, Ti x m i = some en → ∀ y k ls w ρ, en.PB y k ls w ρ → ConsistentX c ρ)
    (hcan : ∀ x m i en en', Ti x m i = some en → To x m i = some en' → en.q ≠ .lin →
      ∀ y k ls (K : Kont) ρ, ConsistentX c ρ → cancelOKK en y k ls K ρ →
        cancelOKK en' y k ls K ρ) :
    ∀ n x ls e ρ, ConsistentX c ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableRK (fl z) (Ti z) R) Q x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableRK (fl z) (To z) (Goal791N.claimX R c)) Q x n ls e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ hc h
  rw [erwpK_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (rwpG_consistentXV h hc)
  obtain ⟨ht, hcσ, hvσ⟩ := ht
  rcases ht with hv | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact Or.inl hv
  · -- a stop: its share is consistent, and so is every answer
    obtain ⟨⟨hpt, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hT', hq, hab', hPA, hPB, hwc, hwk⟩ := hTw x m i en hT
    have hck : ConsistentX c ρk := consistentX_right hcak hcσ hvσ
    refine Or.inr (Or.inl ⟨K₁, m, i, v, en', pure_sep_mk ⟨hpt, hK₁, hT', hab'.trans ha⟩
      ⟨ρa, ρk, hcak, hPA ▸ hA, fun hu' => hu (hq ▸ hu'), f, hf, fun y hy ls'' he =>
        ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hql => ?_⟩⟩⟩)
    · rw [hwk] at hy; rw [hwc] at he; rw [hPB] at hB
      have hc' := (hcont y hy ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpCK, show k' < n by omega, if_true] at hc' ⊢
      exact ih k' (by omega) y _ _ _
        (consistentX_compS hcτ hck (hPBc x m i en hT y k' ls'' w τ₁ hB)) hc'
    · rw [hwk] at hy; rw [hwc] at he
      exact hcan x m i en en' hT hT' (hq ▸ hql) y k ls'' K₁ ρk hck
        ((hcont y hy ls'' he).2 (hq ▸ hql))
  · -- a `raise`: the claim is part of a consistent resource
    obtain ⟨⟨hpt, hK₁, hT, hab⟩, σ₁, ρR, hcσR, hpa, hR⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hT', -, hab', hPA, -, -, -⟩ := hTw x m i en hT
    exact Or.inr (Or.inr ⟨K₁, m, i, v, en', pure_sep_mk ⟨hpt, hK₁, hT', hab'.trans hab⟩
      ⟨σ₁, ρR, hcσR, hPA ▸ hpa, hR, consistentX_right hcσR hcσ hvσ⟩⟩)

/-- **A cancel run carries the view's consistency to its claim, at `erwpK`**
(`erwp_cancelRun_claimX`), as `erwpK_claimX`. -/
theorem erwpK_cancelRun_claimX {V : ι → ι → Prop} {Φ : ι → LocFam} {fl : ι → Life}
    {Ti To : ι → OpTabK ι}
    (hTw : ∀ x m i en, Ti x m i = some en → ∃ en', To x m i = some en' ∧ en'.q = en.q ∧
      en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧ en'.wk = en.wk)
    {c : Loc → Option Life} {R : Nat → WProp}
    (hPBc : ∀ x m i en, Ti x m i = some en → ∀ y k ls w ρ, en.PB y k ls w ρ → ConsistentX c ρ)
    (hcan : ∀ x m i en en', Ti x m i = some en → To x m i = some en' → en.q ≠ .lin →
      ∀ y k ls (K : Kont) ρ, ConsistentX c ρ → cancelOKK en y k ls K ρ →
        cancelOKK en' y k ls K ρ) :
    ∀ n x ls e ρ, ConsistentX c ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => cancelTabRK (fl z) (Ti z) R) (fun _ _ _ _ _ => False) x n ls
        e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => cancelTabRK (fl z) (To z) (Goal791N.claimX R c))
        (fun _ _ _ _ _ => False) x n ls e ρ := by
  have hTT : ∀ x, (Ti x).Twin (To x) := fun x m i en h => by
    obtain ⟨en', h', h₁, h₂, h₃, h₄, h₅, -⟩ := hTw x m i en h
    exact ⟨en', h', h₁, h₂, h₃, h₄, h₅⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x ls e ρ hc h
  rw [erwpK_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (rwpG_consistentXV h hc)
  obtain ⟨ht, hcσ, hvσ⟩ := ht
  rcases ht with ⟨_, _, _, _, hf⟩ | ⟨K₁, m, i, v, en, hp⟩ | ⟨K', err, hp⟩
  · exact hf.elim
  · -- a stop: its share is consistent, and so is every answer
    obtain ⟨⟨hpt, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨en', hT', hq, hab', hPA, hPB, hwc, hwk⟩ := hTw x m i en hT
    have hck : ConsistentX c ρk := consistentX_right hcak hcσ hvσ
    refine Or.inr (Or.inl ⟨K₁, m, i, v, en', pure_sep_mk ⟨hpt, hK₁, hT', hab'.trans ha⟩
      ⟨ρa, ρk, hcak, hPA ▸ hA, fun hu' => hu (hq ▸ hu'), f, hf, fun y hy ls'' he =>
        ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, fun hql => ?_⟩⟩⟩)
    · rw [hwk] at hy; rw [hwc] at he; rw [hPB] at hB
      have hc' := (hcont y hy ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpCK, show k' < n by omega, if_true] at hc' ⊢
      exact ih k' (by omega) y _ _ _
        (consistentX_compS hcτ hck (hPBc x m i en hT y k' ls'' w τ₁ hB)) hc'
    · rw [hwk] at hy; rw [hwc] at he
      exact hcan x m i en en' hT hT' (hq ▸ hql) y k ls'' K₁ ρk hck
        ((hcont y hy ls'' he).2 (hq ▸ hql))
  · -- the cancel's `raise`: the claim is part of a consistent resource
    obtain ⟨hpure, y1, y2, hy, hy1, hR⟩ := pure_sep_iff.mp hp
    obtain ⟨τa, τb, hcab, herr, hnb⟩ := hy1
    exact Or.inr (Or.inr ⟨K', err, pure_sep_mk hpure ⟨y1, y2, hy,
      ⟨τa, τb, hcab, errOkK_twin (hTT x) herr, hnb⟩, hR, consistentX_right hy hcσ hvσ⟩⟩)

/-- **A body at an abortive table carries the view's consistency to its claim, at `erwpK`**
(`erwp_claimX_abort`). -/
theorem erwpK_claimX_abort {V : ι → ι → Prop} {Φ : ι → LocFam} {fl : ι → Life}
    {T : ι → OpTabK ι} {x : ι} {c : Loc → Option Life}
    (hab : ∀ m i en, T x m i = some en → en.abort = true) {R : Nat → WProp} {Q : ι → PostN}
    {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes} (hc : ConsistentX c ρ)
    (h : erwpK (ℍ := ℍ) V Φ (fun z => opTableRK (fl z) (T z) R) Q x n ls e ρ) :
    erwpK (ℍ := ℍ) V Φ (fun z => opTableRK (fl z) (T z) (Goal791N.claimX R c)) Q x n ls e ρ := by
  rw [erwpK_eq] at h ⊢
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (rwpG_consistentXV h hc)
  obtain ⟨ht, hcσ, hvσ⟩ := ht
  rcases ht with hv | ⟨K₁, m, i, v, en, hp⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact Or.inl hv
  · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd ha (by rw [hab m i en hTe]; decide)
  · obtain ⟨hpt, σ₁, ρR, hcσR, hpa, hR⟩ := pure_sep_iff.mp hp
    exact Or.inr (Or.inr ⟨K₁, m, i, v, en, pure_sep_mk hpt
      ⟨σ₁, ρR, hcσR, hpa, hR, consistentX_right hcσR hcσ hvσ⟩⟩)

/-! ### A run at an abortive table reads its tie only at its entry -/

/-- **A run at an abortive table reads its tie only at its entry, at `erwpK`** (`erwp_tieEntry`):
it never stops to resume, so it never reads a later world's location family. -/
theorem erwpK_tieEntry {V : ι → ι → Prop} {Φ Φ' : ι → LocFam} {fl : ι → Life}
    {T : ι → OpTabK ι} {x : ι} (hfam : (Φ' x).fam = (Φ x).fam)
    (hab : ∀ m i en, T x m i = some en → en.abort = true) {Q : ι → PostN} {n : Nat}
    {ls : List SRec} {e : Expr} {ρ : WRes} (hI : ∀ a ∈ (Φ' x).imm, a ∈ (Φ x).imm ∨ a ∈ ls)
    (h : erwpK (ℍ := ℍ) V Φ' (fun z => opTableK (fl z) (T z)) Q x n ls e ρ) :
    erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q x n ls e ρ := by
  rw [erwpK_eq] at h ⊢
  refine Goal791N.rwpG_tieEntry hfam hI (rwpG_mono (fun k ls' t σ ht => ?_) h)
  rcases ht with ht | ⟨K, m, i, v, en, hp⟩ | ht
  · exact Or.inl ht
  · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd (hab m i en hTe) (by rw [ha]; decide)
  · exact Or.inr (Or.inr ht)

/-- **`erwpK_tieEntry` at a table whose raises carry `R`** (`erwp_tieEntryR`). -/
theorem erwpK_tieEntryR {V : ι → ι → Prop} {Φ Φ' : ι → LocFam} {fl : ι → Life}
    {T : ι → OpTabK ι} {x : ι} (hfam : (Φ' x).fam = (Φ x).fam)
    (hab : ∀ m i en, T x m i = some en → en.abort = true) {R : Nat → WProp} {Q : ι → PostN}
    {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (hI : ∀ a ∈ (Φ' x).imm, a ∈ (Φ x).imm ∨ a ∈ ls)
    (h : erwpK (ℍ := ℍ) V Φ' (fun z => opTableRK (fl z) (T z) R) Q x n ls e ρ) :
    erwpK (ℍ := ℍ) V Φ (fun z => opTableRK (fl z) (T z) R) Q x n ls e ρ := by
  rw [erwpK_eq] at h ⊢
  refine Goal791N.rwpG_tieEntry hfam hI (rwpG_mono (fun k ls' t σ ht => ?_) h)
  rcases ht with ht | ⟨K, m, i, v, en, hp⟩ | ht
  · exact Or.inl ht
  · obtain ⟨⟨-, -, hTe, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd (hab m i en hTe) (by rw [ha]; decide)
  · exact Or.inr (Or.inr ht)

/-- `erwp_tieEntryR` from `erwpK_tieEntryR`. -/
theorem erwp_tieEntryR_of_K {Φ Φ' : LocFam} (hfam : Φ'.fam = Φ.fam) {T : OpTabN}
    (hab : ∀ m i en, T m i = some en → en.abort = true) {R : Nat → WProp} {Q : PostN} {n : Nat}
    {ls : List SRec} {e : Expr} {ρ : WRes} (hI : ∀ x ∈ Φ'.imm, x ∈ Φ.imm ∨ x ∈ ls)
    (h : erwp (ℍ := ℍ) Φ' (opTableR T R) Q n ls e ρ) :
    erwp (ℍ := ℍ) Φ (opTableR T R) Q n ls e ρ := by
  rw [erwp_eq_erwpK_of (opTableRK_lift 0 T R) Φ' _] at h
  rw [erwp_eq_erwpK_of (opTableRK_lift 0 T R) Φ _]
  exact erwpK_tieEntryR (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Φ) (Φ' := fun _ => Φ')
    (fl := fun _ => 0) (T := fun _ => liftTabK T) (x := ()) hfam
    (fun m i en h₁ => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
      exact hab m i en₀ h₀) hI h

end BoCa.Fig16.LogRel.Core.Chain.SI

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 ctx791 vals791 jdgC interp_top_of_defines_empty)
open BoCa.BoLo (Heap Kont Head ubindE)

/-- `erwp_tieEntry` from `erwpK_tieEntry`. -/
theorem erwp_tieEntry_of_K {Φ Φ' : LocFam} (hfam : Φ'.fam = Φ.fam) {T : OpTabN}
    (hab : ∀ m i en, T m i = some en → en.abort = true) {Q : PostN} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes} (hI : ∀ x ∈ Φ'.imm, x ∈ Φ.imm ∨ x ∈ ls)
    (h : erwp (ℍ := ℍ) Φ' (opTableN T) Q n ls e ρ) : erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ := by
  rw [erwp_opTableN_eq_erwpK 0] at h ⊢
  exact erwpK_tieEntry (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Φ) (Φ' := fun _ => Φ')
    (fl := fun _ => 0) (T := fun _ => liftTabK T) (x := ()) hfam
    (fun m i en h₁ => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
      exact hab m i en₀ h₀) hI h

/-- `erwp_claimX_abort` from `erwpK_claimX_abort`. -/
theorem erwp_claimX_abort_of_K {Θ : LocTy} {c : Loc → Option Life} {T : OpTabN}
    (hab : ∀ m i en, T m i = some en → en.abort = true) {R : Nat → WProp} {Q : PostN} {n : Nat}
    {ls : List SRec} {e : Expr} {ρ : WRes} (hc : ConsistentX c ρ)
    (h : erwp (ℍ := ℍ) (Θ.view c) (opTableR T R) Q n ls e ρ) :
    erwp (ℍ := ℍ) (Θ.view c) (opTableR T (claimX R c)) Q n ls e ρ := by
  rw [erwp_eq_erwpK_of (opTableRK_lift 0 T R) _ _] at h
  rw [erwp_eq_erwpK_of (opTableRK_lift 0 T _) _ _]
  exact erwpK_claimX_abort (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Θ.view c)
    (fl := fun _ => 0) (T := fun _ => liftTabK T) (x := ())
    (fun m i en h₁ => by
      obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
      exact hab m i en₀ h₀) hc h

/-- The lifted lender's twins at two claims agree but for the cancel obligations. -/
theorem tabR_tabR_twinLiftK (R R' : Nat → WProp) (F : CTy) (δ : LSub) (Θ : LocTy)
    (c : Loc → Option Life) :
    ∀ (_ : Unit) m i en, liftTabK (tabR (ℍ := ℍ) R F δ Θ c) m i = some en →
      ∃ en', liftTabK (tabR (ℍ := ℍ) R' F δ Θ c) m i = some en' ∧ en'.q = en.q ∧
        en'.abort = en.abort ∧ en'.PA = en.PA ∧ en'.PB = en.PB ∧ en'.wc = en.wc ∧
        en'.wk = en.wk := by
  intro _ m i en h
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h
  obtain ⟨q, A, B, fin, -, rfl, -, hR'⟩ := tab_lookupR R F h₀
  exact ⟨_, liftTabK_of_some (hR' R'), rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The answers of a row meeting `CTy.SuspendC` lie in `Res_⊤`, consistent with every view. -/
theorem tabR_pbcLiftK {x : LifeVar} {bnd : Lifetime.Life} (hbnd : LifeCtx.empty.Defines bnd)
    {R : Nat → WProp} {F : CTy} (hF : F.SuspendC x bnd) (δ : LSub) (Θ : LocTy)
    (c : Loc → Option Life) :
    ∀ (_ : Unit) m i en, liftTabK (tabR (ℍ := ℍ) R F δ Θ c) m i = some en →
      ∀ y k ls w ρ, en.PB y k ls w ρ → ConsistentX c ρ := by
  intro _ m i en h _ k ls w ρ hB
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h
  obtain ⟨q, A, B, fin, hLy, rfl, -, -⟩ := tab_lookupR R F h₀
  obtain ⟨-, -, -, -, hOB, -⟩ := layer_suspend F hF hLy
  exact consistentX_of_top (vN_outlives (models_empty_any _)
    (interp_top_of_defines_empty hbnd δ) hOB Θ k w ρ hB.1) c

/-- `erwp_cancelRun_claimX` from `erwpK_cancelRun_claimX`, by induction on how deep cancel rows
nest. -/
theorem erwp_cancelRun_claimX_of_K {x : LifeVar} {bnd : Lifetime.Life} {δ : LSub} {Θ : LocTy}
    {c : Loc → Option Life} {R : Nat → WProp} (hbnd : LifeCtx.empty.Defines bnd) :
    ∀ (d : Nat) (F : CTy), F.cdepth ≤ d → F.SuspendC x bnd →
    ∀ n ls e ρ, ConsistentX c ρ →
      erwp (ℍ := ℍ) (Θ.view c) (cancelTabR (tabR (ℍ := ℍ) R F δ Θ c) R) (fun _ _ _ _ => False)
        n ls e ρ →
      erwp (ℍ := ℍ) (Θ.view c) (cancelTabR (tabR (ℍ := ℍ) (claimX R c) F δ Θ c) (claimX R c))
        (fun _ _ _ _ => False) n ls e ρ := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro F hFd hF n ls e ρ hc h
  rw [erwp_eq_erwpK_of (cancelTabRK_lift 0 _ R) _ _] at h
  rw [erwp_eq_erwpK_of (cancelTabRK_lift 0 _ _) _ _]
  refine erwpK_cancelRun_claimX (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Θ.view c)
    (fl := fun _ => 0) (Ti := fun _ => liftTabK (tabR (ℍ := ℍ) R F δ Θ c))
    (To := fun _ => liftTabK (tabR (ℍ := ℍ) (claimX R c) F δ Θ c))
    (tabR_tabR_twinLiftK R _ F δ Θ c) (tabR_pbcLiftK hbnd hF δ Θ c) ?_ n () ls e ρ hc h
  intro _ m i en en' h₁ h₂ hql y k ls'' K ρk hck hin
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
  obtain ⟨en₀', h₀', rfl⟩ := liftTabK_some h₂
  obtain ⟨q, A, B, fin, hLy, rfl, -, hR₂⟩ := tab_lookupR R F h₀
  rw [hR₂ (claimX R c)] at h₀'
  cases Option.some.inj h₀'
  obtain ⟨-, -, -, -, -, hfinS⟩ := layer_suspend F hF hLy
  refine (cancelOKK_liftEntK _ k ls'' K ρk).mpr fun P hP => ?_
  have hin' := (cancelOKK_liftEntK _ k ls'' K ρk).mp hin
  have hq' : q ≠ .lin := hql
  by_cases hcap : capB q B = true
  · simp only [entN, hcap, if_true] at hP hin'
    by_cases htop : fin = .top
    · subst htop; simp [finR] at hP
    rw [finR_eq _ htop] at hP
    cases Option.some.inj hP
    have hin'' := hin' _ (finR_eq R htop δ Θ c)
    have hfd := layer_cdepth F hLy
    exact ihd fin.cdepth (by omega) fin le_rfl (hfinS hcap) k ls'' _ ρk hck hin''
  · simp [entN, hcap] at hP

/-- `erwp_claimX` from `erwpK_claimX`; its cancel obligations by `erwp_cancelRun_claimX`. -/
theorem erwp_claimX_of_K {x : LifeVar} {bnd : Lifetime.Life} {δ : LSub} {Θ : LocTy}
    {c : Loc → Option Life} {R : Nat → WProp} {F : CTy} (hbnd : LifeCtx.empty.Defines bnd)
    (hF : F.SuspendC x bnd) {Q : PostN} :
    ∀ n ls e ρ, ConsistentX c ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableR (tabR (ℍ := ℍ) R F δ Θ c) R) Q n ls e ρ →
      erwp (ℍ := ℍ) (Θ.view c) (opTableR (tabR (ℍ := ℍ) (claimX R c) F δ Θ c) (claimX R c)) Q
        n ls e ρ := by
  intro n ls e ρ hc h
  rw [erwp_eq_erwpK_of (opTableRK_lift 0 _ R) _ _] at h
  rw [erwp_eq_erwpK_of (opTableRK_lift 0 _ _) _ _]
  refine erwpK_claimX (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Θ.view c)
    (fl := fun _ => 0) (Ti := fun _ => liftTabK (tabR (ℍ := ℍ) R F δ Θ c))
    (To := fun _ => liftTabK (tabR (ℍ := ℍ) (claimX R c) F δ Θ c)) (Q := fun _ => Q)
    (tabR_tabR_twinLiftK R _ F δ Θ c) (tabR_pbcLiftK hbnd hF δ Θ c) ?_ n () ls e ρ hc h
  intro _ m i en en' h₁ h₂ hql y k ls'' K ρk hck hin
  obtain ⟨en₀, h₀, rfl⟩ := liftTabK_some h₁
  obtain ⟨en₀', h₀', rfl⟩ := liftTabK_some h₂
  obtain ⟨q, A, B, fin, hLy, rfl, -, hR₂⟩ := tab_lookupR R F h₀
  rw [hR₂ (claimX R c)] at h₀'
  cases Option.some.inj h₀'
  obtain ⟨-, -, -, -, -, hfinS⟩ := layer_suspend F hF hLy
  refine (cancelOKK_liftEntK _ k ls'' K ρk).mpr fun P hP => ?_
  have hin' := (cancelOKK_liftEntK _ k ls'' K ρk).mp hin
  have hq' : q ≠ .lin := hql
  by_cases hcap : capB q B = true
  · simp only [entN, hcap, if_true] at hP hin'
    by_cases htop : fin = .top
    · subst htop; simp [finR] at hP
    rw [finR_eq _ htop] at hP
    cases Option.some.inj hP
    have hin'' := hin' _ (finR_eq R htop δ Θ c)
    exact erwp_cancelRun_claimX hbnd fin.cdepth fin le_rfl (hfinS hcap) k ls'' _ ρk hck hin''
  · simp [entN, hcap] at hP

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

namespace BoCa.Fig16.LogRel.Core.Chain.SI.LendProg
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  clauseAt capTag ubindE)

/-- `erwp_performG` from `erwpK_performG`. -/
theorem erwp_performG_of_K {Φ : LocFam} {T : OpTabN} {Q : PostN} (K : Kont) {m i : UInt32}
    {v : Val}
    {en : OpEntN} (hK : K.HasHnd m = false) (hT : T m i = some en) (ha : en.abort = false)
    {n : Nat} {ls : List SRec} {ρa ρk ρ : WRes} (hc : ResU.CompS ρa ρk ρ)
    (hA : en.PA n ls v ρa) (hu : en.q = .unr → ρk = PMap.empty)
    (hk : ∀ ls', en.wc ls ls' ρk → ∀ k', k' < n → ∀ w : Val,
      (en.PB k' ls' w ─⋆ erwp (ℍ := ℍ) Φ (opTableN T) Q k' ls' (K.plug (.val w))) ρk)
    (hcan : ∀ ls', en.wc ls ls' ρk → en.q ≠ .lin → cancelOKN en n ls' K ρk) :
    erwp (ℍ := ℍ) Φ (opTableN T) Q n ls (K.plug (performE (.val (opPayload m i v)))) ρ := by
  rw [erwp_opTableN_eq_erwpK 0]
  refine erwpK_performG (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Φ) (fl := fun _ => 0)
    (T := fun _ => liftTabK T) (Q := fun _ => Q) (x := ()) K hK (liftTabK_of_some hT) ha hc hA
    hu 0 le_rfl ?_ ?_
  · intro y _ ls' he k' hk' w
    have h := hk ls' he k' hk' w
    rw [erwp_opTableN_eq_erwpK 0] at h
    exact h
  · intro y _ ls' he hq
    exact (cancelOKK_liftEntK en n ls' K ρk).mpr (hcan ls' he hq)

/-- `erwp_cancelTabR_ctx` from `erwpK_cancelTabR_ctx`. -/
theorem erwp_cancelTabR_ctx_of_K {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} {R : Nat → WProp}
    (K : Kont) (hH : ∀ m, K.HasHnd m = false) (hC : ∀ m, K.Catches m = false)
    (hK : T.CtxClosed K) :
    ∀ n ls x ρ, erwp (ℍ := ℍ) Φ (cancelTabR T R) (fun _ _ _ _ => False) n ls x ρ →
      erwp (ℍ := ℍ) Φ (cancelTabR T R) (fun _ _ _ _ => False) n ls (K.plug x) ρ := by
  intro n ls x ρ h
  rw [erwp_eq_erwpK_of (cancelTabRK_lift 0 T R) Φ _] at h ⊢
  exact erwpK_cancelTabR_ctx (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Φ) (fun _ => hΦ)
    (fl := fun _ => 0) (T := fun _ => liftTabK T) K hH hC (fun _ => liftTabK_ctxClosed hK)
    n () ls x ρ h

end BoCa.Fig16.LogRel.Core.Chain.SI.LendProg

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Hardest791
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal clauseAt
  capTag ubindE)

/-- `erwp_cancelTabN_ctx` from `erwpK_cancelTabN_ctx`. -/
theorem erwp_cancelTabN_ctx_of_K {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (K : Kont)
    (hH : ∀ m, K.HasHnd m = false) (hC : ∀ m, K.Catches m = false) (hK : T.CtxClosed K) :
    ∀ n ls x ρ, erwp (ℍ := ℍ) Φ (cancelTabN T) (fun _ _ _ _ => False) n ls x ρ →
      erwp (ℍ := ℍ) Φ (cancelTabN T) (fun _ _ _ _ => False) n ls (K.plug x) ρ := by
  intro n ls x ρ h
  rw [erwp_eq_erwpK_of (cancelTabK_lift 0 T) Φ _] at h ⊢
  exact erwpK_cancelTabN_ctx (ℍ := ℍ) (V := fun _ _ => True) (Φ := fun _ => Φ) (fun _ => hΦ)
    (fl := fun _ => 0) (T := fun _ => liftTabK T) K hH hC (fun _ => liftTabK_ctxClosed hK)
    n () ls x ρ h

end BoCa.Fig16.LogRel.Core.Chain.SI.Hardest791

end

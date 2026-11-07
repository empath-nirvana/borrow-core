import Core.Chain.SI.HandleN

/-!
# Bind, garbage and stops at `erwp`

`erwp_bind` is `ewp_bind` (`SI/Ewp.lean`) over Core's worlds: a context with no handler and no
catcher around a computation in `erwp`. A value continues in the context; a stop passes the
context outward, which is put back into the continuation the stop owes, and that continuation
is covered by induction on the index, since a stop owes it only below the index it stops at.
The cancel obligations a stop owes are read through the context (`OpTabN.CtxClosed`), as
`bindOK_pure`'s `CtxClosed`.

`erwp_garbage` adds a part with no `own` cell to the resource (`rwpG_frame`, then
`rwpG_garbage`). `erwp_of_rwp` and `erwp_bindR` put a computation that never stops in front of an
`erwp`. `erwp_perform` is a stop at a must-resume operation.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)

/-- The cancel obligations of `T`'s entries are kept when a context `K` is put around the
continuation they cancel. -/
def OpTabN.CtxClosed (T : OpTabN) (K : Kont) : Prop :=
  ∀ m i en P, T m i = some en → en.fin = some P → ∀ k ls (K' : Kont) x ρ,
    P k ls (K'.dead.plug x) ρ → P k ls ((K.comp K').dead.plug x) ρ

/-- **Bind at `erwp`**, around a context with no handler and no catcher. -/
theorem erwp_bind {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} {Q Q' : PostN} (K : Kont)
    (hH : ∀ m, K.HasHnd m = false) (hC : ∀ m, K.Catches m = false) (hK : T.CtxClosed K)
    (hcont : ∀ k ls (v : Val) ρ, Q' k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Q k ls (K.plug v.1) ρ) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T) Q' n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) Q n ls (K.plug e) ρ := by
  have hL := opTableN_local T
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ h
  rw [erwp_eq]
  refine rwpG_bind hΦ K ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwp_unfold_at hL le_rfl h)
  rcases ht with ⟨v, rfl, hv⟩ | ht | ht
  · exact erwp_unfold_at hL hk (hcont k ls' v σ hv)
  · obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont'⟩ := pure_sep_iff.mp hp
    have hKo : (K.comp K₁).HasHnd m = false := by simp [hasHnd_comp, hH, hK₁]
    have ht' : K.plug (K₁.plug (performE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
        ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
          fun hq' P hP => ?_⟩⟩⟩))
    · rw [Kont.plug_comp]
      have hc := (hcont' ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpC, show k' < n by omega, if_true] at hc ⊢
      exact ih k' (by omega) _ _ _ hc
    · exact hK m i en P hT hP _ _ _ _ _ ((hcont' ls'' he).2 hq' P hP)
  · obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, hrest⟩ := pure_sep_iff.mp hp
    have hKo : (K.comp K₁).Catches m = false := by simp [catches_comp, hC, hK₁]
    have ht' : K.plug (K₁.plug (raiseE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE true (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    exact rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩ hrest⟩))

/-- **Garbage at `erwp`**: a part with no `own` cell joins the resource. -/
theorem erwp_garbage {Φ : LocFam} {Tb : TableN} {Q : PostN} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ g ρg : WRes} (hc : ResU.CompS ρ g ρg) (hg : NoOwn g)
    (h : erwp (ℍ := ℍ) Φ Tb Q n ls e ρ) : erwp (ℍ := ℍ) Φ Tb Q n ls e ρg := by
  rw [erwp_eq] at h ⊢
  exact rwpG_garbage (rwpG_mono (fun _ _ _ _ ⟨τ₁, τ₂, hcτ, hq', hnτ⟩ => ⟨τ₁, τ₂, hcτ, hnτ, hq'⟩)
    (rwpG_frame (fun _ τ => NoOwn τ) (fun _ _ _ _ h => h) hc h hg))

/-- A computation that never stops is in `erwp` at every table. -/
theorem erwp_of_rwp {Φ : LocFam} {Tb : TableN} {Q : PostN} {n : Nat} {ls : List SRec}
    {e : Expr} {ρ : WRes} (h : rwp (ℍ := ℍ) Φ Q n ls e ρ) : erwp (ℍ := ℍ) Φ Tb Q n ls e ρ := by
  rw [erwp_eq]
  exact rwpG_mono (fun _ _ _ _ h => Or.inl h) (rwp_iff_rwpG.mp h)

/-- **A computation that never stops, then an `erwp`**: bind with any context. -/
theorem erwp_bindR {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hL : Tb.Local) {Q : PostN}
    (K : Kont) {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : rwp (ℍ := ℍ) Φ (fun k ls' v => erwp (ℍ := ℍ) Φ Tb Q k ls' (K.plug v.1)) n ls e ρ) :
    erwp (ℍ := ℍ) Φ Tb Q n ls (K.plug e) ρ := by
  rw [erwp_eq]
  refine rwpG_bind hΦ K ?_
  refine rwpG_mono_le (fun k hk ls' t σ ⟨v, hv, hq⟩ => ?_) (rwp_iff_rwpG.mp h)
  subst hv
  exact erwp_unfold_at hL hk hq

/-- **A stop at a must-resume operation**: the payload in `PA`, and the continuation owed at
every answer at every lower index. -/
theorem erwp_perform {Φ : LocFam} {T : OpTabN} {Q : PostN} (K : Kont) {m i : UInt32} {v : Val}
    {en : OpEntN} (hK : K.HasHnd m = false) (hT : T m i = some en) (ha : en.abort = false)
    (hq : en.q = .lin) {n : Nat} {ls : List SRec} {ρa ρk ρ : WRes} (hc : ResU.CompS ρa ρk ρ)
    (hA : en.PA n ls v ρa)
    (hk : ∀ ls', en.wc ls ls' ρk → ∀ k', k' < n → ∀ w : Val,
      (en.PB k' ls' w ─⋆ erwp (ℍ := ℍ) Φ (opTableN T) Q k' ls' (K.plug (.val w))) ρk) :
    erwp (ℍ := ℍ) Φ (opTableN T) Q n ls (K.plug (performE (.val (opPayload m i v)))) ρ := by
  rw [erwp_eq]
  refine rwpG_here (final_opPlug (r := false) (payloadName_opPayload m i v) hK) (Or.inr (Or.inl
    ⟨K, m, i, v, en, pure_sep_mk ⟨rfl, hK, hT, ha⟩ ⟨ρa, ρk, hc, hA,
      fun hu => absurd (hq.symm.trans hu) (by simp), fun ls' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
        fun hq' => absurd hq hq'⟩⟩⟩))
  simp only [erwpC, hk', if_true]
  exact hk ls' he k' hk' w τ₁ τ₂ hB hcτ

end BoCa.Fig16.LogRel.Core.Chain.SI

end

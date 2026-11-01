import DtorUnwind.SI.ErwpN
import Core.EffRules

/-!
# A handler at the step index over Core's worlds: `erwp_handle`

`Core`'s `ewp_handle_or` (`Core/EffRules.lean`) proves `[handle]` by induction on the least fixed
point of the handled computation's `ewpTS`. At `erwp` there is no fixed point: the proof is by
induction on the index, as stage 1's `ewp_handle`, and otherwise follows `ewp_handle_or`'s case
split at the end of the handled run: `[ret]`; an operation of the handler's name, whose clause
gets `κ`; an abortive one, whose clause runs and whose continuation is dropped; an operation or
raise of another name, which passes outward with the handler reinstalled in its continuation.
`κ` resumed at an answer at `k′` is the handled continuation at `k′`, which the induction
hypothesis covers since `k′ < k ≤ n`: the stop's continuation is owed only at lower indices, so
no `hdv` (guardedness) premise is needed.

Scope of this file: the handler's non-abortive operations are unrestricted (`unr`, `κ` the plain
`kappa` and its share empty, `hunr`); a must-resume or cancellable `κ` owns a cell
(`kappaCell`), and its resumption and its cancel run are not yet transcribed at the index.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.DtorUnwind.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE kappa kappaC
  kappaCell kappaAt capTag clauseAt hndVal ccatchE)

/-! ### Garbage -/

/-- `wpG_garbage` at the index: a part of the final resource with no `own` cell joins `ρ⁺`. -/
theorem rwpG_garbage {Φ : LocFam} {Q : PostG} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : rwpG (ℍ := ℍ) Φ (fun k ls' t ρ' => ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ' ∧ NoOwn ρ₂ ∧
      Q k ls' t ρ₁) n ls e ρ) :
    rwpG (ℍ := ℍ) Φ Q n ls e ρ := by
  intro ρf fρ ps μ h1 h2 h3 h4 hl hfd j μ' e' hj hrun hfin
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', g1, g2, g3, g6, g7, g9, gA, gB,
    gT, gtg, gps, gls, ρ₁, ρ₂, hc, hno, hQ⟩ := h ρf fρ ps μ h1 h2 h3 h4 hl hfd j μ' e' hj hrun hfin
  obtain ⟨hf₁, -⟩ := ResU.Hash.split hc g1
  obtain ⟨F, hF, hF₂⟩ := (ResU.CompS.assoc ρf ρ₁ ρ₂ fρ').mp ⟨ρ', hc, g2⟩
  obtain ⟨Z, hZ, hFZ⟩ := (ResU.CompS.assoc F ρ₂ ρp fρ'p).mpr ⟨fρ', hF₂, g6⟩
  obtain ⟨Z', hZ', h₁Z⟩ := (ResU.CompS.assoc ρ₁ ρ₂ ρp π).mpr ⟨ρ', hc, g9⟩
  cases ResU.CompS.functional hZ' hZ
  have hv : ResU.Valid fρ'p := by obtain ⟨σ, hσ, -⟩ := g7; exact ⟨σ, hσ⟩
  exact ⟨ρ₁, Z, F, fρ'p, π, ps', ls', hf₁, hF,
    ⟨(ResU.CompS.comm hFZ).1, fρ'p, ResU.CompS.comm hFZ, hv⟩, hFZ, g7, h₁Z, gA,
    noOwn_compS hZ hno gB, gT, gtg, gps, gls, hQ⟩

/-! ### `κ` -/

/-- `KapRelT` at the index, its resume branch: resumed at every answer in `PB` at every
`k′ < k`. -/
def KapRelN (Φ : LocFam) (Tb : TableN) (Q : PostN) (en : OpEntN) (k : Nat) (ls : List SRec)
    (κ : Val) : WProp := fun ρ =>
  (en.q = .unr → ρ = PMap.empty) ∧
  ∀ ls', Ext ls ls' ρ → ∀ k', k' < k → ∀ w : Val,
    (en.PB k' ls' w ─⋆
      erwp (ℍ := ℍ) Φ Tb Q k' ls' (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val w))) ρ

/-- Resuming `κ` at `w` runs `hnd H K[w]` (`ewp_kappa_resume`): four deterministic steps, for
free. -/
theorem erwp_kappa_resume {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hTd : Tb.Down) {Q : PostN}
    (hQ : Q.Down) (H : Val) (K : Kont) (w : Val) {k : Nat} {ls : List SRec} {ρ : WRes}
    (h : erwp (ℍ := ℍ) Φ Tb Q k ls (hndE H (K.plug (.val w))) ρ) :
    erwp (ℍ := ℍ) Φ Tb Q k ls (.app (.app (kappa H K) (.val (Val.inj₁ .unit))) (.val w)) ρ := by
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl (Kont.appL .hole w)) ?_
  refine erwp_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl (Kont.appL .hole w)) ?_
  refine erwp_det hΦ hTd hQ
    (fun μ => step1Only_plug (Head.seq μ _) rfl (Kont.appL .hole w)) ?_
  refine erwp_det hΦ hTd hQ (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, kappa_resume_subst]
  exact h

/-- A stop of an operation is final at every memory. -/
theorem final_opPlug {K : Kont} {r : Bool} {p : Val} {n : UInt32}
    (hn : payloadName p = some n) (hK : OpFree r n K) (μ : Heap) :
    Final (ℍ := ℍ) μ (K.plug (opE r p)) :=
  fun _ _ h => opPlug_no_step hn hK h

/-! ### The handler -/

/-- **A handler at the step index** (`[handle]`), by induction on the index; `ewp_handle_or`'s
cases at the end of the handled run. -/
theorem erwp_handle {Φ : LocFam} (hΦ : Φ.Down) (Tin Tout : OpTabN) (hTout : Tout.Down)
    (n₀ : UInt32) (hTin : ∀ m i, m ≠ n₀ → Tin m i = Tout m i) (qs hr hs : Val)
    (Qin Qout : PostN) (hQout : Qout.Down)
    (hq : ∀ i en, Tin n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag)
    (hunr : ∀ i en, Tin n₀ i = some en → en.abort = false → en.q = .unr)
    (hret : ∀ k ls v ρ, Qin k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val hr) (.val v)) ρ)
    (hop : ∀ i en, Tin n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ k ls v (κ : Val) ρ,
        (en.PA k ls v ⋆ KapRelN (ℍ := ℍ) Φ (opTableN Tout) Qout en k ls κ) ρ →
        erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val c) (.pair (.val v) κ.1)) ρ) ∧
      (en.abort = true → ∀ k ls v ρ, en.PA k ls v ρ →
        erwp (ℍ := ℍ) Φ (opTableN Tout) Qout k ls (.app (.val c) (.val v)) ρ)) :
    ∀ n ls e ρ, erwp (ℍ := ℍ) Φ (opTableN Tin) Qin n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN Tout) Qout n ls (hndE (hndVal n₀ qs hr hs) e) ρ := by
  have hLin := opTableN_local Tin
  have hLout := opTableN_local Tout
  have hDout := opTableN_down hTout
  have hPD := erwpPost_down hDout hQout
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ls e ρ h
  set H := hndVal n₀ qs hr hs with hH
  rw [erwp_eq]
  show rwpG (ℍ := ℍ) Φ _ n ls ((hndK H).plug e) ρ
  refine rwpG_bind hΦ (hndK H) ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwp_unfold_at hLin le_rfl h)
  -- what the continuations of the handled run are owed, read through the induction hypothesis
  have hcontIH : ∀ k', k' < k → ∀ ls'' e'' τ,
      erwpC (ℍ := ℍ) Φ (opTableN Tin) Qin n k' ls'' e'' τ →
      erwpC (ℍ := ℍ) Φ (opTableN Tout) Qout n k' ls'' (hndE H e'') τ := by
    intro k' hk' ls'' e'' τ hc
    simp only [erwpC, show k' < n by omega, if_true] at hc ⊢
    exact ih k' (by omega) ls'' e'' τ hc
  rcases ht with ⟨v, rfl, hv⟩ | ht | ht
  · -- `[ret]`
    exact rwpG_det hΦ (hPD _) (fun μ => step1Only_plug (Head.hret μ n₀ qs hr hs v) rfl .hole)
      (erwp_unfold_at hLout hk (hret k ls' v σ hv))
  · -- a stop at a non-abortive operation
    obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, hcont⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n₀
    · -- `[op]` at the handler's name: the clause, with `κ`
      subst hm
      obtain ⟨c, hc, hna, -⟩ := hop i en hT
      have hqu := hunr i en hT ha
      refine rwpG_det hΦ (hPD _)
        (fun μ => step1Only_plug (Head.hop μ m i qs hr hs c v K₁ hc hK₁) rfl .hole) ?_
      rw [hq i en hT ha, kappaAt_tag, hqu]
      refine erwp_unfold_at hLout hk (hna ha k ls' v
        ⟨kappa H K₁, by unfold kappa; exact .lam⟩ σ ⟨ρa, ρk, hcak, hA, hu, ?_⟩)
      intro ls'' he k' hk' w τ₁ τ₂ hB hcτ
      have h₁ := hcontIH k' hk' _ _ _ ((hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ)
      simp only [erwpC, show k' < n by omega, if_true] at h₁
      exact erwp_kappa_resume hΦ hDout hQout H K₁ w h₁
    · -- an operation of another name passes outward
      have hKo : ((hndK H).comp K₁).HasHnd m = false := by
        rw [hasHnd_comp, hndK_hasHnd, hK₁]; simpa using Ne.symm hm
      have ht' : (hndK H).plug (K₁.plug (performE (.val (opPayload m i v)))) =
          ((hndK H).comp K₁).plug (opE false (opPayload m i v)) := by
        rw [Kont.plug_comp]; rfl
      rw [ht']
      refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
        ⟨(hndK H).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, (hTin m i hm) ▸ hT, ha⟩
          ⟨ρa, ρk, hcak, hA, hu, fun ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
            fun hq' => ?_⟩⟩⟩))
      · rw [Kont.plug_comp]
        exact hcontIH k' hk' _ _ _ ((hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ)
      · intro P hP
        show P k ls'' (((hndK H).comp K₁).dead.plug _) ρk
        rw [dead_comp, dead_hndK]
        exact (hcont ls'' he).2 hq' P hP
  · -- a stop at an abortive operation
    obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩ := pure_sep_iff.mp hp
    by_cases hm : m = n₀
    · -- `[unwind]` at the handler's name: the clause; the continuation is dropped
      subst hm
      obtain ⟨c, hc, -, hab⟩ := hop i en hT
      refine rwpG_det hΦ (hPD _)
        (fun μ => step1Only_plug (Head.hunwind μ m i qs hr hs c v K₁ hc hK₁) rfl .hole) ?_
      refine rwpG_garbage (rwpG_mono (fun _ _ _ _ ⟨τ₁, τ₂, hcτ, hq', hnτ⟩ =>
        ⟨τ₁, τ₂, hcτ, hnτ, hq'⟩) (rwpG_frame (fun _ τ => NoOwn τ) (fun _ _ _ _ h => h) hcan
          (erwp_unfold_at hLout hk (hab ha k ls' v ρa hPA)) hnn))
    · -- an abortive operation of another name passes outward
      have hKo : ((hndK H).comp K₁).Catches m = false := by
        rw [catches_comp, hndK_catches, hK₁]; simpa using Ne.symm hm
      have ht' : (hndK H).plug (K₁.plug (raiseE (.val (opPayload m i v)))) =
          ((hndK H).comp K₁).plug (opE true (opPayload m i v)) := by
        rw [Kont.plug_comp]; rfl
      rw [ht']
      exact rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
        ⟨(hndK H).comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, (hTin m i hm) ▸ hT, ha⟩
          ⟨ρa, ρn, hcan, ⟨hPA, hnA⟩, hnn⟩⟩))

end BoCa.Fig16.LogRel.Core.DtorUnwind.SI

end

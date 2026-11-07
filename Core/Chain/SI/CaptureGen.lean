import Core.Chain.SI.CaptureHeap

/-!
# A handler whose clauses hand `κ` out, at `cerwp`

A scheduler that stores several continuations holds them as values: each task runs under a
handler whose clause returns the stopped task's continuation and payload to the scheduler, which
keeps them and resumes or cancels them later. `cerwp_gen` is `[handle]` for such a handler, one
handled run at a time: at a return the answer clause, at a stop the clause, given `κ` as the
operation's capture cell and the handled computation's own continuation share (`contShareC` at
the handled table). Resuming `κ` runs `hnd H K[w]` (`cerwp_kappaC_resume`), which the scheduler
proves by `cerwp_gen` again from that share; cancelling `κ` runs the share's cancel obligation
(`cerwp_kappaC_cancel`). Every operation of the handled table must be the handler's: nothing
passes outward, so no continuation has to be reinstalled, and no induction on the index is
needed.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE kappa kappaC
  kappaCell kappaAt capTag clauseAt hndVal ccatchE)

/-- The empty table: nothing may stop. -/
def OpTabC.emptyC : OpTabC := fun _ _ => none

theorem opTabC_emptyC_down : OpTabC.emptyC.Down where
  pa := fun _ _ _ h => by cases h
  fin := fun _ _ _ _ h => by cases h

/-! ### `κ` at `cerwp` -/

/-- **The capture cell's allocation** (`erwp_kappaCell` at `cerwp`). -/
theorem cerwp_kappaCell {Tb : TableC} (hL : Tb.Local) (hTd : Tb.Down) {Q : PostCV}
    (hQ : Q.Down) {F : WRes → Prop} (hasCancel : Bool) (H : Val) (K : Kont) (Kc : Kont)
    {n : Nat} {ls : List SRec} {O : List FrameRec} {ρ : WRes}
    (h : ∀ (ℓ : Loc) (ρ' : WRes), ResU.CompS ρ (ResU.single ℓ (CellU.ownOf Val.unit)) ρ' →
      cerwp (ℍ := ℍ) Tb Q F (n - 1) ls O (Kc.plug (kappaC hasCancel ℓ H K)) ρ') :
    cerwp (ℍ := ℍ) Tb Q F n ls O (Kc.plug (kappaCell hasCancel H K)) ρ := by
  have e : Kc.plug (kappaCell hasCancel H K) =
      (Kc.comp (.appR (.val (.lam (BoLo.kappaCBody hasCancel H K))) .hole)).plug
        (.app (.val (.prim .alloc)) (.val Val.unit)) := by
    rw [Kont.plug_comp]; rfl
  rw [e]
  refine cerwp_allocX hL _ Val.unit (fun ℓ ρ' hc => ?_)
  rw [Kont.plug_comp]
  refine cerwp_det hTd hQ (fun μ => step1Only_plug (Head.beta μ _ (Val.loc ℓ)) rfl Kc) ?_
  rw [kappaCBody_subst]
  exact h ℓ ρ' hc

/-- **Resuming a `κ` that owns a cell** (`erwp_kappaC_resume` at `cerwp`): the cell is freed, one
step, and `hnd H K[w]` runs at the index left. -/
theorem cerwp_kappaC_resume {Tb : TableC} (hL : Tb.Local) (hTd : Tb.Down)
    {Q : PostCV} (hQ : Q.Down) {F : WRes → Prop} (hasCancel : Bool) (ℓ : Loc) (H : Val)
    (K : Kont) (w : Val) {k : Nat} {ls : List SRec} {O : List FrameRec} {ρ ρ₂ : WRes}
    (hc : ResU.CompS (ResU.single ℓ (CellU.ownOf Val.unit)) ρ₂ ρ)
    (h : cerwp (ℍ := ℍ) Tb Q F (k - 1) ls O (hndE H (K.plug (.val w))) ρ₂) :
    cerwp (ℍ := ℍ) Tb Q F k ls O
      (.app (.app (kappaC hasCancel ℓ H K) (.val (Val.inj₁ .unit))) (.val w)) ρ := by
  refine cerwp_det hTd hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl (Kont.appL .hole w)) ?_
  refine cerwp_det hTd hQ
    (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl (Kont.appL .hole w)) ?_
  refine cerwp_det hTd hQ
    (fun μ => step1Only_plug (Head.seq μ _) rfl (Kont.appL .hole w)) ?_
  refine cerwp_freeX hL (Kont.appL (Kont.seq .hole _) w) ℓ Val.unit hc ?_
  refine cerwp_det hTd hQ
    (fun μ => step1Only_plug (Head.seq μ _) rfl (Kont.appL .hole w)) ?_
  refine cerwp_det hTd hQ (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, kappa_resume_subst]
  exact h

/-- **Cancelling a cancellable `κ`** (`erwp_kappaC_cancel` at `cerwp`): the cell is freed, then
`ccatch (K†[raise …])` runs. -/
theorem cerwp_kappaC_cancel {Tb : TableC} (hL : Tb.Local) (hTd : Tb.Down)
    {Q : PostCV} (hQ : Q.Down) {F : WRes → Prop} (ℓ : Loc) (H : Val) (K : Kont) {k : Nat}
    {ls : List SRec} {O : List FrameRec} {ρ ρ₂ : WRes}
    (hc : ResU.CompS (ResU.single ℓ (CellU.ownOf Val.unit)) ρ₂ ρ)
    (h : cerwp (ℍ := ℍ) Tb Q F (k - 1) ls O
        (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))) ρ₂) :
    cerwp (ℍ := ℍ) Tb Q F k ls O (.app (kappaC true ℓ H K) (.val (Val.inj₂ .unit))) ρ := by
  refine cerwp_det hTd hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  refine cerwp_det hTd hQ (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
  refine cerwp_det hTd hQ (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  refine cerwp_freeX hL (Kont.seq .hole _) ℓ Val.unit hc ?_
  refine cerwp_det hTd hQ (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, kappa_cancel_subst]
  exact h

/-! ### The handler -/

/-- **A handler whose every operation is caught, one handled run at a time.** At a return, the
answer clause. At a stop of operation `i`, the clause at `i`, given the payload, `κ` (the capture
cell `ℓ` and the handled computation's continuation share, owning the records the stop owns),
under the frame condition the handled run had. -/
theorem cerwp_gen {Tin : OpTabC} {Qin Qout : PostCV} (hQout : Qout.Down)
    {F : WRes → Prop} (n₀ : UInt32) (qs hr hs : Val)
    (hTin : ∀ m i en, Tin m i = some en →
      m = n₀ ∧ en.q ≠ .unr ∧ capTag qs.1 i.toNat = en.q.tag)
    (hret : ∀ k ls O (v : Val) ρ, Qin k ls O v ρ →
      cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Qout F k ls O (.app (.val hr) (.val v)) ρ)
    (hop : ∀ i en, Tin n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      ∀ k ls O (v : Val) (ℓ : Loc) (K : Kont) (ρa ρk ρak ρ : WRes), en.oc O →
        en.PA k ls v ρa → contShareC en F k ls O K v (cerwpC (ℍ := ℍ) (opTableC Tin) Qin k) ρk →
        ResU.CompS ρa ρk ρak → ResU.CompS ρak (ResU.single ℓ (CellU.ownOf Val.unit)) ρ →
        cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Qout F (k - 1) ls O
          (.app (.val c) (.pair (.val v) (kappaC (cellCancel en.q) ℓ
            (hndVal n₀ qs hr hs) K))) ρ) :
    ∀ n ls O e ρ, cerwp (ℍ := ℍ) (opTableC Tin) Qin F n ls O e ρ →
      cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Qout F n ls O (hndE (hndVal n₀ qs hr hs) e) ρ := by
  intro n ls O e ρ h
  set H := hndVal n₀ qs hr hs with hH
  have hLin := opTableC_local Tin
  have hLout := opTableC_local OpTabC.emptyC
  have hDout := opTableC_down opTabC_emptyC_down
  have hPD := cerwpPost_down hDout hQout
  rw [cerwp_eq]
  show crwpG (ℍ := ℍ) F _ n ls O ((hndK H).plug e) ρ
  refine crwpG_bind (hndK H) ?_
  refine crwpG_mono_le (fun k hk ls' O' t σ ht => ?_) (cerwp_unfold_at hLin le_rfl h)
  rcases ht with ⟨v, rfl, hv⟩ | ⟨K₁, m, i, v, en, hp⟩
  · exact crwpG_det (hPD _ F) (fun μ => step1Only_plug (Head.hret μ n₀ qs hr hs v) rfl .hole)
      (cerwp_unfold_at hLout hk (hret k ls' O' v σ hv))
  · obtain ⟨⟨rfl, hK₁, hT, -, hoc⟩, ρa, ρk, hcak, hA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨rfl, hq, htag⟩ := hTin m i en hT
    obtain ⟨c, hc, hob⟩ := hop i en hT
    refine crwpG_det (hPD _ F)
      (fun μ => step1Only_plug (Head.hop μ m i qs hr hs c v K₁ hc hK₁) rfl .hole) ?_
    rw [htag, kappaAt_cell hq]
    refine cerwp_unfold_at hLout hk (cerwp_kappaCell hLout hDout hQout _ H K₁
      (.appR (.val c) (.pairR v .hole)) (fun ℓ ρ' hc₂ => ?_))
    refine hob k ls' O' v ℓ K₁ ρa ρk σ ρ' hoc hA ⟨fun hu => absurd hu hq, fun ls'' he =>
      ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, (hcont ls'' he).2⟩⟩ hcak hc₂
    have h₁ := (hcont ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
    simp only [cerwpC, show k' < n by omega, show k' < k by omega, if_true] at h₁ ⊢
    exact h₁

end BoCa.Fig16.LogRel.Core.Chain.SI

end

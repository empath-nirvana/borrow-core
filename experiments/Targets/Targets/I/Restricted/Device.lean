import GhostEnd.Frames
import Targets.I.Restricted.Core
import Targets.I.RunEnd
import Targets.I.Pins
import Targets.I.Routes

/-!
# The interaction — the proof device at Core σ=[] (RESTRUCTURE §3.7)

The device at `coreW`: `mono_core` (`vC_local`),
`stopVisible_core`, `shareResume_core`, `handleCompat_core` (`handle_compatC`), `wlaws_core`;
`i1_core` (PROVED AT σ=[]), `i2_core_abortive` (PROVED AT A RESTRICTION, abortive rows), `i3_core`
(PROVED AT σ=[]: `coreW` holds nothing), `i5_core`, `i5beta` (every world), `p11_core`, `redLaws_of_mono`; and
`embedsNil_core` (from `conservativeWB_core`).  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

theorem mono_core : Mono (coreW (ℍ := ℍ)) :=
  fun b A _ _ _ _ _ he h => vC_local b A he h

theorem stopVisible_core : StopVisible (coreW (ℍ := ℍ)) :=
  fun _ _ _ _ _ h => h

theorem shareResume_core : ShareResume (coreW (ℍ := ℍ)) := by
  intro T en n i K Φ ρ h _ i' he w
  rcases i' with ⟨ls', ⟨⟩⟩
  exact (h.2 ls' he).1 w

theorem handleCompat_core : HandleCompat (coreW (ℍ := ℍ)) := by
  intro Δ Γ Γ₁ Γ₂ Γr Γc e S E n A R ir ic _ hs hs₁ hr hc hn0 hnS hlen he
  exact semW₀_core.mpr (handle_compatC hs hs₁ hr hc hn0 hnS hlen (semW₀_core.mp he))


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun AStep1 performE raiseE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **`WLaws coreW`.** -/
theorem wlaws_core : WLaws (ℍ := ℍ) (coreW (ℍ := ℍ)) :=
  ⟨sliceShape_core, mono_core, extPre_core, effInterp_core, famEmpty_core, dataVals_core,
    shareMono_core, relLaws_core, adequateEvery_core⟩


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun Step1N performE raiseE opPayload cancelVal kappaC
  hndE hndVal kappa ccatchE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **I5.β at every world**: resuming `κ` at `w` runs `hnd H K[w]` (`ewp_kappa_resume`'s four
administrative steps, at `ewpW`). -/
theorem i5beta (M : SemWorld) : I5beta (ℍ := ℍ) M := by
  intro Tb H K w i Q ρ hTb h
  refine ewpW_step hTb (fun μ => (Step1N.head (Head.beta μ _ _) rfl).plug
    (Kont.appL .hole w)) i Q ρ ?_
  refine ewpW_step hTb (fun μ => (Step1N.head (Head.case₁ μ Val.unit _ _) rfl).plug
    (Kont.appL .hole w)) i Q ρ ?_
  refine ewpW_step hTb (fun μ => (Step1N.head (Head.seq μ _) rfl).plug (Kont.appL .hole w))
    i Q ρ ?_
  refine ewpW_step hTb (fun μ => Step1N.head (Head.beta μ _ w) rfl) i Q ρ ?_
  have e : ∀ (s u : Val), Expr.subst 0 w (Expr.subst 1 u (Expr.subst 2 s
      (hndE (Val.shift 3 0 H) ((Kont.shift 3 0 K).plug (Expr.var 0))))) =
      hndE H (K.plug (.val w)) := by
    intro s u
    simp only [hndE, Expr.subst, Expr.val, Val.val_shift]
    rw [Expr.subst_shift 2 0 2 s H.1 (by omega) (by omega),
      Expr.subst_shift 1 0 1 u H.1 (by omega) (by omega),
      Expr.subst_shift 0 0 0 w H.1 (by omega) (by omega), Expr.shift_zero,
      plug_shift_subst 2 K 0 2 s _ (by omega) (by omega),
      plug_shift_subst 1 K 0 1 u _ (by omega) (by omega),
      plug_shift_subst 0 K 0 0 w _ (by omega) (by omega), Kont.shift_zero]
    simp [Expr.subst]
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, e]
  exact h

theorem mutView_core (ℓ : Loc) (α : Life) (T : VTy) (δ : LSub) (i : Idx (coreW (ℍ := ℍ)).Stk) :
    mutView (coreW (ℍ := ℍ)) ℓ α T δ i = ptoMutS ℓ α i.1 (fun ls₀ => vCE (ℍ := ℍ) none true T ls₀ δ) :=
  ptoMutSW_core_eq ℓ α i T δ

/-- **`I1 coreW`**: `ewp_handle`'s `[op]` case. -/
theorem i1_core : I1 (ℍ := ℍ) (coreW (ℍ := ℍ)) := by
  intro S n E R δ qs hr hs j o K i ℓ ρk σ ρ hn0 hnS hNU hfo ha hsh hcell hc
  rcases i with ⟨ls, ⟨⟩⟩
  obtain ⟨-, hk⟩ := hsh
  have hTin : OpTabI.down (rowTabW (coreW (ℍ := ℍ)) (Row.ofEff n E 0 ++ S) δ) =
      Row.tab (ℍ := ℍ) (Row.ofEff n E 0 ++ S) δ := rowTabW_core _ _
  have hTout : OpTabI.down (rowTabW (coreW (ℍ := ℍ)) S δ) = Row.tab (ℍ := ℍ) S δ :=
    rowTabW_core _ _
  -- the rows are unr-free, so the operation is linear or affine
  have hq : o.q ≠ .unr := by
    obtain ⟨hm, -, -⟩ := Row.find_mem hfo
    have hf : Row.find (Row.ofEff n E 0 ++ S) n j = some o := by
      rw [Row.find_append, hfo]; rfl
    rcases hNU n j o hf with h | h
    · rw [h] at ha; cases ha
    · exact h
  have hκ : KapRel (Row.tab S δ) (fun ls v => vC true R ls δ v) (OpSig.ent δ ⟨n, j, o.q, o.A, o.B⟩)
      ls ⟨kappaC (o.q == .aff) ℓ (hndVal n qs hr hs) K, by unfold kappaC; exact .lam⟩ ρ := by
    refine ⟨fun h' => absurd h' hq, fun ls' he => ⟨fun w τ₁ τ₂ hB hcτ => ?_, fun hq' => ?_⟩⟩
    · obtain ⟨z, hz, hzτ⟩ := compS_exch hc hcτ
      have h₁ := (hk ls' (Ext.left hc he)).1 w τ₁ z hB hz
      simp only [ewpW_core_eq, opTabW_core_down, hTout] at h₁
      exact ewp_kappaC_resume (opTable_mono _) _ ℓ _ K w ⟨σ, z, ResU.CompS.comm hzτ, hcell, h₁⟩
    · have hq'' : o.q ≠ .lin := hq'
      have haff : o.q = .aff := by
        cases hh : o.q
        · exact absurd hh hq''
        · rfl
        · exact absurd hh hq
      have hco := (hk ls' (Ext.left hc he)).2 hq'
      have hcc := ewp_ccatch (T := OpTab.empty) (Tout := Row.tab S δ)
        (fun _ _ _ h => by simp [OpTab.empty] at h) hco
      simp only [haff]
      exact ewp_kappaC_cancel (opTable_mono _) ℓ _ K ⟨σ, ρk, ResU.CompS.comm hc, hcell, hcc⟩
  exact vC_kTy_of_kapRel o.A n j hκ

theorem mutFrameUW_core : MutFrameUW (ℍ := ℍ) (coreW (ℍ := ℍ)) := by
  intro Tb l A δ β hTb hP v e i Q ρ h
  rcases i with ⟨ls, ⟨⟩⟩
  rw [ewpW_core]
  refine ewpTS_M_frameU (TableI.down Tb) (tableI_down_abortive hTb) l A δ β
    (fun ls w σ hw => hP (ls, ()) w σ hw) v e ls (fun ls v => Q (ls, ()) v) ρ ?_
  simp only [ptoMutSW_core_eq, wpGW_core_eq] at h
  exact h

theorem immFrameUW_core : ImmFrameUW (ℍ := ℍ) (coreW (ℍ := ℍ)) := by
  intro Tb l A δ v e i Q hTb hadm hQ ρ h
  rcases i with ⟨ls, ⟨⟩⟩
  rw [ewpW_core]
  refine ewpTS_I_frameU (TableI.down Tb) (tableI_down_abortive hTb) l A δ hadm v e ls
    (fun ls v => Q (ls, ()) v) (fun ls₁ ls₂ w ρ he hp => hQ (ls₁, ()) (ls₂, ()) w ρ he hp) ρ ?_
  simp only [wpGW_core_eq] at h
  exact h

theorem resuming_abortive_empty {I : Type} {T : OpTabI I} (h : T.Resuming .abortive) :
    ∀ n j, T n j = none := by
  intro n j
  cases hT : T n j with
  | none => rfl
  | some en => exact absurd rfl (h n j en hT).2.2.1

theorem mutFrameW_core_abortive : MutFrameW (ℍ := ℍ) (coreW (ℍ := ℍ)) .abortive := by
  intro T l A δ β hT hP v e i Q ρ h
  have hE := resuming_abortive_empty hT
  have hab : Table.Abortive (opTable (OpTabI.down T)) :=
    fun _ _ _ _ _ hp => (opTabW_core_empty hE hp).elim
  rcases i with ⟨ls, ⟨⟩⟩
  rw [ewpW_core, opTabW_core_down]
  refine ewpTS_M_frameU (opTable (OpTabI.down T)) hab l A δ β
    (fun ls w σ hw => hP (ls, ()) w σ hw) v e ls (fun ls v => Q (ls, ()) v) ρ ?_
  obtain ⟨ρ₁, ρ₂, hc, ho, h⟩ := h
  refine ⟨ρ₁, ρ₂, hc, ho, ?_⟩
  obtain ⟨ρ₃, ρ₄, hc', hv, h⟩ := h
  refine ⟨ρ₃, ρ₄, hc', hv, ?_⟩
  obtain ⟨β', hβ'⟩ := h
  refine ⟨β', fun α hα => ⟨fun σ₁ σ₂ hm hcm => ?_, (hβ' α hα).2⟩⟩
  have hw := (hβ' α hα).1 σ₁ σ₂ (by rw [ptoMutSW_core_eq]; exact hm) hcm
  rw [ewpW_core_eq, opTabW_core_down] at hw
  refine wpG_mono (fun ls'' t σ hq => ?_) ((ewp_abortive hab).mp hw)
  rcases hq with ⟨v', rfl, hv'⟩ | hq
  · obtain ⟨hall, hout⟩ := hv'
    exact ⟨fun w τ₁ τ₂ hw' hcw τ₃ τ₄ hv'' hcv => Or.inl ⟨v', rfl, hall w τ₁ τ₂ hw' hcw τ₃ τ₄ hv'' hcv⟩,
      hout⟩
  · exact (opTabW_core_empty hE hq).elim

theorem immFrameW_core_abortive : ImmFrameW (ℍ := ℍ) (coreW (ℍ := ℍ)) .abortive := by
  intro T l A δ v e i Q hT hadm hQ _ ρ h
  have hE := resuming_abortive_empty hT
  have hab : Table.Abortive (opTable (OpTabI.down T)) :=
    fun _ _ _ _ _ hp => (opTabW_core_empty hE hp).elim
  rcases i with ⟨ls, ⟨⟩⟩
  rw [ewpW_core, opTabW_core_down]
  refine ewpTS_I_frameU (opTable (OpTabI.down T)) hab l A δ hadm v e ls
    (fun ls v => Q (ls, ()) v) (fun ls₁ ls₂ w ρ he hp => ?_) ρ ?_
  · rcases hp with ⟨v', rfl, hv'⟩ | hp
    · exact Or.inl ⟨v', rfl, hQ (ls₁, ()) (ls₂, ()) v' ρ he hv'⟩
    · exact (opTabW_core_empty hE hp).elim
  obtain ⟨ρ₁, ρ₂, hc, ho, h⟩ := h
  refine ⟨ρ₁, ρ₂, hc, ho, ?_⟩
  obtain ⟨ρ₃, ρ₄, hc', hv, h⟩ := h
  refine ⟨ρ₃, ρ₄, hc', hv, ?_⟩
  obtain ⟨β', hβ'⟩ := h
  refine ⟨β', fun α hα => ⟨fun ls' hadd hrec σ₁ σ₂ hm hcm => ?_, (hβ' α hα).2⟩⟩
  have hw := (hβ' α hα).1 ls' hadd hrec σ₁ σ₂ hm hcm
  rw [ewpW_core_eq, opTabW_core_down] at hw
  refine wpG_mono (fun ls'' t σ hq => ?_) ((ewp_abortive hab).mp hw)
  rcases hq with ⟨v', rfl, hv'⟩ | hq
  · obtain ⟨hw', hout⟩ := hv'
    exact ⟨fun τ₁ τ₂ ho' hco τ₃ τ₄ hv'' hcv => Or.inl ⟨v', rfl, hw' τ₁ τ₂ ho' hco τ₃ τ₄ hv'' hcv⟩,
      hout⟩
  · exact (opTabW_core_empty hE hq).elim

theorem framesW_core_abortive : FramesW (ℍ := ℍ) (coreW (ℍ := ℍ)) .abortive :=
  ⟨immFrameUW_core, mutFrameUW_core, immFrameW_core_abortive, mutFrameW_core_abortive⟩

theorem spanBorrows_core_abortive :
    SpanBorrows (coreW (ℍ := ℍ)) OutJ.core admClosedOp .abortive := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Δ Γ A B S d x hΓ _ hsc hfA hfB hR hAd hdc hd
    exact semW₀_core.mpr (withbor1U_compatX x hΓ hsc hfA hfB
      (rowSpan_abortive_iff_unwind.mp ⟨hR, hAd⟩) hdc (semW₀_core.mp hd))
  · intro Δ Γ A B S d x hΓ _ hside hfA hfB hR hAd hdc hd
    exact semW₀_core.mpr (withbor2U_compatX x hΓ hside hfA hfB
      (rowSpan_abortive_iff_unwind.mp ⟨hR, hAd⟩) hdc (semW₀_core.mp hd))
  · intro Δ Γ a A B S d x hΓ _ hfA hfB hR hAd hdc hd
    exact semW₀_core.mpr (withbor3U_compatX x hΓ hfA hfB
      (rowSpan_abortive_iff_unwind.mp ⟨hR, hAd⟩) hdc (semW₀_core.mp hd))
  · intro Δ Γ a A B S x hΓ _ hfA hfB hR hAd
    exact semW₀_core.mpr (withloadU_compatX x hΓ hfA hfB
      (rowSpan_abortive_iff_unwind.mp ⟨hR, hAd⟩))
  · intro Δ Γ A B S d x hΓ hsA hsB hfA hfB hR hAd hdc hd
    exact semW₀_core.mpr (sliceBorrowMU_compatX x hΓ hsA hsB hfA hfB
      (rowSpan_abortive_iff_unwind.mp ⟨hR, hAd⟩) hdc (semW₀_core.mp hd))
  · intro Δ Γ A B S d x hΓ hsc hsA hsB hfA hfB hR hAd hdc hd
    exact semW₀_core.mpr (sliceBorrowIU_compatX x hΓ hsc hsA hsB hfA hfB
      (rowSpan_abortive_iff_unwind.mp ⟨hR, hAd⟩) hdc (semW₀_core.mp hd))

/-- **`I2 coreW OutJ.core admClosedOp .abortive`**: PROVED AT A RESTRICTION (abortive rows). -/
theorem i2_core_abortive : I2 (ℍ := ℍ) (coreW (ℍ := ℍ)) OutJ.core admClosedOp .abortive :=
  ⟨arises_core, stopVisible_core, shareResume_core, framesW_core_abortive,
    spanBorrows_core_abortive⟩

/-- **`I3 coreW`**: PROVED AT σ=[] (`coreW` holds nothing, by definition). -/
theorem i3_core : I3 (ℍ := ℍ) (coreW (ℍ := ℍ)) := by
  intro T en n i K Φ ρ h hlin _ i' he
  rcases i' with ⟨ls', ⟨⟩⟩
  rw [ewpW_core]
  have hd : TableI.down (cancelTabW (fun _ _ => none) (fun i'' =>
      (∀ f ∈ ((coreW (ℍ := ℍ)).held i'').1, f ∈ ((coreW (ℍ := ℍ)).held (ls', ())).1) ∧
      (∀ x ∈ ((coreW (ℍ := ℍ)).held i'').2, x ∈ ((coreW (ℍ := ℍ)).held (ls', ())).2))) =
      cancelTab OpTab.empty := by
    funext ls t Φ' ρ'
    exact propext (cancelTabW_core (fun _ => ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩))
  rw [hd]
  exact (h.2 ls' he).2 hlin

theorem antiFrameW_core : AntiFrameW (ℍ := ℍ) (coreW (ℍ := ℍ)) := by
  intro Tb ℓ α T δ Q i e hTb ρ h
  rcases i with ⟨ls, ⟨⟩⟩
  rw [ewpW_core]
  obtain ⟨ρm, ρr, hc, hm, hr⟩ := h
  rw [mutView_core] at hm
  refine GhostEnd.ewpTS_M_antiFrameR (TableI.down Tb) (tableI_down_mono hTb) ℓ α T δ
    (fun ls v => Q (ls, ()) v) ls e ρ ⟨ρm, ρr, hc, hm, ?_⟩
  intro X hX
  refine hr (fun i e => X i.1 e) ?_
  intro i e ρ hF
  refine hX i.1 e ρ ?_
  simp only [antiFW, wpGW_core_eq, mutView_core] at hF
  exact hF

theorem frameW_core : FrameW (ℍ := ℍ) (coreW (ℍ := ℍ)) := by
  intro T K hH hC hU Fr hFs hFe hW Q₁ Q hk i e ρ h ρ₂ ρ' hF hc
  rcases i with ⟨ls, ⟨⟩⟩
  rw [ewpW_core, opTabW_core_down] at h ⊢
  refine ewp_frame_plain (OpTabI.down T) K hH hC (fun ls => Fr (ls, ()))
    (fun ls ls' hs => hFs [] (ls, ()) [] (ls', ()) (.val .unit) ⟨fun _ => Iff.rfl, hs⟩ hs)
    (fun ls ls' ρ he hf => hFe (ls, ()) (ls', ()) ρ he hf) ?_ ?_ (fun ls v => Q₁ (ls, ()) v)
    (fun ls v => Q (ls, ()) v) ?_ h hF hc
  · intro n j en hT hq ls ρ hf
    obtain ⟨en₀, hT₀, rfl⟩ := opTabI_down_some.mp hT
    exact hW n j en₀ hT₀ hq (ls, ()) ρ hf
  · intro n j en hT hq
    obtain ⟨en₀, hT₀, rfl⟩ := opTabI_down_some.mp hT
    exact absurd hq (hU n j en₀ hT₀)
  · intro ls v ρ hq
    have := hk (ls, ()) v ρ hq
    rw [ewpW_core, opTabW_core_down] at this
    exact this

/-- **`I5 coreW`**: PROVED AT σ=[]. -/
theorem i5_core : I5 (ℍ := ℍ) (coreW (ℍ := ℍ)) := ⟨i5beta _, antiFrameW_core, frameW_core⟩


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun AStep1 Step1N performE raiseE opPayload)

/-- A pure head step that allocates nothing is the first step of every run from its plugged redex
that does not end there. -/
theorem arun_first {A : Alloc} {k k' : Nat} {μ μ' : Heap} {K : Kont} {a a' t : Expr}
    (hh : ∀ μ, Head (ℍ := ℍ) μ a μ a') (hn : a.allocs = false)
    (hr : ARun (ℍ := ℍ) A k μ (K.plug a) k' μ' t) (hne : t ≠ K.plug a) :
    ARun (ℍ := ℍ) A k μ (K.plug a') k' μ' t := by
  cases hr with
  | refl => exact absurd rfl hne
  | more s r =>
      have s₀ : AStep1 (ℍ := ℍ) A k μ (K.plug a) k μ (K.plug a') :=
        (Step1N.plug K (Step1N.head (hh μ) hn)).toAStep1 A k
      obtain ⟨rfl, rfl, rfl⟩ := AStep1.deterministic s s₀
      exact r

/-- `wpGW` sheds the step `K[a] ↦ K[a']` when its postcondition rejects `K[a]`. -/
theorem wpGW_strip {M : SemWorld} {K : Kont} {a a' : Expr} (hh : ∀ μ, Head (ℍ := ℍ) μ a μ a')
    (hn : a.allocs = false) {i : Idx M.Stk} {Q : Idx M.Stk → Expr → WProp}
    (hQ : ∀ i' ρ', ¬ Q i' (K.plug a) ρ') {ρ : WRes} (h : wpGW (ℍ := ℍ) M i (K.plug a) Q ρ) :
    wpGW (ℍ := ℍ) M i (K.plug a') Q ρ := by
  intro ρf fρ ps h₁ h₂ h₃ A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', i', a₁, a₂, a₃, a₄, a₅, a₆, ⟨k', hr⟩, a₈, a₉, a₁₀,
    a₁₁, a₁₂, a₁₃⟩ := h ρf fρ ps h₁ h₂ h₃ A k
  refine ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', i', a₁, a₂, a₃, a₄, a₅, a₆,
    ⟨k', arun_first hh hn hr ?_⟩, a₈, a₉, a₁₀, a₁₁, a₁₂, a₁₃⟩
  rintro rfl
  exact hQ _ _ a₁₃

/-- A plugged redex is neither a value nor a stop of an operation table. -/
theorem plug_not_post {M : SemWorld} {K : Kont} {a a' : Expr} (hh : ∀ μ, Head (ℍ := ℍ) μ a μ a')
    (T : OpTabI (Idx M.Stk)) (Q : Idx M.Stk → Val → WProp) (P : Idx M.Stk → Expr → WProp)
    (i' : Idx M.Stk) (ρ' : WRes) :
    ¬ (valPostI Q i' (K.plug a) ρ' ∨ opTabW M T i' (K.plug a) P ρ') := by
  have hs : Step1 (ℍ := ℍ) (fun _ => none) (K.plug a) (fun _ => none) (K.plug a') :=
    ⟨K, a, a', rfl, rfl, hh _⟩
  rintro (⟨v, hv, -⟩ | ⟨K', n, j, v, en, hp⟩ | ⟨K', n, j, v, en, hp⟩)
  · rw [hv] at hs; exact BoCa.BoLo.no_step_val hs
  · obtain ⟨⟨ht, hK, -, -⟩, -⟩ := pure_sep_iff.mp hp
    rw [ht] at hs
    exact opPlug_no_step (r := false) (payloadName_opPayload n j v) hK hs
  · obtain ⟨⟨ht, hK, -, -⟩, -⟩ := pure_sep_iff.mp hp
    rw [ht] at hs
    exact opPlug_no_step (r := true) (payloadName_opPayload n j v) hK hs

/-- **`RedLaws`** at every world whose operation tables are monotone in what they owe. -/
theorem redLaws_of_mono {M : SemWorld} (hM : ∀ T, TableI.Mono (opTabW M T)) :
    RedLaws (ℍ := ℍ) M := by
  intro K a a' i T Q ρ hh hn
  constructor
  · intro h
    exact ewpW_fold (hM T) (wpGW_strip hh hn (fun i' ρ' => plug_not_post hh T Q _ i' ρ')
      (ewpW_unfold (hM T) h))
  · exact ewpW_step (hM T) (fun μ => Step1N.plug K (Step1N.head (hh μ) hn)) i Q ρ

/-- Core's operation tables are monotone in what they owe (`opTable_mono`). -/
theorem opTabW_mono_core (T : OpTabI (Idx Unit)) : TableI.Mono (opTabW (coreW (ℍ := ℍ)) T) := by
  intro i t Φ Φ' ρ hΦ h
  rcases i with ⟨ls, ⟨⟩⟩
  exact opTabW_core.mpr (opTable_mono _ ls t _ _ ρ (fun ls e ρ h => hΦ (ls, ()) e ρ h)
    (opTabW_core.mp h))

/-- **`RedLaws coreW`.** -/
theorem redLaws_core : RedLaws (ℍ := ℍ) (coreW (ℍ := ℍ)) := redLaws_of_mono opTabW_mono_core

/-- **`P11 coreW`.** -/
theorem p11_core : P11 (ℍ := ℍ) (coreW (ℍ := ℍ)) := ⟨handleCompat_core, redLaws_core⟩


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **`EmbedsNil coreW`**, from `ConservativeWB coreW` at the reflexive future (`ExtPre`). -/
theorem embedsNil_core : EmbedsNil (ℍ := ℍ) (coreW (ℍ := ℍ)) :=
  fun b A ls δ v ρ hA h => conservativeWB_core b A ls δ v ρ hA h (ls, ()) (extPre_core.1 _ _)


end Targets

end

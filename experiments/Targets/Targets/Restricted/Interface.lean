import Targets.Restricted.CoreLaws
import GhostEnd.Frames

/-!
# Targets — the interaction interface at Core σ=[] (DESIGN §9 items 8, 9, 10, 13)

* **Generic** (every world): `wpGW_mono`, `wpGW_step`, `ewpW_fold`, `ewpW_unfold`, `ewpW_step`
  (`wpGW`'s shape is fixed, so the step lemmas of `Core/EffWp.lean` hold at every W), and
  `i5beta` : `I5beta M` for every `M`, `ewp_kappa_resume`'s four administrative steps at W.
* `i1_core : I1 coreW`: `ewp_handle`'s `[op]` case (`ewp_kappa_resume`, `ewp_kappa_cancel`,
  `ewp_ccatch`) and `vC_kTy_of_kapRel`.  **PROVED AT σ=[]**.
* `i2_core_abortive : I2 coreW OutJ.core admClosedOp .abortive`: `Arises`, `StopVisible`,
  `ShareResume` by unfolding; `FramesW coreW .abortive` from `ewpTS_I_frameU`/`ewpTS_M_frameU` (at
  `.abortive` the resuming tables are empty, so their frames are the abortive ones); `SpanBorrows`
  from the six `*U` compatibility lemmas through `rowSpan_abortive_iff_unwind`.  **PROVED AT A
  RESTRICTION** (abortive rows): at σ = [] nothing is held, and no lend spans a stop.
* `i3_core : I3 coreW`: `contShare`'s cancel conjunct `cancelOwed`, through `cancelTabW_core`.
  **PROVED AT A RESTRICTION** (nothing held at σ = [], so the closing clause is vacuous).
* `i5_core : I5 coreW`: `i5beta`, GhostEnd's `ewpTS_M_antiFrameR` through `ptoMutSW_core`, and
  `ewp_frame_plain` through the transports.  **PROVED AT σ=[]**.  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun Step1N performE raiseE opPayload cancelVal
  hndE hndVal kappa ccatchE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Generic: the effectful wp at every world -/

theorem wpGW_mono {M : SemWorld} {i : Idx M.Stk} {e : Expr} {Q Q' : Idx M.Stk → Expr → WProp}
    (hQ : ∀ i t ρ, Q i t ρ → Q' i t ρ) {ρ : WRes} (h : wpGW (ℍ := ℍ) M i e Q ρ) :
    wpGW (ℍ := ℍ) M i e Q' ρ := by
  intro ρf fρ ps h1 h2 h3 A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', i', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    a12, a13⟩ := h ρf fρ ps h1 h2 h3 A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', i', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    a12, hQ _ _ _ a13⟩

/-- One pure step in front of a `wpGW` (`wpG_step` at W). -/
theorem wpGW_step {M : SemWorld} {e e' : Expr} (h : ∀ μ : Heap, Step1N (ℍ := ℍ) μ e μ e')
    (i : Idx M.Stk) (Q : Idx M.Stk → Expr → WProp) :
    Entails (wpGW (ℍ := ℍ) M i e' Q) (wpGW (ℍ := ℍ) M i e Q) := by
  intro ρ hw ρf fρ ps hf hc hF A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', i', h₁, h₂, h₃, h₅, h₆, h₇, ⟨j, h₈⟩, h₉, hA, hB,
    hF', hS, hC⟩ := hw ρf fρ ps hf hc hF A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', i', h₁, h₂, h₃, h₅, h₆, h₇,
    ⟨j, BoCa.BoLo.ARun.cons (h μ) h₈⟩, h₉, hA, hB, hF', hS, hC⟩

theorem ewpW_fold {M : SemWorld} {Tb : TableI (Idx M.Stk)} (hTb : Tb.Mono)
    {Q : Idx M.Stk → Val → WProp} {i : Idx M.Stk} {e : Expr} {ρ : WRes}
    (h : wpGW (ℍ := ℍ) M i e (fun i' t ρ' => valPostI Q i' t ρ' ∨
      Tb i' t (fun i e => ewpW (ℍ := ℍ) M i e Tb Q) ρ') ρ) :
    ewpW (ℍ := ℍ) M i e Tb Q ρ := by
  intro P hP
  exact hP i e ρ (wpGW_mono (fun i' t ρ' hq => hq.imp id (hTb i' t _ P ρ'
    (fun _ _ _ h' => h' P hP))) h)

theorem ewpW_unfold {M : SemWorld} {Tb : TableI (Idx M.Stk)} (hTb : Tb.Mono)
    {Q : Idx M.Stk → Val → WProp} {i : Idx M.Stk} {e : Expr} {ρ : WRes}
    (h : ewpW (ℍ := ℍ) M i e Tb Q ρ) :
    wpGW (ℍ := ℍ) M i e (fun i' t ρ' => valPostI Q i' t ρ' ∨
      Tb i' t (fun i e => ewpW (ℍ := ℍ) M i e Tb Q) ρ') ρ :=
  h (fun i e ρ => wpGW (ℍ := ℍ) M i e (fun i' t ρ' => valPostI Q i' t ρ' ∨
      Tb i' t (fun i e => ewpW (ℍ := ℍ) M i e Tb Q) ρ') ρ)
    (fun _ _ _ h' => wpGW_mono (fun i' t ρ' hq => hq.imp id (hTb i' t _ _ ρ'
      (fun _ _ _ h'' => ewpW_fold hTb h''))) h')

/-- One pure step in front of an `ewpW` (`ewp_step` at W). -/
theorem ewpW_step {M : SemWorld} {Tb : TableI (Idx M.Stk)} (hTb : Tb.Mono) {e e' : Expr}
    (h : ∀ μ : Heap, Step1N (ℍ := ℍ) μ e μ e') (i : Idx M.Stk) (Q : Idx M.Stk → Val → WProp) :
    Entails (ewpW (ℍ := ℍ) M i e' Tb Q) (ewpW (ℍ := ℍ) M i e Tb Q) :=
  fun ρ h' => ewpW_fold hTb (wpGW_step h i _ ρ (ewpW_unfold hTb h'))

/-- **I5.β at every world**: resuming `κ` at `w` runs `hnd H K[w]` (`ewp_kappa_resume`'s four
administrative steps, at `ewpW`). -/
theorem i5beta (M : SemWorld) : I5beta (ℍ := ℍ) M := by
  intro Tb n H K w i Q ρ hTb h
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

/-! ### Transports -/

theorem mutView_core (ℓ : Loc) (α : Life) (T : VTy) (δ : LSub) (i : Idx (coreW (ℍ := ℍ)).Stk) :
    mutView (coreW (ℍ := ℍ)) ℓ α T δ i = ptoMutS ℓ α i.1 (fun ls₀ => vCE (ℍ := ℍ) none true T ls₀ δ) :=
  ptoMutSW_core_eq ℓ α i T δ

theorem tableI_down_mono {Tb : TableI (Idx Unit)} (h : Tb.Mono) : Table.Mono (TableI.down Tb) :=
  fun ls t _ _ ρ hΦ hp => h (ls, ()) t _ _ ρ (fun i e ρ hi => hΦ i.1 e ρ hi) hp

theorem tableI_down_abortive {Tb : TableI (Idx Unit)} (h : Tb.Abortive) :
    Table.Abortive (TableI.down Tb) :=
  fun ls t _ _ ρ hp => h (ls, ()) t _ _ ρ hp

/-! ### I1 at Core σ=[] -/

/-- **`I1 coreW`**: `ewp_handle`'s `[op]` case. -/
theorem i1_core : I1 (ℍ := ℍ) (coreW (ℍ := ℍ)) := by
  intro S n E R δ hr hs j o K i ρ hn0 hnS _ hfo ha hsh
  rcases i with ⟨ls, ⟨⟩⟩
  obtain ⟨hu, hk⟩ := hsh
  have hTin : OpTabI.down (rowTabW (coreW (ℍ := ℍ)) (Row.ofEff n E 0 ++ S) δ) =
      Row.tab (ℍ := ℍ) (Row.ofEff n E 0 ++ S) δ := rowTabW_core _ _
  have hTout : OpTabI.down (rowTabW (coreW (ℍ := ℍ)) S δ) = Row.tab (ℍ := ℍ) S δ :=
    rowTabW_core _ _
  have hκ : KapRel (Row.tab S δ) (fun ls v => vC true R ls δ v) (OpSig.ent δ ⟨n, j, o.q, o.A, o.B⟩)
      ls ⟨kappa n (hndVal n hr hs) K, by unfold kappa; exact .lam⟩ ρ := by
    refine ⟨hu, fun ls' he => ⟨fun w σ₁ σ₂ hB hc => ?_, fun hq => ?_⟩⟩
    · have h₁ := (hk ls' he).1 w σ₁ σ₂ hB hc
      simp only [ewpW_core_eq, opTabW_core_down, hTout] at h₁
      exact ewp_kappa_resume (opTable_mono _) n _ K w h₁
    · refine ewp_kappa_cancel (opTable_mono _) n _ K ?_
      have hC0 : (hndK (hndVal n hr hs)).Catches 0 = false := by
        rw [hndK_catches]; simpa using hn0
      have hco := (hk ls' he).2 hq (n :: K.hndNames) List.mem_cons_self
        (fun x hx => List.mem_cons_of_mem _ hx)
      rw [hTin] at hco
      refine ewp_ccatch (Tin := Row.tab (Row.ofEff n E 0 ++ S) δ) _ hC0 (fun m j' en hm h => ?_) hco
      have hmn : m ≠ n := fun e => hm (e ▸ List.mem_cons_self)
      simpa [Row.tab, Row.find_append, Row.find_ofEff_ne n E 0 m j' hmn] using h
  exact vC_kTy_of_kapRel o.A n j hκ

/-! ### I2 at Core σ=[], abortive rows -/

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

/-- A table with no entry has no stop. -/
theorem opTabW_core_empty {T : OpTabI (Idx Unit)} (hT : ∀ n j, T n j = none) {ls : List SRec}
    {t : Expr} {Φ : List SRec → Expr → WProp} {ρ : WRes} :
    ¬ opTable (OpTabI.down T) ls t Φ ρ := by
  rintro (⟨K, n, j, v, en, h⟩ | ⟨K, n, j, v, en, h⟩) <;>
  · obtain ⟨⟨-, -, hT', -⟩, -⟩ := pure_sep_iff.mp h
    simp [OpTabI.down, hT n j] at hT'

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

/-! ### I3 at Core σ=[] -/

/-- **`I3 coreW`**: PROVED AT A RESTRICTION (nothing held at σ = []). -/
theorem i3_core : I3 (ℍ := ℍ) (coreW (ℍ := ℍ)) := by
  intro T en n i K Φ ρ h hlin _ i' he N hN hNK
  rcases i' with ⟨ls', ⟨⟩⟩
  rw [ewpW_core]
  have hd : TableI.down (cancelTabW T N (fun i'' =>
      (∀ f ∈ ((coreW (ℍ := ℍ)).held i'').1, f ∈ ((coreW (ℍ := ℍ)).held (ls', ())).1) ∧
      (∀ x ∈ ((coreW (ℍ := ℍ)).held i'').2, x ∈ ((coreW (ℍ := ℍ)).held (ls', ())).2))) =
      cancelTab (OpTabI.down T) N := by
    funext ls t Φ' ρ'
    exact propext (cancelTabW_core (fun _ => ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩))
  rw [hd]
  exact (h.2 ls' he).2 hlin N hN hNK

/-! ### I5 at Core σ=[] -/

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
  intro T K hH hC hN hU Fr hFs hFe hW Q₁ Q hk i e ρ h ρ₂ ρ' hF hc
  rcases i with ⟨ls, ⟨⟩⟩
  rw [ewpW_core, opTabW_core_down] at h ⊢
  refine ewp_frame_plain (OpTabI.down T) K hH hC hN (fun ls => Fr (ls, ()))
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

end

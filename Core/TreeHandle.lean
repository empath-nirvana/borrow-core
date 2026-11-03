import Core.TreeHeap
import Core.EffRules

/-!
# A scheduler handler at the step-indexed relation over the tree world  `[spec §62]`

`[handle]` at `cerwpT` over the tree, for the handler a program runs at its top (the scheduler):
the handled computation at `cerwpT` at a table `T` whose operations are all the handler's, the
handler's clauses at the empty table. It is `SI/HandleN.lean`'s `erwp_handle` (spike, chain
world) re-proved at `twp`: by induction on the index, with no `hdv` premise, `κ` resumed at
`k′ < k` by the induction hypothesis. What the tree adds is the frame.

**The frame at a resume.** `contShareT` resumes a stored continuation under frames meeting
`fdAt en v F O′`: the stored branch's frame condition and the entry's `fd` at the records it owns
there. A clause that resumes `κ` beside a state it keeps puts that state in the resumed run's
frame. The clause is told what the frame of the resumed run must avoid as a set of locations `M`
(`fdMask M`: valid, and nothing at `M` at any depth): the lent and escrow locations of every record
the branch has owned at a resume (`recMask`). The table's `fd` must follow from that (`fdJoinT`),
and so does the stored branch's frame condition, by induction (`cerwpT_schedHandle`'s `hFe`).

**What the frame avoids is learnt at the stop** (`twp_bind_fd`). A run whose frame avoids the
masks of the records it starts with ends with a frame that avoids the masks of the records it ends
with: where a mask was added, `EndT`'s `MaskDiff` clause says the frame holds nothing; elsewhere
the frame is the start's re-read (`noneAt_recMask_end`). So a record the run opened during the
segment is avoided by the frame as soon as it exists: this is how the clause that receives `κ` at
the stop knows that its own frame holds nothing of the stopped branch's lends.

The cancel steps of `κ` (`twpE_kappa_cancel`, `twpE_kappaC_cancel`) and its cell
(`twpE_kappaCell`, `twpE_kappaC_resume`) are the spike's `erwp_kappa_*` at `twp`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE kappa kappaC
  kappaCell kappaAt capTag clauseAt hndVal ccatchE freeE)

/-! ### Frames that avoid a set of locations -/

/-- **The frame avoids `M`**: it is valid and its flattening holds nothing at `M`. -/
def fdMask (M : BoCa.Loc → Prop) : TFrame := fun _ ρf => ResUT.Valid ρf ∧ NoneAt M ρf

/-- Avoiding a set of locations is kept by re-reading. -/
theorem fdMask_mono (M : BoCa.Loc → Prop) : (fdMask M).Mono := by
  intro w w' ρ ρ' hE hr ⟨hv, hn⟩
  exact ⟨WitRel.ResUT.Valid.sim (W := rrRel _ _ _) hv hr.rsim, NoneAt.rr hE.1 hv hr hn⟩

theorem fdMask_empty (M : BoCa.Loc → Prop) (w : TWd) : fdMask M w (PMap.empty : TRes w.K) :=
  ⟨⟨_, flat_empty⟩, noneAt_empty M⟩

theorem fdMask_le {M M' : BoCa.Loc → Prop} (h : ∀ x, M x → M' x) {w : TWd} {ρf : TRes w.K}
    (hf : fdMask M' w ρf) : fdMask M w ρf :=
  ⟨hf.1, hf.2.mono h⟩

/-- **The resumer's guarantee at a join**: the frame holds nothing at the lent locations and the
escrows' exclusive locations of the records the resumed run owns. -/
def fdJoinT : BoCa.Val → (w : TWd) → List (FrameRecT w.K) → TRes w.K → Prop :=
  fun _ w O ρf => fdMask (recMask O) w ρf

/-- Conjunction of frame conditions. -/
def TFrame.and (F G : TFrame) : TFrame := fun w ρf => F w ρf ∧ G w ρf

theorem TFrame.and_mono {F G : TFrame} (hF : F.Mono) (hG : G.Mono) : (F.and G).Mono :=
  fun w w' ρ ρ' hE hr h => ⟨hF w w' ρ ρ' hE hr h.1, hG w w' ρ ρ' hE hr h.2⟩

/-! ### What the frame avoids at the end of a run -/

/-- **A record the run holds at its end is avoided by the frame** (item 4 of #781 slice (d)): the
frame at the start avoided the masks of the records the run started with; at the end the frame is
the start's re-read, and where the end's masks add a location `EndT`'s `MaskDiff` clause says the
frame holds nothing there. A lend the run opened during the segment is one such location. -/
theorem noneAt_recMask_end {K K' : WCactus} {Θ : LocTy} (hE : K.Ext K') {O₀ : List (FrameRecT K)}
    {O' : List (FrameRecT K')} {ρf : TRes K} {ρf' : TRes K'} (hv : ResUT.Valid ρf)
    (hr : RR Θ ρf ρf') (h₀ : NoneAt (recMask O₀) ρf)
    (hd : NoneAt (MaskDiff (recMask O₀) (recMask O')) ρf') : NoneAt (recMask O') ρf' := by
  refine ((NoneAt.rr hE hv hr h₀).or hd).mono fun x hx => ?_
  by_cases h : recMask O₀ x
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨hx, h⟩)

/-- **Bind, the continuation told what the frame avoids.** As `twp_bind`; the run of `e` is at
a frame condition `Fe` that every `F`-frame meets, the `F`-frames avoid the masks of the records
`e` starts with (`hJ`), and the continuation from `K[t]` is at `F` with the frame avoiding the
masks of the records the run of `e` ended with (`noneAt_recMask_end`). -/
theorem twp_bind_fd {F Fe : TFrame} (hFm : F.Mono) (hFe : ∀ w ρf, F w ρf → Fe w ρf)
    {P Q : TPost} (K : Kont) {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (hJ : ∀ w₀ ρf, F w₀ ρf → NoneAt (recMask O) ρf)
    (he : twp (ℍ := ℍ) Fe P n w ls O e ρ)
    (hk : ∀ k, k ≤ n → ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K)) t
      (ρ' : TRes w'.K), CovR (sem w'.Θ) w'.K ρ' → (∀ x ∈ ls', CovR (sem w'.Θ) w'.K x.1.R) →
      (∀ r ∈ O', CovR (sem w'.Θ) w'.K r.R) → P k w' ls' O' t ρ' →
      twp (ℍ := ℍ) (F.and (fdMask (recMask O'))) Q k w' ls' O' (K.plug t) ρ') :
    twp (ℍ := ℍ) F Q n w ls O (K.plug e) ρ := by
  classical
  intro w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hf hc hS hR hI hfd j μ' E hj hrun hfin
  have go : ∀ j₁ j₂ μ₁ t, j₁ + j₂ = j → StepsN (ℍ := ℍ) j₁ μ e μ₁ t → Final (ℍ := ℍ) μ₁ t →
      StepsN (ℍ := ℍ) j₂ μ₁ (K.plug t) μ' E → EndT Q (n - j) w₀ ρ₀ O₀ ρf psF μ' E := by
    intro j₁ j₂ μ₁ t hjj hrun₁ hfin₁ hrun₂
    obtain ⟨w₁, ρf₁, ρ₁, fρ₁, psF₁, ps₁, O₁, ls₁, g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
        g₁₁⟩ := he w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO (hFe _ _ hF) hf hc hS hR hI hfd j₁ μ₁ t
        (by omega) hrun₁ hfin₁
    have hcov : CovR (sem w₁.Θ) w₁.K ρ₁ := cov_of_comp g₄ g₇
    have hJ₀ : NoneAt (recMask O₀) ρf := (hJ w₀ ρf hF).mono fun x hx => (recMask_rr hO x).mpr hx
    have hF₁ : (F.and (fdMask (recMask O₁))) w₁ ρf₁ :=
      ⟨hFm _ _ _ _ g₀ g₁ hF, covf_valid g₄ g₇,
        noneAt_recMask_end g₀.1 (covf_valid hc hI) g₁ hJ₀ g₁₀⟩
    obtain ⟨w₂, ρf₂, ρ₂, fρ₂, psF₂, ps₂, O₂, ls₂, k₀, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈, k₉, k₁₀,
        k₁₁⟩ := hk (n - j₁) (Nat.sub_le _ _) w₁ ls₁ O₁ t ρ₁ hcov g₆.cov_ls
        (fun r hr => g₆.cov_ps r (g₅.left r hr)) g₈ w₁ ρ₁ ρf₁ fρ₁ ls₁ O₁ ps₁ psF₁ μ₁
        (TWd.Ext.refl _ _) (RR.refl hcov) (SRecsRR.refl g₆.cov_ls)
        (RecsRR.refl fun r hr => g₆.cov_ps r (g₅.left r hr)) hF₁ (ResUT.hash_symm g₃) g₄ g₅ g₆
        g₇ (fd_stepsN hrun₁ hfd) j₂ μ' E (by omega) hrun₂ hfin
    refine ⟨w₂, ρf₂, ρ₂, fρ₂, psF₂, ps₂, O₂, ls₂, g₀.trans g₁ k₀, RRw.trans k₀.1 g₁ k₁,
      g₂.trans k₀.1 k₂, k₃, k₄, k₅, k₆, k₇, ?_, UpdX.trans k₀.1 g₉ k₉, ?_, g₁₁.trans g₉ k₁₁⟩
    · rwa [show n - j₁ - j₂ = n - j by omega] at k₈
    · have hf₂ : NoneAt (MaskDiff (recMask O₀) (recMask O₁)) ρf₂ :=
        g₁₀.rr k₀.1 (covf_valid g₄ g₇) k₁
      exact (hf₂.or k₁₀).mono fun x hx => maskDiff_trans x hx
  rcases stepsN_plug_split K hrun with ⟨e', rfl, hrun'⟩ |
    ⟨j₁, j₂, μ₁, t, hjj, hrun₁, hirr, hrun₂⟩
  · have hfin' : Final (ℍ := ℍ) μ' e' := fun μ'' e'' hs => hfin _ _ (hs.plug K)
    exact go j 0 μ' e' (by omega) hrun' hfin' (.refl _ _)
  · exact go j₁ j₂ μ₁ t hjj hrun₁ hirr hrun₂

/-! ### The top-level table -/

/-- A value in `Q`. -/
def valPost (Q : TPostV) : TPost := fun k w ls O t ρ => ∃ v : Val, t = v.1 ∧ Q k w ls O v ρ

/-- A postcondition over values, downward closed in the index. -/
def TPostV.Down (Q : TPostV) : Prop := ∀ n w ls O v ρ, Q (n + 1) w ls O v ρ → Q n w ls O v ρ

theorem valPost_down {Q : TPostV} (hQ : Q.Down) : (valPost Q).Down :=
  fun _ _ _ _ _ _ ⟨v, hv, hq⟩ => ⟨v, hv, hQ _ _ _ _ _ _ hq⟩

/-- **At the empty table `cerwpT` is `twp` at its values**: nothing stops. -/
theorem cerwpTE_iff {Q : TPostV} {Fb F : TFrame} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K} :
    cerwpT (ℍ := ℍ) (opTableT OpTabT.empty) Q Fb F n w ls O e ρ ↔
      twp (ℍ := ℍ) F (valPost Q) n w ls O e ρ := by
  rw [cerwpT_eq]
  constructor
  · refine fun h => twp_mono (fun _ _ _ _ _ _ ht => ?_) h
    rcases ht with ht | ht
    · exact ht
    · exact (opTableT_empty_false ht).elim
  · exact fun h => twp_mono (fun _ _ _ _ _ _ ht => Or.inl ht) h

/-! ### Allocation at the run's own world -/

/-- **Allocation at `twp`, read at the run's own world**: `twp_alloc` with the continuation at
the resource the run holds, every cell it may allocate at. -/
theorem twp_alloc_here {F : TFrame} {Q : TPost} (hQ : Q.Down) (Kc : Kont) (v : BoCa.Val)
    {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρ : TRes w.K}
    (h : ∀ (l : BoCa.Loc) (ρ₁ : TRes w.K), ResUT.CompS ρ (ResUT.single l (CellUT.ownOf v)) ρ₁ →
      twp (ℍ := ℍ) F Q n w ls O (Kc.plug (.val (.loc l))) ρ₁) :
    twp (ℍ := ℍ) F Q n w ls O (Kc.plug (.app (.val (.prim .alloc)) (.val v))) ρ := by
  classical
  refine twp_alloc hQ Kc v fun w₀ ρ₀ ls₀ O₀ hE hr hl hO l ρ₁₀ hc₀ => ?_
  have hl₀ : ρ₀.get l = none := ResUT.compatS_single_own (ResUT.CompatS.symm hc₀.1)
  have hlw : ρ.get l = none := (hr.1 l).mpr hl₀
  obtain ⟨ρ₁, hρ₁⟩ := (ResUT.compS_defined_iff ρ (ResUT.single l (CellUT.ownOf v))).mpr
    (compatS_single_of_get_noneT hlw)
  have hrs : RR (sem w₀.Θ) (ResUT.single l (CellUT.ownOf (K := w.K) v))
      (ResUT.single l (CellUT.ownOf (K := w₀.K) v)) := by
    refine ⟨fun m => ?_, fun m ψ ψ' e e' => ?_⟩
    · by_cases hm : m = l
      · subst hm; simp
      · simp only [ResUT.single_get_ne _ hm]
    · obtain ⟨rfl, rfl⟩ := ResUT.single_get_eq_some e
      obtain ⟨-, rfl⟩ := ResUT.single_get_eq_some e'
      exact RC.own _ _
  obtain ⟨ρ₁', hc', hr'⟩ := RR.compS hr hrs hρ₁
  obtain rfl := ResUT.CompS.functional hc' hc₀
  have hE₁ : w.Ext w₀ ρ₁ := ⟨hE.1, fun m hm => hE.2 m (holdsMut_of_compS_own hρ₁ hm)⟩
  exact twp_kripke hE₁ hr' hl hO (h l ρ₁ hρ₁)

/-! ### `κ` at `twp` -/

/-- Resuming `κ` at `a` runs `hnd H K[a]`: four deterministic steps, for free. -/
theorem twp_kappa_resume {F : TFrame} {Q : TPost} (hQ : Q.Down) (H : Val) (K : Kont) (a : Val)
    {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρ : TRes w.K}
    (h : twp (ℍ := ℍ) F Q n w ls O (hndE H (K.plug (.val a))) ρ) :
    twp (ℍ := ℍ) F Q n w ls O (.app (.app (kappa H K) (.val (Val.inj₁ .unit))) (.val a)) ρ := by
  refine twp_det hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl (Kont.appL .hole a)) ?_
  refine twp_det hQ
    (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl (Kont.appL .hole a)) ?_
  refine twp_det hQ (fun μ => step1Only_plug (Head.seq μ _) rfl (Kont.appL .hole a)) ?_
  refine twp_det hQ (fun μ => step1Only_plug (Head.beta μ _ a) rfl .hole) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, kappa_resume_subst]
  exact h

/-- **Cancelling `κ`** runs `ccatch (K†[raise …])`: three deterministic steps, for free. -/
theorem twp_kappa_cancel {F : TFrame} {Q : TPost} (hQ : Q.Down) (H : Val) (K : Kont) {n : Nat}
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρ : TRes w.K}
    (h : twp (ℍ := ℍ) F Q n w ls O (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))) ρ) :
    twp (ℍ := ℍ) F Q n w ls O (.app (kappa H K) (.val (Val.inj₂ .unit))) ρ := by
  refine twp_det hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  refine twp_det hQ (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
  refine twp_det hQ (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, kappa_cancel_subst]
  exact h

/-- **The capture cell's allocation**: `κ` before its cell, at an evaluation position, allocates
the cell by the ordinary `alloc` step and becomes `kappaC` at its location. -/
theorem twp_kappaCell {F : TFrame} {Q : TPost} (hQ : Q.Down) (hasCancel : Bool) (H : Val)
    (K Kc : Kont) {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)}
    {ρ : TRes w.K}
    (h : ∀ (l : BoCa.Loc) (ρ₁ : TRes w.K),
      ResUT.CompS ρ (ResUT.single l (CellUT.ownOf BoCa.Val.unit)) ρ₁ →
      twp (ℍ := ℍ) F Q n w ls O (Kc.plug (kappaC hasCancel l H K)) ρ₁) :
    twp (ℍ := ℍ) F Q n w ls O (Kc.plug (kappaCell hasCancel H K)) ρ := by
  have e : Kc.plug (kappaCell hasCancel H K) =
      (Kc.comp (.appR (.val (.lam (BoCa.BoLo.kappaCBody hasCancel H K))) .hole)).plug
        (.app (.val (.prim .alloc)) (.val Val.unit)) := by
    rw [Kont.plug_comp]; rfl
  rw [e]
  refine twp_alloc_here hQ _ Val.unit fun l ρ₁ hc => ?_
  rw [Kont.plug_comp]
  refine twp_det hQ (fun μ => step1Only_plug (Head.beta μ _ (Val.loc l)) rfl Kc) ?_
  rw [kappaCBody_subst]
  exact h l ρ₁ hc

/-- **Resuming a `κ` that owns a cell**: the cell is freed, then `hnd H K[a]` runs. -/
theorem twp_kappaC_resume {F : TFrame} {Q : TPost} (hQ : Q.Down) (hasCancel : Bool)
    (l : BoCa.Loc) (H : Val) (K : Kont) (a : Val) {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {ρ ρ₂ : TRes w.K}
    (hc : ResUT.CompS (ResUT.single l (CellUT.ownOf BoCa.Val.unit)) ρ₂ ρ)
    (h : twp (ℍ := ℍ) F Q n w ls O (hndE H (K.plug (.val a))) ρ₂) :
    twp (ℍ := ℍ) F Q n w ls O
      (.app (.app (kappaC hasCancel l H K) (.val (Val.inj₁ .unit))) (.val a)) ρ := by
  refine twp_det hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl (Kont.appL .hole a)) ?_
  refine twp_det hQ
    (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl (Kont.appL .hole a)) ?_
  refine twp_det hQ (fun μ => step1Only_plug (Head.seq μ _) rfl (Kont.appL .hole a)) ?_
  refine twp_free hQ (Kont.appL (Kont.seq .hole _) a) l Val.unit hc ?_
  refine twp_det hQ (fun μ => step1Only_plug (Head.seq μ _) rfl (Kont.appL .hole a)) ?_
  refine twp_det hQ (fun μ => step1Only_plug (Head.beta μ _ a) rfl .hole) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, show (0 + 1 + 1 : Nat) = 2 from rfl, kappa_resume_subst]
  exact h

/-- **Cancelling a cancellable `κ`**: the cell is freed, then `ccatch (K†[raise …])` runs. -/
theorem twp_kappaC_cancel {F : TFrame} {Q : TPost} (hQ : Q.Down) (l : BoCa.Loc) (H : Val)
    (K : Kont) {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)}
    {ρ ρ₂ : TRes w.K} (hc : ResUT.CompS (ResUT.single l (CellUT.ownOf BoCa.Val.unit)) ρ₂ ρ)
    (h : twp (ℍ := ℍ) F Q n w ls O (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))) ρ₂) :
    twp (ℍ := ℍ) F Q n w ls O (.app (kappaC true l H K) (.val (Val.inj₂ .unit))) ρ := by
  refine twp_det hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl .hole) ?_
  refine twp_det hQ (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
  refine twp_det hQ (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  refine twp_free hQ (Kont.seq .hole _) l Val.unit hc ?_
  refine twp_det hQ (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, kappa_cancel_subst]
  exact h

/-- **Cancelling `κ` inside a context**: `Kc[κ (inj₂ ())]` runs `Kc[ccatch (K†[raise …])]`. -/
theorem twp_kappa_cancel_in {F : TFrame} {Q : TPost} (hQ : Q.Down) (H : Val) (K Kc : Kont)
    {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρ : TRes w.K}
    (h : twp (ℍ := ℍ) F Q n w ls O
      (Kc.plug (ccatchE (K.dead.plug (raiseE (.val (cancelVal none)))))) ρ) :
    twp (ℍ := ℍ) F Q n w ls O (Kc.plug (.app (kappa H K) (.val (Val.inj₂ .unit)))) ρ := by
  refine twp_det hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl Kc) ?_
  refine twp_det hQ (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl Kc) ?_
  refine twp_det hQ (fun μ => step1Only_plug (Head.seq μ _) rfl Kc) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, kappa_cancel_subst]
  exact h

/-- **Cancelling a cancellable `κ` inside a context**: its cell is freed, then
`Kc[ccatch (K†[raise …])]` runs. -/
theorem twp_kappaC_cancel_in {F : TFrame} {Q : TPost} (hQ : Q.Down) (l : BoCa.Loc) (H : Val)
    (K Kc : Kont) {n : Nat} {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)}
    {ρ ρ₂ : TRes w.K} (hc : ResUT.CompS (ResUT.single l (CellUT.ownOf BoCa.Val.unit)) ρ₂ ρ)
    (h : twp (ℍ := ℍ) F Q n w ls O
      (Kc.plug (ccatchE (K.dead.plug (raiseE (.val (cancelVal none)))))) ρ₂) :
    twp (ℍ := ℍ) F Q n w ls O (Kc.plug (.app (kappaC true l H K) (.val (Val.inj₂ .unit)))) ρ := by
  refine twp_det hQ (fun μ => step1Only_plug (Head.beta μ _ _) rfl Kc) ?_
  refine twp_det hQ (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl Kc) ?_
  refine twp_det hQ (fun μ => step1Only_plug (Head.seq μ _) rfl Kc) ?_
  have e₁ : ∀ e : Expr, Kc.plug (.seq (freeE (.val (.loc l))) e) =
      (Kc.comp (Kont.seq .hole e)).plug (freeE (.val (.loc l))) := fun e => by
    rw [Kont.plug_comp]; rfl
  show twp (ℍ := ℍ) F Q n w ls O (Kc.plug (.seq (freeE (.val (.loc l)))
    (Expr.subst 0 Val.unit (Expr.subst (0 + 1) (Val.shift 1 0 Val.unit.inj₂)
      (ccatchE ((Kont.shift 2 0 K.dead).plug (raiseE (Expr.val (cancelVal none))))))))) ρ
  rw [e₁]
  refine twp_free hQ _ l Val.unit hc ?_
  rw [Kont.plug_comp]
  refine twp_det hQ (fun μ => step1Only_plug (Head.seq μ _) rfl Kc) ?_
  rw [show (0 + 1 : Nat) = 1 from rfl, kappa_cancel_subst]
  exact h

/-! ### The scheduler's interface -/

/-- **`κ` as the scheduler's clause receives it.** At every extension of the stop's world, on
the share's and records' re-readings, at every resume list keeping the stop list's records the
share reads (`KeepRel`): resumed at every answer the entry accepts, at every `k′ < k`, it is the
scheduler's relation (`cerwpT` at the empty table) under every frame condition whose frames avoid
`M`; and at a cancellable entry (`q ≠ lin`, `fin`) so is its cancel branch run under the scheduler
`H` again, `hnd H (κ (inj₂ ()))`: the unwinding may stop at an operation of `H`'s, and then comes
back to `H`'s clause as a stored continuation like any other. `M` holds the lent and escrow
locations of the records the branch owns at the stop (`SchedClauseT` hands `recMask O`): a state
the clause keeps beside the resumed run must hold nothing there, and be valid. At an unrestricted
operation `κ` owns nothing, so it may be dropped. -/
def KapSchedT (Qout : TPostV) (M : BoCa.Loc → Prop) (en : OpEntT) (H : Val) (k : Nat) (w : TWd)
    (ls : List (SRecT w.K)) (O : List (FrameRecT w.K)) (v κ : Val) : TRes w.K → Prop := fun ρ =>
  (en.q = .unr → ρ = PMap.empty) ∧ (∀ (w' : TWd) (ρ' : TRes w'.K) (ls' : List (SRecT w'.K))
    (O' : List (FrameRecT w'.K)),
    w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' → KeepRel w'.Θ ls ls' ρ → RecsRR w'.Θ O O' →
    ∀ k', k' < k → ∀ (a : Val) (σ σ' : TRes w'.K), en.PBv v k' w' ls' a σ →
      ResUT.CompS ρ' σ σ' → ∀ F' : TFrame, F'.Mono → (∀ w'' ρf, F' w'' ρf → fdMask M w'' ρf) →
      cerwpT (ℍ := ℍ) (opTableT OpTabT.empty) Qout F' F' k' w' ls' O'
        (.app (.app κ.1 (.val (Val.inj₁ .unit))) (.val a)) σ') ∧
  ∀ (w' : TWd) (ρ' : TRes w'.K) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K)),
    w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' → KeepRel w'.Θ ls ls' ρ → RecsRR w'.Θ O O' →
    en.q ≠ .lin → en.fin = true → ∀ k', k' < k → ∀ F' : TFrame, F'.Mono →
      (∀ w'' ρf, F' w'' ρf → fdMask M w'' ρf) →
      cerwpT (ℍ := ℍ) (opTableT OpTabT.empty) Qout F' F' k' w' ls' O'
        (hndE H (.app κ.1 (.val (Val.inj₂ .unit)))) ρ'

/-- A `κ` held at `w` is held at every extension of `w`, on its re-reading, at any list there
keeping the records of `ls` its share reads. -/
theorem KapSchedT.kripke {Qout : TPostV} {M : BoCa.Loc → Prop} {en : OpEntT} {H : Val} {k : Nat}
    {w w₁ : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ls₁ : List (SRecT w₁.K)}
    {O₁ : List (FrameRecT w₁.K)} {v κ : Val} {ρ : TRes w.K} {ρ₁ : TRes w₁.K}
    (h : KapSchedT (ℍ := ℍ) Qout M en H k w ls O v κ ρ) (hE : w.Ext w₁ ρ)
    (hr : RRw (w := w) (w' := w₁) ρ ρ₁) (hl : KeepRel w₁.Θ ls ls₁ ρ) (hO : RecsRR w₁.Θ O O₁) :
    KapSchedT (ℍ := ℍ) Qout M en H k w₁ ls₁ O₁ v κ ρ₁ :=
  ⟨fun hu => by obtain rfl := h.1 hu; exact RR.of_empty hr,
    fun w' ρ' ls' O' hE' hr' hx hO' => h.2.1 w' ρ' ls' O' (hE.trans hr hE')
      (RRw.trans hE'.1 hr hr') (hl.trans hE'.1 hr hx) (hO.trans hE'.1 hO'),
    fun w' ρ' ls' O' hE' hr' hx hO' => h.2.2 w' ρ' ls' O' (hE.trans hr hE')
      (RRw.trans hE'.1 hr hr') (hl.trans hE'.1 hr hx) (hO.trans hE'.1 hO')⟩

/-- **The return clause**: the handled run's value in `Qin`, under every frame condition whose
frames avoid the masks of the records the run ended with. -/
def SchedRetT (Qin Qout : TPostV) (hr : Val) : Prop :=
  ∀ (F : TFrame) (k : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (v : Val) (ρ : TRes w.K), F.Mono →
    (∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) →
    CovR (sem w.Θ) w.K ρ → (∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) →
    (∀ r ∈ O, CovR (sem w.Θ) w.K r.R) → Qin k w ls O v ρ →
    cerwpT (ℍ := ℍ) (opTableT OpTabT.empty) Qout F F k w ls O (.app (.val hr) (.val v)) ρ

/-- **An operation's clause**: the payload's resource in the entry's `PA`, `κ` in `KapSchedT` at
the masks of the records `O` the branch owns at the stop (which the entry's `oc` admits), under
every frame condition whose frames avoid them. -/
def SchedClauseT (H : Val) (Qout : TPostV) (en : OpEntT) (c : Val) : Prop :=
  ∀ (F : TFrame) (k : Nat) (w : TWd) (ls : List (SRecT w.K))
    (O : List (FrameRecT w.K)) (v κ : Val) (ρ : TRes w.K), F.Mono →
    en.oc w O → (∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) →
    CovR (sem w.Θ) w.K ρ → (∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) →
    (∀ r ∈ O, CovR (sem w.Θ) w.K r.R) →
    (∃ ρa ρk : TRes w.K, ResUT.CompS ρa ρk ρ ∧ en.PA k w ls v ρa ∧
      KapSchedT (ℍ := ℍ) Qout (recMask O) en H k w ls O v κ ρk) →
    cerwpT (ℍ := ℍ) (opTableT OpTabT.empty) Qout F F k w ls O
      (.app (.val c) (.pair (.val v) κ.1)) ρ

/-- **What a top-level scheduler `hnd (n₀, (qs, (h_ret, hs)))` must satisfy**, for tasks at the
table `T` answering `Qin` and the program answering `Qout`:

* every operation of `T` is the scheduler's (`n₀`);
* each non-abortive operation's continuation tag (`qs`) is its entry's qualifier;
* the entry's resumer guarantee `fd` follows from the join's (`fdJoinT`): a resumer whose frame
  avoids the masks of the resumed branch's records meets it;
* `Qout` is downward closed in the index;
* the return clause (`SchedRetT`) and every operation's clause (`SchedClauseT`), at the empty table,
  each `κ` read by `KapSchedT`: resumed beside any state that is valid and holds nothing at the
  masks of the records the branch owns at its stop. -/
def SchedOKT (T : OpTabT) (n₀ : UInt32) (qs hr hs : Val) (Qin Qout : TPostV) : Prop :=
  (∀ m i, m ≠ n₀ → T m i = none) ∧
  (∀ i en, T n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag) ∧
  (∀ i en, T n₀ i = some en → ∀ v w O ρf, fdJoinT v w O ρf → en.fd v w O ρf) ∧
  Qout.Down ∧ SchedRetT (ℍ := ℍ) Qin Qout hr ∧
  (∀ i en, T n₀ i = some en →
    ∃ c, clauseAt hs.1 i.toNat = some c ∧
      SchedClauseT (ℍ := ℍ) (hndVal n₀ qs hr hs) Qout en c)

/-! ### `[handle]` for the scheduler -/

/-- **`[handle]` at `cerwpT` over the tree world, for a top-level scheduler**, by induction on the
index. The handled run `e` at the table `T`, at a base frame condition `Fb` every valid frame
meets, and at a present frame condition `Fe` met by every frame avoiding `M` (which holds the masks
of `e`'s records); the handler's run under frames meeting `F`, each avoiding `M`. At a stop the
clause runs under `F` with the frame avoiding the stopped branch's masks (`twp_bind_fd`), and
receives `κ` at the masks of the records the branch owns at this stop. `κ` resumed is the share's
continuation (`contShareT_resume`) under the handler, at `k′ < k`, by the induction hypothesis:
its frame condition, `fdAt en v Fb O″`, is met by every frame avoiding the branch's masks at the
stop (`SchedOKT`'s `fd` clause). Nothing accumulates along resumes: each resume reads the records
at its stop only. -/
theorem cerwpT_schedHandle {T : OpTabT} {n₀ : UInt32} {qs hr hs : Val} {Qin Qout : TPostV}
    (hSc : SchedOKT (ℍ := ℍ) T n₀ qs hr hs Qin Qout) :
    ∀ (n : Nat) (M : BoCa.Loc → Prop) (F Fb Fe : TFrame) (w : TWd) (ls : List (SRecT w.K))
      (O : List (FrameRecT w.K)) (e : Expr) (ρ : TRes w.K), F.Mono →
      (∀ w' ρf, F w' ρf → fdMask M w' ρf) → (∀ x, recMask O x → M x) →
      (∀ w' ρf, ResUT.Valid ρf → Fb w' ρf) → (∀ w' ρf, fdMask M w' ρf → Fe w' ρf) →
      cerwpT (ℍ := ℍ) (opTableT T) Qin Fb Fe n w ls O e ρ →
      twp (ℍ := ℍ) F (valPost Qout) n w ls O (hndE (hndVal n₀ qs hr hs) e) ρ := by
  obtain ⟨hT, htag, hfd, hQd, hret, hop⟩ := hSc
  have hPd := valPost_down hQd
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M F Fb Fe w ls O e ρ hFm hFM hOM hFb hFe h
  show twp (ℍ := ℍ) F (valPost Qout) n w ls O ((hndK (hndVal n₀ qs hr hs)).plug e) ρ
  rw [cerwpT_eq] at h
  refine twp_bind_fd hFm (fun w ρf hf => hFe w ρf (hFM w ρf hf)) (hndK (hndVal n₀ qs hr hs))
    (fun w₀ ρf hf => (hFM w₀ ρf hf).2.mono hOM) h
    (fun k hk w' ls' O' t ρ' hcov' hls' hO' ht => ?_)
  -- the clause's frame: `F`, avoiding the masks of the records the run ended with
  have hF'm : (F.and (fdMask (recMask O'))).Mono := TFrame.and_mono hFm (fdMask_mono _)
  have hF'M : ∀ w'' ρf, (F.and (fdMask (recMask O'))) w'' ρf → fdMask (recMask O') w'' ρf :=
    fun _ _ hf => hf.2
  rcases ht with ⟨v, rfl, hv⟩ | ht
  · -- `[ret]`
    refine twp_det hPd (fun μ => step1Only_plug (Head.hret μ n₀ qs hr hs v) rfl .hole) ?_
    exact cerwpTE_iff.mp (hret _ k w' ls' O' v ρ' hF'm hF'M hcov' hls' hO' hv)
  · obtain ⟨K₁, m, i, v, en, rfl, hK₁, hTe, ha, hoc, ρa, ρk, hcak, hA, hsh⟩ := ht
    by_cases hm : m = n₀
    swap
    · rw [hT m i hm] at hTe; cases hTe
    subst hm
    obtain ⟨c, hc, hcl⟩ := hop i en hTe
    refine twp_det hPd
      (fun μ => step1Only_plug (Head.hop μ m i qs hr hs c v K₁ hc hK₁) rfl .hole) ?_
    -- the resumed run's present frame condition, met by every frame avoiding the branch's
    -- records at this stop
    have hFe' : ∀ (w'' : TWd) (O'' : List (FrameRecT w''.K)), RecsRR w''.Θ O' O'' →
        ∀ w₃ ρf, fdMask (recMask O') w₃ ρf → fdAt en v Fb O'' w₃ ρf :=
      fun w'' O'' hO w₃ ρf hf => ⟨hFb w₃ ρf hf.1,
        fun O₃ hO₃ => hfd i en hTe v w₃ O₃ ρf (fdMask_le (fun x hx =>
          (recMask_rr hO x).mpr ((recMask_rr hO₃ x).mpr hx)) hf)⟩
    -- the resume: the share's continuation under the handler, by the induction hypothesis
    have hres : ∀ (w'' : TWd) (ρk' : TRes w''.K) (ls'' : List (SRecT w''.K))
        (O'' : List (FrameRecT w''.K)), w'.Ext w'' ρk → RRw (w := w') (w' := w'') ρk ρk' →
        KeepRel w''.Θ ls' ls'' ρk → RecsRR w''.Θ O' O'' →
        ∀ k', k' < k → ∀ (a : Val) (σ σ' : TRes w''.K), en.PBv v k' w'' ls'' a σ →
        ResUT.CompS ρk' σ σ' → ∀ F'' : TFrame, F''.Mono →
        (∀ w₃ ρf, F'' w₃ ρf → fdMask (recMask O') w₃ ρf) →
        twp (ℍ := ℍ) F'' (valPost Qout) k' w'' ls'' O''
          (hndE (hndVal m qs hr hs) (K₁.plug (.val a))) σ' := by
      intro w'' ρk' ls'' O'' hE hr' hx hO k' hk' a σ σ' hB hcσ F'' hF''m hF''M
      have h₁ := contShareT_resume hsh hE hr' hx hO hk' hB hcσ
      simp only [cerwpTC, show k' < n by omega, if_true] at h₁
      exact ih k' (by omega) (recMask O') F'' Fb (fdAt en v Fb O'') w'' ls'' O'' _ σ' hF''m
        hF''M (fun x hx => (recMask_rr hO x).mpr hx) hFb (hFe' w'' O'' hO) h₁
    -- the cancel: the share's unwinding under the handler, by the induction hypothesis
    have hcan : ∀ (w'' : TWd) (ρk' : TRes w''.K) (ls'' : List (SRecT w''.K))
        (O'' : List (FrameRecT w''.K)), w'.Ext w'' ρk → RRw (w := w') (w' := w'') ρk ρk' →
        KeepRel w''.Θ ls' ls'' ρk → RecsRR w''.Θ O' O'' → en.q ≠ .lin → en.fin = true →
        ∀ k', k' < k → ∀ F'' : TFrame, F''.Mono →
        (∀ w₃ ρf, F'' w₃ ρf → fdMask (recMask O') w₃ ρf) →
        twp (ℍ := ℍ) F'' (valPost Qout) k' w'' ls'' O''
          (hndE (hndVal m qs hr hs) (ccatchE (K₁.dead.plug (raiseE (.val (cancelVal none))))))
          ρk' := by
      intro w'' ρk' ls'' O'' hE hr' hx hO hq hf k' hk' F'' hF''m hF''M
      have h₁ := (hsh.2 w'' ρk' ls'' O'' hE hr' hx hO).2 hq hf k' hk'
      simp only [cerwpTC, show k' < n by omega, if_true] at h₁
      exact ih k' (by omega) (recMask O') F'' Fb (fdAt en v Fb O'') w'' ls'' O'' _ ρk' hF''m
        hF''M (fun x hx => (recMask_rr hO x).mpr hx) hFb (hFe' w'' O'' hO) h₁
    rw [htag i en hTe ha, kappaAt_tag]
    cases hqq : en.q with
    | unr =>
        refine cerwpTE_iff.mp (hcl _ k w' ls' O' v ⟨kappa (hndVal m qs hr hs) K₁, by
          unfold kappa; exact .lam⟩ ρ' hF'm hoc hF'M hcov' hls' hO'
          ⟨ρa, ρk, hcak, hA, ⟨hsh.1, ?_, ?_⟩⟩)
        · intro w'' ρk' ls'' O'' hE hr' hx hO k' hk' a σ σ' hB hcσ F'' hF''m hF''M
          exact cerwpTE_iff.mpr (twp_kappa_resume hPd _ K₁ a
            (hres w'' ρk' ls'' O'' hE hr' hx hO k' hk' a σ σ' hB hcσ F'' hF''m hF''M))
        · intro w'' ρk' ls'' O'' hE hr' hx hO hq hf k' hk' F'' hF''m hF''M
          exact cerwpTE_iff.mpr (twp_kappa_cancel_in hPd _ K₁ (hndK _)
            (hcan w'' ρk' ls'' O'' hE hr' hx hO hq hf k' hk' F'' hF''m hF''M))
    | lin | cancel =>
        refine twp_kappaCell hPd _ _ K₁ (.appR (.val c) (.pairR v .hole)) fun l ρ₁ hc₁ => ?_
        obtain ⟨x, hx₂, hx₁⟩ :=
          (ResUT.CompS.assoc ρa ρk (ResUT.single l (CellUT.ownOf Val.unit)) ρ₁).mpr
            ⟨ρ', hcak, hc₁⟩
        have hρkl : ρk.get l = none := ResUT.compatS_single_own (ResUT.CompatS.symm hx₂.1)
        have hxl : x.get l = some (CellUT.ownOf Val.unit) := by
          rw [ResUT.Comp.get_of_left_none hx₂ hρkl, ResUT.single_get_self]
        have hxd : x.del l = ρk := (eq_del_of_compS_single (ResUT.CompS.comm hx₂)).symm
        refine cerwpTE_iff.mp (hcl _ k w' ls' O' v ⟨kappaC _ l (hndVal m qs hr hs) K₁,
          isVal_kappaC _ l _ K₁⟩ ρ₁ hF'm hoc hF'M (covR_compS_own hc₁ hcov') hls' hO'
          ⟨ρa, x, hx₁, hA, ⟨fun hu => (by rw [hqq] at hu; cases hu), ?_, ?_⟩⟩)
        swap
        · intro w'' ρx' ls'' O'' hE hr' hxF hO hq hf k' hk' F'' hF''m hF''M
          first
          | exact absurd hqq hq
          | have hρx'l := RR.own_fwd hr' hxl
            have hrk : RRw (w := w') (w' := w'') ρk (ρx'.del l) := hxd ▸ RR.del hr' l
            exact cerwpTE_iff.mpr (twp_kappaC_cancel_in hPd l _ K₁ (hndK _)
              (compS_single_del hρx'l) (hcan w'' (ρx'.del l) ls'' O'' (hE.of_compS_left hx₂) hrk
                (hxF.of_compS_left hx₂) hO hq hf k' hk' F'' hF''m hF''M))
        intro w'' ρx' ls'' O'' hE hr' hxF hO k' hk' a σ σ' hB hcσ F'' hF''m hF''M
        have hρx'l := RR.own_fwd hr' hxl
        have hrk : RRw (w := w') (w' := w'') ρk (ρx'.del l) := hxd ▸ RR.del hr' l
        obtain ⟨z, hz, hzσ⟩ :=
          (ResUT.CompS.assoc (ResUT.single l (CellUT.ownOf Val.unit)) (ρx'.del l) σ σ').mpr
            ⟨ρx', compS_single_del hρx'l, hcσ⟩
        refine cerwpTE_iff.mpr (twp_kappaC_resume hPd _ l _ K₁ a hzσ ?_)
        exact hres w'' (ρx'.del l) ls'' O'' (hE.of_compS_left hx₂) hrk
          (hxF.of_compS_left hx₂) hO k' hk' a σ z hB hz
          F'' hF''m hF''M

end BoCa.Fig16.Tree.Wp

end
